(** * Milestone 5: fallback sequence emission

    When a block checks several offsets of the same base and array, the
    reducer ([WasmBoundsCheckEliminationReducer]) rewrites each
    committed [FallbackInstructionSequence] [s = [start, end)] in a
    single pass over the block:
    - on the main path ([in_fallback_code_] false), before visiting
      [start], [MaybeInsertFallbackSequence] emits the guard of [s]:
      - when the guard fails, execution jumps to fallback code
        ([CloneAndInlineTrappingInstructions]), which runs a copy of
        [[start, end)] with [in_fallback_code_] true (so no nested
        sequence is emitted there), removing only traps in
        [redundant_traps_] and traps already in [guarded_traps_] (from
        earlier sequences on the same path, whose guards passed),
        followed by [Unreachable];
      - when the guard succeeds, [s]'s guarded traps are added to
        [guarded_traps_], and the main path continues from [start],
        removing every trap in [redundant_traps_] or [guarded_traps_].

    Sequences in the same block may overlap or interleave (for instance
    for two different arrays, or for two uncoalesced sequences of the
    same key).  This file models a basic block as a list of instructions
    (state-transforming steps, unconditional traps, and conditional
    bounds checks carrying their trap identity/position), and proves
    that the transformed block produces the exact same outcome as the
    original block—the same final state, or the same trap after the same
    side effects—and never reaches [Unreachable]. *)

From Coq Require Import List Arith Lia Bool.
Import ListNotations.

Section Fallback.

Variable state : Type.
Variable trap_id : Type.

(** Instructions of a basic block (no phis or non-trapping terminators
    occur inside a fallback sequence). *)
Inductive instr : Type :=
| Step (f : state -> state)
| Fatal (t : trap_id)
| Check (t : trap_id) (cond : state -> bool).

(** Outcome of executing a block (or prefix of a block).
    [Trapped t st] records both which check trapped ([t], its message
    and source position) and the exact state [st] (all side effects
    performed before the trap).  [Stuck] represents reaching
    [Unreachable] (or an abort in verifier mode). *)
Inductive outcome : Type :=
| Ok (st : state)
| Trapped (t : trap_id) (st : state)
| Stuck.

(** ** Original semantics *)

(** Execute [len] instructions of [ops] starting at index [a]. *)
Fixpoint eval_range (ops : list instr) (a len : nat) (st : state) : outcome :=
  match len with
  | 0 => Ok st
  | S k =>
      match nth_error ops a with
      | None => Ok st
      | Some (Step f) => eval_range ops (S a) k (f st)
      | Some (Fatal t) => Trapped t st
      | Some (Check t cond) =>
          if cond st then eval_range ops (S a) k st
          else Trapped t st
      end
  end.

Definition eval_orig (ops : list instr) (st : state) : outcome :=
  eval_range ops 0 (length ops) st.

Lemma eval_range_not_stuck :
  forall ops a len st, eval_range ops a len st <> Stuck.
Proof.
  intros ops a len. revert a. induction len as [| k IH]; intros a st; simpl.
  - discriminate.
  - destruct (nth_error ops a) as [[f | t | t cond] |]; try discriminate.
    + apply IH.
    + destruct (cond st); [apply IH | discriminate].
Qed.

Lemma eval_range_past_end :
  forall ops a len st, length ops <= a -> eval_range ops a len st = Ok st.
Proof.
  intros ops a len. revert a.
  induction len as [| k IH]; intros a st Hle; simpl; [reflexivity |].
  assert (Hn : nth_error ops a = None) by (apply nth_error_None; lia).
  rewrite Hn. reflexivity.
Qed.

Lemma eval_range_app :
  forall ops a n1 n2 st,
  eval_range ops a (n1 + n2) st =
  match eval_range ops a n1 st with
  | Ok st' => eval_range ops (a + n1) n2 st'
  | Trapped t st' => Trapped t st'
  | Stuck => Stuck
  end.
Proof.
  intros ops a n1 n2. revert a.
  induction n1 as [| k IH]; intros a st; simpl.
  - rewrite Nat.add_0_r. reflexivity.
  - destruct (nth_error ops a) as [[f | t | t cond] |] eqn:E.
    + rewrite IH, Nat.add_succ_r. reflexivity.
    + reflexivity.
    + destruct (cond st); [rewrite IH, Nat.add_succ_r; reflexivity | reflexivity].
    + apply nth_error_None in E.
      symmetry. apply eval_range_past_end. lia.
Qed.

(** ** Filtered execution (fallback code) *)

(** Execute [len] instructions from [a], removing every [Check] at an
    index [i] with [skip i = true].  No fallback sequences are emitted
    ([in_fallback_code_] is true). *)
Fixpoint eval_filtered (skip : nat -> bool) (ops : list instr)
    (a len : nat) (st : state) : outcome :=
  match len with
  | 0 => Ok st
  | S k =>
      match nth_error ops a with
      | None => Ok st
      | Some (Step f) => eval_filtered skip ops (S a) k (f st)
      | Some (Fatal t) => Trapped t st
      | Some (Check t cond) =>
          if skip a then eval_filtered skip ops (S a) k st
          else if cond st then eval_filtered skip ops (S a) k st
          else Trapped t st
      end
  end.

(** Fallback code ([CloneAndInlineTrappingInstructions]): execute the
    filtered slice [[start, finish)], followed by [Unreachable] ([Stuck]). *)
Definition eval_fallback (skip : nat -> bool) (ops : list instr)
    (start finish : nat) (st : state) : outcome :=
  match eval_filtered skip ops start (finish - start) st with
  | Ok _ => Stuck
  | Trapped t st' => Trapped t st'
  | Stuck => Stuck
  end.

(** ** Main-path execution with fallback sequences *)

Record seq_info := {
  sq_start : nat;
  sq_end : nat;
  sq_guard : state -> bool;
  sq_guarded : nat -> bool
}.

Definition find_seq (seqs : list seq_info) (i : nat) : option seq_info :=
  find (fun s => Nat.eqb (sq_start s) i) seqs.

Definition union_set (s1 s2 : nat -> bool) : nat -> bool :=
  fun j => orb (s1 j) (s2 j).

(** Execute a single instruction at [a], skipping checks in [skip], and
    continuing with [cont]. *)
Definition eval_step (skip : nat -> bool) (ops : list instr) (a : nat)
    (st : state) (cont : state -> outcome) : outcome :=
  match nth_error ops a with
  | None => Ok st
  | Some (Step f) => cont (f st)
  | Some (Fatal t) => Trapped t st
  | Some (Check t cond) =>
      if skip a then cont st
      else if cond st then cont st
      else Trapped t st
  end.

(** Main-path execution of the rewritten block
    ([WasmBoundsCheckEliminationReducer]):
    at each index [a], if a sequence [s] starts at [a], test its guard:
    - if it fails, run [eval_fallback] with the checks currently known
      safe ([redundant] and [guarded], before adding [s]'s traps);
    - if it succeeds, add [s]'s guarded traps to [guarded] and continue
      on the fast path. *)
Fixpoint eval_main (ops : list instr) (redundant : nat -> bool)
    (seqs : list seq_info) (guarded : nat -> bool)
    (a len : nat) (st : state) : outcome :=
  match len with
  | 0 => Ok st
  | S k =>
      match find_seq seqs a with
      | Some s =>
          if sq_guard s st then
            let guarded' := union_set guarded (sq_guarded s) in
            eval_step (union_set redundant guarded') ops a st
              (eval_main ops redundant seqs guarded' (S a) k)
          else
            eval_fallback (union_set redundant guarded) ops
              (sq_start s) (sq_end s) st
      | None =>
          eval_step (union_set redundant guarded) ops a st
            (eval_main ops redundant seqs guarded (S a) k)
      end
  end.

Definition eval_transformed (ops : list instr) (redundant : nat -> bool)
    (seqs : list seq_info) (st : state) : outcome :=
  eval_main ops redundant seqs (fun _ => false) 0 (length ops) st.

(** ** Verifier mode ([VerifyRedundantBoundsCheck])

    Every removed check is kept as a run-time assertion that aborts
    ([Stuck]) when its condition fails. *)

Definition eval_step_verified (skip : nat -> bool) (ops : list instr) (a : nat)
    (st : state) (cont : state -> outcome) : outcome :=
  match nth_error ops a with
  | None => Ok st
  | Some (Step f) => cont (f st)
  | Some (Fatal t) => Trapped t st
  | Some (Check t cond) =>
      if skip a then
        if cond st then cont st else Stuck
      else if cond st then cont st
      else Trapped t st
  end.

Fixpoint eval_filtered_verified (skip : nat -> bool) (ops : list instr)
    (a len : nat) (st : state) : outcome :=
  match len with
  | 0 => Ok st
  | S k =>
      eval_step_verified skip ops a st
        (eval_filtered_verified skip ops (S a) k)
  end.

Definition eval_fallback_verified (skip : nat -> bool) (ops : list instr)
    (start finish : nat) (st : state) : outcome :=
  match eval_filtered_verified skip ops start (finish - start) st with
  | Ok _ => Stuck
  | Trapped t st' => Trapped t st'
  | Stuck => Stuck
  end.

Fixpoint eval_main_verified (ops : list instr) (redundant : nat -> bool)
    (seqs : list seq_info) (guarded : nat -> bool)
    (a len : nat) (st : state) : outcome :=
  match len with
  | 0 => Ok st
  | S k =>
      match find_seq seqs a with
      | Some s =>
          if sq_guard s st then
            let guarded' := union_set guarded (sq_guarded s) in
            eval_step_verified (union_set redundant guarded') ops a st
              (eval_main_verified ops redundant seqs guarded' (S a) k)
          else
            eval_fallback_verified (union_set redundant guarded) ops
              (sq_start s) (sq_end s) st
      | None =>
          eval_step_verified (union_set redundant guarded) ops a st
            (eval_main_verified ops redundant seqs guarded (S a) k)
      end
  end.

Definition eval_transformed_verified (ops : list instr) (redundant : nat -> bool)
    (seqs : list seq_info) (st : state) : outcome :=
  eval_main_verified ops redundant seqs (fun _ => false) 0 (length ops) st.

(** ** Proof obligations (discharged by the analysis, Canonical.v, and Z3) *)

Section Soundness.

Variable ops : list instr.
Variable redundant : nat -> bool.
Variable seqs : list seq_info.

(** [reaches st0 i st]: starting from [st0], the original block reaches
    index [i] in state [st]. *)
Definition reaches (st0 : state) (i : nat) (st : state) : Prop :=
  eval_range ops 0 i st0 = Ok st.

(** A check set [S] is sound for initial state [st0] when every check in
    [S] succeeds whenever the original execution reaches it. *)
Definition checks_sound_for (st0 : state) (S : nat -> bool) : Prop :=
  forall j st t cond,
  S j = true ->
  reaches st0 j st ->
  nth_error ops j = Some (Check t cond) ->
  cond st = true.

(** 1. Redundant checks cannot fail (Persistence.v + Canonical.v + Z3). *)
Hypothesis redundant_sound :
  forall st0, checks_sound_for st0 redundant.

(** 2. Sequence shape: each sequence stays within the block. *)
Hypothesis seqs_wf :
  forall s, In s seqs -> sq_start s <= sq_end s /\ sq_end s <= length ops.

(** 3. Fast-path soundness: when a sequence's guard holds at [sq_start],
    none of its guarded checks can fail ([guard_value_persists] + Z3
    [covered], [guard-one-sided], [guard-two-sided]). *)
Hypothesis guard_sound :
  forall s st0 st_start,
  In s seqs ->
  reaches st0 (sq_start s) st_start ->
  sq_guard s st_start = true ->
  checks_sound_for st0 (sq_guarded s).

(** 4. Fallback completeness: when a sequence's guard fails at
    [sq_start], executing the original slice [[sq_start, sq_end)] does
    not complete normally (Z3 [guard-two-sided-complete] and the extreme
    offsets belonging to guarded checks in the slice; see
    [guard_complete_from_failing_check] below). *)
Hypothesis guard_complete :
  forall s st0 st_start st_end,
  In s seqs ->
  reaches st0 (sq_start s) st_start ->
  sq_guard s st_start = false ->
  eval_range ops (sq_start s) (sq_end s - sq_start s) st_start <> Ok st_end.

(** Helper showing how [guard_complete] follows from a failing check
    inside [[start, finish)]. *)
Lemma guard_complete_from_failing_check :
  forall start finish st_start j t cond,
  start <= j -> j < finish ->
  nth_error ops j = Some (Check t cond) ->
  (forall st_j, eval_range ops start (j - start) st_start = Ok st_j ->
                cond st_j = false) ->
  forall st_end, eval_range ops start (finish - start) st_start <> Ok st_end.
Proof.
  intros start finish st_start j t cond Hlo Hhi Hj Hfail st_end Hok.
  replace (finish - start) with ((j - start) + S (finish - S j)) in Hok by lia.
  rewrite eval_range_app in Hok.
  destruct (eval_range ops start (j - start) st_start) as [st_j | | ] eqn:Ep;
    try discriminate.
  replace (start + (j - start)) with j in Hok by lia.
  simpl in Hok. rewrite Hj in Hok.
  rewrite (Hfail st_j eq_refl) in Hok. discriminate.
Qed.

Lemma checks_sound_union :
  forall st0 S1 S2,
  checks_sound_for st0 S1 -> checks_sound_for st0 S2 ->
  checks_sound_for st0 (union_set S1 S2).
Proof.
  intros st0 S1 S2 H1 H2 j st t cond Hu Hr Hj.
  unfold union_set in Hu. apply orb_prop in Hu.
  destruct Hu as [Hs | Hs]; [eapply H1 | eapply H2]; eauto.
Qed.

Lemma reaches_step :
  forall st0 a st f,
  reaches st0 a st -> nth_error ops a = Some (Step f) ->
  reaches st0 (S a) (f st).
Proof.
  intros st0 a st f Hr Ha. unfold reaches in *.
  replace (S a) with (a + 1) by lia.
  rewrite eval_range_app, Hr. simpl. rewrite Ha. reflexivity.
Qed.

Lemma reaches_check :
  forall st0 a st t cond,
  reaches st0 a st -> nth_error ops a = Some (Check t cond) ->
  cond st = true ->
  reaches st0 (S a) st.
Proof.
  intros st0 a st t cond Hr Ha Hc. unfold reaches in *.
  replace (S a) with (a + 1) by lia.
  rewrite eval_range_app, Hr. simpl. rewrite Ha, Hc. reflexivity.
Qed.

(** Skipping sound checks preserves exact execution on any slice. *)
Lemma eval_filtered_sound :
  forall st0 skip a len st,
  checks_sound_for st0 skip ->
  reaches st0 a st ->
  eval_filtered skip ops a len st = eval_range ops a len st.
Proof.
  intros st0 skip a len. revert a.
  induction len as [| k IH]; intros a st Hskip Hr; simpl; [reflexivity |].
  destruct (nth_error ops a) as [[f | t | t cond] |] eqn:Ea; try reflexivity.
  - apply IH; [exact Hskip | eapply reaches_step; eauto].
  - destruct (skip a) eqn:Es.
    + assert (Hc : cond st = true) by (eapply Hskip; eauto).
      rewrite Hc. apply IH; [exact Hskip | eapply reaches_check; eauto].
    + destruct (cond st) eqn:Hc; [| reflexivity].
      apply IH; [exact Hskip | eapply reaches_check; eauto].
Qed.

(** Same in verifier mode: verified skipped checks never abort. *)
Lemma eval_filtered_verified_sound :
  forall st0 skip a len st,
  checks_sound_for st0 skip ->
  reaches st0 a st ->
  eval_filtered_verified skip ops a len st = eval_range ops a len st.
Proof.
  intros st0 skip a len. revert a.
  induction len as [| k IH]; intros a st Hskip Hr; simpl; [reflexivity |].
  unfold eval_step_verified.
  destruct (nth_error ops a) as [[f | t | t cond] |] eqn:Ea; try reflexivity.
  - apply IH; [exact Hskip | eapply reaches_step; eauto].
  - destruct (skip a) eqn:Es.
    + assert (Hc : cond st = true) by (eapply Hskip; eauto).
      rewrite Hc. apply IH; [exact Hskip | eapply reaches_check; eauto].
    + destruct (cond st) eqn:Hc; [| reflexivity].
      apply IH; [exact Hskip | eapply reaches_check; eauto].
Qed.

(** When a sequence's guard fails, its fallback code returns the exact
    same trap as the rest of the original block, and never reaches
    [Unreachable]. *)
Lemma eval_fallback_sound :
  forall s st0 guarded a len st,
  In s seqs ->
  sq_start s = a ->
  a + len = length ops ->
  checks_sound_for st0 guarded ->
  reaches st0 a st ->
  sq_guard s st = false ->
  eval_fallback (union_set redundant guarded) ops (sq_start s) (sq_end s) st =
  eval_range ops a len st.
Proof.
  intros s st0 guarded a len st Hin Hstart Hlen Hg Hr Hguard.
  destruct (seqs_wf s Hin) as [Hle1 Hle2].
  unfold eval_fallback. rewrite Hstart.
  rewrite (eval_filtered_sound st0 (union_set redundant guarded) a
             (sq_end s - a) st).
  - replace len with ((sq_end s - a) + (length ops - sq_end s)) by lia.
    rewrite eval_range_app.
    destruct (eval_range ops a (sq_end s - a) st) as [st' | t st' | ] eqn:E.
    + exfalso. eapply (guard_complete s st0 st st' Hin); eauto.
      * rewrite Hstart. exact Hr.
      * rewrite Hstart. exact E.
    + reflexivity.
    + exfalso. eapply eval_range_not_stuck. exact E.
  - apply checks_sound_union; [apply redundant_sound | exact Hg].
  - exact Hr.
Qed.

Lemma eval_fallback_verified_sound :
  forall s st0 guarded a len st,
  In s seqs ->
  sq_start s = a ->
  a + len = length ops ->
  checks_sound_for st0 guarded ->
  reaches st0 a st ->
  sq_guard s st = false ->
  eval_fallback_verified (union_set redundant guarded) ops
    (sq_start s) (sq_end s) st =
  eval_range ops a len st.
Proof.
  intros s st0 guarded a len st Hin Hstart Hlen Hg Hr Hguard.
  destruct (seqs_wf s Hin) as [Hle1 Hle2].
  unfold eval_fallback_verified. rewrite Hstart.
  rewrite (eval_filtered_verified_sound st0 (union_set redundant guarded) a
             (sq_end s - a) st).
  - replace len with ((sq_end s - a) + (length ops - sq_end s)) by lia.
    rewrite eval_range_app.
    destruct (eval_range ops a (sq_end s - a) st) as [st' | t st' | ] eqn:E.
    + exfalso. eapply (guard_complete s st0 st st' Hin); eauto.
      * rewrite Hstart. exact Hr.
      * rewrite Hstart. exact E.
    + reflexivity.
    + exfalso. eapply eval_range_not_stuck. exact E.
  - apply checks_sound_union; [apply redundant_sound | exact Hg].
  - exact Hr.
Qed.

Lemma find_seq_spec :
  forall a s, find_seq seqs a = Some s -> In s seqs /\ sq_start s = a.
Proof.
  intros a s Hf. unfold find_seq in Hf.
  apply find_some in Hf. destruct Hf as [Hin Heq].
  apply Nat.eqb_eq in Heq. auto.
Qed.

Lemma eval_main_sound :
  forall st0 guarded a len st,
  a + len = length ops ->
  checks_sound_for st0 guarded ->
  reaches st0 a st ->
  eval_main ops redundant seqs guarded a len st = eval_range ops a len st.
Proof.
  intros st0 guarded a len. revert guarded a.
  induction len as [| k IH]; intros guarded a st Hlen Hg Hr; simpl;
    [reflexivity |].
  assert (Hstep : forall g',
    checks_sound_for st0 g' ->
    eval_step (union_set redundant g') ops a st
      (eval_main ops redundant seqs g' (S a) k) =
    match nth_error ops a with
    | None => Ok st
    | Some (Step f) => eval_range ops (S a) k (f st)
    | Some (Fatal t) => Trapped t st
    | Some (Check t cond) =>
        if cond st then eval_range ops (S a) k st else Trapped t st
    end).
  { intros g' Hg'. unfold eval_step.
    destruct (nth_error ops a) as [[f | t | t cond] |] eqn:Ea; try reflexivity.
    - apply IH; [lia | exact Hg' | eapply reaches_step; eauto].
    - destruct (union_set redundant g' a) eqn:Eu.
      + assert (Hc : cond st = true).
        { eapply (checks_sound_union st0 redundant g'); eauto. }
        rewrite Hc. apply IH; [lia | exact Hg' | eapply reaches_check; eauto].
      + destruct (cond st) eqn:Hc; [| reflexivity].
        apply IH; [lia | exact Hg' | eapply reaches_check; eauto]. }
  destruct (find_seq seqs a) as [s |] eqn:Ef.
  - destruct (find_seq_spec a s Ef) as [Hin Hstart].
    destruct (sq_guard s st) eqn:Eguard.
    + apply Hstep. apply checks_sound_union; [exact Hg |].
      eapply guard_sound; [exact Hin | rewrite Hstart; exact Hr | exact Eguard].
    + eapply (eval_fallback_sound s st0 guarded a (S k) st); eauto.
  - apply Hstep. exact Hg.
Qed.

Lemma eval_main_verified_sound :
  forall st0 guarded a len st,
  a + len = length ops ->
  checks_sound_for st0 guarded ->
  reaches st0 a st ->
  eval_main_verified ops redundant seqs guarded a len st =
  eval_range ops a len st.
Proof.
  intros st0 guarded a len. revert guarded a.
  induction len as [| k IH]; intros guarded a st Hlen Hg Hr; simpl;
    [reflexivity |].
  assert (Hstep : forall g',
    checks_sound_for st0 g' ->
    eval_step_verified (union_set redundant g') ops a st
      (eval_main_verified ops redundant seqs g' (S a) k) =
    match nth_error ops a with
    | None => Ok st
    | Some (Step f) => eval_range ops (S a) k (f st)
    | Some (Fatal t) => Trapped t st
    | Some (Check t cond) =>
        if cond st then eval_range ops (S a) k st else Trapped t st
    end).
  { intros g' Hg'. unfold eval_step_verified.
    destruct (nth_error ops a) as [[f | t | t cond] |] eqn:Ea; try reflexivity.
    - apply IH; [lia | exact Hg' | eapply reaches_step; eauto].
    - destruct (union_set redundant g' a) eqn:Eu.
      + assert (Hc : cond st = true).
        { eapply (checks_sound_union st0 redundant g'); eauto. }
        rewrite Hc. apply IH; [lia | exact Hg' | eapply reaches_check; eauto].
      + destruct (cond st) eqn:Hc; [| reflexivity].
        apply IH; [lia | exact Hg' | eapply reaches_check; eauto]. }
  destruct (find_seq seqs a) as [s |] eqn:Ef.
  - destruct (find_seq_spec a s Ef) as [Hin Hstart].
    destruct (sq_guard s st) eqn:Eguard.
    + apply Hstep. apply checks_sound_union; [exact Hg |].
      eapply guard_sound; [exact Hin | rewrite Hstart; exact Hr | exact Eguard].
    + eapply (eval_fallback_verified_sound s st0 guarded a (S k) st); eauto.
  - apply Hstep. exact Hg.
Qed.

(** ** Main theorems *)

(** Exact trace/outcome preservation for fallback sequence emission,
    including overlapping and interleaved sequences. *)
Theorem fallback_emission_sound :
  forall st0, eval_transformed ops redundant seqs st0 = eval_orig ops st0.
Proof.
  intro st0. unfold eval_transformed, eval_orig.
  apply eval_main_sound with (st0 := st0); try reflexivity.
  intros j st t cond H. discriminate H.
Qed.

(** [Unreachable] at the end of fallback code is never reached. *)
Corollary fallback_never_unreachable :
  forall st0, eval_transformed ops redundant seqs st0 <> Stuck.
Proof.
  intro st0. rewrite fallback_emission_sound. apply eval_range_not_stuck.
Qed.

(** Under [--turboshaft-verify-wasm-bounds-check-elimination], no
    verifier assertion or fallback [Unreachable] ever triggers, and
    observable behavior is preserved. *)
Theorem fallback_verifier_sound :
  forall st0,
  eval_transformed_verified ops redundant seqs st0 = eval_orig ops st0 /\
  eval_transformed_verified ops redundant seqs st0 <> Stuck.
Proof.
  intro st0.
  assert (Heq : eval_transformed_verified ops redundant seqs st0 =
                eval_orig ops st0).
  { unfold eval_transformed_verified, eval_orig.
    apply eval_main_verified_sound with (st0 := st0); try reflexivity.
    intros j st t cond H. discriminate H. }
  split; [exact Heq | rewrite Heq; apply eval_range_not_stuck].
Qed.

End Soundness.

End Fallback.
