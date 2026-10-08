(** * Milestone 1: facts recorded at dominators persist

    This is the generic soundness argument of the analysis: a fact
    recorded at a point [p] (because it holds whenever [p] is reached)
    holds at every later point [q] dominated by [p], as long as the
    variables it is about are not defined at points strictly dominated by
    [p].  The analysis (snapshot tables merged at the common ancestor of
    the predecessors' snapshots, see [BeginBlock]) only uses at a point
    the facts recorded at its dominators, which is modeled by [A]. *)

From Coq Require Import List Arith Lia Classical.
Import ListNotations.
From BCE Require Import Graph.

(** A maximum: the last time before [k] at which some property held. *)
Lemma last_time :
  forall (P : nat -> Prop) k, (exists t, t <= k /\ P t) ->
  exists t, t <= k /\ P t /\ forall j, t < j -> j <= k -> ~ P j.
Proof.
  intros P k. induction k as [| k IH]; intros [t [Ht HP]].
  - exists 0. assert (t = 0) by lia. subst. split; [lia | split; auto].
    intros; lia.
  - destruct (classic (P (S k))) as [HS | HS].
    + exists (S k). repeat split; auto. intros; lia.
    + destruct (Nat.eq_dec t (S k)) as [-> | Hne]; [contradiction |].
      destruct (IH (ex_intro _ t (conj (ltac:(lia) : t <= k) HP)))
        as (t' & Ht' & HP' & Hlast).
      exists t'. repeat split; auto.
      intros j Hj1 Hj2. destruct (Nat.eq_dec j (S k)) as [-> | ]; auto.
      apply Hlast; lia.
Qed.

Section Persistence.

Variable point : Type.
Variable succ : point -> point -> Prop.
Variable entry : point.

Local Notation path := (path succ).
Local Notation dom := (dom succ entry).
Local Notation reachable := (reachable succ entry).

(** SSA variables, each defined at exactly one point, and their values. *)
Variable var : Type.
Variable val : Type.
Variable def : var -> point.

(** ** Executions

    A finite prefix of an execution: the points [pts 0], ..., [pts len]
    reached, and the values of the variables [env k] just after
    arriving at [pts k].  Arriving at a point only writes the variables
    defined there (for instance, the phis of a block are defined at its
    first point, and written when arriving there).  The values written
    are not constrained: this is an abstraction of any semantics. *)
Record exec := {
  pts : nat -> point;
  env : nat -> var -> val;
  len : nat;
  ex_entry : pts 0 = entry;
  ex_succ : forall k, k < len -> succ (pts k) (pts (S k));
  ex_frame : forall k v, k < len -> pts (S k) <> def v ->
             env (S k) v = env k v
}.

Section Exec.

Variable e : exec.

(** The points visited between times [j] and [j + n]. *)
Lemma exec_path :
  forall n j, j + n <= len e ->
  path (pts e j) (pts e (j + n)) (map (pts e) (seq j (S n))).
Proof.
  induction n as [| n IH]; intros j Hle.
  - rewrite Nat.add_0_r. apply path_refl.
  - rewrite seq_S, map_app.
    change (map (pts e) [j + S n]) with [pts e (j + S n)].
    replace (j + S n) with (S (j + n)) by lia.
    apply path_step with (y := pts e (j + n)).
    + apply IH. lia.
    + apply ex_succ. lia.
Qed.

Lemma in_exec_path :
  forall x j n, In x (map (pts e) (seq j (S n))) ->
  exists i, j <= i <= j + n /\ pts e i = x.
Proof.
  intros x j n H. apply in_map_iff in H. destruct H as (i & <- & Hi).
  apply in_seq in Hi. exists i. split; [lia | reflexivity].
Qed.

Lemma exec_reachable : forall k, k <= len e -> reachable (pts e k).
Proof.
  intros k Hk. exists (map (pts e) (seq 0 (S k))).
  rewrite <- (ex_entry e). apply (exec_path k 0). lia.
Qed.

(** A point dominating the current point was visited before. *)
Lemma dom_visited :
  forall p k, k <= len e -> dom p (pts e k) ->
  exists t, t <= k /\ pts e t = p.
Proof.
  intros p k Hk Hd.
  assert (Hp := exec_path k 0 ltac:(lia)). rewrite ex_entry in Hp.
  destruct (in_exec_path _ _ _ (Hd _ Hp)) as (t & Ht & Hpt).
  exists t. split; [lia | exact Hpt].
Qed.

(** ... and there is a last such visit. *)
Lemma last_visit :
  forall p k, k <= len e -> dom p (pts e k) ->
  exists t, t <= k /\ pts e t = p /\
            forall j, t < j -> j <= k -> pts e j <> p.
Proof.
  intros p k Hk Hd.
  apply (last_time (fun t => pts e t = p)). apply dom_visited; auto.
Qed.

(** A variable that is not defined at any point visited after time
    [t] keeps its value. *)
Lemma frame_interval :
  forall v t k, t <= k -> k <= len e ->
  (forall s, t < s -> s <= k -> pts e s <> def v) ->
  env e k v = env e t v.
Proof.
  intros v t k Htk. induction k as [| k IH]; intros Hk Hs.
  - f_equal. lia.
  - destruct (Nat.eq_dec t (S k)) as [-> | Hne]; [reflexivity |].
    rewrite ex_frame by (lia || apply Hs; lia).
    apply IH; [lia | lia | intros; apply Hs; lia].
Qed.

(** ** The leaves condition

    A variable [v] may be used by a fact recorded at [p] unless it is
    defined at a point strictly dominated by [p].  This holds for any
    variable defined at a dominator of [p] (see [dom_leaf_ok]), which is
    what SSA guarantees for the inputs of the operations that [p]
    depends on, but also for variables defined at points unrelated to
    [p], such as the array length of a length alias (see Alias.v). *)
Definition leaf_ok (p : point) (v : var) : Prop :=
  ~ (dom p (def v) /\ def v <> p).

Lemma dom_leaf_ok :
  forall p v, reachable p -> dom (def v) p -> leaf_ok p v.
Proof.
  intros p v Hr Hd [Hd' Hne]. apply Hne. symmetry.
  apply dom_antisym with (succ := succ) (entry := entry); auto.
Qed.

Lemma not_dom_leaf_ok :
  forall p0 p v, ~ dom p0 (def v) -> dom p0 p -> leaf_ok p v.
Proof.
  intros p0 p v Hn Hd [Hd' _]. apply Hn.
  apply dom_trans with (succ := succ) (entry := entry) (b := p); auto.
Qed.

(** ** The persistence lemma

    Let [t] be the last visit of [p] up to time [k], where [p] dominates
    [pts k].  A variable satisfying the leaves condition at [p] is not
    written between [t] and [k]: a write at time [s] is a visit of
    [def v], which [p] does not dominate, so there is a path to [def v]
    avoiding [p]; followed by the execution from [s] to [k], which does
    not visit [p] either, it gives a path to [pts k] avoiding [p]. *)
Lemma persistence :
  forall p t k v,
  k <= len e -> t <= k -> pts e t = p ->
  (forall j, t < j -> j <= k -> pts e j <> p) ->
  dom p (pts e k) -> leaf_ok p v ->
  env e k v = env e t v.
Proof.
  intros p t k v Hk Htk Hpt Hlast Hdom Hok.
  apply frame_interval; auto.
  intros s Hs1 Hs2 Hdef.
  assert (Hne : def v <> p) by (rewrite <- Hdef; apply Hlast; lia).
  assert (Hnd : ~ dom p (def v)) by (intro H; apply Hok; auto).
  destruct (not_dom_path _ _ _ _ _ Hnd) as (l1 & Hl1 & Hnin).
  assert (Hseg := exec_path (k - s) s ltac:(lia)).
  replace (s + (k - s)) with k in Hseg by lia.
  rewrite <- Hdef in Hl1.
  assert (Hpk := path_app _ _ _ _ _ Hseg entry l1
                   (map (pts e) (seq (S s) (k - s))) eq_refl Hl1).
  specialize (Hdom _ Hpk). apply in_app_or in Hdom.
  destruct Hdom as [H | H]; [contradiction |].
  apply in_map_iff in H. destruct H as (j & Hj & Hjs). apply in_seq in Hjs.
  apply (Hlast j); [lia | lia | exact Hj].
Qed.

End Exec.

(** ** Facts *)

Variable fact : Type.
Variable holds : fact -> (var -> val) -> Prop.
Variable leaves : fact -> list var.

(** Whether a fact holds only depends on the values of its leaves. *)
Hypothesis holds_ext :
  forall F (e1 e2 : var -> val),
  (forall v, In v (leaves F) -> e1 v = e2 v) -> holds F e1 -> holds F e2.

(** The facts recorded at each point: facts that hold whenever the point
    is reached (on arrival). *)
Variable R : point -> fact -> Prop.

(** The facts known at [q]: those recorded at its dominators. *)
Definition A (q : point) (F : fact) : Prop := exists p, dom p q /\ R p F.

(** The leaves condition, for all the recorded facts. *)
Definition leaves_ok : Prop :=
  forall p F v, reachable p -> R p F -> In v (leaves F) -> leaf_ok p v.

(** The known facts held at all the times before [k]. *)
Definition hyps_before (e : exec) (k : nat) : Prop :=
  forall k' F, k' < k -> A (pts e k') F -> holds F (env e k').

(** Local justification of a fact [F] recorded at [p]: whenever [p] is
    reached, [F] holds, provided that the known facts held until then.
    This is the obligation of each rule of the analysis. *)
Definition justified_at (e : exec) (p : point) (F : fact) : Prop :=
  forall k, k <= len e -> pts e k = p -> hyps_before e k ->
  holds F (env e k).

Definition justified (e : exec) : Prop :=
  forall p F, R p F -> justified_at e p F.

(** ** The persistence theorem *)
Theorem soundness :
  forall e, leaves_ok -> justified e ->
  forall k F, k <= len e -> A (pts e k) F -> holds F (env e k).
Proof.
  intros e Hok Hjust k.
  induction k as [k IH] using lt_wf_ind.
  intros F Hk [p [Hdom HR]].
  destruct (last_visit e p k Hk Hdom) as (t & Htk & Hpt & Hlast).
  assert (Ht : holds F (env e t)).
  { apply (Hjust p F HR t); [lia | exact Hpt |].
    intros k' F' Hk' HA. apply IH; [lia | lia | exact HA]. }
  apply holds_ext with (e1 := env e t); auto.
  intros v Hv. symmetry. apply persistence with (p := p); auto.
  apply Hok with (F := F); auto.
  rewrite <- Hpt. apply exec_reachable. lia.
Qed.

(** ** Consequences for local justifications *)

(** When justifying a fact at time [k], the facts recorded at the strict
    dominators of [pts k] can be used, evaluated at time [k]: they held
    on arrival at the predecessor, and their leaves are not defined at
    [pts k].  This covers the facts recorded earlier in the same block,
    such as those of previous traps. *)
Lemma known_at_arrival :
  forall e k p F, leaves_ok -> k <= len e -> hyps_before e k ->
  dom p (pts e k) -> p <> pts e k -> R p F -> holds F (env e k).
Proof.
  intros e k p F Hok Hk Hb Hdom Hne HR.
  destruct k as [| k].
  - rewrite ex_entry in Hdom, Hne. apply dom_entry_inv in Hdom. contradiction.
  - assert (HreachP : reachable p).
    { apply reachable_dom with (q := pts e (S k)); auto.
      apply exec_reachable. lia. }
    assert (Hp : holds F (env e k)).
    { apply Hb; [lia |]. exists p. split; auto.
      apply dom_pred with (q := pts e (S k)); auto. apply ex_succ. lia. }
    apply holds_ext with (e1 := env e k); auto.
    intros v Hv. symmetry. apply ex_frame; [lia |].
    intro Hdef. apply (Hok p F v HreachP HR Hv).
    rewrite <- Hdef. split; [exact Hdom | congruence].
Qed.

(** Facts recorded at the same point can be justified in sequence: a
    fact may rely on the facts recorded before it at the same point,
    evaluated at the same time, as long as those are justified from the
    previous times only.  (For instance, at a loop header, a length alias
    recorded for an increasing loop phi is then used for a decreasing
    one, see Alias.v.) *)
Lemma justified_at_seq :
  forall e p F1 F2,
  justified_at e p F1 ->
  (forall k, k <= len e -> pts e k = p -> hyps_before e k ->
   holds F1 (env e k) -> holds F2 (env e k)) ->
  justified_at e p F2.
Proof. intros e p F1 F2 H1 H2 k Hk Hp Hb. auto. Qed.

End Persistence.


Arguments exec {point} succ entry {var} val def.
Arguments pts {point succ entry var val def} e _.
Arguments env {point succ entry var val def} e _ _.
Arguments len {point succ entry var val def} e.
Arguments leaf_ok {point} succ entry {var} def p v.
Arguments A {point} succ entry {fact} R q F.
Arguments leaves_ok {point} succ entry {var} def {fact} leaves R.
Arguments hyps_before {point} succ entry {var val} def {fact} holds R e k.
Arguments justified_at {point} succ entry {var val} def {fact} holds R e p F.
Arguments justified {point} succ entry {var val} def {fact} holds R e.

(** Recording more facts only makes more facts known.  The proof of a
    rule may need an invariant stronger than the facts that the analysis
    records (for instance [0 <= i <= x] for a loop phi [i], of which only
    [0 <= i] is recorded): such "ghost" facts are added to [R], and the
    theorem then covers the facts actually recorded. *)
Lemma A_mono :
  forall point succ entry fact (R R' : point -> fact -> Prop) q F,
  (forall p F, R p F -> R' p F) -> A succ entry R q F -> A succ entry R' q F.
Proof. intros until F. intros HR (p & Hd & H). exists p. auto. Qed.

Arguments last_visit {point succ entry var val def} e p k _ _.
Arguments persistence {point succ entry var val def} e p t k v _ _ _ _ _ _.
Arguments exec_reachable {point succ entry var val def} e k _.
Arguments soundness {point succ entry var val def fact holds leaves}
  holds_ext {R e} _ _ k F _ _.
