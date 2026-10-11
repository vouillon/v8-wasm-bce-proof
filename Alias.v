(** * Milestone 4: length aliases

    [TryResolveMergeBound]: with a loop bound [x = phi(...) + offset],
    where the phi is a merge (not a loop phi) and [x] is at least some
    lower bound when entering the loop, the constant inputs of the phi
    that the lower bound rules out are excluded; if a single input
    remains, an array length [l] plus a constant, then [x] is [l - r] in
    the loop, which is recorded at the loop header as a length alias.

    The array length [l] does not dominate the loop: it is computed
    before the edge of its input to the merge.  The alias fact is still
    sound: its leaves are not dominated by the header (they are not even
    dominated by the merge, since the merge is not a loop header and so
    does not dominate its predecessors), and it holds on arrival at the
    header from the forward edge, because the last execution of the merge
    took the edge of the remaining input, and the leaves of [l] were not
    computed again since.

    The fact is modeled as [phi = y] for the remaining input [y] of the
    phi, with [y]'s canonical term (an array length plus a constant): the
    alias [x = l - r] follows by arithmetic, as [x = phi + offset], which
    is left abstract ([alias_arith]). *)

From Coq Require Import List Arith Lia Classical.
Import ListNotations.
From BCE Require Import Graph Persistence Loops Canonical.
From BCE Require Induction.

Section Alias.

Variable point : Type.
Variable succ : point -> point -> Prop.
Variable entry : point.

Local Notation dom := (dom succ entry).
Local Notation reachable := (reachable succ entry).

Variable var : Type.
Variable val : Type.
Variable def : var -> point.

Local Notation exec := (exec succ entry val def).
Local Notation leaf_ok := (leaf_ok succ entry def).

Variable fn : Type.
Variable eval_fn : fn -> list val -> val.
Variable op : var -> option (fn * list var).
Hypothesis op_ssa :
  forall x f args y, op x = Some (f, args) -> In y args -> dom (def y) (def x).
Variable comm : fn -> Prop.
Hypothesis comm_ok :
  forall f a b, comm f -> eval_fn f [a; b] = eval_fn f [b; a].
Variable ident : fn -> Prop.
Hypothesis ident_ok : forall f a, ident f -> eval_fn f [a] = a.

Local Notation term := (term var fn).
Local Notation tfact := (tfact var val fn).
Local Notation eval := (eval eval_fn).
Local Notation tholds := (tholds eval_fn).
Local Notation canon := (canon op comm ident).
Local Notation pure_sem := (pure_sem succ entry def eval_fn op).

Variable R : point -> tfact -> Prop.
Local Notation A := (A succ entry R).
Local Notation justified_at := (justified_at succ entry def tholds R).
Local Notation edge_ok := (edge_ok succ entry def tholds R).

(** The loop. *)
Variables h f b : point.
Hypothesis succ_f : succ f h.
Hypothesis succ_b : succ b h.
Hypothesis preds_h : forall x, succ x h -> x = f \/ x = b.
Hypothesis dom_h_b : dom h b.
Hypothesis h_not_entry : h <> entry.

(** The merge [m], with its phi [phi].  The merge dominates the forward
    predecessor ("it dominates {x}, which does": [FindNotEqualBound]
    only accepts a bound [x] computed before the loop, and [phi] is an
    input of [x]), and is not the loop header. *)
Variable m : point.
Variable phi : var.
Hypothesis def_phi : def phi = m.
Hypothesis dom_m_f : dom m f.
Hypothesis m_not_h : m <> h.

(** The remaining input [y] of the phi, for the edge from [pL].  It is
    available at the end of [pL] (SSA).  The merge is not a loop header,
    so it does not dominate its predecessor [pL]: in Turboshaft, an edge
    to a block that dominates its source is a back edge, whose target is
    a loop header. *)
Variable pL : point.
Variable y : var.
Hypothesis succ_pL : succ pL m.
Hypothesis m_not_dom_pL : ~ dom m pL.
Hypothesis dom_y : dom (def y) pL.
Variable ty : term.
Hypothesis canon_y : canon y ty.

(** Semantics of the phi, per incoming edge: from [pL], it takes the
    value of [y]; from the other predecessors, it takes the value of a
    constant input that is ruled out ([Excluded]: [k + offset] is below
    the lower bound of [x] at the entry of the loop). *)
Variable Excluded : val -> Prop.

Definition phi_sem (e : exec) : Prop :=
  forall k, 0 < k -> k <= len e -> pts e k = m ->
  (pts e (k - 1) = pL -> env e k phi = env e (k - 1) y) /\
  (pts e (k - 1) <> pL -> Excluded (env e k phi)).

(** The entry condition: the facts known at the forward predecessor (the
    conditions dominating it, see [EntryLowerBound]) show that [x] is at
    least its lower bound, which rules out the excluded inputs. *)
Hypothesis entry_cond :
  forall en, (forall F', A f F' -> tholds F' en) -> ~ Excluded (en phi).

(** The alias fact: its leaves are [phi] and the leaves of [ty], and it
    holds when [phi] is equal to [y]'s canonical term. *)
Variable Fa : tfact.
Hypothesis Fa_leaves : forall v, In v (tfleaves Fa) -> v = phi \/ In v (tleaves ty).
Hypothesis alias_arith : forall en, en phi = eval en ty -> tholds Fa en.

(** ** The leaves condition *)

Lemma dom_m_h : dom m h.
Proof. apply fwd_dom_header with (f := f) (b := b); auto. Qed.

(** The leaves of the array length are not dominated by the merge:
    otherwise, the merge would dominate [pL]. *)
Lemma leaves_y_not_dom_m : forall v, In v (tleaves ty) -> ~ dom m (def v).
Proof.
  intros v Hv Hd. apply m_not_dom_pL.
  apply dom_trans with (b := def v); auto.
  apply dom_trans with (b := def y); auto.
  apply canon_leaves_dom with (op := op) (comm := comm) (ident := ident) (t := ty); auto.
Qed.

Lemma leaves_y_not_m : forall v, In v (tleaves ty) -> def v <> m.
Proof.
  intros v Hv Hdef. apply (leaves_y_not_dom_m v Hv). rewrite Hdef. apply dom_refl.
Qed.

(** Any fact recorded at a point dominated by the merge (in particular,
    by the loop header), such as the facts about the array length derived
    from the alias, satisfies the leaves condition for these leaves. *)
Lemma leaves_y_ok : forall p v, dom m p -> In v (tleaves ty) -> leaf_ok p v.
Proof.
  intros p v Hd Hv. apply not_dom_leaf_ok with (p0 := m); auto.
  apply leaves_y_not_dom_m. exact Hv.
Qed.

Theorem alias_leaves_ok :
  reachable h -> forall v, In v (tfleaves Fa) -> leaf_ok h v.
Proof.
  intros Hr v Hv. destruct (Fa_leaves v Hv) as [-> | Hy].
  - apply dom_leaf_ok; auto. rewrite def_phi. apply dom_m_h.
  - apply leaves_y_ok; auto. apply dom_m_h.
Qed.

(** None of the leaves is defined at the header: the alias is a
    loop-invariant fact. *)
Lemma alias_leaves_not_h : forall v, In v (tfleaves Fa) -> def v <> h.
Proof.
  intros v Hv Hdef. destruct (Fa_leaves v Hv) as [-> | Hy].
  - rewrite def_phi in Hdef. contradiction.
  - apply (leaves_y_not_dom_m v Hy). rewrite Hdef. apply dom_m_h.
Qed.

(** ** Local justification *)

Section Exec.

Variable e : exec.
Hypothesis He : pure_sem e.
Hypothesis Hphi : phi_sem e.

(** The forward edge: the argument of the comment of
    [TryResolveMergeBound]. *)
Theorem alias_fwd : edge_ok h e f Fa.
Proof.
  intros k Hk Hlen Hpt Hpred Hknown.
  assert (Hk1 : k - 1 <= len e) by lia.
  (* The last execution [tm] of the merge before the forward edge. *)
  assert (Hdm : dom m (pts e (k - 1))) by (rewrite Hpred; exact dom_m_f).
  destruct (last_visit e m (k - 1) Hk1 Hdm) as (tm & Htm & Hptm & Hlast).
  assert (Hlast' : forall j, tm < j -> j <= k -> pts e j <> m).
  { intros j Hj1 Hj2. destruct (Nat.eq_dec j k) as [-> | Hne].
    - rewrite Hpt. apply not_eq_sym. exact m_not_h.
    - apply Hlast; lia. }
  assert (Hdmk : dom m (pts e k)) by (rewrite Hpt; exact dom_m_h).
  (* [phi] keeps its value from [tm] to [k], at the points dominated
     by [m]. *)
  assert (Hphi_k : forall j, tm <= j -> j <= k -> dom m (pts e j) ->
                   env e j phi = env e tm phi).
  { intros j Hj1 Hj2 Hdmj.
    apply persistence with (p := m); auto; [lia | |].
    - intros i Hi1 Hi2. apply Hlast'; lia.
    - intros [_ H]. apply H. exact def_phi. }
  (* The merge was reached from a predecessor. *)
  destruct tm as [| tm].
  { exfalso. apply m_not_dom_pL. rewrite <- Hptm, ex_entry. apply dom_entry. }
  destruct (Hphi (S tm)) as [HpL Hother]; [lia | lia | exact Hptm |].
  replace (S tm - 1) with tm in HpL, Hother by lia.
  destruct (classic (pts e tm = pL)) as [Hp | Hp].
  - (* The edge of [y] was taken. *)
    apply alias_arith.
    rewrite (Hphi_k k) by (auto; lia). rewrite HpL by exact Hp.
    assert (Hy : env e tm y = eval (env e tm) ty).
    { apply canon_sound with (op := op) (comm := comm) (ident := ident); auto.
      - lia.
      - rewrite Hp. exact dom_y. }
    rewrite Hy.
    apply eval_ext. intros v Hv.
    (* The leaves of [y] were not computed again since. *)
    rewrite persistence with (e := e) (p := m) (t := S tm) (k := k);
      [| exact Hlen | lia | exact Hptm | exact Hlast' | exact Hdmk |
         apply leaves_y_ok; [apply dom_refl | exact Hv]].
    symmetry. apply ex_frame; [lia |]. rewrite Hptm.
    apply not_eq_sym, leaves_y_not_m. exact Hv.
  - (* Another edge: ruled out by the entry condition. *)
    exfalso. apply (entry_cond (env e (k - 1)) Hknown).
    rewrite (Hphi_k (k - 1)) by (auto; lia). apply Hother. exact Hp.
Qed.

(** The back edge: the alias is loop-invariant. *)
Theorem alias_back : R h Fa -> edge_ok h e b Fa.
Proof.
  intros HR. apply invariant_back_ok with (leaves := tfleaves); auto.
  - apply tholds_ext.
  - apply alias_leaves_not_h.
Qed.

Theorem alias_justified : R h Fa -> justified_at e h Fa.
Proof.
  intros HR. apply loop_justified with (f := f) (b := b); auto.
  - apply alias_fwd.
  - apply alias_back. exact HR.
Qed.

(** A fact recorded at the header after the alias may rely on it at the
    same time, as [ProcessDecreasingInduction] does when the start [i0]
    of a decreasing loop phi is the aliased bound [x] (through
    [TryExtractArrayLength], once [RecordLoopBound] recorded the alias
    for an increasing phi of the same header). *)
Corollary justified_using_alias :
  R h Fa -> forall G,
  (forall k, k <= len e -> pts e k = h ->
   hyps_before succ entry def tholds R e k ->
   tholds Fa (env e k) -> tholds G (env e k)) ->
  justified_at e h G.
Proof.
  intros HR G HG. apply justified_at_seq with (F1 := Fa); auto.
  apply alias_justified. exact HR.
Qed.

(** The same, for a fact about a loop phi of the header, shown by
    induction on the iterations (Induction.v), whose obligations use the
    alias on arrival: [RecordLoopBound] for the bound [i + [0, r - 1] < l]
    of an increasing phi, and [ProcessDecreasingInduction] for a
    decreasing phi whose start is the aliased bound. *)
Corollary phi_fact_justified_using_alias :
  R h Fa ->
  forall i i0 inext G t0 tn,
  dom (def i0) f -> dom (def inext) b ->
  canon i0 t0 -> canon inext tn ->
  (forall v, In v (tfleaves G) -> def v = h -> v = i) ->
  Induction.phi_sem point succ entry var val def h f b i i0 inext e ->
  Induction.arrival_obligation_with point succ entry var val fn eval_fn R i G
    (fun F' => F' = Fa) f t0 ->
  Induction.arrival_obligation_with point succ entry var val fn eval_fn R i G
    (fun F' => F' = Fa) b tn ->
  justified_at e h G.
Proof.
  intros HR i i0 inext G t0 tn Hi0 Hinext Hc0 Hcn HG Hphi' Hf Hb.
  apply (Induction.phi_fact_justified_with point succ entry var val def fn
           eval_fn op op_ssa comm comm_ok ident ident_ok R h f b preds_h
           h_not_entry i i0 inext Hi0 Hinext G t0 tn Hc0 Hcn HG e
           (fun F' => F' = Fa)); auto.
  intros F' ->. apply alias_justified. exact HR.
Qed.

(** End to end: if the other recorded facts satisfy the leaves condition
    and are locally justified, the alias holds at every point dominated by
    the loop header (inside the loop, and after it). *)
Theorem alias_sound :
  R h Fa ->
  (forall p F v, reachable p -> R p F -> ~ (p = h /\ F = Fa) ->
   In v (tfleaves F) -> leaf_ok p v) ->
  (forall p F, R p F -> ~ (p = h /\ F = Fa) -> justified_at e p F) ->
  forall k, k <= len e -> dom h (pts e k) -> tholds Fa (env e k).
Proof.
  intros HR Hok Hjust k Hk Hd.
  apply (soundness (tholds_ext _ _ _ eval_fn) (R := R) (e := e)); auto.
  - intros p F v Hr HRp Hv. destruct (classic (p = h /\ F = Fa)) as [[-> ->] | Hn].
    + apply alias_leaves_ok; auto.
    + apply Hok with (F := F); auto.
  - intros p F HRp. destruct (classic (p = h /\ F = Fa)) as [[-> ->] | Hn].
    + apply alias_justified. exact HR.
    + apply Hjust; auto.
  - exists h. split; auto.
Qed.

End Exec.

End Alias.
