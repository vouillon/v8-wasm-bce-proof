(** * Milestone 2, instantiated: induction on a loop phi

    A loop phi [i = phi(i0, inext)] at the header [h] takes the value of
    [i0] when arriving from the forward edge, and of [inext] when
    arriving from the back edge.  A fact about [i] (and possibly about
    other values, not defined at the header) recorded at the header is
    justified when the facts known at each predecessor imply it for the
    value of the corresponding input, given by its canonical term.

    This is the argument of the comments of [ProcessLoopHeader] and
    [ProcessDecreasingInduction]: "When the back edge is taken, the
    conditions collected below held when they were tested [...]. The
    value of {i} they tested is the current one, since the header,
    where {i} is defined, is not executed again before the back edge.
    This value satisfied the facts (induction hypothesis), and the
    lemmas show that {i + c}, the value of {i} at the next iteration,
    does too."  The remaining obligations ([fwd_obligation] and
    [back_obligation]) are about values only: they are the arithmetic
    lemmas checked with Z3 ([induction-constant], [induction-length],
    [induction-not-equal], [induction-decreasing]...), applied to the
    values of canonical terms. *)

From Coq Require Import List Arith Lia.
Import ListNotations.
From BCE Require Import Graph Persistence Loops Canonical.

Section Induction.

Variable point : Type.
Variable succ : point -> point -> Prop.
Variable entry : point.

Local Notation dom := (dom succ entry).

Variable var : Type.
Variable val : Type.
Variable def : var -> point.

Local Notation exec := (exec succ entry val def).

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

(** The loop. *)
Variables h f b : point.
Hypothesis succ_f : succ f h.
Hypothesis succ_b : succ b h.
Hypothesis preds_h : forall x, succ x h -> x = f \/ x = b.
Hypothesis dom_h_b : dom h b.
Hypothesis h_not_entry : h <> entry.

(** The loop phi and its inputs, which are available at the end of the
    corresponding predecessors (SSA). *)
Variables i i0 inext : var.
Hypothesis def_i : def i = h.
Hypothesis dom_i0 : dom (def i0) f.
Hypothesis dom_inext : dom (def inext) b.

Definition phi_sem (e : exec) : Prop :=
  forall k, 0 < k -> k <= len e -> pts e k = h ->
  (pts e (k - 1) = f -> env e k i = env e (k - 1) i0) /\
  (pts e (k - 1) = b -> env e k i = env e (k - 1) inext).

(** The fact recorded at the header, and the canonical terms of the
    inputs of the phi. *)
Variable F : tfact.
Variables t0 tn : term.
Hypothesis canon_i0 : canon i0 t0.
Hypothesis canon_inext : canon inext tn.

(** The only leaf of [F] defined at the header is [i] (other phis of the
    header are not involved). *)
Hypothesis leaves_F : forall v, In v (tfleaves F) -> def v = h -> v = i.

(** The obligations, about values only: [en] is the environment when
    leaving the predecessor, in which the facts known there hold, and
    [en'] the environment on arrival at the header, which only differs
    from [en] on [i] (as far as [F] is concerned), whose new value is
    the value of the input. *)
Definition arrival_obligation (pred : point) (t : term) : Prop :=
  forall (en en' : var -> val),
  (forall F', A pred F' -> tholds F' en) ->
  (forall v, In v (tfleaves F) -> v <> i -> en' v = en v) ->
  en' i = eval en t ->
  tholds F en'.

Definition fwd_obligation : Prop := arrival_obligation f t0.
Definition back_obligation : Prop := arrival_obligation b tn.

Lemma arrival_ok :
  forall e pred x t, pure_sem e -> canon x t -> dom (def x) pred ->
  (forall k, 0 < k -> k <= len e -> pts e k = h -> pts e (k - 1) = pred ->
   env e k i = env e (k - 1) x) ->
  arrival_obligation pred t ->
  edge_ok succ entry def tholds R h e pred F.
Proof.
  intros e pred x t He Hc Hdx Hphi Hob k Hk Hlen Hpt Hpred Hknown.
  apply Hob with (en := env e (k - 1)); auto.
  - intros v Hv Hne. destruct k as [| k]; [lia |].
    replace (S k - 1) with k by lia.
    apply ex_frame; [exact Hlen |]. rewrite Hpt.
    intro Hdef. apply Hne, leaves_F; auto.
  - rewrite Hphi by auto. apply canon_sound with (op := op) (comm := comm) (ident := ident); auto.
    + lia.
    + rewrite Hpred. exact Hdx.
Qed.

Theorem phi_fact_justified :
  forall e, pure_sem e -> phi_sem e ->
  fwd_obligation -> back_obligation -> justified_at e h F.
Proof.
  intros e He Hphi Hf Hb.
  apply loop_justified with (f := f) (b := b); auto.
  - apply arrival_ok with (x := i0) (t := t0); auto.
    intros k Hk Hlen Hpt Hpred. apply (Hphi k); auto.
  - apply arrival_ok with (x := inext) (t := tn); auto.
    intros k Hk Hlen Hpt Hpred. apply (Hphi k); auto.
Qed.

(** In the back obligation, the facts known at the back edge include
    [F] itself (the induction hypothesis). *)
Lemma back_obligation_uses_F :
  forall en, (forall F', A b F' -> tholds F' en) -> R h F -> tholds F en.
Proof. intros en H HR. apply H. exists h. auto. Qed.

End Induction.
