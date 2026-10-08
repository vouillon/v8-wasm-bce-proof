(** * Milestone 2: facts recorded at loop headers

    Facts recorded at a loop header (by [ProcessLoopHeader] and
    [ProcessDecreasingInduction]) are justified by induction on the
    iterations: they hold on arrival from the forward predecessor, and
    on arrival from the back edge, assuming that they held at the
    previous iteration.  This file shows that such facts fit the local
    justification of Persistence.v: the induction hypothesis is provided
    by the facts known at the back edge, which include the facts recorded
    at the header, since the header dominates the back edge. *)

From Coq Require Import List Arith Lia Classical.
Import ListNotations.
From BCE Require Import Graph Persistence.

Section Loops.

Variable point : Type.
Variable succ : point -> point -> Prop.
Variable entry : point.

Local Notation path := (path succ).
Local Notation dom := (dom succ entry).
Local Notation reachable := (reachable succ entry).

Variable var : Type.
Variable val : Type.
Variable def : var -> point.

Local Notation exec := (exec succ entry val def).

Variable fact : Type.
Variable holds : fact -> (var -> val) -> Prop.
Variable leaves : fact -> list var.
Hypothesis holds_ext :
  forall F (e1 e2 : var -> val),
  (forall v, In v (leaves F) -> e1 v = e2 v) -> holds F e1 -> holds F e2.

Variable R : point -> fact -> Prop.

Local Notation A := (A succ entry R).
Local Notation hyps_before := (hyps_before succ entry def holds R).
Local Notation justified_at := (justified_at succ entry def holds R).

(** A loop header [h] with two predecessors: the forward edge from [f]
    and the back edge from [b], which [h] dominates
    ([ProcessLoopHeader] gives up on loop headers with more
    predecessors).  The header is not the entry point (it has
    predecessors). *)
Variables h f b : point.
Hypothesis succ_f : succ f h.
Hypothesis succ_b : succ b h.
Hypothesis preds_h : forall x, succ x h -> x = f \/ x = b.
Hypothesis dom_h_b : dom h b.
Hypothesis h_not_entry : h <> entry.

(** Any path to the header first enters it from the forward edge. *)
Lemma fwd_dom_header : forall d, dom d f -> dom d h.
Proof.
  intros d Hd l Hl.
  destruct (path_prefix _ _ _ _ _ Hl h (dom_refl _ _ _ h l Hl))
    as (l1 & l2 & -> & Hnin & Hp).
  apply in_or_app. left.
  destruct (path_last_step _ _ _ _ _ Hp (fun H => h_not_entry (eq_sym H)))
    as (x & l' & Heq & Hpx & Hsx).
  apply app_inj_tail in Heq. destruct Heq as [<- _].
  destruct (preds_h x Hsx) as [-> | ->].
  - apply Hd. exact Hpx.
  - exfalso. apply Hnin. apply dom_h_b. exact Hpx.
Qed.

(** What is known at the header is what is known at the end of the
    forward predecessor, plus what is recorded at the header itself
    (the comment of [BeginBlock]: the back edge is ignored). *)
Lemma known_at_header :
  forall F, A h F <-> A f F \/ R h F.
Proof.
  intros F. split.
  - intros (p & Hd & HR).
    destruct (classic (p = h)) as [-> | Hne]; [right; exact HR | left].
    exists p. split; [| exact HR].
    apply dom_pred with (q := h); auto.
  - intros [(p & Hd & HR) | HR].
    + exists p. split; [apply fwd_dom_header |]; auto.
    + exists h. split; [apply dom_refl | exact HR].
Qed.

(** The facts recorded at the header are known at the back edge. *)
Lemma header_known_at_back : forall F, R h F -> A b F.
Proof. intros F HR. exists h. auto. Qed.

(** The obligation for an edge from [pred] to the header: on arrival
    from [pred] at time [k], [F] holds, provided that the facts known at
    [pred] held when leaving it (at time [k - 1]).  For the back edge,
    these include [F] itself (induction hypothesis). *)
Definition edge_ok (e : exec) (pred : point) (F : fact) : Prop :=
  forall k, 0 < k -> k <= len e -> pts e k = h -> pts e (k - 1) = pred ->
  (forall F', A pred F' -> holds F' (env e (k - 1))) ->
  holds F (env e k).

Theorem loop_justified :
  forall e F, edge_ok e f F -> edge_ok e b F -> justified_at e h F.
Proof.
  intros e F Hf Hb k Hk Hpt Hhyps.
  destruct k as [| k].
  - rewrite ex_entry in Hpt. symmetry in Hpt. contradiction.
  - assert (Hs : succ (pts e (S k - 1)) h).
    { rewrite <- Hpt. replace (S k - 1) with k by lia. apply ex_succ. exact Hk. }
    assert (Hknown : forall F', A (pts e (S k - 1)) F' ->
                                holds F' (env e (S k - 1))).
    { intros F' HA. apply Hhyps; [lia | exact HA]. }
    destruct (preds_h _ Hs) as [Hpred | Hpred]; rewrite Hpred in Hknown;
      [apply Hf | apply Hb]; auto; lia.
Qed.

(** Loop-invariant facts: a fact recorded at the header whose leaves are
    not defined at the header satisfies the back-edge obligation for
    free, as it held when the back edge was taken, and arriving at the
    header does not change its leaves. *)
Lemma invariant_back_ok :
  forall e F, R h F -> (forall v, In v (leaves F) -> def v <> h) ->
  edge_ok e b F.
Proof.
  intros e F HR Hdef k Hk Hlen Hpt Hpred Hknown.
  destruct k as [| k]; [lia |].
  replace (S k - 1) with k in Hpred, Hknown by lia.
  apply holds_ext with (e1 := env e k).
  - intros v Hv. symmetry. apply ex_frame; [exact Hlen |].
    rewrite Hpt. apply not_eq_sym, Hdef, Hv.
  - apply Hknown, header_known_at_back, HR.
Qed.

End Loops.

Arguments edge_ok {point} succ entry {var val} def {fact} holds R h e pred F.
