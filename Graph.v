(** * Control-flow graphs, paths and dominance

    Program points form a graph given by a successor relation [succ]
    and an entry point [entry].  A point [d] dominates a point [q] when
    every path from the entry to [q] goes through [d].  Back edges are
    ordinary edges here: dominance is the usual notion on the whole
    graph, as computed by Turboshaft. *)

From Coq Require Import List Classical.
Import ListNotations.

Section Graph.

Variable point : Type.
Variable succ : point -> point -> Prop.
Variable entry : point.

(** [path x y l]: [l] is the list of the points of a path from [x] to
    [y], both included, in order.  Paths are built by extension at the
    end, as executions are. *)
Inductive path : point -> point -> list point -> Prop :=
| path_refl : forall x, path x x [x]
| path_step : forall x y z l, path x y l -> succ y z -> path x z (l ++ [z]).

Definition dom (d q : point) : Prop :=
  forall l, path entry q l -> In d l.

Definition reachable (q : point) : Prop := exists l, path entry q l.

(** ** Basic properties of paths *)

Lemma path_head : forall x y l, path x y l -> exists l', l = x :: l'.
Proof.
  induction 1 as [x | x y z l _ IH _].
  - eauto.
  - destruct IH as [l' ->]. exists (l' ++ [z]). reflexivity.
Qed.

Lemma path_last : forall x y l, path x y l -> exists l', l = l' ++ [y].
Proof.
  induction 1.
  - exists []. reflexivity.
  - eauto.
Qed.

(** Concatenation: the second path starts where the first one ends. *)
Lemma path_app :
  forall y z l2, path y z l2 ->
  forall x l1 l2', l2 = y :: l2' -> path x y l1 -> path x z (l1 ++ l2').
Proof.
  induction 1 as [y | y w z l Hp IH Hs]; intros x l1 l2' Heq H1.
  - injection Heq as <-. rewrite app_nil_r. exact H1.
  - destruct (path_head _ _ _ Hp) as [l'' ->].
    simpl in Heq. injection Heq as <-.
    rewrite app_assoc. apply path_step with (y := w); auto.
Qed.

(** The prefix of a path up to the first occurrence of a point. *)
Lemma path_prefix :
  forall x y l, path x y l -> forall z, In z l ->
  exists l1 l2, l = l1 ++ z :: l2 /\ ~ In z l1 /\ path x z (l1 ++ [z]).
Proof.
  induction 1 as [x | x y w l Hp IH Hs]; intros z Hz.
  - destruct Hz as [<- | []]. exists [], []. simpl. auto using path_refl.
  - destruct (classic (In z l)) as [Hin | Hnin].
    + destruct (IH z Hin) as (l1 & l2 & -> & Hn & Hp1).
      exists l1, (l2 ++ [w]). rewrite <- app_assoc. auto.
    + apply in_app_or in Hz. destruct Hz as [Hz | [<- | []]].
      * contradiction.
      * exists l, []. split; [reflexivity | split; auto].
        apply path_step with (y := y); auto.
Qed.

(** The last step of a path that is not reduced to a point. *)
Lemma path_last_step :
  forall x z l, path x z l -> x <> z ->
  exists y l', l = l' ++ [z] /\ path x y l' /\ succ y z.
Proof.
  intros x z l H. destruct H as [x | x y z l Hp Hs].
  - intro Hne. now contradiction Hne.
  - intros _. exists y, l. auto.
Qed.

(** ** Dominance *)

Lemma dom_refl : forall q, dom q q.
Proof.
  intros q l H. destruct (path_last _ _ _ H) as [l' ->].
  apply in_or_app. right. left. reflexivity.
Qed.

Lemma dom_entry : forall q, dom entry q.
Proof.
  intros q l H. destruct (path_head _ _ _ H) as [l' ->]. left. reflexivity.
Qed.

Lemma dom_entry_inv : forall d, dom d entry -> d = entry.
Proof.
  intros d H. specialize (H _ (path_refl entry)). destruct H as [-> | []].
  reflexivity.
Qed.

(** If [d] does not dominate [q], some path to [q] avoids [d]. *)
Lemma not_dom_path :
  forall d q, ~ dom d q -> exists l, path entry q l /\ ~ In d l.
Proof.
  intros d q H. apply not_all_ex_not in H. destruct H as [l H].
  apply imply_to_and in H. eauto.
Qed.

Lemma dom_trans : forall a b c, dom a b -> dom b c -> dom a c.
Proof.
  intros a b c Hab Hbc l Hl.
  destruct (path_prefix _ _ _ Hl b (Hbc l Hl)) as (l1 & l2 & -> & _ & Hp).
  specialize (Hab _ Hp). apply in_app_or in Hab.
  apply in_or_app. destruct Hab as [H | [<- | []]]; auto.
  right. left. reflexivity.
Qed.

(** Dominance is antisymmetric on reachable points. *)
Lemma dom_antisym : forall a b, reachable a -> dom a b -> dom b a -> a = b.
Proof.
  intros a b [l Hl] Hab Hba.
  destruct (classic (a = b)) as [| Hne]; [assumption | exfalso].
  destruct (path_prefix _ _ _ Hl b (Hba l Hl)) as (l1 & l2 & _ & Hb1 & Hp1).
  assert (Ha1 : In a l1).
  { specialize (Hab _ Hp1). apply in_app_or in Hab.
    destruct Hab as [H | [H | []]]; [exact H | congruence]. }
  destruct (path_prefix _ _ _ Hp1 a (in_or_app _ _ _ (or_introl Ha1)))
    as (l3 & l4 & Heq & _ & Hp3).
  (* [l3 ++ [a]] is a prefix of [l1], which does not contain [b]. *)
  assert (Hpre : exists l5, l1 = l3 ++ a :: l5).
  { destruct l4 as [| c l4'].
    - apply app_inj_tail in Heq. destruct Heq as [_ Heq]. congruence.
    - destruct (exists_last (l := c :: l4') (fun H => nil_cons (eq_sym H)))
        as (l5 & e & He).
      rewrite He, app_comm_cons, app_assoc in Heq.
      apply app_inj_tail in Heq. destruct Heq as [Heq _]. eauto. }
  destruct Hpre as [l5 ->].
  specialize (Hba _ Hp3). apply in_app_or in Hba.
  destruct Hba as [H | [H | []]]; [| congruence].
  apply Hb1. apply in_or_app. left. exact H.
Qed.

(** A strict dominator of [q] dominates its predecessors. *)
Lemma dom_pred :
  forall d p q, dom d q -> succ p q -> d <> q -> dom d p.
Proof.
  intros d p q Hd Hs Hne l Hl.
  specialize (Hd _ (path_step _ _ _ _ Hl Hs)).
  apply in_app_or in Hd. destruct Hd as [H | [H | []]]; [exact H | congruence].
Qed.

Lemma reachable_succ : forall p q, reachable p -> succ p q -> reachable q.
Proof.
  intros p q [l Hl] Hs. exists (l ++ [q]). apply path_step with (y := p); auto.
Qed.

Lemma reachable_dom : forall d q, reachable q -> dom d q -> reachable d.
Proof.
  intros d q [l Hl] H.
  destruct (path_prefix _ _ _ Hl d (H l Hl)) as (l1 & l2 & _ & _ & Hp).
  exists (l1 ++ [d]). exact Hp.
Qed.

End Graph.

Arguments path {point}.
Arguments dom {point}.
Arguments reachable {point}.
Arguments path_refl {point succ}.
Arguments path_step {point succ}.
