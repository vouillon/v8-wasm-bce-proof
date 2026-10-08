(** * Milestone 3: canonical values

    The analysis records facts about canonical values (see
    [CanonicalValue]): pure operations with the same opcode and options
    and inputs with the same canonical values are identified, while
    phis, loads, parameters... are leaves.  Facts are thus about terms
    whose leaves are such operations, and a fact holds for the current
    values of its leaves.

    This file adds a semantics of pure operations to the executions of
    Persistence.v, and proves the invariant that relates the value of a
    variable to its canonical term: at any time, a variable whose
    definition dominates the current point has the value of its
    canonical term, evaluated with the current values of the leaves (the
    GVN invariant of Barthe, Demange and Pichardie, "Formal verification
    of an SSA-based middle-end for CompCert", TOPLAS 2014).  This
    justifies stating facts over canonical terms, with the leaves of the
    terms as leaves, and connects them to conditions on SSA values, as
    the C++ code sees them. *)

From Coq Require Import List Arith Lia.
Import ListNotations.
From BCE Require Import Graph Persistence.

Section Canonical.

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

(** ** Pure operations

    Some variables are defined by pure operations [x = f(args)]: when
    [def x] is reached, [x] is written with [f] applied to the values of
    [args].  Their arguments are defined at dominators of [def x] (SSA).
    Other variables (phis, loads, parameters...) are unconstrained.

    Pure operations include arithmetic, shifts, conversions, constants
    (with no arguments), and [ArrayLength], whose value is a function of
    the array reference since array lengths never change.  Casts, non-null
    assertions and type annotations are identities, as are the values
    replaced by load elimination (whose replacement dominates them and
    is equal to them): these are the [ident] functions below. *)
Variable fn : Type.
Variable eval_fn : fn -> list val -> val.
Variable op : var -> option (fn * list var).

Hypothesis op_ssa :
  forall x f args y, op x = Some (f, args) -> In y args -> dom (def y) (def x).

(** Commutative operations ([WordBinopOp::IsCommutative]), whose inputs
    are sorted by [CanonicalValue], and identities ([ResolveAliases],
    [ResolveReplacements]). *)
Variable comm : fn -> Prop.
Hypothesis comm_ok :
  forall f a b, comm f -> eval_fn f [a; b] = eval_fn f [b; a].
Variable ident : fn -> Prop.
Hypothesis ident_ok : forall f a, ident f -> eval_fn f [a] = a.

Definition pure_sem (e : exec) : Prop :=
  forall k x f args, k <= len e -> pts e k = def x -> op x = Some (f, args) ->
  env e k x = eval_fn f (map (env e k) args).

(** ** Terms *)

Inductive term : Type :=
| Leaf (v : var)
| App (f : fn) (ts : list term).

Fixpoint eval (en : var -> val) (t : term) : val :=
  match t with
  | Leaf v => en v
  | App f ts => eval_fn f (map (eval en) ts)
  end.

Fixpoint tleaves (t : term) : list var :=
  match t with
  | Leaf v => [v]
  | App _ ts => flat_map tleaves ts
  end.

(** Induction on terms, with an induction hypothesis for the arguments. *)
Fixpoint term_ind2 (P : term -> Prop) (HL : forall v, P (Leaf v))
  (HA : forall f ts, Forall P ts -> P (App f ts)) (t : term) : P t :=
  match t with
  | Leaf v => HL v
  | App f ts =>
      HA f ts
        ((fix go (ts : list term) : Forall P ts :=
            match ts with
            | [] => Forall_nil P
            | t :: ts => Forall_cons t (term_ind2 P HL HA t) (go ts)
            end) ts)
  end.

Lemma eval_ext :
  forall t (e1 e2 : var -> val),
  (forall v, In v (tleaves t) -> e1 v = e2 v) -> eval e1 t = eval e2 t.
Proof.
  induction t as [v | f ts IH] using term_ind2; intros e1 e2 H; simpl.
  - apply H. left. reflexivity.
  - f_equal. induction IH as [| t ts Ht _ IHts]; simpl; [reflexivity |].
    simpl in H. f_equal.
    + apply Ht. intros v Hv. apply H, in_or_app. left. exact Hv.
    + apply IHts. intros v Hv. apply H, in_or_app. right. exact Hv.
Qed.

Lemma map_eval_ext :
  forall ts (e1 e2 : var -> val),
  (forall v, In v (flat_map tleaves ts) -> e1 v = e2 v) ->
  map (eval e1) ts = map (eval e2) ts.
Proof.
  induction ts as [| t ts IH]; intros e1 e2 H; simpl; [reflexivity |].
  simpl in H. f_equal.
  - apply eval_ext. intros v Hv. apply H, in_or_app. left. exact Hv.
  - apply IH. intros v Hv. apply H, in_or_app. right. exact Hv.
Qed.

(** ** Canonical terms

    [canon x t]: [t] is a canonical term of [x].  This is a relation
    rather than a function, which covers the choices made by
    [CanonicalValue]: any variable can be its own canonical value (a
    leaf), which is the case of phis, loads and parameters, and of the
    operations beyond the maximal depth of the recursion; a pure
    operation can be decomposed; the inputs of a commutative operation
    can be swapped; an identity is its input. *)
Inductive canon : var -> term -> Prop :=
| canon_leaf : forall x, canon x (Leaf x)
| canon_app : forall x f args ts,
    op x = Some (f, args) -> canon_list args ts -> canon x (App f ts)
| canon_comm : forall x f a b ta tb,
    op x = Some (f, [a; b]) -> comm f -> canon a ta -> canon b tb ->
    canon x (App f [tb; ta])
| canon_alias : forall x f y t,
    op x = Some (f, [y]) -> ident f -> canon y t -> canon x t
with canon_list : list var -> list term -> Prop :=
| canon_nil : canon_list [] []
| canon_cons : forall x xs t ts,
    canon x t -> canon_list xs ts -> canon_list (x :: xs) (t :: ts).

Scheme canon_mut := Induction for canon Sort Prop
  with canon_list_mut := Induction for canon_list Sort Prop.

(** The leaves of a canonical term of [x] are defined at dominators of
    [def x]. *)
Lemma canon_leaves_dom :
  forall x t, canon x t -> forall v, In v (tleaves t) -> dom (def v) (def x).
Proof.
  apply (canon_mut
    (fun x t _ => forall v, In v (tleaves t) -> dom (def v) (def x))
    (fun xs ts _ => forall v, In v (flat_map tleaves ts) ->
                    exists y, In y xs /\ dom (def v) (def y))).
  - intros x v [<- | []]. apply dom_refl.
  - intros x f args ts Hop _ IH v Hv.
    destruct (IH v Hv) as (y & Hy & Hd).
    apply dom_trans with (b := def y); eauto.
  - intros x f a b ta tb Hop _ _ IHa _ IHb v Hv.
    simpl in Hv. rewrite app_nil_r in Hv. apply in_app_or in Hv.
    destruct Hv as [Hv | Hv].
    + apply dom_trans with (b := def b); eauto. apply (op_ssa x f [a; b]); auto.
      right. left. reflexivity.
    + apply dom_trans with (b := def a); eauto. apply (op_ssa x f [a; b]); auto.
      left. reflexivity.
  - intros x f y t Hop _ _ IH v Hv.
    apply dom_trans with (b := def y); eauto. apply (op_ssa x f [y]); auto.
    left. reflexivity.
  - intros v [].
  - intros x xs t ts _ IH _ IHs v Hv. simpl in Hv. apply in_app_or in Hv.
    destruct Hv as [Hv | Hv].
    + exists x. split; [left; reflexivity | auto].
    + destruct (IHs v Hv) as (y & Hy & Hd). exists y. split; [right |]; auto.
Qed.

Lemma canon_list_leaves_dom :
  forall xs ts, canon_list xs ts ->
  forall v, In v (flat_map tleaves ts) -> exists y, In y xs /\ dom (def v) (def y).
Proof.
  induction 1 as [| x xs t ts Hc Hcs IH]; intros v Hv; [destruct Hv |].
  simpl in Hv. apply in_app_or in Hv. destruct Hv as [Hv | Hv].
  - exists x. split; [left; reflexivity | eapply canon_leaves_dom; eauto].
  - destruct (IH v Hv) as (y & Hy & Hd). exists y. split; [right |]; auto.
Qed.

(** ** The invariant *)

Section Exec.

Variable e : exec.
Hypothesis He : pure_sem e.

(** A term whose leaves are defined at dominators of [p] keeps its value
    from the last visit of [p] to a point dominated by [p] (Persistence.v). *)
Lemma eval_persist :
  forall p t0 k t,
  k <= len e -> t0 <= k -> pts e t0 = p ->
  (forall j, t0 < j -> j <= k -> pts e j <> p) ->
  dom p (pts e k) ->
  (forall v, In v (tleaves t) -> dom (def v) p) ->
  eval (env e k) t = eval (env e t0) t.
Proof.
  intros p t0 k t Hk Ht0 Hp Hlast Hdom Hleaves.
  apply eval_ext. intros v Hv.
  apply persistence with (p := p); auto.
  apply dom_leaf_ok; auto.
  rewrite <- Hp. apply exec_reachable. lia.
Qed.

(** If the invariant holds when [x] is defined, it holds as long as the
    definition of [x] dominates the current point. *)
Lemma canon_transfer :
  forall x t t0 k,
  canon x t -> k <= len e -> t0 <= k -> pts e t0 = def x ->
  (forall j, t0 < j -> j <= k -> pts e j <> def x) ->
  dom (def x) (pts e k) ->
  env e t0 x = eval (env e t0) t ->
  env e k x = eval (env e k) t.
Proof.
  intros x t t0 k Hc Hk Ht0 Hp Hlast Hdom Hx.
  rewrite persistence with (p := def x) (t := t0); auto.
  - rewrite Hx. symmetry. apply eval_persist with (p := def x); auto.
    apply canon_leaves_dom. exact Hc.
  - intros [_ H]. apply H. reflexivity.
Qed.

Theorem canon_sound :
  forall x t, canon x t ->
  forall k, k <= len e -> dom (def x) (pts e k) ->
  env e k x = eval (env e k) t.
Proof.
  apply (canon_mut
    (fun x t _ => forall k, k <= len e -> dom (def x) (pts e k) ->
                  env e k x = eval (env e k) t)
    (fun xs ts _ => forall k, k <= len e ->
                    (forall y, In y xs -> dom (def y) (pts e k)) ->
                    map (env e k) xs = map (eval (env e k)) ts)).
  - reflexivity.
  - intros x f args ts Hop Hcs IH k Hk Hdom.
    destruct (last_visit e (def x) k Hk Hdom) as (t0 & Ht0 & Hp & Hlast).
    apply canon_transfer with (t0 := t0); auto.
    + apply canon_app with (args := args); auto.
    + rewrite He with (f := f) (args := args) by (auto; lia). simpl.
      f_equal. apply IH; [lia |]. intros y Hy. rewrite Hp. eauto.
  - intros x f a b ta tb Hop Hcomm Ha IHa Hb IHb k Hk Hdom.
    destruct (last_visit e (def x) k Hk Hdom) as (t0 & Ht0 & Hp & Hlast).
    apply canon_transfer with (t0 := t0); auto.
    + apply canon_comm with (a := a) (b := b); auto.
    + rewrite He with (f := f) (args := [a; b]) by (auto; lia). simpl.
      rewrite comm_ok by exact Hcomm.
      rewrite IHa, IHb by (lia || (rewrite Hp; apply (op_ssa x f [a; b]); simpl; auto)).
      reflexivity.
  - intros x f y t Hop Hid Hy IH k Hk Hdom.
    destruct (last_visit e (def x) k Hk Hdom) as (t0 & Ht0 & Hp & Hlast).
    apply canon_transfer with (t0 := t0); auto.
    + apply canon_alias with (f := f) (y := y); auto.
    + rewrite He with (f := f) (args := [y]) by (auto; lia). simpl.
      rewrite ident_ok by exact Hid.
      apply IH; [lia |]. rewrite Hp. apply (op_ssa x f [y]); simpl; auto.
  - reflexivity.
  - intros x xs t ts _ IH _ IHs k Hk Hdom. simpl. f_equal.
    + apply IH; auto. apply Hdom. left. reflexivity.
    + apply IHs; auto. intros y Hy. apply Hdom. right. exact Hy.
Qed.

Corollary canon_list_sound :
  forall xs ts, canon_list xs ts ->
  forall k, k <= len e -> (forall y, In y xs -> dom (def y) (pts e k)) ->
  map (env e k) xs = map (eval (env e k)) ts.
Proof.
  induction 1 as [| x xs t ts Hc Hcs IH]; intros k Hk Hdom; simpl; [reflexivity |].
  f_equal.
  - apply canon_sound; auto. apply Hdom. left. reflexivity.
  - apply IH; auto. intros y Hy. apply Hdom. right. exact Hy.
Qed.

(** The argument of the comment of [CanonicalValue], literally: let
    [t0] be the last visit of [p] before time [k], at a point [q]
    dominated by [p].  A variable [x'] used at [q] (its definition
    dominates [q]) with the same canonical value as a variable [x] used
    at [p] has the value that [x] had at [p]. *)
Theorem same_canonical_value :
  forall p t0 k x x' t,
  k <= len e -> t0 <= k -> pts e t0 = p ->
  (forall j, t0 < j -> j <= k -> pts e j <> p) ->
  dom p (pts e k) ->
  dom (def x) p -> dom (def x') (pts e k) ->
  canon x t -> canon x' t ->
  env e k x' = env e t0 x.
Proof.
  intros p t0 k x x' t Hk Ht0 Hp Hlast Hdom Hx Hx' Hc Hc'.
  rewrite canon_sound with (t := t) by auto.
  rewrite canon_sound with (x := x) (t := t);
    [| exact Hc | lia | rewrite Hp; exact Hx].
  apply eval_persist with (p := p); auto.
  intros v Hv. apply dom_trans with (b := def x); auto.
  apply canon_leaves_dom with (t := t); auto.
Qed.

End Exec.

(** ** Facts over canonical terms

    The facts of the analysis are predicates over the values of
    canonical terms: [base + n < l] for offsets [n] in a range
    ([known_bounds_checks_]), [base + n] non-negative
    ([known_non_negative_offsets_]), [l >= m] ([known_min_lengths_]),
    [x = l - r] ([known_length_aliases_]), as well as the branch and trap
    conditions themselves.  The predicates are left abstract: the
    arithmetic is checked separately (Z3 lemmas). *)
Record tfact : Type := mk_tfact {
  tf_pred : list val -> Prop;
  tf_args : list term
}.

Definition tholds (F : tfact) (en : var -> val) : Prop :=
  tf_pred F (map (eval en) (tf_args F)).

Definition tfleaves (F : tfact) : list var := flat_map tleaves (tf_args F).

Lemma tholds_ext :
  forall F (e1 e2 : var -> val),
  (forall v, In v (tfleaves F) -> e1 v = e2 v) -> tholds F e1 -> tholds F e2.
Proof.
  intros F e1 e2 H. unfold tholds. rewrite map_eval_ext with (e2 := e2); auto.
Qed.

(** A fact over the canonical terms of SSA variables used at [p] (whose
    definitions dominate [p]) satisfies the leaves condition. *)
Lemma ssa_fact_leaves_ok :
  forall p xs ts, reachable p -> canon_list xs ts ->
  (forall y, In y xs -> dom (def y) p) ->
  forall v, In v (flat_map tleaves ts) -> leaf_ok p v.
Proof.
  intros p xs ts Hr Hc Hdom v Hv. apply dom_leaf_ok; auto.
  destruct (canon_list_leaves_dom _ _ Hc v Hv) as (y & Hy & Hd).
  apply dom_trans with (b := def y); auto.
Qed.

(** Recording: a condition [P] that holds for the values of SSA
    variables [xs] used at the current point is a fact over their
    canonical terms. *)
Lemma record_ssa_fact :
  forall e P xs ts k, pure_sem e -> canon_list xs ts -> k <= len e ->
  (forall y, In y xs -> dom (def y) (pts e k)) ->
  P (map (env e k) xs) -> tholds (mk_tfact P ts) (env e k).
Proof.
  intros e P xs ts k He Hc Hk Hdom HP. unfold tholds. simpl.
  rewrite <- canon_list_sound with (xs := xs); auto.
Qed.

(** Use: a known fact over canonical terms holds for the values of any
    SSA variables used at the current point that have these canonical
    terms.  This is Milestone 1 instantiated with facts over canonical
    terms. *)
Theorem known_fact_on_ssa_values :
  forall (R : point -> tfact -> Prop) e,
  pure_sem e ->
  leaves_ok succ entry def tfleaves R ->
  justified succ entry def tholds R e ->
  forall k F xs, k <= len e -> A succ entry R (pts e k) F ->
  canon_list xs (tf_args F) ->
  (forall y, In y xs -> dom (def y) (pts e k)) ->
  tf_pred F (map (env e k) xs).
Proof.
  intros R e He Hok Hjust k F xs Hk HA Hc Hdom.
  assert (H := soundness tholds_ext Hok Hjust k F Hk HA).
  unfold tholds in H. rewrite canon_list_sound with (ts := tf_args F); auto.
Qed.

End Canonical.

Arguments Leaf {var fn} v.
Arguments App {var fn} f ts.
Arguments eval {var val fn} eval_fn en t.
Arguments tleaves {var fn} t.
Arguments tfact var val fn : clear implicits.
Arguments mk_tfact {var val fn} tf_pred tf_args.
Arguments tf_pred {var val fn} t _.
Arguments tf_args {var val fn} t.
Arguments tholds {var val fn} eval_fn F en.
Arguments tfleaves {var val fn} F.
Arguments canon {var fn} op comm ident _ _.
Arguments canon_list {var fn} op comm ident _ _.
Arguments pure_sem {point} succ entry {var val} def {fn} eval_fn op e.
