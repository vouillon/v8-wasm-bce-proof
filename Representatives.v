(** * Milestone 3, refined: representatives, the depth limit and truncation keys

    [CanonicalValue] does not build terms: it identifies values through
    representatives.  The canonical value of an operation with a
    structural key (its opcode and options, and the canonical values of
    its inputs) is the first operation found with that key
    ([values_by_structure_]); the canonical value of a phi, a load, a
    parameter, or of an operation beyond the depth limit, is the value
    itself; identities (casts, load-elimination replacements) have the
    canonical value of their input; the inputs of commutative operations
    are sorted.  Besides, [TruncationKey] registers the canonical value
    [cX] of a 64-bit value [X] as the representative of the key of
    [trunc(X)], when no truncation of [X] has been seen: the same
    [OpIndex] then stands for [X] in a 64-bit position, and for
    [trunc(X)] in a 32-bit one.

    This file models these choices by a relation [CV x r] (the analysis
    may give [x] the canonical value [r]), and the table by a function
    [vbs] from keys to representatives, with the properties that the
    code maintains as hypotheses.  A representative [r], in a position
    of representation [rho], unfolds to a term ([U rho r t]).  The
    theorem: any such term is a canonical term ([canon], Canonical.v) of
    any variable of representation [rho] with canonical value [r].  So
    two variables with the same canonical value and representation have
    the same value wherever both are used ([same_representative]), and a
    fact recorded about a representative, as a fact over its unfolding,
    is a fact over the canonical terms of the values it is about. *)

From Coq Require Import List Classical.
Import ListNotations.
From BCE Require Import Graph Persistence Canonical.

Section Representatives.

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
Local Notation eval := (eval eval_fn).
Local Notation canon := (canon op comm ident).
Local Notation canon_list := (canon_list op comm ident).

(** The operations are acyclic: an operation is computed from earlier
    ones (phis, which close the cycles of loops, are not operations). *)
Hypothesis op_wf :
  well_founded (fun y x => exists f args, op x = Some (f, args) /\ In y args).

(** ** Representations

    Each value has a representation ([rp]).  The opcode and the options
    of an operation ([fn], the first component of its structural key)
    determine the representations of its output and of its inputs: the
    options of [WordBinop] and [Shift] include [rep] (the right side of a
    shift being 32-bit), those of [Change] and [TaggedBitcast] the
    representations they convert from and to. *)
Variable repr : Type.
Variable rp : var -> repr.
Variable out_rep : fn -> repr.
Variable in_rep : fn -> list repr.
Hypothesis op_rep :
  forall x f args, op x = Some (f, args) ->
  rp x = out_rep f /\ map rp args = in_rep f.
Hypothesis ident_rep : forall f, ident f -> in_rep f = [out_rep f].
Hypothesis comm_rep : forall f, comm f -> exists rho, in_rep f = [rho; rho].

(** The truncation of 64-bit values to 32 bits. *)
Variables W32 W64 : repr.
Hypothesis W32_W64 : W32 <> W64.
Variable tr : fn.
Hypothesis out_tr : out_rep tr = W32.
Hypothesis in_tr : in_rep tr = [W64].

(** ** The analysis

    [vbs] is the final table [values_by_structure_]: keys are an opcode
    with its options, and the canonical values of the inputs.  As a
    function, it has a single representative per key (the first one
    registered: [emplace]). *)
Variable vbs : fn * list var -> option var.

(** The canonical values that [CanonicalValue] may return.  It is a
    relation, as the depth limit makes the canonical value of an
    operation depend on the depth at which it is reached (operations
    beyond the limit are their own canonical value, and are not
    memoized). *)
Inductive CV : var -> var -> Prop :=
(** A phi, a load, a parameter, an operation beyond the depth limit, or
    without a structural key. *)
| cv_self : forall x, CV x x
(** [ResolveReplacements], [ResolveAliases]. *)
| cv_ident : forall x f y r,
    op x = Some (f, [y]) -> ident f -> CV y r -> CV x r
(** The representative of the structural key. *)
| cv_key : forall x f args rs r,
    op x = Some (f, args) -> CVl args rs -> vbs (f, rs) = Some r -> CV x r
(** Commutative operations, whose inputs are sorted. *)
| cv_comm : forall x f a b ra rb r,
    op x = Some (f, [a; b]) -> comm f -> CV a ra -> CV b rb ->
    vbs (f, [rb; ra]) = Some r -> CV x r
with CVl : list var -> list var -> Prop :=
| cvl_nil : CVl [] []
| cvl_cons : forall x xs r rs, CV x r -> CVl xs rs -> CVl (x :: xs) (r :: rs).

(** What is in the table.  A representative is either the first
    operation found with its key, which it computed from its own inputs
    (possibly sorted), or, for the key of the truncation of a 64-bit
    canonical value [r], [r] itself ([TruncationKey]). *)
Hypothesis vbs_ok :
  forall f rs r, vbs (f, rs) = Some r ->
  (exists args, op r = Some (f, args) /\
     (CVl args rs \/
      (comm f /\ exists a b ra rb,
         args = [a; b] /\ rs = [rb; ra] /\ CV a ra /\ CV b rb))) \/
  (f = tr /\ rs = [r] /\ rp r = W64).

(** A value is the representative of at most one key per output
    representation: its own key, computed once (it is memoized), and,
    for a 64-bit value, the key of its truncation. *)
Hypothesis vbs_inj :
  forall f1 rs1 f2 rs2 r, vbs (f1, rs1) = Some r -> vbs (f2, rs2) = Some r ->
  out_rep f1 = out_rep f2 -> f1 = f2 /\ rs1 = rs2.

(** ** Unfolding a representative

    [U rho r t]: the representative [r], in a position of representation
    [rho], stands for the term [t].  A value that represents no key of
    that representation stands for itself; the representative of a key
    stands for the operation of the key applied to what its inputs stand
    for; [cX], in a 32-bit position, stands for [trunc(X)]. *)
Inductive U : repr -> var -> term -> Prop :=
| u_leaf : forall r,
    (forall f rs, vbs (f, rs) = Some r -> out_rep f <> rp r) ->
    U (rp r) r (Leaf r)
| u_key : forall f rs r ts,
    vbs (f, rs) = Some r -> rp r = out_rep f -> Ul (in_rep f) rs ts ->
    U (out_rep f) r (App f ts)
| u_trunc : forall r t,
    vbs (tr, [r]) = Some r -> rp r = W64 -> U W64 r t -> U W32 r (App tr [t])
with Ul : list repr -> list var -> list term -> Prop :=
| ul_nil : Ul [] [] []
| ul_cons : forall rho rhos r rs t ts,
    U rho r t -> Ul rhos rs ts -> Ul (rho :: rhos) (r :: rs) (t :: ts).

(** ** The theorem *)

Definition P (x : var) : Prop :=
  forall r, CV x r ->
  (exists t, U (rp x) r t) /\ (forall t, U (rp x) r t -> canon x t).

Lemma P_list :
  forall args rs, CVl args rs -> (forall y, In y args -> P y) ->
  (exists ts, Ul (map rp args) rs ts) /\
  (forall ts, Ul (map rp args) rs ts -> canon_list args ts).
Proof.
  induction 1 as [| y ys r rs Hy Hys IH]; intros HP.
  - split; [exists []; constructor |].
    intros ts Hu. inversion Hu; subst. constructor.
  - destruct (HP y (or_introl eq_refl) r Hy) as [[t Ht] Hc].
    destruct IH as [[ts Hts] Hcs]; [intros z Hz; apply HP; right; exact Hz |].
    split; [exists (t :: ts); constructor; assumption |].
    intros ts' Hu. inversion Hu; subst. constructor; auto.
Qed.

Lemma comm_args_rep :
  forall x f a b, op x = Some (f, [a; b]) -> comm f ->
  rp a = rp b /\ in_rep f = [rp a; rp a].
Proof.
  intros x f a b Hop Hc.
  destruct (op_rep _ _ _ Hop) as [_ Hin].
  destruct (comm_rep _ Hc) as [rho Hrho].
  rewrite Hrho in Hin. simpl in Hin. injection Hin as -> ->. auto.
Qed.

Lemma CVl_length : forall args rs, CVl args rs -> length args = length rs.
Proof. induction 1; simpl; auto. Qed.

Theorem representatives_sound : forall x, P x.
Proof.
  intros x. induction x as [x IH] using (well_founded_induction op_wf).
  assert (HPargs : forall f args, op x = Some (f, args) ->
                   forall y, In y args -> P y).
  { intros f args Hop y Hy. apply IH. exists f, args. auto. }
  intros r Hcv. inversion Hcv as [x' | x' f y r' Hop Hid Hy |
                                  x' f args rs r' Hop Hcvl Hvbs |
                                  x' f a b ra rb r' Hop Hcomm Ha Hb Hvbs];
    subst.
  - (* [x] is its own canonical value. *)
    split.
    + destruct (classic (exists f rs, vbs (f, rs) = Some r /\
                                      out_rep f = rp r))
        as [(f & rs & Hvbs & Hrep) | Hno].
      * destruct (vbs_ok _ _ _ Hvbs)
          as [(args & Hop & [Hcvl | (Hc & a & b & ra & rb & -> & -> & Ha & Hb)])
             | (-> & -> & Hw)].
        -- destruct (P_list _ _ Hcvl (HPargs _ _ Hop)) as [[ts Hts] _].
           destruct (op_rep _ _ _ Hop) as [Hout Hin].
           exists (App f ts). rewrite Hout. apply u_key with (rs := rs); auto.
           rewrite <- Hin. exact Hts.
        -- destruct (op_rep _ _ _ Hop) as [Hout _].
           destruct (comm_args_rep _ _ _ _ Hop Hc) as [Eab Hin].
           destruct (HPargs _ _ Hop b (or_intror (or_introl eq_refl)) rb Hb)
             as [[tb Htb] _].
           destruct (HPargs _ _ Hop a (or_introl eq_refl) ra Ha)
             as [[ta Hta] _].
           exists (App f [tb; ta]). rewrite Hout.
           apply u_key with (rs := [rb; ra]); auto.
           rewrite Hin. rewrite <- Eab in Htb. repeat constructor; assumption.
        -- rewrite out_tr, Hw in Hrep. contradiction.
      * exists (Leaf r). apply u_leaf.
        intros f rs Hvbs Hrep. apply Hno. eauto.
    + intros t Hu. inversion Hu as [r' Hno | f rs r' ts Hvbs Hrep Hul |
                                    r' t' Hvbs Hw Ht']; subst.
      * apply canon_leaf.
      * destruct (vbs_ok _ _ _ Hvbs)
          as [(args & Hop & [Hcvl | (Hc & a & b & ra & rb & -> & -> & Ha & Hb)])
             | (-> & -> & Hw)].
        -- destruct (op_rep _ _ _ Hop) as [_ Hin].
           destruct (P_list _ _ Hcvl (HPargs _ _ Hop)) as [_ Hcs].
           apply canon_app with (args := args); auto.
           apply Hcs. rewrite Hin. exact Hul.
        -- destruct (comm_args_rep _ _ _ _ Hop Hc) as [Eab Hin].
           rewrite Hin in Hul.
           inversion Hul as [| ? ? ? ? tb ? Htb Hul']; subst.
           inversion Hul' as [| ? ? ? ? ta ? Hta Hul'']; subst.
           inversion Hul''; subst.
           apply canon_comm with (a := a) (b := b); auto.
           ++ apply (HPargs _ _ Hop a (or_introl eq_refl) ra Ha). exact Hta.
           ++ apply (HPargs _ _ Hop b (or_intror (or_introl eq_refl)) rb Hb).
              rewrite <- Eab. exact Htb.
        -- exfalso. apply W32_W64. rewrite <- out_tr, <- Hrep. exact Hw.
      * (* [x] is 64-bit, not 32-bit. *)
        exfalso. apply W32_W64. rewrite <- Hw. assumption.
  - (* An identity. *)
    destruct (op_rep _ _ _ Hop) as [Hout Hin].
    rewrite (ident_rep _ Hid) in Hin. simpl in Hin. injection Hin as Ey.
    rewrite Hout, <- Ey.
    destruct (HPargs _ _ Hop y (or_introl eq_refl) r Hy) as [Hex Hc].
    split; [exact Hex |].
    intros t Hu. apply canon_alias with (f := f) (y := y); auto.
  - (* A structural key. *)
    destruct (op_rep _ _ _ Hop) as [Hout Hin].
    destruct (P_list _ _ Hcvl (HPargs _ _ Hop)) as [[ts Hts] Hcs].
    rewrite Hin in Hts, Hcs. rewrite Hout.
    split.
    + destruct (vbs_ok _ _ _ Hvbs)
        as [(args' & Hop' & _) | (-> & -> & Hw)].
      * exists (App f ts). apply u_key with (rs := rs); auto.
        destruct (op_rep _ _ _ Hop') as [Hout' _]. exact Hout'.
      * (* The truncation key of a 64-bit canonical value. *)
        rewrite in_tr in Hts.
        inversion Hts as [| ? ? ? ? t ? Ht Hts']; subst.
        inversion Hts'; subst.
        exists (App tr [t]). rewrite out_tr. apply u_trunc; auto.
    + intros t Hu. inversion Hu as [r' Hno | f' rs' r' ts' Hvbs' Hrep Hul |
                                    r' t' Hvbs' Hw Ht']; subst.
      * exfalso. apply (Hno f rs Hvbs). symmetry. assumption.
      * destruct (vbs_inj _ _ _ _ _ Hvbs Hvbs' (eq_sym H)) as [<- <-].
        apply canon_app with (args := args); auto.
      * destruct (vbs_inj _ _ _ _ _ Hvbs Hvbs') as [-> ->];
          [rewrite out_tr; congruence |].
        apply canon_app with (args := args); auto.
        apply Hcs. rewrite in_tr. repeat constructor. exact Ht'.
  - (* A commutative operation. *)
    destruct (op_rep _ _ _ Hop) as [Hout _].
    destruct (comm_args_rep _ _ _ _ Hop Hcomm) as [Eab Hrho].
    destruct (HPargs _ _ Hop a (or_introl eq_refl) ra Ha) as [[ta Hta] Hca].
    destruct (HPargs _ _ Hop b (or_intror (or_introl eq_refl)) rb Hb)
      as [[tb Htb] Hcb].
    rewrite <- Eab in Htb, Hcb. rewrite Hout.
    split.
    + destruct (vbs_ok _ _ _ Hvbs)
        as [(args' & Hop' & _) | (_ & Hl & _)]; [| discriminate Hl].
      exists (App f [tb; ta]). apply u_key with (rs := [rb; ra]); auto.
      * destruct (op_rep _ _ _ Hop') as [Hout' _]. exact Hout'.
      * rewrite Hrho. repeat constructor; assumption.
    + intros t Hu. inversion Hu as [r' Hno | f' rs' r' ts' Hvbs' Hrep Hul |
                                    r' t' Hvbs' Hw Ht']; subst.
      * exfalso. apply (Hno f _ Hvbs). symmetry. assumption.
      * destruct (vbs_inj _ _ _ _ _ Hvbs Hvbs' (eq_sym H)) as [<- <-].
        rewrite Hrho in Hul.
        inversion Hul as [| ? ? ? ? tb' ? Htb' Hul']; subst.
        inversion Hul' as [| ? ? ? ? ta' ? Hta' Hul'']; subst.
        inversion Hul''; subst.
        apply canon_comm with (a := a) (b := b); auto.
      * destruct (vbs_inj _ _ _ _ _ Hvbs Hvbs') as [_ Hl];
          [rewrite out_tr; congruence | discriminate Hl].
Qed.

Corollary unfolding_exists :
  forall x r, CV x r -> exists t, U (rp x) r t.
Proof. intros x r H. apply (representatives_sound x r H). Qed.

Corollary unfolding_canon :
  forall x r t, CV x r -> U (rp x) r t -> canon x t.
Proof. intros x r t H. apply (representatives_sound x r H). Qed.

(** ** Consequences for executions *)

Section Exec.

Variable e : exec.
Hypothesis He : pure_sem succ entry def eval_fn op e.

(** Two values with the same canonical value and representation are
    equal wherever both are used. *)
Theorem same_representative :
  forall x x' r k, CV x r -> CV x' r -> rp x = rp x' -> k <= len e ->
  dom (def x) (pts e k) -> dom (def x') (pts e k) ->
  env e k x = env e k x'.
Proof.
  intros x x' r k Hx Hx' Hrp Hk Hd Hd'.
  destruct (unfolding_exists x r Hx) as [t Ht].
  assert (Ht' : U (rp x') r t) by (rewrite <- Hrp; exact Ht).
  transitivity (eval (env e k) t).
  - apply canon_sound with (op := op) (comm := comm) (ident := ident); auto.
    apply unfolding_canon with (r := r); auto.
  - symmetry.
    apply canon_sound with (op := op) (comm := comm) (ident := ident); auto.
    apply unfolding_canon with (r := r); auto.
Qed.

(** [ExistingTruncation]: the base of [a[trunc(Y + n)]] is a truncation
    [T] of a value with the same canonical value [cY] as [Y], found
    possibly in another branch, so that [T] need not dominate the access.
    It is only used through its canonical value [r], the representative
    of the key of [trunc(cY)]: whatever it unfolds to, its value is the
    truncation of [Y], which dominates the access. *)
Theorem existing_truncation :
  forall y cy r t k, CV y cy -> rp y = W64 -> vbs (tr, [cy]) = Some r ->
  U W32 r t -> k <= len e -> dom (def y) (pts e k) ->
  eval (env e k) t = eval_fn tr [env e k y].
Proof.
  intros y cy r t k Hy Hw Hvbs Hu Hk Hd.
  assert (Hcy : forall t', U W64 cy t' -> eval (env e k) t' = env e k y).
  { intros t' Ht'. symmetry.
    apply canon_sound with (op := op) (comm := comm) (ident := ident); auto.
    apply unfolding_canon with (r := cy); auto. rewrite Hw. exact Ht'. }
  inversion Hu as [r' Hno | f rs r' ts Hvbs' Hrep Hul | r' t' Hvbs' Hw' Ht'];
    subst.
  - exfalso. apply (Hno tr [cy] Hvbs). rewrite out_tr. congruence.
  - destruct (vbs_inj _ _ _ _ _ Hvbs Hvbs') as [<- <-]; [congruence |].
    rewrite in_tr in Hul.
    inversion Hul as [| ? ? ? ? t0 ? Ht0 Hul']; subst.
    inversion Hul'; subst. simpl. rewrite (Hcy t0 Ht0). reflexivity.
  - destruct (vbs_inj _ _ _ _ _ Hvbs Hvbs') as [_ Hl]; [reflexivity |].
    injection Hl as ->. simpl. rewrite (Hcy t' Ht'). reflexivity.
Qed.

End Exec.

End Representatives.
