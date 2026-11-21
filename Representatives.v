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

(** * Deriving [vbs_ok] and [vbs_inj] from table construction

    The section above took [vbs_ok] and [vbs_inj] as hypotheses on the
    final table [values_by_structure_].  Here we model the stateful
    construction of [(canonical_values_, values_by_structure_)] by
    [CanonicalValue] and [TruncationKey] (memoization, depth cut-off,
    no-overwrite [emplace], commutative argument sorting, and truncation
    keys) and prove that [vbs_ok] and [vbs_inj] are invariants of every
    run starting from empty tables. *)

Section TableConstruction.

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

Hypothesis op_wf :
  well_founded (fun y x => exists f args, op x = Some (f, args) /\ In y args).

Variable repr : Type.
Variable rp : var -> repr.
Variable out_rep : fn -> repr.
Variable in_rep : fn -> list repr.
Hypothesis op_rep :
  forall x f args, op x = Some (f, args) ->
  rp x = out_rep f /\ map rp args = in_rep f.
Hypothesis ident_rep : forall f, ident f -> in_rep f = [out_rep f].
Hypothesis comm_rep : forall f, comm f -> exists rho, in_rep f = [rho; rho].

Variables W32 W64 : repr.
Hypothesis W32_W64 : W32 <> W64.
Variable tr : fn.
Hypothesis out_tr : out_rep tr = W32.
Hypothesis in_tr : in_rep tr = [W64].

Local Notation memo_t := (var -> option var).
Local Notation vbs_t := (fn * list var -> option var).
Local Notation CV := (CV var fn op comm ident).
Local Notation CVl := (CVl var fn op comm ident).

(** No-overwrite insertion, modeling [emplace] on [canonical_values_] and
    [values_by_structure_]. *)
Definition map_insert {A B : Type} (m : A -> option B) (k : A) (v : B)
    (m' : A -> option B) : Prop :=
  (forall k', k' <> k -> m' k' = m k') /\
  match m k with
  | Some old => m' k = Some old
  | None => m' k = Some v
  end.

Definition map_ext {A B : Type} (m1 m2 : A -> option B) : Prop :=
  forall k v, m1 k = Some v -> m2 k = Some v.

Lemma map_ext_refl : forall A B (m : A -> option B), map_ext m m.
Proof. intros A B m k v H. exact H. Qed.

Lemma map_ext_trans :
  forall A B (m1 m2 m3 : A -> option B),
  map_ext m1 m2 -> map_ext m2 m3 -> map_ext m1 m3.
Proof. intros A B m1 m2 m3 H12 H23 k v H. apply H23, H12, H. Qed.

Lemma map_insert_ext :
  forall A B (m : A -> option B) k v m',
  map_insert m k v m' -> map_ext m m'.
Proof.
  intros A B m k v m' [Hne Hk] k' v' Hm.
  destruct (classic (k' = k)) as [-> | Hneq].
  - rewrite Hm in Hk. exact Hk.
  - rewrite Hne by exact Hneq. exact Hm.
Qed.

Lemma map_insert_some :
  forall A B (m : A -> option B) k v m',
  map_insert m k v m' -> m' k <> None.
Proof.
  intros A B m k v m' [_ Hk].
  destruct (m k); rewrite Hk; discriminate.
Qed.

(** [CV] is monotone as entries are added to [vbs]. *)
Lemma CV_mono :
  forall v1 v2, map_ext v1 v2 ->
  (forall x r, CV v1 x r -> CV v2 x r) /\
  (forall xs rs, CVl v1 xs rs -> CVl v2 xs rs).
Proof.
  intros v1 v2 Hext.
  assert (Hcv : forall x r, CV v1 x r -> CV v2 x r).
  { fix go 3; intros x r H.
    destruct H as [x | x f y r Hop Hid Hy |
                   x f args rs r Hop Hargs Hvbs |
                   x f a b ra rb r Hop Hc Ha Hb Hvbs].
    - apply cv_self.
    - eapply cv_ident; eauto.
    - eapply cv_key; eauto.
      clear Hop Hvbs. induction Hargs; constructor; auto.
    - eapply cv_comm; eauto. }
  split; [exact Hcv |].
  induction 1; constructor; auto.
Qed.

Lemma CV_mono_1 :
  forall v1 v2 x r, map_ext v1 v2 -> CV v1 x r -> CV v2 x r.
Proof. intros v1 v2 x r Hext. apply (proj1 (CV_mono v1 v2 Hext)). Qed.

Lemma CVl_mono :
  forall v1 v2 xs rs, map_ext v1 v2 -> CVl v1 xs rs -> CVl v2 xs rs.
Proof. intros v1 v2 xs rs Hext. apply (proj2 (CV_mono v1 v2 Hext)). Qed.

(** ** Acyclicity of operation dependencies *)

Inductive dep : var -> var -> Prop :=
| dep_step : forall x f args y, op x = Some (f, args) -> In y args -> dep y x
| dep_trans : forall z y x, dep z y -> dep y x -> dep z x.

Lemma dep_inv :
  forall a b, dep a b ->
  exists z, (exists f args, op b = Some (f, args) /\ In z args) /\
            (a = z \/ dep a z).
Proof.
  induction 1 as [x f args y Hop Hin | z y x Hzy IH1 Hyx IH2].
  - exists y. split; [exists f, args; auto | left; reflexivity].
  - destruct IH2 as (w & Hrel & [<- | Hw]).
    + exists y. split; [exact Hrel | right; exact Hzy].
    + exists w. split; [exact Hrel | right; eapply dep_trans; eauto].
Qed.

Lemma dep_irrefl : forall x, ~ dep x x.
Proof.
  assert (Hgen : forall x y, (y = x \/ dep y x) -> ~ dep x y).
  { intro x. induction x as [x IH] using (well_founded_induction op_wf).
    intros y Hy Hxy.
    assert (Hxx : dep x x).
    { destruct Hy as [-> | Hyx]; [exact Hxy | eapply dep_trans; eauto]. }
    destruct (dep_inv _ _ Hxx) as (z & Hrel & Hz).
    apply (IH z Hrel x Hz).
    destruct Hrel as (f & args & Hop & Hin).
    eapply dep_step; eauto. }
  intro x. apply (Hgen x x). left. reflexivity.
Qed.

(** ** Operational model of [CanonicalValue] and [TruncationKey] *)

Inductive eval_cv :
    memo_t -> vbs_t -> var -> var -> memo_t -> vbs_t -> Prop :=
| ev_memo : forall m v x r,
    m x = Some r ->
    eval_cv m v x r m v
| ev_cutoff : forall m v x,
    eval_cv m v x x m v
| ev_leaf : forall m v x m',
    m x = None ->
    map_insert m x x m' ->
    eval_cv m v x x m' v
| ev_ident_nomemo : forall m v x f y r m' v',
    op x = Some (f, [y]) -> ident f ->
    eval_cv m v y r m' v' ->
    eval_cv m v x r m' v'
| ev_ident : forall m v x f y r m1 v1 m2,
    m x = None ->
    op x = Some (f, [y]) -> ident f ->
    eval_cv m v y r m1 v1 ->
    map_insert m1 x r m2 ->
    eval_cv m v x r m2 v1
| ev_key : forall m v x f args rs m1 v1 v2 r m2,
    m x = None ->
    op x = Some (f, args) -> ~ ident f ->
    eval_cv_list m v args rs m1 v1 ->
    map_insert v1 (f, rs) x v2 ->
    v2 (f, rs) = Some r ->
    map_insert m1 x r m2 ->
    eval_cv m v x r m2 v2
| ev_comm : forall m v x f a b ra rb m1 v1 m2 v2 v3 r m3,
    m x = None ->
    op x = Some (f, [a; b]) -> comm f ->
    eval_cv m v a ra m1 v1 ->
    eval_cv m1 v1 b rb m2 v2 ->
    map_insert v2 (f, [rb; ra]) x v3 ->
    v3 (f, [rb; ra]) = Some r ->
    map_insert m2 x r m3 ->
    eval_cv m v x r m3 v3
with eval_cv_list :
    memo_t -> vbs_t -> list var -> list var -> memo_t -> vbs_t -> Prop :=
| evl_nil : forall m v,
    eval_cv_list m v [] [] m v
| evl_cons : forall m v x xs r rs m1 v1 m2 v2,
    eval_cv m v x r m1 v1 ->
    eval_cv_list m1 v1 xs rs m2 v2 ->
    eval_cv_list m v (x :: xs) (r :: rs) m2 v2.

Scheme eval_cv_mut := Induction for eval_cv Sort Prop
  with eval_cv_list_mut := Induction for eval_cv_list Sort Prop.
Combined Scheme eval_cv_comb from eval_cv_mut, eval_cv_list_mut.

Inductive eval_trunc :
    memo_t -> vbs_t -> var -> var -> memo_t -> vbs_t -> Prop :=
| ev_trunc : forall m v x c m1 v1 v2 r,
    rp x = W64 ->
    eval_cv m v x c m1 v1 ->
    map_insert v1 (tr, [c]) c v2 ->
    v2 (tr, [c]) = Some r ->
    eval_trunc m v x r m1 v2.

(** Any sequence of [CanonicalValue] and [TruncationKey] calls starting
    from empty tables. *)
Inductive table_run : memo_t -> vbs_t -> Prop :=
| run_init : table_run (fun _ => None) (fun _ => None)
| run_cv : forall m v x r m' v',
    table_run m v -> eval_cv m v x r m' v' -> table_run m' v'
| run_trunc : forall m v x r m' v',
    table_run m v -> eval_trunc m v x r m' v' -> table_run m' v'.

(** ** Locality: [CanonicalValue] only writes [memo] at [x] and its dependencies *)

Lemma eval_cv_memo_local :
  (forall m v x r m' v', eval_cv m v x r m' v' ->
     forall z, m' z <> m z -> z = x \/ dep z x) /\
  (forall m v xs rs m' v', eval_cv_list m v xs rs m' v' ->
     forall z, m' z <> m z -> exists y, In y xs /\ (z = y \/ dep z y)).
Proof.
  apply (eval_cv_comb
    (fun m v x r m' v' _ => forall z, m' z <> m z -> z = x \/ dep z x)
    (fun m v xs rs m' v' _ =>
       forall z, m' z <> m z -> exists y, In y xs /\ (z = y \/ dep z y))).
  - intros m v x r _ z Hne. contradiction.
  - intros m v x z Hne. contradiction.
  - intros m v x m' _ [Hne _] z Hz.
    destruct (classic (z = x)) as [-> | Hzx]; [left; reflexivity |].
    exfalso. apply Hz, Hne, Hzx.
  - intros m v x f y r m' v' Hop _ _ IH z Hz.
    right. destruct (IH z Hz) as [-> | Hzy].
    + eapply dep_step; [exact Hop | left; reflexivity].
    + eapply dep_trans; [exact Hzy | eapply dep_step; [exact Hop | left; reflexivity]].
  - intros m v x f y r m1 v1 m2 _ Hop _ _ IH [Hne _] z Hz.
    destruct (classic (z = x)) as [-> | Hzx]; [left; reflexivity |].
    rewrite Hne in Hz by exact Hzx.
    right. destruct (IH z Hz) as [-> | Hzy].
    + eapply dep_step; [exact Hop | left; reflexivity].
    + eapply dep_trans; [exact Hzy | eapply dep_step; [exact Hop | left; reflexivity]].
  - intros m v x f args rs m1 v1 v2 r m2 _ Hop _ _ IH _ _ [Hne _] z Hz.
    destruct (classic (z = x)) as [-> | Hzx]; [left; reflexivity |].
    rewrite Hne in Hz by exact Hzx.
    right. destruct (IH z Hz) as (y & Hin & [-> | Hzy]).
    + eapply dep_step; eauto.
    + eapply dep_trans; [exact Hzy | eapply dep_step; eauto].
  - intros m v x f a b ra rb m1 v1 m2 v2 v3 r m3 _ Hop _ _ IHa _ IHb _ _ [Hne _] z Hz.
    destruct (classic (z = x)) as [-> | Hzx]; [left; reflexivity |].
    rewrite Hne in Hz by exact Hzx.
    right. destruct (classic (m1 z = m z)) as [Heq | Hneq].
    + rewrite <- Heq in Hz. destruct (IHb z Hz) as [-> | Hzb].
      * eapply dep_step; [exact Hop | right; left; reflexivity].
      * eapply dep_trans; [exact Hzb | eapply dep_step; [exact Hop | right; left; reflexivity]].
    + destruct (IHa z Hneq) as [-> | Hza].
      * eapply dep_step; [exact Hop | left; reflexivity].
      * eapply dep_trans; [exact Hza | eapply dep_step; [exact Hop | left; reflexivity]].
  - intros m v z Hne. contradiction.
  - intros m v x xs r rs m1 v1 m2 v2 _ IHx _ IHxs z Hz.
    destruct (classic (m1 z = m z)) as [Heq | Hneq].
    + rewrite <- Heq in Hz. destruct (IHxs z Hz) as (y & Hin & Hy).
      exists y. split; [right; exact Hin | exact Hy].
    + exists x. split; [left; reflexivity | apply IHx, Hneq].
Qed.

(** ** The table invariant *)

Definition vbs_ok_p (v : vbs_t) : Prop :=
  forall f rs r, v (f, rs) = Some r ->
  (exists args, op r = Some (f, args) /\
     (CVl v args rs \/
      (comm f /\ exists a b ra rb,
         args = [a; b] /\ rs = [rb; ra] /\
         CV v a ra /\ CV v b rb))) \/
  (f = tr /\ rs = [r] /\ rp r = W64).

Definition vbs_inj_p (v : vbs_t) : Prop :=
  forall f1 rs1 f2 rs2 r, v (f1, rs1) = Some r -> v (f2, rs2) = Some r ->
  out_rep f1 = out_rep f2 -> f1 = f2 /\ rs1 = rs2.

Record wf_state (m : memo_t) (v : vbs_t) : Prop := {
  wf_vbs_ok : vbs_ok_p v;
  wf_vbs_inj : vbs_inj_p v;
  wf_memo_cv : forall x r, m x = Some r -> CV v x r;
  wf_vbs_memo : forall f rs r, v (f, rs) = Some r ->
    (m r <> None /\ rp r = out_rep f) \/
    (f = tr /\ rs = [r] /\ rp r = W64)
}.

Lemma wf_state_init : wf_state (fun _ => None) (fun _ => None).
Proof.
  split.
  - intros f rs r H. discriminate H.
  - intros f1 rs1 f2 rs2 r H. discriminate H.
  - intros x r H. discriminate H.
  - intros f rs r H. discriminate H.
Qed.

Lemma CV_rp_W64 :
  forall v, vbs_ok_p v -> forall x r, CV v x r -> rp x = W64 -> rp r = W64.
Proof.
  intros v Hok x r Hcv.
  induction Hcv as [x | x f y r Hop Hid Hy IH |
                    x f args rs r Hop _ Hvbs |
                    x f a b ra rb r Hop _ _ _ _ _ Hvbs]; intro Hw.
  - exact Hw.
  - apply IH. destruct (op_rep _ _ _ Hop) as [Hout Hin].
    rewrite (ident_rep _ Hid) in Hin. simpl in Hin. injection Hin as Ey.
    rewrite Ey, <- Hout. exact Hw.
  - destruct (op_rep _ _ _ Hop) as [Hout _].
    destruct (Hok _ _ _ Hvbs) as [(args' & Hop' & _) | (-> & _ & Hwr)].
    + destruct (op_rep _ _ _ Hop') as [Hout' _]. congruence.
    + exact Hwr.
  - destruct (op_rep _ _ _ Hop) as [Hout _].
    destruct (Hok _ _ _ Hvbs) as [(args' & Hop' & _) | (_ & Hl & _)];
      [| discriminate Hl].
    destruct (op_rep _ _ _ Hop') as [Hout' _]. congruence.
Qed.

(** Helper: extending [memo] alone preserves [wf_state] when the new
    binding is a valid [CV]. *)
Lemma wf_insert_memo :
  forall m v x r m',
  wf_state m v -> CV v x r -> map_insert m x r m' -> wf_state m' v.
Proof.
  intros m v x r m' [Hok Hinj Hcv Hvm] Hxr Hins.
  assert (Hext : map_ext m m') by (eapply map_insert_ext; eauto).
  split; auto.
  - intros z rz Hz. destruct (classic (z = x)) as [-> | Hneq].
    + destruct Hins as [_ Hk]. destruct (m x) as [old |] eqn:Em.
      * rewrite Hk in Hz. injection Hz as <-. apply Hcv, Em.
      * rewrite Hk in Hz. injection Hz as <-. exact Hxr.
    + destruct Hins as [Hne _]. rewrite Hne in Hz by exact Hneq.
      apply Hcv, Hz.
  - intros f rs r0 Hv. destruct (Hvm _ _ _ Hv) as [[Hsome Hrep] | Htr].
    + left. split; [| exact Hrep].
      destruct (m r0) as [u |] eqn:Em; [| contradiction].
      rewrite (Hext _ _ Em). discriminate.
    + right. exact Htr.
Qed.

(** Helper: inserting a structural key [(f, rs) -> x] into [vbs] and
    [x -> r] into [memo] when [m x = None]. *)
Lemma wf_insert_key :
  forall m v x f args rs v' r m',
  wf_state m v ->
  m x = None ->
  op x = Some (f, args) ->
  (CVl v args rs \/
   (comm f /\ exists a b ra rb,
      args = [a; b] /\ rs = [rb; ra] /\ CV v a ra /\ CV v b rb)) ->
  map_insert v (f, rs) x v' ->
  v' (f, rs) = Some r ->
  map_insert m x r m' ->
  wf_state m' v' /\ CV v' x r.
Proof.
  intros m v x f args rs v' r m' [Hok Hinj Hcv Hvm] Hmx Hop Hargs Hvins Hr Hmins.
  assert (Hvext : map_ext v v') by (eapply map_insert_ext; eauto).
  assert (Hmext : map_ext m m') by (eapply map_insert_ext; eauto).
  assert (Hxr : CV v' x r).
  { destruct Hargs as [Hcvl | (Hc & a & b & ra & rb & -> & -> & Ha & Hb)].
    - eapply cv_key; eauto. eapply CVl_mono; eauto.
    - eapply cv_comm; eauto; eapply CV_mono_1; eauto. }
  split; [| exact Hxr].
  destruct Hvins as [Hvne Hvk].
  destruct (v (f, rs)) as [old |] eqn:Ev.
  - (* Key already present: [v'] equals [v] everywhere. *)
    assert (Heqv : forall k, v' k = v k).
    { intro k. destruct (classic (k = (f, rs))) as [-> | Hneq].
      - rewrite Hvk, Ev. reflexivity.
      - apply Hvne, Hneq. }
    assert (Hwf1 : wf_state m v').
    { split.
      - intros f0 rs0 r0 Hv0. rewrite Heqv in Hv0.
        destruct (Hok _ _ _ Hv0) as [(a0 & Ha0 & [Hl0 | (Hc0 & a1 & b1 & ra1 & rb1 & -> & -> & H1 & H2)]) | Htr].
        + left. exists a0. split; [exact Ha0 | left; eapply CVl_mono; eauto].
        + left. exists [a1; b1]. split; [exact Ha0 | right; repeat eexists; eauto; eapply CV_mono_1; eauto].
        + right. exact Htr.
      - intros f1 rs1 f2 rs2 r0 H1 H2 Hrep. rewrite !Heqv in H1, H2.
        apply Hinj with (r := r0); auto.
      - intros z rz Hz. eapply CV_mono_1; [exact Hvext | apply Hcv, Hz].
      - intros f0 rs0 r0 Hv0. rewrite Heqv in Hv0. apply Hvm, Hv0. }
    eapply wf_insert_memo; eauto.
  - (* Fresh key: [v' (f, rs) = Some x], so [r = x] and [m' x = Some x]. *)
    assert (Er : r = x) by congruence. subst r.
    assert (Hrx : rp x = out_rep f) by (apply (op_rep _ _ _ Hop)).
    split.
    + intros f0 rs0 r0 Hv0.
      destruct (classic ((f0, rs0) = (f, rs))) as [Heq | Hneq].
      * injection Heq as -> ->. rewrite Hvk in Hv0. injection Hv0 as <-.
        left. exists args. split; [exact Hop |].
        destruct Hargs as [Hcvl | (Hc & a & b & ra & rb & -> & -> & Ha & Hb)].
        -- left. eapply CVl_mono; eauto.
        -- right. split; [exact Hc |]. exists a, b, ra, rb.
           repeat split; eapply CV_mono_1; eauto.
      * rewrite Hvne in Hv0 by exact Hneq.
        destruct (Hok _ _ _ Hv0) as [(a0 & Ha0 & [Hl0 | (Hc0 & a1 & b1 & ra1 & rb1 & -> & -> & H1 & H2)]) | Htr].
        -- left. exists a0. split; [exact Ha0 | left; eapply CVl_mono; eauto].
        -- left. exists [a1; b1]. split; [exact Ha0 | right; repeat eexists; eauto; eapply CV_mono_1; eauto].
        -- right. exact Htr.
    + intros f1 rs1 f2 rs2 r0 H1 H2 Hrep.
      destruct (classic ((f1, rs1) = (f, rs))) as [E1 | N1];
      destruct (classic ((f2, rs2) = (f, rs))) as [E2 | N2].
      * rewrite <- E1 in E2. injection E2. auto.
      * injection E1 as -> ->. rewrite Hvk in H1. injection H1 as <-.
        rewrite Hvne in H2 by exact N2.
        exfalso. destruct (Hvm _ _ _ H2) as [[Hsome _] | (-> & _ & Hw)].
        -- contradiction.
        -- apply W32_W64. rewrite <- out_tr, <- Hrep, <- Hrx. exact Hw.
      * injection E2 as -> ->. rewrite Hvk in H2. injection H2 as <-.
        rewrite Hvne in H1 by exact N1.
        exfalso. destruct (Hvm _ _ _ H1) as [[Hsome _] | (-> & _ & Hw)].
        -- contradiction.
        -- apply W32_W64. rewrite <- out_tr, Hrep, <- Hrx. exact Hw.
      * rewrite Hvne in H1, H2 by assumption. apply Hinj with (r := r0); auto.
    + intros z rz Hz. destruct (classic (z = x)) as [-> | Hneq].
      * destruct Hmins as [_ Hmk]. rewrite Hmx in Hmk.
        rewrite Hmk in Hz. injection Hz as <-. exact Hxr.
      * destruct Hmins as [Hmne _]. rewrite Hmne in Hz by exact Hneq.
        eapply CV_mono_1; [exact Hvext | apply Hcv, Hz].
    + intros f0 rs0 r0 Hv0.
      destruct (classic ((f0, rs0) = (f, rs))) as [Heq | Hneq].
      * injection Heq as -> ->. rewrite Hvk in Hv0. injection Hv0 as <-.
        left. split; [eapply map_insert_some; eauto | exact Hrx].
      * rewrite Hvne in Hv0 by exact Hneq.
        destruct (Hvm _ _ _ Hv0) as [[Hsome Hrep0] | Htr].
        -- left. split; [| exact Hrep0].
           destruct (m r0) as [u |] eqn:Em; [| contradiction].
           rewrite (Hmext _ _ Em). discriminate.
        -- right. exact Htr.
Qed.

(** [CanonicalValue] preserves [wf_state], grows [vbs] monotonically, and
    returns a valid [CV]. *)
Lemma eval_cv_preserves :
  (forall m v x r m' v', eval_cv m v x r m' v' ->
     wf_state m v -> wf_state m' v' /\ map_ext v v' /\ CV v' x r) /\
  (forall m v xs rs m' v', eval_cv_list m v xs rs m' v' ->
     wf_state m v -> wf_state m' v' /\ map_ext v v' /\ CVl v' xs rs).
Proof.
  apply (eval_cv_comb
    (fun m v x r m' v' _ =>
       wf_state m v -> wf_state m' v' /\ map_ext v v' /\ CV v' x r)
    (fun m v xs rs m' v' _ =>
       wf_state m v -> wf_state m' v' /\ map_ext v v' /\ CVl v' xs rs)).
  - (* ev_memo *)
    intros m v x r Hmx Hwf.
    split; [exact Hwf | split; [apply map_ext_refl |]].
    apply (wf_memo_cv _ _ Hwf), Hmx.
  - (* ev_cutoff *)
    intros m v x Hwf.
    split; [exact Hwf | split; [apply map_ext_refl | apply cv_self]].
  - (* ev_leaf *)
    intros m v x m' _ Hins Hwf.
    split; [eapply wf_insert_memo; eauto; apply cv_self
          | split; [apply map_ext_refl | apply cv_self]].
  - (* ev_ident_nomemo *)
    intros m v x f y r m' v' Hop Hid _ IH Hwf.
    destruct (IH Hwf) as (Hwf' & Hext & Hcv).
    split; [exact Hwf' | split; [exact Hext | eapply cv_ident; eauto]].
  - (* ev_ident *)
    intros m v x f y r m1 v1 m2 _ Hop Hid _ IH Hins Hwf.
    destruct (IH Hwf) as (Hwf1 & Hext & Hcv).
    assert (Hxr : CV v1 x r) by (eapply cv_ident; eauto).
    split; [eapply wf_insert_memo; eauto | split; [exact Hext | exact Hxr]].
  - (* ev_key *)
    intros m v x f args rs m1 v1 v2 r m2 Hmx Hop _ Hargs IH Hvins Hr Hmins Hwf.
    destruct (IH Hwf) as (Hwf1 & Hext1 & Hcvl).
    assert (Hm1x : m1 x = None).
    { destruct (classic (m1 x = m x)) as [Heq | Hneq]; [congruence |].
      exfalso. destruct (proj2 eval_cv_memo_local _ _ _ _ _ _ Hargs x Hneq)
        as (y & Hin & [Exy | Hxy]).
      - subst y. apply (dep_irrefl x). eapply dep_step; eauto.
      - apply (dep_irrefl x). eapply dep_trans; [exact Hxy | eapply dep_step; eauto]. }
    destruct (wf_insert_key m1 v1 x f args rs v2 r m2 Hwf1 Hm1x Hop
                (or_introl Hcvl) Hvins Hr Hmins) as [Hwf2 Hxr].
    split; [exact Hwf2 | split; [| exact Hxr]].
    eapply map_ext_trans; [exact Hext1 | eapply map_insert_ext; eauto].
  - (* ev_comm *)
    intros m v x f a b ra rb m1 v1 m2 v2 v3 r m3 Hmx Hop Hc Ha IHa Hb IHb
           Hvins Hr Hmins Hwf.
    destruct (IHa Hwf) as (Hwf1 & Hext1 & Hcva).
    destruct (IHb Hwf1) as (Hwf2 & Hext2 & Hcvb).
    assert (Hm1x : m1 x = None).
    { destruct (classic (m1 x = m x)) as [Heq | Hneq]; [congruence |].
      exfalso. destruct (proj1 eval_cv_memo_local _ _ _ _ _ _ Ha x Hneq)
        as [Exa | Hxa].
      - subst a. apply (dep_irrefl x). eapply dep_step; [exact Hop | left; reflexivity].
      - apply (dep_irrefl x).
        eapply dep_trans; [exact Hxa | eapply dep_step; [exact Hop | left; reflexivity]]. }
    assert (Hm2x : m2 x = None).
    { destruct (classic (m2 x = m1 x)) as [Heq | Hneq]; [congruence |].
      exfalso. destruct (proj1 eval_cv_memo_local _ _ _ _ _ _ Hb x Hneq)
        as [Exb | Hxb].
      - subst b. apply (dep_irrefl x). eapply dep_step; [exact Hop | right; left; reflexivity].
      - apply (dep_irrefl x).
        eapply dep_trans; [exact Hxb | eapply dep_step; [exact Hop | right; left; reflexivity]]. }
    assert (Hcva2 : CV v2 a ra) by (eapply CV_mono_1; eauto).
    destruct (wf_insert_key m2 v2 x f [a; b] [rb; ra] v3 r m3 Hwf2 Hm2x Hop
                (or_intror (conj Hc (ex_intro _ a (ex_intro _ b
                  (ex_intro _ ra (ex_intro _ rb
                    (conj eq_refl (conj eq_refl (conj Hcva2 Hcvb)))))))))
                Hvins Hr Hmins) as [Hwf3 Hxr].
    split; [exact Hwf3 | split; [| exact Hxr]].
    eapply map_ext_trans; [exact Hext1 |].
    eapply map_ext_trans; [exact Hext2 | eapply map_insert_ext; eauto].
  - (* evl_nil *)
    intros m v Hwf.
    split; [exact Hwf | split; [apply map_ext_refl | constructor]].
  - (* evl_cons *)
    intros m v x xs r rs m1 v1 m2 v2 _ IHx _ IHxs Hwf.
    destruct (IHx Hwf) as (Hwf1 & Hext1 & Hcvx).
    destruct (IHxs Hwf1) as (Hwf2 & Hext2 & Hcvxs).
    split; [exact Hwf2 | split; [eapply map_ext_trans; eauto |]].
    constructor; [eapply CV_mono_1; eauto | exact Hcvxs].
Qed.

(** [TruncationKey] preserves [wf_state] and grows [vbs] monotonically. *)
Lemma eval_trunc_preserves :
  forall m v x r m' v',
  eval_trunc m v x r m' v' -> wf_state m v ->
  wf_state m' v' /\ map_ext v v'.
Proof.
  intros m v x r m' v' [m0 v0 x0 c m1 v1 v2 r0 Hw Hcv Hvins Hr] Hwf.
  destruct (proj1 eval_cv_preserves _ _ _ _ _ _ Hcv Hwf)
    as (Hwf1 & Hext1 & Hcvc).
  assert (Hrc : rp c = W64) by (eapply CV_rp_W64; [apply (wf_vbs_ok _ _ Hwf1) | exact Hcvc | exact Hw]).
  assert (Hext2 : map_ext v1 v2) by (eapply map_insert_ext; eauto).
  split; [| eapply map_ext_trans; eauto].
  destruct Hwf1 as [Hok1 Hinj1 Hcv1 Hvm1].
  destruct Hvins as [Hvne Hvk].
  destruct (v1 (tr, [c])) as [old |] eqn:Ev.
  - assert (Heqv : forall k, v2 k = v1 k).
    { intro k. destruct (classic (k = (tr, [c]))) as [-> | Hneq].
      - rewrite Hvk, Ev. reflexivity.
      - apply Hvne, Hneq. }
    split.
    + intros f0 rs0 r1 Hv0. rewrite Heqv in Hv0.
      destruct (Hok1 _ _ _ Hv0) as [(a0 & Ha0 & [Hl0 | (Hc0 & a1 & b1 & ra1 & rb1 & -> & -> & H1 & H2)]) | Htr].
      * left. exists a0. split; [exact Ha0 | left; eapply CVl_mono; eauto].
      * left. exists [a1; b1]. split; [exact Ha0 | right; repeat eexists; eauto; eapply CV_mono_1; eauto].
      * right. exact Htr.
    + intros f1 rs1 f2 rs2 r1 H1 H2 Hrep. rewrite !Heqv in H1, H2.
      apply Hinj1 with (r := r1); auto.
    + intros z rz Hz. eapply CV_mono_1; [exact Hext2 | apply Hcv1, Hz].
    + intros f0 rs0 r1 Hv0. rewrite Heqv in Hv0. apply Hvm1, Hv0.
  - split.
    + intros f0 rs0 r1 Hv0.
      destruct (classic ((f0, rs0) = (tr, [c]))) as [Heq | Hneq].
      * injection Heq as -> ->. rewrite Hvk in Hv0. injection Hv0 as <-.
        right. auto.
      * rewrite Hvne in Hv0 by exact Hneq.
        destruct (Hok1 _ _ _ Hv0) as [(a0 & Ha0 & [Hl0 | (Hc0 & a1 & b1 & ra1 & rb1 & -> & -> & H1 & H2)]) | Htr].
        -- left. exists a0. split; [exact Ha0 | left; eapply CVl_mono; eauto].
        -- left. exists [a1; b1]. split; [exact Ha0 | right; repeat eexists; eauto; eapply CV_mono_1; eauto].
        -- right. exact Htr.
    + intros f1 rs1 f2 rs2 r1 H1 H2 Hrep.
      destruct (classic ((f1, rs1) = (tr, [c]))) as [E1 | N1];
      destruct (classic ((f2, rs2) = (tr, [c]))) as [E2 | N2].
      * rewrite <- E1 in E2. injection E2. auto.
      * injection E1 as -> ->. rewrite Hvk in H1. injection H1 as <-.
        rewrite Hvne in H2 by exact N2.
        exfalso. destruct (Hvm1 _ _ _ H2) as [[_ Hrep2] | (-> & -> & _)].
        -- apply W32_W64. rewrite <- out_tr, Hrep, <- Hrep2. exact Hrc.
        -- apply N2. reflexivity.
      * injection E2 as -> ->. rewrite Hvk in H2. injection H2 as <-.
        rewrite Hvne in H1 by exact N1.
        exfalso. destruct (Hvm1 _ _ _ H1) as [[_ Hrep1] | (-> & -> & _)].
        -- apply W32_W64. rewrite <- out_tr, <- Hrep, <- Hrep1. exact Hrc.
        -- apply N1. reflexivity.
      * rewrite Hvne in H1, H2 by assumption. apply Hinj1 with (r := r1); auto.
    + intros z rz Hz. eapply CV_mono_1; [exact Hext2 | apply Hcv1, Hz].
    + intros f0 rs0 r1 Hv0.
      destruct (classic ((f0, rs0) = (tr, [c]))) as [Heq | Hneq].
      * injection Heq as -> ->. rewrite Hvk in Hv0. injection Hv0 as <-.
        right. auto.
      * rewrite Hvne in Hv0 by exact Hneq. apply Hvm1, Hv0.
Qed.

(** ** Main theorem: every run maintains [vbs_ok] and [vbs_inj] *)

Theorem table_run_wf :
  forall m v, table_run m v -> wf_state m v.
Proof.
  induction 1 as [| m v x r m' v' _ IH Hcv | m v x r m' v' _ IH Htr].
  - exact wf_state_init.
  - apply (proj1 eval_cv_preserves _ _ _ _ _ _ Hcv IH).
  - apply (eval_trunc_preserves _ _ _ _ _ _ Htr IH).
Qed.

Corollary table_run_vbs_ok :
  forall m v, table_run m v -> vbs_ok_p v.
Proof. intros m v H. apply (wf_vbs_ok _ _ (table_run_wf _ _ H)). Qed.

Corollary table_run_vbs_inj :
  forall m v, table_run m v -> vbs_inj_p v.
Proof. intros m v H. apply (wf_vbs_inj _ _ (table_run_wf _ _ H)). Qed.

(** End-to-end instantiation of [same_representative] without assuming
    [vbs_ok] or [vbs_inj]: for any table built by [CanonicalValue] and
    [TruncationKey], two values with the same canonical value and
    representation are equal wherever both are used. *)
Corollary table_run_same_representative :
  forall m v e,
  table_run m v ->
  pure_sem succ entry def eval_fn op e ->
  forall x x' r k,
  CV v x r -> CV v x' r -> rp x = rp x' -> k <= len e ->
  dom (def x) (pts e k) -> dom (def x') (pts e k) ->
  env e k x = env e k x'.
Proof.
  intros m v e Hrun He x x' r k Hx Hx' Hrp Hk Hd Hd'.
  exact (same_representative point succ entry var val def fn eval_fn op
           op_ssa comm comm_ok ident ident_ok op_wf repr rp out_rep in_rep
           op_rep ident_rep comm_rep W32 W64 W32_W64 tr out_tr in_tr v
           (table_run_vbs_ok _ _ Hrun) (table_run_vbs_inj _ _ Hrun)
           e He x x' r k Hx Hx' Hrp Hk Hd Hd').
Qed.

Corollary table_run_existing_truncation :
  forall m v e,
  table_run m v ->
  pure_sem succ entry def eval_fn op e ->
  forall y cy r t k,
  CV v y cy -> rp y = W64 -> v (tr, [cy]) = Some r ->
  U var fn repr rp out_rep in_rep W32 W64 tr v W32 r t ->
  k <= len e -> dom (def y) (pts e k) ->
  eval eval_fn (env e k) t = eval_fn tr [env e k y].
Proof.
  intros m v e Hrun He y cy r t k Hy Hw Hvbs Hu Hk Hd.
  exact (existing_truncation point succ entry var val def fn eval_fn op
           op_ssa comm comm_ok ident ident_ok op_wf repr rp out_rep in_rep
           op_rep ident_rep comm_rep W32 W64 W32_W64 tr out_tr in_tr v
           (table_run_vbs_ok _ _ Hrun) (table_run_vbs_inj _ _ Hrun)
           e He y cy r t k Hy Hw Hvbs Hu Hk Hd).
Qed.

End TableConstruction.
