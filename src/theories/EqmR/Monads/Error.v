From Coq Require Import
     Logic.FunctionalExtensionality
     Morphisms
     Setoid.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Basics.HeterogeneousRelations Basics.Tacs
     EqmR.EqmRMonad EqmR.EqmRMonadT.

Import MonadNotation.
Import RelNotations.
Local Open Scope cat_scope.
Local Open Scope monad_scope.
Local Open Scope relationH_scope.

Definition error (exn A : Type) : Type :=
  sum exn A.

Section Error.
  Variable exn : Type.

  Global Instance Monad_error : Monad (error exn) :=
    {|
      ret := fun (t : Type) (X : t) => inr X;
      bind :=
        fun (t u : Type) (X : error exn t) (X0 : t -> error exn u) =>
        match X with
        | inl e => inl e
        | inr t0 => X0 t0
        end
    |}.

  Global Instance EqmR_error : EqmR (error exn) :=
    {| eqmR :=
         fun A B R x y => match x, y with
                   | inl _, inl _ => True
                   | inr r1, inr r2 => R r1 r2
                   | _, _ => False
                   end |}.

  Global Instance eqmR_transport_PER_error : TransportPER (error exn).
  Proof.
    intros A R PER_R. split.
    - intros PA PB. repeat intro. destruct PA, PB; try inv H.
      all : red; auto.
      red in H. symmetry; auto.
    - intros PA PB PC. repeat intro. destruct PA, PB, PC; try inv H; auto.
      red in H, H0. cbn. etransitivity; eauto.
  Qed.

  Global Instance eqmR_transport_Equiv_error : TransportEquiv (error exn).
  Proof.
    split. 2, 3 : apply eqmR_transport_PER_error; typeclasses eauto.
    repeat intro. repeat red. destruct x. eauto. reflexivity.
  Qed.

  Global Instance eqmR_rel_comp_error : RelComp (error exn).
  Proof.
    repeat intro. destruct ma, mb, mc; try inv H; try inv H0; cbn; auto.
    econstructor; constructor; eauto.
  Qed.

  Global Instance eqmR_prod_fst_inv_error : FmapFst (error exn).
  Proof.
    repeat intro. destruct m1, m2; try inv H; auto. cbn. auto.
  Qed.

  Global Instance eqmR_prod_snd_inv_error : FmapSnd (error exn).
  Proof.
    repeat intro. destruct m1, m2; try inv H; auto. cbn. auto.
  Qed.

  Global Instance eqmR_prod_rel_error : RelProd (error exn).
  Proof.
    repeat intro. destruct m1, m2; try inv H; try inv H0; auto; cbn; auto.
    destruct p, p0. cbn in *. constructor; auto.
  Qed.

  Global Instance eqmR_sum_inl_error : FmapInl (error exn).
  Proof.
    repeat intro. destruct m1, m2; try inv H; try inv H0; auto; cbn; auto.
  Qed.

  Global Instance eqmR_sum_inr_error : FmapInr (error exn).
  Proof.
    repeat intro. destruct m1, m2; try inv H; try inv H0; auto; cbn; auto.
  Qed.

  Global Instance eqmR_sum_rel_error : RelSum (error exn).
  Proof.
    repeat intro. split; intros; destruct m1, m2; cbn in *; eauto.
    4 : destruct s, s0; cbn in *; eauto; eapply H; repeat intro ;eauto.
    destruct s, s0; inv H; eauto.
    1, 2 :specialize (H (A1 + B1)%type (A2 + B2)%type inl inl inr inr (RA ⊕ RB));
      eapply H; repeat intro; eauto.
  Qed.

  Global Instance eqmR_conj_error : RelConj (error exn).
  Proof.
    repeat intro. destruct ma, mb; eauto. constructor; eauto.
  Qed.

  Global Instance eqmR_lift_transpose_error : LiftTranspose (error exn).
  Proof.
    repeat intro. split; repeat intro; destruct x, y; cbn in *; eauto.
  Qed.

  Global Instance eqmR_Proper_error : forall A B : Type, Proper ((@eq_rel A B) ==> eq_rel) eqmR.
  Proof.
    repeat intro. destruct H. split; repeat intro; destruct x0, y0; cbn in *; eauto.
  Qed.

  Global Instance eqmR_Proper_mono :
    forall A B : Type, Proper (subrelationH (A:=A)(B:=B) ==> subrelationH (B:=error exn B)) eqmR.
  Proof.
    repeat intro. destruct x0, y0; cbn in *; eauto.
  Qed.

  Instance transport_refl : TransportReflexive (error exn).
  Proof.
    repeat intro; repeat red; destruct x; eauto.
  Qed.

  Instance transport_symm : TransportSymmetric (error exn).
  Proof.
    repeat intro; repeat red; destruct x, y; eauto.
  Qed.

  Instance transport_trans : TransportTransitive (error exn).
  Proof.
    repeat intro; repeat red; destruct x, y, z;  eauto. destruct H0.
  Qed.

  Global Instance EqmR_OK_error : EqmR_OK (error exn).
  Proof.
    constructor; try typeclasses eauto.
  Qed.

  Lemma PER_bot : forall A, PER (A := A) (fun _ _ => False).
  Proof.
    split; repeat intro; try contradiction.
  Qed.

  Lemma mayRet_error :
    forall A (a :A) (ma : error exn A), a ∈ ma -> ma = inr a.
  Proof.
    intros. destruct ma.
    - specialize (H _ (PER_bot _) I). inv H.
    - f_equiv. repeat red in H.
      specialize (H (singletonR a0)).
      cbn in *. destruct H; eauto.
      split. apply singletonR_SymmetricH. apply singletonR_TransitiveH.
      constructor; auto.
  Qed.

  Lemma mayRet_ret_error :
    forall A (a :A), a ∈ ret a.
  Proof.
    intros. repeat intro. apply EQR.
  Qed.

  Ltac errtac :=
    match goal with
    | [H : ?a ∈ ?ma |- _] => apply mayRet_error in H; subst
    end.

  Global Instance eqmR_mayRet_l_error : MayRetL (error exn).
  Proof.
    repeat intro.
    errtac.
    destruct ma2; cbn in *. inv EQH. esplit; split; eauto.
    apply mayRet_ret_error.
  Qed.

  Global Instance eqmR_mayRet_r_error : MayRetR (error exn).
  Proof.
    repeat intro.
    errtac.
    destruct ma1; cbn in *. inv EQH. esplit; split; eauto.
    apply mayRet_ret_error.
  Qed.

  Global Instance eqmR_ret_error : RetFinal (error exn).
  Proof.
    repeat intro. apply H.
  Qed.

  Global Instance eqmR_bind_ProperH_error : ProperBind (error exn).
  Proof.
    repeat intro. destruct ma1, ma2; try inv H. cbn; auto.
    cbn. cbn in H. specialize (H0 _ _ H).
    eauto.
  Qed.

  Global Instance eqmR_bind_ret_l_error : BindRetL (error exn).
  Proof.
    repeat intro. cbn. destruct (f a); eauto.
  Qed.

  Global Instance eqmR_bind_ret_r_error : BindRetR (error exn).
  Proof.
    repeat intro. cbn. destruct (ma); eauto.
  Qed.

  Global Instance eqmR_bind_bind_error : BindBind (error exn).
  Proof.
    repeat intro. cbn. destruct (ma); eauto.
    destruct (f a); eauto. destruct (g b); eauto.
  Qed.

  Global Instance EqmRMonad_error : EqmRMonadLaws (error exn).
  Proof.
    constructor; try typeclasses eauto.
    repeat intro. cbn. destruct ma; eauto.
    repeat intro. apply EQR.
  Qed.

  Global Instance eqmR_ret_inv_error : RetInv (error exn).
  Proof.
    repeat intro. apply H.
  Qed.

  Global Instance mayRet_bind_inv_error : MayRetBindInv (error exn).
  Proof.
    repeat intro. errtac. cbn in *. destruct ma. inv H. exists a.
    split; try rewrite H; apply mayRet_ret_error.
  Qed.

  Global Instance fmap_inv_mayRet_error : FmapInvRet (error exn).
  Proof.
    repeat intro. errtac. cbn in *. auto.
  Qed.

  Global Instance fmap_inv_error : FmapInv_mayRet (error exn).
  Proof.
    repeat intro. cbn in *. destruct ma1, ma2; cbn in *; eauto.
    split; eauto. red. split; apply mayRet_ret_error.
  Qed.

  Global Instance eqmR_inv_error : EqmRInv (error exn).
  repeat intro. cbn in *. apply mayRet_error in H0. subst. auto.
  Qed.

  Global Instance EqmRMonadInverses_error : EqmRInversionProperties (error exn).
  Proof.
    constructor; try typeclasses eauto.
  Qed.

End Error.
