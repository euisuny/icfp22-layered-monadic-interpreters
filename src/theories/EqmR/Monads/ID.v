(* begin hide *)
From Coq Require Import
     Init.Specif
     Program
     Setoid
     Morphisms
     RelationClasses.

Import ProperNotations.
From ITree Require Import
     Basics.Basics
     Basics.HeterogeneousRelations
     Basics.CategoryOps
     Basics.CategoryTheory
     Basics.CategoryFunctor.

From ITree Require Import
     Basics.Tacs EqmR.EqmRMonad.

From ExtLib Require Import
     Structures.Functor
     Monad.

Import FunctorNotation.
Import CatNotations.
Open Scope cat_scope.
Import RelNotations.
Local Open Scope relationH_scope.
(* end hide *)

(** *Identity monad. *)

Definition ID (X: Type) := X.

Global Instance Monad_MonadID : Monad ID.
split.
- exact id_.
- unfold ID. intros a b f. auto.
Defined.

Definition eqmR_ID : forall (A B : Type) (R : relationH A B), relationH (ID A) (ID B) :=
  fun _ _ R => R.

#[global] 
Instance EqmR_ID : EqmR ID :=
  {
  eqmR := eqmR_ID;
  }.

Lemma eqmR_prod_sum_rel_ID:
  forall (A B C : Type) (ma ma' : ID (C + A * B)%type) (RA : relationH A A)
    (RB : relationH B B) (RC : relationH C C),
    (fst_sum <$> ma) ≈{ RC ⊕ RA } (fst_sum <$> ma') ->
    (snd_sum <$> ma) ≈{ RC ⊕ RB } (snd_sum <$> ma') -> ma ≈{ RC ⊕ RA ⊗ RB } ma'.
Proof.
  intros. repeat red in H. repeat red in H0.
  inv H; inv H0.
  all : repeat red.
  all : unfold fmap, fst_sum, snd_sum, id_, Function.Id_Fun in *.
  all : destruct ma eqn: Hma; destruct ma' eqn: Hma'; cbn in *.
  all : repeat match goal with
        | [H : inl _ = _ |- _] => inv H
        | [H : inr _ = _ |- _] => inv H
        end; eauto.
  constructor. destruct p, p0. eauto.
Qed.

Ltac unfold_id := unfold fmap, fst_sum, snd_sum, bind, ret, Monad_MonadID, id_, Function.Id_Fun in *.

#[global]
Instance eqmR_prod_fst_inv_ID : FmapFst ID.
Proof.
  repeat intro. unfold_id. repeat red in H. inv H.
  red; auto.
Defined.

#[global]
Instance eqmR_prod_snd_inv_ID : FmapSnd ID.
Proof.
  repeat intro. unfold_id. repeat red in H. inv H.
  red; auto.
Defined.

#[global]
Instance eqmR_prod_rel_ID : RelProd ID.
Proof.
  repeat intro. unfold_id. repeat red in H, H0.
  destruct m1, m2; constructor; auto.
Defined.

#[global]
Instance eqmR_sum_inl_ID : FmapInl ID.
Proof.
  repeat intro. unfold_id. repeat red in H.
  constructor; auto.
Defined.

#[global]
Instance eqmR_sum_inr_ID : FmapInr ID.
Proof.
  repeat intro. unfold_id. repeat red in H.
  constructor; auto.
Defined.

#[global]
Instance eqmR_sum_rel_ID : RelSum ID.
Proof.
  repeat intro; split; unfold_id; intros; repeat red in H.
  - destruct m1, m2; inv H; repeat red; [apply H0 | apply H1]; auto.
  - repeat red.
    specialize (H (A1 + B1)%type (A2 + B2)%type inl inl inr inr (RA ⊕ RB)).
    destruct m1, m2; repeat red; eapply H; repeat intro; eauto.
Defined.

#[global]
Instance eqmR_conj_ID : RelConj ID.
Proof.
  repeat intro; split; unfold_id; intros; repeat red in H; auto.
Defined.

#[global]
Instance eqmR_transport_PER_ID : TransportPER ID.
Proof.
  red. intros. cbn in *. unfold eqmR_ID in *. repeat intro. split; red; intuition; auto. etransitivity; eauto.
Defined.

#[global]
Instance eqmR_rel_comp_ID : RelComp ID.
Proof.
  red.
  intros. cbn in *. unfold eqmR_ID in *. repeat intro. red.
  exists mb. tauto.
Defined.

#[global]
Instance eqmR_lift_transpose_ID : LiftTranspose ID.
Proof.
  red. intros. cbn in *. unfold eqmR_ID in *. repeat intro.
  red. split; red; intuition; auto.
Defined.

#[global]
Instance Proper_eqmR_ID :
  forall A B : Type, Proper (eq_rel (A:=A) (B:=B) ==> eq_rel) eqmR.
Proof.
  red. intros. do 2 red. cbn. unfold eqmR_ID. intros. eauto.
Defined.

#[global]
Instance Proper_eqmR_mono_ID:
  forall A B : Type,
  Proper (subrelationH (A:=A) (B:=B) ==> subrelationH (B:=ID B)) eqmR.
Proof.
  red. intros. do 2 red. cbn. unfold eqmR_ID. intros. apply H. tauto.
Defined.

#[global]
Instance transport_Equiv_ID : TransportEquiv ID.
Proof.
  repeat intro. split; typeclasses eauto.
Defined.

#[global]
Instance transport_refl:
  TransportReflexive ID.
Proof.
  repeat intro. repeat red; auto.
Qed.

#[global]
Instance transport_symm:
 TransportSymmetric ID.
Proof.
  repeat intro. repeat red; auto.
Qed.

#[global]
Instance transport_trans:
 TransportTransitive ID.
Proof.
  repeat intro. repeat red; auto. repeat red in H0, H1; eauto.
Qed.

Global Instance EqmR_OK_ID : EqmR_OK ID.
split; try typeclasses eauto.
Defined.

Lemma imageH_diag_refl {A} :
  forall (ma : ID A) , ma ≈{imageH_diag ma} ma.
Proof.
  repeat red. split; intros; repeat intro; eauto.
Qed.

Lemma image_Id :
  forall A (ma : ID A) (a1 a2 : A), image ma a1 a2 -> a1 = ma /\ a2 = ma.
Proof.
  intros.
  epose (fun x y => x = ma /\ y = ma) as Q.
  Unshelve.
  assert (ma ≈{Q} ma).
  { repeat red. split; cbn; reflexivity. }
  assert (SymmetricH Q).
  { repeat red. intros x y ; split; cbn in *. red in H1. intuition. red in H1. intuition. }
  assert (TransitiveH Q).
  { repeat red. intros x y1 y2 (HX & HY) (HY' & HZ); split; intros; cbn in *; tauto. }
  assert (PER Q). constructor; auto.
  specialize (H Q H3 H0).
  repeat red in H.
  apply H.
Qed.

Lemma mayRet_Id : forall A (ma : ID A) (a : A), a ∈ ma <-> a = ma.
Proof.
  intros. split.
  - intros. epose (fun a => a = ma) as Q.
    assert (eqmR (diagonal_prop Q) ma ma).
    { repeat red. split; cbn; reflexivity. }
    assert (PER (diagonal_prop Q)). {
      split.
      exact (diagonal_prop_SymmetricH Q).
      exact (diagonal_prop_TransitiveH Q).
    }
    specialize (H (diagonal_prop Q) H1 H0).
    repeat red in H. destruct H as (EQ2 & _).
    apply EQ2.
  - red. intros. subst. red. repeat intro. red in EQR. apply EQR.
Qed.

#[global]
Instance eqmR_mayRet_l_ID : MayRetL ID.
Proof.
  red; intros.
  rewrite mayRet_Id in H. subst.
  exists ma2. split; auto.
  rewrite mayRet_Id. reflexivity.
Defined.

#[global]
Instance eqmR_mayRet_r_ID : MayRetR ID.
Proof.
  red; intros.
  rewrite mayRet_Id in H. subst.
  exists ma1. split; auto.
  rewrite mayRet_Id. reflexivity.
Defined.

#[global]
Instance eqmR_ret_ID : RetFinal ID.
Proof.
  red; intros. repeat red. unfold ret. auto.
Defined.

#[global]
Instance eqmR_bind_ProperH_ID : ProperBind ID.
Proof.
  red; intros.
  red. red. unfold bind. unfold Monad_MonadID. apply H0.
  apply H.
Qed.

#[global]
Instance eqmR_bind_ret_l_ID : BindRetL ID.
Proof.
  intros A B f a.
  repeat red; reflexivity.
Qed.

#[global]
Instance eqmR_bind_ret_r_ID : BindRetR ID.
Proof.
  intros A ma.
  repeat red; reflexivity.
Qed.

#[global]
Instance eqmR_bind_bind_ID : BindBind ID.
Proof.
  intros A B C ma f g. repeat red; reflexivity.
Qed.

Global Instance EqmRMonad_ID : EqmRMonadLaws ID.
split; try typeclasses eauto.
  repeat red. intros; repeat intro; eauto.
Qed.

Lemma fmap_inv_ID:
  forall (A B : Type) (ma : A) (f f' : A -> B) (R : relationH B B),
    (f <$> ma) ≈{ R } (f' <$> ma) -> forall a : A, a ∈ ma -> ret (f a) ≈{ R } ret (f' a).
Proof.
  intros A B ma f f' R H a H0.
  repeat red. repeat intro. repeat red in H. unfold fmap in H.
  unfold bind, ret, Monad_MonadID, id_ in H. rewrite mayRet_Id in H0.
  subst. eauto.
Qed.

#[global]
Instance eqmR_ret_inv_ID : RetInv ID.
Proof.
  red; intros. tauto.
Defined.

#[global]
Instance mayRet_bind_inv_ID : MayRetBindInv ID.
Proof.
  red; intros.
  apply image_Id in H. crunch; eauto. subst. esplit; eauto. split.
  repeat red. repeat intro. repeat red in EQR. eauto.
  repeat red. repeat intro. repeat red in EQR. eauto.
Defined.

#[global]
Instance fmap_inv_mayRet_ID : FmapInvRet ID.
Proof.
  repeat red. repeat intro. repeat red in H. unfold fmap in H.
  unfold bind, ret, Monad_MonadID, id_ in H. rewrite mayRet_Id in H0.
  subst. eauto.
Defined.

#[global]
Instance eqmR_fmap_inv_ID : FmapInv_mayRet ID.
Proof.
  repeat intro.
  repeat red. repeat red in H. crunch.
  repeat red. rewrite! mayRet_Id. split; eauto.
  apply H.
Defined.

#[global]
Instance eqmR_inv_ID : EqmRInv ID.
repeat intro; eauto. apply image_Id in H0. destruct H0; subst; auto.
Qed.

Global Instance EqmRMonadInverses_ID : EqmRInversionProperties ID.
  split; try typeclasses eauto.
Defined.
