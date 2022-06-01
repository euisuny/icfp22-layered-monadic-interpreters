(* begin hide *)
From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From Paco Require Import paco.

From Coq Require Import Morphisms
     Program
     Classes.RelationClasses
     Relation_Definitions.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.HeterogeneousRelations
     Basics.Tacs
     Core.ITreeDefinition
     Eq.Eq Eq.UpToTaus
     EqmR.EqmRMonad.

Import CatNotations.
Import FunctorNotation.
Import MonadNotation.
Import RelNotations.
Local Open Scope monad_scope.
Local Open Scope cat_scope.
Local Open Scope relationH_scope.
(* end hide *)

Global Instance eqitF_Proper_R {E : Type -> Type} {R1 R2:Type} :
  Proper ((@eq_rel R1 R2) ==> eq ==> eq ==> (eq_rel ==> eq_rel) ==> eq_rel ==> eq_rel)
    (@eqitF E R1 R2).
Proof.
  repeat red.
  intros. subst. split; unfold subrelationH; intros.
  - induction H0; try auto.
    econstructor. apply H. assumption.
    econstructor. apply H3. assumption.
    econstructor. intros. specialize (REL v). specialize (H2 x3 y3). apply H2 in H3. apply H3. assumption.
  - induction H0; try auto.
    econstructor. apply H. assumption.
    econstructor. apply H3. assumption.
    econstructor. intros. specialize (REL v). specialize (H2 x3 y3). apply H2 in H3. apply H3. assumption.
Qed.

Global Instance eqitF_Proper_R2 {E : Type -> Type} {R1 R2:Type} :
  Proper ((@eq_rel R1 R2) ==> eq ==> eq ==> eq ==> eq ==> eq ==> eq ==> iff)
         (@eqitF E R1 R2).
Proof.
  repeat red.
  intros. subst. split; intros.
  - induction H0; try auto.
    econstructor. apply H. assumption.
  - induction H0; try auto.
    econstructor. apply H. assumption.
Qed.

Global Instance eqit_Proper_R {E : Type -> Type} {R1 R2:Type}
  : Proper ( (@eq_rel R1 R2) ==> eq ==> eq ==> eq ==> eq ==> iff) (@eqit E R1 R2).
Proof.
  repeat red.
  intros. subst.
  split.
  -  revert_until y1. pcofix CIH. intros.
     pstep. punfold H1. red in H1. red.
     hinduction H1 before CIH; intros; eauto.
     + apply EqRet. apply H. assumption.
     + apply EqTau. right. apply CIH. pclearbot. pinversion REL.
     + apply EqVis. intros. red. right. apply CIH.
       specialize (REL v).
       red in REL. pclearbot. pinversion REL.
  -  revert_until y1. pcofix CIH. intros.
     pstep. punfold H1. red in H1. red.
     hinduction H1 before CIH; intros; eauto.
     + apply EqRet. apply H. assumption.
     + apply EqTau. right. apply CIH. pclearbot. pinversion REL.
     + apply EqVis. intros. red. right. apply CIH.
       specialize (REL v).
       red in REL. pclearbot. pinversion REL.
Qed.

Global Instance eutt_Proper_R {E : Type -> Type} {R1 R2:Type}
  : Proper ( (@eq_rel R1 R2) ==> eq ==> eq ==> iff) (@eutt E R1 R2).
Proof.
  unfold eutt. repeat red.
  intros. split; intros; subst.
  - rewrite <- H. assumption.
  - rewrite H. assumption.
Qed.

From ITree Require Import Eq.

(* Sanity check of definitions on ITree. *)
#[global]
Instance EqmR_ITree_strong {E} : EqmR (itree E) := {| eqmR := fun a b => eq_itree |}.

Lemma compose_rcompose_equiv : forall {A B C} (R1 : relationH A B) (R2 : relationH B C),
  eq_rel (rcompose R1 R2) (rel_compose R2 R1) .
Proof.
  intros.
  split; unfold compose, subrelationH.
  - intros. inversion H. exists r2; split; assumption.
  - intros. edestruct H as (? & ? & ?).
    econstructor; eassumption.
Qed.

#[global]
Instance eqmR_conj_ITree {E}: RelConj (itree E).
repeat intro; eapply eq_itree_conj; eauto.
Qed.

#[global]
Instance itree_transport_PER_ {E}: TransportPER (itree E).
Proof.
  intros. split. unfold SymmetricH, relationH in *. intros.
  red. apply Symmetric_eqit. red. apply H.
  apply H0.
  intros. unfold TransitiveH, relationH in *. intros.
  red. eapply Transitive_eqit. red. apply H. apply H0. apply H1.
Qed.

#[global]
Instance itree_rel_comp {E} : RelComp (itree E).
Proof.
  red.
  intros until C. unfold eutt in *.
  intros R1 R2 ma mb mc HR1 HR2. intros.
  setoid_rewrite <- compose_rcompose_equiv.
  eapply eqit_trans; eassumption.
Qed.

#[global]
Instance transport_refl {E} :TransportReflexive (itree E).
Proof.
  repeat intro. reflexivity.
Qed.
#[global]
Instance transport_symm {E} : TransportSymmetric (itree E).
Proof.
  repeat intro. symmetry; auto.
Qed.
#[global]
Instance transport_trans {E} : TransportTransitive (itree E).
Proof.
  repeat intro. etransitivity; eauto.
Qed.

#[global]
Instance itree_lift_transpose {E} : LiftTranspose (itree E).
Proof.
  intros A B. unfold eq_rel. split.
  + pcofix CIH. intros a b H'.
    pstep. red. punfold H'. red in H'.
    remember (observe a) as x'.
    remember (observe b) as y'.
    generalize dependent a; generalize dependent b.
    induction H'; intros.
    * constructor. intuition.
    * constructor. destruct REL. right.
      eapply CIH. intuition.
      destruct H.
    * constructor. red in REL. intros. unfold id.
      specialize (REL v).
      destruct REL. right. eapply CIH. intuition. intuition.
    * constructor. assumption. intuition.
    * constructor. assumption. eapply IHH'. reflexivity.
      eassumption.
  + pcofix CIH. intros a b H'.
    pstep. red. punfold H'. red in H'.
    remember (observe a) as x'.
    remember (observe b) as y'.
    generalize dependent a; generalize dependent b.
    induction H'; intros.
    * constructor. intuition.
    * constructor. destruct REL. right.
      eapply CIH. intuition. intuition.
    * constructor. red in REL. intros. unfold id.
      specialize (REL v).
      destruct REL. right. eapply CIH. intuition.
      intuition.
    * constructor. assumption. eapply IHH'.
      reflexivity. eassumption.
    * constructor. assumption. eapply IHH'.
      eassumption.
      reflexivity.
Qed.

#[global]
Instance itree_eq_itree_Proper {E}:
  forall A B : Type, Proper (eq_rel (A := A) (B := B) ==> eq_rel) (eq_itree (E :=E)).
Proof.
  intros A B. unfold eq_rel. split.
  + pcofix CIH. intros a b H'.
    pstep. red. punfold H'. red in H'.
    remember (observe a) as x'.
    remember (observe b) as y'.
    generalize dependent a; generalize dependent b.
    induction H'; intros.
    * constructor. intuition.
    * constructor. destruct REL. right.
      eapply CIH. intuition.
      destruct H. intuition.
    * constructor. red in REL. intros. unfold id.
      specialize (REL v).
      destruct REL. right. eapply CIH. intuition. intuition.
    * constructor. assumption. intuition.
    * inv CHECK.
  + pcofix CIH. intros a b H'.
    pstep. red. punfold H'. red in H'.
    remember (observe a) as x'.
    remember (observe b) as y'.
    generalize dependent a; generalize dependent b.
    induction H'; intros.
    * constructor. intuition.
    * constructor. destruct REL. right.
      eapply CIH. intuition. intuition.
    * constructor. red in REL. intros. unfold id.
      specialize (REL v).
      destruct REL. right. eapply CIH. intuition.
      intuition.
    * constructor. assumption. eapply IHH'. eassumption. 
      reflexivity. 
    * constructor. assumption. eapply IHH'.
      reflexivity.
      eassumption.
Qed.

#[global]
Instance itree_eq_itree_Proper_mono {E}:
  forall A B : Type, Proper (subrelationH (A:=A) (B:=B) ==> subrelationH (B:=itree E B)) eq_itree.
Proof.
  intros A B. do 3 red.
  intros x y. pcofix CIH. pstep. red.
  intros sub a b H.
  do 2 red in H. punfold H. red in H.
  remember (observe a) as a'.
  remember (observe b) as b'.
  generalize dependent a. generalize dependent b.
  induction H; intros; eauto.
  + constructor. red in REL. destruct REL.
    right. apply CIH. assumption. assumption.
    destruct H.
  + constructor. red in REL. intros.
    specialize (REL v). unfold id.
    destruct REL. right. apply CIH. assumption. assumption.
    destruct H.
Qed.

Inductive Returns {E} {A: Type} (a: A) : itree E A -> Prop :=
| ReturnsRet: forall t, t ≅ Ret a -> Returns a t
| ReturnsTau: forall t u, t ≅ Tau u -> Returns a u -> Returns a t
| ReturnsVis: forall {X} (e: E X) (x: X) t k, t ≅ Vis e k -> Returns a (k x) -> Returns a t
.

Global Instance Returns_eq_itree {E A} a: Proper (eq_itree eq ==> iff) (@Returns E A a).
Proof.
  repeat intro; split; intros HRet.
  - revert y H. induction HRet; intros.
    constructor; rewrite <- H, H0; reflexivity.
    eapply ReturnsTau. rewrite <- H0. eauto. eauto.
    eapply ReturnsVis. rewrite <- H0. eauto. eauto.
  - revert x H; induction HRet; intros ? EQ.
    constructor; rewrite EQ; eauto.
    eapply ReturnsTau. rewrite EQ. eauto. eauto.
    eapply ReturnsVis. rewrite EQ. eauto. eauto.
Qed.

Lemma Returns_Vis_sub :  forall {E} {R} X (e : E X) (k : X -> itree E R) u x, Returns u (k x) -> Returns u (Vis e k).
Proof.
  intros.
  eapply ReturnsVis. reflexivity. apply H.
Qed.

Lemma Returns_ret_inv_ : forall {E} A (a b : A) (t : itree E A), t ≅ (Ret b) -> Returns a t -> a = b.
Proof.
  intros E A a b t eq H. 
  revert b eq.
  induction H; intros; subst.
  - rewrite H in eq. apply Eq.eqit_Ret in eq. auto.
  - rewrite  H in eq. apply eqit_inv in eq. inv eq.
  - rewrite H in eq. symmetry in eq. apply eqit_inv in eq. inv eq.
Qed.

Lemma Returns_ret_inv :  forall {E} A (a b : A), Returns a ((ret b) : itree E A) -> a = b.
Proof.
  intros.
  eapply Returns_ret_inv_. reflexivity. cbn in H. apply H.
Qed.

Lemma eq_itree_Returns_ : forall {E} {R} (RR : R -> Prop) (ta : itree E R) 
    (IN: forall (a : R), Returns a ta -> RR a), eq_itree (fun u1 u2 => u1 = u2 /\ RR u1) ta ta.
Proof.
  intros E R.
  ginit.
  gcofix CIH; intros.

  setoid_rewrite (itree_eta ta) in IN.

  gstep. red.

  destruct (observe ta).
  - econstructor.  split; auto. apply IN. econstructor. reflexivity.
  - econstructor. gfinal. left. apply CIH. intros. eapply IN. eapply ReturnsTau; eauto.
    reflexivity.
  - econstructor. intros. red.
    gfinal. left. apply CIH. intros. eapply IN. eapply Returns_Vis_sub. apply H.
Qed.

Lemma eq_itree_Returns2_ : forall {E} {R' R} (RR : R -> Prop) (RR' : R' -> Prop) (ta : itree E R) (ta' : itree E R') RU
    (IN1: forall (a : R'), Returns a ta' -> RR' a)
    (IN2: forall (a : R), Returns a ta -> RR a),
    eq_itree RU ta ta' ->
    eq_itree (fun u1 u2 => RU u1 u2 /\ RR u1 /\ RR' u2) ta ta'.
Proof.
  intros E R.
  ginit.
  gcofix CIH; intros.

  setoid_rewrite (itree_eta ta) in IN2.
  setoid_rewrite (itree_eta ta') in IN1.
  setoid_rewrite (itree_eta ta) in H0.
  setoid_rewrite (itree_eta ta') in H0.

  gstep. red.

  remember (observe ta); remember (observe ta').

  punfold H0. red in H0. cbn in *.
  revert ta ta' Heqi0 Heqi.
  induction H0.
  - econstructor.  split; auto. constructor;
    [apply IN2 | apply IN1]; econstructor; reflexivity.
  - econstructor. gfinal. left. apply CIH.
    intros. eapply IN1. eapply ReturnsTau; eauto; reflexivity.
    intros. eapply IN2. eapply ReturnsTau; eauto; reflexivity.
    pclearbot; eauto.
  - econstructor. intros. red.
    gfinal. left. apply CIH. intros. eapply IN1. eapply Returns_Vis_sub. apply H.
    intros. eapply IN2. eapply Returns_Vis_sub. apply H.
    pclearbot. eauto.

  - inv CHECK.
  - inv CHECK.
Qed.


Lemma Returns_impl_image {E A}:
  forall (ma : itree E A) (x y : A), x = y /\ Returns x ma -> image ma x y.
Proof.
  intro.
  intros. destruct H. subst. red.
  induction H0.
  - repeat intro; subst.
    rewrite H in EQR.
    apply eqit_inv_Ret in EQR. auto.
  - repeat intro.
    apply IHReturns. eauto.
    rewrite H in EQR. apply eqit_inv in EQR. cbn in *. auto.
  - repeat intro.
    apply IHReturns. eauto. rewrite H in EQR.
    red in EQR. red in EQR.
    eapply eqit_inv_Vis in EQR. apply EQR.
Qed.

Lemma Returns_eq_rel_image :
  forall E A (ma : itree E A), eq_rel (fun (x y : A) =>  x = y /\ Returns x ma) (fun x y => image ma x y).
Proof.
  intros; split; intros.
  - intro. apply Returns_impl_image.
  - repeat intro. apply H. split. red; intros; intuition; subst; eauto.
    red. intros. destruct H0, H1. subst; split; intuition.
    apply eq_itree_Returns_. auto.
Qed.

Lemma Returns_mayRet :
  forall E A (ma : itree E A) (a : A),
    a ∈ ma <-> Returns a ma.
Proof.
  intros; split; intros.
  - eapply proj2. Unshelve.
    2 : exact (a = a). pose proof Returns_eq_rel_image.
    unfold eq_rel in H0. specialize (H0 E A ma). destruct H0.
    apply H1. apply H.
  - apply Returns_eq_rel_image. split; auto.
Qed.


Lemma observe_eutt {E A}:
  forall (ma : itree E A) t,
    observe ma = t -> ma ≈ go t.
Proof.
  intros. rewrite itree_eta.
  destruct (observe ma) eqn : Hma.
  all : subst; reflexivity.
Qed.

Lemma observe_eqitree {E A}:
  forall (ma : itree E A) t,
    observe ma = t -> ma ≅ go t.
Proof.
  intros. rewrite itree_eta.
  destruct (observe ma) eqn : Hma.
  all : subst; reflexivity.
Qed.

Lemma eq_itree_bind_inv {E} :
  forall A B (ma : itree E A) (k k' : A -> itree E B) R,
  bind ma k ≈{R} bind ma k' ->
  forall a, a ∈ ma -> exists a', a' ∈ ma /\ k a ≈{R} k' a'.
Proof.
  intros.
  exists a. split; auto.
  pose proof @eqit_Vis.
  cbn in H.
  rewrite Returns_mayRet in H0.
  revert k k' H.
  induction H0; intros.
  + rewrite <- bind_ret_l. cbn.
    setoid_rewrite <- bind_ret_l at 3.
    rewrite <- H. auto.
  + rewrite H in H2. do 2 rewrite bind_tau in H2.
    apply eqit_inv in H2. cbn in H2. apply IHReturns; auto.
  + rewrite H in H2. do 2 rewrite bind_vis in H2.
    eapply eqit_inv_Vis in H2. eapply IHReturns; eauto.
Qed.

Lemma eq_itree_bind_inv_homog {E} :
  forall A B (ma : itree E A) (k k': A -> itree E B) R,
  bind ma k ≈{R} bind ma k' ->
  forall a, a ∈ ma -> k a ≈{R} k' a.
Proof.
  intros.
  pose proof @eqit_Vis.
  cbn in H.
  rewrite Returns_mayRet in H0.
  induction H0.
  + rewrite <- bind_ret_l. cbn.
    rewrite <- H0. rewrite H0 in H. rewrite !bind_ret_l in H.
    rewrite H0. rewrite bind_ret_l. auto.
  + rewrite H0 in H. do 2 rewrite bind_tau in H. apply eqit_inv in H.
    cbn in H.
    apply IHReturns; auto.
  + rewrite H0 in H. do 2 rewrite bind_vis in H.
    eapply eqit_inv_Vis in H. eapply IHReturns; eauto.
Qed.

Lemma mayRet_eq_Refl_ITree:
  forall E A (ma : itree E A), ma ≈{ fun a1 a2 => a1 = a2 /\ a1 ∈ ma } ma.
Proof.
  intros. eapply itree_eq_itree_Proper.
  Unshelve.
  3 : exact (fun a1 a2 => a1 = a2 /\ Returns a1 ma).
  red. split; repeat intro.
  crunch; eauto. rewrite Returns_mayRet in H0. auto.
  crunch; eauto. rewrite <- Returns_mayRet in H0. auto.
  apply eq_itree_Returns_. intros; eauto.
Qed.

Lemma mayRet_eq_Refl_ITree2:
  forall E A (ma : itree E A), ma ≈{ fun a1 a2 => a1 = a2 /\ a1 ∈ ma /\ a2 ∈ ma } ma.
Proof.
  intros. eapply itree_eq_itree_Proper.
  Unshelve.
  3 : exact (fun a1 a2 => a1 = a2 /\ Returns a1 ma /\ Returns a2 ma).
  red. split; repeat intro.
  crunch; eauto. rewrite Returns_mayRet in H0. auto.
  crunch; eauto. rewrite Returns_mayRet in H1. auto.
  crunch; eauto. rewrite <- Returns_mayRet in H0. auto.
  rewrite <- Returns_mayRet in H1. auto.
  apply eq_itree_Returns2_. all : intros; eauto. reflexivity.
Qed.


Lemma image_ma_Refl_ITree:
  forall E A (ma : itree E A), ma ≈{ image ma } ma.
Proof.
  intros. eapply itree_eq_itree_Proper_mono.
  Unshelve.
  3 : exact (fun a1 a2 => a1 = a2 /\ Returns a1 ma).
  2 : apply eq_itree_Returns_; intros; eauto.
  red. repeat intro.  destruct H. subst.
  eapply Returns_impl_image; eauto.
Qed.

Lemma ret_eq_itree_L:
  forall E A B (a : A) (mb : itree E B) (R: relationH A B),
    Ret a ≈{ R } mb -> exists (b : B), mb ≅ Ret b /\ R a b.
Proof.
  intros.
  repeat red in H.
  punfold H. red in H.
  remember (Ret a) as tl.
  genobs tl otl.
  genobs mb otr.
  revert Heqotr.
  rewrite Heqtl in Heqotl.
  clear Heqtl. revert Heqotl.
  clear tl. revert mb.
  induction H.
  - intros.
    exists r2. repeat red. split. pstep. red. cbn. rewrite <- Heqotr.
    constructor; auto.
    inversion Heqotl. subst. auto.
  - intros. subst. inversion Heqotl.
  - intros. subst. inversion Heqotl.
  - intros; subst; inversion Heqotl.
  - intros. apply simpobs in Heqotr.
    setoid_rewrite Heqotr.
    assert ((exists b : B, t2 ≈ Ret b /\ R a b) -> exists b: B, Tau t2 ≈ Ret b /\ R a b).
    intro. destruct H0. exists x. destruct H0. split. rewrite H0. repeat red. pstep; red.
    constructor. auto. constructor; reflexivity. auto. inv CHECK.
Qed.

Lemma ret_eq_itree_R:
  forall E A B (b : B) (ma : itree E A) (R: relationH A B),
    ma ≈{ R } Ret b -> exists (a : A), ma ≅ Ret a /\ R a b.
Proof.
  intros.
  repeat red in H.
  punfold H. red in H.
  remember (Ret b) as tl.
  genobs tl otl.
  genobs ma otr.
  revert Heqotr.
  rewrite Heqtl in Heqotl.
  clear Heqtl. revert Heqotl.
  clear tl. revert ma.
  induction H.
  - intros.
    exists r1. repeat red. split. pstep. red. cbn. rewrite <- Heqotr.
    constructor; auto.
    inversion Heqotl. subst. auto.
  - intros. subst. inversion Heqotl.
  - intros. subst. inversion Heqotl.
  - inv CHECK.
  - inv CHECK.
Qed.

Lemma vis_eq_itree_L:
  forall E A B X (e : E X) (k : X -> itree E A) (mb : itree E B) (R: relationH A B),
    Vis e k ≈{ R } mb -> exists (k' : X -> itree E B), mb ≅ Vis e k'.
Proof.
  intros.
  repeat red in H.
  punfold H. red in H.
  remember (Vis e k) as tl.
  genobs tl otl.
  genobs mb otr.
  revert Heqotr.
  rewrite Heqtl in Heqotl.
  clear Heqtl. revert Heqotl.
  clear tl. revert mb. revert e k.
  induction H.
  - intros; subst; inversion Heqotl.
  - intros; subst; inversion Heqotl.
  - intros. red in REL. cbn in Heqotl. inversion Heqotl.
    subst. dependent destruction H2. dependent destruction H1.
    exists k2. rewrite Heqotr. rewrite <- itree_eta. reflexivity.
  - intros; subst; inversion Heqotl.
  - inv CHECK.
Qed.

Lemma vis_eq_itree_R:
  forall E A B X (e : E X) (k : X -> itree E B) (ma : itree E A) (R: relationH A B),
    ma ≈{ R } Vis e k -> exists (k' : X -> itree E A), ma ≅ Vis e k'.
Proof.
  intros.
  repeat red in H.
  punfold H. red in H.
  remember (Vis e k) as tl.
  genobs tl otl.
  genobs ma otr.
  revert Heqotr.
  rewrite Heqtl in Heqotl.
  clear Heqtl. revert Heqotl.
  clear tl. revert ma. revert e k.
  induction H.
  - intros; subst; inversion Heqotl.
  - intros; subst; inversion Heqotl.
  - intros. red in REL. cbn in Heqotl. inversion Heqotl.
    subst. dependent destruction H2. dependent destruction H1.
    exists k1. rewrite Heqotr. rewrite <- itree_eta. reflexivity.
  - inv CHECK.
  - inv CHECK.
Qed.

Lemma ret_mayRet : forall E A (x : A), x ∈ ret (m := itree E) x.
Proof.
  repeat intro. eapply eqit_inv_Ret in EQR; auto.
Qed.

#[global]
Instance eqmR_mayRet_l_ITree {E}: MayRetL (itree E).
Proof.
  red.
  intros* EQ a1 IN.
  rewrite Returns_mayRet in IN.
  revert EQ. revert RA ma2.
  induction IN.
  - intros.
    assert (Ret a1 ≈{ RA } ma2). {
      rewrite <- H. auto.
    }
    apply ret_eq_itree_L in H0. destruct H0.
    exists x. destruct H0. split; auto. repeat intro. rewrite H0 in EQR. apply eqit_inv_Ret in EQR. auto.
  - intros. rewrite H in EQ. apply eqit_inv in EQ. cbn in EQ.
    destruct (_observe ma2) eqn: Hma2; try solve [inv EQ].
    specialize (IHIN _ _ EQ). symmetry in Hma2. apply simpobs in Hma2.
    crunch. eexists. split; eauto. apply Returns_mayRet.
    eapply ReturnsTau; eauto. apply Returns_mayRet in H1. auto.
  - intros.
    assert (Vis e k ≈{ RA } ma2). {
      rewrite <- H. auto.
    } clear EQ H. assert (EQ := H0).
    apply vis_eq_itree_L in H0. destruct H0.
    assert (Vis e k ≈{RA} Vis e x0).
    rewrite <- H. auto.
    eapply eqit_inv_Vis with (u := x)in H0.
    specialize (IHIN RA (x0 x) H0).
    destruct IHIN as (? & ? & ?).
    exists x1. split; auto. rewrite Returns_mayRet. rewrite H. eapply ReturnsVis.
    reflexivity. rewrite <- Returns_mayRet. eauto.
Qed.

#[global]
Instance eqmR_mayRet_r_ITree {E}: MayRetR (itree E).
Proof.
  red. intros* EQ a2 IN.
  rewrite Returns_mayRet in IN.
  revert EQ. revert RA ma1.
  induction IN.
  - intros.
    assert (ma1 ≈{ RA } Ret a2). {
      rewrite <- H. auto.
    }
    apply ret_eq_itree_R in H0. destruct H0.
    exists x. destruct H0. split; auto. repeat intro. rewrite H0 in EQR. apply eqit_inv_Ret in EQR.
    auto.
  - intros. rewrite H in EQ. apply eqit_inv in EQ. cbn in EQ.
    destruct (_observe ma1) eqn: Hma1; try solve [inv EQ].
    specialize (IHIN _ _ EQ). symmetry in Hma1. apply simpobs in Hma1.
    crunch. eexists. split; eauto. apply Returns_mayRet.
    eapply ReturnsTau; eauto. apply Returns_mayRet in H1. auto.
  - intros.
    assert (ma1 ≈{ RA } Vis e k). {
      rewrite <- H. auto.
    } clear EQ H. assert (EQ := H0).
    apply vis_eq_itree_R in H0. destruct H0.
    assert (Vis e x0 ≈{RA} Vis e k).
    rewrite <- H. auto.
    eapply eqit_inv_Vis with (u := x) in H0.
    specialize (IHIN RA (x0 x) H0).
    destruct IHIN as (? & ? & ?).
    exists x1. split; auto. rewrite Returns_mayRet. rewrite H. eapply ReturnsVis.
    reflexivity. rewrite <- Returns_mayRet. eauto.
Qed.

Lemma eq_itree_prod_rel {E}:
  forall (A B : Type)
    (RA : relationH A A) (RB : relationH B B) (ma : itree E (A * B)),
  eq_itree RA (fst <$> ma) (fst <$> ma) -> eq_itree RB (snd <$> ma) (snd <$> ma) -> eq_itree (prod_rel RA RB) ma ma.
Proof.
  intros until RB.
  ginit. gcofix CIH.
  intros * H_fst H_snd.
  rewrite itree_eta.
  genobs ma oma.
  destruct (observe ma) eqn: EQma; subst; intros; pclearbot; simpl.
  - assert (ma ≅ Ret r0). {
      repeat red. pstep. red. rewrite EQma. constructor. auto.
    }
    rewrite H in H_fst, H_snd. cbn in *. unfold ITree.map in *.
    rewrite bind_ret_l in H_fst. rewrite bind_ret_l in H_snd.
    apply eqit_inv_Ret in H_fst.
    apply eqit_inv_Ret in H_snd.
    destruct r0. gstep. constructor. split; auto.
  - assert (ma ≅ Tau t). {
      repeat red. pstep. red. rewrite EQma. constructor.
      assert (t ≅ t) by reflexivity.
      left. apply H.
    }
    gstep.
    constructor. gfinal. left.
    rewrite H in H_fst, H_snd. unfold fmap in H_snd, H_fst.
    setoid_rewrite bind_tau in H_snd.
    setoid_rewrite bind_tau in H_fst.
    apply eqit_inv in H_snd, H_fst; cbn in H_snd, H_fst. eauto.
  - assert (ma ≅ Vis e k). {
      repeat red. pstep. red. rewrite EQma. constructor.
      intros. red. left.
      assert (k v ≅ k v) by reflexivity.
      apply H.
    }
    clear EQma.
    gstep. constructor. intros. gfinal. left.
    eapply CIH.
    rewrite H in H_fst, H_snd. cbn in *. unfold ITree.map in *.
    rewrite bind_vis in H_fst. rewrite bind_vis in H_snd.
    repeat red in H_fst. punfold H_fst. inv H_fst.
    dependent destruction H2.
    dependent destruction H3.
    dependent destruction H4.
    dependent destruction H5.
    red in REL. specialize (REL v). destruct REL.
    punfold H0. inv H0.

    rewrite H in H_fst, H_snd. cbn in *. unfold ITree.map in *.
    rewrite bind_vis in H_snd.
    repeat red in H_snd. punfold H_snd. inv H_snd.
    dependent destruction H2.
    dependent destruction H3.
    dependent destruction H4.
    dependent destruction H5.
    red in REL. specialize (REL v). destruct REL.
    punfold H0. inv H0.
Qed.

Lemma eq_itree_prod_rel_homo' {E}:
  forall (A B : Type)
    (RA : relationH A A) (RB : relationH B B)
    (ma ma' : itree E (A * B)),
    ma ≅ ma' ->
    eq_itree RA (fst <$> ma) (fst <$> ma') ->
    eq_itree RB (snd <$> ma) (snd <$> ma') ->
    eq_itree (prod_rel RA RB) ma ma'.
Proof.
  intros. rewrite H in *. apply eq_itree_prod_rel; auto.
Qed.

#[global]
Instance eqmR_prod_rel_ITree {E} : RelProd (itree E).
Proof.
  intros until RB.
  ginit. gcofix CIH.
  intros * EQ EQ'.
  rewrite itree_eta, (itree_eta m2).
  punfold EQ; red in EQ.
  remember (fst <$> m1) eqn: P; remember (fst <$> m2) eqn: P'.
  assert (Q: fst <$> m1 ≅ i) by (subst; reflexivity).
  assert (Q': fst <$> m2 ≅ i0) by (subst; reflexivity).
  clear P P'.
  genobs i ot; genobs i0 os.
  hinduction EQ before CIH; intros; pclearbot; simpl.
  - apply simpobs in Heqot, Heqos.
    unfold fmap in *. subst. rewrite <- Q in Heqot. rewrite <- Q' in Heqos.
    apply eqit_inv_bind_ret in Heqot, Heqos. crunch.
    rewrite H0, H in EQ'. gfinal. right.
    apply eqit_inv in H1, H2. cbn in *. subst. rewrite! bind_ret_l in EQ'.
    apply eqit_inv in EQ'. cbn in *. subst. destruct x, x0.
    eapply eqit_inv in H, H0; cbn in *. unfold observe.
    destruct (_observe m1), (_observe m2); try contradiction.
    pstep. constructor.  subst. auto.
  - symmetry in Heqot, Heqos.
    apply observe_eqitree in Heqot, Heqos.
    unfold fmap in Heqot, Heqos.
    rewrite <- Q in Heqot.
    rewrite <- Q' in Heqos.
    apply eqitree_inv_bind_tau in Heqot. crunch.
    2 : { punfold H0. inv H0. inv CHECK. }
    apply eqitree_inv_bind_tau in Heqos. crunch.
    2 : { punfold H2. inv H2. inv CHECK. }
    rewrite H, H1.
    gstep. constructor. gbase; eapply CIH; eauto.
    rewrite H0, H2. auto.
    rewrite H, H1 in EQ'.
    unfold fmap in EQ'. setoid_rewrite bind_tau in EQ'. apply eqit_inv in EQ'.
     eauto.
  - symmetry in Heqot, Heqos. apply observe_eqitree in Heqot, Heqos.
    rename Heqot into H. rename Heqos into H0.
    rewrite <- Q in H; rewrite <- Q' in H0.
    apply eqitree_inv_bind_vis in H. crunch.
    2 : { punfold H1. inv H1. }
    apply eqitree_inv_bind_vis in H0. crunch.
    2 : { punfold H2. inv H2. }
    rewrite H, H0. gstep. constructor. intros. gbase.
    apply CIH; auto.
    unfold fmap. setoid_rewrite H1. setoid_rewrite H2.
    apply REL.
    rewrite H, H0 in EQ'.
    unfold fmap in EQ'. setoid_rewrite bind_vis in EQ'.
    eapply eqit_inv_Vis in EQ'. cbn in *. crunch.
    eauto.
  - inv CHECK.
  - inv CHECK.
Qed.

#[global]
Instance eqmR_prod_fst_inv_ITree {E}: FmapFst (itree E).
Proof.
  repeat intro. unfold fmap.
  red in H. cbn. eapply eq_itree_clo_bind; eauto.
  intros.
  apply eqit_Ret. destruct u1, u2; inv H0; eauto.
Qed.

#[global]
Instance eqmR_prod_snd_inv_ITree {E}: FmapSnd (itree E).
Proof.
  repeat intro. unfold fmap.
  red in H. eapply eq_itree_clo_bind; eauto.
  intros.
  apply eqit_Ret. destruct u1, u2; inv H0; eauto.
Qed.


#[global]
Instance eqmR_sum_inl_ITree {E}: FmapInl (itree E).
Proof.
  repeat intro. unfold fmap.
  red in H. eapply eq_itree_clo_bind; eauto.
  intros.
  apply eqit_Ret. constructor; eauto.
Qed.

#[global]
Instance eqmR_sum_inr_ITree {E}: FmapInr (itree E).
Proof.
  repeat intro. unfold fmap.
  red in H. eapply eq_itree_clo_bind; eauto.
  intros.
  apply eqit_Ret. constructor; eauto.
Qed.

#[global]
Instance fmap_inv_ITree' {E}: FmapInv_mayRet (itree E).
Proof.
  intros until ma2.
  remember (fun a a' => mayRet_rel (itree E) ma1 ma2 a a' /\ R (f1 a) (f2 a')) as QQ.
  assert ((fun a a' => mayRet_rel (itree E) ma1 ma2 a a' /\ R (f1 a) (f2 a')) ⊑ QQ).
  { subst; eauto. repeat intro; eauto. }
  clear HeqQQ. rename H into HeqQQ.
  revert ma1 ma2 HeqQQ.
  ginit. gcofix CIH.
  intros * ? EQ. intros.

  rewrite itree_eta, (itree_eta ma2).
  punfold EQ; red in EQ.
  remember (f1 <$> ma1) eqn: P; remember (f2 <$> ma2) eqn: P'.
  assert (Q: f1 <$> ma1 ≅ i) by (subst; reflexivity).
  assert (Q': f2 <$> ma2 ≅ i0) by (subst; reflexivity).
  clear P P'.
  genobs i ot; genobs i0 os.
  hinduction EQ before CIH; intros; pclearbot; simpl.
  - symmetry in Heqot; symmetry in Heqos.
    apply observe_eqitree in Heqot, Heqos.
    unfold fmap in *. subst. rewrite <- Q in Heqot. rewrite <- Q' in Heqos.
    apply eqitree_inv_bind_ret in Heqot, Heqos. crunch.
    rewrite H0 in Q. rewrite H in Q'.
    rewrite H0, H. gstep. constructor.
    apply HeqQQ. split. red.
    rewrite!Returns_mayRet. rewrite H0, H.
    split; constructor; reflexivity.
    apply eqit_inv in H1, H2 ; cbn in *. subst; auto.
  - symmetry in Heqot, Heqos.
    apply observe_eqitree in Heqot, Heqos.
    unfold fmap in Heqot, Heqos.
    rewrite <- Q in Heqot.
    rewrite <- Q' in Heqos.
    apply eqitree_inv_bind_tau in Heqot. crunch.
    2 : { punfold H0. inv H0. inv CHECK. }
    apply eqitree_inv_bind_tau in Heqos. crunch.
    2 : { punfold H2. inv H2. inv CHECK. }
    rewrite H, H1.
    gstep; constructor. gbase. eapply CIH; eauto; cycle 1.
    rewrite H0, H2. auto. subst.
    unfold mayRet_rel. repeat intro.
    apply HeqQQ. crunch; eauto. red.
    rewrite!Returns_mayRet.
    rewrite H, H1. split; eapply ReturnsTau;
    rewrite Returns_mayRet in H3, H5;
    eauto; reflexivity.
  - symmetry in Heqot, Heqos. apply observe_eqitree in Heqot, Heqos.
    rename Heqot into H. rename Heqos into H0.
    rewrite <- Q in H; rewrite <- Q' in H0.
    apply eqitree_inv_bind_vis in H. crunch.
    2 : { punfold H1. inv H1. }
    apply eqitree_inv_bind_vis in H0. crunch.
    2 : { punfold H2. inv H2. }
    rewrite H, H0. gstep. constructor.  gbase.
    intros; apply CIH; auto; cycle 1.
    unfold fmap. setoid_rewrite H1. setoid_rewrite H2.
    specialize (REL v). red. apply REL.
    repeat intro; unfold mayRet_rel in *.
    apply HeqQQ.
    crunch; auto.
    apply Returns_mayRet in H3, H5.
    crunch; apply Returns_mayRet; eapply ReturnsVis; eauto; try reflexivity.
    apply Returns_mayRet in H3, H5.
    crunch; apply Returns_mayRet; eapply ReturnsVis; eauto; try reflexivity.
  - inv CHECK.
  - inv CHECK.
Qed.

#[global]
Instance eqmR_sum_rel_ITree {E}: RelSum (itree E).
Proof.
  repeat intro; split; intros; [red in H; unfold fmap|].
  - eapply eq_itree_clo_bind; eauto.
    intros. apply eqit_Ret. destruct u1, u2; try inv H2.
    apply H0; auto. apply H1; auto.
  - specialize (H (A1 + B1)%type (A2 + B2)%type inl inl inr inr (RA ⊕ RB)).
    assert (inl_P: ProperH (respectfulH A1 A2 (A1 + B1) (A2 + B2) RA (RA ⊕ RB)) inl inl) by
      (repeat intro; constructor; auto).
    assert (inr_P: ProperH (respectfulH B1 B2 (A1 + B1) (A2 + B2) RB (RA ⊕ RB)) inr inr) by
      (repeat intro; constructor; auto).
    specialize (H inl_P inr_P).
    apply fmap_inv_ITree' in H. eapply itree_eq_itree_Proper_mono; eauto.
    repeat intro; crunch; eauto.
    destruct x, y; eauto.
Qed.

#[global]
Lemma eqmR_prod_sum_rel_ITree {E}:
  forall (A B C : Type)
    (RA : relationH A A) (RB : relationH B B) (RC : relationH C C)
    (ma ma' : itree E (C + A * B)%type),
    (fst_sum <$> ma) ≈{ RC ⊕ RA } (fst_sum <$> ma') ->
    (snd_sum <$> ma) ≈{ RC ⊕ RB } (snd_sum <$> ma') -> ma ≈{ RC ⊕ RA ⊗ RB } ma'.
Proof.
  intros until RC.
  ginit. gcofix CIH.
  intros * EQ EQ'.
  rewrite itree_eta, (itree_eta ma').
  punfold EQ; red in EQ.
  remember (fst_sum <$> ma) eqn: P; remember (fst_sum <$> ma') eqn: P'.
  assert (Q: fst_sum <$> ma ≅ i) by (subst; reflexivity).
  assert (Q': fst_sum <$> ma' ≅ i0) by (subst; reflexivity).
  clear P P'.
  genobs i ot; genobs i0 os.
  hinduction EQ before CIH; intros; pclearbot; simpl.
  - apply simpobs in Heqot, Heqos.
    unfold fmap in *. subst. rewrite <- Q in Heqot. rewrite <- Q' in Heqos.
    apply eqit_inv_bind_ret in Heqot, Heqos. crunch.
    rewrite H0, H in EQ'. apply eqit_inv in H0, H2, H; cbn in *; try contradiction.
    unfold observe. destruct (_observe ma), (_observe ma'); try contradiction. subst.
    gstep. unfold ITree.map in *. do 2 rewrite bind_ret_l in EQ'.
    apply eqit_inv in H1, EQ'. cbn in *. subst.
    clear Q Q'.
    constructor. inv REL.
    all : unfold fst_sum, snd_sum in *; destruct x0 eqn: Hx0; destruct x eqn: Hx.
    all : repeat match goal with
          | [H : _ = inl _  |- _] => inv H
          | [H : _ = inr _ |- _] => inv H
          end; eauto.
    all : constructor; eauto; cbn in *.
    destruct p, p0. constructor; eauto. cbn in *; eauto. inv EQ'. auto.
  - apply simpobs in Heqot, Heqos.
    unfold fmap in Heqot, Heqos.
    rewrite <- Q in Heqot.
    rewrite <- Q' in Heqos.
    apply eqitree_inv_bind_tau in Heqot. crunch.
    2 : { punfold H0. inv H0. inv CHECK. }
    apply eqitree_inv_bind_tau in Heqos. crunch.
    2 : { punfold H2. inv H2. inv CHECK. }
    rewrite H, H1.
    gstep; constructor. gbase. eapply CIH; eauto.
    rewrite H0, H2. auto.
    rewrite H, H1 in EQ'. unfold fmap in EQ'. setoid_rewrite bind_tau in EQ'.
    apply eqit_inv in EQ'. cbn in *; auto.
  - symmetry in Heqot, Heqos. apply observe_eqitree in Heqot, Heqos.
    rename Heqot into H. rename Heqos into H0.
    rewrite <- Q in H; rewrite <- Q' in H0.
    apply eqitree_inv_bind_vis in H. crunch.
    2 : { punfold H1. inv H1. }
    apply eqitree_inv_bind_vis in H0. crunch.
    2 : { punfold H2. inv H2. }
    rewrite H, H0. gstep. constructor. gbase. intros. eapply CIH; auto.
    + unfold fmap. setoid_rewrite H1. setoid_rewrite H2. auto.
      rewrite H, H0 in EQ'.
      unfold fmap in EQ'. setoid_rewrite bind_vis in EQ'.
      eapply eqit_inv_Vis in EQ'. eapply REL.
    + rewrite H, H0 in EQ'. unfold fmap in EQ'. setoid_rewrite bind_vis in EQ'.
      eapply eqit_inv_Vis in EQ'. cbn in *. eauto.
  - inv CHECK.
  - inv CHECK.
    Unshelve. auto.
Qed.

Global Instance eqmR_transport_Equiv_itree {E} : TransportEquiv (itree E).
Proof.
  repeat intro. typeclasses eauto.
Qed.

Global Instance EqmR_OK_ITree {E} : EqmR_OK (itree E).
Proof.
  split; try typeclasses eauto; unfold eqmR, EqmR_ITree.
Qed.

#[global]
Instance eqmR_bind_ProperH_ITree {E}: ProperBind (itree E).
Proof.
  red.
  intros.
  pose proof (H).
  eapply eqmR_rel_comp in H. 2 : typeclasses eauto.
  Unshelve. 3 : exact (fun a1 a2 => a1 = a2 /\ a1 ∈ ma2).
  eapply eq_itree_clo_bind.
  apply H.
  apply mayRet_eq_Refl_ITree.
  intros. destruct H2 as (? & ? & ?). destruct H3. subst.
  apply H0. auto.
Qed.

#[global]
Instance bind_ret_l_ITree {E}: BindRetL (itree E).
Proof.
  red. intros *. red. setoid_rewrite bind_ret_l. reflexivity.
Qed.

#[global]
Instance bind_ret_r_ITree {E}: BindRetR (itree E).
Proof.
  red. intros *. red. setoid_rewrite bind_ret_r. reflexivity.
Qed.

#[global]
Instance bind_bind_ITree {E}: BindBind (itree E).
Proof.
  red. intros *. red. setoid_rewrite bind_bind. reflexivity.
Qed.

#[global]
Instance eqmR_ret_ITree {E}: RetFinal (itree E).
Proof.
  red. intros *. apply eqit_Ret.
Qed.

Global Instance EqmRMonad_ITree {E} : EqmRMonadLaws (itree E).
Proof.
  split; try typeclasses eauto.
  repeat intro. eapply image_ma_Refl_ITree.
Qed.

#[global]
Instance eqmR_ret_inv_itree {E}: RetInv (itree E).
Proof.
  red; intros; eapply eqit_inv_Ret; eauto. apply H.
Qed.

#[global]
Instance mayRet_bind_inv_itree {E}: MayRetBindInv (itree E).
Proof.
  red.
  intros.
  rewrite Returns_mayRet in H.
  remember (x <- ma;; k x).
  assert (i ≅ x <- ma ;; k x) by (subst; reflexivity). clear Heqi.
  revert ma k H0.
  induction H; intros.
  - rewrite H in H0. symmetry in H0. apply eqit_inv_bind_ret in H0.
    crunch. exists x. rewrite! Returns_mayRet.
    split; [rewrite H0|rewrite H1]; constructor; reflexivity.
  - rewrite H in H1. symmetry in H1. apply eqit_inv_bind_tau in H1; crunch.
    + symmetry in H2. specialize (IHReturns _ _ H2). crunch.
      eexists; split; eauto. apply Returns_mayRet.
      rewrite Returns_mayRet in H3, H4. rewrite H1. eapply ReturnsTau; eauto.
      reflexivity.
    + eapply eqit_inv in H2. cbn in H2.
      destruct (_observe (k x)) eqn: Hk; try contradiction.
      assert (u ≅ Ret x ;; t0).
      rewrite <- H2. setoid_rewrite bind_ret_l. reflexivity.
      specialize (IHReturns _ _ H3). crunch; eauto.
      exists x0. split; eauto. rewrite H1; auto.
      apply Returns_mayRet in H4.
      inv H4; apply eqit_inv in H6; cbn in *; try contradiction; subst.
      apply Returns_mayRet. symmetry in Hk. eapply simpobs in Hk.
      eapply ReturnsTau; eauto. apply Returns_mayRet in H5. auto.
  - rewrite H in H1. clear H. symmetry in H1. apply eqit_inv_bind_vis in H1; crunch.
    + edestruct IHReturns.
      rewrite <- H1. eapply eq_itree_clo_bind; intros; subst; try reflexivity. subst. reflexivity.
      crunch; esplit; split; eauto.
      rewrite H. apply Returns_mayRet. eapply ReturnsVis. reflexivity.
      apply Returns_mayRet in H2. eauto.
    + exists x0. split. rewrite H. apply Returns_mayRet. constructor; reflexivity.
      rewrite H1. eapply ReturnsVis in H0. apply Returns_mayRet. eauto. reflexivity.
Qed.

#[global]
Instance fmap_inv_mayRet_itree {E}: FmapInvRet (itree E).
Proof.
  red. intros. unfold fmap in H. eapply eq_itree_bind_inv_homog in H; eauto.
Qed.

#[global]
Instance _eqmR_inv' {E}: EqmRInv (itree E).
Proof.
  repeat intro.
  rewrite <- (Eq.bind_ret_r ma) in H.
  eapply @eq_itree_bind_inv_homog in H; eauto.
  eapply eqit_inv in H; eauto.
Qed.


Global Instance EqmRMonadInverses_ITree {E} : EqmRInversionProperties (itree E).
Proof.
  constructor;try typeclasses eauto.
Qed.

Global Instance EQM_ITree {E} : EQM (itree E) _.
Proof.
  econstructor;typeclasses eauto.
Qed.
