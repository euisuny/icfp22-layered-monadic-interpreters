(** *EqmR-related laws for the itree monad with weak bisimulation. *)
(* This file provides the instances for eqmR-related laws for the itree monad
 with weak bisimulation, [eutt]. *)

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
     Basics.Tacs Eq Eq.Eq
     Core.ITreeDefinition
     Eq.Eq Eq.UpToTaus
     EqmR.EqmRMonad
     EqmR.EqmRMonadT.

Import FunctorNotation.
Import CatNotations.
Import MonadNotation.
Import RelNotations.
Local Open Scope monad_scope.
Local Open Scope cat_scope.
Local Open Scope relationH_scope.
(* end hide *)

#[global]
Instance EqmR_ITree {E} : EqmR (itree E) := {| eqmR := (fun a b => eutt) |}.

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
repeat intro; eapply eutt_conj; eauto.
Defined.

#[global]
Instance itree_transport_PER_ {E}: TransportPER (itree E).
Proof.
  intros. split. unfold SymmetricH, relationH in *. intros.
  red. apply Symmetric_eqit. red. apply H.
  apply H0.
  intros. unfold TransitiveH, relationH in *. intros.
  red. eapply Transitive_eqit. red. apply H. apply H0. apply H1.
Defined.

#[global]
Instance itree_rel_comp {E} : RelComp (itree E).
Proof.
  red.
  intros until C. unfold eutt in *.
  intros R1 R2 ma mb mc HR1 HR2. intros.
  setoid_rewrite <- compose_rcompose_equiv.
  eapply eqit_trans; eassumption.
Defined.

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
      eapply IHH'. eassumption.
      reflexivity.
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
Defined.

#[global]
Instance itree_eutt_Proper {E}:
  forall A B : Type, Proper (eq_rel (A := A) (B := B) ==> eq_rel) (eutt (E :=E)).
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
      eapply IHH'. eassumption.
      reflexivity.
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
    * constructor. assumption. eapply IHH'. eassumption. 
      reflexivity. 
    * constructor. assumption. eapply IHH'.
      reflexivity.
      eassumption.
Defined.

#[global]
Instance itree_eutt_Proper_mono {E}:
  forall A B : Type, Proper (subrelationH (A:=A) (B:=B) ==> subrelationH (B:=itree E B)) eutt.
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
| ReturnsRet: forall t, t ≈ Ret a -> Returns a t
| ReturnsTau: forall t u, t ≈ Tau u -> Returns a u -> Returns a t
| ReturnsVis: forall {X} (e: E X) (x: X) t k, t ≈ Vis e k -> Returns a (k x) -> Returns a t
.

Global Instance Returns_eutt {E A} a: Proper (eutt eq ==> iff) (@Returns E A a).
Proof.
  repeat intro; split; intros HRet.
  - revert y H. induction HRet; intros.
    constructor; rewrite <- H, H0; reflexivity.
    apply IHHRet, eqit_inv_Tau_l; auto.
    rewrite <- H0. rewrite H. reflexivity.
    econstructor 3; [rewrite <- H0, H; reflexivity | apply IHHRet; reflexivity].
  - revert x H; induction HRet; intros ? EQ.
    constructor; rewrite EQ; eauto.
    apply IHHRet, eqit_inv_Tau_r; auto.
    rewrite EQ. rewrite <- H. reflexivity.
    econstructor 3; [rewrite EQ, H; reflexivity | apply IHHRet; reflexivity].
Defined.

Lemma Returns_Vis_sub :  forall {E} {R} X (e : E X) (k : X -> itree E R) u x, Returns u (k x) -> Returns u (Vis e k).
Proof.
  intros.
  eapply ReturnsVis. reflexivity. apply H.
Qed.

Lemma Returns_ret_inv_ : forall {E} A (a b : A) (t : itree E A), t ≈ (Ret b) -> Returns a t -> a = b.
Proof.
  intros E A a b t eq H. 
  revert b eq.
  induction H; intros; subst.
  - rewrite H in eq. apply Eq.eqit_Ret in eq. auto.
  - eapply IHReturns. rewrite tau_eutt in H. rewrite <- H. assumption.
  - rewrite H in eq. symmetry in eq. apply eqit_inv in eq. inv eq.
Qed.

Lemma Returns_ret_inv :  forall {E} A (a b : A), Returns a ((ret b) : itree E A) -> a = b.
Proof.
  intros.
  eapply Returns_ret_inv_. reflexivity. cbn in H. apply H.
Qed.

Lemma eutt_Returns_ : forall {E} {R} (RR : R -> Prop) (ta : itree E R) 
    (IN: forall (a : R), Returns a ta -> RR a), eutt (fun u1 u2 => u1 = u2 /\ RR u1) ta ta.
Proof.
  intros E R.
  ginit.
  gcofix CIH; intros.

  setoid_rewrite (itree_eta ta) in IN.

  gstep. red.

  destruct (observe ta).
  - econstructor.  split; auto. apply IN. econstructor. reflexivity.
  - econstructor. gfinal. left. apply CIH. intros. eapply IN. rewrite tau_eutt. assumption.
  - econstructor. intros. red.
    gfinal. left. apply CIH. intros. eapply IN. eapply Returns_Vis_sub. apply H.
Qed.

Lemma eutt_Returns2_ : forall {E} {R' R} (RR : R -> Prop) (RR' : R' -> Prop) (ta : itree E R) (ta' : itree E R') RU
    (IN1: forall (a : R'), Returns a ta' -> RR' a)
    (IN2: forall (a : R), Returns a ta -> RR a),
    eutt RU ta ta' ->
    eutt (fun u1 u2 => RU u1 u2 /\ RR u1 /\ RR' u2) ta ta'.
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
  - econstructor. gfinal. left. apply CIH. intros.
    eapply IN1. rewrite tau_eutt. assumption.
    intros. eapply IN2. rewrite tau_eutt. assumption.
    pclearbot; eauto.
  - econstructor. intros. red.
    gfinal. left. apply CIH. intros. eapply IN1. eapply Returns_Vis_sub. apply H.
    intros. eapply IN2. eapply Returns_Vis_sub. apply H.
    pclearbot. eauto.
  - econstructor; eauto. eapply IHeqitF; eauto. intros; eapply IN2.
    eapply ReturnsTau; eauto. rewrite <- itree_eta; reflexivity.
  - econstructor; eauto. eapply IHeqitF; eauto. intros; eapply IN1.
    eapply ReturnsTau; eauto. rewrite <- itree_eta; reflexivity.
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
  - eapply eqit_inv_Tau_r in H. repeat intro.
    apply IHReturns. eauto.
    rewrite <- H. auto.
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
    apply eutt_Returns_. auto.
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

Lemma eutt_bind_inv {E} :
  forall A B (ma : itree E A) (k k' : A -> itree E B) R,
  bind ma k ≈{R} bind ma k' ->
  forall a, a ∈ ma -> exists a', a' ∈ ma /\ k a ≈{R} k' a'.
Proof.
  intros.
  exists a. split; auto.
  pose proof @eqit_Vis.
  cbn in H.
  rewrite Returns_mayRet in H0.
  induction H0.
  + rewrite <- Eq.bind_ret_l. cbn.
    setoid_rewrite <- Eq.bind_ret_l at 3.
    rewrite <- H0. apply H.
  + eapply eqit_Tau_l in H0.
    setoid_rewrite eutt_Tau in H0.
    apply IHReturns.
    rewrite <- H0. apply H.
  + assert (eutt R (ITree.bind (Vis e k0) k) (ITree.bind (Vis e k0) k')).
    rewrite <- H0. apply H.
    assert (eutt R (Vis e (fun x => ITree.bind (k0 x) k)) (Vis e (fun x => ITree.bind (k0 x) k'))).
    do 2 rewrite <- bind_vis. apply H3.
    repeat red in H4. punfold H4. red in H4. inversion H4. subst.
    dependent destruction H10. red in REL.
    specialize (REL x). destruct REL.
    * eapply IHReturns. apply H5.
    * red in H5. contradiction.
Qed.

Lemma eutt_bind_inv_homog {E} :
  forall A B (ma : itree E A) (k k': A -> itree E B) R,
  bind ma k ≈{R} bind ma k' ->
  forall a, a ∈ ma -> k a ≈{R} k' a.
Proof.
  intros.
  pose proof @eqit_Vis.
  cbn in H.
  rewrite Returns_mayRet in H0.
  induction H0.
  + rewrite <- Eq.bind_ret_l. cbn.
    rewrite <- H0. rewrite H0 in H. rewrite !Eq.bind_ret_l in H.
    rewrite H0. rewrite Eq.bind_ret_l. auto.
  + eapply eqit_Tau_l in H0.
    setoid_rewrite eutt_Tau in H0.
    apply IHReturns.
    rewrite <- H0. apply H.
  + assert (eutt R (ITree.bind (Vis e k0) k) (ITree.bind (Vis e k0) k')).
    rewrite <- H0. apply H.
    assert (eutt R (Vis e (fun x => ITree.bind (k0 x) k)) (Vis e (fun x => ITree.bind (k0 x) k'))).
    do 2 rewrite <- bind_vis. apply H3.
    repeat red in H4. punfold H4. red in H4. inversion H4. subst.
    dependent destruction H10. red in REL.
    specialize (REL x). destruct REL.
    * eapply IHReturns. apply H5.
    * red in H5. contradiction.
Qed.


Lemma mayRet_eq_Refl_ITree2:
  forall E A (ma : itree E A), ma ≈{ fun a1 a2 => a1 = a2 /\ a1 ∈ ma /\ a2 ∈ ma } ma.
Proof.
  intros. eapply itree_eutt_Proper.
  Unshelve.
  3 : exact (fun a1 a2 => a1 = a2 /\ Returns a1 ma /\ Returns a2 ma).
  red. split; repeat intro.
  crunch; eauto. rewrite Returns_mayRet in H0. auto.
  crunch; eauto. rewrite Returns_mayRet in H1. auto.
  crunch; eauto. rewrite <- Returns_mayRet in H0. auto.
  rewrite <- Returns_mayRet in H1. auto.
  apply eutt_Returns2_. all : intros; eauto. reflexivity.
Qed.

Lemma mayRet_eq_Refl_ITree:
  forall E A (ma : itree E A), ma ≈{ fun a1 a2 => a1 = a2 /\ a1 ∈ ma } ma.
Proof.
  intros. eapply itree_eutt_Proper.
  Unshelve.
  3 : exact (fun a1 a2 => a1 = a2 /\ Returns a1 ma).
  red. split; repeat intro.
  crunch; eauto. rewrite Returns_mayRet in H0. auto.
  crunch; eauto. rewrite <- Returns_mayRet in H0. auto.
  apply eutt_Returns_. intros; eauto.
Qed.

Lemma image_ma_Refl_ITree:
  forall E A (ma : itree E A), ma ≈{ image ma } ma.
Proof.
  intros. eapply itree_eutt_Proper_mono.
  Unshelve.
  3 : exact (fun a1 a2 => a1 = a2 /\ Returns a1 ma).
  2 : apply eutt_Returns_; intros; eauto.
  intros x y [-> ?].
  eapply Returns_impl_image. split; auto.
Qed.

Lemma tau_eutt_L:
  forall E A (t t': itree E A), Tau t ≈ t' <-> t ≈ t'.
Proof.
  intros. split; intros.
  - eapply eutt_Tau.
    repeat red; pstep; red.
    eapply EqTauR; auto. punfold H.
  - repeat red; pstep; red.
    eapply EqTauL; auto. punfold H.
Qed.

Lemma tau_eutt_R:
  forall E A (t t': itree E A), t ≈ Tau t' <-> t ≈ t'.
Proof.
  intros. split; intros.
  - eapply eutt_Tau.
    repeat red; pstep; red.
    eapply EqTauL; auto. punfold H.
  - repeat red; pstep; red.
    eapply EqTauR; auto. punfold H.
Qed.

Lemma ret_eutt_L:
  forall E A B (a : A) (mb : itree E B) (R: relationH A B),
    Ret a ≈{ R } mb -> exists (b : B), mb ≈ Ret b /\ R a b.
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
    constructor. auto. constructor; reflexivity. auto.
    apply H0. apply IHeqitF; auto.
Qed.

Lemma ret_eutt_R:
  forall E A B (b : B) (ma : itree E A) (R: relationH A B),
    ma ≈{ R } Ret b -> exists (a : A), ma ≈ Ret a /\ R a b.
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
  - intros; subst. apply simpobs in Heqotr.
    setoid_rewrite Heqotr.
    setoid_rewrite tau_eutt_L.
    apply IHeqitF; auto.
  - intros; subst; inversion Heqotl.
Qed.

Lemma vis_eutt_L:
  forall E A B X (e : E X) (k : X -> itree E A) (mb : itree E B) (R: relationH A B),
    Vis e k ≈{ R } mb -> exists (k' : X -> itree E B), mb ≈ Vis e k'.
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
  - intros. apply simpobs in Heqotr.
    setoid_rewrite Heqotr.
    setoid_rewrite tau_eutt_L.
    eapply IHeqitF; eauto.
Qed.


Lemma vis_eutt_R:
  forall E A B X (e : E X) (k : X -> itree E B) (ma : itree E A) (R: relationH A B),
    ma ≈{ R } Vis e k -> exists (k' : X -> itree E A), ma ≈ Vis e k'.
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
  - intros. apply simpobs in Heqotr.
    setoid_rewrite Heqotr.
    setoid_rewrite tau_eutt_L.
    eapply IHeqitF; eauto.
  - intros; subst; inversion Heqotl.
Qed.

Lemma ret_mayRet : forall E A (x : A), x ∈ ret (m := itree E) x.
Proof.
  repeat intro. eapply eqit_inv_Ret in EQR; auto.
Qed.

Lemma bind_mayRet :
  forall E A (u : A) (ma : itree E A),
    u ∈ ma ->
    forall B (v : B) (k : A -> itree E B),
      v ∈ k u ->
      v ∈ (bind ma k).
Proof.
  intros.
  rewrite Returns_mayRet in H, H0.
  rewrite Returns_mayRet.
  revert k v H0.
  induction H; intros.
  - rewrite H. setoid_rewrite Eq.bind_ret_l.
    eauto.
  - rewrite tau_eutt in H. rewrite H. eapply IHReturns; eauto.
  - rewrite H. setoid_rewrite bind_vis.
    eapply ReturnsVis. reflexivity.
    eapply IHReturns. eauto.
Qed.

#[global]
Instance eqmR_mayRet_l_ITree {E}: MayRetL (itree E).
red.
  intros* EQ a1 IN.
  rewrite Returns_mayRet in IN.
  revert EQ. revert RA ma2.
  induction IN.
  - intros.
    assert (Ret a1 ≈{ RA } ma2). {
      rewrite <- H. auto.
    }
    apply ret_eutt_L in H0. destruct H0.
    exists x. destruct H0. split; auto. repeat intro. rewrite H0 in EQR. apply eqit_inv_Ret in EQR. auto.
  - intros. apply IHIN.
    rewrite tau_eutt_R in H. rewrite <- H. apply EQ.
  - intros.
    assert (Vis e k ≈{ RA } ma2). {
      rewrite <- H. auto.
    } clear EQ H. assert (EQ := H0).
    apply vis_eutt_L in H0. destruct H0.
    assert (Vis e k ≈{RA} Vis e x0).
    rewrite <- H. auto.
    eapply eqit_inv_Vis with (u := x)in H0.
    specialize (IHIN RA (x0 x) H0).
    destruct IHIN as (? & ? & ?).
    exists x1. split; auto. rewrite Returns_mayRet. rewrite H. eapply ReturnsVis.
    reflexivity. rewrite <- Returns_mayRet. eauto.
Defined.

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
    apply ret_eutt_R in H0. destruct H0.
    exists x. destruct H0. split; auto. repeat intro. rewrite H0 in EQR. apply eqit_inv_Ret in EQR.
    auto.
  - intros. apply IHIN.
    rewrite tau_eutt_R in H. rewrite <- H. apply EQ.
  - intros.
    assert (ma1 ≈{ RA } Vis e k). {
      rewrite <- H. auto.
    } clear EQ H. assert (EQ := H0).
    apply vis_eutt_R in H0. destruct H0.
    assert (Vis e x0 ≈{RA} Vis e k).
    rewrite <- H. auto.
    eapply eqit_inv_Vis with (u := x) in H0.
    specialize (IHIN RA (x0 x) H0).
    destruct IHIN as (? & ? & ?).
    exists x1. split; auto. rewrite Returns_mayRet. rewrite H. eapply ReturnsVis.
    reflexivity. rewrite <- Returns_mayRet. eauto.
Defined.

Lemma eutt_prod_rel {E}:
  forall (A B : Type)
    (RA : relationH A A) (RB : relationH B B) (ma : itree E (A * B)),
  eutt RA (fst <$> ma) (fst <$> ma) -> eutt RB (snd <$> ma) (snd <$> ma) -> eutt (prod_rel RA RB) ma ma.
Proof.
  intros until RB.
  einit. ecofix CIH.
  intros * H_fst H_snd.
  rewrite itree_eta.
  genobs ma oma.
  destruct (observe ma) eqn: EQma; subst; intros; pclearbot; simpl.
  - assert (ma ≈ Ret r). {
      repeat red. pstep. red. rewrite EQma. constructor. auto.
    }
    rewrite H in H_fst, H_snd. cbn in *. unfold ITree.map in *.
    rewrite Eq.bind_ret_l in H_fst. rewrite Eq.bind_ret_l in H_snd.
    apply eqit_inv_Ret in H_fst.
    apply eqit_inv_Ret in H_snd.
    destruct r. apply euttG_ret. split; eauto.
  - assert (ma ≈ Tau t). {
      repeat red. pstep. red. rewrite EQma. constructor.
      assert (t ≈ t) by reflexivity.
      left. apply H.
    }
    constructor. gstep. constructor. gfinal. left. eapply CIHL.
    rewrite tau_eutt in H. rewrite <- H. eauto.
    rewrite tau_eutt in H. rewrite <- H. eauto.
  - assert (ma ≈ Vis e k). {
      repeat red. pstep. red. rewrite EQma. constructor.
      intros. red. left.
      assert (k v ≈ k v) by reflexivity.
      apply H.
    }
    clear EQma.
    constructor. gstep. constructor. intros. gfinal. left.
    econstructor. reflexivity. reflexivity. right.
    eapply CIHH.
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

    intros. subst. auto.
    intros. subst. auto.
Qed.

Lemma eutt_prod_rel_homo' {E}:
  forall (A B : Type)
    (RA : relationH A A) (RB : relationH B B)
    (ma ma' : itree E (A * B)),
    ma ≈ ma' ->
    eutt RA (fst <$> ma) (fst <$> ma') ->
    eutt RB (snd <$> ma) (snd <$> ma') ->
    eutt (prod_rel RA RB) ma ma'.
Proof.
  intros. rewrite H in *. apply eutt_prod_rel; auto.
Qed.

#[global]
Instance eqmR_prod_rel_ITree {E} : RelProd (itree E).
Proof.
  intros until RB.
  einit. ecofix CIH.
  intros * EQ EQ'.
  rewrite itree_eta, (itree_eta m2).
  punfold EQ; red in EQ.
  remember (fst <$> m1) eqn: P; remember (fst <$> m2) eqn: P'.
  assert (Q: fst <$> m1 ≅ i) by (subst; reflexivity).
  assert (Q': fst <$> m2 ≅ i0) by (subst; reflexivity).
  clear P P'.
  genobs i ot; genobs i0 os.
  hinduction EQ before CIHH; intros; pclearbot; simpl.
  - symmetry in Heqot; symmetry in Heqos.
    apply observe_eutt in Heqot, Heqos.
    unfold fmap in *. subst. rewrite <- Q in Heqot. rewrite <- Q' in Heqos.
    apply eqit_inv_bind_ret in Heqot, Heqos. crunch.
    rewrite H0, H in EQ'. efinal. rewrite H, H0.
    apply eqit_inv in H1, H2. cbn in *. subst. rewrite! Eq.bind_ret_l in EQ'.
    apply eqit_inv in EQ'. cbn in *. subst. destruct x, x0.
    apply eqit_Ret. constructor; eauto.
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
    estep; ebase; right; eapply CIHL; eauto.
    rewrite H0, H2. auto.
    rewrite H, H1 in EQ'. rewrite!tau_eutt in EQ'. auto.
  - symmetry in Heqot, Heqos. apply observe_eqitree in Heqot, Heqos.
    rename Heqot into H. rename Heqos into H0.
    rewrite <- Q in H; rewrite <- Q' in H0.
    apply eqitree_inv_bind_vis in H. crunch.
    2 : { punfold H1. inv H1. }
    apply eqitree_inv_bind_vis in H0. crunch.
    2 : { punfold H2. inv H2. }
    rewrite H, H0.
    eapply euttG_vis; ebase; left; apply CIHH; auto.
    unfold fmap. setoid_rewrite H1. setoid_rewrite H2.
    apply REL.
    rewrite H, H0 in EQ'.
    unfold fmap in EQ'. setoid_rewrite bind_vis in EQ'.
    eapply eqit_inv_Vis in EQ'. cbn in *. crunch.
    eauto.
  - subst.
    destruct (observe m1) eqn : Hm1.
    + apply observe_eqitree in Hm1. rewrite Hm1 in EQ'.
      symmetry in Heqot. apply observe_eqitree in Heqot.
      unfold fmap in *. rewrite <- Q in Heqot. rewrite Hm1 in Heqot.
      setoid_rewrite Eq.bind_ret_l in Heqot.
      punfold Heqot. inv Heqot. inv CHECK0.
    + rewrite tau_euttge. rewrite itree_eta. eapply IHEQ; eauto.
      symmetry in Heqot. apply observe_eqitree in Hm1, Heqot.
      unfold fmap in Heqot. rewrite <- Q in Heqot. rewrite Hm1 in Heqot. setoid_rewrite bind_tau in Heqot.
      rewrite <- (tau_eutt t). rewrite <- Hm1. auto.
      apply observe_eqitree in Hm1. symmetry in Heqot.
      apply observe_eqitree in Heqot.
      rewrite Heqot in Q. rewrite Hm1 in Q.
      unfold fmap in Q. setoid_rewrite bind_tau in Q.
      rewrite eqitree_Tau in Q. auto.
    + apply observe_eqitree in Hm1. rewrite Hm1 in EQ'.
      symmetry in Heqot. apply observe_eqitree in Heqot.
      unfold fmap in *. rewrite <- Q in Heqot. rewrite Hm1 in Heqot. setoid_rewrite bind_vis in Heqot.
      punfold Heqot. inv Heqot. inv CHECK0.
  - subst.
    destruct (observe m2) eqn : Hm1.
    + apply observe_eqitree in Hm1. rewrite Hm1 in EQ'.
      symmetry in Heqos. apply observe_eqitree in Heqos.
      unfold fmap in *. rewrite <- Q' in Heqos. rewrite Hm1 in Heqos. setoid_rewrite Eq.bind_ret_l in Heqos.
      punfold Heqos. inv Heqos. inv CHECK0.
    + rewrite tau_euttge. rewrite (itree_eta t). eapply IHEQ; eauto.
      symmetry in Heqos. apply observe_eqitree in Hm1, Heqos.
      unfold fmap in Heqos. rewrite <- Q' in Heqos. rewrite Hm1 in Heqos. setoid_rewrite bind_tau in Heqos.
      rewrite <- (tau_eutt t). rewrite <- Hm1. auto.
      apply observe_eqitree in Hm1. symmetry in Heqos.
      apply observe_eqitree in Heqos.
      rewrite Heqos in Q'. rewrite Hm1 in Q'.
      unfold fmap in Q'. setoid_rewrite bind_tau in Q'.
      rewrite eqitree_Tau in Q'. auto.
    + apply observe_eqitree in Hm1. rewrite Hm1 in EQ'.
      symmetry in Heqos. apply observe_eqitree in Heqos.
      unfold fmap in *. rewrite <- Q' in Heqos. rewrite Hm1 in Heqos. setoid_rewrite bind_vis in Heqos.
      punfold Heqos. inv Heqos. inv CHECK0.
Defined.

#[global]
Instance eqmR_prod_fst_inv_ITree {E}: FmapFst (itree E).
Proof.
  repeat intro. unfold fmap.
  red in H. eapply eutt_clo_bind; eauto.
  intros.
  apply eqit_Ret. destruct u1, u2; inv H0; eauto.
Defined.

#[global]
Instance eqmR_prod_snd_inv_ITree {E}: FmapSnd (itree E).
Proof.
  repeat intro. unfold fmap.
  red in H. eapply eutt_clo_bind; eauto.
  intros.
  apply eqit_Ret. destruct u1, u2; inv H0; eauto.
Defined.


#[global]
Instance eqmR_sum_inl_ITree {E}: FmapInl (itree E).
Proof.
  repeat intro. unfold fmap.
  red in H. eapply eutt_clo_bind; eauto.
  intros.
  apply eqit_Ret. constructor; eauto.
Defined.

#[global]
Instance eqmR_sum_inr_ITree {E}: FmapInr (itree E).
Proof.
  repeat intro. unfold fmap.
  red in H. eapply eutt_clo_bind; eauto.
  intros.
  apply eqit_Ret. constructor; eauto.
Defined.

#[global]
Instance fmap_inv_ITree' {E}: FmapInv_mayRet (itree E).
Proof.
  intros until ma2.
  remember (fun a a' => mayRet_rel (itree E) ma1 ma2 a a' /\ R (f1 a) (f2 a')) as QQ.
  assert ((fun a a' => mayRet_rel (itree E) ma1 ma2 a a' /\ R (f1 a) (f2 a')) ⊑ QQ).
  { subst; eauto. repeat intro; eauto. }
  clear HeqQQ. rename H into HeqQQ.
  revert ma1 ma2 HeqQQ.
  einit. ecofix CIH.
  intros * ? EQ. intros.

  rewrite itree_eta, (itree_eta ma2).
  punfold EQ; red in EQ.
  remember (f1 <$> ma1) eqn: P; remember (f2 <$> ma2) eqn: P'.
  assert (Q: f1 <$> ma1 ≅ i) by (subst; reflexivity).
  assert (Q': f2 <$> ma2 ≅ i0) by (subst; reflexivity).
  clear P P'.
  genobs i ot; genobs i0 os.
  hinduction EQ before CIHH; intros; pclearbot; simpl.
  - symmetry in Heqot; symmetry in Heqos.
    apply observe_eqitree in Heqot, Heqos.
    unfold fmap in *. subst. rewrite <- Q in Heqot. rewrite <- Q' in Heqos.
    apply eqitree_inv_bind_ret in Heqot, Heqos. crunch.
    rewrite H0 in Q. rewrite H in Q'.
    rewrite H0, H.
    efinal. apply eqit_Ret. apply HeqQQ. split. red.
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
    estep; ebase. right. eapply CIHL; eauto; cycle 1.
    rewrite H0, H2. auto. subst.
    unfold mayRet_rel. repeat intro.
    apply HeqQQ. crunch; eauto. red.
    rewrite!Returns_mayRet.
    rewrite H, H1. rewrite! tau_eutt.
    rewrite Returns_mayRet in H3, H5.
    auto.
  - symmetry in Heqot, Heqos. apply observe_eqitree in Heqot, Heqos.
    rename Heqot into H. rename Heqos into H0.
    rewrite <- Q in H; rewrite <- Q' in H0.
    apply eqitree_inv_bind_vis in H. crunch.
    2 : { punfold H1. inv H1. }
    apply eqitree_inv_bind_vis in H0. crunch.
    2 : { punfold H2. inv H2. }
    rewrite H, H0.
    eapply euttG_vis; ebase; left; apply CIHH; auto; cycle 1.
    unfold fmap. setoid_rewrite H1. setoid_rewrite H2.
    specialize (REL v). red. apply REL.
    repeat intro; unfold mayRet_rel in *.
    apply HeqQQ.
    crunch; auto.
    apply Returns_mayRet in H3, H5.
    crunch; apply Returns_mayRet; eapply ReturnsVis; eauto; try reflexivity. rewrite H.
    reflexivity.
    apply Returns_mayRet; eapply ReturnsVis; eauto; try reflexivity. rewrite H0.
    reflexivity. apply Returns_mayRet in H5. eauto.
  - subst.
    destruct (observe ma1) eqn : Hma1.
    + apply observe_eqitree in Hma1. rewrite Hma1 in Q.
      symmetry in Heqot. apply observe_eqitree in Heqot.
      unfold fmap in *. rewrite <- Q in Heqot. setoid_rewrite Eq.bind_ret_l in Heqot.
      punfold Heqot. inv Heqot. inv CHECK0.
    + rewrite tau_euttge. rewrite itree_eta. eapply IHEQ; eauto; cycle 1.
      symmetry in Heqot. apply observe_eqitree in Hma1, Heqot.
      unfold fmap in Heqot. rewrite <- Q in Heqot. rewrite Hma1 in Heqot. setoid_rewrite bind_tau in Heqot.
      rewrite eqitree_Tau in Heqot. eauto. repeat intro. eapply HeqQQ.
      unfold mayRet_rel in *. crunch; eauto.
      apply observe_eutt in Hma1. rewrite tau_eutt in Hma1.
      apply Returns_mayRet. rewrite Hma1. rewrite <- Returns_mayRet; auto.
    + apply observe_eqitree in Hma1.
      symmetry in Heqot. apply observe_eqitree in Heqot.
      unfold fmap in *. rewrite <- Q in Heqot. rewrite Hma1 in Heqot.
      setoid_rewrite bind_vis in Heqot.
      punfold Heqot. inv Heqot. inv CHECK0.
  - subst.
    destruct (observe ma2) eqn : Hma1.
    + apply observe_eqitree in Hma1.
      symmetry in Heqos. apply observe_eqitree in Heqos.
      unfold fmap in *. rewrite <- Q' in Heqos. rewrite Hma1 in Heqos. setoid_rewrite Eq.bind_ret_l in Heqos.
      punfold Heqos. inv Heqos. inv CHECK0.
    + rewrite tau_euttge. rewrite (itree_eta t). eapply IHEQ; eauto; cycle 1.
    symmetry in Heqos. apply observe_eqitree in Hma1, Heqos.
    unfold fmap in Heqos. rewrite <- Q' in Heqos.
    rewrite Hma1 in Heqos. setoid_rewrite bind_tau in Heqos.
      rewrite eqitree_Tau in Heqos. eauto. repeat intro. eapply HeqQQ.
      unfold mayRet_rel in *. crunch; eauto.
      apply observe_eutt in Hma1. rewrite tau_eutt in Hma1.
      apply Returns_mayRet. rewrite Hma1. rewrite <- Returns_mayRet; auto.
    + apply observe_eqitree in Hma1.
      symmetry in Heqos. apply observe_eqitree in Heqos.
      unfold fmap in *. rewrite <- Q' in Heqos. rewrite Hma1 in Heqos.
      setoid_rewrite bind_vis in Heqos.
      punfold Heqos. inv Heqos. inv CHECK0.
Defined.

#[global]
Instance eqmR_sum_rel_ITree {E}: RelSum (itree E).
Proof.
  repeat intro; split; intros; [red in H; unfold fmap|].
  - eapply eutt_clo_bind; eauto.
    intros. apply eqit_Ret. destruct u1, u2; try inv H2.
    apply H0; auto. apply H1; auto.
  - specialize (H (A1 + B1)%type (A2 + B2)%type inl inl inr inr (RA ⊕ RB)).
    assert (inl_P: ProperH (respectfulH A1 A2 (A1 + B1) (A2 + B2) RA (RA ⊕ RB)) inl inl) by
      (repeat intro; constructor; auto).
    assert (inr_P: ProperH (respectfulH B1 B2 (A1 + B1) (A2 + B2) RB (RA ⊕ RB)) inr inr) by
      (repeat intro; constructor; auto).
    specialize (H inl_P inr_P).
    apply fmap_inv_ITree' in H. eapply itree_eutt_Proper_mono; eauto.
    repeat intro; crunch; eauto.
    destruct x, y; eauto.
Defined.

#[global]
Lemma eqmR_prod_sum_rel_ITree {E}:
  forall (A B C : Type)
    (RA : relationH A A) (RB : relationH B B) (RC : relationH C C)
    (ma ma' : itree E (C + A * B)%type),
    (fst_sum <$> ma) ≈{ RC ⊕ RA } (fst_sum <$> ma') ->
    (snd_sum <$> ma) ≈{ RC ⊕ RB } (snd_sum <$> ma') -> ma ≈{ RC ⊕ RA ⊗ RB } ma'.
Proof.
  intros until RC.
  einit. ecofix CIH.
  intros * EQ EQ'.
  rewrite itree_eta, (itree_eta ma').
  punfold EQ; red in EQ.
  remember (fst_sum <$> ma) eqn: P; remember (fst_sum <$> ma') eqn: P'.
  assert (Q: fst_sum <$> ma ≅ i) by (subst; reflexivity).
  assert (Q': fst_sum <$> ma' ≅ i0) by (subst; reflexivity).
  clear P P'.
  genobs i ot; genobs i0 os.
  hinduction EQ before CIHH; intros; pclearbot; simpl.
  - symmetry in Heqot; symmetry in Heqos.
    apply observe_eutt in Heqot, Heqos.
    unfold fmap in *. subst. rewrite <- Q in Heqot. rewrite <- Q' in Heqos.
    apply eqit_inv_bind_ret in Heqot, Heqos. crunch.
    rewrite H0, H in EQ'. efinal. rewrite H, H0.
    apply eqit_inv in H1, H2. cbn in *. subst. unfold ITree.map in *. rewrite! Eq.bind_ret_l in EQ'.
    apply eqit_inv in EQ'. cbn in *. subst.
    inv REL. inv EQ'.
    all : unfold fst_sum, snd_sum in *; destruct x0 eqn: Hx0; destruct x eqn: Hx.
    all : repeat match goal with
          | [H : inl _ = _ |- _] => inv H
          | [H : inr _ = _ |- _] => inv H
          end; eauto.
    all : apply eqit_Ret; constructor; eauto.
    inv EQ'.
    destruct p, p0. constructor; eauto.
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
    estep; ebase; right. eapply CIHL; eauto.
    rewrite H0, H2. auto.
    rewrite H, H1 in EQ'. rewrite!tau_eutt in EQ'. auto.
  - symmetry in Heqot, Heqos. apply observe_eqitree in Heqot, Heqos.
    rename Heqot into H. rename Heqos into H0.
    rewrite <- Q in H; rewrite <- Q' in H0.
    apply eqitree_inv_bind_vis in H. crunch.
    2 : { punfold H1. inv H1. }
    apply eqitree_inv_bind_vis in H0. crunch.
    2 : { punfold H2. inv H2. }
    rewrite H, H0.
    eapply euttG_vis; ebase; left; apply CIHH; auto.
    + unfold fmap. setoid_rewrite H1. setoid_rewrite H2. auto.
      rewrite H, H0 in EQ'.
      unfold fmap in EQ'. setoid_rewrite bind_vis in EQ'.
      eapply eqit_inv_Vis in EQ'. cbn in *. crunch.
      eapply REL.
    + rewrite H, H0 in EQ'. unfold fmap in EQ'. setoid_rewrite bind_vis in EQ'.
      eapply eqit_inv_Vis in EQ'. cbn in *. eauto.
  - subst.
    destruct (observe ma) eqn : Hma.
    + apply observe_eqitree in Hma. rewrite Hma in EQ'.
      symmetry in Heqot. apply observe_eqitree in Heqot.
      unfold fmap in *. rewrite <- Q in Heqot. rewrite Hma in Heqot. setoid_rewrite Eq.bind_ret_l in Heqot.
      punfold Heqot. inv Heqot. inv CHECK0.
    + rewrite tau_euttge. rewrite itree_eta. eapply IHEQ; eauto.
      symmetry in Heqot. apply observe_eqitree in Hma, Heqot.
      unfold fmap in Heqot. rewrite <- Q in Heqot. rewrite Hma in Heqot. setoid_rewrite bind_tau in Heqot.
      rewrite <- (tau_eutt t). rewrite <- Hma. auto.
      apply observe_eqitree in Hma. symmetry in Heqot.
      apply observe_eqitree in Heqot.
      rewrite Heqot in Q. rewrite Hma in Q.
      unfold fmap in Q. setoid_rewrite bind_tau in Q.
      rewrite eqitree_Tau in Q. auto.
    + apply observe_eqitree in Hma. rewrite Hma in EQ'.
      symmetry in Heqot. apply observe_eqitree in Heqot.
      unfold fmap in *. rewrite <- Q in Heqot. rewrite Hma in Heqot. setoid_rewrite bind_vis in Heqot.
      punfold Heqot. inv Heqot. inv CHECK0.
  - subst.
    destruct (observe ma') eqn : Hma.
    + apply observe_eqitree in Hma. rewrite Hma in EQ'.
      symmetry in Heqos. apply observe_eqitree in Heqos.
      unfold fmap in *. rewrite <- Q' in Heqos. rewrite Hma in Heqos. setoid_rewrite Eq.bind_ret_l in Heqos.
      punfold Heqos. inv Heqos. inv CHECK0.
    + rewrite tau_euttge. rewrite (itree_eta t). eapply IHEQ; eauto.
      symmetry in Heqos. apply observe_eqitree in Hma, Heqos.
      unfold fmap in Heqos. rewrite <- Q' in Heqos. rewrite Hma in Heqos. setoid_rewrite bind_tau in Heqos.
      rewrite <- (tau_eutt t). rewrite <- Hma. auto.
      apply observe_eqitree in Hma. symmetry in Heqos.
      apply observe_eqitree in Heqos.
      rewrite Heqos in Q'. rewrite Hma in Q'.
      unfold fmap in Q'. setoid_rewrite bind_tau in Q'.
      rewrite eqitree_Tau in Q'. auto.
    + apply observe_eqitree in Hma. rewrite Hma in EQ'.
      symmetry in Heqos. apply observe_eqitree in Heqos.
      unfold fmap in *. rewrite <- Q' in Heqos. rewrite Hma in Heqos. setoid_rewrite bind_vis in Heqos.
      punfold Heqos. inv Heqos. inv CHECK0.
      Unshelve.
      eauto.
Qed.

Global Instance eqmR_transport_Equiv_itree {E} : TransportEquiv (itree E).
Proof.
  repeat intro. typeclasses eauto.
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

Global Instance EqmR_OK_ITree {E} : EqmR_OK (itree E).
Proof.
  split; try typeclasses eauto; unfold eqmR, EqmR_ITree.
Defined.

#[global]
Instance eqmR_bind_ProperH_ITree {E}: ProperBind (itree E).
Proof.
  red.
  intros.
  pose proof (H).
  eapply eqmR_rel_comp in H. 2 : typeclasses eauto.
  Unshelve. 3 : exact (fun a1 a2 => a1 = a2 /\ a1 ∈ ma2).
  eapply eutt_clo_bind.
  apply H.
  apply mayRet_eq_Refl_ITree.
  intros. destruct H2 as (? & ? & ?). destruct H3. subst.
  apply H0. auto.
Qed.

#[global]
Instance bind_ret_l_ITree {E}: BindRetL (itree E).
Proof.
  red. intros *. red. setoid_rewrite Eq.bind_ret_l. reflexivity.
Qed.

#[global]
Instance bind_ret_r_ITree {E}: BindRetR (itree E).
Proof.
  red. intros *. red. setoid_rewrite Eq.bind_ret_r. reflexivity.
Qed.

#[global]
Instance bind_bind_ITree {E}: BindBind (itree E).
Proof.
  red. intros *. red. setoid_rewrite Eq.bind_bind. reflexivity.
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
  assert (i ≈ x <- ma ;; k x) by (subst; reflexivity). clear Heqi.
  revert ma k H0.
  induction H; intros.
  - rewrite H in H0. symmetry in H0. apply eutt_inv_bind_ret in H0.
    crunch. exists x. rewrite! Returns_mayRet.
    split; [rewrite H0|rewrite H1]; constructor; reflexivity.
  - rewrite H in H1. symmetry in H1. apply eutt_inv_bind_tau in H1; crunch.
    + edestruct IHReturns; cycle 1; eauto.
      rewrite H1.
      rewrite <- H2.
      cbn. rewrite bind_tau. rewrite tau_eutt. reflexivity.
    + edestruct IHReturns; cycle 1; eauto.
      rewrite H1.
      rewrite tau_eutt in H2.
      rewrite <- H2. setoid_rewrite Eq.bind_ret_l. reflexivity.
  - rewrite H in H1. clear H. symmetry in H1. apply eutt_inv_bind_vis in H1; crunch.
    + edestruct IHReturns.
      rewrite <- H1. eapply eutt_clo_bind; intros; subst; try reflexivity. subst. reflexivity.
      crunch; esplit; split; eauto.
      rewrite H. apply Returns_mayRet. eapply ReturnsVis. reflexivity.
      apply Returns_mayRet in H2. eauto.
    + exists x0. split. rewrite H. apply Returns_mayRet. constructor; reflexivity.
      rewrite H1. eapply ReturnsVis in H0. apply Returns_mayRet. eauto. reflexivity.
Defined.

#[global]
Instance fmap_inv_mayRet_itree {E}: FmapInvRet (itree E).
Proof.
  red. intros. unfold fmap in H. eapply eutt_bind_inv_homog in H; eauto.
Defined.

#[global]
Instance eqmR_inv_itree {E}: EqmRInv (itree E).
Proof.
  repeat intro.
  rewrite <- (Eq.bind_ret_r ma) in H.
  eapply @eutt_bind_inv_homog in H; eauto.
  eapply eqit_inv in H; eauto.
Qed.

Global Instance EqmRMonadInverses_ITree {E} : EqmRInversionProperties (itree E).
Proof.
  constructor;try typeclasses eauto.
Defined.

Global Instance EQM_ITree {E} : EQM (itree E) _.
Proof.
  econstructor;typeclasses eauto.
Defined.
