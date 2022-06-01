(** * Theorems about [interpH] *)

(** Main facts:
    - [unfold_interpH]: Unfold lemma.
    - [interpH_bind]: [interpH] is a monad morphism.
    - [interpH_trigger]: Events are interpHreted using a handler.
 *)

(* begin hide *)
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree.Basics Require Import
     Basics Category CategoryKleisli CategoryKleisliFacts
     HeterogeneousRelations
     Tacs MonadFail.

From ITree.Core Require Import
     ITreeDefinition KTree KTreeFacts Subevent.

From ITree.Eq Require Import
     Eq UpToTaus Paco2.

From ITree.Indexed Require Import
     Sum Function Relation.

From ITree.Interp Require Import
     Interp HFunctor Handler TranslateFacts.

From ITree.EqmR Require Import
     EqmRMonad EqmRMonadT
     Monads.ITree_weak
     Monads.StateT Monads.ErrorT.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad.
(* end hide *)

Set Primitive Projections.

Import RelNotations.
Import ITreeNotations.
Import MonadNotation.
Import CatNotations.
Local Open Scope relationH_scope.
Local Open Scope cat_scope.
Local Open Scope monad_scope.

Section interp_laws.

  Context (T : (Type -> Type) -> Type -> Type)
          (M : Type -> Type)
          {T_HFunctor : HFunctor T}
          {T_MonadT:MonadT T}
          {T_MonadIter:(forall m : Type -> Type, Monad m -> MonadIter m -> MonadIter (T m))}
          {M_Monad : Monad M}
          {M_EqmR : EqmR M}
          {M_MonadIter : MonadIter M}
          {TM_Interp : Interp (T := T) itree M}.

  Class InterpRet : Prop :=
    interp_ret :
      forall {E R} {f : E ~> M} (x: R),
        eqmR eq (interp f (ret x)) (ret x : T M R).

  Class InterpTrigger : Prop :=
    interp_trigger :
      forall {E R} (f : E ~> M) (e : E R),
        eqmR eq (interp f (trigger e)) (morph (MT := T M) (f _ e) : T M R).

  Class InterpOverTrigger : Prop :=
      interp_over_trigger :
      forall {E F G R} {S : F +? E -< G} {S_wf : Subevent_wf S}
        {Tr : Trigger E M} (f : F ~> M) (e : F R),
          eqmR eq
              (interp (@over F G E M S _ f) (trigger e : T (itree G) R))
              (morph (f _ e)).

  Class InterpOverIgnoreTrigger : Prop :=
    interp_over_ignore_trigger :
      forall (A B C BC ABC : Type -> Type) {S : B +? C -< BC} {S' : A +? BC -< ABC}
        {S_wf : Subevent_wf S} {S'_wf : Subevent_wf S'}
        R (h : A ~> M) (e : B R) {Tr : Trigger BC M},
      eqmR eq (m := T M)
      (interp (IM := itree) (T := T) (I := ABC) (M := M) (over h) (trigger (E := B) e))
      (morph (MT := T M) (trigger (E := BC) (inj1 e))).

  Class InterpBind : Prop :=
    interp_bind :
      forall {E R S} (f : E ~> M) (k : R -> T (itree E) S) t,
        eqmR eq (interp f (bind t k)) (bind (interp f t) (fun r => interp f (k r))).

  Class InterpIter : Prop :=
    interp_iter :
      forall {E I R} (f : E ~> M) (t : I -> T (itree E) (I + R)) (t' : I -> T M (I + R)) (i:I),
        (forall i, eqmR eq (interp f (t i)) (t' i))  ->
          interp f (Basics.iter t i) ≈{ eq } Basics.iter t' i.

  Class InterpProper : Prop :=
    interp_proper :
      forall {E} (h : E ~> M) R1 R2 (RR : R1 -> R2 -> Prop),
      ProperH (eqmR (m := T (itree E)) RR ~~> eqmR (B := R2) RR)
            (interp h (T0 := R1)) (interp h (T0 := R2)).

  Class InterpLaws : Prop :=
    { InterpLaws_InterpRet :> InterpRet;
      InterpLaws_InterpTrigger :> InterpTrigger;
      InterpLaws_InterpOverIgnoreTrigger :> InterpOverIgnoreTrigger;
      InterpLaws_InterpBind :> InterpBind;
      InterpLaws_InterpIter :> InterpIter;
      InterpLaws_InterpProper :> InterpProper }.

End interp_laws.

Arguments InterpLaws _ _ {_ _ _ _ _ _}.
Arguments interp_ret {_ _ _ _ _ _ _} [_ _].
Arguments interp_trigger {_ _ _ _ _ _ _} [_ _].
Arguments interp_over_trigger {_ _ _ _ _ _ _ _ _ _} [_ _] {_ _}.
Arguments interp_over_ignore_trigger {_ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _} [_].
Arguments interp_bind {_ _ _ _ _ _ _} [_ _ _].
Arguments interp_iter {_ _ _ _ _ _ _} [_ _ _].
Arguments interp_proper {_ _ _ _ _ _ _} [_].

#[global]
Existing Instance itree_interp.
(* We can define [U] to be a monad transformer which is a higher-order functor. *)
(*    Higher-order functors (Ghani & Johann) allow a functorial structure over *)
(*    higher-order functions *)
#[global] Instance stack_interp
       {T : (Type -> Type) -> Type -> Type}
       {M : Type -> Type}
       {T_HFunctor : HFunctor T}
       {M_Monad : IterativeMonad M}
        : Interp itree M  | 10 :=
  fun E h R t => hfmap (f := T) (itree_interp h) t.

#[global] Instance Proper_eq_itree_interp_body (E M:Type->Type) `{WF_IterativeMonad M} (A:Type) (RR:A->A->Prop) (f:E~>M):
  Proper (eq_itree RR ==> eqmR (sum_rel (eq_itree RR) RR)) (interp_body (E := E) (M := M) f A).
Proof.
  repeat intro. unfold interp_body.
  punfold H0. red in H0. remember (observe x); remember (observe y).
  revert x y Heqi Heqi0.
  induction H0; pclearbot; intros; subst; try inv CHECK.
  - eapply eqmR_ret; eauto; typeclasses eauto.
  - eapply eqmR_ret; eauto; try typeclasses eauto.
  - eapply eqmR_bind_ProperH; try typeclasses eauto; [ reflexivity | ..]; intros; subst;
      eapply eqmR_ret; eauto; typeclasses eauto.
Qed.

Section InterpITree.

  (** Unfolding of [interp]. *)
  Definition _interp {E F R} (f : E ~> itree F) (ot : itreeF E R _)
    : itree F R :=
    match ot with
    | RetF r => Ret r
    | TauF t => Tau (interp f t)
    | VisF e k => f _ e >>= (fun x => Tau (interp f (k x)))
    end.

  (** Unfold lemma. *)
  Lemma unfold_interp {E F R} {f : E ~> itree F} (t : itree E R) :
    interp f t ≅ (_interp f (observe t)).
  Proof.
    unfold interp, Basics.iter, MonadIter_itree. setoid_rewrite unfold_iter.
    unfold interp_body.
    destruct (observe t); cbn; try rewrite ?Eq.bind_bind;
      rewrite ?Eq.bind_ret_l, ?bind_map.
    all: try solve [tau_steps; reflexivity].
    setoid_rewrite Eq.bind_ret_l. reflexivity.
  Qed.

  #[global]
  Instance eq_itree_interp' {E F R} (f : E ~> itree F)
    : Proper (eq_itree eq ==> eq_itree eq) (interp f (T0 := R)).
  Proof.
    repeat red.
    ginit. pcofix CIH.
    intros l r0 Hlr.
    rewrite 2 unfold_interp.
    punfold Hlr; red in Hlr.
    destruct Hlr; cbn; subst; try discriminate; pclearbot; try (gstep; constructor; eauto with paco; fail).
    guclo eqit_clo_bind. econstructor; eauto.
    eapply reflexivity.
    intros; subst.
    gstep; econstructor; eauto with paco.
  Qed.

  #[global]
  Instance eutt_interp {E F R} (f : E ~> itree F)
    : Proper (eutt eq ==> eutt eq) (interp f (T0 := R)).
  Proof.
    repeat red.
    ginit. pcofix CIH. intros.

    rewrite !unfold_interp. punfold H0. red in H0.
    induction H0; intros; subst; pclearbot; simpl.
    - gstep. constructor. eauto.
    - gstep. constructor. eauto with paco.
    - guclo eqit_clo_bind; econstructor; eauto. eapply reflexivity.
      intros; subst.
      gstep; constructor; eauto with paco.
    - rewrite tau_euttge, unfold_interp. auto.
    - rewrite tau_euttge, unfold_interp. auto.
  Qed.

  #[global]
  Definition eutt_interp' {E F : Type -> Type} {R1 R2 : Type} (RR: R1 -> R2 -> Prop) (f : E ~> itree F) :
    ProperH (eutt RR ~~> eutt RR) (interp f (T0 := R1)) (interp f (T0 := R2)).
  Proof.
    repeat red.
    einit.
    ecofix CIH. intros.
    rewrite !unfold_interp.
    punfold H0.
    induction H0; intros; subst; pclearbot; simpl.
    - estep.
    - estep.
    - ebind; econstructor.
      + reflexivity.
      + intros; subst. estep. ebase.
    - rewrite tau_euttge, unfold_interp. eauto.
    - rewrite tau_euttge, unfold_interp. eauto.
  Qed.

  #[global]
  Instance itree_morph_ret:
    forall (E F : Type -> Type) (f : E ~> itree F),
      MorphRet (itree E) (itree F) (itree_interp f).
  Proof. repeat intro. setoid_rewrite unfold_interp. cbn.
        apply eqit_Ret; eauto. Qed.

  Lemma itree_interp_tau {E F R} {f : E ~> itree F} (t: itree E R):
    eq_itree eq (interp f (Tau t)) (Tau (interp f t)).
  Proof. rewrite unfold_interp. reflexivity. Qed.

  Lemma itree_interp_vis {E F R} {f : E ~> itree F} U (e: E U) (k: U -> itree E R) :
    eq_itree eq (interp f (Vis e k)) (ITree.bind (f _ e) (fun x => Tau (interp f (k x)))).
  Proof. rewrite unfold_interp. reflexivity. Qed.

  Lemma itree_interp_bind {E F R S}
        (f : E ~> itree F) (t : itree E R) (k : R -> itree E S) :
      interp f (ITree.bind t k)
    ≅ ITree.bind (interp f t) (fun r => interp f (k r)).
  Proof.
    revert R t k. ginit. pcofix CIH; intros.
    rewrite unfold_bind, (unfold_interp t).
    destruct (observe t); cbn.
    - rewrite Eq.bind_ret_l. apply reflexivity.
    - rewrite bind_tau, !itree_interp_tau.
      gstep. econstructor. eauto with paco.
    - rewrite itree_interp_vis, Eq.bind_bind.
      guclo eqit_clo_bind; econstructor; try reflexivity.
      intros; subst.
      rewrite bind_tau. gstep; constructor; eauto with paco.
  Qed.

  #[global]
  Instance itree_morph_bind:
    forall (E F : Type -> Type) (f : E ~> itree F),
      MorphBind (itree E) (itree F) (itree_interp f).
  Proof.
    repeat intro. setoid_rewrite itree_interp_bind.
    eapply eutt_clo_bind. eapply eutt_interp'; eauto.
    intros. eapply eutt_interp'; eauto. eapply H0; eauto.
  Qed.

  #[global] Instance itree_MonadMorphism :
    forall (E F : Type -> Type) (f : E ~> itree F),
      MonadMorphism _ _ (itree_interp f).
  Proof.
    constructor; [constructor; try typeclasses eauto |..]; try typeclasses eauto.
    repeat intro; eapply eutt_interp'; repeat intro; eauto.
  Qed.

  Lemma itree_interp_iter' {E F} (f : E ~> itree F) {I A}
        (t  : I -> itree E (I + A))
        (t' : I -> itree F (I + A))
        (EQ_t : forall i, eq_itree eq (interp f (t i)) (t' i))
    : forall i,
      interp f (ITree.iter t i)
    ≅ ITree.iter t' i.
  Proof.
    ginit. pcofix CIH; intros i.
    rewrite 2 unfold_iter.
    rewrite itree_interp_bind.
    guclo eqit_clo_bind; econstructor; eauto.
    { apply EQ_t. }
    intros [] _ []; cbn.
    - rewrite itree_interp_tau; gstep; constructor; auto with paco.
    - setoid_rewrite unfold_interp. cbn. gstep; constructor; auto with paco.
  Qed.

  Lemma itree_interp_iter {E F} (f : E ~> itree F) {A B}
        (t : A -> itree E (A + B)) a0
    : interp f (iter (C := ktree E) t a0) ≅ iter (C := ktree F) (fun a => interp f (t a)) a0.
  Proof.
    unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree.
    apply itree_interp_iter'.
    reflexivity.
  Qed.

  #[global] Instance itree_IterMorphism:
    forall (E F : Type -> Type) (f : E ~> itree F),
      IterMorphism (itree_interp f).
  Proof.
    unfold IterMorphism. cbn.
    ginit. gcofix CIH; intros. cbn.
    setoid_rewrite unfold_iter at 2.
    setoid_rewrite unfold_iter at 2. cbn.
    pose proof @itree_interp_bind. setoid_rewrite H. clear H.
    guclo eqit_clo_bind; econstructor; eauto.
    - apply H0; eauto.
    - intros [|] [ |] H; cbn; subst; inv H.
      + setoid_rewrite itree_interp_tau.
        gstep; constructor. gfinal. left. eapply CIH; eauto.
      + pose proof @itree_morph_ret. cbn in H. unfold MorphRet in H.
        unfold morph in H.
        specialize (H E F f R _ eq r1 _ eq_refl).
        gfinal. right. cbn in H.
        eapply paco2_mon; eauto; intros; contradiction.
  Qed.

End InterpITree.

(* Facts about [interp] *)
Section Facts.

  Context {T : (Type -> Type) -> Type -> Type} {M : Type -> Type}
          {T_MonadT:MonadT T}
          {T_HFunctor:HFunctor T}
          {T_MonadIter:(forall m : Type -> Type, Monad m -> MonadIter m -> MonadIter (T m))}
          {WF_IMT : WF_IterativeMonadT T  _ _}
          {T_wf : @WF_HFunctor T _ _ _ _}
          {M_Monad : Monad M}
          {M_EqmR : EqmR M}
          {M_MonadIter : MonadIter M}
          {M_wf : WF_IterativeMonad M _ _ _}
          {itree_monad_morphism : forall (E : Type -> Type) (f : E ~> M), MonadMorphism (itree_interp (I := E) f)}
          {itree_iter_morphism : forall (E : Type -> Type) (f : E ~> M), IterMorphism (itree_interp (I := E) f)}.

  #[local] Instance M_IM: IterativeMonad M. constructor; eauto. Defined.

  (** ** [interp] and constructors *)
  (** These are specializations of [unfold_interp], which can be added as
      rewrite hints. *)
  Lemma _interp_ret {E R} (f : E ~> M) (x: R):
    eqmR (m := T M) eq (interp f (ret x)) (ret x).
  Proof.
    unfold interp. unfold stack_interp.
    pose proof (@hfmap_nat T _ _ _ _ _ _ _ _ _ _ _ _ _ (itree_interp (I := E) f) _).
    destruct H.
    eapply morph_ret; eauto.
  Qed.

  Ltac unfold_cat := unfold cat, Cat_Kleisli.

  Lemma _interp_bind {E R S} (f : E ~> M) (k : R -> _ S) t:
    eqmR (m := T M) eq (interp f (bind t k))
        (bind (interp f t) (fun r => interp f (k r))).
  Proof.
    eapply MM_morph_bind; eauto; try typeclasses eauto.

    Unshelve. 3 : exact eq.
    all : intros; subst; eapply reflexivity.
  Qed.

  Lemma _interp_trigger {R E} (f : E ~> M) (e : E R) :
    eqmR (m := T M) eq (interp f (trigger e)) (morph (f _ e)).
  Proof.
    { pose proof @hfmap_lift as Hlift.
      specialize (Hlift T _ _ _).

      specialize (Hlift _ _ R (itree E) M).
      specialize (Hlift _ _).
      specialize (Hlift _ _ _ _ _ _ (itree_interp f)).
      etransitivity.
      eapply Hlift; typeclasses eauto.

      eapply morph_proper; try typeclasses eauto.

      unfold ITree.trigger. unfold interp.
      unfold Basics.iter, MonadIter_itree, Kleisli_MonadIter.
      pose proof (iter_unfold (C := Kleisli M)) as Hunfold.
      specialize (Hunfold _ _ (interp_body f R)).
      specialize (Hunfold (trigger e)).
      unfold_cat; cbn. unfold iter, Iter_Kleisli in Hunfold. rewrite Hunfold.
      unfold_cat. unfold case_, Case_Kleisli, Function.case_sum.

      eapply Proper_eqmR_eq_impl; try typeclasses eauto.
      2 : symmetry; eapply (bind_ret_r (f R e)).
      2 : reflexivity.
      unfold id_.

      eapply Proper_bind.
      { unfold interp_body; cbn. setoid_rewrite <- bind_ret_r at 5.
        eapply Proper_bind. unfold id_. reflexivity.
        all : intros; subst. Unshelve.
        2 : exact(fun x y => match x with
                          | inl a => a = Ret y
                          | _ => False end).
        all : eapply eqmR_ret; try typeclasses eauto; try reflexivity. }
      all : intros; cbn; destruct a1; inv H.
      { unfold Basics.iter, MonadIter_itree. clear Hunfold.
        pose proof (iter_unfold (C := Kleisli M)) as Hunfold.
        specialize (Hunfold _ _ (interp_body f R) (ret a2)).
        unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree in Hunfold.
        rewrite Hunfold.
        unfold_cat; cbn. rewrite bind_ret_l. cbn.
        apply eqmR_ret; eauto.
        typeclasses eauto. } }
  Qed.


  Lemma _interp_over_trigger:
    forall (E F : Type -> Type) (R : Type) (G : Type -> Type) (S : E +? G -< F)
      (S_wf : Subevent_wf S)
      (M_Trigger : Trigger G M)
      (f : E ~> M) (e : E R),
      interp (over f) (trigger e : T (itree F) R) ≋ morph (f _ e).
  Proof.
    intros E F R G S ? M_Trigger f e.
    { pose proof @hfmap_lift as Hlift.
      unfold interp, stack_interp.
      specialize (Hlift T _ _ _).
      specialize (Hlift _ _  R _ _ _ _ _ _ _ _ _ _ (itree_interp (over f)) _).
      etransitivity.

      eapply Hlift; typeclasses eauto.

      eapply morph_proper; try typeclasses eauto.

      unfold ITree.trigger. unfold interp.
      unfold Basics.iter, MonadIter_itree, Kleisli_MonadIter.
      pose proof (iter_unfold (C := Kleisli M)) as Hunfold.
      specialize (Hunfold _ _ (interp_body (over f) R)).
      specialize (Hunfold (trigger e)).
      unfold_cat; cbn. unfold iter, Iter_Kleisli in Hunfold. rewrite Hunfold.
      unfold_cat. unfold case_, Case_Kleisli, Function.case_sum.

      eapply Proper_eqmR_eq_impl; try typeclasses eauto.
      3 : reflexivity.
      unfold id_.

      eapply Proper_bind.
      { unfold interp_body; cbn. setoid_rewrite <- bind_ret_r.
        rewrite bind_bind. setoid_rewrite bind_ret_r.
        eapply Proper_bind. unfold id_. reflexivity.
        all : intros; subst. Unshelve.
        3 : exact (fun x => ret (inl (Ret x))).
        reflexivity. shelve. }
      all: intros; subst.
      Unshelve.
      3 : exact (fun a2 =>
          match a2 with
          | inl a => Basics.iter (interp_body (over f) R) a
          | inr b => Id_Kleisli R b
          end).
      reflexivity.
      rewrite bind_bind. setoid_rewrite bind_ret_l.
      setoid_rewrite <- bind_ret_r at 1.
      eapply eqmR_bind_ProperH_simple; [typeclasses eauto | ..]; intros; subst.
      { unfold over. unfold inj1, inl_, Inl_sum1, case.
        unfold_cat; unfold Cat_IFun.
        clear Hunfold.
        pose proof (iter_unfold (C := Kleisli M)) as Hunfold.
        specialize (Hunfold _ _ (interp_body (over f) R)).
        unfold iter, Iter_Kleisli in Hunfold. repeat red in Hunfold.
        pose proof @sub_iso as Hiso.
        specialize (Hiso _ _ _ S _). destruct Hiso.
        repeat red in iso_epi.
        unfold cat, Cat_IFun in iso_epi.
        rewrite iso_epi. cbn.
        reflexivity. }
      { unfold Basics.iter, MonadIter_itree. clear Hunfold.
        pose proof (iter_unfold (C := Kleisli M)) as Hunfold.
        specialize (Hunfold _ _ (interp_body (over f) R) (ret a2)).
        unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree in Hunfold.
        rewrite Hunfold.
        unfold_cat; cbn. rewrite bind_ret_l. cbn.
        apply eqmR_ret; eauto.
        typeclasses eauto. } }
  Qed.

  Lemma _interp_over_ignore_trigger:
    forall (A B C BC ABC : Type -> Type) (S : B +? C -< BC) (S' : A +? BC -< ABC)
      (S_wf : Subevent_wf S) (S'_wf : Subevent_wf S')
      (R : Type) (h : forall T0 : Type, A T0 -> M T0)
            (e : B R) (Tr : Trigger BC M),
      eqmR eq
           (interp (IM := itree) (T := T) (I := ABC) (M := M) (over h)
                   (trigger (E := B) e))
           (morph (MT := T M) (trigger (E := BC) (inj1 e))).
   Proof.
     intros A B C BC ABC S S' ? ? R h e Tr.
     pose proof @hfmap_lift as Hlift.
     specialize (Hlift T _ _ _ _ _ R (itree ABC) M _ _ _ _ _ _ _ _ (itree_interp (over h)) _).
     etransitivity.
     eapply Hlift. clear Hlift.

     eapply morph_proper.


    unfold ITree.trigger. unfold interp.
    unfold Basics.iter, MonadIter_itree, Kleisli_MonadIter.
    pose proof (iter_unfold (C := Kleisli M)) as Hunfold.
    specialize (Hunfold _ _ (interp_body (over h) R)).
    specialize (Hunfold (trigger e)).
    unfold_cat; cbn. unfold iter, Iter_Kleisli in Hunfold. rewrite Hunfold.
    unfold_cat. unfold case_, Case_Kleisli, Function.case_sum.

    eapply Proper_eqmR_eq_impl; try typeclasses eauto.
    3 : reflexivity.
    2 : symmetry; eapply (bind_ret_r (trigger (inj1 e))).
    unfold id_, Id_Kleisli.

    eapply eqmR_bind_ProperH_simple; [ typeclasses eauto | ..].
    { unfold interp_body; cbn. setoid_rewrite <- bind_ret_r at 5.
      eapply eqmR_bind_ProperH_simple; [ typeclasses eauto | ..].
      unfold_cat. unfold Cat_IFun, over.
      unfold case.
      pose proof @sub_iso as Hiso.
      specialize (Hiso _ _ _ S' _). destruct Hiso.
      repeat red in iso_epi.
      unfold cat, Cat_IFun in iso_epi.
      rewrite iso_epi. cbn.

      repeat red in iso_mono.
      unfold cat, Cat_IFun in iso_mono.
      unfold inj1. unfold_cat. unfold Cat_IFun. reflexivity.
      intros; subst; apply eqmR_ret; try typeclasses eauto.
      Unshelve.
      2 : exact(fun x y => match x with
                        | inl a => a = Ret y
                        | _ => False end). cbn. reflexivity. }
    all : intros; cbn; destruct a1; inv H.
    { unfold Basics.iter, MonadIter_itree. clear Hunfold.
      pose proof (iter_unfold (C := Kleisli M)) as Hunfold.
      specialize (Hunfold _ _ (interp_body (over h) R) (ret a2)).
      unfold iter, Iter_Kleisli, Basics.iter, MonadIter_itree in Hunfold.
      rewrite Hunfold.
      unfold_cat; cbn. rewrite bind_ret_l. cbn.
      apply eqmR_ret; eauto.
      typeclasses eauto. }
   Qed.

  Lemma _interp_iter {I E R} (f : E ~> M) t t' (i:I):
    (forall i, eqmR eq (interp f (t i)) (t' i)) ->
      interp f
        (@Basics.iter (T (itree E)) _ R I t i)
      ≈{ @eq R
      } @Basics.iter (T M) _ R I t' i.
  Proof.
    cbn. intros.

    pose proof (@hfmap_iter T _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (itree_interp f) _ _).
    eapply H0; eauto.
  Qed.

  Lemma _interp_proper {E} :
    forall (h : forall T0 : Type, E T0 -> M T0) (R1 R2 : Type) (RR : R1 -> R2 -> Prop),
      ProperH (eqmR (m := T (itree E)) RR ~~> eqmR (B := R2) RR)
            (fun t => interp h t) (fun t => interp h t).
  Proof.
    cbn. repeat intro.
    pose proof (@hfmap_nat T _ _ _ _ _ _ _ _ _ _ _ _ _ (itree_interp h) _).
    destruct H0.
    eapply morph_proper; eauto.
  Qed.

  Global Instance InterpLaws_: InterpLaws T M.
  constructor; repeat intro.
  apply _interp_ret.
  apply _interp_trigger.
  apply _interp_over_ignore_trigger; eauto.
  apply _interp_bind.
  apply _interp_iter; auto.
  apply _interp_proper; auto.
  Qed.

End Facts.

#[global] Program Instance WF_IterativeMonad_Trans T M `{T_WF_IterativeMonadT : WF_IterativeMonadT T}
 `{M_WF_IterativeMonad : WF_IterativeMonad M} : WF_IterativeMonad (T M) _ _ _.

#[global] Instance IterativeMonad_itree E : IterativeMonad (itree E).
Proof.
  constructor; repeat intro; try constructor; intros; eauto.
  exact (ret X).
  exact (bind X X0).
  exact (eqmR R).
  exact (observe (ITree.iter X X0)).
Defined.

(* Facts about [interp] when the *base monad* is an ITree. *)
Section Facts.

  Context {T : (Type -> Type) -> Type -> Type} {F : Type -> Type}
          {T_MonadT:IterativeMonadT T}
          {T_HFunctor:HFunctor T}
          {T_WF_IterativeMonadT : WF_IterativeMonadT T _ _}
          {T_wf : @WF_HFunctor T _ _ _ _}
          {itree_monad_morphism : forall (E : Type -> Type) (f : E ~> T (itree F)), MonadMorphism (itree_interp (I := E) f)}
          {itree_iter_morphism : forall (E : Type -> Type) (f : E ~> T (itree F)),
              IterMorphism (itree_interp (I := E) f)}.

  #[global] Instance IM_TF : IterativeMonad (T (itree F)).
  constructor; try typeclasses eauto.
  Defined.

  #[global] Instance InterpLaws_itree_base :
    InterpLaws (fun x => x) (T (itree F)) (TM_Interp := stack_interp).
  eapply InterpLaws_.
  Defined.

End Facts.
