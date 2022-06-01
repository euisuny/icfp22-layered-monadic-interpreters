From Coq Require Import
     Logic.FunctionalExtensionality
     Morphisms
     Setoid.

From ExtLib Require Import
     Structures.Monad
     Structures.Functor.

From ITree Require Import
     Basics.HeterogeneousRelations Basics.Tacs
     EqmR.EqmRMonad
     EqmR.EqmRMonadT.

Import FunctorNotation.
Import MonadNotation.
Import RelNotations.
Local Open Scope cat_scope.
Local Open Scope monad_scope.
Local Open Scope relationH_scope.

Definition errorT (exn: Type) (m: Type -> Type) (A: Type) : Type :=
  m (sum exn A).

Global Instance MonadT_errorT {exn} {M} {M_Monad : Monad M} : MonadTrans.MonadT (errorT exn M) M :=
  {| MonadTrans.lift := fun (t : Type) (X : M t) => x <- X;; ret (inr x) |}.

Section Monad_Error.
  Variable m : Type -> Type.
  Variable exn : Type.
  Context {EqmRm : EqmR m}.
  Context {Mm: Monad m}.
  Context {EqmROKm : EqmR_OK m}.
  Context {MLm: EqmRMonadLaws m}.
  Context {MLmI: EqmRInversionProperties m}.

  Notation errorT := (errorT exn m).

  Global Instance Monad_errorT : Monad errorT
    := {|
        ret _ a := ret (inr a)
        ; bind _ _ t k :=
            bind (m := m) t
                 (fun x =>
                    match x with
                    | inl e => ret (inl e)
                    | inr a => k a
                    end)
      |}.

  #[global] Instance EqmR_errorT : EqmR errorT :=
    {| eqmR := fun _ _ R => eqmR (sum_rel eq R) |}.

  Ltac unfold_error := unfold eqmR, EqmR_errorT, errorT in *.

  Ltac sumtac :=
    repeat
      match goal with
      | [H : inl _ = _ |- _] => inv H
      | [H : inr _ = _ |- _] => inv H
      end.

  Instance eqmR_prod_rel_errorT : RelProd errorT.
  Proof.
    repeat intro.
    cbn in *. red in m1, m2.

    assert (forall A B, (fun x : sum exn (prod A B) =>
              match x with
              | inl e => ret (m := m) (inl e)
              | inr a => ret (m := m) (inr (snd a))
            end) =
            fun y => ret (m := m) ((fun x => match x with | inl e => (inl e) | inr a => (inr (snd a)) end) y)
           ). {
      intros. apply functional_extensionality.
      intros. destruct x; eauto.
    }
    assert (forall A B, (fun x : sum exn (prod A B) =>
              match x with
              | inl e => ret (m := m) (inl e)
              | inr a => ret (m := m) (inr (fst a))
            end) =
            fun y => ret (m := m) ((fun x => match x with | inl e => (inl e) | inr a => (inr (fst a)) end) y)
           ). {
      intros; apply functional_extensionality.
      intros. destruct x; eauto.
    }
    rewrite !H1 in H0.
    rewrite !H2 in H. clear H1 H2.
    (* IY : Why doesn't [rewrite eqmR_sum_rel] work here? *)
    pose proof rel_sum as SR.
    rewrite SR.
    intros.

    eapply fmap_inv in H; eauto.
    eapply fmap_inv in H0; eauto.
    unfold fmap.
    eapply eqmR_bind_ProperH;[eauto|..].
    eapply rel_conj;[eauto|..]. apply H.

    - intros. cbn in H3. crunch.
      destruct a1; crunch; eauto;
        destruct a2; crunch; eauto;
        apply eqmR_ret; eauto.
      all : inv H3; inv H4; subst; eauto.
      apply H2. destruct p, p0. constructor; cbn in *; auto.
  Qed.

  Instance eqmR_prod_fst_inv_errorT : FmapFst errorT.
  Proof.
    repeat intro. red in H. red.
    unfold fmap. cbn. eapply eqmR_bind_ProperH; eauto.
    - intros. destruct a1, a2; apply eqmR_ret; inv H0; eauto.
      destruct p, p0; inv H3; eauto.
  Qed.

  Instance eqmR_prod_snd_inv_errorT : FmapSnd errorT.
  Proof.
    repeat intro. red in H. red.
    unfold fmap. cbn. eapply eqmR_bind_ProperH; eauto.
    - intros. destruct a1, a2; apply eqmR_ret; inv H0; eauto.
      destruct p, p0; inv H3; eauto.
  Qed.

  Instance eqmR_sum_inl_errorT : FmapInl errorT.
  Proof.
    repeat intro. red in H. red.
    unfold fmap; cbn; eapply eqmR_bind_ProperH; eauto.
    - intros. destruct a1, a2; apply eqmR_ret; inv H0; eauto.
  Qed.

  Instance eqmR_sum_inr_errorT : FmapInr errorT.
  Proof.
    repeat intro. red in H. red.
    unfold fmap; cbn; eapply eqmR_bind_ProperH; eauto.
    - intros. destruct a1, a2; apply eqmR_ret; inv H0; eauto.
  Qed.

  Instance eqmR_sum_rel_errorT : RelSum errorT.
  Proof.
    repeat intro. split.
    - intros; red in H. red. unfold fmap; cbn; eapply eqmR_bind_ProperH; eauto.
      + intros. destruct a1, a2; apply eqmR_ret; eauto; inv H2. constructor; eauto.
        constructor. destruct s, s0; eauto.
        all: inv H5. apply H0; auto. apply H1; auto.
    - intros. red in H.
      specialize (H (A1 + B1)%type (A2 + B2)%type inl inl inr inr (RA ⊕ RB)).
      assert (inl_P: ProperH (respectfulH A1 A2 (A1 + B1) (A2 + B2) RA (RA ⊕ RB)) inl inl) by
        (intros; constructor; eauto).
      assert (inr_P: ProperH (respectfulH B1 B2 (A1 + B1) (A2 + B2) RB (RA ⊕ RB)) inr inr) by
        (intros; constructor; eauto).
      specialize (H inl_P inr_P). cbn in H.
    assert (forall A B C, (fun x : C + (A + B) =>
              match x with
              | inl e => ret (m := m) (inl e)
              | inr a => ret (m := m) (inr match a with
                                          | inl a0 => inl a0
                                          | inr b => inr b end)
            end) =
            fun y => ret (m := m) ((fun x => match x with | inl e => (inl e) | inr a => (inr ( match a with
                           | inl a0 => inl a0
                           | inr b => inr b
                           end)) end) y)
           ). {
      intros. apply functional_extensionality.
      intros. destruct x; eauto.
    }
    rewrite !H0 in H.
    apply fmap_inv in H. repeat red.
    eapply Proper_eqmR_mono ; eauto.
    repeat intro. destruct x, y; eauto; inv H1; eauto; inv H4; cbn in *;
    destruct s, s0; eauto; inv H1; inv H2; constructor; constructor; auto.
  Qed.

  Instance eqmR_conj_errorT : RelConj errorT.
  Proof.
    repeat intro. red in H, H0. red.
    eapply rel_sum.
    intros. unfold fmap; eapply Proper_bind.
    eapply rel_conj; [ apply H | apply H0 ].
    - intros. inv H3. apply final; eauto. destruct a1, a2; inv H5; inv H4; auto.
  Qed.

  Instance eqmR_transport_PER_errorT : TransportPER errorT.
  Proof.
    destruct EqmROKm. red. intros; eapply eqmR_transport_PER.
    split; [eapply sum_rel_sym | eapply sum_rel_trans]; try typeclasses eauto.
  Qed.

  Instance eqmR_rel_comp_errorT : RelComp errorT.
  Proof.
    red; intros. red. red in H, H0.
    eapply Proper_eqmR; eauto.
    eapply Proper_sum_rel. setoid_rewrite <-eq_id_l. reflexivity.
    reflexivity.
    eapply Proper_eqmR; eauto.
    rewrite sum_compose. reflexivity.
    eapply eqmR_rel_comp; eauto.
  Qed.

  Instance eqmR_lift_transpose_errorT : LiftTranspose errorT.
  Proof.
    intros!; split; intros!.
    - (* TODO: Rewrite fails here for a reason unbeknownst to me.
          See https://coq.discourse.group/t/confused-with-a-failure-of-a-generalized-rewrite/783
        *)
      pose proof eqmR_lift_transpose.
      specialize (H0 m _ _ _ _ _ (@eq exn ⊕ R)).
      do 2 red.
      eapply H0.
      eapply Proper_eqmR; eauto.
      rewrite transpose_sum. 
      rewrite HeterogeneousRelations.transpose_eq; auto. reflexivity.
    - red. eapply Proper_eqmR; auto.
      rewrite <- HeterogeneousRelations.transpose_eq, <- transpose_sum; auto. reflexivity. auto.
      eapply eqmR_lift_transpose; eauto.
  Qed.

  Instance eqmR_Proper_errorT :
    forall A B : Type, Proper (eq_rel ==> eq_rel) (fun R : relationH A B => eqmR (m := errorT) R).
  Proof.
    repeat intro. repeat red. split; repeat intro.
    red. red in H0. eapply Proper_eqmR; eauto. rewrite H. reflexivity.
    red. red in H0. eapply Proper_eqmR; eauto. rewrite H. reflexivity.
  Qed.

  Instance eqmR_Proper_mono_errorT :
    forall A B : Type, Proper (subrelationH (B:=B) ==> subrelationH (B:=m (exn + B))) (fun R : relationH A B => eqmR R).
  Proof.
    intros!. red. red in H0.
    eapply Proper_eqmR_mono; eauto.
    eapply sum_rel_monotone; eauto.
    apply subrelation_refl.
  Qed.

  Instance transport_refl: TransportReflexive errorT.
  repeat intro; repeat red; eapply refl; typeclasses eauto.
  Qed.

  Global Instance EqMProps_errorT : EqmR_OK errorT.
  Proof.
    constructor; try typeclasses eauto.
  Qed.

  Lemma mayRet_errorT :
    forall (A : Type) (ma : errorT A) (a : A), a ∈ ma <-> (mayRet m ma (inr a)).
  Proof.
    intros. split; intros; red in H; repeat intro.
    - repeat red in H.
      specialize (H (fun x y => R (inr x) (inr y))).
      eapply H.
      split; repeat intro; crunch; subst; eauto. cbn. symmetry; auto. etransitivity; eauto.
      cbn. eapply rel_sum; eauto.
      repeat intro.
      unfold fmap. eapply eqmR_bind_ProperH.
      eauto. eapply rel_conj. eauto.
      eapply refl; typeclasses eauto. eauto.
      intros; apply eqmR_ret; eauto; inv H2; destruct a2.
      apply H0; eauto.
      apply H1; eauto.
    - repeat red in H.
      specialize (H (fun x y => match x, y with | inr a, inr b => R a b | _, _ => x = y end)).
      eapply H.
      split; repeat intro; eauto. destruct x, y; eauto. symmetry; auto.
      destruct x, y, z; eauto. inv H0; inv H1. auto. all : try sumtac.
      etransitivity; eauto.
      eapply Proper_eqmR_mono; eauto. repeat intro. inv H0; auto.
  Qed.

  Instance eqmR_mayRet_l_errorT : MayRetL errorT.
  Proof.
    repeat intro.
    red in EQH.
    eapply eqmR_mayRet_l in EQH. 2 : eauto.
    specialize (EQH (inr a1)).
    destruct EQH.

    repeat red in H.
    repeat intro.
    specialize (H (fun x y => R (inr x) (inr y))).
    eapply H.
    split; repeat intro; crunch; subst; eauto. cbn. symmetry; auto. etransitivity; eauto.

    cbn. eapply rel_sum; eauto.
    repeat intro.
    unfold fmap. eapply eqmR_bind_ProperH.
    eauto. eapply rel_conj. eauto.
    eapply refl; typeclasses eauto. 
    intros; apply eqmR_ret; eauto; inv H2; destruct a2.
    apply H0; eauto.
    apply H1; eauto.
    inv H0. inv H1. exists b2. split; eauto.
    repeat intro. repeat red in H2.
    specialize (H2 (fun x y => match x, y with | inr a, inr b => R a b | _, _ => x = y end)).
    eapply H2.
    split; repeat intro; eauto. destruct x, y; eauto. symmetry; auto.
    destruct x, y, z; eauto. inv H0; inv H1. auto. all : try sumtac.
    etransitivity; eauto.
    eapply Proper_eqmR_mono; eauto. repeat intro. inv H0; auto.
  Qed.

  Instance eqmR_mayRet_r_errorT : MayRetR errorT.
  Proof.
    repeat intro.
    red in EQH.
    eapply eqmR_mayRet_r in EQH. 2 : eauto.
    specialize (EQH (inr a2)).
    destruct EQH. repeat red in H.
    repeat intro.
    specialize (H (fun x y => R (inr x) (inr y))).
    eapply H.
    split; repeat intro; crunch; subst; eauto. cbn. symmetry; auto. etransitivity; eauto.
    cbn. eapply rel_sum; eauto.
    repeat intro.
    unfold fmap. eapply eqmR_bind_ProperH.
    eauto. eapply rel_conj. eauto.
    eapply refl; typeclasses eauto. 
    intros; apply eqmR_ret; eauto; inv H2; destruct a0.
    apply H0; eauto.
    apply H1; eauto.
    inv H0. inv H1. exists b1. split; eauto.
    repeat intro. repeat red in H2.
    specialize (H2 (fun x y => match x, y with | inr a, inr b => R a b | _, _ => x = y end)).
    eapply H2.
    split; repeat intro; eauto. destruct x, y; eauto. symmetry; auto.
    destruct x, y, z; eauto. inv H0; inv H1. auto. all : try sumtac.
    etransitivity; eauto.
    eapply Proper_eqmR_mono; eauto. repeat intro. inv H0; auto.
  Qed.

  Instance eqmR_ret_errorT : RetFinal errorT.
  Proof.
    red; cbn; intros!.
      apply eqmR_ret; auto.
  Qed.

  Instance eqmR_bind_ProperH_errorT : ProperBind errorT.
  Proof.
    red;
    cbn; intros * PRE; intros EQ1.
    eapply eqmR_bind_ProperH; [auto | apply PRE |..].
    all : intros; invn sum_rel; auto.
    apply eqmR_ret; auto.
  Qed.

  Instance eqmR_bind_ret_l_errorT : BindRetL errorT.
  Proof.
    red. intros; cbn.
    eapply Proper_eqmR ; eauto.
    apply sum_rel_eq.
    rewrite bind_ret_l. reflexivity.
  Qed.

  Instance eqmR_bind_ret_r_errorT : BindRetR errorT.
  Proof.
    intros!; cbn.
    eapply Proper_eqmR; eauto.
    apply sum_rel_eq. red in ma.
    rewrite <- (bind_ret_r ma) at 2.
    apply Proper_bind with (RR := eq); [ reflexivity | ..];
      intros; subst; destruct a2; apply final; eauto.
  Qed.

  Instance eqmR_bind_bind_errorT : BindBind errorT.
  Proof.
    red. intros; cbn.
    eapply Proper_eqmR; eauto.
    apply sum_rel_eq.
    rewrite bind_bind.

    apply Proper_bind with (RR := eq); [ reflexivity | ..];
      intros; subst; destruct a2.
    rewrite bind_ret_l; apply final; auto.
    reflexivity.
  Qed.

  Global Instance EqmRMonad_errorT : EqmRMonadLaws errorT.
  Proof.
    constructor; try typeclasses eauto.
    repeat intro. eapply eqmR_rel_sum; [typeclasses eauto | ..].
    intros.
    unfold fmap. eapply Proper_bind.
    eapply image_post. typeclasses eauto. reflexivity. intros.
    eapply eqmR_ret; eauto. destruct H1 as(?&?&?). subst.
    destruct a2. eapply H. reflexivity. eapply H0.
    rewrite <- mayRet_errorT in H2. eauto.
  Qed.

  Instance eqmR_ret_inv_errorT : RetInv errorT.
  Proof.
    repeat intro.
    cbn in H. apply eqmR_ret_inv in H; eauto. inv H. auto.
  Qed.

  Instance mayRet_bind_inv_errorT : MayRetBindInv errorT.
  Proof.
    repeat intro.
    cbn in H. apply mayRet_errorT in H.
    apply eqmR_mayRet_bind_inv in H; auto. crunch. destruct x.
    repeat red in H0.
    exfalso.
    specialize (H0 (fun x y => match x, y with
                            | inl a, inl b => a = b /\ a = e
                            | _, _ => False
                            end)).
    eapply H0; clear H0. split; repeat intro; eauto.
    destruct x, y; eauto. crunch; subst; auto.
    destruct x, y, z; eauto. crunch; subst; auto. inv H0.
    apply eqmR_ret; eauto.
    exists a. rewrite !mayRet_errorT. split; auto.
  Qed.

  Instance fmap_inv_errorT : FmapInv errorT.
  Proof.
    repeat intro.
    cbn in H.
    assert (forall A B (f : A -> B), (fun x : sum exn A =>
              match x with
              | inl e => ret (m := m) (inl e)
              | inr a => ret (m := m) (inr (f a))
            end) =
            fun y => ret (m := m) ((fun x => match x with | inl e => (inl e) | inr a => (inr (f a)) end) y)
           ). {
      intros. apply functional_extensionality.
      intros. destruct x; eauto.
    }
    rewrite !H0 in H.
    apply fmap_inv in H. red.
    eapply Proper_eqmR_mono; eauto.
    repeat intro. crunch. destruct x, y; inv H1; eauto.
  Qed.

  Instance eqmR_inv_errorT: EqmRInv errorT.
  Proof.
    repeat intro.
    rewrite mayRet_errorT in H0. cbn in H.
    eapply eqmR_inv in H; eauto. 2 : typeclasses eauto. inv H; auto.
  Qed.

  Global Instance EqmRMonadInverses_errorT : EqmRInversionProperties errorT.
  Proof.
    constructor; try typeclasses eauto.
  Qed.

  Global Instance EQM_errorT : EQM errorT _.
  Proof.
    econstructor; typeclasses eauto.
  Qed.

End Monad_Error.

Section MonadT_Error.

  Context (exn:Type).

  #[global ] Instance lift_errorT : MonadT (errorT exn) :=
    { lift := fun _ _ _ ma => inr <$> ma }.

  Arguments lift /.

  Instance MorphRet_errorT (m : Type -> Type) (Monad_m : Monad m) (EqmR_m : EqmR m)
    (EqmO_m : EqmR_OK m) (EqmM : EqmRMonadLaws m) (EqmI : EqmRInversionProperties m) :
      MorphRet m (errorT exn m) _.
  Proof.
    repeat intro.
    red. unfold lift_errorT.
    unfold fmap. cbn; unfold liftM. pose proof @eqmR_bind_ret_l. red in H0.
    rewrite bind_ret_l. apply final. constructor; auto.
  Qed.

  Instance MorphBind_errorT (m : Type -> Type) (Monad_m : Monad m) (EqmR_m : EqmR m)
    (EqmO_m : EqmR_OK m) (EqmM : EqmRMonadLaws m) (EqmI : EqmRInversionProperties m) :
      MorphBind m (errorT exn m) _.
  Proof.
    repeat intro. unfold lift_errorT in *.
    unfold fmap. cbn; unfold liftM.
    do 2 rewrite bind_bind.
    apply Proper_bind with (RR := RA); [ apply H |]; intros; rewrite bind_ret_l.
    eapply Proper_bind; [ apply H0 | ..]; eauto; intros; apply final; eauto.
  Qed.

  Instance MorphProper_errorT (m : Type -> Type) (Monad_m : Monad m) (EqmR_m : EqmR m)
    (EqmO_m : EqmR_OK m) (EqmM : EqmRMonadLaws m) (EqmI : EqmRInversionProperties m) :
      MorphProper m (errorT exn m) _ _.
  Proof.
    repeat intro.
    repeat intro. unfold lift_errorT.
      cbn in *.
      eapply rel_sum; eauto.
      repeat intro.
      unfold fmap.
      eapply eqmR_bind_ProperH; eauto.
      eapply eqmR_bind_ProperH; eauto.
      intros. apply eqmR_ret; eauto. Unshelve. 3 : exact ((fun _ _ => False) ⊕ RR).
      constructor; auto.
      intros. apply eqmR_ret; eauto. inv H2; try inv H3.
      apply H1. auto.
  Qed.

  Global Instance MonadTransformer_errorT : MonadTLaws (errorT exn).
  Proof.
    econstructor; intros; constructor; [ constructor | ..]; typeclasses eauto.
  Qed.

End MonadT_Error.
