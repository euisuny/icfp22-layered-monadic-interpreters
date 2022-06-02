(** * EqmR-related laws for the state monad. *)

(* begin hide *)
From Coq Require Import
     Lia
     Setoid
     Morphisms.

From ExtLib Require Import
     Structures.Monad
     Structures.MonadState
     Structures.Functor.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.HeterogeneousRelations.

From ITree Require Import
     EqmR.EqmRMonad
     Basics.Tacs.

Import ITree.Basics.Basics.Monads.
Import FunctorNotation.
Import CatNotations.
Local Open Scope cat_scope.
Local Open Scope cat.

Import RelNotations.
Local Open Scope relationH_scope.

Existing Class inhabited.
(* end hide *)

Section StateEq.
  Variable S : Type.

  Definition state (s a : Type) : Type :=
    s -> s * a.

  Definition eqmR_state (A B : Type) (R : relationH A B) :=
    fun (x : state S A) (y : state S B) =>
      forall (s : S),
        R (snd (x s)) (snd (y s)) /\ fst (x s) = fst (y s).

  Lemma equal_typ {A} {x : A} : x = x. reflexivity. Qed.

  #[global]
   Instance EqmR_state : EqmR (state S) := {|eqmR := eqmR_state|}.

  (* Couple properties about state [mayRet]. *)
  Definition state_prop {A : Type} (ma : state S A) :=
    (fun a : A => exists s s', ma s = (s', a)).

  Definition const_state {A : Type} (s : S) (a : A) : S -> (S * A) :=
    fun s => (s, a).

  Lemma mayRet_state {A:Type} (ma : state S A) (a : A) :
    (exists s s' : S, (ma s) = (s', a)) <->
    a ∈ ma.
  Proof.
    split. intro.
    - edestruct H as (? & ? & ?); clear H.
      red. red. repeat intro.
      red in EQR; unfold eqmR_state in EQR.
      specialize (EQR x). crunch. subst. rewrite H0 in H; auto.
    - intros EQR. repeat red in EQR.
      epose (state_prop ma : A -> Prop) as Q.
      assert (eqmR (diagonal_prop Q) ma ma).
      { intro. cbn. split.
        - intros.
          unfold state_prop. split. repeat red.
          exists s. destruct (ma s) eqn: Hma. cbn in *. subst. eauto.
          exists s. destruct (ma s) eqn: Hma. cbn in *. subst. eauto.
        - reflexivity.
      }
      specialize (EQR (diagonal_prop Q) (diagonal_prop_PER Q) H).
      unfold diagonal_prop in EQR.
      destruct EQR. clear H1 H.
      edestruct H0 as (? & ? & ?).
      auto.
  Qed.

  (* The [eqmR_state] definition is [EqmR_OK]. *)
  Ltac destruct_hyp :=
    match goal with
    | [H : (_ /\ _) /\ fst (?x ?s0) = fst (?y ?s1) |- _] =>
      destruct H as ((? & ?) & ?); destruct (x s0) eqn: ?HX;
      destruct (y s1) eqn : ?HY; cbn in *; subst
    | [H : (_ /\ _) /\ _ = _ |- _] =>
      destruct H as ((? & ?) & <-)
    end.

  Ltac rewrite_eq :=
    do 2 match goal with
    | [H : forall _, ?x = _ -> _ |- _] => destruct (H x) as (? & ? & <-); try reflexivity; clear H
    end; eauto.

  Ltac ok_crush :=
    cbn in *;
    match goal with
    | [ x : S , H : eqmR_state _ _ _ _ _ |- _ ] => specialize (H x)
    end;
    destruct_hyp; split; [ split | ]; auto; intros * <-; rewrite_eq.

  Instance eqmR_conj_state: RelConj (state S).
  Proof.
    intros A B R1 R2 ma mb H H0.
    cbn in *. unfold eqmR_state in *.
    intros. split; cycle 1.
    specialize (H s); specialize (H0 s). crunch.
    auto.
    specialize (H s). crunch. subst.
    specialize (H0 s). crunch. subst. eauto.
    specialize (H0 s). crunch. subst. eauto.
  Qed.

  Lemma eqmR_transport_refl_St:
    forall (A : Type) (R : relationH A A), Reflexive R -> Reflexive (eqmR R).
  Proof.
    repeat intro.  split; eauto.
  Qed.

  Instance eqmR_Proper_eq_St:
    forall A B : Type, Proper (eq_rel ==> eqmR (@eq A) ==> eqmR (@eq B) ==> Basics.flip Basics.impl) eqmR.
  Proof.
    repeat intro. split; eauto; repeat red in H0, H1, H2; edestruct H0, H1, H2.
    - apply H. rewrite H3, H5. eauto.
    - edestruct H0, H1, H2. rewrite H4, H6. eauto.
      Unshelve. all: eauto.
  Qed.

  (* State monad is a monad. *)
  Definition ret_state (A : Type) (x : A) := fun s : S => (s, x).

  Definition bind_state (A B : Type) (sa : state S A) (f : A -> state S B) :=
    (fun s : S => (f (snd (sa s)) (fst (sa s)))).

  Global Instance Monad_state : Monad (state S) :=
    {|
      ret := ret_state;
      bind := bind_state
    |}.

  Global Instance MonadState_state : MonadState S (state S) :=
    {|
      get := (fun x => (x, x));
      put := (fun v => (fun _ => (v, tt)))
    |}.

  Ltac unfold_state := unfold fmap, bind, Monad_state, bind_state, ret, ret_state; cbn in *.

  Instance eqmR_prod_fst_inv_state : FmapFst (state S).
  Proof.
    repeat intro.
    repeat red in H. unfold_state.
    specialize (H s); crunch;
      destruct (m1 s) eqn: Hma; destruct (m2 s) eqn: Hma';
        cbn in *; subst; auto.
    destruct p, p0; inv H; eauto.
  Defined.

  Instance eqmR_prod_snd_inv_state : FmapSnd (state S).
  Proof.
    repeat intro.
    repeat red in H. unfold_state.
    specialize (H s); crunch;
      destruct (m1 s) eqn: Hma; destruct (m2 s) eqn: Hma';
        cbn in *; subst; auto.
    destruct p, p0; inv H; eauto.
  Defined.

  Instance eqmR_prod_rel_state : RelProd (state S).
  Proof.
    intros. red. split; eauto. red in H, H0.
    unfold eqmR_state in *.
    destruct (snd (m1 s)) eqn: Hm1.
    destruct (snd (m2 s)) eqn: Hm2.
    cbn in *. constructor; eauto.
    specialize (H s); specialize (H0 s).
    rewrite Hm1 in H, H0.
    rewrite Hm2 in H, H0.
    crunch. cbn in *; eauto.
    specialize (H s); specialize (H0 s).
    rewrite Hm1 in H, H0.
    rewrite Hm2 in H, H0.
    crunch. eauto. cbn in *; eauto.
    cbn in *; unfold eqmR_state in *; crunch; eauto.
    specialize (H s); specialize (H0 s). crunch.
    unfold bind_state, ret_state in *. cbn in *. eauto.
  Defined.

  Instance eqmR_sum_inl_state : FmapInl (state S).
  Proof.
    repeat intro.
    repeat red in H. unfold_state.
    specialize (H s); crunch;
      destruct (m1 s) eqn: Hma; destruct (m2 s) eqn: Hma';
        cbn in *; subst; auto.
  Defined.

  Instance eqmR_sum_inr_state : FmapInr (state S).
  Proof.
    repeat intro.
    repeat red in H. unfold_state.
    specialize (H s); crunch;
      destruct (m1 s) eqn: Hma; destruct (m2 s) eqn: Hma';
        cbn in *; subst; auto.
  Defined.

  Instance eqmR_sum_rel_state : RelSum (state S).
  Proof.
    repeat intro.
    repeat red in H. unfold_state.
    split; repeat intro.
    - specialize (H s); crunch;
      destruct (m1 s) eqn: Hma; destruct (m2 s) eqn: Hma';
        cbn in *; subst; auto.
      destruct s1, s3; inv H.
      apply H0. auto. apply H1; auto.
    - specialize (H (A1 + B1)%type (A2 + B2)%type inl inl inr inr (RA ⊕ RB)).
      assert (inl_P :ProperH (respectfulH A1 A2 (A1 + B1) (A2 + B2) RA (RA ⊕ RB)) inl inl) by
        (repeat intro; constructor; eauto).
      assert (inr_P: ProperH (respectfulH B1 B2 (A1 + B1) (A2 + B2) RB (RA ⊕ RB)) inr inr) by
        (repeat intro; constructor; eauto).
      destruct (m1 s) eqn: Hma; destruct (m2 s) eqn: Hma'.
      cbn.
      specialize (H inl_P inr_P s). cbn in *.
      rewrite Hma, Hma' in H; cbn in *.
      crunch; eauto.
      destruct s1, s3; crunch; eauto.
  Defined.

  Lemma eqmR_prod_sum_rel_state :
    forall (A B C : Type) (ma ma' : state S (C + A * B)%type)
      (RA : relationH A A) (RB : relationH B B) (RC : relationH C C),
      (fst_sum <$> ma) ≈{ RC ⊕ RA } (fst_sum <$> ma') ->
      (snd_sum <$> ma) ≈{ RC ⊕ RB } (snd_sum <$> ma') -> ma ≈{ RC ⊕ RA ⊗ RB } ma'.
  Proof.
    intros. repeat red in H. repeat red in H0.
    intro. specialize (H s); specialize (H0 s). crunch.
    all : unfold fmap, fst_sum, snd_sum in *.
    all : inv H0; inv H; inv H1; inv H2;
      destruct (ma s) eqn: Hma; destruct (ma' s) eqn: Hma'; cbn in *; destruct s1 eqn: Hs1; destruct s3 eqn: Hs3.
    all : eauto.
    all : repeat match goal with
          | [H : inl _ = _ |- _] => inv H
          | [H : inr _ = _ |- _] => inv H
          end; eauto.
    constructor. destruct p, p0. eauto.
  Qed.

  Instance eqmR_transport_PER_state : TransportPER (state S).
  Proof.
    split.
    - repeat intro; crunch. repeat red in H0.  symmetry. eauto.
      symmetry. edestruct H0. symmetry. eauto.
      edestruct H0. symmetry. eauto.
    - repeat intro. intros. repeat intro. unfold TransitiveH in H.
      cbn in *. unfold eqmR_state in *.
      destruct (x s) eqn: HX.
      specialize (H0 s).
      specialize (H1 s).
      crunch. subst. etransitivity; eauto.  rewrite <- HX. auto.
      cbn. rewrite HX in *. cbn in *. subst. auto.
  Defined.

  Instance eqmR_rel_comp_state : RelComp (state S).
  Proof.
    repeat intro. cbn in *. unfold eqmR_state in *.
    intros. specialize (H s). specialize (H0 s).
    destruct H. destruct H0. split; eauto. esplit; split; eauto.
    rewrite H1, H2. auto.
  Defined.

  Instance eqmR_lift_transpose_state : LiftTranspose (state S).
  Proof.
    intros.
    split; repeat intro; repeat red in H; specialize (H s) ;
      crunch; eauto.
  Defined.

  Instance eqmR_Proper_state :
    forall A B : Type, Proper (eq_rel (A:=A) (B:=B) ==> eq_rel) eqmR.
  Proof.
    repeat intro; split; repeat intro; crunch; repeat red in H0;
      specialize (H0 s); crunch; subst; try eexists; try split;
        eauto; apply H; auto.
  Defined.

  Instance eqmR_Proper_mono_state:
    forall A B : Type,
      Proper (subrelationH (A:=A) (B:=B) ==> subrelationH (B:=state S B)) eqmR.
  Proof.
    repeat intro; crunch; repeat red in H0; specialize (H0 s);
      crunch; subst; eauto.
  Defined.

  Instance eqmR_transport_Equiv_state: TransportEquiv (state S).
  Proof.
    repeat intro; destruct H; split; try typeclasses eauto.
    repeat intro; eauto.
    eapply eqmR_transport_PER_state; split; eauto.
    apply eqmR_transport_PER_state; split; eauto.
  Qed.

  Instance transport_refl : TransportReflexive (state S).
  repeat intro; eauto.
  Qed.

  Instance transport_symm : TransportSymmetric (state S).
  repeat intro; eauto. repeat red in H0. edestruct H0; eauto.
  Qed.

  Instance transport_trans : TransportTransitive (state S).
  repeat intro; eauto. repeat red in H0. edestruct H0, H1; split; subst; eauto.
  rewrite H3. auto.
  Qed.

  Global Instance EqmR_OK_state : EqmR_OK (state S).
  Proof.
    constructor; try typeclasses eauto.
  Defined.

  Opaque mayRet.

  (* EqmRMonad properties for state monad. *)
  Lemma mayRet_image :
    forall A (a: A) ma, (a ∈ ma -> image ma a a).
  Proof.
    intros. apply H.
  Qed.

  Lemma image_eqmR_state :
    forall (A : Type) (ma : state S A), ma ≈{ image ma } ma.
  Proof.
    intros. cbn. unfold eqmR_state. intros. cbn.
    destruct (ma s) eqn: Hma.
    cbn in *. split.
    - intros. repeat red. intros. repeat red in EQR.
      edestruct EQR. rewrite Hma in *. cbn in *; auto.
    - reflexivity.
  Qed.

  Instance eqmR_mayRet_l_state : MayRetL (state S).
  Proof.
    red;intros.
    rewrite <- mayRet_state in H. edestruct H as (? & ? & ?); clear H.
    cbn in *.
    destruct (ma1 x) eqn: Hma. cbn in *.
    inv H0. rename EQH into H.
    unfold eqmR_state in H. cbn in H.
    specialize (H x). setoid_rewrite Hma in H.
    cbn in *. setoid_rewrite <- mayRet_state.
    destruct (ma2 x) eqn: Hma2. cbn in *.
    crunch. eauto.
  Defined.

  Instance eqmR_mayRet_r_state : MayRetR (state S).
  Proof.
    red;intros.
    rewrite <- mayRet_state in H. edestruct H as (? & ? & ?); clear H.
    cbn in *.
    destruct (ma1 x) eqn: Hma. cbn in *.
    inv H0. rename EQH into H.
    unfold eqmR_state in H. cbn in H.
    specialize (H x). setoid_rewrite Hma in H. crunch.
    cbn in *. setoid_rewrite <- mayRet_state.
    exists a. split; eauto. rewrite H1 in H. auto.
  Defined.

  Instance eqmR_ret_state : RetFinal (state S).
  Proof.
    red; intros. cbn. unfold eqmR_state. cbn. intros.
    split.
    - eauto.
    - reflexivity.
  Defined.

  Instance eqmR_bind_ProperH_state : ProperBind (state S).
  Proof.
    red;intros.
    cbn in *. unfold eqmR_state in *. cbn in *. intro.
    specialize (H s).
    destruct (ma1 s) eqn: Hma1. destruct (ma2 s) eqn: Hma2. cbn in *. subst.

    destruct H.
    specialize (H0 _ _ H). subst.
    edestruct H0; eauto. constructor; eauto.

    unfold bind_state. rewrite Hma1, Hma2. cbn. eauto.
    unfold bind_state. rewrite Hma1, Hma2. cbn. eauto.
  Qed.

  Instance eqmR_bind_ret_l_state : BindRetL (state S).
  Proof.
    red;intros. repeat red. cbn. intros.
    unfold bind_state, ret_state. cbn in *. split; auto.
  Defined.

  Instance eqmR_bind_ret_r_state : BindRetR (state S).
  Proof.
    repeat intro. cbn. split; try split; try reflexivity.
  Defined.

  Instance eqmR_bind_bind_state : BindBind (state S).
  Proof.
    repeat intro. cbn.
    unfold bind_state.
    split; try split; try reflexivity;
      intros; subst.
  Defined.

  Global Instance EqmRMonad_state : EqmRMonadLaws (state S).
  Proof.
    constructor; try typeclasses eauto.
    repeat intro. eapply image_eqmR_state.
  Qed.

  (* [EqmRMonadInverses] for state monad. *)

  Lemma are_continuations_functions:
    forall {A B : Type} (a : A) (k : A -> state S B) (mb mb' : state S B),
      k a = mb /\ k a = mb' -> mb = mb'.
  Proof.
    intros. destruct H. rewrite <- H, <- H0. reflexivity.
  Qed.

  Context {IS: inhabited S}.

  Instance ret_inv_St : RetInv (state S).
  Proof.
    inv IS.
    repeat intro. repeat red in H.
    edestruct H. crunch; eauto. Unshelve. eauto.
  Defined.

  Definition imageA {A : Type} : relationH A A :=
    fun a a' =>
      forall (R : relationH A A) (PH : PER R), R a a'.

  Definition mayRetA {A : Type} : A -> Prop :=
    (fun (a : A) => imageA a a).

  Instance state_mayRet_bind_inv : MayRetBindInv (state S).
  Proof.
    red; intros.
    apply mayRet_state in H.
    setoid_rewrite <- mayRet_state.
    crunch.
    unfold bind, Monad_state, bind_state in H.
    destruct (ma x) eqn:Hma1.
    exists a. split; eauto; eauto.
  Defined.

  Lemma fmap_inv_state_hetero :
    forall (A B : Type) (ma ma' : state S A) (f f' : A -> B) (R : relationH B B),
      (f <$> ma) ≈{ R } (f' <$> ma') ->
      forall a : A, a ∈ ma -> exists a', a' ∈ ma' /\ ret (f a) ≈{ R } ret (f' a').
  Proof.
    repeat intro.
    repeat red in H.
    unfold fmap, bind, ret, Monad_state, bind_state, ret_state in H.
    eapply mayRet_state in H0.
    setoid_rewrite <- mayRet_state. crunch.
    destruct (ma' x) eqn: Hma.
    exists a0. specialize (H x). crunch. cbn in *; rewrite H0, Hma in H, H1.
    crunch; eauto.
    eapply eqmR_ret. typeclasses eauto.
    cbn in *.
    rewrite Hma, H0 in H. eauto.
  Qed.

  Definition state_prop_ {A : Type} (ma ma': state S A) :=
    (fun a a' : A => exists s s' s'' : S, (ma s) = (s', a) /\ (ma' s) = (s'', a')).

  Lemma image_state {A:Type} (ma ma': state S A) (a a': A) :
    (exists s s' s'': S, (ma s) = (s', a) /\ (ma' s) = (s'', a')) ->
    image_ _ ma ma' a a'.
  Proof.
    intro.
    - edestruct H as (? & ? & ?); clear H.
      red. repeat intro.
      red in EQR; unfold eqmR_state in EQR.
      specialize (EQR x). crunch. subst.
      rewrite H, H2 in H0. auto.
  Qed.

  Instance fmap_inv_mayRet_state : FmapInvRet (state S).
  Proof.
    repeat intro.
    repeat red in H.
    unfold fmap, bind, ret, Monad_state, bind_state, ret_state in H.
    eapply mayRet_state in H0.
    crunch.
    specialize (H x). crunch. cbn in *. rewrite H0 in H, H1.
    crunch; eauto. cbn in *; constructor.
  Defined.

  Instance fmap_inv_state_ : FmapInv_mayRet (state S).
  Proof.
    repeat intro.
    Ltac sunfold := unfold fmap, bind, ret, Monad_state, bind_state, ret_state in *; cbn in *; unfold eqmR_state in *.
    sunfold.
    specialize (H s). crunch; destruct (ma1 s) eqn: Hma, (ma2 s) eqn: Hma'; cbn in *; subst; eauto.
    red. rewrite<- !mayRet_state; split; eauto.
  Defined.

  Instance eqmR_inv_state : EqmRInv (state S).
  Proof.
    repeat intro. rewrite <- mayRet_state in H0. destruct H0 as (?&?&?).
    repeat red in H. specialize (H x). rewrite H0 in H.
    destruct H; eauto.
  Qed.

  Global Instance EqmRMonadInverses_state : EqmRInversionProperties (state S).
  Proof.
    constructor; try typeclasses eauto.
  Defined.

  Global Instance EQM_state : EQM (state S) _.
  Proof.
    econstructor; typeclasses eauto.
  Defined.

End StateEq.

Example bind_ret_inv_counterexample:
  forall A B (a:A) (b:B) (x y : nat),
    bind (m := state nat) (fun x => (x+1, a)) (fun x => (fun y => (y-1, b))) ≈{eq} ret b.
Proof.
  intros.
  repeat red. unfold bind, ret, Monad_state, bind_state, ret_state; cbn.
  intros. split; eauto. lia.
Qed.

Definition ma : state nat nat := (fun s => if Nat.eqb s 2 then (s, 0) else (s + 1, 1)).

Definition k : nat -> state nat nat := (fun s => if Nat.eqb s 0 then (fun s => (s, s)) else (fun s => (s, 1))).

Lemma ma_mayRet :
  0 ∈ ma.
Proof. apply mayRet_state. exists 2. cbn. exists 2; eauto. Qed.

Lemma k_mayRet :
  0 ∈ k 0.
Proof. apply mayRet_state. cbn. eauto. Qed.

Lemma bind_mayRet:
  ~ (0 ∈ bind ma k).
Proof.
  intro. apply mayRet_state in H. destruct H as (? & ? & ?).
  cbn in *. unfold bind_state in H.
  unfold ma in H.
  destruct (Nat.eqb x 2) eqn: Hx. cbn in *.
  apply EqNat.beq_nat_true in Hx. subst. inv H. cbn in *. inv H.
Qed.
