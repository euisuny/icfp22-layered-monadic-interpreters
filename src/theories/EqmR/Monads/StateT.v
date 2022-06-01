From Coq Require Import
     Logic.Classical_Prop
     Morphisms
     Relations.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts
     Basics.HeterogeneousRelations
     Basics.Tacs
     Basics.Function.

From ExtLib Require Import
     Structures.Monad Structures.Functor.

From ITree.EqmR Require Import
     EqmRMonad
     EqmRMonadT.

Import ITree.Basics.Basics.Monads.
Import FunctorNotation.
Import CatNotations.
Local Open Scope cat_scope.
Local Open Scope cat.

Import RelNotations.
Local Open Scope relationH_scope.

Existing Class inhabited.

Class setoid (S : Type) := {
  EQS : relation S;
  Equivalence_EQS :> Equivalence EQS
}.
Global Hint Mode setoid ! : typeclasses_instances.

#[global] Instance eq_setoid {A : Type} : setoid A | 100 :=
  { EQS := eq; Equivalence_EQS := _ }.
Global Hint Mode eq_setoid ! : typeclasses_instances.

Section stateT.
  Variable S : Type.
  Context (Setoid_S : setoid S).

  #[global] Instance EqmR_StateT m `{EqmR m}: EqmR (stateT S m) :=
    {| eqmR := fun (A B : Type) (R : relationH A B) (x : stateT S m A) (y : stateT S m B) =>
        forall s s' : S, EQS s s' -> x s ≈{ EQS ⊗ R } y s' |}.

  #[global] Instance MonadT_StateT : MonadT (stateT S).
    constructor; try typeclasses eauto.
    - exact (fun _ _ _ c s => (fun x => (s, x)) <$> c).
  Defined.

  #[global] Arguments MonadT_StateT /.

  (* Alternatively, one can imagine a "refinement" definition as follows..
     monad m => ret, bind equipped with properness
     fun x s => ret (s, x)

     forall s1 s2 x1, EQS s1 s2 -> eqmR (EQS x id) (ret (s1, x1)) (ret (s2, x1)) *)

  (* One property that we would like from the state transformer is as follows;
            a ∈ ma -> ∃ s s' : S, (s', a) ∈ ma s
     Namely, the space of returned values get refined as there are more effects
     introduced. *)

  Global Instance relationH_PER_Symmetric {A : Type} (R : relationH A A) {PR : PER R}:
    Symmetric R.
    destruct PR. apply SymmetricH_Symmetric. apply per_symm.
  Qed.

  Global Instance relationH_PER_Transitive {A : Type} (R : relationH A A) {PR : PER R}:
    Transitive R.
    destruct PR. apply TransitiveH_Transitive. apply per_trans.
  Qed.

  Global Instance relationH_Equivalence_PER {A : Type} (R : relationH A A) {ER : Equivalence R}:
    PER R.
    destruct ER. split; eauto.
  Qed.

  Lemma R_id_PER :
    forall {A} (R : relationH A A), PER R -> R ∘ R ≡ R.
  Proof.
    intros; split; intros * x y HR; intuition.
    destruct HR as (? & ? & ?). etransitivity; eauto.
    esplit; split; eauto. etransitivity. symmetry; eauto. eauto.
  Qed.

  Context (m : Type -> Type)
          (EqmRM_ : EqmR m) (Monad_m : Monad m)
          (EQM_M : EQM m EqmRM_).

  Context {Proper_EQS : forall A (ma : stateT S m A), Proper (EQS ==> eqmR (m := m) (@eq (S * A))) ma}.

  Definition prod_rel_right {A B} (R :relationH (A * B) (A * B)) (a : A):
    relationH B B :=
    fun x y => R (a, x) (a, y).

  Instance prod_rel_right_PER {A B} :
    forall a (R :relationH (A * B) (A * B)), PER R -> PER (prod_rel_right R a).
  Proof.
    intros.
    constructor.
    - red. repeat intro. unfold prod_rel_right in *. crunch.
      symmetry. auto.
    - red. repeat intro. unfold prod_rel_right in *. etransitivity; eauto.
  Qed.

  Definition state_prop {A : Type}
             (ma : stateT S m A) :=
    (fun a : A => exists s s', (s', a) ∈ ma s).

  Lemma stateT_mayRet:
    forall A a (ma : stateT S m A), a ∈ ma <-> (exists s s', (s', a) ∈ ma s).
  Proof.
    intros. split; intros.
    - repeat red in H. unfold mayRet, image. cbn in H.
      epose (state_prop ma : A -> Prop) as Q.
      assert (eqmR (diagonal_prop Q) ma ma).
      {
        cbn. unfold diagonal_prop, Q, state_prop.
        repeat intro.
        eapply rel_prod; eauto...
        unfold fmap.
        eapply Proper_bind.
        apply Proper_EQS; eauto.
        intros; subst; apply final; reflexivity.
        unfold fmap.
        eapply Proper_bind.
        eapply image_post; try typeclasses eauto.
        Unshelve.
        apply Proper_EQS; eauto.
        intros; subst; apply final.

        edestruct H1 as (?&?&?). subst.
        split; try destruct a2; eexists _, _; eauto.
      }
      specialize (H (diagonal_prop Q) (diagonal_prop_PER Q) H0).
      unfold diagonal_prop in H.
      destruct H. red in H.
      edestruct H as (? & ? & ?).
      auto.
    - crunch. red. repeat intro. repeat red in H.

      specialize (H (EQS ⊗ R) _). red in EQR.
      specialize (EQR x x). assert (Hr: EQS x x) by reflexivity.
      specialize (EQR Hr). specialize (H EQR). inv H; auto.
  Qed.

  Ltac unfold_StateT := unfold fmap, bind, ret, Monad_stateT.

  Instance eqmR_prod_fst_inv_StateT : FmapFst (stateT S m).
  Proof with (try typeclasses eauto).
    repeat intro.
    red in H. specialize (H s). unfold_StateT.
    eapply eqmR_bind_ProperH; eauto... all: intros; apply eqmR_ret; eauto...
    all : inv H1; inv H3; constructor; eauto.
  Qed.

  Instance eqmR_prod_snd_inv_StateT : FmapSnd (stateT S m).
  Proof.
    repeat intro.
    red in H. specialize (H s). unfold_StateT.
    eapply eqmR_bind_ProperH; eauto... typeclasses eauto.
    all: intros; eapply eqmR_ret; eauto...
    all : inv H1; inv H3; constructor; eauto.
    all : typeclasses eauto.
  Qed.

  Lemma prod_rel_assoc :
    forall A1 A2 B1 B2 C1 C2 (RA : relationH A1 A2) (RB : relationH B1 B2) (RC : relationH C1 C2)
      a1 b1 c1 a2 b2 c2,
      ((RA ⊗ RB) ⊗ RC) (a1, b1, c1) (a2, b2, c2) <-> (RA ⊗ (RB ⊗ RC)) (a1, (b1, c1)) (a2, (b2, c2)).
  Proof.
    intros. split; intros; constructor; inv H; try inv H3; try inv H5; eauto.
  Qed.

  Definition fst_snd {A B S} : (S * (A * B))%type -> (S * A)%type :=
    fun sa => (fst sa, fst (snd sa)).

  Definition snd_snd {A B S} : (S * (A * B))%type -> (S * B)%type :=
    fun sa => (fst sa, snd (snd sa)).

  Ltac rel_hyp_destruct :=
    match goal with
    | H : context[?R1 ⊗ ?R2] |- _ => inv H
    | H : context[?R1 ⊕ ?R2] |- _ => inv H
    | H : context[mayRet_rel] |- _ => destruct H as (? & ?)
    | x : (_ * _) |- _ => destruct x
    | x : (_ + _) |- _ => destruct x
    | H : inl _ = inl _ |- _ => inv H
    | H : inr _ = inr _ |- _ => inv H
    | H : inl _ = inr _ |- _ => inv H
    | H : inr _ = inl _ |- _ => inv H
    end.

  Ltac scrunch := repeat rel_hyp_destruct; cbn; eauto; try typeclasses eauto.

  Instance eqmR_prod_rel_StateT : RelProd (stateT S m).
  Proof with (scrunch).
    intros.
    repeat red. intros.

    specialize (H s); specialize (H0 s).

    unfold fmap in *. cbn in *.
    change (bind (m1 s) (fun sa : S * (A1 * B1) => ret (fst sa, fst (snd sa))))
      with (fst_snd <$> (m1 s)) in H.
    change (bind (m2 s) (fun sa : S * (A2 * B2) => ret (fst sa, fst (snd sa))))
      with (fst_snd <$> (m2 s)) in H.

    change (bind (m1 s) (fun sa : S * (A1 * B1) => ret (fst sa, snd (snd sa))))
      with (snd_snd <$> (m1 s)) in H0.
    change (bind (m2 s) (fun sa : S * (A2 * B2) => ret (fst sa, snd (snd sa))))
      with (snd_snd <$> (m2 s)) in H0.

    eapply rel_prod; eauto...
    unfold fmap.
    - eapply eqmR_bind_ProperH; eauto...
      + unfold fst_snd in H.
        eapply fmap_inv in H. eapply H. eauto.
      + intros. destruct a1, a2. crunch.
        apply eqmR_ret; eauto...
    - eapply eqmR_bind_ProperH; eauto...
      + eapply fmap_inv in H, H0. 2,3: eauto...
        eapply rel_conj. apply H. apply H0.
      + intros. destruct a1, a2. crunch.
        destruct p, p0; eauto... apply final. constructor; auto.
  Qed.

  Instance eqmR_sum_inl_StateT : FmapInl (stateT S m).
  Proof.
    repeat intro. cbn.
    eapply eqmR_bind_ProperH; [typeclasses eauto|eauto|intros].
    all : apply eqmR_ret; [typeclasses eauto|]; scrunch; constructor; auto.
  Qed.

  Instance eqmR_sum_inr_StateT : FmapInr (stateT S m).
  Proof.
    repeat intro. cbn.
    eapply eqmR_bind_ProperH; [typeclasses eauto|eauto|intros].
    all : apply eqmR_ret; [typeclasses eauto|]; scrunch; constructor; auto.
  Qed.

  Instance eqmR_sum_rel_StateT : RelSum (stateT S m).
  Proof.
    repeat intro. split; repeat intro; cbn in *.
    - eapply eqmR_bind_ProperH; [typeclasses eauto|eauto|..]; intros; scrunch.
      all : apply eqmR_ret; try typeclasses eauto; constructor; eauto.
    - specialize (H (A1 + B1)%type (A2 + B2)%type inl inl inr inr (RA ⊕ RB)).
      assert (inl_P : ProperH (respectfulH A1 A2 (A1 + B1) (A2 + B2) RA (RA ⊕ RB)) inl inl) by
        (intros; constructor; eauto).
      assert (inr_P : ProperH (respectfulH B1 B2 (A1 + B1) (A2 + B2) RB (RA ⊕ RB)) inr inr) by
        (intros; constructor; eauto).
      specialize (H inl_P inr_P s).
      specialize (H _ H0).
      apply fmap_inv in H.
      eapply Proper_eqmR_mono; eauto... repeat intro.
      crunch. destruct x, y; constructor; inv H1; eauto.
      destruct s1, s3; eauto. all : scrunch.
  Qed.

  Instance eqmR_conj_StateT : RelConj (stateT S m).
  Proof with (scrunch).
    repeat intro. red in H, H0.
    specialize (H s); specialize (H0 s).
    eapply rel_prod; eauto...
    eapply eqmR_bind_ProperH; eauto; intros...
    apply eqmR_ret; eauto...
    eapply eqmR_bind_ProperH. eauto...
    eapply rel_conj. eapply H; eauto. eapply H0; eauto.
    intros... apply eqmR_ret...
  Qed.

  Instance eqmR_transport_PER_StateT : TransportPER (stateT S m).
  Proof.
    repeat intro.
    split; repeat intro. red in H0. symmetry in H1.
    specialize (H0 _ _ H1).
    symmetry. auto.
    etransitivity.
    eapply H0. 2 : eapply H1. reflexivity. auto.
  Qed.

  Instance eqmR_transport_Equiv_StateT : TransportEquiv (stateT S m).
  Proof.
    repeat intro; eauto. destruct H.
    constructor. 2, 3 : apply eqmR_transport_PER_StateT; constructor; eauto. repeat intro.
    revert s s' H.
    pose proof (Proper_EQS _  x). red in H. intros.
    eapply Proper_eqmR_mono; eauto. repeat intro.
    destruct x0 ,y. inv H1. constructor. 2 : reflexivity. auto. reflexivity.
  Qed.

  Instance eqmR_rel_comp_StateT : RelComp (stateT S m).
  Proof with (try typeclasses eauto).
    repeat intro. cbn in *. unfold EqmR_StateT in *.
    intros. specialize (H s). specialize (H0 s').
    eapply Proper_eqmR; eauto...
    rewrite <- (R_id_PER EQS).
    rewrite prod_compose. reflexivity. typeclasses eauto.
    eapply eqmR_rel_comp; eauto...
    specialize (H0 s'). assert (EQS s' s') by reflexivity.
    specialize (H0 H2); eauto.
  Qed.

  Instance eqmR_lift_transpose_StateT : LiftTranspose (stateT S m).
  Proof with (try typeclasses eauto).
    red. intros.
    assert (forall A, † (@eq A) ⊗ † R ≡ eq ⊗ † R).
    { intros; split; repeat intro. destruct H. split. symmetry. auto. auto.
      destruct H. split. red. symmetry. auto. auto. }

    split; repeat intro.
    {
      rewrite H1.
      eapply eqmR_lift_transpose; eauto... red.
      eapply Proper_eqmR; eauto...
      setoid_rewrite transpose_prod...
      rewrite transpose_sym.
      reflexivity. typeclasses eauto. eapply H0. reflexivity.
    }
    {
      rewrite H1.
      eapply Proper_eqmR; eauto...
      setoid_rewrite <- (transpose_sym EQS). reflexivity.
      eapply eqmR_lift_transpose; eauto... red.
      eapply Proper_eqmR; eauto... 2 : apply H0; reflexivity.
      split; repeat intro; scrunch.
    }
  Qed.


  Instance eqmR_Proper_StateT :
    forall {A B : Type}, Proper (eq_rel (A:=A) (B:=B) ==> eq_rel) (eqmR (m := stateT S m)).
  Proof.
    repeat intro. split; repeat intro.
    red in H0. eapply Proper_eqmR; eauto... rewrite H. reflexivity.
    red in H0. eapply Proper_eqmR; eauto... rewrite H. reflexivity.
  Qed.

  Instance Proper_eqmR_mono_StateT :
    forall {A B : Type}, Proper (subrelationH (A:=A) (B:=B) ==> subrelationH (B:=stateT S m B)) eqmR.
  Proof.
    repeat intro.
    red in H0. eapply Proper_eqmR_mono; eauto...
    eapply prod_rel_monotone; eauto. apply subrelation_refl.
  Qed.

  Instance transport_refl: TransportReflexive (stateT S m).
  Proof.
    repeat intro. rewrite H0. eapply refl; typeclasses eauto.
  Qed.

  Global Instance EqmR_OK_StateT :
    EqmR_OK (stateT S m).
  Proof.
    econstructor; try typeclasses eauto.
  Qed.

  Context `{inhabited0: inhabited S}.

  Instance eqmR_ret_inv_StateT : RetInv (stateT S m).
  Proof with (try typeclasses eauto).
    intros A B R a b Heq. cbn in Heq.
    inv inhabited0. eauto.
    specialize (Heq X X).
    assert (eqx: EQS X X) by reflexivity. specialize (Heq eqx).
    apply eqmR_ret_inv in Heq; eauto...
    inv Heq. auto.
  Qed.

  Instance eqmR_mayRet_l_StateT: MayRetL (stateT S m).
  Proof.
    red.
    intros* Hpre * Hcont. cbn in Hpre, Hcont.
    inv inhabited0.
    set (MayRet:= exists s s', (s', a1) ∈ ma1 s).
    pose proof classic as Classic. specialize (Classic MayRet).
    destruct Classic.
    {
      destruct H as (si & sf & mr).
      repeat red in Hpre. specialize (Hpre si si).
      assert (EQS si si) by reflexivity.
      specialize (Hpre H).
      eapply eqmR_mayRet_l in Hpre. 2 : eauto.
      specialize (Hpre _ mr).
      crunch. inv H0. eexists; split; eauto.
      repeat intro. repeat red in H0.
      set (R' := EQS ⊗ R).
      assert (PER_R' : PER R'). {
        split; repeat red; unfold R'; repeat intro; destruct x, y.
        - split; scrunch; symmetry; auto.
        - destruct z; split; crunch; etransitivity; eauto; scrunch.
      }
      specialize (H1 _ PER_R').
      assert (ma2 si ≈{R'} ma2 si). {
        cbn in EQR. unfold R'. eapply EQR. reflexivity.
      }
      specialize (H1 H0).
      unfold R' in H1. inv H1. auto. typeclasses eauto.
    }
    {
      red in H. exfalso. apply H. unfold MayRet.
      rewrite <- stateT_mayRet. eauto.
    }
  Qed.

  Instance eqmR_mayRet_r_StateT : MayRetR (stateT S m).
  Proof.
    red.
    intros* Hpre * Hcont. cbn in Hpre, Hcont.
    inv inhabited0.
    set (MayRet:= exists s s', (s', a2) ∈ ma2 s).
    pose proof classic as Classic. specialize (Classic MayRet).
    destruct Classic.
    {
      destruct H as (si & sf & mr).
      repeat red in Hpre. specialize (Hpre si si).
      assert (EQS si si) by reflexivity.
      specialize (Hpre H).
      eapply eqmR_mayRet_r in Hpre. 2 : eauto.
      specialize (Hpre _ mr).
      crunch. inv H0. eexists; split; eauto.
      repeat intro. repeat red in H0.
      set (R' := EQS ⊗ R).
      assert (PER_R' : PER R'). {
        split; repeat red; unfold R'; repeat intro; destruct x, y.
        - split; scrunch; symmetry; auto.
        - destruct z; split; crunch; etransitivity; eauto; scrunch.
      }
      specialize (H1 _ PER_R').
      assert (ma1 si ≈{R'} ma1 si). {
        cbn in EQR. unfold R'. eapply EQR. reflexivity.
      }
      specialize (H1 H0).
      unfold R' in H1. inv H1. auto. typeclasses eauto.
    }
    {
      red in H. exfalso. apply H. unfold MayRet.
      rewrite <- stateT_mayRet. eauto.
    }
  Qed.

  Instance eqmR_ret_StateT : RetFinal (stateT S m).
  Proof with (scrunch).
    red. repeat intro. apply eqmR_ret; eauto...
  Qed.

  Instance eqmR_bind_ProperH_StateT : ProperBind (stateT S m).
  Proof.
    red.
    repeat intro.
    eapply eqmR_bind_ProperH; eauto; intros... typeclasses eauto.
    scrunch. cbn in *. eapply H0; eauto.
  Qed.

  Instance eqmR_bind_ret_l_StateT : BindRetL (stateT S m).
  Proof.
    red;intros. intro. intros.
    rewrite H.
    setoid_rewrite bind_ret_l; cbn.
    eapply refl; eauto. typeclasses eauto.
    apply prod_rel_eqv; typeclasses eauto.
  Qed.

  Instance eqmR_bind_ret_r_StateT : BindRetR (stateT S m).
  Proof.
    red;repeat intro.
    eapply Proper_eqmR_cong.
    symmetry. apply bind_ret_r. reflexivity.
    setoid_rewrite bind_bind. setoid_rewrite bind_ret_l.
    eapply Proper_eqmR_cong. eapply Proper_bind with (RR := eq).
    apply Proper_EQS; eauto.
    intros; subst; destruct a2; cbn; reflexivity. reflexivity.
    rewrite bind_ret_r.

    eapply refl; eauto. typeclasses eauto.
    apply prod_rel_eqv; typeclasses eauto.
  Qed.

  Instance eqmR_bind_bind_StateT: BindBind (stateT S m).
  Proof.
    red;repeat intro.
    setoid_rewrite bind_bind.
    apply Proper_bind with (RR := eq).
    - apply Proper_EQS; auto.
    - intros; subst. destruct a2. cbn.
      eapply refl; eauto. typeclasses eauto.
      apply prod_rel_eqv; typeclasses eauto.
  Qed.

  Global Instance EqmRMonad_StateT : EqmRMonadLaws (stateT S m).
  Proof.
    constructor;try typeclasses eauto.
    repeat intro. eapply eqmR_rel_prod; [typeclasses eauto | ..].
    eapply eqmR_fmap_fst; eauto. typeclasses eauto.
    rewrite H. eapply reflexivity.
    unfold fmap. eapply Proper_bind.
    eapply Proper_eqmR_cong. rewrite H. reflexivity. reflexivity.
    eapply eqmR_image.
    typeclasses eauto. intros.
    eapply eqmR_ret; eauto. typeclasses eauto.
    destruct a1, a2. cbn. repeat red in H0.
    repeat intro.
    red in EQR.
    specialize (EQR s' s').
    assert (EQS s' s') by reflexivity.
    specialize (EQR H1).
    specialize (H0 (EQS ⊗ R) _ EQR).
    inv H0; eauto.
  Qed.


  Instance mayRet_bind_inv_StateT : MayRetBindInv (stateT S m).
  Proof.
    red;intros.
    rewrite stateT_mayRet in H.
    crunch. apply eqmR_mayRet_bind_inv in H; eauto...
    crunch. destruct x1. cbn in *. exists a.
    split; eauto.
    apply stateT_mayRet; eauto.
    apply stateT_mayRet; eauto. typeclasses eauto.
  Qed.

  (* Instance fmap_inv_mayRet_StateT: FmapInvRet (stateT S m). *)
  (* Proof with (try typeclasses eauto). *)
  (*   red;intros. repeat red in H. repeat intro. *)
  (*   apply stateT_mayRet in H0. crunch. *)
  (*   specialize (H x). *)

  (*   eapply fmap_inv_ret in H; eauto... *)
  (*   eapply eqmR_ret_inv in H; eauto... inv H. *)

  (*   apply eqmR_ret; eauto... reflexivity. *)
  (* Qed. *)

  Instance fmap_inv_StateT: FmapInv (stateT S m).
  Proof.
    repeat intro.
    specialize (H s).
    cbn in H.
    Definition fst_f {A B : Type} (f : A -> B) : S * A -> S * B:=
      fun sa => (fst sa, f (snd sa)).

    specialize (H s' H0).

    apply fmap_inv in H; eauto...
    eapply Proper_eqmR_mono; eauto...
    repeat intro; eauto. destruct x, y; constructor; crunch; eauto.
    all: try inv H1; eauto.
  Qed.

  Instance eqmR_inv_StateT : EqmRInv (stateT S m).
  Proof.
    repeat intro.
    cbn in H. rewrite stateT_mayRet in H0. destruct H0 as (?&?&?).
    specialize (H x x).
    eapply eqmR_inv in H; eauto. 2 : typeclasses eauto. 2 : reflexivity.
    inv H; eauto.
  Qed.

  Global Instance EqmRMonadInverses_StateT : EqmRInversionProperties (stateT S m).
  Proof.
    constructor; try typeclasses eauto.
  Qed.

  Global Instance EQM_StateT : EQM (stateT S m) _.
  Proof.
    econstructor; typeclasses eauto.
  Qed.

  Instance MorphRet_StateT : MorphRet m (stateT S m) _.
  Proof.
    repeat intro. unfold morph, MonadT_StateT. unfold fmap.
    eapply Proper_eqmR_cong. unfold lift. cbn; unfold liftM.
    rewrite bind_ret_l. 1,2 : reflexivity.
    apply final; eauto.
  Qed.

  Instance MorphBind_StateT : MorphBind m (stateT S m) _.
  Proof.
    repeat intro. cbn.
    unfold fmap.
    eapply Proper_eqmR_cong. unfold liftM.
    rewrite bind_bind. reflexivity.
    setoid_rewrite bind_bind. setoid_rewrite bind_ret_l.  reflexivity.
    eapply Proper_bind with (RR:=RA); eauto; intros; cbn; subst; eauto.
    eapply Proper_bind with (RR:=RB); eauto; intros; cbn; subst; apply final; eauto.
  Qed.

  Instance MorphProper_StateT : MorphProper m (stateT S m) _ _.
  Proof.
    repeat intro; cbn.
    eapply rel_prod; cbn; eauto.
    unfold fmap, liftM.
    do 2 rewrite bind_bind.
    eapply Proper_bind with (RR := RR); eauto; intros; do 2 rewrite bind_ret_l; apply final; eauto.
    unfold fmap, liftM.
    do 2 rewrite bind_bind.
    eapply Proper_bind with (RR := RR); eauto; intros; do 2 rewrite bind_ret_l; apply final; eauto.
  Qed.

  Global Instance MonadMorphism_StateT : MonadMorphism m (stateT S m) _.
  constructor; try typeclasses eauto.
  Qed.

End stateT.

Section Transformer.
  Context {S : Type}.
  Context {IS : inhabited S}.

  Parameter proper : forall m (EqmR_m: EqmR m) (A : Type) (ma : stateT S m A), Proper (EQS ==> eqmR eq) ma.

  Instance EqmRT_StateT : forall m : Type -> Type, EqmR m -> EqmR (stateT S m).
  Proof.
    intros. eapply EqmR_StateT; try typeclasses eauto; eauto.
  Defined.

  #[global] Instance MonadTransformer_StateT : @MonadTLaws (stateT S) (MonadT_StateT S eq_setoid).
  Proof.
    econstructor; intros; try typeclasses eauto.
  Qed.

End Transformer.
