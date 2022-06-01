(** * EqmR Monad laws and associated typeclasses *)

(* This file contains an equational axiomatization of the monadic structures that
   arise from the construction of layered monadic interpreters.

   The base theory, [EqmR] is a framework for relational reasoning over monads.
   They are a generalization of the ITree equational theory on [eutt], and have
   a notion of [image] of a computation which capture the set of values possibly
   returned by a monadic computation.

   The well-formedness conditions capture standard monad laws.
   Roughly, they also characterize forming a bicartesian closed category (a
    cartesian closed category with finite coproducts).
   The laws also characterize inversion properties which consume relations over
   monads. *)

(* begin hide *)
From Coq Require Import
     Morphisms
     Program.

From ExtLib Require Import
     Structures.Functor
     Monad.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.HeterogeneousRelations
     Basics.Function
     Basics.FunctionFacts.

Set Primitive Projections.

Import FunctorNotation.
Import CatNotations.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope cat_scope.
(* end hide *)

Section EqmR.

  (* We consider heterogeneous relations on computations parameterized by a
     relation on the return types *)
  Class EqmR (m : Type -> Type) : Type :=
    { eqmR : forall {A B : Type} (R : relationH A B), relationH (m A) (m B) }.

End EqmR.
Infix "≈{ R  }" := (eqmR R) (at level 30) : cat_scope.
Notation "t1 ≋ t2" := (eqmR eq t1 t2) (at level 40) : cat_scope.

Arguments eqmR {m _ A B}.

Import RelNotations.
Local Open Scope relationH_scope.

(* [EqmR_OK] : Well-formedness properties of EqmR. *)
Section EqmRRel.
  Context (m : Type -> Type).
  Context {EqMR : EqmR m} {Mm : Monad m}.

  (* [eqmR] should transport elementary structures of the relation [R] *)
  Class TransportEquiv : Prop :=
    equiv : forall {A : Type} (R : relationH A A), Equivalence R -> Equivalence (eqmR R).

  Class TransportPER : Prop :=
    per : forall {A : Type} (R : relationH A A), PER R -> PER (eqmR R).

  Class TransportReflexive : Prop :=
    refl : forall {A : Type} (R : relationH A A), Reflexive R -> Reflexive (eqmR R).

  Class TransportSymmetric : Prop :=
    symm : forall {A : Type} (R : relationH A A), Symmetric R -> Symmetric (eqmR R).

  Class TransportTransitive : Prop :=
    trans : forall {A : Type} (R : relationH A A), Transitive R -> Transitive (eqmR R).

  Class LiftTranspose : Prop :=
    lift_transpose :
      forall {A B : Type} (R : relationH A B) , eq_rel (eqmR †R) (†(eqmR R)).

  (* Product rules *)
  Class FmapFst : Prop :=
    fmap_fst :
      forall {A1 A2 B1 B2: Type} (RA : relationH A1 A2) (RB : relationH B1 B2)
        (m1 : m (A1 * B1)) (m2: m (A2 * B2)),
        eqmR (RA ⊗ RB) m1 m2 ->
        eqmR RA (fst <$> m1) (fst <$> m2).

  Class FmapSnd : Prop :=
    fmap_snd :
      forall {A1 A2 B1 B2: Type} (RA : relationH A1 A2) (RB : relationH B1 B2)
        (m1 : m (A1 * B1)) (m2: m (A2 * B2)),
        eqmR (RA ⊗ RB) m1 m2 ->
        eqmR RB (snd <$> m1) (snd <$> m2).

  Class RelProd : Prop :=
    rel_prod :
      forall {A1 A2 B1 B2: Type} (RA : relationH A1 A2) (RB : relationH B1 B2)
        (m1 : m (A1 * B1)) (m2: m (A2 * B2)),
        eqmR RA (fst <$> m1) (fst <$> m2) ->
        eqmR RB (snd <$> m1) (snd <$> m2) ->
        eqmR (RA ⊗ RB) m1 m2.

  (* Sum rules *)
  Class FmapInl : Prop :=
    fmap_inl :
      forall {A1 A2 B1 B2: Type} (RA : relationH A1 A2) (RB : relationH B1 B2)
        (m1 : m A1) (m2: m A2),
        eqmR RA m1 m2 ->
        eqmR (RA ⊕ RB) (inl <$> m1) (inl <$> m2).

  Class FmapInr : Prop :=
    fmap_inr :
      forall {A1 A2 B1 B2: Type} (RA : relationH A1 A2) (RB : relationH B1 B2)
        (m1 : m B1) (m2: m B2),
        eqmR RB m1 m2 ->
        eqmR (RA ⊕ RB) (inr <$> m1) (inr <$> m2).

  Class RelSum : Prop :=
    rel_sum :
      forall {A1 A2 B1 B2: Type} (RA : relationH A1 A2) (RB : relationH B1 B2)
        (m1 : m (A1 + B1)) (m2: m (A2 + B2)),
        eqmR (RA ⊕ RB) m1 m2 <->
        (forall (C1 C2 : Type) (f1 : A1 -> C1) (f2 : A2 -> C2) (g1 : B1 -> C1) (g2 : B2 -> C2) (RC : relationH C1 C2),
        ProperH (RA ~~> RC) f1 f2 ->
        ProperH (RB ~~> RC) g1 g2 ->
        eqmR RC ((fun a => match a with
                        | inl a => f1 a
                        | inr b => g1 b
                        end) <$> m1)
                 ((fun a => match a with
                        | inl a => f2 a
                        | inr b => g2 b
                        end) <$> m2)).

  (* [eqmR] composes by composing the underlying relationHs *)
  Class RelComp : Prop :=
    rel_comp :
      forall {A B C : Type} (R1 : relationH A B) (R2 : relationH B C)
        (ma : m A) (mb : m B) (mc : m C),
        eqmR R1 ma mb ->
        eqmR R2 mb mc ->
        eqmR (R2 ∘ R1) ma mc.

  Class RelConj : Prop :=
    rel_conj :
      forall {A B : Type} (R R': relationH A B) (ma : m A) (mb : m B),
        eqmR R ma mb ->
        eqmR R' ma mb ->
        eqmR (R /2\ R') ma mb.

  (* Requirements of well-formedness of [eqmR] *)
  Class EqmR_OK : Type :=
    {
    eqmR_transport_refl :> TransportReflexive;
    eqmR_transport_PER :> TransportPER;

    eqmR_lift_transpose :> LiftTranspose;
    (* product rules *)
    eqmR_fmap_fst :> FmapFst;
    eqmR_fmap_snd :> FmapSnd;
    eqmR_rel_prod :> RelProd;
    (* sum rules *)
    eqmR_fmap_inl :> FmapInl;
    eqmR_fmap_inr :> FmapInr;
    eqmR_rel_sum :> RelSum;
    (* other relational rules *)
    eqmR_rel_comp :> RelComp;
    eqmR_rel_conj :> RelConj;

    (* [eqmR] respects extensional equality of the underlying relationH
        and [eqm] on both arguments over the monad *)
    Proper_eqmR :> forall {A B : Type}, Proper (@eq_rel A B ==> eq_rel) eqmR;
    (* [eqmR] is monotone as a morphism on relationHs *)
    Proper_eqmR_mono :> forall {A B}, Proper ((@subrelationH _ _) ==> (@subrelationH _ _)) (@eqmR m _ A B);
    }.

End EqmRRel.

Arguments equiv {m _ _ _} [_].
Arguments per {m _ _ _} [_].
Arguments rel_comp {m _ _} [_ _ _].
Arguments lift_transpose {m _ _} [_ _].
Arguments fmap_fst {m _ _ _} [_ _ _ _].
Arguments fmap_snd {m _ _ _} [_ _ _ _].
Arguments rel_prod {m _ _ _} [_ _ _ _].
Arguments fmap_inl {m _ _ _} [_ _ _ _].
Arguments fmap_inr {m _ _ _} [_ _ _ _].
Arguments rel_sum {m _ _ _} [_ _ _ _].
Arguments rel_conj {m _ _ _} [_ _ _ _].
Arguments Proper_eqmR {m _ _ _} [_ _].
Arguments Proper_eqmR_mono {m _ _ _} [_ _].

Section PER.

  Context {m : Type -> Type}.
  Context {Mm : Monad m}.
  Context {E : EqmR m}.
  Context {E_OK : EqmR_OK m}.

  Global Instance Refl_eqmR_eq {A} :
    Reflexive (eqmR (@eq A)).
  Proof.
    repeat intro. eapply eqmR_transport_refl; typeclasses eauto.
  Qed.

  Global Instance Equivalence_eqmR_eq {A} :
    Equivalence (eqmR (@eq A)).
  Proof.
    repeat intro. constructor; destruct E_OK;
    repeat intro;
      specialize (eqmR_transport_PER0 A eq _);
      [ reflexivity | symmetry; auto | etransitivity; eauto].
  Qed.

  Global Instance Equivalence_eqmR_R {A} (R : relationH A A) `{Equivalence A R} :
    Equivalence (eqmR R).
  Proof.
    repeat intro. destruct H; try typeclasses eauto.
    assert (PER R) by (constructor; auto).
    destruct E_OK; constructor;
    repeat intro;
      specialize (eqmR_transport_PER0 A R H);
      [ | symmetry; auto | etransitivity; eauto].
    eapply eqmR_transport_refl; auto.
  Qed.

  Global Instance Symm_eqmR_PER {A} {R : relationH A A} `{PER A R}:
    Symmetric (eqmR R).
  Proof.
    repeat intro. eapply eqmR_transport_PER; auto.
  Qed.

  Global Instance Trans_eqmR_PER {A} {R : relationH A A} `{PER A R}:
    Transitive (eqmR R).
  Proof.
    repeat intro. pose proof (eqmR_transport_PER m _ R H).
    destruct H2. etransitivity; eauto.
  Qed.

  Global Instance PER_eqmR_PER {A} {R : relationH A A} `{PER A R}:
    PER (eqmR R).
  Proof.
    split. red. apply Symm_eqmR_PER.
    red. apply Trans_eqmR_PER.
  Qed.

  Global Instance Proper_eqmR_PER {A} {R : relationH A A} `{PER A R}:
      Proper (eqmR R ==> eqmR R ==> iff) (eqmR R).
  Proof.
    repeat intro.
    split; intros.
    etransitivity.
    symmetry. apply H0. etransitivity. apply H2. apply H1.
    etransitivity. apply H0.
    etransitivity. apply H2. symmetry. apply H1.
  Qed.

  Global Instance Proper_eqmR_eq {A}:
      Proper (eqmR (@eq A) ==> eqmR (@eq A) ==> iff) (eqmR (@eq A)).
  Proof.
    repeat intro.
    split; intros.
    etransitivity.
    symmetry. apply H. etransitivity. apply H1. apply H0.
    etransitivity. apply H.
    etransitivity. apply H1. symmetry. apply H0.
  Qed.

  Global Instance Proper_eqmR_cong {A B} {R : relationH A B}:
      Proper (eqmR (@eq A) ==> eqmR (@eq B) ==> iff) (eqmR R).
  Proof.
    repeat intro.
    split.
    - repeat intro.
      pose proof @eqmR_rel_comp.
      specialize (H2 m _ _ _ _ _ _ (@eq A) R y x x0).
      symmetry in H. specialize (H2 H H1).
      pose proof @eqmR_rel_comp.
      specialize (H3 m _ _ _ _ _ _ R (@eq B) y x0 y0).
      eapply Proper_eqmR in H2. 2 : eauto.
      2 : { rewrite eq_id_l. reflexivity. }
      specialize (H3 H2 H0).
      eapply Proper_eqmR in H3. 2 : eauto.
      2 : { rewrite eq_id_r. reflexivity. }
      eauto.
    - repeat intro.
      pose proof @eqmR_rel_comp.
      specialize (H2 m _ _ _ _ _ _ (@eq A) R x y y0).
      specialize (H2 H H1).
      pose proof @eqmR_rel_comp.
      specialize (H3 m _ _ _ _ _ _ R (@eq B) x y0 x0).
      eapply Proper_eqmR in H2. 2 : eauto.
      2 : { rewrite eq_id_l. reflexivity. }
      symmetry in H0.
      specialize (H3 H2 H0).
      eapply Proper_eqmR in H3. 2 : eauto.
      2 : { rewrite eq_id_r. reflexivity. }
      eauto.
  Qed.

  Global Instance Proper_eqmR_impl {A B} {R : relationH A B}:
    Proper (eqmR (@eq A) ==> eqmR (@eq B) ==> impl) (eqmR R).
  Proof.
    repeat intro.
    edestruct @Proper_eqmR_cong; cycle 2.
    eapply H2; eauto. all : eauto.
  Qed.

  Global Instance Proper_eqmR_flip_impl {A B} {R : relationH A B}:
    Proper (eqmR (@eq A) ==> eqmR (@eq B) ==> flip impl) (eqmR R).
  Proof.
    repeat intro.
    edestruct @Proper_eqmR_cong; cycle 2.
    eapply H3; eauto. all : eauto.
  Qed.

End PER.

Arguments Proper_eqmR_cong {_ _ _ _} [_ _ _].

Section Image.
  Context (m : Type -> Type).
  Context {Mm : Monad m}.
  Context {EqMR : EqmR m} {EqmROKm : EqmR_OK m}.

  (*
   * An _image_ is a (unary) logical predicate that specifies the intersection
   * of PER's that a monadic value satisfies. Intuitively, what this entails is
   * the possible set of elements of the specified Type [A] that a monadic
   * value can return. In this sense, it is an "image" as in set theory,
   * indicating the set of all output values that a monad may produce.
   *
   * Notice the definition of _image_ takes the universal quantification over
   * all PER's satisfying [EQ], giving the smallest relation which will
   * describe the set of elements that a monadic value may return.
   *
   * Consider [image spin] in ITrees, or more simply, [image Nothing] for the
   * option monad, where the carrier Typee is [A].
   *
   * There exists no PER over any carrier Type that this option monad may have
   * in which [Nothing] can give an image to, i.e. the smallest relation over
   * [Nothing] cannot say anything about values of Type [A].
   *)
  (* Elements contained in the least specification that relates two monadic
     computations. *)
  Definition imageH {A1 A2 :Type} (ma1 : m A1) (ma2 : m A2) : relationH (A1 * A2) (A1 * A2) :=
    fun '(a1, a2) '(a1', a2') =>
      forall (RA : relationH A1 A2)
        (EQA : eqmR (m := m) RA ma1 ma2)
        (H : Zigzag RA), RA a1 a2 /\ RA a1' a2'.

  Definition imageH_Z {A1 A2 :Type} (ma1 : m A1) (ma2 : m A2) : relationH A1 A2 :=
    fun a1 a2 =>
      forall (RA : relationH A1 A2)
        (EQA : eqmR (m := m) RA ma1 ma2)
        (H : Zigzag RA), RA a1 a2.

  Definition mayRetH {A1 A2 : Type} (ma1 : m A1) (ma2 : m A2): A1 * A2 -> Prop :=
    fun '(x, y) => imageH ma1 ma2 (x, y) (x, y).

  Definition imageH_diag {A : Type} (ma : m A) : relationH A A :=
    fun x y => imageH ma ma (x, y) (y, x) /\ imageH ma ma (x, x) (y, y).

  Definition mayRetH_diag {A : Type} (ma : m A) : A -> Prop :=
    fun a => imageH_diag ma a a.

  (* NB: Every PER is difunctional, but the converse does not hold. *)
  Definition image_ {A:Type} (ma ma': m A) : relationH A A :=
    fun x y =>
      forall (R : relationH A A) (PH : PER R)
        (EQR: eqmR R ma ma'), R x y.

  Definition image {A:Type} (ma:m A):= image_ ma ma.

  (* Using [image] we can define the [mayRet] predicate, which identifies
   * the subset of A on which the computation [ma] can halt with
   * a [ret x]. (When we characterize monadic computations, we use [mayRet]
   * and we only care about this unary form.) *)
  Definition mayRet {A:Type} (ma : m A) : A -> Prop :=
    (fun (a:A) => image ma a a).

  Notation "a1 ∈ ma" := (mayRet ma a1) (at level 40) : cat_scope.
  Notation "a1 ∈̂ ma" := (mayRetH_diag ma a1) (at level 40) : cat_scope.

  Definition eqmR_bind_ProperH_homo := forall (A1 A2 B1 B2 : Type)
                            (RA : relationH A1 A2)
                            (RB : relationH B1 B2)
                            ma1 ma2
          (k1 : A1 -> m B1) (k2 : A2 -> m B2),
        ma1 ≈{RA} ma2 ->
        (forall (a1 : A1), a1 ∈ ma1 ->
                      forall a2, RA a1 a2 -> k1 a1 ≈{RB} k2 a2) ->
        (forall (a2 : A2), a2 ∈ ma2 ->
                      forall a1, RA a1 a2 -> k1 a1 ≈{RB} k2 a2) ->
        bind ma1 k1 ≈{RB} bind ma2 k2.

  Definition eqmR_bind_ProperH_hetero := forall (A1 A2 B1 B2 : Type)
                            (RA : relationH A1 A2)
                            (RB : relationH B1 B2)
                            ma1 ma2
          (k1 : A1 -> m B1) (k2 : A2 -> m B2),
        ma1 ≈{RA} ma2 ->
        (forall (a1 : A1), a1 ∈̂ ma1 ->
                      forall a2, RA a1 a2 -> k1 a1 ≈{RB} k2 a2) ->
        (forall (a2 : A2), a2 ∈̂ ma2 ->
                      forall a1, RA a1 a2 -> k1 a1 ≈{RB} k2 a2) ->
        bind ma1 k1 ≈{RB} bind ma2 k2.

  Lemma transpose_eq {A} (R : relationH A A) (x:A) :
    R x x <-> (transpose R) x x.
  Proof.
    split; intros; assumption.
  Qed.

  Global Instance image_PER {A} (ma : m A) : PER (image ma).
  Proof.
    constructor.
    - red.
      intros a.
      repeat intro.
      apply per_symm.
      apply H; auto.
    - red.
      intros.
      repeat intro. subst. unfold image in *.
      specialize (H R _ EQR). specialize (H0 R _ EQR).
      pose proof (per_trans x y z).
      cbn in H1.
      apply H1. apply H; assumption.
      apply H0; assumption.
  Qed.

  Global Instance imageH_PER {A1 A2} (m1 : m A1) (m2 : m A2) : PER (imageH m1 m2).
  Proof.
    split; repeat intro.
    - destruct x, y.
      red in H. repeat intro.
      specialize (H RA EQA H0).
      destruct H.
      split; auto.
    - destruct x, y, z.
      red in H, H0. repeat intro.
      specialize (H RA EQA H1). destruct H.
      specialize (H0 RA EQA H1). destruct H0.
      split; auto.
  Qed.

  Definition imageH_refl {A} ma x y := @imageH A A ma ma (x, y) (x, y).

  Lemma imageH_refl_subrel_image:
    forall A (ma : m A) x y,
      @imageH_refl A ma x y -> image ma x y.
  Proof.
    unfold image, imageH_diag. intros.
    repeat intro. edestruct H. eauto. eapply PER_is_ZZC; eauto.
    eauto.
  Qed.

  Global Instance imageHZ_ZZC {A1 A2} (m1 : m A1) (m2 : m A2) : Zigzag (imageH_Z m1 m2).
  Proof.
    repeat intro.
    eapply H0.
    destruct H as (? & ? & ?).
    destruct H as (? & ? & ?).
    esplit; split.
    esplit; split.
    unfold imageH_Z in *. eapply H; eauto. eapply H2; eauto.
    eapply H1; eauto.
  Qed.

  Lemma image_Reflexive_l {A:Type} (ma : m A) (a1 a2:A)
    (H : image ma a1 a2) : image ma a1 a1.
  Proof.
    assert (image ma a2 a1).
    { apply per_symm in H. apply H. }
    eapply per_trans in H. apply H in H0. apply H0.
  Qed.

  Lemma image_Reflexive_r {A:Type} (ma : m A) (a1 a2:A)
    (H : image ma a1 a2) : image ma a2 a2.
  Proof.
    assert (image ma a2 a1).
    { apply per_symm in H. apply H. }
    eapply per_trans in H0. apply H0 in H. apply H.
  Qed.

  Lemma image_least {A} (ma : m A)
        (R : relationH A A) (PH : PER R)
        (G: eqmR R ma ma)
    : (image ma) ⊑ R.
  Proof.
    intros x y D.
    unfold image in D.
    cbn in *.
    apply D; assumption.
  Qed.

  Global Instance Proper_image {A} :
    Proper (@eq (m A) ==> eq_rel) image.
  Proof.
    do 2 red.
    intros x y EQR.
    split.
    - red. intros a b H.
      repeat red.
      intros.
      repeat red in H.
      rewrite <- EQR in EQR0.
      specialize (H R PH EQR0).
      apply H.
    - red. intros a b H.
      repeat red.
      intros.
      repeat red in H.
      rewrite  EQR in EQR0.
      specialize (H R PH EQR0).
      apply H.
  Qed.

  Global Instance Proper_image2 {A}  :
    Proper (@eq (m A) ==> @eq A ==> @eq A ==> iff) (fun ma => (image ma)).
  Proof.
    do 3 red.
    intros.
    split; intros; cbn in *;  intros.
    - repeat intro. inversion H0; subst. apply H2. eauto. apply EQR.
    - repeat intro. inversion H0; subst. subst. apply H2. eauto. apply EQR.
  Qed.

  Global Instance Proper_image3 {A}  :
    Proper (@eq (m A) ==> (@eq2 Type Fun _ _ _)) image.
  Proof.
    do 3 red.
    repeat intro.
    rewrite H; reflexivity.
  Qed.

  Global Instance Proper_mayRet {A:Type} :
    Proper (@eq (m A) ==> (@eq A) ==> iff) (fun ma => (mayRet ma)).
  Proof.
    do 3 red.
    intros x y H x0 y0 H0.
    split; intros; cbn in *; intros.
    - rewrite <- H0. subst; auto.
    - rewrite H0. subst; auto.
  Qed.

  Global Instance Proper_mayRet2 {A}  :
    Proper (@eq (m A) ==> (@eq2 Type Fun _ _ _)) mayRet.
  Proof.
    repeat intro. subst; reflexivity.
  Qed.

  Lemma imageH_subrel_image_diag :
    forall A (ma : m A), imageH_diag ma ⊑ image ma.
  Proof.
    unfold image, imageH_diag. intros.
    red. intros * EQ.
    repeat intro. edestruct EQ. edestruct H.  eauto. eapply PER_is_ZZC; eauto. auto.
  Qed.

  Lemma imageH_diag_PER {A} (ma : m A) : (PER (imageH_diag ma)).
  Proof.
    split; repeat intro.
    - unfold imageH_diag in H.
      destruct H.
      red in H. split; repeat intro. specialize (H _ EQA H1). destruct H. eauto.
      specialize (H0 _ EQA H1). destruct H0. eauto.
    - unfold imageH_diag in H, H0.
      destruct H, H0. split; repeat intro.
      red in H, H1, H0, H2.
      specialize (H _ EQA H3). destruct H. eauto.
      specialize (H0 _ EQA H3). destruct H0.
      specialize (H1 _ EQA H3). destruct H1.
      specialize (H2 _ EQA H3). destruct H2.
      split; eapply H3. esplit; split. esplit; split.
      apply H. apply H6. auto.
      esplit; split. esplit; split.
      apply H5. apply H2. auto.
      specialize (H _ EQA H3). destruct H. eauto.
      specialize (H0 _ EQA H3). destruct H0.
      specialize (H1 _ EQA H3). destruct H1.
      specialize (H2 _ EQA H3). destruct H2.
      split; eapply H3. esplit; split. esplit; split.
      apply H. apply H6. auto.
      esplit; split. esplit; split.
      apply H5. apply H2. auto.
  Qed.

  Lemma image_subrel_imageH_diag :
    forall A (ma : m A),
      ma ≈{imageH_diag ma} ma ->
      image ma ⊑ imageH_diag ma.
  Proof.
    unfold image, imageH_diag. intros.
    repeat intro.
    pose proof @imageH_diag_PER.
    specialize (H1 A ma).
    specialize (H0 _ H1).
    apply H0; auto.
  Qed.

  Lemma imageH_image_eq :
    forall A (ma : m A),
      ma ≈{imageH_diag ma} ma ->
      eq_rel (image ma) (imageH_diag ma).
  Proof.
    intros.
    split. eapply image_subrel_imageH_diag; auto.
    apply imageH_subrel_image_diag.
  Qed.

  Lemma image_subset {A:Type} (ma : m A) :
    eqmR (image ma) ⊑ eqmR (@eq A).
  Proof.
    intros x y D.
    eapply Proper_eqmR_mono; eauto.
    eapply image_least. typeclasses eauto. reflexivity.
  Qed.

  Lemma image_inv:
    forall {A : Type} (ma : m A) (a1 a2 : A),
      image ma a1 a2  ->
      forall (R : relationH A A) (H : PER R), ma ≈{R} ma -> R a1 a2.
  Proof.
    repeat intro. unfold image in *.
    cbn in H. apply H; eauto.
  Qed.

  Global Instance Proper_image_eqmR {A} :
    Proper (eqmR eq ==> @eq A ==> @eq A ==> iff) image.
  Proof.
    intros x y EQ a1 a2 EQ' a3 a4 EQ''.
    subst. split; intros H.
    - red. unfold image_. intros.
      eapply H; eauto. rewrite EQ. auto.
    - red. unfold image_. intros.
      eapply H; eauto. rewrite <- EQ. auto.
  Qed.

  Global Instance Proper_mayRet_eqmR {A} :
    Proper (eqmR eq ==> @eq A ==> iff) mayRet.
  Proof.
    repeat intro. apply Proper_image_eqmR; eauto.
  Qed.

  Definition map_to_domain {A B} : relationH A B -> relationH A A :=
    fun R a1 a2 => a1 = a2 /\ exists (b : B), R a1 b.

  Lemma eqmR_property:
    forall A B (R : relationH A B) (ma : m A) (mb : m B),
      ma ≈{R} mb ->
      ma ≈{map_to_domain R} ma -> (forall x x', image ma x x' -> map_to_domain R x x').
  Proof.
    intros* EQ MAP x x' IMG.
    unfold map_to_domain in *.
    split. apply IMG. split; red; intuition; subst; auto.
    eapply Proper_eqmR_mono; eauto. repeat intro. destruct H. auto.
    eapply image_inv in MAP ; cycle 1. apply IMG.
    {
      split; red; intuition; subst; auto.
    } destruct MAP. auto.
  Qed.

End Image.

Notation "a1 ∈ ma" := (mayRet _ ma a1) (at level 40) : cat_scope.
Arguments image {_ _ _}.
Arguments imageH_diag {_ _ _}.

Section EqmRMonadLaws.
  Context (m : Type -> Type).
  Context {EqMRm : EqmR m}.
  Context {Mm : Monad m}.

  Class MayRetL : Prop :=
    mayRet_l : forall {A1 A2 : Type} (RA : relationH A1 A2) (ma1 : m A1) (ma2 : m A2)
                 (EQH : ma1 ≈{RA} ma2),
      forall a1, a1 ∈ ma1 -> exists a2, RA a1 a2 /\ a2 ∈ ma2.

  Class MayRetR : Prop :=
    mayRet_r : forall {A1 A2 : Type} (RA : relationH A1 A2) (ma1 : m A1) (ma2 : m A2)
                 (EQH : ma1 ≈{RA} ma2),
        forall a2, a2 ∈ ma2 -> exists a1, RA a1 a2 /\ a1 ∈ ma1.

  Class RetFinal : Prop :=
    final : forall {A1 A2 : Type} (RA : relationH A1 A2) (a1:A1) (a2:A2),
        RA a1 a2 -> ret a1 ≈{RA} ret a2.

  Class ImageEqmR : Prop :=
    image_eqmR : forall A (ma : m A), ma ≈{image ma} ma.

  Class ImagePost :=
    image_post :
      forall {A1 A2 : Type} (RR : relationH A1 A2) ma1 ma2,
        ma1 ≈{RR} ma2 -> ma1 ≈{fun x y => RR x y /\ x ∈ ma1 /\ y ∈ ma2 } ma2.

  Class ProperBind : Prop :=
    Proper_bind:
      forall {A1 A2 B1 B2 : Type} (RR : relationH A1 A2) (RB : relationH B1 B2)
        ma1 ma2 k1 k2,
      ma1 ≈{RR} ma2 ->
      (forall (a1 : A1) (a2 : A2), RR a1 a2 -> k1 a1 ≈{RB} k2 a2) ->
      bind ma1 k1 ≈{RB} bind ma2 k2.

  (* Monad laws *)
  Class BindRetL : Prop :=
    bind_ret_l : forall {A B : Type} (f : A -> m B) (a : A),
      bind (ret a) f ≈{eq} f a.

  Class BindRetR : Prop :=
    bind_ret_r : forall {A : Type} (ma : m A),
      bind ma ret ≈{eq} ma.

  Class BindBind : Prop :=
    bind_bind : forall {A B C : Type} (ma : m A) (f : A -> m B) (g : B -> m C),
      bind (bind ma f) g ≈{eq} bind ma (fun x => bind (f x) g).

  (* Generalization of monadic laws.
     These are of two quite distinct natures:
     * Heterogeneous generalizations of the usual three monad laws
     * Reasoning principles relating [eqmR R] to [R]
     *)
  Class EqmRMonadLaws :=
    {
    eqmR_mayRet_l :> MayRetL;
    eqmR_mayRet_r :> MayRetR;
    eqmR_image :> ImageEqmR;
    eqmR_ret :> RetFinal;
    eqmR_bind_ProperH :> ProperBind;
    eqmR_bind_ret_l :> BindRetL;
    eqmR_bind_ret_r :> BindRetR;
    eqmR_bind_bind :> BindBind
    }.

End EqmRMonadLaws.

Global Instance Proper_bind_pointwise {m : Type -> Type} {m_EqmR : EqmR m} {m_Monad : Monad m} {m_EqmR_OK : EqmR_OK m} {m_EqmRMonadLaws : EqmRMonadLaws m} : forall {A B},
    (@Proper (m A -> (A -> m B) -> m B)
             (eqmR eq ==> pointwise_relation _ (eqmR eq) ==> eqmR eq) bind).
Proof.
  repeat intro. eapply Proper_bind with (RR := eq); eauto; intros; subst; eauto. typeclasses eauto.
Qed.

Arguments mayRet_l {m _ _} [_ _].
Arguments mayRet_r {m _ _} [_ _].
Arguments final {m _ _ _} [_ _].
Arguments bind_ret_l {m _ _ _} [_ _].
Arguments bind_ret_r {m _ _ _} [_].
Arguments bind_bind {m _ _ _} [_ _ _].
Arguments Proper_bind {m _ _ _} [_ _ _ _].
Arguments Proper_bind_pointwise {m _ _ _ _} [_ _].

Section EqmRInversion.
  Context (m : Type -> Type).
  Context {Mm : Monad m}.
  Context {EqMR : EqmR m} {EqmRm: EqmRMonadLaws m} {EqmROKm : EqmR_OK m}.

  Definition mayRet_rel {A B} (ma : m A) (mb : m B) :=
    fun x y => x ∈ ma /\ y ∈ mb.

  Class RetInv : Prop :=
    ret_inv :
      forall {A1 A2 : Type} (RA : relationH A1 A2) (a1:A1) (a2:A2),
        ret a1 ≈{RA} ret a2 -> RA a1 a2.

  Class MayRetBindInv : Prop :=
    mayRet_bind_inv :
      forall (A B:Type) (ma:m A) (k:A -> m B),
      forall b, b ∈ bind ma k -> exists a, a ∈ ma /\ b ∈ k a.

  Class FmapInvRet : Prop :=
    fmap_inv_ret :
      forall (A B:Type) (ma :m A) (f f' :A -> B) (R:relationH B B),
        (f <$> ma) ≈{ R } (f' <$> ma) ->
        forall a : A, a ∈ ma -> ret (f a) ≈{ R } ret (f' a).

  Class BindInv : Prop :=
    bind_inv : forall (A1 A2 B1 B2: Type) (R : relationH B1 B2)
      (ma1 : m A1) (ma2 : m A2) (k1 : A1 -> m B1) (k2 : A2 -> m B2),
      (x <- ma1;; k1 x) ≈{ R } (x <- ma2;; k2 x) ->
      ma1 ≈{ fun x y => k1 x ≈{ R } k2 y } ma2.

  Class FmapInv_mayRet :=
    fmap_inv_mayRet :
      forall (A1 A2 B1 B2:Type) (R : relationH B1 B2)
        (f1 : A1 -> B1) (f2 :A2 -> B2) (ma1 : m A1) (ma2:m A2),
        (f1 <$> ma1) ≈{ R } (f2 <$> ma2) ->
        ma1 ≈{ fun a1 a2 => mayRet_rel ma1 ma2 a1 a2 /\ R (f1 a1) (f2 a2)} ma2.

  Class EqmRInv :=
    eqmR_inv : forall A (R : A -> A -> Prop) (ma : m A),
        ma ≈{R} ma -> forall a, a ∈ ma -> R a a.

  Class FmapInv :=
    fmap_inv :
      forall (A1 A2 B1 B2:Type) (R : relationH B1 B2)
        (f1 : A1 -> B1) (f2 :A2 -> B2) (ma1 : m A1) (ma2:m A2),
        (f1 <$> ma1) ≈{ R } (f2 <$> ma2) ->
        ma1 ≈{ fun a1 a2 => R (f1 a1) (f2 a2)} ma2.

  (* This is the key lemma that checks whether or not the monad has computations
     which are impure and has an observable step.

     Notably, the state monad does not respect this property (see [bind_ret_inv_counterexample]
     in [Monads/State.v]) which means that two impure computations can be
     composed to form a pure computation. This is especially true for states
     where you can "undo" what's been done.
   *)
  Class BindRetInv :=
    bind_ret_inv:
      forall {A B : Type} (ma : m A) (kb : A -> m B) (b : B),
        bind ma kb ≈{eq} ret b -> exists a : A, ma ≈{eq} ret a /\ kb a ≈{eq} ret b.

  Class EqmRInversionProperties :=
    {
      eqmR_ret_inv :> RetInv;
      eqmR_mayRet_bind_inv :> MayRetBindInv;
      eqmR_fmap_inv :> FmapInv;
      eqmR_inv_ :> EqmRInv
    }.

End EqmRInversion.

#[global]
 Instance FmapInv_ m  `{EqmR_OK m} {m_FmapInv_mayRet : FmapInv_mayRet m} : FmapInv m.
Proof.
  repeat intro. eapply fmap_inv_mayRet in H0; eauto.
  unfold mayRet_rel in H0.
  eapply Proper_eqmR_mono; eauto.
  repeat intro. destruct H1 as (?&?). auto.
Qed.

Arguments ret_inv {m _ _ _} [_ _].
Arguments mayRet_bind_inv {m _ _ _} [_ _].
Arguments fmap_inv_ret {m _ _ _} [_ _].
Arguments fmap_inv {m _ _ _} [_ _ _ _].

(* Notions of computational purity based on image. *)
Section Comp.

  Context {m : Type -> Type}.

  Context {Mm : Monad m}.
  Context {EqMR : EqmR m} {EqmRm: EqmRMonadLaws m} {EqmROKm : EqmR_OK m} {EqmRMonadInverses : EqmRInversionProperties m}.

  Import RelNotations.
  Local Open Scope relationH_scope.

  (* A sanity check about the images: *)
  Definition singletonR {A:Type} (x:A) : relationH A A :=
    fun a b => a = b /\ a = x.

  Lemma singletonR_SymmetricH {A:Type} (x:A) : SymmetricH (singletonR x).
  Proof.
    repeat red. intros a1 a2 H. unfold singletonR in H. cbn in *.
    destruct H. split; symmetry. tauto. rewrite <- H. symmetry. assumption.
  Qed.

  Lemma singletonR_TransitiveH {A:Type} (x:A) : TransitiveH (singletonR x).
  Proof.
    repeat red.
    intros.
    unfold singletonR in *. cbn in *.
    destruct H0, H; split; etransitivity; eauto. subst. auto.
  Qed.

  Lemma ret_image {A:Type} (x:A) : image (ret x) ≡ singletonR x.
  Proof.
    split.
    - repeat red. intros.
      unfold image in H. cbn in *.
      specialize (H (singletonR x)).
      assert (PER (singletonR x)).
      { split. apply singletonR_SymmetricH.
        apply singletonR_TransitiveH. }
      specialize (H H0).
      assert (eqmR (singletonR x) (ret x) (ret x)).
      { apply eqmR_ret. typeclasses eauto.  auto. esplit; reflexivity. }
      apply H in H1. repeat red in H2. assumption.
    - do 2 red. intros.
      unfold singletonR in H. destruct H. cbn in *.
      rewrite <- H. rewrite H0.
      subst.
      repeat intro.
      eapply eqmR_ret_inv; eauto...
  Qed.

  Lemma ret_mayRet {A : Type} : forall (a : A), a ∈ ret a.
  Proof.
    intros; unfold mayRet. apply ret_image. split; eauto.
  Qed.

  (* Under these well-formedness conditions of EqmR, eqmR eq and
    eqmR (image ma) coincides.*)
  Lemma image_eq {A} (ma ma': m A):
    eqmR eq ma ma' <-> eqmR (image ma) ma ma'.
  Proof.
    split.
    - repeat intro. eapply Proper_eqmR_cong; eauto...
      reflexivity. rewrite <- H. apply image_eqmR. typeclasses eauto.
    - eapply image_subset; eauto...
  Qed.

End Comp.

Section EqmRConsequences.

  Context (m : Type -> Type).
  Context {Mm : Monad m}.
  Context {EqMR : EqmR m} {EqmRm: EqmRMonadLaws m} {EqmROKm : EqmR_OK m} {EqmRMonadInverses : EqmRInversionProperties m}.

  Lemma eqmR_bind_ProperH_simple : forall {A1 A2 B1 B2 : Type}
                                     (RA : relationH A1 A2)
                                     (RB : relationH B1 B2)
                                     (ma1 : m A1) (ma2 : m A2)
                                     (k1 : A1 -> m B1) (k2 : A2 -> m B2),
      ma1 ≈{RA} ma2 ->
      (forall a1 a2, RA a1 a2 -> k1 a1 ≈{RB} k2 a2) ->
      bind ma1 k1 ≈{RB} bind ma2 k2.
  Proof.
    intros. apply Proper_bind with (RR := RA); auto.
  Qed.

  Global Instance Proper_eqmR_eq_impl :
    forall {m : Type -> Type} {Mm : Monad m} {E : EqmR m},
      EqmR_OK m -> forall A : Type,
        Proper (eqmR (@eq A) ==> eqmR eq ==> Basics.flip Basics.impl) (eqmR eq).
  Proof.
    repeat intro.
    symmetry.
    etransitivity; eauto.
    etransitivity; eauto.
    symmetry; eauto. symmetry; auto.
  Qed.

  Instance imageH_diag_Zigzag {A} (ma : m A) : Zigzag (imageH_diag ma).
  Proof.
    pose proof @imageH_diag_PER.
    eapply PER_is_ZZC; eauto.
  Qed.

  Lemma image_bind_eq {A B:Type} (ma : m A) (k1 k2 : A -> m B)
        (HK : forall (a1 a2 : A), image ma a1 a2 -> k1 a1 ≈{eq} k2 a2) :
    bind ma k1 ≈{eq} bind ma k2.
  Proof.
    eapply eqmR_bind_ProperH with (RR := image ma); auto...
    eapply image_eqmR. typeclasses eauto.
  Qed.

  Lemma image_ret_bind {A:Type} (ma : m A) (k : A -> m A) :
    (forall (a1 a2 : A), image ma a1 a2 -> k a1 ≈{eq} ret a2) ->
      bind ma k ≈{eq} bind ma ret.
  Proof.
    intros H.
    apply image_bind_eq. intros.
    apply H. assumption.
  Qed.

  Lemma mayRet_image1 {A:Type} (ma : m A) (a1 a2 : A) (HI : image ma a1 a2) :
    a1 ∈ ma.
  Proof.
    repeat red.
    intros.
    specialize (HI R PH EQR).
    change (R a1 a1).
    PER_reflexivityH.
  Qed.

  Lemma mayRet_image2 {A:Type} (ma : m A) (a1 a2 : A) (HI : image ma a1 a2) :
    a2 ∈ ma.
  Proof.
    repeat red.
    intros.
    specialize (HI R PH EQR).
    change (R a2 a2).
    PER_reflexivityH.
  Qed.

  Lemma image_ma_eq :
    forall A (ma1 : m A),
      ma1 ≈{fun x y => x = y /\ x ∈ ma1} ma1.
  Proof.
    intros. eapply eqmR_rel_conj; eauto. reflexivity.
    eapply Proper_eqmR_mono. 2 : eapply image_eqmR.
    intros ? ?. eapply mayRet_image1. typeclasses eauto.
  Qed.

  #[global] Instance image_post' : ImagePost m.
  Proof.
    repeat intro.
    pose proof (eqmR_rel_comp m). red in H0.
    specialize (H0 _ _ _ _ _ _ _ _ (image_ma_eq _ ma1) H). unfold rel_compose in H.
    pose proof (eqmR_rel_comp m). red in H1.
    specialize (H1 _ _ _ _ _ _ _ _ H0 (image_ma_eq _ ma2)). unfold rel_compose in H.
    eapply Proper_eqmR_mono; eauto.
    repeat intro. unfold rel_compose in H2. destruct H2 as (?&?&?).
    destruct H2 as (?&?&?). destruct H2, H3. subst. econstructor; eauto.
  Qed.

  Lemma clo_bind_gen :
    forall {A1 A2 B1 B2 : Type} (RR : relationH A1 A2) (RB : relationH B1 B2)
      ma1 ma2 k1 k2,
    ma1 ≈{RR} ma2 ->
    (forall (a1 : A1) (a2 : A2), a1 ∈ ma1 -> a2 ∈ ma2 -> RR a1 a2 -> k1 a1 ≈{RB} k2 a2) ->
    bind ma1 k1 ≈{RB} bind ma2 k2.
  Proof.
    intros. eapply Proper_bind. eapply image_post; eauto.
    typeclasses eauto. intros ? ? (?&?&?); eauto.
  Qed.


End EqmRConsequences.

Section InversionFacts.
  Context (m : Type -> Type).
  Context {Mm : Monad m}.
  Context {EqMR : EqmR m} {EqmRm: EqmRMonadLaws m} {EqmROKm : EqmR_OK m} {EqmRMonadInverses : EqmRInversionProperties m}.

  Instance FmapInvRet': FmapInvRet m.
  Proof.
  repeat intro.
  eapply fmap_inv in H. eapply eqmR_inv in H; eauto. 2 : typeclasses eauto.
  apply eqmR_ret; eauto.
  Qed.

  Instance FmapInvMayRet' : FmapInv_mayRet m.
  Proof.
    repeat intro.
    eapply fmap_inv in H. unfold mayRet_rel.
    eapply image_post in H; try typeclasses eauto.
    eapply Proper_eqmR_mono; eauto.
    repeat intro. destruct H0 as (?&?&?); repeat constructor; eauto.
  Qed.

  Lemma mayRet_fmap_inv {A B: Type} (ma : m A) (k : A -> B) (a:A) (b:B) :
    a ∈ ma ->
    b ∈ ret (k a) ->
    b ∈ (k <$> ma).
  Proof.
    intros HM HK.
    repeat red.
    intros.
    eapply fmap_inv_ret in EQR ; eauto.
    apply ret_inv in EQR.
    eapply HK; eauto. apply final; eauto.
  Qed.

  Lemma fmap_image :
    forall A B (x : B) (f : A -> B) (ma : m A),
      x ∈ (f <$> ma) <-> (exists y, y ∈ ma /\ (f y) = x).
  Proof.
    repeat intro. split; repeat intro; eauto.
    - eapply mayRet_bind_inv in H; eauto.
      destruct H as (? & ? & ?).
      eexists. unfold mayRet in H0.
      apply ret_image in H0.
      red in H0. destruct H0; subst; eauto.
    - destruct H as (? & ? & ?).
      apply fmap_inv in EQR; eauto...
      eapply eqmR_mayRet_l in EQR; eauto...
      specialize (EQR _ H). destruct EQR as (? & ? & ?). subst; auto.
      PER_reflexivityH.
  Qed.

  Lemma eqmR_fmap_R {A} (ma : m A) :
    (forall B (mb : m B) (f : B -> A) (R : A -> A -> Prop),
        ma ≈{(fun x y => R x (f y))} mb -> ma ≈{R} fmap f mb).
  Proof.
    repeat intro; eauto; intros.
    assert ((x <- ma;; ret x) ≈{R} (x <- mb;; ret (f x))).

    eapply eqmR_bind_ProperH; eauto; repeat intro...
    1: apply eqmR_ret; eauto...
    eapply Proper_eqmR_cong; eauto.
    rewrite bind_ret_r. reflexivity. unfold fmap. reflexivity.
  Qed.

End InversionFacts.

Class EQM (M : Type -> Type) {Monad_M : Monad M} (EQM_EqmR : EqmR M):= {
  EQM_EqmR_OK :> EqmR_OK M;
  EQM_EqmRMonad :> EqmRMonadLaws M;
  EQM_EqmRMonadInverses :> EqmRInversionProperties M
}.
