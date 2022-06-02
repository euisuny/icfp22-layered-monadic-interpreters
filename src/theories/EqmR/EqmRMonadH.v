(** * Relations over different monads *)
(** In many practical situations, such as when expressing the correctness of a
  pass of compilation from distinct source and target languages, we need to state
  a relation over distinct monads.

  We provide a more general notion of family of relations that are parameterized
  by two monads, and lifts relations at return types. Each monad comes with its
  own relational theory, and this "hetergeneous" [eqmR] respects the relational
  theory for each monad. *)

(* begin hide *)
From Coq Require Import
     Morphisms
     Program.

From ExtLib Require Import
     Monad.

From ITree Require Import
     Basics.HeterogeneousRelations
     Basics.Function
     Basics.FunctionFacts
     CategoryTheory
     CategoryOps
     EqmR.EqmRMonad.

Set Primitive Projections.

Import CatNotations.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope cat_scope.
(* end hide *)

Section EqmRH.

  Class EqmRH (m : Type -> Type) (m' : Type -> Type): Type :=
    {
    eqmRH : forall {A B : Type} (R : relationH A B), relationH (m A) (m' B);
    }.

  (** The more traditional notion of monadic equivalence is recovered at the
    equality relation [forall A,  m A -> m A -> Prop] *)
  Definition eqmH {m m': Type -> Type} `{@EqmRH m m'} {A: Type} := @eqmRH m m'.

End EqmRH.

Arguments eqmRH {m m' _ A B}.
Arguments eqmH {m m' _ A _}.

Import RelNotations.
Local Open Scope relationH_scope.

#[global] Instance EqmR_EqmRH {m} {m_EqmR : EqmR m} : EqmRH m m :=
  {| eqmRH := fun (A B : Type) (R : relationH A B) => let X := @eqmR _ m_EqmR in X A B R |}.

Section EqmRH_WF.
  Context (m m': Type -> Type).
  Context {m_EqmRH: EqmRH m m'}.
  Context {m_EqmR: EqmR m}.
  Context {m'_EqmR : EqmR m'}.

  Class Proper_EqmRH : Type :=
      proper_eqmRH :> forall {A B} (R : relationH A B),
          Proper (eqmR (m := m) eq ==> eqmR (m := m') eq ==> iff) (eqmRH R).

End EqmRH_WF.
Arguments Proper_EqmRH {_ _} _ {_ _}.
Arguments proper_eqmRH {_ _ _ _ _ _} [_ _].

Section EqmRRelH.
  Context (m m': Type -> Type).
  Context {m_EqmRH: EqmRH m m'}.
  Context {m_EqmR: EqmR m}.
  Context {m'_EqmR : EqmR m'}.

  (** Requirements of well-formedness of [eqmRH] *)
  Class EqmRH_OK : Type :=
    {
      eqmRH_transport_Zigzag :
        forall {A B : Type} (R : relationH A B), Zigzag R -> Zigzag (eqmRH (m := m) (m' := m') R);

      eqmRH_rel_comp : forall {A B C : Type}
                        (R1 : relationH A B)
                        (R2 : relationH B C)
                        (ma : m A) (mb : m' B) (mc : m' C),
          eqmRH R1 ma mb ->
          eqmRH R2 mb mc ->
          eqmRH (R2 ∘ R1) ma mc;

      eqmRH_lift_transpose : forall {A B : Type} (R : relationH A B)
        , eq_rel (eqmRH †R) (†(eqmRH R));

      eqmRH_Proper :> forall {A B : Type},
          Proper (@eq_rel A B ==> eq_rel) eqmRH;

      eqmRH_Proper_mono :> forall {A B},
          Proper ((@subrelationH _ _) ==> (@subrelationH _ _)) (@eqmRH m m' _ A B);
    }.

End EqmRRelH.

#[global] Instance EqmR_OK_EqmRH_OK
 {m} {m_EqmR : EqmR m} {m_Monad : Monad m} {m_EqmR_OK : EqmR_OK m} : EqmRH_OK m m.
Proof.
  constructor.
  { (* Zigzag *)
    repeat intro. repeat destruct H0 as (?&?&?).
    cbn in *. repeat red in H.
    eapply Proper_eqmR_mono; [ repeat intro; eapply H; eauto | ].
    eapply eqmR_rel_comp; eauto.
    eapply eqmR_rel_comp; eauto.
    eapply eqmR_lift_transpose; eauto. }
  { (* Comp *)
    repeat intro; eapply eqmR_rel_comp; eauto. }
  { (* Transpose *)
    repeat intro; eapply eqmR_lift_transpose; eauto. }
  { (* Proper *)
    cbn; repeat intro; rewrite H; reflexivity. }
  { (* Proper_mono *)
    cbn; repeat intro; eapply Proper_eqmR_mono; eauto. }
Qed.

Section Image.
  Context (m m' : Type -> Type).
  Context {Mm : Monad m} {Mm' : Monad m'}.
  Context {m_EqmRH : EqmRH m m'}
          {m_EqmR : EqmR m} {m'_EqmR : EqmR m'}
          {m_EqmRH_OK : EqmRH_OK m m'}.

  Definition imageH {A1 A2 :Type} (ma1 : m A1) (ma2 : m' A2) : relationH (A1 * A2) (A1 * A2) :=
    fun '(a1, a2) '(a1', a2') =>
      forall (RA : relationH A1 A2)
        (EQA : eqmRH (m := m) (m' := m') RA ma1 ma2)
        (H : Zigzag RA), RA a1 a2 /\ RA a1' a2'.

  (* NB: Every PER is difunctional, but the converse does not hold. *)
  Definition image {A:Type} (ma : m A) : relationH A A :=
    fun x y =>
      forall (R : relationH A A) (PH : PER R)
        (EQR: eqmRH R ma ma), R x y.

  Definition mayRet {A:Type} (ma : m A) : A -> Prop :=
    (fun (a:A) => image ma a a).

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
  Defined.

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
        (G: eqmRH R ma ma)
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


  Lemma image_inv:
    forall {A : Type} (ma : m A) (a1 a2 : A),
      image ma a1 a2  ->
      forall (R : relationH A A) (H : PER R), ma ≈{R} ma -> R a1 a2.
  Proof.
    repeat intro. unfold image in *.
    cbn in H. apply H; eauto.
  Qed.

End Image.

Arguments image {_ _ _}.
Arguments mayRet {_ _ _}.

Section EqmRHMonad.
  Context (m : Type -> Type).
  Context (m' : Type -> Type).
  Context {m_EqmRH : EqmRH m m'}.
  Context {m_EqmR : EqmR m}.
  Context {m'_EqmR : EqmR m'}.
  Context {m_EqmRH_OK: EqmRH_OK m m'}.
  Context {Mm : Monad m}.
  Context {Mm' : Monad m'}.

  Class EqmRHMonadLaws :=
    {
    eqmRH_mayRet_l : forall {A1 A2 : Type}
                      (RA : relationH A1 A2)
                      (ma1 : m A1) (ma2 : m' A2)
                      (EQH : eqmRH RA ma1 ma2),
        forall a1, mayRet ma1 a1 -> exists a2, RA a1 a2 /\ mayRet ma2 a2;

    eqmRH_mayRet_r : forall {A1 A2 : Type}
                      (RA : relationH A1 A2)
                      (ma1 : m A1) (ma2 : m' A2)
                      (EQH : eqmRH RA ma1 ma2),
        forall a2, mayRet ma2 a2 -> exists a1, RA a1 a2 /\ mayRet ma1 a1;

    eqmRH_ret : forall {A1 A2 : Type} (RA : relationH A1 A2) (a1:A1) (a2:A2),
        RA a1 a2 -> eqmRH RA (ret a1) (ret a2);

    eqmRH_Proper_bindH:
      forall {A1 A2 B1 B2 : Type} (RR : relationH A1 A2) (RB : relationH B1 B2)
        (ma1 : m A1) (ma2 : m' A2) k1 k2,
      eqmRH RR ma1 ma2 ->
      (forall (a1 : A1) (a2 : A2), RR a1 a2 -> eqmRH RB (k1 a1) (k2 a2)) ->
      eqmRH RB (bind ma1 k1) (bind ma2 k2);

    (* Monad laws *)
    eqmRH_bind_ret_l : forall {A B : Type}
                        (f : A -> m B)
                        (R : relationH B B)
                        (a : A),
        eqmRH eq (bind (ret a) f) (f a);

    eqmRH_bind_ret_r : forall {A : Type}
                             (R : relationH A A)
                            (ma : m A),
        eqmRH eq (bind ma ret) ma;

    eqmRH_bind_bind : forall {A B C : Type}
                       (ma : m A)
                       (R : relationH C C)
                       (f : A -> m B)
                       (g : B -> m C),
        eqmRH eq (bind (bind ma f) g) (bind ma (fun x => bind (f x) g))
    }.

End EqmRHMonad.

(* We can derive a diagonal [eqmRH] from a [eqmR] *)
#[global] Instance EqmRMonad_EqmRMonadH
 {m} {m_EqmR : EqmR m} {m_Monad : Monad m}
 {m_EqmR_OK : EqmR_OK m} {m_EqmRMonad : EqmRMonadLaws m} : EqmRHMonadLaws m m.
Proof.
  constructor; repeat intro; eauto.
  { (* MayRet L *)
    eapply eqmR_mayRet_l; eauto. }
  { (* MayRet R *)
    eapply eqmR_mayRet_r; eauto. }
  { (* Ret done *)
    eapply eqmR_ret; eauto. }
  { (* Bind proper *)
    eapply Proper_bind; eauto. }
  { (* Bind left unital *)
    rewrite eqmR_bind_ret_l; eauto; reflexivity. }
  { (* Bind right unital *)
    rewrite eqmR_bind_ret_r; eauto; reflexivity. }
  { (* Bind bind *)
    rewrite eqmR_bind_bind; eauto; reflexivity. }
Qed.

