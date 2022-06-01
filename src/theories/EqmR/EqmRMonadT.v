(* We are interested in various equational theories of monads, and also how they
   interplay with each other. There are two motivations for this : one is the
   existence of multiple valid equational theories for a particular monad (or a
   family of monads, such as the state monad that can be parameterized with a
   state). The second is the curious, but useful existence of monad transformers
    -- curious, because they tend to be rather awkward to formalize
   categorically, and also since they derive the question: what does it mean to
   transform an equational theory of one monad to another? Another point is that
   it is not immediately clear that there are valid monad transformers that
   preserves equational theories, since categorically the distributive law does
   not hold for any pair of arbitrary monads.

   Let's start with the notion of a monad transformer being "a natural
   transformation between two monads as functors that commutes with the two
   monads’ unit (return) and bind (>>=) operations" [1] and see if we can
   define a lifting of the theories that correspond to a natural transformation.

    [1] http://conway.rutgers.edu/~ccshan/wiki/blog/posts/Monad_transformers/
 *)

From Coq Require Import
     Morphisms.

From ExtLib Require Import
     Monad.

From ITree Require Import
     Basics.Basics
     Basics.HeterogeneousRelations
     Basics.CategoryKleisli
     CategoryOps
     CategoryTheory
     CategoryFunctor .

From ITree.EqmR Require Import
     EqmRMonad.

Import CatNotations.
Import MonadNotation.
Import RelNotations.
Local Open Scope cat_scope.
Local Open Scope monad_scope.
Local Open Scope relationH_scope.

(* Definition of a monad morphism from monad [M] to monad [N] parameterized by
   EqmR definition *)
Section MonadMorphism.

  Context (M : Type -> Type) (MT : Type -> Type).

  Context (M_Monad : Monad M) (N_Monad : Monad MT)
          (EqmRM : EqmR M) (EqmRN : EqmR MT).

  Class Morph :=
    morph : forall (A : Type), (M A) -> (MT A).

  Context {M_morph : Morph}.

  Class MorphRet : Prop :=
    morph_ret : forall (A B : Type) (R : A -> B -> Prop) (x : A) (x' : B),
      R x x' ->
      morph A (ret (m := M) x) ≈{R} ret (m := MT) x'.

  (* morph (`bind` ma k) = `bind` (morph ma) (morph . k) *)
  Class MorphBind : Prop :=
    morph_bind : forall (A1 A2 B1 B2 : Type) (RA : A1 -> A2 -> Prop) (RB : B1 -> B2 -> Prop) ma ma' (k : A1 -> M B1) (k': A2 -> M B2),
      eqmR (m := M) RA ma ma' ->
      (forall a a', RA a a' -> k a ≈{RB} k' a') ->
      morph B1 (bind ma k) ≈{RB} bind (morph A2 ma') (fun x => morph B2 (k' x)).

  Class MorphProper : Prop :=
    morph_proper : forall (R1 R2 : Type) (RR : R1 -> R2 -> Prop),
      ProperH (eqmR RR ~~> eqmR RR) (morph R1) (morph R2).

  Class IterMorphism {M_MonadIter: Basics.MonadIter M} {MT_MonadIter: Basics.MonadIter MT} : Prop :=
    morph_iter : forall I R t t' (i : I),
      (forall (i : I), eqmR (m := MT) eq (morph _ (t i)) (t' i)) ->
      eqmR (m := MT) (@eq R) (morph _ (Basics.iter t i)) (Basics.iter t' i).

  Class MonadMorphism :=
    {
      MM_EQM :> EQM MT EqmRN;
      MM_morph_ret :> MorphRet;
      MM_morph_bind :> MorphBind;
      MM_morph_proper :> MorphProper;
    }.

End MonadMorphism.

Arguments MorphRet _ _ {_ _ _} _.
Arguments MorphBind _ _ {_ _ _ _} _.
Arguments MonadMorphism _ _ {_ _ _ _} _.
Arguments IterMorphism {_ _ _} _ {_ _}.
Arguments morph / {_ _ _ _}.
Arguments morph_ret {_ _ _ _ _ _ _} [_ _].
Arguments morph_bind {_ _ _ _ _ _ _ _} [_ _ _ _].
Arguments morph_proper {_ _ _ _ _ _} [_ _].
Arguments morph_iter {_ _ _ _ _ _ _} [_ _].

Section EqmRMonadTransformer.

  Context (T : (Type -> Type) -> Type -> Type).

  Class MonadT (T : (Type -> Type) -> Type -> Type) := {
    lift :> forall m {Monad_m : Monad m}, Morph m (T m);
    MT_Monad :> forall (m : Type -> Type), Monad m -> Monad (T m);
    MT_EqmR :> forall (m : Type -> Type), EqmR m -> EqmR (T m);
  }.

  Class MonadTLaws (T : (Type -> Type) -> Type -> Type) {MT : MonadT T} := {
    MT_MonadMorphism:>
        forall (m : Type -> Type) (Monad_m : Monad m) (EqmR_m : EqmR m) (EQM_m : EQM m EqmR_m),
        @MonadMorphism m (T m) Monad_m (MT_Monad m Monad_m) EqmR_m (MT_EqmR m EqmR_m) (lift m)
    }.

End EqmRMonadTransformer.

Arguments lift / {_ _ _ _} [A].

#[global] Instance compose_MonadT (S T : (Type -> Type) -> Type -> Type)
 {S_MonadT : MonadT S} {T_MonadT : MonadT T} : MonadT (fun x => S (T x)).
Proof.
  constructor; repeat intro; try typeclasses eauto.
  - exact (lift (T := S) (lift (T := T) X)).
Defined.

Class IterativeMonad (M : Type -> Type) := {
  IM_Monad :> Monad M;
  M_EqmR :> EqmR M;
  IM_MonadIter :> MonadIter M;}.

Class WF_IterativeMonad (M : Type -> Type) (IM_Monad : Monad M) (M_EqmR : EqmR M) (IM_MonadIter : MonadIter M) := {
  M_EQM :> EQM M M_EqmR;
  M_Iterative :> Iterative (Kleisli M) sum;
  M_ProperIter :> @ProperIterH M _ _;}.

Class IterativeMonadT (T : (Type -> Type) -> Type -> Type) := {
  T_MonadT :> MonadT T;
  T_MonadIter :> forall (m : Type -> Type), Monad m -> MonadIter m -> MonadIter (T m);}.

Global Hint Mode IterativeMonadT ! : typeclasses_instances.
Global Hint Mode T_MonadIter ! ! ! ! ! : typeclasses_instances.

#[global] Instance compose_IterativeMonadT {S T : (Type -> Type) -> Type -> Type} `{IterativeMonadT S} `{IterativeMonadT T}:
  IterativeMonadT ((fun x => S (T x))).
Proof.
  constructor; try typeclasses eauto.
Defined.

Class WF_IterativeMonadT (T : (Type -> Type) -> Type -> Type) (T_MonadT : MonadT T)
  (T_MonadIter : forall (m : Type -> Type), Monad m -> MonadIter m -> MonadIter (T m)) := {
  (* Rules w.r.t. iteration body *)
  T_Iterative :> forall (m : Type -> Type)  `{WF_IterativeMonad m},
      Iterative (Kleisli (T m)) sum;
  (* Rules w.r.t indexing of iter *)
  T_ProperIter :> forall M `{WF_IterativeMonad M},
      ProperIterH (T M);
 (* Monad transformer laws*)
    T_MonadTLaws :> MonadTLaws T;}.

Global Hint Mode WF_IterativeMonadT ! ! ! : typeclasses_instances.

#[global] Instance compose_WF_IterativeMonadT {S T : (Type -> Type) -> Type -> Type}
 `{WF_IterativeMonadT S} `{WF_IterativeMonadT T}:
  WF_IterativeMonadT ((fun x => S (T x))) _ _.
Proof.
  econstructor; try typeclasses eauto.
  2 : {
    repeat intro.
    destruct H.
    pose proof (T_ProperIter0 (T M)).
    specialize (H _ _ _).
    repeat red in H. eapply H; eauto.
    econstructor; try typeclasses eauto.
  }
  repeat intro. destruct H. eapply T_Iterative0; econstructor; try typeclasses eauto.
  {
    repeat intro. destruct H.
    constructor; eauto.
    destruct T_MonadTLaws0.
    intros.
    pose proof (MT_MonadMorphism0 (T m) _ _ _).
    constructor; try typeclasses eauto.
    all : destruct H; repeat intro.
    - repeat intro; eauto.
      cbn.
      repeat red in MM_morph_proper0. cbn in MM_morph_proper0.
      specialize (MM_morph_proper0 A A eq ((let (lift0, _, _) := T_MonadT1 in lift0) m Monad_m A (ret x))).
      rewrite MM_morph_proper0.
      eapply MM_morph_ret; try typeclasses eauto; eauto.
      eapply MM_morph_ret; try typeclasses eauto; eauto.
    - repeat intro; eauto.
      cbn.
      repeat red in MM_morph_proper0. cbn in MM_morph_proper0.
      specialize (MM_morph_proper0 B1 B1 eq ((let (lift0, _, _) := T_MonadT1 in lift0) m Monad_m B1 (x <- ma;; k x))).
      rewrite MM_morph_proper0.
      eapply MM_morph_bind; try typeclasses eauto; eauto.
      eapply MM_morph_proper; try typeclasses eauto; eauto.
      intros.
      eapply MM_morph_proper; try typeclasses eauto; eauto.
      eapply MM_morph_bind; try typeclasses eauto; eauto. eapply reflexivity.
      intros; subst; reflexivity.
    - cbn.
      eapply MM_morph_proper; try typeclasses eauto.
      eapply MM_morph_proper; try typeclasses eauto. eauto.
  }
Qed.
