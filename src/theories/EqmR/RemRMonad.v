From Coq Require Import
     Morphisms
     Program.

From ExtLib Require Import
     Monad.

From ITree Require Import
     Basics.HeterogeneousRelations
     CategoryKleisli
     CategoryTheory
     CategoryOps.

From ITree.EqmR Require Import
     Tacs
     EqmRMonad.

Import CatNotations.
Import MonadNotation.
Local Open Scope monad_scope.
Local Open Scope cat_scope.

(* Equality between Kleisli arrows (C(K)ontinuations...)*)
Section Keq.

  Context (m : Type -> Type).
  Context `{EqmR m}.

  (* We consider heterogeneous relations on kleisli arrows parameterized by
    relations on return types *)

  Definition keq {A1 A2 B1 B2 : Type} (P : relationH A1 A2) (Q : relationH B1 B2)
    : relationH (A1 -> m B1) (A2 -> m B2) :=
      fun (k1 : A1 -> m B1) (k2 : A2 -> m B2) =>
        (forall a1 a2, P a1 a2 -> k1 a1 ≈{Q} k2 a2).

  Notation "⟦ P ⟧ k1 ≲ k2 ⟦ Q ⟧" := (keq P Q k1 k2) (at level 100) : cat_scope.

End Keq.

Arguments keq {_ _ _ _ _ _}.
Notation "⟦ P ⟧ k1 ≲ k2 ⟦ Q ⟧" := (keq P Q k1 k2) (at level 100) : cat_scope.

Import RelNotations.
Local Open Scope relationH_scope.
From ITree Require Import Basics.Function Basics.FunctionFacts.

Section Image.

  Context {m : Type -> Type}.
  Context {K : EqmR m}.

  (* Heterogeneous image of two continuations, using zigzag complete relations. *)
  (* A family of images, with preconditions satisfying a fixed binary
    specification [P]. *)

  (* Homogeneous version of image. *)
  Definition imageK_ {A B : Type} (P : relationH A A) (k : A -> m B)  : relationH B B :=
    fun x y => forall (Q : relationH B B) (PQ : PER Q)
              (EQR : ⟦ P ⟧ k ≲ k ⟦ Q ⟧), Q x y.

  (* IY: move to [Relations.v]? *)
  Definition diagL {A B : Type} (R : relationH A B) : relationH A A :=
    fun x y => exists b b', R x b /\ R y b'.

  Definition diagR {A B : Type} (R : relationH A B) : relationH B B :=
    fun x y => exists a a', R a x /\ R a' y.

  Definition imageK {A1 A2 B1 B2 :Type} (P : relationH A1 A2)
             (k1 : A1 -> m B1) (k2 : A2 -> m B2) : relationH B1 B2 :=
    fun x y => imageK_ (diagL P) k1 x x /\ imageK_ (diagR P) k2 y y.

  Definition mayRetK {A B : Type} (P : relationH A A) (k : A -> m B) (x : B) :=
    imageK P k k x x.

  Global Instance image_ZZC {A1 A2 B1 B2: Type}
         (P : relationH A1 A2) (k1 : A1 -> m B1) (k2 : A2 -> m B2) :
    Zigzag (imageK P k1 k2).
  Proof.
    unfold imageK. red. repeat intro.
    destruct H as (? & ? & ?). destruct H as (? & ? & ?).
    cbn in *. red in H1. crunch; eauto.
  Qed.

  (* TODO: We should be able to prove properties about intersection with images? *)
End Image.

(* Idea: Hoare triples on continuations (Q. How does this relate to computations?)
    What does it mean to apply a continuation? *)
Section KEqMonad.
  Context (m : Type -> Type).
  Context {EqMRm : EqmR m}.
  Context {Mm : Monad m}.

  (* [ret] : identity in kleisli category *)
  (* [bind] : morphisms in kleisli category *)

  (* {| eq |} (fun x => ret 0) ≲ (fun x => ret 0) {| eq |}*)

  (* (fun x => ret {0} ) ≲ (fun x => ret {0, 1} ) *)
  (* (fun x => ret (x + x)) ≲ (fun x => ret (2 * x)) *)

  (* Example :
      Monad morphism
      state S A, state T A
      (H : state S A -> state T A) (Commutativity : H (ret x) ≈ ...)
   *)
  (* Precondition states that our entry is a singleton
      (encoding application in precondtion)
     Postcondition is the "R" in the old relation
   *)
  (* {| fun x y => x = y /\ x = 0 } |} (fun x => ret 0) ≲ (fun x => ret 0) {| eq |} *)

  Class keq_ret : Prop :=
    ret_ : forall (A1 A2 : Type) (P : relationH A1 A2) (Q : relationH A1 A2),
      (forall x y, P x y -> Q x y) -> ⟦ P ⟧ ret ≲ ret ⟦ Q ⟧.

  Class keq_bind : Prop :=
    bind_ : forall (A1 A2 B1 B2 C1 C2 : Type) (P : relationH A1 A2) (Q : relationH B1 B2) (R : relationH C1 C2)
      (f : A1 -> m B1) (g : A2 -> m B2) (k1 : B1 -> m C1) (k2 : B2 -> m C2),
      ⟦ P ⟧ f ≲ g ⟦ Q ⟧ ->
        ⟦ fun x y => Q x y /\ mayRetK (diagL P) f x ⟧ k1 ≲ k2 ⟦ R ⟧ ->
        ⟦ fun x y => Q x y /\ mayRetK (diagR P) g y ⟧ k1 ≲ k2 ⟦ R ⟧ ->
        ⟦ P ⟧ (f >>> k1) ≲ (g >>> k2) ⟦ R ⟧.

  Class keq_bind_ret_l :=
    bind_ret_l : forall (A : Type) (f : A -> m A),
      ⟦ eq ⟧ ret >>> f ≲ f ⟦ eq ⟧.

  Class keq_bind_ret_r :=
    bind_ret_r : forall (A : Type) (P Q : relationH A A) (f : A -> m A),
      ⟦ eq ⟧ f >>> ret (m := m) ≲ f ⟦ eq ⟧.

  Class keq_bind_bind :=
    bind_bind : forall (A B C D: Type) (f : A -> m B) (g : B -> m C) (k : C -> m D),
      ⟦ eq ⟧ f >>> g >>> k ≲ f >>> (g >>> k) ⟦ eq ⟧.

  Class KEqMonad :=
  {
    keqm_ret :> keq_ret;
    keqm_bind :> keq_bind;
    keqm_bind_ret_l :> keq_bind_ret_l;
    keqm_bind_ret_r :> keq_bind_ret_r;
    keqm_bind_bind :> keq_bind_bind;
  }.

  (* TODO : mayRet rules are a little funny..  *)
  Class keq_mayRet_l :=
    mayRet_l : forall (A1 A2 B1 B2 : Type) (P : relationH A1 A2) (Q : relationH B1 B2)
      (k1 : A1 -> m B1) (k2 : A2 ->  m B2) (EQH : ⟦ P ⟧ k1 ≲ k2 ⟦ Q ⟧),
        forall b1, mayRetK (diagL P) k1 b1 -> exists b2, Q b1 b2 /\ mayRetK (diagR P) k2 b2.

  Class keq_mayRet_r :=
    mayRet_R : forall (A1 A2 B1 B2 : Type) (P : relationH A1 A2) (Q : relationH B1 B2)
      (k1 : A1 -> m B1) (k2 : A2 ->  m B2) (EQH : ⟦ P ⟧ k1 ≲ k2 ⟦ Q ⟧),
      forall b2, mayRetK (diagR P) k2 b2 -> exists b1, Q b1 b2 /\ mayRetK (diagL P) k1 b1.

End KEqMonad.

Section KEqMonadInstance.
  Context (m : Type -> Type).
  Context {Mm : Monad m}.
  Context {EqMRm : EqmR m}.
  Context {EqMOm : EqmR_OK m}.
  Context {EqMm : EqmRMonad m}.
  Context {EqMIm : EqmRMonadInverses m}.

  Instance keqm_ret_ : keq_ret m.
  Proof.
    repeat intro.
    apply eqmR_ret ; eauto.
  Qed.

  Instance keqm_bind_ : keq_bind m.
  Proof.
    repeat intro.
    unfold cat, Cat_Kleisli.
    eapply eqmR_bind_ProperH; eauto.
    all : intros; eauto.
    eapply H0; split; auto; repeat intro.
    red. split; repeat intro.
    eapply H3; eauto. eapply EQR.
    red. eexists; eexists; split; eauto.
    1, 2 : red; eexists; eexists; split; eauto.
    eapply H3; eauto. eapply EQR.
    red. eexists; eexists; split; eauto.
    1, 2 : red; eexists; eexists; split; eauto.

    eapply H1; split; auto; repeat intro;
    red; red; split; red; intros; eapply H3; eauto; eapply EQR;
    red; eexists; eexists; split; eauto;
      red; eexists; eexists; split; eauto.
  Qed.

  Instance keqm_bind_ret_l_ : keq_bind_ret_l m.
  Proof.
    repeat intro.
    unfold cat, Cat_Kleisli.
    eapply Proper_eqmR_morphism; auto.
    rewrite eqmR_bind_ret_l. 1, 2 : eapply eqmR_transport_Equiv; eauto.
    1, 2 : typeclasses eauto.
    subst. eapply eqmR_transport_Equiv; typeclasses eauto.
  Qed.

  Instance keqm_bind_ret_r_ : keq_bind_ret_r m.
  Proof.
    repeat intro.
    unfold cat, Cat_Kleisli.
    eapply Proper_eqmR_morphism; auto.
    rewrite eqmR_bind_ret_r; eauto. 1, 2 : eapply eqmR_transport_Equiv; typeclasses eauto.
    subst. eapply eqmR_transport_Equiv ; typeclasses eauto.
  Qed.

  Instance keqm_bind_bind_ : keq_bind_bind m.
  Proof.
    repeat intro.
    unfold cat, Cat_Kleisli.
    eapply Proper_eqmR_morphism; auto.
    rewrite eqmR_bind_bind; eauto. 1, 2 : eapply eqmR_transport_Equiv ; typeclasses eauto.
    subst. eapply eqmR_transport_Equiv ; typeclasses eauto.
  Qed.

  Global Instance KeqmMonad : KEqMonad m.
  Proof.
    constructor; typeclasses eauto.
  Qed.

End KEqMonadInstance.

(* Section Kleisli_Eq2. *)
(*   Context (m : Type -> Type). *)
(*   Context {Mm : Monad m}. *)
(*   Context {EqMRm : EqmR m}. *)
(*   Context {EQM_m : EQM m EqMRm}. *)

(*   Global Instance Eq2_Kleisli_m : (Eq2 (Kleisli m)) := *)
(*     fun (a b : Type) (f g : Kleisli m a b) => ⟦ eq ⟧ f ≲ g ⟦ eq ⟧. *)
(* End Kleisli_Eq2. *)

