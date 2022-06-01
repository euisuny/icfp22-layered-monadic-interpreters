(** * Kleisli category *)

(** The category of "effectful functions", of type [a -> m b],
  for some monad [m]. *)

(** Note that this is not quite a Kleisli category over the
  category [Fun], as the notion of morphism equivalence is
  different. The category [Fun] uses pointwise equality,
  [eq ==> eq], while [Kleisli m] uses pointwise equivalence,
  [eq ==> eq1], for an equivalence relation [eq1] associated
  with the monad [m]. The right underlying category for [Kleisli]
  would be a category of setoids and respectful functions, but
  this seems awkward to program with. Investigating this
  question further is future work.
 *)

(* begin hide *)
From Coq Require Import
     Morphisms.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.Function
     Basics.HeterogeneousRelations
     EqmR.EqmRMonad.
(* end hide *)

Implicit Types m : Type -> Type.
Implicit Types a b c : Type.

Definition Kleisli m a b : Type := a -> m b.

(* SAZ: We need to show how these are intended to be used. *)
(** A trick to allow rewriting in pointful contexts. *)
Definition Kleisli_arrow {m a b} : (a -> m b) -> Kleisli m a b := fun f => f.
Definition Kleisli_apply {m a b} : Kleisli m a b -> (a -> m b) := fun f => f.

Definition pure {m} `{Monad m} {a b} (f : a -> b) : Kleisli m a b :=
  fun x => ret (f x).

Section Instances.
  Context {m : Type -> Type}.
  Context `{Monad m}.
  Context `{EqmR m}.

  Global Instance Eq2_Kleisli : Eq2 (Kleisli m) :=
    fun _ _ => pointwise_relation _ (eqmR eq).

  Global Instance Cat_Kleisli : Cat (Kleisli m) :=
    fun _ _ _ u v x =>
      bind (u x) (fun y => v y).

  Definition map {a b c} (g:b -> c) (ab : Kleisli m a b) : Kleisli m a c :=
     cat ab (pure g).

  #[global]
   Instance Initial_Kleisli : Initial (Kleisli m) void :=
    fun _ v => match v : void with end.

  #[global]
   Instance Id_Kleisli : Id_ (Kleisli m) :=
    fun _ => pure id.

  #[global]
   Instance Case_Kleisli : Case (Kleisli m) sum :=
    fun _ _ _ l r => case_sum _ _ _ l r.

  #[global]
   Instance Inl_Kleisli : Inl (Kleisli m) sum :=
    fun _ _ => pure inl.

  #[global]
   Instance Inr_Kleisli : Inr (Kleisli m) sum :=
    fun _ _ => pure inr.

  #[global]
   Instance Iter_Kleisli `{MonadIter m} : Iter (Kleisli m) sum :=
    fun a b => Basics.iter.

  (* #[global] *)
  (*  Instance Kleisli_MonadIter (m : Type -> Type) `{Iter _ (Kleisli m) sum} : MonadIter m := *)
  (*   fun a b => iter. *)

  Class ProperIter `{MonadIter m}: Prop :=
    Proper_iter: forall {A B: Type},
      Proper (pointwise_relation A (eqmR eq) ==> pointwise_relation A (eqmR (@eq B))) (iter (C := Kleisli m) (bif := sum)).

  Import RelNotations.
  Local Open Scope relationH_scope.
  Import MonadNotation.
  Local Open Scope monad_scope.

  (* [Iterative] laws describe how to manipulate the iter body, while these
   rules pertain to how to manipulate the loop index given that the domain of the
    index is a monad. *)
  Class ProperIterH `{MonadIter m}: Prop :=
    Proper_iterH : forall {A1 A2 B1 B2: Type} (RA : relationH A1 A2) (RB : relationH B1 B2),
      ProperH (pointwise_relationH RA (eqmR (sum_rel RA RB)) ~~> pointwise_relationH RA (eqmR RB))
              (iter (C := Kleisli m) (bif := sum))
              (iter (C := Kleisli m) (bif := sum)).

End Instances.

Arguments ProperIterH _ {_ _}.
Global Hint Mode Iter_Kleisli ! ! : typeclasses_instances.
(* Global Hint Mode Kleisli_MonadIter ! ! : typeclasses_instances. *)
