(** * Interpretable Monads *)

(** Interpretable monads encompass monads built from ITrees through
    layers of interpretation. Essentially, they are iterative monads
    that may trigger events. Interpretable monads interpret into
    interpretable monads, so that they can be layered.

    We define the following terminology for this library.
    Other sources may have different usages for the same or related
    words.

    The notation [E ~> F] stands for [forall T, E T -> F T]
    (in [ITree.Basics]).
    It can mean many things, including the following:

    - The semantics of itrees are given as monad morphisms
      [itree E ~> M], also called "interpreters".

    - "ITree interpreters" (or "itree morphisms") are monad morphisms
      where the codomain is made of ITrees: [itree E ~> itree F].

    Interpreters can be obtained from handlers:

    - In general, "event handlers" are functions [E ~> M] where
      [M] is a monad.

    - "ITree event handlers" are functions [E ~> itree F].

    Categorically, this boils down to saying that [itree] is a free
    monad (not quite, but close enough). *)

(* begin hide *)
From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Core.ITreeDefinition
     Core.Subevent
     Eq.Eq Eq.UpToTaus Eq.Paco2
     EqmR.EqmRMonad
     Indexed.Relation.

From ITree.EqmR Require Import
     EqmRMonad EqmRMonadT.

From Paco Require Import paco.

Import MonadNotation.
Local Open Scope cat_scope.
Local Open Scope monad_scope.
(* end hide *)

(** ** Translate *)

(** An event morphism [E ~> F] lifts to an itree morphism [itree E ~> itree F]
    by applying the event morphism to every visible event.  We call this
    process _event translation_.

    Translation is a special case of interpretation:
[[
    translate h t ≈ interp (trigger ∘ h) t
]]
    However this definition of [translate] yields strong bisimulations
    more often than [interp].
    For example, [translate (id_ E) t ≅ id_ (itree E)].
*)

(** A plain event morphism [E ~> F] defines an itree morphism
    [itree E ~> itree F]. *)
Definition translateF {E F R} (h : E ~> F) (rec: itree E R -> itree F R) (t : itreeF E R _) : itree F R  :=
  match t with
  | RetF x => Ret x
  | TauF t => Tau (rec t)
  | VisF e k => Vis (h _ e) (fun x => rec (k x))
  end.

Definition translate {E F} (h : E ~> F)
  : itree E ~> itree F
  := fun R => cofix translate_ t := translateF h translate_ (observe t).

Arguments translate {E F} h [T].

(** * Interpret *)
(** Interpretation schemes can be generalized as a function from a stack of monads
   [T] applied to a interpretable monad [IM] with an indexing [I] to a semantic
   domain [T M].

   It takes as handler [h: I ~> M], which is informative of how the index should
   be interpreted into the semantic domain.

   We call any such [T IM] that has an [interp] function defined over it an
   _interpretable monad_.
 *)
Class Interp (IM T: (Type -> Type) -> Type -> Type) (M : Type -> Type) :=
  interp : forall (I : Type -> Type) (h: I ~> M), T (IM I) ~> T M.

(** Typically, an event handler [E ~> M] defines a monad morphism [itree E ~> M]
  for any monad [M] with a loop operator.

  This itree interpretation is an instance of the general interpretation scheme. *)
Definition interp_body {E M : Type -> Type}
            {MM : Monad M} {MI : MonadIter M}
           (h : E ~> M) :
  forall R : Type, itree E R -> M (itree E R + R)%type :=
  (fun _ t =>
    match observe t with
    | RetF r => ret (inr r)
    | TauF t => ret (inl t)
    | VisF e k => bind (h _ e) (fun x => (ret (inl (k x))))
    end).

(** ITrees are an interpretable monad. *)
#[global] Instance itree_interp {M : Type -> Type}
           {MM : Monad M} {MI : MonadIter M} :
  Interp itree (fun x => x) M := fun _ h R => iter (interp_body h _).

Arguments itree_interp / {_ _ _ _}.
Arguments interp {IM T M _ _} h [_].
Arguments Interp _ {_} _.

