(** * State *)

(** Events to read and update global state. *)

(* begin hide *)
From ExtLib Require Import
     Structures.Functor.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.CategoryKleisli
     Core.ITreeDefinition
     Indexed.Function
     Indexed.Sum
     Core.Subevent
     EqmR.EqmRMonadT
     EqmR.Monads.StateT
     Interp.Interp
     Interp.HFunctor
     Interp.InterpFacts.

Import ITree.Basics.Basics.Monads.

Local Open Scope itree_scope.
(* end hide *)

(* Stateful handlers [E ~> stateT S (itree F)] and morphisms
   [E ~> state S] define stateful itree morphisms
   [itree E ~> stateT S (itree F)]. *)

Section State.

  Variable (S : Type) (RS : S -> S -> Prop).

  #[local] Instance MonadT_StateT_RS : MonadT (stateT S) := MonadT_StateT _ _.

  Variant stateE : Type -> Type :=
  | Get : stateE S
  | Put : S -> stateE unit.

  Definition get {E F} `{stateE +? F -< E} : itree E S := trigger Get.
  Definition put {E F} `{stateE +? F -< E} : S -> itree E unit := fun s => trigger (Put s).

  Definition h_state {E} : stateE ~> stateT S (itree E) :=
    fun _ e s =>
      match e with
      | Get => Ret (s, s)
      | Put s' => Ret (s', tt)
      end.

  Definition run_state {E F} `{stateE +? E -< F} : itree F ~> stateT S (itree E) :=
    interp (over h_state).

End State.

Arguments get {S E F _}.
Arguments put {S E F _}.
Arguments run_state {S E F _} [_] _.

(* ----------------------------------------------------------------------- *)
(* SAZ: The code from here to <END> below doesn't belong to State.v  it should 
   go in Prop.v or something like that . *)
(* todo(gmm): this can be stronger if we allow for a `can_returnE` *)
Inductive can_return {E : Type -> Type} {t : Type} : itree E t -> t -> Prop :=
| can_return_Ret {x} : can_return (Ret x) x
| can_return_Tau {tr x} (_ : can_return tr x) : can_return (Tau tr) x
| can_return_Vis {u e k} {x: u} {res} (_ : can_return (k x) res)
  : can_return (Vis e k) res.

(** A propositional "interpreter"
    This can be useful for non-determinism.
 *)
Section interp_prop.
  Context {E F : Type -> Type}.

  Definition eff_hom_prop : Type :=
    forall t, E t -> itree F t -> Prop.

  CoInductive interp_prop (f : eff_hom_prop) (R : Type)
  : itree E R -> itree F R -> Prop :=
  | ipRet : forall x, interp_prop f R (Ret x) (Ret x)
  | ipVis : forall {T} {e : E T} {e' : itree F T}
              (k : _ -> itree E R) (k' : T -> itree F R),
      f _ e e' ->
      (forall x,
          can_return e' x ->
          interp_prop f R (k x) (k' x)) ->
      interp_prop f R (Vis e k) (ITree.bind e' k')
  | ipDelay : forall a b, interp_prop f R a b ->
                     interp_prop f R (Tau a) (Tau b).

End interp_prop.
Arguments eff_hom_prop _ _ : clear implicits.
(* <END> -------------------------------------------------------------------- *)


(** An extensional stateful handler *)
Section eff_hom_e.
  Context {E F : Type -> Type}.

  (* note(gmm): you should be able to add events here
   * using a monad transformer. In that case, the type
   * of `eval` is:
   *
   *   forall t, E t -> m (itree F) (t * eff_hom_e)
   *
   * but you have the usual conditions on strictly positive uses
   *)
  CoInductive eff_hom_e : Type :=
  { eval : forall t, E t -> itree F (eff_hom_e * t) }.

  Definition interp_e (h : eff_hom_e) : itree E ~> itree F := fun R t =>
    ITree.iter (fun '(s, t) =>
      match observe t with
      | RetF r => Ret (inr r)
      | TauF t => Ret (inl (s, t))
      | VisF e k => ITree.map (fun '(s, x) => inl (s, k x)) (h.(eval) _ e)
      end) (h, t).

End eff_hom_e.
