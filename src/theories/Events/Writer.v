(** * Writer *)

(** Output events. *)

(* begin hide *)
Set Implicit Arguments.
Set Contextual Implicit.

From Coq Require Import
     List.
Import ListNotations.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad
     Structures.Monoid.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Core.ITreeDefinition
     Indexed.Sum
     Core.Subevent
     Interp.Interp
     Interp.Handler
     Events.State.

Import Basics.Basics.Monads.
(* end hide *)

(** Event to output values of type [W]. *)
Variant writerE (W : Type) : Type -> Type :=
| Tell : W -> writerE W unit.

(** Output action. *)
Definition tell {W E F} `{writerE W +? F -< E} : W -> itree E unit :=
  fun w => trigger (Tell w).

(** One interpretation is to accumulate outputs in a list. *)

(** Note that this handler appends new outputs to the front of the list. *)
Definition handle_writer_list {W E}
  : writerE W ~> stateT (list W) (itree E)
  := fun _ e s =>
       match e with
       | Tell w => Ret (w :: s, tt)
       end.

Definition run_writer_list_state {W E F} `{writerE W +? E -< F}
  : itree F ~> stateT (list W) (itree E)
  := interp_state (over handle_writer_list).

Arguments run_writer_list_state {W E F _} [T].

(** Returns the outputs in order: the first output at the head, the last
    output and the end of the list. *)
Definition run_writer_list {W E F} `{writerE W +? E -< F}
  : itree F ~> writerT (list W) (itree E)
  := fun _ t =>
       ITree.map (fun wsx => (rev' (fst wsx), snd wsx))
                 (run_writer_list_state t []).

Arguments run_writer_list {W E F _} [T].

(** When [W] is a monoid, we can also use that to append the outputs together. *)

Definition handle_writer {W E} (Monoid_W : Monoid W)
  : writerE W ~> stateT W (itree E)
  := fun _ e s =>
       match e with
       | Tell w => Ret (monoid_plus Monoid_W s w, tt)
       end.

Definition run_writer {W E F} (Monoid_W : Monoid W) `{writerE W +? E -< F}
  : itree F ~> writerT W (itree E)
  := fun _ t =>
       interp_state (over (handle_writer Monoid_W)) t
                    (monoid_unit Monoid_W).

Arguments run_writer {W E _} Monoid_W {_} [T].
