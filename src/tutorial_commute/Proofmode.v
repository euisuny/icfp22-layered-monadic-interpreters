From ITree Require Import
     ITree
     Interp.HFunctor
     Interp.InterpFacts
     EqmR.EqmRMonad
     Basics.HeterogeneousRelations
    Basics.CategoryKleisli.

From Coq Require Import Morphisms. 
Require Import ExtLib.Structures.Monad.

Import RelNotations.
Import CatNotations.
Local Open Scope cat_scope.
Local Open Scope relationH_scope.

(* Custom tactic for properness instance. Naive application of rewrite goal *)
(* LATER: Is there a way to [Existing Instance] out of this ? *)
Ltac iproper_body TR h x :=
  let HProper := fresh "HProper" in
  let X := fresh "X" in
  remember x as X; cbn in X;
  match type of h with
  | forall T : Type, ?E T -> ?M T =>
      match type of X with
      | ?T (itree E) ?A =>
          pose proof (@interp_proper T M _ _ _ _ _ h _ A eq) as HProper
      | itree ?E ?A =>
          pose proof (@interp_proper (fun x => x) M _ _ _ _ E h _ A eq)
      | _ ?A =>
          pose proof (@interp_proper TR M _ _ _ _ _ h _ A eq) as HProper
      end
  end; subst.

Ltac iproper_rec x :=
  match x with
  | interp (T := ?TR) ?h ?x_ =>
      try iproper_rec x_;
      iproper_body TR h x
  end.

Ltac iproper :=
  try match goal with
  | |- interp (T :=  ?TR) ?h ?x ≈{_} _ =>
      try iproper_rec x;
      iproper_body TR h x
  | |- context [interp (T := ?TR) ?h ?x] =>
      try iproper_rec x;
      iproper_body TR h x
  end;
  try match goal with
    | |- _ ≈{_} interp (T :=  ?TR) ?h ?x =>
      try iproper_rec x;
      iproper_body TR h x
  end.

Ltac itrigger :=
  let HTrigger := fresh "HTrigger" in
  match goal with
  | |- context[interp (T := ?T) (M := ?M) (I := ?I) (Subevent.over (A := ?A) (S := ?S) ?h) (T0 := ?R) (trigger (E := ?F) ?e)] =>
      pose proof (@interp_trigger T M _ _ _ _ _ I R (Subevent.over h)) as HTrigger
  end.

Ltac iignoretrigger :=
  let HTrigger := fresh "HTrigger" in
  match goal with
  | |- context[interp (T := ?T) (M := ?M) (I := ?I) (over (A := ?A) (S := ?S) ?h) (T0 := ?R) (trigger ?e)] =>
    pose proof (@interp_over_ignore_trigger T M _ _ _ _ _) as HTrigger
  end.

Ltac f_equiv :=
  match goal with
  | |- (?R _ _) (?f _) (?f' _) =>
      eapply (_ : Proper (eqmR eq ==> eqmR eq ==> iff) (R _ _))
  end.

Ltac clear_ProperH :=
  repeat match goal with
  | [HP : ProperH (eqmR eq ~~> eqmR eq) _ _ |- _] => clear HP
  end.

Ltac irewrite H :=
  match type of H with
  | interp ?f _ ≋ _ =>
      iproper;
      match goal with
      | [HP : ProperH (eqmR eq ~~> eqmR eq) (interp ?f (T0 := _)) (interp ?f (T0 := _)) |- _] =>
          specialize (HP _ _ H);
          try setoid_rewrite HP at 1;
          try irewrite HP; clear HP
      end
  | ?x ≋ ?y =>
      repeat match goal with
      | [ |- interp ?h ?x ≈{ ?RR } _ ] =>
          iproper;
          match goal with
          | [ HProper :
              ProperH (eqmR eq ~~> eqmR eq)
                      (interp _ (T0 := _)) (interp _ (T0 := _)) |- _] =>
              repeat red in HProper;
              specialize (HProper _ _ H);
              rewrite HProper;
              clear H HProper
          end
      | |- interp ?h ?x ≈{ ?RR } interp ?h ?y =>
        let HProper := fresh "HProper" in
        pose proof (@interp_proper _ _ _ _ _ _ _ h _ _ RR x y) as HProper;
        eapply HProper; clear HProper
      end; eauto
  end; clear_ProperH.

Ltac iret :=
  match goal with
  | |- context[interp (T := ?TR) ?h (ret ?r)] =>
      match type of h with
      | forall T : Type, ?E T -> _ T =>
          let Hret := fresh "Hret" in
          pose proof (interp_ret (T := TR) (E := E) h r) as Hret;
          try (irewrite Hret)
      end
  | |- context[interp (T := ?TR) ?h (Ret ?r)] =>
      match type of h with
      | forall T : Type, ?E T -> _ T =>
          let Hret := fresh "Hret" in
          pose proof (interp_ret (T := TR) (E := E) h r) as Hret;
          try (irewrite Hret)
      end
  end.

Ltac ibind_body TR h t k :=
  match type of h with
  | forall T : Type, ?E T -> _ T =>
      let Hbind := fresh "Hbind" in
      pose proof (interp_bind (T := TR) (E := E) h k t) as Hbind;
      try (irewrite Hbind)
  end.

Ltac ibind_rec TR h x :=
  match x with
  | interp (T := ?TR) ?h ?x_ =>
      ibind_rec TR h x_
  | bind ?t ?k =>
      ibind_body TR h t k
  | ITree.bind ?t ?k =>
      ibind_body TR h t k
  end.

Ltac ibind :=
  match goal with
  | |- eqmR _ (interp (T := ?TR) ?h ?x) _ =>
      ibind_rec TR h x
  | |- context[interp (T := ?TR) ?h (ITree.bind ?t ?k)] =>
      ibind_body TR h t k
  | |- context[interp (T := ?TR) ?h (bind ?t ?k)] =>
      ibind_body TR h t k
  end.

Ltac bind_cong :=
  eapply eqmR_bind_ProperH_simple; [ typeclasses eauto | ..].

Ltac iiter :=
  match goal with
  | |- context[interp (T := ?TR) ?h (Basics.iter ?f ?i)] =>
      match type of h with
      | forall T : Type, ?E T -> _ T =>
          let Hiter := fresh "Hiter" in
          pose proof (interp_iter (T := TR) (E := E) _ _ h f) as Hiter;
          try (irewrite Hiter)
      end
  | |- context[interp (T := ?TR) ?h (iter ?f ?i)] =>
      unfold iter, Iter_Kleisli;
      match type of h with
      | forall T : Type, ?E T -> _ T =>
          let Hiter := fresh "Hiter" in
          pose proof (interp_iter (T := TR) (E := E) _ _ h f) as Hiter;
          try (irewrite Hiter)
      end
  end.
