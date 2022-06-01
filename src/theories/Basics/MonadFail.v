(** * Iterative laws for failure monad *)

(* begin hide *)
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.HeterogeneousRelations
     Core.ITreeDefinition
     Core.KTree
     Core.KTreeFacts
     Eq.Eq
     Eq.UpToTaus
     Eq.Paco2
     Indexed.Sum.

From ExtLib Require Import
     Structures.Monad
     Structures.MonadTrans.

From ITree.EqmR Require Import
     Monads.ErrorT EqmRMonad EqmRMonadT.

Import ITreeNotations.
Import ITree.Basics.Basics.Monads.
Local Open Scope itree_scope.

Import Monads.
(* end hide *)

(* Failure handlers [E ~> stateT S (itree F)] and morphisms
   [E ~> state S] define stateful itree morphisms
   [itree E ~> stateT S (itree F)]. *)

#[global]
 Instance errorT_iter {m} {exn} {Mm : Monad m} {MIm : MonadIter m}
  : MonadIter (errorT exn m) :=
  fun A I body i =>
    Basics.iter (M := m) (I := I) (R := exn + A)
        (fun i => bind (m := m)
                       (body i)
                       (fun x => ret ( match x with
                          | inl e => (inr (inl e))
                          | inr (inl j) => (inl j)
                          | inr (inr a) => (inr (inr a)) end))) i.

Global Hint Mode errorT_iter ! ! ! ! : typeclasses_instances.

Ltac sum_rel_conv :=
  eapply eutt_Proper_R; [ rewrite sum_rel_eq; reflexivity | reflexivity | reflexivity | ..].

Section ErrorTIterative.

  Variable exn: Type.
  Variable M : Type -> Type.

  Context `{IM : WF_IterativeMonad M}.

  Ltac pacify :=
    eapply Proper_eqmR; [ apply HeterogeneousRelations.sum_rel_eq | ].

  Instance IterUnfold_errorT : IterUnfold (Kleisli (errorT exn M)) sum.
  Proof.
    repeat intro. unfold_ktree.
    destruct IM. pacify.
    etransitivity. eapply Proper_eqmR_mono; cycle 1. unfold iter, Iter_Kleisli.
    pose proof @iter_unfold. specialize (H _ (Kleisli M) _ _ _ _ _ _).
    eapply H; eauto. typeclasses eauto. eapply subrelationH_Reflexive.
    setoid_rewrite bind_bind.
    eapply Proper_bind; try reflexivity.
    intros; subst. rewrite bind_ret_l. unfold case_, Case_Kleisli, Function.case_sum.
    destruct a2; try reflexivity.
    destruct s; try reflexivity.
  Qed.

  Definition sum_comm_rel {A B C} : relationH (A + (B + C)) (B + (A + C)) :=
    (fun x y => match x, y with
            | inl a, inr (inl a') => a = a'
            | inr (inl b), inl b' => b = b'
            | inr (inr c), inr (inr c') => c = c'
            | _, _ => False
            end).

  Instance IterNatural_errorT : IterNatural (Kleisli (errorT exn M)) sum.
  Proof.
    repeat intro. unfold_ktree. pacify.
    destruct IM.
    etransitivity.
    { eapply Proper_eqmR_mono; cycle 1.
      { unfold iter, Iter_Kleisli.
        match goal with
        | |- context[bind _ ?k] => remember k
        end.
        unfold errorT in *.
        unfold Kleisli in f.

        eapply Proper_bind with (ma2 := (Basics.iter
                                    (fun a0 : a =>
                                    bind (f a0)
                                      (fun x : exn + (a + b) => ret
                                        match x with
                                        | inl e => (inr (inl e))
                                        | inr (inl a1) => (inl a1)
                                        | inr (inr b0) => (inr (inr b0))
                                        end)) a0)) (RR := eq) (k1 := m)
                                (k2 := fun a2 => match a2 with | inl e => ret (inl e) | inr a1 => g a1 end);
          intros; subst; reflexivity. }
      eapply subrelationH_Reflexive. }
    etransitivity.
    { pose proof @iterative_natural. specialize (H _ (Kleisli M) _ _ _ _ _ _ _ _ _).
      repeat red in H. unfold cat, Cat_Kleisli in H.
      unfold iter, Iter_Kleisli, Kleisli in H.
      unfold errorT in *.
      unfold Kleisli in f.
      specialize (H _ (exn + b)%type (exn + c)%type (fun a => bind (f a) (fun x => ret match x with
                                                        | inl e => (inr (inl e))
                                                        | inr (inl a) => (inl a)
                                                        | inr (inr b) => (inr (inr b))
                                                                                  end)) ((fun x : exn + b => match x with
                                 | inl e => ret (inl e)
                                 | inr a => g a
                                                                                                          end)) a0).
      eapply H. }
    { (* IY: Why can't we directly apply [Proper_iter] here? *)
      pose proof @Proper_iterH as Piter.
      specialize (Piter M _ _ _). repeat red in Piter.
      unfold iter, Iter_Kleisli in Piter.
      eapply Piter.

      repeat intro.
      setoid_rewrite bind_bind.
      eapply Proper_bind; [ pacify; subst; rewrite H; reflexivity | intros; subst ].
      { rewrite bind_ret_l.
        unfold bimap, Bimap_Coproduct, case_, Case_Kleisli, Function.case_sum.
        destruct a3; [ | destruct s]; pacify; eapply sum_rel_eq in H0; subst.
        - unfold cat. setoid_rewrite bind_ret_l. unfold inr_, Inr_Kleisli. reflexivity.
        - unfold cat. setoid_rewrite bind_ret_l. unfold inl_, Inl_Kleisli.
          unfold pure. unfold id. symmetry. rewrite bind_ret_l. reflexivity.
        - unfold cat. symmetry. setoid_rewrite bind_bind.
          eapply Proper_bind; [ reflexivity | ..]; intros; subst.
          + destruct a3; rewrite bind_ret_l; reflexivity. }
    auto.
    }
  Qed.


  Instance IterDinatural_errorT: IterDinatural (Kleisli (errorT exn M)) sum.
  Proof.
    intros A B C f g a.
    unfold_ktree; pacify.

    { pose proof @iter_dinatural as Hdin .
      specialize (Hdin _ (Kleisli M) _ _ _ sum _ _ _ _).
      repeat red in Hdin.
      unfold cat, case_, Cat_Kleisli, Case_Kleisli, Function.case_sum, inr_, Inr_Kleisli, pure in Hdin.
      unfold Kleisli, errorT in f, g, Hdin.
      specialize (Hdin A B (exn + C)%type).
      specialize (Hdin (fun x => bind (f x) (fun y => ret match y with
                                                | inl e => (inr (inl e))
                                                | inr (inl b) => (inl b)
                                                | inr (inr c) => (inr (inr c))
                                                end))).
      specialize (Hdin (fun x => bind (g x) (fun y => ret match y with
                                                | inl e => (inr (inl e))
                                                | inr (inl b) => (inl b)
                                                | inr (inr c) => (inr (inr c))
                                                end)) a).
      match goal with
      | [H : eqmR eq ?lhs _ |- _] => remember lhs as m
      end.
      transitivity m; subst.

      { (* IY: Why can't we directly apply [Proper_iter] here? *)
        pose proof @Proper_iterH as Piter.
        specialize (Piter M _ _ _). repeat red in Piter.
        unfold iter, Iter_Kleisli in Piter.
        eapply Piter.

        repeat intro. setoid_rewrite bind_bind.
        eapply Proper_bind; [ pacify; subst; rewrite H; reflexivity | ..]; intros; subst; try pacify.
        { symmetry. setoid_rewrite bind_ret_l.
          destruct a3 as [a3 | [a3 | a3]];
          destruct a0 as [a0 | [a0 | a0]]; inv H0; try inv H2.
          - symmetry. rewrite bind_ret_l. reflexivity.
          - reflexivity.
          - symmetry. rewrite bind_ret_l. reflexivity. } eauto. }

      etransitivity; [ eapply Hdin | ].
      rewrite bind_bind.
      eapply Proper_bind; [ reflexivity |..]; intros; subst.
      { rewrite bind_ret_l.
        destruct a2 as [a2 | [a2 | a2]].
        - unfold id_, Id_Kleisli; reflexivity.
        - (* IY: Why can't we directly apply [Proper_iter] here? *)
          pose proof @Proper_iterH as Piter.
          specialize (Piter M _ _ _). repeat red in Piter.
          unfold iter, Iter_Kleisli in Piter.
          eapply Piter; eauto.

          repeat intro; subst; pacify. setoid_rewrite bind_bind.
          eapply Proper_bind; [ |..]; intros; subst. reflexivity.
          {  setoid_rewrite bind_ret_l.
             destruct a3 as [a3 | [a3 | a3]]; try (symmetry; rewrite bind_ret_l); eauto. subst.
             rewrite bind_ret_l. apply eqmR_ret. typeclasses eauto. reflexivity.
             subst.  reflexivity. subst.
             rewrite bind_ret_l. apply eqmR_ret. typeclasses eauto. reflexivity.
          } auto.
        - unfold id_, Id_Kleisli; reflexivity. }
    }
  Qed.


  Instance IterCodiagonal_errorT : IterCodiagonal (Kleisli (errorT exn M)) sum.
  Proof.
    intros A B f a.
    unfold_ktree; pacify.

    pose proof @iter_codiagonal as Hcod.
    specialize (Hcod _ (Kleisli M) _ _ _ sum _ _ _ _).
    repeat red in Hcod.
    unfold cat, case_, Cat_Kleisli, Case_Kleisli, Function.case_sum, inr_, Inr_Kleisli, pure in Hcod.
    unfold Kleisli, errorT in f, Hcod.
    specialize (Hcod A (exn + B)%type).
    specialize (Hcod (fun x => bind (f x) (fun y => ret match y with
                                              | inl e => inr (inr (inl e))
                                              | inr (inl a) => (inl a)
                                              | inr (inr (inl a)) => (inr (inl a))
                                              | inr (inr (inr b)) => (inr (inr (inr b)))
                                              end)) a).
    match goal with
    | [H : eqmR eq ?lhs _ |- _] => remember lhs as m
    end.
    transitivity m; subst.

    { (* IY: Why can't we directly apply [Proper_iter] here? *)
      pose proof @Proper_iterH as Piter.
      specialize (Piter M _ _ _). repeat red in Piter.
      unfold iter, Iter_Kleisli in Piter.
      eapply Piter; eauto.

      repeat intro; subst. pacify.
      symmetry. rewrite <- bind_ret_r.
      eapply Proper_bind.
      { eapply Piter; eauto.
        repeat intro. subst.
        eapply Proper_bind; [ | ..]; intros; subst. rewrite H0; reflexivity. subst.
        eapply eqmR_ret; [ typeclasses eauto | ..].
        Unshelve. 3 : exact sum_comm_rel.
        destruct a4 as [a4 | [a4 | [a4 | a4]]]; repeat econstructor; eauto. auto. }
      { repeat intro.
        destruct a0 as [a0 | [a0 | a0]];
          destruct a3 as [a3 | [a3 | a3]]; inv H; eauto. inv H0; eauto. inv H0; eauto. reflexivity.
        inv H0; eauto. inv H0; eauto. reflexivity.
        inv H0; eauto. inv H0; eauto.
        inv H0; eauto. inv H0; eauto.
        inv H0; eauto. reflexivity.
    } auto. }
    etransitivity; [ eapply Hcod | ].

    pose proof @Proper_iterH as Piter.
    specialize (Piter M _ _ _). repeat red in Piter.
    unfold iter, Iter_Kleisli in Piter.
    eapply Piter; eauto.
    repeat intro; subst; pacify.
    setoid_rewrite bind_bind.
    eapply Proper_bind; [ | ..]; intros; subst; eauto; try reflexivity.
    { rewrite bind_ret_l.
      destruct a0 as [a0 | [a0 | [a0 | a0]]]; try (symmetry; rewrite bind_ret_l); try reflexivity. subst.
      rewrite bind_ret_l; reflexivity. subst. cbn.
      rewrite bind_ret_l; reflexivity. subst.
      rewrite bind_ret_l; reflexivity. subst.
      rewrite bind_ret_l; reflexivity.
    } eauto.
  Qed.

  Instance Proper_iter_errorT :
    forall a b : Type, Proper (eq2 ==> eq2 (a := a) (b := b)) (iter (C := Kleisli (errorT exn M))).
  Proof.
    repeat intro; cbn. pacify.

    pose proof @Proper_iterH as Piter.
    specialize (Piter M _ _ _). repeat red in Piter.
    unfold iter, Iter_Kleisli in Piter.
    eapply Piter; eauto.

    repeat intro;subst;pacify.
    eapply Proper_bind; eauto; intros. subst. eapply H. 2 : auto.
    inv H1. reflexivity. reflexivity.
  Qed.

  Global Instance Iterative_errorT : Iterative (Kleisli (errorT exn M)) sum.
  Proof.
    split; try typeclasses eauto.
  Qed.


End ErrorTIterative.

Section ErrorIter.

  (* N.B. Keeping this instance local keeps the [Iter] instance resolution not
    loop between [Kleisli_MonadIter] and [Iter_Kleisli] in the global context *)
  #[local] Instance Kleisli_MonadIter (m : Type -> Type) `{Iter _ (Kleisli m) sum} : MonadIter m :=
  fun a b => iter.

  #[global] Instance IterativeMonadT_errorT {exn}:
    IterativeMonadT (errorT exn) := {|
    T_MonadIter := fun (m : Type -> Type) (Mm : Monad m) (MIm : MonadIter m) =>
                    @Kleisli_MonadIter (errorT exn m) (@Iter_Kleisli (errorT exn m) (@errorT_iter m exn Mm MIm)) |}.

  #[global] Program Instance WF_IterativeMonadT_errorT {exn}: WF_IterativeMonadT (errorT exn) _ _.
  Next Obligation.
    repeat intro. subst. destruct H.
    repeat red in M_ProperIter.
    eapply M_ProperIter; eauto. repeat red. intros; subst; eauto.
    eapply Proper_bind; eauto; intros; subst.
    inv H2; apply eqmR_ret; eauto; try typeclasses eauto.
    inv H3; eauto.
  Defined.

End ErrorIter.
