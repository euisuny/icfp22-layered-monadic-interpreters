(** * Iterative laws for state monad *)

(* begin hide *)
From Coq Require Import
     Setoid
     Morphisms.

From ExtLib Require Import
     Structures.Monad.

From ITree Require Import
     Basics.Basics
     Basics.Category
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts
     Basics.HeterogeneousRelations
    Core.ITreeDefinition
    Eq.Eq Eq.UpToTaus.

From Paco Require Import paco.

Import ITree.Basics.Basics.Monads.
From ITree.EqmR Require Import EqmRMonad EqmRMonadT Monads.StateT.
Import CatNotations.
Import MonadNotation.
Local Open Scope cat_scope.
Local Open Scope cat.
Local Open Scope monad_scope.
(* end hide *)

Section State.
  Variable M : Type -> Type.
  Variable S : Type.
  Context {inh_S : inhabited S}.

  Context {EQMR : EqmR M}.
  Context {HM: Monad M}.
  Context {HEQP: EQM M EQMR}.

  Context {IM: MonadIter M}.
  Context {CM: Iterative (Kleisli M) sum}.

  Definition iso {a b:Type} (sab : S * (a + b)) : (S * a) + (S * b) :=
    match sab with
    | (s, inl x) => inl (s, x)
    | (s, inr y) => inr (s, y)
    end.

  Definition iso_inv {a b:Type} (sab : (S * a) + (S * b)) : S * (a + b) :=
    match sab with
    | inl (s, a) => (s, inl a)
    | inr (s, b) => (s, inr b)
    end.

  Definition internalize {a b:Type} (f : Kleisli (stateT S M) a b) : Kleisli M (S * a) (S * b) :=
    fun (sa : S * a) => f (snd sa) (fst sa).

  Lemma internalize_eq {a b:Type} (f g : Kleisli (stateT S M) a b) :
    eq2 f g <-> eq2 (internalize f) (internalize g).
  Proof.
    split.
    - intros.
      repeat red. intros. subst. destruct a0.
      unfold internalize. cbn.  repeat red in H. specialize (H a0 s _ eq_refl).
      eapply Proper_eqmR.
      symmetry. apply HeterogeneousRelations.prod_rel_eq. auto.
    - intros.
      repeat red. intros.
      unfold internalize in H. repeat red in H. subst.
      repeat intro. subst.
      specialize (H (s', a0)). cbn in *.
      eapply Proper_eqmR.
      apply HeterogeneousRelations.prod_rel_eq. auto. subst; auto.
  Qed.

  Lemma internalize_cat {a b c} (f : Kleisli (stateT S M) a b) (g : Kleisli (stateT S M) b c) :
    (internalize (f >>> g)) ⩯ ((internalize f) >>> (internalize g)).
  Proof.
    repeat red. repeat intro. subst.
    destruct a0.
    cbn.
    unfold internalize.
    unfold cat, Cat_Kleisli.
    cbn. reflexivity.
  Qed.

  Lemma internalize_pure {a b c} (f : Kleisli (stateT S M) a b) (g : S * b -> S * c) :
    internalize f >>> pure g   ⩯   (internalize (f >>> (fun b s => ret (g (s,b))))).
  Proof.
    repeat red. repeat intro; subst.
    destruct a0.
    unfold internalize, cat, Cat_Kleisli. cbn.
    apply Proper_bind with (RR := eq); [ reflexivity | ].
    intros; subst. unfold pure. destruct a2; reflexivity.
  Qed.

  Global Instance Iter_stateTM: Iter (Kleisli (stateT S M)) sum.
  Proof.
    exact
      (fun (a b : Type) (f : a -> S -> M (S * (a + b))) (x:a) (s:S) =>
        iter ((internalize f) >>> (pure iso)) (s, x)).
  Defined.

  Ltac pacify :=
    cbn; intros; subst; eapply Proper_eqmR; [ apply HeterogeneousRelations.prod_rel_eq | ].

  Global Instance Proper_Iter_stateTM : forall a b, @Proper (Kleisli (stateT S M) a (a + b) -> (Kleisli (stateT S M) a b)) (eq2 ==> eq2) iter.
  Proof.
    destruct CM.
    repeat red.
    intros a b x y H a0 s ? ->. pacify.
    apply iterative_proper_iter; auto.
    repeat red. intros; subst. eapply Proper_bind.
    apply internalize_eq; auto.
    intros; subst; reflexivity.
 Qed.

  Global Instance IterUnfold_stateTM : IterUnfold (Kleisli (stateT S M)) sum.
  Proof.
  destruct CM.
  unfold IterUnfold.
  intros a b f.
  repeat red.
  intros a0 s ? ->.
  unfold cat, Cat_Kleisli.
  unfold iter, Iter_stateTM. 
  rewrite iterative_unfold.  (* SAZ: why isn't iter_unfold exposed here? *)
  unfold cat, Cat_Kleisli.
  simpl. pacify.
  rewrite bind_bind.
  apply Proper_bind with (RR := eq); [ reflexivity | ].
  intros; subst; auto. unfold pure. rewrite bind_ret_l.
  destruct a2, s0;cbn in *; reflexivity.
  Qed.

  Global Instance IterNatural_stateTM : IterNatural (Kleisli (stateT S M)) sum.
  Proof.
    destruct CM.
    unfold IterNatural.
    intros a b c f g.
    repeat red.
    intros a0 s ? ->.
    setoid_rewrite iterative_natural; auto.
    pacify.
    apply iterative_proper_iter.
    repeat red.
    destruct a1.
    unfold cat, Cat_Kleisli.
    cbn. intros; subst. do 2 rewrite bind_bind. cbn.

    apply Proper_bind with (RR := eq) ; [ reflexivity | ..]; intros; subst.
    - destruct a3. destruct s1. unfold pure. rewrite bind_ret_l.
      cbn. unfold cat, Cat_Kleisli. cbn. rewrite bind_bind. do 2 rewrite bind_ret_l.
      cbn. unfold id_, Id_Kleisli. unfold pure. rewrite bind_ret_l. reflexivity.
      unfold pure. rewrite bind_ret_l.
      cbn. unfold cat, Cat_Kleisli. cbn. rewrite bind_bind.
      apply Proper_bind with (RR := eq); [ reflexivity | ..]; intros; subst; rewrite bind_ret_l; cbn.
      + destruct a3; reflexivity.
  Qed.

  Lemma internalize_pure_iso {a b c} (f : Kleisli (stateT S M) a (b + c)) :
    ((internalize f) >>> pure iso) ⩯ (fun sa => (bind (f (snd sa) (fst sa))) (fun sbc => ret (iso sbc))).
  Proof.
    repeat intro; subst; reflexivity.
  Qed.

  Lemma eq2_to_eq1 : forall a b (f g : Kleisli (stateT S M) a b) (x:a) (s:S),
      eq2 f g ->
      (f x s) ≈{eq} (g x s).
  Proof.
    intros a b f g x s H. repeat red in H.
    specialize (H x s _ eq_refl).
    eapply Proper_eqmR; [ | ..]. symmetry.
    apply HeterogeneousRelations.prod_rel_eq. auto.
  Qed.

  Lemma iter_dinatural_helper:
    forall (a b c : Type) (f : Kleisli (stateT S M) a (b + c)) (g : Kleisli (stateT S M) b (a + c)),
      internalize (f >>> case_ g inr_) >>> pure iso ⩯ internalize f >>> pure iso >>> case_ (internalize g >>> pure iso) inr_.
  Proof.
    destruct CM.
    intros a b c f g.
    repeat red. intros. subst.
    unfold cat, Cat_Kleisli, internalize.
    cbn.
    do 2 rewrite bind_bind.
    apply Proper_bind with (RR := eq); [reflexivity | ..].
    - intros; subst; destruct a0, a2, s1.
      + unfold pure. rewrite bind_ret_l.
        unfold case_, Case_Kleisli, Function.case_sum.
        reflexivity.
      + unfold pure. rewrite bind_ret_l.
        unfold case_, Case_Kleisli, Function.case_sum.
          cbn. rewrite bind_ret_l. reflexivity.
  Qed.

  Global Instance IterDinatural_stateTM : IterDinatural (Kleisli (stateT S M)) sum.
  Proof.
    destruct CM.
    unfold IterDinatural.
    repeat red.
    intros a b c f g a0 a1. intros; subst.
    unfold iter, Iter_stateTM.
    eapply transitivity. cbn. intros; subst.
    eapply Proper_eqmR; [ apply HeterogeneousRelations.prod_rel_eq | ].
    eapply iterative_proper_iter; auto.
    apply iter_dinatural_helper.
    repeat intro; subst.
    eapply Proper_eqmR; [ apply HeterogeneousRelations.prod_rel_eq | ].
    rewrite iterative_dinatural; auto.
    cbn.
    unfold cat, Cat_Kleisli.
    rewrite bind_bind.
    unfold internalize. cbn in H; subst.
    apply Proper_bind with (RR := eq) ; [ cbn ; reflexivity | .. ]; intros; subst.
    - repeat red.
      destruct a2 as [s [x | y]].
      + unfold pure. rewrite bind_ret_l.
        cbn.
        eapply iterative_proper_iter; auto.
        repeat red. intros. destruct a1.
        cbn. rewrite bind_bind. intros; subst. rewrite bind_bind.
        apply Proper_bind with (RR := eq) ; [ reflexivity | ..]; intros; subst.
        * destruct a2 as [s'' [x' | y]].
          ** cbn. rewrite bind_ret_l. unfold case_, Case_Kleisli, Function.case_sum.
             reflexivity.
          ** cbn. rewrite bind_ret_l. unfold case_, Case_Kleisli, Function.case_sum.
             rewrite bind_ret_l. reflexivity.
      + unfold pure. rewrite bind_ret_l.
        cbn. reflexivity.
    Qed.

  Instance Proper_cat_Kleisli_eqmR {a b c}
    : @Proper (Kleisli M a b -> Kleisli M b c -> _)
              (eq2 ==> eq2 ==> eq2) cat.
  Proof.
    repeat intro.
    unfold cat, Cat_Kleisli. subst. eapply Proper_bind; auto.
    repeat red in H. eauto.
    all : intros; subst; eauto.
  Qed.

  Global Instance IterCodiagonal_stateTM : IterCodiagonal (Kleisli (stateT S M)) sum.
  Proof.
    destruct CM.
    unfold IterCodiagonal.
    intros a b f.
    unfold iter, Iter_stateTM.
    repeat red.
    intros. subst.
    eapply transitivity.
    repeat intro; subst; auto.
    eapply Proper_eqmR; [ apply HeterogeneousRelations.prod_rel_eq | ].
    eapply iterative_proper_iter.
    eapply Proper_cat_Kleisli_eqmR.

    assert (internalize (fun (x:a) (s:S) => iter (internalize f >>> pure iso) (s, x))
                       ⩯
                       iter (internalize f >>> pure iso)).
    { repeat red. intros; subst.
      destruct a1.
      unfold internalize.
      cbn.  reflexivity.
    } cbn in H; subst.
   apply H0. repeat intro; subst ;reflexivity.
   eapply transitivity.

   pacify.
   eapply iterative_proper_iter.
   apply iterative_natural. auto.
   pacify.
   rewrite iterative_codiagonal. cbn in H; subst.
   eapply iterative_proper_iter.
   unfold pure at 3. unfold cat at 4. unfold Cat_Kleisli. cbn.
   repeat intro. subst.
   cbn. rewrite bind_bind.
   unfold cat, Cat_Kleisli. cbn. rewrite bind_bind. rewrite bind_bind.
   unfold internalize, pure. cbn.
   cbn.
   eapply Proper_bind; [ reflexivity | ..].
   { intros; subst. rewrite bind_ret_l.
     destruct a3 as [s'' [x | [y | z]]].
     - cbn. unfold id_, Id_Kleisli, pure. rewrite bind_ret_l.
        unfold cat, Cat_Kleisli. rewrite bind_bind. rewrite bind_ret_l.
        cbn.  unfold inl_, Inl_Kleisli, pure. rewrite bind_ret_l.
        reflexivity.
     - cbn. unfold id_, Id_Kleisli, pure. rewrite bind_ret_l.
        unfold cat, Cat_Kleisli. rewrite bind_bind. rewrite bind_ret_l.
        cbn.  unfold inl_, Inl_Kleisli, pure. unfold inr_, Inr_Kleisli, pure.
        rewrite bind_ret_l. reflexivity.
     - cbn. unfold id_, Id_Kleisli, pure. rewrite bind_ret_l.
        unfold cat, Cat_Kleisli. rewrite bind_bind. rewrite bind_ret_l.
        cbn.  unfold inl_, Inl_Kleisli, pure. unfold inr_, Inr_Kleisli, pure.
        rewrite bind_ret_l. reflexivity.
   }
Qed.

  Global Instance Iterative_stateTM : Iterative (Kleisli (stateT S M)) sum.
  Proof.
  constructor;
  typeclasses eauto.
  Qed.

  Global Instance Iter_stateTM_eq : Iter (Kleisli (stateT S M)) sum := @Iter_Kleisli _ MonadIter_stateT0.

  Lemma Iter_stateTM_equivalent :
    forall a b t, @iter _ (Kleisli (stateT S M)) _ Iter_stateTM_eq a b  t ⩯ @iter _ _ _ Iter_stateTM a _  t.
  Proof.
    repeat intro. subst. unfold iter, Iter_stateTM, Iter_stateTM_eq, Iter_Kleisli, iter.
    unfold Basics.iter, MonadIter_stateT0. unfold Basics.iter.
    pose proof @iterative_proper_iter. repeat red in H.
    specialize (H0 _ (Kleisli M) _ _ _ sum _ _ _ _ _).
    repeat red in H0. unfold iter, Iter_Kleisli, Basics.iter in H. pacify. eapply H0.
    repeat intro. repeat red. unfold cat, Cat_Kleisli, internalize, pure.
    eapply Proper_bind; [ reflexivity | ..]; intros; subst; destruct a3; cbn;  destruct s0; reflexivity.
  Qed.

  Lemma Iter_stateTM_eqmR:
    forall a b t s (i:a), @iter _ (Kleisli (stateT S M)) _ Iter_stateTM_eq _ b  t i s ≈{eq} @iter _ _ _ Iter_stateTM a _  t i s.
  Proof.
    repeat intro. subst. unfold iter, Iter_stateTM, Iter_stateTM_eq, Iter_Kleisli, iter.
    unfold Basics.iter, MonadIter_stateT0. unfold Basics.iter.
    pose proof @iterative_proper_iter. repeat red in H.
    specialize (H _ (Kleisli M) _ _ _ sum _ _ _ _ _).
    repeat red in H. unfold iter, Iter_Kleisli, Basics.iter in H. eapply H.
    repeat intro. repeat red. unfold cat, Cat_Kleisli, internalize, pure.
    eapply Proper_bind; [ reflexivity | ..]; intros; subst; destruct a2; cbn;  destruct s1; reflexivity.
  Qed.

  Global Instance Iterative_stateTM_ : Iterative (Iter_C := Iter_stateTM_eq) (Kleisli (stateT S M)) sum.
  Proof.
    constructor; red; intros.
    - rewrite Iter_stateTM_equivalent.
      eapply IterUnfold_stateTM.
    - do 2 rewrite Iter_stateTM_equivalent.
      eapply IterNatural_stateTM.
    - repeat rewrite Iter_stateTM_equivalent.
      eapply IterDinatural_stateTM.
    - repeat rewrite Iter_stateTM_equivalent.
      eapply IterCodiagonal_stateTM.
    - red. intros. repeat rewrite Iter_stateTM_equivalent.
      eapply Proper_Iter_stateTM; auto.
  Qed.

End State.

Section StateIter.

  (* N.B. Keeping this instance local keeps the [Iter] instance resolution not
    loop between [Kleisli_MonadIter] and [Iter_Kleisli] in the global context *)
  #[local] Instance Kleisli_MonadIter (m : Type -> Type) `{Iter _ (Kleisli m) sum} : MonadIter m :=
    fun a b => iter.

  #[global] Instance stateT_IterativeMonadT {S} (inh_S : inhabited S):
    IterativeMonadT (stateT S) :=
    {| T_MonadT := MonadT_StateT S _;
      T_MonadIter := fun (m : Type -> Type) (Mm : Monad m) (MIm : MonadIter m) =>
                        @Kleisli_MonadIter (stateT S m) (@Iter_stateTM_eq m S Mm MIm);
    |}.

  #[global] Program Instance stateT_WF_IterativeMonadT {S} (inh_S : inhabited S):
    WF_IterativeMonadT (stateT S) _ _:=
    {| T_MonadTLaws := @MonadTransformer_StateT _ inh_S |}.
  Next Obligation.
    repeat intro. subst. destruct H.
    repeat red in M_ProperIter.
    eapply M_ProperIter; eauto. repeat red. intros; subst; eauto.
    destruct a0.
    eapply Proper_bind; eauto; intros; subst. cbn. cbn in H0; subst. eapply H0; eauto.
    Unshelve.
    5 : { exact (fun '(s1, a1) '(s2, a2) => RA a1 a2 /\ s1 = s2). }
    destruct a3; destruct H; eauto.
    destruct a3; destruct H; eauto.
    destruct H3; eauto. subst.
    eapply eqmR_ret; try typeclasses eauto.
    repeat inv H; repeat inv H4; repeat constructor; eauto. constructor; eauto.
  Defined.

End StateIter.
