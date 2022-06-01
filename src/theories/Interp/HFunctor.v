(** * Higher-order functors *)

(* This file defines higher-order functors and well-formedness properties for them,
   which are from Johann and Ghani's work on primitive nested types in Haskell
   (See https://arxiv.org/pdf/2101.04819.pdf).

   We use higher-order functor well-formedness properties for stating well-formedness
   properties over monad transformers, which are higher order functors (similarly
   to how monads form a functor).

   We provide higher-order functor instances for ID, State, and Error transformers
   and show that the higher-order functor well-formedness properties are closed under
   nesting these monad transformers. *)

(* begin hide *)
From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses.

From Paco Require Import paco.

From ITree Require Import
     Basics.Basics
     Basics.MonadState
     Basics.Category
     Basics.CategoryKleisli
     Basics.CategoryKleisliFacts
     Basics.HeterogeneousRelations
     Basics.Tacs
     Basics.MonadFail
     Core.ITreeDefinition
     Core.KTree
     Core.KTreeFacts
     Core.Subevent
     Eq.Eq
     Eq.UpToTaus
     Eq.Paco2
     Indexed.Sum
     Indexed.Function
     Interp.Interp.

From ITree.EqmR Require Import
     EqmRMonad EqmRMonadT
     Monads.ITree_weak
     Monads.StateT Monads.ErrorT.

From ExtLib Require Import
     Structures.Functor
     Structures.Monad.

Set Primitive Projections.

Import RelNotations.
Import ITreeNotations.
Import FunctorNotation.
Import MonadNotation.
Import CatNotations.
Local Open Scope relationH_scope.
Local Open Scope cat_scope.
Local Open Scope monad_scope.
(* end hide *)

(* Higher-order functors *)
Class HFunctor (f : (Type -> Type) -> Type -> Type) :=
{ ffmap : forall A B g, Functor g -> (A -> B) -> f g A -> f g B;
  hfmap : forall g h, (g ~> h) -> (f g ~> f h) }.

Arguments ffmap {_ _ _ _ _ _} _ _.
Arguments hfmap {_ _ _ _} F [_].

Definition pointwise_eqmR
    (g h : Type -> Type)
    {g_Monad : Monad g} {h_Monad : Monad h} {g_EqmR : EqmR g} {h_EqmR : EqmR h} : relation (g ~> h).
Proof.
  repeat intro.
  exact (forall (T : Type) (x y : g T), eqmR eq x y -> eqmR eq (X _ x) (X0 _ y)).
Defined.

Class HFmapProper f (f_Hfunctor : HFunctor f) `{f_WF_MonadTLaws : WF_IterativeMonadT f} : Type :=
  hfmap_proper_ :
    forall (g h : Type -> Type)
      {g_Monad : Monad g} {h_Monad : Monad h} {g_EqmR : EqmR g} {h_EqmR : EqmR h}
        {g_EQM : EQM g _} {h_EQM : EQM h _} X,
    Proper (pointwise_eqmR g h ==> eqmR (m := f g) eq ==> eqmR (m := f h) eq) (fun x => @hfmap f _ g h x X).

(* Standard well-formedness property for higher-order functors *)
Class HFunctorLaws (f : (Type -> Type) -> Type -> Type)
      {f_Hfunctor : HFunctor f}
      `{f_WF_MonadTLaws : WF_IterativeMonadT f} :=
  { hfmap_id :
      forall T (g : Type -> Type) `{g_EQM : EQM g} (t : f g T),
        hfmap (fun _ x => x) t ≈{eq} t;
    hfmap_nat :>
      forall (g h : Type -> Type)
        {g_Monad : Monad g} {h_Monad : Monad h} {g_EqmR : EqmR g} {h_EqmR : EqmR h}
        {g_EQM : EQM g _} {h_EQM : EQM h _}
        (F : forall T, g T -> h T) {F_Nat : MonadMorphism _ _ F},
        MonadMorphism _ _ (hfmap F);
    hfmap_proper :> HFmapProper f f_Hfunctor
  }.

(* Well-formedness properties of higher-order functors w.r.t. iterative monads *)
Class HFunctorLawsExtra (f : (Type -> Type) -> Type -> Type)
      {f_Hfunctor : HFunctor f}
      `{f_WF_MonadTLaws : WF_IterativeMonadT f} :=
  { hfmap_lift :
    forall (T : Type) (g h : Type -> Type)
           `{g_IM : WF_IterativeMonad g} `{h_IM : WF_IterativeMonad h}
           (F : g ~> h) {F_MNT : MonadMorphism _ _ F} (t : g T),
      hfmap (f := f) F (EqmRMonadT.lift t) ≈{eq} EqmRMonadT.lift (F _ t);
    hfmap_iter :
    forall (g h : Type -> Type)
           `{g_IM : WF_IterativeMonad g} `{h_IM : WF_IterativeMonad h}
           (F : forall T : Type, g T -> h T),
      @MonadMorphism g h _ _ _ _ F ->
      @IterMorphism g h _ F _ _ ->
      @IterMorphism (f g) (f h) _ (@hfmap _ f_Hfunctor g h F) _ _;
  }.

Class WF_HFunctor (T : (Type -> Type) -> Type -> Type) {T_HFunctor : HFunctor T}
      `{M_IterativeMonadT : WF_IterativeMonadT T}:= {
  T_HFunctorLaws :> HFunctorLaws T;
  T_HFunctorLawsExtra :> HFunctorLawsExtra T; }.

Import Monads.

Section HFunctorInstances.
  (* State transformer forms a higher-order functor and respects well-formedness
    laws. *)
  #[global] Instance stateT_HFunctor {S} : HFunctor (stateT S) :=
  {| ffmap := fun A B g _ f x s => fmap (fun '(s', a) => (s', f a)) (x s);
    hfmap := fun g h f _ x s => f _ (x s) |}.

  #[global] Existing Instance stateT_HFunctor | 0.

  Arguments EqmRMonadT.lift /.

  #[global] Instance stateT_HFunctorLaws {S} {inh_S : inhabited S}:
    @HFunctorLaws (stateT S) _ _ _
                  (stateT_WF_IterativeMonadT inh_S).
  Proof.
    constructor.
    - intros. cbn. intros; subst; eapply reflexivity.
    - intros; constructor; intros; cbn in *; cycle 1.
      { repeat intro. destruct F_Nat. intros; subst.
        eapply Proper_eqmR_cong. cbn. eapply morph_ret; eauto. eapply reflexivity.
        apply eqmR_ret; eauto. typeclasses eauto. }
      { repeat intro. subst.
        destruct F_Nat. intros; subst. eapply morph_bind; eauto. intros. destruct a, a'.
        inv H1. eapply H0; eauto; eauto.
        all : inv H2; cbn; eauto. }
      { repeat intro. subst. cbn. eapply morph_proper; eauto; try typeclasses eauto. }
      { constructor; try typeclasses eauto. }
      Unshelve.
      destruct F_Nat. auto.
    - repeat intro. cbn. eapply Proper_eqmR. setoid_rewrite prod_rel_eq.
      reflexivity.
      eapply H. cbn in H0.
      eapply Proper_eqmR_mono; eauto.
      repeat intro. repeat inv H2 ;eauto.
  Qed.

  Definition prod_sum_dist_rel {A B C} : relationH (A * B + A * C) (A * (B + C)) :=
    (fun x '(s, y) => match x with
                    | inl (s', i) =>
                      match y with
                      | inl i' => s' = s /\ i = i' | _ => False
                      end
                    | inr (s', r) =>
                      match y with
                      | inr r' => s' = s /\ r = r' | _ => False
                      end
                    end).

  Definition sum_comm_rel {A B C} : relationH (A + (B + C)) (B + (A + C)) :=
    (fun x y => match x, y with
            | inl a, inr (inl a') => a = a'
            | inr (inl b), inl b' => b = b'
            | inr (inr c), inr (inr c') => c = c'
            | _, _ => False
            end).

  Arguments prod_sum_dist_rel /.

  Ltac crush :=
    crunch;
    repeat match goal with
            | [ H : (_ * _)%type |- _ ] => destruct H
            | [ H : (_ + _)%type |- _ ] => destruct H
          end.

  Ltac done := intros; subst; solve [apply final; reflexivity | crush ; eapply final; crush;
              cbn in *; crush; subst; solve [eauto | tauto | reflexivity]].

  #[global] Instance stateT_HFunctorLawsExt {S} {inh_S : inhabited S} :
    @HFunctorLawsExtra (stateT S) _ _ _
                  (stateT_WF_IterativeMonadT inh_S).
  Proof.
    constructor.
    - repeat intro.
      destruct F_MNT.
      subst. cbn. unfold fmap.
      subst. eapply Proper_eqmR_cong.
      eapply morph_bind. eauto.
      all : repeat intro; subst ; try reflexivity.
      subst. Unshelve. 3 : exact (fun x => ret (s', x)). cbn in H; subst. reflexivity.
      eapply Proper_eqmR. rewrite prod_rel_eq. reflexivity.
      cbn.
      eapply Proper_bind. reflexivity. intros; subst.
      setoid_rewrite morph_ret. reflexivity. eauto.
    - repeat intro. subst.
      eapply Proper_eqmR.
      { rewrite prod_rel_eq; reflexivity. }
      unfold EqmRMonadT.morph in *. cbn in *. subst.
      eapply H0. intros; cbn. destruct i0. cbn in *.
      specialize (H1 i0 s _ eq_refl).
      eapply Proper_eqmR in H1; cycle 1.
      { rewrite prod_rel_eq; reflexivity. }
      etransitivity;cycle 1.
      { eapply Proper_bind with (k1 := fun a2 => ret match snd a2 with
                      | inl i' => inl (fst a2, i')
                      | inr r => inr (fst a2, r)
                      end). eapply H1.
        all : intros; subst; reflexivity. }
      etransitivity; cycle 1.
      { eapply Proper_eqmR_mono; cycle 1.
        { eapply Proper_bind with
              (A1 := (S*I + S*R)%type)
              (RR := prod_sum_dist_rel) (RB := eq) (k1 := ret); try done.
          eapply MM_morph_proper with
              (x := (x <- t i0 s ;; ret match x with
                                        | (s, inl i) => (inl (s, i))
                                        | (s, inr r) => (inr (s, r))
                                      end)).
          typeclasses eauto.
          eapply Proper_eqmR_cong.
          2 : symmetry; eapply bind_ret_r. reflexivity.
          eapply Proper_bind with (RR := eq); [ reflexivity | ..]; done. }
        apply subrelation_refl. }
      { destruct g_IM, h_IM, M_EQM, M_EQM0. rename H into F_Nat.
        destruct F_Nat.
        repeat red in MM_morph_bind. cbn in MM_morph_bind.
        rewrite bind_ret_r.
        specialize (MM_morph_bind (S * (I + R))%type _ (S*I + S*R)%type _ eq eq (t i0 s) (t i0 s)).
        erewrite MM_morph_bind; try solve [ done | reflexivity ].
        etransitivity.
        { eapply Proper_bind; [ reflexivity | .. ]; intros; subst;
          apply MM_morph_ret ; eauto. }
        setoid_rewrite <- bind_ret_r at 5.
        eapply Proper_bind.
        { apply MM_morph_proper. setoid_rewrite <- bind_ret_r at 1.
          eapply Proper_bind with (RB := flip prod_sum_dist_rel); [ reflexivity | .. ]; done. }
        all : done. }
  Qed.

  (* Error transformer forms a higher-order functor and respects well-formedness
    laws. *)
  #[global] Instance errorT_HFunctor {exn} : HFunctor (errorT exn) :=
  {| ffmap := fun A B g _ f x =>
      fmap (fun e => match e with
                  | inl e => inl e
                  | inr a => inr (f a)
                  end) x;
    hfmap := fun g h f _ x => f _ x |}.

  #[global] Existing Instance errorT_HFunctor | 0.

  #[global] Instance errorT_HFunctorLaws {exn} : HFunctorLaws (errorT exn).
  Proof.
    constructor.
    - intros. cbn. reflexivity.
    - constructor; intros; cbn in *;cycle 1.
      { destruct F_Nat. intros; subst. repeat intro.
        eapply Proper_eqmR_cong. cbn. eapply morph_ret; eauto.
        eapply reflexivity. cbn. eapply eqmR_ret; eauto. typeclasses eauto. }
      { destruct F_Nat. repeat intro. cbn.
        eapply Proper_eqmR_cong.
        { eapply morph_bind; [eapply reflexivity | ..].
          intros; subst.
          Unshelve.
          3 : {
            intros. destruct X. exact (ret (m := g) (inl e)).
            eapply (k a). }
          cbn. reflexivity. shelve.
        }
        reflexivity.
        eapply Proper_bind. cbn. eapply morph_proper; eauto.
        intros. all : try inv H1; eauto. cbn.
        eapply MM_morph_proper; eauto. }
      { destruct F_Nat. repeat intro. cbn. eapply morph_proper; eauto. }
      constructor; typeclasses eauto.
    - repeat intro. cbn.
      eapply Proper_eqmR. rewrite sum_rel_eq. reflexivity.
      cbn in H0. eapply H.
      eapply Proper_eqmR_mono; eauto.
      repeat intro. repeat inv H1; eauto.
  Qed.

  #[global] Instance errorT_HFunctorLawsExt {exn} :
    HFunctorLawsExtra (errorT exn).
  Proof.
    constructor.
    { repeat intro. cbn. unfold fmap. 
      destruct F_MNT; eauto.
      eapply Proper_eqmR. rewrite sum_rel_eq. reflexivity.
      subst. etransitivity. eapply morph_bind.
      2 , 3 : repeat intro; try reflexivity. eauto.
      Unshelve. 6 : exact (fun x => ret (inr x)). subst; reflexivity. 
      cbn. subst; eapply reflexivity.
      eapply Proper_bind. reflexivity. intros; subst.
      eapply morph_ret. eauto. }
    { repeat intro. cbn in *.
      eapply Proper_eqmR.
      { rewrite sum_rel_eq; reflexivity. }
      unfold EqmRMonadT.morph in *. cbn in *. rename H0 into F_IM.
      eapply F_IM. intros; cbn.
      specialize (H1 i0).
      eapply Proper_eqmR in H1; cycle 1.
      { rewrite sum_rel_eq; reflexivity. }
      symmetry.
      rewrite <- H1. rename H into F_Nat. destruct F_Nat. symmetry.
      repeat red in MM_morph_proper; cbn in MM_morph_proper.
      etransitivity; cycle 1.
      { eapply Proper_eqmR_mono; cycle 1.
        { eapply Proper_bind with (RR := sum_comm_rel) (RB := eq) (k1 := ret); try done.
          eapply MM_morph_proper with
                (x := x <- (t i0 : g (exn + (I + R))%type) ;; ret
                          match x with
                              | inl e => inr (inl e)
                              | inr (inl i) => inl i
                              | inr (inr r) => inr (inr r)
                          end).
          eapply Proper_eqmR_cong; [ reflexivity | ..].
          { cbn. symmetry. apply bind_ret_r. }
          eapply Proper_bind with (RR := eq); [ reflexivity | ..]; done. }
        apply subrelation_refl. }
      { repeat red in MM_morph_bind. cbn in MM_morph_bind.
        symmetry.
        rewrite bind_ret_r.
        specialize (MM_morph_bind _ _ (I + (exn + R))%type _ eq eq (t i0) (t i0)).
        erewrite MM_morph_bind; try solve [ done | reflexivity ]. } }
  Qed.

  #[global] Instance MonadT_ID : MonadT (fun x : Type -> Type => x).
  econstructor; eauto.
  intros. repeat red. eauto.
  Defined.

  #[global] Instance ID_HFunctor : HFunctor (fun x : Type -> Type => x).
  econstructor; intros; eauto. exact (fmap X0 X1).
  Defined.

  #[global] Program Instance ID_WF_IterativeMonadT : WF_IterativeMonadT (fun x : Type -> Type => x) _ _.
  Next Obligation.
    econstructor; eauto.
    repeat intro; eauto. econstructor; repeat intro; eauto. cbn.
    eapply eqmR_ret; eauto. typeclasses eauto.
    cbn. eapply Proper_bind; eauto.
  Defined.

  #[global] Program Instance ID_WF_HFunctor : WF_HFunctor (fun x : Type -> Type => x).
  Next Obligation.
    econstructor; try typeclasses eauto; repeat intro; eauto; cbn.
    reflexivity.
  Qed.
  Next Obligation.
    econstructor; try typeclasses eauto; repeat intro; eauto; cbn.
    reflexivity.
  Qed.

  #[global] Program Instance stateT_WF_HFunctor {S} {inh_S : inhabited S} : WF_HFunctor (stateT S).

  #[global] Program Instance errorT_WF_HFunctor {exn} : WF_HFunctor (errorT exn).

  Lemma stateT_morph_ret:
    forall S : Type, inhabited S ->
      forall (E F : Type -> Type) (f : forall T : Type, E T -> stateT S (itree F) T),
        MorphRet (itree E) (stateT S (itree F)) (itree_interp f).
  Proof.
    intros S inh_S E F f.
    repeat intro.
    rewrite itree_eta. cbn.
    apply eqit_Ret; eauto.
  Qed.

  Definition _interp_state {E F S R}
            (f : E ~> stateT S (itree F)) (ot : itreeF E R _)
    : stateT S (itree F) R := fun s =>
    match ot with
    | RetF r => Ret (s, r)
    | TauF t => Tau (interp f t s)
    | VisF e k => f _ e s >>= (fun sx => Tau (interp f (k (snd sx)) (fst sx)))
    end.

  Lemma unfold_interp_state {E F S R} (h : E ~> Monads.stateT S (itree F))
        (t : itree E R) s :
      eq_itree eq
        (interp h t s)
        (_interp_state h (observe t) s).
  Proof.
    unfold interp, Basics.iter, MonadIter_stateT0, Basics.iter, MonadIter_itree; cbn.
    setoid_rewrite unfold_iter; cbn.
    rewrite Eq.bind_bind. setoid_rewrite Eq.bind_ret_l. unfold interp_body.
    destruct observe; cbn; try setoid_rewrite Eq.bind_ret_l; cbn.
    - reflexivity.
    - reflexivity.
    - setoid_rewrite Eq.bind_bind.
      setoid_rewrite Eq.bind_ret_l. cbn. reflexivity.
  Qed.

  #[global]
  Instance eq_itree_interp_state {E F S R} (h : E ~> Monads.stateT S (itree F)) :
    Proper (eq_itree eq ==> eq ==> eq_itree eq)
          (interp h (T0 := R)).
  Proof.
    revert_until R.
    ginit. gcofix CIH. intros h x y H0 x2 _ [].
    rewrite !unfold_interp_state.
    punfold H0; repeat red in H0.
    destruct H0; subst; pclearbot; try discriminate; cbn.
    - gstep; constructor; auto.
    - gstep; constructor; auto with paco.
    - guclo eqit_clo_bind. econstructor.
      + reflexivity.
      + intros [] _ []. gstep; constructor; auto with paco.
  Qed.

  #[global]
  Instance eutt_interp_state {E F: Type -> Type} {S : Type}
          (h : E ~> Monads.stateT S (itree F)) R RR :
    Proper (eutt RR ==> eq ==> eutt (prod_rel eq RR)) (interp h (T0 :=R)).
  Proof.
    repeat intro. subst. revert_until RR.
    einit. ecofix CIH. intros.

    rewrite !unfold_interp_state. punfold H0. red in H0.
    induction H0; intros; subst; simpl; pclearbot.
    - eret.
    - etau.
    - ebind. econstructor; [reflexivity|].
      intros; subst.
      etau. ebase.
    - rewrite tau_euttge, unfold_interp_state; eauto.
    - rewrite tau_euttge, unfold_interp_state; eauto.
  Qed.

  #[global]
  Definition euttH_interp_state {E F: Type -> Type} {S : Type}
          (h : E ~> Monads.stateT S (itree F)) R1 R2 RR :
    ProperH (eutt RR ~~> eq ~~> eutt (prod_rel eq RR)) (interp h (T0:=R1)) (interp h (T0:=R2)).
  Proof.
    repeat intro. subst. revert_until RR.
    einit. ecofix CIH. intros.

    rewrite !unfold_interp_state. punfold H0. red in H0.
    induction H0; intros; subst; simpl; pclearbot.
    - eret.
    - etau.
    - ebind. econstructor; [reflexivity|].
      intros; subst.
      etau. ebase.
    - rewrite tau_euttge, unfold_interp_state; eauto.
    - rewrite tau_euttge, unfold_interp_state; eauto.
  Qed.

  Lemma interp_state_tau {E F : Type -> Type} S {T : Type}
        (t : itree E T) (h : E ~> Monads.stateT S (itree F)) (s : S)
    : interp h (Tau t) s ≅ Tau (interp h t s).
  Proof.
    rewrite unfold_interp_state; reflexivity.
  Qed.

  Lemma interp_state_vis {E F : Type -> Type} {S T U : Type}
        (e : E T) (k : T -> itree E U) (h : E ~> Monads.stateT S (itree F)) (s : S)
    : interp h (Vis e k) s
    ≅ h T e s >>= fun sx => Tau (interp h (k (snd sx)) (fst sx)).
  Proof.
    rewrite unfold_interp_state; reflexivity.
  Qed.

  Lemma interp_state_bind {E F : Type -> Type} {A B S : Type}
        (f : E ~> Monads.stateT S (itree F))
        (t : itree E A) (k : A -> itree E B)
        (s : S) :
    (interp f (t >>= k) s)
      ≅
      (interp f t s >>= fun st => interp f (k (snd st)) (fst st)).
  Proof.
    revert t k s.
    ginit. pcofix CIH.
    intros t k s.
    setoid_rewrite unfold_bind at 1.
    setoid_rewrite (unfold_interp_state f _) at 2.
    destruct (observe t).
    - cbn. rewrite !Eq.bind_ret_l. cbn.
      apply reflexivity.
    - cbn. rewrite !bind_tau, interp_state_tau.
      gstep. red. apply EqTau. gbase. apply CIH.
    - cbn. rewrite interp_state_vis, Eq.bind_bind.
      guclo eqit_clo_bind. econstructor.
      + reflexivity.
      + intros u2 ? [].
        rewrite bind_tau.
        gstep; constructor.
        ITree.fold_subst.
        auto with paco.
  Qed.

  Lemma stateT_morph_bind:
    forall S : Type,
      inhabited S ->
      forall (E F : Type -> Type) (f : forall T : Type, E T -> stateT S (itree F) T),
        MorphBind (itree E) (stateT S (itree F)) (itree_interp f).
  Proof.
    repeat intro. setoid_rewrite interp_state_bind.
    eapply eutt_clo_bind; eauto.
    eapply euttH_interp_state; eauto.
    intros.
    eapply euttH_interp_state; eauto; inv H3; eauto.
    cbn. eapply H1; eauto.
  Qed.

  (* These are the base interpretations into state and error monads. *)
  #[global] Instance stateT_MonadMorphism :
    forall S {inh_S : inhabited S} (E F : Type -> Type) (f : E ~> stateT S (itree F)),
      MonadMorphism _ _ (itree_interp f).
  Proof.
    constructor; [ typeclasses eauto |
                  apply stateT_morph_ret; eauto |
                  apply stateT_morph_bind; eauto | ..].
    repeat intro. eapply euttH_interp_state; eauto.
  Qed.

  #[global] Instance stateT_IterMorphism:
    forall S {inh_S : inhabited S} (E F : Type -> Type) (f : E ~> stateT S (itree F)),
      IterMorphism (itree_interp f).
  Proof.
    unfold IterMorphism. cbn. setoid_rewrite prod_rel_eq.
    ginit. gcofix CIH; intros. cbn.
    setoid_rewrite unfold_iter at 2.
    setoid_rewrite unfold_iter at 2. cbn.
    rewrite !Eq.bind_bind.
    setoid_rewrite Eq.bind_ret_l.
    pose proof @interp_state_bind. setoid_rewrite H. clear H.
    guclo eqit_clo_bind; econstructor; eauto.
    - apply H0; eauto.
    - intros [s'' [|]] [s''' [ |]] []; cbn; subst.
      + subst. setoid_rewrite interp_state_tau.
        gstep; constructor. gfinal. left. eapply CIH; eauto.
      + subst. setoid_rewrite interp_state_tau.
        gstep; constructor. gfinal. left. eapply CIH; eauto.
      + pose proof @stateT_morph_ret. cbn in H. unfold MorphRet in H.
        unfold morph in H.
        specialize (H S _ E F f R _ eq r0 _ eq_refl s'' _ eq_refl).
        gfinal. right. cbn in H. rewrite prod_rel_eq in H.
        eapply paco2_mon; eauto; intros; contradiction.
      + pose proof @stateT_morph_ret. cbn in H. unfold MorphRet in H.
        unfold morph in H.
        specialize (H S _ E F f R _ eq r0 _ eq_refl s'' _ eq_refl).
        gfinal. right. cbn in H. rewrite prod_rel_eq in H.
        eapply paco2_mon; eauto; intros; contradiction.
  Qed.

  (** Unfolding of [interp_errorT]. *)
  Definition _interp_errorT {exn E F R} (f : E ~> errorT exn (itree F)) (ot : itreeF E R _)
    : errorT exn (itree F) R :=
    match ot with
    | RetF r => ret r
    | TauF t => Tau (interp f t)
    | VisF e k => bind (f _ e) (fun x => Tau (interp f (k x)))
    end.

  (** Unfold lemma. *)
  Lemma unfold_interp_errorT {exn E F R} (f : E ~> errorT exn (itree F)) (t : itree E R) :
    interp f t ≅
          (_interp_errorT f (observe t)).
  Proof.
    unfold interp. unfold Basics.iter, _interp_errorT, itree_interp
      , errorT_iter, Basics.iter, MonadIter_itree.
    rewrite unfold_iter. cbn.
    rewrite Eq.bind_bind. setoid_rewrite  Eq.bind_ret_l.
    unfold interp_body.
    destruct (observe t).
    tau_steps. reflexivity.
    tau_steps. reflexivity.
    setoid_rewrite Eq.bind_bind.
    apply eq_itree_clo_bind with (UU := Logic.eq); [reflexivity | intros x ? <-]. 
    destruct x as [x|].
    - cbn. rewrite Eq.bind_ret_l; reflexivity.
    - cbn. rewrite Eq.bind_ret_l; reflexivity.
  Qed.

  Lemma errorT_morph_ret:
    forall (exn : Type) (E F : Type -> Type) (f : forall T : Type, E T -> errorT exn (itree F) T),
      MorphRet (itree E) (errorT exn (itree F)) (itree_interp f).
  Proof.
    intros exn E F f.
    repeat intro. setoid_rewrite unfold_interp_errorT.
    eapply eqmR_ret; eauto. typeclasses eauto.
  Qed.

  Global Instance interp_errorT_eq_itree {exn X E F} {R : X -> X -> Prop}
        (h : E ~> errorT exn (itree F)) :
    Proper (eq_itree R ==> eq_itree (eq ⊕ R)) (interp h (T0 := X)).
  Proof.
    repeat red. 
    ginit.
    pcofix CIH.
    intros s t EQ.
    rewrite 2 unfold_interp_errorT.
    punfold EQ; red in EQ.
    destruct EQ; cbn; subst; try discriminate; pclearbot; try (gstep; constructor; eauto with paco; fail).
    guclo eqit_clo_bind; econstructor; [reflexivity | intros x ? <-].
    destruct x as [x|]; gstep; econstructor; eauto with paco.
  Qed.

  Global Instance interp_errorT_eq_itree_eq {exn X E F} (h : E ~> errorT exn (itree F)) :
    Proper (eq_itree eq ==> eq_itree eq) (interp h (T0 := X)).
  Proof.
    repeat intro. rewrite <- sum_rel_eq.
    eapply interp_errorT_eq_itree; auto.
  Qed.

  Global Instance interp_errorT_eutt {exn X E F R} (h : E ~> errorT exn (itree F)) :
    Proper (eutt R ==> eutt (eq ⊕ R)) (interp h (T0 := X)).
  Proof.
    repeat red. 
    einit.
    ecofix CIH.
    intros s t EQ.
    setoid_rewrite unfold_interp_errorT.
    punfold EQ; red in EQ.
    induction EQ; intros; cbn; subst; try discriminate; pclearbot; try (estep; constructor; eauto with paco; fail).
    - ebind; econstructor; [reflexivity |].
      intros [] [] EQ; inv EQ.
      + estep; ebase.
      + estep; ebase.
    - rewrite tau_euttge, unfold_interp_errorT; eauto.
    - rewrite tau_euttge, unfold_interp_errorT; eauto.
  Qed.

  Global Definition interp_errorT_euttH {exn X1 X2 E F} (R : X1 -> X2 -> Prop)
        (h : E ~> errorT exn (itree F)) :
    ProperH (eutt R ~~> eutt (eq ⊕ R)) (interp h (T0 := X1)) (interp h (T0 := X2)).
  Proof.
    repeat red. 
    einit.
    ecofix CIH.
    intros s t EQ.
    setoid_rewrite unfold_interp_errorT.
    punfold EQ; red in EQ.
    induction EQ; intros; cbn; subst; try discriminate; pclearbot; try (estep; constructor; eauto with paco; fail).
    - ebind; econstructor; [reflexivity |].
      intros [] [] EQ; inv EQ.
      + estep; ebase.
      + estep; ebase.
    - rewrite tau_euttge, unfold_interp_errorT; eauto.
    - rewrite tau_euttge, unfold_interp_errorT; eauto.
  Qed.

  Global Instance interp_errorT_eutt_eq {exn X E F} (h : E ~> errorT exn (itree F)) :
    Proper (eutt eq ==> eutt eq) (interp h (T0 := X)).
  Proof.
    repeat intro.
    rewrite <- sum_rel_eq.
    apply interp_errorT_eutt; auto.
  Qed.


  Lemma interp_errorT_tau {exn E F R} {f : E ~> errorT exn (itree F)} (t: itree E R):
    eq_itree eq (interp f (Tau t)) (Tau (interp f t)).
  Proof. rewrite unfold_interp_errorT. reflexivity. Qed.

  Lemma interp_errorT_vis {E F : Type -> Type} {T U exn : Type}
        (e : E T) (k : T -> itree E U) (h : E ~> errorT exn (itree F)) 
    : interp h (Vis e k)
                  ≅ bind (h T e) (fun mx => Tau (interp h (k mx))).
  Proof.
    rewrite unfold_interp_errorT. reflexivity.
  Qed.

  Lemma interp_errorT_bind : forall {exn X Y E F} (t : itree _ X) (k : X -> itree _ Y)
                              (h : E ~> errorT exn (itree F)),
      interp h (bind t k) ≅
                  bind (interp h t) (fun x => interp h (k x)).
  Proof.
    intros exn X Y E F; ginit; gcofix CIH; intros.
    pose proof (@unfold_interp_errorT exn E F X h t).
    unfold interp, itree_interp in *. cbn.
    rewrite H.
    setoid_rewrite unfold_bind at 1.
    destruct (observe t) eqn:EQ; cbn.
    - rewrite Eq.bind_ret_l. apply reflexivity.
    - cbn. rewrite bind_tau. setoid_rewrite interp_errorT_tau.
      gstep. econstructor; eauto with paco.
      cbn in CIH. gbase. eapply CIH.
    - rewrite Eq.bind_bind. setoid_rewrite interp_errorT_vis.
      guclo eqit_clo_bind; econstructor.
      reflexivity.
      intros [] ? <-; cbn.
      + rewrite Eq.bind_ret_l.
        apply reflexivity.
      + rewrite bind_tau.
        gstep; constructor.
        ITree.fold_subst. gbase. eapply CIH.
  Qed.

  Lemma errorT_morph_bind:
    forall (exn : Type) (E F : Type -> Type) (f : forall T : Type, E T -> errorT exn (itree F) T),
      MorphBind (itree E) (errorT exn (itree F)) (itree_interp f).
  Proof.
    repeat intro. setoid_rewrite interp_errorT_bind.
    eapply eutt_clo_bind; eauto.
    eapply interp_errorT_euttH; eauto.
    intros. inv H1; try apply eqit_Ret; eauto.
    eapply interp_errorT_euttH; eauto. eapply H0; eauto.
  Qed.

  #[global] Instance errorT_MonadMorphism :
    forall exn (E F : Type -> Type) (f : E ~> errorT exn (itree F)),
      MonadMorphism _ _ (itree_interp f).
  Proof.
    constructor; [constructor; try typeclasses eauto |
                  apply errorT_morph_ret |
                  apply errorT_morph_bind |..].
    repeat intro; eapply interp_errorT_euttH; eauto.
  Qed.

  #[global] Instance errorT_IterMorphism:
    forall exn (E F : Type -> Type) (f : E ~> errorT exn (itree F)),
      IterMorphism (itree_interp f).
  Proof.
    unfold IterMorphism. cbn. setoid_rewrite sum_rel_eq.
    ginit. gcofix CIH; intros. cbn.
    setoid_rewrite unfold_iter at 2.
    setoid_rewrite unfold_iter at 2. cbn.
    rewrite !Eq.bind_bind.
    setoid_rewrite Eq.bind_ret_l.
    pose proof @interp_errorT_bind. setoid_rewrite H. clear H.
    guclo eqit_clo_bind; econstructor; eauto.
    - apply H0; eauto.
    - intros [s'' | [|]] [s''' | [ |]] H; cbn; subst; inv H.
      + gstep; constructor; eauto.
      + subst. setoid_rewrite interp_errorT_tau.
        gstep; constructor. gfinal. left. eapply CIH; eauto.
      + pose proof @errorT_morph_ret. cbn in H. unfold MorphRet in H.
        unfold morph in H.
        specialize (H exn E F f R _ eq r1 _ eq_refl).
        gfinal. right. cbn in H. rewrite sum_rel_eq in H.
        eapply paco2_mon; eauto; intros; contradiction.
  Qed.

End HFunctorInstances.

(** *Nesting HFunctors *)
(* HFunctors compose(nest) to make a HFunctor, and also the well-formedness
  properties are closed under nesting as well. *)
Section ComposeHFunctors.

  #[local] Instance compose_HFunctor {S T : (Type -> Type) -> Type -> Type} `{HFunctor S} `{HFunctor T}:
    HFunctor (fun x => S (T x)).
  Proof.
    constructor.
    - intros. eapply (ffmap X0 X1).
      Unshelve.
      constructor. exact (fun x y F X => ffmap F X).
    - intros. exact (hfmap (hfmap X) X0).
  Defined.

  #[local] Instance compose_WF_HFunctor {S T : (Type -> Type) -> Type -> Type} `{WF_HFunctor S} `{WF_HFunctor T}:
    WF_HFunctor (fun x => S (T x)).
  Proof.
    econstructor; constructor; intros.
    - cbn. etransitivity. eapply @hfmap_proper; try typeclasses eauto.
      repeat intro; eauto. Unshelve. 4 : exact (fun _ X => X).
      cbn. etransitivity. eapply morph_proper; eauto.
      eapply hfmap_id; eauto. reflexivity.
      eapply hfmap_id; eauto. typeclasses eauto.
    - cbn; constructor; try typeclasses eauto; repeat intro.
      + cbn.
        destruct H.
        destruct T_HFunctorLaws0.
        pose proof (hfmap_nat0 (T g) (T h) _ _ _ _ _ _ (@hfmap _ _ g h F) _).
        destruct H. repeat red in MM_morph_ret. cbn in *. eapply MM_morph_ret; eauto.
      + cbn.
        destruct H.
        destruct T_HFunctorLaws0.
        pose proof (hfmap_nat0 (T g) (T h) _ _ _ _ _ _ (@hfmap _ _ g h F) _).
        destruct H. repeat red in MM_morph_bind. cbn in *. eapply MM_morph_bind; eauto.
      + cbn.
        destruct H.
        destruct T_HFunctorLaws0.
        pose proof (hfmap_nat0 (T g) (T h) _ _ _ _ _ _ (@hfmap _ _ g h F) _).
        destruct H. repeat red in MM_morph_proper. cbn in *. eapply MM_morph_proper; eauto.
    - repeat intro. cbn.
      eapply (@hfmap_proper S); try typeclasses eauto.
      repeat intro.
      eapply (@hfmap_proper T); try typeclasses eauto; repeat intro; eauto. eauto.
    - cbn -[lift].
      etransitivity.
      eapply (@hfmap_lift S); try typeclasses eauto.
      econstructor; try typeclasses eauto.
      econstructor; try typeclasses eauto.
      eapply morph_proper.
      eapply (@hfmap_lift T); try typeclasses eauto.
    - repeat intro. cbn.
      etransitivity.
      eapply (@hfmap_iter S); try typeclasses eauto.
      econstructor; try typeclasses eauto.
      econstructor; try typeclasses eauto.
      destruct H0. destruct T_HFunctorLawsExtra0. eapply hfmap_iter0; typeclasses eauto.
      eauto. reflexivity.
      Unshelve.
      destruct H0. destruct T_HFunctorLaws0.
      pose proof (hfmap_nat0 g g _ _ _ _ _ _ (fun _ x => x)).
      edestruct H0; eauto.
      econstructor; repeat intro; cbn; eauto.
      eapply eqmR_ret; try typeclasses eauto; eauto.
      eapply eqmR_bind_ProperH; try typeclasses eauto; eauto.
  Defined.

End ComposeHFunctors.
