(** * Extensible effects *)

(** Interface for extensible effects.

    This file contains the Subevent, Over, and Trigger typeclasses, which is a
    practical solution for handling sums of events for extensible effects.
    - [Subevent]: an isomorphism between event signatures
    - [Trigger]: operation for a minimal impure computation
    - [Over]: lifting of handlers over sums of events

    We characterize isomorphisms between _sums of events_, where we use
    typeclass resolution to infer the correct type-injections for the [over] and
    [trigger] combinators.

    Typeclass resolution is used for the automatic injection of handlers over large
    sums of events. *)

(* begin hide *)
From Coq Require Import
     Setoid Morphisms.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.CategoryTheory
     Basics.CategoryFacts
     Basics.Function
     Basics.FunctionFacts
     Core.ITreeDefinition
     Indexed.Sum
     Indexed.Function
     Indexed.FunctionFacts
     EqmR.EqmRMonadT.

From ExtLib Require Import
     Monad.

Import MonadNotation.
Import CatNotations.
Open Scope cat_scope.
Import ITree.Basics.Basics.Monads.

Set Implicit Arguments.
(* end hide *)

(** ** Subevents

  Subevents provide an isomorphism between event signatures. Instances of
  subevents can be used for automatically inferring whether or not an event
  signature is part of a large sum of events.

  The operator for sums is associative and commutative (which is formulated
  in Section [Subevent_Instances]). *)
Section Subevent.

  Class Subevent {A B C : Type -> Type} : Type := {
    split_E : B ~> A +' C ;
    merge_E : (A +' C) ~> B
  }.

  Class Subevent_wf {A B C} (sub: @Subevent A B C): Prop :=
    sub_iso :> Iso _ split_E merge_E.

  Arguments Subevent : clear implicits.
  Arguments split_E {_ _ _ _} [_].
  Arguments merge_E {_ _ _ _} [_].

  (** Injection and case analysis for events *)
  Definition inj1 {A B C} `{Subevent A B C} : A ~> B :=  inl_ >>> merge_E.
  Definition inj2 {A B C} `{Subevent A B C} : C ~> B :=  inr_ >>> merge_E.
  Definition case  {A B C} `{Subevent A B C} : B ~> (A +' C) := split_E.

End Subevent.

Arguments Subevent : clear implicits.
Arguments case {_ _ _ _} [_].
Arguments inj1 {_ _ _ _} [_].
Arguments inj2 {_ _ _ _} [_].

Notation "A +? C -< B" := (Subevent A B C)
                            (at level 89, left associativity) : type_scope.

(** ** Triggerable Monads

    A _trigger_ is defined as the "minimal" impure computation performing an
    uninterpreted event.

    For the case of ITrees, it corresponds to the [trigger] combinator, i.e.
    [trigger e := Vis e (fun x => x)]. We generalize this notion for any monad
    that can perform a minimal impure computation. *)
Section Trigger.


  (** The [Trigger M E] typeclass contains an operation that given
     an event [e] builds the "smallest" monadic value that executes [e]. *)
  Class Trigger (E: Type -> Type) (M: Type -> Type) := trigger: E ~> M.

End Trigger.

Arguments trigger {E M Trigger} [T].
Notation vis e k := (Vis (inj1 e) k).

(** *** Instances of Triggerable monads  *)
Section Trigger_Instances.

  (** The minimal [itree] that performs [e] is [Vis e (fun x => Ret x)], already
      defined as [ITree.trigger] *)
  #[global] Instance Trigger_ITree {E F G} `{E +? F -< G}: Trigger E (itree G) :=
    fun _ e => ITree.trigger (inj1 e).

  (** We allow to look for the inclusion by commuting the two arguments.
      By doing it only at this level it's a cheap way to explore both options
      while avoiding looping resolutions *)
  #[global] Instance Trigger_ITree_base {E} : Trigger E (itree E) :=
    fun _ e => ITree.trigger e.

  (** Monad transformers with ITrees as a base monad are triggerable. *)
  #[global] Instance Trigger_MonadT {E F G} `{E +? F -< G}
            {T : (Type -> Type) -> Type -> Type} {T_MonadT: MonadT T} : Trigger E (T (itree G)) :=
    (fun X e => lift (trigger e)).

  (** The [PropT] transformer returns the propositional singleton of the
    underlying trigger. However, we might want this singleton to be up to some equivalence *)
  #[global] Instance Trigger_Prop {E} {M} `{Monad M} `{Trigger E M} :
    Trigger E (fun X => M X -> Prop) :=
    (fun T e m => m = (trigger e)).

End Trigger_Instances.


(** ** Over: injection for handlers over sums of events

   Generic lifting of an handler over a super-set of events. The function relies
   on the constraint [A +? C -< B] to know how to case analyse on a [B] event. *)
Definition over {A B C M : Type -> Type} {S:A +? C -< B} {T:Trigger C M} (f : A ~> M) : B ~> M  :=
  fun t b =>  match case b with
           | inl1 a => f _ a
           | inr1 c => trigger c
           end.

Arguments over {_ _ _ _ _ _} _ [_] _.

(** A few auxiliary lemmas for injection. *)
Lemma case_inj1: forall {A B C: Type -> Type} `{Sub: A +? C -< B} {SubWF: Subevent_wf Sub} {T} (e: A T),
    case (inj1 e) = inl_ _ e.
Proof.
  intros.
  pose proof (iso_epi IFun T (inl_ _ e)).
  auto.
Qed.

Lemma case_inj2: forall {A B C: Type -> Type} `{Sub: A +? C -< B} {SubWF: Subevent_wf Sub} {T} (e: C T),
    case (inj2 e) = inr_ _ e.
Proof.
  intros.
  pose proof (iso_epi IFun T (inr_ _ e)).
  auto.
Qed.

Lemma over_inj1: forall {A B C M: Type -> Type}
                   {Sub: A +? C -< B} {SubWF: Subevent_wf Sub} {Trig: Trigger C M}
                   (h: A ~> M)
                   {T} (e: A T),
    over h (inj1 e) = h _ e.
Proof.
  intros.
  unfold over; rewrite case_inj1; reflexivity.
Qed.

Lemma over_inj2: forall {A B C M: Type -> Type}
                   {Sub: A +? C -< B} {SubWF: Subevent_wf Sub} {Trig: Trigger C M}
                   (h: A ~> M)
                   {T} (e: C T),
    over h (inj2 e) = trigger e.
Proof.
  intros.
  unfold over; rewrite case_inj2; reflexivity.
Qed.

(** ** Instances for Automatic Injection

    We characterize the algebraic properties of the abstract sum operation [+?]
    for automatically injecting the handlers over a sum of events.

    The rules are as follows:
    [void1] is the unital operator, and the [+?] operation is associative and
    coummutative.

    Each of the instances come with a proof of isomorphism, thus guaranteeing
    soundness of inference. *)
Section Subevent_Instances.

    Class CUnit : Type := CUnitC {}.
    Global Instance cUnit: CUnit := CUnitC.

    (** *** Event level instances *)
    (* The subeffect relationship is reflexive: [A -<  A] *)
    #[local] Instance Subevent_refl `{CUnit} {A : Type -> Type} : A +? void1 -< A :=
      {| split_E := inl_: IFun _ _
         ; merge_E := unit_r: IFun _ _
      |}.

    #[global] Instance Subevent_void `{CUnit} {A : Type -> Type} : void1 +? A -< A :=
      {| split_E := inr_: IFun _ _
         ; merge_E := unit_l: IFun _ _
      |}.

    (* Extends the domain to the left: [A -< B -> C +' A -< C +' B] *)
    #[local] Instance Subevent_Sum_In `{CUnit} {A B C D: Type -> Type} `{A +? D -< B} : (C +' A) +? D -< C +' B :=
      {|
        split_E := case_ (inl_ >>> inl_) (split_E >>> bimap inr_ (id_ _));
        merge_E := assoc_r >>> bimap (id_ _) merge_E
      |}.

    #[local] Instance Subevent_Sum_Out `{CUnit} {A B C D: Type -> Type}
             `{A +? D -< B} : A +? C +' D -< C +' B :=
      {|
        split_E := case_ (inl_ >>> inr_) (split_E >>> bimap (id_ _) inr_)
        ; merge_E := case_ (inl_ >>> merge_E >>> inr_) (bimap (id_ _) (inr_ >>> merge_E))
      |}.

    #[local] Instance Subevent_Base `{CUnit} {A B}: A +? B -< A +' B :=
      {|
        split_E := id_ _;
        merge_E := id_ _
      |}.

    #[local] Instance Subevent_to_complement `{CUnit} {A B C E} `{A +' B +? C -< E}: A +? B +' C -< E :=
      {|
        split_E := split_E >>> assoc_r;
        merge_E := assoc_l >>> merge_E
      |}.

    (** Associativity of subevents *)
    #[local] Instance Subevent_Assoc1 `{CUnit} {A B C D E: Type -> Type} `{Subevent (A +' (B +' C)) D E} : Subevent ((A +' B) +' C) D E :=
      {| split_E := split_E >>> case_ (assoc_l >>> inl_) inr_
         ; merge_E := bimap assoc_r (id_ _) >>> merge_E
      |}.

    #[local] Instance Subevent_Assoc2 `{CUnit} {A B C D E: Type -> Type}
      `{A +? E -< (B +' (C +' D))}: A +? E -< ((B +' C) +' D) :=
        {| split_E := assoc_r >>> split_E
           ; merge_E := merge_E >>> assoc_l
        |}.

    #[local] Instance Subevent_Assoc3 `{CUnit} {A B C D E: Type -> Type}
       `{A +? (B +' (C +' D)) -< E} : A +? ((B +' C) +' D) -< E :=
      {| split_E := split_E >>> (bimap (id_ _) assoc_l)
          ; merge_E := (bimap (id_ _) assoc_r) >>> merge_E
      |}.

    (** Other instances that are useful for efficient resolution. *)
    #[local] Instance Subevent_forget_order `{CUnit}
             {E C1 C2 A B}
             {Sub1: A +? C1 -< E}
             {Sub2: B +? C2 -< C1}:
      Subevent B E (A +' C2) :=
      {| split_E := split_E >>> case_
                            (inl_ >>> inr_)
                            (split_E >>> case_
                                     inl_
                                     (inr_ >>> inr_))
         ; merge_E := case_
                        (inl_ >>> merge_E >>> inr_ >>> merge_E)
                        (case_
                           (inl_ >>> merge_E)
                           (inr_ >>> merge_E >>> inr_ >>> merge_E))
      |}.

    #[local] Instance Subevent_forget_order_wf
             `{CUnit}
             {E C1 C2 A B}
             {Sub1: A +? C1 -< E}
             {Sub2: B +? C2 -< C1}
             {Sub1WF: Subevent_wf Sub1}
             {Sub2WF: Subevent_wf Sub2}
      : Subevent_wf (@Subevent_forget_order _ _ _ _ _ _ Sub1 Sub2).
    Proof.
      split.
      - cbn.
        unfold SemiIso.
        rewrite cat_assoc, cat_case.
        rewrite cat_assoc, case_inr, case_inl.
        rewrite cat_assoc, cat_case.
        rewrite cat_assoc, case_inl.
        rewrite (cat_assoc inr_ inr_), 2 case_inr.
        (* Can we avoid this mess? *)
        unfold cat, Cat_IFun, case_, Case_sum1, case_sum1, inl_, Inl_sum1, inr_, Inr_sum1, id_, Id_IFun.
        intros ? e.
        generalize (iso_mono _ (Iso := sub_iso) _ e); intros ISO1.
        unfold cat, Cat_IFun, case_, Case_sum1, case_sum1, inl_, Inl_sum1, inr_, Inr_sum1, id_, Id_IFun in *.
        destruct (split_E T e) eqn:EQ.
        + auto.
        + generalize (iso_mono _ (Iso := sub_iso) _ c); intros ISO2.
          unfold cat, Cat_IFun, case_, Case_sum1, case_sum1, inl_, Inl_sum1, inr_, Inr_sum1, id_, Id_IFun in *.
          destruct (split_E T c) eqn:EQ'.
          * rewrite <- EQ' in *; rewrite ISO2.
            auto.
          * rewrite <- EQ' in *; rewrite ISO2.
            auto.
      - cbn.
        unfold SemiIso.
        repeat rewrite cat_case.
        repeat rewrite cat_assoc.
        generalize (@sub_iso _ _ _ _ Sub1WF); intros [_ epi1].
        generalize (@sub_iso _ _ _ _ Sub2WF); intros [_ epi2].
        unfold SemiIso in *.
        rewrite <- (cat_assoc merge_E split_E).
        rewrite epi1, cat_id_l, case_inr, case_inl.
        rewrite <- (cat_assoc merge_E split_E).
        rewrite epi2, cat_id_l, case_inr, case_inl.
        intros ? [|[|]]; cbn; reflexivity.
    Qed.

    (** Commutativity of subevents *)
    #[local] Instance Subevent_commute
             `{CUnit}
             {A B C}
             {Sub: A +? B -< C}:
      B +? A -< C :=
      {| split_E := split_E >>> swap
         ; merge_E := swap >>> merge_E |}.

   (** *** Well-formedness of the instances

      Each subevent instance defines an isomorphism. *)
    #[local] Instance Subevent_refl_wf {A : Type -> Type} : @Subevent_wf A _ _ Subevent_refl.
    Proof.
      constructor.
      - cbv; reflexivity.
      - cbv; intros ? [? | []]; reflexivity.
    Qed.

    #[local] Instance Subevent_void_wf {A : Type -> Type} : @Subevent_wf _ A _ Subevent_void.
    Proof.
      constructor.
      - cbv; reflexivity.
      - cbv. intros ? [[] | ?]; reflexivity.
    Qed.

    #[global] Instance Subevent_Base_wf {A B: Type -> Type} : Subevent_wf (@Subevent_Base _ A B).
    Proof.
      constructor; split; cbv; reflexivity.
    Qed.

    #[local] Instance Subevent_to_complement_wf {A B C D: Type -> Type}
             {Sub: (A +' B) +? C -< D}
             {SubWf: Subevent_wf Sub}
      : Subevent_wf (@Subevent_to_complement _ _ _ _ _ Sub).
    Proof.
      constructor.
      - cbn.
        apply SemiIso_Cat.
        apply SubWf.
        apply AssocRMono_Coproduct.
      - cbn.
        apply SemiIso_Cat.
        apply AssocLMono_Coproduct.
        apply SubWf.
    Qed.

    #[local] Instance Subevent_Assoc1_wf {A B C D E: Type -> Type}
             {Sub: (A +' B +' C) +? E -< D}
             {SubWf: Subevent_wf Sub}
      : Subevent_wf (@Subevent_Assoc1 _ A B C D E Sub).
    Proof.
      constructor.
      - cbn.
        apply SemiIso_Cat.
        apply SubWf.
        unfold SemiIso.
        rewrite cat_case.
        rewrite cat_assoc, inl_bimap.
        rewrite <- cat_assoc, assoc_l_mono, cat_id_l.
        rewrite inr_bimap, cat_id_l.
        rewrite <- case_eta.
        reflexivity.
      - cbn. apply SemiIso_Cat.
        2 : apply SubWf.
        unfold SemiIso.
        rewrite bimap_case.
        rewrite cat_id_l.
        rewrite <- cat_assoc, assoc_r_mono.
        rewrite cat_id_l.
        rewrite <- case_eta.
        reflexivity.
    Qed.

    #[local] Instance Subevent_Assoc2_wf {A B C D E: Type -> Type}
             {Sub: A +? E -< (B +' (C +' D))}
             {SubWf: Subevent_wf Sub}
      : Subevent_wf (@Subevent_Assoc2 _ A B C D E Sub).
    Proof.
      constructor.
      - cbn.
        apply SemiIso_Cat, SubWf.
        unfold SemiIso.
        rewrite assoc_r_mono; reflexivity.
      - cbn.
        apply SemiIso_Cat.
        apply SubWf.
        unfold SemiIso.
        rewrite assoc_l_mono; reflexivity.
    Qed.

    #[local] Instance Subevent_Assoc3_wf {A B C D E: Type -> Type}
             {Sub: A +? (B +' (C +' D)) -< E}
             {SubWf: Subevent_wf Sub}
      : Subevent_wf (@Subevent_Assoc3 _ A B C D E Sub).
    Proof.
      constructor.
      - cbn.
        apply SemiIso_Cat. apply SubWf.
        apply SemiIso_Bimap.
        apply SemiIso_Id.
        apply AssocLMono_Coproduct.
      - cbn.
        apply SemiIso_Cat.
        apply SemiIso_Bimap.
        apply SemiIso_Id.
        apply AssocRMono_Coproduct.
        apply SubWf.
    Qed.

    #[local] Instance Subevent_Sum_In_wf {A B C D: Type -> Type}
             {Sub: A +? D -< B}
             {SubWf: Subevent_wf Sub}
      : Subevent_wf (@Subevent_Sum_In _ A B C D Sub).
    Proof.
      constructor.
      - cbn.
        unfold SemiIso.
        rewrite cat_case.
        rewrite <- cat_assoc, (cat_assoc inl_ inl_), inl_assoc_r.
        do 2 rewrite inl_bimap, cat_id_l.
        rewrite <- inr_assoc_l.
        rewrite ! cat_assoc, <- (cat_assoc _ assoc_r _), assoc_l_mono, cat_id_l.
        rewrite inr_bimap, <- cat_assoc.
        rewrite semi_iso; [| apply SubWf].
        rewrite cat_id_l, case_eta.
        reflexivity.
      - cbn.
        unfold SemiIso.
        rewrite cat_assoc, bimap_case, cat_id_l.
        rewrite <- cat_assoc.
        rewrite (@semi_iso _ _ _ _ _ _ _ merge_E split_E); [| apply SubWf].
        rewrite cat_id_l.
        unfold assoc_r, AssocR_Coproduct.
        rewrite cat_case.
        rewrite cat_assoc, case_inr.
        rewrite cat_case.
        rewrite cat_assoc, case_inr, case_inl.
        rewrite inr_bimap, inl_bimap, cat_id_l.
        rewrite <- case_eta', <- case_eta.
        reflexivity.
    Qed.

    #[local] Instance Subevent_Sum_Out_wf {A B C D: Type -> Type}
             {Sub: A +? D -< B}
             {SubWf: Subevent_wf Sub}
      : Subevent_wf (@Subevent_Sum_Out _ A B C D Sub).
    Proof.
      constructor.
      - cbn.
        unfold SemiIso.
        rewrite cat_case.
        rewrite cat_assoc, inr_case, inl_bimap, cat_id_l.
        rewrite cat_assoc, bimap_case, cat_id_l.
        rewrite inr_bimap.
        rewrite 2 cat_assoc, <- cat_case, <- case_eta, cat_id_l.
        rewrite <- cat_assoc, semi_iso; [| apply SubWf].
        rewrite cat_id_l, <- case_eta.
        reflexivity.
      - cbn.
        unfold SemiIso.
        rewrite cat_case.
        rewrite 2 cat_assoc, inr_case.
        rewrite <- (cat_assoc _ split_E _), semi_iso; [| apply SubWf].
        rewrite cat_id_l, inl_bimap, cat_id_l.
        rewrite bimap_case, cat_id_l.
        rewrite <- cat_assoc, (cat_assoc _ merge_E _), semi_iso; [| apply SubWf].
        rewrite cat_id_r, inr_bimap, <- case_eta', <- case_eta.
        reflexivity.
    Qed.

End Subevent_Instances.

(** ** Automatic solver for associating subevents *)
#[global] Existing Instance Subevent_refl          | 0.
#[global] Existing Instance Subevent_void          | 0.
#[global] Existing Instance Subevent_Base          | 0.
#[global] Existing Instance Subevent_Sum_In        | 2.
#[global] Existing Instance Subevent_Sum_Out       | 3.
#[global] Existing Instance Trigger_ITree          | 1.
#[global] Existing Instance Trigger_MonadT         | 1.
#[global] Existing Instance Trigger_Prop           | 1.
#[global] Existing Instances Trigger_ITree Trigger_ITree_base Trigger_MonadT Trigger_Prop.

#[global]
Hint Extern 10 (Subevent ?A ?B ?C) =>
match goal with
| h: _ +? ?E -< ?C |- _ =>
  match goal with
  | h': ?A +? _ -< ?E |- _ =>
    apply (@Subevent_forget_order _ _ _ _ _ _ h h')
  end
end: typeclass_instances.
#[global]
Hint Extern 10 (Subevent ?A ?B ?C) =>
match goal with
| h: ?B +? ?A -< ?C |- _ =>
  exact (@Subevent_commute _ _ _ _ h)
end: typeclass_instances.
