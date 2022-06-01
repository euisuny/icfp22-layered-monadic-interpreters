(** * Heterogeneous relations *)

(* A categorical account of this file is given in [CategoryRelation.v] *)

(* begin hide *)
From Coq Require Import
     Logic.ChoiceFacts
     Morphisms
     Setoid
     Relation_Definitions
     RelationClasses.

From ITree Require Import Tacs.
(* end hide *)

Definition relationH (A B : Type) := A -> B -> Prop.

Section RelationH_Operations.

  Definition rel_compose {A B C} (S : relationH B C) (R : relationH A B): relationH A C :=
    fun x y => exists b, R x b /\ S b y.

  (** ** Relations for morphisms/parametricity *)

  (* Heterogeneous notion of [subrelation] *)
  Definition subrelationH {A B} (R S : relationH A B) : Prop :=
    forall (x : A) (y : B), R x y -> S x y.

  Definition eq_rel {A B} (R S : relationH A B) :=
      subrelationH R S /\ subrelationH S R.

  Definition transpose {A B: Type} (R: relationH A B): relationH B A :=
    fun x y => R y x.

  (* The graph of a function forms a relation *)
  Definition fun_rel {A B: Type} (f: A -> B): relationH A B :=
    fun x y => y = f x.

  (** ** Relations for morphisms/parametricity *)

  (** Logical relation for the [sum] type. *)
  Variant sum_rel {A1 A2 B1 B2 : Type}
      (RA : relationH A1 A2) (RB : relationH B1 B2)
  : relationH (A1 + B1) (A2 + B2) :=
  | inl_morphism a1 a2 : RA a1 a2 -> sum_rel RA RB (inl a1) (inl a2)
  | inr_morphism b1 b2 : RB b1 b2 -> sum_rel RA RB (inr b1) (inr b2).

  (** Logical relation for the [prod] type. *)
  Variant prod_rel {A1 A2 B1 B2 : Type}
      (RA : relationH A1 A2) (RB : relationH B1 B2)
    : relationH (A1 * B1) (A2 * B2) :=
  | prod_morphism a1 a2 b1 b2 : RA a1 a2 -> RB b1 b2 -> prod_rel RA RB (a1, b1) (a2, b2)
  .

  (* Heterogeneous properness *)
  Definition ProperH :=
    let U := Type in fun (A1 A2 : U) (R : relationH A1 A2) (m1 : A1) (m2 : A2) => R m1 m2.

  (* Non-dependent heterogeneous respectfulness. c.f. [respectful_hetero] *)
  Definition respectfulH :=
    let U := Type in
    fun (A1 A2 B1 B2 : U) (R : relationH A1 A2) (R' : relationH B1 B2) (f : A1 -> B1) (g : A2 -> B2) =>
      forall (x : A1) (y : A2), R x y -> R' (f x) (g y).

  Definition pointwise_relationH {A1 A2 B1 B2}
             (RA : relationH A1 A2) (RB : relationH B1 B2) : relationH (A1 -> B1) (A2 -> B2) :=
    fun f g => forall (a1 : A1) (a2 : A2), RA a1 a2 -> RB (f a1) (g a2).

End RelationH_Operations.

Global Hint Constructors prod_rel: core.
Global Hint Constructors sum_rel: core.

Arguments inl_morphism {A1 A2 B1 B2 RA RB}.
Arguments inr_morphism {A1 A2 B1 B2 RA RB}.
Arguments prod_morphism {A1 A2 B1 B2 RA RB}.

Arguments rel_compose [A B C] S R.
Arguments subrelationH [A B] R S.
Arguments transpose [A B] R.
Arguments sum_rel [A1 A2 B1 B2] RA RB.
Arguments prod_rel [A1 A2 B1 B2] RA RB.

Arguments ProperH {_ _}.
Declare Scope relationH_scope.

Module RelNotations.

  (* Notice the levels: (R ⊕ S ⊗ T ∘ U) is parsed as ((R ⊕ (S ⊗ T)) ∘ U) *)
  Infix "∘" := rel_compose (at level 40, left associativity) : relationH_scope.
  Infix "⊕" := sum_rel (at level 39, left associativity) : relationH_scope.
  Infix "⊗" := prod_rel (at level 38, left associativity) : relationH_scope.

  Infix "⊑" := subrelationH (at level 70, no associativity) : relationH_scope.
  Notation "† R" := (transpose R) (at level 5, right associativity) : relationH_scope.

  Infix "≡" := eq_rel (at level 70, no associativity) : relationH_scope.

  Notation " R ~~> R' " := (@respectfulH _ _ _ _ (R%signature) (R'%signature))
                             (right associativity, at level 55) : relationH_scope.

End RelNotations.

Import RelNotations.
Local Open Scope relationH_scope.

#[global]
Instance Proper_relation {A: Type} (R : relationH A A) :
  Proper (@eq A ==> @eq A ==> iff) R.
Proof.
  repeat intro.
  repeat red.
  split; intros.
  - rewrite <- H,<- H0. auto.
  - rewrite H, H0. auto.
Qed.

(* Properties of Heterogeneous Relations ************************************ *)

Class ReflexiveH {A: Type} (R : relationH A A) : Prop :=
  reflexive : forall (a:A), R  a a.

Class SymmetricH {A: Type} (R : relationH A A) : Prop :=
  symmetric : forall x y, R x y -> R y x.

Class TransitiveH {A: Type} (R : relationH A A) : Prop :=
  transitive : forall x y z, R  x y -> R  y z -> R x z.

Class PER {A : Type} (R : relationH A A) : Type :=
  {per_symm :> SymmetricH R;
    per_trans :> TransitiveH R
  }.

(** *Partitions on Heterogeneous Relations *)
(* https://en.wikipedia.org/wiki/Heterogeneous_relation#Difunctional
  Among homogeneous relations, equivalence relations partition the set.

  For heterogeneous relations, a partitioning relation is a
  _difunctional_ relation, R = F (†G), where F and G are univalent
  (functional), i.e. forall x y z, F x y /\ F x z => y = z.

  N.B.: For homogeneous relations, PER's are _difunctional_.

  This is also known as a "quasi-PER" (QPER) or zig-zag complete relation.
    (See Krishnaswami and Dreyer 2012, 2013.)

            a1 -----> b1
              -
                -
                  -
                    ->
            a2 -----> b2

     Given the following diagram, there must also be a (a2, b1) ∈ R. *)
(* Two possible formulations of Zigzag. *)
Class Zigzag {A B : Type} (R : relationH A B) : Type :=
  zigzag : R ∘ († R ∘ R) ⊑ R.

Class Zigzag' {A B : Type} (R : relationH A B) : Type :=
  zigzag' : forall {a b a' b'}, R a b -> R a' b -> R a' b' -> R a b'.

(* The two defs of Zigzag are equivalent. *)
Lemma ZZC_zigzag_zigzag'_iff :
  forall {A B : Type} (R : relationH A B),
    Zigzag' R <-> Zigzag R.
Proof.
  intros. split; unfold Zigzag', Zigzag. intros.
  - intros a b (? & (? & ? & ?) & ?).
    eauto.
  - intros. red in H. apply H. esplit; split. esplit; split.
    all: eauto.
Qed.

Class Preorder {A : Type} (R : relationH A A) : Type :=
  {
    pre_refl :> ReflexiveH R;
    pre_trans :> TransitiveH R
  }.

Class EquivalenceH {A : Type} (R : relationH A A) : Type :=
  {
    equiv_refl :> ReflexiveH R;
    equiv_symm :> SymmetricH R;
    equiv_trans :> TransitiveH R
  }.

Global Instance relationH_reflexive : forall (A:Type), ReflexiveH (@eq A).
Proof.
  repeat intro.
  reflexivity.
Defined.

Global Instance relationH_symmetric : forall (A:Type), SymmetricH (@eq A).
Proof.
  repeat intro. cbn; auto.
Defined.

Global Instance relationH_transitive : forall (A:Type), TransitiveH (@eq A).
Proof.
  repeat intro. cbn in *. etransitivity.
  apply H. apply H0.
Defined.

Global Instance relationH_PER {A : Type} : PER (@eq A).
  constructor; typeclasses eauto.
Defined.

Global Instance relationH_Preorder {A : Type} : Preorder (@eq A).
  constructor; typeclasses eauto.
Defined.

Global Instance relationH_Equiv {A : Type} : EquivalenceH  (@eq A).
  constructor; typeclasses eauto.
Defined.

Lemma ReflexiveH_Reflexive {A: Type} (R : relationH A A) :
  ReflexiveH R <-> Reflexive R.
Proof.
  split; intros.
  - red. apply H.
  - apply H.
Qed.

Lemma SymmetricH_Symmetric {A: Type} (R : relationH A A) :
  SymmetricH R <-> Symmetric R.
Proof.
  split; intros.
  - red. unfold SymmetricH in H. intros. specialize (H x y). cbn in H.
    apply H. assumption.
  - red. intros p HP. cbn in *. apply H.
Qed.

Lemma TransitiveH_Transitive {A: Type} (R : relationH A A) :
  TransitiveH R <-> Transitive R.
Proof.
  split; intros.
  - red. intros x y z H0 H1. unfold TransitiveH in H. eapply H; eauto.
  - red. intros p q HP HQ EQ.
    unfold Transitive in H. cbn in EQ.
    eapply H; eauto.
Qed.

Global Instance SymmetricH_Symmetric_ {A : Type} (R : relationH A A) {SR : SymmetricH R} :
  Symmetric R.
  apply SymmetricH_Symmetric; eauto.
Defined.

Global Instance TransitiveH_Transitive_ {A : Type} (R : relationH A A) {SR : TransitiveH R} :
  Transitive R.
  apply TransitiveH_Transitive; eauto.
Defined.

Global Instance relationH_PER_Symmetric {A : Type} (R : relationH A A) {PR : PER R}:
  Symmetric R.
  destruct PR. apply SymmetricH_Symmetric. apply per_symm0.
Defined.

Global Instance relationH_PER_Transitive {A : Type} (R : relationH A A) {PR : PER R}:
  Transitive R.
  destruct PR. apply TransitiveH_Transitive. apply per_trans0.
Defined.

Global Instance relationH_Equivalence_PER {A : Type} (R : relationH A A) {ER : Equivalence R}:
  PER R.
  destruct ER. split; eauto.
Defined.

(** ** subrelationH *)
Section SubRelationH.

  Lemma subrelationH_Reflexive {A B: Type} (R: relationH A B): R ⊑ R.
  Proof.
    intros!; auto.
  Qed.

  Lemma subrelationH_antisym {A B: Type} (R S: relationH A B) `{R ⊑ S} `{S ⊑ R}: R ≡ S.
  Proof.
    split; auto.
  Qed.

  Lemma subrelationH_trans {A B: Type} (R S T: relationH A B)
         `{R ⊑ S} `{S ⊑ T} : R ⊑ T.
  Proof.
    intros!; auto.
  Qed.

  Lemma subrelationH_refl_eq {A: Type} (R: relationH A A) (H : Reflexive R) : (@eq A) ⊑ R.
  Proof.
    intros!.
    rewrite H0. cbn. apply H.
  Qed.

End SubRelationH.

Section RelationEqRel.

  (* [eq_rel] is an equivalence relation *)
  Global Instance eq_rel_Reflexive {A B} : Reflexive (@eq_rel A B).
  Proof.
    red. unfold eq_rel, subrelationH. tauto.
  Qed.

  Global Instance eq_rel_Symmetric {A B} : Symmetric (@eq_rel A B).
  Proof.
    red. unfold eq_rel, subrelationH. tauto.
  Qed.

  Global Instance eq_rel_Transitive {A B} : Transitive (@eq_rel A B).
  Proof.
    red. unfold eq_rel, subrelationH. intros.
    destruct H, H0. split; eauto.
  Qed.

  Global Instance eq_rel_Equiv {A B} : Equivalence (@eq_rel A B).
  Proof.
    split; typeclasses eauto.
  Qed.

  Global Instance eq_rel_Proper {A B} : Proper (eq_rel ==> eq_rel ==> iff) (@eq_rel A B).
  Proof.
    intros ? ? EQ1 ? ? EQ2.
    rewrite EQ1,EQ2; reflexivity.
  Qed.

End RelationEqRel.

Section RelationCompose.

  (* [eq] define identities *)
  Lemma eq_id_r: forall {A B : Type} (R : relationH A B),
    ((@eq B) ∘ R) ≡ R.
  Proof.
    split; intros!.
    - cbn in *. destruct H as (b & HR & EQ).
      rewrite <- EQ. assumption.
    - cbn. exists y. split; auto.
  Qed.

  Lemma eq_id_l: forall {A B} (R : relationH A B),
      R ∘  (@eq A) ≡ R.
  Proof.
    split; intros!.
    - cbn in *. destruct H as (b & EQ & HR).
      rewrite EQ. assumption.
    - cbn. exists x. split; auto.
  Qed.

  Lemma R_id_PER :
    forall {A} (R : relationH A A), PER R -> R ∘ R ≡ R.
  Proof.
    intros; split; intros * x y HR; intuition.
    destruct HR as (? & ? & ?). etransitivity; eauto.
    esplit; split; eauto. etransitivity. symmetry; eauto. eauto.
  Qed.

  (* Composition is associative *)

  Lemma compose_assoc: forall {A B C D} (R : relationH A B) (S : relationH B C) (T : relationH C D),
      T ∘ S ∘ R ≡ T ∘ (S ∘ R).
  Proof.
    split; intros!; cbn in *.
    - repeat destruct H. repeat destruct H0.
      repeat (eexists; split; eauto).
    - repeat destruct H. repeat destruct H0.
      repeat (eexists; split; eauto).
  Qed.

  Global Instance Proper_compose: forall A B C,
      Proper
        (eq_rel ==> eq_rel ==> eq_rel) (@rel_compose A B C).
  Proof.
    intros ? ? ? S S' EQS R R' EQR.
    split; intros ? ? EQ; destruct EQ as (? & ? & ?); econstructor; split; (apply EQR || apply EQS); eauto.
  Qed.

End RelationCompose.

Section TransposeFacts.

  #[local]
   Instance transpose_Reflexive {A} (R : relationH A A) {RR: Reflexive R} : Reflexive † R | 100.
  Proof.
    red. intros x. apply RR.
  Qed.

  #[local]
  Instance transpose_Symmetric {A} (R : relationH A A) {RS: Symmetric R} : Symmetric † R | 100.
  Proof.
    red; intros x; unfold transpose; intros. apply SymmetricH_Symmetric in RS.
    apply RS. assumption.
  Qed.

  #[local]
  Instance transpose_Transitive {A} (R : relationH A A) {RT : Transitive R} : Transitive † R | 100.
  Proof.
    red; intros x; unfold transpose; intros.
    apply TransitiveH_Transitive in RT.
    unfold TransitiveH in RT.
    specialize (RT z y x). apply RT; eauto.
  Qed.

  (* [transpose] is a functor (from the opposite category into itself) *)
  Lemma transpose_eq {A: Type}
    : † (@eq A) ≡ (@eq A).
  Proof.
    split; unfold transpose; intros!; subst; auto.
  Qed.

  Lemma transpose_sym {A : Type} (R : relationH A A) {RS: Symmetric R}
    : † R ≡ R.
  Proof.
    unfold transpose; split; intros!; cbn in *.
    apply SymmetricH_Symmetric in RS. red in RS.
    apply (RS y x). assumption.
    apply SymmetricH_Symmetric in RS. red in RS.
    apply (RS x y). assumption.
  Qed.

  Lemma transpose_compose {A B C : Type}
        (R : relationH A B) (S : relationH B C)
    : † (S ∘ R) ≡ (†R ∘ †S).
  Proof.
    split; unfold transpose; cbn; intros!; cbn in *.
    - destruct H as (b & HR & HS). exists b. tauto.
    - destruct H as (b & HR & HS). exists b. tauto.
  Qed.

  Global Instance Proper_transpose {A B : Type}
    : Proper (eq_rel ==> eq_rel) (@transpose A B).
  Proof.
    intros ? ? EQ; split; unfold transpose; intros!; apply EQ; auto.
  Qed.

  (* [transpose] is an involution *)
  Lemma transpose_involution : forall {A B} (R : relationH A B),
      † † R ≡ R.
  Proof.
    intros A B R.
    split.
    - unfold subrelationH. unfold transpose. tauto.
    - unfold subrelationH, transpose. tauto.
  Qed.

  Lemma transpose_inclusion : forall {A B} (R1 : relationH A B) (R2 : relationH A B),
      R1 ⊑ R2 <-> († R1 ⊑ † R2).
  Proof.
    intros A B R1 R2.
    split.
    - intros HS.
      unfold subrelationH, transpose in *. eauto.
    - intros HS.
      unfold subrelationH, transpose in *. eauto.
  Qed.

  Global Instance transpose_Proper :forall A B, Proper (@eq_rel A B ==> eq_rel) (@transpose A B).
  Proof.
    intros A B R1 R2 (Hab & Hba).
    split.
    - apply transpose_inclusion in Hab. assumption.
    - apply transpose_inclusion in Hba. assumption.
  Qed.

  (* [transpose] is monotone *)
  Lemma transpose_monotone
         {A B} (R S: relationH A B) `{R ⊑ S}
    : †R ⊑ †S.
  Proof.
    unfold transpose; intros!.
    apply H. auto.
  Qed.

End TransposeFacts.

Section ProdRelFacts.

  (* [prod_rel] preserves the structure of equivalence relations (what does one call it for a [bifunctor]?) *)
  Section Equivalence.
    Context {R S : Type}.
    Context (RR : relationH R R).
    Context (SS : relationH S S).

    Global Instance prod_rel_refl `{Reflexive _ RR} `{Reflexive _ SS} : Reflexive (RR ⊗ SS).
    Proof.
      intros []. apply ReflexiveH_Reflexive in H. apply ReflexiveH_Reflexive in H0.
      cbn. split. apply H. apply H0.
    Qed.

    Global Instance prod_rel_sym `{Symmetric _ RR} `{Symmetric _ SS}  : Symmetric (RR ⊗ SS).
    Proof.
      intros ? ? ?. apply SymmetricH_Symmetric in H. apply SymmetricH_Symmetric in H0.
      destruct x; destruct y; cbn in *. destruct H1. split.
      - unfold SymmetricH in H. apply H. auto.
      - unfold SymmetricH in H0. apply H0. auto.
    Qed.

    Global Instance prod_rel_trans `{Transitive _ RR} `{Transitive _ SS}  : Transitive (RR ⊗ SS).
    Proof.
      intros!.
      apply TransitiveH_Transitive in H. apply TransitiveH_Transitive in H0.
      unfold TransitiveH in *.
      inversion H1; inversion H2; subst; eauto; inversion H9; subst.
      split. inversion H9.  eapply H;  eauto.
      eapply H0; eauto.
    Qed.

    Global Instance prod_rel_eqv `{Equivalence _ RR} `{Equivalence _ SS} : Equivalence (RR ⊗ SS).
    Proof.
      constructor; typeclasses eauto.
    Qed.

    Global Instance prod_rel_PER `{PER _ RR} `{PER _ SS} : @PER _ (RR ⊗ SS).
    Proof.
      constructor. destruct H, H0.
      eapply SymmetricH_Symmetric.
      eapply prod_rel_sym.
      eapply TransitiveH_Transitive.
      eapply prod_rel_trans.
    Qed.

  End Equivalence.

  Section Zigzag.

    Lemma ZZC_eq_tL :
      forall {A B} (R : relationH A B),
        Zigzag R -> † R ∘ R ∘ † R ≡ † R.
    Proof.
      red. repeat intro; split; repeat intro. red in H0.
      crunch. red in H1. crunch. apply H; repeat (esplit; eauto).
      red. repeat (esplit; eauto).
    Qed.

    Lemma ZZC_eq_tR :
      forall {A B} (R : relationH A B),
        Zigzag R -> R ∘ † R ∘ R ≡ R.
    Proof.
      red. repeat intro; split; repeat intro. red in H0.
      crunch. red in H1. crunch. apply H; repeat (esplit; eauto).
      red. repeat (esplit; eauto).
    Qed.

    Lemma ZZC_not_symmetric:
      exists A (P: relationH A A), Zigzag P /\ not (SymmetricH P).
    Proof.
      intros. exists nat. exists (fun x y => (x = 1 /\ y = 10) \/ (x = 2 /\ y = 20) \/ (x = 1 /\ y = 20) \/ (x = 2 /\ y = 10)).
      assert (Zigzag (fun x y => (x = 1 /\ y = 10) \/ (x = 2 /\ y = 20) \/ (x = 1 /\ y = 20) \/ (x = 2 /\ y = 10))). {
        red. red. intros. red in H.
        destruct H as (? & ? & ?). destruct H as (? & ? & ?). red in H1.
        intuition.
      }
      split. auto.

      intuition.
      red in H0.
      specialize (H0 1 20).
      assert (H1: 1 = 1 /\ 20 = 10 \/ 1 = 2 /\ 20 = 20 \/ 1 = 1 /\ 20 = 20 \/ 1 = 2 /\ 20 = 10) by intuition.
      specialize (H0 H1).
      intuition; try inversion H0; try inversion H2; try inversion H3.
    Qed.

    (* Zarrad and Gumm seems to suggest that difunctionality with reflexivity *and
      symmetry* implies transitivity (see page 15 linked below), but we see here
      that we only need reflexivity.
      [https://hal.inria.fr/hal-01446032/document *)
    Lemma ZZC_with_reflexivity_is_transitive:
      forall A (P : relationH A A), Zigzag P -> ReflexiveH P -> TransitiveH P.
    Proof.
      intros. red in H.
      red. intros. red in H.
      apply H. red. esplit; esplit. esplit. split. 2 : red.
      eauto. eapply H; esplit; esplit. esplit. split.
      3 : apply H0. 2 : eauto.
      eapply H. 2 : eauto. esplit. split; try esplit. split.
      all : eauto.
    Qed.

    Lemma PER_is_ZZC :
      forall A (P : relationH A A), PER P -> Zigzag P.
    Proof.
      intros. destruct H. unfold SymmetricH, TransitiveH in *.
      repeat intro. destruct H as (? & ? & ?). destruct H as (? & ? & ?).
      red in H1. eapply per_trans0.
      eapply H. eapply per_trans0.
      apply per_symm0. all : eauto.
    Qed.

    Instance Proper_Zigzag {A B} : Proper (@eq_rel A B ==> iff) Zigzag.
    Proof.
      repeat intro. split; intros; repeat intro; intuition.
      apply H. apply H0. eapply Proper_compose. eauto.
      eapply Proper_compose; eauto. eapply Proper_transpose; eauto. eauto.
      apply H. apply H0. symmetry in H. eapply Proper_compose. eauto.
      eapply Proper_compose; eauto. eapply Proper_transpose; eauto. eauto.
    Defined.

    Instance Zigzag_eq {A} : Zigzag (@eq A).
    Proof.
      apply PER_is_ZZC. typeclasses eauto.
    Qed.

    (* Pair of elements in A that share the same domain on B *)
    Definition left_inj {A B : Type} (R : relationH A B) : relationH A A :=
      † R ∘ R.

    (* Pair of elements in B that share the same domain on A *)
    Definition right_inj {A B : Type} (R : relationH A B) : relationH B B :=
      R ∘ † R.

    Notation "R ←" := (left_inj R) (at level 40).
    Notation "R →" := (right_inj R) (at level 40).

    Lemma ZZC_PER_l :
      forall A B (R : relationH A B), Zigzag R -> PER (R←).
    Proof.
      intros. red in H. split.
      (* The symmetric case doesn't need the zigzag property *)
      - clear H. repeat intro. destruct H as (? & ? & ?).
        esplit; split. eauto. eauto.
      (* The transitive case does, though.*)
      - repeat intro. destruct H0 as (? & ? & ?). destruct H1 as (? & ? & ?).
        esplit; split. eapply H. esplit; split. esplit; split.
        all : eauto.
    Qed.

    Lemma ZZC_PER_r :
      forall A B (R : relationH A B), Zigzag R -> PER (R→).
    Proof.
      intros. red in H. split.
      (* The symmetric case doesn't need the zigzag property *)
      - clear H. repeat intro. destruct H as (? & ? & ?).
        esplit; split. red. eauto. eauto.
      (* The transitive case does, though.*)
      - repeat intro. destruct H0 as (? & ? & ?). destruct H1 as (? & ? & ?).
        esplit; split. eauto. eapply H. esplit; split. esplit; split.
        all : eauto.
    Qed.

    Lemma ZZC_r :
      forall {A B} (R : relationH A B),
        Zigzag R -> Zigzag (R→).
    Proof.
      intros.
      apply PER_is_ZZC. apply ZZC_PER_r. auto.
    Qed.

    Lemma ZZC_l :
      forall {A B} (R : relationH A B),
        Zigzag R -> Zigzag (R←).
    Proof.
      intros.
      apply PER_is_ZZC. apply ZZC_PER_l. auto.
    Qed.

    Lemma ZZC_l_Symmetric :
      forall {A B} (R : relationH A B),
        Symmetric (R←).
    Proof.
      intros.
      red. intros * (? & ? & ?).
      esplit; split; eauto.
    Qed.

    Lemma ZZC_r_Symmetric :
      forall {A B} (R : relationH A B),
        Symmetric (R→).
    Proof.
      intros.
      red. intros * (? & ? & ?).
      esplit; split; eauto.
    Qed.

    Lemma Transitive_injL_iff :
      forall {A B} (R : relationH A B),
        Transitive (R←) <->
          (forall a a' b, R a b -> R a' b ->
              forall a'' b', R a' b' -> R a'' b' ->
                  exists b'', R a b'' /\ R a'' b'').
    Proof.
      intros.
      split; intros. eapply H. esplit; split. eauto. eauto.
      esplit; split; eauto.
      repeat intro. destruct H0 as (? & ? & ?). destruct H1 as (? & ? & ?).
      eapply H; eauto.
    Qed.

  End Zigzag.

  (* [prod_rel] is monotone in both parameters *)
  Lemma prod_rel_monotone
         {A B C D: Type} (R R': relationH A B) (S S': relationH C D)
         `{R ⊑ R'} `{S ⊑ S'}
  : R ⊗ S ⊑ R' ⊗ S'.
  Proof.
    intros!. destruct x, y. repeat red. repeat red in H1. destruct H1.
    split.
    - apply H. assumption.
    - apply H0. assumption.
  Qed.

  (* [prod_rel] is a bifunctor *)
  Lemma prod_rel_eq : forall (A B:Type),  (@eq A) ⊗ (@eq B) ≡ @eq (A * B).
  Proof.
    intros.
    unfold eq_rel; split; unfold subrelationH; intros.
    - destruct x, y. repeat red in H. destruct H. cbn.  subst; reflexivity.
    - destruct x; destruct y. cbn in H. repeat red. inversion H. split; reflexivity.
  Qed.

  Definition prod_fst_rel {A B : Type} (R : relationH (A * B) (A * B)) :
    relationH A A :=
    fun x y => forall (b1 b2 : B), R  (x, b1) (y, b2).

  Definition prod_snd_rel {A B : Type} (R : relationH (A * B) (A * B)) :
    relationH B B :=
    fun x y => forall (a1 a2 : A), R  (a1, x) (a2, y).

  Lemma prod_inv (A B : Type) :
    forall (R : relationH (A * B) (A * B)) (x1 x2 : A) (y1 y2 : B),
        prod_fst_rel R x1 x2 /\ prod_snd_rel R y1 y2 ->
        R (x1, y1) (x2, y2).
  Proof.
    intros.
    destruct H. unfold prod_fst_rel, prod_snd_rel in *. cbn in *.
    apply H0.
  Qed.

  Lemma prod_compose {A B C D E F: Type}
        (R: relationH A B) (S: relationH B C)
        (T: relationH D E) (U: relationH E F)
    : (S ∘ R) ⊗ (U ∘ T) ≡ (S ⊗ U) ∘ (R ⊗ T).
  Proof.
    split; intros!.
    - destruct x, y. repeat red. repeat red in H. destruct H.
      unfold fst, snd. cbn in H, H0.
      edestruct H as (b & HR & HS).
      edestruct H0 as (e & HT & HU).
      exists (b, e). split; cbn; split; eauto.
    - destruct x, y. repeat red. repeat red in H. destruct H.
      unfold fst, snd in H. destruct H.
      cbn.
      split. exists (fst x). split.
      destruct x. cbn. cbn in H. inversion H ; inversion H0; subst. tauto.
      inversion H; inversion H0; inversion H8; subst. inversion H8. subst.
      cbn; auto.
      inversion H; inversion H0. subst. inversion H8. subst.
      esplit. split; eauto.
  Qed.

  Global Instance Proper_prod_rel {A B C D}: Proper (eq_rel ==> eq_rel ==> eq_rel) (@prod_rel A B C D).
  Proof.
    intros!. split; intros!; destruct x1, y1; cbn in *; destruct H1; split;
    try apply H; try apply H0; eauto.
  Qed.

  (* Distributivity of [transpose] over [prod_rel] *)
  Lemma transpose_prod {A B C D: Type}
        (R: relationH A B) (S: relationH C D)
    : † (S ⊗ R) ≡ (†S ⊗ †R).
  Proof.
    split; unfold transpose; cbn; intros!; destruct x, y; cbn in *;
    destruct H; split; eauto.
  Qed.
End ProdRelFacts.


Section SumRelFacts.

  (* [sum_rel] preserves the structure of equivalence relations (what does one call it for a [bifunctor]?) *)
  Section Equivalence.
    Context {A B : Type}.
    Context (R : relationH A A).
    Context (S : relationH B B).

    Global Instance sum_rel_refl {RR: Reflexive R} {SR: Reflexive S} : Reflexive (R ⊕ S).
    Proof.
      intros []. apply ReflexiveH_Reflexive in RR.
      apply ReflexiveH_Reflexive in SR.
      cbn.
      constructor. apply RR.
      constructor. apply SR.
    Qed.

    Global Instance sum_rel_sym {RS: Symmetric R} {SS: Symmetric S} : Symmetric (R ⊕ S).
    Proof.
      intros ? ? ?. apply SymmetricH_Symmetric in RS.
      apply SymmetricH_Symmetric in SS.
      destruct x, y.
      - constructor. inversion H. subst. apply RS. auto.
      - inversion H.
      - inversion H.
      - constructor. inversion H. subst. apply SS. auto.
    Qed.

    Global Instance sum_rel_trans {RT: Transitive R} {ST: Transitive S}  : Transitive (R ⊕ S).
    Proof.
      intros!.
      apply TransitiveH_Transitive in RT. apply TransitiveH_Transitive in ST.
      unfold TransitiveH in *.
      destruct x, y, z; try contradiction; inversion H; inversion H0; subst.
      cbn in *.
      constructor. eauto. constructor. eauto.
    Qed.

    Global Instance sum_rel_eqv {RE: Equivalence R} {SE: Equivalence S} : Equivalence (R ⊕ S).
    Proof.
      constructor; typeclasses eauto.
    Qed.

  End Equivalence.

  (* [sum_rel] is monotone in both parameters *)
  Lemma sum_rel_monotone
         {A B C D: Type} (R R': relationH A B) (S S': relationH C D)
         `{R ⊑ R'} `{S ⊑ S'}
    : R ⊕ S ⊑ R' ⊕ S'.
  Proof.
    intros!; destruct x, y; repeat red; repeat red in H1;
    inversion H1; subst; constructor; eauto.
  Qed.

  Lemma sum_rel_eq : forall (A B: Type),  @eq A ⊕ @eq B ≡ @eq (A + B).
  Proof.
    intros. red.
    split; repeat intro; eauto.
    inversion H; subst; auto; try reflexivity.
    subst. destruct y; constructor; eauto.
  Qed.

  Lemma sum_compose {A B C D E F: Type}
        (R: relationH A B) (S: relationH B C)
        (T: relationH D E) (U: relationH E F)
  : (S ∘ R) ⊕ (U ∘ T) ≡ (S ⊕ U) ∘ (R ⊕ T).
  Proof.
    split; intros!.
    - destruct x, y; inv H.
      destruct H2 as (? & ? & ?); eexists; eauto.
      destruct H2 as (? & ? & ?); eexists; eauto.
    - destruct H as (? & H1 & H2); inv H1; inv H2.
      econstructor; eexists; eauto.
      econstructor; eexists; eauto.
  Qed.

  Global Instance Proper_sum_rel {A B C D}: Proper (eq_rel ==> eq_rel ==> eq_rel) (@sum_rel A B C D).
  Proof.
    intros!.
    split; intros!; destruct x1, y1; cbn in *; try inversion H1;
      try apply H; try apply H0; eauto; subst; inversion H1; subst;
        try econstructor; try apply H; try apply H0; eauto.
  Qed.

(*    [sum_rel] is a bifunctor *)

(* Note: we also have associators and unitors, forming a monoidal category.
    See [CategoryRelation.v] if needed. *)

  (* Distributivity of [transpose] over [sum_rel] *)
  Lemma transpose_sum {A B C D: Type}
        (R: relationH A B) (S: relationH C D)
    : † (S ⊕ R) ≡ (†S ⊕ †R).
  Proof.
    split; unfold transpose; cbn; intros!; destruct x, y; cbn in *;
      try inversion H; eauto; subst; inversion H; subst; try econstructor; eauto.
  Qed.

End SumRelFacts.

Lemma PER_reflexivityH1 : forall {A:Type} (R : relationH A A) (RS: SymmetricH R) (RT: TransitiveH R)
                            (a b : A), R  a b -> R a a.
Proof.
  intros.
  assert (R  b a). { specialize (RS a b). apply RS. assumption. }
  specialize (RT a b a). apply RT; auto.
Qed.

Lemma PER_reflexivityH2 : forall {A:Type} (R : relationH A A) (RS: SymmetricH R) (RT: TransitiveH R)
                            (a b : A), R  b a -> R a a.
Proof.
  intros.
  assert (R a b). { specialize (RS b a). apply RS. assumption. }
  specialize (RT a b a). apply RT; auto.
Qed.

Ltac PER_reflexivityH :=
  match goal with
  | [ H : ?R  ?X ?Y |- ?R  ?X ?X ] =>  eapply PER_reflexivityH1; eauto
  | [ H : ?R  ?Y ?X |- ?R  ?X ?X ] =>  eapply PER_reflexivityH2; eauto
  end; try apply per_symm ; try apply per_trans.


Definition diagonal_prop {A : Type} (P : A -> Prop) : relationH A A :=
  fun x y => (P  x /\ P y).

Lemma diagonal_prop_SymmetricH {A : Type} (P : A -> Prop) : SymmetricH (diagonal_prop P).
Proof.
  red. intros a1 a2 H.
  cbn in *. unfold diagonal_prop in *. tauto.
Qed.

Lemma diagonal_prop_TransitiveH {A : Type} (P : A -> Prop) : TransitiveH (diagonal_prop P).
Proof.
  red. intros.
  cbn in *. unfold diagonal_prop in *.
  tauto.
Qed.

Lemma diagonal_prop_PER {A : Type} (P : A -> Prop) : PER (diagonal_prop P).
Proof.
  constructor.
  red. intros.
  cbn in *. unfold diagonal_prop in *; tauto.
  red. intros.
  cbn in *. unfold diagonal_prop in *; tauto.
Qed.
