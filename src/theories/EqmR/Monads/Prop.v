(** *EqmR-related laws for the prop monad. *)

(* begin hide *)
From Coq Require Import
     Lia
     Setoid
     Morphisms.

From ExtLib Require Import
     Structures.Monad Structures.MonadState.

From ITree Require Import
     Basics.Basics
     Basics.CategoryOps
     Basics.HeterogeneousRelations.

From ITree Require Import
     EqmR.EqmRMonad
     Basics.Tacs.

Import ITree.Basics.Basics.Monads.
Import CatNotations.
Local Open Scope cat_scope.
Local Open Scope cat.

Import RelNotations.
Local Open Scope relationH_scope.
(* end hide *)

(* Trying to define the EqmR version of PropM

   Problems:
   1. What does [eqmR R PA PB] mean?
        "equal propositions, modulo R"

    PA <= A

    PB <= B

    R <= (A * B)

    PA * PB  <= R <= (A * B)

   Questions:
     -  must it be the case that [eq_rel (eqmR A A A) (m A)]  ?
     -  or would only one inclusion suffice?  (m A) <2= (eqmR A A A)
*)

(* Nondeterminism monad. *)
Definition PropM (X: Type) : Type := X -> Prop.

Definition ret_ (A:Type) : A -> (PropM A) :=
  fun (x y:A) => x = y.

Program Definition bind_ (A B : Type) (ma : PropM A) : (A -> PropM B) -> PropM B :=
  (fun (k : A -> PropM B) (b:B) => exists (a:A), ma a /\ (k a b)).

Global Instance MonadPropM : Monad PropM.
split.
- exact ret_.
- exact bind_.
Defined.

Section PropM.

  Definition eqmR_sched {A B : Type} (R : A -> B -> Prop) f g : (PropM A) -> (PropM B) -> Prop:=
    fun (ma : PropM A)  (mb : PropM B) =>
      (forall (a:A), ma a -> R a (f a) /\ mb (f a)) /\
      (forall (b:B), mb b -> R (g b) b /\ ma (g b)).

  Definition eqmR_' {A B : Type} (R : A -> B -> Prop) : (PropM A) -> (PropM B) -> Prop:=
    fun (ma : PropM A)  (mb : PropM B) =>
      exists f g, eqmR_sched R f g ma mb.

  Ltac rel_crunch:=
    match goal with
    | [H : forall _, ?ma _ -> ?R _ _ /\ _ , H' : ?ma _ |- ?R _ _] =>
      specialize (H _ H'); destruct H; eauto
    | [H : forall _, ?ma _ -> _ /\ ?mb _ , H' : ?ma _ |- ?mb _] =>
      specialize (H _ H'); destruct H; eauto
    | [H : forall _, ?ma _ -> ?R _ _ /\ _ , H' : ?ma _ |- _] =>
      specialize (H _ H'); destruct H; eauto
    end.

  Lemma eqmR_rel_conj_ :
    forall (A B : Type) (R1 R2 : relationH A B) (ma : PropM A) (mb : PropM B) f g,
      eqmR_sched R1 f g ma mb ->
      eqmR_sched R2 f g ma mb ->
      eqmR_sched (fun (x : A) (y : B) => R1 x y /\ R2 x y) f g ma mb.
  Proof.
    unfold eqmR_sched; intros * [] [].
    split; intros; split; try split; rel_crunch.
  Qed.

  Definition eqmR_ {A B : Type} (R : A -> B -> Prop) : (PropM A) -> (PropM B) -> Prop:=
    fun (ma : PropM A)  (mb : PropM B) =>
      (forall (a:A), ma a -> exists (b:B), R a b /\ mb b) /\
      (forall (b:B), mb b -> exists (a:A), R a b /\ ma a).

  From Coq Require Import Logic.ClassicalDescription.

From Coq Require Import
     Program
     Setoid
     Morphisms
     RelationClasses
     micromega.Lia.
  (* Needs classical assumption *)
  Lemma eqmR_eqmR_'_logically_equivalent :
    forall A B (R : A -> B -> Prop) pa pb,
        (forall x : A, exists ! y : B, R x y) ->
        (forall x0 : B, exists ! y : A, flip R x0 y) ->
      (eqmR_' R pa pb <-> eqmR_ R pa pb).
  Proof.
    pose proof @unique_choice as UC.
    intros * R_func fR_func.
    unfold eqmR_', eqmR_, eqmR_sched.
    split.
    (* sched imples non-sched def *)
    - intros SCH.
      crunch; intros; rel_crunch; crunch.
    (* non-sched implies sched def *)
    - intros D.
      crunch.
      destruct (UC A B R R_func) as (f & Rf).
      destruct (UC _ _ _ fR_func) as (g & Rg).
      clear UC. exists f, g.
      split; intros; split; eauto. 2 : apply Rg.
      + destruct (H _ H1) as (b & HR & HP).
        assert (R a (f a)) by eauto.
        edestruct (R_func a). red in H3. destruct H3.
        pose proof (H4 _ H2).
        pose proof (H4 _ HR). subst. auto.
      + destruct (H0 _ H1) as (? & ? & ?).
        assert (R (g b) b) by apply Rg.
        edestruct (fR_func b). red in H5. destruct H5.
        pose proof (H6 _ H2).
        pose proof (H6 _ H4).
        subst. eauto.
  Qed.

  Instance eqmR_PropM : EqmR PropM :=
    { eqmR := @eqmR_ }.

  Ltac destruct_all :=
    repeat match goal with
          | [ H : exists X, _ |- _ ] => destruct H
          | [ H : _ /\ _ |- _ ] => destruct H
          | [ H : _ \/ _ |- _ ] => destruct H
          | [ |- _ /\ _ ] => split
          end.

  Ltac PER_symmetry :=
    match goal with
    | [ H : SymmetricH ?R,
        H1 : ?R ?x ?y
        |- ?R ?y ?x ] => apply (H _ H1)
    end.

  Ltac pintro := repeat intro; unfold eqmR_ in *; destruct_all; intros.
  Ltac propM y a :=
    match goal with
    | [y : PropM ?A, H : forall a : ?A, y a -> exists b : ?B, _ /\ _,
        a : ?A, H2 : y a |- _] => destruct (H _ H2) as (? & ? & ?)
    end.
  Ltac per :=
    match goal with
    | [ H : ?R ?x ?y |- ?R ?y ?x] => symmetry; auto
    | [ H: ?R ?x ?y, H' : ?R ?y ?z |- ?R ?x ?z] => etransitivity; [apply H | apply H']
    end.
  Ltac pexists := eexists; split ; [ | eauto]; try per.

  (* Instance eqmR_transport_refl_ND: eqmR_transport_refl_ PropM. *)
  (* Proof. *)
  (*   repeat intro. repeat red. split; eauto. *)
  (* Qed. *)

  Lemma eqmR_Proper_eq_ND:
    forall A B : Type, Proper (eq_rel ==> eqmR (@eq A) ==> eqmR (@eq B) ==> flip impl) eqmR.
  Proof.
    repeat intro. repeat red. repeat red in H0, H1, H2. crunch.
    intros. propM x0 a. subst. propM x0 x2. subst. propM y0 x3. subst.
    eexists. split. apply H. eauto.
    clear -H4 H8 H6 H9 H7 H10.
    propM y1 x2. subst; eauto.
    intros. propM x1 b. subst. propM y1 x2. propM y0 x3.
    eexists. split. apply H. eauto.
    clear -H9 H5. propM y0 x3. subst; auto.
  Qed.

  Lemma mayRet_PropM {A:Type} (ma : PropM A) (a : A) : (ma a) <-> mayRet PropM ma a.
  Proof.
    split.
    - intros HM.
      do 2 red. repeat intro.
      repeat red in EQ.
      destruct EQR.
      cbn in *.
      specialize (H a HM).
      destruct H as (b & RB & MAB).
      PER_reflexivityH.
    - intros HM.
      repeat red in HM.
      epose (fun a => ma a) as Q.
      assert (eqmR (diagonal_prop Q) ma ma).
      { repeat red. unfold diagonal_prop. split; cbn; intros; eauto. }
      specialize (HM (diagonal_prop Q) (diagonal_prop_PER Q) H).
      destruct H as (HA & HB). apply HM.
  Qed.

  Instance RetInv_PropM: RetInv PropM.
  Proof.
    repeat intro; cbn in *; eauto.
    red in H. crunch. unfold ret_ in *.
    specialize (H a1 eq_refl). destruct H. destruct H. subst; auto.
  Qed.

  Instance MayRetBindInv_PropM : MayRetBindInv PropM.
  Proof.
    repeat intro; cbn in *; eauto.
    eapply mayRet_PropM in H. red in H.
    setoid_rewrite <- mayRet_PropM; eauto.
  Qed.

  Instance FmapInv_PropM : FmapInv_mayRet PropM.
  Proof.
    repeat intro; cbn in *; eauto.
    unfold eqmR_ in *.
    destruct H. unfold bind_, ret_ in *.
    split; intros; unfold mayRet_rel;
      setoid_rewrite <- mayRet_PropM.
    + specialize (H (f1 a)).
      edestruct H as (?&?&?&?&?).
      eexists; eauto. subst; eauto.
    + specialize (H0 (f2 b)).
      edestruct H0 as (?&?&?&?&?).
      eexists; eauto. subst; eauto.
  Qed.

  (* FmapInvRet does not hold for PropM. Counterexample:
  In general,
  ma ~ R ~ mb -> a \in ma -> b \in mb -> R a b doesn't hold for the PropM because
  if your sets are : [true, false] [false, true] and you take boolean equality as R,
  the property does not hold.
  *)

  Lemma FmapInvRet_PropM_counter: ~(FmapInvRet PropM).
  Proof.
    repeat intro. repeat red in H.
    specialize (H bool bool (fun x => True) (fun x => negb x) id eq).
    cbn in *. unfold bind_ in *. unfold eqmR_ in H.
    edestruct H with (a := true); cycle 1.
    rewrite <- mayRet_PropM; eauto.
    specialize (H0 _ eq_refl). destruct H0 as (?&?&?). subst. inv H2.
    split; intros; crunch; eauto; destruct x; eauto; try inv H0.
    destruct b; eauto. red in H1; subst. eexists; eauto. split; eauto.
    eexists; eauto. split; eauto. Unshelve. 4 : exact false.  cbn. reflexivity.
    inv H1.
    red in H1. subst. exists false. split; eauto; cycle 1.
    exists true.  split; auto.
    reflexivity.
  Qed.

  Instance transp_refl_: TransportReflexive PropM.
  repeat intro. repeat red. split; eauto.
  Qed.

  Instance transp_symm_ : TransportSymmetric PropM.
    repeat red.
    intros.  destruct H0 as (Q1 & Q2); split; intros.
    - specialize (Q2 _ H0); destruct Q2 as (?&?&?); eauto.
    - specialize (Q1 _ H0); destruct Q1 as (?&?&?); eauto.
  Qed.

  Instance transp_trans_ : TransportTransitive PropM.
    repeat red.
    intros.
    destruct H0 as (Q1 & Q2);
      destruct H1 as (Q1' & Q2'); split; intros.
    edestruct (Q1 _ H0) as (?&?&?).
    edestruct (Q1' _ H2) as (?&?&?).
    exists x1; eauto.
    edestruct (Q2' _ H0) as (?&?&?).
    edestruct (Q2 _ H2) as (?&?&?).
    exists x1; eauto.
  Qed.

  Instance lift_trans_ : LiftTranspose PropM.
    repeat red. intros; split; repeat intro; destruct H as (?&?); split; intros; eauto.
  Qed.

  Instance fmapfst_ : FmapFst PropM.
  repeat red. intros; split; repeat intro; destruct H,H0 as (?&?); destruct H0;
    intros; eauto;
    repeat red in H2; subst.
  specialize (H _ H0); destruct H as(?&?&?); inv H; unfold fmap; eexists; split; eauto; repeat red; eexists; split; eauto; repeat red; auto.
  specialize (H1 _ H0); destruct H1 as(?&?&?); inv H1; unfold fmap; eexists; split; eauto; repeat red; eexists; split; eauto; repeat red; auto.
  Qed.

  Instance fmapsnd_: FmapSnd PropM.
  repeat red. intros; split; repeat intro; destruct H,H0 as (?&?); destruct H0;
    intros; eauto;
    repeat red in H2; subst.
  specialize (H _ H0); destruct H as(?&?&?); inv H; unfold fmap; eexists; split; eauto; repeat red; eexists; split; eauto; repeat red; auto.
  specialize (H1 _ H0); destruct H1 as(?&?&?); inv H1; unfold fmap; eexists; split; eauto; repeat red; eexists; split; eauto; repeat red; auto.
    Qed.

  Instance fmapinl_: FmapInl PropM.
  repeat red. intros; split; repeat intro; destruct H,H0 as (?&?); destruct H0;
    intros; eauto;
    repeat red in H2; subst.
  specialize (H _ H0); destruct H as(?&?&?); unfold fmap; eexists; split; eauto; repeat red; eexists; split; eauto; repeat red; auto.
  specialize (H1 _ H0); destruct H1 as(?&?&?); unfold fmap; eexists; split; eauto; repeat red; eexists; split; eauto; repeat red; auto.
  Qed.

  Instance fmapinr_: FmapInr PropM.
  repeat red. intros; split; repeat intro; destruct H,H0 as (?&?); destruct H0;
    intros; eauto;
    repeat red in H2; subst.
  specialize (H _ H0); destruct H as(?&?&?); unfold fmap; eexists; split; eauto; repeat red; eexists; split; eauto; repeat red; auto.
  specialize (H1 _ H0); destruct H1 as(?&?&?); unfold fmap; eexists; split; eauto; repeat red; eexists; split; eauto; repeat red; auto.
  Qed.

  Instance relcomp_:RelComp PropM.
    split; intros; cbn in *; pintro.
    - propM ma a. propM mb x. eexists; split; eauto.
      econstructor; eauto.
    - propM mc b. clear H0 H2. propM mb x. eexists; split; eauto.
      econstructor; eauto.
  Qed.

  Instance relsum_: RelSum PropM.
    repeat red. intros; split; repeat intro; repeat red in H.
    - destruct H as (?&?); unfold fmap, bind, ret; repeat red; cbn; unfold bind_, ret_.
      split; eauto; intros.
      + crunch; eauto.
        propM m1 x. inv H5.
        specialize (H2 _ H6). destruct H2 as (?&?&?).
        inv H2; eauto.
        exists (f2 a2); eauto.
        exists (g2 b2); eauto.
      + crunch; eauto.
        propM m2 x. inv H5.
        specialize (H _ H6). destruct H as (?&?&?).
        inv H; eauto.
        exists (f1 a1); eauto.
        exists (g1 b1); eauto.
    - repeat red.
      specialize (H (A1 + B1)%type (A2 + B2)%type inl inl inr inr (RA ⊕ RB)).
      assert (inl_P :ProperH (respectfulH A1 A2 (A1 + B1) (A2 + B2) RA (RA ⊕ RB)) inl inl) by
        (repeat intro; constructor; eauto).
      assert (inr_P: ProperH (respectfulH B1 B2 (A1 + B1) (A2 + B2) RB (RA ⊕ RB)) inr inr) by
        (repeat intro; constructor; eauto).
      specialize (H inl_P inr_P).
      destruct H as (?&?); unfold fmap, bind, ret in *; repeat red in H; cbn; unfold bind_, ret_ in *.
      cbn in *. unfold bind_, ret_ in *.
      split; intros; eauto.
      + specialize (H a).
        assert (AUX : exists a0 : A1 + B1, m1 a0 /\ match a0 with
                                     | inl a => inl a
                                     | inr b => inr b
                                              end = a).
        {  eexists; split; eauto. destruct a; eauto. }
        specialize (H AUX).
        destruct H as (?&?&?&?&?).
        exists x; eauto. split; eauto. destruct x; inv H3; eauto.
        all : try destruct x0; inv H5; eauto.
      + specialize (H0 b).
        assert (AUX : (exists a : A2 + B2, m2 a /\ match a with
                                    | inl a0 => inl a0
                                    | inr b => inr b
                                    end = b)).
        {  eexists; split; eauto. destruct b; eauto. }
        specialize (H0 AUX).
        destruct H0 as (?&?&?&?&?).
        exists x; eauto. split; eauto. destruct x; inv H3; eauto.
        all : try destruct x0; inv H5; eauto.
  Qed.

  Instance eqmR_Proper_proper_rel:
    forall A B : Type, Proper (eq_rel (A := A) (B := B)==> eq_rel) eqmR.
  Proof.
    repeat intro. destruct H; split; intro.
    intros. repeat red in H1; destruct H1; split; intros; eauto.
    propM x0 a. eexists x1; eauto.
    propM y0 b. eexists x1; eauto.
    intros. repeat red in H1; destruct H1; split; intros; eauto.
    propM x0 a. eexists x1; eauto.
    propM y0 b. eexists x1; eauto.
  Qed.

  Instance eqmR_Proper_subRel:
    forall A B : Type, Proper (subrelationH (A := A) (B:=B) ==> subrelationH (B:=PropM B)) eqmR.
  Proof.
    repeat intro. destruct H0; split; intros.
    propM x0 a. eexists x1; eauto.
    propM y0 b. eexists x1; eauto.
  Qed.

  Instance EqmR_OKPropM_ : EqmR_OK PropM.
  Proof.
    constructor; try typeclasses eauto.
  Qed.

  Lemma eqmR_ret_PropM : forall {A1 A2 : Type} (RA : relationH A1 A2) (a1:A1) (a2:A2),
          RA a1 a2 -> eqmR RA (ret a1) (ret a2 : PropM A2).
  Proof.
    intros A1 A2 RA a1 a2 H.
    red. cbn.
    split; intros. unfold ret_ in H0. exists a2. rewrite <- H0. split; auto. reflexivity.
    unfold ret_ in H0. exists a1. rewrite <- H0. split; auto. reflexivity.
  Qed.

  Lemma bind_ret_l_PropM :
    forall (A B : Type) (f : A -> PropM B) (a : A), bind (ret a) f ≈{ eq } f a.
  Proof.
    repeat red. cbn.
      unfold bind_. cbn. unfold ret_. cbn.
      intros b1 b2 HB.
      split.
    - intros * (a2 & HA & HK). rewrite HA. exists a0. split; auto.
    - intros. exists b. split; eauto.
  Qed.

  Lemma bind_ret_r_PropM :
    forall (A : Type) (ma : PropM A), bind ma ret ≈{ eq } ma.
  Proof.
  intros; repeat red. unfold bind_. cbn.
    split.
    - unfold ret_. intros * (a & HH & HR). subst. exists a0. split; auto.
    - unfold bind_, ret_. intros. exists b.
      split; eauto.
  Qed.

  Lemma bind_bind_PropM :
    forall (A B C : Type) (ma : PropM A) (f : A -> PropM B) (g : B -> PropM C),
  bind (bind ma f) g ≈{ eq } bind ma (fun x : A => bind (f x) g).
  Proof.
  cbn. unfold bind_, ret_, eqmR_. intros. split.
  - intros * (a2 & (a & HA & HF) & HG).
    exists a0. split; eauto.
  - intros * (a2 & HA & (b & HF & HG)).
    exists b0. split; eauto.
  Qed.

  Lemma eqmR_mayRet_l_PropM : forall {A1 A2 : Type}
                        (RA : relationH A1 A2)
                        (ma1 : PropM A1) (ma2 : PropM A2)
                        (EQ : eqmR RA ma1 ma2),
      forall a1, mayRet PropM ma1 a1 -> exists a2, RA a1 a2 /\ mayRet PropM ma2 a2.
  Proof.
    intros.
    destruct EQ as (HA & HB). cbn in HA, HB.
    rewrite <- mayRet_PropM in H.
    destruct (HA _ H) as (b & HR & HM).
    exists b. split; auto. rewrite <- mayRet_PropM. auto.
  Qed.

  Lemma eqmR_mayRet_r_PropM : forall {A1 A2 : Type}
                        (RA : relationH A1 A2)
                        (ma1 : PropM A1) (ma2 : PropM A2)
                        (EQ : eqmR RA ma1 ma2),
          forall a2, mayRet PropM ma2 a2 -> exists a1, RA a1 a2 /\ mayRet PropM ma1 a1.
    intros.
    destruct EQ as (HA & HB). cbn in HA, HB.
    rewrite <- mayRet_PropM in H.
    destruct (HB _ H) as (a & HR & HM).
    exists a. split; auto. rewrite <- mayRet_PropM. auto.
  Qed.

  Lemma image_eqmR_PropM {A : Type} (ma : PropM A) : eqmR (image ma) ma ma.
  Proof.
    repeat red.
    split.
    - intros a HMA; cbn in HMA.
      exists a. split; auto. red. repeat intro.
      destruct EQR as (HX & HY).
      specialize (HX a HMA). destruct HX as (b & RB & HB).
      PER_reflexivityH. 
    - intros a HMA; cbn in HMA.
      exists a. split; auto. red. repeat intro.
      destruct EQR as (HX & HY).
      specialize (HX a HMA). destruct HX as (b & RB & HB).
      PER_reflexivityH.
  Qed.

  Lemma eqmR_bind_ProperH_PropM' :
    forall {A1 A2 B1 B2 : Type}
      (RA : relationH A1 A2)
      (RB : relationH B1 B2)
      ma1 ma2
      (kb1 : A1 -> PropM B1) (kb2 : A2 -> PropM B2),
      eqmR RA ma1 ma2 ->
      (forall (a1 : A1), mayRet PropM ma1 a1 -> forall a2, RA a1 a2 -> eqmR RB (kb1 a1) (kb2 a2))
      ->
      (forall (a2 : A2), mayRet PropM ma2 a2 -> forall a1, RA a1 a2 -> eqmR RB (kb1 a1) (kb2 a2))
      ->
      eqmR RB (bind ma1 kb1) (bind ma2 kb2).
  Proof.
    intros.
    repeat red.
    destruct H as (HX & HY).
    Opaque mayRet.
    split; intros; cbn in *.
    - destruct H as (a1 & HA1 & HK1).
      assert (mayRet PropM ma1 a1).
      { rewrite <- mayRet_PropM. apply HA1. }
      apply HX in HA1.
      destruct HA1 as (a2 & R & MA).
      specialize (H0 a1 H a2 R).
      destruct H0 as (HA & HB).
      apply HA in HK1.
      destruct HK1 as (b2 & HRB & HKB).
      exists b2. split.  auto. red. exists a2. split; auto.
  -  destruct H as (a2 & HA2 & HK2).
      assert (mayRet PropM ma2 a2).
      { rewrite <- mayRet_PropM. apply HA2. }
      apply HY in HA2.
      destruct HA2 as (a1 & R & MA).
      specialize (H1 a2 H a1 R).
      destruct H1 as (HA & HB).
      apply HB in HK2.
      destruct HK2 as (b1 & HRB & HKB).
      exists b1. split.  auto. red. exists a1. split; auto.
  Qed.

  Instance EqmRMonadLaws_PropM : EqmRMonadLaws PropM.
  constructor.
  - repeat intro ; eapply eqmR_mayRet_l_PropM; eauto.
  - repeat intro; eapply eqmR_mayRet_r_PropM; eauto.
  - repeat intro; eapply image_eqmR_PropM.
  - repeat intro; eapply eqmR_ret_PropM; eauto.
  - repeat intro; eapply eqmR_bind_ProperH_PropM'; eauto.
  - repeat intro; apply bind_ret_l_PropM; eauto.
  - repeat intro; apply bind_ret_r_PropM; eauto.
  - repeat intro; apply bind_bind_PropM; eauto.
  Qed.

ection PropM.
