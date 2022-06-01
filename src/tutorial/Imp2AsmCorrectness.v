(** * Functional correctness of the compiler *)

(** We finally turn to proving our compiler correct.

SAZ: This needs to be updated.

    We express the result as a (weak) bisimulation between
    the [itree] resulting from the denotation of the source
    _Imp_ statement and the denotation of the compiled _Asm_
    program. This weak bisimulation is a _up-to-tau_ bisimulation.
    More specifically, we relate the itrees after having
    interpreted the events contained in the trees, and run
    the resulting computation from the state monad:
    [ImpState] on the _Imp_ side, [Reg] and [Memory] on the
    _Asm_ side.

    The proof is essentially structured as followed:
    - a simulation relation is defined to relate the _Imp_
    state to the _Asm_ memory during the simulation. This
    relation is strengthened into a second one additionally
    relating the result of the denotation of an expression to
    the _Asm_ set of registers, and used during the simulation
    of expressions.
    - the desired bisimulation is defined to carry out the
    the simulation invariant into a up-to-tau equivalence after
    interpretation of events. Once again a slightly different
    bisimulation is defined when handling expressions.
    - Linking is proved in isolation: the "high level" control
    flow combinators for _Asm_ defined in [Imp2Asm.v] are
    proved correct in the same style as the elementary ones
    from [AsmCombinators.v].
    - Finally, all the pieces are tied together to prove the
    correctness.

    We emphasize the following aspects of the proof:
    - Despite establishing a termination-sensitive correctness
    result over Turing-complete languages, we have not written
    a single [cofix]. All coinductive reasoning is internalized
    into the [itree] library.
    - We have separated the control-flow-related reasoning from
    the functional correctness one. In particular, the low-level
    [asm] combinators are entirely reusable, and the high-level
    ones are only very loosely tied to _Imp_.
    - All reasoning is equational. In particular, reasoning at the
    level of [ktree]s rather than introducing the entry label and
    trying to reason at the level of [itree]s ease sensibly the pain
    by reducing the amount of binders under which we need to work.
    - We transparently make use of the heterogeneous bisimulation provided
    by the [itree] library to relate computations of _Asm_ expressions that
    return a pair of environments (registers and memory) and a [unit] value to
    ones of _Imp_ that return a single environment and an [Imp.value].
 *)

(* begin hide *)
From ITreeTutorial Require Import
     Imp Asm Utils_tutorial
     AsmCombinators Imp2Asm Fin KTreeFin Proofmode.

From Coq Require Import
     Psatz
     Strings.String
     List
     Program.Basics
     Morphisms
     ZArith
     Setoid
     Relations
     RelationClasses.

From ITree Require Import
     ITree
     ITreeFacts
     Eq.Eq
     Basics.CategorySub
     Basics.HeterogeneousRelations
     Interp.InterpFacts
     Interp.HFunctor
     EqmR.EqmRMonad
     EqmR.EqmRMonadH
     EqmR.EqmRMonadT
     Events.MapDefault.

Import ITreeNotations.

From ExtLib Require Import
     Core.RelDec
     Structures.Monad
     Structures.Maps
     Data.Map.FMapAList.

Import ListNotations.
Open Scope string_scope.

Import CatNotations.
Import RelNotations.
Local Open Scope cat_scope.
Local Open Scope itree_scope.
Local Open Scope relationH_scope.

(* end hide *)


(* ================================================================= *)
(** ** Simulation relations and invariants *)

(** The compiler is proved correct by constructing a (itree) bisimulation
    between the source program and its compilation.  The compiler does two
    things that affect the state:

      - it translates source Imp variables to Asm global variables, which should
        match at each step of computation

      - it introduces temporary local variables that name intermediate values

    As is traditional, we define, to this end, a simulation relation [Renv] and
    invariants that relate the source Imp environment to the target Asm
    environment, following the description above.

    [Renv] relates two [alist var value] environments if they act as
    equivalent maps.  This is used to relate Imp's [ImpState] environment to
    Asm's [Memory].

*)

Section Simulation_Relation.

  (** ** Definition of the simulation relations *)

  (** The simulation relation for evaluation of statements.
      The relation relates two environments of type [alist var value].
      The source and target environments exactly agree on user variables.
   *)
  Definition Renv (g_imp : Imp.env) (g_asm : Asm.memory) : Prop :=
    forall k v, alist_In k g_imp v <-> alist_In k g_asm v.

  Global Instance Renv_refl : Reflexive Renv.
  Proof.
    red. intros. unfold Renv. tauto.
  Qed.

  Global Instance Renv_Equiv : Equivalence Renv.
  Proof.
    constructor; try typeclasses eauto.
    all : constructor; repeat intro; eauto.
    red in H. symmetry in H. edestruct H; eauto.
    red in H. symmetry in H. edestruct H; eauto.
    red in H, H0. edestruct H, H0; eauto.
    red in H, H0. edestruct H, H0; eauto.
  Qed.

 (** The simulation relation for evaluation of expressions.

     The relation connects

       - the global state at the Imp level

       - the memory and register states at the Asm level

     and, additionally the returned value at the _Imp_ level. The _Asm_ side
     does not carry a [value], but a [unit], since its denotation does not
     return any [value].

     The [sim_rel] relation is parameterized by the state of the local [asm]
     environment before the step, and the name of the variable used to store the
     result.


     It enforces three conditions:
     - [Renv] on the global environments, ensuring that evaluation of expressions does
     not change user variables;

     - Agreement on the computed value, i.e. the returned value [v] is stored at
     the assembly level in the expected temporary;

     - The "stack" of temporaries used to compute intermediate results is left
       untouched.
  *)
  Definition sim_rel l_asm n: (env * value) -> (registers * (memory * unit)) -> Prop :=
    fun '(g_imp', v) '(l_asm', (g_asm', _))  =>
      Renv g_imp' g_asm' /\            (* we don't corrupt any of the imp variables *)
      alist_In n l_asm' v /\           (* we get the right value *)
      (forall m, m < n -> forall v,              (* we don't mess with anything on the "stack" *)
            alist_In m l_asm v <-> alist_In m l_asm' v).


  Lemma sim_rel_find : forall g_asm g_imp l_asm l_asm' n  v,
    sim_rel l_asm n (g_imp, v) (l_asm', (g_asm, tt)) ->
    alist_find n l_asm' = Some v.
  Proof.
    intros.
    destruct H as [_ [IN _]].
    apply IN.
  Qed.

  (* (** ** Facts on the simulation relations *) *)

  (* (** [Renv] entails agreement of lookup of user variables. *) *)
  Lemma Renv_find:
    forall g_asm g_imp x,
      Renv g_imp g_asm ->
      alist_find x g_imp = alist_find x g_asm.
  Proof.
    intros.
    destruct (alist_find x g_imp) eqn:LUL, (alist_find x g_asm) eqn:LUR; auto.
    - eapply H in LUL.
      rewrite LUL in LUR; auto.
    - eapply H in LUL.
      rewrite LUL in LUR; auto.
    - eapply H in LUR.
      rewrite LUR in LUL; inv LUL.
  Qed.

  (** [sim_rel] can be initialized from [Renv]. *)
  Lemma sim_rel_add: forall g_asm l_asm g_imp n v,
      Renv g_imp g_asm ->
      sim_rel l_asm n  (g_imp, v) (alist_add n v l_asm, (g_asm, tt)).
  Proof.
    intros.
    split; [| split].
    - assumption.
    - apply In_add_eq.
    - intros m LT v'.
      apply In_add_ineq_iff; lia.
  Qed.

  (** [Renv] can be recovered from [sim_rel]. *)
  Lemma sim_rel_Renv: forall l_asm n s1 l v1 s2 v2,
      sim_rel l_asm n (s2,v2) (l,(s1,v1)) -> Renv s2 s1 .
  Proof.
    intros ? ? ? ? ? ? ? H; apply H.
  Qed.

  Lemma sim_rel_find_tmp_n:
    forall l_asm g_asm' n l_asm' g_imp' v,
      sim_rel l_asm n  (g_imp',v) (l_asm', (g_asm', tt)) ->
      alist_In n l_asm' v.
  Proof.
    intros ? ? ? ? ? ? [_ [H _]]; exact H.
  Qed.

  (** [sim_rel] entails agreement of lookups in the "stack" between its argument *)
  (*     and the current Asm environement *)
  Lemma sim_rel_find_tmp_lt_n:
    forall l_asm g_asm' n m l_asm' g_imp' v,
      m < n ->
      sim_rel l_asm n (g_imp',v) (l_asm', (g_asm', tt)) ->
      alist_find m l_asm = alist_find m l_asm'.
  Proof.
    intros ? ? ? ? ? ? ? ineq [_ [_ H]].
    match goal with
    | |- _ = ?x => destruct x eqn:EQ
    end.
    setoid_rewrite (H _ ineq); auto.
    match goal with
    | |- ?x = _ => destruct x eqn:EQ'
    end; [| reflexivity].
    setoid_rewrite (H _ ineq) in EQ'.
    rewrite EQ' in EQ; easy.
  Qed.

  Lemma sim_rel_find_tmp_n_trans:
    forall l_asm n l_asm' l_asm'' g_asm' g_asm'' g_imp' g_imp'' v v',
      sim_rel l_asm n (g_imp',v) (l_asm', (g_asm', tt))  ->
      sim_rel l_asm' (S n) (g_imp'',v') (l_asm'', (g_asm'', tt))  ->
      alist_In n l_asm'' v.
  Proof.
    intros.
    generalize H; intros LU; apply sim_rel_find_tmp_n in LU.
    unfold alist_In in LU; erewrite sim_rel_find_tmp_lt_n in LU; eauto.
  Qed.

  (** [Renv] is preserved by assignment. *)
  (*  *)
  Lemma Renv_write_local:
    forall (k : Imp.var) (g_asm g_imp : alist var value) v,
      Renv g_imp g_asm ->
      Renv (alist_add k v g_imp) (alist_add k v g_asm).
  Proof.
    intros k m m' v HRel k' v'.
    unfold alist_add, alist_In; simpl.
    flatten_goal;
      repeat match goal with
             | h: _ = true |- _ => rewrite rel_dec_correct in h
             | h: _ = false |- _ => rewrite <- neg_rel_dec_correct in h
             end; try subst.
    - tauto.
    - setoid_rewrite In_remove_In_ineq_iff; eauto using RelDec_string_Correct.
  Qed.

  (** [sim_rel] can be composed when proving binary arithmetic operators. *)
  Lemma sim_rel_binary_op:
    forall (l_asm l_asm' l_asm'' : registers) (g_asm' g_asm'' : memory) (g_imp' g_imp'' : env)
      (n v v' : nat)
      (Hsim : sim_rel l_asm n (g_imp', v) (l_asm', (g_asm', tt)))
      (Hsim': sim_rel l_asm' (S n) (g_imp'', v') (l_asm'', (g_asm'', tt)))
      (op: nat -> nat -> nat),
      sim_rel l_asm n (g_imp'', op v v') ((alist_add n (op v v') l_asm'', (g_asm'', tt))).
  Proof.
    intros.
    split; [| split].
    - eapply sim_rel_Renv; eassumption.
    - apply In_add_eq.
    - intros m LT v''.
      rewrite <- In_add_ineq_iff; [| lia].
      destruct Hsim as [_ [_ Hsim]].
      destruct Hsim' as [_ [_ Hsim']].
      rewrite Hsim; [| auto with arith].
      rewrite Hsim'; [| auto with arith].
      reflexivity.
  Qed.

End Simulation_Relation.

(* ================================================================= *)
(** ** Bisimulation *)

(** We now make precise the bisimulation established to show the correctness of
    the compiler.  Naturally, we cannot establish a _strong bisimulation_
    between the source program and the target program: the [asm] counterpart
    performs "more steps" when evaluating expressions.  The appropriate notion
    is of course the _equivalence up to tau_. However, the [itree] structures
    are also quite different.  [asm] programs manipulate two state
    components. The simulation will establish that the [imp] global state
    corresponds to the [asm] memory, but to be able to  establish this
    correspondence, we also need to interpret the [asm] register effects.  *)

Section Bisimulation.
  Context {E C1 F D1 D2 G: Type -> Type}.
  Context {HasMemory : Memory +? E -< D1}.
  Context {HasReg : Reg +? D1 -< D2}.
  Context {HasAbort : Abort +? D2 -< G}.
  Context {HasState : ImpState +? E -< C1}.
  Context {HasFail : ImpFail +? C1 -< F}.
  Context {HasRegWf : Subevent_wf HasReg}.

  (** Definition of our bisimulation relation.

      As previously explained, the bisimulation relates (up-to-tau)
      two [itree]s after having interpreted their events.

      We additionally bake into it a simulation invariant:
      - Events are interpreted from states related by [Renv]
      - Returned values must contain related states, as well as computed datas
      related by another relation [RAB] taken in parameter.
      In our case, we will specialize [RAB] to the total relation since the trees return
      respectively [unit] and the unique top-level label [F0: fin 1].
   *)

  Section RAB.

    Definition state_invariant {A B} (RAB : A -> B -> Prop) (a : Imp.env * A) (b : Asm.registers * (Asm.memory * B))  :=
      Renv (fst a) (fst (snd b)) /\ (RAB (snd a) (snd (snd b))).

    #[global]
     Instance imp_asm_EqmRH {EE} : EqmRH (stateT env (Imp.failT (itree EE)))
                                    (stateT memory (stateT registers (Imp.failT (itree EE)))).
    Proof.
      constructor.
      intros A' B' RR ma mb. red in ma, mb. red in mb.
      exact (forall env mem reg, Renv env mem -> eqmR (m := Imp.failT (itree EE))
                                                      (state_invariant RR) (ma env) (mb mem reg)).
    Defined.

    #[global]
     Instance imp_asm_Proper_EqmR {EE} : Proper_EqmRH (@imp_asm_EqmRH EE).
    Proof.
      constructor; cbn; repeat intro; cbn in H, H0; eauto.
      { specialize (H env _ eq_refl);
          specialize (H0 mem _ eq_refl reg _ eq_refl);
          specialize (H1 _ _ reg H2).
        rewrite prod_rel_eq, sum_rel_eq in H.
        rewrite prod_rel_eq, ?sum_rel_eq in H0.
        rewrite prod_rel_eq, sum_rel_eq in H0.
        rewrite <- H, <- H0; eauto. }
      { specialize (H env _ eq_refl);
          specialize (H0 mem _ eq_refl reg _ eq_refl);
          specialize (H1 _ _ reg H2).
        rewrite prod_rel_eq, sum_rel_eq in H.
        rewrite prod_rel_eq, ?sum_rel_eq in H0.
        rewrite prod_rel_eq, sum_rel_eq in H0.
        rewrite H, H0; eauto. }
    Qed.

    Definition bisimilar {E A B} (RAB : A -> B -> Prop) t1 t2 :=
      eqmRH (EqmRH := @imp_asm_EqmRH E) RAB (interp_imp t1) (interp_asm t2).

  End RAB.

  (** [bisimilar] is compatible with [eutt]. *)

  Opaque interp.
  (* Opaque eqmR. *)

  #[global] Instance Proper_bisim {EE A B} (RAB : A -> B -> Prop):
    Proper (eqmR eq ==> eqmR eq ==> iff) (bisimilar (E := EE) RAB).
  Proof.
    repeat intro.
    unfold bisimilar. split.
    - intros. red; intros. unfold interp_imp, interp_asm, interp_map in *.
      Proofmode.f_equiv.
      iproper. repeat red in HProper0. cbn. cbn in HProper0.
      setoid_rewrite prod_rel_eq in HProper0.
      setoid_rewrite sum_rel_eq in HProper0.
      iproper. repeat red in HProper. cbn. cbn in HProper.
      setoid_rewrite prod_rel_eq in HProper.
      erewrite HProper0; eauto.
      2 : { intros; subst. eapply HProper; symmetry. apply H. reflexivity. }
      eapply reflexivity.

      iproper. repeat red in HProper1. cbn. cbn in HProper1.
      repeat setoid_rewrite prod_rel_eq in HProper1.
      repeat setoid_rewrite sum_rel_eq in HProper1.
      repeat red in HProper0. cbn. cbn in HProper0.
      do 2 setoid_rewrite prod_rel_eq in HProper0.
      repeat red in HProper. cbn. cbn in HProper.
      setoid_rewrite prod_rel_eq in HProper.
      erewrite HProper1; eauto.
      2 : {
        intros; subst.
        eapply HProper0; symmetry.
        eapply HProper. apply H0. all : eauto. }

      eapply reflexivity. eauto.
    - intros. red; intros. unfold interp_imp, interp_asm, interp_map in *.
      Proofmode.f_equiv.
      iproper. repeat red in HProper0. cbn. cbn in HProper0.
      setoid_rewrite prod_rel_eq in HProper0.
      setoid_rewrite sum_rel_eq in HProper0.
      iproper. repeat red in HProper. cbn. cbn in HProper.
      setoid_rewrite prod_rel_eq in HProper.
      erewrite HProper0; eauto.
      eapply reflexivity.

      iproper. repeat red in HProper1. cbn. cbn in HProper1.
      repeat setoid_rewrite prod_rel_eq in HProper1.
      repeat setoid_rewrite sum_rel_eq in HProper1.
      repeat red in HProper0. cbn. cbn in HProper0.
      do 2 setoid_rewrite prod_rel_eq in HProper0.
      repeat red in HProper. cbn. cbn in HProper.
      setoid_rewrite prod_rel_eq in HProper.
      erewrite HProper1; eauto.

      eapply reflexivity. eauto.
      Unshelve. all : eauto; intros; eauto; exact (ret (inl tt)).
  Qed.

  Lemma bisimilar_bind' {EE A A' B C} (RAA' : A -> A' -> Prop) (RBC: B -> C -> Prop):
    forall (t1 : itree (ImpFail +' ImpState +' EE) A) (t2 : itree (Memory +' Reg +' Abort +' EE) A') ,
      bisimilar (E := EE) RAA' t1 t2 ->
      forall (k1 : A -> itree (ImpFail +' ImpState +' EE) B) (k2 : A' -> itree (Memory +' Reg +' Abort +' EE) C)
        (H: forall (a:A) (a':A'), RAA' a a' -> bisimilar RBC (k1 a) (k2 a')),
        bisimilar RBC (t1 >>= k1) (t2 >>= k2).
  Proof.
    intros. unfold bisimilar.
    rewrite interp_imp_bind.
    setoid_rewrite interp_asm_bind. repeat intro.
    eapply eutt_clo_bind.
    { eapply H; auto. }
    intros.
    destruct u1 as [? | [? ?]];
      destruct u2 as [? | [? [? ?]]]; inv H2.
    apply eutt_Ret; eauto.
    unfold state_invariant in H5. inv H5.
    eapply H0; eauto.
  Qed.

  (* IY: Should hold true, and are instances of [EQMRH] --
    proving these properties will always be a separate proof obligation but
   are still desirable to have under the [EQMRH] framework due to the layer of abstraction
   it provides w.r.t [EqmR]. *)
  Lemma bisimilar_iter {EE A A' B B'}
        (R : A -> A' -> Prop)
        (S : B -> B' -> Prop)
      (t1 : A-> itree (ImpFail +' ImpState +' EE) (A + B)) (t2 : A' -> itree (Memory +' Reg +' Abort +' EE) (A' + B')):
    (forall l l', R l l' -> bisimilar (E := EE) (sum_rel R S) (t1 l) (t2 l')) ->
    forall x x', R x x' ->
    bisimilar (E := EE) S (iter (C := ktree _) t1 x) (iter (C := ktree _) t2 x').
  Proof.

    intros.
    unfold bisimilar, interp_asm, interp_imp, interp_map in *.
    Proofmode.f_equiv.
    iproper. eapply HProper0.

    { iiter. eapply Hiter. intros; apply reflexivity. }
    { iiter. iproper. eapply HProper1, HProper0.
      eapply Hiter. intros; apply reflexivity. }

    Proofmode.f_equiv.
    { iiter. eapply Hiter. intros; apply reflexivity. }
    { iiter. iproper. eapply HProper0.
      eapply Hiter. intros; apply reflexivity. }

    Proofmode.f_equiv; [ reflexivity | ..].
    { iiter. eapply Hiter. intros; apply reflexivity. }

    cbn. intros.
    eapply (eutt_iter' (state_invariant R)).
    intros.
    destruct H2; cbn. repeat rewrite Eq.bind_bind.
    2 : constructor; auto.
    eapply eutt_clo_bind; [ eapply H; eauto | ].
    intros * [-> | ]; subst; tau_steps; apply eqit_Ret; try constructor; eauto.
    inv H4. inv H6; subst.
    constructor. constructor; eauto.
    constructor. constructor; eauto.
    constructor. eauto. eauto.
  Qed.

  (** [sim_rel] at [n] entails that [GetVar (gen_tmp n)] gets interpreted *)
  (*     as returning the same value as the _Imp_ related one. *)
  Lemma sim_rel_get_tmp0:
    forall EE n l l' g_asm g_imp v,
      sim_rel l' n (g_imp,v) (l, (g_asm, tt)) ->
      (interp_asm (C := EE) ((trigger (GetReg n))) g_asm l)
      ≈     (ret (inr (l, (g_asm, v)))).
  Proof.
    intros.
    unfold interp_asm.

    iproper.
    Proofmode.f_equiv.
    - cbn. repeat red in HProper1. cbn in HProper1.
      repeat setoid_rewrite prod_rel_eq in HProper1.
      setoid_rewrite sum_rel_eq in HProper1.
      eapply HProper1. intros; subst; eauto.
      repeat red in HProper0. cbn in HProper0.
      repeat setoid_rewrite prod_rel_eq in HProper0.
      eapply HProper0. all : eauto.
      intros; subst.
      iignoretrigger.
      cbn in HTrigger.
      setoid_rewrite prod_rel_eq in HTrigger.
      eapply HTrigger; try typeclasses eauto. auto.
    - reflexivity.
    - Proofmode.f_equiv.
      repeat red in HProper1. cbn in HProper1.
      repeat setoid_rewrite prod_rel_eq in HProper1.
      setoid_rewrite sum_rel_eq in HProper1.
      eapply HProper1; eauto.
      intros; subst.
      pose proof @interp_trigger.
      specialize (H0 (stateT memory) (stateT registers (itree (Abort +' EE))) _ _ _ _ _).
      cbn in H0.
      repeat setoid_rewrite prod_rel_eq in H0.
      eapply H0; eauto. reflexivity. cbn.

      repeat red in HProper1. cbn in HProper1.
      repeat setoid_rewrite prod_rel_eq in HProper1.
      setoid_rewrite sum_rel_eq in HProper1.
      rewrite HProper1; eauto.
      2 : { intros. subst. setoid_rewrite Eq.bind_ret_l. cbn.
            apply reflexivity. }

    Transparent interp. cbn.
    unfold MonadFail.Kleisli_MonadIter. cbn. setoid_rewrite unfold_iter.
    cbn. tau_steps.
    apply eqit_Ret.
    unfold lookup_default, lookup, Map_alist.
    erewrite sim_rel_find.
    reflexivity.
    apply H.
  Qed.

  Opaque interp.

End Bisimulation.

(* ================================================================= *)
(** ** Linking *)

(** We first show that our "high level" [asm] combinators are correct.  These
    proofs are mostly independent from the compiler, and therefore fairly
    reusable.  Once again, these notion of correctness are expressed as
    equations commuting the denotation with the combinator.  *)

Section Linking.

    Context {E C1 C2 C3 C4 : Type -> Type}.
    Context {HasReg : Reg +? C1 -< E}.
    Context {HasMemory : Memory +? C2 -< E}.
    Context {HasExit : Exit +? C3 -< E}.
    Context {HasAbort : Abort +? C4 -< E}.

    (* IY: Why is this inferring the ITree equivalence here? *)
    (** [seq_asm] is denoted as the (horizontal) composition of denotations. *)
    Lemma seq_asm_correct {A B C} (ab : asm A B) (bc : asm B C) :
      denote_asm (seq_asm ab bc)
                 ⩯ denote_asm ab >>> denote_asm bc.
    Proof.
      unfold seq_asm.
      rewrite loop_asm_correct, relabel_asm_correct, app_asm_correct.
      rewrite fmap_id0, cat_id_r, fmap_swap.
      apply cat_from_loop.
    Qed.

  (** [if_asm] is denoted as the ktree first denoting the branching condition,
      then looking-up the appropriate variable and following with either denotation. *)
  Lemma if_asm_correct {A} (e : list instr) (tp fp : asm 1 A) :
      denote_asm (if_asm e tp fp)
    ⩯ ((fun _ =>
         denote_list e ;;
         v <- trigger (GetReg tmp_if) ;;
         if v : value then denote_asm fp f0 else denote_asm tp f0)).
  Proof.
    unfold if_asm.
    rewrite seq_asm_correct.
    unfold cond_asm.
    rewrite raw_asm_block_correct_lifted.
    rewrite relabel_asm_correct.

    intros ?.
    Local Opaque denote_asm.

    unfold CategoryOps.cat, Cat_sub, CategoryOps.cat, Cat_Kleisli; simpl.
    rewrite denote_after.
    cbn.
    repeat setoid_rewrite Eq.bind_bind. 
    apply eqit_bind; try reflexivity. intros _.
    apply eqit_bind; try reflexivity. intros [].

    - rewrite !Eq.bind_ret_l.
      setoid_rewrite (app_asm_correct tp fp _).
      setoid_rewrite Eq.bind_bind.
      match goal with
      | [ |- _ (?t >>= _) _ ] => let y := eval compute in t in change t with y
      end.
      rewrite Eq.bind_ret_l. cbn.
      setoid_rewrite Eq.bind_ret_l.
      rewrite Eq.bind_bind.
      setoid_rewrite Eq.bind_ret_l.
      unfold from_bif, FromBifunctor_ktree_fin; cbn.
      rewrite bind_ret_r'.
      { rewrite (unique_f0 (fi' 0)). reflexivity. }
      { intros.
        Local Opaque split_fin_sum R. cbv. Local Transparent split_fin_sum R.
        rewrite split_fin_sum_R. reflexivity. }

    - rewrite !Eq.bind_ret_l.
      setoid_rewrite (app_asm_correct tp fp _).
      repeat setoid_rewrite Eq.bind_bind.
      match goal with
      | [ |- _ (?t >>= _) _ ] => let y := eval compute in t in change t with y
      end.
      rewrite Eq.bind_ret_l. cbn. rewrite Eq.bind_bind.
      setoid_rewrite Eq.bind_ret_l.
      unfold from_bif, FromBifunctor_ktree_fin.
      setoid_rewrite Eq.bind_ret_l.
      rewrite bind_ret_r'.
      { rewrite (unique_f0 (fi' 0)). reflexivity. }
      { intros. Local Opaque split_fin_sum L. cbv. Local Transparent split_fin_sum R.
        rewrite split_fin_sum_L. reflexivity. }
  Qed.

  (** [while_asm] is denoted as the loop of the body with two entry point, the exit
      of the loop, and the body in which we have the same structure as for the conditional *)
  Notation label_case := (split_fin_sum _ _).

  Lemma while_asm_correct (e : list instr) (p : asm 1 1) :
      denote_asm (while_asm e p)
    ⩯ (loop (C := sub (ktree _) fin) (fun l : fin (1 + 1) =>
         match label_case l with
         | inl _ =>
           denote_list e ;;
           v <- trigger (GetReg tmp_if) ;;
           if (v:value) then Ret (fS f0) else (denote_asm p f0;; Ret f0)
         | inr _ => Ret f0
         end)).
  Proof.
    unfold while_asm.
    rewrite loop_asm_correct.
    apply Proper_loop.
    rewrite relabel_asm_correct.
    rewrite fmap_id0, cat_id_l.
    rewrite app_asm_correct.
    rewrite if_asm_correct.
    intros x.
    cbn.
    unfold to_bif, ToBifunctor_ktree_fin.
    rewrite Eq.bind_ret_l.
    destruct (label_case x); cbn.
    - rewrite !Eq.bind_bind. setoid_rewrite Eq.bind_ret_l.
      eapply eutt_clo_bind; try reflexivity. intros; subst.
      rewrite Eq.bind_bind.
      eapply eutt_clo_bind; try reflexivity. intros; subst.
      unfold from_bif, FromBifunctor_ktree_fin; cbn.
      setoid_rewrite Eq.bind_ret_l.
      destruct u0.
      + rewrite (pure_asm_correct _ _); cbn.
        rewrite !Eq.bind_ret_l.
        apply eqit_Ret.
        apply unique_fin; reflexivity.
      + rewrite (relabel_asm_correct _ _ _ _). cbn.
        rewrite Eq.bind_ret_l.
        setoid_rewrite Eq.bind_bind.
        eapply eutt_clo_bind; try reflexivity.
        intros ? ? [].
        repeat rewrite Eq.bind_ret_l.
        apply eqit_Ret.
        rewrite (unique_f0 u1).
        apply unique_fin; reflexivity.

    - cbn.
      rewrite (pure_asm_correct _ _).
      rewrite Eq.bind_bind. cbn.
      unfold from_bif, FromBifunctor_ktree_fin.
      rewrite !Eq.bind_ret_l.
      apply eqit_Ret.
      rewrite (unique_f0 f).
      apply unique_fin; reflexivity.
Qed.

End Linking.

(* ================================================================= *)
(** ** Correctness *)
Instance Subevent_forget_order
         {E C1 C2 A B}
         {Sub1: A +? C1 -< E}
         {Sub2: B +? C2 -< C1}:
  Subevent B E (A +' C2) :=
  {|
    split_E :=
      fun _ e => match split_E _ e with
              | inl1 a => inr1 (inl1 a)
              | inr1 c1 =>
                match split_E _ c1 with
                | inl1 b => inl1 b
                | inr1 c2 => inr1 (inr1 c2)
                end
              end;
    merge_E :=
      fun _ e => match e with
              | inl1 b => merge_E (inr1 (merge_E (inl1 b)))
              | inr1 (inl1 a) => merge_E (inl1 a)
              | inr1 (inr1 c2) => merge_E (inr1 (merge_E (inr1 c2)))
              end
  |}.

Arguments split_E {_ _ _} _ {_}.
Arguments merge_E {_ _ _} _ {_}.
Arguments case /.
Arguments id_ /.
Arguments Id_IFun /.
Arguments cat /.
Arguments Cat_IFun /.

(* Rewriting TC instances *)
Class SubeventRewrite {A C E} (Sub : A +? C -< E) {Sub_wf : Subevent_wf Sub} :=
  {
    merge_split : forall (T : Type) (a : E T), merge_E Sub (split_E Sub a) = a;
    split_merge : forall (T : Type) (a : (A +' C) T), split_E Sub (merge_E Sub a) = a
  }.

Global Instance SubeventRewriteInstances {A C E} {Sub : A +? C -< E} {Sub_wf : Subevent_wf Sub} :
  SubeventRewrite Sub.
Proof.
  destruct Sub_wf.
  destruct sub_iso. red in iso_mono, iso_epi.
  cbn in *. unfold eq2, Eq2_IFun, Relation.i_pointwise in *.
  constructor; eauto.
Qed.

Module SubeventRewr.

  Context {A C E} {Sub: A +? C -< E} {Sub_wf : Subevent_wf Sub}.

  Ltac simpl_sub := repeat
    match goal with
      | |- context[merge_E _ (split_E _ _)] => setoid_rewrite merge_split
      | |- context[split_E _ (merge_E _ _)] => setoid_rewrite split_merge
      | |- context[case (inj1 _)] => rewrite case_inj1
      | |- context[case (inj2 _)] => rewrite case_inj2
    end.

End SubeventRewr.

Import SubeventRewr.

Instance Subevent_forget_order_wf
         {E C1 C2 A B}
         {Sub1: A +? C1 -< E}
         {Sub1_wf : Subevent_wf Sub1}
         {Sub2: B +? C2 -< C1}
         {Sub2_wf : Subevent_wf Sub2}
  : Subevent_wf (@Subevent_forget_order E C1 C2 A B _ _).
Proof with (simpl_sub; eauto).
  repeat constructor; repeat intro.
  cbn.
  - destruct (split_E _ a) eqn: Hsplit.
    { rewrite <- Hsplit; auto... }
    { destruct (split_E _ c) eqn: Hsplit_c.
      - rewrite <- Hsplit_c...
        rewrite <- Hsplit...
      - rewrite <- Hsplit_c...
        rewrite <- Hsplit... }
  - cbn. destruct a eqn: Ha.
    { setoid_rewrite <- Ha... }
    { destruct s eqn: Hs... }
Qed.

Section Correctness.
  Context {E F C1 C2 : Type -> Type}.
  Context {HasReg : Reg +? C1 -< E}
          {HasReg_wf : Subevent_wf HasReg}.
  Context {HasMemory : Memory +? C2 -< C1}
          {HasMemory_wf : Subevent_wf HasMemory}.
  Context {HasState : ImpState +? C2 -< F}
          {HasState_wf : Subevent_wf HasState}.
  (* Context {HasExit : Exit +? C3 -< E}. *)

  Ltac hide_l :=
    let lhs := fresh "lhs" in
    match goal with
    | [ |- eutt _ ?L _ ] => remember L as lhs
    end.

  Ltac hide_r :=
    let rhs := fresh "rhs" in
    match goal with
    | [ |- eutt _ _ ?R ] => remember R as rhs
    end.

  Ltac unfold_interp :=
    repeat unfold interp_imp, interp_map, interp_asm.

  #[global] Program Instance ID_HFunctor : HFunctor.HFunctor (fun x : Type -> Type => x).
  Next Obligation.
    eapply X; eauto.
  Defined.


  Definition expr_bisim {EE} l n (ma:stateT env (Imp.failT (itree EE)) value)
             (mb:stateT memory (stateT registers (Imp.failT (itree EE))) unit) :=
    forall env mem, Renv env mem ->
                   eqmR (m := Imp.failT (itree EE)) (sim_rel l n) (ma env) (mb mem l).

  #[local] Instance expr_bisim_Proper {EE} l n :
    Proper (eqmR eq ==> eqmR eq ==> iff) (@expr_bisim EE l n).
  Proof.
    repeat intro. split; repeat intro; cbn in *.
    { red in H.
      repeat setoid_rewrite prod_rel_eq in H.
      repeat setoid_rewrite prod_rel_eq in H0.
      repeat setoid_rewrite sum_rel_eq in H.
      repeat setoid_rewrite sum_rel_eq in H0.
      rewrite <-H, <-H0; eauto; red in H1. eapply H1; eauto. }
    { red in H.
      repeat setoid_rewrite prod_rel_eq in H.
      repeat setoid_rewrite prod_rel_eq in H0.
      repeat setoid_rewrite sum_rel_eq in H.
      repeat setoid_rewrite sum_rel_eq in H0.
      rewrite H, H0; eauto; red in H1. eapply H1; eauto. }
  Qed.

  Opaque eqmR. Opaque eqmRH. Opaque interp.
  Opaque Interp. Opaque stack_interp. Opaque ret.


  From Coq Require Import ssr.ssreflect.

  Ltac done := solve [reflexivity | done].

  #[local] Transparent interp. #[local] Transparent stack_interp.
  #[local] Transparent eqmR. #[local] Transparent ret.

  Ltac ibind :=
    match goal with
    | |- eqmR _ (interp (T := ?TR) ?h ?x) _ =>
        ibind_rec TR h x
    | |- context[interp (T := ?TR) ?h (ITree.bind ?t ?k)] =>
        ibind_body TR h t k
    | |- context[interp (T := ?TR) ?h (bind ?t ?k)] =>
        ibind_body TR h t k
    end.

  Ltac unfold_expr_bisim :=
    unfold expr_bisim; intros; cbn -[interp stack_interp eqmR]; cbn;
    unfold handle_ImpState, handle_map, MonadIter_itree, interp_body, ret.

  Ltac bind_cong :=
    eapply eqmR_bind_ProperH_simple; [ typeclasses eauto | ..].

  Arguments MonadState.Kleisli_MonadIter /.
  Arguments MonadFail.Kleisli_MonadIter /.
  Ltac unfold_iter :=
    unfold iter, Iter_Kleisli, Basics.iter, MonadFail.errorT_iter, Basics.iter.

  (** Correctness of expressions.
      We strengthen [bisimilar]: initial environments are still related by [Renv],
      but intermediate ones must now satisfy [sim_rel].
      Note that by doing so, we use a _heterogeneous bisimulation_: the trees
      return values of different types ([alist var value * unit] for _Asm_,
      [alist var value * value] for _Imp_). The difference is nonetheless mostly
      transparent for the user, except for the use of the more general lemma [eqit_bind'].
   *)
  Lemma compile_expr_correct : forall EE e l n,
      expr_bisim (EE := EE) l n
                 (interp_imp (denote_expr e))
                 (interp_asm (denote_list (compile_expr n e))).
  Proof with (cbn; autorewrite with itree).
    intros ? e ? ? .
    set (H := (@denote_list E _ _ _ _ (compile_expr n e))). revert n l H.

    induction e; simpl; intros.
    - (* Var case *)
      (* We first compute and eliminate taus on both sides. *)
      unfold_interp.

      Proofmode.f_equiv.
      { unfold bisimilar.
        itrigger. iproper. eapply HProper0. eapply HTrigger. }
      { do 3 ibind. }

      Proofmode.f_equiv; [ done | ..].
    { bind_cong; [ do 3 ibind | ..];
        intros; subst; do 3 iret.
        eapply Hret1. }
      rewrite bind_bind.

      Proofmode.f_equiv; [ done | ..].
    { bind_cong. itrigger. iproper. eapply HProper1, HProper0.
        eapply HTrigger.

        all :
          intros; subst; bind_cong.
          iignoretrigger; iproper; eapply HProper1, HProper0;
            iignoretrigger; eapply HTrigger0; try typeclasses eauto.

        intros; eapply reflexivity.  }

    (* Unfolding the definitions to expose the global invariant : there is no
      other way to re-establish it, because the invariant must be aware of all
      resources*)
      {
        unfold_expr_bisim.


        cbn.
        unfold_iter.
        rewrite unfold_iter. tau_steps.

        apply eqit_Ret; econstructor.

        unfold lookup_default, lookup, Map_alist.

        (* On the _Asm_ side, we bind to [gen_tmp n] a lookup to [varOf v] *)
        (* On the _Imp_ side, we return the value of a lookup to [varOf v] *)
        erewrite Renv_find; [| eassumption].
        eapply sim_rel_add; eassumption. }

    - (* Literal case *)
      (* We reduce both sides to Ret constructs *)
      unfold_interp.

      Proofmode.f_equiv; [ do 2 iret | ..].
      { iproper. eapply HProper1, HProper0, HProper.
        cbn. rewrite Eq.bind_bind Eq.bind_ret_l. reflexivity. }

      Proofmode.f_equiv ; [ done | do 3 ibind | ].

      Proofmode.f_equiv; [ done | .. ].
      { bind_cong.
        { iignoretrigger. iproper.
          eapply HProper1, HProper0; eapply HTrigger;
            try typeclasses eauto. }
        intros; subst; do 3 iret; eapply Hret1. }

      Proofmode.f_equiv; [ done | ..].
      bind_cong. unfold morph, lift.
      cbn -[interp eqmR lift].
      intros; subst; eapply reflexivity.
      intros; subst; eapply reflexivity.

      unfold_expr_bisim. cbn.
      unfold_iter; tau_steps.
      apply eqit_Ret. constructor; eauto.

      (* _Asm_ bind the literal to [gen_tmp n] while _Imp_ returns it *)
      apply sim_rel_add; assumption.

    (* The three binary operator cases are identical *)
    - (* Plus case *)
      (* We push [interp_locals] into the denotations *)
      unfold_interp.
      Proofmode.f_equiv; [ do 2 ibind | ..].
       { pose proof @denote_list_app. iproper.
         eapply HProper1, HProper0, HProper. erewrite H.
         bind_cong. reflexivity.
         intros; subst; setoid_rewrite denote_list_app at 1; apply reflexivity. }

       Proofmode.f_equiv; [ done | do 3 ibind |..].

      unfold expr_bisim; intros.
      (* The Induction hypothesis on [e1] relates the first itrees *)

      bind_cong.
      { eapply IHe1; assumption. }
      (* We obtain new related environments *)
      { intros.

        ibind.
        iproper.
        specialize (HProper0 _ _ Hbind). repeat red in HProper0.
        (* FIXME : Get rid of [Proofmode] header *)
        Proofmode.f_equiv.

        { (* LHS *)
          Transparent eqmR. unfold eqmR. cbn -[interp bind] in *.
          setoid_rewrite prod_rel_eq in HProper0.
          rewrite HProper0; eauto. clear HProper0 Hbind.

          ibind. cbn -[interp bind] in *.
          setoid_rewrite prod_rel_eq in Hbind. rewrite Hbind; eauto.

          reflexivity.

          (* TODO : Tactic should be aware of the eqmR instance inferred.
            There are multiple instances given the same type, which is why
            [iproper] is not proposing an Instance that is applicable here. *)
          (* IY : Is this actually true? I'm not sure that providing the explicit
            eqmR instance would help..*)
          }

        { (* RHS *) clear Hbind.
          ibind. iproper.
          specialize (HProper1 _ _ Hbind).
          specialize (HProper2 _ _ HProper1).
          cbn -[interp bind] in *.
          do 2 setoid_rewrite prod_rel_eq in HProper2. rewrite HProper2.
          clear HProper2 HProper1 HProper Hbind HProper0. 2, 3 : eauto.

          ibind. iproper.
          specialize (HProper0 _ _ Hbind).
          cbn -[interp bind] in *.
          do 2 setoid_rewrite prod_rel_eq in HProper0. rewrite HProper0.
          clear HProper HProper0 Hbind. 2, 3 : eauto.

          ibind. iproper.
          cbn -[interp bind] in *.
          do 2 setoid_rewrite prod_rel_eq in Hbind. rewrite Hbind.
          2, 3 : eauto. clear Hbind HProper. reflexivity. }


        clear Hbind HProper HProper0.
        (* The Induction hypothesis on [e2] relates the second itrees *)

        eapply eutt_clo_bind.
        { apply IHe2; eauto.
          eapply sim_rel_Renv with (n := n) (l_asm := l) (v2 := snd a1) (l := fst a2) (v1 := snd (snd a2)).
          destruct a1, a2, p; eauto. }
        (* And we once again get new related environments *)
        intros [exn_imp | [g_imp'' v']] [exn_asm | [g_asm'' [l'' []]]] HSIM'; try solve [repeat inv HSIM'].
        { inv HSIM'. apply eutt_Ret; eauto. }

        (* We can now reduce down to Ret constructs that remains to be related *)
        tau_steps.
        red. rewrite <- eqit_Ret.
        inv HSIM'.

        destruct a1, a2, p.
        unfold lookup_default, lookup, Map_alist. constructor.
        erewrite sim_rel_find_tmp_n_trans; eauto.
        erewrite sim_rel_find_tmp_n; eauto.
        eapply sim_rel_binary_op; eauto. }

    - (* Sub case *)

      (* We push [interp_locals] into the denotations *)
      unfold_interp.
      Proofmode.f_equiv; [ do 2 ibind | ..].
       { pose proof @denote_list_app. iproper.
         eapply HProper1, HProper0, HProper. erewrite H.
         bind_cong. reflexivity.
         intros; subst; setoid_rewrite denote_list_app at 1; apply reflexivity. }

       Proofmode.f_equiv; [ done | do 3 ibind |..].

      unfold expr_bisim; intros.
      (* The Induction hypothesis on [e1] relates the first itrees *)

      bind_cong.
      { eapply IHe1; assumption. }
      (* We obtain new related environments *)
      { intros.

        ibind.
        iproper.
        specialize (HProper0 _ _ Hbind). repeat red in HProper0.
        (* FIXME : Get rid of [Proofmode] header *)
        Proofmode.f_equiv.

        { (* LHS *)
          Transparent eqmR. unfold eqmR. cbn -[interp bind] in *.
          setoid_rewrite prod_rel_eq in HProper0.
          rewrite HProper0; eauto. clear HProper0 Hbind.

          ibind. cbn -[interp bind] in *.
          setoid_rewrite prod_rel_eq in Hbind. rewrite Hbind; eauto.

          reflexivity.

          (* TODO : Tactic should be aware of the eqmR instance inferred.
            There are multiple instances given the same type, which is why
            [iproper] is not proposing an Instance that is applicable here. *)
          (* IY : Is this actually true? I'm not sure that providing the explicit
            eqmR instance would help..*)
          }

        { (* RHS *) clear Hbind.
          ibind. iproper.
          specialize (HProper1 _ _ Hbind).
          specialize (HProper2 _ _ HProper1).
          cbn -[interp bind] in *.
          do 2 setoid_rewrite prod_rel_eq in HProper2. rewrite HProper2.
          clear HProper2 HProper1 HProper Hbind HProper0. 2, 3 : eauto.

          ibind. iproper.
          specialize (HProper0 _ _ Hbind).
          cbn -[interp bind] in *.
          do 2 setoid_rewrite prod_rel_eq in HProper0. rewrite HProper0.
          clear HProper HProper0 Hbind. 2, 3 : eauto.

          ibind. iproper.
          cbn -[interp bind] in *.
          do 2 setoid_rewrite prod_rel_eq in Hbind. rewrite Hbind.
          2, 3 : eauto. clear Hbind HProper. reflexivity. }


        clear Hbind HProper HProper0.
        (* The Induction hypothesis on [e2] relates the second itrees *)

        eapply eutt_clo_bind.
        { apply IHe2; eauto.
          eapply sim_rel_Renv with (n := n) (l_asm := l) (v2 := snd a1) (l := fst a2) (v1 := snd (snd a2)).
          destruct a1, a2, p; eauto. }
        (* And we once again get new related environments *)
        intros [exn_imp | [g_imp'' v']] [exn_asm | [g_asm'' [l'' []]]] HSIM'; try solve [repeat inv HSIM'].
        { inv HSIM'. apply eutt_Ret; eauto. }

        (* We can now reduce down to Ret constructs that remains to be related *)
        tau_steps.
        red. rewrite <- eqit_Ret.
        inv HSIM'.

        destruct a1, a2, p.
        unfold lookup_default, lookup, Map_alist. constructor.
        erewrite sim_rel_find_tmp_n_trans; eauto.
        erewrite sim_rel_find_tmp_n; eauto.
        eapply sim_rel_binary_op; eauto. }

    - (* Mul case *)

      (* We push [interp_locals] into the denotations *)
      unfold_interp.
      Proofmode.f_equiv; [ do 2 ibind | ..].
       { pose proof @denote_list_app. iproper.
         eapply HProper1, HProper0, HProper. erewrite H.
         bind_cong. reflexivity.
         intros; subst; setoid_rewrite denote_list_app at 1; apply reflexivity. }

       Proofmode.f_equiv; [ done | do 3 ibind |..].

      unfold expr_bisim; intros.
      (* The Induction hypothesis on [e1] relates the first itrees *)

      bind_cong.
      { eapply IHe1; assumption. }
      (* We obtain new related environments *)
      { intros.

        ibind.
        iproper.
        specialize (HProper0 _ _ Hbind). repeat red in HProper0.
        (* FIXME : Get rid of [Proofmode] header *)
        Proofmode.f_equiv.

        { (* LHS *)
          Transparent eqmR. unfold eqmR. cbn -[interp bind] in *.
          setoid_rewrite prod_rel_eq in HProper0.
          rewrite HProper0; eauto. clear HProper0 Hbind.

          ibind. cbn -[interp bind] in *.
          setoid_rewrite prod_rel_eq in Hbind. rewrite Hbind; eauto.

          reflexivity.

          (* TODO : Tactic should be aware of the eqmR instance inferred.
            There are multiple instances given the same type, which is why
            [iproper] is not proposing an Instance that is applicable here. *)
          (* IY : Is this actually true? I'm not sure that providing the explicit
            eqmR instance would help..*)
          }

        { (* RHS *) clear Hbind.
          ibind. iproper.
          specialize (HProper1 _ _ Hbind).
          specialize (HProper2 _ _ HProper1).
          cbn -[interp bind] in *.
          do 2 setoid_rewrite prod_rel_eq in HProper2. rewrite HProper2.
          clear HProper2 HProper1 HProper Hbind HProper0. 2, 3 : eauto.

          ibind. iproper.
          specialize (HProper0 _ _ Hbind).
          cbn -[interp bind] in *.
          do 2 setoid_rewrite prod_rel_eq in HProper0. rewrite HProper0.
          clear HProper HProper0 Hbind. 2, 3 : eauto.

          ibind. iproper.
          cbn -[interp bind] in *.
          do 2 setoid_rewrite prod_rel_eq in Hbind. rewrite Hbind.
          2, 3 : eauto. clear Hbind HProper. reflexivity. }

        clear Hbind HProper HProper0.
        (* The Induction hypothesis on [e2] relates the second itrees *)

        eapply eutt_clo_bind.
        { apply IHe2; eauto.
          eapply sim_rel_Renv with (n := n) (l_asm := l) (v2 := snd a1) (l := fst a2) (v1 := snd (snd a2)).
          destruct a1, a2, p; eauto. }
        (* And we once again get new related environments *)
        intros [exn_imp | [g_imp'' v']] [exn_asm | [g_asm'' [l'' []]]] HSIM'; try solve [repeat inv HSIM'].
        { inv HSIM'. apply eutt_Ret; eauto. }

        (* We can now reduce down to Ret constructs that remains to be related *)
        tau_steps.
        red. rewrite <- eqit_Ret.
        inv HSIM'.

        destruct a1, a2, p.
        unfold lookup_default, lookup, Map_alist. constructor.
        erewrite sim_rel_find_tmp_n_trans; eauto.
        erewrite sim_rel_find_tmp_n; eauto.
        eapply sim_rel_binary_op; eauto. }

      (* FIXME : Extraneous shelved arguments *)
      Unshelve. all : eauto.
      all : repeat intro; red; exact (ret (inl tt)).
  Qed.

  (** Correctness of the assign statement.
      The resulting list of instructions is denoted as
      denoting the expression followed by setting the variable.
   *)
  Lemma compile_assign_correct : forall EE e x,
      bisimilar (E := EE) eq
        (v <- denote_expr e ;; trigger (Imp.SetVar x v))
        (denote_list (compile_assign x e)).
  Proof.
    red; intros.
    unfold compile_assign.
    (* We push interpreters inside of the denotations *)
    Proofmode.f_equiv.
    rewrite interp_imp_bind. eapply reflexivity; eauto.

    eapply eutt_interp_asm.
    rewrite denote_list_app; eapply reflexivity.
    rewrite interp_asm_bind.

    (* By correctness of the compilation of expressions,
       we can match the head trees.
     *)
    Transparent eqmRH.
    cbn -[interp eqmR]; intros.
    pose proof @compile_expr_correct as HExpr ;
    unfold expr_bisim in HExpr; unfold eqmR in HExpr.
    cbn -[interp] in HExpr.

    eapply eutt_clo_bind with (UU := eq ⊕ sim_rel reg 0); eauto.

    (* Once again, we get related environments *)
     intros [exn_imp | [g_imp' v]]  [exn_asm | [g_asm' [l' y]]] HSIM; try solve [repeat inv HSIM].
     { apply eutt_Ret; econstructor. inv HSIM. auto. }
    simpl in HSIM.

    (* We can now reduce to Ret constructs *)
    tau_steps.
    red. rewrite <- eqit_Ret.

    (* And remains to relate the results *)
    unfold state_invariant.
    unfold lookup_default, lookup, Map_alist. constructor.
    cbn. split; auto.
    inv HSIM.
    setoid_rewrite sim_rel_find_tmp_n; eauto; simpl.
    apply sim_rel_Renv in H2.
    split; auto.
    eapply Renv_write_local; eauto. symmetry; auto.
    eapply Renv_write_local; eauto.
  Qed.

  (* The first parameter of [bisimilar] is unnecessary for this development.
     The return type is heterogeneous, the singleton type [F 1] on one side
     and [unit] on the other, hence we instantiate the parameter with the trivial
     relation.
   *)
  Definition TT {A B}: A -> B -> Prop  := fun _ _ => True.
  Hint Unfold TT: core.

  Definition equivalent {E} (s:stmt) (t:asm 1 1) : Prop :=
   bisimilar (E := Exit +' E) TT (denote_imp s) (denote_asm t f0).

  Inductive RI : (unit + unit) -> (unit + unit + unit) -> Prop :=
  | RI_inl : RI (inl tt) (inl (inl tt))
  | RI_inr : RI (inr tt) (inr tt).

  (* Utility: slight rephrasing of [while] to facilitate rewriting
     in the main theorem.*)
  Lemma while_is_loop {A} (body : itree A (unit+unit)) :
    while body
          ≈ iter (C := ktree _) (fun l : unit + unit =>
                    match l with
                    | inl _ => x <- body;; match x with inl _ => Ret (inl (inl tt)) | inr _ => Ret (inr tt) end
                    | inr _ => Ret (inl (inl tt))   (* Enter loop *)
                    end) (inr tt).
  Proof.
    unfold while.
    rewrite! unfold_iter_ktree.
    rewrite Eq.bind_ret_l tau_eutt.
    rewrite unfold_iter_ktree.
    rewrite !Eq.bind_bind.
    eapply eutt_clo_bind. reflexivity.
    intros. subst.
    destruct u2 as [[]|[]].
    2 : { force_right. reflexivity. }
    rewrite Eq.bind_ret_l !tau_eutt.
    unfold iter, Iter_Kleisli.
    apply eutt_iter' with (RI := fun _ r => inl tt = r).
    - intros _ _ [].
      rewrite <- bind_ret_r at 1.
      eapply eutt_clo_bind; try reflexivity.
      intros [|[]] _ []; apply eqit_Ret; auto; constructor; auto.
    - constructor.
  Qed.

  Definition to_itree' {E A} (f : ktree_fin E 1 A) : itree E (fin A) := f f0.
  Lemma fold_to_itree' {A} (f : ktree_fin A 1 1) : f f0 = to_itree' f.
  Proof. reflexivity. Qed.

  Global Instance Proper_to_itree' {EE A} :
    Proper (eq2 ==> eutt eq) (@to_itree' EE A).
  Proof.
    repeat intro.
    apply H.
  Qed.

  Notation Inr_Kleisli := Inr_Kleisli.

  (** Correctness of the compiler.
      After interpretation of the [Locals], the source _Imp_ statement
      denoted as an [itree] and the compiled _Asm_ program denoted
      as an [itree] are equivalent up-to-taus.
      The correctness is termination sensitive, but nonetheless a simple
      induction on statements.
      We are only left with reasoning about the functional correctness of
      the compiler, all control-flow related reasoning having been handled
      in isolation.
   *)
  Theorem compile_correct {EE} (s : stmt) :
    equivalent (E := EE) s (compile s).
  Proof.
    unfold equivalent.
    induction s.

    - (* Assign *)
      simpl.
      (* We push [denote_asm] inside of the combinators *)
      rewrite raw_asm_block_correct.
      rewrite denote_after.
      (* The head trees match by correctness of assign *)
      rewrite <- (bind_ret_r (ITree.bind (denote_expr e) _)).
      eapply bisimilar_bind'.
      { eapply compile_assign_correct; auto. }

      (* And remains to trivially relate the results *)

      intros []; simpl.
      repeat intro.
      force_left; force_right.
      Transparent eutt. red.
      rewrite <- eqit_Ret; auto.
      unfold state_invariant; auto.

    - (* Seq *)
      (* We commute [denote_asm] with [seq_asm] *)
      rewrite fold_to_itree'; simpl.
      rewrite seq_asm_correct. unfold to_itree'.

      (* And the result is immediate by indcution hypothesis *)
      eapply bisimilar_bind'.
      { eassumption. }
      intros [] ? _. rewrite (unique_f0 a').
      eassumption.

    - (* If *)
      (* We commute [denote_asm] with [if_asm] *)
      rewrite fold_to_itree'. simpl.
      rewrite if_asm_correct.
      unfold to_itree'.

      (* We now need to line up the evaluation of the test,
         and eliminate them by correctness of [compile_expr] *)
      red; intros.
      rewrite interp_asm_bind.
      rewrite interp_imp_bind.
      repeat intro.
      eapply eutt_clo_bind.
      { apply compile_expr_correct; auto. }

      (* We get in return [sim_rel] related environments *)
      intros [exn_imp | [g_imp' v]] [exn_asm | [g_asm' [l' x]]] HSIM; repeat inv HSIM.
      apply eutt_Ret; eauto.

      (* We know that interpreting [GetVar tmp_if] is eutt to [Ret (g_asm,v)] *)
      generalize H2; intros EQ. eapply sim_rel_get_tmp0 in H2.
      unfold tmp_if.
      pose proof @interp_asm_bind. cbn -[interp] in H0.
      do 2 setoid_rewrite prod_rel_eq  in H0. setoid_rewrite sum_rel_eq in H0.
      rewrite H0; eauto.
      cbn -[interp_asm interp_imp denote_asm].
      clear H0.
      rewrite sim_rel_get_tmp0; eauto.

      rewrite bind_ret_; simpl.

      (* We can weaken [sim_rel] down to [Renv] *)
      apply sim_rel_Renv in EQ.
      (* And finally conclude in both cases *)
      destruct v; simpl; auto.

      eapply IHs2; eauto.
      eapply IHs1; eauto.

    - (* While *)
      (* We commute [denote_asm] with [while_asm], and restructure the
         _Imp_ [loop] with [while_is_loop] *)
      Local Opaque denote_asm.
      simpl; rewrite fold_to_itree'.
      rewrite while_is_loop.
      rewrite while_asm_correct.
      Local Opaque denote_asm.
      Local Opaque denote_list.

      unfold to_itree'.
      unfold loop. unfold iter at 2.
      unfold Iter_sub, Inr_sub, Inr_Kleisli, inr_, lift_ktree, cat, Cat_sub, cat, Cat_Kleisli.
      unfold from_bif, FromBifunctor_ktree_fin.
      rewrite bind_bind. do 2 rewrite bind_ret_l.
      eapply (bisimilar_iter (fun x x' => (x = inl tt /\ x' = f0) \/ (x = inr tt /\ x' = fS f0))).
      2: {
        right. split. auto. apply unique_fin; reflexivity.
        }
      (* The two cases correspond to entering the loop, or exiting it*)
      intros ? ? [[] | []]; subst.

      (* The exiting case is trivial *)
      2:{ rewrite bind_bind bind_ret_l.
          unfold to_bif, ToBifunctor_ktree_fin. cbn -[interp bisimilar bind].
          rewrite bind_bind. unfold to_bif.
          rewrite bind_ret_l. cbn -[bind interp bisimilar].
          do 2 rewrite bind_bind. unfold inl_, Inl_Kleisli, lift_ktree_.
          rewrite bind_ret_l. unfold from_bif. 
          rewrite bind_ret_l. unfold Inl_sub. unfold cat.
          rewrite bind_bind. unfold inl_, Inl_Kleisli, lift_ktree_.
          rewrite bind_ret_l. unfold from_bif.
          rewrite bind_ret_l.

          unfold_expr_bisim. intros. unfold_iter. tau_steps. apply eutt_Ret.
          unfold state_invariant. simpl.
          constructor; auto.
          constructor; auto.
          setoid_rewrite split_fin_sum_L_L_f1.
          constructor. left. auto.
      }

      Local Opaque denote_asm.
      (* We now need to line up the evaluation of the test,
         and eliminate them by correctness of [compile_expr] *)
      (* repeat intro. *)
      repeat rewrite bind_bind. rewrite Eq.bind_bind.

      red; intros.
      rewrite interp_asm_bind.
      rewrite interp_imp_bind.
      repeat intro.
      eapply eutt_clo_bind.
      { apply compile_expr_correct; auto. }

      intros [exn_imp | [g_imp' v]] [exn_asm | [g_asm' [l' x]]] HSIM; repeat inv HSIM.
      { apply eutt_Ret; constructor; eauto. }

      pose proof @interp_asm_bind; pose proof @interp_imp_bind.
      cbn -[interp_asm] in H0.
      do 2 setoid_rewrite prod_rel_eq in H0.
      setoid_rewrite sum_rel_eq in H0. rewrite H0; eauto. cbn -[interp_asm interp_imp].
      rewrite H0. rewrite Eq.bind_bind.
      rename H2 into HSIM.

      cbn -[interp_imp] in H1.
      setoid_rewrite prod_rel_eq in H1.
      setoid_rewrite sum_rel_eq in H1. rewrite H1; eauto. cbn -[interp_asm interp_imp].

      (* We know that interpreting [GetVar tmp_if] is eutt to [Ret (g_asm,v)] *)
      generalize HSIM; intros EQ. eapply sim_rel_get_tmp0 in EQ.
      unfold tmp_if.

      erewrite EQ; clear EQ. all : eauto.
      rewrite bind_ret_; simpl.

      (* We can weaken [sim_rel] down to [Renv] *)
      apply sim_rel_Renv in HSIM.
      (* And now consider both cases *)
      destruct v; auto.
      + (* The false case is trivial *)
        force_left; force_right.
        red.
        rewrite <- eqit_Ret.
        unfold state_invariant. simpl.
        repeat (constructor; auto).

      + (* In the true case, we line up the body of the loop to use the induction hypothesis *)
        Opaque compile.
        rewrite H0.
        rewrite !Eq.bind_bind.
        repeat rewrite H1.
        rewrite !Eq.bind_bind. all : eauto.

        cbn -[interp_asm interp_imp].
        eapply eutt_clo_bind.
        { eapply IHs; eauto. }
        intros [exn_imp | [g_imp'' v'']] [exn_asm | [g_asm'' [l'' x']]] HSIM'; repeat inv HSIM'.
        tau_steps.
        apply eqit_Ret. constructor; eauto.

        tau_steps.
        apply eqit_Ret. constructor; eauto.
        setoid_rewrite split_fin_sum_L_L_f1.
        constructor; auto. inv H4.  cbn; auto.
        constructor; left; auto.

    - (* Skip *)

      simpl.
      unfold id_asm.
      pose proof (@pure_asm_correct).
      do 5 red in H. rewrite H.
      red. unfold eqmRH. cbn. intros. unfold_expr_bisim.
      unfold_iter; tau_steps.
      apply eqit_Ret.
      unfold state_invariant. auto.

    - (* Abort *)
      simpl. Transparent denote_asm. Transparent compile.
      cbn. intros; tau_steps. apply eqit_Ret; eauto.
      Unshelve. eauto.
  Qed.

End Correctness.

(* ================================================================= *)
(** ** Closing word. *)

(** Through this medium-sized example, we have seen how to use [itree]s to
    denote two languages, how to run them and how to prove correct a compiler
    between them.
    We have emphasized that the theory of [ktree]s allowed us to decouple
    all reasoning about the control-flow from the proof of the compiler itself.
    The resulting proof is entirely structurally inductive and equational. In
    particular, we obtain a final theorem relating potentially infinite
    computations without having to write any cofixed-point.

    If this result is encouraging, one might always wonder how things scale.

    A first good sanity check is to extend the languages with a _Print_
    instruction.
    It requires to add a new event to the language and therefore makes the
    correctness theorem relate trees actually still containing events.
    This change, which a good exercise to try, turns out to be as
    straightforward as one would hope. The only new lemma needed is to show
    that [interp_locals] leaves the new [Print] event untouched.
    This extension can be found in the _tutorial-print_ branch.

    More importantly, our compiler is fairly stupid and inefficient: it creates
    blocks for each compiled statement! One would hope to easily write and
    prove an optimization coalescing elementary blocks together.

    A first example of optimization at the [asm] level proved correct is
    demonstrated in the _AsmOptimization.v_ file.
 *)
