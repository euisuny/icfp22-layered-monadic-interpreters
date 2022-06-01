# Formal Reasoning about Layered Monadic Interpreters Artifact

This is the artifact for the paper submission of "Formal Reasoning About Layered Monadic Interpreters".
We have mechanized and proved all claims made in the paper in Coq.

### Dependencies

The following are necessary dependencies for the code base.

- coq 8.13.2
- coq-paco 4.1.1

These packages can be installed via `opam`.

## Section 3 : Building Layered Monadic Interpreters

### Section 3.1
The following contain the relevant definitions for Section 3.
- [Trigger](theories/Core/Subevent.v): search for `Class Trigger`

### Section 3.2
- [Subevent](theories/Core/Subevent.v): search for `Class Subevent`
- [Subevent Instances](theories/Core/Subevent.v): `Section Subevent_Instances` contains relevant instances

### Section 3.4
- [Interp](theories/Interp/Interp.v) for interpretable monads: search for `Class Interp`
- [HFunctor](theories/Interp/HFunctor.v) for higher-order functors: search for `Class HFunctor`
- [stack_interp](theories/Interp/InterpFacts.v): search for `Instance stack_interp`

## Section 4 : Building Layered Monadic Interpreters

### Section 4.1
- [OK EqmR Laws](theories/EqmR/EqmRMonad.v) Figure 7 "OK EqmR Laws": search for `Class EqmR_OK`

### Section 4.2
- [image](theories/EqmR/EqmRMonad.v): search for `Definition image`

### Section 4.3
- [EqmRMonad Laws](theories/EqmR/EqmRMonad.v) Figure 8 "EqmRMonad Laws": search for `Class EqmRMonadLaws`
- [EqmRMonadInverses Laws](theories/EqmR/EqmRMonad.v) Figure 9 "EqmRMonadInverses Laws": search for `Class EqmRInversionProperties`

The specific instances for the laws mentioned in Sections 4.1-4.3 for the ID, State, Error, Prop, and ITree monads are proved in the following files:
- [ITree instances for weak bisimulation](theories/EqmR/Monads/ITree_weak.v)
- [ITree instances for strong bisimulation](theories/EqmR/Monads/ITree_strong.v)
- [State monad](theories/EqmR/Monads/State.v)
- [Error monad](theories/EqmR/Monads/Error.v)
- [Prop monad](theories/EqmR/Monads/Prop.v)
- [ID monad](theories/EqmR/ID.v)

### Section 4.4
- [MonadMorphism laws](theories/EqmR/EqmRMonadT.v) Figure 10 "Monad morphism laws": search for `Section MonadMorphism`
- [MonadTransformer laws](theories/EqmR/EqmRMonadT.v) Figure 11 "Monad transformer well-formedness conditions": search for `Class MonadTLaws`

The specific instances for the laws mentioned in Section 4.4. for StateT, ErorrT are proved in the following files:
- [StateT monad transformer](theories/EqmR/Monads/StateT.v)
- [ErrorT monad transformer](theories/EqmR/Monads/ErrorT.v)

### Section 4.5
- theories/EqmR/EqmRMonadH.v contains the definition of EqmR across distinct monads

## Section 5 : Layering EqmR with Interpreters

- [InterpLaws](theories/Interp/InterpFacts.v) Figure 12 "Interpretation laws"
- [Higher-order functor laws](theories/Interp/HFunctor.v) Figure 13 "Select HFunctor Laws"
- Figure 14 "Composable Structures and Laws": 
  (In `theories/EqmR/EqmRMonadT.v`, see `compose_MonadT`, `compose_IterativeMonadT`, and `compose_WF_IterativeMonadT`.
  In `theories/Interp/HFunctor.v`, see `compose_HFunctor` and `compose_WF_HFunctor`)
  
## Section 6 : EqmR in Practice : Implementation and Case Study

The case study is in `tutorial/`, where the definition of languages are in `Imp.v` and `Asm.v`, and the proof of correctness for the compiler is in `Imp2AsmCorrectness.v`.
The custom tactics mentioned is in `tutorial/Proofmode.v`
