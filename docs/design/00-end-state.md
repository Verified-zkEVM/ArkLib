# 00 — End State: ArkLib as the Formalization Library for SNARKs

## The ambition

ArkLib is to be the library in which **all of SNARKs is formalized**: hash-based (FRI, STIR, WHIR, BaseFold, Binius, BCS/Micali compilers), curve-based (KZG/PLONK, Groth16, IPA/Bulletproofs, Nova/ProtoStar folding, pairing and discrete-log assumptions, AGM), and lattice-based (Ajtai commitments, LaBRADOR/Greyhound-style arguments, RoK-and-roll style lattice reductions) — with **abstract specifications, concrete implementations, and verified refinements between them**, compositional all the way up (recursion, IVC, PCD, aggregation) and all the way down (Rust/production code ↔ Lean models via zkLean / Hax / Aeneas).

## The layer cake

```
L6  Implementations            Rust ↔ Lean extraction/refinement (zkLean, Hax, Aeneas)
L5  Argument systems           NARGs/SNARKs in oracle worlds; Fiat–Shamir; exact bounds
L4  Compiled reductions        committed relations Com_A[R]; commitment backends
L3  Oracle reductions (ideal)  IORs/IOPs/PIOPs; claims, virtual oracles, composition   ← 02
L2  Adversarial execution      worlds, traces, budgets, games, extractors              ← 03
L1  Oracle computation         OracleComp, QueryImpl, probability      (VCVio)
L0  Interaction substrate      trees, paths, decorations, lenses       (PolyFun) + mathlib
```

Every protocol formalization is a path through this cake; every compiler (`04`) is a verified functor between adjacent layers; every security theorem transports along it with explicit error/budget bookkeeping.

## Why this design enables that future

**One claim discipline for all three families.** Curve-based and lattice-based systems differ from hash-based ones in their *backends* (L4) and *assumptions* (L2 worlds and adversary classes), not in their ideal-model shape (L3). A folding scheme over Pedersen commitments, a PIOP compiled with KZG, and an IOP compiled with Merkle trees are the *same L3 objects* with different `CommitBackend` capability records and different `CompilePolicy` rules (inline / seal-and-link / homomorphic `CommitAction`). This is already demonstrated by the Nova case study (`04` §6): the fold is an ideal oracle reduction; Pedersen linearity is a `CommitAction`; binding enters only in the tree-extraction bridge.

**Assumption families are world + adversary-class data.** ROM = a lazily-sampled function world. AGM = an adversary-class restriction plus an instrumented trace. Discrete-log/SIS/pairing assumptions = hardness predicates on games over group/module worlds. Quantum = a different (linear) execution model, explicitly out of the classical core's scope. All enter at L2 without touching L3 — this is what makes "all of SNARKs" a library rather than a family of forks.

**Refinement is built into the carrier split.** Abstract behavior (extensional) vs. `Materialization`/`ExecutableMaterialization` (data + cost) vs. `TypedPlan` (inspectable programs) is exactly the spec-to-implementation refinement seam. L6 work attaches to `ExecutableMaterialization` and plan interpreters; it never needs to reopen L3 semantics.

**Exact bounds are structural, not aspirational.** Budgets and errors are typed functionals from day one (D4); matching or beating textbook bounds is then a matter of proving better lemmas, not re-architecting.

## What we write down NOW to bring this future into possibility

1. **The stable interfaces** (this suite): `ClaimWith`/closing, `SourceCtx`/`subst`, `ExecutionArtifact`/`WorldTrace`/`TraceTransducer`, `Budget`/error functionals, `CommitBackend` capability records, compiler pass contracts. Everything else may churn; these are the load-bearing walls, so they get the audits.
2. **The registry discipline.** Every security notion is registered with: its game record, quantifier order in the name, its position in the implication map (`03` §8), and its losses. Every backend capability likewise. New papers land as new registry entries + bridges, not as parallel frameworks.
3. **The guarantee-transport principle** (D1) as a compiler invariant — this is the single sentence that connects ideal-model typing to cryptographic obligations across all three families.
4. **The negative space.** Explicitly out of the classical core: quantum messages (linear execution model, separate), relativized relations querying the model's own RO (impossible-territory, per 2024/728), UC-style environments (future L2 extension, cf. VCVio-UC sketches in paper-note).
5. **The foundation contracts** (`01`): what ArkLib demands of PolyFun and VCVio, so those libraries can evolve independently without breaking L3+.

## Non-goals for the core

- A closed DSL of all derived oracles (the record + `ofQuery` escape hatch is canonical; constructor zoo grows by need).
- One monolithic "secure protocol" structure (properties are separate records + bridges).
- Category-theory-first APIs (state the algebra concretely; adopt Mathlib category theory only when several clients demonstrate payoff).
- Uniform treatment of every "transcript" (four distinct objects, named, with conversions: `InteractionTranscript`, `VerifierLocalView`, `WorldTrace`, `SRMoveTrace`).
