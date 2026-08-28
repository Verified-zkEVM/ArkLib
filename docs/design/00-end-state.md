# 00 — End State: A Verified Architecture for SNARKs

## 0. Status and scope

This document is a **north star and coverage contract**, not a claim that every proof system has
already been reduced to one carrier. The near-term scope is classical hash-, algebraic-, and
lattice-based proof systems under explicitly stated oracle and adversary models. Quantum access,
relativized relations that query the model's own random oracle, and other execution models require
new semantics; the architecture must leave seams for them without pretending that the classical
core already covers them.

The design is being developed on `design/oracle-reduction-v2`, but that branch is documentation and
prototype provenance, **not an implementation base**. At the 2026-07-13 audit it forked from ArkLib
at `9f6e989`, while current ArkLib `main` was `e2c3710`; it also carried the older core-rebuild tree.
Every implementation PR described in [`01a-foundation-pr-plan.md`](01a-foundation-pr-plan.md) starts
from the then-current default branch. Prototype declarations may be transplanted only as reviewed
source material.

There is already a separate Lean 4.31 migration candidate, `quang/bump-v4.31.0` at `55a9ccc` after
merging current `main`. It pins VCVio `cbd4144b` and VCVio's tested PolyFun revision `04a12b6`.
AR-0 should review, rebase, validate, and land that work (or its successor), not recreate the
migration from scratch; candidate-branch existence is not itself an acceptance result.

## 1. The ambition

ArkLib should become the integration library in which a broad range of SNARK constructions can be
stated, composed, compiled, and connected to executable implementations:

- hash-based protocols such as FRI, STIR, WHIR, BaseFold, Binius, and BCS/Micali compilers;
- algebraic systems such as KZG/PLONK, IPA/Bulletproofs, Nova/ProtoStar folding, pairing-based
  systems, and protocols proved in the AGM;
- lattice-based commitments and arguments, including Ajtai-style commitments and structured
  lattice reductions;
- recursion, IVC, PCD, aggregation, preprocessing, and executable refinement.

This is a **coverage hypothesis** tested by conformance cases, not an axiom. The first cases are
sumcheck, FRI, and Nova; a polynomial-commitment protocol, a preprocessing protocol, and one
lattice-backed protocol must follow before the common carrier is treated as mature. A construction
that does not naturally pass through ideal oracle reduction may enter at the committed-relation or
argument-system layer. The architecture must accommodate that route rather than force a false
encoding.

## 2. Architecture: pipeline plus two cross-cutting planes

The former “layer cake” was useful intuition but misleading as a dependency stack: security games
quantify over objects at several layers, and ideal reductions do not depend on adversarial worlds.
The end state has one object/compilation pipeline and two cross-cutting planes.

### 2.1 Object and compilation pipeline

```text
generic interaction syntax
        ↓ specialize to oracle protocols
ideal claims and oracle reductions (Δ)
        ↓ represent / lower / transport
committed relations and backend capabilities
        ↓ Fiat–Shamir / argument compiler
interactive or noninteractive argument systems
        ↓ executable refinement
production representations and implementations
```

- **PolyFun** supplies domain-agnostic interaction semantics: polynomial functors, `FreeM` and
  `ITree`, displayed data, handlers/responders, dynamical systems, finite and infinite runs,
  structural traces, generic sequential/multiparty/concurrent wiring, and refinement.
- **VCVio** specializes that substrate to oracle computation and probabilistic semantics:
  `OracleSpec`, `OracleComp`, `QueryImpl`, stateful simulation, evaluation distributions, random
  oracles, query resources, and cryptographic games.
- **ArkLib** supplies protocol meaning: prover/verifier roles, public and oracle messages, claims,
  relations, reductions, extractors, commitment-backend adapters, compilers, and concrete proof
  systems.

### 2.2 Adversarial-execution plane (Γ)

Worlds, persistent state, query-event traces, replay/reprogramming, probability, and resource
accounting interpret the pipeline's objects. PolyFun owns their effect-polymorphic structural
algebra; VCVio owns oracle/probability specializations; ArkLib owns the protocol games and security
notions that consume them. This plane is the subject of `03`, not a prerequisite for defining the
ideal carrier in `02`.

### 2.3 Mathematical and representation plane

`ArkLib/Data`, CompPoly, coding theory, finite fields, curves, modules, lattices, encodings, and
serialization cross several semantic layers. They are not “below” protocol syntax in a useful
sense. Each backend states exactly which mathematical structures and representation theorems it
uses.

## 3. The commonality claim, stated precisely

The target is **one capability-parametric language of ideal resources and claims**, not literal
identity of every hash-, curve-, and lattice-based construction.

- A FRI fold, a Nova fold, and a polynomial-evaluation reduction may all expose virtual output
  oracles, but their interfaces and guarantees differ.
- A backend advertises operations it can realize: random access, batch opening, evaluation,
  linear action on commitments, proximity enforcement, or a link argument.
- `GuaranteeTransport` says how an ideal slot guarantee becomes a commit/open/link obligation. It
  does not assert that every backend can realize every guarantee.
- A conformance theorem embeds a concrete construction into the common carrier and discharges its
  capability obligations. Failed conformance is evidence that the carrier needs a principled
  extension, not permission to add a scheme-local parallel framework.

Nova and FRI remain the canonical contrast. Pedersen linearity realizes a virtual linear action on
committed witnesses without a fresh prover message; Merkle commitments do not, so FRI requires a
fresh committed word plus consistency and proximity obligations. The shared abstraction is the
ideal transformation plus an explicit backend action—not a claim that the concrete protocols are
the same.

## 4. Security assumptions are complete game data

An assumption family is not merely “world + adversary class.” A usable computational game records:

1. the security parameter and public parameter/setup distribution;
2. the world and representation semantics in which the experiment runs;
3. the adversary interface and admissible class (including uniformity/advice choices);
4. the event or advantage functional;
5. the cost/resource model and reduction loss.

ROM, AGM, DLOG, SIS, and pairing assumptions instantiate different parts of this record. AGM, for
example, combines an instrumented algebraic-representation semantics with an adversary restriction;
it is not only a trace flag. VCVio owns generic game/reduction carriers and standalone primitive or
hardness games (for example Merkle, DLOG, or SIS); ArkLib owns protocol-security experiments that
consume them. AGM may therefore split into a VCVio algebraic world/representation adapter and an
ArkLib protocol adversary restriction.

## 5. Real objects and virtual views

The design deliberately tracks both layers.

- The **real layer** contains setup/input resources, prover messages, concrete data, world state,
  commitments, and openings.
- The **virtual layer** contains source-scoped query programs describing the oracle behavior a
  claim exposes.
- A runner-produced artifact relates them: the security-game API consumes the paired output of one
  execution and does not expose a constructor from independently supplied parts. This prevents
  accidental mixing by construction of the experiment; it does not claim that two executions have
  different Lean types or that malicious Lean code cannot fabricate values.
- Compilation transforms real resources and transfers virtual guarantees into cryptographic
  obligations. It does not erase the distinction.

This is why `SourceCtx` should remain an extensional handler presentation while resource identity,
origin, aliasing, and guarantees live in a separate `ResourceSchema`. Combining these prematurely
would make semantic substitution depend on compiler metadata; omitting the schema would make trace
and guarantee claims unverifiable.

## 6. Refinement obligations at the executable boundary

`ExecutableMaterialization` is an attachment point, not the whole L6 story. A production refinement
theorem may need to relate:

- mathematical values to encoded/serialized representations;
- field, group, polynomial, or lattice operations to concrete arithmetic;
- abstract randomness and oracle calls to executable entropy sources and hash APIs;
- partiality, faults, and termination to the mathematical outcome model;
- executable memory/FFI traces to mathematical query and cost traces;
- measured or certified resource use to the stated budget model;
- constant-time or leakage behavior, when such a property is claimed.

Executable correctness therefore connects back to ideal and adversarial observations; it cannot be
proved wholly inside a detached materialization record.

## 7. What is fixed now, and what is evidence

Fixed design principles:

1. closed relations consume extensional oracle behavior;
2. virtual derivations are source-scoped and compose by handler substitution;
3. security games derive real/virtual closing from one runner-produced artifact rather than accepting split parts;
4. resource aliasing is explicit and disjoint tensor does not duplicate persistent resources;
5. security notions expose quantifier order, views, budgets, and losses;
6. compiler passes expose guarantee-transport and security-transfer obligations;
7. existing PolyFun/VCVio semantics are extended, not shadowed by ArkLib-private copies.

Still provisional until Lean clients elaborate:

- exact universes and field layouts of `OracleFamily`, `SourceCtx`, `ClaimWith`, and `RunCore`;
- the final `ResourceSchema` and stable-resource-identity representation;
- compiler plan and backend capability field names;
- whether existing `TypeTree.Chain` is sufficient for n-ary reduction presentation.

The prototype `ArkLib/Interaction` tree on this design branch is valuable evidence and a lemma
bank. It is not proof that those APIs are current, stable, or mergeable wholesale.

## 8. Success criteria

The architecture has earned its abstraction when all of the following are true:

- sumcheck, FRI, Nova, one polynomial-commitment protocol, and one lattice-backed protocol use the
  same claim/closing discipline without scheme-local security frameworks;
- hash and homomorphic backends instantiate distinct capability sets and obtain transfer theorems
  with explicit losses;
- ordinary, state-restoration, and knowledge-soundness theorems compose only under their stated
  hypotheses, with exact resource/error accounting;
- an existing VCVio Merkle theorem is adapted into an ArkLib compiler capability without restating
  the primitive game;
- one executable implementation is related to its mathematical execution and resource trace;
- the three repositories remain acyclic and are released in a reproducible dependency train.

## 9. Non-goals for the first core

- A closed DSL of every derived oracle; `ofQuery` remains the escape hatch.
- One monolithic “secure protocol” structure; properties remain separate games plus bridges.
- Category-theory-first APIs or calling translations “functors” before categories and laws exist.
- A single execution-record type: structural branch/execution paths, verifier views, world query
  logs, and state-restoration move traces remain distinct with explicit conversions.
- Solving quantum-access or impossible-relativization cases inside the classical runner.
- Rebuilding generic UC machinery: PolyFun and VCVio already contain open-process and UC layers;
  the first oracle-reduction core merely does not depend on them.
