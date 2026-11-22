# D9. Quantum provers and adversary models

**Status:** Proposed: awaiting maintainer approval.
**Implemented by:** ArkLib PR A (security notions stated against an adversary model; record D7),
then a post-milestone quantum track: one PolyFun change, one VCVio change, and ArkLib modules under
`ArkLib/Interaction/Core/Quantum/`. Nothing in P, B or C changes.

## Problem

Post-quantum security means two things for interactive proofs. A cheating prover may be a quantum
algorithm, and security reductions may run quantum adversaries as subroutines. Some honest provers
are also quantum: in classical verification of quantum computation the honest prover holds a
quantum state and the verifier is classical. The messages are classical in all of these
applications.

The interaction layer types a prover as a strategy whose slots are computations in a monad `m`
(record D4). A quantum prover does not fit that type. Its memory between moves is a quantum
register, and the register it holds after a move may depend on the move. VCVio's quantum programs
(`VCVio/Quantum/Comp/Basic.lean`) carry this dependence in their type: `QuantumComp L spec X A` is
a program that starts on register `A` and ends at some leaf `x : X u` on the register `u` it
reached. That is an indexed effect, not a monad.

This record fixes three things: which parties may be quantum, what a quantum prover is, and how
the security notions of record D7 are stated so that the same definition covers classical and
quantum adversaries.

## Decision

### 1. Scope

- Messages, challenges, oracle messages and transcripts are classical.
- Verifiers are classical. The sampler draws classical coins and the decision is a classical
  computation on the transcript (record D4).
- A prover may be quantum. One type covers quantum adversaries and honest quantum provers.
- Out of scope: quantum messages (QIP-style protocols), quantum verifiers, and runs in which both
  parties hold quantum registers. The last one would need the subsystem framing of
  `VCVio/Quantum/Comp/Lift.lean` and no planned client needs it.

### 2. A quantum prover

A quantum prover is a strategy over the same protocol tree and lens as a classical one, with
uniform effect slots (record D4). Each slot is a quantum program that starts on the register the
prover currently holds.

```lean
-- intended, not existing (ArkLib/Interaction/Core/Quantum/Prover.lean)
/-- Quantum prover on the tree `s`, holding register `R`. `Out tr u` is its output at the end
of the transcript `tr`, on the final register `u`. -/
def QProver (L : LocalSig.{1, 0}) (spec : QuantumOracleSpec.{0, 0}) :
    (s : FreeM P PUnit) → (Out : PathAlong l s → QReg → Type 1) → QReg → Type 1
  | .pure _,         Out => fun R => QuantumComp L spec (Out ⟨⟩) R
  | .liftBind a k,   Out => fun R =>
      if prover owns a then
        QuantumComp L spec (fun u => (x : Move l a) × QProver L spec (k (l.toFunB a x)) (Out ∘ cons x) u) R
      else
        QuantumComp L spec (fun u => (x : Move l a) → QProver L spec (k (l.toFunB a x)) (Out ∘ cons x) u) R
```

At a message node the program measures out the message `x` and stops on a register `u`, which may
depend on its outcomes. At a challenge node the program runs before the challenge is drawn, so it
cannot depend on the challenge. It stops on a register `u` with one continuation for each
challenge, and every continuation starts on `u`. This is record D4's slot discipline with the
register as an index. The output family `Out tr u` may depend on the final register. A prover
whose output is a quantum state hands that state to the next stage of a composed protocol through
this register.

The local signature `L` has operations in `Type 1` and outcomes in `Type`: for instance
`LocalSig.instruments.{0}` (any subinstrument with outcomes in `Type`) or a gate set. The
definition only closes if one slot maps leaves in `Type 1` to a program in `Type 1`, which holds
after the PolyFun fix of section 7. A classical prover lives in the universe of its messages,
`Type` for ArkLib's protocols, because `OracleComp oSpec : Type → Type`. The quantum prover lives
one universe higher, in `Type 1`, because each node of a quantum program records its register and
`QReg : Type 1` (a register carries its carrier type). That is a fixed floor, not a climb: moves,
challenges and transcripts stay in `Type`.

The run against a classical verifier is one quantum program:

```lean
-- intended, not existing (ArkLib/Interaction/Core/Quantum/Run.lean)
def QProver.run (q : ∀ B, QueryImpl oSpec (QComp spec B B))
    (p : QProver L spec s Out R) (v : Sampler l (OracleComp oSpec) s) :
    QuantumComp L' spec (fun u => (tr : PathAlong l s) × Out tr u) R
```

At a challenge node the sampler's coins are drawn by the instrument `SubInstrument.uniform`, which
leaves the register untouched (`VCVio/Quantum/Oracle/ClassicalCalls.lean`). The classical sampler
runs on whatever register the prover holds, through `OracleComp.toQuantumAt`
(`VCVio/Quantum/Oracle/Classical.lean:580`) with `q` answering its `oSpec` queries; `QComp.coinImpl`
answers uniform coins. The decision then runs on the final register in the same way, as VCVio's
`Quantum.experiment` runs a classical challenger after a quantum adversary
(`VCVio/Quantum/VC/MultiExtractable.lean`). The verdict's distribution is the outcome measure of
this program under a quantum runtime (`VCVio/Quantum/Comp/Runtime.lean`), from an initial state
`ρ` on `R`.

Classical provers embed. `QProver.ofClassical p R` runs each classical slot on the held register
`R` through `toQuantumAt`, and

```lean
-- intended, not existing
theorem QProver.run_ofClassical :
    (QProver.ofClassical p R).run q v = (run p v).toQuantumAt q   -- program equality
```

so every classical prover is a quantum prover whose register never changes. With the agreement
theorem of section 7, the two runs have the same verdict distribution.

### 3. Security notions take an adversary model

Record D7 states each notion once, against an adversary model:

```lean
-- intended, not existing (ArkLib/Interaction/Core/Security/Model.lean)
structure AdversaryModel (V : Verifier l s) where
  Adv : Type*
  /-- The subprobability distribution of (transcript, verdict, prover output). -/
  outcome : Adv → StmtIn → Measure (Observation V)
```

- *Classical model* (the default, and the one the legacy embedding targets). `Adv` is D7's class
  of focal strategies in `OracleComp oSpec`, and `outcome` is `evalDist` of the run under the
  ambient implementation.
- *Quantum model.* `Adv` is a register `A`, an initial substate `ρ` on `A`, and a quantum prover on
  `A`, quantified over all of them, as VCVio quantifies its adversaries
  (`VC/MultiExtractable.lean`, "Conventions"). `outcome` is the outcome measure of
  `QProver.run`.

`soundness M ε` and `completeness M ε` take the model as an argument; `knowledgeSoundness M I κ`
also takes an extraction interface `I` over the model (section 4).
They are stated through `outcome`, the law of the whole run, and never through a per-slot
semantics. For `OracleComp`, `evalDist` is a monad morphism and proofs may factor it slot by slot.
For quantum programs the observation is not a monad morphism: what follows a slot depends on the
register state the slot leaves, which its classical outcome does not determine. So a generic lemma
that rewrites `outcome` with an `evalDist_bind`-style law would be false for the quantum model.
The round-by-round notions do not: their error bounds the flip probability of a fixed prefix
over a fresh challenge alone (record D7), so they say nothing about the prover's computation
model.

The quantum model quantifies over every initial register and substate because sequential
composition needs it. After the prefix, the suffix adversary starts on the register the prefix
left, in the state conditioned on the prefix transcript. That state is an arbitrary substate, and
it is not entangled with the verifier, who is classical.

### 4. Extractors: what a model lets them do

An extractor's power has four parts: what it computes with, what it sees of the finished run,
whether it can re-enter the adversary (rewinding), and what it must achieve at what cost. The
adversary model fixes the first and limits the other three. Within one model several choices
remain (straight-line or rewinding, with or without query logs), so they form a separate structure
over the model, an *extraction interface*:

```lean
-- intended, not existing (ArkLib/Interaction/Core/Security/Model.lean)
structure ExtractionInterface (M : AdversaryModel V) where
  /-- Extractors: programs over the interface's access operations. -/
  Ext : Type*
  /-- The extraction experiment: the law of the run together with the extracted witness. -/
  experiment : Ext → M.Adv → StmtIn → Measure (Observation V × WitIn)
  /-- Expected number of access operations an extractor makes; zero for straight-line ones. -/
  cost : Ext → M.Adv → StmtIn → ℝ≥0∞
```

`knowledgeSoundness M I κ` asks for one extractor `E : I.Ext` such that, for every adversary and
input, the run inside `I.experiment` is the model's run (the first marginal is `M.outcome`) and the
probability of acceptance with `(x, w) ∉ R` is at most `κ`. The first clause matters: without it an
extractor could make the run reject and meet the bound trivially. Classical interfaces satisfy it
exactly, because the extractor acts only after the run or only reads it. The QROM interface below
satisfies it up to a distance `δ`, carried as a parameter.

**1. What it computes with.** In the classical model an extractor is an `OracleComp` program. In
the quantum model it is a quantum program, which may hold the adversary's register as a subsystem
through VCVio's framing (`QuantumComp.lift`, `VCVio/Quantum/Comp/Lift.lean`). That is where
quantum reductions live. A classical extractor is a quantum one through `toQuantumAt`.

**2. What it sees of the finished run.** Always the input statement, the transcript and the
prover's classical output. The classical model can also hand it the prover's `oSpec` query log,
as legacy `Extractor.Straightline` does. A quantum prover leaves no query log, because recording
superposition queries disturbs them. With an emulated quantum random oracle the extractor instead
calls an extraction port of the emulator, as in `Quantum.extractQuery`
(`VCVio/Quantum/VC/MultiExtractable.lean`). Calling it measures the emulator's database, which can
change the rest of the run; hence the `δ` above.

**3. Whether it can re-enter the adversary.** This is decided by the type of what the adversary
leaves at a challenge node, so it needs no flag.

- *Classical.* The challenge slot returns a value `f : (x : C) → Strategy (k x) _`. A value can be
  used any number of times. Applying `f` to a second challenge after the first run is rewinding to
  that node, keeping everything the prover did before it, including the coins it drew. What
  happens to the coins it draws after the fork is the reset policy of the rewinding engine (issue
  #1410): a frozen world (fixed tape, the 2026-10-28 decision) or fresh coins. Rewinding
  extractors are programs over access operations (run a slot, apply a continuation to a chosen
  challenge), interpreted against the adversary, as the engine's `rerunSpec` does. So an extractor
  cannot inspect the prover's code, and `cost` counts operations.
- *Quantum.* The challenge slot returns, on the register `u` it ends on, a classical function
  `f : (x : C) → QProver (k x) _ u`, together with the state of `u`. The function is a program
  value and can be copied. The state cannot. `f x₁` starts on `u` and ends on some register `u₁`,
  while `f x₂` needs `u` in the state it had before `f x₁` ran. `QuantumComp` has no instruction
  that copies a register's state, and its instruments have no inverses, so no extractor program
  produces that state. Rewinding does not typecheck; this is no-cloning, plus the measurement of
  the message. Quantum rewinding needs an interface with more operations: each slot presented as
  an isometry followed by a measurement of the message, and the extractor allowed the isometry's
  adjoint and binary projective measurements of its choice (Unruh 2012; Chiesa–Ma–Spooner–Zhandry
  2021, Def 3.7). That interface only exists over a smaller class of adversaries, the
  unitary-presented ones. A normal-form theorem (Stinespring dilation, obligation 6 of VCVio's
  `quantum-layer.md`) would show that every `QProver` on finite registers has an equivalent
  unitary presentation.

**4. What it must achieve, at what cost.** Straight-line interfaces use the bound above with
`cost = 0`. The classical rewinding interface runs the adversary once and, on acceptance,
re-enters it; `cost` is the expected number of slot executions, with the worst-case bound from the
truncation corollary (2026-10-28 decision). Quantum rewinding needs a different statement
(CMSZ21 Def 3.6): given `1/ε`, the extractor outputs a witness with probability polynomial in
`ε − κ`, where `ε` is the acceptance probability from the adversary's state. The main run's
measurements disturb that state, so the coupled bound above does not apply.

| Interface | Model | Sees | Re-entry | Statement |
|---|---|---|---|---|
| Straight-line, transcript | classical and quantum | statement, transcript, output | none | coupled |
| Straight-line, query log | classical | also the `oSpec` query log | none | coupled (legacy `Extractor.Straightline`) |
| Rewinding | classical | also the logs of reruns | continuations reused; reset policy | coupled after the main run; expected and truncated run counts |
| QROM extraction port | quantum, emulated oracle | also the extraction port | none | coupled, run preserved up to `δ` |
| Unitary rewinding (later) | quantum, unitary-presented provers | statement, transcript, output | isometry adjoints, binary measurements | CMSZ21 Def 3.6 |

The three classical interfaces are nested: an extractor that reads only the transcript is also a
query-log extractor, and a query-log extractor is also a rewinding extractor that never re-enters.
So knowledge with a weaker interface implies knowledge with a stronger one. Straight-line
knowledge with the transcript interface transfers from the classical to the quantum model by the
game-value theorem (section 5).

### 5. What transfers to quantum provers for free

**Theorem (game value).** For a protocol without a shared oracle (`oSpec` empty), let `val s` be
the value of the game: the supremum over moves at message nodes, the average over the fresh
challenge at challenge nodes, and the indicator of the bad event (acceptance of a false claim, or
acceptance with an extraction failure) at the leaf. Then the bad-event probability of every
quantum prover, from every initial substate, is at most `val s`.

*Proof sketch.* By induction on the tree. At a message node the program's outcome measure splits
over the measured message `x` into weights `w_x` with `Σ w_x ≤ 1`, and each branch continues from
a substate of the same trace as its weight, so the bad-event probability is at most
`Σ w_x · val (k x) ≤ sup_x val (k x)`. At a challenge node the coin instrument scales the state by
`1/|C|` on each outcome and does not touch the register, so the probability is the average over
challenges of the continuations' probabilities. At the leaf it is the indicator. ∎

Deterministic classical provers attain `val s` up to any `δ > 0`: choose a `δ`-optimal move at
each message node. So:

- *IT soundness transfers.* Soundness `ε` against all classical provers implies soundness `ε`
  against all quantum provers. The same argument does not assume a public-coin verifier, but our
  verifiers are public-coin anyway.
- *Straight-line IT knowledge soundness transfers*, when the extractor reads only the transcript and
  the prover's classical output. The bad event is still a function of the transcript and that
  output, so the same game-value bound applies.
- *Round-by-round soundness and knowledge* imply classical soundness and knowledge by the usual
  union bound over challenge nodes, and hence, by the game-value theorem, the same bounds against
  quantum provers.

No paper states this lift as a lemma; it is used implicitly (Don–Fehr–Majenz–Schaffner 2019,
Thm 8; Chiesa–Manohar–Spooner 2019 and Chiesa–Di–Hu–Zheng use round-by-round soundness of the IOP
as a classical property). The usual argument builds a classical behavioural strategy from the
conditional laws of the quantum prover's messages, which needs conditional quantum states. The
game-value argument above needs only that a run's outcome measure is linear in the initial state
and splits over branches, both already in VCVio's runtime semantics.

This covers ArkLib's IOPs and IPs (Sumcheck, FRI, STIR, WHIR and the rest), all of which are
proved in the information-theoretic setting.

### 6. What does not transfer, and where it is handled

- *Shared random oracles.* With an `oSpec` shared by prover and verifier, the game-value argument
  fails: the prover's queries correlate with the verifier's. Post-quantum security of Fiat–Shamir
  and BCS is a quantum random oracle model theorem. In the known proofs (Chiesa–Manohar–Spooner
  2019 for BCS; Don–Fehr–Majenz–Schaffner 2019 for Fiat–Shamir; Chiesa–Di–Hu–Zheng, ePrint
  2025/2166, for multi-extractable vector commitments) the adversary is one non-interactive
  quantum program with oracle access. These proofs reduce it, through the compressed oracle, to a
  classical round-by-round or state-restoration bound on the underlying protocol. The quantum
  adversary there is a VCVio program, not an interaction-layer strategy. What the interaction layer
  owes those theorems is the classical round-by-round notion of record D7, unchanged. The chain in
  Chiesa–Di–Hu–Zheng is: round-by-round knowledge implies post-quantum state-restoration knowledge
  with an `O((t + k)² ε)` loss for `t` queries and `k` rounds, tight by Grover (Thms 6.9, 6.10);
  that, with a post-quantum extractable vector commitment, gives adaptive knowledge of BCS
  (Thm 11.3; Merkle error `O(t³ / 2^σ)`, Thm 8.3, the target of VCVio's
  `VC/Merkle/MultiExtractable.lean`). Post-quantum state restoration queries one challenge oracle
  on (round, input, output) with the round in superposition. VCVio has no coherent choice of port
  (open obligation 2 of `quantum-layer.md`), so that oracle is one port on the product, served by
  its own runtime. The state-restoration game belongs in ArkLib (milestone 2) and should be stated
  over an oracle-access model, with a classical and a quantum instance.
- *Extractors that read query logs, and rewinding extractors.* Both are classical-model
  interfaces (section 4). A quantum prover leaves no query log, and the quantum model's general
  provers cannot be re-entered. Quantum rewinding (Unruh's rewinding for strict soundness,
  collapsing commitments, Chiesa–Ma–Spooner–Zhandry 2021 for Kilian's protocol,
  Lai–Malavolta–Spooner 2022 for many-round protocols) is research-level. It needs the
  unitary-presentation interface and the CMSZ21 statement of section 4, both of which can be added
  later as a second interface and knowledge notion over the quantum model.

### 7. Dependencies

- **PolyFun.** `IFreeM` (`PolyFun/IPFunctor/Free/Family.lean:45`), `IPFunctor.FreeM`
  (`Free/Basic.lean:45`) and `FreeM₂` (`Free/Indexed.lean:57`) are declared in
  `Type (max uI uA uB (v + 1))`. The `+ 1` is not needed: a leaf stores `x : X s : Type v`, and the
  family `X` is a parameter, not a field. It has been there since `IPFunctor` was added (PolyFun
  #4), with no stated reason. The fix declares all three in `Type (max uI uA uB v)`. Checked: PolyFun
  main afb9c1e5 builds in full with the change (2602 jobs). Why `QProver` needs it: its defining
  equation puts `QProver` of the children inside the leaves of a `QuantumComp`, so it needs one
  universe `w` with `QuantumComp L spec : (QReg → Type w) → QReg → Type w`. With the `+ 1` no such `w`
  exists ("failed to solve universe constraint 1 =?= 2"); without it `w = 1` works.
- **VCVio.** An agreement theorem for the classical embedding: running
  `toQuantumAt oa coinImpl` gives the outcome distribution `evalDist oa`. Today only the branch
  form `exists_branch_run₂_toQuantumAt_coinImpl_eq_smul` (`VC/Proof/Extraction.lean:292`) exists.
  This extends open obligation 4 of `docs/design/quantum-layer.md`. Separately, the PolyFun fix
  changes two declared universes: `QuantumComp` and `QuantumComp₂` become
  `Type (max 1 u v u₁ v₁ w)` (the `1` because `QReg : Type 1`). `QComp` keeps `Type (max u₁ v₁ (w + 1))`,
  since its local operations `LocalSig.instruments.{w}` lie in `Type (w + 1)`. Checked: with
  VCVio's PolyFun pin (4181c822) patched and those two declarations changed, VCVio's 73 quantum and
  quantum-dependent modules build (3820 jobs). Against those definitions, the section 2 prover over
  `QuantumComp LocalSig.instruments.{0} spec` (on a toy protocol tree) elaborates in `Type 1`, its
  classical analogue over `OracleComp` in `Type`, and a `QComp` slot with `Type 1` leaves fails at
  `Type 2`.
- **ArkLib.** `Interaction/Core/Quantum/{Prover,Run,Embed,GameValue}.lean`, after milestone 1.

## Why

**Why only the prover is quantum.** Every target application has classical messages and a
classical verifier: post-quantum soundness of IOPs, IPs and interactive arguments, and classical
verification of quantum computation. Making the verifier quantum would require two quantum parties
in one run (framing both registers), and no client needs it.

**Why a separate prover type and not a generalization of P.** P's strategies, run and composition
laws are built on PolyFun's generic `InteractionOver.run` over an ordinary monad. Indexing the
effect by registers would generalize that generic runner and every law in P, and PolyFun would need
a lawful indexed-monad class in McBride's style. PolyFun has Atkey's `IndexedMonad`
(`PolyFun/Control/Monad/Indexed.lean`) and the free `IFreeM`, but no such class. The classical
milestone needs none of this. `QProver` is the general definition (registers vary), and the
classical prover embeds into it by `ofClassical`, which keeps the restricted form a derived case.
If a second indexed effect appears (for instance resource-graded strategies), P's API can be
generalized then and `QProver` becomes its instance.

**Why not a fixed register** (`m := QComp spec A A`). It cannot be P's monad as things stand:
`QComp spec A A : Type w → Type (w + 1)` (`VCVio/Quantum/Comp/Basic.lean:570`), while P's strategies
need `m : Type u → Type u`, and the universe fix of section 7 does not change that: `QComp` takes
its local operations from `LocalSig.instruments.{w}`, which lie in `Type (w + 1)`. After the fix,
`QuantumComp₂ LocalSig.instruments.{0} spec A A` maps `Type 1` to `Type 1` and would fit. It is the
smallest change, but it fixes one
register for the whole interaction and makes a theorem out of the general case: that every prover
can be padded into a common register. That theorem fails without a bound on the registers reached
(the same obstacle as obligation 1 of `quantum-layer.md`).

**Why the definitions take a model.** The notions are the same sentence with a different class of
adversaries and a different semantics. One definition with a model argument avoids parallel
classical and quantum definitions. The legacy transfers of record D7 are stated for the classical
model.

## Alternatives considered

- **Generalize P to register-indexed effects now.** One API for both. Rejected for now: it
  rewrites P and PolyFun's generic runner for a feature the first milestone does not use.
- **Fixed-register quantum provers as P strategies.** Rejected: it restricts the definition, and it
  needs the same universe fix.
- **Quantum verifiers and quantum messages.** Out of scope; see section 1.

## Consequences

- Record D7 states completeness, soundness and knowledge against an `AdversaryModel`. Its current
  adversary class becomes the classical model, and its legacy transfers are classical-model
  theorems. Round-by-round notions are unchanged.
- Knowledge soundness takes an extraction interface over the model. A defines the classical
  straight-line interfaces (transcript only, and with query logs); the rewinding interface comes
  with the rewinding engine (issue #1410).
- P, B and C are unaffected. A defines `AdversaryModel` and the classical model; the quantum
  model, `QProver`, the embedding and the game-value theorem come after milestone 1.

## Open points

- Composition of compiled protocols under a quantum random oracle. The composed verifier decides at
  the end (record D5), so in a compiled run the prefix decision's oracle queries move past the
  suffix's run. In the standard presentation of the quantum random oracle (a uniformly random
  function, queried by a fixed unitary) the verifier's classical queries are deterministic in the
  function and leave the adversary's register alone, so the move should preserve the distribution.
  In the compressed-oracle runtime it is not a program equality. To check when the compiled layer
  is written; the IOP-layer law is unaffected.

- Whether `AdversaryModel.outcome` lands in `Measure` (as the quantum runtime's
  `outcomeMeasure`) or in `SPMF` with a bridge. The classical layer uses `SPMF`; the quantum layer
  uses `Measure` because outcome types may be uncountable. Default: `Measure`, with the classical
  model's `outcome` as `evalDist` pushed to a measure.
- Universe placement: whether ArkLib's protocols should be universe-polymorphic enough to host
  `Type 1` outputs, or whether `QProver`'s outputs stay at `Type 1` through `ULift`.
