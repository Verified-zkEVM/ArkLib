# D4. The paired run with uniform effect slots, and the passive verifier

**Status:** Proposed: awaiting maintainer approval.
**Implemented by:** PolyFun PR P (commit 3, syntax and run; commit 5, public-coin replay and swap)
and ArkLib PR A (commits 2–3, plain execution and the passive oracle verifier). ArkLib PR B uses
the slot correspondence below to embed legacy provers.

## Decision

**Uniform effect slots.** A strategy has one effect slot at every *boundary* between events, for
each party: one before every node and one at the end. On a path with `n` moves a party has
`n + 1` slots. Every node is wrapped the same way:

```lean
-- intended, not existing
-- Strategy of participant `who` on tree `s`, with output family `Out : PathAlong l s → Type u`.
Strat l who (pure _) Out    = m (Out ⟨⟩)                                            -- leaf
Strat l who (roll a k) Out  =
  if who owns a  then m ((x : Move l a) × Strat l who (k (l.toFunB a x)) (Out ∘ cons x))
  else                m ((x : Move l a) → Strat l who (k (l.toFunB a x)) (Out ∘ cons x))
```

`who owns a` is computed from `owner l a` (record D2). Each continuation is again a strategy, so
it starts with its own slot; an observer reacts to the move `x` in its next slot.

**Run schedule.** The run is defined from generic `InteractionOver.run`
(`Interaction/Basic/Interaction.lean:111`), whose leaf collector is pure; the collected leaf
actions are executed afterwards in the schedule's order. The run takes a schedule, and `run` is
the focal-first instance:

```lean
-- intended, not existing
inductive Schedule | focalFirst | counterpartFirst
runWith (sched : Schedule) : Strat l .focal s OutP → Strat l .counterpart s OutC →
    m ((tr : PathAlong l s) × OutP tr × OutC tr)
abbrev run := runWith .focalFirst

run_done   : run p c = do let a ← p; let b ← c; pure ⟨⟨⟩, a, b⟩
run_owner  : -- focal owns `a`
  run p c = do let ⟨x, p'⟩ ← p; let f ← c; let ⟨tr, a, b⟩ ← run p' (f x); pure ⟨cons x tr, a, b⟩
run_observ : -- counterpart owns `a`
  run p c = do let f ← p; let ⟨x, c'⟩ ← c; let ⟨tr, a, b⟩ ← run (f x) c'; pure ⟨cons x tr, a, b⟩
```

Under `run`, at each boundary the focal slot runs, then the counterpart slot, then the move is
exchanged; at the end the focal leaf runs, then the counterpart leaf. `runWith
.counterpartFirst` swaps the first two binds in each equation. The default is focal-first
because that schedule makes sequential composition exact under `LawfulMonad` (record D5).

**Exchanging the schedules.** The two schedules agree whenever, at every boundary, the
counterpart's slot commutes with the focal party's slot:

```lean
-- intended, not existing (PolyFun PR P, next to `runWith`)
theorem runWith_focalFirst_eq_counterpartFirst (p c)
    (hcomm : at every boundary, the counterpart slot commutes with the focal slot) :
    runWith .focalFirst p c = runWith .counterpartFirst p c
```

For the ArkLib sampler the hypothesis is discharged in two ways. (a) As program equality whenever
the prover's slots at challenge nodes are `pure`: the sampler's slots elsewhere are `pure`, so
only challenge nodes matter, and a `pure` slot commutes with anything under `LawfulMonad`. (b) As
equality in distribution for an arbitrary prover, when the challenge implementation is stateless
and separate from the shared-oracle state, as in the legacy experiment's
`QueryImpl.addLift impl challengeQueryImpl` (`Security/Basic.lean:95`). The monad-generic lemma
belongs to P; the distributional form (b) belongs to ArkLib PR B, and the VCVio lemmas it needs
are unverified.

**Zero rounds.** On `s = pure _` the run is `run_done`: each leaf action executes exactly once.

**Swap.** With `l.swapOwners` from record D2, a focal strategy for `l` is a counterpart strategy
for `l.swapOwners` with the same type, and conversely. The exchange law is stated against the
schedule, not as an unconditional equation:

```lean
-- intended, not existing
theorem run_swap (p c) :
  runWith .focalFirst (l := l) p c =
    (fun ⟨tr, b, a⟩ => ⟨tr, a, b⟩) <$> runWith .counterpartFirst (l := l.swapOwners) c p
```

**Totality.** A generic `m` can fail. Any statement that a run reaches the end carries an explicit
totality premise. Protocol rejection (the decision returning `none`, below) is distinct from
ambient failure or missing probability mass.

**Passive verifier.** A verifier has two parts.

- *Sampler:* the public-coin counterpart determined by the signature. At a challenge node its
  slot queries the challenge oracle for that node and sends the answer; at message and oracle
  nodes its slot is `pure` and it ignores the move; its leaf is `pure ⟨⟩`. Fiat–Shamir later
  changes only the implementation of the challenge oracle.
- *Decision:* `decide : StmtIn → (p : Path s) → View s p → OptionT (OracleComp (oSpec +
  [OStmtIn]ₒ + oracles s p)) StmtOut`, run once after the interaction on the shape path and the
  verifier view of the run (record D3). Public messages and challenges are values; oracle
  messages are reached only by queries to `oracles s p` (record D6).

The decision's oracle implementation is built from the same run's payloads; no other
implementation is admitted:

```lean
-- intended, not existing
def Reduction.run (R) (stmt wit) : OptionT (OracleComp (oSpec + chal)) (...) := do
  let ⟨tr, outP, ⟨⟩⟩ ← TwoParty.run (R.prover stmt wit) (sampler l s)
  let p := projectPathAlong l s tr
  let stmtOut ← simulateQ (idImpl oSpec + inputImpl oStmt + payloadImpl s tr)
    (R.decide stmt p (toView s tr))          -- `payloadImpl s tr` answers `oracles s p`
  pure (tr, outP, stmtOut)
```

Nothing rejects early. The interaction runs every round; `OptionT` failure in the decision skips
later checks of the decision only.

**Legacy slot correspondence** (used by ArkLib PR B). The legacy prover's fields are exactly
the slots of a strategy:

| Legacy prover field (`OracleReduction/Basic.lean`) | Slot |
|---|---|
| `input` (line 139), pure | None: the first node's slot plays its role |
| `sendMessage` (line 158) | The prover's owned slot at a message node, `m ((x : Move) × Cont x)` |
| `receiveChallenge` (line 161), `PrvState → OracleComp oSpec (Challenge → PrvState)` | The prover's observed slot at a challenge node, `m ((x : Move) → Cont x)`: an effect that cannot see the challenge, returning a continuation |
| `output` (line 173) | The leaf |

An effect that a strategy takes after seeing a challenge sits in the next node's slot, in both
layers. Legacy execution (`Prover.processRound`, `OracleReduction/Execution.lean:47–61`) samples
the challenge, then runs `receiveChallenge`'s effect, then applies the result to the challenge.
That is `runWith .counterpartFirst`: at a challenge node the sampler's slot (the draw) precedes the
prover's slot; at message nodes and at the leaf the sampler's slots are `pure`, so the order there
is immaterial. Hence, for every protocol shape, including protocols that open with a challenge and
protocols with consecutive challenges:

- the run of an embedded legacy reduction equals `runWith .counterpartFirst` of the embedded
  strategies, as program equality;
- translating an interaction-layer adversary into a legacy prover is exact against
  `runWith .counterpartFirst`, slot for slot.

The legacy layer is not changed. Relating either statement to the default `run` is the exchange
lemma above.

## Why

The current PolyFun syntax gives the owner `m ((d) × Cont d)` and the observer
`(d) → m (Cont d)` (`TwoParty/Syntax.lean:69–72`). There is no focal slot between the focal party's
own send and a following challenge. Adding only a leaf slot does not help: at a seam where the
prefix ends with a send and the suffix begins with a challenge, the prefix's final action has
nowhere to run except after the challenge is sampled. That is exactly the legacy seam hypothesis
`hSeam : ∀ hn : 0 < n, P₁.OutputIsPure ∨ pSpec₂.dir ⟨0, hn⟩ = .P_to_V` of `append_run_of_seam`
(`Composition/Sequential/Append/Execution.lean:1009`), which also appears in guarded completeness
(`GuardedCompleteness.lean:157`). Uniform slots give every boundary a place for each party's
effect; with the focal-first schedule the seam then needs no hypothesis (record D5). Legacy runs
counterpart-first, and `hSeam` is the cost of composing under that schedule.

The current interaction layer's verifier is an active counterpart that may reject in any round,
and `legacy-layer-limitations.md` (lines 38–42) lists the legacy verifier's acting only after the
interaction as a limitation. The rebuild reverses that judgment: the legacy shape is the intended
one. Under the commitment that nothing rejects early, the verifier needs no access at
intermediate nodes, which removes the per-node access machinery (record D6).

## Alternatives considered

- **The current owner/observer syntax plus a leaf slot.** Leaves the seam problem above.
- **The current syntax without a leaf slot,** with the prefix output produced inside the last
  node. Composition must then reorder effects across the seam, which needs
  `LawfulCommMonad` (`TwoParty/Compose.lean:57`, used at line 780).
- **An active verifier that may reject at any round.** Excluded by the no-early-rejection
  commitment; it would also need oracle access that grows during the run.
- **Private-coin verifiers.** Out of scope; no ArkLib protocol uses one. The decision may still
  use randomness through the ambient oracles.

## Consequences

- Every strategy, honest or adversarial, has the same slot structure; adversaries keep arbitrary
  private memory in their continuations.
- The sampler is the same for every verifier on a given signature, so an ArkLib verifier is
  specified by its decision. Replay of recorded challenges (P commit 5) follows a recorded
  challenge even if the stored sampler would fail.
- Party outputs stay separate (`OutputP`, `OutputC`) until an agreement theorem identifies them.

**Acceptance tests.** In P: done/owner/observer equations; a stateful trace monad showing focal
before counterpart at each boundary; zero-round leaf actions execute once; replay with a failing
sampler; ownership swap; `runWith .focalFirst = runWith .counterpartFirst` for a focal strategy
whose observed slots are `pure`. In A: the decision reaches oracle messages only by queries, answered
from the same run; verdict versus ambient failure.

## Open points

- **Open: how the challenge oracle is indexed.** "The challenge oracle at that node" may be indexed
  by node (the prefix leading to it, which Fiat–Shamir needs), by challenge carrier, or by round
  as legacy `[pSpec.Challenge]ₒ` is. The legacy embedding (record D8) needs the embedded index to
  match `ChallengeIdx`.
