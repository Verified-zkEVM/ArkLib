# D5. Sequential composition, prefix decomposition, and the end-decided verifier

**Status:** Proposed: awaiting maintainer approval.
**Implemented by:** PolyFun PR P (commit 4, composition and run laws; commit 5, iteration) and
ArkLib PR A (commit 4, reduction composition).

## Decision

Only trees are appended: `FreeM.append s₁ s₂` with `s₂ : Path s₁ → FreeM P PUnit` (record D0). A
suffix participant after a prefix transcript `tr₁` lives on `s₂ (projectPathAlong l s₁ tr₁)`; it
may depend on all of `tr₁` and on its own intermediate output.

**The prefix's leaf action builds the suffix strategy.** A prefix strategy whose output at `tr₁`
is a suffix strategy has a leaf of type `m (Strat l who (s₂ …) …)`. Because a strategy begins with
its own slot, that leaf is `m (m …)`. Flat composition joins the two: the prefix's leaf action
runs, then the suffix's first slot, as one slot of the composed strategy.

```lean
-- intended, not existing
Focal.compFlat :
  Strat l .focal s₁ (fun tr₁ => Strat l .focal (s₂ (proj tr₁)) (fun tr₂ => Out (append tr₁ tr₂))) →
  Strat l .focal (s₁.append s₂) Out
Counterpart.appendFlat : -- the same for the counterpart
Focal.splitPrefix : Strat l .focal (s₁.append s₂) Out →
  Strat l .focal s₁ (fun tr₁ => Strat l .focal (s₂ (proj tr₁)) (fun tr₂ => Out (append tr₁ tr₂)))
theorem compFlat_splitPrefix (p) [LawfulMonad m] : compFlat (splitPrefix p) = p
```

`splitPrefix` cuts a whole strategy at the seam. Let `σ` be the strategy's slot at the seam. The
prefix's leaf action runs `σ` and returns its result as a suffix strategy whose first slot is
`pure`: the leaf is `pure <$> σ`.

**Run laws.** At the seam the sequential run has four slots in order: focal end, counterpart end,
focal start, counterpart start. The composed run has two: (focal end, then focal start), then
(counterpart end, then counterpart start).

```lean
-- intended, not existing
-- (1) Counterpart's prefix leaf is pure: its suffix is chosen purely from its prefix output.
theorem run_compFlat_appendFlat [LawfulMonad m] (p c₁ c₂) (hc : c₁'s leaf is `pure (c₂ tr₁ ·)`) :
  run (compFlat p) (appendFlat c₁ c₂) = do
    let ⟨tr₁, p₂, mid⟩ ← run p c₁
    let ⟨tr₂, a, b⟩ ← run p₂ (c₂ tr₁ mid)
    pure ⟨append tr₁ tr₂, a, b⟩
-- (2) General counterpart: conditional on commuting its end action past the focal start slot.
theorem run_compFlat_appendFlat_of_comm [LawfulMonad m] (p c₁ c₂) (hcomm : …) : … -- same conclusion
-- (3) Arbitrary adversary: split at the seam, no purity hypothesis.
theorem run_appendFlat_splitPrefix [LawfulMonad m] (p : Strat l .focal (s₁.append s₂) Out) (c₁ c₂) :
  run p (appendFlat c₁ c₂) = do
    let ⟨tr₁, p₂, mid⟩ ← run (splitPrefix p) c₁
    let ⟨tr₂, a, b⟩ ← run p₂ (c₂ tr₁ mid)
    pure ⟨append tr₁ tr₂, a, b⟩
```

Law (1) holds because a `pure` counterpart end vanishes from both orders. The focal suffix
construction may be effectful. Law (3) holds without any hypothesis on the counterpart: the
composed seam is `σ; c₁end; c₂start`, and the sequential run of the split is
`σ; c₁end; pure; c₂start`, which is the same program. Law (3) preserves an arbitrary adversary's
actual suffix strategy and memory. No law uses `LawfulCommMonad`. Explicit laws pack separate
statement and witness outputs through `PathAlong.liftAppendProd` (record D0).

**Composed verifier.** The composed sampler is the counterpart `appendFlat` of the two samplers,
and equals the sampler of the appended tree. The composed decision is the legacy fold: decide the
prefix, then the suffix, at the end.

```lean
-- intended, not existing
def Verifier.append (V₁ : Verifier s₁ S₁ S₂) (V₂ : (p : Path s₁) → Verifier (s₂ p) S₂ S₃)
    (route : …)  -- record D6
    : Verifier (s₁.append s₂) S₁ S₃ where
  decide stmt p v := do
    let ⟨p₁, p₂⟩ := Path.split p                      -- p₂ : Path (s₂ p₁)
    let ⟨v₁, v₂⟩ := View.split v                      -- v₁ : View s₁ p₁, v₂ : View (s₂ p₁) p₂
    let mid ← liftPrefix (V₁.decide stmt p₁ v₁)
    simulateQ (route stmt p₁ v₁) ((V₂ p₁).decide mid p₂ v₂)
```

The views split along the same path split, so the prefix decision, the suffix decision and the
routing map (record D6) are all indexed by `p₁` and `p₂`, with no cast between oracle families.
`View.split` is built from `PathAlong.split` on the view transcript and the fibre equation. The
suffix part of the view transcript lies over `s₂ (projectPathAlong viewSig s₁ v₁)`, which equals
`s₂ p₁` only by the prefix's fibre equation, so `View.split` transports that transcript along the
equation. The transport is on a view transcript, inside `View.split` and its lemmas, never on an
`OracleComp` index.

If the prefix decision fails, `OptionT` skips the suffix decision; the suffix interaction has
already run. This is legacy `Verifier.append` (`Composition/Sequential/Append/Basic.lean:236`),
which also decides the prefix at the end, and its oracle form `OracleVerifier.append` (line 619).
A composed run equals the sequential run with a seam decision only after moving the prefix
decision's queries past the suffix interaction. Security of composition is proved directly on the
end-decided definition; commutativity is not assumed to identify the two.

**Iteration.** Uniform rounds use `FreeM.replicate` (`PFunctor/Free/Replicate.lean:33`), the
`PathAlong.replicate*` ledger (record D0), and `Focal.iterate`/`Counterpart.iterate` with run
equations at zero and successor. A round's carriers are fixed by the protocol parameters. Round
index, arithmetic state, challenge history and validity are strategy state.

## Why

The current PolyFun composition builds the suffix inside the last prefix node, so its run law
`run_compFlat_appendFlat` (`TwoParty/Compose.lean:643`) needs `LawfulCommMonad` (defined at line 57,
`bind_comm` used at line 780). Only the variant with a pure suffix constructor,
`run_compFlat_appendFlat_pure` (line 474), needs only `LawfulMonad`. ArkLib inherits the stronger
assumption: `Reduction.execute_then` (`ArkLib/Interaction/Reduction.lean:281`) requires
`[TwoParty.LawfulCommMonad m]`, which a monad that records query order, such as `OracleComp`,
does not satisfy. The legacy layer instead carries `hSeam` (`Append/Execution.lean:1009`). With uniform slots
(record D4) and the focal-first schedule both disappear: the seam effects run in their actual
order in both runs.

The schedule matters here. The laws above hold for `run`, which is `runWith .focalFirst`
(record D4): the composed seam then needs only the counterpart's prefix end to be `pure`, which the
sampler's is. Under `runWith .counterpartFirst` the same seam would instead need the suffix's first
counterpart slot to commute with the prover's suffix construction; when the suffix opens with a
challenge that slot is a draw, and the prover's construction may be effectful. Legacy executes
counterpart-first (record D4), and its `hSeam` (prefix output pure, or suffix opening with a
prover message) is exactly that cost. Statements about legacy runs are moved to the default
schedule by the exchange lemma of record D4.

## Alternatives considered

- **Suffix built inside the last prefix node** (current PolyFun). Needs `LawfulCommMonad`.
- **A leaf slot without uniform slots.** Leaves the legacy `hSeam` problem (record D4).
- **Counterpart-first as the default schedule** (legacy's order). Composition would need the
  commuting hypothesis above whenever a suffix opens with a challenge.
- **Deciding the prefix at the seam.** A seam decision is an early rejection point, excluded by
  the commitment that nothing rejects early, and its equality with the end-decided form needs
  commutativity of decision queries with the suffix run.
- **An optional challenge (`Option C`) to signal earlier failure.** Rejected: the Sumcheck
  decision is the legacy fold, whose failed `guard` skips later checks, not rounds.

## Consequences

- Seam effect order is preserved under `LawfulMonad` alone; legacy `OutputIsPure` and `hSeam`
  are not needed in the interaction layer.
- Security proofs for composed verifiers work on the end-decided program, as legacy proofs do.
- Sumcheck is a replicated single round with challenge-independent shape (record D1).

**Acceptance tests.** In P, with a stateful monad whose trace exposes effect order, at three seams
(an empty prefix, a prefix ending in a send, a prefix ending in a receive): leaf actions run
exactly once, at the seam, in both the composed and the sequential run; zero and several
iterations. In A: rejection in stage one does not stop the interaction of stage two; state effects
keep their order; the routing law of record D6.

## Open points

- **Open: dependent iteration state.** If convenient Sumcheck state types vary with the round
  index, iteration needs a dependent finite fold or a bounded history with a length invariant;
  the current constant-state `iterate` (`Compose.lean:1052`, `1071`) does not transport dependent
  state. The choice is made in P or C when the Sumcheck round is written.
