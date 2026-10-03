# Program logic: completeness and bounds with `prvcgen`

Many statements in ArkLib are about the outputs of one oracle computation: perfect completeness,
the support of an honest execution, correctness of a commitment scheme, an event that never
happens, or a bound on the probability of an event. VCVio's `prvcgen` proves them by running Lean's
verification-condition generator `vcgen` through the program. The proof then states what is
specific to the protocol and leaves the monadic bookkeeping to the tactic, so there is no chain of
`mem_support_bind_iff` peels.

Import `ArkLib.OracleReduction.ProgramLogic`. It re-exports `prvcgen` and adds two facts for
reduction executions: `Reduction.run_run_eq`, which states `Reduction.run` as one oracle
computation, and `ProtocolSpec.Necessary.Spec.getChallenge`, a rule saying a verifier challenge
may be any value.

## What `prvcgen` proves

`prvcgen` reads the goal and states it as a core triple in the matching reading of an oracle
computation:

| Goal | Reading |
|------|---------|
| `Pr{…}[p] = 1` (uniform answers), `∀ x ∈ support oa, p x` | every possible output (necessary) |
| `0 < Pr{…}[p]` (uniform answers), `∃ x ∈ support oa, p x` | some possible output (possible) |
| `r ≤ Pr{…}[p]`, `Pr{…}[p] ≥ r` | expectation lower bound |
| `r ≤ 𝔼{…}[g]`, `r ≤ wp⟦oa⟧ g` | expectation lower bound |
| `Pr{…}[p] ≤ ε`, `Pr{…}[p] = 0` | expectation upper bound |
| `Pr{…}[p] = c` | both bounds |

An expectation `𝔼{…}[g]` or `wp⟦oa⟧ g` stands wherever `Pr{…}[p]` does, so an upper bound on an
expectation is read in the upper-bound reading as well. Without uniform answers, `prvcgen` splits
`Pr{…}[p] = 1` into its two bounds.

`vcgen` then walks the program's own `do` blocks: binds, `if` and `match`, uniform draws, oracle
queries, lifts between oracle worlds, and verifier challenges. It leaves one verification
condition per path, stated about the values the program produced. A sub-program it cannot see
into, such as a prover's run or a `simulateQ` of an unknown computation, stops it unless a rule
for that sub-program is passed in brackets. `OracleComp.Necessary.Spec.ofSupport oa` and
`OracleComp.Upper.Spec.ofSupport oa` read such a program through its support. VCVio's guide,
`docs/agents/program-logic.md` in the VCVio repository, lists the rules and the forms `prvcgen`
accepts.

## The recipe for an honest execution

The support of an honest run takes four lines. Rewrite the run into one computation with the
verifier's value in place, state the honest prover's run in closed form with the protocol's own
round-unfolding lemma, and let `prvcgen` walk the challenge draws:

```lean
lemma reduction_run_support (stmt : Stmt) (wit : WitIn) (hdir : …) :
    ∀ x ∈ support ((reduction K computeW).run stmt wit).run,
      ∃ c : Challenge, x = some (…) := by
  simp only [Reduction.run_run_eq, reduction, verifier, Verifier.run, OptionT.run_pure]
  rw [prover_run_eq K computeW stmt wit hdir]
  prvcgen
  exact ⟨_, rfl⟩
```

This is `CoordinateWise.CommittedScalar.reduction_run_support`. Variations:

- **A prover-first, one-message protocol** has its run in closed form already:
  `Prover.run_of_prover_first` (with a `ProverOnly` instance) goes in the first `simp only`.
- **A prover with no closed form**, such as one with many challenge rounds, enters through its
  support: `prvcgen [OracleComp.Necessary.Spec.ofSupport (Prover.run _ _ _)]`. The prover's own
  support lemma then closes the verification condition.
- **A verifier that can reject**, `if c then pure a else failure`, is split into one verification
  condition per branch once `apply_ite OptionT.run`, `OptionT.run_pure` and
  `OptionT.run_failure` bring the `if` to the top of the lifted run.

## A whole game: KZG correctness

`KZG.CommitmentScheme.correctness` reduces the correctness game to the possible outputs of the
unsimulated computation. `prvcgen` then walks key generation, the commitment and the one-message
opening. The only mathematical input is the pairing check at each trapdoor:

```lean
  refine OptionT.prEvent_mk_simulateQ_run'_eq_one_of_support _ _ _ _ ?_
  have : ProverOnly ({ dir := !v[.P_to_V], «Type» := !v[G₁] } : ProtocolSpec 1) :=
    { prover_first' := by simp }
  have hverify (τ : ZMod p) : verifyOpening pairing (g₁ := g₁) (g₂ := g₂) _ _ _ query
      (OracleInterface.answer data query) := KZG.correctness pairing hpG1 n τ data query
  simp only [kzg, Reduction.run_run_eq, Prover.run_of_prover_first, Verifier.run,
    OptionT.run_pure]
  prvcgen [Groups.sampleNonzeroZMod]
  simp [acceptRejectRel, hverify]
```

## Bounds that average over a challenge

A soundness bound `Pr{…}[p] ≤ ε` is read in the upper-bound reading. The registered rules bound a
uniform draw by its largest value, which proves events of probability zero and bounds that hold on
every path. A bound that averages over a uniform challenge passes the averaging rule
`OracleComp.Upper.Spec.uniformSample_avg` in brackets. Its precondition is the finite average
`(∑ c, post c) / Fintype.card β`. The per-challenge hypothesis is therefore stated as the same
average, and the two sums are compared term by term.

The rule needs a `Fintype` instance on the challenge type. A `SampleableType` instance makes the
type `Finite`, and `have := Fintype.ofFinite (…)` builds the `Fintype` instance from that. Without
it, `prvcgen` skips the averaging rule without a message and applies the registered rule, which
takes the largest value. From
`ProtocolSpec.prEvent_optionT_simulateQ_addLift_getChallenge_bind_some_le`
(`ArkLib/OracleReduction/Security/RbrGame.lean`):

```lean
  have := Fintype.ofFinite (pSpec.Challenge i)
  simp only [expect_norm, SampleableType.wp_uniformSample_eq_sum] at h
  prvcgen [Upper.Spec.ofSupport init, Upper.Spec.uniformSample_avg]
  refine le_trans (ENNReal.div_le_div_right (Finset.sum_le_sum fun c _ => ?_) _) h
  simp only [expect_norm]
  exact OracleComp.ProgramLogic.wp_le_const_of_support _ fun _ _ =>
    propInd_mono fun hE => ⟨_, hE⟩
```

Each term of the sum is the expectation of the opaque tail after one challenge, and
`OracleComp.ProgramLogic.wp_le_const_of_support` bounds it through the tail's support. The
sumcheck first-round bound `Sumcheck.Interaction.Native.exportedPrefixRun_soundness`
(`ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolSoundness.lean`) follows the same recipe. Its
field carries `[Fintype F]`, so it needs no `have`.

## Opaque sub-programs and your own rules

- A sub-program with no rule, such as an adversary, a key generator treated abstractly, or a
  simulated handler, is passed as `prvcgen [OracleComp.Necessary.Spec.ofSupport oa]`, or
  `OracleComp.Upper.Spec.ofSupport oa` in an upper bound. Its verification condition then
  carries `x ∈ support oa`.
- `prvcgen (errorOnMissingSpec := false)` leaves a sub-program without a rule as a verification
  condition stating its weakest precondition, instead of failing.
- A definition or equation to unfold can go in the brackets. Rewriting it first with `simp only`
  is more robust: `vcgen` matches programs syntactically and does not reduce structure
  projections such as `(reduction K computeW).prover`.
- A reusable fact about a protocol primitive becomes a rule with `@[spec]` on a core triple,
  stated in the reading it belongs to. `ProtocolSpec.Necessary.Spec.getChallenge` in
  `ArkLib/OracleReduction/ProgramLogic.lean` is the pattern.

## Unreduced projections in the program

A `do` block that a rewrite produced can keep projections and redexes that `vcgen` does not see
through, in particular when the rewriting lemma is stated under
`backward.isDefEq.respectTransparency false`. `vcgen` then reports that `Std.WP.Spec.bind` is not
applicable. Reduce the block with `dsimp only` before `prvcgen`. In
`Sumcheck.Interaction.Native.exportedPrefixRun_admissibility`
(`ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolSoundness.lean`), the rewrite by
`exportedPrefixRun_firstRound` and the pattern that names the prover's first message leave
projections such as `⟨q, respond⟩.fst` in the program:

```lean
  rw [exportedPrefixRun_firstRound]
  refine (ExpectationWP.wp_bind _ _ _).trans_le
    (wp_le_of_forall_le _ fun ⟨q, respond⟩ => ?_)
  dsimp only
  prvcgen (errorOnMissingSpec := false)
```

## Bounds stated as nested expectations

An event of several draws is a nest of expectations, one per draw, and `simp only [expect_norm]`
brings an event of a `do` block into that form. A bound then descends one draw at a time with two
lemmas, which hold over any monad with lawful measure semantics. `wp_le_of_forall_le` bounds an
expectation by a constant that bounds each of its values. `ExpectationWP.wp_mono` compares two
observations of one draw pointwise. From `NativeCompositionTest.guess_soundness`
(`ArkLibTest/Interaction/CompositionSoundness.lean`), a guessing game over a generic monad `m`:

```lean
  simp only [guessVerifier, expect_norm]
  refine wp_le_of_forall_le _ fun chosen => (ExpectationWP.wp_mono _ fun sample =>
    wp_le_of_forall_le _ fun _ => ?_).trans (hsample chosen.1)
  simp [hprior]
```

The outer `wp_le_of_forall_le` fixes the prover's move `chosen`. At each challenge `sample`,
`ExpectationWP.wp_mono` compares the rest of the game with the indicator that the guess `chosen.1`
equals `sample`, and the inner `wp_le_of_forall_le` proves that comparison for every response of
the prover. The challenge bound `hsample chosen.1` finishes the proof.

`ProximityGap.exists_basepoint_with_large_line_prob_aux`
(`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineSpaces/Basic.lean`) bounds an average of
line probabilities the same way. When no basepoint `a` has a line probability above `ε` (`hno a`),
neither does their average:

```lean
  simp only [P2, expect_norm]
  exact wp_le_of_forall_le _ fun a => by simpa only [expect_norm] using hno a
```

An outer draw on which the event does not depend is the expectation of a constant, which
`ExpectationWP.wp_const_of_oracle` evaluates for an oracle computation. The same proof uses it in
`simp only [expect_norm, hconst, ExpectationWP.wp_const_of_oracle]`.

## What stays outside `prvcgen`

- **Program equalities** between two games, such as bind swaps and shared prefixes, are VCVio's
  `prrw`, its couplings (`rvcgen`), or `=ᵈ`. `prvcgen` refuses an equation between two programs'
  probabilities.
- **Round invariants** over `Prover.runToRound` take an induction on the round.
- **Counting arguments inside one draw**, such as Schwartz–Zippel or a uniform challenge hitting
  a small set, are ordinary probability lemmas (see
  [`probability-conventions.md`](probability-conventions.md)). `prvcgen` brings a proof to
  that point.
