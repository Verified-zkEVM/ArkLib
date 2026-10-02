# Program logic: completeness and bounds with `prvcgen`

Many statements in ArkLib are about the possible outputs of one oracle computation: perfect
completeness, the support of an honest execution, correctness of a commitment scheme, or an event
that never happens. VCVio's `prvcgen` proves them by running Lean's verification-condition
generator `vcgen` through the program. The proof then states what is specific to the protocol and
leaves the monadic bookkeeping to the tactic, so there is no chain of `mem_support_bind_iff` peels.

Import `ArkLib.OracleReduction.ProgramLogic`. It re-exports `prvcgen` and adds two facts for
reduction executions: `Reduction.run_run_eq`, which states `Reduction.run` as one oracle
computation, and `ProtocolSpec.Necessary.Spec.getChallenge`, a rule saying a verifier challenge
may be any value.

## What `prvcgen` proves

`prvcgen` reads the goal and states it as a core triple in the matching reading of an oracle
computation:

| Goal | Reading |
|------|---------|
| `Pr{…}[p] = 1`, `∀ x ∈ support oa, p x` | every possible output (necessary) |
| `0 < Pr{…}[p]`, `∃ x ∈ support oa, p x` | some possible output (possible) |
| `r ≤ Pr{…}[p]` | expectation lower bound |
| `Pr{…}[p] ≤ ε`, `Pr{…}[p] = 0` | expectation upper bound |
| `Pr{…}[p] = c` | both bounds |

`vcgen` then walks the program's own `do` blocks: binds, `if` and `match`, uniform draws, oracle
queries, lifts between oracle worlds, and verifier challenges. It leaves one verification
condition per path, stated about the values the program produced. A sub-program it cannot see
into, such as a prover's run or a `simulateQ` of an unknown computation, stops it unless a rule
for that sub-program is passed in brackets; `OracleComp.Necessary.Spec.ofSupport oa` and
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

This is `CoordinateWise.CommittedScalar.reduction_run_support`. The proof it replaces peeled the
same program in 27 lines. Variations:

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

The earlier proof took 57 lines of support peeling.

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

## What stays outside `prvcgen`

- **Program equalities** between two games, such as bind swaps and shared prefixes, are VCVio's
  `prrw`, its couplings (`rvcgen`), or `=ᵈ`. `prvcgen` refuses an equation between two programs'
  probabilities.
- **Round invariants** over `Prover.runToRound` still take an induction on the round.
- **Counting arguments inside one draw**, such as Schwartz–Zippel or a uniform challenge hitting
  a small set, are ordinary probability lemmas (see
  [`probability-conventions.md`](probability-conventions.md)). `prvcgen` brings a proof to
  that point.
