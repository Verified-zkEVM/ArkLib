/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.ZeroCheck.Reduction
import ArkLib.ToCompPoly.Multilinear.Basic

/-!
  # Zero-check — completeness (Hachi Figure 5)

  The honest side of the zero-check link. Where `ZeroCheck/Reduction.lean` certifies that *any*
  prover the verifier accepts yields a witness (coordinate-wise special soundness, the corrected
  Lemma 10), this file works towards the converse: that the honest prover is always accepted.

  ## What is proved here

  `nestedZeroCheckReduction_perfectCompleteness`: the honest run of Figure 5 succeeds with
  probability one, the prover's and the verifier's output statements agree, and the resulting
  statement/witness pair lies in `relNestedZeroCheck`. That is `Reduction.perfectCompleteness`
  (`OracleReduction/Security/Basic.lean`) in full, for arbitrary shared oracles `oSpec`, state
  initialization `init` and query implementation `impl`.

  It rests on two independent halves.

  * *Algebra.* `mem_relNestedZeroCheck_of_relBatched`, the relation-preservation step: an honest
    witness for `relBatched` satisfies `relNestedZeroCheck` at the statement reshaped by *any*
    pair of evaluation points. This is where the mathematics lives.
  * *Execution.* `nestedZeroCheckReduction_run_support`: an honest run cannot fail, and whatever
    challenges it draws, prover and verifier come out holding the *same* statement, with the input
    witness passed through untouched. They agree because each reads the transcript the same way —
    the prover's `Fin.castAdd`/`Fin.natAdd` split of its accumulated challenges is literally the
    one `nestedZeroCheckVerifier` applies. Proved by induction over the rounds
    (`nestedZeroCheckProver_state_eq_of_mem_support`), read off at the last round
    (`nestedZeroCheckProver_output_of_mem_support`).

  The two halves are joined by `Reduction.perfectCompleteness_of_run_support`, a general-purpose
  criterion added to `Security/Basic.lean` for this proof: to get perfect completeness it is enough
  to show that *every* possible outcome of the run succeeds and satisfies the completeness event.
  That trades the probabilistic statement for a support statement once and for all, and it holds
  for any reduction of any length over any `oSpec` — so every later link in the chain can reuse it
  rather than unfolding the execution monads by hand.

  The preceding link is closed here too. `batchReduction` / `batchReduction_perfectCompleteness`
  (bottom of this file) is the batching bridge as a protocol object and its perfect completeness,
  so the honest side reaches `relBatched` from `relLift` and the two links meet. What is *not*
  here is the composition of the two: appending completeness needs the generic
  `Reduction.append_completeness`, still `sorry` (the appended statements live in
  `HonestChain.lean` and carry the resulting `sorryAx`).

  ## Why the two directions are so unequal in difficulty

  `relBatched` asserts the *polynomial identities* `H₀ ≡ 0` and `H_α ≡ 0`, so both polynomials
  vanish at **every** point — in particular at whatever `τ₀`, `τα` the verifier's challenges
  assemble. The honest direction therefore needs no probabilistic argument and no facts about the
  challenge distribution: `mem_relNestedZeroCheck_of_relBatched` below is stated for arbitrary
  evaluation points, which is why the completeness error for this link is exactly zero. The
  `SampleableType F` hypothesis of the completeness theorem is needed only so that execution can
  draw the challenges at all, never for a property of their distribution.

  The soundness direction is the hard one for the mirror-image reason: a single evaluation
  `H₀(τ₀) = 0` does not imply `H₀ ≡ 0`
  (`MvPolynomial.exists_nonzero_vanishing_on_axis_cross`), which is what forced the repair
  documented in `ZeroCheck/Reduction.lean`. The asymmetry is structural, not an artefact of how
  much effort went into either side.

  ## Shortness

  `relNestedZeroCheck` carries the commitment's shortness index `liftShort`, which `relBatched`
  does *not* assume. It is derived here exactly as on the soundness side
  (`mem_relLift_of_relBatched`): from the range identity `H₀ ≡ 0` via
  `hZero_eq_zero_imp_liftShort`, which is what the arithmetic hypotheses `hd`, `hμn`, `hbound`,
  `hρBound` pay for.
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly CPoly ArkLib.Lattices.CyclotomicModulus
open OracleComp OracleSpec ProtocolSpec

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ} {F : Type} [Field F] [BEq F] [LawfulBEq F]
variable (m₀ m₁ : ℕ) (bound ρBound : ℕ)
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

-- `[IsCyclotomic Φ]` is needed only to synthesize the `Rq`/`wTable` instances inside the `hZero`
-- term carried by the relations, which the linter's usage analysis misses.
set_option linter.unusedSectionVars false in
/-- **The relation-preservation step of the zero-check.** An honest witness for the batched
identities satisfies the point relation at *every* pair of evaluation points, so no property of
the challenges is used.

This is the relation obligation of completeness, not completeness itself: it says nothing about
executing `nestedZeroCheckReduction`, about probability, or about the prover and verifier agreeing
on the output statement. Those are supplied by `nestedZeroCheckReduction_run_support`, and the two
are combined in `nestedZeroCheckReduction_perfectCompleteness`.

Stated for arbitrary `τ₀`, `τα` rather than for the transcript's points, so that the
execution-level proof can instantiate it at whatever the challenges assemble. -/
theorem mem_relNestedZeroCheck_of_relBatched
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ)
    (hd : 0 < Φ.φ.natDegree) (hμn : (μ + n) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (hbound : b - 1 ≤ bound) (hρBound : b - 1 ≤ ρBound)
    (X : LiftStatement Φ K.TCom F n μ) (w : LiftedWitness Φ μ n)
    (h : (X, w) ∈ relBatched Φ m₀ m₁ bound ρBound K φF b)
    (τ₀ : Fin m₀ → F) (τα : Fin m₁ → F) :
    (nestedZcMapStmt Φ m₀ m₁ X τ₀ τα, w)
      ∈ relNestedZeroCheck Φ m₀ m₁ bound ρBound K φF b := by
  simp only [relBatched, Set.mem_setOf_eq] at h
  obtain ⟨hcom, hZeroZ, hAlphaZ, hbound'⟩ := h
  refine ⟨hcom, ?_, ?_, ?_, hbound'⟩
  · exact hZero_eq_zero_imp_liftShort Φ m₀ φF b bound ρBound hd hμn hbound hρBound w hZeroZ
  · rw [hZeroZ, CMlPolynomialEval.eval_zero]
  · simp only [nestedZcMapStmt]
    rw [hAlphaZ, CMlPolynomialEval.eval_zero]

/-! ## Honest execution

The zero-check has no prover-message rounds, so an honest run only accumulates challenges. The
invariant below is what makes the prover's and verifier's output statements agree: the challenge
prefix the prover carries in its state *is* the transcript, because `Transcript.concat` and the
prover's `Fin.snoc` are the same operation. -/

set_option linter.unusedSectionVars false in
/-- **Honest-run invariant.** After `i` challenge rounds, the honest prover's state is the input
statement/witness pair together with the transcript so far — the accumulated challenges *are* the
transcript, since `Transcript.concat` is by definition the `Fin.snoc` the prover uses.

This is the bookkeeping half of the `perfectCompleteness` proof: it is what forces the prover's
output statement to coincide with the verifier's, both being `nestedZcMapStmt` applied to the same
`Fin.castAdd`/`Fin.natAdd` split of the same transcript. -/
lemma nestedZeroCheckProver_state_eq_of_mem_support {TCom Wit : Type} [SampleableType F]
    (stmt : LiftStatement Φ TCom F n μ) (wit : Wit) (i : Fin (m₀ + m₁ + 1)) :
    ∀ x ∈ support ((nestedZeroCheckProver (oSpec := oSpec) (TCom := TCom) (Wit := Wit)
        Φ m₀ m₁).runToRound i stmt wit),
      x.2 = ((stmt, wit), x.1) := by
  induction i using Fin.induction with
  | zero =>
    intro x hx
    simp only [Prover.runToRound, Fin.induction_zero, support_pure,
      Set.mem_singleton_iff] at hx
    subst hx
    refine Prod.ext rfl ?_
    funext j
    exact j.elim0
  | succ i ih =>
    intro x hx
    rw [Prover.runToRound_succ, Prover.processRound_of_dir_eq_V_to_P i rfl] at hx
    rw [mem_support_bind_iff] at hx
    obtain ⟨⟨tr, st⟩, hprev, hx⟩ := hx
    rw [mem_support_bind_iff] at hx
    obtain ⟨c, -, hx⟩ := hx
    rw [mem_support_bind_iff] at hx
    obtain ⟨f, hf, hx⟩ := hx
    rw [mem_support_pure_iff] at hx
    have hst := ih (tr, st) hprev
    simp only [nestedZeroCheckProver] at hf
    simp only [liftM, monadLift, MonadLift.monadLift] at hf
    obtain rfl : st = ((stmt, wit), tr) := hst
    subst hf
    subst hx
    rfl

set_option linter.unusedSectionVars false in
/-- **Honest prover output.** Every result of an honest run of the zero-check prover carries the
input witness unchanged and the statement reshaped by exactly the `castAdd`/`natAdd` split of the
produced transcript that `nestedZeroCheckVerifier` performs.

This is the state invariant `nestedZeroCheckProver_state_eq_of_mem_support` read at the last round
and pushed through `Prover.output`. -/
lemma nestedZeroCheckProver_output_of_mem_support {TCom Wit : Type} [SampleableType F]
    (stmt : LiftStatement Φ TCom F n μ) (wit : Wit) :
    ∀ x ∈ support ((nestedZeroCheckProver (oSpec := oSpec) (TCom := TCom) (Wit := Wit)
        Φ m₀ m₁).run stmt wit),
      x.2 = (nestedZcMapStmt Φ m₀ m₁ stmt
        (nestedZeroCheckTauZero x.1) (nestedZeroCheckTauAlpha x.1), wit) := by
  intro x hx
  simp only [Prover.run, mem_support_bind_iff] at hx
  obtain ⟨⟨tr, st⟩, hprev, hx⟩ := hx
  obtain rfl : st = ((stmt, wit), tr) :=
    nestedZeroCheckProver_state_eq_of_mem_support Φ m₀ m₁ stmt wit
      (Fin.last (m₀ + m₁)) (tr, st) hprev
  simp only [nestedZeroCheckProver, support_pure, Set.mem_singleton_iff] at hx
  obtain ⟨y, hy, hx⟩ := hx
  subst hy
  subst hx
  rfl

set_option linter.unusedSectionVars false in
/-- **Honest-run characterization.** Every element of the support of an honest execution of
`nestedZeroCheckReduction` is a success, and it is determined by the transcript alone: the input
witness is transported unchanged, and prover and verifier both output
`nestedZcMapStmt Φ m₀ m₁ X (τ₀ tr) (τα tr)`.

This is the whole execution content of completeness. Failure is impossible because the only
`OptionT` layer in `Reduction.run` comes from the verifier, and `nestedZeroCheckVerifier` is a
`pure` map with no acceptance test to fail. -/
lemma nestedZeroCheckReduction_run_support {TCom Wit : Type} [SampleableType F]
    (X : LiftStatement Φ TCom F n μ) (w : Wit) :
    ∀ x ∈ support ((nestedZeroCheckReduction (oSpec := oSpec) (TCom := TCom) (Wit := Wit)
        Φ m₀ m₁).run X w).run,
      ∃ tr : (pSpecNestedZeroCheck F m₀ m₁).FullTranscript,
        x = some ((tr,
            nestedZcMapStmt Φ m₀ m₁ X
              (nestedZeroCheckTauZero tr) (nestedZeroCheckTauAlpha tr), w),
          nestedZcMapStmt Φ m₀ m₁ X
            (nestedZeroCheckTauZero tr) (nestedZeroCheckTauAlpha tr)) := by
  intro x hx
  unfold Reduction.run at hx
  simp only [OptionT.run_bind, Option.elimM] at hx
  rw [mem_support_bind_iff] at hx
  obtain ⟨prOpt, hpr, hx⟩ := hx
  -- The prover is lifted into `OptionT`, so it never contributes a failure.
  rw [show ((liftM (Prover.run X w (nestedZeroCheckReduction (oSpec := oSpec) Φ m₀ m₁).prover) :
      OptionT (OracleComp _) _)).run
      = (Prover.run X w (nestedZeroCheckReduction (oSpec := oSpec) Φ m₀ m₁).prover) >>=
        fun a => pure (some a) from rfl] at hpr
  rw [mem_support_bind_iff] at hpr
  obtain ⟨pr, hpr, hprOpt⟩ := hpr
  rw [mem_support_pure_iff] at hprOpt
  subst hprOpt
  -- The verifier is `pure`, so neither does it.
  simp only [Option.elim_some, nestedZeroCheckReduction, nestedZeroCheckVerifier,
    Verifier.run] at hx
  simp only [ChallengeIdx, Challenge, OptionT.run_pure, liftM_pure,
    ProgrammingPolicy.empty_apply, pure_bind, Option.elim_some, Option.getM_some, support_pure,
    Set.mem_singleton_iff] at hx
  simp only [nestedZeroCheckReduction] at hpr
  have hout := nestedZeroCheckProver_output_of_mem_support Φ m₀ m₁ X w pr hpr
  exact ⟨pr.1, by rw [hx, ← hout]⟩

set_option linter.unusedSectionVars false in
/-- **Perfect completeness of the zero-check (Hachi Figure 5).** An honest prover holding a witness
for the batched identities `H₀ ≡ 0 ∧ H_α ≡ 0` is accepted with probability one, and the pair it
hands on lies in `relNestedZeroCheck`, with the prover's and the verifier's output statements
equal.

The completeness error is `0` rather than something in `1 / |F|`: `relBatched` asserts the
polynomial identities, so both polynomials vanish at *every* point, in particular at whatever
`τ₀`, `τα` the challenges assemble. `SampleableType F` is required only so that execution can draw
the challenges, not for any property of their distribution — the proof quantifies over the whole
support of the run. -/
theorem nestedZeroCheckReduction_perfectCompleteness [SampleableType F]
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ)
    (hd : 0 < Φ.φ.natDegree) (hμn : (μ + n) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (hbound : b - 1 ≤ bound) (hρBound : b - 1 ≤ ρBound) :
    (nestedZeroCheckReduction (oSpec := oSpec) (TCom := K.TCom)
        (Wit := LiftedWitness Φ μ n) Φ m₀ m₁).perfectCompleteness init impl
      (relBatched Φ m₀ m₁ bound ρBound K φF b)
      (relNestedZeroCheck Φ m₀ m₁ bound ρBound K φF b) := by
  apply Reduction.perfectCompleteness_of_run_support
  intro X w hBatched x hx
  obtain ⟨tr, rfl⟩ := nestedZeroCheckReduction_run_support Φ m₀ m₁ X w x hx
  exact ⟨_, rfl,
    mem_relNestedZeroCheck_of_relBatched Φ m₀ m₁ bound ρBound K φF b hd hμn hbound hρBound
      X w hBatched _ _, rfl⟩

/-! ## The batching bridge: the honest direction, closed

`Batch.lean` has both relation directions (`mem_relLift_of_relBatched` and
`mem_relBatched_of_relLift`), and a zero-round `ReduceClaim` link needs only the honest one:
`ReduceClaim.reduction_completeness_of_imp` consumes the forward implication
`mem_relBatched_of_relLift` alone. Taking only that direction is what keeps the range hypotheses
in a single orientation — see `batchReduction_perfectCompleteness` below, and `HonestChain.lean`
for what the two-sided reading would cost.
-/

/-- **The batching bridge as a protocol object**: the zero-round `ReduceClaim` reduction at
`mapStmt := id` and the identity witness map — the honest prover of a bridge that only changes how
the claims are *read* does nothing at all. Its verifier is `batchPackage`'s
(`batchReduction_verifier`), so the two security directions of the link cannot drift apart. -/
def batchReduction (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound)) :
    Reduction oSpec
      (LiftStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n)
      (LiftStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n)
      (!p[] : ProtocolSpec 0) :=
  ReduceClaim.reduction oSpec id (fun _ w => w)

set_option linter.unusedSectionVars false in
/-- The bridge's protocol object and its soundness certificate share a verifier. Holds by `rfl`. -/
@[simp] theorem batchReduction_verifier
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) (hn : n ≤ 2 ^ m₁) (hd : 0 < Φ.φ.natDegree)
    (hμn : (μ + n) * Φ.φ.natDegree ≤ 2 ^ m₀)
    (hbound : b - 1 ≤ bound) (hρBound : b - 1 ≤ ρBound) :
    (batchReduction (oSpec := oSpec) Φ bound ρBound K).verifier
      = (batchPackage Φ m₀ m₁ bound ρBound init impl K φF b hn hd hμn hbound hρBound).verifier :=
  rfl

set_option linter.unusedSectionVars false in
/-- **Perfect completeness of the batching bridge** (Hachi Eqs. (22)–(23)), at error exactly `0`.

An honest prover holding a lift-valid short witness is accepted with probability one and the very
same statement/witness pair satisfies the batched identities, the prover's and the verifier's output
statements being equal for the trivial reason that both are the input statement.

**Only the honest direction is used**, via `ReduceClaim.reduction_completeness_of_imp`: the content
is `mem_relBatched_of_relLift` alone, so the range hypotheses appear in one orientation only
(`bound ≤ b − 1`, `ρBound ≤ b − 1` — the declared norm bounds are dominated by the range base), and
the pull-back's arity conditions `n ≤ 2 ^ m₁` and `(μ + n)·deg φ ≤ 2 ^ m₀` are not needed at all.

That matters for the chain: a *single* parameterization serving both directions is pinned to
`bound = ρBound = b − 1` (the pull-back needs the reverse orientation); honest completeness alone
leaves `bound` free below `b − 1`. See `HonestChain.lean`. -/
theorem batchReduction_perfectCompleteness
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) (b : ℕ) (hd : 0 < Φ.φ.natDegree)
    (hbound : bound ≤ b - 1) (hρBound : ρBound ≤ b - 1) :
    (batchReduction (oSpec := oSpec) Φ bound ρBound K).perfectCompleteness init impl
      (relLift Φ bound ρBound K φF) (relBatched Φ m₀ m₁ bound ρBound K φF b) :=
  ReduceClaim.reduction_completeness_of_imp
    (relLift Φ bound ρBound K φF) (relBatched Φ m₀ m₁ bound ρBound K φF b)
    (fun X w h => mem_relBatched_of_relLift Φ m₀ m₁ bound ρBound K φF b hd hbound hρBound X w h)

end ArkLib.Lattices.Ajtai.InnerOuter
