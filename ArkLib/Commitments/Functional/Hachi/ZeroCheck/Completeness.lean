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
  Lemma 10), this file certifies that the honest prover is *always* accepted: the protocol object
  `nestedZeroCheckReduction` carries `relBatched` into `relNestedZeroCheck`.

  ## Why the two directions are so unequal in difficulty

  `relBatched` asserts the *polynomial identities* `H₀ ≡ 0` and `H_α ≡ 0`, so both polynomials
  vanish at **every** point — in particular at whatever `τ₀`, `τα` the verifier's challenges
  assemble. The honest direction therefore needs no probabilistic argument and no facts about the
  challenge distribution: `mem_relNestedZeroCheck_of_relBatched` below is stated for arbitrary
  evaluation points, which is exactly why completeness here is *perfect*.

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
/-- **The completeness content of the zero-check.** An honest witness for the batched identities
satisfies the point relation at *every* pair of evaluation points, so no property of the
challenges is used.

Stated for arbitrary `τ₀`, `τα` rather than for the transcript's points: that generality is the
proof that this link contributes no completeness error, and it is what lets the execution-level
statement below be about `perfectCompleteness`. -/
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

end ArkLib.Lattices.Ajtai.InnerOuter
