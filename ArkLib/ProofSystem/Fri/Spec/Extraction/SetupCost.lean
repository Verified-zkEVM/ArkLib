/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Fri.Spec.Extraction.Cost
public import ArkLib.ProofSystem.Fri.Spec.Extraction.GeneratorCost

/-!
# Bounded extractor initialization

The final degree guard precedes coefficient copying and every domain or challenge access. The
initialization envelope includes all copied coefficients, domain seeds, cached roots, and
challenges.
-/

@[expose] public section

namespace Fri.Spec.Extractor
open Domain OracleComp OracleSpec CompPoly
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (o : ∀ j, FinalOracleStatement s ω j)
variable (α : FinalStatement F k)

/-- Copying coefficients reads each array entry and ticks once per entry and terminator. -/
theorem profile_copyCoefficients_apply (p : CPolynomial.Raw F) (kind : CostKind) :
    (profile s o α (copyCoefficients s o α p)).2 kind =
      if kind = .inl .coefficientRead then p.size
      else if kind = .inl .metadata then p.size + 1 else 0 := by
  cases kind with
  | inl kind => cases kind <;>
      simp [copyCoefficients, profile_arrayProgram_apply, embedArithmeticCost,
        arithmeticCost, ArithmeticOp.costKind]
  | inr kind => cases kind <;>
      simp [copyCoefficients, profile_arrayProgram_apply, embedArithmeticCost]

/-- Computing a cached block root uses exactly one multiplication and tick per squaring. -/
theorem profile_initRoundGenerator_apply (gen : Generator ω) (i : Fin (k + 1))
    (kind : CostKind) :
    (profile s o α (initRoundGenerator s o α gen i)).2 kind =
      if kind = .inl .mul ∨ kind = .inl .metadata then n - (s i).val else 0 := by
  cases kind with
  | inl kind => cases kind <;>
      simp [initRoundGenerator, Arithmetic.profileArithmetic_squareIter, embedArithmeticCost]
  | inr kind => cases kind <;>
      simp [initRoundGenerator, embedArithmeticCost]

/-- An explicit envelope for all input reads and arithmetic used during initialization. -/
def initializationBound (n : ℕ) {r : ℕ} (s : Fin (r + 1) → ℕ+) (d : ℕ) : Cost
  | .inl .mul => 1 + ∑ i : Fin (r + 1), (n - (s i).val)
  | .inl .inv => 1
  | .inl .coefficientRead => d
  | .inl .metadata => d + (∑ i : Fin (r + 1), (n - (s i).val)) + 2 * (r + 1) + 4
  | .inr .domainRead => 2
  | .inr .challengeRead => r + 1
  | .inr .finalPolynomialRead => 1
  | _ => 0

/-- Initialization obeys its explicit envelope even when the final degree guard rejects. -/
theorem profile_prepareInputs_apply_le (d : ℕ+) (kind : CostKind) :
    (profile s o α (prepareInputs s o α d)).2 kind ≤ initializationBound n s d.val kind := by
  by_cases hd : (finalPolynomial s o).natDegree < d.val
  · have hsize := CPolynomial.size_le_of_natDegree_lt (finalPolynomial s o) hd
    simp only [prepareInputs, profile_bind, profile_readFinalPolynomial, profile_readDegree,
      accessAnswer, hd, dite_true, profile_pure, add_zero, Pi.add_apply,
      profile_copyCoefficients_apply, profile_initGenerator, profile_arrayProgram_apply,
      profile_initRoundGenerator_apply, profile_readChallenge]
    by_cases hn : n = 0 <;>
      cases kind with
      | inl kind => cases kind <;>
          simp [initializationBound, instructionCost, AccessOp.costKind, hn,
            ← List.ofFn_eq_map, List.sum_ofFn, Fin.sum_univ_succ] <;> omega
      | inr kind => cases kind <;>
          simp [initializationBound, instructionCost, AccessOp.costKind, hn]
  · simp only [prepareInputs, profile_bind, profile_readFinalPolynomial, profile_readDegree,
      accessAnswer, hd, dite_false, profile_pure, Pi.add_apply, add_zero]
    cases kind with
    | inl kind => cases kind <;> simp [initializationBound, instructionCost, AccessOp.costKind]
    | inr kind => cases kind <;> simp [initializationBound, instructionCost, AccessOp.costKind]

end Fri.Spec.Extractor
