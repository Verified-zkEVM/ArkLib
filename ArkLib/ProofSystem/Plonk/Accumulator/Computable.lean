/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Plonk.Accumulator.Residual
public import ArkLib.ProofSystem.Plonk.Encoding.Computable

/-! # Executable Plonk accumulators

Coefficient arrays compute the numerator, denominator, honest accumulator and its two residuals.
Their interpretations agree with the mathematical polynomials.
-/

@[expose] public section

namespace Plonk.Computable

open CompPoly
open scoped BigOperators

variable {F : Type} [Field F] [BEq F] [LawfulBEq F] {n : ℕ}

/-- Compute the numerator product from the three wire polynomials. -/
def accumulatorNumerator (a : Fin 3 → CPolynomial F) (k : Fin 3 → F) (β γ : F) :
    CPolynomial F :=
  ∏ c, (a c + CPolynomial.C (β * k c) * CPolynomial.X + CPolynomial.C γ)

/-- Compute the denominator product from the wire and permutation polynomials. -/
def accumulatorDenominator (a s : Fin 3 → CPolynomial F) (β γ : F) : CPolynomial F :=
  ∏ c, (a c + CPolynomial.C β * s c + CPolynomial.C γ)

/-- The executable numerator agrees with any degree-bounded representatives of its wires. -/
theorem accumulatorNumerator_toPoly (a : Fin 3 → CPolynomial F)
    (p : Fin 3 → Polynomial.degreeLT F n) (ha : ∀ c, (a c).toPoly = (p c).val)
    (k : Fin 3 → F) (β γ : F) :
    (accumulatorNumerator a k β γ).toPoly = Plonk.accumulatorNumerator p k β γ := by
  simp [accumulatorNumerator, Plonk.accumulatorNumerator, ha]

/-- The executable denominator agrees with degree-bounded wire and permutation representatives. -/
theorem accumulatorDenominator_toPoly (a s : Fin 3 → CPolynomial F)
    (p t : Fin 3 → Polynomial.degreeLT F n)
    (ha : ∀ c, (a c).toPoly = (p c).val) (hs : ∀ c, (s c).toPoly = (t c).val)
    (β γ : F) :
    (accumulatorDenominator a s β γ).toPoly = Plonk.accumulatorDenominator p t β γ := by
  simp [accumulatorDenominator, Plonk.accumulatorDenominator, ha, hs]

/-- Interpolate the executable prefix products of numerator-to-denominator ratios. -/
def honestAccumulator (ω : F) (hω : IsPrimitiveRoot ω n) (N Q : CPolynomial F) :
    CPolynomial F :=
  interpolate (EvaluationDomain.primitiveRoot ω hω)
    (fun i => CyclicProduct.ratioPrefix (fun j => N.eval (ω ^ j))
      (fun j => Q.eval (ω ^ j)) i.val)

/-- Executable interpolation represents the honest mathematical accumulator. -/
@[simp]
theorem honestAccumulator_toPoly (ω : F) (hω : IsPrimitiveRoot ω n)
    (N Q : CPolynomial F) :
    (honestAccumulator ω hω N Q).toPoly =
      (Plonk.honestAccumulator ω hω N.toPoly Q.toPoly).val := by
  simp only [honestAccumulator, Plonk.honestAccumulator, interpolate_toPoly,
    CPolynomial.eval_toPoly]

/-- The executable accumulator has degree less than the number of rows. -/
theorem honestAccumulator_mem_degreeLT (ω : F) (hω : IsPrimitiveRoot ω n)
    (N Q : CPolynomial F) :
    honestAccumulator ω hω N Q ∈ CPolynomial.degreeLT (R := F) n :=
  interpolate_mem_degreeLT _ _

/-- Compute the boundary residual using the first-row Lagrange indicator. -/
def boundaryResidual (D : EvaluationDomain F n) (hn : 0 < n) (Z : CPolynomial F) :
    CPolynomial F :=
  interpolate D (fun i => if i = ⟨0, hn⟩ then 1 else 0) * (Z - 1)

/-- The executable boundary residual represents the mathematical residual. -/
@[simp]
theorem boundaryResidual_toPoly (D : EvaluationDomain F n) (hn : 0 < n)
    (Z : CPolynomial F) :
    (boundaryResidual D hn Z).toPoly = Plonk.boundaryResidual D hn Z.toPoly := by
  simp [boundaryResidual, Plonk.boundaryResidual, EvaluationDomain.lagrange]

/-- Compute the cyclic residual by substituting `ωX` in the accumulator. -/
def recurrenceResidual (ω : F) (N Q Z : CPolynomial F) : CPolynomial F :=
  (Z.support.sum (fun j => CPolynomial.C (Z.coeff j) *
    (CPolynomial.C ω * CPolynomial.X) ^ j)) * Q - Z * N

/-- The executable recurrence residual represents the mathematical residual. -/
@[simp]
theorem recurrenceResidual_toPoly (ω : F) (N Q Z : CPolynomial F) :
    (recurrenceResidual ω N Q Z).toPoly =
      Plonk.recurrenceResidual ω N.toPoly Q.toPoly Z.toPoly := by
  unfold recurrenceResidual Plonk.recurrenceResidual
  rw [CPolynomial.toPoly_sub, CPolynomial.toPoly_mul, CPolynomial.toPoly_mul]
  congr 2
  rw [CPolynomial.toPoly_sum, Polynomial.comp, Polynomial.eval₂_eq_sum,
    Polynomial.sum, ← CPolynomial.support_toPoly]
  apply Finset.sum_congr rfl
  intro j _
  rw [CPolynomial.toPoly_mul, CPolynomial.toPoly_pow, CPolynomial.toPoly_mul,
    CPolynomial.C_toPoly, CPolynomial.X_toPoly, CPolynomial.C_toPoly,
    CPolynomial.coeff_toPoly]

end Plonk.Computable
