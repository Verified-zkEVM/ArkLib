/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.TaylorCutoff
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Parameters.GeometricCounting
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Geometry.SolutionExtension
/-!
# Prescribed inputs for correlated-agreement charts

The prescribed weighted-support certificate supplies a symbolic equation and all size
bounds
needed with Taylor cap `K = n`. The characteristic contract supplies every stage's pivots,
including after extension of the ground field. No correlated-agreement conclusion is assumed.
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon

open HiddenDerivative SymbolicReceivedInterpolation

universe u

/-- Prescribed interpolation and scalar inputs, with the Taylor cap equal to block length.
The certificate's extension universe equals the base universe, admitting its algebraic closure. -/
theorem exists_prescribed_correlated_parameters {F : Type u} [Field F]
    (δ : ℝ) (n k : ℕ) (centers : Fin n ↪ F) (f g : Fin n → F)
    (hδ : 0 < δ) (hδ' : δ < 1 / 4) (hk : 0 < k)
    (hblock : 8 * Nat.ceil
      (100 * (Nat.ceil (Real.exp ((27 / 10) / δ)) : ℝ) ^ 2 *
        harmonicNumber (Nat.ceil (Real.exp ((27 / 10) / δ)) - 1)) ≤ n)
    (hA : agreementThreshold δ n k ≤ n)
    (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    let A := agreementThreshold δ n k
    let d := Nat.ceil (Real.exp ((27 / 10) / δ))
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * harmonicNumber (d - 1))
    let ν := 2 * m - 1
    Nonempty (Certificate.{u, u} F A k ν d (12 * ν - 1) centers f g) ∧
      0 < n ∧ 0 < ν ∧ ν < n ∧ d < n ∧ k ≤ n ∧ k ≤ A ∧
      (k : ℝ) + δ * n ≤ A ∧
      ∀ r i, r < i → i < n → (i.choose r : F) ≠ 0 := by
  dsimp only
  obtain ⟨hn, _hm, hν, _hνm, hνn, hdK, hkK, hKn, hkA, hgap⟩ :=
    prescribed_geometric_parameters δ n k hδ hδ' hk hblock hA
  exact ⟨exists_prescribed_symbolic_weightedSupport_certificate δ n k centers f g
      hδ hδ' hk hblock hA,
    hn, hν, hνn, hdK.trans_le hKn, hkK.trans hKn, hkA, hgap,
    binomial_pivots_of_characteristic hchar⟩

/-- The characteristic contract at cap `n` supplies every binomial pivot after any field
embedding. This is stronger than restricting the order to a prescribed stage bound. -/
theorem prescribed_correlated_extension_pivots {F E : Type*} [Field F] [Field E]
    (iota : F →+* E) (n : ℕ) (hchar : ringChar F = 0 ∨ n ≤ ringChar F) :
    ∀ r i, r < i → i < n → (i.choose r : E) ≠ 0 := by
  intro r
  exact map_binomial_pivots iota n (binomial_pivots_of_characteristic hchar r)

end ReedSolomon
