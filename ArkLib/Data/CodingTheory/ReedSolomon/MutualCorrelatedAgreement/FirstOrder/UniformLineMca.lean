/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.AutomaticHybrid
public import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.FirstOrder.UniformMca
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.FirstOrder.CurveCertificate

/-!
# Uniform first-order line agreement

For dimension `k ≥ 2` and agreement `A ≥ k + 6 n / 25`, the first-order certificate with
multiplicity `12`, derivative cap `4`, jet degree `23` and challenge height `276` exists for every
received line over an arbitrary field. Its hybrid transfer gives one exceptional set of at most
`1325775 n²` challenges, chosen before the challenge and the candidate polynomial. Outside it,
every polynomial of degree below `k` agreeing with the line in at least `A` places has an exact
correlated pair, with equality of the complete agreement set.

## Main statements

* `ReedSolomon.exists_uniformFirstOrder_lineMca_of_two_le`: the uniform exceptional-set
  bound for exact correlated agreement along a received line.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial

namespace ReedSolomon

open HiddenDerivative

/-- For `2 ≤ k`, `2 ≤ n` and `k + 6 n / 25 ≤ A ≤ n`, every received line over a field of
characteristic zero or larger than `max (k - 1) 4` has one set of at most `1325775 n²` exceptional
challenges. Outside it, every polynomial of degree below `k` agreeing with the line in at least
`A` places has an exact correlated pair. -/
theorem exists_uniformFirstOrder_lineMca_of_two_le
    {F : Type*} [Field F] [DecidableEq F]
    (n k A : ℕ) (domain : Fin n ↪ F) (f g : Fin n → F)
    (hn : 2 ≤ n) (hk : 2 ≤ k) (hAn : A ≤ n)
    (hgap : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A)
    (hchar : ringChar F = 0 ∨ max (k - 1) 4 < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ 1325775 * (n : ℝ) ^ 2 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  have hgapNat : 25 * k + 6 * n ≤ 25 * A := by
    have hgapReal : (25 : ℝ) * k + 6 * n ≤ 25 * A := by linarith
    exact_mod_cast hgapReal
  obtain ⟨hDpos, hbudget, hkD, hheight⟩ := uniformFirstOrderMca_parameters n k A hk hgapNat
  obtain ⟨cert⟩ := exists_finite_firstOrder_symbolic_certificate_of_heightSlotCount (F := F)
    (k := k) hDpos hbudget hkD domain f g hheight
  obtain ⟨exceptional, hraw, -, -, hgood⟩ := cert.exists_exceptional_hybrid (D := k - 1)
    (by omega) (by omega) (by omega) hAn (by norm_num) hchar
  exact ⟨exceptional, hraw.trans (uniformFirstOrderMca_optimizedExceptionCharge_le_ceiling
    hn (by omega) (by omega) hAn (by omega)), hgood⟩

end ReedSolomon
