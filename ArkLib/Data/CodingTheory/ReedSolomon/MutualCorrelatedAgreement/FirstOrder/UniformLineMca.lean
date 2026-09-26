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
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Agreement
public import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement.ConstantCode

/-!
# Uniform first-order line agreement

For dimension `k ≥ 2` and agreement `A ≥ k + 6 n / 25`, the first-order certificate with
multiplicity `12`, derivative cap `4`, jet degree `23` and challenge height `276` exists for every
received line over an arbitrary field. Its hybrid transfer gives one exceptional set of at most
`1325775 n²` challenges, chosen before the challenge and the candidate polynomial. Outside it,
every polynomial of degree below `k` agreeing with the line in at least `A` places has an exact
correlated pair, with equality of the complete agreement set.

The same bound holds for every `k ≥ 1` when the characteristic is only assumed to be zero or
larger than `k - 1`. Constant messages need no characteristic assumption. If the characteristic is
two or three, then `k ≤ 3`: the Johnson bound covers `n ≥ 139`, and retaining every
common-sample interpolant covers shorter lengths.

## Main statements

* `ReedSolomon.exists_uniformFirstOrder_lineMca_of_two_le`: the uniform exceptional-set
  bound for exact correlated agreement along a received line.
* `ReedSolomon.exists_uniformFirstOrder_lineMca`: the same bound for every `k ≥ 1`, assuming only
  characteristic zero or `k - 1 < char F`.

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

/-- If `k - 1 < char F ≤ 4`, then the characteristic is two or three, so `k ≤ 3`. -/
private theorem le_three_of_ringChar_le_four {F : Type*} [Field F] {k : ℕ}
    (hdegreeChar : k - 1 < ringChar F) (hsupportChar : ringChar F ≤ 4) : k ≤ 3 := by
  have hpPos : 0 < ringChar F := by omega
  have : NeZero (ringChar F) := ⟨hpPos.ne'⟩
  have hpPrime : (ringChar F).Prime := (CharP.char_is_prime_of_pos F (ringChar F)).out
  have hpNeFour : ringChar F ≠ 4 := by
    intro hp
    rw [hp] at hpPrime
    exact absurd hpPrime (by decide)
  omega

/-- For `0 < k`, `2 ≤ n` and `k + 6 n / 25 ≤ A ≤ n`, every received line over a field of
characteristic zero or larger than `k - 1` has one set of at most `1325775 n²` exceptional
challenges. Outside it, every polynomial of degree below `k` agreeing with the line in at least
`A` places has an exact correlated pair. -/
theorem exists_uniformFirstOrder_lineMca
    {F : Type*} [Field F] [decF : DecidableEq F]
    (n k A : ℕ) (domain : Fin n ↪ F) (f g : Fin n → F)
    (hn : 2 ≤ n) (hk : 0 < k) (hAn : A ≤ n)
    (hgap : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A)
    (hchar : ringChar F = 0 ∨ k - 1 < ringChar F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ 1325775 * (n : ℝ) ^ 2 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < k →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) k z P := by
  have hnSq : (0 : ℝ) ≤ (n : ℝ) ^ 2 := sq_nonneg _
  have hkA : k ≤ A := by
    have h : (k : ℝ) ≤ A := hgap.trans' (le_add_of_nonneg_right (by positivity))
    exact_mod_cast h
  by_cases hkOne : k = 1
  · subst k
    apply exists_line_exactCorrelatedPair_of_powerAgreement
    obtain ⟨exceptional, hcard, hgood⟩ := uniformExactPowerAgreement_constantCode domain ![f, g] A
    refine ⟨exceptional, ?_, hgood⟩
    have hchoose : 1 * (Fintype.card (Fin n)).choose 2 / max (A - 1) 1 ≤ n ^ 2 := by
      rw [Fintype.card_fin, one_mul]
      exact (Nat.div_le_self _ _).trans (Nat.choose_le_pow n 2)
    have hcardR : (exceptional.card : ℝ) ≤ (n : ℝ) ^ 2 := by exact_mod_cast hcard.trans hchoose
    linarith
  have hkTwo : 2 ≤ k := by omega
  by_cases hsupport : ringChar F = 0 ∨ max (k - 1) 4 < ringChar F
  · exact exists_uniformFirstOrder_lineMca_of_two_le n k A domain f g hn hkTwo hAn hgap hsupport
  have hdegreeChar := hchar.resolve_left fun hzero ↦ hsupport (Or.inl hzero)
  have hkThree : k ≤ 3 := le_three_of_ringChar_le_four hdegreeChar
    (not_lt.mp fun hfour ↦ hsupport (Or.inr (max_lt hdegreeChar hfour)))
  by_cases hnLarge : 139 ≤ n
  · have hscale : 4 * ((k : ℝ) - 1) ≤ (6 / 25 : ℝ) ^ 2 * n := by
      have hkR : (k : ℝ) ≤ 3 := by exact_mod_cast hkThree
      have hnR : (139 : ℝ) ≤ n := by exact_mod_cast hnLarge
      nlinarith
    have hdec : (fun a b : F ↦ Classical.propDecidable (a = b)) = decF := Subsingleton.elim _ _
    cases hdec
    obtain ⟨exceptional, hcard, hgood⟩ := exists_johnson_line_exactCorrelatedPair_of_gap
      domain f g (by norm_num) hkTwo hscale hgap hAn
    exact ⟨exceptional, hcard.le.trans (by linarith), hgood⟩
  · apply exists_line_exactCorrelatedPair_of_powerAgreement
    obtain ⟨exceptional, hcard, hgood⟩ :=
      uniformExactPowerAgreement_of_all_samples domain ![f, g] hkA
    refine ⟨exceptional, ?_, hgood⟩
    have hraw : (Fintype.card (Fin n)).choose k * (1 * (Fintype.card (Fin n) - k)) ≤ n ^ 4 := by
      rw [Fintype.card_fin, one_mul]
      calc
        n.choose k * (n - k) ≤ n ^ k * n := Nat.mul_le_mul (Nat.choose_le_pow n k) (Nat.sub_le n k)
        _ = n ^ (k + 1) := (pow_succ n k).symm
        _ ≤ n ^ 4 := pow_le_pow_right₀ (by omega) (by omega)
    have hcardR : (exceptional.card : ℝ) ≤ (n : ℝ) ^ 2 * (n : ℝ) ^ 2 := by
      rw [← pow_add]
      exact_mod_cast hcard.trans hraw
    have hnSmall : (n : ℝ) ^ 2 ≤ 139 ^ 2 := by
      have hnR : (n : ℝ) ≤ 139 := by exact_mod_cast (by omega : n ≤ 139)
      exact pow_le_pow_left₀ (Nat.cast_nonneg n) hnR 2
    nlinarith

end ReedSolomon
