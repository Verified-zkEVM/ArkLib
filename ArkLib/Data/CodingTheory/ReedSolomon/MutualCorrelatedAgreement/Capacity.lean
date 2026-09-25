/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity.MathematicalUniformRate
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.UniformLineMca

/-!
# Mutual correlated agreement up to capacity

For every positive gap `δ`, Reed–Solomon codes have exact mutual correlated agreement at agreement
`k + δ n`, with a block-length threshold `N ≥ 4`, a derivative order `d` and a constant `C` that
depend only on `δ`: not on the field, the rate, the evaluation points or the received words. The
exceptional set is chosen before the challenge and the candidate polynomial. Outside it, every
candidate is the corresponding combination of low-degree constituent polynomials, and its whole
agreement set is their common agreement set.

* **Lines:** at most `C n^(d+1)` exceptional challenges for `f + z g`, over any field of
  characteristic zero or larger than `k - 1`.
* **Affine families:** exceptional density at most `C n^(d+1) / (|F| - 1)` for
  `a + ∑ j, t j • u j` over a finite field, independently of the number of directions. The line
  and affine-space MCA errors at radius `1 - k / n - δ` are at most `C n^(d+1) / |F|` and
  `C n^(d+1) / (|F| - 1)`.
* **Power batching:** at most `ℓ C n^(d+1)` exceptional challenges for
  `w₀ + z w₁ + ⋯ + z^ℓ w_ℓ`. The characteristic is zero or larger than `max (k - 1) ν`, where
  `ν` depends only on `δ`, not on `ℓ`; constant messages need no characteristic assumption.

Affine families use independent parameters and power batching uses the powers of one parameter.
An affine exceptional set can contain a whole power curve, so the power-batching theorem is a
separate result.

For lines, gaps below `6/25` use the mathematical uniform rate-partition construction with
`d = ⌈exp (3/(2δ))⌉₊` and the constant `max C(δ) (343/3)`; gaps from `6/25` on use the uniform
first-order certificate, with `d = 1` and `C = 1325775`. Power batching uses the rate-partition
construction at the gap `min δ (1/8)`.

## Main definitions

* `ReedSolomon.HasCapacityLineAgreement`, `ReedSolomon.HasCapacityAffineAgreement`,
  `ReedSolomon.HasCapacityPowerBatchingAgreement`: exact mutual correlated agreement at a gap,
  with a length threshold and an exceptional-set bound.
* `ReedSolomon.capacityLineLength`, `ReedSolomon.capacityLineDerivativeOrder`,
  `ReedSolomon.capacityLineConstant`: the gap-only parameters for lines and affine families.
* `ReedSolomon.capacityPowerGap`, `ReedSolomon.capacityPowerLength`,
  `ReedSolomon.capacityPowerDerivativeOrder`, `ReedSolomon.capacityPowerJetBound`,
  `ReedSolomon.capacityPowerConstant`: the gap-only parameters for power batching.

## Main statements

* `ReedSolomon.capacity_lineAgreement`, `ReedSolomon.exists_capacity_lineAgreement`: line
  agreement up to capacity.
* `ReedSolomon.HasCapacityLineAgreement.affineAgreement`,
  `ReedSolomon.exists_capacity_affineAgreement`: line agreement gives affine-family agreement with
  the same parameters.
* `ReedSolomon.HasCapacityLineAgreement.mcaError_le`, `ReedSolomon.exists_capacity_mcaError`: line
  agreement bounds the line and affine-space MCA errors.
* `ReedSolomon.capacity_powerBatchingAgreement`,
  `ReedSolomon.exists_capacity_powerBatchingAgreement`: power-batching agreement up to capacity.

## References

* [DKTZ26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial CoreDefinitions HiddenDerivative.RatePartition

universe u

/-! ## Gap-only parameters for lines and affine families -/

/-- The derivative order `d(δ)` for lines: `⌈exp (3/(2δ))⌉₊` below `6/25` and `1` from `6/25` on.
The exceptional-set bound is `C(δ) n^(d(δ)+1)`. -/
def capacityLineDerivativeOrder (δ : ℝ) : ℕ :=
  if δ < 6 / 25 then uniformDerivativeOrder δ else 1

/-- The block-length threshold `N(δ)` for lines: the mathematical uniform capacity length (at least
four) below `6/25`, and `4` from `6/25` on. -/
def capacityLineLength (δ : ℝ) : ℕ :=
  if δ < 6 / 25 then max 4 (uniformMathematicalCapacityLength δ) else 4

/-- The constant `C(δ)` for lines: `mathematicalUniformLineAgreementConstant δ` below `6/25`, and
the first-order constant `1325775` from `6/25` on. -/
def capacityLineConstant (δ : ℝ) : ℝ :=
  if δ < 6 / 25 then mathematicalUniformLineAgreementConstant δ else 1325775

/-- The line length threshold is at least four. -/
theorem four_le_capacityLineLength (δ : ℝ) : 4 ≤ capacityLineLength δ := by
  unfold capacityLineLength
  split_ifs
  · exact le_max_left _ _
  · exact le_rfl

/-- The line constant is at least one. -/
theorem one_le_capacityLineConstant (δ : ℝ) : 1 ≤ capacityLineConstant δ := by
  unfold capacityLineConstant mathematicalUniformLineAgreementConstant
  split_ifs
  · exact (by norm_num : (1 : ℝ) ≤ 343 / 3).trans (le_max_right _ _)
  · norm_num

/-! ## Lines -/

/-- **Exact line agreement at a gap.** For every block length `n ≥ N`, dimension `0 < k ≤ n`,
integer threshold `A ≥ k + δ n`, field `F` of characteristic zero or larger than `k - 1`, and
distinct evaluation points `domain`, every received line `f + z g` has one set of at most `E n`
exceptional challenges. Outside it, every polynomial `P` of degree below `k` with at least `A`
agreements is `P₀ + C z * P₁` for polynomials of degree below `k`, and the agreement set of `P` is
the common agreement set of `P₀` with `f` and `P₁` with `g` (`LineExactAgreementBound`). The field
may be infinite. -/
def HasCapacityLineAgreement (δ : ℝ) (N : ℕ) (E : ℕ → ℝ) : Prop :=
  ∀ n k A : ℕ, N ≤ n → 0 < k → k ≤ n → (k : ℝ) + δ * n ≤ A →
    ∀ (F : Type u) [Field F] [DecidableEq F], (ringChar F = 0 ∨ k - 1 < ringChar F) →
      ∀ domain : Fin n ↪ F, LineExactAgreementBound domain k A (E n)

/-- **Line agreement up to capacity.** At every positive gap `δ`, exact line agreement holds from
length `capacityLineLength δ` on with at most
`capacityLineConstant δ * n ^ (capacityLineDerivativeOrder δ + 1)` exceptional challenges
[DKTZ26, “Mutual correlated agreement up to capacity”]. -/
theorem capacity_lineAgreement {δ : ℝ} (hδ : 0 < δ) :
    HasCapacityLineAgreement δ (capacityLineLength δ)
      (fun n ↦ capacityLineConstant δ * (n : ℝ) ^ (capacityLineDerivativeOrder δ + 1)) := by
  intro n k A hn hk _hkn hgap F _ decF hchar domain
  have hbound : 0 ≤ capacityLineConstant δ * (n : ℝ) ^ (capacityLineDerivativeOrder δ + 1) :=
    mul_nonneg (zero_le_one.trans (one_le_capacityLineConstant δ)) (by positivity)
  by_cases hAn : A ≤ n
  swap
  · refine fun f g ↦ ⟨∅, by simpa using hbound, fun z _ P _ hA ↦ absurd (hA.trans ?_) hAn⟩
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  apply lineExactAgreementBound_of_exactCorrelatedPair
  intro f g
  by_cases hsmall : δ < 6 / 25
  · have hnMath : uniformMathematicalCapacityLength δ ≤ n := by
      simp only [capacityLineLength, hsmall, ↓reduceIte] at hn
      exact (le_max_right _ _).trans hn
    have hdec : (fun a b : F ↦ Classical.propDecidable (a = b)) = decF := Subsingleton.elim _ _
    cases hdec
    simpa only [capacityLineConstant, capacityLineDerivativeOrder, hsmall, ↓reduceIte] using
      exists_mathematicalUniformRatePartition_line_exactCorrelatedPair hδ hsmall hnMath hk hgap
        hAn domain f g hchar
  · have hgapFirstOrder : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A := by
      have := mul_le_mul_of_nonneg_right (le_of_not_gt hsmall) (Nat.cast_nonneg (α := ℝ) n)
      linarith
    have hnTwo : 2 ≤ n := by have := (four_le_capacityLineLength δ).trans hn; omega
    simpa only [capacityLineConstant, capacityLineDerivativeOrder, hsmall, ↓reduceIte] using
      exists_uniformFirstOrder_lineMca n k A domain f g hnTwo hk hAn hgapFirstOrder hchar

/-- **Line agreement up to capacity, with gap-only constants.** For every `δ > 0` there are
`N ≥ 4`, `d` and `C > 0`, chosen before the code, the field and the received line, such that
exact line agreement holds from length `N` on with at most `C n^(d+1)` exceptional challenges
[DKTZ26, “Mutual correlated agreement up to capacity”]. -/
theorem exists_capacity_lineAgreement {δ : ℝ} (hδ : 0 < δ) :
    ∃ N d : ℕ, ∃ C : ℝ, 4 ≤ N ∧ 0 < C ∧
      HasCapacityLineAgreement δ N (fun n ↦ C * (n : ℝ) ^ (d + 1)) :=
  ⟨capacityLineLength δ, capacityLineDerivativeOrder δ, capacityLineConstant δ,
    four_le_capacityLineLength δ, zero_lt_one.trans_le (one_le_capacityLineConstant δ),
    capacity_lineAgreement hδ⟩

/-! ## Affine families -/

/-- **Exact affine-family agreement at a gap.** For every block length `n ≥ N`, dimension
`0 < k ≤ n`, finite field `F` of characteristic zero or larger than `k - 1`, distinct evaluation
points `domain`, number `s` of directions, offset `a` and directions `u`, one set of parameters
`t : Fin s → F` of size at most `E n * |F|^s / (|F| - 1)` is exceptional: its density is at most
`E n / (|F| - 1)`, independently of `s`. Outside it, every polynomial `P` of degree below `k` with
at least `k + δ n` agreements with `a + ∑ j, t j • u j` is `P₀ + ∑ j, t j • P₁ j` for polynomials of
degree below `k`, and `P` agrees with the received word exactly where `P₀` agrees with `a` and
every `P₁ j` agrees with `u j`. -/
def HasCapacityAffineAgreement (δ : ℝ) (N : ℕ) (E : ℕ → ℝ) : Prop :=
  ∀ n k : ℕ, N ≤ n → 0 < k → k ≤ n →
    ∀ (F : Type) [Field F] [Fintype F] [DecidableEq F], (ringChar F = 0 ∨ k - 1 < ringChar F) →
      ∀ (domain : Fin n ↪ F) (s : ℕ) (a : Fin n → F) (u : Fin s → Fin n → F),
        ∃ exceptional : Finset (Fin s → F),
          (exceptional.card : ℝ) ≤ E n * (Fintype.card F : ℝ) ^ s / ((Fintype.card F : ℝ) - 1) ∧
          ∀ t ∉ exceptional, ∀ P : F[X], P.degree < k →
            (k : ℝ) + δ * n ≤
              ((Finset.univ.filter fun i ↦ P.eval (domain i) = a i + ∑ j, t j * u j i).card : ℝ) →
            ∃ (P₀ : F[X]) (P₁ : Fin s → F[X]),
              P₀.degree < k ∧ (∀ j, (P₁ j).degree < k) ∧ P = P₀ + ∑ j, t j • P₁ j ∧
              ∀ i, (P.eval (domain i) = a i + ∑ j, t j * u j i ↔
                P₀.eval (domain i) = a i ∧ ∀ j, (P₁ j).eval (domain i) = u j i)

/-- At radius `1 - k / n - δ`, the agreement threshold `n (1 - radius)` is `k + δ n`. -/
private theorem card_mul_one_sub_capacityRadius {δ : ℝ} {n k : ℕ} (hn : 0 < n) :
    (Fintype.card (Fin n) : ℝ) * (1 - (1 - k / n - δ)) = k + δ * n := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Fintype.card_fin]
  field_simp
  ring

/-- **Affine-family agreement from line agreement.** Exact line agreement at a nonnegative gap
gives exact affine-family agreement with the same length threshold and exceptional-set bound
[DKTZ26, “Mutual agreement for affine families”]. -/
theorem HasCapacityLineAgreement.affineAgreement {δ : ℝ} {N : ℕ} {E : ℕ → ℝ}
    (h : HasCapacityLineAgreement.{0} δ N E) (hδ : 0 ≤ δ) : HasCapacityAffineAgreement δ N E := by
  intro n k hn hk hkn F _ _ _ hchar domain s a u
  have hthreshold := card_mul_one_sub_capacityRadius (δ := δ) (k := k) (hk.trans_le hkn)
  have hline := h n k ⌈(k : ℝ) + δ * n⌉₊ hn hk hkn (Nat.le_ceil _) F hchar domain
  obtain ⟨exceptional, hcard, hgood⟩ := exists_affine_exceptionalSet_full_agreement_of_exactLine
    domain _ hline _ (by rw [hthreshold]) (by rw [hthreshold]; nlinarith) (Fin.cons a u)
  refine ⟨exceptional, hcard, fun t ht P hP hA ↦ ?_⟩
  obtain ⟨P₀, hdegree, heq, hsets⟩ := hgood t ht P hP (by
    rw [hthreshold]
    simpa [AffineSpaceGenerator, Fin.sum_univ_succ] using hA)
  refine ⟨P₀ 0, fun j ↦ P₀ j.succ, hdegree 0, fun j ↦ hdegree j.succ, ?_, fun i ↦ ?_⟩
  · simpa [AffineSpaceGenerator, Fin.sum_univ_succ] using heq
  · simpa [AffineSpaceGenerator, Fin.sum_univ_succ, Fin.forall_fin_succ] using hsets i

/-- **Affine-family agreement up to capacity, with gap-only constants.** For every `δ > 0` there
are `N ≥ 4`, `d` and `C > 0` such that exact affine-family agreement holds from length `N` on with
exceptional density at most `C n^(d+1) / (|F| - 1)` in every number of directions
[DKTZ26, “Mutual agreement for affine families”]. -/
theorem exists_capacity_affineAgreement {δ : ℝ} (hδ : 0 < δ) :
    ∃ N d : ℕ, ∃ C : ℝ, 4 ≤ N ∧ 0 < C ∧
      HasCapacityAffineAgreement δ N (fun n ↦ C * (n : ℝ) ^ (d + 1)) :=
  ⟨capacityLineLength δ, capacityLineDerivativeOrder δ, capacityLineConstant δ,
    four_le_capacityLineLength δ, zero_lt_one.trans_le (one_le_capacityLineConstant δ),
    (capacity_lineAgreement hδ).affineAgreement hδ.le⟩

/-- **MCA errors from line agreement.** Under exact line agreement at a gap `δ`, for every
Reed–Solomon code of block length `n ≥ N` and dimension `0 < k ≤ n` over a finite field of
characteristic zero or larger than `k - 1`, the MCA error at radius `1 - k / n - δ` is at most
`E n / |F|` for the affine-line generator and at most `E n / (|F| - 1)` for the affine-space
generator of every dimension. -/
theorem HasCapacityLineAgreement.mcaError_le {δ : ℝ} {N : ℕ} {E : ℕ → ℝ}
    (h : HasCapacityLineAgreement.{0} δ N E) {n k : ℕ} (hn : N ≤ n) (hk : 0 < k) (hkn : k ≤ n)
    {F : Type} [Field F] [Fintype F] [SampleableType F]
    (hchar : ringChar F = 0 ∨ k - 1 < ringChar F) (domain : Fin n ↪ F) :
    mcaError (AffineLineGenerator F) (code domain k) (1 - k / n - δ) ≤
        ENNReal.ofReal (E n / Fintype.card F) ∧
      ∀ s : ℕ, mcaError (AffineSpaceGenerator F s) (code domain k) (1 - k / n - δ) ≤
        ENNReal.ofReal (E n / ((Fintype.card F : ℝ) - 1)) := by
  classical
  have hthreshold := card_mul_one_sub_capacityRadius (δ := δ) (k := k) (hk.trans_le hkn)
  have hline := h n k ⌈(k : ℝ) + δ * n⌉₊ hn hk hkn (Nat.le_ceil _) F hchar domain
  exact ⟨mcaError_affineLine_le_of_exactAgreement domain _ hline _ (by rw [hthreshold]),
    fun _ ↦ mcaError_affineSpace_le_of_exactAgreement domain _ hline _ (by rw [hthreshold])⟩

/-- **MCA errors up to capacity, with gap-only constants.** For every `δ > 0` there are `N ≥ 4`,
`d` and `C > 0` such that every Reed–Solomon code of length `n ≥ N` over a finite field of
characteristic zero or larger than `k - 1` has MCA error at radius `1 - k / n - δ` at most
`C n^(d+1) / |F|` for lines and at most `C n^(d+1) / (|F| - 1)` for affine spaces of every
dimension [DKTZ26, “Uniform finite choices up to capacity”]. -/
theorem exists_capacity_mcaError {δ : ℝ} (hδ : 0 < δ) :
    ∃ N d : ℕ, ∃ C : ℝ, 4 ≤ N ∧ 0 < C ∧
      ∀ n k : ℕ, N ≤ n → 0 < k → k ≤ n →
      ∀ (F : Type) [Field F] [Fintype F] [SampleableType F],
        (ringChar F = 0 ∨ k - 1 < ringChar F) → ∀ domain : Fin n ↪ F,
          mcaError (AffineLineGenerator F) (code domain k) (1 - k / n - δ) ≤
              ENNReal.ofReal (C * (n : ℝ) ^ (d + 1) / Fintype.card F) ∧
            ∀ s : ℕ, mcaError (AffineSpaceGenerator F s) (code domain k) (1 - k / n - δ) ≤
              ENNReal.ofReal (C * (n : ℝ) ^ (d + 1) / ((Fintype.card F : ℝ) - 1)) :=
  ⟨capacityLineLength δ, capacityLineDerivativeOrder δ, capacityLineConstant δ,
    four_le_capacityLineLength δ, zero_lt_one.trans_le (one_le_capacityLineConstant δ),
    fun _ _ hn hk hkn _ _ _ _ hchar domain ↦
      (capacity_lineAgreement hδ).mcaError_le hn hk hkn hchar domain⟩

/-! ## Power batching -/

/-- The auxiliary gap `min δ (1/8)` of the power-batching parameters. It is at most `δ` and below
`6/25`, and it is positive when `δ` is. -/
def capacityPowerGap (δ : ℝ) : ℝ := min δ (1 / 8)

/-- The power-batching derivative order: the uniform derivative order at `min δ (1/8)`. -/
def capacityPowerDerivativeOrder (δ : ℝ) : ℕ := uniformDerivativeOrder (capacityPowerGap δ)

/-- The power-batching jet bound `ν`: the mathematical uniform jet bound at `min δ (1/8)`. The
characteristic must be zero or larger than `max (k - 1) ν`, independently of the batching
degree. -/
def capacityPowerJetBound (δ : ℝ) : ℕ := uniformMathematicalJetBound (capacityPowerGap δ)

/-- The power-batching length threshold: the mathematical uniform length at `min δ (1/8)`, and at
least four. -/
def capacityPowerLength (δ : ℝ) : ℕ := max 4 (uniformMathematicalLength (capacityPowerGap δ))

/-- The power-batching constant: the maximum of one and the polynomial-curve agreement constant
at `min δ (1/8)`, with jet cap `capacityPowerJetBound δ`, height `150` times that cap and
derivative order `capacityPowerDerivativeOrder δ`. -/
def capacityPowerConstant (δ : ℝ) : ℝ :=
  max (polynomialCurveProductAgreementConstant (capacityPowerGap δ) (capacityPowerJetBound δ)
    (150 * capacityPowerJetBound δ) (capacityPowerDerivativeOrder δ)) 1

/-- The power-batching length threshold is at least four. -/
theorem four_le_capacityPowerLength (δ : ℝ) : 4 ≤ capacityPowerLength δ :=
  le_max_left _ _

/-- The power-batching constant is at least one. -/
theorem one_le_capacityPowerConstant (δ : ℝ) : 1 ≤ capacityPowerConstant δ :=
  le_max_right _ _

/-- **Exact power-batching agreement at a gap.** For every batching degree `0 < ℓ`, block length
`n ≥ N`, dimension `0 < k ≤ n`, integer threshold `A ≥ k + δ n`, field `F` with `k = 1`, or of
characteristic zero or larger than `max (k - 1) ν`, distinct evaluation points `domain`, and rows
`w : Fin (ℓ + 1) → Fin n → F`, one set of at most `E ℓ n` challenges is exceptional. Outside it,
every polynomial `Q` of degree below `k` with at least `A` agreements with
`powerBatchedWord w z = ∑ t, z ^ t • w t` has exact power agreement: `Q = ∑ t, z ^ t • P t` for
polynomials `P t` of degree below `k`, and the agreement set of `Q` is the common agreement set of
the `P t` with the rows. The field may be infinite. -/
def HasCapacityPowerBatchingAgreement (δ : ℝ) (N ν : ℕ) (E : ℕ → ℕ → ℝ) : Prop :=
  ∀ ℓ n k A : ℕ, 0 < ℓ → N ≤ n → 0 < k → k ≤ n → (k : ℝ) + δ * n ≤ A →
    ∀ (F : Type u) [Field F] [DecidableEq F],
      (k = 1 ∨ ringChar F = 0 ∨ max (k - 1) ν < ringChar F) →
      ∀ (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F),
        ∃ exceptional : Finset F, (exceptional.card : ℝ) ≤ E ℓ n ∧
          ∀ z ∉ exceptional, ∀ Q : F[X], Q.degree < k →
            A ≤ (polynomialAgreementSet domain (powerBatchedWord w z) Q).card →
            HasExactPowerAgreement domain w (RingHom.id F) k z Q

/-- **Power-batching agreement up to capacity.** At every positive gap `δ`, exact power-batching
agreement holds from length `capacityPowerLength δ` on, with characteristic bound
`capacityPowerJetBound δ` and at most
`ℓ * capacityPowerConstant δ * n ^ (capacityPowerDerivativeOrder δ + 1)` exceptional challenges
[DKTZ26, “Symbolic transfer for polynomial curves”]. -/
theorem capacity_powerBatchingAgreement {δ : ℝ} (hδ : 0 < δ) :
    HasCapacityPowerBatchingAgreement δ (capacityPowerLength δ) (capacityPowerJetBound δ)
      (fun ℓ n ↦ (ℓ : ℝ) * capacityPowerConstant δ *
        (n : ℝ) ^ (capacityPowerDerivativeOrder δ + 1)) := by
  have hε : 0 < capacityPowerGap δ := lt_min hδ (by norm_num)
  have hεsmall : capacityPowerGap δ < 6 / 25 := (min_le_right _ _).trans_lt (by norm_num)
  have hd : 519 ≤ capacityPowerDerivativeOrder δ := uniformDerivativeOrder_ge_519 hε hεsmall
  have hC := one_le_capacityPowerConstant δ
  intro ℓ n k A hℓ hn hk _hkn hgap F _ decF hchar domain w
  have hnFour : 4 ≤ n := (four_le_capacityPowerLength δ).trans hn
  have hbound : 0 ≤ (ℓ : ℝ) * capacityPowerConstant δ *
      (n : ℝ) ^ (capacityPowerDerivativeOrder δ + 1) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg ℓ) (zero_le_one.trans hC)) (by positivity)
  by_cases hAn : A ≤ n
  swap
  · refine ⟨∅, by simpa using hbound, fun z _ Q _ hA ↦ absurd (hA.trans ?_) hAn⟩
    exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin n)
  by_cases hkOne : k = 1
  · subst k
    obtain ⟨exceptional, hcard, hgood⟩ := uniformExactPowerAgreement_constantCode domain w A
    refine ⟨exceptional, ?_, hgood⟩
    have hchoose : ℓ * (Fintype.card (Fin n)).choose 2 / max (A - 1) 1 ≤ ℓ * n ^ 2 := by
      rw [Fintype.card_fin]
      exact (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left ℓ (Nat.choose_le_pow n 2))
    have hcardR : (exceptional.card : ℝ) ≤ (ℓ : ℝ) * (n : ℝ) ^ 2 := by
      exact_mod_cast hcard.trans hchoose
    have hpow : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ (capacityPowerDerivativeOrder δ + 1) :=
      pow_le_pow_right₀ (by exact_mod_cast (by omega : 1 ≤ n)) (by omega)
    calc
      (exceptional.card : ℝ) ≤ (ℓ : ℝ) * 1 * (n : ℝ) ^ (capacityPowerDerivativeOrder δ + 1) := by
        rw [mul_one]
        exact hcardR.trans (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg ℓ))
      _ ≤ _ := by dsimp only; gcongr
  have hgapε : (k : ℝ) + capacityPowerGap δ * n ≤ A := by
    have := mul_le_mul_of_nonneg_right (min_le_left δ (1 / 8 : ℝ)) (Nat.cast_nonneg (α := ℝ) n)
    exact hgap.trans' (by simp only [capacityPowerGap]; linarith)
  have hdec : (fun a b : F ↦ Classical.propDecidable (a = b)) = decF := Subsingleton.elim _ _
  cases hdec
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_mathematicalUniformRatePartition_baseCurve_exactPowerAgreement hε hεsmall
      ((le_max_right _ _).trans hn) hk hgapε hAn hℓ domain w (hchar.resolve_left hkOne)
  refine ⟨exceptional, hcard.trans ?_, hgood⟩
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (le_max_left _ _) (Nat.cast_nonneg ℓ)) (by positivity)

/-- **Power-batching agreement up to capacity, with gap-only constants.** For every `δ > 0` there
are `N ≥ 4`, `d`, a characteristic bound `ν` and `C > 0`, chosen before the batching degree, the
code, the field and the rows, such that exact power-batching agreement holds from length `N` on
with at most `ℓ C n^(d+1)` exceptional challenges
[DKTZ26, “Symbolic transfer for polynomial curves”]. -/
theorem exists_capacity_powerBatchingAgreement {δ : ℝ} (hδ : 0 < δ) :
    ∃ N d ν : ℕ, ∃ C : ℝ, 4 ≤ N ∧ 0 < C ∧
      HasCapacityPowerBatchingAgreement δ N ν (fun ℓ n ↦ (ℓ : ℝ) * C * (n : ℝ) ^ (d + 1)) :=
  ⟨capacityPowerLength δ, capacityPowerDerivativeOrder δ, capacityPowerJetBound δ,
    capacityPowerConstant δ, four_le_capacityPowerLength δ,
    zero_lt_one.trans_le (one_le_capacityPowerConstant δ), capacity_powerBatchingAgreement hδ⟩

end ReedSolomon
