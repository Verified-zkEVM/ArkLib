/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLibExamples.ReedSolomon.Fields
import ArkLibExamples.ReedSolomon.ProveKitInterpolation
import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.FirstOrder.SharpListBound

/-!
# Sharp scalar list bounds for the two ProveKit profiles

The interpolation module constructs a nonzero first-order differential equation for every
received word. The cap-sensitive root theorem counts its close polynomial solutions while
retaining the separate cap on the first derivative variable. At the two ProveKit parameter rows,
this gives exactly the list sizes supplied by the paper calculation: `147000408479737` for BN254
and `8279136487` for cubic Goldilocks.

## Reading the statements

Both rows use block length `n = 2^20`, candidate degree strictly below `k = 2^18`, and Taylor
cutoff `K = k`. The BN254 row requires `A = 492831` agreements and uses total/first-jet caps
`(μ, M) = (688, 168)`. The cubic row requires `A = 508263` and uses `(μ, M) = (30, 7)`.
The BN254 envelope evaluates the legacy cap-sensitive expression. The revised cubic row evaluates
the dimension-sensitive charge directly:

```text
firstOrderTightListWeight n A k (2 K - 3) μ M.
```

The scalar theorems bound these expressions by the recorded `Profile.listSize`.

Each field-uniform theorem quantifies over an arbitrary domain embedding, received word, and
finite set `S`. Its sole assumption on `S` is that every member has degree below `k` and at least
`A` agreements, through `IsAgreementSolution`. The list cap occurs only in the conclusion. The
concrete corollaries discharge the characteristic and cardinality facts using `Fields`.

## Mathematical scope

These are scalar finite-family bounds. The width-preserving rational-function argument needed for
an interleaved `Code.Lambda` statement is separate, as are polynomial-curve exceptional counts
and the composition of protocol error terms. The theorem does not assume that a decoder returns
the complete list.
-/

open PolynomialDifferential Polynomial
open ReedSolomon.HiddenDerivative

namespace ArkLibExamples.ReedSolomon.ProveKit

open ConcreteFields

set_option maxRecDepth 4096

/-- The cap-sensitive rational expression rounds up to the BN254 row's supplied list size. -/
theorem bn254_sharp_list_envelope :
    (((bn254.n * firstOrderListWeight bn254.k bn254.totalJetDegreeCap
      bn254.firstJetCap : ℕ) : ℚ) /
        (((bn254.agreementNumerator - bn254.k + 1 : ℕ) : ℚ))) ≤ bn254.listSize := by
  norm_num [bn254, firstOrderListWeight]

/-- The cap-sensitive rational expression rounds up to the cubic Goldilocks supplied list size. -/
theorem goldilocksCubic113_sharp_list_envelope :
    firstOrderTightListWeight goldilocksCubic113.n goldilocksCubic113.agreementNumerator
      goldilocksCubic113.k (2 * goldilocksCubic113.k - 3)
        goldilocksCubic113.totalJetDegreeCap goldilocksCubic113.firstJetCap ≤
          goldilocksCubic113.listSize := by
  norm_num [goldilocksCubic113, firstOrderTightListWeight]

/-- Every finite scalar BN254-profile agreement list obeys the supplied sharp list cap. -/
theorem bn254_finite_list_bound_sharp {F : Type*} [Field F]
    (domain : Fin bn254.n ↪ F) (received : Fin bn254.n → F)
    (hchar : ringChar F = 0 ∨
      max bn254.n bn254.totalJetDegreeCap < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S,
      IsAgreementSolution domain received bn254.k bn254.agreementNumerator P) :
    (S.card : ℚ) ≤ bn254.listSize := by
  have hb := finite_firstOrder_list_bound_of_heightSlotCount_sharp
    (F := F) (D := 262143) (A := 492831) (m := 384) (M := 168) (μ := 688)
      (k := 262144) (h := 867623) (K := 262144)
      (by norm_num) (by norm_num) (by norm_num)
      (by simpa only [bn254] using domain) (by simpa only [bn254] using received)
      bn254_interpolation_height
      (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simpa only [bn254] using hchar) S (by simpa only [bn254] using hS)
  exact hb.trans (by simpa only [bn254] using bn254_sharp_list_envelope)

/-- Every finite scalar cubic-Goldilocks-profile agreement list obeys its supplied sharp cap. -/
theorem goldilocksCubic113_finite_list_bound_sharp {F : Type*} [Field F]
    (domain : Fin goldilocksCubic113.n ↪ F) (received : Fin goldilocksCubic113.n → F)
    (hchar : ringChar F = 0 ∨
      max goldilocksCubic113.n goldilocksCubic113.totalJetDegreeCap < ringChar F)
    (S : Finset F[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received goldilocksCubic113.k
      goldilocksCubic113.agreementNumerator P) :
    (S.card : ℚ) ≤ goldilocksCubic113.listSize := by
  have hb := finite_firstOrder_list_bound_of_shiftedHeightSlotCount_tight
    (F := F) (D := 262143) (A := 508263) (m := 16) (M := 7) (μ := 30)
      (k := 262144) (h := 339) (K := 262144)
      (by norm_num) (by norm_num) (by norm_num)
      (by simpa only [goldilocksCubic113] using domain)
      (by simpa only [goldilocksCubic113] using received)
      goldilocksCubic113_interpolation_height
      (by norm_num) le_rfl (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by simpa only [goldilocksCubic113] using hchar) S
      (by simpa only [goldilocksCubic113] using hS)
  exact hb.trans (by simpa only [goldilocksCubic113] using
    goldilocksCubic113_sharp_list_envelope)

/-- The canonical BN254 scalar field has the cardinality recorded in the ProveKit row. -/
theorem bn254_concrete_field_card : Fintype.card BN254Scalar = bn254.fieldSize := by
  rw [bn254Scalar_card]
  norm_num [BN254.scalarFieldSize, bn254]

/-- The canonical cubic Goldilocks field has the cardinality recorded in the ProveKit row. -/
theorem goldilocksCubic113_concrete_field_card :
    Fintype.card ConcreteFields.GoldilocksCubic = goldilocksCubic113.fieldSize := by
  rw [ConcreteFields.goldilocksCubic_card]
  norm_num [Goldilocks.fieldSize, goldilocksCubic113]

/-- The sharp list theorem specialized to the actual BN254 scalar-field model. -/
theorem bn254_concrete_finite_list_bound_sharp
    (domain : Fin bn254.n ↪ BN254Scalar) (received : Fin bn254.n → BN254Scalar)
    (S : Finset BN254Scalar[X])
    (hS : ∀ P ∈ S,
      IsAgreementSolution domain received bn254.k bn254.agreementNumerator P) :
    (S.card : ℚ) ≤ bn254.listSize ∧
      (S.card : ℚ) / Fintype.card BN254Scalar ≤ (1 : ℚ) / 2 ^ 128 := by
  have hlist := bn254_finite_list_bound_sharp domain received (by
    right
    rw [bn254Scalar_ringChar]
    norm_num [BN254.scalarFieldSize, bn254]) S hS
  refine ⟨hlist, ?_⟩
  rw [bn254_concrete_field_card]
  calc
    (S.card : ℚ) / bn254.fieldSize ≤ (bn254.listSize : ℚ) / bn254.fieldSize := by
      exact div_le_div_of_nonneg_right hlist (by positivity)
    _ ≤ (1 : ℚ) / 2 ^ 128 := by norm_num [bn254]

/-- The sharp list theorem specialized to the actual degree-three Goldilocks field model. -/
theorem goldilocksCubic113_concrete_finite_list_bound_sharp
    (domain : Fin goldilocksCubic113.n ↪ ConcreteFields.GoldilocksCubic)
    (received : Fin goldilocksCubic113.n → ConcreteFields.GoldilocksCubic)
    (S : Finset ConcreteFields.GoldilocksCubic[X])
    (hS : ∀ P ∈ S, IsAgreementSolution domain received goldilocksCubic113.k
      goldilocksCubic113.agreementNumerator P) :
    (S.card : ℚ) ≤ goldilocksCubic113.listSize ∧
      (S.card : ℚ) / Fintype.card ConcreteFields.GoldilocksCubic ≤
        (1 : ℚ) / 2 ^ 128 := by
  have hlist := goldilocksCubic113_finite_list_bound_sharp domain received (by
    right
    rw [ConcreteFields.goldilocksCubic_ringChar]
    norm_num [Goldilocks.fieldSize, goldilocksCubic113]) S hS
  refine ⟨hlist, ?_⟩
  rw [goldilocksCubic113_concrete_field_card]
  calc
    (S.card : ℚ) / goldilocksCubic113.fieldSize ≤
        (goldilocksCubic113.listSize : ℚ) / goldilocksCubic113.fieldSize := by
      exact div_le_div_of_nonneg_right hlist (by positivity)
    _ ≤ (1 : ℚ) / 2 ^ 128 := by norm_num [goldilocksCubic113]

end ArkLibExamples.ReedSolomon.ProveKit
