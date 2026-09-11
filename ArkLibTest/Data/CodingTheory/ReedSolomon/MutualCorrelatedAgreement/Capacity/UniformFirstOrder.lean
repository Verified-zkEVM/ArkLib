/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Capacity
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.CapacityOutputBounds
import ArkLib.Data.CodingTheory.ReedSolomon.ListDecodability.FirstOrder.Uniform

/-!
# Checks for the uniform first-order certificate

These examples exercise the smallest admissible block-code parameters.  The first reaches the
shifted height-851 constructor at `k = 2`; the second checks that the public theorem also covers
the constant-message edge `k = 1` without exposing a numerical premise.
-/

namespace ReedSolomon

open Polynomial HiddenDerivative CoreDefinitions LinearCode

example :
    firstOrderCurveShiftedRowSlotBound (2 - 1) 3 12 4 22 3 1 851 <
      firstOrderCurveShiftedHeightSlotCount (2 - 1) 3 12 4 22 1 851 := by
  exact (uniformFirstOrder_parameters 3 2 3 (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).2.2.2

/-- The separate MCA support also works at the formerly widened `k = 2` endpoint. -/
example :
    firstOrderCurveShiftedRowSlotBound (2 - 1) 3 12 4 23 3 1 276 <
      firstOrderCurveShiftedHeightSlotCount (2 - 1) 3 12 4 23 1 276 := by
  exact (uniformFirstOrderMCA_parameters 3 2 3 (by norm_num) (by norm_num)
    (by norm_num)).2.2.2

example {F : Type*} [Field F] [DecidableEq F]
    (domain : Fin 2 ↪ F) (received : Fin 2 → F) :
    ∃ list : Finset F[X],
      (∀ P, P ∈ list ↔ P ∈ closePolynomialSet domain received 1 2) ∧
      list.card ≤ 307 * 2 := by
  exact exists_uniformFirstOrder_list 2 1 2 domain received
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by omega)

/-- The elementary `k = 1` branch retains one exceptional set and equality of the complete
agreement set, with the same public quadratic budget. -/
example {F : Type*} [Field F] [DecidableEq F]
    (domain : Fin 2 ↪ F) (f g : Fin 2 → F) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℝ) ≤ 1325775 * (2 : ℝ) ^ 2 ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < 1 →
        2 ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) 1 z P := by
  exact exists_uniformFirstOrder_lineMCA 2 1 2 domain f g
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by omega)

/-- The public affine-family corollary keeps the quadratic exceptional budget and incurs only the
dimension-independent `|F| - 1` denominator. -/
example {F : Type} [Field F] [Fintype F]
    (n k A s : ℕ) (domain : Fin n ↪ F)
    (hn : 2 ≤ n) (hk : 0 < k) (hAn : A ≤ n)
    (hgap : (k : ℝ) + (6 / 25 : ℝ) * n ≤ A)
    (hchar : 2 ≤ k → ringChar F = 0 ∨ max (k - 1) 4 < ringChar F)
    (hs : 1 ≤ s) (radius : ℝ) (hthreshold : A ≤ ⌈(n : ℝ) * (1 - radius)⌉₊) :
    mcaError (AffineSpaceGenerator F s) (code domain k) radius ≤
      ENNReal.ofReal
        (1325775 * (n : ℝ) ^ 2 / ((Fintype.card F : ℝ) - 1)) := by
  exact mcaError_affineSpace_uniformFirstOrder_le n k A s domain
    hn hk hAn hgap hchar hs radius hthreshold

/-- Gap monotonicity promotes the fixed `6/25` line theorem to the capacity interface with
block threshold `23`. -/
example : HasCapacityLineAgreement (6 / 25 : ℝ) 23
    (fun n ↦ 1325775 * (n : ℝ) ^ 2) := by
  exact uniformFirstOrder_capacity_lineAgreement (6 / 25) le_rfl

/-- The mathematical exact-list interface exposes the matching `307 n` bound. -/
example : HasCapacityLists (6 / 25 : ℝ) 23
    (fun n _k _q _A listSize ↦ listSize ≤ 307 * n) := by
  exact uniformFirstOrder_capacity_list (6 / 25) le_rfl

local instance primeTwentyThree : Fact (Nat.Prime 23) := ⟨by decide⟩

private def uniformCanaryDomain : Fin 23 ↪ ZMod 23 where
  toFun i := (i : ℕ)
  inj' i j hij := by
    apply Fin.ext
    have hval := congrArg ZMod.val hij
    simpa [ZMod.val_natCast_of_lt (by omega : (i : ℕ) < 23),
      ZMod.val_natCast_of_lt (by omega : (j : ℕ) < 23)] using hval

/-- The weakened positive-characteristic boundary is usable at `q = n = 23` and `k = 2`. -/
example (received : Fin 23 → ZMod 23) :
    ∃ list : Finset (Polynomial (ZMod 23)),
      list.card ≤ 307 * 23 ∧
      ∀ P, P ∈ list ↔ P.degree < 2 ∧
        8 ≤ Code.agree (fun i ↦ P.eval (uniformCanaryDomain i)) received := by
  have h := uniformFirstOrder_capacity_list (6 / 25 : ℝ) le_rfl
  obtain ⟨list, hexact, _hempty, hcard⟩ := h 23 2 23 8
    (by norm_num) (by norm_num) (by norm_num) (by decide) (by norm_num)
    (by norm_num) (by norm_num) uniformCanaryDomain received
  exact ⟨list, hcard, hexact⟩

end ReedSolomon
