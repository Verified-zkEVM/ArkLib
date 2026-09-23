/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Agreement
import ArkLib.Data.CodingTheory.ReedSolomon.AgreementThreshold
import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement
import Mathlib.FieldTheory.Finite.Extension
import Mathlib.Tactic.NormNum

/-!
# Reed–Solomon acceptance tests

Concrete instances check the agreement threshold, its distance interpretation, codeword
determination, and the single-word power-agreement guarantee.
-/

open Polynomial ReedSolomon CoreDefinitions

namespace ReedSolomonAcceptance

-- Block length `10`, message length `3`, gap `1 / 4`: the threshold is `3 + ⌈5 / 2⌉ = 6`.
example : agreementThreshold (1 / 4) 10 3 = 6 := by
  have hceil : ⌈(5 / 2 : ℝ)⌉₊ = 3 := by
    rw [Nat.ceil_eq_iff (by decide)]
    norm_num
  apply Nat.le_antisymm
  · exact (agreementThreshold_le_iff_real (by norm_num) 10 3 6).2 (by norm_num)
  · norm_num [agreementThreshold, hceil]

example :
    agreementThreshold (1 / 4) 2 1 ≤ Code.agree ![false, false] ![false, false] ∧
      (Code.relHammingDist ![false, false] ![false, false] : ℝ) ≤
        capacityRadius (1 / 4) 2 1 := by
  have hthreshold : agreementThreshold (1 / 4) 2 1 ≤ 2 := by
    rw [agreementThreshold_le_iff_real (by norm_num) 2 1 2]
    norm_num
  have hagree : Code.agree ![false, false] ![false, false] = 2 := by
    simp [Code.agree]
  constructor
  · simpa [hagree] using hthreshold
  · exact (relHammingDist_le_capacityRadius_iff_agreementThreshold_le
      (delta := 1 / 4) (messageDim := 1) (by norm_num) (by decide)
      ![false, false] ![false, false]).mpr (by simpa [hagree] using hthreshold)

end ReedSolomonAcceptance

namespace PowerAgreementTest

/-- The evaluation points `0, 1, 2` in `ℚ`. -/
def domain3 : Fin 3 ↪ ℚ :=
  ⟨fun i ↦ ((i : ℕ) : ℚ), fun _ _ h ↦ Fin.ext (Nat.cast_injective (R := ℚ) h)⟩

example : Code.DeterminedByAgreement (code domain3 2) 2 :=
  determinedByAgreement_code domain3 le_rfl

-- A single received word has uniform exact power agreement with no exceptional challenge.
example : UniformExactPowerAgreement domain3 ![![1, 2, 5]] 2 0 0 :=
  uniformExactPowerAgreement_singleton domain3 _ 2 0

end PowerAgreementTest

namespace ReedSolomonAgreementAcceptance

noncomputable section

private abbrev E₄ := FiniteField.Extension (ZMod 2) 2 2
local instance : DecidableEq E₄ := Classical.decEq _

private def twoPointDomain : Fin 2 ↪ ZMod 2 where
  toFun i := if i.val = 0 then 0 else 1
  inj' := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all

/-- The polynomial `X` agrees with zero at the first of two evaluation points, over the base
field and its degree-two extension. -/
example :
    polynomialAgreementSet twoPointDomain (fun _ ↦ 0) (X : (ZMod 2)[X]) = {0} ∧
      polynomialAgreementSet
        (twoPointDomain.trans
          ⟨algebraMap (ZMod 2) E₄, (algebraMap (ZMod 2) E₄).injective⟩)
        (fun _ ↦ algebraMap (ZMod 2) E₄ (0 : ZMod 2))
        ((X : (ZMod 2)[X]).map (algebraMap (ZMod 2) E₄)) = {0} ∧
      polynomialAgreementSet
        (twoPointDomain.trans
          ⟨algebraMap (ZMod 2) E₄, (algebraMap (ZMod 2) E₄).injective⟩)
        (fun _ ↦ algebraMap (ZMod 2) E₄ (0 : ZMod 2))
        ((X : (ZMod 2)[X]).map (algebraMap (ZMod 2) E₄)) =
          polynomialAgreementSet twoPointDomain (fun _ ↦ 0) (X : (ZMod 2)[X]) := by
  refine ⟨?_, ?_, ?_⟩
  · ext i
    fin_cases i <;> norm_num [polynomialAgreementSet, twoPointDomain, Polynomial.eval_X]
  · ext i
    fin_cases i <;> norm_num [polynomialAgreementSet, twoPointDomain, Polynomial.eval_X]
  · exact polynomialAgreementSet_map twoPointDomain (algebraMap (ZMod 2) E₄)
      (algebraMap (ZMod 2) E₄).injective (fun _ ↦ 0) (X : (ZMod 2)[X])

private def repeatedDomain : Fin 3 → ZMod 2 := fun i => if i.val = 1 then 1 else 0

/-- Agreement counts are preserved on a finite indexed domain with repeated evaluation points. -/
example :
    (Finset.univ.filter fun i : Fin 3 =>
      (X : (ZMod 2)[X]).eval (repeatedDomain i) = (0 : ZMod 2)).card = 2 ∧
      (Finset.univ.filter fun i : Fin 3 =>
        ((X : (ZMod 2)[X]).map (algebraMap (ZMod 2) E₄)).eval
            (algebraMap (ZMod 2) E₄ (repeatedDomain i)) = (0 : E₄)).card = 2 := by
  have hsource : (Finset.univ.filter fun i : Fin 3 =>
      (X : (ZMod 2)[X]).eval (repeatedDomain i) = (0 : ZMod 2)).card = 2 := by
    have hset : (Finset.univ.filter fun i : Fin 3 =>
        (X : (ZMod 2)[X]).eval (repeatedDomain i) = (0 : ZMod 2)) = {0, 2} := by
      ext i
      fin_cases i <;> norm_num [Polynomial.eval_X, repeatedDomain]
    rw [hset]
    norm_num
  refine ⟨hsource, ?_⟩
  simpa [Polynomial.eval_X] using
    (card_polynomialAgreement_map (algebraMap (ZMod 2) E₄)
      (algebraMap (ZMod 2) E₄).injective repeatedDomain
      (fun _ ↦ 0) X).trans hsource

end
end ReedSolomonAgreementAcceptance
