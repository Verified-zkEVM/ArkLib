/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AgreementBounds
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AnchoredAgreement
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AnchoredReconstruction
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.PowerAgreement
import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.TensorFoldAgreement
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-!
# Interleaved Reed–Solomon acceptance tests

Concrete instances exercise agreement bounds, anchored evaluation, cubic reconstruction, trace
remainders, scalar-to-interleaved power agreement at a singleton domain, and the height-three
tensor-fold count for concrete interleaved leaves.
-/

open Polynomial Code ReedSolomon ReedSolomon.AnchoredAgreement TensorMCA
open scoped ProbabilityTheory

namespace InterleavedAcceptance

private theorem degree_le_zero_of_degree_lt_one {F : Type*} [Semiring F] (P : F[X])
    (hP : P.degree < 1) : P.degree ≤ 0 := by
  apply (degree_le_iff_coeff_zero P 0).2
  intro m hm
  have hm' : 0 < m := by exact_mod_cast hm
  exact (degree_lt_iff_coeff_zero P 1).mp hP m (Nat.succ_le_iff.mpr hm')

example : tupleRatFunc ![(1 : ZMod 2), 0] ≠ tupleRatFunc ![0, 1] := by
  intro h
  have := congrFun (tupleRatFunc_injective h) 0
  simp at this

/-- The single evaluation point `0` of `ZMod 2`. -/
private def point : Fin 1 ↪ ZMod 2 :=
  ⟨fun _ ↦ 0, fun a b _ ↦ Subsingleton.elim a b⟩

private theorem singletonPowerGuarantee (w : Fin 2 → Fin 1 → ZMod 2) :
    UniformExactPowerAgreement point w 1 1 0 := by
  refine ⟨∅, by simp, fun z _ Q hQ hclose ↦ ?_⟩
  have hagree : polynomialAgreementSet point (powerBatchedWord w z) Q = Finset.univ :=
    Finset.eq_univ_of_card _
      (le_antisymm (Finset.card_le_univ _) (by simpa [Fintype.card_fin] using hclose))
  have heval := (mem_polynomialAgreementSet ..).mp (hagree ▸ Finset.mem_univ (0 : Fin 1))
  have hcoeff : Q.coeff 0 = powerBatchedWord w z 0 := by
    have hpoint : point 0 = 0 := rfl
    rw [hpoint] at heval
    exact (coeff_zero_eq_eval_zero Q).trans heval
  have hQeq : Q = C (powerBatchedWord w z 0) := by
    rw [eq_C_of_degree_le_zero (degree_le_zero_of_degree_lt_one Q hQ), hcoeff]
  have hbatch : powerBatchedPolynomial (fun t ↦ C (w t 0)) z =
      C (powerBatchedWord w z 0) := by
    simp [powerBatchedPolynomial, powerBatchedWord, Fin.sum_univ_two, smul_eq_C_mul]
  have hcommon : commonCurveAgreementSet point w (fun t ↦ C (w t 0)) = Finset.univ := by
    ext i
    fin_cases i
    simp [commonCurveAgreementSet, point]
  apply (hasExactPowerAgreement_id_iff point w 1 z Q).mpr
  refine ⟨fun t ↦ C (w t 0), ?_, ?_, ?_⟩
  · intro t
    exact (degree_C_le).trans_lt (by norm_num)
  · exact hQeq.trans hbatch.symm
  · rw [hagree, hcommon]

private def powerValues : Fin 2 → Fin 1 → Fin 1 → ZMod 2 :=
  fun t _ _ ↦ if t = 0 then 1 else 0

example : UniformExactInterleavedPowerAgreement point powerValues 1 1 0 :=
  uniformExactInterleavedPowerAgreement_of_scalar point singletonPowerGuarantee le_rfl powerValues

private def foldValues : (Fin 3 → Bool) → Fin 1 → Fin 1 → ZMod 2 :=
  fun leaf _ _ ↦ if leaf 0 then 1 else 0

example :
    (tensorFoldBad
      (fullSetLevelWitness_interleaved_of_exactAgreement point singletonPowerGuarantee le_rfl
        (Fin 1)) foldValues).card ≤ 0 := by
  simpa using interleavedRS_tensorFoldBad_card_le_heightThree point singletonPowerGuarantee
    le_rfl (κ := Fin 1) foldValues

-- Packing into `F(Z)` bounds the list size of a concrete two-fold interleaving.
example :
    Lambda (interleavedCodeSet (κ := Fin 2) (code point 1 : Set (Fin 1 → ZMod 2))) 1 ≤
      Lambda (code (point.trans ⟨algebraMap (ZMod 2) (RatFunc (ZMod 2)),
        (algebraMap (ZMod 2) (RatFunc (ZMod 2))).injective⟩) 1 :
          Set (Fin 1 → RatFunc (ZMod 2))) 1 :=
  Lambda_interleaved_le_ratFunc point 1 2 1

private def domain3 : Fin 3 ↪ ℚ :=
  ⟨fun i ↦ (i : ℚ), fun a b h ↦ Fin.ext (by simpa using h)⟩

example : Set.InjOn (evalTuple (domain3 : Fin 3 → ℚ))
    {Q : Fin 1 → ℚ[X] | ∀ j, (Q j).degree < 2} :=
  injOn_evalTuple_of_degree_lt domain3 (by decide)

example : cubicAnchorDivisor (0 : ℚ) 1 2 = Lagrange.nodal Finset.univ ![0, 1, 2] :=
  cubicAnchorDivisor_eq_nodal 0 1 2

example : (cubicAnchorReconstruct (0 : ℚ) 1 2 1 (X ^ 2)).eval 2 = 4 := by
  rw [(cubicAnchorReconstruct_eval_anchors (0 : ℚ) 1 2 1 (X ^ 2)).2.2]
  norm_num

example : (cubicAnchorReconstruct (0 : ℚ) 1 2 1 (X ^ 2)).eval 3 = 15 :=
  cubicAnchorReconstruct_eval_of_quotient 0 1 2 3 15 1 (X ^ 2)
    (by simp [cubicAnchorDivisor]; norm_num)

example : (cubicAnchorReconstruct (0 : ℚ) 1 2 1 (X ^ 2)).degree < (1 + 3 : ℕ) :=
  cubicAnchorReconstruct_degree_lt 0 1 2 (by simp) (by rw [degree_X_pow]; decide)

example : ((X ^ 3 : ℚ[X]) %ₘ (X ^ 2 - C 1)).eval (-1) = -1 := by
  rw [traceRemainder_eval_eq 2 1 (X ^ 3) (by norm_num)]
  norm_num

example : ((X ^ 3 : ℚ[X]) %ₘ (X ^ 2 - C 1)).degree < (2 : ℕ) :=
  traceRemainder_degree_lt 2 (by decide) 1 _

end InterleavedAcceptance
