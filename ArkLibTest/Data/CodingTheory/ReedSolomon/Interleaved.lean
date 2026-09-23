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
remainders, anchored candidate lists and reconstructions, scalar-to-interleaved power agreement at
a singleton domain, and the height-three tensor-fold count for concrete interleaved leaves.
-/

open Polynomial Code ReedSolomon ReedSolomon.AnchoredAgreement TensorMCA
open scoped ProbabilityTheory

namespace InterleavedAcceptance

example : tupleRatFunc ![(1 : ZMod 2), 0] ≠ tupleRatFunc ![0, 1] := by
  intro h
  have := congrFun (tupleRatFunc_injective h) 0
  simp at this

/-- The single evaluation point `0` of `ZMod 2`. -/
private def point : Fin 1 ↪ ZMod 2 :=
  ⟨fun _ ↦ 0, fun a b _ ↦ Subsingleton.elim a b⟩

private def singletonReceived : Fin 1 → Fin 1 → ZMod 2 := fun _ _ ↦ 0

private theorem singletonInterleavedLambdaBound :
    Lambda (interleavedCodeSet (κ := Fin 1) (code point 1 : Set (Fin 1 → ZMod 2))) 0 ≤ 2 := by
  apply Lambda_le_iff_forall_encard_le.mpr
  intro y
  calc
    (closeCodewordsRel
      (interleavedCodeSet (κ := Fin 1) (code point 1 : Set (Fin 1 → ZMod 2))) y 0).encard ≤
        (Set.univ : Set (Fin 1 → Fin 1 → ZMod 2)).encard := Set.encard_mono (by simp)
    _ = (Fintype.card (Fin 1 → Fin 1 → ZMod 2) : ℕ∞) := by simp
    _ = 2 := by norm_num [Fintype.card_fun]

-- The zero received word has a degree-below-one candidate at full agreement.
example :
    (candidateSet point singletonReceived 1 1).encard ≤ 2 ∧
      (candidateSet point singletonReceived 1 1).Finite ∧
      (fun _ : Fin 1 ↦ (0 : (ZMod 2)[X])) ∈ candidateSet point singletonReceived 1 1 := by
  have hΛ :
      Lambda (interleavedCodeSet (κ := Fin 1) (code point 1 : Set (Fin 1 → ZMod 2)))
        (1 - (1 : ℝ) / Fintype.card (Fin 1)) ≤ 2 := by
    simpa using singletonInterleavedLambdaBound
  refine ⟨?_, ?_, ?_⟩
  · exact (encard_candidateSet_le_Lambda point singletonReceived (K := 1) (by decide) 1).trans
      (by simpa using hΛ)
  · exact finite_candidateSet_of_Lambda_le point singletonReceived (K := 1) (a := 1) (L := 2)
      (by decide) (by simpa using hΛ)
  · rw [mem_candidateSet]
    constructor
    · intro j
      simp
    · rw [agree, Finset.one_le_card]
      refine ⟨0, ?_⟩
      simp only [Finset.mem_filter]
      constructor
      · simp
      · funext j
        simp [evalTuple, point, singletonReceived]

private def singletonChallengePoint : Fin 1 → Fin 1 → ZMod 2 := fun _ _ ↦ 0

-- At the singleton challenge the only candidate is the zero polynomial, so the bad-anchor
-- probability is zero in this concrete instance.
example :
    Pr{let ω ← $ᵗ (Fin 1)}[
      ¬ Set.InjOn (evalTuple (singletonChallengePoint ω))
        (candidateSet point singletonReceived 1 1)] ≤ 0 := by
  have hpt : Function.Injective singletonChallengePoint := by
    intro a b _
    exact Subsingleton.elim a b
  simpa [singletonChallengePoint, singletonReceived] using
    (prob_not_injOn_candidateSet_le (pt := singletonChallengePoint) hpt point singletonReceived
      (K := 1) (a := 1) (L := 2) (by decide)
      (by simpa using singletonInterleavedLambdaBound))

private def domainTwo : Fin 2 ↪ ℚ :=
  ⟨fun i ↦ (i.val : ℚ), fun a b h ↦ Fin.ext (by simpa using h)⟩

noncomputable section

private def slopeReceived : Fin 2 → Fin 1 → ℚ := fun i _ ↦ domainTwo i
private def slopeTuple : Fin 1 → ℚ[X] := fun _ ↦ X
private def zeroTuple : Fin 1 → ℚ[X] := fun _ ↦ 0
private def vanishingDivisor : ℚ[X] := X * (X - C 1)

private theorem vanishingDivisor_eval (i : Fin 2) : vanishingDivisor.eval (domainTwo i) = 0 := by
  fin_cases i
  · change (X * (X - C (1 : ℚ))).eval (0 : ℚ) = 0
    norm_num
  · change (X * (X - C (1 : ℚ))).eval (1 : ℚ) = 0
    norm_num

private theorem vanishingDivisor_degree : vanishingDivisor.natDegree ≤ 2 := by
  change (X * (X - C (1 : ℚ))).natDegree ≤ 2
  calc
    _ ≤ X.natDegree + (X - C (1 : ℚ)).natDegree := natDegree_mul_le
    _ ≤ 1 + 1 := Nat.add_le_add (by simp) (by
      calc
        _ ≤ max X.natDegree (C (1 : ℚ)).natDegree := natDegree_sub_le _ _
        _ ≤ 1 := by simp)
    _ = 2 := by norm_num

private theorem slopeAnchorValues :
    evalTuple (domainTwo : Fin 2 → ℚ) slopeTuple = slopeReceived := by
  ext i j
  simp [slopeTuple, slopeReceived]

private theorem slopeQuotientAgrees :
    2 ≤ agree (fun i j ↦ vanishingDivisor.eval (domainTwo i) * (zeroTuple j).eval (domainTwo i))
      (fun i j ↦ slopeReceived i j - (slopeTuple j).eval (domainTwo i)) := by
  rw [← slopeAnchorValues]
  norm_num [agree, vanishingDivisor_eval, zeroTuple, slopeTuple, domainTwo, evalTuple]

-- The quotient equation and its reconstruction agree at both concrete domain points.
example :
    agree (evalTuple (domainTwo : Fin 2 → ℚ) slopeTuple) slopeReceived = 2 ∧
      agree (fun _ : Fin 2 => fun _ : Fin 1 => (0 : ℚ))
        (fun _ : Fin 2 => fun _ : Fin 1 => 0) = 2 := by
  have h := agree_evalTuple_mul_add (x := (domainTwo : Fin 2 → ℚ))
    (received := slopeReceived) (D := vanishingDivisor) (q := zeroTuple) (I := slopeTuple)
  have h' :
      agree (evalTuple (domainTwo : Fin 2 → ℚ) (fun _ : Fin 1 ↦ (X : ℚ[X]))) slopeReceived =
        agree (fun _ : Fin 2 => fun _ : Fin 1 => (0 : ℚ))
          (fun _ : Fin 2 => fun _ : Fin 1 => 0) := by
    simpa [slopeTuple, zeroTuple, vanishingDivisor, slopeReceived, domainTwo, evalTuple] using h
  constructor
  · change agree (evalTuple (domainTwo : Fin 2 → ℚ) (fun _ : Fin 1 ↦ (X : ℚ[X])))
      slopeReceived = 2
    rw [h']
    norm_num [agree]
  · norm_num [agree]

-- The nonzero reconstruction `X` is a candidate after the divisor and zero quotient vanish.
example : (fun _ : Fin 1 ↦ (X : ℚ[X])) ∈ candidateSet domainTwo slopeReceived 2 2 := by
  have hmem := mul_add_mem_candidateSet domainTwo slopeReceived (D := vanishingDivisor)
    (e := 2) (k := 0) (K := 2) (a := 2) vanishingDivisor_degree
    (by decide) (q := zeroTuple) (I := slopeTuple)
    (by intro _j; simp [zeroTuple]) (by intro _j; norm_num [slopeTuple]) slopeQuotientAgrees
  simpa [zeroTuple, slopeTuple] using hmem

-- Separating the candidate list at both anchors fixes this concrete later reconstruction.
example :
    ∃ selected : Option (Fin 1 → ℚ[X]),
      (∀ Q, selected = some Q ↔ Q ∈ candidateSet domainTwo slopeReceived 2 2 ∧
        evalTuple (domainTwo : Fin 2 → ℚ) Q = (fun i _ ↦ domainTwo i)) ∧
      selected = some (fun _ : Fin 1 ↦ (X : ℚ[X])) := by
  have hgood :
      Set.InjOn (evalTuple (domainTwo : Fin 2 → ℚ))
        (candidateSet domainTwo slopeReceived 2 2) := by
    intro P hP Q hQ h
    exact (injOn_evalTuple_of_degree_lt domainTwo (K := 2) (by decide)) hP.1 hQ.1 h
  obtain ⟨selected, hselected, hlater⟩ :=
    exists_selected_before_reconstruction domainTwo slopeReceived hgood
      (fun i j ↦ domainTwo i)
  refine ⟨selected, hselected, ?_⟩
  simpa [zeroTuple, slopeTuple, vanishingDivisor] using
    (hlater vanishingDivisor 2 0 zeroTuple slopeTuple vanishingDivisor_eval
      vanishingDivisor_degree (by decide) (by intro j; simp [zeroTuple])
      (by intro j; norm_num [slopeTuple]) slopeAnchorValues slopeQuotientAgrees)

end

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
    rw [eq_C_of_degree_le_zero (Order.lt_succ_iff.mp hQ), hcoeff]
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
