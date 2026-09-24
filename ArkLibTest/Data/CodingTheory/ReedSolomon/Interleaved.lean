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
import ArkLib.Data.CodingTheory.ListDecodability.AgreementBound
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

private def domainTwoZMod2 : Fin 2 ↪ ZMod 2 :=
  ⟨fun i ↦ (i.val : ZMod 2), fun a b h ↦ by
    fin_cases a <;> fin_cases b <;> simp_all⟩

local instance : Fact (Nat.Prime 3) := ⟨by decide⟩

private def anchorDomainThree : Fin 2 ↪ ZMod 3 :=
  ⟨fun i ↦ (i.val : ZMod 3), by decide⟩

private def anchorReceivedThree : Fin 2 → Fin 1 → ZMod 3 := fun _ _ ↦ 0

private noncomputable def zeroAnchorCandidate : Fin 1 → (ZMod 3)[X] := fun _ ↦ 0

private noncomputable def lineAnchorCandidate : Fin 1 → (ZMod 3)[X] := fun _ ↦ X

private theorem anchorInterleavedLambdaBound :
    Lambda (interleavedCodeSet (κ := Fin 1)
      (code anchorDomainThree 2 : Set (Fin 2 → ZMod 3)))
        (1 - (1 : ℝ) / Fintype.card (Fin 2)) ≤ 9 := by
  apply Lambda_le_iff_forall_encard_le.mpr
  intro y
  calc
    (closeCodewordsRel (interleavedCodeSet (κ := Fin 1)
      (code anchorDomainThree 2 : Set (Fin 2 → ZMod 3))) y
        (1 - (1 : ℝ) / Fintype.card (Fin 2))).encard ≤
        (Set.univ : Set (Fin 2 → Fin 1 → ZMod 3)).encard := Set.encard_mono (by simp)
    _ = (Fintype.card (Fin 2 → Fin 1 → ZMod 3) : ℕ∞) := by simp
    _ = 9 := by norm_num [Fintype.card_fun]

private theorem anchorCandidate_mem (p : (ZMod 3)[X])
    (hdeg : p.degree < (2 : WithBot ℕ)) (hp0 : p.eval 0 = 0) :
    (fun _ : Fin 1 ↦ p) ∈ candidateSet anchorDomainThree anchorReceivedThree 2 1 := by
  rw [mem_candidateSet]
  constructor
  · intro _
    exact hdeg
  · rw [agree, Finset.one_le_card]
    refine ⟨0, ?_⟩
    simp only [Finset.mem_filter]
    constructor
    · simp
    · funext j
      fin_cases j
      simp [evalTuple, anchorDomainThree, anchorReceivedThree, hp0]

-- The zero and linear candidates agree at the anchor 0; four sampled anchors give a subunit
-- collision bound.
example :
    zeroAnchorCandidate ∈ candidateSet anchorDomainThree anchorReceivedThree 2 1 ∧
      lineAnchorCandidate ∈ candidateSet anchorDomainThree anchorReceivedThree 2 1 ∧
      zeroAnchorCandidate ≠ lineAnchorCandidate ∧
      Pr{let ω ← $ᵗ (Fin 4 → ZMod 3)}[
        ¬ Set.InjOn (evalTuple ω)
          (candidateSet anchorDomainThree anchorReceivedThree 2 1)] ≤
        ENNReal.ofReal (1 / 2 : ℝ) := by
  have hzero : zeroAnchorCandidate ∈
      candidateSet anchorDomainThree anchorReceivedThree 2 1 := by
    change (fun _ : Fin 1 ↦ (0 : (ZMod 3)[X])) ∈
      candidateSet anchorDomainThree anchorReceivedThree 2 1
    exact anchorCandidate_mem (p := 0)
      (by rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe _)
      (by simp)
  have hone : lineAnchorCandidate ∈
      candidateSet anchorDomainThree anchorReceivedThree 2 1 := by
    change (fun _ : Fin 1 ↦ (X : (ZMod 3)[X])) ∈
      candidateSet anchorDomainThree anchorReceivedThree 2 1
    exact anchorCandidate_mem (p := X) (by norm_num) (by simp)
  have hne : zeroAnchorCandidate ≠ lineAnchorCandidate := by
    intro h
    have hval := congrFun h 0
    exact (X_ne_zero (R := ZMod 3)) (by
      simpa [zeroAnchorCandidate, lineAnchorCandidate] using hval.symm)
  have hΛ : Lambda (interleavedCodeSet (κ := Fin 1)
      (code anchorDomainThree 2 : Set (Fin 2 → ZMod 3)))
        (1 - (1 : ℝ) / Fintype.card (Fin 2)) ≤ 9 := anchorInterleavedLambdaBound
  have hprob := prob_not_injOn_candidateSet_le
    (pt := fun ω : Fin 4 → ZMod 3 ↦ ω) (by intro ω ω' h; exact h)
    anchorDomainThree anchorReceivedThree (K := 2) (a := 1) (L := 9) (by decide)
    (by simpa using hΛ)
  refine ⟨hzero, hone, hne, ?_⟩
  have hchoose : (9).choose 2 = 36 := by rw [Nat.choose_two_right]
  have hΩ : Fintype.card (Fin 4 → ZMod 3) = 81 := by
    rw [Fintype.card_fun]
    norm_num
  calc
    Pr{let ω ← $ᵗ (Fin 4 → ZMod 3)}[
        ¬ Set.InjOn (evalTuple ω)
          (candidateSet anchorDomainThree anchorReceivedThree 2 1)] ≤
        ENNReal.ofReal (((9).choose 2 * (2 - 1) ^ Fintype.card (Fin 4) : ℕ) /
          (Fintype.card (Fin 4 → ZMod 3) : ℝ)) := hprob
    _ ≤ ENNReal.ofReal (1 / 2 : ℝ) := ENNReal.ofReal_le_ofReal (by
      norm_num [hchoose, hΩ, Fintype.card_fin])

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

private def nestedDegree : Fin 2 → ℕ := fun _ ↦ 1

private def nestedValues : (g : Fin 2) → Fin 2 → Fin 1 → ZMod 2 :=
  fun g t _ ↦ if g = t then 1 else 0

-- Both batching levels use two coefficients. The scalar singleton guarantee supplies the inner
-- interleaved guarantee and the outer guarantee for this concrete array.
example :
    ∃ bad : Finset (ZMod 2 × ZMod 2),
      bad.card ≤ Fintype.card (ZMod 2) * (0 + 0) ∧
        (1, 1) ∉ bad ∧
        HasExactNestedPowerAgreement point nestedDegree nestedValues 1 1 1 0 := by
  have hdegree : ∀ g : Fin 2, nestedDegree g ≤ 1 := by
    intro g
    simp [nestedDegree]
  have hinner : UniformExactInterleavedPowerAgreement point
      (paddedPowerValues nestedDegree hdegree nestedValues) 1 1 0 :=
    uniformExactInterleavedPowerAgreement_of_scalar point singletonPowerGuarantee le_rfl _
  have houter : ∀ u, UniformExactPowerAgreement point
      (fun g ↦ powerBatchedWord (nestedValues g) u) 1 1 0 := by
    intro u
    exact singletonPowerGuarantee (fun g ↦ powerBatchedWord (nestedValues g) u)
  have hshared := nestedPowerAgreement_sharedInner (maxDegree := 1) (k := 1) (L := 1)
    (innerE := 0) (outerE := 0) point nestedDegree hdegree nestedValues le_rfl hinner houter
  obtain ⟨bad, hbadCard, hgood⟩ := hshared
  have hbad : bad = ∅ := Finset.card_eq_zero.mp (by
    have : bad.card ≤ 0 := by simpa using hbadCard
    omega)
  have hword : powerBatchedWord (fun g ↦ powerBatchedWord (nestedValues g) 1) 1 =
      fun _ : Fin 1 ↦ (0 : ZMod 2) := by
    funext i
    fin_cases i
    norm_num [powerBatchedWord, nestedValues, Fin.sum_univ_two, ZMod.natCast_self]
    exact ZMod.natCast_self 2
  have hclose : 1 ≤ (polynomialAgreementSet point
      (powerBatchedWord (fun g ↦ powerBatchedWord (nestedValues g) 1) 1) 0).card := by
    rw [hword]
    simp [polynomialAgreementSet, point]
  exact ⟨bad, hbadCard, by simp [hbad], hgood 1 1 (by simp [hbad]) 0 (by simp) hclose⟩

private def foldValues : (Fin 3 → Bool) → Fin 1 → Fin 1 → ZMod 2 :=
  fun leaf _ _ ↦ (if leaf 0 then 1 else 0) + (if leaf 1 then 1 else 0) +
    (if leaf 2 then 1 else 0)

example :
    (tensorFoldBad
      (fullSetLevelWitness_interleaved_of_exactAgreement point singletonPowerGuarantee le_rfl
        (Fin 1)) foldValues).card ≤ 0 := by
  simpa using interleavedRS_tensorFoldBad_card_le_heightThree point singletonPowerGuarantee
    le_rfl (κ := Fin 1) foldValues

noncomputable section

local instance : DecidableEq (RatFunc (ZMod 2)) := Classical.decEq _

private theorem scalarRatFuncLambdaHalfBound :
    Lambda (code (domainTwoZMod2.trans ⟨algebraMap (ZMod 2) (RatFunc (ZMod 2)),
      (algebraMap (ZMod 2) (RatFunc (ZMod 2))).injective⟩) 1 :
        Set (Fin 2 → RatFunc (ZMod 2))) (1 / 2 : ℝ) ≤ 8 := by
  apply Lambda_le_of_forall_finset_card_le
  intro y T hT
  have hpair : ∀ c ∈ code (domainTwoZMod2.trans ⟨algebraMap (ZMod 2) (RatFunc (ZMod 2)),
      (algebraMap (ZMod 2) (RatFunc (ZMod 2))).injective⟩) 1,
      ∀ c' ∈ code (domainTwoZMod2.trans ⟨algebraMap (ZMod 2) (RatFunc (ZMod 2)),
        (algebraMap (ZMod 2) (RatFunc (ZMod 2))).injective⟩) 1,
        c ≠ c' → (agree c c' : ℝ) ≤ (1 / 4 : ℝ) ^ 2 * Fintype.card (Fin 2) := by
    intro c hc c' hc' hne
    have hlt := agree_lt_of_mem_code hc hc' hne
    have hzero : agree c c' = 0 := by omega
    rw [hzero]
    norm_num [Fintype.card_fin]
  have hbound := Code.card_le_of_pairwise_agree_le (by norm_num : (0 : ℝ) < 1 / 4)
    (by norm_num : (0 : ℝ) < 1 / 4) hpair y T (by
      intro c hc
      convert hT c hc using 1
      norm_num)
  have hreal : (T.card : ℝ) ≤ 8 := by
    norm_num at hbound ⊢
    exact hbound
  exact_mod_cast hreal

-- Packing over a two-point domain at radius one half has a finite scalar list-size bound.
example :
    Lambda (interleavedCodeSet (κ := Fin 2)
      (code domainTwoZMod2 1 : Set (Fin 2 → ZMod 2))) (1 / 2 : ℝ) ≤
        Lambda (code (domainTwoZMod2.trans ⟨algebraMap (ZMod 2) (RatFunc (ZMod 2)),
          (algebraMap (ZMod 2) (RatFunc (ZMod 2))).injective⟩) 1 :
            Set (Fin 2 → RatFunc (ZMod 2))) (1 / 2 : ℝ) ∧
      Lambda (code (domainTwoZMod2.trans ⟨algebraMap (ZMod 2) (RatFunc (ZMod 2)),
        (algebraMap (ZMod 2) (RatFunc (ZMod 2))).injective⟩) 1 :
          Set (Fin 2 → RatFunc (ZMod 2))) (1 / 2 : ℝ) ≤ 8 := by
  exact ⟨Lambda_interleaved_le_ratFunc domainTwoZMod2 1 2 (1 / 2 : ℝ),
    scalarRatFuncLambdaHalfBound⟩

end

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
