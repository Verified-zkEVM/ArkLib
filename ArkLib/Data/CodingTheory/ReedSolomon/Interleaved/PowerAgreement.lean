/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.NestedPowerAgreement
public import ArkLib.Data.CodingTheory.ReedSolomon.Interleaved.AgreementBounds
/-!
# Shared-challenge power agreement for interleaved Reed--Solomon codes

A scalar power-agreement certificate controls every nonempty row-wise interleaving with the
same exceptional count.  For each bad challenge, the coefficient projections that already lie
in the punctured scalar code form a proper subspace of the row-dual space.  At most `|F|` such
proper subspaces cannot cover that space, so one scalar projection detects every bad challenge.

The resulting certificate recovers all row polynomials and the complete simultaneous agreement
set.  It retains the scalar curve bound, without an additional factor for the row width or the
number of coefficients.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial Code CoreDefinitions LinearCode
open scoped BigOperators

variable {F : Type} [Field F]

/-- Simultaneous agreements between a tuple of polynomials and a row-wise received word. -/
def interleavedPolynomialAgreementSet [DecidableEq F] {n width : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → Fin width → F)
    (Q : Fin width → F[X]) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ ∀ j, (Q j).eval (domain i) = received i j

/-- Simultaneous constituent agreements for an interleaved power curve. -/
def interleavedCommonPowerAgreementSet [DecidableEq F] {n width ℓ : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → Fin width → F)
    (P : Fin (ℓ + 1) → Fin width → F[X]) : Finset (Fin n) :=
  Finset.univ.filter fun i ↦ ∀ t j, (P t j).eval (domain i) = values t i j

/-- The row-wise power combination selected by one scalar challenge. -/
def interleavedPowerBatchedWord {n width ℓ : ℕ}
    (values : Fin (ℓ + 1) → Fin n → Fin width → F) (z : F) :
    Fin n → Fin width → F :=
  fun i j ↦ ∑ t, z ^ t.val * values t i j

/-- Exact recovery for every row of an interleaved power curve, including equality of the
complete simultaneous agreement set. -/
def HasExactInterleavedPowerAgreement [DecidableEq F] {n width ℓ : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → Fin width → F)
    (k : ℕ) (z : F) (Q : Fin width → F[X]) : Prop :=
  ∃ P : Fin (ℓ + 1) → Fin width → F[X],
    (∀ t j, (P t j).degree < k) ∧
    (∀ j, Q j = powerBatchedPolynomial (fun t ↦ P t j) z) ∧
    interleavedPolynomialAgreementSet domain (interleavedPowerBatchedWord values z) Q =
      interleavedCommonPowerAgreementSet domain values P

/-- A single exceptional set works for every degree-bounded interleaved candidate tuple. -/
def UniformExactInterleavedPowerAgreement [DecidableEq F] {n width ℓ : ℕ}
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → Fin width → F)
    (k agreement exceptionalCount : ℕ) : Prop :=
  ∃ bad : Finset F, bad.card ≤ exceptionalCount ∧
    ∀ z ∉ bad, ∀ Q : Fin width → F[X], (∀ j, (Q j).degree < k) →
      agreement ≤
        (interleavedPolynomialAgreementSet domain (interleavedPowerBatchedWord values z) Q).card →
      HasExactInterleavedPowerAgreement domain values k z Q

/-- Extend a finite tuple by zero to a larger width. -/
def padFin {A : Type*} [Zero A] {a b : ℕ} (_h : a ≤ b) (f : Fin a → A) (i : Fin b) : A :=
  if hi : i.val < a then f ⟨i.val, hi⟩ else 0

/-- Zero-padding does not change the sum of a finite tuple. -/
theorem sum_padFin {A : Type*} [AddCommMonoid A] {a b : ℕ} (h : a ≤ b) (f : Fin a → A) :
    ∑ i : Fin b, padFin h f i = ∑ i : Fin a, f i := by
  let g : ℕ → A := fun i ↦ if hi : i < a then f ⟨i, hi⟩ else 0
  calc
    ∑ i : Fin b, padFin h f i = ∑ i : Fin b, g i.val := by
      apply Finset.sum_congr rfl
      intro i _
      simp [padFin, g]
    _ = ∑ i ∈ Finset.range b, g i := Fin.sum_univ_eq_sum_range g b
    _ = (∑ i ∈ Finset.range a, g i) + ∑ i ∈ Finset.Ico a b, g i :=
      (Finset.sum_range_add_sum_Ico g h).symm
    _ = ∑ i ∈ Finset.range a, g i := by
      have hz : ∑ i ∈ Finset.Ico a b, g i = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        simp only [Finset.mem_Ico] at hi
        simp [g, Nat.not_lt.mpr hi.1]
      rw [hz, add_zero]
    _ = ∑ i : Fin a, g i.val := (Fin.sum_univ_eq_sum_range g a).symm
    _ = ∑ i : Fin a, f i := by
      apply Finset.sum_congr rfl
      intro i _
      simp [g]

/-- Pad ragged power-curve rows to one common maximum degree. -/
def paddedPowerValues {n rows maxDegree : ℕ} (degree : Fin rows → ℕ)
    (hdegree : ∀ g, degree g ≤ maxDegree)
    (values : (g : Fin rows) → Fin (degree g + 1) → Fin n → F) :
    Fin (maxDegree + 1) → Fin n → Fin rows → F :=
  fun t i g ↦ padFin (Nat.add_le_add_right (hdegree g) 1) (fun j ↦ values g j i) t

/-- Padding each group by zero preserves its power-batched received word. -/
theorem interleavedPowerBatchedWord_padded_apply {n rows maxDegree : ℕ}
    (degree : Fin rows → ℕ) (hdegree : ∀ g, degree g ≤ maxDegree)
    (values : (g : Fin rows) → Fin (degree g + 1) → Fin n → F)
    (z : F) (i : Fin n) (g : Fin rows) :
    interleavedPowerBatchedWord (paddedPowerValues degree hdegree values) z i g =
      powerBatchedWord (values g) z i := by
  unfold interleavedPowerBatchedWord paddedPowerValues powerBatchedWord
  rw [← sum_padFin (Nat.add_le_add_right (hdegree g) 1)
    (fun j : Fin (degree g + 1) ↦ z ^ j.val * values g j i)]
  apply Finset.sum_congr rfl
  intro t _
  simp only [padFin]
  split_ifs <;> simp

/-- At most `|K|` proper subspaces cannot cover a nontrivial finite `K`-vector space. -/
theorem exists_vector_avoiding_submodules
    {α K M : Type} [Field K] [Fintype K] [AddCommGroup M] [Module K M]
    [Finite M] [Nontrivial M]
    (s : Finset α) (p : α → Submodule K M)
    (hp : ∀ i ∈ s, p i ≠ ⊤) (hs : s.card ≤ Fintype.card K) :
    ∃ x : M, ∀ i ∈ s, x ∉ p i := by
  classical
  let := Fintype.ofFinite M
  let q := Fintype.card K
  let d := Module.finrank K M
  let nz (i : α) := Finset.univ.filter fun x : M => x ∈ p i ∧ x ≠ 0
  let covered := insert (0 : M) (s.biUnion nz)
  have hq : 1 < q := Fintype.one_lt_card
  have hd : 0 < d := Module.finrank_pos
  have hnz (i : α) (hi : i ∈ s) : (nz i).card ≤ q ^ (d - 1) - 1 := by
    let allp := Finset.univ.filter fun x : M => x ∈ p i
    have hzero : (0 : M) ∈ allp := by simp [allp]
    have hnz_eq : nz i = allp.erase 0 := by
      ext x
      simp [nz, allp, and_comm]
    rw [hnz_eq, Finset.card_erase_of_mem hzero]
    have hcard : allp.card = Fintype.card (p i) := by
      symm
      exact Fintype.card_ofFinset allp (by simp [allp])
    have hcardpow : Fintype.card (p i) = q ^ Module.finrank K (p i) := by
      simpa [q] using (Module.card_eq_pow_finrank (K := K) (V := p i))
    rw [hcard, hcardpow]
    exact Nat.sub_le_sub_right
      (Nat.pow_le_pow_right (Nat.zero_lt_of_lt hq)
        (Nat.le_sub_one_of_lt (Submodule.finrank_lt (hp i hi)))) 1
  have hcovered : covered.card < Fintype.card M := by
    have hbi : (s.biUnion nz).card ≤ s.card * (q ^ (d - 1) - 1) := by
      calc
        (s.biUnion nz).card ≤ ∑ i ∈ s, (nz i).card := Finset.card_biUnion_le
        _ ≤ ∑ _i ∈ s, (q ^ (d - 1) - 1) :=
          Finset.sum_le_sum fun i hi => hnz i hi
        _ = s.card * (q ^ (d - 1) - 1) := by simp
    have hmul : s.card * (q ^ (d - 1) - 1) ≤ q * (q ^ (d - 1) - 1) :=
      Nat.mul_le_mul_right _ hs
    have hpow : q ^ d = q * q ^ (d - 1) := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hd]
      simp [pow_succ, Nat.mul_comm]
    have hcardM : Fintype.card M = q ^ d := by
      simpa [q, d] using (Module.card_eq_pow_finrank (K := K) (V := M))
    rw [hcardM, hpow]
    calc
      covered.card ≤ (s.biUnion nz).card + 1 := Finset.card_insert_le _ _
      _ ≤ s.card * (q ^ (d - 1) - 1) + 1 := Nat.add_le_add_right hbi 1
      _ ≤ q * (q ^ (d - 1) - 1) + 1 := Nat.add_le_add_right hmul 1
      _ < q * q ^ (d - 1) := by
        have hpos : 0 < q ^ (d - 1) := pow_pos (Nat.zero_lt_of_lt hq) _
        have hqmul : q ≤ q * q ^ (d - 1) := by
          simpa using Nat.mul_le_mul_left q hpos
        rw [Nat.mul_sub_left_distrib]
        simp only [mul_one]
        omega
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := covered) (t := Finset.univ) (by simpa using hcovered)
  refine ⟨x, fun i hi hxi => hx ?_⟩
  by_cases hx0 : x = 0
  · simp [covered, hx0]
  · simp only [covered, Finset.mem_insert]
    exact Or.inr (Finset.mem_biUnion.mpr ⟨i, hi, by simp [nz, hxi, hx0]⟩)

/-- Two interleaved Reed--Solomon codewords agreeing on at least `k` positions are equal. -/
theorem interleavedCodeword_eq_of_agree_on
    {τ : Type} {n k : ℕ} (domain : Fin n ↪ F)
    (S : Finset (Fin n)) (hkS : k ≤ S.card)
    {c d : Fin n → τ → F}
    (hc : c ∈ ModuleCode.moduleInterleavedCode F F (τ) (Fin n) (code domain k))
    (hd : d ∈ ModuleCode.moduleInterleavedCode F F (τ) (Fin n) (code domain k))
    (hagree : ∀ i ∈ S, c i = d i) : c = d := by
  apply _root_.funext
  intro i
  apply _root_.funext
  intro j
  have hcj := (mem_moduleInterleavedCode_iff F F (τ) (Fin n)
    (code domain k) c).mp hc j
  have hdj := (mem_moduleInterleavedCode_iff F F (τ) (Fin n)
    (code domain k) d).mp hd j
  obtain ⟨P, hP, hPeval⟩ := mem_code_iff_eval.mp hcj
  obtain ⟨Q, hQ, hQeval⟩ := mem_code_iff_eval.mp hdj
  change ∀ x, P.eval (domain x) = c x j at hPeval
  change ∀ x, Q.eval (domain x) = d x j at hQeval
  have hPQ : P = Q := by
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := S) domain.injective.injOn
      (hP.trans_le (by exact_mod_cast hkS)) (hQ.trans_le (by exact_mod_cast hkS))
    intro x hx
    rw [hPeval x, hQeval x]
    exact congrFun (hagree x hx) j
  change c i j = d i j
  rw [← hPeval i, ← hQeval i, hPQ]

/-- Failure of constituent projection at an integer agreement threshold. -/
private def powerProjectionBad {ι A : Type*} [Fintype ι]
    [AddCommMonoid A] [Module F A]
    (C : ModuleCode ι F A) (agreement : ℕ) (z : F)
    {ℓ : ℕ} (values : Fin (ℓ + 1) → ι → A) : Prop :=
  ∃ T : Finset ι,
    agreement ≤ T.card ∧
    projectedWord (fun i ↦ ∑ t, z ^ t.val • values t i) T ∈ projectedCodeSubmod C T ∧
    ∃ t, projectedWord (values t) T ∉ projectedCodeSubmod C T

open Classical in
private theorem scalar_powerProjectionBad_card_le
    [Fintype F] [DecidableEq F]
    {n k agreement exceptionalCount ℓ : ℕ}
    (domain : Fin n ↪ F)
    (values : Fin (ℓ + 1) → Fin n → F)
    (hpower : UniformExactPowerAgreement domain values k agreement exceptionalCount) :
    (Finset.univ.filter fun z : F ↦
      powerProjectionBad (code domain k) agreement z values).card ≤ exceptionalCount := by
  classical
  obtain ⟨exceptional, hcard, hgood⟩ := hpower
  apply (Finset.card_le_card ?_).trans hcard
  intro z hz
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz
  obtain ⟨T, hTcard, hroot, t, ht⟩ := hz
  have hroot' : projectedWord (powerBatchedWord values z) T ∈
      projectedCodeSubmod (code domain k) T := by
    convert hroot using 1
    ext i
    rfl
  obtain ⟨Q, hQdegree, hQonT⟩ :=
    (projectedWord_mem_code_iff_exists_polynomial domain k _ T).mp hroot'
  have hsubset : T ⊆ polynomialAgreementSet domain (powerBatchedWord values z) Q := by
    intro i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, by
      simpa [powerBatchedWord, smul_eq_mul] using hQonT i hi⟩
  have hagreement : agreement ≤
      (polynomialAgreementSet domain (powerBatchedWord values z) Q).card :=
    hTcard.trans (Finset.card_le_card hsubset)
  by_contra hzExceptional
  obtain ⟨P, hPdegree, -, hset⟩ := hgood z hzExceptional Q hQdegree hagreement
  apply ht
  apply (projectedWord_mem_code_iff_exists_polynomial domain k (values t) T).mpr
  refine ⟨P t, hPdegree t, fun i hi ↦ ?_⟩
  have hmem := congrArg (fun s : Finset (Fin n) ↦ i ∈ s) hset
  have hi' := hmem.mp (hsubset hi)
  have hall : ∀ t, (P t).eval (domain i) = values t i := by
    simpa only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ, true_and]
      using hi'
  exact hall t

open Classical in
private theorem interleaved_powerProjectionBad_card_le
    [Fintype F]
    {ι : Type} [Fintype ι] {agreement exceptionalCount width ℓ : ℕ}
    (C : ModuleCode ι F F) (hwidth : 0 < width)
    (hscalar : ∀ values : Fin (ℓ + 1) → ι → F,
      (Finset.univ.filter fun z : F ↦
        powerProjectionBad C agreement z values).card ≤ exceptionalCount)
    (values : Fin (ℓ + 1) → ι → Fin width → F) :
    (Finset.univ.filter fun z : F ↦
      powerProjectionBad (C ^⋈ (Fin width)) agreement z values).card ≤ exceptionalCount := by
  classical
  let : Nonempty (Fin width) := Fin.pos_iff_nonempty.mp hwidth
  let isBad (z : F) := powerProjectionBad (C ^⋈ (Fin width)) agreement z values
  let bad := Finset.univ.filter isBad
  obtain ⟨T, hT⟩ : ∃ T : F → Finset ι, ∀ z, isBad z →
      agreement ≤ (T z).card ∧
      projectedWord (fun i ↦ ∑ t, z ^ t.val • values t i) (T z) ∈
        projectedCodeSubmod (C ^⋈ (Fin width)) (T z) ∧
      ∃ t, projectedWord (values t) (T z) ∉
        projectedCodeSubmod (C ^⋈ (Fin width)) (T z) := by
    choose! T hT using fun z (hz : isBad z) => hz
    exact ⟨T, hT⟩
  let rowComb (l : Fin width → F) (t : Fin (ℓ + 1)) : ι → F := fun i ↦
    ∑ j, l j * values t i j
  let K (z : F) : Submodule F (Fin width → F) := {
    carrier := {l | ∀ t,
      projectedWord (rowComb l t) (T z) ∈ projectedCodeSubmod C (T z)}
    zero_mem' := by
      intro t
      have hz : projectedWord (rowComb 0 t) (T z) = 0 := by
        ext i
        simp [projectedWord, rowComb]
      rw [hz]
      exact (projectedCodeSubmod C (T z)).zero_mem
    add_mem' := by
      intro l l' hl hl' t
      have hadd : projectedWord (rowComb (l + l') t) (T z) =
          projectedWord (rowComb l t) (T z) + projectedWord (rowComb l' t) (T z) := by
        ext i
        simp [projectedWord, rowComb, add_mul, Finset.sum_add_distrib]
      rw [hadd]
      exact (projectedCodeSubmod C (T z)).add_mem (hl t) (hl' t)
    smul_mem' := by
      intro a l hl t
      have hsmul : projectedWord (rowComb (a • l) t) (T z) =
          a • projectedWord (rowComb l t) (T z) := by
        ext i
        simp [projectedWord, rowComb, Finset.mul_sum, mul_assoc]
      rw [hsmul]
      exact (projectedCodeSubmod C (T z)).smul_mem a (hl t) }
  have hK (z : F) (hz : z ∈ bad) : K z ≠ ⊤ := by
    obtain ⟨t, ht⟩ := (hT z (Finset.mem_filter.mp hz).2).2.2
    have ht' : ∃ j : Fin width,
        projectedWord (fun i ↦ values t i j) (T z) ∉ projectedCodeSubmod C (T z) := by
      by_contra hall
      push Not at hall
      apply ht
      exact (projectedCodeSubmod_moduleInterleavedCode_iff F F (Fin width) ι
        C (values t) (T z)).mpr hall
    obtain ⟨j, hj⟩ := ht'
    intro htop
    let e : Fin width → F := fun j' ↦ if j' = j then 1 else 0
    have he : e ∈ K z := by rw [htop]; exact Submodule.mem_top
    apply hj
    have hrow := he t
    convert hrow using 1
    ext i
    change values t (i : ι) j = ∑ j', e j' * values t (i : ι) j'
    simp [e]
  have hbadcard : bad.card ≤ Fintype.card F := by
    simpa [bad] using Finset.card_filter_le Finset.univ isBad
  obtain ⟨l, hl⟩ := exists_vector_avoiding_submodules bad K hK hbadcard
  have himp : ∀ z : F, isBad z →
      powerProjectionBad C agreement z (rowComb l) := by
    intro z hz
    have hzbad : z ∈ bad := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
    have hd := hT z hz
    refine ⟨T z, hd.1, ?_, ?_⟩
    · let batched : InterleavedWord F (Fin width) ι := fun i j ↦
        ∑ t, z ^ t.val * values t i j
      have hbatched : (fun i ↦ ∑ t, z ^ t.val • values t i) = batched := by
        funext i j
        simp [batched]
      have hroot : projectedWord batched (T z) ∈
          projectedCodeSubmod (C ^⋈ (Fin width)) (T z) := by
        rw [← hbatched]
        exact hd.2.1
      have hrows : ∀ j : Fin width,
          projectedWord (fun i ↦ ∑ t, z ^ t.val • values t i j) (T z) ∈
            projectedCodeSubmod C (T z) := by
        intro j
        have hj := (projectedCodeSubmod_moduleInterleavedCode_iff F F (Fin width) ι C
          batched (T z)).mp hroot j
        convert hj using 1
        ext i
        change (∑ t, z ^ t.val * values t (i : ι) j) = batched (i : ι) j
        rfl
      rw [mem_projectedCodeSubmod_iff]
      convert projectedCode_linearCombination C (T z)
        (fun j i ↦ ∑ t, z ^ t.val • values t i j) l
        (fun j ↦ (mem_projectedCodeSubmod_iff C (T z) _).mp (hrows j)) using 1
      ext i
      change ∑ t, z ^ t.val * (∑ j, l j * values t i j) =
        ∑ j, l j * (∑ t, z ^ t.val * values t i j)
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      apply Finset.sum_congr rfl
      intro j _
      ring
    · have hnot := hl z hzbad
      change ¬ ∀ t, projectedWord (rowComb l t) (T z) ∈
        projectedCodeSubmod C (T z) at hnot
      push Not at hnot
      exact hnot
  calc
    (Finset.univ.filter isBad).card ≤
        (Finset.univ.filter fun z : F ↦
          powerProjectionBad C agreement z (rowComb l)).card := by
      apply Finset.card_le_card
      intro z hz
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
      exact himp z hz
    _ ≤ exceptionalCount := hscalar _

/-- A scalar uniform exact-power certificate lifts to every nonempty row-wise interleaving,
without increasing its exceptional count. -/
theorem uniformExactInterleavedPowerAgreement_of_scalar
    [Finite F] [DecidableEq F]
    {n k agreement exceptionalCount width ℓ : ℕ}
    (domain : Fin n ↪ F)
    (hscalar : ∀ values : Fin (ℓ + 1) → Fin n → F,
      UniformExactPowerAgreement domain values k agreement exceptionalCount)
    (hwidth : 0 < width) (hkAgreement : k ≤ agreement)
    (values : Fin (ℓ + 1) → Fin n → Fin width → F) :
    UniformExactInterleavedPowerAgreement domain values k agreement exceptionalCount := by
  classical
  let _ := Fintype.ofFinite F
  let exceptional := Finset.univ.filter fun z : F ↦
    powerProjectionBad ((code domain k) ^⋈ (Fin width)) agreement z values
  refine ⟨exceptional, ?_, ?_⟩
  · exact interleaved_powerProjectionBad_card_le (code domain k) hwidth
      (fun scalarValues ↦ scalar_powerProjectionBad_card_le domain scalarValues
        (hscalar scalarValues)) values
  · intro z hz Q hQdegree hagreement
    have hgood : ¬ powerProjectionBad ((code domain k) ^⋈ (Fin width))
        agreement z values := by
      simpa [exceptional] using hz
    let S := interleavedPolynomialAgreementSet domain
      (interleavedPowerBatchedWord values z) Q
    let c : Fin n → Fin width → F := fun i j ↦ (Q j).eval (domain i)
    have hc : c ∈ ModuleCode.moduleInterleavedCode F F (Fin width) (Fin n)
        (code domain k) := by
      apply (mem_moduleInterleavedCode_iff F F (Fin width) (Fin n)
        (code domain k) c).mpr
      intro j
      exact evalOnPoints_mem_code_of_degree_lt (hQdegree j)
    have hroot : projectedWord (interleavedPowerBatchedWord values z) S ∈
        projectedCodeSubmod ((code domain k) ^⋈ (Fin width)) S := by
      rw [mem_projectedCodeSubmod_iff]
      refine ⟨c, hc, ?_⟩
      funext i
      funext j
      exact ((Finset.mem_filter.mp i.property).2 j).symm
    have hconstituents : ∀ t,
        projectedWord (values t) S ∈
          projectedCodeSubmod ((code domain k) ^⋈ (Fin width)) S := by
      by_contra h
      push Not at h
      obtain ⟨t, ht⟩ := h
      apply hgood
      refine ⟨S, hagreement, ?_, t, ht⟩
      convert hroot using 1
      ext i j
      change (∑ t, z ^ t.val • values t (i : Fin n)) j =
        ∑ t, z ^ t.val * values t (i : Fin n) j
      simp
    choose cP hcP hcPS using fun t ↦
      (mem_projectedCodeSubmod_iff _ S _).mp (hconstituents t)
    let P : Fin (ℓ + 1) → Fin width → F[X] := fun t j ↦
      Classical.choose (mem_code_iff_eval.mp
        ((mem_moduleInterleavedCode_iff F F (Fin width) (Fin n)
          (code domain k) (cP t)).mp (hcP t) j))
    have hPdegree (t) (j) : (P t j).degree < k :=
      (Classical.choose_spec (mem_code_iff_eval.mp
        ((mem_moduleInterleavedCode_iff F F (Fin width) (Fin n)
          (code domain k) (cP t)).mp (hcP t) j))).1
    have hPeval (t) (j) (i) : (P t j).eval (domain i) = cP t i j :=
      (Classical.choose_spec (mem_code_iff_eval.mp
        ((mem_moduleInterleavedCode_iff F F (Fin width) (Fin n)
          (code domain k) (cP t)).mp (hcP t) j))).2 i
    let combined : Fin n → Fin width → F := fun i j ↦ ∑ t, z ^ t.val * cP t i j
    have hcombined : combined ∈ ModuleCode.moduleInterleavedCode F F (Fin width) (Fin n)
        (code domain k) := by
      rw [show combined = ∑ t, (z ^ t.val) • cP t by
        funext i j
        simp [combined]]
      apply Submodule.sum_mem
      intro t _
      exact (ModuleCode.moduleInterleavedCode F F (Fin width) (Fin n)
        (code domain k)).smul_mem (z ^ t.val) (hcP t)
    have hcEq : c = combined := by
      apply interleavedCodeword_eq_of_agree_on domain S
        (hkAgreement.trans hagreement) hc hcombined
      intro i hi
      apply _root_.funext
      intro j
      have hci := (Finset.mem_filter.mp hi).2 j
      change (Q j).eval (domain i) = ∑ t, z ^ t.val * cP t i j
      rw [hci]
      apply Finset.sum_congr rfl
      intro t _
      have hti := congrFun (hcPS t) ⟨i, hi⟩
      change values t i = cP t i at hti
      rw [congrFun hti j]
    have hQidentity (j) : Q j = powerBatchedPolynomial (fun t ↦ P t j) z := by
      apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := S) domain.injective.injOn
        (hQdegree j |>.trans_le (by exact_mod_cast hkAgreement.trans hagreement))
        ((powerBatchedPolynomial_degree_lt (fun t ↦ P t j) z k
          (fun t ↦ hPdegree t j)).trans_le (by exact_mod_cast hkAgreement.trans hagreement))
      intro i hi
      rw [powerBatchedPolynomial_eval]
      have hcEqAt := congrFun (congrFun hcEq i) j
      change (Q j).eval (domain i) = combined i j at hcEqAt
      rw [hcEqAt]
      apply Finset.sum_congr rfl
      intro t _
      rw [hPeval]
    refine ⟨P, hPdegree, hQidentity, ?_⟩
    · ext i
      simp only [interleavedPolynomialAgreementSet, interleavedCommonPowerAgreementSet,
        Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hi t j
        have hiS : i ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩
        have ht := congrFun (hcPS t) ⟨i, hiS⟩
        change values t i = cP t i at ht
        rw [hPeval, ← congrFun ht j]
      · intro hi j
        rw [hQidentity]
        rw [powerBatchedPolynomial_eval]
        apply Finset.sum_congr rfl
        intro t _
        rw [hi t j]

/-- Exact outer agreement and one shared padded inner certificate recover the original ragged
groups. Coefficients beyond a group's degree vanish because they agree with zero on at least
`k` points. -/
theorem exactNestedPowerAgreement_of_interleaved
    [DecidableEq F] {n m maxDegree k agreement : ℕ}
    (domain : Fin n ↪ F) (degree : Fin (m + 1) → ℕ)
    (hdegree : ∀ g, degree g ≤ maxDegree)
    (values : (g : Fin (m + 1)) → Fin (degree g + 1) → Fin n → F)
    (hkAgreement : k ≤ agreement) (u v : F) (Q : F[X])
    (hclose : agreement ≤ (polynomialAgreementSet domain
      (powerBatchedWord (fun g ↦ powerBatchedWord (values g) u) v) Q).card)
    (houter : HasExactPowerAgreement domain (fun g ↦ powerBatchedWord (values g) u)
      (RingHom.id F) k v Q)
    (hinner : ∀ R : Fin (m + 1) → F[X], (∀ g, (R g).degree < k) →
      agreement ≤ (interleavedPolynomialAgreementSet domain
        (interleavedPowerBatchedWord (paddedPowerValues degree hdegree values) u) R).card →
      HasExactInterleavedPowerAgreement domain
        (paddedPowerValues degree hdegree values) k u R) :
    HasExactNestedPowerAgreement domain degree values k u v Q := by
  classical
  obtain ⟨R, hRdegree, hQeq, houterSet⟩ := houter
  simp only [Polynomial.map_id] at hQeq
  have houterSet' : polynomialAgreementSet domain
      (powerBatchedWord (fun g ↦ powerBatchedWord (values g) u) v) Q =
      commonCurveAgreementSet domain (fun g ↦ powerBatchedWord (values g) u) R := by
    simpa [mappedDomain] using houterSet
  let padded := paddedPowerValues degree hdegree values
  have hbatched (i : Fin n) (g : Fin (m + 1)) :
      interleavedPowerBatchedWord padded u i g = powerBatchedWord (values g) u i :=
    interleavedPowerBatchedWord_padded_apply degree hdegree values u i g
  have hsets : interleavedPolynomialAgreementSet domain
      (interleavedPowerBatchedWord padded u) R =
      polynomialAgreementSet domain
        (powerBatchedWord (fun g ↦ powerBatchedWord (values g) u) v) Q := by
    rw [houterSet']
    ext i
    simp only [interleavedPolynomialAgreementSet, commonCurveAgreementSet,
      Finset.mem_filter, Finset.mem_univ, true_and]
    constructor <;> intro h g
    · simpa [hbatched] using h g
    · simpa [hbatched] using h g
  have hinnerClose : agreement ≤
      (interleavedPolynomialAgreementSet domain
        (interleavedPowerBatchedWord padded u) R).card := by
    rw [hsets]
    exact hclose
  obtain ⟨Ppad, hPdegree, hReq, hinnerSet⟩ := hinner R hRdegree hinnerClose
  have hcommonCard : k ≤
      (interleavedCommonPowerAgreementSet domain
        (paddedPowerValues degree hdegree values) Ppad).card := by
    apply hkAgreement.trans
    rw [← hinnerSet]
    exact hinnerClose
  let P : (g : Fin (m + 1)) → Fin (degree g + 1) → F[X] :=
    fun g t ↦ Ppad ⟨t.val, (Nat.lt_succ_iff.mpr
      ((Nat.le_of_lt_succ t.isLt).trans (hdegree g)))⟩ g
  have hPdegree' (g) (t) : (P g t).degree < k := hPdegree _ g
  have hReq' (g) : R g = powerBatchedPolynomial (P g) u := by
    rw [hReq g]
    unfold powerBatchedPolynomial
    rw [← sum_padFin (Nat.add_le_add_right (hdegree g) 1)
      (fun t : Fin (degree g + 1) ↦ u ^ t.val • P g t)]
    apply Finset.sum_congr rfl
    intro t _
    simp only [padFin]
    split_ifs with ht
    · rfl
    · have hzero : Ppad t g = 0 := by
        let S := interleavedCommonPowerAgreementSet domain padded Ppad
        have hScard : k ≤ S.card := by simpa [S, padded] using hcommonCard
        apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := S) domain.injective.injOn
          (hPdegree t g |>.trans_le (by exact_mod_cast hScard))
          (by simp)
        intro i hi
        have hall := (Finset.mem_filter.mp hi).2 t g
        rw [hall]
        simp [padded, paddedPowerValues, padFin, ht]
      simp [hzero]
  refine ⟨P, hPdegree', ?_, ?_⟩
  · rw [hQeq]
    congr 1
    funext g
    exact hReq' g
  · have hcommonSets : commonCurveAgreementSet domain
        (fun g ↦ powerBatchedWord (values g) u) R =
        interleavedCommonPowerAgreementSet domain
          (paddedPowerValues degree hdegree values) Ppad :=
      houterSet'.symm.trans (hsets.symm.trans hinnerSet)
    rw [houterSet', hcommonSets]
    ext i
    simp only [interleavedCommonPowerAgreementSet, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · intro h g t
      have ht : t.val ≤ degree g := Nat.lt_succ_iff.mp t.isLt
      simpa [P, paddedPowerValues, padFin, ht] using
        h ⟨t.val, (Nat.lt_succ_iff.mpr
          ((Nat.le_of_lt_succ t.isLt).trans (hdegree g)))⟩ g
    · intro h t g
      by_cases ht : t.val < degree g + 1
      · simpa [P, paddedPowerValues, padFin, ht] using h g ⟨t.val, ht⟩
      · let S := interleavedCommonPowerAgreementSet domain padded Ppad
        have hScard : k ≤ S.card := by simpa [S, padded] using hcommonCard
        have hzero : Ppad t g = 0 := by
          apply Polynomial.eq_of_degrees_lt_of_eval_index_eq (s := S) domain.injective.injOn
            (hPdegree t g |>.trans_le (by exact_mod_cast hScard))
            (by simp)
          intro x hx
          have hall := (Finset.mem_filter.mp hx).2 t g
          rw [hall]
          simp [padded, paddedPowerValues, padFin, ht]
        simp [hzero, paddedPowerValues, padFin, ht]

/-- Two challenges compose one shared inner interleaving with the outer power curve. The inner
exception budget is paid once, independently of the number and widths of ragged groups. -/
theorem nestedPowerAgreement_sharedInner
    [Fintype F] [DecidableEq F] {n m maxDegree k agreement innerE outerE : ℕ}
    (domain : Fin n ↪ F) (degree : Fin (m + 1) → ℕ)
    (hdegree : ∀ g, degree g ≤ maxDegree)
    (values : (g : Fin (m + 1)) → Fin (degree g + 1) → Fin n → F)
    (hkAgreement : k ≤ agreement)
    (hinner : UniformExactInterleavedPowerAgreement domain
      (paddedPowerValues degree hdegree values) k agreement innerE)
    (houter : ∀ u, UniformExactPowerAgreement domain
      (fun g ↦ powerBatchedWord (values g) u) k agreement outerE) :
    ∃ bad : Finset (F × F),
      bad.card ≤ Fintype.card F * (innerE + outerE) ∧
      ∀ u v, (u, v) ∉ bad → ∀ Q : F[X], Q.degree < k →
        agreement ≤ (polynomialAgreementSet domain
          (powerBatchedWord (fun g ↦ powerBatchedWord (values g) u) v) Q).card →
        HasExactNestedPowerAgreement domain degree values k u v Q := by
  classical
  obtain ⟨innerBad, hinnerCard, hinnerGood⟩ := hinner
  choose outerBad houterCard houterGood using houter
  let outerPairs := Finset.univ.biUnion (fun u ↦ ({u} : Finset F).product (outerBad u))
  let bad := innerBad.product (Finset.univ : Finset F) ∪ outerPairs
  have ho : outerPairs.card ≤ Fintype.card F * outerE := by
    apply Finset.card_biUnion_le.trans
    calc
      ∑ u : F, (({u} : Finset F).product (outerBad u)).card ≤ ∑ _u : F, outerE := by
        apply Finset.sum_le_sum
        intro u _
        simpa using houterCard u
      _ = Fintype.card F * outerE := by simp
  refine ⟨bad, ?_, ?_⟩
  · calc
      bad.card ≤ (innerBad.product (Finset.univ : Finset F)).card + outerPairs.card :=
        Finset.card_union_le _ _
      _ ≤ innerE * Fintype.card F + Fintype.card F * outerE := by
        simpa using Nat.add_le_add (Nat.mul_le_mul_right (Fintype.card F) hinnerCard) ho
      _ = _ := by ring
  · intro u v huv Q hQ hclose
    have hu : u ∉ innerBad := by
      intro hu
      apply huv
      exact Finset.mem_union.mpr (Or.inl (Finset.mem_product.mpr
        ⟨hu, Finset.mem_univ _⟩))
    have hv : v ∉ outerBad u := by
      intro hv
      apply huv
      exact Finset.mem_union.mpr (Or.inr
        (Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, by simp [hv]⟩))
    apply exactNestedPowerAgreement_of_interleaved domain degree hdegree values
      hkAgreement u v Q hclose (houterGood u v hv Q hQ hclose)
    intro R hRdegree hRclose
    exact hinnerGood u hu R hRdegree hRclose

end ReedSolomon
