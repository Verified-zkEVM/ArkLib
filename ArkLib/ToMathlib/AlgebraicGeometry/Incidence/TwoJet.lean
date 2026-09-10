/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.TwoJetPoints
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.SharpCutFamily
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.SharpPrimeFamily

/-! # Sharp incidence in the capped two-jet presentation -/

@[expose] public section

noncomputable section

open MvPolynomial
open scoped BigOperators

namespace AffineHilbert

variable {F : Type*} [Field F] [IsAlgClosed F]

/-- A source plane curve whose equation and cuts have separate total- and derivative-degree
caps obeys the sharp one-dimensional incidence bound.  All cuts are linear after passage to
the capped two-jet presentation; component recognition is stated back in source coordinates. -/
theorem twoJetHypersurface_source_incidence_sharp
    {b c j r n A k : ℕ} (hb : 0 < b) (hc : 0 < c) (hcb : c ≤ b)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (g s : MvPolynomial (Fin 2) F) (hg0 : g ≠ 0)
    (hproper : Ideal.span ({g} : Set (MvPolynomial (Fin 2) F)) ≠ ⊤)
    (hg : g ∈ restrictTwoJet (F := F) j r)
    (hgbc : g ∈ restrictTwoJet (F := F) b c)
    (hsbc : s ∈ restrictTwoJet (F := F) b c)
    (highCuts : List (MvPolynomial (Fin 2) F))
    (hhigh : ∀ f ∈ highCuts, f ∈ restrictTwoJet (F := F) b c)
    (cuts : Fin n → MvPolynomial (Fin 2) F)
    (hcuts : ∀ i, cuts i ∈ restrictTwoJet (F := F) b c)
    (S : Finset (Fin 2 → F))
    (hS : ∀ x ∈ S, aeval x g = 0 ∧ aeval x s ≠ 0 ∧
      (∀ f ∈ highCuts, aeval x f = 0))
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card)
    (hunique : ∀ J : Ideal (MvPolynomial (Fin 2) F),
      J.IsPrime → s ∉ J → g ∈ J → (∀ f ∈ highCuts, f ∈ J) →
      ∀ U : Finset (Fin n), U.card = k →
      ∀ x y : Fin 2 → F,
        x ∈ zeroLocus F J → aeval x s ≠ 0 →
        y ∈ zeroLocus F J → aeval y s ≠ 0 →
        (∀ i ∈ U, aeval x (cuts i) = 0 ∧ aeval y (cuts i) = 0) → x = y) :
    (S.card : ℚ) ≤ (fixedFiberDerivativeImageDegree j r b c : ℕ) *
      (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  classical
  let J := twoJetHypersurfaceIdeal (F := F) b c g
  let gl := twoJetLift b c g hgbc
  let sl := twoJetLift b c s hsbc
  let highCuts' : List (MvPolynomial (CappedTwoJetIndex b c) F) :=
    highCuts.attach.map fun f ↦ twoJetLift b c f.1 (hhigh f.1 f.2)
  let cuts' : Fin n → MvPolynomial (CappedTwoJetIndex b c) F :=
    fun i ↦ twoJetLift b c (cuts i) (hcuts i)
  let T₀ := J.retainedMinimalPrimes sl
  let S' := S.image (twoJetPoint (F := F) b c)
  have hT₀prime : ∀ P ∈ T₀, P.IsPrime := by
    intro P hP
    exact ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hP).1.isPrime
  have hT₀open : ∀ P ∈ T₀, sl ∉ P := by
    intro P hP
    exact ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hP).2
  have hsum : ∑ P ∈ T₀, affineDegree P ≤ fixedFiberDerivativeImageDegree j r b c := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
      (twoJetHypersurface_sum_minimalPrimes_affineDegree_le_bound
        hb hc hcb hg0 hproper hg hgbc)
    · intro P hP
      exact mem_minimalPrimesFinset.mpr ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hP).1
    · intro P _ _
      exact affineDegree_nonneg P
  have hdim : ∀ P ∈ T₀, (hilbertPolynomial P).natDegree = 1 := by
    intro P hP
    have hmin := ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hP).1
    have hbase := twoJetIdeal_hilbertPolynomial_natDegree (F := F) b c hb hc
    have hsource := hilbertPolynomial_span_singleton_natDegree_add_one hg0 hproper
    have hgl : gl ∉ twoJetIdeal b c := by
      intro hmem
      change twoJetMap b c gl = 0 at hmem
      dsimp only [gl] at hmem
      rw [twoJetMap_twoJetLift] at hmem
      exact hg0 hmem
    have hp := principalCut_component_hilbertPolynomial_natDegree_add_one
      (twoJetIdeal_isPrime b c) hgl (by
        rw [← twoJetHypersurfaceIdeal_eq_sup b c g hgbc hb hc]
        exact hmin)
    have hbase' :
        (hilbertPolynomial (twoJetIdeal (F := F) b c)).natDegree = 2 := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hbase
    have hsource' : (hilbertPolynomial (Ideal.span {g})).natDegree + 1 = 2 := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hsource
    rw [hbase', ← hsource'] at hp
    omega
  have hhighDegree : ∀ f ∈ highCuts', f.totalDegree ≤ 1 := by
    intro f hf
    simp only [highCuts', List.mem_map, List.mem_attach] at hf
    obtain ⟨q, _, rfl⟩ := hf
    exact twoJetLift_totalDegree_le_one b c q.1 (hhigh q.1 q.2)
  have hcardS : S'.card = S.card := Finset.card_image_of_injective _
    (twoJetPoint_injective (F := F) b c hb hc)
  let t : ℚ := ((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)
  have ht : 1 ≤ t := by
    apply (le_div_iff₀ (by exact_mod_cast (show 0 < A - k + 1 by omega))).2
    simpa only [one_mul] using (show
      ((A - k + 1 : ℕ) : ℚ) ≤ (n - k + 1 : ℕ) by exact_mod_cast (by omega))
  have hbound := iteratedRetainedCutFamily_incidence_sharp T₀ sl
    hT₀prime hT₀open hdim ht hsum
    highCuts' hhighDegree S' ?_ ?_
  · rw [hcardS] at hbound
    simpa only [pow_one, t] using hbound
  · intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hxJ := (mem_zeroLocus_twoJetHypersurfaceIdeal_iff b c hb hc g x).2 (hS x hx).1
    have hxsl : aeval (twoJetPoint (F := F) b c x) sl ≠ 0 :=
      (not_congr (aeval_twoJetLift_iff b c x s hsbc)).mpr (hS x hx).2.1
    apply exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus T₀ highCuts'
      (twoJetPoint (F := F) b c x)
    · obtain ⟨P, hP, hxP⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus J sl
        (twoJetPoint (F := F) b c x) hxJ hxsl
      exact ⟨P, hP, hxP⟩
    · exact hxsl
    · intro f hf
      simp only [highCuts', List.mem_map, List.mem_attach] at hf
      obtain ⟨q, _, rfl⟩ := hf
      exact (aeval_twoJetLift_iff b c x q.1 (hhigh q.1 q.2)).2
        ((hS x hx).2.2 q.1 q.2)
  · intro P hP
    obtain ⟨P₀, hP₀, hP₀P, hhighP⟩ :=
      mem_iteratedRetainedCutFamily_contains T₀ highCuts' hP
    have hprimeOpen := iteratedRetainedCutFamily_prime_open T₀ hT₀prime hT₀open
      highCuts' P hP
    have hP₀J : J ≤ P₀ := ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hP₀).1.le
    have hbaseP : twoJetIdeal b c ≤ P := by
      apply le_trans _ (hP₀J.trans hP₀P)
      dsimp only [J]
      rw [twoJetHypersurfaceIdeal_eq_sup b c g hgbc hb hc]
      exact le_sup_left
    let Q : Ideal (MvPolynomial (Fin 2) F) := P.map (twoJetMap b c).toRingHom
    let _ : P.IsPrime := hprimeOpen.1
    have hQprime : Q.IsPrime := Ideal.map_isPrime_of_surjective
      (f := (twoJetMap b c).toRingHom) (twoJetMap_surjective b c hb hc) hbaseP
    have hcomap : Q.comap (twoJetMap b c).toRingHom = P := by
      change (P.map (twoJetMap b c).toRingHom).comap (twoJetMap b c).toRingHom = P
      rw [Ideal.comap_map_of_surjective (twoJetMap b c).toRingHom
        (twoJetMap_surjective b c hb hc) P]
      apply sup_eq_left.mpr
      rw [← RingHom.ker_eq_comap_bot]
      exact hbaseP
    have hsQ : s ∉ Q := by
      intro hsQ
      have hsl : sl ∈ Q.comap (twoJetMap b c).toRingHom := by
        change twoJetMap b c sl ∈ Q
        dsimp only [sl]
        rwa [twoJetMap_twoJetLift]
      rw [hcomap] at hsl
      exact hprimeOpen.2 hsl
    have hgQ : g ∈ Q := by
      rw [← twoJetMap_twoJetLift b c g hgbc]
      apply Ideal.mem_map_of_mem (twoJetMap b c).toRingHom
      apply hP₀P
      apply hP₀J
      dsimp only [J, gl]
      rw [twoJetHypersurfaceIdeal_eq_sup b c g hgbc hb hc]
      exact (le_sup_right : Ideal.span {twoJetLift b c g hgbc} ≤
        twoJetIdeal b c ⊔ Ideal.span {twoJetLift b c g hgbc})
          (Ideal.subset_span (Set.mem_singleton _))
    have hhighQ : ∀ f ∈ highCuts, f ∈ Q := by
      intro f hf
      rw [← twoJetMap_twoJetLift b c f (hhigh f hf)]
      apply Ideal.mem_map_of_mem (twoJetMap b c).toRingHom
      apply hhighP
      simp only [highCuts', List.mem_map, List.mem_attach]
      exact ⟨⟨f, hf⟩, trivial, rfl⟩
    have hinc : (componentPoints S' P).card ≤ affineDegree P *
        (((((n - k + 1) * 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) ^
          (hilbertPolynomial P).natDegree) := by
      apply affineAgreementIncidence_bound_sharp hprimeOpen.1 hprimeOpen.2 cuts'
        (fun i ↦ twoJetLift_totalDegree_le_one b c _ (hcuts i)) (by omega) hk hkA hAn
      · intro z hz
        rw [mem_componentPoints] at hz
        exact ⟨hz.2, by
          rw [Finset.mem_image] at hz
          obtain ⟨x, hx, rfl⟩ := hz.1
          exact (not_congr (aeval_twoJetLift_iff b c x s hsbc)).mpr (hS x hx).2.1⟩
      · intro z hz
        rw [mem_componentPoints] at hz
        rw [Finset.mem_image] at hz
        obtain ⟨x, hx, rfl⟩ := hz.1
        have heq : agreementIndices cuts' (twoJetPoint (F := F) b c x) =
            agreementIndices cuts x := by
          ext i
          rw [mem_agreementIndices, mem_agreementIndices]
          exact aeval_twoJetLift_iff b c x (cuts i) (hcuts i)
        rw [heq]
        exact hA x hx
      · intro U hU z z' hzP hzs hz'P hz's hzero
        have hzbase : z ∈ zeroLocus F (twoJetIdeal (F := F) b c) :=
          zeroLocus_anti_mono hbaseP hzP
        have hz'base : z' ∈ zeroLocus F (twoJetIdeal (F := F) b c) :=
          zeroLocus_anti_mono hbaseP hz'P
        obtain ⟨x, rfl⟩ := exists_twoJetPoint_of_mem_zeroLocus_twoJetIdeal b c hb hc z hzbase
        obtain ⟨y, rfl⟩ := exists_twoJetPoint_of_mem_zeroLocus_twoJetIdeal b c hb hc z' hz'base
        apply congrArg (twoJetPoint (F := F) b c)
        apply hunique Q hQprime hsQ hgQ hhighQ U hU x y
        · intro f hf
          obtain ⟨q, hq, rfl⟩ :=
            (Ideal.mem_map_iff_of_surjective (twoJetMap b c).toRingHom
              (twoJetMap_surjective b c hb hc)).mp hf
          have hzq := hzP q hq
          rw [aeval_twoJetPoint] at hzq
          change aeval x (twoJetMap b c q) = 0
          exact hzq
        · exact (not_congr (aeval_twoJetLift_iff b c x s hsbc)).mp hzs
        · intro f hf
          obtain ⟨q, hq, rfl⟩ :=
            (Ideal.mem_map_iff_of_surjective (twoJetMap b c).toRingHom
              (twoJetMap_surjective b c hb hc)).mp hf
          have hzq := hz'P q hq
          rw [aeval_twoJetPoint] at hzq
          change aeval y (twoJetMap b c q) = 0
          exact hzq
        · exact (not_congr (aeval_twoJetLift_iff b c y s hsbc)).mp hz's
        · intro i hi
          exact ⟨(aeval_twoJetLift_iff b c x (cuts i) (hcuts i)).mp (hzero i hi).1,
            (aeval_twoJetLift_iff b c y (cuts i) (hcuts i)).mp (hzero i hi).2⟩
    simpa only [Nat.mul_one, t] using hinc

end AffineHilbert
