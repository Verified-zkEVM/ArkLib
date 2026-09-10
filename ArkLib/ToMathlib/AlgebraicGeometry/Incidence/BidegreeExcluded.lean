/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.BidegreePoints
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.SharpCutFamily
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.DimensionSensitive

/-!
# Sharp excluded incidence through the bidegree presentation

Source hypersurfaces and all fixed and agreement equations are lifted to linear equations in
the affine bidegree presentation. Terminal positive-dimensional components are recognized
after mapping their presentation primes back to source-coordinate primes. Thus the statement
uses the actual source equations and does not require global point uniqueness.
-/

@[expose] public section

noncomputable section

open MvPolynomial
open scoped BigOperators

namespace AffineHilbert

variable {F σ : Type*} [Field F] [Finite σ]

/-- Transport sharp off-excluded incidence from the bidegree presentation back to source
points. Both the fixed high cuts and the agreement cuts are genuine source equations. -/
theorem bidegreeHypersurface_source_incidence_off_excluded_sharp
    {a b n A L : ℕ} (ha : 0 < a) (hb : 0 < b) (hLA : L ≤ A) (hAn : A ≤ n)
    (g s : MvPolynomial (Option σ) F) (hg0 : g ≠ 0)
    (hproper : Ideal.span ({g} : Set (MvPolynomial (Option σ) F)) ≠ ⊤)
    (hg : g ∈ restrictBidegree (F := F) (σ := σ) a b)
    (hs : s ∈ restrictBidegree (F := F) (σ := σ) a b)
    (highCuts : List (MvPolynomial (Option σ) F))
    (hhigh : ∀ f ∈ highCuts, f ∈ restrictBidegree (F := F) (σ := σ) a b)
    (cuts : Fin n → MvPolynomial (Option σ) F)
    (hcuts : ∀ i, cuts i ∈ restrictBidegree (F := F) (σ := σ) a b)
    (excluded : Set (Option σ → F))
    (hterminal : ∀ J : Ideal (MvPolynomial (Option σ) F),
      J.IsPrime → s ∉ J → g ∈ J → (∀ f ∈ highCuts, f ∈ J) →
      0 < (hilbertPolynomial J).natDegree →
      L ≤ (cutsInIdeal J cuts).card → principalOpenZeroLocus J s ⊆ excluded)
    (S : Finset (Option σ → F))
    (hS : ∀ x ∈ S, aeval x g = 0 ∧ aeval x s ≠ 0 ∧
      (∀ f ∈ highCuts, aeval x f = 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card) :
    (S.card : ℚ) ≤ affineDegree (bidegreeHypersurfaceIdeal a b g) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^
        (hilbertPolynomial (Ideal.span {g})).natDegree := by
  classical
  let J := bidegreeHypersurfaceIdeal (F := F) a b g
  let gl := bidegreeLift a b g hg
  let sl := bidegreeLift a b s hs
  let highCuts' : List (MvPolynomial (BidegreeIndex a b σ) F) :=
    highCuts.attach.map fun f ↦ bidegreeLift a b f.1 (hhigh f.1 f.2)
  let cuts' : Fin n → MvPolynomial (BidegreeIndex a b σ) F :=
    fun i ↦ bidegreeLift a b (cuts i) (hcuts i)
  let T₀ := J.retainedMinimalPrimes sl
  let S' := S.image (bidegreePoint (F := F) a b)
  let excluded' : Set (BidegreeIndex a b σ → F) :=
    bidegreePoint (F := F) a b '' excluded
  let d := (hilbertPolynomial (Ideal.span {g})).natDegree
  have hT₀prime : ∀ P ∈ T₀, P.IsPrime := by
    intro P hP
    exact ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hP).1.isPrime
  have hT₀open : ∀ P ∈ T₀, sl ∉ P := by
    intro P hP
    exact ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hP).2
  have hsum : ∑ P ∈ T₀, affineDegree P ≤ affineDegree J := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
      (bidegreeHypersurface_sum_minimalPrimes_affineDegree_le ha hb hg0 hproper hg)
    · intro P hP
      exact mem_minimalPrimesFinset.mpr ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hP).1
    · intro P _ _
      exact affineDegree_nonneg P
  have hdim : ∀ P ∈ T₀, (hilbertPolynomial P).natDegree = d := by
    intro P hP
    have hmin := ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hP).1
    have hbase := bidegreeIdeal_hilbertPolynomial_natDegree (F := F) (σ := σ) a b ha hb
    have hsource := hilbertPolynomial_span_singleton_natDegree_add_one hg0 hproper
    have hgl : gl ∉ bidegreeIdeal a b := by
      intro h
      change bidegreeMap a b gl = 0 at h
      dsimp only [gl] at h
      rw [bidegreeMap_bidegreeLift] at h
      exact hg0 h
    have hp := principalCut_component_hilbertPolynomial_natDegree_add_one
      (bidegreeIdeal_isPrime a b) hgl (by
        rw [← bidegreeHypersurfaceIdeal_eq_sup a b g hg ha hb]
        exact hmin)
    dsimp only [d]
    rw [hbase, ← hsource] at hp
    omega
  have hhighDegree : ∀ f ∈ highCuts', f.totalDegree ≤ 1 := by
    intro f hf
    simp only [highCuts', List.mem_map, List.mem_attach] at hf
    obtain ⟨q, _, rfl⟩ := hf
    exact bidegreeLift_totalDegree_le_one a b q.1 (hhigh q.1 q.2)
  have hcardS : S'.card = S.card := Finset.card_image_of_injective _
    (bidegreePoint_injective (F := F) a b ha hb)
  have hbound := iteratedRetainedCutFamily_incidence_off_excluded_sharp T₀ sl
    hT₀prime hT₀open hdim hsum highCuts' hhighDegree cuts'
    (fun i ↦ bidegreeLift_totalDegree_le_one a b _ (hcuts i))
    (show 0 < (1 : ℕ) by omega) hLA hAn excluded' ?_ S' ?_ ?_
  · rw [hcardS] at hbound
    simpa only [Nat.mul_one] using hbound
  · intro P hPT₀ Q hPQ hQ hsQ hhighQ hdQ hcutsQ
    have hPJ : J ≤ P := ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hPT₀).1.le
    have hbaseQ : bidegreeIdeal a b ≤ Q := by
      apply le_trans _ (hPJ.trans hPQ)
      dsimp only [J]
      rw [bidegreeHypersurfaceIdeal_eq_sup a b g hg ha hb]
      exact le_sup_left
    let K : Ideal (MvPolynomial (Option σ) F) := Q.map (bidegreeMap a b).toRingHom
    have hK : K.IsPrime := Ideal.map_isPrime_of_surjective
      (f := (bidegreeMap a b).toRingHom) (bidegreeMap_surjective a b ha hb) hbaseQ
    have hcomap : K.comap (bidegreeMap a b).toRingHom = Q := by
      change (Q.map (bidegreeMap a b).toRingHom).comap (bidegreeMap a b).toRingHom = Q
      rw [Ideal.comap_map_of_surjective (bidegreeMap a b).toRingHom
        (bidegreeMap_surjective a b ha hb) Q]
      apply sup_eq_left.mpr
      rw [← RingHom.ker_eq_comap_bot]
      exact hbaseQ
    have hsK : s ∉ K := by
      intro hsK
      have hsl : sl ∈ K.comap (bidegreeMap a b).toRingHom := by
        change bidegreeMap a b sl ∈ K
        dsimp only [sl]
        rwa [bidegreeMap_bidegreeLift]
      rw [hcomap] at hsl
      exact hsQ hsl
    have hgK : g ∈ K := by
      rw [← bidegreeMap_bidegreeLift a b g hg]
      apply Ideal.mem_map_of_mem (bidegreeMap a b).toRingHom
      apply hPQ
      apply hPJ
      dsimp only [J, gl]
      rw [bidegreeHypersurfaceIdeal_eq_sup a b g hg ha hb]
      exact (le_sup_right :
        Ideal.span {bidegreeLift a b g hg} ≤
          bidegreeIdeal a b ⊔ Ideal.span {bidegreeLift a b g hg})
        (Ideal.subset_span (Set.mem_singleton _))
    have hhighK : ∀ f ∈ highCuts, f ∈ K := by
      intro f hf
      rw [← bidegreeMap_bidegreeLift a b f (hhigh f hf)]
      apply Ideal.mem_map_of_mem (bidegreeMap a b).toRingHom
      apply hhighQ
      simp only [highCuts', List.mem_map, List.mem_attach]
      exact ⟨⟨f, hf⟩, trivial, rfl⟩
    have hdK : 0 < (hilbertPolynomial K).natDegree := by
      have hQK : Q ≤ K.comap (bidegreeMap a b).toRingHom := by
        intro q hq
        exact Ideal.mem_map_of_mem (bidegreeMap a b).toRingHom hq
      let qmap :
          (MvPolynomial (BidegreeIndex a b σ) F ⧸ Q) →ₐ[F]
            (MvPolynomial (Option σ) F ⧸ K) :=
        Ideal.quotientMapₐ K (bidegreeMap a b) hQK
      have hqinj : Function.Injective qmap := by
        intro x y hxy
        rw [← sub_eq_zero]
        have hz : qmap (x - y) = 0 := by rw [map_sub, hxy, sub_self]
        obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (I := Q) (x - y)
        rw [← hp] at hz ⊢
        change Ideal.Quotient.mk K (bidegreeMap a b p) = 0 at hz
        rw [Ideal.Quotient.eq_zero_iff_mem] at hz ⊢
        have hpQ : p ∈ K.comap (bidegreeMap a b).toRingHom := hz
        rwa [hcomap] at hpQ
      have hqsurj : Function.Surjective qmap := by
        intro y
        obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (I := K) y
        obtain ⟨q, hq⟩ := bidegreeMap_surjective (F := F) a b ha hb p
        refine ⟨Ideal.Quotient.mk Q q, ?_⟩
        rw [← hp, ← hq]
        exact Ideal.quotientMap_mk (H := hQK)
      let e :
          (MvPolynomial (BidegreeIndex a b σ) F ⧸ Q) ≃ₐ[F]
            (MvPolynomial (Option σ) F ⧸ K) :=
        AlgEquiv.ofBijective qmap ⟨hqinj, hqsurj⟩
      have hdeg :
          (hilbertPolynomial Q).natDegree = (hilbertPolynomial K).natDegree := by
        apply hilbertPolynomial_natDegree_eq_of_finite_injective_algHom
          e.symm.toAlgHom e.symm.injective hQ.ne_top
        let _ : Algebra (MvPolynomial (Option σ) F ⧸ K)
            (MvPolynomial (BidegreeIndex a b σ) F ⧸ Q) :=
          e.symm.toRingHom.toAlgebra
        exact Module.Finite.of_surjective (Algebra.linearMap _ _) e.symm.surjective
      rw [← hdeg]
      exact hdQ
    have hcutsEq : cutsInIdeal K cuts = cutsInIdeal Q cuts' := by
      ext i
      simp only [mem_cutsInIdeal]
      constructor
      · intro hi
        have hil : cuts' i ∈ K.comap (bidegreeMap a b).toRingHom := by
          change bidegreeMap a b (cuts' i) ∈ K
          dsimp only [cuts']
          rwa [bidegreeMap_bidegreeLift]
        rwa [hcomap] at hil
      · intro hi
        rw [← bidegreeMap_bidegreeLift a b (cuts i) (hcuts i)]
        exact Ideal.mem_map_of_mem (bidegreeMap a b).toRingHom hi
    have hsource := hterminal K hK hsK hgK hhighK hdK (by rwa [hcutsEq])
    intro z hz
    have hzbase : z ∈ zeroLocus F (bidegreeIdeal (F := F) (σ := σ) a b) :=
      zeroLocus_anti_mono hbaseQ hz.1
    obtain ⟨x, rfl⟩ := exists_bidegreePoint_of_mem_zeroLocus_bidegreeIdeal
      a b ha hb z hzbase
    have hxK : x ∈ zeroLocus F K := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective (bidegreeMap a b).toRingHom
          (bidegreeMap_surjective a b ha hb)).mp hp
      change aeval x (bidegreeMap a b q) = 0
      rw [← aeval_bidegreePoint]
      exact hz.1 q hq
    have hxs : aeval x s ≠ 0 := by
      rw [← bidegreeMap_bidegreeLift a b s hs, ← aeval_bidegreePoint]
      exact hz.2
    exact ⟨x, hsource ⟨hxK, hxs⟩, rfl⟩
  · intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hxJ := (mem_zeroLocus_bidegreeHypersurfaceIdeal_iff a b ha hb g x).2
      (hS x hx).1
    have hxsl : aeval (bidegreePoint (F := F) a b x) sl ≠ 0 := by
      exact (not_congr (aeval_bidegreeLift_iff a b x s hs)).mpr (hS x hx).2.1
    refine ⟨?_, hxsl, ?_, ?_⟩
    · obtain ⟨P, hP, hxP⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus J sl
        (bidegreePoint (F := F) a b x) hxJ hxsl
      exact ⟨P, hP, hxP⟩
    · intro f hf
      simp only [highCuts', List.mem_map, List.mem_attach] at hf
      obtain ⟨q, _, rfl⟩ := hf
      exact (aeval_bidegreeLift_iff a b x q.1 (hhigh q.1 q.2)).2
        ((hS x hx).2.2.1 q.1 q.2)
    · rintro ⟨y, hy, hxy⟩
      have heq := bidegreePoint_injective (F := F) a b ha hb hxy
      exact (hS x hx).2.2.2 (heq ▸ hy)
  · intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have heq : agreementIndices cuts' (bidegreePoint (F := F) a b x) =
        agreementIndices cuts x := by
      ext i
      rw [mem_agreementIndices, mem_agreementIndices]
      exact aeval_bidegreeLift_iff a b x (cuts i) (hcuts i)
    rw [heq]
    exact hA x hx

/-- Arbitrary-dimensional bidegree incidence with the terminal graph threshold at dimension one
and the hereditary coefficient-space product in every higher dimension. Presentation primes are
mapped back to genuine source-coordinate primes before either premise is applied. -/
theorem bidegreeHypersurface_source_incidence_off_excluded_hybrid
    {a b n A L k : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hLA : L ≤ A) (hkA : k ≤ A) (hAn : A ≤ n)
    (g s : MvPolynomial (Option σ) F) (hg0 : g ≠ 0)
    (hproper : Ideal.span ({g} : Set (MvPolynomial (Option σ) F)) ≠ ⊤)
    (hgAB : g ∈ restrictBidegree (F := F) (σ := σ) a b)
    (hs : s ∈ restrictBidegree (F := F) (σ := σ) a b)
    (highCuts : List (MvPolynomial (Option σ) F))
    (hhigh : ∀ f ∈ highCuts, f ∈ restrictBidegree (F := F) (σ := σ) a b)
    (cuts : Fin n → MvPolynomial (Option σ) F)
    (hcuts : ∀ i, cuts i ∈ restrictBidegree (F := F) (σ := σ) a b)
    (excluded : Set (Option σ → F))
    (hdimension : ∀ J : Ideal (MvPolynomial (Option σ) F),
      J.IsPrime → s ∉ J → g ∈ J → (∀ f ∈ highCuts, f ∈ J) →
      0 < (hilbertPolynomial J).natDegree →
      (hilbertPolynomial J).natDegree ≤ k + 1 ∧
        (1 < (hilbertPolynomial J).natDegree →
          (cutsInIdeal J cuts).card ≤ k + 1 - (hilbertPolynomial J).natDegree))
    (hterminal : ∀ J : Ideal (MvPolynomial (Option σ) F),
      J.IsPrime → s ∉ J → g ∈ J → (∀ f ∈ highCuts, f ∈ J) →
      0 < (hilbertPolynomial J).natDegree →
      L ≤ (cutsInIdeal J cuts).card → principalOpenZeroLocus J s ⊆ excluded)
    (S : Finset (Option σ → F))
    (hS : ∀ x ∈ S, aeval x g = 0 ∧ aeval x s ≠ 0 ∧
      (∀ f ∈ highCuts, aeval x f = 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card) :
    (S.card : ℚ) ≤ affineDegree (bidegreeHypersurfaceIdeal a b g) *
      hybridDimensionSensitiveIncidenceProduct n A L k 1
        (min ((hilbertPolynomial (Ideal.span {g})).natDegree - 1) k + 1) := by
  classical
  let J := bidegreeHypersurfaceIdeal (F := F) a b g
  let gl := bidegreeLift a b g hgAB
  let sl := bidegreeLift a b s hs
  let highCuts' : List (MvPolynomial (BidegreeIndex a b σ) F) :=
    highCuts.attach.map fun f ↦ bidegreeLift a b f.1 (hhigh f.1 f.2)
  let cuts' : Fin n → MvPolynomial (BidegreeIndex a b σ) F :=
    fun i ↦ bidegreeLift a b (cuts i) (hcuts i)
  let T₀ := J.retainedMinimalPrimes sl
  let S' := S.image (bidegreePoint (F := F) a b)
  let excluded' : Set (BidegreeIndex a b σ → F) :=
    bidegreePoint (F := F) a b '' excluded
  let d := (hilbertPolynomial (Ideal.span {g})).natDegree
  have hT₀prime : ∀ P ∈ T₀, P.IsPrime := by
    intro P hP
    exact ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hP).1.isPrime
  have hT₀open : ∀ P ∈ T₀, sl ∉ P := by
    intro P hP
    exact ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hP).2
  have hsum : ∑ P ∈ T₀, affineDegree P ≤ affineDegree J := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
      (bidegreeHypersurface_sum_minimalPrimes_affineDegree_le ha hb hg0 hproper hgAB)
    · intro P hP
      exact mem_minimalPrimesFinset.mpr ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hP).1
    · intro P _ _
      exact affineDegree_nonneg P
  have hdim : ∀ P ∈ T₀, (hilbertPolynomial P).natDegree = d := by
    intro P hP
    have hmin := ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hP).1
    have hbase := bidegreeIdeal_hilbertPolynomial_natDegree
      (F := F) (σ := σ) a b ha hb
    have hsource := hilbertPolynomial_span_singleton_natDegree_add_one hg0 hproper
    have hgl : gl ∉ bidegreeIdeal a b := by
      intro hmem
      change bidegreeMap a b gl = 0 at hmem
      dsimp only [gl] at hmem
      rw [bidegreeMap_bidegreeLift] at hmem
      exact hg0 hmem
    have hp := principalCut_component_hilbertPolynomial_natDegree_add_one
      (bidegreeIdeal_isPrime a b) hgl (by
        rw [← bidegreeHypersurfaceIdeal_eq_sup a b g hgAB ha hb]
        exact hmin)
    dsimp only [d]
    rw [hbase, ← hsource] at hp
    omega
  have hhighDegree : ∀ f ∈ highCuts', f.totalDegree ≤ 1 := by
    intro f hf
    simp only [highCuts', List.mem_map, List.mem_attach] at hf
    obtain ⟨q, _, rfl⟩ := hf
    exact bidegreeLift_totalDegree_le_one a b q.1 (hhigh q.1 q.2)
  have hsourceData (P : Ideal (MvPolynomial (BidegreeIndex a b σ) F))
      (hPT₀ : P ∈ T₀) (Q : Ideal (MvPolynomial (BidegreeIndex a b σ) F))
      (hPQ : P ≤ Q) (hQ : Q.IsPrime) (hsQ : sl ∉ Q)
      (hhighQ : ∀ f ∈ highCuts', f ∈ Q) :
      let K : Ideal (MvPolynomial (Option σ) F) :=
        Q.map (bidegreeMap a b).toRingHom
      K.IsPrime ∧ s ∉ K ∧ g ∈ K ∧ (∀ f ∈ highCuts, f ∈ K) ∧
        (hilbertPolynomial K).natDegree = (hilbertPolynomial Q).natDegree ∧
        cutsInIdeal K cuts = cutsInIdeal Q cuts' := by
    dsimp only
    have hPJ : J ≤ P := ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hPT₀).1.le
    have hbaseQ : bidegreeIdeal a b ≤ Q := by
      apply le_trans _ (hPJ.trans hPQ)
      dsimp only [J]
      rw [bidegreeHypersurfaceIdeal_eq_sup a b g hgAB ha hb]
      exact le_sup_left
    let K : Ideal (MvPolynomial (Option σ) F) :=
      Q.map (bidegreeMap a b).toRingHom
    have hK : K.IsPrime := Ideal.map_isPrime_of_surjective
      (f := (bidegreeMap a b).toRingHom) (bidegreeMap_surjective a b ha hb) hbaseQ
    have hcomap : K.comap (bidegreeMap a b).toRingHom = Q := by
      change (Q.map (bidegreeMap a b).toRingHom).comap (bidegreeMap a b).toRingHom = Q
      rw [Ideal.comap_map_of_surjective (bidegreeMap a b).toRingHom
        (bidegreeMap_surjective a b ha hb) Q]
      apply sup_eq_left.mpr
      rw [← RingHom.ker_eq_comap_bot]
      exact hbaseQ
    have hsK : s ∉ K := by
      intro hsK
      have hsl : sl ∈ K.comap (bidegreeMap a b).toRingHom := by
        change bidegreeMap a b sl ∈ K
        dsimp only [sl]
        rwa [bidegreeMap_bidegreeLift]
      rw [hcomap] at hsl
      exact hsQ hsl
    have hgK : g ∈ K := by
      rw [← bidegreeMap_bidegreeLift a b g hgAB]
      apply Ideal.mem_map_of_mem (bidegreeMap a b).toRingHom
      apply hPQ
      apply hPJ
      dsimp only [J, gl]
      rw [bidegreeHypersurfaceIdeal_eq_sup a b g hgAB ha hb]
      exact (le_sup_right : Ideal.span {bidegreeLift a b g hgAB} ≤
        bidegreeIdeal a b ⊔ Ideal.span {bidegreeLift a b g hgAB})
          (Ideal.subset_span (Set.mem_singleton _))
    have hhighK : ∀ f ∈ highCuts, f ∈ K := by
      intro f hf
      rw [← bidegreeMap_bidegreeLift a b f (hhigh f hf)]
      apply Ideal.mem_map_of_mem (bidegreeMap a b).toRingHom
      apply hhighQ
      simp only [highCuts', List.mem_map, List.mem_attach]
      exact ⟨⟨f, hf⟩, trivial, rfl⟩
    have hdeg : (hilbertPolynomial K).natDegree = (hilbertPolynomial Q).natDegree := by
      have hQK : Q ≤ K.comap (bidegreeMap a b).toRingHom := by
        intro q hq
        exact Ideal.mem_map_of_mem (bidegreeMap a b).toRingHom hq
      let qmap :
          (MvPolynomial (BidegreeIndex a b σ) F ⧸ Q) →ₐ[F]
            (MvPolynomial (Option σ) F ⧸ K) :=
        Ideal.quotientMapₐ K (bidegreeMap a b) hQK
      have hqinj : Function.Injective qmap := by
        intro x y hxy
        rw [← sub_eq_zero]
        have hz : qmap (x - y) = 0 := by rw [map_sub, hxy, sub_self]
        obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (I := Q) (x - y)
        rw [← hp] at hz ⊢
        change Ideal.Quotient.mk K (bidegreeMap a b p) = 0 at hz
        rw [Ideal.Quotient.eq_zero_iff_mem] at hz ⊢
        have hpQ : p ∈ K.comap (bidegreeMap a b).toRingHom := hz
        rwa [hcomap] at hpQ
      have hqsurj : Function.Surjective qmap := by
        intro y
        obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (I := K) y
        obtain ⟨q, hq⟩ := bidegreeMap_surjective (F := F) a b ha hb p
        refine ⟨Ideal.Quotient.mk Q q, ?_⟩
        rw [← hp, ← hq]
        exact Ideal.quotientMap_mk (H := hQK)
      let e :
          (MvPolynomial (BidegreeIndex a b σ) F ⧸ Q) ≃ₐ[F]
            (MvPolynomial (Option σ) F ⧸ K) :=
        AlgEquiv.ofBijective qmap ⟨hqinj, hqsurj⟩
      symm
      apply hilbertPolynomial_natDegree_eq_of_finite_injective_algHom
        e.symm.toAlgHom e.symm.injective hQ.ne_top
      let _ : Algebra (MvPolynomial (Option σ) F ⧸ K)
          (MvPolynomial (BidegreeIndex a b σ) F ⧸ Q) :=
        e.symm.toRingHom.toAlgebra
      exact Module.Finite.of_surjective (Algebra.linearMap _ _) e.symm.surjective
    have hcutsEq : cutsInIdeal K cuts = cutsInIdeal Q cuts' := by
      ext i
      simp only [mem_cutsInIdeal]
      constructor
      · intro hi
        have hil : cuts' i ∈ K.comap (bidegreeMap a b).toRingHom := by
          change bidegreeMap a b (cuts' i) ∈ K
          dsimp only [cuts']
          rwa [bidegreeMap_bidegreeLift]
        rwa [hcomap] at hil
      · intro hi
        rw [← bidegreeMap_bidegreeLift a b (cuts i) (hcuts i)]
        exact Ideal.mem_map_of_mem (bidegreeMap a b).toRingHom hi
    exact ⟨hK, hsK, hgK, hhighK, hdeg, hcutsEq⟩
  have hcardS : S'.card = S.card := Finset.card_image_of_injective _
    (bidegreePoint_injective (F := F) a b ha hb)
  have hbound := iteratedRetainedCutFamily_incidence_off_excluded_hybrid T₀ sl
    hT₀prime hT₀open hdim hsum highCuts' hhighDegree (show 0 < 1 by omega)
    cuts' (fun i ↦ bidegreeLift_totalDegree_le_one a b _ (hcuts i))
    hLA hkA hAn excluded' ?_ ?_ S' ?_ ?_
  · rw [hcardS] at hbound
    simpa only [Nat.cast_one, one_pow, mul_one, J, d] using hbound
  · intro P hPT₀ Q hPQ hQ hsQ hhighQ hdQ
    obtain ⟨hK, hsK, hgK, hhighK, hdeg, hcutsEq⟩ :=
      hsourceData P hPT₀ Q hPQ hQ hsQ hhighQ
    have hdK : 0 < (hilbertPolynomial
        (Q.map (bidegreeMap a b).toRingHom)).natDegree := by rwa [hdeg]
    have hsource := hdimension _ hK hsK hgK hhighK hdK
    rwa [hdeg, hcutsEq] at hsource
  · intro P hPT₀ Q hPQ hQ hsQ hhighQ hdQ hcutsQ
    obtain ⟨hK, hsK, hgK, hhighK, hdeg, hcutsEq⟩ :=
      hsourceData P hPT₀ Q hPQ hQ hsQ hhighQ
    have hdK : 0 < (hilbertPolynomial
        (Q.map (bidegreeMap a b).toRingHom)).natDegree := by rwa [hdeg]
    have hsource := hterminal _ hK hsK hgK hhighK hdK (by rwa [hcutsEq])
    intro z hz
    have hPJ : J ≤ P := ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hPT₀).1.le
    have hbaseQ : bidegreeIdeal a b ≤ Q := by
      apply le_trans _ (hPJ.trans hPQ)
      dsimp only [J]
      rw [bidegreeHypersurfaceIdeal_eq_sup a b g hgAB ha hb]
      exact le_sup_left
    have hzbase : z ∈ zeroLocus F (bidegreeIdeal (F := F) (σ := σ) a b) :=
      zeroLocus_anti_mono hbaseQ hz.1
    obtain ⟨x, rfl⟩ := exists_bidegreePoint_of_mem_zeroLocus_bidegreeIdeal
      a b ha hb z hzbase
    have hxK : x ∈ zeroLocus F (Q.map (bidegreeMap a b).toRingHom) := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective (bidegreeMap a b).toRingHom
          (bidegreeMap_surjective a b ha hb)).mp hp
      change aeval x (bidegreeMap a b q) = 0
      rw [← aeval_bidegreePoint]
      exact hz.1 q hq
    have hxs : aeval x s ≠ 0 := by
      rw [← bidegreeMap_bidegreeLift a b s hs, ← aeval_bidegreePoint]
      exact hz.2
    exact ⟨x, hsource ⟨hxK, hxs⟩, rfl⟩
  · intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hxJ := (mem_zeroLocus_bidegreeHypersurfaceIdeal_iff a b ha hb g x).2
      (hS x hx).1
    have hxsl : aeval (bidegreePoint (F := F) a b x) sl ≠ 0 :=
      (not_congr (aeval_bidegreeLift_iff a b x s hs)).mpr (hS x hx).2.1
    refine ⟨?_, hxsl, ?_, ?_⟩
    · obtain ⟨P, hP, hxP⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus J sl
        (bidegreePoint (F := F) a b x) hxJ hxsl
      exact ⟨P, hP, hxP⟩
    · intro f hf
      simp only [highCuts', List.mem_map, List.mem_attach] at hf
      obtain ⟨q, _, rfl⟩ := hf
      exact (aeval_bidegreeLift_iff a b x q.1 (hhigh q.1 q.2)).2
        ((hS x hx).2.2.1 q.1 q.2)
    · rintro ⟨y, hy, hxy⟩
      have heq := bidegreePoint_injective (F := F) a b ha hb hxy
      exact (hS x hx).2.2.2 (heq ▸ hy)
  · intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have heq : agreementIndices cuts' (bidegreePoint (F := F) a b x) =
        agreementIndices cuts x := by
      ext i
      rw [mem_agreementIndices, mem_agreementIndices]
      exact aeval_bidegreeLift_iff a b x (cuts i) (hcuts i)
    rw [heq]
    exact hA x hx

/-- Two-dimensional bidegree incidence with a dimension-sensitive joint recurrence.

The bidegree presentation makes both the fixed high cuts and the agreement cuts linear.  The
former are charged once through the retained-family degree potential.  The latter use the hybrid
threshold: dimension one is controlled by the terminal excluded locus at `L`, while dimension
two uses the source coefficient-space budget at `k`.  Presentation primes are mapped back to
the genuine source-coordinate primes before either hereditary premise is applied. -/
theorem bidegreeHypersurface_source_incidence_off_excluded_hybrid_two
    {a b h v n A L k : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hLA : L ≤ A) (hkA : k ≤ A) (hAn : A ≤ n)
    (g s : MvPolynomial (Option (Fin 2)) F) (hg0 : g ≠ 0)
    (hproper : Ideal.span ({g} : Set (MvPolynomial (Option (Fin 2)) F)) ≠ ⊤)
    (hg : g ∈ restrictBidegree (F := F) (σ := Fin 2) h v)
    (hgAB : g ∈ restrictBidegree (F := F) (σ := Fin 2) a b)
    (hs : s ∈ restrictBidegree (F := F) (σ := Fin 2) a b)
    (highCuts : List (MvPolynomial (Option (Fin 2)) F))
    (hhigh : ∀ f ∈ highCuts, f ∈ restrictBidegree (F := F) (σ := Fin 2) a b)
    (cuts : Fin n → MvPolynomial (Option (Fin 2)) F)
    (hcuts : ∀ i, cuts i ∈ restrictBidegree (F := F) (σ := Fin 2) a b)
    (excluded : Set (Option (Fin 2) → F))
    (hdimension : ∀ J : Ideal (MvPolynomial (Option (Fin 2)) F),
      J.IsPrime → s ∉ J → g ∈ J → (∀ f ∈ highCuts, f ∈ J) →
      0 < (hilbertPolynomial J).natDegree →
      (hilbertPolynomial J).natDegree ≤ k + 1 ∧
        (1 < (hilbertPolynomial J).natDegree →
          (cutsInIdeal J cuts).card ≤ k + 1 - (hilbertPolynomial J).natDegree))
    (hterminal : ∀ J : Ideal (MvPolynomial (Option (Fin 2)) F),
      J.IsPrime → s ∉ J → g ∈ J → (∀ f ∈ highCuts, f ∈ J) →
      0 < (hilbertPolynomial J).natDegree →
      L ≤ (cutsInIdeal J cuts).card → principalOpenZeroLocus J s ⊆ excluded)
    (S : Finset (Option (Fin 2) → F))
    (hS : ∀ x ∈ S, aeval x g = 0 ∧ aeval x s ≠ 0 ∧
      (∀ f ∈ highCuts, aeval x f = 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card) :
    (S.card : ℚ) ≤ (h * b ^ 2 + 2 * v * a * b : ℕ) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  classical
  let J := bidegreeHypersurfaceIdeal (F := F) a b g
  let gl := bidegreeLift a b g hgAB
  let sl := bidegreeLift a b s hs
  let highCuts' : List (MvPolynomial (BidegreeIndex a b (Fin 2)) F) :=
    highCuts.attach.map fun f ↦ bidegreeLift a b f.1 (hhigh f.1 f.2)
  let cuts' : Fin n → MvPolynomial (BidegreeIndex a b (Fin 2)) F :=
    fun i ↦ bidegreeLift a b (cuts i) (hcuts i)
  let T₀ := J.retainedMinimalPrimes sl
  let S' := S.image (bidegreePoint (F := F) a b)
  let excluded' : Set (BidegreeIndex a b (Fin 2) → F) :=
    bidegreePoint (F := F) a b '' excluded
  have hT₀prime : ∀ P ∈ T₀, P.IsPrime := by
    intro P hP
    exact ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hP).1.isPrime
  have hT₀open : ∀ P ∈ T₀, sl ∉ P := by
    intro P hP
    exact ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hP).2
  have hsum : ∑ P ∈ T₀, affineDegree P ≤ affineDegree J := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
      (bidegreeHypersurface_sum_minimalPrimes_affineDegree_le ha hb hg0 hproper hgAB)
    · intro P hP
      exact mem_minimalPrimesFinset.mpr ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hP).1
    · intro P _ _
      exact affineDegree_nonneg P
  have hdim : ∀ P ∈ T₀, (hilbertPolynomial P).natDegree = 2 := by
    intro P hP
    have hmin := ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hP).1
    have hbase := bidegreeIdeal_hilbertPolynomial_natDegree
      (F := F) (σ := Fin 2) a b ha hb
    have hsource := hilbertPolynomial_span_singleton_natDegree_add_one hg0 hproper
    have hgl : gl ∉ bidegreeIdeal a b := by
      intro hmem
      change bidegreeMap a b gl = 0 at hmem
      dsimp only [gl] at hmem
      rw [bidegreeMap_bidegreeLift] at hmem
      exact hg0 hmem
    have hp := principalCut_component_hilbertPolynomial_natDegree_add_one
      (bidegreeIdeal_isPrime a b) hgl (by
        rw [← bidegreeHypersurfaceIdeal_eq_sup a b g hgAB ha hb]
        exact hmin)
    have hbase' :
        (hilbertPolynomial (bidegreeIdeal (F := F) (σ := Fin 2) a b)).natDegree = 3 := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_option,
        Fintype.card_fin] using hbase
    have hsource' : (hilbertPolynomial (Ideal.span {g})).natDegree + 1 = 3 := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_option,
        Fintype.card_fin] using hsource
    rw [hbase', ← hsource'] at hp
    omega
  have hhighDegree : ∀ f ∈ highCuts', f.totalDegree ≤ 1 := by
    intro f hf
    simp only [highCuts', List.mem_map, List.mem_attach] at hf
    obtain ⟨q, _, rfl⟩ := hf
    exact bidegreeLift_totalDegree_le_one a b q.1 (hhigh q.1 q.2)
  have hsourceData (P : Ideal (MvPolynomial (BidegreeIndex a b (Fin 2)) F))
      (hPT₀ : P ∈ T₀) (Q : Ideal (MvPolynomial (BidegreeIndex a b (Fin 2)) F))
      (hPQ : P ≤ Q) (hQ : Q.IsPrime) (hsQ : sl ∉ Q)
      (hhighQ : ∀ f ∈ highCuts', f ∈ Q) :
      let K : Ideal (MvPolynomial (Option (Fin 2)) F) :=
        Q.map (bidegreeMap a b).toRingHom
      K.IsPrime ∧ s ∉ K ∧ g ∈ K ∧ (∀ f ∈ highCuts, f ∈ K) ∧
        (hilbertPolynomial K).natDegree = (hilbertPolynomial Q).natDegree ∧
        cutsInIdeal K cuts = cutsInIdeal Q cuts' := by
    dsimp only
    have hPJ : J ≤ P := ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hPT₀).1.le
    have hbaseQ : bidegreeIdeal a b ≤ Q := by
      apply le_trans _ (hPJ.trans hPQ)
      dsimp only [J]
      rw [bidegreeHypersurfaceIdeal_eq_sup a b g hgAB ha hb]
      exact le_sup_left
    let K : Ideal (MvPolynomial (Option (Fin 2)) F) :=
      Q.map (bidegreeMap a b).toRingHom
    have hK : K.IsPrime := Ideal.map_isPrime_of_surjective
      (f := (bidegreeMap a b).toRingHom) (bidegreeMap_surjective a b ha hb) hbaseQ
    have hcomap : K.comap (bidegreeMap a b).toRingHom = Q := by
      change (Q.map (bidegreeMap a b).toRingHom).comap (bidegreeMap a b).toRingHom = Q
      rw [Ideal.comap_map_of_surjective (bidegreeMap a b).toRingHom
        (bidegreeMap_surjective a b ha hb) Q]
      apply sup_eq_left.mpr
      rw [← RingHom.ker_eq_comap_bot]
      exact hbaseQ
    have hsK : s ∉ K := by
      intro hsK
      have hsl : sl ∈ K.comap (bidegreeMap a b).toRingHom := by
        change bidegreeMap a b sl ∈ K
        dsimp only [sl]
        rwa [bidegreeMap_bidegreeLift]
      rw [hcomap] at hsl
      exact hsQ hsl
    have hgK : g ∈ K := by
      rw [← bidegreeMap_bidegreeLift a b g hgAB]
      apply Ideal.mem_map_of_mem (bidegreeMap a b).toRingHom
      apply hPQ
      apply hPJ
      dsimp only [J, gl]
      rw [bidegreeHypersurfaceIdeal_eq_sup a b g hgAB ha hb]
      exact (le_sup_right : Ideal.span {bidegreeLift a b g hgAB} ≤
        bidegreeIdeal a b ⊔ Ideal.span {bidegreeLift a b g hgAB})
          (Ideal.subset_span (Set.mem_singleton _))
    have hhighK : ∀ f ∈ highCuts, f ∈ K := by
      intro f hf
      rw [← bidegreeMap_bidegreeLift a b f (hhigh f hf)]
      apply Ideal.mem_map_of_mem (bidegreeMap a b).toRingHom
      apply hhighQ
      simp only [highCuts', List.mem_map, List.mem_attach]
      exact ⟨⟨f, hf⟩, trivial, rfl⟩
    have hdeg : (hilbertPolynomial K).natDegree = (hilbertPolynomial Q).natDegree := by
      have hQK : Q ≤ K.comap (bidegreeMap a b).toRingHom := by
        intro q hq
        exact Ideal.mem_map_of_mem (bidegreeMap a b).toRingHom hq
      let qmap :
          (MvPolynomial (BidegreeIndex a b (Fin 2)) F ⧸ Q) →ₐ[F]
            (MvPolynomial (Option (Fin 2)) F ⧸ K) :=
        Ideal.quotientMapₐ K (bidegreeMap a b) hQK
      have hqinj : Function.Injective qmap := by
        intro x y hxy
        rw [← sub_eq_zero]
        have hz : qmap (x - y) = 0 := by rw [map_sub, hxy, sub_self]
        obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (I := Q) (x - y)
        rw [← hp] at hz ⊢
        change Ideal.Quotient.mk K (bidegreeMap a b p) = 0 at hz
        rw [Ideal.Quotient.eq_zero_iff_mem] at hz ⊢
        have hpQ : p ∈ K.comap (bidegreeMap a b).toRingHom := hz
        rwa [hcomap] at hpQ
      have hqsurj : Function.Surjective qmap := by
        intro y
        obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (I := K) y
        obtain ⟨q, hq⟩ := bidegreeMap_surjective (F := F) a b ha hb p
        refine ⟨Ideal.Quotient.mk Q q, ?_⟩
        rw [← hp, ← hq]
        exact Ideal.quotientMap_mk (H := hQK)
      let e :
          (MvPolynomial (BidegreeIndex a b (Fin 2)) F ⧸ Q) ≃ₐ[F]
            (MvPolynomial (Option (Fin 2)) F ⧸ K) :=
        AlgEquiv.ofBijective qmap ⟨hqinj, hqsurj⟩
      symm
      apply hilbertPolynomial_natDegree_eq_of_finite_injective_algHom
        e.symm.toAlgHom e.symm.injective hQ.ne_top
      let _ : Algebra (MvPolynomial (Option (Fin 2)) F ⧸ K)
          (MvPolynomial (BidegreeIndex a b (Fin 2)) F ⧸ Q) :=
        e.symm.toRingHom.toAlgebra
      exact Module.Finite.of_surjective (Algebra.linearMap _ _) e.symm.surjective
    have hcutsEq : cutsInIdeal K cuts = cutsInIdeal Q cuts' := by
      ext i
      simp only [mem_cutsInIdeal]
      constructor
      · intro hi
        have hil : cuts' i ∈ K.comap (bidegreeMap a b).toRingHom := by
          change bidegreeMap a b (cuts' i) ∈ K
          dsimp only [cuts']
          rwa [bidegreeMap_bidegreeLift]
        rwa [hcomap] at hil
      · intro hi
        rw [← bidegreeMap_bidegreeLift a b (cuts i) (hcuts i)]
        exact Ideal.mem_map_of_mem (bidegreeMap a b).toRingHom hi
    exact ⟨hK, hsK, hgK, hhighK, hdeg, hcutsEq⟩
  have hcardS : S'.card = S.card := Finset.card_image_of_injective _
    (bidegreePoint_injective (F := F) a b ha hb)
  have hbound := iteratedRetainedCutFamily_incidence_off_excluded_hybrid_two T₀ sl
    hT₀prime hT₀open hdim hsum highCuts' hhighDegree (show 0 < 1 by omega)
    cuts' (fun i ↦ bidegreeLift_totalDegree_le_one a b _ (hcuts i))
    hLA hkA hAn excluded' ?_ ?_ S' ?_ ?_
  · rw [hcardS] at hbound
    norm_num only [Nat.cast_one, one_pow, mul_one] at hbound
    have hdegree := bidegreeHypersurface_affineDegree_le_two ha hb hg0 hproper hg
    let R : ℚ :=
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ))
    have hbound' : (S.card : ℚ) ≤ affineDegree J * R := by
      simpa only [R, mul_assoc] using hbound
    calc
      (S.card : ℚ) ≤ affineDegree J * R := hbound'
      _ ≤ (h * b ^ 2 + 2 * v * a * b : ℕ) * R :=
        mul_le_mul_of_nonneg_right (by simpa only [J] using hdegree) (by positivity)
      _ = _ := by dsimp only [R]; ring
  · intro P hPT₀ Q hPQ hQ hsQ hhighQ hdQ
    obtain ⟨hK, hsK, hgK, hhighK, hdeg, hcutsEq⟩ :=
      hsourceData P hPT₀ Q hPQ hQ hsQ hhighQ
    have hdK : 0 < (hilbertPolynomial
        (Q.map (bidegreeMap a b).toRingHom)).natDegree := by rwa [hdeg]
    have hsource := hdimension _ hK hsK hgK hhighK hdK
    rwa [hdeg, hcutsEq] at hsource
  · intro P hPT₀ Q hPQ hQ hsQ hhighQ hdQ hcutsQ
    obtain ⟨hK, hsK, hgK, hhighK, hdeg, hcutsEq⟩ :=
      hsourceData P hPT₀ Q hPQ hQ hsQ hhighQ
    have hdK : 0 < (hilbertPolynomial
        (Q.map (bidegreeMap a b).toRingHom)).natDegree := by rwa [hdeg]
    have hsource := hterminal _ hK hsK hgK hhighK hdK (by rwa [hcutsEq])
    intro z hz
    have hPJ : J ≤ P := ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hPT₀).1.le
    have hbaseQ : bidegreeIdeal a b ≤ Q := by
      apply le_trans _ (hPJ.trans hPQ)
      dsimp only [J]
      rw [bidegreeHypersurfaceIdeal_eq_sup a b g hgAB ha hb]
      exact le_sup_left
    have hzbase : z ∈ zeroLocus F (bidegreeIdeal (F := F) (σ := Fin 2) a b) :=
      zeroLocus_anti_mono hbaseQ hz.1
    obtain ⟨x, rfl⟩ := exists_bidegreePoint_of_mem_zeroLocus_bidegreeIdeal
      a b ha hb z hzbase
    have hxK : x ∈ zeroLocus F (Q.map (bidegreeMap a b).toRingHom) := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective (bidegreeMap a b).toRingHom
          (bidegreeMap_surjective a b ha hb)).mp hp
      change aeval x (bidegreeMap a b q) = 0
      rw [← aeval_bidegreePoint]
      exact hz.1 q hq
    have hxs : aeval x s ≠ 0 := by
      rw [← bidegreeMap_bidegreeLift a b s hs, ← aeval_bidegreePoint]
      exact hz.2
    exact ⟨x, hsource ⟨hxK, hxs⟩, rfl⟩
  · intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hxJ := (mem_zeroLocus_bidegreeHypersurfaceIdeal_iff a b ha hb g x).2
      (hS x hx).1
    have hxsl : aeval (bidegreePoint (F := F) a b x) sl ≠ 0 :=
      (not_congr (aeval_bidegreeLift_iff a b x s hs)).mpr (hS x hx).2.1
    refine ⟨?_, hxsl, ?_, ?_⟩
    · obtain ⟨P, hP, hxP⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus J sl
        (bidegreePoint (F := F) a b x) hxJ hxsl
      exact ⟨P, hP, hxP⟩
    · intro f hf
      simp only [highCuts', List.mem_map, List.mem_attach] at hf
      obtain ⟨q, _, rfl⟩ := hf
      exact (aeval_bidegreeLift_iff a b x q.1 (hhigh q.1 q.2)).2
        ((hS x hx).2.2.1 q.1 q.2)
    · rintro ⟨y, hy, hxy⟩
      have heq := bidegreePoint_injective (F := F) a b ha hb hxy
      exact (hS x hx).2.2.2 (heq ▸ hy)
  · intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have heq : agreementIndices cuts' (bidegreePoint (F := F) a b x) =
        agreementIndices cuts x := by
      ext i
      rw [mem_agreementIndices, mem_agreementIndices]
      exact aeval_bidegreeLift_iff a b x (cuts i) (hcuts i)
    rw [heq]
    exact hA x hx

/-- One-jet source specialization with the expected mixed degree. -/
theorem bidegreeHypersurface_source_incidence_off_excluded_sharp_one
    {a b h v n A L : ℕ} (ha : 0 < a) (hb : 0 < b) (hLA : L ≤ A) (hAn : A ≤ n)
    (g s : MvPolynomial (Option (Fin 1)) F) (hg0 : g ≠ 0)
    (hproper : Ideal.span ({g} : Set (MvPolynomial (Option (Fin 1)) F)) ≠ ⊤)
    (hg : g ∈ restrictBidegree (F := F) (σ := Fin 1) h v)
    (hgAB : g ∈ restrictBidegree (F := F) (σ := Fin 1) a b)
    (hs : s ∈ restrictBidegree (F := F) (σ := Fin 1) a b)
    (highCuts : List (MvPolynomial (Option (Fin 1)) F))
    (hhigh : ∀ f ∈ highCuts, f ∈ restrictBidegree (F := F) (σ := Fin 1) a b)
    (cuts : Fin n → MvPolynomial (Option (Fin 1)) F)
    (hcuts : ∀ i, cuts i ∈ restrictBidegree (F := F) (σ := Fin 1) a b)
    (excluded : Set (Option (Fin 1) → F))
    (hterminal : ∀ J : Ideal (MvPolynomial (Option (Fin 1)) F),
      J.IsPrime → s ∉ J → g ∈ J → (∀ f ∈ highCuts, f ∈ J) →
      0 < (hilbertPolynomial J).natDegree →
      L ≤ (cutsInIdeal J cuts).card → principalOpenZeroLocus J s ⊆ excluded)
    (S : Finset (Option (Fin 1) → F))
    (hS : ∀ x ∈ S, aeval x g = 0 ∧ aeval x s ≠ 0 ∧
      (∀ f ∈ highCuts, aeval x f = 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card) :
    (S.card : ℚ) ≤ (h * b + v * a : ℕ) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) := by
  have hc := bidegreeHypersurface_source_incidence_off_excluded_sharp ha hb hLA hAn
    g s hg0 hproper hgAB hs highCuts hhigh cuts hcuts excluded hterminal S hS hA
  have hd := hilbertPolynomial_span_singleton_natDegree_add_one hg0 hproper
  simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin] at hd
  have hd' : (hilbertPolynomial (Ideal.span {g})).natDegree = 1 := by omega
  rw [hd', pow_one] at hc
  exact hc.trans (mul_le_mul_of_nonneg_right
    (bidegreeHypersurface_affineDegree_le_one ha hb hg0 hproper hg) (by positivity))

/-- Two-jet source specialization with the expected mixed degree. -/
theorem bidegreeHypersurface_source_incidence_off_excluded_sharp_two
    {a b h v n A L : ℕ} (ha : 0 < a) (hb : 0 < b) (hLA : L ≤ A) (hAn : A ≤ n)
    (g s : MvPolynomial (Option (Fin 2)) F) (hg0 : g ≠ 0)
    (hproper : Ideal.span ({g} : Set (MvPolynomial (Option (Fin 2)) F)) ≠ ⊤)
    (hg : g ∈ restrictBidegree (F := F) (σ := Fin 2) h v)
    (hgAB : g ∈ restrictBidegree (F := F) (σ := Fin 2) a b)
    (hs : s ∈ restrictBidegree (F := F) (σ := Fin 2) a b)
    (highCuts : List (MvPolynomial (Option (Fin 2)) F))
    (hhigh : ∀ f ∈ highCuts, f ∈ restrictBidegree (F := F) (σ := Fin 2) a b)
    (cuts : Fin n → MvPolynomial (Option (Fin 2)) F)
    (hcuts : ∀ i, cuts i ∈ restrictBidegree (F := F) (σ := Fin 2) a b)
    (excluded : Set (Option (Fin 2) → F))
    (hterminal : ∀ J : Ideal (MvPolynomial (Option (Fin 2)) F),
      J.IsPrime → s ∉ J → g ∈ J → (∀ f ∈ highCuts, f ∈ J) →
      0 < (hilbertPolynomial J).natDegree →
      L ≤ (cutsInIdeal J cuts).card → principalOpenZeroLocus J s ⊆ excluded)
    (S : Finset (Option (Fin 2) → F))
    (hS : ∀ x ∈ S, aeval x g = 0 ∧ aeval x s ≠ 0 ∧
      (∀ f ∈ highCuts, aeval x f = 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card) :
    (S.card : ℚ) ≤ (h * b ^ 2 + 2 * v * a * b : ℕ) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^ 2 := by
  have hc := bidegreeHypersurface_source_incidence_off_excluded_sharp ha hb hLA hAn
    g s hg0 hproper hgAB hs highCuts hhigh cuts hcuts excluded hterminal S hS hA
  have hd := hilbertPolynomial_span_singleton_natDegree_add_one hg0 hproper
  simp only [Nat.card_eq_fintype_card, Fintype.card_option, Fintype.card_fin] at hd
  have hd' : (hilbertPolynomial (Ideal.span {g})).natDegree = 2 := by omega
  rw [hd'] at hc
  exact hc.trans (mul_le_mul_of_nonneg_right
    (bidegreeHypersurface_affineDegree_le_two ha hb hg0 hproper hg) (by positivity))

end AffineHilbert
