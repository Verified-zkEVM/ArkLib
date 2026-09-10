/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.DerivativeBidegreePoints
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.BidegreeExcluded

/-!
# Joint incidence with a separate derivative-degree bound

The monomial presentation makes agreement and high-coefficient cuts linear. Its degree
retains both total jet degree and degree in the derivative variable. The strict truncated
triangle and full-triangle boundary are treated separately, then exposed through one theorem.
The coefficient-space dimensions are checked on the original source components.
-/

@[expose] public section

noncomputable section

open MvPolynomial
open scoped BigOperators

namespace AffineHilbert

variable {F : Type*} [Field F]

/-- Two-dimensional bidegree incidence with a dimension-sensitive joint recurrence.

The capped derivative presentation makes both the fixed high cuts and the agreement cuts linear.
The former are charged once through the retained-family degree potential.  The latter use the
hybrid threshold: dimension one is controlled by the terminal excluded locus at `L`, while
dimension two uses the source coefficient-space budget at `k`. Presentation primes are mapped
back to the genuine source-coordinate primes before either hereditary premise is applied. -/
theorem derivativeBidegreeHypersurface_source_incidence_off_excluded_hybrid_two_of_lt
    {a b c h j r n A L k : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcb : c < b) (hrj : r ≤ j)
    (hLA : L ≤ A) (hkA : k ≤ A) (hAn : A ≤ n)
    (g s : MvPolynomial (Option (Fin 2)) F) (hg0 : g ≠ 0)
    (hproper : Ideal.span ({g} : Set (MvPolynomial (Option (Fin 2)) F)) ≠ ⊤)
    (hg : g ∈ restrictDerivativeBidegree (F := F) h j r)
    (hgAB : g ∈ restrictDerivativeBidegree (F := F) a b c)
    (hs : s ∈ restrictDerivativeBidegree (F := F) a b c)
    (highCuts : List (MvPolynomial (Option (Fin 2)) F))
    (hhigh : ∀ f ∈ highCuts, f ∈ restrictDerivativeBidegree (F := F) a b c)
    (cuts : Fin n → MvPolynomial (Option (Fin 2)) F)
    (hcuts : ∀ i, cuts i ∈ restrictDerivativeBidegree (F := F) a b c)
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
    (S.card : ℚ) ≤ (mixedDerivativeImageDegree h j r a b c : ℕ) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  classical
  let J := derivativeBidegreeHypersurfaceIdeal (F := F) a b c g
  let gl := derivativeBidegreeLift a b c g hgAB
  let sl := derivativeBidegreeLift a b c s hs
  let highCuts' : List (MvPolynomial (DerivativeBidegreeIndex a b c) F) :=
    highCuts.attach.map fun f ↦ derivativeBidegreeLift a b c f.1 (hhigh f.1 f.2)
  let cuts' : Fin n → MvPolynomial (DerivativeBidegreeIndex a b c) F :=
    fun i ↦ derivativeBidegreeLift a b c (cuts i) (hcuts i)
  let T₀ := J.retainedMinimalPrimes sl
  let S' := S.image (derivativeBidegreePoint (F := F) a b c)
  let excluded' : Set (DerivativeBidegreeIndex a b c → F) :=
    derivativeBidegreePoint (F := F) a b c '' excluded
  have hT₀prime : ∀ P ∈ T₀, P.IsPrime := by
    intro P hP
    exact ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hP).1.isPrime
  have hT₀open : ∀ P ∈ T₀, sl ∉ P := by
    intro P hP
    exact ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hP).2
  have hsum : ∑ P ∈ T₀, affineDegree P ≤ affineDegree J := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
      (derivativeBidegreeHypersurface_sum_minimalPrimes_affineDegree_le ha hb hc hg0 hproper hgAB)
    · intro P hP
      exact mem_minimalPrimesFinset.mpr ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hP).1
    · intro P _ _
      exact affineDegree_nonneg P
  have hdim : ∀ P ∈ T₀, (hilbertPolynomial P).natDegree = 2 := by
    intro P hP
    have hmin := ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hP).1
    have hbase := derivativeBidegreeIdeal_hilbertPolynomial_natDegree
      (F := F) a b c ha hb hc
    have hsource := hilbertPolynomial_span_singleton_natDegree_add_one hg0 hproper
    have hgl : gl ∉ derivativeBidegreeIdeal a b c := by
      intro hmem
      change derivativeBidegreeMap a b c gl = 0 at hmem
      dsimp only [gl] at hmem
      rw [derivativeBidegreeMap_derivativeBidegreeLift] at hmem
      exact hg0 hmem
    have hp := principalCut_component_hilbertPolynomial_natDegree_add_one
      (derivativeBidegreeIdeal_isPrime a b c) hgl (by
        rw [← derivativeBidegreeHypersurfaceIdeal_eq_sup a b c g hgAB ha hb hc]
        exact hmin)
    have hbase' :
        (hilbertPolynomial (derivativeBidegreeIdeal (F := F) a b c)).natDegree = 3 := by
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
    exact derivativeBidegreeLift_totalDegree_le_one a b c q.1 (hhigh q.1 q.2)
  have hsourceData (P : Ideal (MvPolynomial (DerivativeBidegreeIndex a b c) F))
      (hPT₀ : P ∈ T₀) (Q : Ideal (MvPolynomial (DerivativeBidegreeIndex a b c) F))
      (hPQ : P ≤ Q) (hQ : Q.IsPrime) (hsQ : sl ∉ Q)
      (hhighQ : ∀ f ∈ highCuts', f ∈ Q) :
      let K : Ideal (MvPolynomial (Option (Fin 2)) F) :=
        Q.map (derivativeBidegreeMap a b c).toRingHom
      K.IsPrime ∧ s ∉ K ∧ g ∈ K ∧ (∀ f ∈ highCuts, f ∈ K) ∧
        (hilbertPolynomial K).natDegree = (hilbertPolynomial Q).natDegree ∧
        cutsInIdeal K cuts = cutsInIdeal Q cuts' := by
    dsimp only
    have hPJ : J ≤ P := ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hPT₀).1.le
    have hbaseQ : derivativeBidegreeIdeal a b c ≤ Q := by
      apply le_trans _ (hPJ.trans hPQ)
      dsimp only [J]
      rw [derivativeBidegreeHypersurfaceIdeal_eq_sup a b c g hgAB ha hb hc]
      exact le_sup_left
    let K : Ideal (MvPolynomial (Option (Fin 2)) F) :=
      Q.map (derivativeBidegreeMap a b c).toRingHom
    have hK : K.IsPrime := Ideal.map_isPrime_of_surjective
      (f := (derivativeBidegreeMap a b c).toRingHom)
      (derivativeBidegreeMap_surjective a b c ha hb hc) hbaseQ
    have hcomap : K.comap (derivativeBidegreeMap a b c).toRingHom = Q := by
      change (Q.map (derivativeBidegreeMap a b c).toRingHom).comap
        (derivativeBidegreeMap a b c).toRingHom = Q
      rw [Ideal.comap_map_of_surjective (derivativeBidegreeMap a b c).toRingHom
        (derivativeBidegreeMap_surjective a b c ha hb hc) Q]
      apply sup_eq_left.mpr
      rw [← RingHom.ker_eq_comap_bot]
      exact hbaseQ
    have hsK : s ∉ K := by
      intro hsK
      have hsl : sl ∈ K.comap (derivativeBidegreeMap a b c).toRingHom := by
        change derivativeBidegreeMap a b c sl ∈ K
        dsimp only [sl]
        rwa [derivativeBidegreeMap_derivativeBidegreeLift]
      rw [hcomap] at hsl
      exact hsQ hsl
    have hgK : g ∈ K := by
      rw [← derivativeBidegreeMap_derivativeBidegreeLift a b c g hgAB]
      apply Ideal.mem_map_of_mem (derivativeBidegreeMap a b c).toRingHom
      apply hPQ
      apply hPJ
      dsimp only [J, gl]
      rw [derivativeBidegreeHypersurfaceIdeal_eq_sup a b c g hgAB ha hb hc]
      exact (le_sup_right : Ideal.span {derivativeBidegreeLift a b c g hgAB} ≤
        derivativeBidegreeIdeal a b c ⊔ Ideal.span {derivativeBidegreeLift a b c g hgAB})
          (Ideal.subset_span (Set.mem_singleton _))
    have hhighK : ∀ f ∈ highCuts, f ∈ K := by
      intro f hf
      rw [← derivativeBidegreeMap_derivativeBidegreeLift a b c f (hhigh f hf)]
      apply Ideal.mem_map_of_mem (derivativeBidegreeMap a b c).toRingHom
      apply hhighQ
      simp only [highCuts', List.mem_map, List.mem_attach]
      exact ⟨⟨f, hf⟩, trivial, rfl⟩
    have hdeg : (hilbertPolynomial K).natDegree = (hilbertPolynomial Q).natDegree := by
      have hQK : Q ≤ K.comap (derivativeBidegreeMap a b c).toRingHom := by
        intro q hq
        exact Ideal.mem_map_of_mem (derivativeBidegreeMap a b c).toRingHom hq
      let qmap :
          (MvPolynomial (DerivativeBidegreeIndex a b c) F ⧸ Q) →ₐ[F]
            (MvPolynomial (Option (Fin 2)) F ⧸ K) :=
        Ideal.quotientMapₐ K (derivativeBidegreeMap a b c) hQK
      have hqinj : Function.Injective qmap := by
        intro x y hxy
        rw [← sub_eq_zero]
        have hz : qmap (x - y) = 0 := by rw [map_sub, hxy, sub_self]
        obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (I := Q) (x - y)
        rw [← hp] at hz ⊢
        change Ideal.Quotient.mk K (derivativeBidegreeMap a b c p) = 0 at hz
        rw [Ideal.Quotient.eq_zero_iff_mem] at hz ⊢
        have hpQ : p ∈ K.comap (derivativeBidegreeMap a b c).toRingHom := hz
        rwa [hcomap] at hpQ
      have hqsurj : Function.Surjective qmap := by
        intro y
        obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (I := K) y
        obtain ⟨q, hq⟩ := derivativeBidegreeMap_surjective (F := F) a b c ha hb hc p
        refine ⟨Ideal.Quotient.mk Q q, ?_⟩
        rw [← hp, ← hq]
        exact Ideal.quotientMap_mk (H := hQK)
      let e :
          (MvPolynomial (DerivativeBidegreeIndex a b c) F ⧸ Q) ≃ₐ[F]
            (MvPolynomial (Option (Fin 2)) F ⧸ K) :=
        AlgEquiv.ofBijective qmap ⟨hqinj, hqsurj⟩
      symm
      apply hilbertPolynomial_natDegree_eq_of_finite_injective_algHom
        e.symm.toAlgHom e.symm.injective hQ.ne_top
      let _ : Algebra (MvPolynomial (Option (Fin 2)) F ⧸ K)
          (MvPolynomial (DerivativeBidegreeIndex a b c) F ⧸ Q) :=
        e.symm.toRingHom.toAlgebra
      exact Module.Finite.of_surjective (Algebra.linearMap _ _) e.symm.surjective
    have hcutsEq : cutsInIdeal K cuts = cutsInIdeal Q cuts' := by
      ext i
      simp only [mem_cutsInIdeal]
      constructor
      · intro hi
        have hil : cuts' i ∈ K.comap (derivativeBidegreeMap a b c).toRingHom := by
          change derivativeBidegreeMap a b c (cuts' i) ∈ K
          dsimp only [cuts']
          rwa [derivativeBidegreeMap_derivativeBidegreeLift]
        rwa [hcomap] at hil
      · intro hi
        rw [← derivativeBidegreeMap_derivativeBidegreeLift a b c (cuts i) (hcuts i)]
        exact Ideal.mem_map_of_mem (derivativeBidegreeMap a b c).toRingHom hi
    exact ⟨hK, hsK, hgK, hhighK, hdeg, hcutsEq⟩
  have hcardS : S'.card = S.card := Finset.card_image_of_injective _
    (derivativeBidegreePoint_injective (F := F) a b c ha hb hc)
  have hbound := iteratedRetainedCutFamily_incidence_off_excluded_hybrid_two T₀ sl
    hT₀prime hT₀open hdim hsum highCuts' hhighDegree (show 0 < 1 by omega)
    cuts' (fun i ↦ derivativeBidegreeLift_totalDegree_le_one a b c _ (hcuts i))
    hLA hkA hAn excluded' ?_ ?_ S' ?_ ?_
  · rw [hcardS] at hbound
    norm_num only [Nat.cast_one, one_pow, mul_one] at hbound
    have hdegree := derivativeBidegreeHypersurface_affineDegree_le_two_of_lt
      ha hb hc hcb hrj hg0 hproper hg
    let R : ℚ :=
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ))
    have hbound' : (S.card : ℚ) ≤ affineDegree J * R := by
      simpa only [R, mul_assoc] using hbound
    calc
      (S.card : ℚ) ≤ affineDegree J * R := hbound'
      _ ≤ (mixedDerivativeImageDegree h j r a b c : ℕ) * R :=
        mul_le_mul_of_nonneg_right (by simpa only [J] using hdegree) (by positivity)
      _ = _ := by dsimp only [R]; ring
  · intro P hPT₀ Q hPQ hQ hsQ hhighQ hdQ
    obtain ⟨hK, hsK, hgK, hhighK, hdeg, hcutsEq⟩ :=
      hsourceData P hPT₀ Q hPQ hQ hsQ hhighQ
    have hdK : 0 < (hilbertPolynomial
        (Q.map (derivativeBidegreeMap a b c).toRingHom)).natDegree := by rwa [hdeg]
    have hsource := hdimension _ hK hsK hgK hhighK hdK
    rwa [hdeg, hcutsEq] at hsource
  · intro P hPT₀ Q hPQ hQ hsQ hhighQ hdQ hcutsQ
    obtain ⟨hK, hsK, hgK, hhighK, hdeg, hcutsEq⟩ :=
      hsourceData P hPT₀ Q hPQ hQ hsQ hhighQ
    have hdK : 0 < (hilbertPolynomial
        (Q.map (derivativeBidegreeMap a b c).toRingHom)).natDegree := by rwa [hdeg]
    have hsource := hterminal _ hK hsK hgK hhighK hdK (by rwa [hcutsEq])
    intro z hz
    have hPJ : J ≤ P := ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hPT₀).1.le
    have hbaseQ : derivativeBidegreeIdeal a b c ≤ Q := by
      apply le_trans _ (hPJ.trans hPQ)
      dsimp only [J]
      rw [derivativeBidegreeHypersurfaceIdeal_eq_sup a b c g hgAB ha hb hc]
      exact le_sup_left
    have hzbase : z ∈ zeroLocus F (derivativeBidegreeIdeal (F := F) a b c) :=
      zeroLocus_anti_mono hbaseQ hz.1
    obtain ⟨x, rfl⟩ := exists_derivativeBidegreePoint_of_mem_zeroLocus_derivativeBidegreeIdeal
      a b c ha hb hc z hzbase
    have hxK : x ∈ zeroLocus F (Q.map (derivativeBidegreeMap a b c).toRingHom) := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective (derivativeBidegreeMap a b c).toRingHom
          (derivativeBidegreeMap_surjective a b c ha hb hc)).mp hp
      change aeval x (derivativeBidegreeMap a b c q) = 0
      rw [← aeval_derivativeBidegreePoint]
      exact hz.1 q hq
    have hxs : aeval x s ≠ 0 := by
      rw [← derivativeBidegreeMap_derivativeBidegreeLift a b c s hs,
        ← aeval_derivativeBidegreePoint]
      exact hz.2
    exact ⟨x, hsource ⟨hxK, hxs⟩, rfl⟩
  · intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have hxJ := (mem_zeroLocus_derivativeBidegreeHypersurfaceIdeal_iff a b c ha hb hc g x).2
      (hS x hx).1
    have hxsl : aeval (derivativeBidegreePoint (F := F) a b c x) sl ≠ 0 :=
      (not_congr (aeval_derivativeBidegreeLift_iff a b c x s hs)).mpr (hS x hx).2.1
    refine ⟨?_, hxsl, ?_, ?_⟩
    · obtain ⟨P, hP, hxP⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus J sl
        (derivativeBidegreePoint (F := F) a b c x) hxJ hxsl
      exact ⟨P, hP, hxP⟩
    · intro f hf
      simp only [highCuts', List.mem_map, List.mem_attach] at hf
      obtain ⟨q, _, rfl⟩ := hf
      exact (aeval_derivativeBidegreeLift_iff a b c x q.1 (hhigh q.1 q.2)).2
        ((hS x hx).2.2.1 q.1 q.2)
    · rintro ⟨y, hy, hxy⟩
      have heq := derivativeBidegreePoint_injective (F := F) a b c ha hb hc hxy
      exact (hS x hx).2.2.2 (heq ▸ hy)
  · intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    have heq : agreementIndices cuts' (derivativeBidegreePoint (F := F) a b c x) =
        agreementIndices cuts x := by
      ext i
      rw [mem_agreementIndices, mem_agreementIndices]
      exact aeval_derivativeBidegreeLift_iff a b c x (cuts i) (hcuts i)
    rw [heq]
    exact hA x hx

/-- Capped two-jet incidence, including the boundary `c = b`.  At the boundary the cap is
redundant and the existing full-triangle presentation gives the same mixed degree. -/
theorem derivativeBidegreeHypersurface_source_incidence_off_excluded_hybrid_two
    {a b c h j r n A L k : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hcb : c ≤ b) (hrj : r ≤ j)
    (hLA : L ≤ A) (hkA : k ≤ A) (hAn : A ≤ n)
    (g s : MvPolynomial (Option (Fin 2)) F) (hg0 : g ≠ 0)
    (hproper : Ideal.span ({g} : Set (MvPolynomial (Option (Fin 2)) F)) ≠ ⊤)
    (hg : g ∈ restrictDerivativeBidegree (F := F) h j r)
    (hgAB : g ∈ restrictDerivativeBidegree (F := F) a b c)
    (hs : s ∈ restrictDerivativeBidegree (F := F) a b c)
    (highCuts : List (MvPolynomial (Option (Fin 2)) F))
    (hhigh : ∀ f ∈ highCuts, f ∈ restrictDerivativeBidegree (F := F) a b c)
    (cuts : Fin n → MvPolynomial (Option (Fin 2)) F)
    (hcuts : ∀ i, cuts i ∈ restrictDerivativeBidegree (F := F) a b c)
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
    (S.card : ℚ) ≤ mixedDerivativeImageDegree h j r a b c *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  by_cases hlt : c < b
  · exact derivativeBidegreeHypersurface_source_incidence_off_excluded_hybrid_two_of_lt
      ha hb hc hlt hrj hLA hkA hAn g s hg0 hproper hg hgAB hs highCuts hhigh
        cuts hcuts excluded hdimension hterminal S hS hA
  · have hbc : b = c := Nat.le_antisymm (Nat.le_of_not_gt hlt) hcb
    subst b
    have hold := bidegreeHypersurface_source_incidence_off_excluded_hybrid_two
      ha hc hLA hkA hAn g s hg0 hproper
      (mem_restrictBidegree_of_mem_restrictDerivativeBidegree hg)
      (mem_restrictBidegree_of_mem_restrictDerivativeBidegree hgAB)
      (mem_restrictBidegree_of_mem_restrictDerivativeBidegree hs) highCuts
      (fun f hf ↦ mem_restrictBidegree_of_mem_restrictDerivativeBidegree (hhigh f hf))
      cuts (fun i ↦ mem_restrictBidegree_of_mem_restrictDerivativeBidegree (hcuts i))
      excluded hdimension hterminal S hS hA
    have htri : 2 * c * c - c ^ 2 = c ^ 2 := by
      rw [show 2 * c * c = c ^ 2 + c ^ 2 by ring, Nat.add_sub_cancel_left]
    have hdegree : mixedDerivativeImageDegree h j r a c c =
        h * c ^ 2 + 2 * j * a * c := by
      simp only [mixedDerivativeImageDegree, htri, Nat.sub_self, Nat.mul_zero,
        Nat.add_zero]
      ring
    rw [hdegree]
    simpa only [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hold


end AffineHilbert
