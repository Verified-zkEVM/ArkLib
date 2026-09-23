/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertCappedBidegree
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertComap
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.MonomialMap
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.DimensionSensitiveIncidence

/-!
# Hybrid incidence on capped bidegree hypersurfaces

For a nonzero polynomial with capped bidegree bounds, the monomial presentation turns its
hypersurface into a family of affine primes of dimension at most two. A hybrid incidence budget on
these primes bounds the number of points satisfying the agreement cuts by the capped mixed volume
times two incidence factors.

## Main statements

* `MvPolynomial.cappedBidegreeHypersurface_incidence_off_excluded_hybrid_two`: a hybrid incidence
  bound using the capped mixed volume, valid for every positive cap.

## References
- [DKT26]
-/

@[expose] public section

noncomputable section

open MvPolynomial
open scoped BigOperators

namespace MvPolynomial

variable {F : Type*} [Field F]

private theorem aeval_monomialLift_iff
    (E : Set ((Option (Fin 2)) →₀ ℕ)) (x : Option (Fin 2) → F)
    (p : MvPolynomial (Option (Fin 2)) F) (hp : p ∈ restrictSupport F E) :
    aeval (monomialPoint E x) (monomialLift p hp) = 0 ↔ aeval x p = 0 := by
  rw [aeval_monomialPoint, monomialMap_monomialLift]

/-- Hybrid incidence on a capped bidegree hypersurface. The high cuts and agreement cuts become
linear after the monomial presentation. The high cuts contribute through the retained-family
degree potential. Dimension-one components use the terminal excluded locus at `L`, and
dimension-two components use the coefficient-space budget at `k`. -/
theorem cappedBidegreeHypersurface_incidence_off_excluded_hybrid_two
    {a b c h j r n A L k : ℕ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hLA : L ≤ A) (hkA : k ≤ A)
    (g s : MvPolynomial (Option (Fin 2)) F) (hg0 : g ≠ 0)
    (hproper : Ideal.span ({g} : Set (MvPolynomial (Option (Fin 2)) F)) ≠ ⊤)
    (hg : g ∈ restrictCappedBidegree (Fin 2) F 1 h j r)
    (hgAB : g ∈ restrictCappedBidegree (Fin 2) F 1 a b c)
    (hs : s ∈ restrictCappedBidegree (Fin 2) F 1 a b c)
    (highCuts : List (MvPolynomial (Option (Fin 2)) F))
    (hhigh : ∀ f ∈ highCuts, f ∈ restrictCappedBidegree (Fin 2) F 1 a b c)
    (cuts : Fin n → MvPolynomial (Option (Fin 2)) F)
    (hcuts : ∀ i, cuts i ∈ restrictCappedBidegree (Fin 2) F 1 a b c)
    (excluded : Set (Option (Fin 2) → F))
    (hdimension : ∀ J : Ideal (MvPolynomial (Option (Fin 2)) F),
      J.IsPrime → s ∉ J → g ∈ J → (∀ f ∈ highCuts, f ∈ J) →
      0 < (affineHilbertPolynomial J).natDegree →
      (affineHilbertPolynomial J).natDegree ≤ k + 1 ∧
        (1 < (affineHilbertPolynomial J).natDegree →
          ({i | cuts i ∈ J}.ncard) ≤ k + 1 - (affineHilbertPolynomial J).natDegree))
    (hterminal : ∀ J : Ideal (MvPolynomial (Option (Fin 2)) F),
      J.IsPrime → s ∉ J → g ∈ J → (∀ f ∈ highCuts, f ∈ J) →
      0 < (affineHilbertPolynomial J).natDegree →
      L ≤ ({i | cuts i ∈ J}.ncard) →
        {x | x ∈ zeroLocus F J ∧ aeval x s ≠ 0} ⊆ excluded)
    (S : Finset (Option (Fin 2) → F))
    (hS : ∀ x ∈ S, aeval x g = 0 ∧ aeval x s ≠ 0 ∧
      (∀ f ∈ highCuts, aeval x f = 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ ({i | aeval x (cuts i) = 0}.ncard)) :
    (S.card : ℚ) ≤ (cappedBidegreeMixedVolume h j r a b c : ℕ) *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  classical
  let E := cappedBidegreeExponents (Fin 2) 1 a b c
  let φ := monomialMap F E
  let hφ := monomialMap_cappedBidegreeExponents_surjective (σ := Fin 2) (R := F) (i := 1)
    (a := a) (b := b) (c := c) ha hb hc
  have hgAB' : g ∈ restrictSupport F E := by
    simpa [restrictCappedBidegree, E] using hgAB
  have hs' : s ∈ restrictSupport F E := by
    simpa [restrictCappedBidegree, E] using hs
  have hhigh' : ∀ f ∈ highCuts, f ∈ restrictSupport F E := by
    intro f hf
    simpa [restrictCappedBidegree, E] using hhigh f hf
  have hcuts' : ∀ i, cuts i ∈ restrictSupport F E := by
    intro i
    simpa [restrictCappedBidegree, E] using hcuts i
  let J := (Ideal.span {g}).comap φ
  let gl := monomialLift g hgAB'
  let sl := monomialLift s hs'
  have hJ_eq : J = RingHom.ker φ ⊔ Ideal.span {gl} := by
    dsimp only [J]
    rw [← monomialMap_monomialLift g hgAB']
    exact Ideal.comap_span_singleton_of_surjective φ hφ gl
  let highCuts' : List (MvPolynomial E F) :=
    highCuts.attach.map fun f ↦ monomialLift f.1 (hhigh' f.1 f.2)
  let cuts' : Fin n → MvPolynomial E F :=
    fun i ↦ monomialLift (cuts i) (hcuts' i)
  let T₀ := J.retainedMinimalPrimes sl
  let S' := S.image (monomialPoint E)
  let excluded' : Set (E → F) :=
    monomialPoint E '' excluded
  have hT₀prime : ∀ P ∈ T₀, P.IsPrime := by
    intro P hP
    exact ((Ideal.mem_retainedMinimalPrimes).mp hP).1.isPrime
  have hT₀open : ∀ P ∈ T₀, sl ∉ P := by
    intro P hP
    exact ((Ideal.mem_retainedMinimalPrimes).mp hP).2
  have hsum : ∑ P ∈ T₀, affineDegree P ≤ affineDegree J := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
      (sum_affineDegree_minimalPrimes_comap_span_singleton_le_of_surjective φ hφ g)
    · intro P hP
      exact Ideal.mem_minimalPrimesFinset.mpr ((Ideal.mem_retainedMinimalPrimes).mp hP).1
    · intro P _ _
      exact affineDegree_nonneg P
  have hdegree := affineDegree_comap_cappedBidegree_span_singleton_le
    ha hb hc hg0 hg
  have hdim : ∀ P ∈ T₀, (affineHilbertPolynomial P).natDegree = 2 := by
    intro P hP
    have hmin := ((Ideal.mem_retainedMinimalPrimes).mp hP).1
    have hbase := natDegree_affineHilbertPolynomial_ker_of_surjective φ hφ
    have hprincipal := natDegree_affineHilbertPolynomial_span_singleton_add_one hg0 hproper
    have hgl : gl ∉ RingHom.ker φ := by
      intro hmem
      change φ gl = 0 at hmem
      dsimp only [φ, gl] at hmem
      rw [monomialMap_monomialLift] at hmem
      exact hg0 hmem
    have hkerprime : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
    rw [hJ_eq] at hmin
    have hp := @MvPolynomial.principalCut_natDegree_affineHilbertPolynomial_add_one
      F E inferInstance inferInstance (RingHom.ker φ) P hkerprime gl hgl hmin
    have hbase' :
        (affineHilbertPolynomial (RingHom.ker φ)).natDegree = 3 := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_option,
        Fintype.card_fin] using hbase
    have hprincipal' : (affineHilbertPolynomial (Ideal.span {g})).natDegree + 1 = 3 := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_option,
        Fintype.card_fin] using hprincipal
    rw [hbase', ← hprincipal'] at hp
    omega
  have hhighDegree : ∀ f ∈ highCuts', f.totalDegree ≤ 1 := by
    intro f hf
    simp only [highCuts', List.mem_map, List.mem_attach] at hf
    obtain ⟨q, _, rfl⟩ := hf
    exact totalDegree_monomialLift_le_one q.1 (hhigh q.1 q.2)
  have hprincipalData (P : Ideal (MvPolynomial E F))
      (hPT₀ : P ∈ T₀) (Q : Ideal (MvPolynomial E F))
      (hPQ : P ≤ Q) (hQ : Q.IsPrime) (hsQ : sl ∉ Q)
      (hhighQ : ∀ f ∈ highCuts', f ∈ Q) :
      let K : Ideal (MvPolynomial (Option (Fin 2)) F) :=
        Q.map φ.toRingHom
      K.IsPrime ∧ s ∉ K ∧ g ∈ K ∧ (∀ f ∈ highCuts, f ∈ K) ∧
        (affineHilbertPolynomial K).natDegree = (affineHilbertPolynomial Q).natDegree ∧
        {i | cuts i ∈ K}.ncard = {i | cuts' i ∈ Q}.ncard := by
    dsimp only
    have hPJ : J ≤ P := ((Ideal.mem_retainedMinimalPrimes).mp hPT₀).1.le
    have hbaseQ : RingHom.ker φ ≤ Q := by
      calc
        RingHom.ker φ ≤ RingHom.ker φ ⊔ Ideal.span {gl} := le_sup_left
        _ = J := hJ_eq.symm
        _ ≤ Q := hPJ.trans hPQ
    let K : Ideal (MvPolynomial (Option (Fin 2)) F) :=
      Q.map φ.toRingHom
    have hK : K.IsPrime := Ideal.map_isPrime_of_surjective
      (f := φ.toRingHom) hφ hbaseQ
    have hcomap : K.comap φ.toRingHom = Q := by
      change (Q.map φ.toRingHom).comap
        φ.toRingHom = Q
      rw [Ideal.comap_map_of_surjective φ.toRingHom hφ Q]
      apply sup_eq_left.mpr
      rw [← RingHom.ker_eq_comap_bot]
      exact hbaseQ
    have hsK : s ∉ K := by
      intro hsK
      have hsl : sl ∈ K.comap φ.toRingHom := by
        change φ sl ∈ K
        dsimp only [φ, sl]
        rwa [monomialMap_monomialLift]
      rw [hcomap] at hsl
      exact hsQ hsl
    have hgK : g ∈ K := by
      rw [← monomialMap_monomialLift g hgAB']
      apply Ideal.mem_map_of_mem φ.toRingHom
      apply hPQ
      apply hPJ
      rw [hJ_eq]
      exact (le_sup_right : Ideal.span {gl} ≤ RingHom.ker φ ⊔ Ideal.span {gl})
        (Ideal.subset_span (Set.mem_singleton _))
    have hhighK : ∀ f ∈ highCuts, f ∈ K := by
      intro f hf
      rw [← monomialMap_monomialLift f (hhigh' f hf)]
      apply Ideal.mem_map_of_mem φ.toRingHom
      apply hhighQ
      simp only [highCuts', List.mem_map, List.mem_attach]
      exact ⟨⟨f, hf⟩, trivial, rfl⟩
    have hdeg : (affineHilbertPolynomial K).natDegree = (affineHilbertPolynomial Q).natDegree := by
      have hQK : Q ≤ K.comap φ.toRingHom := by
        intro q hq
        exact Ideal.mem_map_of_mem φ.toRingHom hq
      let qmap :
          (MvPolynomial E F ⧸ Q) →ₐ[F]
            (MvPolynomial (Option (Fin 2)) F ⧸ K) :=
        Ideal.quotientMapₐ K φ hQK
      have hqinj : Function.Injective qmap := by
        intro x y hxy
        rw [← sub_eq_zero]
        have hz : qmap (x - y) = 0 := by rw [map_sub, hxy, sub_self]
        obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (I := Q) (x - y)
        rw [← hp] at hz ⊢
        change Ideal.Quotient.mk K (φ p) = 0 at hz
        rw [Ideal.Quotient.eq_zero_iff_mem] at hz ⊢
        have hpQ : p ∈ K.comap φ.toRingHom := hz
        rwa [hcomap] at hpQ
      have hqsurj : Function.Surjective qmap := by
        intro y
        obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (I := K) y
        obtain ⟨q, hq⟩ := hφ p
        refine ⟨Ideal.Quotient.mk Q q, ?_⟩
        rw [← hp, ← hq]
        exact Ideal.quotientMap_mk (H := hQK)
      let e :
          (MvPolynomial E F ⧸ Q) ≃ₐ[F]
            (MvPolynomial (Option (Fin 2)) F ⧸ K) :=
        AlgEquiv.ofBijective qmap ⟨hqinj, hqsurj⟩
      symm
      apply natDegree_affineHilbertPolynomial_eq_of_finite_of_injective
        e.symm.toAlgHom ?_ e.symm.injective
      let _ : Algebra (MvPolynomial (Option (Fin 2)) F ⧸ K)
          (MvPolynomial E F ⧸ Q) :=
        e.symm.toRingHom.toAlgebra
      exact Module.Finite.of_surjective (Algebra.linearMap _ _) e.symm.surjective
    have hcutsEq : {i | cuts i ∈ K}.ncard = {i | cuts' i ∈ Q}.ncard := by
      congr 1
      ext i
      simp only [Set.mem_ofPred_eq]
      constructor
      · intro hi
        have hil : cuts' i ∈ K.comap φ.toRingHom := by
          change φ (cuts' i) ∈ K
          dsimp only [φ, cuts']
          rwa [monomialMap_monomialLift]
        rwa [hcomap] at hil
      · intro hi
        rw [← monomialMap_monomialLift (cuts i) (hcuts' i)]
        exact Ideal.mem_map_of_mem φ.toRingHom hi
    exact ⟨hK, hsK, hgK, hhighK, hdeg, hcutsEq⟩
  have hpoint : Function.Injective (monomialPoint (E := F) E) :=
    monomialPoint_injective (fun v ↦ single_mem_cappedBidegreeExponents ha hb hc v)
  have hcardS : S'.card = S.card := Finset.card_image_of_injective _ hpoint
  have hsumPotential :
      ∑ P ∈ T₀, affineDegree P * (1 : ℚ) ^ (affineHilbertPolynomial P).natDegree ≤
        affineDegree J := by
    simpa using hsum
  have hbound := card_le_hybridDimensionSensitiveIncidenceProduct_two_of_iteratedRetainedCutFamily
    hT₀prime (fun P hP ↦ (hdim P hP).le) sl (show 1 ≤ 1 by omega)
    hhighDegree hsumPotential
    cuts' (fun i ↦ totalDegree_monomialLift_le_one _ (hcuts' i))
    (show 0 < 1 by omega) hLA hkA excluded'
    (by
      intro P hPT₀ Q hPQ hQ hsQ hhighQ hdQ
      obtain ⟨hK, hsK, hgK, hhighK, hdeg, hcutsEq⟩ :=
        hprincipalData P hPT₀ Q hPQ hQ hsQ hhighQ
      have hdQ' : 0 < (affineHilbertPolynomial Q).natDegree := by omega
      have hdK : 0 < (affineHilbertPolynomial (Q.map φ.toRingHom)).natDegree := by
        rwa [hdeg]
      have hprincipal := hdimension _ hK hsK hgK hhighK hdK
      have hdimK : 1 < (affineHilbertPolynomial
          (Q.map φ.toRingHom)).natDegree := by rwa [hdeg]
      have hcutsK := hprincipal.2 hdimK
      have hcutsQ : {i | cuts' i ∈ Q}.ncard ≤
          k + 1 - (affineHilbertPolynomial Q).natDegree := by
        rw [← hcutsEq, ← hdeg]
        exact hcutsK
      omega)
    (by
      intro P hPT₀ Q hPQ hQ hsQ hhighQ hdQ hcutsQ
      obtain ⟨hK, hsK, hgK, hhighK, hdeg, hcutsEq⟩ :=
        hprincipalData P hPT₀ Q hPQ hQ hsQ hhighQ
      have hdK : 0 < (affineHilbertPolynomial (Q.map φ.toRingHom)).natDegree := by
        rwa [hdeg]
      have hprincipal := hterminal _ hK hsK hgK hhighK hdK (by rwa [hcutsEq])
      intro z hz
      have hPJ : J ≤ P := ((Ideal.mem_retainedMinimalPrimes).mp hPT₀).1.le
      have hbaseQ : RingHom.ker φ ≤ Q := by
        calc
          RingHom.ker φ ≤ RingHom.ker φ ⊔ Ideal.span {gl} := le_sup_left
          _ = J := hJ_eq.symm
          _ ≤ Q := hPJ.trans hPQ
      have hzbase : z ∈ zeroLocus F (RingHom.ker φ) :=
        zeroLocus_anti_mono hbaseQ hz.1
      obtain ⟨x, rfl⟩ := exists_monomialPoint_eq_of_mem_zeroLocus_ker
        (fun v ↦ single_mem_cappedBidegreeExponents ha hb hc v) hzbase
      have hxK : x ∈ zeroLocus F (Q.map φ.toRingHom) := by
        intro p hp
        obtain ⟨q, hq, rfl⟩ :=
          (Ideal.mem_map_iff_of_surjective φ.toRingHom hφ).mp hp
        change aeval x (φ q) = 0
        rw [← aeval_monomialPoint]
        exact hz.1 q hq
      have hxs : aeval x s ≠ 0 := by
        rw [← monomialMap_monomialLift s hs', ← aeval_monomialPoint]
        exact hz.2
      exact ⟨x, hprincipal ⟨hxK, hxs⟩, rfl⟩)
    S'
    (by
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      have hxJ : monomialPoint E x ∈ zeroLocus F J := by
        change monomialPoint E x ∈ zeroLocus F ((Ideal.span {g}).comap φ)
        rw [monomialPoint_mem_zeroLocus_comap_iff
          (fun v ↦ single_mem_cappedBidegreeExponents ha hb hc v) (Ideal.span {g}) x]
        simpa [zeroLocus_span] using (hS x hx).1
      have hxsl : aeval (monomialPoint E x) sl ≠ 0 :=
        (not_congr (aeval_monomialLift_iff E x s hs')).mpr (hS x hx).2.1
      refine ⟨?_, hxsl, ?_, ?_⟩
      · obtain ⟨P, hP, hxP⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus J sl
          (monomialPoint E x) hxJ hxsl
        exact ⟨P, hP, hxP⟩
      · intro f hf
        simp only [highCuts', List.mem_map, List.mem_attach] at hf
        obtain ⟨q, _, rfl⟩ := hf
        exact (aeval_monomialLift_iff E x q.1 (hhigh' q.1 q.2)).2
          ((hS x hx).2.2.1 q.1 q.2)
      · rintro ⟨y, hy, hxy⟩
        have heq := hpoint hxy
        exact (hS x hx).2.2.2 (heq ▸ hy))
    (by
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      have heq : {i | aeval (monomialPoint E x) (cuts' i) = 0} =
          {i | aeval x (cuts i) = 0} := by
        ext i
        exact aeval_monomialLift_iff E x (cuts i) (hcuts' i)
      rw [heq]
      exact hA x hx)
  let R : ℚ :=
    (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
      (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ))
  have hbound' : (S.card : ℚ) ≤ affineDegree J * R := by
    simp only [Fintype.card_fin, mul_one] at hbound
    rw [hcardS] at hbound
    simpa only [R, mul_assoc] using hbound
  calc
    (S.card : ℚ) ≤ affineDegree J * R := hbound'
    _ ≤ (cappedBidegreeMixedVolume h j r a b c : ℕ) * R :=
      mul_le_mul_of_nonneg_right (by simpa only [J] using hdegree) (by positivity)
    _ = _ := by dsimp only [R]; ring

end MvPolynomial
