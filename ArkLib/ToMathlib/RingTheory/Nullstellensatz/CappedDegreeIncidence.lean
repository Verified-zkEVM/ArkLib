/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertCappedDegree
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.MonomialMap
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.AgreementIncidence

/-!
# Sharp incidence on capped-degree hypersurfaces

For a plane curve with separate total-degree and coordinate-degree bounds, the monomial map of
the capped exponents presents its hypersurface as a family of curves with bounded total affine
degree. If every choice of `k` agreement cuts determines at most one point on each relevant
principal open subset, then the number of plane points is bounded by the capped mixed volume and
the sharp agreement ratio.

## Main statements

* `MvPolynomial.cappedDegreeHypersurface_incidence_sharp`: the sharp incidence bound for a
  hypersurface in the capped-degree presentation.

## References
- [DKT26]
-/

@[expose] public section

noncomputable section

open MvPolynomial
open scoped BigOperators Finset

namespace MvPolynomial

variable {F : Type*} [Field F]

private theorem ncard_coe_inter_setOf {α : Type*} (S : Finset α) (p : α → Prop)
    [DecidablePred p] : ((S : Set α) ∩ {x | p x}).ncard = #(S.filter p) := by
  rw [← Set.ncard_coe_finset, Finset.coe_filter]
  rfl

private theorem aeval_monomialLift_iff
    (E : Set ((Fin 2) →₀ ℕ)) (x : Fin 2 → F)
    (p : MvPolynomial (Fin 2) F) (hp : p ∈ restrictSupport F E) :
    aeval (monomialPoint E x) (monomialLift p hp) = 0 ↔ aeval x p = 0 := by
  rw [aeval_monomialPoint, monomialMap_monomialLift]

/-- Let `g` have capped-degree bounds `(j, r)` and let `highCuts` have bounds `(b, c)`. If every
set of `k` agreement cuts determines at most one point on each relevant component away from `s`,
then every finite set of plane points on `g = 0` satisfying the high cuts and agreeing with at
least `A` cuts has size at most
`cappedDegreeMixedVolume j r b c * ((n - k + 1) / (A - k + 1))`. -/
theorem cappedDegreeHypersurface_incidence_sharp
    [IsAlgClosed F] {b c j r n A k : ℕ} (hb : 0 < b) (hc : 0 < c)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (g s : MvPolynomial (Fin 2) F) (hg0 : g ≠ 0)
    (hg : g ∈ restrictCappedDegree (Fin 2) F 1 j r)
    (hgbc : g ∈ restrictCappedDegree (Fin 2) F 1 b c)
    (hsbc : s ∈ restrictCappedDegree (Fin 2) F 1 b c)
    (highCuts : List (MvPolynomial (Fin 2) F))
    (hhigh : ∀ f ∈ highCuts, f ∈ restrictCappedDegree (Fin 2) F 1 b c)
    (cuts : Fin n → MvPolynomial (Fin 2) F)
    (hcuts : ∀ i, cuts i ∈ restrictCappedDegree (Fin 2) F 1 b c)
    (S : Finset (Fin 2 → F))
    (hS : ∀ x ∈ S, aeval x g = 0 ∧ aeval x s ≠ 0 ∧
      (∀ f ∈ highCuts, aeval x f = 0))
    (hA : ∀ x ∈ S, A ≤ {i | aeval x (cuts i) = 0}.ncard)
    (hunique : ∀ J : Ideal (MvPolynomial (Fin 2) F),
      J.IsPrime → s ∉ J → g ∈ J → (∀ f ∈ highCuts, f ∈ J) →
      ∀ U : Finset (Fin n), U.card = k →
      ∀ x y : Fin 2 → F,
        x ∈ zeroLocus F J → aeval x s ≠ 0 →
        y ∈ zeroLocus F J → aeval y s ≠ 0 →
        (∀ i ∈ U, aeval x (cuts i) = 0 ∧ aeval y (cuts i) = 0) → x = y) :
    (S.card : ℚ) ≤ (cappedDegreeMixedVolume j r b c : ℕ) *
      (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  classical
  let E := cappedDegreeExponents (Fin 2) 1 b c
  let φ := monomialMap F E
  have hφ : Function.Surjective φ :=
    monomialMap_cappedDegreeExponents_surjective (σ := Fin 2) (R := F) (i := 1) hb hc
  have hE : ∀ i : Fin 2, Finsupp.single i 1 ∈ E :=
    single_mem_cappedDegreeExponents hb hc
  have hg' : g ∈ restrictSupport F E := by
    simpa [restrictCappedDegree, E] using hgbc
  have hs' : s ∈ restrictSupport F E := by
    simpa [restrictCappedDegree, E] using hsbc
  have hhigh' : ∀ f ∈ highCuts, f ∈ restrictSupport F E := by
    intro f hf
    simpa [restrictCappedDegree, E] using hhigh f hf
  have hcuts' : ∀ i, cuts i ∈ restrictSupport F E := by
    intro i
    simpa [restrictCappedDegree, E] using hcuts i
  let J := (Ideal.span {g}).comap φ
  let gl := monomialLift g hg'
  let sl := monomialLift s hs'
  have hJ_eq : J = RingHom.ker φ ⊔ Ideal.span {gl} := by
    dsimp only [J]
    rw [← monomialMap_monomialLift g hg']
    exact Ideal.comap_span_singleton_of_surjective φ hφ gl
  let highCuts' : List (MvPolynomial E F) :=
    highCuts.attach.map fun f ↦ monomialLift f.1 (hhigh' f.1 f.2)
  let cuts' : Fin n → MvPolynomial E F := fun i ↦ monomialLift (cuts i) (hcuts' i)
  let T₀ := J.retainedMinimalPrimes sl
  let S' := S.image (monomialPoint E)
  have hT₀prime : ∀ P ∈ T₀, P.IsPrime := by
    intro P hP
    exact ((Ideal.mem_retainedMinimalPrimes).mp hP).1.isPrime
  have hT₀open : ∀ P ∈ T₀, sl ∉ P := by
    intro P hP
    exact ((Ideal.mem_retainedMinimalPrimes).mp hP).2
  have hsum : ∑ P ∈ T₀, affineDegree P ≤ cappedDegreeMixedVolume j r b c := by
    apply le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_)
      (sum_affineDegree_minimalPrimes_comap_cappedDegree_span_singleton_le hb hc hg0 hg)
    · intro P hP
      exact Ideal.mem_minimalPrimesFinset.mpr
        ((Ideal.mem_retainedMinimalPrimes).mp hP).1
    · intro P _ _
      exact affineDegree_nonneg P
  have hdim : ∀ P ∈ T₀, (affineHilbertPolynomial P).natDegree = 1 := by
    intro P hP
    have hmin := ((Ideal.mem_retainedMinimalPrimes).mp hP).1
    have hbase := natDegree_affineHilbertPolynomial_ker_of_surjective φ hφ
    have hgl : gl ∉ RingHom.ker φ := by
      intro hmem
      change φ gl = 0 at hmem
      dsimp only [φ, gl] at hmem
      rw [monomialMap_monomialLift] at hmem
      exact hg0 hmem
    have hkerprime : (RingHom.ker φ).IsPrime := RingHom.ker_isPrime φ
    rw [hJ_eq] at hmin
    have hp := @principalCut_natDegree_affineHilbertPolynomial_add_one
      F E inferInstance inferInstance (RingHom.ker φ) P hkerprime gl hgl hmin
    have hbase' : (affineHilbertPolynomial (RingHom.ker φ)).natDegree = 2 := by
      simpa only [Nat.card_eq_fintype_card, Fintype.card_fin] using hbase
    rw [hbase'] at hp
    omega
  have hhighDegree : ∀ f ∈ highCuts', f.totalDegree ≤ 1 := by
    intro f hf
    simp only [highCuts', List.mem_map, List.mem_attach] at hf
    obtain ⟨q, _, rfl⟩ := hf
    exact totalDegree_monomialLift_le_one q.1 (hhigh q.1 q.2)
  have hprincipalData (P : Ideal (MvPolynomial E F)) (hP : P ∈ T₀)
      (Q : Ideal (MvPolynomial E F)) (hPQ : P ≤ Q) (hQ : Q.IsPrime)
      (hsQ : sl ∉ Q) (hhighQ : ∀ f ∈ highCuts', f ∈ Q) :
      let K : Ideal (MvPolynomial (Fin 2) F) := Q.map φ.toRingHom
      K.IsPrime ∧ s ∉ K ∧ g ∈ K ∧ (∀ f ∈ highCuts, f ∈ K) := by
    dsimp only
    have hPJ : J ≤ P := ((Ideal.mem_retainedMinimalPrimes).mp hP).1.le
    have hbaseQ : RingHom.ker φ ≤ Q := by
      calc
        RingHom.ker φ ≤ RingHom.ker φ ⊔ Ideal.span {gl} := le_sup_left
        _ = J := hJ_eq.symm
        _ ≤ Q := hPJ.trans hPQ
    let K : Ideal (MvPolynomial (Fin 2) F) := Q.map φ.toRingHom
    have hK : K.IsPrime := Ideal.map_isPrime_of_surjective
      (f := φ.toRingHom) hφ hbaseQ
    have hcomap : K.comap φ.toRingHom = Q := by
      change (Q.map φ.toRingHom).comap φ.toRingHom = Q
      rw [Ideal.comap_map_of_surjective φ.toRingHom hφ Q]
      apply sup_eq_left.mpr
      rw [← RingHom.ker_eq_comap_bot]
      exact hbaseQ
    have hsK : s ∉ K := by
      intro hsK
      have hsl : sl ∈ K.comap φ.toRingHom := by
        change φ sl ∈ K
        dsimp only [sl]
        rwa [monomialMap_monomialLift]
      rw [hcomap] at hsl
      exact hsQ hsl
    have hgK : g ∈ K := by
      rw [← monomialMap_monomialLift g hg']
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
    exact ⟨hK, hsK, hgK, hhighK⟩
  have hpoint : Function.Injective (monomialPoint (E := F) E) :=
    monomialPoint_injective hE
  have hcardS : S'.card = S.card := Finset.card_image_of_injective _ hpoint
  have hsumPotential :
      ∑ P ∈ T₀, affineDegree P * (1 : ℚ) ^ (affineHilbertPolynomial P).natDegree ≤
        (cappedDegreeMixedVolume j r b c : ℚ) := by
    simpa using hsum
  let t : ℚ := ((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)
  have ht : 1 ≤ t := by
    apply (le_div_iff₀ (by exact_mod_cast (show 0 < A - k + 1 by omega))).2
    simpa only [one_mul] using
      (show ((A - k + 1 : ℕ) : ℚ) ≤ (n - k + 1 : ℕ) by exact_mod_cast (by omega))
  have hS' : ∀ z ∈ S', aeval z sl ≠ 0 := by
    intro z hz
    rw [Finset.mem_image] at hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact (not_congr (aeval_monomialLift_iff E x s hs')).mpr (hS x hx).2.1
  have hbound := card_le_mul_pow_of_iteratedRetainedCutFamily hT₀prime
    (d := 1) (fun P hP ↦ (hdim P hP).le) sl (show 1 ≤ 1 by omega)
    hhighDegree hsumPotential ht S'
    (by
      intro z hz
      rw [Finset.mem_image] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      have hxJ : monomialPoint E x ∈ zeroLocus F J := by
        rw [monomialPoint_mem_zeroLocus_comap_iff hE (Ideal.span {g}) x]
        simpa [zeroLocus_span] using (hS x hx).1
      have hxsl : aeval (monomialPoint E x) sl ≠ 0 :=
        (not_congr (aeval_monomialLift_iff E x s hs')).mpr (hS x hx).2.1
      have hhighZero : ∀ f ∈ highCuts', aeval (monomialPoint E x) f = 0 := by
        intro f hf
        simp only [highCuts', List.mem_map, List.mem_attach] at hf
        obtain ⟨q, _, rfl⟩ := hf
        exact (aeval_monomialLift_iff E x q.1 (hhigh' q.1 q.2)).2
          ((hS x hx).2.2 q.1 q.2)
      obtain ⟨P, hP, hxP⟩ := exists_retainedMinimalPrime_of_mem_zeroLocus J sl
        (monomialPoint E x) hxJ hxsl
      obtain ⟨Q, hQ, -, hxQ⟩ :=
        exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus hP hxP hxsl hhighZero
      exact ⟨Q, hQ, hxQ⟩)
    (by
      intro Q hQ
      have hQprime :=
        Ideal.isPrime_of_mem_iteratedRetainedCutFamily hT₀prime sl highCuts' hQ
      have hsQ :=
        Ideal.notMem_of_mem_iteratedRetainedCutFamily hT₀open highCuts' hQ
      obtain ⟨P, hP, hPQ, hhighQ⟩ := Ideal.exists_le_of_mem_iteratedRetainedCutFamily hQ
      have hprincipal := hprincipalData P hP Q hPQ hQprime hsQ hhighQ
      let points := S'.filter fun z ↦ z ∈ zeroLocus F Q
      have hinc₀ : (#points : ℚ) ≤ affineDegree Q *
          ((((Fintype.card (Fin n) - k + 1) * 1 : ℕ) : ℚ) /
            ((A - k + 1 : ℕ) : ℚ)) ^ (affineHilbertPolynomial Q).natDegree := by
        apply card_le_of_agreement_of_subsingleton_sharp (P := Q) sl cuts'
          (b := 1) (A := A) (m := k)
        · intro i
          exact totalDegree_monomialLift_le_one (cuts i) (hcuts' i)
        · exact hkA
        · intro U hU z hz z' hz'
          rcases hz with ⟨hzQ, hzs, hcut⟩
          rcases hz' with ⟨hz'Q, hzs', hcut'⟩
          have hbaseQ : RingHom.ker φ ≤ Q := by
            have hPJ : J ≤ P := ((Ideal.mem_retainedMinimalPrimes).mp hP).1.le
            calc
              RingHom.ker φ ≤ RingHom.ker φ ⊔ Ideal.span {gl} := le_sup_left
              _ = J := hJ_eq.symm
              _ ≤ Q := hPJ.trans hPQ
          have hzbase : z ∈ zeroLocus F (RingHom.ker φ) :=
            zeroLocus_anti_mono hbaseQ hzQ
          have hz'base : z' ∈ zeroLocus F (RingHom.ker φ) :=
            zeroLocus_anti_mono hbaseQ hz'Q
          obtain ⟨x, rfl⟩ := exists_monomialPoint_eq_of_mem_zeroLocus_ker hE hzbase
          obtain ⟨y, rfl⟩ := exists_monomialPoint_eq_of_mem_zeroLocus_ker hE hz'base
          have hK := hprincipal.1
          have hsK := hprincipal.2.1
          have hgK := hprincipal.2.2.1
          have hhighK := hprincipal.2.2.2
          apply congrArg (monomialPoint E)
          apply hunique (Q.map φ.toRingHom) hK hsK hgK hhighK U hU x y
          · intro f hf
            obtain ⟨q, hq, rfl⟩ :=
              (Ideal.mem_map_iff_of_surjective φ.toRingHom hφ).mp hf
            have hzq := hzQ q hq
            rw [aeval_monomialPoint] at hzq
            exact hzq
          · rw [← monomialMap_monomialLift s hs', ← aeval_monomialPoint]
            exact hzs
          · intro f hf
            obtain ⟨q, hq, rfl⟩ :=
              (Ideal.mem_map_iff_of_surjective φ.toRingHom hφ).mp hf
            have hzq := hz'Q q hq
            rw [aeval_monomialPoint] at hzq
            exact hzq
          · rw [← monomialMap_monomialLift s hs', ← aeval_monomialPoint]
            exact hzs'
          · intro i hi
            exact ⟨(aeval_monomialLift_iff E x (cuts i) (hcuts' i)).mp
                (by simpa [cuts'] using (hcut i hi)),
              (aeval_monomialLift_iff E y (cuts i) (hcuts' i)).mp
                (by simpa [cuts'] using (hcut' i hi))⟩
        · intro z hz
          rw [Finset.mem_filter] at hz
          exact ⟨hz.2, hS' z hz.1⟩
        · intro z hz
          rw [Finset.mem_filter] at hz
          obtain ⟨hzS, hzQ⟩ := hz
          rw [Finset.mem_image] at hzS
          obtain ⟨x, hx, rfl⟩ := hzS
          have heq : {i | aeval (monomialPoint E x) (cuts' i) = 0} =
              {i | aeval x (cuts i) = 0} := by
            ext i
            exact aeval_monomialLift_iff E x (cuts i) (hcuts' i)
          rw [heq]
          exact hA x hx
      have hinc : (#points : ℚ) ≤ affineDegree Q *
          t ^ (affineHilbertPolynomial Q).natDegree := by
        simpa only [Fintype.card_fin, Nat.mul_one, t] using hinc₀
      have hcard :
          ((S' : Set (E → F)) ∩ zeroLocus F Q).ncard = points.card := by
        rw [show (S' : Set (E → F)) ∩ zeroLocus F Q =
          (S' : Set (E → F)) ∩ {z | z ∈ zeroLocus F Q} from rfl,
          ncard_coe_inter_setOf]
      rw [← hcard] at hinc
      exact hinc)
  rw [hcardS] at hbound
  simpa only [pow_one, t] using hbound

end MvPolynomial
