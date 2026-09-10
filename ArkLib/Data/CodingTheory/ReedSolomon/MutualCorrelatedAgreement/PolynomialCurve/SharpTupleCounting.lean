/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.GraphCounting
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.SharpPairCounting
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.ComponentDimension
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.ProductBounds
/-!
# Sharp counting of admissible polynomial tuples

A generic batching challenge injects a finite admissible tuple family into one ordinary Taylor
chart. Applying the dimension-sensitive chart count retains the evaluation product

```text
prod_{j<r} (n-k+j+1) / (L-k+j+1),
```

while the Taylor cut degree is charged once through the high-cut component potential.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n r ℓ : ℕ}

private theorem jetDegree_pos_of_initialSeparant_ne_zero_sharpTuple (center : E)
    (Q : DifferentialPolynomial E r) (hS : initialJetSeparant center Q ≠ 0) :
    0 < Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) := by
  by_contra! h
  have hdeg : (initialJetEquation center Q).totalDegree = 0 :=
    Nat.eq_zero_of_le_zero ((totalDegree_initialJetEquation_le center Q).trans h)
  have hC := totalDegree_eq_zero_iff_eq_C.mp hdeg
  have hd := pderiv_initialJetEquation center Q (Fin.last r)
  rw [hC, pderiv_C] at hd
  exact hS hd.symm

/-- Product-form incidence for a finite set of regular high-cut jets.  The nonlinear Taylor cuts
are charged through the retained-family Bezout potential, while agreement cuts contribute the
dimension-sensitive evaluation product. -/
theorem finite_regularHighCutJets_card_le_dimensionSensitive_of_exponent
    [IsAlgClosed E]
    (center : E) (Q : DifferentialPolynomial E r) (K k τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hK : r < K) (hkK : k ≤ K)
    (hsep : initialJetSeparant center Q ≠ 0)
    (hv : 0 < Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)))
    {n A : ℕ} (domain : Fin n ↪ E) (received : Fin n → E)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (hproduct : ∀ d ≤ r, dimensionSensitiveIncidenceProduct n A k 1 d ≤
      dimensionSensitiveIncidenceProduct n A k 1 r)
    (S : Finset (Fin (r + 1) → E))
    (hS : ∀ jet ∈ S,
      aeval jet (initialJetEquation center Q) = 0 ∧
      aeval jet (initialJetSeparant center Q) ≠ 0 ∧
      ∀ l : {l : Fin K // k ≤ l.val},
        aeval jet (commonTaylorNumerator center Q K l.val (τ := τ)) = 0)
    (hA : ∀ jet ∈ S, A ≤ (agreementIndices
      (fun i ↦ taylorAgreementEquation center Q K (domain i) (received i) (τ := τ))
        jet).card) :
    (S.card : ℚ) ≤
      (Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) : ℕ) *
        (rationalTaylorCutDegreeBound Q K (τ := τ) : ℚ) ^ r *
          dimensionSensitiveIncidenceProduct n A k 1 r := by
  classical
  let B := rationalTaylorCutDegreeBound Q K (τ := τ)
  let T := highTaylorPrimeFamily center Q K k (τ := τ)
  let cuts : Fin n → MvPolynomial (Fin (r + 1)) E := fun i ↦
    taylorAgreementEquation center Q K (domain i) (received i) (τ := τ)
  have hinit : initialJetEquation center Q ≠ 0 :=
    initialJetEquation_ne_zero_of_separant_ne_zero center Q hsep
  have hspec := highTaylorPrimeFamily_spec (F := E) (E := E) center Q K k (τ := τ)
  have hcoverNat : S.card ≤ ∑ P ∈ T, (componentPoints S P).card := by
    calc
      S.card ≤ (T.biUnion fun P ↦ componentPoints S P).card := by
        apply Finset.card_le_card
        intro jet hjet
        obtain ⟨P, hPT, hjetP⟩ := hspec.2 jet
          (hS jet hjet).1 (hS jet hjet).2.1 (hS jet hjet).2.2
        exact Finset.mem_biUnion.mpr ⟨P, hPT, by
          rw [mem_componentPoints]
          exact ⟨hjet, hjetP⟩⟩
      _ ≤ ∑ P ∈ T, (componentPoints S P).card := Finset.card_biUnion_le
  have hcomponent : ∀ P ∈ T, ((componentPoints S P).card : ℚ) ≤
      affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree *
        dimensionSensitiveIncidenceProduct n A k 1 r := by
    intro P hPT
    have hPspec := hspec.1 P hPT
    have hbound := affineAgreementIncidence_bound_dimensionSensitive hPspec.1 hPspec.2.1
      cuts (fun i ↦ totalDegree_taylorAgreementEquation_le_of_exponent
        center Q hv K τ hτ _ _) hkA hAn
      (fun J hPJ hJ hsJ hdJ ↦ chart_dimensionSensitive_component_of_exponent
        center Q K k n τ hτ hK hkK J hJ hsJ
          (fun l hl ↦ hPJ (hPspec.2.2 (by
            rw [highTaylorCutsIdeal]
            exact Ideal.subset_span ⟨⟨l, hl⟩, rfl⟩))) domain received hdJ)
      (componentPoints S P)
      (fun jet hjet ↦ by
        rw [mem_componentPoints] at hjet
        exact ⟨hjet.2, (hS jet hjet.1).2.1⟩)
      (fun jet hjet ↦ by rw [mem_componentPoints] at hjet; exact hA jet hjet.1)
    refine hbound.trans ?_
    rw [dimensionSensitiveIncidenceProduct_eq_pow_mul]
    calc
      affineDegree P * ((B : ℚ) ^ (hilbertPolynomial P).natDegree *
          dimensionSensitiveIncidenceProduct n A k 1 (hilbertPolynomial P).natDegree) =
        (affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree) *
          dimensionSensitiveIncidenceProduct n A k 1 (hilbertPolynomial P).natDegree := by ring
      _ ≤ (affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree) *
          dimensionSensitiveIncidenceProduct n A k 1 r :=
        mul_le_mul_of_nonneg_left (hproduct _
          (highTaylorPrimeFamily_hilbertPolynomial_natDegree_le
            center Q K k (τ := τ) hinit hPT))
          (mul_nonneg (affineDegree_nonneg P) (by positivity))
      _ = affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree *
          dimensionSensitiveIncidenceProduct n A k 1 r := rfl
  have hpotential := sum_highTaylorPrimeFamily_affineDegree_mul_pow_le_of_exponent
    center Q hsep hv K k τ hτ
  calc
    (S.card : ℚ) ≤ ∑ P ∈ T, ((componentPoints S P).card : ℚ) := by
      exact_mod_cast hcoverNat
    _ ≤ ∑ P ∈ T, affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree *
        dimensionSensitiveIncidenceProduct n A k 1 r := Finset.sum_le_sum hcomponent
    _ = (∑ P ∈ T, affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree) *
        dimensionSensitiveIncidenceProduct n A k 1 r := by rw [Finset.sum_mul]
    _ ≤ ((Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) : ℕ) *
        (B : ℚ) ^ r) * dimensionSensitiveIncidenceProduct n A k 1 r :=
      mul_le_mul_of_nonneg_right hpotential
        (dimensionSensitiveIncidenceProduct_nonneg n A k 1 r)
    _ = _ := rfl

/-- Any finite family of admissible polynomial tuples at exponent `τ` obeys the
dimension-sensitive evaluation product after one common regular batching specialization. -/
theorem admissibleChartTuples_card_le_dimensionSensitive_of_exponent
    [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L v τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (hK : r < K) (hkK : k ≤ K) (_hk : 0 < k) (hkL : k ≤ L) (hLn : L ≤ n)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (tuples : Finset (Fin (ℓ + 1) → F[X]))
    (htuples : ∀ P ∈ tuples,
      IsAdmissibleChartTupleAtExponent domain w iota center Q K k L τ P) :
    (tuples.card : ℚ) ≤ (v : ℚ) * (1 + τ * (v - 1) : ℕ) ^ r *
      dimensionSensitiveIncidenceProduct n L k 1 r := by
  classical
  by_cases hempty : tuples = ∅
  · subst tuples
    simp only [Finset.card_empty, Nat.cast_zero]
    exact mul_nonneg (mul_nonneg (by positivity) (by positivity))
      (dimensionSensitiveIncidenceProduct_nonneg n L k 1 r)
  let auxiliary := tuples.image fun P ↦
    chartTuplePullback iota center P (symbolicSourceSeparant center Q)
  obtain ⟨z, _, hinj, havoid⟩ :=
    exists_polynomialTuple_specialization_injective_avoiding_roots (ℓ := ℓ)
      iota tuples ∅ auxiliary (by
      intro R hR
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hR
      exact (htuples P hP).regular)
  let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
  let jets : Finset (Fin (r + 1) → E) := tuples.image (chartTupleJet iota center z)
  have hspec (P : Fin (ℓ + 1) → F[X]) (hP : P ∈ tuples) :=
    (htuples P hP).specialize hτ hkK z
      (havoid _ (Finset.mem_image.mpr ⟨P, hP, rfl⟩))
  have hjetinj : Set.InjOn (chartTupleJet (r := r) iota center z)
      (tuples : Set (Fin (ℓ + 1) → F[X])) := by
    intro P hP R hR heq
    apply hinj hP hR
    change powerBatchedPolynomial (fun t ↦ (P t).map iota) z =
      powerBatchedPolynomial (fun t ↦ (R t).map iota) z
    rw [← (hspec P hP).2.2.2, ← (hspec R hR).2.2.2, heq]
  have hcard : jets.card = tuples.card := Finset.card_image_of_injOn hjetinj
  obtain ⟨P₀, hP₀⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
  have hsep : initialJetSeparant center Qz ≠ 0 := by
    intro hz
    exact (hspec P₀ hP₀).2.1 (by rw [hz]; simp)
  have hvz := jetDegree_pos_of_initialSeparant_ne_zero_sharpTuple center Qz hsep
  let domainE : Fin n ↪ E := mappedDomain domain iota
  let received : Fin n → E := powerBatchedWord (fun t i ↦ iota (w t i)) z
  have hbound := finite_regularHighCutJets_card_le_dimensionSensitive_of_exponent
    center Qz K k τ hτ hK hkK hsep hvz
    domainE received hkL hLn
    (fun d hd ↦ dimensionSensitiveIncidenceProduct_mono_dimension
      n L k 1 d r hLn Nat.zero_lt_one hd) jets (by
      intro jet hjetmem
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hjetmem
      exact ⟨(hspec P hP).1, (hspec P hP).2.1,
        fun l ↦ (hspec P hP).2.2.1 l.val l.property⟩) (by
      intro jet hjetmem
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hjetmem
      apply (htuples P hP).common.trans
      apply Finset.card_le_card
      intro i hi
      rw [mem_agreementIndices, taylorAgreementEquation_eq_zero_iff_of_exponent
        _ _ _ τ hτ _ (hspec P hP).2.1, (hspec P hP).2.2.2]
      have hi' : ∀ t, (P t).eval (domain i) = w t i := by
        simpa only [commonCurveAgreementSet, Finset.mem_filter, Finset.mem_univ,
          true_and] using hi
      change (powerBatchedPolynomial (fun t ↦ (P t).map iota) z).eval
          (iota (domain i)) = ∑ t, z ^ t.val * iota (w t i)
      rw [powerBatchedPolynomial_eval]
      apply Finset.sum_congr rfl
      intro t _
      congr 1
      rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hi' t])
  rw [hcard] at hbound
  apply hbound.trans
  have hvle : Qz.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v := by
    apply Finset.sup_le_iff.mpr
    intro m hm
    exact (le_weightedTotalDegree _
      (support_map_subset (Polynomial.evalRingHom z) Q hm)).trans hjet
  have hB : rationalTaylorCutDegreeBound Qz K (τ := τ) ≤ 1 + τ * (v - 1) := by
    unfold rationalTaylorCutDegreeBound
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hvle 1)) 1
  apply mul_le_mul_of_nonneg_right _
    (dimensionSensitiveIncidenceProduct_nonneg n L k 1 r)
  apply mul_le_mul
  · exact_mod_cast hvle
  · exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hB) r
  · positivity
  · positivity

/-- The complete finite admissible tuple family at exponent `τ` obeys the
dimension-sensitive evaluation product. -/
theorem admissibleChartTupleFamilyAtExponent_card_le_dimensionSensitive
    [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L v τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L) (hLn : L ≤ n)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v) :
    ((admissibleChartTupleFamilyAtExponent domain w iota center Q K k L τ).card : ℚ) ≤
      (v : ℚ) * (1 + τ * (v - 1) : ℕ) ^ r *
        dimensionSensitiveIncidenceProduct n L k 1 r := by
  apply admissibleChartTuples_card_le_dimensionSensitive_of_exponent
    domain w iota center Q K k L v τ hτ
    hK hkK hk hkL hLn hjet
  intro P hP
  exact (mem_admissibleChartTupleFamilyAtExponent_iff
    domain w iota center Q K k L τ hkL P).mp hP

end ReedSolomon
