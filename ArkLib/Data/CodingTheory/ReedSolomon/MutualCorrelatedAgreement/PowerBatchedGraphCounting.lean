/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedAdmissibility
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TupleSpecialization
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedIncidence
public import ArkLib.Data.Polynomial.Differential.TaylorChartIncidence
public import ArkLib.Data.Polynomial.Differential.BaseChange
public import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement
public import ArkLib.Data.Polynomial.Differential.TaylorChart

/-!
# Counting admissible polynomial tuple graphs

Polynomial tuples of bounded degree with enough common agreements lie in a finite interpolation
family. Admissible tuple graphs inject into regular high-cut Taylor jets at one common challenge,
so the sharp incidence bound controls every finite family of them.

## Main statements

* `polynomialTupleFamily` and `mem_polynomialTupleFamily_iff`: the family of sample interpolants
  and its characterization by degree and common agreement.
* `admissibleChartTupleFamilyAtExponent` and
  `admissibleChartTupleFamilyAtExponent_card_le`: the finite admissible family and its sharp
  cardinality bound.
* `admissibleChartTuples_card_le_of_exponent`: a cardinality bound for any finite family of
  admissible tuple graphs.
* `admissibleChartTupleFamilyAtExponent_card_le_dimensionSensitive` and
  `admissibleChartTuples_card_le_dimensionSensitive_of_exponent`: sharper bounds using the
  dimension-sensitive evaluation product.
* `exists_regularHighCutJetImage_of_admissibleChartTuples`: a regular high-cut jet image for a
  finite family of admissible tuple graphs.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial MvPolynomial PolynomialDifferential
open scoped BigOperators

noncomputable section

namespace ReedSolomon

variable {F E : Type*} [Field F] [Field E] {n r ℓ : ℕ}

/-- The finite family of sample interpolants satisfying the chart identities at exponent `τ`. -/
def admissibleChartTupleFamilyAtExponent [DecidableEq F]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (K k L τ : ℕ) : Finset (Fin (ℓ + 1) → F[X]) := by
  classical
  exact (polynomialTupleFamily domain w k).filter
    (IsAdmissibleChartTupleAtExponent domain w iota center Q K k L τ)

/-- When `k ≤ L`, membership in the finite family is equivalent to chart admissibility. -/
theorem mem_admissibleChartTupleFamilyAtExponent_iff [DecidableEq F]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (K k L τ : ℕ) (hkL : k ≤ L) (P : Fin (ℓ + 1) → F[X]) :
    P ∈ admissibleChartTupleFamilyAtExponent domain w iota center Q K k L τ ↔
      IsAdmissibleChartTupleAtExponent domain w iota center Q K k L τ P := by
  classical
  simp only [admissibleChartTupleFamilyAtExponent, Finset.mem_filter]
  constructor
  · exact And.right
  · intro hP
    exact ⟨mem_polynomialTupleFamily_of_commonAgreement domain w P k hP.degree
      (hkL.trans hP.common), hP⟩

private theorem positive_jetTotalDegree_of_initialJetSeparant_ne_zero (center : E)
    (Q : DifferentialPolynomial E r) (hS : initialJetSeparant center Q ≠ 0) :
    0 < jetTotalDegree Q := by
  by_contra! h
  have hdeg : (initialJetEquation center Q).totalDegree = 0 :=
    Nat.eq_zero_of_le_zero ((totalDegree_initialJetEquation_le center Q).trans h)
  have hC := totalDegree_eq_zero_iff_eq_C.mp hdeg
  have hd := pderiv_initialJetEquation center Q (Fin.last r)
  rw [hC, pderiv_C] at hd
  exact hS hd.symm

/-- A finite family of admissible tuple graphs injects into regular high-cut Taylor jets, and
each image jet has at least `L` agreement equations. -/
theorem exists_regularHighCutJetImage_of_admissibleChartTuples
    [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ) (hkK : k ≤ K)
    (tuples : Finset (Fin (ℓ + 1) → F[X]))
    (htuples : ∀ P ∈ tuples,
      IsAdmissibleChartTupleAtExponent domain w iota center Q K k L τ P) :
    ∃ z : E, ∃ jets : Finset (Fin (r + 1) → E),
      (∀ jet ∈ jets, ∃ P ∈ tuples, jet = chartTupleJet iota center z P) ∧
      (∀ P ∈ tuples, chartTupleJet iota center z P ∈ jets) ∧
      Set.InjOn (chartTupleJet (r := r) iota center z)
        (tuples : Set (Fin (ℓ + 1) → F[X])) ∧
      jets.card = tuples.card ∧
      (∀ jet ∈ jets,
        aeval jet (initialJetEquation center (MvPolynomial.map (Polynomial.evalRingHom z) Q)) =
          0 ∧
        aeval jet
          (initialJetSeparant center (MvPolynomial.map (Polynomial.evalRingHom z) Q)) ≠ 0 ∧
        ∀ l : {l : Fin K // k ≤ l.val},
          aeval jet (commonTaylorNumerator center
            (MvPolynomial.map (Polynomial.evalRingHom z) Q) τ l.val) = 0) ∧
      (∀ jet ∈ jets, L ≤
        {i | aeval jet
          (taylorAgreementEquation center
            (MvPolynomial.map (Polynomial.evalRingHom z) Q) K τ (iota (domain i))
            (powerBatchedWord (fun t j ↦ iota (w t j)) z i)) = 0}.ncard) := by
  classical
  let auxiliary := tuples.image fun P ↦
    chartTuplePullback iota center P (jointInitialJetSeparant center Q)
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
  refine ⟨z, jets, ?_, ?_, hjetinj, hcard, ?_, ?_⟩
  · intro jet hjetmem
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hjetmem
    exact ⟨P, hP, rfl⟩
  · intro P hP
    exact Finset.mem_image.mpr ⟨P, hP, rfl⟩
  · intro jet hjetmem
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hjetmem
    exact ⟨(hspec P hP).1, (hspec P hP).2.1,
      fun l ↦ (hspec P hP).2.2.1 l.val l.property⟩
  · intro jet hjetmem
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hjetmem
    have hsubset : (commonCurveAgreementSet domain w P : Set (Fin n)) ⊆
        {i | aeval (chartTupleJet iota center z P)
          (taylorAgreementEquation center Qz K τ (iota (domain i))
            (powerBatchedWord (fun t j ↦ iota (w t j)) z i)) = 0} := by
      intro i hi
      have hi' : ∀ t, (P t).eval (domain i) = w t i :=
        (mem_commonCurveAgreementSet domain w P i).mp hi
      have hbatch :
          (powerBatchedPolynomial (fun t ↦ (P t).map iota) z).eval
            (iota (domain i)) = powerBatchedWord (fun t j ↦ iota (w t j)) z i := by
        change (powerBatchedPolynomial (fun t ↦ (P t).map iota) z).eval
            (iota (domain i)) = ∑ t, z ^ t.val * iota (w t i)
        rw [powerBatchedPolynomial_eval]
        apply Finset.sum_congr rfl
        intro t _
        congr 1
        rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hi' t]
      have heval :
          (rationalTaylorPolynomial center Qz K (chartTupleJet iota center z P)).eval
            (iota (domain i)) = powerBatchedWord (fun t j ↦ iota (w t j)) z i := by
        rw [(hspec P hP).2.2.2]
        exact hbatch
      exact (taylorAgreementEquation_eq_zero_iff center Qz hτ
        (chartTupleJet iota center z P) (hspec P hP).2.1 (iota (domain i))
        (powerBatchedWord (fun t j ↦ iota (w t j)) z i)).mpr heval
    calc
      L ≤ (commonCurveAgreementSet domain w P).card := (htuples P hP).common
      _ = (commonCurveAgreementSet domain w P : Set (Fin n)).ncard :=
        (Set.ncard_coe_finset _).symm
      _ ≤ _ := Set.ncard_le_ncard hsubset

/-- Every finite family of admissible tuples at exponent `τ` satisfies the bound using the
dimension-sensitive evaluation product. -/
theorem admissibleChartTuples_card_le_dimensionSensitive_of_exponent
    [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L v τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (hK : r < K) (hkK : k ≤ K) (hkL : k ≤ L) (hLn : L ≤ n)
    (hjet : jetTotalDegree Q ≤ v)
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
  obtain ⟨z, jets, _, _, _, hcard, hS, hA⟩ :=
    exists_regularHighCutJetImage_of_admissibleChartTuples
    domain w iota center Q K k L τ hτ hkK tuples htuples
  let Qz := MvPolynomial.map (Polynomial.evalRingHom z) Q
  let domainE : Fin n ↪ E :=
    ⟨fun i ↦ iota (domain i), iota.injective.comp domain.injective⟩
  let received : Fin n → E := powerBatchedWord (fun t i ↦ iota (w t i)) z
  have hbound := finite_regularHighCutJets_card_le_dimensionSensitive_of_exponent
    center Qz K k τ hτ hK hkK domainE received hkL hLn jets hS hA
  rw [hcard] at hbound
  apply hbound.trans
  have hvz' : jetTotalDegree Qz ≤ v := (jetTotalDegree_map_le _ Q).trans hjet
  have hB : rationalTaylorCutDegreeBound Qz τ ≤ 1 + τ * (v - 1) := by
    unfold rationalTaylorCutDegreeBound
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hvz' 1)) 1
  apply mul_le_mul_of_nonneg_right _
    (dimensionSensitiveIncidenceProduct_nonneg n L k 1 r)
  apply mul_le_mul
  · exact_mod_cast hvz'
  · exact pow_le_pow_left₀ (by positivity) (by exact_mod_cast hB) r
  · positivity
  · positivity

/-- Every finite family of admissible tuple graphs satisfies the sharp Taylor-chart bound when
the message degree bound is positive. -/
theorem admissibleChartTuples_card_le_of_exponent [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L v τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLn : L ≤ n) (hjet : jetTotalDegree Q ≤ v)
    (tuples : Finset (Fin (ℓ + 1) → F[X]))
    (htuples : ∀ P ∈ tuples,
      IsAdmissibleChartTupleAtExponent domain w iota center Q K k L τ P) :
    (tuples.card : ℚ) ≤ (v : ℚ) *
      ((((n * (1 + τ * (v - 1)) : ℕ) : ℚ) /
        ((L - k + 1 : ℕ) : ℚ)) ^ r) := by
  let B := 1 + τ * (v - 1)
  have hbound := admissibleChartTuples_card_le_dimensionSensitive_of_exponent
    domain w iota center Q K k L v τ hτ hK hkK hkL hLn hjet tuples htuples
  have hproduct := dimensionSensitiveIncidenceProduct_le_first_pow n L k r hkL hLn
  have hnumerator : n - k + 1 ≤ n := by omega
  have hratio :
      (B : ℚ) * (((n - k + 1 : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)) ≤
        (((n * B : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have hnat : B * (n - k + 1) ≤ n * B := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_right B hnumerator
    exact_mod_cast hnat
  calc
    (tuples.card : ℚ) ≤
        (v : ℚ) * (B : ℚ) ^ r * dimensionSensitiveIncidenceProduct n L k 1 r :=
      hbound
    _ ≤ (v : ℚ) * (B : ℚ) ^ r *
        (((n - k + 1 : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)) ^ r :=
      mul_le_mul_of_nonneg_left hproduct (by positivity)
    _ = (v : ℚ) *
        ((B : ℚ) * (((n - k + 1 : ℕ) : ℚ) /
          ((L - k + 1 : ℕ) : ℚ))) ^ r := by
      rw [mul_pow]
      ring
    _ ≤ (v : ℚ) *
        ((((n * B : ℕ) : ℚ) / ((L - k + 1 : ℕ) : ℚ)) ^ r) :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) hratio r) (by positivity)
    _ = (v : ℚ) *
        ((((n * (1 + τ * (v - 1)) : ℕ) : ℚ) /
          ((L - k + 1 : ℕ) : ℚ)) ^ r) := by
      simp only [B]
/-- The complete finite family of admissible tuples satisfies the sharp Taylor-chart bound. -/
theorem admissibleChartTupleFamilyAtExponent_card_le [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L v τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (hK : r < K) (hkK : k ≤ K) (hk : 0 < k) (hkL : k ≤ L)
    (hLn : L ≤ n) (hjet : jetTotalDegree Q ≤ v) :
    ((admissibleChartTupleFamilyAtExponent domain w iota center Q K k L τ).card : ℚ) ≤
      (v : ℚ) *
        ((((n * (1 + τ * (v - 1)) : ℕ) : ℚ) /
          ((L - k + 1 : ℕ) : ℚ)) ^ r) := by
  apply admissibleChartTuples_card_le_of_exponent domain w iota center Q K k L v τ hτ
    hK hkK hk hkL hLn hjet
  intro P hP
  exact (mem_admissibleChartTupleFamilyAtExponent_iff
    domain w iota center Q K k L τ hkL P).mp hP

/-- The complete finite family of admissible tuples at exponent `τ` satisfies the bound using the
dimension-sensitive evaluation product. -/
theorem admissibleChartTupleFamilyAtExponent_card_le_dimensionSensitive
    [DecidableEq F] [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k L v τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (hK : r < K) (hkK : k ≤ K) (hkL : k ≤ L) (hLn : L ≤ n)
    (hjet : jetTotalDegree Q ≤ v) :
    ((admissibleChartTupleFamilyAtExponent domain w iota center Q K k L τ).card : ℚ) ≤
      (v : ℚ) * (1 + τ * (v - 1) : ℕ) ^ r *
        dimensionSensitiveIncidenceProduct n L k 1 r := by
  apply admissibleChartTuples_card_le_dimensionSensitive_of_exponent
    domain w iota center Q K k L v τ hτ hK hkK hkL hLn hjet
  intro P hP
  exact (mem_admissibleChartTupleFamilyAtExponent_iff
    domain w iota center Q K k L τ hkL P).mp hP

end ReedSolomon
