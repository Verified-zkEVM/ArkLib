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
  classical
  by_cases hempty : tuples = ∅
  · subst tuples
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  let auxiliary := tuples.image fun P ↦
    chartTuplePullback iota center P (jointInitialJetSeparant center Q)
  obtain ⟨z, _, hinj, havoid⟩ :=
    exists_polynomialTuple_specialization_injective_avoiding_roots
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
  have hvz := positive_jetTotalDegree_of_initialJetSeparant_ne_zero center Qz hsep
  let domainE : Fin n ↪ E := ⟨fun i ↦ iota (domain i), iota.injective.comp domain.injective⟩
  let received : Fin n → E := powerBatchedWord (fun t i ↦ iota (w t i)) z
  have hbound := card_le_of_highTaylorCuts_of_agreement_sharp center Qz hτ hK
    domainE received domainE.injective hkL (by simpa using hLn) jets (by
      intro jet hjetmem
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hjetmem
      exact ⟨(hspec P hP).1, (hspec P hP).2.1,
        fun l hkl hlK ↦ (hspec P hP).2.2.1 ⟨l, hlK⟩ hkl⟩) (by
      intro jet hjetmem
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hjetmem
      have hsubset : (commonCurveAgreementSet domain w P : Set (Fin n)) ⊆
          {i | aeval (chartTupleJet iota center z P)
            (taylorAgreementEquation center Qz K τ (domainE i) (received i)) = 0} := by
        intro i hi
        have hi' : ∀ t, (P t).eval (domain i) = w t i := by
          exact (mem_commonCurveAgreementSet domain w P i).mp (by simpa using hi)
        have hbatch : (powerBatchedPolynomial (fun t ↦ (P t).map iota) z).eval
            (domainE i) = received i := by
          change (powerBatchedPolynomial (fun t ↦ (P t).map iota) z).eval
              (iota (domain i)) = ∑ t, z ^ t.val * iota (w t i)
          rw [powerBatchedPolynomial_eval]
          apply Finset.sum_congr rfl
          intro t _
          congr 1
          rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hi' t]
        have hrec := (hspec P hP).2.2.2
        have heval :
            (rationalTaylorPolynomial center Qz K (chartTupleJet iota center z P)).eval
              (domainE i) = received i := by
          rw [hrec]
          exact hbatch
        exact (taylorAgreementEquation_eq_zero_iff center Qz hτ
          (chartTupleJet iota center z P) (hspec P hP).2.1 (domainE i) (received i)).mpr
            heval
      calc
        L ≤ (commonCurveAgreementSet domain w P).card := (htuples P hP).common
        _ = (commonCurveAgreementSet domain w P : Set (Fin n)).ncard := by simp
        _ ≤ _ := Set.ncard_le_ncard hsubset)
  rw [hcard] at hbound
  have hbound' := by simpa only [Fintype.card_fin] using hbound
  have hvz' : jetTotalDegree Qz ≤ v := by
    exact (jetTotalDegree_map_le (Polynomial.evalRingHom z) Q).trans hjet
  have hB : rationalTaylorCutDegreeBound Qz τ ≤ 1 + τ * (v - 1) := by
    unfold rationalTaylorCutDegreeBound
    exact Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.sub_le_sub_right hvz' 1)) 1
  have hnum : n - k + 1 ≤ n := by omega
  have hnumerator :
      (n - k + 1) * rationalTaylorCutDegreeBound Qz τ ≤
        n * (1 + τ * (v - 1)) := by
    calc
      (n - k + 1) * rationalTaylorCutDegreeBound Qz τ ≤
          n * rationalTaylorCutDegreeBound Qz τ :=
        Nat.mul_le_mul_right _ hnum
      _ ≤ n * (1 + τ * (v - 1)) := Nat.mul_le_mul_left _ hB
  apply hbound'.trans
  apply mul_le_mul
  · exact_mod_cast hvz'
  · apply pow_le_pow_left₀ (by positivity)
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hnumerator
  · positivity
  · positivity

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

end ReedSolomon
