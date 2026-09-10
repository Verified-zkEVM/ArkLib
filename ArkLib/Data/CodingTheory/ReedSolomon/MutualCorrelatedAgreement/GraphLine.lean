/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Agreement
public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Algebra.Polynomial.BigOperators
/-!
# Recognizing graph lines from a common agreement sample

A common sample of `k` distinct evaluation points determines two degree-`< k`
polynomials over the base field.  Over every field extension, any degree-`< k`
polynomial agreeing with the corresponding affine received word on that sample is
the affine combination of those two polynomials.  For a fixed pair of polynomials,
at most one challenge per position can create an agreement which is not common to
the pair.
-/

@[expose] public section

namespace ReedSolomon

noncomputable section

open Polynomial

/-- The evaluation-domain embedding induced by a field extension. -/
def mappedDomain {F E : Type*} [Field F] [Field E] {n : ℕ}
    (domain : Fin n ↪ F) (iota : F →+* E) : Fin n ↪ E :=
  domain.trans ⟨iota, iota.injective⟩

private lemma eval_map_at_mappedDomain {F E : Type*} [Field F] [Field E] {n : ℕ}
    (domain : Fin n ↪ F) (iota : F →+* E) (P : F[X]) (i : Fin n) :
    (P.map iota).eval (mappedDomain domain iota i) = iota (P.eval (domain i)) := by
  simp [mappedDomain, Polynomial.eval_map]

/-- Interpolation on `k` common positions recognizes the entire affine graph line,
uniformly over every extension field. -/
theorem exists_graphLine_polynomials_of_sample
    {F : Type*} [Field F] {n k : ℕ} (domain : Fin n ↪ F)
    (f g : Fin n → F) (sample : Finset (Fin n)) (hsampleCard : sample.card = k) :
    ∃ F₀ G₀ : F[X], F₀.degree < k ∧ G₀.degree < k ∧
      (∀ i ∈ sample, F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i) ∧
      ∀ {E : Type*} [Field E] (iota : F →+* E) (z : E) (P : E[X]),
        P.degree < k →
        (∀ i ∈ sample,
          P.eval (mappedDomain domain iota i) = iota (f i) + z * iota (g i)) →
        P = F₀.map iota + Polynomial.C z * G₀.map iota := by
  let F₀ : F[X] := Lagrange.interpolate sample domain f
  let G₀ : F[X] := Lagrange.interpolate sample domain g
  have hsampleInjective : Set.InjOn domain sample := domain.injective.injOn
  have hF₀Degree : F₀.degree < k := by
    simpa [F₀, hsampleCard] using Lagrange.degree_interpolate_lt f hsampleInjective
  have hG₀Degree : G₀.degree < k := by
    simpa [G₀, hsampleCard] using Lagrange.degree_interpolate_lt g hsampleInjective
  refine ⟨F₀, G₀, hF₀Degree, hG₀Degree, ?_, ?_⟩
  · intro i hi
    exact ⟨Lagrange.eval_interpolate_at_node f hsampleInjective hi,
      Lagrange.eval_interpolate_at_node g hsampleInjective hi⟩
  · intro E _ iota z P hPDegree hPAgreement
    have hmapInjective : Set.InjOn (mappedDomain domain iota) sample :=
      (mappedDomain domain iota).injective.injOn
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq sample hmapInjective
    · simpa [hsampleCard] using hPDegree
    · have hFmap : (F₀.map iota).degree < k :=
        Polynomial.degree_map_le.trans_lt hF₀Degree
      have hGmap : (G₀.map iota).degree < k :=
        Polynomial.degree_map_le.trans_lt hG₀Degree
      have hsum : (F₀.map iota + Polynomial.C z * G₀.map iota).degree < k := by
        apply (Polynomial.degree_add_le _ _).trans_lt
        apply max_lt hFmap
        rw [← Polynomial.smul_eq_C_mul]
        exact (Polynomial.degree_smul_le _ _).trans_lt hGmap
      simpa [hsampleCard] using hsum
    · intro i hi
      rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
        eval_map_at_mappedDomain, eval_map_at_mappedDomain,
        Lagrange.eval_interpolate_at_node f hsampleInjective hi,
        Lagrange.eval_interpolate_at_node g hsampleInjective hi]
      exact hPAgreement i hi

private def accidentalFactor {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (F₀ G₀ : F[X]) (i : Fin n) : F[X] :=
  if F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i then 1
  else Polynomial.C (F₀.eval (domain i) - f i) +
    Polynomial.X * Polynomial.C (G₀.eval (domain i) - g i)

private def accidentalPolynomial {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (F₀ G₀ : F[X]) : F[X] :=
  ∏ i, accidentalFactor domain f g F₀ G₀ i

private lemma accidentalFactor_ne_zero {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (F₀ G₀ : F[X]) (i : Fin n) :
    accidentalFactor domain f g F₀ G₀ i ≠ 0 := by
  by_cases hi : F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i
  · simp [accidentalFactor, hi]
  · simp only [accidentalFactor, hi, if_false]
    intro hzero
    have hconst := congrArg (Polynomial.eval 0) hzero
    have hlinear := congrArg (Polynomial.eval 1) hzero
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X, zero_mul, add_zero, Polynomial.eval_zero] at hconst
    simp only [Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X, one_mul, Polynomial.eval_zero] at hlinear
    apply hi
    refine ⟨sub_eq_zero.mp hconst, ?_⟩
    rw [hconst, zero_add] at hlinear
    exact sub_eq_zero.mp hlinear

private lemma accidentalPolynomial_ne_zero {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (F₀ G₀ : F[X]) :
    accidentalPolynomial domain f g F₀ G₀ ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  exact accidentalFactor_ne_zero domain f g F₀ G₀ i

private lemma accidentalPolynomial_natDegree_le {F : Type*} [Field F] [DecidableEq F] {n : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (F₀ G₀ : F[X]) :
    (accidentalPolynomial domain f g F₀ G₀).natDegree ≤
      n - (commonPolynomialAgreementSet domain f g F₀ G₀).card := by
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    ∑ i, (accidentalFactor domain f g F₀ G₀ i).natDegree ≤
        ∑ i : Fin n, if F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i
          then 0 else 1 := by
      apply Finset.sum_le_sum
      intro i _
      simp only [accidentalFactor]
      split_ifs
      · simp
      · exact (Polynomial.natDegree_add_le _ _).trans <| by
          exact max_le (by simp) <| Polynomial.natDegree_mul_le.trans (by simp)
    _ = n - (commonPolynomialAgreementSet domain f g F₀ G₀).card := by
      simp only [Finset.sum_ite, Finset.sum_const_zero, zero_add,
        Finset.sum_const, smul_eq_mul, mul_one]
      have h := Finset.card_filter_add_card_filter_not
        (s := Finset.univ) (p := fun i : Fin n ↦
          F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i)
      simp only [Finset.card_univ, Fintype.card_fin] at h
      unfold commonPolynomialAgreementSet
      omega

/-- Each position outside the common agreement set contributes at most one exceptional
challenge. Outside their union, affine agreement equals common agreement exactly. -/
theorem exists_exceptional_graphLine_challenges
    {F E : Type*} [Field F] [Field E] [DecidableEq F] [DecidableEq E]
    {n : ℕ} (domain : Fin n ↪ F)
    (f g : Fin n → F) (F₀ G₀ : F[X]) (iota : F →+* E) :
    ∃ exceptional : Finset E,
      exceptional.card ≤ n - (commonPolynomialAgreementSet domain f g F₀ G₀).card ∧
      ∀ z ∉ exceptional,
      polynomialAgreementSet (mappedDomain domain iota)
          (fun i ↦ iota (f i) + z * iota (g i))
          (F₀.map iota + Polynomial.C z * G₀.map iota) =
        commonPolynomialAgreementSet domain f g F₀ G₀ := by
  classical
  let baseAccidental := accidentalPolynomial domain f g F₀ G₀
  let extensionAccidental : E[X] := baseAccidental.map iota
  have hbaseNe : baseAccidental ≠ 0 :=
    accidentalPolynomial_ne_zero domain f g F₀ G₀
  have hextensionNe : extensionAccidental ≠ 0 :=
    Polynomial.map_ne_zero hbaseNe
  let exceptional := extensionAccidental.roots.toFinset
  refine ⟨exceptional, ?_, ?_⟩
  · calc
      exceptional.card ≤ extensionAccidental.natDegree :=
        (Multiset.toFinset_card_le extensionAccidental.roots).trans
          (Polynomial.card_roots' extensionAccidental)
      _ ≤ baseAccidental.natDegree := Polynomial.natDegree_map_le
      _ ≤ n - (commonPolynomialAgreementSet domain f g F₀ G₀).card :=
        accidentalPolynomial_natDegree_le domain f g F₀ G₀
  · intro z hz
    have haccidentalEval : extensionAccidental.eval z ≠ 0 := by
      intro heval
      have hzroots : z ∈ extensionAccidental.roots :=
        (Polynomial.mem_roots hextensionNe).2 heval
      exact hz (by simpa [exceptional] using hzroots)
    ext i
    simp only [polynomialAgreementSet, commonPolynomialAgreementSet, Finset.mem_filter,
      Finset.mem_univ, true_and, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, eval_map_at_mappedDomain]
    constructor
    · intro hAgreement
      by_contra hCommon
      have hfactorEval :
          ((accidentalFactor domain f g F₀ G₀ i).map iota).eval z = 0 := by
        simp only [accidentalFactor, hCommon, if_false, Polynomial.map_add,
          Polynomial.map_C, Polynomial.map_mul, Polynomial.map_X, Polynomial.eval_add,
          Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
        rw [show iota (F₀.eval (domain i) - f i) +
              z * iota (G₀.eval (domain i) - g i) =
            (iota (F₀.eval (domain i)) + z * iota (G₀.eval (domain i))) -
              (iota (f i) + z * iota (g i)) by
              simp only [map_sub]; ring]
        exact sub_eq_zero.mpr hAgreement
      apply haccidentalEval
      change ((∏ j, accidentalFactor domain f g F₀ G₀ j).map iota).eval z = 0
      rw [Polynomial.map_prod, Polynomial.eval_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) hfactorEval
    · rintro ⟨hF, hG⟩
      rw [hF, hG]

/-- The graph-line recognition and accidental-agreement conclusions with a common
choice of base-field constituent polynomials. -/
theorem exists_graphLine_polynomials_and_exceptional_challenges
    {F : Type*} [Field F] [DecidableEq F] {n k : ℕ} (domain : Fin n ↪ F)
    (f g : Fin n → F) (sample : Finset (Fin n)) (hsampleCard : sample.card = k) :
    ∃ F₀ G₀ : F[X], F₀.degree < k ∧ G₀.degree < k ∧
      (∀ i ∈ sample, F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i) ∧
      (∀ {E : Type*} [Field E] (iota : F →+* E) (z : E) (P : E[X]),
        P.degree < k →
        (∀ i ∈ sample,
          P.eval (mappedDomain domain iota i) = iota (f i) + z * iota (g i)) →
        P = F₀.map iota + Polynomial.C z * G₀.map iota) ∧
      ∀ {E : Type*} [Field E] [DecidableEq E] (iota : F →+* E),
        ∃ exceptional : Finset E, exceptional.card ≤ n ∧ ∀ z ∉ exceptional,
          polynomialAgreementSet (mappedDomain domain iota)
              (fun i ↦ iota (f i) + z * iota (g i))
              (F₀.map iota + Polynomial.C z * G₀.map iota) =
            commonPolynomialAgreementSet domain f g F₀ G₀ := by
  obtain ⟨F₀, G₀, hF₀, hG₀, hsample, hrecognize⟩ :=
    exists_graphLine_polynomials_of_sample domain f g sample hsampleCard
  refine ⟨F₀, G₀, hF₀, hG₀, hsample, hrecognize, ?_⟩
  intro E _ _ iota
  obtain ⟨exceptional, hcard, hagree⟩ :=
    exists_exceptional_graphLine_challenges domain f g F₀ G₀ iota
  exact ⟨exceptional, hcard.trans (Nat.sub_le _ _), hagree⟩

end

end ReedSolomon
