/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.Combinatorics.Enumerative.InclusionExclusion
public import Mathlib.RingTheory.Polynomial.HilbertPoly

/-!
# Eventual polynomial counting outside finitely many monomial cones

For finitely many forbidden exponent vectors, inclusion--exclusion expresses the
number of exponent vectors of bounded total degree outside all their upper cones
as an eventual rational polynomial.
-/

@[expose] public section

namespace MonomialHilbertCounting

noncomputable section

open scoped BigOperators
open Polynomial

/-- Exponent vectors of total degree at most `N`. -/
def degreeBall (σ : Type*) [Fintype σ] [DecidableEq σ] (N : ℕ) : Finset (σ →₀ ℕ) :=
  (Finset.range (N + 1)).biUnion fun t ↦
    (Finset.univ : Finset σ).finsuppAntidiag t

@[simp]
theorem mem_degreeBall {σ : Type*} [Fintype σ] [DecidableEq σ]
    {N : ℕ} {e : σ →₀ ℕ} : e ∈ degreeBall σ N ↔ Finsupp.degree e ≤ N := by
  simp only [degreeBall, Finset.mem_biUnion, Finset.mem_range,
    Finset.mem_finsuppAntidiag']
  rw [Finsupp.degree_eq_sum]
  constructor
  · rintro ⟨t, ht, heq, _⟩
    rw [Finsupp.sum_fintype _ _ (by simp)] at heq
    omega
  · intro he
    refine ⟨∑ i, e i, by omega, ?_, Finset.subset_univ _⟩
    rw [Finsupp.sum_fintype _ _ (by simp)]

theorem card_degreeBall (σ : Type*) [Fintype σ] [DecidableEq σ] (N : ℕ) :
    (degreeBall σ N).card = (N + Fintype.card σ).choose (Fintype.card σ) := by
  rw [degreeBall, Finset.card_biUnion]
  · simp only [Finset.card_finsuppAntidiag_nat_eq_multichoose]
    exact Nat.sum_range_multichoose N (Fintype.card σ)
  · intro a ha b hb hab
    change Disjoint ((Finset.univ : Finset σ).finsuppAntidiag a)
      ((Finset.univ : Finset σ).finsuppAntidiag b)
    rw [Finset.disjoint_left]
    intro e hea heb
    have heaDegree := (Finset.mem_finsuppAntidiag'.mp hea).1
    have hebDegree := (Finset.mem_finsuppAntidiag'.mp heb).1
    exact hab (heaDegree.symm.trans hebDegree)

/-- The part of a degree ball lying above a fixed exponent vector. -/
def upperConeInBall (σ : Type*) [Fintype σ] [DecidableEq σ]
    (b : σ →₀ ℕ) (N : ℕ) : Finset (σ →₀ ℕ) :=
  (degreeBall σ N).filter fun e ↦ b ≤ e

@[simp]
theorem mem_upperConeInBall {σ : Type*} [Fintype σ] [DecidableEq σ]
    {b e : σ →₀ ℕ} {N : ℕ} :
    e ∈ upperConeInBall σ b N ↔ Finsupp.degree e ≤ N ∧ b ≤ e := by
  simp [upperConeInBall]

theorem card_upperConeInBall {σ : Type*} [Fintype σ] [DecidableEq σ]
    (b : σ →₀ ℕ) (N : ℕ) (hbN : Finsupp.degree b ≤ N) :
    (upperConeInBall σ b N).card =
      (N - Finsupp.degree b + Fintype.card σ).choose (Fintype.card σ) := by
  calc
    (upperConeInBall σ b N).card = (degreeBall σ (N - Finsupp.degree b)).card := by
      apply Finset.card_bij' (fun e _ ↦ e - b) (fun u _ ↦ u + b)
      · intro e he
        rw [mem_degreeBall]
        have heData := mem_upperConeInBall.mp he
        rw [Finsupp.degree_eq_sum]
        change ∑ i, (e i - b i) ≤ N - Finsupp.degree b
        rw [Finset.sum_tsub_distrib Finset.univ]
        · rw [← Finsupp.degree_eq_sum, ← Finsupp.degree_eq_sum]
          exact Nat.sub_le_sub_right heData.1 _
        · intro i _
          exact heData.2 i
      · intro u hu
        rw [mem_upperConeInBall]
        constructor
        · rw [Finsupp.degree_eq_sum]
          simp_rw [Finsupp.add_apply]
          rw [Finset.sum_add_distrib,
            ← Finsupp.degree_eq_sum, ← Finsupp.degree_eq_sum]
          exact (Nat.add_le_add_right (mem_degreeBall.mp hu) _).trans_eq
            (Nat.sub_add_cancel hbN)
        · intro i
          simp only [Finsupp.add_apply]
          exact Nat.le_add_left _ _
      · intro e he
        apply Finsupp.ext
        intro i
        simp only [Finsupp.add_apply]
        have hi : b i ≤ e i := (mem_upperConeInBall.mp he).2 i
        exact Nat.sub_add_cancel hi
      · intro u hu
        apply Finsupp.ext
        intro i
        change u i + b i - b i = u i
        omega
    _ = _ := card_degreeBall σ _

/-- The coordinatewise supremum of a finite collection of exponents. -/
def forbiddenSup {σ : Type*} [DecidableEq σ] (T : Finset (σ →₀ ℕ)) : σ →₀ ℕ :=
  T.sup id

@[simp]
theorem forbiddenSup_le_iff {σ : Type*} [DecidableEq σ]
    {T : Finset (σ →₀ ℕ)} {e : σ →₀ ℕ} :
    forbiddenSup T ≤ e ↔ ∀ b ∈ T, b ≤ e := by
  exact Finset.sup_le_iff

/-- Exponents in the degree ball which avoid every forbidden upper cone. -/
def standardExponentFinset (σ : Type*) [Fintype σ] [DecidableEq σ]
    (B : Finset (σ →₀ ℕ)) (N : ℕ) : Finset (σ →₀ ℕ) :=
  (degreeBall σ N).filter fun e ↦ ∀ b ∈ B, ¬b ≤ e

@[simp]
theorem mem_standardExponentFinset {σ : Type*} [Fintype σ] [DecidableEq σ]
    {B : Finset (σ →₀ ℕ)} {N : ℕ} {e : σ →₀ ℕ} :
    e ∈ standardExponentFinset σ B N ↔
      Finsupp.degree e ≤ N ∧ ∀ b ∈ B, ¬b ≤ e := by
  simp [standardExponentFinset]

private lemma mem_finset_inf {I α : Type*} [Fintype α]
    [DecidableEq α] (s : Finset I) (S : I → Finset α) (x : α) :
    x ∈ s.inf S ↔ ∀ i ∈ s, x ∈ S i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih => simp [Finset.inf_insert, ih]

private theorem standardExponent_card_inclusion_exclusion
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (B : Finset (σ →₀ ℕ)) (N : ℕ) :
    ((standardExponentFinset σ B N).card : ℤ) =
      ∑ T ∈ B.powerset, (-1 : ℤ) ^ T.card *
        (upperConeInBall σ (forbiddenSup T) N).card := by
  classical
  let ballType := {e // e ∈ degreeBall σ N}
  let cones : (σ →₀ ℕ) → Finset ballType := fun b ↦
    Finset.univ.filter fun e ↦ b ≤ e.1
  have hleft :
      (B.inf fun b ↦ (cones b)ᶜ).card = (standardExponentFinset σ B N).card := by
    apply Finset.card_bij (fun e _ ↦ e.1)
    · intro e he
      rw [mem_standardExponentFinset]
      refine ⟨mem_degreeBall.mp e.2, ?_⟩
      have he' := (mem_finset_inf B (fun b ↦ (cones b)ᶜ) e).mp he
      intro b hb hbe
      have := he' b hb
      simp [cones, hbe] at this
    · intro e₁ he₁ e₂ he₂ heq
      exact Subtype.ext heq
    · intro e he
      refine ⟨⟨e, mem_degreeBall.mpr (mem_standardExponentFinset.mp he).1⟩, ?_, rfl⟩
      apply (mem_finset_inf B (fun b ↦ (cones b)ᶜ) _).mpr
      intro b hb
      simp [cones, (mem_standardExponentFinset.mp he).2 b hb]
  have hintersection : ∀ T ∈ B.powerset,
      (T.inf cones).card = (upperConeInBall σ (forbiddenSup T) N).card := by
    intro T hT
    apply Finset.card_bij (fun e _ ↦ e.1)
    · intro e he
      rw [mem_upperConeInBall]
      refine ⟨mem_degreeBall.mp e.2, ?_⟩
      rw [forbiddenSup_le_iff]
      intro b hb
      have he' := (mem_finset_inf T cones e).mp he b hb
      simpa [cones] using he'
    · intro e₁ he₁ e₂ he₂ heq
      exact Subtype.ext heq
    · intro e he
      refine ⟨⟨e, mem_degreeBall.mpr (mem_upperConeInBall.mp he).1⟩, ?_, rfl⟩
      apply (mem_finset_inf T cones _).mpr
      intro b hb
      simp [cones, (forbiddenSup_le_iff.mp (mem_upperConeInBall.mp he).2) b hb]
  rw [← hleft, Finset.inclusion_exclusion_card_inf_compl]
  apply Finset.sum_congr rfl
  intro T hT
  rw [hintersection T hT]

/-- A threshold above every coordinatewise-supremum shift occurring in
inclusion--exclusion. -/
def forbiddenThreshold {σ : Type*} [DecidableEq σ]
    (B : Finset (σ →₀ ℕ)) : ℕ :=
  B.powerset.sup fun T ↦ Finsupp.degree (forbiddenSup T)

theorem forbiddenSup_degree_le_threshold {σ : Type*} [DecidableEq σ]
    {B T : Finset (σ →₀ ℕ)} (hT : T ∈ B.powerset) :
    Finsupp.degree (forbiddenSup T) ≤ forbiddenThreshold B := by
  exact Finset.le_sup (f := fun T ↦ Finsupp.degree (forbiddenSup T)) hT

/-- The alternating simplex-counting polynomial attached to a finite forbidden
monomial basis. -/
def countingPolynomial (σ : Type*) [Fintype σ] [DecidableEq σ]
    (B : Finset (σ →₀ ℕ)) : ℚ[X] :=
  ∑ T ∈ B.powerset, ((-1 : ℚ) ^ T.card) •
    Polynomial.preHilbertPoly ℚ (Fintype.card σ) (Finsupp.degree (forbiddenSup T))

theorem countingPolynomial_natDegree_le
    (σ : Type*) [Fintype σ] [DecidableEq σ]
    (B : Finset (σ →₀ ℕ)) :
    (countingPolynomial σ B).natDegree ≤ Fintype.card σ := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro T hT
  exact (Polynomial.natDegree_smul_le _ _).trans_eq
    (Polynomial.natDegree_preHilbertPoly ℚ (Fintype.card σ)
      (Finsupp.degree (forbiddenSup T)))

/-- For every `N` beyond the explicit finite shift threshold, the counting
polynomial evaluates to the number of degree-bounded exponents outside all
forbidden upper cones. -/
theorem countingPolynomial_eval_eq_card
    (σ : Type*) [Fintype σ] [DecidableEq σ]
    (B : Finset (σ →₀ ℕ)) (N : ℕ) (hN : forbiddenThreshold B ≤ N) :
    (countingPolynomial σ B).eval (N : ℚ) =
      ((standardExponentFinset σ B N).card : ℚ) := by
  have hinc := standardExponent_card_inclusion_exclusion B N
  have hincRat : ((standardExponentFinset σ B N).card : ℚ) =
      ∑ T ∈ B.powerset, ((-1 : ℚ) ^ T.card) *
        (upperConeInBall σ (forbiddenSup T) N).card := by
    exact_mod_cast hinc
  rw [countingPolynomial, Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_smul, smul_eq_mul]
  rw [hincRat]
  apply Finset.sum_congr rfl
  intro T hT
  congr 1
  have hshift : Finsupp.degree (forbiddenSup T) ≤ N :=
    (forbiddenSup_degree_le_threshold hT).trans hN
  rw [Polynomial.preHilbertPoly_eq_choose_sub_add ℚ _ hshift,
    card_upperConeInBall _ _ hshift]

/-- Eventual polynomiality of the standard-exponent count, with degree at most
the number of variables and an explicit sufficient threshold. -/
theorem exists_eventual_countingPolynomial
    (σ : Type*) [Fintype σ] [DecidableEq σ]
    (B : Finset (σ →₀ ℕ)) :
    ∃ P : ℚ[X], P.natDegree ≤ Fintype.card σ ∧
      ∀ N ≥ forbiddenThreshold B,
        P.eval (N : ℚ) = ((standardExponentFinset σ B N).card : ℚ) := by
  exact ⟨countingPolynomial σ B, countingPolynomial_natDegree_le σ B,
    countingPolynomial_eval_eq_card σ B⟩

/-- The standard exponents as a set, independent of any chosen finite-type or
decidable-equality instances. -/
def standardExponentSet {σ : Type*} (B : Finset (σ →₀ ℕ)) (N : ℕ) : Set (σ →₀ ℕ) :=
  {e | Finsupp.degree e ≤ N ∧ ∀ b ∈ B, ¬b ≤ e}

theorem standardExponentSet_ncard_eq_finset_card
    (σ : Type*) [Fintype σ] [DecidableEq σ]
    (B : Finset (σ →₀ ℕ)) (N : ℕ) :
    (standardExponentSet B N).ncard = (standardExponentFinset σ B N).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext e
  simp [standardExponentSet]

/-- Instance-independent form: for every finite variable type, the forbidden
monomial count agrees eventually with a rational polynomial of degree at most
`Nat.card σ`. -/
theorem exists_eventual_standardExponent_countingPolynomial
    (σ : Type*) [Finite σ] (B : Finset (σ →₀ ℕ)) :
    ∃ P : ℚ[X], P.natDegree ≤ Nat.card σ ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀,
      P.eval (N : ℚ) = ((standardExponentSet B N).ncard : ℚ) := by
  classical
  let _ : Fintype σ := Fintype.ofFinite σ
  refine ⟨countingPolynomial σ B, ?_, forbiddenThreshold B, ?_⟩
  · rw [Nat.card_eq_fintype_card]
    exact countingPolynomial_natDegree_le σ B
  · intro N hN
    rw [countingPolynomial_eval_eq_card σ B N hN,
      standardExponentSet_ncard_eq_finset_card]

end

end MonomialHilbertCounting
