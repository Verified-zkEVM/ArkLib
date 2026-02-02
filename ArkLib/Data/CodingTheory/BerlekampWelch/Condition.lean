/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov
-/
import Init.Data.List.FinRange
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Definitions
import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Matrix.Reflection

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.Polynomial.Interface
import ArkLib.Data.CodingTheory.BerlekampWelch.ElocPoly
import ArkLib.Data.CodingTheory.BerlekampWelch.Sorries

namespace BerlekampWelch

variable {α : Type} {F : Type} [Field F]
         {n e k : ℕ}
         {i : Fin n}
         {j : Fin (2 * e + k)}
         {ωs f : Fin n → F}
         {v : Fin (2 * e + k) → F}
         {E Q : Polynomial F}
         {p : Polynomial F}

structure BerlekampWelchCondition (e k : ℕ) (ωs f : Fin n → F) (E Q : Polynomial F) : Prop where
  cond: ∀ i : Fin n, Q.eval (ωs i) = (f i) * E.eval (ωs i)
  E_natDegree : E.natDegree = e
  E_leadingCoeff : E.coeff e = 1
  Q_natDegree : Q.natDegree ≤ e + k - 1

def Rhs (e : ℕ) (ωs f : Fin n → F) (i : Fin n) : F :=
  let αᵢ := ωs i
  (-(f i) * αᵢ^e)

def BerlekampWelchMatrix
  (e k : ℕ)
  (ωs f : Fin n → F) : Matrix (Fin n) (Fin (2 * e + k)) F :=
  Matrix.of fun i j =>
    let αᵢ := ωs i
    if ↑j < e then -Rhs j.1 ωs f i else -αᵢ^(j - e)

lemma bwm_of_pos [NeZero n] (h : j.1 < e) :
  BerlekampWelchMatrix e k ωs f i j = -Rhs j.1 ωs f i := by
  simp [BerlekampWelchMatrix, h]

lemma bwm_of_neg [NeZero n] (h : e ≤ j.1) :
  BerlekampWelchMatrix e k ωs f i j = -(ωs i)^(j - e) := by
  simp [BerlekampWelchMatrix, h]

@[simp]
lemma Rhs_zero_eq_neg : Rhs 0 ωs f i = -f i := by simp [Rhs]

@[simp]
lemma Rhs_zero_eq_neg' : Rhs 0 ωs f = -f := by ext; simp [Rhs]

def IsBerlekampWelchSolution
  (e k : ℕ)
  (ωs f : Fin n → F)
  (v : Fin (2 * e + k) → F)
  : Prop
  := Matrix.mulVec (BerlekampWelchMatrix e k ωs f) v = Rhs e ωs f

lemma IsBerlekampWelchSolution_def
  : IsBerlekampWelchSolution e k ωs f v
  ↔ Matrix.mulVec (BerlekampWelchMatrix e k ωs f) v = (Rhs e ωs f) := by rfl

lemma linsolve_is_berlekamp_welch_solution
  (h_linsolve : linsolve (BerlekampWelchMatrix e k ωs f) (Rhs e ωs f) = some v)
  : IsBerlekampWelchSolution e k ωs f v := by
  simp [IsBerlekampWelchSolution, linsolve_some h_linsolve]

lemma is_berlekamp_welch_solution_ext
  (h : ∀ i, (Matrix.mulVec (BerlekampWelchMatrix e k ωs f) v) i = -(f i) * (ωs i) ^ e)
  : IsBerlekampWelchSolution e k ωs f v := by
  aesop (add simp [IsBerlekampWelchSolution, Rhs])

@[simp]
lemma Rhs_add_one : Rhs (e + 1) ωs f = fun i ↦ Rhs e ωs f i * ωs i := by
  ext n
  unfold Rhs
  ring

noncomputable def E_and_Q_to_a_solution (e : ℕ) (E Q : Polynomial F) (i : Fin n) : F :=
  if i < e then E.toFinsupp i else Q.toFinsupp (i - e)

@[simp]
lemma E_and_Q_to_a_solution_coeff
  : E_and_Q_to_a_solution e E Q i = if i < e then E.coeff i else Q.coeff (i - e) := rfl

def truncate (p : Polynomial F) (n : ℕ) : Polynomial F
  := ⟨⟨p.1.1 ∩ Finset.range n, fun i ↦ if i < n then p.1.2 i else 0, by aesop⟩⟩

@[simp]
lemma coeff_truncate : (truncate p n).coeff k = if k < n then p.coeff k else 0 := rfl

@[simp]
lemma truncate_zero_eq_zero : (truncate p 0) = 0 := by aesop

@[simp]
lemma natDegree_truncate [φ : NeZero n] : (truncate p n).natDegree < n := by
  have : 0 < n := by rcases φ; omega
  simp only [truncate, Polynomial.natDegree, Polynomial.degree]
  rw [WithBot.unbotD_lt_iff] <;>
  aesop (add simp [Finset.max]) (add safe [(by omega)])

lemma mulVec_BerlekampWelchMatrix_eq :
  (BerlekampWelchMatrix e k ωs f).mulVec v i =
  ∑ x : Fin (2 * e + k), v x * if x < e then f i * ωs i ^ x.1 else -ωs i ^ (x - e) := by
  simp [BerlekampWelchMatrix, Matrix.mulVec, dotProduct, Rhs]
  ring_nf

section

open Polynomial Finset in
private lemma BerlekampWelchCondition_to_Solution [NeZero n]
  (hk_or_e : 1 ≤ k ∨ 1 ≤ e)
  (h : BerlekampWelchCondition e k ωs f E Q)
  : IsBerlekampWelchSolution e k ωs f (E_and_Q_to_a_solution e E Q) := by
  rcases h with ⟨h_cond, h_E_deg, h_E_coeff, h_Q_deg⟩
  refine is_berlekamp_welch_solution_ext fun i ↦ ?p₁
  letI bound := 2 * e + k
  generalize eq : BerlekampWelchMatrix _ _ _ f = M₁
  letI leftσ : Finset _ := {j : Fin bound | j < e}
  letI rightσ : Finset _ := univ (α := Fin bound) \ leftσ
  generalize eq₁ : ∑ j ∈ leftσ, E.coeff j * (ωs i)^j.1 = σ₁
  generalize eq₂ : ∑ j ∈ rightσ, Q.coeff (j - e) * -(ωs i)^(j - e) = σ₂
  calc _ = ∑ j : Fin bound, if ↑j < e
                            then E.coeff ↑j * M₁ i j
                            else Q.coeff (↑j - e) * M₁ i j := by
                              simp [Matrix.mulVec_eq_sum, ite_apply]; rfl
       _ = f i * σ₁ + σ₂ := by
        rw [sum_ite]
        exact eq ▸ eq₁ ▸ eq₂ ▸
          congr_arg₂ _
            (by rw [mul_sum]; exact sum_congr rfl fun _ _ ↦ by rw [
                                                                 bwm_of_pos (by aesop), Rhs
                                                               ]; ring)
            (sum_congr (by aesop) fun j hj ↦ by rw [bwm_of_neg (by aesop)])
  replace eq₁ : eval (ωs i) E - ωs i ^ e * E.coeff e = σ₁ := calc
                _ = ∑ i_1 ∈ range (e + 1), E.coeff i_1 * ωs i ^ i_1 - ωs i ^ e * E.coeff e :=
                  by rw [eval_eq_sum_range, h_E_deg]
                _ = ∑ x ∈ range e, E.coeff x * ωs i ^ x :=
                  by rw [sum_range_succ]; ring
                _ = σ₁ := by rw [←eq₁]; symm
                             apply sum_nbij (i := Fin.val) <;>
                               try intros a _; aesop (add safe (by existsi ⟨a, by omega⟩))
                                                     (add simp Set.InjOn)
  letI δσ := {j | j < e + k}.toFinset
  replace eq₂ : -eval (ωs i) Q = σ₂ := calc
                _              = -∑ j ∈ δσ.attach, ωs i ^ j.1 * Q.coeff j := by
                  rw [
                    eval_eq_sum, neg_inj,
                    sum_eq_of_subset (s := δσ) _ (by simp) fun _ hj ↦
                      by rw [mem_support_iff, ←ite_le_natDegree_coeff _ _ inferInstance] at hj
                         aesop (add safe (by omega)),
                    ←sum_attach
                  ]
                  ac_rfl
                _              = σ₂ := by
                  simp only [
                    ←eq₂, mul_neg, sum_neg_distrib, neg_inj, ←sum_attach (s := rightσ)
                  ]
                  let F (n : {x // x ∈ δσ}) : {x // x ∈ rightσ} :=
                    ⟨⟨n.1 + e, by aesop (add safe (by omega))⟩, by aesop⟩
                  have : Function.Bijective F :=
                    ⟨
                      fun _ ↦ by aesop,
                      fun a ↦ by use ⟨a - e, by aesop (add safe (by omega))⟩; aesop
                    ⟩
                  apply sum_bijective F <;> aesop (add safe [(by omega), (by ring)])
  aesop (add safe (by ring))

open Fin
open Polynomial

variable [DecidableEq F]

def solutionToE (e k : ℕ) (v : Fin (2 * e + k) → F) : Polynomial F :=
  ⟨
    insert e ((Finset.range e).filter (fun x => liftF v x ≠ 0)),
    fun i => if i = e then 1 else if i < e then liftF v i else 0,
    by aesop (add safe forward lt_of_liftF_ne_zero)
  ⟩

lemma solutionToE_eq_polynomialOfCoeffs
  (h : n < e) : (solutionToE e k v).coeff n = (polynomialOfCoeffs v).coeff n := by
  unfold solutionToE polynomialOfCoeffs
  aesop

@[simp]
lemma eval_solutionToE {x : F} :
  eval x (solutionToE e k v) = x ^ e + ∑ y : Fin e, v ⟨y, by omega⟩ * x ^ y.1 := by
  suffices ∑ y ∈ Finset.range e, liftF v y * x ^ y = _ by
    simp [solutionToE, Polynomial.eval_eq_sum, Polynomial.sum_def]
    rw [Finset.sum_ite_of_false, Finset.sum_ite_of_true, Finset.sum_filter_of_ne]
    all_goals aesop
  rw [Finset.sum_bij (i := fun x h ↦ ⟨x, Finset.mem_range.1 h⟩)
                     (g := fun y : Fin e ↦ v ⟨y.1, by omega⟩ * x ^ y.1)] <;>
    aesop (add simp liftF) (add safe (by omega))

@[simp]
lemma coeff_solutionToE :
  (solutionToE e k v).coeff n = if n = e then 1 else if n < e then liftF v n else 0 := rfl

@[simp]
lemma natDegree_solutionToE :
  (solutionToE e k v).natDegree = e := by
  simp [solutionToE, Polynomial.natDegree, Polynomial.degree]
  rw [sup_eq_left.2 ] <;> try simp
  omega

@[simp]
lemma solutionToE_zero_eq_C {v : Fin (2 * 0 + k) → F} :
  solutionToE 0 k v = C (1 : F) := by
  ext (n | n) <;>
  rw [Polynomial.coeff_C] <;> simp

@[simp]
lemma solutionToE_ne_zero : (solutionToE e k v) ≠ 0 := by
  by_cases he : e = 0
  · subst he
    simp
  · have h_deg : 0 < (solutionToE e k v).natDegree := by
      aesop (add safe (by omega))
    intro contr
    simp_all

def solutionToQ (e k : ℕ) (v : Fin (2 * e + k) → F) : Polynomial F :=
  ⟨
    (Finset.range (e + k)).filter (fun x => liftF v (e + x) ≠ 0),
    fun i => if i < e + k then liftF v (e + i) else 0,
    by aesop (add safe (by omega))
  ⟩

@[simp]
lemma solutionToQ_coeff :
  (solutionToQ e k v).coeff n = if n < e + k then liftF v (e + n) else 0 := rfl

@[simp]
lemma natDegree_solutionToQ :
  (solutionToQ e k v).natDegree ≤ e + k - 1 := by
  simp [solutionToQ, Polynomial.natDegree, Polynomial.degree]
  rw [WithBot.unbotD_le_iff] <;>
  aesop (add safe (by omega))

private lemma eval_solutionToQ_aux {i : Fin ((solutionToQ e k v).natDegree + 1)} [NeZero e]
  : e + i < 2 * e + k := by
  have : e ≠ 0 := by aesop
  have := natDegree_solutionToQ (e := e) (k := k) (v := v)
  omega

lemma eval_solutionToQ_cast {x : F} (h : e = 0) :
  eval x (solutionToQ e k v) = ∑ i ∈ Finset.range k, liftF v i * x ^ i := by
  subst h
  simp [solutionToQ]
  rw [eval_eq_sum, sum_def]; simp
  rw [Finset.sum_filter]; simp
  exact Finset.sum_congr rfl (by aesop)

@[simp]
lemma eval_solutionToQ {x : F} :
  eval x (solutionToQ e k v) =
  ∑ i ∈ Finset.range (e + k), liftF v (e + i) * x ^ i := by
  rcases e with _ | e
  · simp [eval_solutionToQ_cast]
  · rw [Polynomial.eval_eq_sum_range'
          (n := (e + 1) + k)
          (Nat.lt_of_le_of_lt natDegree_solutionToQ (by omega))]
    refine Finset.sum_congr rfl fun x hx ↦ by simp at *; rw [liftF_eq_of_lt (by omega)]; omega

@[simp]
lemma eval_solutionToQ_zero {x : F} {v} : eval x (solutionToQ 0 k v) =
                                          ∑ a ∈ Finset.range k, liftF v a * x ^ a := by
  simp [eval_eq_sum, sum_def, solutionToQ, Finset.sum_filter]
  refine Finset.sum_congr rfl (by aesop)

@[simp]
lemma solutionToE_and_Q_E_and_Q_to_a_solution :
  E_and_Q_to_a_solution e (solutionToE e k v) (solutionToQ e k v) = v := by
  ext i
  aesop (add simp liftF) (add safe (by omega))

@[simp]
lemma solutionToQ_zero {v : Fin (2 * 0 + 0) → F} :
  solutionToQ (F := F) 0 0 v = 0 := rfl

private lemma BerlekampWelchCondition_to_Solution' [NeZero n]
  (h : BerlekampWelchCondition e k ωs f (solutionToE e k v) (solutionToQ e k v))
  : IsBerlekampWelchSolution e k ωs f v := by
  by_cases hk : 1 ≤ k
  · rw [←solutionToE_and_Q_E_and_Q_to_a_solution (v := v)]
    exact BerlekampWelchCondition_to_Solution (by aesop) h
  · obtain ⟨rfl⟩ := show k = 0 by omega
    rcases e with _ | e
    · ext i
      simp only [
        Nat.mul_zero, Nat.add_zero, Matrix.mulVec_empty, Pi.zero_apply, Rhs_zero_eq_neg, zero_eq_neg
      ]
      suffices (solutionToQ 0 0 v).eval (ωs i) = 0 by cases h; symm; aesop
      aesop
    · rw [←solutionToE_and_Q_E_and_Q_to_a_solution (v := v)]
      exact BerlekampWelchCondition_to_Solution (by omega) h

omit [DecidableEq F] in
@[simp]
lemma isBerlekampWelchSolution_zero_zero [NeZero n] {v : Fin (2 * 0 + 0) → F} :
  IsBerlekampWelchSolution 0 0 ωs f v ↔ f = 0 := by
  simp [IsBerlekampWelchSolution]

private lemma solution_to_BerlekampWelch_condition {e k : ℕ}
  [NeZero n]
  {ωs f : Fin n → F}
  {v : Fin (2 * e + k) → F}
  (h_sol : IsBerlekampWelchSolution e k ωs f v)
  : BerlekampWelchCondition e k ωs f (solutionToE e k v) (solutionToQ e k v) := by
  constructor <;> try simp
  intros i
  apply congrFun (a := i) at h_sol
  simp [liftF, mulVec_BerlekampWelchMatrix_eq] at h_sol ⊢
  apply_fun (-1 * ·) using (by simp [Function.Injective]); simp only [neg_one_mul]
  rw [
    ←neg_mul, mul_add, ←Rhs.eq_def, ←h_sol,
    Finset.sum_dite_of_true (by simp; omega), Finset.sum_ite
  ]
  generalize_proofs p₁ p₂
  set sum₁ := -∑ x, v ⟨e + x.1, p₁ x⟩ * ωs i ^ x.1 with eq₁
  set sum₂ := ∑ x with x.1 < e, v x * (f i * ωs i ^ x.1) with eq₂
  set sum₃ := ∑ x with ¬x.1 < e, -(v x * ωs i ^ (x - e)) with eq₃
  set sum₄ := -f i * ∑ y, v ⟨y.1, p₂ y⟩ * ωs i ^ y.1 with eq₄
  suffices sum₂ = -sum₄ ∧ sum₁ = sum₃ by rw [this.1, this.2]; ring
  refine ⟨?p₃, ?p₄⟩
  · simp [eq₂, eq₄]
    rw [Finset.mul_sum]
    apply Finset.sum_bij' (i := fun a ha ↦ ⟨a.1, by simp at ha; omega⟩)
                          (j := fun a _ ↦ ⟨a.1, by omega⟩) <;> try simp <;> (intros; ring)
  · simp [eq₁, eq₃]
    apply Finset.sum_bij' (i := fun ⟨a, ha₁⟩ _ ↦ ⟨a + e, by simp at ha₁; omega⟩)
                          (j := fun ⟨a, _⟩ ha₂ ↦ ⟨a - e, by simp at ha₂ ⊢; omega⟩) <;> try simp
    case p₄.right_neg => aesop
    case h => intros; left; ring_nf

theorem BerlekampWelchCondition_iff_Solution {e k : ℕ} [NeZero n]
  {ωs f : Fin n → F} {v : Fin (2 * e + k) → F}
  :
  IsBerlekampWelchSolution e k ωs f v
  ↔
  (BerlekampWelchCondition e k ωs f (solutionToE e k v) (solutionToQ e k v)) :=
  ⟨solution_to_BerlekampWelch_condition, BerlekampWelchCondition_to_Solution'⟩

lemma linsolve_to_BerlekampWelch_condition {e k : ℕ}
  [NeZero n]
  {ωs f : Fin n → F}
  {v : Fin (2 * e + k) → F}
  (h_sol : linsolve (BerlekampWelchMatrix e k ωs f) (Rhs e ωs f) = some v)
  : BerlekampWelchCondition e k ωs f (solutionToE e k v) (solutionToQ e k v) :=
  solution_to_BerlekampWelch_condition (linsolve_is_berlekamp_welch_solution h_sol)

end

lemma BerlekampWelch_E_ne_zero {e k : ℕ}
  {ωs f : Fin n → F}
  {E Q : Polynomial F}
  (h_cond : BerlekampWelchCondition e k ωs f E Q)
  : E ≠ 0 := by
  have h_deg := h_cond.E_natDegree
  have h_leadCoeff := h_cond.E_leadingCoeff
  aesop

section

open Polynomial

variable [DecidableEq F]

lemma BerlekampWelch_Q_ne_zero {e k : ℕ}
  [NeZero n]
  {ωs f : Fin n → F}
  {E Q : Polynomial F}
  (h_bw : BerlekampWelchCondition e k ωs f E Q)
  (h_dist : e < Δ₀(f, 0))
  (h_inj : Function.Injective ωs)
  : Q ≠ 0 := fun contr ↦
  have h_cond := h_bw.cond
  let S : Finset (Fin n) := {i | ¬f i = 0}
  by replace h_dist : e < S.card := by simpa [hammingDist]
     simp [contr] at h_cond
     have h_card := Polynomial.card_le_degree_of_subset_roots
       (Z := Finset.image ωs S) (p := E)
       (fun _ hx ↦ by
          obtain ⟨i, _⟩ := by simpa using hx
          specialize (h_cond i); aesop (add simp (BerlekampWelch_E_ne_zero h_bw)))
     rw [Finset.card_image_of_injective _ h_inj, h_bw.E_natDegree] at h_card
     omega

lemma solutionToQ_ne_zero {e k : ℕ}
  [NeZero n]
  {ωs f : Fin n → F}
  {v : Fin (2 * e + k) → F}
  (h_dist : e < Δ₀(f, 0))
  (h_sol : IsBerlekampWelchSolution e k ωs f v)
  (h_inj : Function.Injective ωs)
  : solutionToQ e k v ≠ 0 :=
    BerlekampWelch_Q_ne_zero
      (solution_to_BerlekampWelch_condition h_sol)
      h_dist
      h_inj

lemma E_and_Q_unique
  [NeZero n]
  {e k : ℕ}
  {E Q E' Q' : Polynomial F}
  {ωs f : Fin n → F}
  (he : 2 * e < n - k + 1)
  (hk_n : k ≤ n)
  (h_Q : Q ≠ 0)
  (h_Q' : Q' ≠ 0)
  (h_inj : Function.Injective ωs)
  (h_bw₁ : BerlekampWelchCondition e k ωs f E Q)
  (h_bw₂ : BerlekampWelchCondition e k ωs f E' Q')
: E * Q' = E' * Q := by
  let R := E * Q' - E' * Q
  have hr_deg : R.natDegree ≤ 2 * e + k - 1 := by
    simp [R]
    apply Nat.le_trans (natDegree_add_le _ _)
    simp [
      natDegree_mul
        (BerlekampWelch_E_ne_zero h_bw₁)
        h_Q',
      natDegree_neg,
      natDegree_mul
        (BerlekampWelch_E_ne_zero h_bw₂)
        h_Q
      ]
    aesop (add safe cases BerlekampWelchCondition) (add safe (by omega))
  by_cases hr : R = 0
  · rw [←add_zero (E' * Q), ←hr]; ring
  · let roots := Multiset.ofList <| (List.finRange n).map ωs
    have hsub : (⟨roots, by simp [roots]; rw [List.nodup_map_iff h_inj]
                            exact List.nodup_finRange _⟩ : Finset F).val ⊆ R.roots := fun _ _ ↦ by
      aesop (add safe cases BerlekampWelchCondition) (add safe (by ring))
    have hcard := card_le_degree_of_subset_roots hsub
    simp at *
    cases k <;> cases e <;> aesop (add safe (by omega))

end

end BerlekampWelch
