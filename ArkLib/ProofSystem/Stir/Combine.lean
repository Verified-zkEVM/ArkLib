/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter, Poulami Das (Least Authority)
-/

import Mathlib.Tactic.FieldSimp

import ArkLib.Data.CodingTheory.ProximityGap
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation
import ArkLib.ProofSystem.Stir.ProximityBound

/-! Section 4.5 from STIR [ACFY24] -/

open BigOperators Finset NNReal

namespace Combine
variable {m : ℕ}
         {F : Type*} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type*} [Fintype ι]

/-- Fact 4.10
  Geometric series formula in a field, for a unit `r : F`. -/
lemma geometric_sum_units {F : Type*} [Field F] [DecidableEq F] {r : Fˣ} {a : ℕ} :
  ∑ j ∈ range (a + 1), (r ^ j : F) =
    if r = 1 then (a + 1 : F)
    else (1 - r ^ (a + 1)) / (1 - r) := by
  by_cases h : r = 1
  · rw [h]
    simp
  · simp only [h, ↓reduceIte]
    rw [geom_sum_eq]
    · have {a b : F} : a / b = -a / -b := by
        field_simp
      rw [@this _ (1 - ↑r)]
      simp
    · simp only [ne_eq, Units.val_eq_one]
      exact h

def ri (dstar : ℕ) (degs : Fin m → ℕ) (r : F) (i : Fin m) : F :=
          match i.1 with
          | 0 => 1
          | .succ i' =>
            let exp := i' + ∑ j < i, (dstar - degs j)
            r ^ exp

/-- Definition 4.11.1
    Combine(d*, r, (f_0, d_0), …, (f_{m-1}, d_{m-1}))(x)
      := sum_{i < m} r_i * f_i(x) * ( sum_{l < (d* - d_i + 1)} (r * φ(x))^l ) -/
def combine
  (φ : ι ↪ F) (dstar : ℕ) (r : F) (fs : Fin m → ι → F) (degs : Fin m → ℕ) (x : ι) : F :=
    ∑ i, (ri dstar degs r i) * (fs i x) * (∑ l ∈ range (dstar - degs i + 1), ((φ x) * r)^l)

/-- Definition 4.11.2
    Combine(d*, r, (f_0, d_0), …, (f_{m-1}, d_{m-1}))(x) :=
      if (r * φ(x)) = 1 then sum_{i < m} r_i * f_i(x) * (dstar - degree + 1)
      else sum_{i < m} r_i * f_i(x) * (1 - r * φ(x)^(dstar - degree + 1)) / (1 - r * φ(x))
-/
lemma combine_eq_cases {F ι : Type*} [Field F] [DecidableEq F]
  (φ : ι ↪ F) (dstar : ℕ) (r : F) (fs : Fin m → ι → F) (degs : Fin m → ℕ)
    (hdegs : ∀ i, degs i ≤ dstar) (φ_neq_0 : ∀ i, φ i ≠ 0) :
  combine φ dstar r fs degs =
    fun x =>
      let q := φ x * r
      if q ≠ 1
      then ∑ i, (ri dstar degs r i) * (fs i x) * (1 - q^(dstar - degs i + 1)) / (1 - q)
      else ∑ i, (ri dstar degs r i) * (fs i x) *  (dstar - degs i + 1) := by
  ext x
  unfold combine
  simp only
  by_cases h : r = 0
  · aesop
  · by_cases h' : φ x * r = 1
    · aesop
    · simp only [ne_eq, h', not_false_eq_true, ↓reduceIte]
      congr
      ext i
      have :
        ri dstar degs r i * fs i x * (1 - (φ x * r) ^ (dstar - degs i + 1)) / (1 - φ x * r) =
          (ri dstar degs r i * fs i x) * ((1 - (φ x * r) ^ (dstar - degs i + 1)) / (1 - φ x * r))
        := by
          field_simp
      rw [this]
      congr
      have := GroupWithZero.eq_zero_or_unit (φ x * r)
      simp only [mul_eq_zero, φ_neq_0 x, h, or_self, false_or] at this
      rcases this with ⟨r', this⟩
      rw [this, geometric_sum_units]
      have : r' ≠ 1 := by
        aesop
      simp [this]

-- def DegCor

/-- Definition 4.12.1
    DegCor(d*, r, f, degree)(x) := f(x) * ( sum_{ l < d* - d + 1 } (r * φ(x))^l ) -/
def degCor
  (φ : ι ↪ F) (dstar degree : ℕ) (r : F) (f : ι → F) (x : ι) : F :=
    f x * ∑ l ∈ range (dstar - degree + 1), ((φ x) * r) ^ l

/-- Definition 4.12.2
    DegCor(d*, r, f, d)(x) := f(x) * conditionalExp(x) -/

lemma degreeCor_eq {F : Type u_1} [Field F] [DecidableEq F] {ι : Type u_2} (φ : ι ↪ F)
  (dstar degree : ℕ) (r : F) (f : ι → F) (hd : degree ≤ dstar) (x : ι) :
  let q := φ x * r
  degCor φ dstar degree r f x =
    if q ≠ 1
    then f x * (1 - q^(dstar - degree + 1)) / (1 - q)
    else f x * (dstar - degree + 1) := by
  intros q
  unfold degCor
  by_cases h : q = 1
  · simp only [h, ne_eq, not_true_eq_false, ↓reduceIte]
    congr
    rcases GroupWithZero.eq_zero_or_unit (φ x * r) with h' | h'
    · aesop
    · dsimp [q] at h
      rcases h' with ⟨r', h'⟩
      rw [h', geometric_sum_units]
      aesop
  · simp only [ne_eq, h, not_false_eq_true, ↓reduceIte]
    have :
      f x * (1 - q ^ (dstar - degree + 1)) / (1 - q) =
        f x * ((1 - q ^ (dstar - degree + 1)) / (1 - q)) := by
      field_simp
    rw [this]
    congr
    rcases GroupWithZero.eq_zero_or_unit (φ x * r) with h' | h'
    · aesop
    · rcases h' with ⟨r', h'⟩
      rw [h', geometric_sum_units]
      aesop


variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι] [Nonempty ι]

open LinearCode ProbabilityTheory ReedSolomon STIR in
/-- Lemma 4.13
  Let `dstar` be the target degree, `f₁,...,f_{m-1} : ι → F`,
  `0 < degs₁,...,degs_{m-1} < dstar` be degrees and
  `δ ∈ (0, min{(1-BStar(ρ)), (1-ρ-1/|ι|)})` be a distance parameter, then
      Pr_{r ← F} [δᵣ(Combine(dstar,r,(f₁,degs₁),...,(fₘ,degsₘ)))]
                   > err' (dstar, ρ, δ, m * (dstar + 1) - ∑ i degsᵢ) -/
lemma combine_theorem
  {φ : ι ↪ F} {dstar m degree : ℕ}
  (fs : Fin m → ι → F) (degs : Fin m → ℕ) (hdegs : ∀ i, degs i ≤ dstar)
  (δ : ℝ) (hδPos : δ > 0)
  (hδLt : δ < (min (1 - Bstar (rate (code φ degree)))
                   (1 - (rate (code φ degree)) - 1 / Fintype.card ι)))
  (hProb : Pr_{ let r ← $ᵖ F}[δᵣ((combine φ dstar r fs degs), (code φ dstar)) ≤ δ] >
    ENNReal.ofReal (proximityError F dstar (rate (code φ degree)) δ (m * (dstar + 1) - ∑ i, degs i))) :
      correlatedAgreement (code φ degree) ⟨δ, by linarith⟩ fs
      := by sorry

end Combine
