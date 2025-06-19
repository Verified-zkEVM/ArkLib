/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter, Poulami Das (Least Authority)
-/

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
lemma geometric_sum_units {r :  Units F} {a : ℕ} :
  ∑ j : Fin (a + 1), (r ^ ( j : ℕ ) : F) =
    if r = 1 then (a + 1 : F)
    else (1 - r ^ (a + 1)) / (1 - r) := by sorry

/--Coefficients r_i as used in the definition of Combine,
    for i < m, r_i := r^{i - 1 + sum_{j < i}(d* - d_j)} -/
def ri (dstar : ℕ) (degs : Fin m → ℕ) (r : F) : Fin m → F :=
  fun i =>
    let ipred := Nat.pred i.val
    let exp := ipred + ∑ j < i, (dstar - degs j)
    r ^ exp

/-- Definition 4.11.1
    Combine(d*, r, (f_0, d_0), …, (f_{m-1}, d_{m-1}))(x)
      := sum_{i < m} r_i * f_i(x) * ( sum_{l < (d* - d_i + 1)} (r * φ(x))^l ) -/
def combineInterm
  {φ : ι ↪ F} (dstar : ℕ) (r : F) (fs : Fin m → ι → F) (degs : Fin m → ℕ)
  (hdegs : ∀ i, degs i ≤ dstar) : ι → F :=
    fun x =>
        ∑ i, (ri dstar degs r i) * (fs i x) * (∑ l < (dstar - degs i + 1), (r * (φ x))^l)

/--if (r * φ(x)) = 1, then (dstar - degree + 1)
   else (1 - r * φ(x)^(dstar - degree + 1)) / (1 - r * φ(x))-/
def conditionalExp
  (φ : ι ↪ F) (dstar : ℕ) (degree : ℕ) (r : F) : ι → F :=
  fun x =>
    let q := r * (φ x)
    if q = 1 then (dstar - degree + 1 : F)
    else (1 - q^(dstar - degree + 1)) / (1 - q)

/-- Definition 4.11.2
    Combine(d*, r, (f_0, d_0), …, (f_{m-1}, d_{m-1}))(x) :=
      sum_{i < m} r_i * f_i(x) * conditionExp(dstar, degsᵢ, r) -/
def combineFinal
  (φ : ι ↪ F) (dstar : ℕ) (r : F) (fs : Fin m → ι → F)
  (degs : Fin m → ℕ) (hdegs : ∀ i, degs i ≤ dstar) : ι → F :=
    fun x =>
       ∑ i, (ri dstar degs r i) * (fs i x) * conditionalExp φ dstar (degs i) r x

/-- Definition 4.12.1
    DegCor(d*, r, f, degree)(x) := f(x) * ( sum_{ l < d* - d + 1 } (r * φ(x))^l ) -/
def degreeCorrInterm
  {φ : ι ↪ F} (dstar degree : ℕ) (r : F) (f : ι → F) (hd : degree ≤ dstar) : ι → F :=
    fun x =>
      let geom := ∑ l < (dstar - degree + 1), (r * (φ x)) ^ l
      f x * geom

/-- Definition 4.12.2
    DegCor(d*, r, f, d)(x) := f(x) * conditionalExp(x) -/
def degreeCorrFinal
{φ : ι ↪ F} (dstar degree : ℕ) (r : F) (f : ι → F) (hd : degree ≤ dstar) : ι → F :=
  fun x =>
    f x * conditionalExp φ dstar degree r x

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι] [Nonempty ι]

open LinearCode ProbabilityTheory ReedSolomon

/--Lemma 4.13
  Let `dstar` be the target degree, `f₁,...,f_{m-1} : ι → F`,
  `0 < degs₁,...,degs_{m-1} < dstar` be degrees and
  `δ ∈ (0, min{(1-BStar(ρ)), (1-ρ-1/|ι|)})` be a distance parameter, then
      Pr_{r ← F} [δᵣ(Combine(dstar,r,(f₁,degs₁),...,(fₘ,degsₘ)))]
                   > err' (dstar, ρ, δ, m * (dstar + 1) - ∑ i degsᵢ)
  -/
lemma combine
  {φ : ι ↪ F} {dstar m degree : ℕ}
  (fs : Fin m → ι → F) (degs : Fin m → ℕ) (hdegs : ∀ i, degs i ≤ dstar)
  (δ : ℝ) (hδPos : δ > 0)
  (hδLt : δ < (min (1 - Bstar (rate (code φ degree)))
                   (1- (rate (code φ degree)) - 1/ Fintype.card ι)))
  (hProb : Pr_{ let r ←$ᵖ F }[ δᵣ((combineFinal φ dstar r fs degs hdegs), (code φ dstar)) ≤ δ ]  >
    ENNReal.ofReal (err' F dstar (rate (code φ degree)) δ (m * (dstar + 1) - ∑ i, degs i))) :
    ∃ S : Finset ι,
      S.card ≥ (1 - δ) * Fintype.card ι ∧
      ∀ i : Fin m, ∃ u : (ι → F),
      u ∈ (code φ (degs i)) ∧
      ∀ x ∈ S, fs i x = u x
  := by sorry

end Combine
