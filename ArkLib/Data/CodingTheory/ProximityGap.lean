/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov
-/

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.GuruswamiSudan
import ArkLib.Data.CodingTheory.Prelims
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Polynomial.Bivariate
import ArkLib.Data.Polynomial.RationalFunctions
import ArkLib.Data.Probability.Notation

import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.Module.Submodule.Defs
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Defs
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.Probability.Distributions.Uniform
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Substitution

/-!
  # Definitions and Theorems about Proximity Gaps

  We define the proximity gap properties of linear codes over finite fields.

  [BCIKS20] refers to the paper "Proximity Gaps for Reed-Solomon Codes" by Eli Ben-Sasson,
  Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.

  ## Main Definitions

-/

namespace ProximityGap

open NNReal Finset Function

open scoped BigOperators

section

variable {n : Type*} [Fintype n] [DecidableEq n]
universe u

open NNReal Finset Function ProbabilityTheory Finset

open scoped BigOperators LinearCode

section

variable {n : Type} [Fintype n] [DecidableEq n]

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

variable (C : Submodule F (n → F)) [DecidablePred (· ∈ C)]

/-- The proximity measure of two vectors `u` and `v` from a code `C` at distance `d` is the number
  of vectors at distance at most `d` from the linear combination of `u` and `v` with coefficients
  `r` in `F`. -/
def proximityMeasure (u v : n → F) (d : ℕ) : ℕ :=
  Fintype.card {r : F | Δ₀'(r • u + (1 - r) • v, C) ≤ d}

/-- A code `C` exhibits proximity gap at distance `d` and cardinality bound `bound` if for every
      pair of vectors `u` and `v`, whenever the proximity measure for `C u v d` is greater than
      `bound`, then the distance of `[u | v]` from the interleaved code `C ^⊗ 2` is at most `d`. -/
def proximityGap (d : ℕ) (bound : ℕ) : Prop :=
  ∀ u v : n → F, (proximityMeasure C u v d > bound)
    → (Δ₀( u ⋈ v , C ^⋈ Fin 2 ) ≤ d)

/-- A code `C` exhibits `δ`-correlated agreement with respect to a tuple of vectors `W_1, ..., W_k`
  if there exists a set `S` of coordinates such that the size of `S` is at least `(1 - δ) * |n|`,
  and there exists a tuple of codewords `v_1, ..., v_k` such that `v_i` agrees with `W_i` on `S`
  for all `i`. -/
def correlatedAgreement (C : Set (n → F)) (δ : ℝ≥0) {k : ℕ} (W : Fin k → n → F) : Prop :=
  ∃ S : Finset n, #(S) ≥ (1 - δ) * (Fintype.card n) ∧
    ∃ v : Fin k → n → F, ∀ i, v i ∈ C ∧ {j | v i j = W i j} = S

end

section

variable {ι : Type} [Fintype ι] [Nonempty ι]
         {F : Type}

/-- `Definition 1.1` in [BCIKS20]. -/
noncomputable def generalProximityGap {α : Type} [DecidableEq α] [Nonempty α]
  (P : Finset (ι → α)) (C : Set (Finset (ι → α))) (δ ε : ℝ≥0) : Prop :=
  ∀ S ∈ C, ∀ [Nonempty S],
  Xor'
  ( Pr_{let x ← $ᵖ S}[Code.relHammingDistToCode x.1 P ≤ δ] = 1 )
  ( Pr_{let x ← $ᵖ S}[Code.relHammingDistToCode x.1 P ≤ δ] ≤ ε )
end

section
variable {ι : Type} [Fintype ι] [Nonempty ι]
         {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The error bound `ε` in the pair of proximity and error parameters `(δ,ε)` for Reed-Solomon codes
  defined up to the Johnson bound. More precisely, let `ρ` be the rate of the Reed-Solomon code.
  Then for `δ ∈ (0, 1 - √ρ)`, we define the relevant error parameter `ε` for the unique decoding
  bound, i.e. `δ ∈ [0, (1-ρ)/2]` and Johnson bound, i.e. `δ ∈ [(1-ρ)/2 , 1 - √ρ]`. Otherwise,
  we set `ε = 0`.
-/
noncomputable def errorBound (δ : ℝ≥0) (deg : ℕ) (domain : ι ↪ F) : ℝ≥0 :=
  letI ρ : ℝ≥0 := ρ (ReedSolomon.code domain deg)
  if δ ∈ Set.Ioc 0 ((1 - ρ)/2)
  then Fintype.card ι / Fintype.card F
  else if δ ∈ Set.Ioo ((1 - ρ)/2) (1 - ρ.sqrt)
       then letI m := min (1 - ρ.sqrt - δ) (ρ.sqrt / 20)
            ⟨(deg ^ 2 : ℝ≥0) / ((2 * m) ^ 7 * (Fintype.card F : ℝ)), by positivity⟩
       else 0

/-- `Theorem 1.2` (Proximity Gaps for Reed-Solomon Codes) in [BCIKS20]. -/
theorem proximity_gap_RSCodes {k t : ℕ} [NeZero k] [NeZero t] {deg : ℕ} {domain : ι ↪ F}
  (C : Fin t → (Fin k → (ι → F))) {δ : ℝ≥0} (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain)) :
  generalProximityGap
    (ReedSolomonCode.toFinset domain deg)
    (Affine.AffSpanFinsetCol C)
    δ
    (errorBound δ deg domain) := by sorry

set_option linter.style.commandStart false

/-- `Theorem 1.4` (Main Theorem — Correlated agreement over lines) in [BCIKS20]. -/
theorem correlatedAgreement_lines {u : Fin 2 → ι → F} {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
  (hproximity :
    Pr_{ let z ← $ᵖ F}[
        Code.relHammingDistToCode (u 0 + z • u 1) (ReedSolomon.code domain deg) ≤ δ
      ] > errorBound δ deg domain
  ) : correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry

/-- `Theorem 1.5` (Correlated agreement for low-degree parameterised curves) in [BCIKS20]. -/
theorem correlatedAgreement_affine_curves [DecidableEq ι] {k : ℕ} {u : Fin k → ι → F}
  {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
  (hδ : δ ≤ 1 - ReedSolomonCode.sqrtRate deg domain)
  (hproximity :
    Pr_{let y ← $ᵖ (Curve.parametrisedCurveFinite u)}[
      Code.relHammingDistToCode y.1 (ReedSolomon.code domain deg) ≤ δ
    ] >
      k * (errorBound δ deg domain)) :
  correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry

open Affine in
/-- `Theorem 1.6` (Correlated agreement over affine spaces) in [BCIKS20]. -/
theorem correlatedAgreement_affine_spaces {k : ℕ} [NeZero k] {u : Fin (k + 1) → ι → F}
  {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0} (hδ : δ ≤ 1 - (ReedSolomonCode.sqrtRate deg domain))
  (hproximity :
    Pr_{let y ← $ᵖ (u 0 +ᵥ affineSpan F (Finset.univ.image (Fin.tail u)).toSet)}[
        Code.relHammingDistToCode (ι := ι) (F := F) y (ReedSolomon.code domain deg) ≤ δ
    ] > errorBound δ deg domain) :
  correlatedAgreement (ReedSolomon.code domain deg) δ u := by sorry

end

namespace Trivariate
section Trivariate

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]

open Polynomial Bivariate


noncomputable def eval_on_Z₀ (p : (RatFunc F)) (z : F) : F :=
  RatFunc.eval (RingHom.id _) z p


notation3:max R "[Z][X]" => Polynomial (Polynomial R)

notation3:max R "[Z][X][Y]" => Polynomial (Polynomial (Polynomial (R)))

notation3:max "Y" => Polynomial.X
notation3:max "X" => Polynomial.C Polynomial.X
notation3:max "Z" => Polynomial.C (Polynomial.C Polynomial.X)

noncomputable opaque eval_on_Z (p : F[Z][X][Y]) (z : F) : F[X][Y] :=
  p.map (Polynomial.mapRingHom (Polynomial.evalRingHom z))

open Polynomial.Bivariate in
noncomputable def toRatFuncPoly (p : F[Z][X][Y]) : (RatFunc F)[X][Y] :=
  p.map (Polynomial.mapRingHom (algebraMap F[X] (RatFunc F)))

end Trivariate
end Trivariate

section ProximityGapSection5
variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
variable {n : ℕ}

section

open GuruswamiSudan
open Polynomial.Bivariate
open RatFunc

/-- The degree bound (a.k.a. `D_X`) for instantiation of Guruswami-Sudan
    in lemma 5.3 of the Proximity Gap paper.
    D_X(m) = (m + 1/2)√rhon.
-/
noncomputable def D_X (rho : ℚ) (n m : ℕ) : ℝ := (m + 1/2) * (Real.sqrt rho) * n

open Classical in
noncomputable def proximity_gap_degree_bound (rho : ℚ) (m n : ℕ) : ℕ :=
  let b := D_X rho m n
  if h : ∃ n : ℕ, b = n
  then h.choose - 1
  else Nat.floor b

/-- The ball radius from lemma 5.3 of the Proximity Gap paper,
    which follows from the Johnson bound.
    δ₀(rho, m) = 1 - √rho - √rho/2m.
-/
noncomputable def proximity_gap_johnson (rho : ℚ) (m : ℕ) : ℝ :=
  (1 : ℝ) - Real.sqrt rho - Real.sqrt rho / (2 * m)


/-- The first part of lemma 5.3 from the Proximity gap paper.
    Given the D_X (`proximity_gap_degree_bound`) and δ₀ (`proximity_gap_johnson`),
    a solution to Guruswami-Sudan system exists.
-/
lemma guruswami_sudan_for_proximity_gap_existence {k m : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F} :
  ∃ Q, Condition (k + 1) m ((proximity_gap_degree_bound ((k + 1 : ℚ) / n) m n)) ωs f Q := by
  sorry

open Polynomial in
/-- The second part of lemma 5.3 from the Proximity gap paper.
    For any solution Q of the Guruswami-Sudan system, and for any
    polynomial P ∈ RS[n, k, rho] such that δᵣ(w, P) ≤ δ₀(rho, m),
    we have that Y - P(X) divides Q(X, Y) in the polynomial ring
    F[X][Y]. Note that in F[X][Y], the term X actually refers to
    the outer variable, Y.
-/
lemma guruswami_sudan_for_proximity_gap_property {k m : ℕ} {ωs : Fin n ↪ F}
  {w : Fin n → F}
  {Q : F[X][Y]}
  (cond : Condition (k + 1) m (proximity_gap_degree_bound ((k + 1 : ℚ) / n) m n) ωs w Q)
  {p : ReedSolomon.code ωs n}
  (h : δᵣ(w, p) ≤ proximity_gap_johnson ((k + 1 : ℚ) / n) m)
  :
  (X - Polynomial.C (ReedSolomon.codewordToPoly p)) ∣ Q := by sorry


section

open Polynomial
open Polynomial.Bivariate

/-- Following the Proximity Gap paper this the Y-degree of 
    a trivariate polynomial `Q`.
-/
def D_Y (Q : F[Z][X][Y]) : ℕ := Bivariate.natDegreeY Q

/-- The YZ-degree of a trivariate polynomial.
-/
def D_YZ (Q : F[Z][X][Y]) : ℕ :=
  Option.getD (dflt := 0) <| Finset.max
    (Finset.image
            (
              fun j =>
                Option.getD (
                  Finset.max (
                    Finset.image
                      (fun k => j + (Bivariate.coeff Q j k).natDegree)
                      (Q.coeff j).support
                  )
                ) 0
            )
            Q.support
    )

end

/-- The Guruswami-Sudan condition as it is stated in
    the proximity gap paper.
-/
structure ModifiedGuruswami
  (m n k : ℕ)
  (ωs : Fin n ↪ F)
  (Q : F[Z][X][Y])
  (u₀ u₁ : Fin n → F)
  where
  Q_ne_0 : Q ≠ 0
  /-- Degree of the polynomial. -/
  Q_deg : natWeightedDegree Q 1 k < D_X ((k + 1) / (n : ℚ)) n m
  /-- Multiplicity of the roots is at least `m`. -/
  Q_multiplicity : ∀ i, rootMultiplicity Q
              (Polynomial.C <| ωs i)
              ((Polynomial.C <| u₀ i) + Polynomial.X * (Polynomial.C <| u₁ i))
            ≥ m
  /-- The X-degree bound. -/
  Q_deg_X :
    degreeX Q < D_X ((k + 1) / (n : ℚ)) n m
  /-- The Y-degree bound. -/
  Q_D_Y :
    D_Y Q < D_X (k + 1 / (n : ℚ)) n m / k
  /-- The YZ-degree bound. -/
  Q_D_YZ :
    D_YZ Q ≤ n * (m + 1/(2 : ℚ))^3 / (6 * Real.sqrt ((k + 1) / n))

/-- The claim 5.4 from the proximity gap paper.
    It essentially claims that there exists 
    a soultion to the Guruswami-Sudan constraints above.
-/
lemma modified_guruswami_has_a_solution
  {m n k : ℕ}
  {ωs : Fin n ↪ F} {u₀ u₁ : Fin n → F}
  :
  ∃ Q : F[Z][X][Y], ModifiedGuruswami m n k ωs Q u₀ u₁
    := by sorry

end

variable {m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}
         [Finite F]

noncomputable instance {α : Type} (s : Set α) [inst : Finite s] : Fintype s := Fintype.ofFinite _

/-- The set `S` (equation 5.2 of the proximity gap paper). -/
noncomputable def coeffs_of_close_proximity (ωs : Fin n ↪ F) (δ : ℚ) (u₀ u₁ : Fin n → F)
  : Finset F := Set.toFinset { z | ∃ v : ReedSolomon.code ωs (k + 1), δᵣ(u₀ + z • u₁, v) ≤ δ}

open Polynomial

omit [DecidableEq (RatFunc F)] in
/-- There exists a `δ`-close polynomial `P_z` for each `z` 
    from the set `S`.
-/
lemma exists_Pz_of_coeffs_of_close_proximity
  {k : ℕ}
  {z : F}
  (hS : z ∈ coeffs_of_close_proximity (k := k) ωs δ u₀ u₁)
  :
  ∃ Pz : F[X], Pz.natDegree ≤ k ∧ δᵣ(u₀ + z • u₁, Pz.eval ∘ ωs) ≤ δ := by
    unfold coeffs_of_close_proximity at hS
    obtain ⟨w, hS, dist⟩ : ∃ a ∈ ReedSolomon.code ωs (k + 1), ↑δᵣ(u₀ + z • u₁, a) ≤ δ := by
      simpa using hS
    obtain ⟨p, hS⟩ : ∃ y ∈ degreeLT F (k + 1), (ReedSolomon.evalOnPoints ωs) y = w := by
      simpa using hS
    exact ⟨p, ⟨
      by if h : p = 0
         then simp [h]
         else rw [mem_degreeLT, degree_eq_natDegree h, Nat.cast_lt] at hS; grind,
      by convert dist; rw [←hS.2]; rfl
    ⟩⟩

/-- The `δ`-close polynomial `Pz` for each `z` 
    from the set `S` (`coeffs_of_close_proximity`).
-/
noncomputable def Pz
  {k : ℕ}
  {z : F}
  (hS : z ∈ coeffs_of_close_proximity k ωs δ u₀ u₁)
  :
  F[X]
  := (exists_Pz_of_coeffs_of_close_proximity (n := n) (k := k) hS).choose

/-- Proposition 5.5 from the proximity gap paper.
    There exists a subset `S'` of the set `S` and
    a bivariate polynomial `P(X, Z)` that matches
    `Pz` on that set. 
-/
lemma exists_a_set_and_a_matching_polynomial
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
  ∃ S', ∃ (h_sub : S' ⊆ coeffs_of_close_proximity k ωs δ u₀ u₁), ∃ P : F[Z][X],
    #S' > #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (2 * D_Y Q) ∧
    ∀ z : S', Pz (h_sub z.2) = P.map (Polynomial.evalRingHom z.1) ∧
    P.natDegree ≤ k ∧
    Bivariate.degreeX P ≤ 1 := by sorry

/-- The subset `S'` extracted from the proprosition 5.5.
-/
noncomputable def matching_set
  (ωs : Fin n ↪ F)
  (δ : ℚ)
  (u₀ u₁ : Fin n → F)
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  : Finset F := (exists_a_set_and_a_matching_polynomial k h_gs (δ := δ)).choose

/-- `S'` is indeed a subset of `S` -/
lemma matching_set_is_a_sub_of_coeffs_of_close_proximity
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  : matching_set k ωs δ u₀ u₁ h_gs ⊆ coeffs_of_close_proximity k ωs δ u₀ u₁ := by sorry

/-- The equation 5.12 from the proximity gap paper. -/
lemma irreducible_factorization_of_gs_solution
  {k : ℕ}
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
  ∃ (C : F[Z][X]) (R : List F[Z][X][Y]) (f : List ℕ) (e : List ℕ),
    R.length = f.length ∧
    f.length = e.length ∧
    ∀ eᵢ ∈ e, 1 ≤ eᵢ ∧
    ∀ Rᵢ ∈ R, Rᵢ.Separable ∧
    ∀ Rᵢ ∈ R, Irreducible Rᵢ ∧
    Q = (Polynomial.C C) *
        ∏ (Rᵢ ∈ R.toFinset) (fᵢ ∈ f.toFinset) (eᵢ ∈ e.toFinset),
          (Rᵢ.comp ((Y : F[Z][X][Y]) ^ fᵢ))^eᵢ
  := sorry

/-- Claim 5.6 of the proximity gap paper. -/
lemma discr_of_irred_components_nonzero
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  : ∃ x₀,
      ∀ R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose,
      Bivariate.evalX x₀ (Bivariate.discr_y R) ≠ 0 := by sorry

open Trivariate in
open Bivariate in
/-- Claim 5.7 of the proximity gap paper. -/
lemma exists_factors_with_large_common_root_set
  (δ : ℚ) (x₀ : F)
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
  ∃ R H, R ∈ (irreducible_factorization_of_gs_solution h_gs).choose_spec.choose ∧
    Irreducible H ∧ H ∣ (Bivariate.evalX (Polynomial.C x₀) R) ∧
    #(@Set.toFinset _ { z : coeffs_of_close_proximity (F := F) k ωs δ u₀ u₁ |
        letI Pz := Pz z.2
        (Trivariate.eval_on_Z R z.1).eval Pz = 0 ∧
        (Bivariate.evalX z.1 H).eval (Pz.eval x₀) = 0} sorry)
    ≥ #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q)
    ∧ #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (Bivariate.natDegreeY Q) >
      2 * D_Y Q ^ 2 * (D_X ((k + 1 : ℚ) / n) n m) * D_YZ Q := by sorry

/-- Claim 5.7 establishes existens of a polynomial `R`.
    This is the extraction of this polynomial.
-/
noncomputable def R
  (δ : ℚ) (x₀ : F)
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  : F[Z][X][Y] := (exists_factors_with_large_common_root_set k δ x₀ h_gs).choose

/-- Claim 5.7 establishes existens of a polynomial `H`.
    This is the extraction of this polynomial.
-/
noncomputable def H
  (δ : ℚ) (x₀ : F)
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  : F[Z][X] := (exists_factors_with_large_common_root_set k δ x₀ h_gs).choose_spec.choose

/-- An important property of the polynomial
    `H` extracted from claim 5.7 is that it is 
    irreducible.
-/
lemma irreducible_H
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
  Irreducible (H k δ x₀ h_gs) := by
  have h := Classical.choose_spec <| Classical.choose_spec 
    (exists_factors_with_large_common_root_set (δ := δ) (x₀ := x₀) k h_gs)
  simp [H]
  rcases h with ⟨_, h, _⟩
  sorry

open AppendixA.ClaimA2 in
/-- The claim 5.8 from the proximity gap paper.
    States that the approximate solution is 
    actually a solution.
    This version of the claim is stated in terms
    of coefficients.
-/
lemma approximate_solution_is_exact_solution_coeffs
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  : ∀ t ≥ k,
  α' 
    x₀ 
    (R k δ x₀ h_gs) 
    (irreducible_H k h_gs) 
    t 
  = 
  (0 : AppendixA.𝕃 (H k δ x₀ h_gs))
  := by sorry

open AppendixA.ClaimA2 in
/-- The claim 5.8 from the proximity gap paper.
    States that the approximate solution is 
    actually a solution.
    This version is in terms of polynomials.
-/
lemma approximate_solution_is_exact_solution_coeffs'
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
    γ' x₀ (R k δ x₀ h_gs) (irreducible_H k h_gs) =
        PowerSeries.mk (fun t =>
          if t ≥ k
          then (0 : AppendixA.𝕃 (H k δ x₀ h_gs))
          else PowerSeries.coeff _ t
            (γ' 
              x₀
              (R k (x₀ := x₀) (δ := δ) h_gs)
              (irreducible_H k h_gs))) := by
   sorry

open AppendixA.ClaimA2 in
/-- Claim 5.9 from the proximity gap paper.
    States that the solution `γ` is linear in 
    the variable `Z`.
-/
lemma solution_gamma_is_linear_in_Z
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
  ∃ (v₀ v₁ : F[X]),
    γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs) =
        AppendixA.polyToPowerSeries𝕃 _
          (
            (Polynomial.map Polynomial.C v₀) +
            (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)
          ) := by sorry

/-- The linear represenation of the solution `γ` 
    extracted from the claim 5.9.
-/
noncomputable def P
  (δ : ℚ) (x₀ : F)
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
  F[Z][X] :=
  let v₀ := Classical.choose (solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs)
  let v₁ := Classical.choose 
    (Classical.choose_spec <| solution_gamma_is_linear_in_Z k (δ := δ) (x₀ := x₀) h_gs)
  (
    (Polynomial.map Polynomial.C v₀) +
    (Polynomial.C Polynomial.X) * (Polynomial.map Polynomial.C v₁)
  )

open AppendixA.ClaimA2 in
/-- The extracted `P` from claim 5.9 equals `γ`.
-/
lemma gamma_eq_P
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  :
  γ' x₀ (R k δ x₀ h_gs) (irreducible_H k (x₀ := x₀) (δ := δ) h_gs) =
  AppendixA.polyToPowerSeries𝕃 _ 
    (P k δ x₀ h_gs) := by sorry

/-- The set `S'_x` from the proximity gap paper (just before claim 5.10).
    The set of all `z∈S'` such that `w(x,z)` matches `P_z(x)`.
-/
noncomputable def matching_set_at_x
  (δ : ℚ)
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  (x : Fin n)
  : Finset F := @Set.toFinset _ {z : F | ∃ h : z ∈ matching_set k ωs δ u₀ u₁ h_gs,
    u₀ x + z * u₁ x = 
      (Pz (matching_set_is_a_sub_of_coeffs_of_close_proximity k h_gs h)).eval (ωs x)} sorry

/-- Claim 5.10 of the proximity gap paper.
    Needed to prove the claim 5.9.
    This claim states that `γ(x)=w(x,Z)` if
    the cardinality |S'_x| is big enough.
-/
lemma solution_gamma_matches_word_if_subset_large
  {ωs : Fin n ↪ F}
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  {x : Fin n}
  {D : ℕ}
  (hD : D ≥ Bivariate.totalDegree (H k δ x₀ h_gs))
  (hx : (matching_set_at_x k δ h_gs x).card >
    (2 * k + 1)
      * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
      * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
      * D)
  : (P k δ x₀ h_gs).eval (Polynomial.C (ωs x)) =
    (Polynomial.C <| u₀ x) + u₁ x • Polynomial.X
  := by sorry

/-- Claim 5.11 from the proximity gap paper.
    There exists a set of points `{x₀,...,x_{k+1}}` 
    such that the sets S_{x_j} satisfy the condition
    in the claim 5.10.
-/
lemma exists_points_with_large_matching_subset
  {ωs : Fin n ↪ F}
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁)
  {x : Fin n}
  {D : ℕ}
  (hD : D ≥ Bivariate.totalDegree (H k δ x₀ h_gs))
  :
  ∃ Dtop : Finset (Fin n),
    Dtop.card = k + 1 ∧
    ∀ x ∈ Dtop,
      (matching_set_at_x k δ h_gs x).card >
        (2 * k + 1)
        * (Bivariate.natDegreeY <| H k δ x₀ h_gs)
        * (Bivariate.natDegreeY <| R k δ x₀ h_gs)
        * D := by sorry

end ProximityGapSection5
end

end ProximityGap
