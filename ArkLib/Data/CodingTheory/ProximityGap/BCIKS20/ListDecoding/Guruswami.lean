/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Katerina Hristova, František Silváši, Julian Sutherland,
         Ilia Vlasov, Chung Thai Nguyen
-/

import ArkLib.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Data.CodingTheory.GuruswamiSudan.Basic
import ArkLib.Data.CodingTheory.GuruswamiSudan.GuruswamiSudan
import ArkLib.Data.Polynomial.Trivariate

namespace ProximityGap

open NNReal Finset Function ProbabilityTheory Code
open scoped BigOperators LinearCode

universe u v w k l

section BCIKS20ProximityGapSection5

variable {F : Type} [Field F] [DecidableEq F] [DecidableEq (RatFunc F)]
variable {n : ℕ}

section

open GuruswamiSudan Polynomial.Bivariate RatFunc Trivariate

/-- The degree bound (a.k.a. `D_X`) for instantiation of Guruswami-Sudan in Lemma 5.3 of [BCIKS20].
`D_X(m) = (m + 1/2)√rhon.` -/
noncomputable def D_X (rho : ℚ) (n m : ℕ) : ℝ := (m + 1/2) * (Real.sqrt rho) * n

omit [DecidableEq (RatFunc F)] in
/-- The first part of Lemma 5.3 from [BCIKS20].
Given `D_X` (`proximity_gap_degree_bound`) and `δ₀` (`proximity_gap_johnson`), a solution to
Guruswami-Sudan system exists. -/
lemma guruswami_sudan_for_proximity_gap_existence {k m : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F}
    (hm : 1 ≤ m) :
    ∃ Q, Conditions (k + 1) m (_root_.proximity_gap_degree_bound (k + 1) n m) ωs f Q :=
    GuruswamiSudan.proximity_gap_existence (k + 1) n ωs f hm

omit [DecidableEq (RatFunc F)] in
open Polynomial in
/-- The second part of Lemma 5.3 from [BCIKS20].
For any solution `Q` of the Guruswami-Sudan system, and for any polynomial `P ∈ RS[n, k, rho]`
such that `δᵣ(w, P) ≤ δ₀(rho, m)`, we have that `Y - P(X)` divides `Q(X, Y)` in the polynomial ring
`F[X][Y]`. Note that in `F[X][Y]`, the term `X` actually refers to the outer variable, `Y`.
-/
lemma guruswami_sudan_for_proximity_gap_property {k m : ℕ} {ωs : Fin n ↪ F}
    {w : Fin n → F}
    {Q : F[X][Y]}
    (hk : k + 2 ≤ n) (hm : 1 ≤ m)
    (cond : Conditions (k + 1) m (_root_.proximity_gap_degree_bound (k + 1) n m) ωs w Q)
    {p : ReedSolomon.code ωs (k + 1)}
    (h : (↑Δ₀(w, fun i ↦ Polynomial.eval (ωs i) (ReedSolomon.toPolynomial p)) : ℝ) / ↑n <
         _root_.proximity_gap_johnson (k + 1) n m)
    :
    (Polynomial.X - Polynomial.C (ReedSolomon.toPolynomial p)) ∣ Q :=
  GuruswamiSudan.proximity_gap_divisibility hk hm p cond h

/-- The Guruswami-Sudan condition as it is stated in [BCIKS20]. -/
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
    D_Y Q < D_X ((k + 1 : ℚ) / n) n m / k
  /-- The YZ-degree bound. -/
  Q_D_YZ :
    D_YZ Q ≤ n * (m + 1/(2 : ℚ))^3 / (6 * Real.sqrt ((k + 1) / n))

/-- The univariate polynomial `∏ i, (X - ωs i) ^ m`, which vanishes to order `m` at each of the
`n` interpolation points. -/
noncomputable def vanishingBase (ωs : Fin n ↪ F) (m : ℕ) : Polynomial F :=
  ∏ i, (Polynomial.X - Polynomial.C (ωs i)) ^ m

/-- The Guruswami-Sudan witness in the high-rate regime: `∏ i, (X - ωs i) ^ m`, viewed as a
trivariate polynomial that is constant in both `Y` and `Z`. Since it does not involve `Y`, it
vanishes to order `m` along the whole curve `(ωs i, u₀ i + Z * u₁ i)`, at the price of an
`X`-degree of `n * m`. -/
noncomputable def vanishingWitness (ωs : Fin n ↪ F) (m : ℕ) : F[Z][X][Y] :=
  Polynomial.C ((vanishingBase ωs m).map (Polynomial.C : F →+* Polynomial F))

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- `vanishingBase` is monic, being a product of monic polynomials. -/
lemma vanishingBase_monic (ωs : Fin n ↪ F) (m : ℕ) : (vanishingBase ωs m).Monic :=
  Polynomial.monic_prod_of_monic _ _ fun i _ ↦ (Polynomial.monic_X_sub_C (ωs i)).pow m

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- `vanishingBase` has degree `n * m`. -/
lemma natDegree_vanishingBase (ωs : Fin n ↪ F) (m : ℕ) :
    (vanishingBase ωs m).natDegree = n * m := by
  rw [vanishingBase,
    Polynomial.natDegree_prod_of_monic _ _ fun i _ ↦ (Polynomial.monic_X_sub_C (ωs i)).pow m]
  simp [Polynomial.natDegree_pow]

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- The coefficients of `vanishingWitness` are constant in `Z`, since it is the image of a
univariate polynomial over `F`. -/
lemma natDegree_coeff_vanishingWitness (ωs : Fin n ↪ F) (m i j : ℕ) :
    (Polynomial.Bivariate.coeff (vanishingWitness ωs m) i j).natDegree = 0 := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp [Polynomial.Bivariate.coeff, vanishingWitness, Polynomial.coeff_C]
  · simp [Polynomial.Bivariate.coeff, vanishingWitness, Polynomial.coeff_C, hj]

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- `vanishingWitness` is non-zero. -/
lemma vanishingWitness_ne_zero (ωs : Fin n ↪ F) (m : ℕ) : vanishingWitness ωs m ≠ 0 := by
  simpa [vanishingWitness, Polynomial.C_eq_zero] using
    ((vanishingBase_monic ωs m).map (Polynomial.C : F →+* Polynomial F)).ne_zero

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- `vanishingWitness` is supported on `Y ^ 0`. -/
lemma support_vanishingWitness (ωs : Fin n ↪ F) (m : ℕ) :
    (vanishingWitness ωs m).support = {0} :=
  Polynomial.support_C (by
    simpa [Polynomial.C_eq_zero] using
      ((vanishingBase_monic ωs m).map (Polynomial.C : F →+* Polynomial F)).ne_zero)

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- Every weighted degree of `vanishingWitness` is carried by its `X`-degree `n * m`. -/
lemma natWeightedDegree_vanishingWitness (ωs : Fin n ↪ F) (m u v : ℕ) :
    Polynomial.Bivariate.natWeightedDegree (vanishingWitness ωs m) u v = u * (n * m) := by
  rw [Polynomial.Bivariate.natWeightedDegree, support_vanishingWitness]
  simp [vanishingWitness, (vanishingBase_monic ωs m).natDegree_map, natDegree_vanishingBase]

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- The `X`-degree of `vanishingWitness` is `n * m`. -/
lemma degreeX_vanishingWitness (ωs : Fin n ↪ F) (m : ℕ) :
    Polynomial.Bivariate.degreeX (vanishingWitness ωs m) = n * m := by
  rw [Polynomial.Bivariate.degreeX_as_weighted_deg, natWeightedDegree_vanishingWitness, one_mul]

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- The `Y`-degree of `vanishingWitness` is zero. -/
lemma D_Y_vanishingWitness (ωs : Fin n ↪ F) (m : ℕ) : D_Y (vanishingWitness ωs m) = 0 := by
  simp [D_Y, Polynomial.Bivariate.natDegreeY, vanishingWitness]

omit [DecidableEq F] [DecidableEq (RatFunc F)] in
/-- The `YZ`-degree of `vanishingWitness` is zero: it is constant in both `Y` and `Z`. -/
lemma D_YZ_vanishingWitness (ωs : Fin n ↪ F) (m : ℕ) : D_YZ (vanishingWitness ωs m) = 0 := by
  have hmax : ∀ s : Finset ℕ, (∀ x ∈ s, x = 0) → Option.getD s.max 0 = 0 := by
    intro s hs
    rcases s.eq_empty_or_nonempty with rfl | hne
    · rfl
    · obtain ⟨a, ha⟩ := Finset.max_of_nonempty hne
      rw [ha]
      exact hs a (Finset.mem_of_max ha)
  refine hmax _ fun x hx ↦ ?_
  simp only [Finset.mem_image, support_vanishingWitness, Finset.mem_singleton] at hx
  obtain ⟨j, rfl, rfl⟩ := hx
  refine hmax _ fun y hy ↦ ?_
  simp only [Finset.mem_image] at hy
  obtain ⟨i, -, rfl⟩ := hy
  simp [natDegree_coeff_vanishingWitness]

omit [DecidableEq (RatFunc F)] in
/-- `vanishingWitness` vanishes to order at least `m` at every point of the form `(ωs i, y)`,
in particular along the curve `(ωs i, u₀ i + Z * u₁ i)`. -/
lemma le_rootMultiplicity_vanishingWitness (ωs : Fin n ↪ F) (m : ℕ) (i : Fin n)
    (y : Polynomial F) :
    (m : Option ℕ) ≤ Polynomial.Bivariate.rootMultiplicity (vanishingWitness ωs m)
      (Polynomial.C (ωs i)) y := by
  set p := (vanishingBase ωs m).map (Polynomial.C : F →+* Polynomial F) with hp
  have hshift : Polynomial.Bivariate.shift (vanishingWitness ωs m) (Polynomial.C (ωs i)) y
      = Polynomial.C (p.comp (Polynomial.X + Polynomial.C (Polynomial.C (ωs i)))) := by
    simp [Polynomial.Bivariate.shift, vanishingWitness, hp]
  have hmap : ((Polynomial.X - Polynomial.C (ωs i)) ^ m).map (Polynomial.C : F →+* Polynomial F)
      = (Polynomial.X - Polynomial.C (Polynomial.C (ωs i))) ^ m := by
    rw [Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  have hfac : (Polynomial.X - Polynomial.C (Polynomial.C (ωs i))) ^ m ∣ p := by
    rw [hp, vanishingBase, ← hmap]
    exact Polynomial.map_dvd _ (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
  have hcomp : ((Polynomial.X - Polynomial.C (Polynomial.C (ωs i))) ^ m).comp
      (Polynomial.X + Polynomial.C (Polynomial.C (ωs i))) = Polynomial.X ^ m := by
    rw [Polynomial.pow_comp, Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
      add_sub_cancel_right]
  have hXm : Polynomial.X ^ m ∣ p.comp (Polynomial.X + Polynomial.C (Polynomial.C (ωs i))) := by
    rw [← hcomp]
    exact map_dvd (Polynomial.compRingHom _) hfac
  refine Polynomial.Bivariate.le_rootMultiplicity_of_coeff_shift_eq_zero ?_ ?_
  · rw [hshift]
    simpa [Polynomial.C_eq_zero] using
      (((vanishingBase_monic ωs m).map (Polynomial.C : F →+* Polynomial F)).comp_X_add_C _).ne_zero
  · intro s t hst
    rw [hshift]
    rcases eq_or_ne t 0 with rfl | ht
    · simpa [Polynomial.Bivariate.coeff] using Polynomial.X_pow_dvd_iff.mp hXm s (by omega)
    · simp [Polynomial.Bivariate.coeff, Polynomial.coeff_C, ht]

omit [DecidableEq (RatFunc F)] in
/-- Claim 5.4 from [BCIKS20] in the high-rate regime, where the degree budget `D_X` already
accommodates a polynomial vanishing to order `m` at all `n` interpolation points: the explicit
witness `∏ i, (X - ωs i) ^ m` solves the system.

This is the branch of `modified_guruswami_has_a_solution` that an interpolation count cannot
cover: when `n * m < D_X` the number of monomials below the weighted degree bound need not exceed
the number of linear conditions. -/
lemma exists_modifiedGuruswami_of_lt_D_X {m k : ℕ} (hk : 0 < k)
    (hD : ((n * m : ℕ) : ℝ) < D_X ((k + 1) / (n : ℚ)) n m)
    {ωs : Fin n ↪ F} {u₀ u₁ : Fin n → F} :
    ∃ Q : F[Z][X][Y], ModifiedGuruswami m n k ωs Q u₀ u₁ := by
  have hDX : 0 < D_X ((k + 1) / (n : ℚ)) n m := lt_of_le_of_lt (Nat.cast_nonneg _) hD
  refine ⟨vanishingWitness ωs m, vanishingWitness_ne_zero ωs m, ?_,
    fun i ↦ le_rootMultiplicity_vanishingWitness ωs m i _, ?_, ?_, ?_⟩
  · simpa [natWeightedDegree_vanishingWitness] using hD
  · simpa [degreeX_vanishingWitness] using hD
  · simpa [D_Y_vanishingWitness] using div_pos hDX (by exact_mod_cast hk)
  · simp only [D_YZ_vanishingWitness, Nat.cast_zero]
    positivity

omit [DecidableEq (RatFunc F)] in
/-- The modified Guruswami-Sudan system is solvable: for every evaluation domain `ωs` and word
pair `u₀ u₁`, some nonzero trivariate `Q` meets all the degree and multiplicity constraints of
`ModifiedGuruswami` (Claim 5.4).

The hypotheses `0 < n` and `0 < k` are necessary: with `n = 0` or `k = 0` the rational degree
bounds `D_X` and `D_X / k` collapse to `0`, making the strict degree constraints unsatisfiable.
`1 ≤ m` matches the interpolation count that supplies `Q`. -/
lemma modified_guruswami_has_a_solution {m n k : ℕ}
    (hn : 0 < n) (hk : 0 < k) (hm : 1 ≤ m)
    {ωs : Fin n ↪ F} {u₀ u₁ : Fin n → F} :
    ∃ Q : F[Z][X][Y], ModifiedGuruswami m n k ωs Q u₀ u₁ := by
  sorry

end

variable {m : ℕ} (k : ℕ) {δ : ℚ} {x₀ : F} {u₀ u₁ : Fin n → F} {Q : F[Z][X][Y]} {ωs : Fin n ↪ F}
         [Finite F]

noncomputable instance {α : Type} (s : Set α) [inst : Finite s] : Fintype s := Fintype.ofFinite _

/-- The set `S` (equation 5.2 of [BCIKS20]). -/
noncomputable def coeffs_of_close_proximity (ωs : Fin n ↪ F) (δ : ℚ) (u₀ u₁ : Fin n → F)
    : Finset F := Set.toFinset { z | ∃ v : ReedSolomon.code ωs (k + 1), δᵣ(u₀ + z • u₁, v) ≤ δ}

open Polynomial

omit [DecidableEq (RatFunc F)] in
/-- There exists a `δ`-close polynomial `P_z` for each `z` from the set `S`. -/
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
      change ∃ y ∈ degreeLT F (k + 1), (ReedSolomon.evalOnPoints ωs) y = w at hS
      exact hS
    exact ⟨p, ⟨
      by if h : p = 0
         then simp [h]
         else rw [mem_degreeLT, degree_eq_natDegree h, Nat.cast_lt] at hS; grind,
      by convert dist; rw [←hS.2]; rfl
    ⟩⟩

/-- The `δ`-close polynomial `Pz` for each `z` from the set `S` (`coeffs_of_close_proximity`). -/
noncomputable def Pz {k : ℕ} {z : F} (hS : z ∈ coeffs_of_close_proximity k ωs δ u₀ u₁) : F[X] :=
  (exists_Pz_of_coeffs_of_close_proximity (n := n) (k := k) hS).choose

open Trivariate
omit [DecidableEq (RatFunc F)] in
/-- Proposition 5.5 from [BCIKS20].
There exists a subset `S'` of the set `S` and a bivariate polynomial `P(X, Z)` that matches `Pz` on
that set. -/
lemma exists_a_set_and_a_matching_polynomial
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    ∃ S', ∃ (h_sub : S' ⊆ coeffs_of_close_proximity k ωs δ u₀ u₁), ∃ P : F[Z][X],
     #S' > #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (2 * D_Y Q) ∧
     ∀ z : S', Pz (h_sub z.2) = P.map (Polynomial.evalRingHom z.1) ∧
     P.natDegree ≤ k ∧
     Bivariate.degreeX P ≤ 1 := by
    sorry

/-- The subset `S'` extracted from Proprosition 5.5 [BCIKS20]. -/
noncomputable def matching_set (ωs : Fin n ↪ F) (δ : ℚ) (u₀ u₁ : Fin n → F)
  (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) : Finset F :=
  (exists_a_set_and_a_matching_polynomial k h_gs (δ := δ)).choose

omit [DecidableEq (RatFunc F)] in
/-- `S'` is indeed a subset of `S` -/
lemma matching_set_is_a_sub_of_coeffs_of_close_proximity
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    matching_set k ωs δ u₀ u₁ h_gs ⊆ coeffs_of_close_proximity k ωs δ u₀ u₁ :=
  (exists_a_set_and_a_matching_polynomial k h_gs (δ := δ)).choose_spec.choose

end BCIKS20ProximityGapSection5

end ProximityGap
