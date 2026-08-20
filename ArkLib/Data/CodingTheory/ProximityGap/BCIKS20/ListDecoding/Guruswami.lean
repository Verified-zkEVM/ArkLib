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

private theorem finsetMaxGetD_le (s : Finset ℕ) (B : ℕ)
    (h : ∀ a ∈ s, a ≤ B) : Option.getD (Finset.max s) 0 ≤ B := by
  have hmax : Finset.max s ≤ (B : WithBot ℕ) := by
    apply Finset.max_le
    intro a ha
    exact WithBot.coe_le_coe.mpr (h a ha)
  have hunbot : (Finset.max s).unbotD 0 ≤ B := by
    rw [WithBot.unbotD_le_iff]
    · exact hmax
    · intro hbot
      omega
  have heq : (Finset.max s).unbotD 0 = Option.getD (Finset.max s) 0 := by
    cases Finset.max s <;> rfl
  rw [← heq]
  exact hunbot




private noncomputable def symbolicGSEvalConstraint {F : Type} [Field F]
    (x y : Polynomial F) (s t d : ℕ) :
    Polynomial (Polynomial (Polynomial F)) →ₗ[F] F where
  toFun Q := ((((Polynomial.Bivariate.shift Q x y).coeff t).coeff s).coeff d)
  map_add' Q R := by simp [Polynomial.Bivariate.shift]
  map_smul' a Q := by simp [Polynomial.Bivariate.shift]

private theorem symbolicInnerMonomial_shift_coeff {F : Type} [Field F]
    (a h : ℕ) (x : F) (s : ℕ) :
    (((Polynomial.monomial a (Polynomial.monomial h 1) :
      Polynomial (Polynomial F)).comp
        (Polynomial.X + Polynomial.C (Polynomial.C x))).coeff s) =
      Polynomial.monomial h (x ^ (a - s) * (a.choose s : F)) := by
  rw [Polynomial.monomial_comp, Polynomial.coeff_C_mul,
    Polynomial.coeff_X_add_C_pow]
  rw [← Polynomial.C_eq_natCast]
  rw [← map_pow, ← map_mul, Polynomial.monomial_mul_C, one_mul]

private noncomputable def symbolicModifiedGSCap (n k m : ℕ) : ℕ :=
  _root_.proximity_gap_degree_bound k n m

private theorem symbolicModifiedGSCap_le_DX {n k m : ℕ} (hn : 0 < n) :
    (symbolicModifiedGSCap n k m : ℝ) ≤
      D_X ((k + 1 : ℚ) / n) n m := by
  unfold symbolicModifiedGSCap _root_.proximity_gap_degree_bound D_X
  dsimp only
  exact Nat.floor_le (by positivity)

private theorem symbolicModifiedGSCap_pos {n k m : ℕ}
    (hn : 0 < n) (hk : 0 < k) (hm : 1 ≤ m) :
    0 < symbolicModifiedGSCap n k m := by
  unfold symbolicModifiedGSCap _root_.proximity_gap_degree_bound
  dsimp only
  rw [Nat.floor_pos]
  let y : ℝ := Real.sqrt (↑((k + 1 : ℚ) / n)) * n
  have hy0 : 0 ≤ y := by positivity
  have hr : 0 ≤ (↑((k + 1 : ℚ) / n) : ℝ) := by positivity
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hysq : y ^ 2 = ((k : ℝ) + 1) * n := by
    dsimp [y]
    rw [mul_pow, Real.sq_sqrt hr]
    push_cast
    field_simp [hn0]
  have hysq2 : 2 ≤ y ^ 2 := by
    rw [hysq]
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hn' : (1 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [mul_le_mul (show (2 : ℝ) ≤ k + 1 by linarith) hn' (by positivity) (by positivity)]
  have hy1 : 1 ≤ y := by nlinarith
  have hy1' : 1 ≤ Real.sqrt (↑((k + 1 : ℚ) / n)) * n := by exact hy1
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  rw [mul_assoc]
  have hfac : (1 : ℝ) ≤ m + 1 / 2 := by linarith
  have hmul : (m + 1 / 2 : ℝ) * 1 ≤
      (m + 1 / 2 : ℝ) * (Real.sqrt (↑((k + 1 : ℚ) / n)) * n) :=
    mul_le_mul_of_nonneg_left hy1' (by positivity)
  exact hfac.trans (by simpa only [mul_one] using hmul)

private theorem symbolicModifiedGSCap_sq_gt {n k m : ℕ} (hn : 0 < n) :
    ((symbolicModifiedGSCap n k m : ℝ) + 1) ^ 2 >
      (m + 1 / 2) ^ 2 * (k + 1) * n := by
  unfold symbolicModifiedGSCap
  exact GuruswamiSudan.proximity_gap_degree_bound_sq_gt
    (k := k) (n := n) (m := m) (ne_of_gt hn)

private theorem symbolicOuterAffine_map {F : Type} [Field F]
    (x y₀ y₁ : F) :
    Polynomial.map
      (Polynomial.compRingHom (Polynomial.X + Polynomial.C (Polynomial.C x)))
      (Polynomial.X + Polynomial.C
        (Polynomial.C (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁))) =
      Polynomial.X + Polynomial.C
        (Polynomial.C (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁)) := by
  simp [Polynomial.coe_compRingHom_apply]


private noncomputable def symbolicUpperTriangleBase (n k m : ℕ) : Finset (ℕ × ℕ) :=
  (GuruswamiSudan.weightBoundIndices (k + 2) (symbolicModifiedGSCap n k m - 1)).image
    (fun p => (p.1 + p.2, p.2))

private theorem symbolicCapPoint_not_mem_base {n k m : ℕ}
    (hn : 0 < n) (hk : 0 < k) (hm : 1 ≤ m) :
    (symbolicModifiedGSCap n k m, 0) ∉ symbolicUpperTriangleBase n k m := by
  classical
  intro hmem
  unfold symbolicUpperTriangleBase at hmem
  rw [Finset.mem_image] at hmem
  obtain ⟨q, hq, heq⟩ := hmem
  unfold GuruswamiSudan.weightBoundIndices at hq
  simp only [Finset.mem_filter] at hq
  simp only [Prod.mk.injEq] at heq
  have hLpos := symbolicModifiedGSCap_pos hn hk hm
  have hq2 : q.2 = 0 := heq.2
  have hq1 : q.1 = symbolicModifiedGSCap n k m := by omega
  have hw := hq.2
  rw [hq2, hq1] at hw
  simp only [mul_zero, add_zero] at hw
  omega

private theorem symbolicUpperTriangleBase_card (n k m : ℕ) :
    (symbolicUpperTriangleBase n k m).card =
      GuruswamiSudan.numVars (k + 2) (symbolicModifiedGSCap n k m - 1) := by
  classical
  let s := GuruswamiSudan.weightBoundIndices (k + 2)
    (symbolicModifiedGSCap n k m - 1)
  let f : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + p.2, p.2)
  have hinj : Set.InjOn f (s : Set (ℕ × ℕ)) := by
    intro p hp q hq h
    rcases p with ⟨p₁, p₂⟩
    rcases q with ⟨q₁, q₂⟩
    simp only [f, Prod.mk.injEq] at h ⊢
    omega
  unfold symbolicUpperTriangleBase GuruswamiSudan.numVars
  exact Finset.card_image_iff.mpr hinj

private noncomputable def symbolicUpperTriangleCandidates (n k m : ℕ) : Finset (ℕ × ℕ) :=
  if (symbolicModifiedGSCap n k m : ℝ) < D_X ((k + 1 : ℚ) / n) n m then
    insert (symbolicModifiedGSCap n k m, 0) (symbolicUpperTriangleBase n k m)
  else
    symbolicUpperTriangleBase n k m

private theorem symbolicUpperTriangleCandidates_support {n k m : ℕ}
    (hn : 0 < n) (hk : 0 < k) (hm : 1 ≤ m) :
    ∀ p ∈ symbolicUpperTriangleCandidates n k m,
      p.2 ≤ p.1 ∧
      ((p.1 + k * p.2 : ℕ) : ℝ) < D_X ((k + 1 : ℚ) / n) n m := by
  intro p hp
  have hLpos := symbolicModifiedGSCap_pos hn hk hm
  have hLle := symbolicModifiedGSCap_le_DX (n := n) (k := k) (m := m) hn
  unfold symbolicUpperTriangleCandidates at hp
  split at hp
  · rename_i hstrict
    simp only [Finset.mem_insert] at hp
    rcases hp with rfl | hp
    · exact ⟨by simp only [Nat.zero_le], by simpa using hstrict⟩
    · unfold symbolicUpperTriangleBase at hp
      rw [Finset.mem_image] at hp
      obtain ⟨q, hq, rfl⟩ := hp
      unfold GuruswamiSudan.weightBoundIndices at hq
      simp only [Finset.mem_filter] at hq
      have hweight : q.1 + (k + 1) * q.2 ≤ symbolicModifiedGSCap n k m - 1 := by
        simpa only [show k + 2 - 1 = k + 1 by omega] using hq.2
      constructor
      · omega
      · have heq : q.1 + q.2 + k * q.2 = q.1 + (k + 1) * q.2 := by ring
        have hnat : q.1 + q.2 + k * q.2 < symbolicModifiedGSCap n k m := by
          rw [heq]
          omega
        exact (by exact_mod_cast hnat :
          ((q.1 + q.2 + k * q.2 : ℕ) : ℝ) < symbolicModifiedGSCap n k m) |>.trans_le hLle
  · unfold symbolicUpperTriangleBase at hp
    rw [Finset.mem_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    unfold GuruswamiSudan.weightBoundIndices at hq
    simp only [Finset.mem_filter] at hq
    have hweight : q.1 + (k + 1) * q.2 ≤ symbolicModifiedGSCap n k m - 1 := by
      simpa only [show k + 2 - 1 = k + 1 by omega] using hq.2
    constructor
    · omega
    · have heq : q.1 + q.2 + k * q.2 = q.1 + (k + 1) * q.2 := by ring
      have hnat : q.1 + q.2 + k * q.2 < symbolicModifiedGSCap n k m := by
        rw [heq]
        omega
      exact (by exact_mod_cast hnat :
        ((q.1 + q.2 + k * q.2 : ℕ) : ℝ) < symbolicModifiedGSCap n k m) |>.trans_le hLle

open scoped BigOperators in
private def symbolicYSum (A : Finset (ℕ × ℕ)) : ℕ := ∑ p ∈ A, p.2

private def SymbolicGSConstraintIndex (n m : ℕ) (A : Finset (ℕ × ℕ)) :=
  Fin n × (GuruswamiSudan.constraintIndices m) × Fin (symbolicYSum A + 1)

private abbrev SymbolicGSIndex (A : Finset (ℕ × ℕ)) :=
  Σ p : {q // q ∈ A}, Fin (symbolicYSum A - p.1.2 + 1)

private noncomputable def symbolicGSBasis {F : Type} [Field F]
    {A : Finset (ℕ × ℕ)} (q : SymbolicGSIndex A) :
    Polynomial (Polynomial (Polynomial F)) :=
  Polynomial.monomial q.1.1.2
    (Polynomial.monomial q.1.1.1 (Polynomial.monomial q.2.1 1))

private theorem symbolicGSBasis_shift_coeff_formula {F : Type} [Field F]
    {A : Finset (ℕ × ℕ)} (q : SymbolicGSIndex A)
    (x y₀ y₁ : F) (s t : ℕ) :
    ((Polynomial.Bivariate.shift (symbolicGSBasis (F := F) q)
      (Polynomial.C x)
      (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁)).coeff t).coeff s =
    Polynomial.monomial q.2.1
      (x ^ (q.1.1.1 - s) * (q.1.1.1.choose s : F) * (q.1.1.2.choose t : F)) *
      (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁) ^ (q.1.1.2 - t) := by
  classical
  unfold symbolicGSBasis Polynomial.Bivariate.shift
  rw [Polynomial.monomial_comp, Polynomial.map_mul, Polynomial.map_C,
    Polynomial.map_pow, symbolicOuterAffine_map]
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_add_C_pow]
  rw [← Polynomial.C_eq_natCast]
  rw [← map_pow, ← map_mul, Polynomial.coeff_mul_C]
  rw [Polynomial.coe_compRingHom_apply, symbolicInnerMonomial_shift_coeff]
  rw [← Polynomial.C_eq_natCast]
  calc
    Polynomial.monomial q.2.1
        (x ^ (q.1.1.1 - s) * (q.1.1.1.choose s : F)) *
        ((Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁) ^ (q.1.1.2 - t) *
          Polynomial.C (q.1.1.2.choose t : F)) =
      (Polynomial.monomial q.2.1
        (x ^ (q.1.1.1 - s) * (q.1.1.1.choose s : F)) *
          Polynomial.C (q.1.1.2.choose t : F)) *
        (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁) ^ (q.1.1.2 - t) := by ring
    _ = Polynomial.monomial q.2.1
        (x ^ (q.1.1.1 - s) * (q.1.1.1.choose s : F) * (q.1.1.2.choose t : F)) *
        (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁) ^ (q.1.1.2 - t) := by
      rw [Polynomial.monomial_mul_C]

private theorem symbolicGSBasis_shift_coeff_natDegree_le {F : Type} [Field F]
    {A : Finset (ℕ × ℕ)} (q : SymbolicGSIndex A)
    (x y₀ y₁ : F) (s t : ℕ) :
    (((Polynomial.Bivariate.shift (symbolicGSBasis (F := F) q)
      (Polynomial.C x)
      (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁)).coeff t).coeff s).natDegree ≤
      q.2.1 + q.1.1.2 := by
  rw [symbolicGSBasis_shift_coeff_formula]
  have hL : (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁).natDegree ≤ 1 := by
    rw [show Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁ =
      Polynomial.C y₁ * Polynomial.X + Polynomial.C y₀ by ring]
    exact Polynomial.natDegree_linear_le
  have hpow := Polynomial.natDegree_pow_le_of_le (q.1.1.2 - t) hL
  have hmono := Polynomial.natDegree_monomial_le
    (m := q.2.1)
    (x ^ (q.1.1.1 - s) * (q.1.1.1.choose s : F) * (q.1.1.2.choose t : F))
  calc
    (Polynomial.monomial q.2.1
        (x ^ (q.1.1.1 - s) * (q.1.1.1.choose s : F) * (q.1.1.2.choose t : F)) *
      (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁) ^ (q.1.1.2 - t)).natDegree
        ≤ (Polynomial.monomial q.2.1
          (x ^ (q.1.1.1 - s) * (q.1.1.1.choose s : F) * (q.1.1.2.choose t : F))).natDegree +
          ((Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁) ^ (q.1.1.2 - t)).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ q.2.1 + (q.1.1.2 - t) := by
      exact add_le_add hmono (by simpa only [mul_one] using hpow)
    _ ≤ q.2.1 + q.1.1.2 := by omega

private noncomputable instance symbolicGSConstraintIndexFintype (n m : ℕ)
    (A : Finset (ℕ × ℕ)) : Fintype (SymbolicGSConstraintIndex n m A) := by
  unfold SymbolicGSConstraintIndex
  infer_instance

private theorem symbolicGSConstraintIndex_card (n m : ℕ) (A : Finset (ℕ × ℕ)) :
    Fintype.card (SymbolicGSConstraintIndex n m A) =
      GuruswamiSudan.numConstraints n m * (symbolicYSum A + 1) := by
  classical
  change Fintype.card
    (Fin n × ((GuruswamiSudan.constraintIndices m) × Fin (symbolicYSum A + 1))) = _
  rw [Fintype.card_prod, Fintype.card_prod]
  simp only [Fintype.card_fin, Fintype.card_coe, GuruswamiSudan.numConstraints,
    Nat.mul_assoc]

open scoped BigOperators in
private theorem symbolicGSIndex_card_sum (A : Finset (ℕ × ℕ)) :
    Fintype.card (SymbolicGSIndex A) =
      ∑ p : {q // q ∈ A}, (symbolicYSum A - p.1.2 + 1) := by
  classical
  simpa only [Fintype.card_fin] using
    (Fintype.card_sigma :
      Fintype.card (Σ p : {q // q ∈ A}, Fin (symbolicYSum A - p.1.2 + 1)) =
        ∑ p : {q // q ∈ A}, Fintype.card (Fin (symbolicYSum A - p.1.2 + 1)))

private noncomputable def symbolicGSPolyLinearMap {F : Type} [Field F]
    (A : Finset (ℕ × ℕ)) : (SymbolicGSIndex A → F) →ₗ[F]
      Polynomial (Polynomial (Polynomial F)) :=
  Finsupp.linearCombination F (fun q : SymbolicGSIndex A =>
    Polynomial.monomial q.1.1.2
      (Polynomial.monomial q.1.1.1 (Polynomial.monomial q.2.1 1))) ∘ₗ
    (Finsupp.linearEquivFunOnFinite F F (SymbolicGSIndex A)).symm.toLinearMap

private noncomputable def symbolicGSConstraintMap {F : Type} [Field F]
    (n m : ℕ) (A : Finset (ℕ × ℕ)) (ωs : Fin n ↪ F) (u₀ u₁ : Fin n → F) :
    (SymbolicGSIndex A → F) →ₗ[F] (SymbolicGSConstraintIndex n m A → F) :=
  LinearMap.pi (fun q =>
    symbolicGSEvalConstraint
      (Polynomial.C (ωs q.1))
      (Polynomial.C (u₀ q.1) + Polynomial.X * Polynomial.C (u₁ q.1))
      q.2.1.1.1 q.2.1.1.2 q.2.2 ∘ₗ
    symbolicGSPolyLinearMap (F := F) A)

private structure SymbolicGSKernelWitness {F : Type} [Field F]
    (n m : ℕ) (A : Finset (ℕ × ℕ)) (ωs : Fin n ↪ F) (u₀ u₁ : Fin n → F) where
  c : SymbolicGSIndex A → F
  c_ne_zero : c ≠ 0
  constraints : symbolicGSConstraintMap n m A ωs u₀ u₁ c = 0

open scoped BigOperators in
private noncomputable def symbolicGSPoly {F : Type} [Field F] (A : Finset (ℕ × ℕ))
    (c : SymbolicGSIndex A → F) : Polynomial (Polynomial (Polynomial F)) :=
  symbolicGSPolyLinearMap (F := F) A c

private theorem symbolicGSConstraintMap_apply {F : Type} [Field F]
    (n m : ℕ) (A : Finset (ℕ × ℕ)) (ωs : Fin n ↪ F) (u₀ u₁ : Fin n → F)
    (c : SymbolicGSIndex A → F) (q : SymbolicGSConstraintIndex n m A) :
    symbolicGSConstraintMap n m A ωs u₀ u₁ c q =
      ((((Polynomial.Bivariate.shift (symbolicGSPoly (F := F) A c)
        (Polynomial.C (ωs q.1))
        (Polynomial.C (u₀ q.1) + Polynomial.X * Polynomial.C (u₁ q.1))).coeff
          q.2.1.1.2).coeff q.2.1.1.1).coeff q.2.2) := by
  rfl

private theorem symbolicGSPolyMultiplicityBridge {F : Type} [Field F] [DecidableEq F]
    {m n : ℕ} {A : Finset (ℕ × ℕ)} {ωs : Fin n ↪ F} {u₀ u₁ : Fin n → F}
    {c : SymbolicGSIndex A → F}
    (hQ : symbolicGSPoly (F := F) A c ≠ 0)
    (hvan : ∀ i s t, s + t < m →
      (((Polynomial.Bivariate.shift (symbolicGSPoly (F := F) A c)
        (Polynomial.C (ωs i))
        (Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (u₁ i))).coeff t).coeff s) = 0) :
    ∀ i, m ≤ Polynomial.Bivariate.rootMultiplicity
      (symbolicGSPoly (F := F) A c)
      (Polynomial.C (ωs i))
      (Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (u₁ i)) := by
  intro i
  let g := Polynomial.Bivariate.shift (symbolicGSPoly (F := F) A c)
    (Polynomial.C (ωs i))
    (Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (u₁ i))
  have hg : ∀ s t, s + t < m → Polynomial.Bivariate.coeff g s t = 0 := by
    intro s t hst
    exact hvan i s t hst
  have H := (Polynomial.Bivariate.rootMultiplicity₀_ge_iff g m).mp hg
  have hgne : g ≠ 0 := Polynomial.Bivariate.shift_ne_zero _ _ _ hQ
  have hroot : Polynomial.Bivariate.rootMultiplicity₀ g ≠ none :=
    Polynomial.Bivariate.rootMultiplicity₀_ne_none g hgne
  change (some m : Option ℕ) ≤ Polynomial.Bivariate.rootMultiplicity₀ g
  cases hr : Polynomial.Bivariate.rootMultiplicity₀ g with
  | none => exact False.elim (hroot hr)
  | some r =>
      have hmr : m ≤ r := H r (by simp only [hr, Option.mem_def])
      simpa only [hr, Option.some_le_some] using hmr

open scoped BigOperators in
private theorem symbolicGSPoly_eq_sum {F : Type} [Field F]
    (A : Finset (ℕ × ℕ)) (c : SymbolicGSIndex A → F) :
    symbolicGSPoly (F := F) A c =
      ∑ q : SymbolicGSIndex A, c q •
        Polynomial.monomial q.1.1.2
          (Polynomial.monomial q.1.1.1 (Polynomial.monomial q.2.1 1)) := by
  unfold symbolicGSPoly symbolicGSPolyLinearMap
  rw [Finsupp.linearCombination_eq_fintype_linearCombination,
    Fintype.linearCombination_apply]

open scoped BigOperators in
private theorem symbolicGSPoly_coeff_pair {F : Type} [Field F]
    (A : Finset (ℕ × ℕ)) (c : SymbolicGSIndex A → F) (i j : ℕ) :
    ((symbolicGSPoly (F := F) A c).coeff j).coeff i =
      ∑ q : SymbolicGSIndex A,
        if q.1.1 = (i, j) then Polynomial.monomial q.2.1 (c q) else 0 := by
  classical
  rw [symbolicGSPoly_eq_sum]
  rw [Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hp : q.1.1 = (i, j)
  · have hi : q.1.1.1 = i := congrArg Prod.fst hp
    have hj : q.1.1.2 = j := congrArg Prod.snd hp
    simp [
      Polynomial.smul_monomial, hp]
  · have hcases : q.1.1.2 ≠ j ∨ q.1.1.1 ≠ i := by
      by_contra h
      push Not at h
      exact hp (Prod.ext h.2 h.1)
    rcases hcases with hj | hi
    · simp [Polynomial.coeff_smul, Polynomial.coeff_monomial, hj, hp]
    · by_cases hj : q.1.1.2 = j
      · simp [Polynomial.coeff_smul, Polynomial.coeff_monomial, hi, hj, hp]
      · simp [Polynomial.coeff_smul, Polynomial.coeff_monomial, hj, hp]

open scoped BigOperators in
private theorem symbolicGSPoly_coeff_index {F : Type} [Field F]
    (A : Finset (ℕ × ℕ)) (c : SymbolicGSIndex A → F) (q : SymbolicGSIndex A) :
    ((((symbolicGSPoly (F := F) A c).coeff q.1.1.2).coeff q.1.1.1).coeff q.2.1) =
      c q := by
  classical
  rw [symbolicGSPoly_coeff_pair]
  change (∑ r ∈ Finset.univ,
    (if r.1.1 = q.1.1 then Polynomial.monomial r.2.1 (c r) else 0)).coeff q.2.1 = c q
  rw [Polynomial.finsetSum_coeff]
  rw [Finset.sum_eq_single q]
  · simp []
  · intro r hr hrq
    by_cases hp : r.1.1 = q.1.1
    · have hz : r.2.1 ≠ q.2.1 := by
        intro hz
        apply hrq
        rcases r with ⟨rp, rh⟩
        rcases q with ⟨qp, qh⟩
        simp only at hp hz ⊢
        have hp' : rp = qp := Subtype.ext hp
        subst qp
        have hz' : rh = qh := Fin.ext hz
        subst qh
        rfl
      simp [hp, hz, Polynomial.coeff_monomial]
    · simp [hp]
  · simp

open scoped BigOperators in
private theorem symbolicGSPoly_coeff_ne_zero_mem {F : Type} [Field F]
    (A : Finset (ℕ × ℕ)) (c : SymbolicGSIndex A → F) {i j : ℕ}
    (hcoeff : ((symbolicGSPoly (F := F) A c).coeff j).coeff i ≠ 0) :
    (i, j) ∈ A := by
  by_contra hp
  rw [symbolicGSPoly_coeff_pair] at hcoeff
  apply hcoeff
  apply Finset.sum_eq_zero
  intro q hq
  rw [if_neg]
  intro heq
  apply hp
  rw [← heq]
  exact q.1.2

private theorem symbolicGSPoly_ne_zero {F : Type} [Field F]
    (A : Finset (ℕ × ℕ)) (c : SymbolicGSIndex A → F) (hc : c ≠ 0) :
    symbolicGSPoly (F := F) A c ≠ 0 := by
  intro hQ
  apply hc
  funext q
  have h := symbolicGSPoly_coeff_index (F := F) A c q
  rw [hQ] at h
  simp only [Polynomial.coeff_zero] at h
  exact h.symm

open scoped BigOperators in
private theorem symbolicGSPoly_shift_coeff_eq_sum {F : Type} [Field F]
    (A : Finset (ℕ × ℕ)) (c : SymbolicGSIndex A → F)
    (x y : Polynomial F) (s t : ℕ) :
    ((Polynomial.Bivariate.shift (symbolicGSPoly (F := F) A c) x y).coeff t).coeff s =
      ∑ q : SymbolicGSIndex A, c q •
        ((Polynomial.Bivariate.shift
          (Polynomial.monomial q.1.1.2
            (Polynomial.monomial q.1.1.1 (Polynomial.monomial q.2.1 1))) x y).coeff t).coeff s := by
  ext d
  change symbolicGSEvalConstraint x y s t d (symbolicGSPoly (F := F) A c) = _
  rw [symbolicGSPoly_eq_sum, map_sum]
  simp only [map_smul]
  change (∑ q : SymbolicGSIndex A,
      c q • symbolicGSEvalConstraint x y s t d
        (Polynomial.monomial q.1.1.2
          (Polynomial.monomial q.1.1.1 (Polynomial.monomial q.2.1 1)))) =
    (∑ q ∈ Finset.univ, c q •
      ((Polynomial.Bivariate.shift
        (Polynomial.monomial q.1.1.2
          (Polynomial.monomial q.1.1.1 (Polynomial.monomial q.2.1 1)))
            x y).coeff t).coeff s).coeff d
  rw [Polynomial.finsetSum_coeff]
  rfl


private theorem symbolicGSPoly_weighted_lt {F : Type} [Field F]
    (A : Finset (ℕ × ℕ)) (c : SymbolicGSIndex A → F) {k : ℕ} {D : ℝ}
    (hQ : symbolicGSPoly (F := F) A c ≠ 0)
    (hA : ∀ p ∈ A, ((p.1 + k * p.2 : ℕ) : ℝ) < D) :
    Polynomial.Bivariate.natWeightedDegree (symbolicGSPoly (F := F) A c) 1 k < D := by
  unfold Polynomial.Bivariate.natWeightedDegree
  obtain ⟨j, hj, hsup⟩ := Finset.exists_mem_eq_sup
    (symbolicGSPoly (F := F) A c).support
    (Polynomial.nonempty_support_iff.mpr hQ)
    (fun j => 1 * ((symbolicGSPoly (F := F) A c).coeff j).natDegree + k * j)
  rw [hsup]
  norm_num
  have hc : (symbolicGSPoly (F := F) A c).coeff j ≠ 0 :=
    Polynomial.mem_support_iff.mp hj
  have hi : ((symbolicGSPoly (F := F) A c).coeff j).natDegree ∈
      ((symbolicGSPoly (F := F) A c).coeff j).support :=
    Polynomial.natDegree_mem_support_of_nonzero hc
  have hp := symbolicGSPoly_coeff_ne_zero_mem A c
    (Polynomial.mem_support_iff.mp hi)
  simpa only [Prod.fst, Prod.snd, Nat.cast_add, Nat.cast_mul] using
    hA (((symbolicGSPoly (F := F) A c).coeff j).natDegree, j) hp

open scoped BigOperators in
private theorem symbolicUpperTriangleBase_ySum (n k m : ℕ) :
    symbolicYSum (symbolicUpperTriangleBase n k m) =
      ∑ p ∈ GuruswamiSudan.weightBoundIndices (k + 2)
        (symbolicModifiedGSCap n k m - 1), p.2 := by
  classical
  let s := GuruswamiSudan.weightBoundIndices (k + 2)
    (symbolicModifiedGSCap n k m - 1)
  let f : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + p.2, p.2)
  have hinj : Set.InjOn f (s : Set (ℕ × ℕ)) := by
    intro p hp q hq h
    rcases p with ⟨p₁, p₂⟩
    rcases q with ⟨q₁, q₂⟩
    simp only [f, Prod.mk.injEq] at h ⊢
    omega
  unfold symbolicYSum symbolicUpperTriangleBase
  rw [Finset.sum_image hinj]

open scoped BigOperators in
private theorem symbolicUpperTriangleCandidates_ySum_eq_base (n k m : ℕ) :
    symbolicYSum (symbolicUpperTriangleCandidates n k m) =
      symbolicYSum (symbolicUpperTriangleBase n k m) := by
  classical
  unfold symbolicUpperTriangleCandidates symbolicYSum
  split <;> simp

open scoped BigOperators in
private theorem symbolicUpperTriangleCandidates_ySum_nat_bound {n k m : ℕ}
    (hn : 0 < n) (hk : 0 < k) (hm : 1 ≤ m) :
    6 * (k + 1) ^ 2 * symbolicYSum (symbolicUpperTriangleCandidates n k m) ≤
      (symbolicModifiedGSCap n k m) ^ 3 := by
  rw [symbolicUpperTriangleCandidates_ySum_eq_base,
    symbolicUpperTriangleBase_ySum]
  have h := GuruswamiSudan.sum_snd_weightBoundIndices_le
    (k := k + 2) (D := symbolicModifiedGSCap n k m - 1) (by omega : 1 < k + 2)
  have hLpos := symbolicModifiedGSCap_pos hn hk hm
  simpa only [show k + 2 - 1 = k + 1 by omega,
    Nat.sub_add_cancel (by omega : 1 ≤ symbolicModifiedGSCap n k m)] using h

private theorem symbolic_DX_cube_div_identity {n k m : ℕ} (hn : 0 < n) (hk : 0 < k) :
    D_X ((k + 1 : ℚ) / n) n m ^ 3 / (6 * ((k : ℝ) + 1) ^ 2) =
      n * (m + 1 / (2 : ℚ)) ^ 3 /
        (6 * Real.sqrt ((k + 1) / n)) := by
  unfold D_X
  push_cast
  set s : ℝ := Real.sqrt (((k : ℝ) + 1) / n) with hs
  have hspos : 0 < s := by
    rw [hs]
    positivity
  have hsne : s ≠ 0 := ne_of_gt hspos
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hsquare : s ^ 2 = ((k : ℝ) + 1) / n := by
    rw [hs, Real.sq_sqrt (by positivity)]
  field_simp [hsne, hn0]
  rw [show ((k : ℝ) + 1) = s ^ 2 * n by
    rw [hsquare]
    field_simp [hn0]]
  ring

private theorem symbolicUpperTriangleCandidates_ySum_real_bound {n k m : ℕ}
    (hn : 0 < n) (hk : 0 < k) (hm : 1 ≤ m) :
    (symbolicYSum (symbolicUpperTriangleCandidates n k m) : ℝ) ≤
      n * (m + 1 / (2 : ℚ)) ^ 3 /
        (6 * Real.sqrt ((k + 1) / n)) := by
  have hnat := symbolicUpperTriangleCandidates_ySum_nat_bound hn hk hm
  have hcast : 6 * ((k : ℝ) + 1) ^ 2 *
      (symbolicYSum (symbolicUpperTriangleCandidates n k m) : ℝ) ≤
      (symbolicModifiedGSCap n k m : ℝ) ^ 3 := by
    exact_mod_cast hnat
  have hcap := symbolicModifiedGSCap_le_DX (n := n) (k := k) (m := m) hn
  have hcube : (symbolicModifiedGSCap n k m : ℝ) ^ 3 ≤
      D_X ((k + 1 : ℚ) / n) n m ^ 3 := by
    gcongr
  rw [← symbolic_DX_cube_div_identity (n := n) (k := k) (m := m) hn hk]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < 6 * ((k : ℝ) + 1) ^ 2)]
  simpa only [mul_comm] using hcast.trans hcube

private theorem symbolic_DX_sq_identity {n k m : ℕ} (hn : 0 < n) :
    D_X ((k + 1 : ℚ) / n) n m ^ 2 =
      ((m : ℝ) + 1 / 2) ^ 2 * ((k : ℝ) + 1) * n := by
  unfold D_X
  rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity)]
  push_cast
  field_simp [show (n : ℝ) ≠ 0 by exact_mod_cast (ne_of_gt hn)]

private theorem symbolicModifiedGSCap_strict_k_one_n_one {m : ℕ} (_hm : 1 ≤ m) :
    (symbolicModifiedGSCap 1 1 m : ℝ) < D_X (2 : ℚ) 1 m := by
  have hle := symbolicModifiedGSCap_le_DX (n := 1) (k := 1) (m := m) (by omega)
  norm_num at hle
  by_contra hnot
  have heq : (symbolicModifiedGSCap 1 1 m : ℝ) = D_X (2 : ℚ) 1 m :=
    le_antisymm hle (le_of_not_gt hnot)
  have hsquare := symbolic_DX_sq_identity (n := 1) (k := 1) (m := m) (by omega)
  norm_num at hsquare
  rw [← heq] at hsquare
  have hdoubleR : (((2 * (symbolicModifiedGSCap 1 1 m) ^ 2 : ℕ) : ℝ)) =
      (((4 * m * (m + 1) + 1 : ℕ) : ℝ)) := by
    push_cast
    nlinarith
  have hdouble : 2 * (symbolicModifiedGSCap 1 1 m) ^ 2 =
      4 * m * (m + 1) + 1 := by exact_mod_cast hdoubleR
  have hmod := congrArg (fun x : ℕ => x % 2) hdouble
  norm_num [Nat.add_mod, Nat.mul_mod] at hmod

private theorem symbolic_numConstraints_scaled (n k m : ℕ) :
    2 * (k + 1) * GuruswamiSudan.numConstraints n m =
      (k + 1) * n * m * (m + 1) := by
  unfold GuruswamiSudan.numConstraints
  rw [GuruswamiSudan.card_constraintIndices]
  have heven : Even (m * (m + 1)) := Nat.even_mul_succ_self m
  have htwo : 2 * (m * (m + 1) / 2) = m * (m + 1) :=
    Nat.two_mul_div_two_of_even heven
  calc
    2 * (k + 1) * (n * (m * (m + 1) / 2))
        = (k + 1) * n * (2 * (m * (m + 1) / 2)) := by ring
    _ = (k + 1) * n * (m * (m + 1)) := by rw [htwo]
    _ = (k + 1) * n * m * (m + 1) := by ring

private theorem symbolic_numVars_lower_bound_boundary (a D : ℕ) (ha : 0 < a) :
    (D + 1) ^ 2 + a * (D + 1) ≤
      2 * a * GuruswamiSudan.numVars (a + 1) D := by
  have h_numVars_def : GuruswamiSudan.numVars (a + 1) D =
      ((D / a) + 1) * (2 * D + 2 - a * (D / a)) / 2 := by
    simpa only [Nat.add_sub_cancel] using
      (GuruswamiSudan.numVars_eq_of_gt_one (D := D) (k := a + 1) (by omega : 1 < a + 1))
  rw [h_numVars_def, ← Nat.mul_div_assoc]
  · rw [Nat.le_div_iff_mul_le] <;> ring_nf
    · zify
      rw [Nat.cast_sub] <;> push_cast <;>
        nlinarith [D.div_mul_le_self a, D.div_add_mod a, D.mod_lt ha]
    · norm_num
  · cases le_total (2 * D + 2) (a * (D / a)) <;>
      simp_all [← even_iff_two_dvd, parity_simps]
    by_cases h : Even (D / a) <;> simp_all [parity_simps]

private theorem symbolicUpperTriangleBase_card_ge_k_one_n_one {m : ℕ} (hm : 1 ≤ m) :
    GuruswamiSudan.numConstraints 1 m ≤
      (symbolicUpperTriangleBase 1 1 m).card := by
  let T := symbolicModifiedGSCap 1 1 m
  have hTpos : 0 < T := symbolicModifiedGSCap_pos (by omega) (by omega) hm
  have hbound := symbolic_numVars_lower_bound_boundary 2 (T - 1) (by omega)
  have hcard := symbolicUpperTriangleBase_card 1 1 m
  rw [← hcard] at hbound
  have hTone : T - 1 + 1 = T := by omega
  rw [hTone] at hbound
  have hsq := symbolicModifiedGSCap_sq_gt (n := 1) (k := 1) (m := m) (by omega)
  have hident : ((m : ℝ) + 1 / 2) ^ 2 =
      (m : ℝ) * (m + 1) + 1 / 4 := by ring
  rw [hident] at hsq
  norm_num at hsq
  change ((m : ℝ) * (m + 1) + 1 / 4) * 2 < ((T : ℝ) + 1) ^ 2 at hsq
  have hscaled : 2 * m * (m + 1) ≤ T ^ 2 + 2 * T := by
    by_contra hnot
    have hplus : T ^ 2 + 2 * T + 1 ≤ 2 * m * (m + 1) := by omega
    have hplusR : (((T ^ 2 + 2 * T + 1 : ℕ) : ℝ)) ≤
        (((2 * m * (m + 1) : ℕ) : ℝ)) := by exact_mod_cast hplus
    push_cast at hplusR
    nlinarith
  have hscaled' : 2 * (1 + 1) * GuruswamiSudan.numConstraints 1 m ≤
      T ^ 2 + (1 + 1) * T := by
    rw [symbolic_numConstraints_scaled]
    simpa only [Nat.reduceAdd, Nat.reduceMul, one_mul] using hscaled
  have hmul : 2 * (1 + 1) * GuruswamiSudan.numConstraints 1 m ≤
      2 * (1 + 1) * (symbolicUpperTriangleBase 1 1 m).card :=
    hscaled'.trans hbound
  exact le_of_mul_le_mul_left hmul (by omega)

private theorem symbolicUpperTriangleBase_card_gt_k_one_of_two_le_n {n m : ℕ}
    (hn : 2 ≤ n) (hm : 1 ≤ m) :
    GuruswamiSudan.numConstraints n m <
      (symbolicUpperTriangleBase n 1 m).card := by
  let T := symbolicModifiedGSCap n 1 m
  have hnpos : 0 < n := by omega
  have hTpos : 0 < T := symbolicModifiedGSCap_pos hnpos (by omega) hm
  have hbound := symbolic_numVars_lower_bound_boundary 2 (T - 1) (by omega)
  have hcard := symbolicUpperTriangleBase_card n 1 m
  rw [← hcard] at hbound
  have hTone : T - 1 + 1 = T := by omega
  rw [hTone] at hbound
  have hsq := symbolicModifiedGSCap_sq_gt (n := n) (k := 1) (m := m) hnpos
  have hident : ((m : ℝ) + 1 / 2) ^ 2 =
      (m : ℝ) * (m + 1) + 1 / 4 := by ring
  rw [hident] at hsq
  have hncast : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hscaledR : ((2 * n * m * (m + 1) : ℕ) : ℝ) <
      ((T ^ 2 + 2 * T : ℕ) : ℝ) := by
    push_cast
    nlinarith
  have hscaled : 2 * n * m * (m + 1) < T ^ 2 + 2 * T := by
    exact_mod_cast hscaledR
  have hscaled' : 2 * (1 + 1) * GuruswamiSudan.numConstraints n m <
      T ^ 2 + (1 + 1) * T := by
    rw [symbolic_numConstraints_scaled]
    simpa only [Nat.reduceAdd, Nat.reduceMul] using hscaled
  have hmul : 2 * (1 + 1) * GuruswamiSudan.numConstraints n m <
      2 * (1 + 1) * (symbolicUpperTriangleBase n 1 m).card :=
    hscaled'.trans_le hbound
  exact lt_of_mul_lt_mul_left' hmul

private theorem symbolicUpperTriangleBase_card_gt_of_two_le_k {n k m : ℕ}
    (hn : 0 < n) (hk : 2 ≤ k) (hm : 1 ≤ m) :
    GuruswamiSudan.numConstraints n m <
      (symbolicUpperTriangleBase n k m).card := by
  let T := symbolicModifiedGSCap n k m
  have hTpos : 0 < T := symbolicModifiedGSCap_pos hn (by omega) hm
  have hbound := symbolic_numVars_lower_bound_boundary (k + 1) (T - 1) (by omega)
  have hcard := symbolicUpperTriangleBase_card n k m
  rw [← hcard] at hbound
  have hTone : T - 1 + 1 = T := by omega
  rw [hTone] at hbound
  have hsq := symbolicModifiedGSCap_sq_gt (n := n) (k := k) (m := m) hn
  have hident : ((m : ℝ) + 1 / 2) ^ 2 =
      (m : ℝ) * (m + 1) + 1 / 4 := by ring
  rw [hident] at hsq
  have hTcast : (1 : ℝ) ≤ T := by exact_mod_cast hTpos
  have hkcast : (2 : ℝ) ≤ k := by exact_mod_cast hk
  have hscaledR : (((k + 1) * n * m * (m + 1) : ℕ) : ℝ) <
      ((T ^ 2 + (k + 1) * T : ℕ) : ℝ) := by
    push_cast
    nlinarith [mul_pos (show (0 : ℝ) < k + 1 by positivity)
      (show (0 : ℝ) < n by exact_mod_cast hn)]
  have hscaled : (k + 1) * n * m * (m + 1) <
      T ^ 2 + (k + 1) * T := by exact_mod_cast hscaledR
  rw [← symbolic_numConstraints_scaled] at hscaled
  have hmul : 2 * (k + 1) * GuruswamiSudan.numConstraints n m <
      2 * (k + 1) * (symbolicUpperTriangleBase n k m).card :=
    hscaled.trans_le hbound
  exact lt_of_mul_lt_mul_left' hmul

private theorem symbolicUpperTriangleCandidates_card_gt {n k m : ℕ}
    (hn : 0 < n) (hk : 0 < k) (hm : 1 ≤ m) :
    GuruswamiSudan.numConstraints n m <
      (symbolicUpperTriangleCandidates n k m).card := by
  by_cases hk2 : 2 ≤ k
  · have hbase := symbolicUpperTriangleBase_card_gt_of_two_le_k hn hk2 hm
    unfold symbolicUpperTriangleCandidates
    split
    · rw [Finset.card_insert_of_notMem (symbolicCapPoint_not_mem_base hn hk hm)]
      omega
    · exact hbase
  · have hk1 : k = 1 := by omega
    subst k
    by_cases hn2 : 2 ≤ n
    · have hbase := symbolicUpperTriangleBase_card_gt_k_one_of_two_le_n hn2 hm
      unfold symbolicUpperTriangleCandidates
      split
      · rw [Finset.card_insert_of_notMem
          (symbolicCapPoint_not_mem_base hn (by omega) hm)]
        omega
      · exact hbase
    · have hn1 : n = 1 := by omega
      subst n
      have hstrict := symbolicModifiedGSCap_strict_k_one_n_one hm
      have hbase := symbolicUpperTriangleBase_card_ge_k_one_n_one hm
      unfold symbolicUpperTriangleCandidates
      rw [if_pos]
      · rw [Finset.card_insert_of_notMem
          (symbolicCapPoint_not_mem_base (by omega) (by omega) hm)]
        omega
      · norm_num at hstrict ⊢
        exact hstrict

open scoped BigOperators in
private theorem symbolic_snd_le_ySum (A : Finset (ℕ × ℕ)) {p : ℕ × ℕ} (hp : p ∈ A) :
    p.2 ≤ symbolicYSum A := by
  unfold symbolicYSum
  exact Finset.single_le_sum (fun q hq => Nat.zero_le q.2) hp

open scoped BigOperators in
private theorem symbolicGSIndex_card_closed (A : Finset (ℕ × ℕ)) :
    Fintype.card (SymbolicGSIndex A) + symbolicYSum A =
      A.card * (symbolicYSum A + 1) := by
  classical
  rw [symbolicGSIndex_card_sum]
  have hsum : (∑ p : {q // q ∈ A}, p.1.2) = symbolicYSum A := by
    rw [Finset.sum_coe_sort_eq_attach, Finset.sum_attach]
    rfl
  calc
    (∑ p : {q // q ∈ A}, (symbolicYSum A - p.1.2 + 1)) + symbolicYSum A
        = (∑ p : {q // q ∈ A}, (symbolicYSum A - p.1.2 + 1)) +
            ∑ p : {q // q ∈ A}, p.1.2 := by rw [hsum]
    _ = ∑ p : {q // q ∈ A},
          ((symbolicYSum A - p.1.2 + 1) + p.1.2) := by
      rw [← Finset.sum_add_distrib]
    _ = ∑ p : {q // q ∈ A}, (symbolicYSum A + 1) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hle := symbolic_snd_le_ySum A p.2
      omega
    _ = A.card * (symbolicYSum A + 1) := by
      simp

private theorem symbolicGSConstraintIndex_card_lt (n m : ℕ) (A : Finset (ℕ × ℕ))
    (hcount : GuruswamiSudan.numConstraints n m < A.card) :
    Fintype.card (SymbolicGSConstraintIndex n m A) <
      Fintype.card (SymbolicGSIndex A) := by
  let C := GuruswamiSudan.numConstraints n m
  let B := symbolicYSum A
  let J := Fintype.card (SymbolicGSConstraintIndex n m A)
  let I := Fintype.card (SymbolicGSIndex A)
  have hc : J = C * (B + 1) := by
    exact symbolicGSConstraintIndex_card n m A
  have hi : I + B = A.card * (B + 1) := by
    exact symbolicGSIndex_card_closed A
  have hsucc : C + 1 ≤ A.card := by omega
  have hmul : (C + 1) * (B + 1) ≤ A.card * (B + 1) :=
    Nat.mul_le_mul_right (B + 1) hsucc
  have hid : C * (B + 1) + B + 1 = (C + 1) * (B + 1) := by ring
  have hstep : J + B < (C + 1) * (B + 1) := by
    rw [hc, ← hid]
    omega
  have hsum : J + B < I + B := by
    rw [hi]
    exact hstep.trans_le hmul
  omega

private theorem exists_symbolicGSKernelWitness {F : Type} [Field F]
    (n m : ℕ) (A : Finset (ℕ × ℕ)) (ωs : Fin n ↪ F) (u₀ u₁ : Fin n → F)
    (hcount : GuruswamiSudan.numConstraints n m < A.card) :
    Nonempty (SymbolicGSKernelWitness n m A ωs u₀ u₁) := by
  have hcard := symbolicGSConstraintIndex_card_lt n m A hcount
  have hfinrank : Module.finrank F (SymbolicGSConstraintIndex n m A → F) <
      Module.finrank F (SymbolicGSIndex A → F) := by
    simpa only [Module.finrank_fintype_fun_eq_card] using hcard
  have hker : LinearMap.ker (symbolicGSConstraintMap n m A ωs u₀ u₁) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt hfinrank
  obtain ⟨c, hc, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  refine ⟨{ c := c, c_ne_zero := hc0, constraints := ?_ }⟩
  exact hc

private theorem symbolicGSIndex_z_add_y_le (A : Finset (ℕ × ℕ)) (q : SymbolicGSIndex A) :
    q.2.1 + q.1.1.2 ≤ symbolicYSum A := by
  have hy := symbolic_snd_le_ySum A q.1.2
  have hz := q.2.2
  omega

open scoped BigOperators in
private theorem symbolicGSPoly_coeff_natDegree_add_le_of_mem {F : Type} [Field F]
    (A : Finset (ℕ × ℕ)) (c : SymbolicGSIndex A → F) {i j : ℕ}
    (hp : (i, j) ∈ A) :
    (((symbolicGSPoly (F := F) A c).coeff j).coeff i).natDegree + j ≤
      symbolicYSum A := by
  rw [symbolicGSPoly_coeff_pair]
  have hjB := symbolic_snd_le_ySum A hp
  have hdeg : (∑ q : SymbolicGSIndex A,
      if q.1.1 = (i, j) then Polynomial.monomial q.2.1 (c q) else 0).natDegree ≤
      symbolicYSum A - j := by
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro q hq
    by_cases heq : q.1.1 = (i, j)
    · rw [if_pos heq]
      have hbudget := symbolicGSIndex_z_add_y_le A q
      have hj : q.1.1.2 = j := congrArg Prod.snd heq
      have hmono := Polynomial.natDegree_monomial_le (m := q.2.1) (c q)
      omega
    · rw [if_neg heq]
      simp only [Polynomial.natDegree_zero]
      omega
  omega

private theorem symbolicGSPoly_DYZ_term_le {F : Type} [Field F]
    (A : Finset (ℕ × ℕ)) (c : SymbolicGSIndex A → F) {i j : ℕ}
    (hi : i ∈ ((symbolicGSPoly (F := F) A c).coeff j).support) :
    j + (Polynomial.Bivariate.coeff (symbolicGSPoly (F := F) A c) i j).natDegree ≤
      symbolicYSum A := by
  have hp : (i, j) ∈ A := symbolicGSPoly_coeff_ne_zero_mem A c
    (Polynomial.mem_support_iff.mp hi)
  have hdeg := symbolicGSPoly_coeff_natDegree_add_le_of_mem A c hp
  unfold Polynomial.Bivariate.coeff
  omega

private theorem symbolicGSPoly_DYZ_le {F : Type} [Field F]
    (A : Finset (ℕ × ℕ)) (c : SymbolicGSIndex A → F) :
    Trivariate.D_YZ (symbolicGSPoly (F := F) A c) ≤ symbolicYSum A := by
  unfold Trivariate.D_YZ
  apply finsetMaxGetD_le
  intro outer houter
  rw [Finset.mem_image] at houter
  obtain ⟨j, hj, rfl⟩ := houter
  apply finsetMaxGetD_le
  intro inner hinner
  rw [Finset.mem_image] at hinner
  obtain ⟨i, hi, rfl⟩ := hinner
  exact symbolicGSPoly_DYZ_term_le A c hi

open scoped BigOperators in
private theorem symbolicGSPoly_shift_coeff_natDegree_le {F : Type} [Field F]
    (A : Finset (ℕ × ℕ)) (c : SymbolicGSIndex A → F)
    (x y₀ y₁ : F) (s t : ℕ) :
    (((Polynomial.Bivariate.shift (symbolicGSPoly (F := F) A c)
      (Polynomial.C x)
      (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁)).coeff t).coeff s).natDegree ≤
      symbolicYSum A := by
  rw [symbolicGSPoly_shift_coeff_eq_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro q hq
  calc
    (c q • ((Polynomial.Bivariate.shift
      (Polynomial.monomial q.1.1.2
        (Polynomial.monomial q.1.1.1 (Polynomial.monomial q.2.1 1)))
      (Polynomial.C x)
      (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁)).coeff t).coeff s).natDegree
      ≤ (((Polynomial.Bivariate.shift
        (Polynomial.monomial q.1.1.2
          (Polynomial.monomial q.1.1.1 (Polynomial.monomial q.2.1 1)))
        (Polynomial.C x)
        (Polynomial.C y₀ + Polynomial.X * Polynomial.C y₁)).coeff t).coeff s).natDegree :=
        Polynomial.natDegree_smul_le _ _
    _ ≤ q.2.1 + q.1.1.2 :=
      symbolicGSBasis_shift_coeff_natDegree_le q x y₀ y₁ s t
    _ ≤ symbolicYSum A := symbolicGSIndex_z_add_y_le A q

private theorem symbolicGSKernelWitness_shift_vanish {F : Type} [Field F]
    {n m : ℕ} (A : Finset (ℕ × ℕ)) (ωs : Fin n ↪ F) (u₀ u₁ : Fin n → F)
    (w : SymbolicGSKernelWitness n m A ωs u₀ u₁) :
    ∀ i s t, s + t < m →
      ((Polynomial.Bivariate.shift (symbolicGSPoly (F := F) A w.c)
        (Polynomial.C (ωs i))
        (Polynomial.C (u₀ i) + Polynomial.X * Polynomial.C (u₁ i))).coeff t).coeff s = 0 := by
  intro i s t hst
  apply Polynomial.ext
  intro d
  by_cases hd : d ≤ symbolicYSum A
  · have hstmem : (s, t) ∈ GuruswamiSudan.constraintIndices m := by
      unfold GuruswamiSudan.constraintIndices
      refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, hst⟩
      · exact Finset.mem_range.mpr (by omega)
      · exact Finset.mem_range.mpr (by omega)
    let q : SymbolicGSConstraintIndex n m A :=
      (i, (⟨(s, t), hstmem⟩, ⟨d, Nat.lt_succ_of_le hd⟩))
    have hzero := congrFun w.constraints q
    simp only [Pi.zero_apply] at hzero
    rw [symbolicGSConstraintMap_apply] at hzero
    exact hzero
  · have hdeg := symbolicGSPoly_shift_coeff_natDegree_le A w.c
      (ωs i) (u₀ i) (u₁ i) s t
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdeg (by omega))


private theorem symbolicDY_lt_of_weighted {R : Type} [Semiring R]
    {Q : Polynomial (Polynomial R)} {k : ℕ} (hk : 0 < k) {B : ℝ}
    (hQ : ((Polynomial.Bivariate.natWeightedDegree Q 1 k : ℕ) : ℝ) < B) :
    ((Polynomial.Bivariate.natDegreeY Q : ℕ) : ℝ) < B / k := by
  have h := Polynomial.Bivariate.mul_natDegreeY_le_natWeightedDegree Q k
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  rw [lt_div_iff₀ hkR]
  calc ((Polynomial.Bivariate.natDegreeY Q : ℕ) : ℝ) * k
      = ((k * Polynomial.Bivariate.natDegreeY Q : ℕ) : ℝ) := by push_cast; ring
    _ ≤ ((Polynomial.Bivariate.natWeightedDegree Q 1 k : ℕ) : ℝ) := by exact_mod_cast h
    _ < B := hQ

private theorem modified_guruswami_has_a_solution_core
    {F : Type} [Field F] [DecidableEq F] {m n k : ℕ}
    (hn : 0 < n) (hk : 0 < k) (hm : 1 ≤ m)
    {ωs : Fin n ↪ F} {u₀ u₁ : Fin n → F} :
    ∃ Q : F[Z][X][Y], ModifiedGuruswami m n k ωs Q u₀ u₁ := by
  classical
  let A := symbolicUpperTriangleCandidates n k m
  let w : SymbolicGSKernelWitness n m A ωs u₀ u₁ :=
    Classical.choice (exists_symbolicGSKernelWitness n m A ωs u₀ u₁
      (by simpa only [A] using symbolicUpperTriangleCandidates_card_gt hn hk hm))
  let Q := symbolicGSPoly (F := F) A w.c
  have hsupp := symbolicUpperTriangleCandidates_support hn hk hm
  have hweight : ∀ p ∈ A,
      ((p.1 + k * p.2 : ℕ) : ℝ) < D_X ((k + 1 : ℚ) / n) n m := by
    intro p hp
    exact (hsupp p (by simpa only [A] using hp)).2
  have hQ : Q ≠ 0 := by
    exact symbolicGSPoly_ne_zero A w.c w.c_ne_zero
  have hdeg : Polynomial.Bivariate.natWeightedDegree Q 1 k <
      D_X ((k + 1 : ℚ) / n) n m := by
    exact symbolicGSPoly_weighted_lt A w.c hQ hweight
  refine ⟨Q, {
    Q_ne_0 := hQ
    Q_deg := hdeg
    Q_multiplicity := ?_
    Q_deg_X := ?_
    Q_D_Y := ?_
    Q_D_YZ := ?_ }⟩
  · apply symbolicGSPolyMultiplicityBridge hQ
    exact symbolicGSKernelWitness_shift_vanish A ωs u₀ u₁ w
  · have hx := Polynomial.Bivariate.degreeX_le_natWeightedDegree Q k
    exact lt_of_le_of_lt (by exact_mod_cast hx) hdeg
  · have hy := symbolicDY_lt_of_weighted (Q := Q) hk hdeg
    simpa only [Trivariate.D_Y] using hy
  · have hyz := symbolicGSPoly_DYZ_le A w.c
    have hyzR : (Trivariate.D_YZ Q : ℝ) ≤ symbolicYSum A := by
      exact_mod_cast hyz
    exact hyzR.trans (by
      simpa only [A] using symbolicUpperTriangleCandidates_ySum_real_bound hn hk hm)


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
    ∃ Q : F[Z][X][Y], ModifiedGuruswami m n k ωs Q u₀ u₁ :=
  modified_guruswami_has_a_solution_core hn hk hm

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
that set, with `degX P ≤ k` and `degZ P ≤ 1`.

The three conjuncts are (5.9), (5.10) and (5.11) of [BCIKS20]. Note that (5.11) is *not* under the
`∀ z ∈ S'` binder in the paper, and that (5.9) is a division of reals; both are reflected here.

Still missing relative to the paper: the standing hypothesis on `#S` from Theorem 5.1 (eq. 5.3).
Without it the statement is false whenever `coeffs_of_close_proximity = ∅` — then `S' ⊆ ∅` forces
`#S' = 0`, while (5.9) demands `#S' > 0`. Separately, `ModifiedGuruswami` permits `D_Y Q = 0`, and
there `2 * D_Y Q = 0` makes the right-hand side of (5.9) zero rather than the paper's `+∞`. -/
lemma exists_a_set_and_a_matching_polynomial
    (h_gs : ModifiedGuruswami m n k ωs Q u₀ u₁) :
    ∃ S', ∃ (h_sub : S' ⊆ coeffs_of_close_proximity k ωs δ u₀ u₁), ∃ P : F[Z][X],
     (#S' : ℝ) > #(coeffs_of_close_proximity k ωs δ u₀ u₁) / (2 * D_Y Q) ∧
     (∀ z : S', Pz (h_sub z.2) = P.map (Polynomial.evalRingHom z.1)) ∧
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
