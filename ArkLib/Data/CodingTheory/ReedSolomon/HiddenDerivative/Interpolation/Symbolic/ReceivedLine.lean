/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.SourceMonomial
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.ConstraintMap
public import ArkLib.ToMathlib.LinearAlgebra.PrimitivePolynomialKernel


/-!
# Symbolic received-line interpolation

The concrete local-constraint matrix retains the line challenge as a polynomial variable.
Finite support reduction handles its infinite row index without assuming a finite local
contact space. An actual rank bound gives a primitive polynomial kernel, whose assembled
interpolant remains nonzero after every field-extension and challenge specialization.
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

open Polynomial

namespace ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation

open MvPolynomial
open scoped BigOperators

variable {F : Type*} [Field F] {d : ℕ}

/-- The received value `f + Z g`, retained as a polynomial in the symbolic challenge. -/
def receivedLine (f g : F) : F[X] := Polynomial.C f + Polynomial.X * Polynomial.C g

theorem receivedLine_natDegree_le (f g : F) : (receivedLine f g).natDegree ≤ 1 := by
  rw [receivedLine]
  apply (Polynomial.natDegree_add_le _ _).trans
  apply max_le
  · simp
  · exact Polynomial.natDegree_mul_le_of_le Polynomial.natDegree_X_le
      (show (Polynomial.C g).natDegree ≤ 0 by rw [Polynomial.natDegree_C])

/-- A coefficientwise polynomial-degree bound for a multivariate polynomial over `F[Z]`. -/
def CoeffDegreeLE {σ : Type*} (P : MvPolynomial σ F[X]) (B : ℕ) : Prop :=
  ∀ e, (MvPolynomial.coeff e P).natDegree ≤ B

/-- A joint coefficient/monomial weight bound.  A nonzero challenge coefficient of degree
`q` attached to a local monomial of weight `u` consumes the combined budget `q + ℓ u`.
Unlike a plain coefficient-degree bound, this predicate records the degree recovered when
translation lowers the local jet grade. -/
def GradedCoeffDegreeLE {σ : Type*} (weight : σ → ℕ)
    (P : MvPolynomial σ F[X]) (ℓ B : ℕ) : Prop :=
  ∀ e, MvPolynomial.coeff e P ≠ 0 →
    (MvPolynomial.coeff e P).natDegree + ℓ * Finsupp.weight weight e ≤ B

private theorem gradedCoeffDegreeLE_C {σ : Type*} (weight : σ → ℕ)
    {p : F[X]} {ℓ B : ℕ} (hp : p.natDegree ≤ B) :
    GradedCoeffDegreeLE weight (MvPolynomial.C p : MvPolynomial σ F[X]) ℓ B := by
  classical
  intro e he
  have : e = 0 := by
    by_contra hne
    exact he (by simp [MvPolynomial.coeff_C, Ne.symm hne])
  subst e
  simpa using hp

private theorem gradedCoeffDegreeLE_X {σ : Type*} (weight : σ → ℕ) (ℓ : ℕ) (i : σ) :
    GradedCoeffDegreeLE weight (MvPolynomial.X i : MvPolynomial σ F[X]) ℓ
      (ℓ * weight i) := by
  classical
  intro e he
  have : e = Finsupp.single i 1 := by
    by_contra hne
    exact he (by simp [MvPolynomial.coeff_X, Ne.symm hne])
  subst e
  simp [Finsupp.weight_single]

private theorem GradedCoeffDegreeLE.add {σ : Type*} {weight : σ → ℕ}
    {P Q : MvPolynomial σ F[X]} {ℓ B : ℕ}
    (hP : GradedCoeffDegreeLE weight P ℓ B)
    (hQ : GradedCoeffDegreeLE weight Q ℓ B) :
    GradedCoeffDegreeLE weight (P + Q) ℓ B := by
  intro e he
  rw [MvPolynomial.coeff_add] at he ⊢
  have hdeg : (MvPolynomial.coeff e P + MvPolynomial.coeff e Q).natDegree ≤
      B - ℓ * Finsupp.weight weight e := by
    apply (Polynomial.natDegree_add_le _ _).trans
    apply max_le
    · by_cases hz : MvPolynomial.coeff e P = 0
      · simp [hz]
      · exact Nat.le_sub_of_add_le (hP e hz)
    · by_cases hz : MvPolynomial.coeff e Q = 0
      · simp [hz]
      · exact Nat.le_sub_of_add_le (hQ e hz)
  have hweight : ℓ * Finsupp.weight weight e ≤ B := by
    by_cases hz : MvPolynomial.coeff e P = 0
    · have hQne : MvPolynomial.coeff e Q ≠ 0 := by simpa [hz] using he
      exact (Nat.le_add_left _ _).trans (hQ e hQne)
    · exact (Nat.le_add_left _ _).trans (hP e hz)
  exact Nat.add_le_of_le_sub hweight hdeg

private theorem GradedCoeffDegreeLE.mono {σ : Type*} {weight : σ → ℕ}
    {P : MvPolynomial σ F[X]} {ℓ A B : ℕ}
    (hP : GradedCoeffDegreeLE weight P ℓ A) (hAB : A ≤ B) :
    GradedCoeffDegreeLE weight P ℓ B :=
  fun e he ↦ (hP e he).trans hAB

private theorem GradedCoeffDegreeLE.mul {σ : Type*} {weight : σ → ℕ}
    {P Q : MvPolynomial σ F[X]} {ℓ A B : ℕ}
    (hP : GradedCoeffDegreeLE weight P ℓ A)
    (hQ : GradedCoeffDegreeLE weight Q ℓ B) :
    GradedCoeffDegreeLE weight (P * Q) ℓ (A + B) := by
  classical
  intro e he
  rw [MvPolynomial.coeff_mul] at he ⊢
  have hweight : ℓ * Finsupp.weight weight e ≤ A + B := by
    by_contra hnle
    have hallzero : ∀ pair ∈ Finset.antidiagonal e,
        MvPolynomial.coeff pair.1 P * MvPolynomial.coeff pair.2 Q = 0 := by
      intro pair hpair
      by_cases hp : MvPolynomial.coeff pair.1 P = 0
      · simp [hp]
      by_cases hq : MvPolynomial.coeff pair.2 Q = 0
      · simp [hq]
      have heq : pair.1 + pair.2 = e := by
        simpa [Multiset.mem_toFinset] using hpair
      have hw : Finsupp.weight weight e =
          Finsupp.weight weight pair.1 + Finsupp.weight weight pair.2 := by
        rw [← heq, map_add]
      have hpw : ℓ * Finsupp.weight weight pair.1 ≤ A :=
        (Nat.le_add_left _ _).trans (hP pair.1 hp)
      have hqw : ℓ * Finsupp.weight weight pair.2 ≤ B :=
        (Nat.le_add_left _ _).trans (hQ pair.2 hq)
      have := Nat.add_le_add hpw hqw
      rw [← Nat.mul_add, ← hw] at this
      omega
    exact he (Finset.sum_eq_zero hallzero)
  apply Nat.add_le_of_le_sub hweight
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro pair hpair
  by_cases hp : MvPolynomial.coeff pair.1 P = 0
  · simp [hp]
  by_cases hq : MvPolynomial.coeff pair.2 Q = 0
  · simp [hq]
  have heq : pair.1 + pair.2 = e := by
    simpa [Multiset.mem_toFinset] using hpair
  have hw : Finsupp.weight weight e =
      Finsupp.weight weight pair.1 + Finsupp.weight weight pair.2 := by
    rw [← heq, map_add]
  apply Nat.le_sub_of_add_le
  rw [hw, Nat.mul_add]
  calc
    (MvPolynomial.coeff pair.1 P * MvPolynomial.coeff pair.2 Q).natDegree +
          (ℓ * Finsupp.weight weight pair.1 + ℓ * Finsupp.weight weight pair.2) ≤
        ((MvPolynomial.coeff pair.1 P).natDegree +
          (MvPolynomial.coeff pair.2 Q).natDegree) +
          (ℓ * Finsupp.weight weight pair.1 + ℓ * Finsupp.weight weight pair.2) :=
      Nat.add_le_add_right Polynomial.natDegree_mul_le _
    _ = ((MvPolynomial.coeff pair.1 P).natDegree +
          ℓ * Finsupp.weight weight pair.1) +
        ((MvPolynomial.coeff pair.2 Q).natDegree +
          ℓ * Finsupp.weight weight pair.2) := by omega
    _ ≤ A + B := Nat.add_le_add (hP pair.1 hp) (hQ pair.2 hq)

private theorem GradedCoeffDegreeLE.pow {σ : Type*} {weight : σ → ℕ}
    {P : MvPolynomial σ F[X]} {ℓ B : ℕ}
    (hP : GradedCoeffDegreeLE weight P ℓ B) (n : ℕ) :
    GradedCoeffDegreeLE weight (P ^ n) ℓ (n * B) := by
  induction n with
  | zero =>
      simpa using gradedCoeffDegreeLE_C weight (p := (1 : F[X])) (ℓ := ℓ) (B := 0) (by simp)
  | succ n ih =>
      rw [pow_succ, Nat.succ_mul]
      exact ih.mul hP

private theorem GradedCoeffDegreeLE.sum {σ ι : Type*} {weight : σ → ℕ}
    (s : Finset ι) (P : ι → MvPolynomial σ F[X]) {ℓ B : ℕ}
    (hP : ∀ i ∈ s, GradedCoeffDegreeLE weight (P i) ℓ B) :
    GradedCoeffDegreeLE weight (∑ i ∈ s, P i) ℓ B := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro e he
      simp at he
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hP i (Finset.mem_insert_self i s)).add
        (ih fun j hj ↦ hP j (Finset.mem_insert_of_mem hj))

private theorem GradedCoeffDegreeLE.prod {σ ι : Type*} {weight : σ → ℕ}
    (s : Finset ι) (P : ι → MvPolynomial σ F[X]) (ℓ : ℕ) (B : ι → ℕ)
    (hP : ∀ i ∈ s, GradedCoeffDegreeLE weight (P i) ℓ (B i)) :
    GradedCoeffDegreeLE weight (∏ i ∈ s, P i) ℓ (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using gradedCoeffDegreeLE_C weight (p := (1 : F[X])) (ℓ := ℓ) (B := 0) (by simp)
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi, Finset.sum_insert hi]
      exact (hP i (Finset.mem_insert_self i s)).mul
        (ih fun j hj ↦ hP j (Finset.mem_insert_of_mem hj))

private theorem coeffDegreeLE_C {σ : Type*} {p : F[X]} {B : ℕ}
    (hp : p.natDegree ≤ B) : CoeffDegreeLE (MvPolynomial.C p : MvPolynomial σ F[X]) B := by
  classical
  intro e
  by_cases he : e = 0
  · subst e
    simpa using hp
  · simp [MvPolynomial.coeff_C, Ne.symm he]

private theorem coeffDegreeLE_X {σ : Type*} (i : σ) :
    CoeffDegreeLE (MvPolynomial.X i : MvPolynomial σ F[X]) 0 := by
  classical
  intro e
  by_cases he : e = Finsupp.single i 1
  · subst e
    simp
  · simp [MvPolynomial.coeff_X, Ne.symm he]

private theorem CoeffDegreeLE.add {σ : Type*} {P Q : MvPolynomial σ F[X]} {B : ℕ}
    (hP : CoeffDegreeLE P B) (hQ : CoeffDegreeLE Q B) : CoeffDegreeLE (P + Q) B := by
  intro e
  rw [MvPolynomial.coeff_add]
  exact (Polynomial.natDegree_add_le _ _).trans (max_le (hP e) (hQ e))

private theorem CoeffDegreeLE.mono {σ : Type*} {P : MvPolynomial σ F[X]} {A B : ℕ}
    (hP : CoeffDegreeLE P A) (hAB : A ≤ B) : CoeffDegreeLE P B :=
  fun e ↦ (hP e).trans hAB

private theorem CoeffDegreeLE.mul {σ : Type*} {P Q : MvPolynomial σ F[X]} {A B : ℕ}
    (hP : CoeffDegreeLE P A) (hQ : CoeffDegreeLE Q B) : CoeffDegreeLE (P * Q) (A + B) := by
  classical
  intro e
  rw [MvPolynomial.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro pair _
  exact Polynomial.natDegree_mul_le_of_le (hP pair.1) (hQ pair.2)

private theorem CoeffDegreeLE.pow {σ : Type*} {P : MvPolynomial σ F[X]} {B : ℕ}
    (hP : CoeffDegreeLE P B) (n : ℕ) : CoeffDegreeLE (P ^ n) (n * B) := by
  induction n with
  | zero =>
      simpa using coeffDegreeLE_C (σ := σ) (p := (1 : F[X])) (B := 0) (by simp)
  | succ n ih =>
      rw [pow_succ, Nat.succ_mul]
      exact ih.mul hP

private theorem CoeffDegreeLE.sum {σ ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial σ F[X]) {B : ℕ} (hP : ∀ i ∈ s, CoeffDegreeLE (P i) B) :
    CoeffDegreeLE (∑ i ∈ s, P i) B := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using coeffDegreeLE_C (σ := σ) (p := (0 : F[X])) (B := B) (by simp)
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hP i (Finset.mem_insert_self i s)).add
        (ih fun j hj ↦ hP j (Finset.mem_insert_of_mem hj))

private theorem CoeffDegreeLE.prod_zero {σ ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial σ F[X]) (hP : ∀ i ∈ s, CoeffDegreeLE (P i) 0) :
    CoeffDegreeLE (∏ i ∈ s, P i) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simpa using coeffDegreeLE_C (σ := σ) (p := (1 : F[X])) (B := 0) (by simp)
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      simpa using (hP i (Finset.mem_insert_self i s)).mul
        (ih fun j hj ↦ hP j (Finset.mem_insert_of_mem hj))

private theorem localCorrection_coeffDegreeLE_zero (d : ℕ) :
    CoeffDegreeLE (localCorrection (R := F[X]) d) 0 := by
  rw [localCorrection]
  apply CoeffDegreeLE.sum
  intro j _
  have hC : CoeffDegreeLE
      (MvPolynomial.C ((-1 : F[X]) ^ j.val) : LocalPolynomial F[X] d) 0 :=
    coeffDegreeLE_C (by simp)
  have hT : CoeffDegreeLE (MvPolynomial.X (localT d) : LocalPolynomial F[X] d) 0 :=
    coeffDegreeLE_X _
  have hY : CoeffDegreeLE (MvPolynomial.X (localY j) : LocalPolynomial F[X] d) 0 :=
    coeffDegreeLE_X _
  simpa using (hC.mul (hT.pow (j.val + 1))).mul hY

private theorem localCorrection_gradedCoeffDegreeLE
    (weight : LocalVariable d → ℕ)
    (hT : weight (localT d) = 0) (hY : ∀ j, weight (localY j) = 1)
    (ℓ : ℕ) :
    GradedCoeffDegreeLE weight (localCorrection (R := F[X]) d) ℓ ℓ := by
  rw [localCorrection]
  apply GradedCoeffDegreeLE.sum
  intro j _
  have hC : GradedCoeffDegreeLE weight
      (MvPolynomial.C ((-1 : F[X]) ^ j.val) : LocalPolynomial F[X] d) ℓ 0 :=
    gradedCoeffDegreeLE_C weight (by simp)
  have hT' := gradedCoeffDegreeLE_X (F := F) weight ℓ (localT d)
  have hY' := gradedCoeffDegreeLE_X (F := F) weight ℓ (localY j)
  simpa [hT, hY] using (hC.mul (hT'.pow (j.val + 1))).mul hY'

/-- Substitution by a received curve obeys the joint challenge-degree/local-grade budget.
Every source jet contributes budget `ℓ`; a term of local grade `u` therefore leaves at most
`ℓ (t-u)` challenge degree from a source monomial of total jet degree `t`. -/
theorem sourceMonomial_curve_unscaled_gradedCoeffDegreeLE
    (weight : LocalVariable d → ℕ)
    (hT : weight (localT d) = 0) (hE : weight (localE d) = 1)
    (hY : ∀ j, weight (localY j) = 1)
    (a : F) (w : F[X]) (ℓ : ℕ) (hw : w.natDegree ≤ ℓ)
    (x b : ℕ) (higher : Fin d → ℕ) :
    GradedCoeffDegreeLE weight
      (unscaledLocalSubstitution d (Polynomial.C a) w
        (sourceMonomial x b higher)) ℓ (ℓ * (b + ∑ j, higher j)) := by
  have hcenter : (Polynomial.C a).natDegree ≤ 0 := by rw [Polynomial.natDegree_C]
  have hcenterC : GradedCoeffDegreeLE weight
      (MvPolynomial.C (Polynomial.C a) : LocalPolynomial F[X] d) ℓ 0 :=
    gradedCoeffDegreeLE_C weight hcenter
  have hT' := gradedCoeffDegreeLE_X (F := F) weight ℓ (localT d)
  have hE' := gradedCoeffDegreeLE_X (F := F) weight ℓ (localE d)
  have hTzero : GradedCoeffDegreeLE weight
      (MvPolynomial.X (localT d) : LocalPolynomial F[X] d) ℓ 0 := by
    simpa [hT] using hT'
  have hXimage : GradedCoeffDegreeLE weight
      (MvPolynomial.C (Polynomial.C a) + MvPolynomial.X (localT d) :
        LocalPolynomial F[X] d) ℓ 0 := by
    exact hcenterC.add hTzero
  have hreceivedC : GradedCoeffDegreeLE weight
      (MvPolynomial.C w : LocalPolynomial F[X] d) ℓ ℓ :=
    gradedCoeffDegreeLE_C weight hw
  have hcorrection := localCorrection_gradedCoeffDegreeLE
    (F := F) weight hT hY ℓ
  have hTE : GradedCoeffDegreeLE weight
      (MvPolynomial.X (localT d) * MvPolynomial.X (localE d) :
        LocalPolynomial F[X] d) ℓ ℓ := by
    simpa [hE] using hTzero.mul hE'
  have hYimage : GradedCoeffDegreeLE weight
      (MvPolynomial.C w + localCorrection d +
        MvPolynomial.X (localT d) * MvPolynomial.X (localE d) :
          LocalPolynomial F[X] d) ℓ ℓ :=
    hreceivedC.add hcorrection |>.add hTE
  have hhigher : GradedCoeffDegreeLE weight
      (∏ j, MvPolynomial.X (localY j) ^ higher j : LocalPolynomial F[X] d) ℓ
        (∑ j, ℓ * higher j) := by
    apply GradedCoeffDegreeLE.prod
    intro j _
    simpa [hY, Nat.mul_comm] using
      (gradedCoeffDegreeLE_X (F := F) weight ℓ (localY j)).pow (higher j)
  simp only [sourceMonomial, map_mul, map_pow, map_prod,
    unscaledLocalSubstitution_X, unscaledLocalSubstitution_Y_zero,
    unscaledLocalSubstitution_Y_succ]
  have h := ((hXimage.pow x).mul (hYimage.pow b)).mul hhigher
  simpa [Finset.mul_sum, Nat.mul_add, Nat.mul_comm, Nat.mul_left_comm,
    Nat.mul_assoc] using h

/-- A translated source monomial cannot acquire local weight above its source jet degree.
This remains valid for constant received curves (`ℓ = 0`). -/
theorem sourceMonomial_curve_unscaled_coeff_eq_zero_of_weight_gt
    (weight : LocalVariable d → ℕ)
    (hT : weight (localT d) = 0) (hE : weight (localE d) = 1)
    (hY : ∀ j, weight (localY j) = 1)
    (a : F) (w : F[X]) (ℓ : ℕ) (hw : w.natDegree ≤ ℓ)
    (x b : ℕ) (higher : Fin d → ℕ) (e : LocalVariable d →₀ ℕ)
    (hweight : b + ∑ j, higher j < Finsupp.weight weight e) :
    MvPolynomial.coeff e
      (unscaledLocalSubstitution d (Polynomial.C a) w
        (sourceMonomial x b higher)) = 0 := by
  by_contra hne
  let L := max ℓ 1
  have hwL : w.natDegree ≤ L := hw.trans (le_max_left _ _)
  have hjoint := sourceMonomial_curve_unscaled_gradedCoeffDegreeLE
    (F := F) weight hT hE hY a w L hwL x b higher e hne
  have hmul : L * Finsupp.weight weight e ≤ L * (b + ∑ j, higher j) :=
    (Nat.le_add_left _ _).trans hjoint
  have hL : 0 < L := lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  exact (Nat.not_le_of_lt hweight) (Nat.le_of_mul_le_mul_left hmul hL)

/-- After projecting to a local monomial of weight `u`, a source monomial of jet degree `t`
has challenge degree at most `ℓ (t-u)`. -/
theorem sourceMonomial_curve_unscaled_coeff_natDegree_le_shift
    (weight : LocalVariable d → ℕ)
    (hT : weight (localT d) = 0) (hE : weight (localE d) = 1)
    (hY : ∀ j, weight (localY j) = 1)
    (a : F) (w : F[X]) (ℓ : ℕ) (hw : w.natDegree ≤ ℓ)
    (x b : ℕ) (higher : Fin d → ℕ) (e : LocalVariable d →₀ ℕ) :
    (MvPolynomial.coeff e
      (unscaledLocalSubstitution d (Polynomial.C a) w
        (sourceMonomial x b higher))).natDegree ≤
      ℓ * ((b + ∑ j, higher j) - Finsupp.weight weight e) := by
  by_cases hzero : MvPolynomial.coeff e
      (unscaledLocalSubstitution d (Polynomial.C a) w
        (sourceMonomial x b higher)) = 0
  · simp [hzero]
  have hle : Finsupp.weight weight e ≤ b + ∑ j, higher j := by
    by_contra hnot
    exact hzero (sourceMonomial_curve_unscaled_coeff_eq_zero_of_weight_gt
      weight hT hE hY a w ℓ hw x b higher e (by omega))
  have hjoint := sourceMonomial_curve_unscaled_gradedCoeffDegreeLE
    (F := F) weight hT hE hY a w ℓ hw x b higher e hzero
  rw [Nat.mul_sub_left_distrib]
  apply Nat.le_sub_of_add_le
  exact hjoint

/-- The low-contact projection preserves the translated grade-shift degree bound. -/
theorem sourceMonomial_curve_localConstraint_coeff_natDegree_le_shift
    (weight : LocalVariable d → ℕ)
    (hT : weight (localT d) = 0) (hE : weight (localE d) = 1)
    (hY : ∀ j, weight (localY j) = 1)
    (a : F) (w : F[X]) (ℓ : ℕ) (hw : w.natDegree ≤ ℓ)
    (x b m : ℕ) (higher : Fin d → ℕ) (e : LocalVariable d →₀ ℕ) :
    (MvPolynomial.coeff e
      (localConstraintAt m (Polynomial.C a) w
        (sourceMonomial x b higher))).natDegree ≤
      ℓ * ((b + ∑ j, higher j) - Finsupp.weight weight e) := by
  rw [localConstraintAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    projectLowContact, coeff_filterLocalMonomials]
  split
  · exact sourceMonomial_curve_unscaled_coeff_natDegree_le_shift
      weight hT hE hY a w ℓ hw x b higher e
  · simp

/-- A projected translated source monomial has no row above its source jet grade. -/
theorem sourceMonomial_curve_localConstraint_coeff_eq_zero_of_weight_gt
    (weight : LocalVariable d → ℕ)
    (hT : weight (localT d) = 0) (hE : weight (localE d) = 1)
    (hY : ∀ j, weight (localY j) = 1)
    (a : F) (w : F[X]) (ℓ : ℕ) (hw : w.natDegree ≤ ℓ)
    (x b m : ℕ) (higher : Fin d → ℕ) (e : LocalVariable d →₀ ℕ)
    (hweight : b + ∑ j, higher j < Finsupp.weight weight e) :
    MvPolynomial.coeff e
      (localConstraintAt m (Polynomial.C a) w
        (sourceMonomial x b higher)) = 0 := by
  rw [localConstraintAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    projectLowContact, coeff_filterLocalMonomials]
  split
  · exact sourceMonomial_curve_unscaled_coeff_eq_zero_of_weight_gt
      weight hT hE hY a w ℓ hw x b higher e hweight
  · rfl

/-- Substitution of a received polynomial of degree at most `ℓ` gives column degree at most
`ℓ * b`, where `b` is the source `Y₀` exponent. No positivity assumption on `ℓ` is needed. -/
theorem sourceMonomial_curve_unscaled_coeffDegreeLE (a : F) (w : F[X])
    (ℓ : ℕ) (hw : w.natDegree ≤ ℓ) (x b : ℕ)
    (higher : Fin d → ℕ) :
    CoeffDegreeLE
      (unscaledLocalSubstitution d (Polynomial.C a) w
        (sourceMonomial x b higher)) (ℓ * b) := by
  have hcenter : (Polynomial.C a).natDegree ≤ 0 := by rw [Polynomial.natDegree_C]
  have hcenterC : CoeffDegreeLE
      (MvPolynomial.C (Polynomial.C a) : LocalPolynomial F[X] d) 0 :=
    coeffDegreeLE_C hcenter
  have hT : CoeffDegreeLE
      (MvPolynomial.X (localT d) : LocalPolynomial F[X] d) 0 := coeffDegreeLE_X _
  have hE : CoeffDegreeLE
      (MvPolynomial.X (localE d) : LocalPolynomial F[X] d) 0 := coeffDegreeLE_X _
  have hXimage : CoeffDegreeLE
      (MvPolynomial.C (Polynomial.C a) + MvPolynomial.X (localT d) :
        LocalPolynomial F[X] d) 0 := hcenterC.add hT
  have hreceivedC : CoeffDegreeLE
      (MvPolynomial.C w : LocalPolynomial F[X] d) ℓ :=
    coeffDegreeLE_C hw
  have hcorrection : CoeffDegreeLE (localCorrection (R := F[X]) d) ℓ :=
    (localCorrection_coeffDegreeLE_zero d).mono (by omega)
  have hTE : CoeffDegreeLE
      (MvPolynomial.X (localT d) * MvPolynomial.X (localE d) :
        LocalPolynomial F[X] d) ℓ :=
    (hT.mul hE).mono (by omega)
  have hYimage : CoeffDegreeLE
      (MvPolynomial.C w + localCorrection d +
        MvPolynomial.X (localT d) * MvPolynomial.X (localE d) :
          LocalPolynomial F[X] d) ℓ :=
    hreceivedC.add hcorrection |>.add hTE
  have hhigher : CoeffDegreeLE
      (∏ j, MvPolynomial.X (localY j) ^ higher j : LocalPolynomial F[X] d) 0 := by
    apply CoeffDegreeLE.prod_zero
    intro j _
    simpa using (coeffDegreeLE_X (F := F) (localY j)).pow (higher j)
  simp only [sourceMonomial, map_mul, map_pow, map_prod,
    unscaledLocalSubstitution_X, unscaledLocalSubstitution_Y_zero,
    unscaledLocalSubstitution_Y_succ]
  simpa [Nat.mul_comm] using ((hXimage.pow x).mul (hYimage.pow b)).mul hhigher

/-- For one source monomial, every unscaled received-line coefficient has challenge degree at
most its source `Y₀` exponent. -/
theorem sourceMonomial_unscaled_coeffDegreeLE (a f g : F) (x b : ℕ)
    (higher : Fin d → ℕ) :
    CoeffDegreeLE
      (unscaledLocalSubstitution d (Polynomial.C a) (receivedLine f g)
        (sourceMonomial x b higher)) b := by
  simpa using sourceMonomial_curve_unscaled_coeffDegreeLE a (receivedLine f g) 1
    (receivedLine_natDegree_le f g) x b higher

/-- The local contact projection preserves the challenge-degree bound for polynomial curves. -/
theorem sourceMonomial_curve_localConstraint_coeffDegreeLE (a : F) (w : F[X])
    (ℓ : ℕ) (hw : w.natDegree ≤ ℓ) (x b m : ℕ) (higher : Fin d → ℕ) :
    CoeffDegreeLE
      (localConstraintAt m (Polynomial.C a) w (sourceMonomial x b higher)) (ℓ * b) := by
  have hunscaled := sourceMonomial_curve_unscaled_coeffDegreeLE
    (d := d) a w ℓ hw x b higher
  intro e
  rw [localConstraintAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    projectLowContact, coeff_filterLocalMonomials]
  split
  · exact hunscaled e
  · simp

/-- For one source monomial, every projected local-constraint coefficient has challenge degree at
most its source `Y₀` exponent. -/
theorem sourceMonomial_localConstraint_coeffDegreeLE (a f g : F) (x b m : ℕ)
    (higher : Fin d → ℕ) :
    CoeffDegreeLE
      (localConstraintAt m (Polynomial.C a) (receivedLine f g)
        (sourceMonomial x b higher)) b := by
  have hunscaled := sourceMonomial_unscaled_coeffDegreeLE
    (d := d) a f g x b higher
  intro e
  rw [localConstraintAt, LinearMap.comp_apply, AlgHom.toLinearMap_apply,
    projectLowContact, coeff_filterLocalMonomials]
  split
  · exact hunscaled e
  · simp

/-- Exponent data for one monomial in the symbolic interpolation space. -/
structure SourceColumn (d : ℕ) where
  x : ℕ
  y₀ : ℕ
  higher : Fin d → ℕ

/-- The full source exponent represented by a `SourceColumn`. -/
def SourceColumn.exponent (c : SourceColumn d) : JetVariable d →₀ ℕ :=
  Finsupp.single none c.x + Finsupp.single (some 0) c.y₀ +
    ∑ j, Finsupp.single (some j.succ) (c.higher j)

@[simp] theorem SourceColumn.exponent_none (c : SourceColumn d) : c.exponent none = c.x := by
  simp [SourceColumn.exponent]

@[simp] theorem SourceColumn.exponent_zero (c : SourceColumn d) : c.exponent (some 0) = c.y₀ := by
  simp [SourceColumn.exponent]

@[simp] theorem SourceColumn.exponent_succ (c : SourceColumn d) (j : Fin d) :
    c.exponent (some j.succ) = c.higher j := by
  simp only [SourceColumn.exponent, Finsupp.add_apply, Finsupp.single_apply]
  simp only [Option.some.injEq, reduceCtorEq, if_false,
    show (0 : Fin (d + 1)) ≠ j.succ from Ne.symm (Fin.succ_ne_zero j)]
  simp only [zero_add]
  classical
  change Finsupp.applyAddHom (some j.succ)
      (∑ k, Finsupp.single (some k.succ) (c.higher k)) = c.higher j
  rw [map_sum]
  calc
    ∑ k, Finsupp.applyAddHom (some j.succ)
        (Finsupp.single (some k.succ) (c.higher k)) =
        Finsupp.applyAddHom (some j.succ)
          (Finsupp.single (some j.succ) (c.higher j)) := by
      apply Fintype.sum_eq_single j
      · intro k hkj
        simp [hkj]
    _ = c.higher j := by simp

/-- The source grade of a symbolic column is its `Y₀` exponent plus all higher-jet
exponents. -/
@[simp] theorem SourceColumn.totalJetDegree_exponent (c : SourceColumn d) :
    totalJetDegree c.exponent = c.y₀ + ∑ j, c.higher j := by
  rw [totalJetDegree, Finsupp.degree_eq_sum]
  have h := Fin.sum_univ_succ (fun j : Fin (d + 1) ↦ c.exponent (some j))
  simpa only [Finsupp.some_apply, SourceColumn.exponent_zero,
    SourceColumn.exponent_succ] using h

/-- The actual source monomial represented by a `SourceColumn`. -/
def SourceColumn.polynomial {R : Type*} [CommSemiring R] (c : SourceColumn d) :
    DifferentialPolynomial R d := MvPolynomial.monomial c.exponent 1

theorem SourceColumn.polynomial_eq_sourceMonomial {R : Type*} [CommRing R]
    (c : SourceColumn d) :
    (c.polynomial : DifferentialPolynomial R d) =
      sourceMonomial (F := R) c.x c.y₀ c.higher := by
  classical
  rw [sourceMonomial, SourceColumn.polynomial]
  simp only [MvPolynomial.X_pow_eq_monomial, MvPolynomial.monomial_mul, mul_one]
  have hhigher :
      (∏ j, MvPolynomial.monomial (Finsupp.single (some j.succ) (c.higher j)) (1 : R)) =
        MvPolynomial.monomial
          (∑ j, Finsupp.single (some j.succ) (c.higher j)) 1 := by
    induction (Finset.univ : Finset (Fin d)) using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
        rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, MvPolynomial.monomial_mul]
        simp
  rw [hhigher]
  simp [SourceColumn.exponent, add_assoc]

theorem SourceColumn.exponent_injective :
    Function.Injective (SourceColumn.exponent : SourceColumn d → JetVariable d →₀ ℕ) := by
  intro c c' h
  have hx := congrArg (fun e ↦ e none) h
  have hy₀ := congrArg (fun e ↦ e (some 0)) h
  cases c with
  | mk x y₀ higher =>
      cases c' with
      | mk x' y₀' higher' =>
          simp only [SourceColumn.mk.injEq]
          have hx' : x = x' := by simpa [SourceColumn.exponent] using hx
          have hy₀' : y₀ = y₀' := by simpa [SourceColumn.exponent] using hy₀
          refine ⟨hx', hy₀', ?_⟩
          funext j
          have eval_higher (a : Fin d → ℕ) :
              (∑ k, Finsupp.single (some k.succ) (a k)) (some j.succ) = a j := by
            change Finsupp.applyAddHom (some j.succ)
              (∑ k, Finsupp.single (some k.succ) (a k)) = a j
            rw [map_sum]
            calc
              ∑ k, Finsupp.applyAddHom (some j.succ)
                  (Finsupp.single (some k.succ) (a k)) =
                  Finsupp.applyAddHom (some j.succ)
                    (Finsupp.single (some j.succ) (a j)) := by
                apply Fintype.sum_eq_single j
                intro k hkj
                simp [hkj]
              _ = a j := by simp
          have hj := congrArg (fun e ↦ e (some j.succ)) h
          simp only [SourceColumn.exponent, Finsupp.add_apply] at hj
          rw [eval_higher higher, eval_higher higher'] at hj
          simpa [Finsupp.single_apply] using hj

/-- The symbolic received-line constraint matrix over `F[Z]`. -/
def matrix {n N : ℕ} (m : ℕ) (centers f g : Fin n → F)
    (columns : Fin N → SourceColumn d) :
    Matrix (Fin n × LowContactIndex d m) (Fin N) F[X] := fun row j ↦
  localConstraintCoordinatesAt m (Polynomial.C (centers row.1))
    (receivedLine (f row.1) (g row.1)) (columns j).polynomial row.2

theorem matrix_entry_eq_coeff_localConstraintAt {n N : ℕ} (m : ℕ)
    (centers f g : Fin n → F) (columns : Fin N → SourceColumn d)
    (row : Fin n × LowContactIndex d m) (j : Fin N) :
    matrix m centers f g columns row j =
      MvPolynomial.coeff row.2.1
        (localConstraintAt m (Polynomial.C (centers row.1))
          (receivedLine (f row.1) (g row.1)) (columns j).polynomial) := by
  simp [matrix, localConstraintCoordinatesAt, lowContactCoefficients, localConstraintAt,
    projectLowContact, coeff_filterLocalMonomials, row.2.2]

/-- Low-contact exponents occurring in a concrete projected local polynomial. -/
def lowContactSupport (m : ℕ) (P : LocalPolynomial F[X] d) :
    Finset (LowContactIndex d m) :=
  P.support.preimage Subtype.val (fun _ _ _ _ h ↦ Subtype.ext h)

/-- The finite set of rows on which at least one symbolic matrix column is supported. -/
def activeRows {n N : ℕ} (m : ℕ) (centers f g : Fin n → F)
    (columns : Fin N → SourceColumn d) : Finset (Fin n × LowContactIndex d m) := by
  classical
  exact Finset.univ.biUnion fun i ↦
    Finset.univ.biUnion fun j ↦
      (lowContactSupport m
        (localConstraintAt m (Polynomial.C (centers i)) (receivedLine (f i) (g i))
          (columns j).polynomial)).image (Prod.mk i)

theorem mem_activeRows_of_matrix_entry_ne_zero {n N : ℕ} (m : ℕ)
    (centers f g : Fin n → F) (columns : Fin N → SourceColumn d)
    (row : Fin n × LowContactIndex d m) (j : Fin N)
    (h : matrix m centers f g columns row j ≠ 0) :
    row ∈ activeRows m centers f g columns := by
  classical
  simp only [activeRows, Finset.mem_biUnion]
  refine ⟨row.1, Finset.mem_univ _, ?_⟩
  refine ⟨j, Finset.mem_univ _, ?_⟩
  rw [Finset.mem_image]
  refine ⟨row.2, ?_, rfl⟩
  have hsupp : row.2.1 ∈
      (localConstraintAt m (Polynomial.C (centers row.1))
        (receivedLine (f row.1) (g row.1)) (columns j).polynomial).support := by
    rw [MvPolynomial.mem_support_iff, ← matrix_entry_eq_coeff_localConstraintAt]
    exact h
  simpa [lowContactSupport] using hsupp

/-- The finite matrix obtained by retaining exactly the active rows. -/
def activeMatrix {n N : ℕ} (m : ℕ) (centers f g : Fin n → F)
    (columns : Fin N → SourceColumn d) :
    Matrix {row // row ∈ activeRows m centers f g columns} (Fin N) F[X] :=
  (matrix m centers f g columns).submatrix Subtype.val (Equiv.refl _)

/-- The active-row matrix reindexed by a `Fin`, as required by polynomial kernel height. -/
def finMatrix {n N : ℕ} (m : ℕ) (centers f g : Fin n → F)
    (columns : Fin N → SourceColumn d) :
    Matrix (Fin (Fintype.card {row // row ∈ activeRows m centers f g columns}))
      (Fin N) F[X] :=
  (activeMatrix m centers f g columns).submatrix
    (Fintype.equivFin {row // row ∈ activeRows m centers f g columns}).symm (Equiv.refl _)

private theorem rank_submatrix_rows_le {K ρ ρ' κ : Type*} [Field K] [Fintype κ]
    (A : Matrix ρ κ K) (r : ρ' → ρ) :
    (A.submatrix r (Equiv.refl κ)).rank ≤ A.rank := by
  rw [Matrix.rank, Matrix.rank, Matrix.mulVecLin_submatrix, LinearMap.range_comp,
    LinearMap.range_comp,
    show LinearMap.funLeft K K (Equiv.refl κ).symm =
      LinearEquiv.funCongrLeft K K (Equiv.refl κ).symm from rfl,
    LinearEquiv.range, Submodule.map_top]
  exact Submodule.finrank_map_le _ _

theorem finMatrix_rank_le_matrix_rank {n N : ℕ} (m : ℕ) (centers f g : Fin n → F)
    (columns : Fin N → SourceColumn d) :
    ((finMatrix m centers f g columns).map (algebraMap F[X] (RatFunc F))).rank ≤
      ((matrix m centers f g columns).map (algebraMap F[X] (RatFunc F))).rank := by
  calc
    _ = ((activeMatrix m centers f g columns).map
        (algebraMap F[X] (RatFunc F))).rank := by
      change
        ((((activeMatrix m centers f g columns).map
          (algebraMap F[X] (RatFunc F))).submatrix
            (Fintype.equivFin {row // row ∈ activeRows m centers f g columns}).symm
              (Equiv.refl _))).rank = _
      exact Matrix.rank_submatrix _ _ _
    _ ≤ _ := by
      let A := (matrix m centers f g columns).map (algebraMap F[X] (RatFunc F))
      change (A.submatrix Subtype.val (Equiv.refl _)).rank ≤ A.rank
      exact rank_submatrix_rows_le A Subtype.val

theorem activeMatrix_mulVec_eq_zero_iff {n N : ℕ} (m : ℕ) (centers f g : Fin n → F)
    (columns : Fin N → SourceColumn d) (v : Fin N → F[X]) :
    Matrix.mulVec (activeMatrix m centers f g columns) v = 0 ↔
      Matrix.mulVec (matrix m centers f g columns) v = 0 := by
  constructor
  · intro h
    funext row
    by_cases hrow : row ∈ activeRows m centers f g columns
    · have := congrFun h ⟨row, hrow⟩
      simpa [activeMatrix, Matrix.mulVec, dotProduct] using this
    · rw [Matrix.mulVec, dotProduct]
      apply Finset.sum_eq_zero
      intro j _
      have hentry : matrix m centers f g columns row j = 0 := by
        by_contra hne
        exact hrow (mem_activeRows_of_matrix_entry_ne_zero m centers f g columns row j hne)
      simp [hentry]
  · intro h
    funext row
    have := congrFun h row.1
    simpa [activeMatrix, Matrix.mulVec, dotProduct] using this

theorem finMatrix_mulVec_eq_zero_iff {n N : ℕ} (m : ℕ) (centers f g : Fin n → F)
    (columns : Fin N → SourceColumn d) (v : Fin N → F[X]) :
    Matrix.mulVec (finMatrix m centers f g columns) v = 0 ↔
      Matrix.mulVec (matrix m centers f g columns) v = 0 := by
  rw [finMatrix, Matrix.submatrix_mulVec_equiv]
  constructor
  · intro h
    apply (activeMatrix_mulVec_eq_zero_iff m centers f g columns v).mp
    funext row
    have hrow := congrFun h
      ((Fintype.equivFin {row // row ∈ activeRows m centers f g columns}) row)
    simpa using hrow
  · intro h
    have hactive := (activeMatrix_mulVec_eq_zero_iff m centers f g columns v).mpr h
    funext k
    have hk := congrFun hactive
      ((Fintype.equivFin {row // row ∈ activeRows m centers f g columns}).symm k)
    simpa using hk

/-- Every symbolic matrix entry has challenge degree at most its column's source `Y₀` exponent. -/
theorem matrix_entry_natDegree_le_y₀ {n N : ℕ} (m : ℕ) (centers f g : Fin n → F)
    (columns : Fin N → SourceColumn d) (row : Fin n × LowContactIndex d m) (j : Fin N) :
    (matrix m centers f g columns row j).natDegree ≤ (columns j).y₀ := by
  have h := sourceMonomial_unscaled_coeffDegreeLE
    (d := d) (centers row.1) (f row.1) (g row.1)
      (columns j).x (columns j).y₀ (columns j).higher
  rw [show matrix m centers f g columns row j = MvPolynomial.coeff row.2.1
    (unscaledLocalSubstitution d (Polynomial.C (centers row.1))
      (receivedLine (f row.1) (g row.1)) (columns j).polynomial) by
        simp [matrix, localConstraintCoordinatesAt, lowContactCoefficients]]
  rw [SourceColumn.polynomial_eq_sourceMonomial]
  exact h row.2.1

theorem finMatrix_entry_natDegree_le_y₀ {n N : ℕ} (m : ℕ) (centers f g : Fin n → F)
    (columns : Fin N → SourceColumn d)
    (row : Fin (Fintype.card {r // r ∈ activeRows m centers f g columns})) (j : Fin N) :
    (finMatrix m centers f g columns row j).natDegree ≤ (columns j).y₀ := by
  simpa [finMatrix, activeMatrix] using
    matrix_entry_natDegree_le_y₀ m centers f g columns
      ((Fintype.equivFin {r // r ∈ activeRows m centers f g columns}).symm row).1 j

/-- Linear combination of the concrete source monomials with polynomial challenge coefficients. -/
def interpolant {N : ℕ} (columns : Fin N → SourceColumn d) (v : Fin N → F[X]) :
    DifferentialPolynomial F[X] d :=
  ∑ j, MvPolynomial.monomial (columns j).exponent (v j)

theorem coeff_interpolant {N : ℕ} (columns : Fin N → SourceColumn d)
    (hcolumns : Function.Injective columns) (v : Fin N → F[X]) (j : Fin N) :
    MvPolynomial.coeff (columns j).exponent (interpolant columns v) = v j := by
  classical
  rw [interpolant, MvPolynomial.coeff_sum]
  calc
    ∑ k, MvPolynomial.coeff (columns j).exponent
        (MvPolynomial.monomial (columns k).exponent (v k)) =
        MvPolynomial.coeff (columns j).exponent
          (MvPolynomial.monomial (columns j).exponent (v j)) := by
      apply Finset.sum_eq_single j
      · intro k _ hkj
        rw [MvPolynomial.coeff_monomial]
        simp only [ite_eq_right_iff]
        intro hexp
        exact (hkj (hcolumns (SourceColumn.exponent_injective hexp))).elim
      · simp
    _ = v j := by simp

/-- Matrix multiplication is the coordinate vector of the local constraints on the assembled
interpolant. -/
theorem matrix_mulVec_apply {n N : ℕ} (m : ℕ) (centers f g : Fin n → F)
    (columns : Fin N → SourceColumn d) (v : Fin N → F[X])
    (row : Fin n × LowContactIndex d m) :
    Matrix.mulVec (matrix m centers f g columns) v row =
      localConstraintCoordinatesAt m (Polynomial.C (centers row.1))
        (receivedLine (f row.1) (g row.1)) (interpolant columns v) row.2 := by
  classical
  rw [interpolant, Matrix.mulVec, dotProduct, map_sum]
  simp only [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  change
    localConstraintCoordinatesAt m (Polynomial.C (centers row.1))
        (receivedLine (f row.1) (g row.1)) (columns j).polynomial row.2 * v j =
      localConstraintCoordinatesAt m (Polynomial.C (centers row.1))
        (receivedLine (f row.1) (g row.1))
          (MvPolynomial.monomial (columns j).exponent (v j)) row.2
  rw [show MvPolynomial.monomial (columns j).exponent (v j) =
      v j • (columns j).polynomial by
        rw [SourceColumn.polynomial, MvPolynomial.smul_monomial]
        simp, LinearMap.map_smul]
  simp [mul_comm]

/-- A coefficient vector is in the symbolic matrix kernel exactly when its concrete interpolant
satisfies every received-line local constraint. -/
theorem matrix_mulVec_eq_zero_iff {n N : ℕ} (m : ℕ) (centers f g : Fin n → F)
    (columns : Fin N → SourceColumn d) (v : Fin N → F[X]) :
    Matrix.mulVec (matrix m centers f g columns) v = 0 ↔
      ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i))
        (receivedLine (f i) (g i)) (interpolant columns v) := by
  constructor
  · intro h i
    rw [satisfiesLocalConstraints_iff_coordinates_eq_zero]
    funext e
    rw [← matrix_mulVec_apply m centers f g columns v (i, e), congrFun h (i, e)]
    rfl
  · intro h
    funext row
    rw [matrix_mulVec_apply]
    have hi := (satisfiesLocalConstraints_iff_coordinates_eq_zero
      m (Polynomial.C (centers row.1)) (receivedLine (f row.1) (g row.1))
        (interpolant columns v)).mp (h row.1)
    exact congrFun hi row.2

/-- If the coefficient vector does not vanish simultaneously after a scalar extension and
challenge specialization, then neither does the assembled interpolant. -/
theorem map_interpolant_ne_zero {N : ℕ} (columns : Fin N → SourceColumn d)
    (hcolumns : Function.Injective columns) (v : Fin N → F[X])
    {E : Type*} [Field E] (ι : F →+* E) (z : E)
    (hv : (fun j ↦ (v j).eval₂ ι z) ≠ 0) :
    MvPolynomial.map (Polynomial.eval₂RingHom ι z) (interpolant columns v) ≠ 0 := by
  intro hzero
  apply hv
  funext j
  have hj := congrArg (MvPolynomial.coeff (columns j).exponent) hzero
  rw [MvPolynomial.coeff_map, coeff_interpolant columns hcolumns v j,
    MvPolynomial.coeff_zero] at hj
  exact hj

/-- Symbolic received-line interpolation from a rational-function rank bound. The returned
polynomial is the actual linear combination of the supplied source monomials. Its local
constraints vanish identically as polynomials in the challenge, and it remains nonzero after
every field extension and every specialization of that challenge. -/
theorem exists_symbolic_received_line_interpolant_of_rank_le {n N : ℕ}
    (m ν r₀ : ℕ) (centers f g : Fin n → F) (columns : Fin N → SourceColumn d)
    (hcolumns : Function.Injective columns) (hy₀ : ∀ j, (columns j).y₀ ≤ ν)
    (hrank : ((matrix m centers f g columns).map
      (algebraMap F[X] (RatFunc F))).rank ≤ n * r₀)
    (hN : n * r₀ < N) :
    ∃ v : Fin N → F[X],
      v ≠ 0 ∧
        Matrix.mulVec (matrix m centers f g columns) v = 0 ∧
          (∀ j, (v j).natDegree ≤ n * r₀ * ν / (N - n * r₀)) ∧
            Ideal.span (Set.range v) = ⊤ ∧
              (∀ {E : Type*} [Field E] (ι : F →+* E) (z : E),
                MvPolynomial.map (Polynomial.eval₂RingHom ι z)
                  (interpolant columns v) ≠ 0) ∧
                ∀ i, SatisfiesLocalConstraints m (Polynomial.C (centers i))
                  (receivedLine (f i) (g i)) (interpolant columns v) := by
  let M := finMatrix m centers f g columns
  let s := (M.map (algebraMap F[X] (RatFunc F))).rank
  have hs_le : s ≤ n * r₀ := by
    exact (finMatrix_rank_le_matrix_rank m centers f g columns).trans hrank
  have hsN : s < N := hs_le.trans_lt hN
  have hdeg : ∀ i j, (M i j).natDegree ≤ ν := by
    intro i j
    exact (finMatrix_entry_natDegree_le_y₀ m centers f g columns i j).trans (hy₀ j)
  obtain ⟨v, hv, hMv, hvdeg, hprimitive, hnozero⟩ :=
    Matrix.exists_primitive_ne_zero_mulVec_eq_zero_natDegree_le_of_rank_eq
      M hdeg (show (M.map (algebraMap F[X] (RatFunc F))).rank = s from rfl) hsN
  have hdegree (j : Fin N) : (v j).natDegree ≤ n * r₀ * ν / (N - n * r₀) := by
    refine (hvdeg j).trans (Nat.div_le_div (Nat.mul_le_mul_right ν hs_le) ?_ ?_)
    · exact Nat.sub_le_sub_left hs_le N
    · exact Nat.sub_ne_zero_of_lt hN
  have hkernel : Matrix.mulVec (matrix m centers f g columns) v = 0 :=
    (finMatrix_mulVec_eq_zero_iff m centers f g columns v).mp hMv
  refine ⟨v, hv, hkernel, hdegree, hprimitive, ?_,
    (matrix_mulVec_eq_zero_iff m centers f g columns v).mp hkernel⟩
  intro E _ ι z
  exact map_interpolant_ne_zero columns hcolumns v ι z (hnozero ι z)

end ReedSolomon.HiddenDerivative.SymbolicReceivedInterpolation
