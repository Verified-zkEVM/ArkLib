/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.CodingTheory.PolishchukSpielman.Resultant
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Resultants detecting regular specializations

For a polynomial in an outer variable whose coefficients are polynomials in a challenge
variable, the fixed-degree resultant of the polynomial and its outer derivative detects the
challenge values at which a root can fail to be regular.  Separability over the fraction field
makes this resultant nonzero, while the Polishchuk--Spielman determinant estimate bounds its
degree in the challenge variable.

The fixed degree parameters are retained under specialization.  Consequently the regularity
implication below remains valid even when specialization lowers one of the outer degrees.
-/

@[expose] public section

open Polynomial.Bivariate

namespace Polynomial

noncomputable section

variable {R F L : Type*}

/-- The outer-variable derivative resultant, with the expected outer degrees `b - 1` and `b`.
The result is a polynomial in the challenge variable. -/
def separableResultant [CommRing R] (A : R[X][X]) (b : ℕ) : R[X] :=
  resultant A.derivative A (b - 1) b

/-- Fraction-field separability makes the derivative resultant nonzero.  Exact outer degree is
needed because the Sylvester matrix uses the declared degrees `b - 1` and `b`. -/
theorem separableResultant_ne_zero_of_map_separable
    [CommRing R] [IsDomain R] [Field L] [Algebra R[X] L] [IsFractionRing R[X] L]
    (A : R[X][X]) {b : ℕ} (hdegree : A.natDegree = b)
    (hseparable : (A.map (algebraMap R[X] L)).Separable) :
    separableResultant A b ≠ 0 := by
  let φ : R[X] →+* L := algebraMap R[X] L
  let A' : L[X] := A.map φ
  have hA'degree : A'.natDegree = b := by
    simpa only [A', φ, hdegree] using
      (natDegree_map_eq_of_injective (IsFractionRing.injective R[X] L) A)
  have hderivativeDegree : A'.derivative.natDegree ≤ b - 1 :=
    (natDegree_derivative_le A').trans (Nat.sub_le_sub_right hA'degree.le 1)
  obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le hderivativeDegree
  have hA'ne : A' ≠ 0 := hseparable.ne_zero
  have hleading : A'.coeff b ≠ 0 := by
    rw [← hA'degree, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hA'ne
  have hcanonical : resultant A'.derivative A' ≠ 0 :=
    resultant_ne_zero A'.derivative A' hseparable.symm
  have hcanonical' :
      resultant A'.derivative A' A'.derivative.natDegree b ≠ 0 := by
    simpa only [hA'degree] using hcanonical
  have hfieldResultant : resultant A'.derivative A' (b - 1) b ≠ 0 := by
    rw [hc, resultant_add_left_deg A'.derivative A'
      A'.derivative.natDegree b c le_rfl]
    exact _root_.mul_ne_zero
      (_root_.mul_ne_zero (by simp) (pow_ne_zero c hleading)) hcanonical'
  have hmap : φ (separableResultant A b) =
      resultant A'.derivative A' (b - 1) b := by
    rw [separableResultant, ← resultant_map_map]
    congr 2
    exact (derivative_map A φ).symm
  intro hzero
  apply hfieldResultant
  rw [← hmap, hzero, map_zero]

/-- An irreducible positive-degree polynomial with nonzero outer derivative satisfies the
fraction-field separability premise.  Primitivity is obtained from irreducibility before applying
Gauss's lemma. -/
theorem separableResultant_ne_zero_of_irreducible
    [Field F] [Field L]
    [Algebra F[X] L] [IsFractionRing F[X] L]
    (A : F[X][X]) {b : ℕ} (hdegree : A.natDegree = b) (hb : 0 < b)
    (hirreducible : Irreducible A) (hderivative : A.derivative ≠ 0) :
    separableResultant A b ≠ 0 := by
  have hpositive : 0 < A.natDegree := by simpa only [hdegree] using hb
  have hprimitive : A.IsPrimitive := hirreducible.isPrimitive (Nat.ne_of_gt hpositive)
  have hmapIrreducible : Irreducible (A.map (algebraMap F[X] L)) :=
    (hprimitive.irreducible_iff_irreducible_map_fraction_map (K := L)).mp hirreducible
  have hmapDerivative : derivative (A.map (algebraMap F[X] L)) ≠ 0 := by
    rw [derivative_map]
    exact (Polynomial.map_ne_zero_iff (p := A.derivative)
      (IsFractionRing.injective F[X] L)).mpr hderivative
  exact separableResultant_ne_zero_of_map_separable A hdegree
    ((separable_iff_derivative_ne_zero hmapIrreducible).mpr hmapDerivative)

/-- If `A` and its outer derivative have challenge degree at most `h`, their derivative
resultant has challenge degree at most `(2 * b - 1) * h`. -/
theorem natDegree_separableResultant_le [CommRing R] (A : R[X][X]) {b h : ℕ}
    (_hdegree : A.natDegree = b) (hb : 0 < b)
    (hA : degreeX A ≤ h) (hderivative : degreeX A.derivative ≤ h) :
    (separableResultant A b).natDegree ≤ (2 * b - 1) * h := by
  calc
    (separableResultant A b).natDegree ≤
        b * degreeX A.derivative + (b - 1) * degreeX A := by
      simpa only [separableResultant] using
        (ps_nat_degree_resultant_le A A.derivative b (b - 1))
    _ ≤ b * h + (b - 1) * h :=
      Nat.add_le_add (Nat.mul_le_mul_left b hderivative)
        (Nat.mul_le_mul_left (b - 1) hA)
    _ = (2 * b - 1) * h := by
      rw [show 2 * b - 1 = b + (b - 1) by omega, Nat.add_mul]

/-- Differentiating in the outer variable does not increase the challenge degree. -/
theorem degreeX_derivative_le [CommRing R] (A : R[X][X]) :
    degreeX A.derivative ≤ degreeX A := by
  classical
  unfold degreeX
  apply Finset.sup_le
  intro i _
  rw [coeff_derivative]
  have h := natDegree_mul_le (p := A.coeff (i + 1)) (q := (i + 1 : ℕ))
  simp only [natDegree_natCast, Nat.add_zero] at h
  simpa only [Nat.cast_add, Nat.cast_one, degreeX] using
    h.trans (coeff_natDegree_le_degreeX A (i + 1))

/-- The resultant bound follows from the challenge height of the original polynomial alone. -/
theorem natDegree_separableResultant_le_of_height [CommRing R] (A : R[X][X]) {b h : ℕ}
    (hdegree : A.natDegree = b) (hb : 0 < b) (hA : degreeX A ≤ h) :
    (separableResultant A b).natDegree ≤ (2 * b - 1) * h :=
  natDegree_separableResultant_le A hdegree hb hA ((degreeX_derivative_le A).trans hA)

/-- A nonzero value of the derivative resultant makes the specialized outer polynomial
separable.  The proof uses the fixed-degree Sylvester Bezout identity, so no preservation of
outer degree under specialization is required. -/
theorem specialization_separable_of_separableResultant_eval_ne_zero
    [Field F]
    (A : F[X][X]) {b : ℕ} (hb : 0 < b) (hdegree : A.natDegree ≤ b) (w : F)
    (hresultant : (separableResultant A b).eval w ≠ 0) :
    (A.map (evalRingHom w)).Separable := by
  let A' : F[X] := A.map (evalRingHom w)
  have hA'degree : A'.natDegree ≤ b := by
    exact (natDegree_map_le (p := A) (f := evalRingHom w)).trans hdegree
  have hderivativeDegree : A'.derivative.natDegree ≤ b - 1 :=
    (natDegree_derivative_le A').trans (Nat.sub_le_sub_right hA'degree 1)
  have hevalResultant : (separableResultant A b).eval w =
      resultant A'.derivative A' (b - 1) b := by
    change (evalRingHom w) (resultant A.derivative A (b - 1) b) = _
    rw [← resultant_map_map]
    congr 2
    exact (derivative_map A (evalRingHom w)).symm
  have hfixedResultant : resultant A'.derivative A' (b - 1) b ≠ 0 := by
    rwa [← hevalResultant]
  obtain ⟨P, Q, -, -, hbezout⟩ :=
    exists_mul_add_mul_eq_C_resultant A'.derivative A' hderivativeDegree hA'degree
      (Or.inr (Nat.ne_of_gt hb))
  rw [separable_def]
  refine ⟨C (resultant A'.derivative A' (b - 1) b)⁻¹ * Q,
    C (resultant A'.derivative A' (b - 1) b)⁻¹ * P, ?_⟩
  calc
    (C (resultant A'.derivative A' (b - 1) b)⁻¹ * Q) * A' +
        (C (resultant A'.derivative A' (b - 1) b)⁻¹ * P) * A'.derivative =
        C (resultant A'.derivative A' (b - 1) b)⁻¹ *
          (A'.derivative * P + A' * Q) := by ring
    _ = C (resultant A'.derivative A' (b - 1) b)⁻¹ *
          C (resultant A'.derivative A' (b - 1) b) := by rw [hbezout]
    _ = 1 := by
      rw [← C_mul, inv_mul_cancel₀ hfixedResultant, C_1]

/-- Away from the derivative resultant, every specialized root is regular. -/
theorem eval_derivative_ne_zero_of_separableResultant_eval_ne_zero
    [Field F]
    (A : F[X][X]) {b : ℕ} (hb : 0 < b) (hdegree : A.natDegree ≤ b)
    (w u : F) (hresultant : (separableResultant A b).eval w ≠ 0)
    (hroot : (A.map (evalRingHom w)).eval u = 0) :
    (A.map (evalRingHom w)).derivative.eval u ≠ 0 := by
  have hseparable := specialization_separable_of_separableResultant_eval_ne_zero
    A hb hdegree w hresultant
  exact hseparable.eval₂_derivative_ne_zero (RingHom.id F) (by simpa using hroot)

/-- Over a domain, a nonzero specialized resultant forces regularity at every root.
This also applies when the root and the coefficients are themselves polynomials. -/
theorem eval_derivative_ne_zero_of_separableResultant_map_ne_zero
    [CommRing R] [IsDomain R]
    {S : Type*} [CommRing S] [IsDomain S]
    (A : R[X][X]) {b : ℕ} (hb : 0 < b) (hdegree : A.natDegree ≤ b)
    (φ : R[X] →+* S) (u : S)
    (hresultant : φ (separableResultant A b) ≠ 0)
    (hroot : (A.map φ).eval u = 0) :
    (A.map φ).derivative.eval u ≠ 0 := by
  let A' := A.map φ
  have hA'degree : A'.natDegree ≤ b := (natDegree_map_le).trans hdegree
  have hderivativeDegree : A'.derivative.natDegree ≤ b - 1 :=
    (natDegree_derivative_le A').trans (Nat.sub_le_sub_right hA'degree 1)
  have hmap : φ (separableResultant A b) =
      resultant A'.derivative A' (b - 1) b := by
    rw [separableResultant, ← resultant_map_map]
    congr 2
    exact (derivative_map A φ).symm
  obtain ⟨P, Q, -, -, hbezout⟩ :=
    exists_mul_add_mul_eq_C_resultant A'.derivative A' hderivativeDegree hA'degree
      (Or.inr (Nat.ne_of_gt hb))
  intro hderivative
  apply hresultant
  rw [hmap]
  change A'.eval u = 0 at hroot
  change A'.derivative.eval u = 0 at hderivative
  have heval := congrArg (Polynomial.eval u) hbezout
  simpa only [eval_add, eval_mul, eval_C, hderivative, hroot,
    zero_mul, add_zero] using heval.symm

/-- Polynomial-valued exceptional specializations have cardinality bounded by the challenge
degree. The base field embeds as constant polynomials, so no coefficient-degree factor appears. -/
theorem finite_polynomial_specializations_eq_zero_card_le [Field F]
    (B : F[X][X]) (hB : B ≠ 0) (S : Finset F)
    (hS : ∀ w ∈ S, B.eval (C w) = 0) : S.card ≤ B.natDegree := by
  classical
  have hcard : S.card = (S.image (C : F → F[X])).card :=
    (Finset.card_image_of_injective S C_injective).symm
  rw [hcard]
  apply le_trans (Finset.card_le_card (t := B.roots.toFinset) ?_)
    ((Multiset.toFinset_card_le B.roots).trans (card_roots' B))
  intro x hx
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hx
  exact Multiset.mem_toFinset.mpr ((mem_roots hB).mpr (hS w hw))

/-- A nonmonic linear canary.  Its outer leading coefficient is `X`, and the derivative
resultant records that coefficient exactly rather than collapsing to a constant. -/
theorem separableResultant_nonmonicLinear_canary [Field F] :
    let A : F[X][X] := C X * X + C 1
    A.natDegree = 1 ∧ ¬A.Monic ∧ A.derivative = C X ∧
      separableResultant A 1 = X ∧ (separableResultant A 1).natDegree = 1 := by
  dsimp only
  let a : F[X] := X
  have ha : a ≠ 0 := X_ne_zero
  have hdegree : (C a * X + C 1 : F[X][X]).natDegree = 1 :=
    natDegree_linear ha
  have hleading : (C a * X + C 1 : F[X][X]).leadingCoeff = a := by
    exact leadingCoeff_linear ha
  have hnotMonic : ¬(C a * X + C 1 : F[X][X]).Monic := by
    rw [Monic, hleading]
    intro haone
    exact X_ne_C (1 : F) (by simpa only [a, C_1] using haone)
  have hderivative : derivative (C a * X + C 1 : F[X][X]) = C a := by simp
  have hresultant : separableResultant (C a * X + C 1 : F[X][X]) 1 = a := by
    simp [separableResultant]
  refine ⟨hdegree, hnotMonic, hderivative, hresultant, ?_⟩
  rw [hresultant]
  exact natDegree_X

/-- Over an infinite domain, one can specialize the coefficient variable away from any finite
set while preserving the exact degree in the outer variable. -/
theorem exists_map_evalRingHom_ne_zero_avoiding [CommRing R] [IsDomain R] [Infinite R]
    (A : R[X][X]) (hA : A ≠ 0) (forbidden : Finset R) :
    ∃ t : R, t ∉ forbidden ∧ A.map (evalRingHom t) ≠ 0 ∧
      (A.map (evalRingHom t)).natDegree = A.natDegree := by
  classical
  let c : R[X] := A.leadingCoeff
  have hc : c ≠ 0 := by
    simpa only [c] using leadingCoeff_ne_zero.mpr hA
  obtain ⟨t, ht⟩ := Infinite.exists_notMem_finset (c.roots.toFinset ∪ forbidden)
  have htforbidden : t ∉ forbidden := fun hmem ↦ ht (Finset.mem_union_right _ hmem)
  have hceval : c.eval t ≠ 0 := by
    intro hzero
    have hroot : IsRoot c t := hzero
    have hmem : t ∈ c.roots.toFinset :=
      Multiset.mem_toFinset.mpr ((mem_roots hc).mpr hroot)
    exact ht (Finset.mem_union_left _ hmem)
  have hleading : (evalRingHom t) (A.leadingCoeff) ≠ 0 := by
    simpa only [c, coe_evalRingHom] using hceval
  have hmapne : A.map (evalRingHom t) ≠ 0 := by
    intro hzero
    have hcoeff := hleading
    rw [leadingCoeff, ← coeff_map, hzero, coeff_zero] at hcoeff
    exact hcoeff rfl
  have hdegree : (A.map (evalRingHom t)).natDegree = A.natDegree :=
    natDegree_map_of_leadingCoeff_ne_zero (evalRingHom t) hleading
  exact ⟨t, htforbidden, hmapne, hdegree⟩

/-- A nonzero polynomial over an infinite domain has a nonzero coefficient specialization,
with exact preservation of its outer degree. -/
theorem exists_map_evalRingHom_ne_zero [CommRing R] [IsDomain R] [Infinite R]
    (A : R[X][X]) (hA : A ≠ 0) :
    ∃ t : R, A.map (evalRingHom t) ≠ 0 ∧
      (A.map (evalRingHom t)).natDegree = A.natDegree := by
  obtain ⟨t, -, ht, hdegree⟩ :=
    exists_map_evalRingHom_ne_zero_avoiding A hA ∅
  exact ⟨t, ht, hdegree⟩

end

end Polynomial
