/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.ConstraintMap
public import Mathlib.Algebra.BigOperators.Intervals
/-!
# The exact order-zero local image is triangular

At order zero the actual generator images are a+T and y+T*E. Every image monomial therefore
has E exponent at most T exponent. The actual contact projection retains T exponent below m,
so the full local map, even on its infinite-dimensional domain, has triangular finite rank.
This local result alone is not a global interpolation witness or a small-block decoder.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

noncomputable section

open MvPolynomial PolynomialDifferential
open scoped BigOperators Pointwise

variable {R : Type*} [CommRing R]

private theorem cone_C (a : R) :
    ∀ e ∈ (C a : LocalPolynomial R 0).support, e (localE 0) ≤ e (localT 0) := by
  intro e he
  have hh := MvPolynomial.support_monomial_subset he
  have heq : e = 0 := Finset.mem_singleton.mp hh
  subst e
  simp

private theorem cone_add {P Q : LocalPolynomial R 0}
    (hp : ∀ e ∈ P.support, e (localE 0) ≤ e (localT 0))
    (hq : ∀ e ∈ Q.support, e (localE 0) ≤ e (localT 0)) :
    ∀ e ∈ (P + Q).support, e (localE 0) ≤ e (localT 0) := by
  intro e he
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with he | he
  · exact hp e he
  · exact hq e he

private theorem cone_mul {P Q : LocalPolynomial R 0}
    (hp : ∀ e ∈ P.support, e (localE 0) ≤ e (localT 0))
    (hq : ∀ e ∈ Q.support, e (localE 0) ≤ e (localT 0)) :
    ∀ e ∈ (P * Q).support, e (localE 0) ≤ e (localT 0) := by
  intro e he
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q he)
  exact add_le_add (hp a ha) (hq b hb)

private theorem cone_T :
    ∀ e ∈ (X (localT 0) : LocalPolynomial R 0).support, e (localE 0) ≤ e (localT 0) := by
  intro e he
  have hh := MvPolynomial.support_monomial_subset he
  have heq := Finset.mem_singleton.mp hh
  subst e
  simp [localT, localE, localAux]

private theorem cone_TE :
    ∀ e ∈ (X (localT 0) * X (localE 0) : LocalPolynomial R 0).support,
      e (localE 0) ≤ e (localT 0) := by
  intro e he
  rw [X, X, monomial_mul] at he
  have hh := MvPolynomial.support_monomial_subset he
  have heq := Finset.mem_singleton.mp hh
  subst e
  simp [localT, localE, localAux]

/-- The unscaled source map has triangular support before any projection, for every polynomial. -/
theorem unscaled_zero_support (a y : R) (Q : DifferentialPolynomial R 0) :
    ∀ e ∈ (unscaledLocalSubstitution 0 a y Q).support,
      e (localE 0) ≤ e (localT 0) := by
  induction Q using MvPolynomial.induction_on with
  | C c => simp [unscaledLocalSubstitution]
  | add P Q hp hq => simpa only [map_add] using cone_add hp hq
  | mul_X P v hp =>
    rw [map_mul]
    apply cone_mul hp
    cases v with
    | none => rw [unscaledLocalSubstitution_X]; exact cone_add (cone_C a) cone_T
    | some j =>
      have hj : j = 0 := by apply Fin.ext; omega
      subst j
      rw [unscaledLocalSubstitution_Y_zero]
      simpa [localCorrection] using cone_add (cone_C y) cone_TE

/-- Contact order at d=0 is exactly the T exponent. -/
theorem localContactOrder_zero (e : LocalVariable 0 →₀ ℕ) :
    localContactOrder 0 e = e (localT 0) := by
  rw [localContactOrder, Finsupp.weight_eq_sum]
  simp only [smul_eq_mul, Fintype.sum_option, Finset.univ_unique, Finset.sum_singleton]
  simp only [localContactWeight, localT, mul_one, add_eq_left, mul_eq_zero]
  right
  rfl

/-- The actual local constraint image has E≤T<m, without any source-support hypothesis. -/
theorem localConstraint_zero_support (m : ℕ) (a y : R) (Q : DifferentialPolynomial R 0)
    (e : LocalVariable 0 →₀ ℕ) (he : e ∈ (localConstraintAt m a y Q).support) :
    e (localE 0) ≤ e (localT 0) ∧ e (localT 0) < m := by
  have hc := MvPolynomial.mem_support_iff.mp he
  change MvPolynomial.coeff e (projectLowContact m (unscaledLocalSubstitution 0 a y Q)) ≠ 0 at hc
  simp only [projectLowContact, coeff_filterLocalMonomials, localContactOrder_zero] at hc
  split_ifs at hc with h
  · exact ⟨unscaled_zero_support a y Q e (MvPolynomial.mem_support_iff.mpr hc), h⟩
  · exact (hc rfl).elim

/-- Finite triangular coordinates, ordered by T exponent and then E exponent. -/
abbrev ZeroLocalIndex (m : ℕ) := Σ t : Fin m, Fin (t.val + 1)

/-- Embed the two exponents into the actual local variable type. -/
def zeroLocalExponent (t b : ℕ) : LocalVariable 0 →₀ ℕ :=
  Finsupp.single (localT 0) t + Finsupp.single (localE 0) b

/-- No further local coordinates exist at derivative order zero. -/
theorem zeroLocalExponent_reconstruct (e : LocalVariable 0 →₀ ℕ) :
    zeroLocalExponent (e (localT 0)) (e (localE 0)) = e := by
  ext v
  cases v with
  | none => simp [zeroLocalExponent, localT, localE, localAux]
  | some v =>
    cases v with
    | none => simp [zeroLocalExponent, localT, localE, localAux]
    | some j => exact Fin.elim0 j

/-- The literal finite triangular exponent set. -/
def zeroLocalExponents (m : ℕ) : Finset (LocalVariable 0 →₀ ℕ) :=
  Finset.univ.image (fun p : ZeroLocalIndex m ↦ zeroLocalExponent p.1.val p.2.val)

/-- Membership is precisely the triangular support predicate. -/
theorem mem_zeroLocalExponents (m : ℕ) (e : LocalVariable 0 →₀ ℕ) :
    e ∈ zeroLocalExponents m ↔ e (localE 0) ≤ e (localT 0) ∧ e (localT 0) < m := by
  constructor
  · intro he
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
    simpa [zeroLocalExponent, localT, localE, localAux] using
      And.intro (Nat.le_of_lt_succ p.2.isLt) p.1.isLt
  · rintro ⟨hle, hlt⟩
    exact Finset.mem_image.mpr ⟨⟨⟨_, hlt⟩, ⟨_, Nat.lt_succ_of_le hle⟩⟩,
      Finset.mem_univ _, zeroLocalExponent_reconstruct e⟩

/-- The finite triangular index has m(m+1)/2 entries. -/
theorem card_zeroLocalIndex (m : ℕ) : Fintype.card (ZeroLocalIndex m) = m * (m + 1) / 2 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [show (∑ x : Fin m, (x.val + 1)) = ∑ x ∈ Finset.range m, (x + 1) from
    Fin.sum_univ_eq_sum_range (fun x ↦ x + 1) m]
  have hsum := Finset.sum_range_id_mul_two m
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one]
  have hm : m * (m - 1) + 2 * m = m * (m + 1) := by
    cases m with
    | zero => rfl
    | succ m => simp; ring
  omega

/-- The actual triangular exponent set has at most the expected number of coordinates. -/
theorem card_zeroLocalExponents_le (m : ℕ) : (zeroLocalExponents m).card ≤ m * (m + 1) / 2 := by
  exact (Finset.card_image_le).trans (by rw [Finset.card_univ, card_zeroLocalIndex])

/-- The entire actual local map lands in the finite triangular monomial subspace. -/
theorem range_localConstraint_zero_le (m : ℕ) (a y : R) :
    (localConstraintAt (d := 0) m a y).range ≤
      MvPolynomial.restrictSupport R (zeroLocalExponents m : Set (LocalVariable 0 →₀ ℕ)) := by
  rintro P ⟨Q, rfl⟩
  rw [MvPolynomial.mem_restrictSupport_iff]
  intro e he
  exact (mem_zeroLocalExponents m e).mpr (localConstraint_zero_support m a y Q e he)

/-- The actual whole-map range is finite dimensional despite its unrestricted source domain. -/
theorem finite_localConstraint_zero_range {F : Type*} [Field F] (m : ℕ) (a y : F) :
    Module.Finite F (localConstraintAt (d := 0) m a y).range := by
  let s := zeroLocalExponents m
  let V := MvPolynomial.restrictSupport F (s : Set (LocalVariable 0 →₀ ℕ))
  let b := MvPolynomial.basisRestrictSupport (R := F) (s : Set (LocalVariable 0 →₀ ℕ))
  let _ : Module.Finite F V := Module.Finite.of_basis b
  exact Submodule.finiteDimensional_of_le (range_localConstraint_zero_le m a y)

/-- The whole local constraint range is finite dimensional and has triangular rank. -/
theorem finrank_localConstraint_zero_le {F : Type*} [Field F] (m : ℕ) (a y : F) :
    Module.finrank F (localConstraintAt (d := 0) m a y).range ≤ m * (m + 1) / 2 := by
  let s := zeroLocalExponents m
  let V := MvPolynomial.restrictSupport F (s : Set (LocalVariable 0 →₀ ℕ))
  let b := MvPolynomial.basisRestrictSupport (R := F) (s : Set (LocalVariable 0 →₀ ℕ))
  let _ : Module.Finite F V := Module.Finite.of_basis b
  have hdim : Module.finrank F V = s.card := by
    rw [← Fintype.card_coe]
    exact Module.finrank_eq_card_basis b
  exact (Submodule.finrank_mono (range_localConstraint_zero_le m a y)).trans
    (hdim.le.trans (card_zeroLocalExponents_le m))

/-- Any restricted source space inherits the same triangular local rank bound. -/
theorem finrank_localConstraint_zero_domRestrict_le {F : Type*} [Field F] (m : ℕ) (a y : F)
    (V : Submodule F (DifferentialPolynomial F 0)) :
    Module.finrank F ((localConstraintAt (d := 0) m a y).domRestrict V).range ≤
      m * (m + 1) / 2 := by
  let _ := finite_localConstraint_zero_range m a y
  have h : ((localConstraintAt (d := 0) m a y).domRestrict V).range ≤
      (localConstraintAt (d := 0) m a y).range := by
    rintro P ⟨Q, rfl⟩
    exact ⟨Q.val, rfl⟩
  exact (Submodule.finrank_mono h).trans (finrank_localConstraint_zero_le m a y)

end
end ReedSolomon.HiddenDerivative
