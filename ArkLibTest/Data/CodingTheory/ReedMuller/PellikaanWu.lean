/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedMuller.PellikaanWu
import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! # Acceptance cases for the Pellikaan–Wu substitution -/

open FiniteField ReedMuller Polynomial

private instance : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩

private theorem finrank_eq : Module.finrank (ZMod 2) (GaloisField 2 2) = 2 :=
  GaloisField.finrank 2 (by norm_num)

private noncomputable def b : Module.Basis (Fin 2) (ZMod 2) (GaloisField 2 2) :=
  Module.finBasisOfFinrankEq _ _ finrank_eq

-- Over `F₂ ⊆ F₄` (`k = 2`, `n = 4`), substituting into `X₀ X₁` evaluates to the product of the
-- trace coordinates `Tr(b₀ x) Tr(b₁ x)`.
example (x : GaloisField 2 2) :
    (traceSubstitution b (MvPolynomial.X 0 * MvPolynomial.X 1 :
      MvPolynomial (Fin 2) (GaloisField 2 2))).eval x =
      algebraMap (ZMod 2) _
        (Algebra.trace (ZMod 2) _ (b 0 * x) * Algebra.trace (ZMod 2) _ (b 1 * x)) := by
  have h := eval_traceSubstitution (F' := GaloisField 2 2) b
    (MvPolynomial.X 0 * MvPolynomial.X 1) x
  rw [Algebra.algebraMap_self, RingHom.id_apply] at h
  rw [h]
  simp

-- A polynomial of total degree `D` becomes a univariate polynomial of degree at most
-- `D n / q₀ = 2 D`.
example (P : MvPolynomial (Fin 2) (GaloisField 2 2)) :
    (traceSubstitution b P).natDegree ≤ P.totalDegree * 2 := by
  simpa [ZMod.card] using natDegree_traceSubstitution_le b P

-- Affine polynomials over `F₄` in two variables have total degree `1 < q₀ = 2`, so they are
-- determined by their substitutions.
example (P₁ P₂ : MvPolynomial (Fin 2) (GaloisField 2 2)) (h₁ : P₁.totalDegree ≤ 1)
    (h₂ : P₂.totalDegree ≤ 1) (h : traceSubstitution b P₁ = traceSubstitution b P₂) :
    P₁ = P₂ :=
  injOn_traceSubstitution_totalDegree_lt b (by simp [ZMod.card]; omega)
    (by simp [ZMod.card]; omega) h

-- `X₀ X₁` has total degree `2 = q₀` but degree `1 < q₀` in each variable.
-- It is still determined, among such polynomials, by its substitution.
example (P : MvPolynomial (Fin 2) (GaloisField 2 2))
    (hP : P ∈ MvPolynomial.restrictDegree (Fin 2) (GaloisField 2 2) 1)
    (h : traceSubstitution b P = traceSubstitution b (MvPolynomial.X 0 * MvPolynomial.X 1)) :
    P = MvPolynomial.X 0 * MvPolynomial.X 1 := by
  refine injOn_traceSubstitution b (by simpa [ZMod.card] using hP) ?_ h
  rw [SetLike.mem_coe, ZMod.card, MvPolynomial.mem_restrictDegree_iff_sup]
  intro i
  rw [MvPolynomial.degrees_mul_eq (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _),
    MvPolynomial.degrees_X, MvPolynomial.degrees_X]
  fin_cases i <;> simp

-- A polynomial over the subfield `F₂` maps into `F₄` before substitution.
-- Those of total degree below `2` are still determined.
example (P₁ P₂ : MvPolynomial (Fin 2) (ZMod 2)) (h₁ : P₁.totalDegree ≤ 1)
    (h₂ : P₂.totalDegree ≤ 1)
    (h : traceSubstitution b (P₁.map (algebraMap (ZMod 2) (GaloisField 2 2))) =
      traceSubstitution b (P₂.map (algebraMap (ZMod 2) (GaloisField 2 2)))) :
    P₁ = P₂ :=
  injOn_traceSubstitution_map_totalDegree_lt b (by simp [ZMod.card]; omega)
    (by simp [ZMod.card]; omega) h

-- Over `F₂`, `X₀ X₁` has total degree `2 = q₀` but degree `1 < q₀` in each variable.
-- After mapping into `F₄`, it is still determined among such polynomials by its substitution.
example (P : MvPolynomial (Fin 2) (ZMod 2))
    (hP : P ∈ MvPolynomial.restrictDegree (Fin 2) (ZMod 2) 1)
    (h : traceSubstitution b (P.map (algebraMap (ZMod 2) (GaloisField 2 2))) =
      traceSubstitution b ((MvPolynomial.X 0 * MvPolynomial.X 1 : MvPolynomial (Fin 2) (ZMod 2)).map
        (algebraMap (ZMod 2) (GaloisField 2 2)))) :
    P = MvPolynomial.X 0 * MvPolynomial.X 1 := by
  refine injOn_traceSubstitution_map b (by simpa [ZMod.card] using hP) ?_ h
  rw [SetLike.mem_coe, ZMod.card, MvPolynomial.mem_restrictDegree_iff_sup]
  intro i
  rw [MvPolynomial.degrees_mul_eq (MvPolynomial.X_ne_zero _) (MvPolynomial.X_ne_zero _),
    MvPolynomial.degrees_X, MvPolynomial.degrees_X]
  fin_cases i <;> simp

/-- info: 'ReedMuller.natDegree_traceSubstitution_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.natDegree_traceSubstitution_le

/-- info: 'ReedMuller.eval_traceSubstitution' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.eval_traceSubstitution


/-- info: 'ReedMuller.traceSubstitution_X' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.traceSubstitution_X

/-- info: 'ReedMuller.injOn_traceSubstitution' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.injOn_traceSubstitution

/-- info: 'ReedMuller.injOn_traceSubstitution_totalDegree_lt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.injOn_traceSubstitution_totalDegree_lt

/-- info: 'ReedMuller.injOn_traceSubstitution_map' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.injOn_traceSubstitution_map

/-- info: 'ReedMuller.injOn_traceSubstitution_map_totalDegree_lt' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.injOn_traceSubstitution_map_totalDegree_lt
