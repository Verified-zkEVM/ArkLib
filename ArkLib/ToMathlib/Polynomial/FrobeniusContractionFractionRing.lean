/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.Polynomial.FrobeniusContraction
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Frobenius contraction and passage to a fraction field

The terminal polynomial produced by coefficient-preserving Frobenius contraction is primitive
when the original polynomial is irreducible and has positive degree.  Gauss's lemma therefore
makes it irreducible over the fraction field.  Its nonzero derivative remains nonzero under the
injective fraction-field map, so the mapped polynomial is separable.

This file only connects contraction over a GCD domain to the corresponding fraction-field
polynomial.  It does not prove a geometric reconstruction or an agreement bound.
-/

@[expose] public section

namespace Polynomial

noncomputable section

variable {R K : Type*} [CommRing R] [IsDomain R] [IsGCDMonoid R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- An irreducible positive-degree polynomial with nonzero derivative over a GCD domain is
primitive, and its image in the fraction field is irreducible and separable.  The injectivity of
the fraction-field map also preserves its exact natural degree. -/
theorem irreducible_separable_map_fractionRing {G : R[X]} (hGirr : Irreducible G)
    (hGpos : 0 < G.natDegree) (hGder : derivative G ≠ 0) :
    G.IsPrimitive ∧
      Irreducible (G.map (algebraMap R K)) ∧
      derivative (G.map (algebraMap R K)) ≠ 0 ∧
      (G.map (algebraMap R K)).Separable ∧
      (G.map (algebraMap R K)).natDegree = G.natDegree := by
  have hprimitive : G.IsPrimitive := hGirr.isPrimitive (Nat.ne_of_gt hGpos)
  have hmapirr : Irreducible (G.map (algebraMap R K)) :=
    (hprimitive.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hGirr
  have hmapder : derivative (G.map (algebraMap R K)) ≠ 0 := by
    rw [derivative_map]
    exact (Polynomial.map_ne_zero_iff (IsFractionRing.injective R K)).mpr hGder
  exact ⟨hprimitive, hmapirr, hmapder, (separable_iff_derivative_ne_zero hmapirr).mpr hmapder,
    natDegree_map_eq_of_injective (IsFractionRing.injective R K) G⟩

variable (p : ℕ) [CharP R p] [Fact p.Prime]

/-- A positive-degree irreducible polynomial over a GCD domain admits a coefficient-preserving
Frobenius contraction whose terminal polynomial becomes irreducible and separable over the
fraction field.  Both the contraction degree identity and the mapped polynomial's exact degree
are retained. -/
theorem exists_frobeniusContraction_fractionRing {P : R[X]} (hPpos : 0 < P.natDegree)
    (hPirr : Irreducible P) :
    ∃ e : ℕ, ∃ G : R[X],
      derivative G ≠ 0 ∧
      expand R (p ^ e) G = P ∧
      G.natDegree * (p ^ e) = P.natDegree ∧
      0 < G.natDegree ∧
      G.IsPrimitive ∧
      Irreducible (G.map (algebraMap R K)) ∧
      derivative (G.map (algebraMap R K)) ≠ 0 ∧
      (G.map (algebraMap R K)).Separable ∧
      (G.map (algebraMap R K)).natDegree = G.natDegree := by
  obtain ⟨e, G, hGder, hGP, hGdeg, hGpos, hGirr⟩ :=
    exists_irreducible_frobeniusContraction p hPpos hPirr
  obtain ⟨hprimitive, hmapirr, hmapder, hmapsep, hmapdeg⟩ :=
    irreducible_separable_map_fractionRing (K := K) hGirr hGpos hGder
  exact ⟨e, G, hGder, hGP, hGdeg, hGpos, hprimitive, hmapirr, hmapder, hmapsep, hmapdeg⟩

omit [IsDomain R] [IsGCDMonoid R] [IsFractionRing R K] in
/-- A small fraction-field canary: the variable itself retains degree one, stays irreducible, and
is separable after mapping into the fraction field. -/
theorem fractionRing_X_canary :
    Irreducible ((X : R[X]).map (algebraMap R K)) ∧
      ((X : R[X]).map (algebraMap R K)).Separable ∧
      ((X : R[X]).map (algebraMap R K)).natDegree = 1 := by
  have hmapX : (X : R[X]).map (algebraMap R K) = X := map_X (algebraMap R K)
  rw [hmapX]
  exact ⟨irreducible_X, separable_X, natDegree_X⟩

/-- A coefficient-sensitive canary for the fraction-field bridge.  The nonmonic linear
polynomial `a * X + 1` is primitive over the source GCD domain, remains irreducible and becomes
separable over the fraction field, and its mapped derivative records the nonzero image of `a`.
-/
theorem fractionRing_nonmonicLinear_canary (a : R) (ha : a ≠ 0) :
    let G : R[X] := C a * X + 1
    G.IsPrimitive ∧
      Irreducible (G.map (algebraMap R K)) ∧
      derivative (G.map (algebraMap R K)) = C (algebraMap R K a) ∧
      derivative (G.map (algebraMap R K)) ≠ 0 ∧
      (G.map (algebraMap R K)).Separable ∧
      (G.map (algebraMap R K)).natDegree = 1 := by
  dsimp only
  let G : R[X] := C a * X + 1
  have hGirr : Irreducible G := by
    simpa only [G, C_1] using irreducible_C_mul_X_add_C ha isRelPrime_one_right
  have hGdeg : G.natDegree = 1 := by
    simpa only [G, C_1] using natDegree_linear (b := 1) ha
  have hGpos : 0 < G.natDegree := by
    rw [hGdeg]
    exact Nat.zero_lt_one
  have hGder : derivative G ≠ 0 := by
    simpa only [G, derivative_add, derivative_C_mul_X, derivative_one, add_zero] using
      C_ne_zero.mpr ha
  obtain ⟨hprimitive, hmapirr, hmapder, hmapsep, hmapdeg⟩ :=
    irreducible_separable_map_fractionRing (K := K) hGirr hGpos hGder
  have hmapder_eq : derivative (G.map (algebraMap R K)) = C (algebraMap R K a) := by
    rw [derivative_map]
    simp only [G, derivative_add, derivative_C_mul_X, derivative_one, add_zero, map_C]
  refine ⟨hprimitive, hmapirr, hmapder_eq, hmapder, hmapsep, ?_⟩
  rw [hmapdeg, hGdeg]

end

end Polynomial
