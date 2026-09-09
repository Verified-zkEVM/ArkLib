/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Polynomial.Rojas.HyperplaneAvoidance
import ArkLib.Data.Polynomial.Rojas.SpecializationFamily

/-!
# Correctness of computed Rojas specialization families

This file connects the executable Step 0--3 family to the geometric
factorization supplied by the toric perturbation theorem.  The factorization
is an explicit premise: this module neither constructs a toric resultant nor
assumes that an arbitrary polynomial has the required factors.
-/

namespace ArkLib.Rojas

open CPoly
open CompPoly CompPoly.CPolynomial
open Polynomial

variable {F K : Type*} [Field F] [Field K] [Fintype F]
variable [BEq F] [LawfulBEq F]
variable {s M : ℕ}

/-- The geometric root of the specialized linear form attached to one point. -/
def geometricProjection (ι : F →+* K) (u : Fin s → F) (point : Fin s → K) : K :=
  -∑ i, ι (u i) * point i

/-- Required output contract of the upstream toric perturbation producer.
Every actual specialization factors over `K` into the stated geometric linear
forms with a nonzero scalar. -/
structure PerturbationFactorization
    (ι : F →+* K) (perturbation : CMvPolynomial (s + 1) F)
    (points : Fin M → Fin s → K) where
  leading : K
  leading_ne_zero : leading ≠ 0
  factors : ∀ u : Fin s → F,
    (specializePerturbation perturbation u).toPoly.map ι =
      Polynomial.C leading * ∏ j,
        (Polynomial.X - Polynomial.C (geometricProjection ι u (points j)))

variable (p : ℕ) [Fact p.Prime] [CharP F p]

/-- One factorization with distinct projected roots certifies the executable
squarefree support as nonzero and of exact degree `M`. -/
theorem squarefreeSupport_degree_eq_of_factorization
    (ι : F →+* K) {perturbation : CMvPolynomial (s + 1) F}
    {points : Fin M → Fin s → K}
    (hfactorization : PerturbationFactorization ι perturbation points)
    (u : Fin s → F)
    (hinjective : Function.Injective fun j ↦ geometricProjection ι u (points j)) :
    let eliminant := specializePerturbation perturbation u
    eliminant ≠ 0 ∧ (squarefreeSupport p eliminant).natDegree = M := by
  classical
  dsimp only
  let eliminant := specializePerturbation perturbation u
  have hdegreeMap : (eliminant.toPoly.map ι).natDegree = M := by
    rw [hfactorization.factors u,
      Polynomial.natDegree_C_mul hfactorization.leading_ne_zero,
      Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
    simp
  have hdegree : eliminant.natDegree = M := by
    rw [natDegree_toPoly, ← Polynomial.natDegree_map_eq_of_injective ι.injective]
    exact hdegreeMap
  have heliminant : eliminant ≠ 0 := by
    have hmapNe : eliminant.toPoly.map ι ≠ 0 := by
      rw [hfactorization.factors u]
      exact mul_ne_zero (Polynomial.C_ne_zero.mpr hfactorization.leading_ne_zero)
        (by
          simpa using (Polynomial.monic_prod_X_sub_C
            (fun j ↦ geometricProjection ι u (points j))
            (Finset.univ : Finset (Fin M))).ne_zero)
    have htoPoly := (Polynomial.map_ne_zero_iff ι.injective).mp hmapNe
    exact fun hzero ↦ htoPoly ((CPolynomial.toPoly_eq_zero_iff eliminant).mpr hzero)
  have hsupportNe := squarefreeSupport_ne_zero p heliminant
  let roots : Finset K := Finset.univ.image fun j ↦
    geometricProjection ι u (points j)
  have hrootsCard : roots.card = M := by
    calc
      roots.card = (Finset.univ : Finset (Fin M)).card := by
        apply Finset.card_image_iff.mpr
        intro left _ right _ hequal
        exact hinjective hequal
      _ = M := by simp
  have hrootsSubset :
      roots ⊆ ((squarefreeSupport p eliminant).toPoly.map ι).roots.toFinset := by
    intro root hroot
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hroot
    rw [Multiset.mem_toFinset, Polynomial.mem_roots]
    · change Polynomial.eval _
        ((squarefreeSupport p eliminant).toPoly.map ι) = 0
      rw [Polynomial.eval_map]
      rw [eval₂_squarefreeSupport_eq_zero_iff p ι _ heliminant]
      rw [← Polynomial.eval_map, hfactorization.factors u]
      simp only [Polynomial.eval_mul, Polynomial.eval_C, mul_eq_zero]
      right
      change Polynomial.evalRingHom (geometricProjection ι u (points j))
        (∏ j, (Polynomial.X -
          Polynomial.C (geometricProjection ι u (points j)))) = 0
      rw [map_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp
    · exact (Polynomial.map_ne_zero_iff ι.injective).mpr
        ((CPolynomial.toPoly_eq_zero_iff _).not.mpr hsupportNe)
  have hlower : M ≤ (squarefreeSupport p eliminant).natDegree := by
    rw [← hrootsCard]
    exact (Finset.card_le_card hrootsSubset).trans <|
      (Multiset.toFinset_card_le _).trans <|
        ((Polynomial.card_roots' _).trans_eq
          (Polynomial.natDegree_map_eq_of_injective ι.injective
            (squarefreeSupport p eliminant).toPoly)).trans_eq
              (natDegree_toPoly _).symm
  have hupper : (squarefreeSupport p eliminant).natDegree ≤ M :=
    (natDegree_squarefreeSupport_le p heliminant).trans_eq hdegree
  exact ⟨heliminant, Nat.le_antisymm hupper hlower⟩

end ArkLib.Rojas
