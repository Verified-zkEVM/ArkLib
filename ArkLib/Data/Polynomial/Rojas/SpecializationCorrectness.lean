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
For every specialization, the entire finite perturbation-root multiset factors
over `K` into the stated geometric linear forms, up to a specialization-dependent
nonzero scalar.  The indexed points therefore cannot merely be a subset of
isolated roots when extra roots or positive-dimensional components remain. -/
structure PerturbationFactorization
    (ι : F →+* K) (perturbation : CMvPolynomial (s + 1) F)
    (points : Fin M → Fin s → K) where
  leading : (Fin s → F) → K
  leading_ne_zero : ∀ u, leading u ≠ 0
  factors : ∀ u : Fin s → F,
    (specializePerturbation perturbation u).toPoly.map ι =
      Polynomial.C (leading u) * ∏ j,
        (Polynomial.X - Polynomial.C (geometricProjection ι u (points j)))

variable (p : ℕ) [Fact p.Prime] [CharP F p]

omit [Fintype F] [BEq F] [LawfulBEq F] in
theorem geometricProjection_momentCurve
    (ι : F →+* K) (ε : F) (point : Fin s → K) :
    geometricProjection ι (momentCurve ε) point =
      (shiftedProjectionPolynomial (0 : K) (.inl ()) point).eval (ι ε) := by
  simp [geometricProjection, momentCurve]

omit [Fintype F] [BEq F] [LawfulBEq F] in
theorem sum_setCoordinate
    (ι : F →+* K) (u : Fin s → F) (point : Fin s → K)
    (i : Fin s) (value : F) :
    (∑ j, ι (setCoordinate u i value j) * point j) =
      (∑ j, ι (u j) * point j) + (ι value - ι (u i)) * point i := by
  calc
    _ = ∑ j, (ι (u j) * point j +
        if j = i then (ι value - ι (u i)) * point i else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hji : j = i
      · subst j
        simp [setCoordinate]
        ring
      · simp [setCoordinate, hji]
    _ = _ := by
      rw [Finset.sum_add_distrib]
      simp

omit [Fintype F] [BEq F] [LawfulBEq F] in
theorem geometricProjection_momentCurve_minus
    (ι : F →+* K) (ε : F) (point : Fin s → K) (i : Fin s) :
    geometricProjection ι
        (setCoordinate (momentCurve ε) i (momentCurve ε i - 1)) point =
      (shiftedProjectionPolynomial (0 : K) (.inr (.inl i)) point).eval (ι ε) := by
  rw [geometricProjection, sum_setCoordinate]
  simp [momentCurve]
  ring

omit [Fintype F] [BEq F] [LawfulBEq F] in
theorem geometricProjection_momentCurve_plus
    (ι : F →+* K) (α ε : F) (point : Fin s → K) (i : Fin s) :
    geometricProjection ι
        (setCoordinate (momentCurve ε) i (momentCurve ε i + α)) point =
      (shiftedProjectionPolynomial (ι α) (.inr (.inr i)) point).eval (ι ε) := by
  rw [geometricProjection, sum_setCoordinate]
  simp [momentCurve]
  ring

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
      Polynomial.natDegree_C_mul (hfactorization.leading_ne_zero u),
      Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
    simp
  have hdegree : eliminant.natDegree = M := by
    rw [natDegree_toPoly, ← Polynomial.natDegree_map_eq_of_injective ι.injective]
    exact hdegreeMap
  have heliminant : eliminant ≠ 0 := by
    have hmapNe : eliminant.toPoly.map ι ≠ 0 := by
      rw [hfactorization.factors u]
      exact mul_ne_zero (Polynomial.C_ne_zero.mpr (hfactorization.leading_ne_zero u))
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

/-- Simultaneous injectivity of the `2s+1` geometric projections makes the
actually computed Step 0--3 candidate pass the executable support-degree
guard. -/
theorem candidate_hasExpected_of_injectiveProjections
    (ι : F →+* K) {perturbation : CMvPolynomial (s + 1) F}
    {points : Fin M → Fin s → K}
    (hfactorization : PerturbationFactorization ι perturbation points)
    (α ε : F)
    (hinjective : ∀ kind : ProjectionKind s,
      Function.Injective fun j ↦
        (shiftedProjectionPolynomial (ι α) kind (points j)).eval (ι ε)) :
    HasExpectedSupportDegree p s M
      (candidateFromParameter perturbation α ε) := by
  have hbase := squarefreeSupport_degree_eq_of_factorization p ι hfactorization
    (momentCurve ε) (by
      intro left right hequal
      apply hinjective (.inl ())
      simpa only [geometricProjection_momentCurve,
        eval_shiftedProjectionPolynomial_base] using hequal)
  refine ⟨candidateFromParameter_shiftedEliminants_length perturbation α ε,
    hbase.1, hbase.2, ?_⟩
  intro shifted hshifted
  change shifted ∈
    (specializationFamily perturbation (momentCurve ε) α).shiftedEliminants at hshifted
  rw [SpecializationFamily.shiftedEliminants, List.mem_append] at hshifted
  rcases hshifted with hminus | hplus
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hminus
    apply squarefreeSupport_degree_eq_of_factorization p ι hfactorization
    intro left right hequal
    apply hinjective (.inr (.inl i))
    simpa only [geometricProjection_momentCurve_minus,
      eval_shiftedProjectionPolynomial_plus] using hequal
  · obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hplus
    apply squarefreeSupport_degree_eq_of_factorization p ι hfactorization
    intro left right hequal
    apply hinjective (.inr (.inr i))
    simpa only [geometricProjection_momentCurve_plus] using hequal

/-- Under the explicit complete perturbation factorization, any duplicate-free
parameter list longer than the collision bound makes the actual executable scan
succeed.  The selected value is one of the candidates computed from that list. -/
theorem selectParameter?_exists_of_factorization
    (ι : F →+* K) {perturbation : CMvPolynomial (s + 1) F}
    {points : Fin M → Fin s → K}
    (hfactorization : PerturbationFactorization ι perturbation points)
    (hpoints : Function.Injective points)
    (α : F) (parameters : List F) (hnodup : parameters.Nodup)
    (hlength : s * (2 * s + 1) * M.choose 2 < parameters.length) :
    ∃ selected,
      selectParameter? p perturbation α M parameters = some selected ∧
      HasExpectedSupportDegree p s M selected ∧
      ∃ ε ∈ parameters,
        selected = candidateFromParameter perturbation α ε := by
  obtain ⟨ε, hε, hinjective⟩ :=
    exists_parameter_with_injective_projections ι (ι α) hpoints parameters hnodup hlength
  have hvalid := candidate_hasExpected_of_injectiveProjections
    p ι hfactorization α ε hinjective
  have hexists : ∃ selected,
      selectParameter? p perturbation α M parameters = some selected :=
    (selectParameter?_exists_iff p perturbation α M parameters).2 ⟨ε, hε, hvalid⟩
  obtain ⟨selected, hselected⟩ := hexists
  exact ⟨selected, hselected, selectParameter?_sound p hselected⟩

end ArkLib.Rojas
