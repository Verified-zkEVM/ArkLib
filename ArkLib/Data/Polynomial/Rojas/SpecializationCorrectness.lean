/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.HyperplaneAvoidance
public import ArkLib.Data.Polynomial.Rojas.SpecializationFamily
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.Perfect

/-!
# Correctness of computed Rojas specialization families

This file connects the executable Step 0--3 family to the geometric
factorization supplied by the toric perturbation theorem.  The factorization
is an explicit premise: this module neither constructs a toric resultant nor
assumes that an arbitrary polynomial has the required factors.
-/

@[expose] public section

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
  multiplicity : Fin M → ℕ
  multiplicity_pos : ∀ j, 0 < multiplicity j
  factors : ∀ u : Fin s → F,
    (specializePerturbation perturbation u).toPoly.map ι =
      Polynomial.C (leading u) * ∏ j,
        (Polynomial.X - Polynomial.C (geometricProjection ι u (points j))) ^
          multiplicity j

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
    [IsAlgClosed K]
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
  have heliminant : eliminant ≠ 0 := by
    have hmapNe : eliminant.toPoly.map ι ≠ 0 := by
      rw [hfactorization.factors u]
      exact mul_ne_zero (Polynomial.C_ne_zero.mpr (hfactorization.leading_ne_zero u))
        (by
          apply Finset.prod_ne_zero_iff.mpr
          intro j _
          exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero _))
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
          Polynomial.C (geometricProjection ι u (points j))) ^
            hfactorization.multiplicity j) = 0
      rw [map_prod]
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      simp [Nat.ne_of_gt (hfactorization.multiplicity_pos j)]
    · exact (Polynomial.map_ne_zero_iff ι.injective).mpr
        ((CPolynomial.toPoly_eq_zero_iff _).not.mpr hsupportNe)
  have hsupportRootsSubset :
      ((squarefreeSupport p eliminant).toPoly.map ι).roots.toFinset ⊆ roots := by
    intro root hroot
    have hsupportMapNe :
        (squarefreeSupport p eliminant).toPoly.map ι ≠ 0 :=
      (Polynomial.map_ne_zero_iff ι.injective).mpr
        ((CPolynomial.toPoly_eq_zero_iff _).not.mpr hsupportNe)
    have hsupportEval :
        Polynomial.eval root ((squarefreeSupport p eliminant).toPoly.map ι) = 0 :=
      (Polynomial.mem_roots hsupportMapNe).mp (Multiset.mem_toFinset.mp hroot)
    rw [Polynomial.eval_map] at hsupportEval
    have heliminantEval : Polynomial.eval root (eliminant.toPoly.map ι) = 0 := by
      rw [Polynomial.eval_map]
      exact (eval₂_squarefreeSupport_eq_zero_iff p ι root heliminant).mp hsupportEval
    rw [hfactorization.factors u, Polynomial.eval_mul,
      Polynomial.eval_C] at heliminantEval
    rcases mul_eq_zero.mp heliminantEval with hleading | hproduct
    · exact (hfactorization.leading_ne_zero u hleading).elim
    · change (Polynomial.evalRingHom root)
        (∏ j, (Polynomial.X -
          Polynomial.C (geometricProjection ι u (points j))) ^
            hfactorization.multiplicity j) = 0 at hproduct
      rw [map_prod] at hproduct
      obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hproduct
      rw [map_pow] at hj
      have hjbase := (pow_eq_zero_iff
        (Nat.ne_of_gt (hfactorization.multiplicity_pos j))).mp hj
      change Polynomial.eval root
        (Polynomial.X - Polynomial.C (geometricProjection ι u (points j))) = 0 at hjbase
      rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at hjbase
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ j, (sub_eq_zero.mp hjbase).symm⟩
  have hrootsEq :
      roots = ((squarefreeSupport p eliminant).toPoly.map ι).roots.toFinset :=
    Finset.Subset.antisymm hrootsSubset hsupportRootsSubset
  have hseparable :
      ((squarefreeSupport p eliminant).toPoly.map ι).Separable :=
    (PerfectField.separable_iff_squarefree.mpr
      (squarefreeSupport_squarefree p heliminant)).map
  have hdegreeSupport : (squarefreeSupport p eliminant).natDegree = M := by
    calc
      _ = ((squarefreeSupport p eliminant).toPoly.map ι).natDegree := by
        rw [Polynomial.natDegree_map_eq_of_injective ι.injective, natDegree_toPoly]
      _ = ((squarefreeSupport p eliminant).toPoly.map ι).roots.card :=
        (IsAlgClosed.splits _).natDegree_eq_card_roots
      _ = ((squarefreeSupport p eliminant).toPoly.map ι).roots.toFinset.card :=
        (Multiset.toFinset_card_of_nodup (Polynomial.nodup_roots hseparable)).symm
      _ = roots.card := congrArg Finset.card hrootsEq.symm
      _ = M := hrootsCard
  exact ⟨heliminant, hdegreeSupport⟩

/-- Simultaneous injectivity of the `2s+1` geometric projections makes the
actually computed Step 0--3 candidate pass the executable support-degree
guard. -/
theorem candidate_hasExpected_of_injectiveProjections
    [IsAlgClosed K]
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
    [IsAlgClosed K]
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
