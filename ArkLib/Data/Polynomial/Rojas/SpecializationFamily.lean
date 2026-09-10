/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Rojas.DeterministicSpecialization
public import ArkLib.ToCompPoly.Multivariate.Substitution

/-!
# Executable Rojas Step 0--3 specialization families

This file turns one already-computed toric perturbation polynomial
`Pert(t, u₁, ..., uₙ)` into the actual univariate family used in Rojas's
Steps 0--3.  It specializes `t` to the univariate indeterminate, uses a
moment-curve Step-0 vector `uᵢ = ε^(i+1)`, and computes all `uᵢ - 1` and
`uᵢ + α` variants.

The toric resultant producer for `Pert`, an explicit candidate set containing
a generic `ε`, and the characteristic-dependent construction of `α` remain
separate obligations.  In characteristic two the paper requires
`α * (α + 1) = 1`; otherwise it takes `α = 1`.
-/

@[expose] public section

namespace ArkLib.Rojas

open CPoly CPoly.CMvPolynomial
open CompPoly CompPoly.CPolynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]
variable {n : ℕ}

/-- Assign `t` to the univariate indeterminate and the remaining variables to
the supplied Step-0 vector. -/
def perturbationAssignment (u : Fin n → F) : Fin (n + 1) → CPolynomial F :=
  Fin.cases X fun i ↦ C (u i)

/-- Executably specialize `Pert(t,u₁,...,uₙ)` to a univariate polynomial in
`t`. -/
def specializePerturbation (perturbation : CMvPolynomial (n + 1) F)
    (u : Fin n → F) : CPolynomial F :=
  perturbation.eval₂ CHom (perturbationAssignment u)

/-- Bundled evaluation used only to prove the specialization semantics. -/
private def cPolynomialEval₂Hom
    {K : Type*} [Field K] (ι : F →+* K) (θ : K) : CPolynomial F →+* K where
  toFun := fun polynomial ↦ polynomial.eval₂ ι θ
  map_one' := by rw [CPolynomial.eval₂_toPoly, CPolynomial.toPoly_one]; simp
  map_mul' p q := by
    simp only [CPolynomial.eval₂_toPoly, CPolynomial.toPoly_mul,
      Polynomial.eval₂_mul]
  map_zero' := by rw [CPolynomial.eval₂_toPoly, CPolynomial.toPoly_zero]; simp
  map_add' p q := by
    simp only [CPolynomial.eval₂_toPoly, CPolynomial.toPoly_add,
      Polynomial.eval₂_add]

@[simp]
private theorem cPolynomialEval₂Hom_apply
    {K : Type*} [Field K] (ι : F →+* K) (θ : K) (polynomial : CPolynomial F) :
    cPolynomialEval₂Hom ι θ polynomial = polynomial.eval₂ ι θ := rfl

/-- Exact arbitrary-extension semantics of executable specialization. -/
theorem eval₂_specializePerturbation
    {K : Type*} [Field K] (ι : F →+* K) (θ : K)
    (perturbation : CMvPolynomial (n + 1) F) (u : Fin n → F) :
    (specializePerturbation perturbation u).toPoly.eval₂ ι θ =
      perturbation.eval₂ ι (Fin.cases θ fun i ↦ ι (u i)) := by
  rw [← CPolynomial.eval₂_toPoly, specializePerturbation, CPoly.eval₂_equiv,
    CPoly.eval₂_equiv]
  change cPolynomialEval₂Hom ι θ
      (MvPolynomial.eval₂ CHom (perturbationAssignment u)
        (fromCMvPolynomial perturbation)) = _
  rw [MvPolynomial.eval₂_comp_left]
  congr 1
  · ext coefficient
    simp [cPolynomialEval₂Hom, CHom, CPolynomial.eval₂_toPoly,
      CPolynomial.toPoly_C]
  · funext i
    refine Fin.cases ?_ (fun j ↦ ?_) i
    · simp [perturbationAssignment, cPolynomialEval₂Hom,
        CPolynomial.eval₂_toPoly, CPolynomial.X_toPoly]
    · simp [perturbationAssignment, cPolynomialEval₂Hom,
        CPolynomial.eval₂_toPoly, CPolynomial.toPoly_C]

/-- Replace one coordinate of a parameter vector. -/
def setCoordinate (u : Fin n → F) (i : Fin n) (value : F) : Fin n → F :=
  fun j ↦ if j = i then value else u j

/-- The moment-curve Step-0 parameter vector attached to `ε`. -/
def momentCurve (ε : F) : Fin n → F := fun i ↦ ε ^ (i.val + 1)

/-- The characteristic-dependent condition on the Step-3 shift from the
paper.  Construction of a satisfying element is deliberately external. -/
def IsRojasShiftParameter (α : F) : Prop :=
  if ringChar F = 2 then α * (α + 1) = 1 else α = 1

/-- The concrete univariate eliminants computed in Rojas Steps 1--3. -/
structure SpecializationFamily where
  eliminant : CPolynomial F
  minus : Fin n → CPolynomial F
  plus : Fin n → CPolynomial F

/-- Compute the base, `uᵢ - 1`, and `uᵢ + α` specializations. -/
def specializationFamily (perturbation : CMvPolynomial (n + 1) F)
    (u : Fin n → F) (α : F) : SpecializationFamily (F := F) (n := n) :=
  {
    eliminant := specializePerturbation perturbation u
    minus := fun i ↦ specializePerturbation perturbation
      (setCoordinate u i (u i - 1))
    plus := fun i ↦ specializePerturbation perturbation
      (setCoordinate u i (u i + α)) }

/-- Semantics of the Step-1 eliminant. -/
theorem eval₂_specializationFamily_eliminant
    {K : Type*} [Field K] (ι : F →+* K) (θ : K)
    (perturbation : CMvPolynomial (n + 1) F) (u : Fin n → F) (α : F) :
    (specializationFamily perturbation u α).eliminant.toPoly.eval₂ ι θ =
      perturbation.eval₂ ι (Fin.cases θ fun i ↦ ι (u i)) :=
  eval₂_specializePerturbation ι θ perturbation u

/-- Semantics of every Step-2 `uᵢ - 1` eliminant. -/
theorem eval₂_specializationFamily_minus
    {K : Type*} [Field K] (ι : F →+* K) (θ : K)
    (perturbation : CMvPolynomial (n + 1) F) (u : Fin n → F) (α : F)
    (i : Fin n) :
    ((specializationFamily perturbation u α).minus i).toPoly.eval₂ ι θ =
      perturbation.eval₂ ι
        (Fin.cases θ fun j ↦ ι (setCoordinate u i (u i - 1) j)) :=
  eval₂_specializePerturbation ι θ perturbation _

/-- Semantics of every Step-3 `uᵢ + α` eliminant. -/
theorem eval₂_specializationFamily_plus
    {K : Type*} [Field K] (ι : F →+* K) (θ : K)
    (perturbation : CMvPolynomial (n + 1) F) (u : Fin n → F) (α : F)
    (i : Fin n) :
    ((specializationFamily perturbation u α).plus i).toPoly.eval₂ ι θ =
      perturbation.eval₂ ι
        (Fin.cases θ fun j ↦ ι (setCoordinate u i (u i + α) j)) :=
  eval₂_specializePerturbation ι θ perturbation _

/-- Fixed order used by the deterministic guard: all minus shifts, then all
plus shifts. -/
def SpecializationFamily.shiftedEliminants
    (family : SpecializationFamily (F := F) (n := n)) : List (CPolynomial F) :=
  List.ofFn family.minus ++ List.ofFn family.plus

omit [BEq F] [LawfulBEq F] in
@[simp]
theorem SpecializationFamily.length_shiftedEliminants
    (family : SpecializationFamily (F := F) (n := n)) :
    family.shiftedEliminants.length = 2 * n := by
  simp [SpecializationFamily.shiftedEliminants]
  omega

/-- Package an actually computed Step 1--3 family for the genericity guard. -/
def SpecializationFamily.toCandidate (parameter : F)
    (family : SpecializationFamily (F := F) (n := n)) :
    SpecializationCandidate (F := F) :=
  {
    parameter
    eliminant := family.eliminant
    shiftedEliminants := family.shiftedEliminants }

/-- Compute one full candidate directly from a moment-curve parameter `ε`. -/
def candidateFromParameter (perturbation : CMvPolynomial (n + 1) F)
    (α ε : F) : SpecializationCandidate (F := F) :=
  (specializationFamily perturbation (momentCurve ε) α).toCandidate ε

/-- Compute the concrete candidates examined by a deterministic scan. -/
def candidatesFromParameters (perturbation : CMvPolynomial (n + 1) F)
    (α : F) (parameters : List F) : List (SpecializationCandidate (F := F)) :=
  parameters.map (candidateFromParameter perturbation α)

@[simp]
theorem candidateFromParameter_shiftedEliminants_length
    (perturbation : CMvPolynomial (n + 1) F) (α ε : F) :
    (candidateFromParameter perturbation α ε).shiftedEliminants.length = 2 * n :=
  SpecializationFamily.length_shiftedEliminants _

variable (p : ℕ) [Fact p.Prime] [CharP F p] [Fintype F]

/-- Compute Step-0--3 data for every supplied `ε` and scan the resulting
actual eliminant families. -/
def selectParameter? (perturbation : CMvPolynomial (n + 1) F) (α : F)
    (expectedDegree : ℕ) (parameters : List F) :
    Option (SpecializationCandidate (F := F)) :=
  selectSpecialization? p n expectedDegree
    (candidatesFromParameters perturbation α parameters)

omit [Fact (Nat.Prime p)] [CharP F p] in
/-- A successful scan returns a guard-valid family computed from one of the
supplied moment-curve parameters. -/
theorem selectParameter?_sound
    {perturbation : CMvPolynomial (n + 1) F} {α : F}
    {expectedDegree : ℕ} {parameters : List F}
    {selected : SpecializationCandidate (F := F)}
    (hselected :
      selectParameter? p perturbation α expectedDegree parameters = some selected) :
    HasExpectedSupportDegree p n expectedDegree selected ∧
      ∃ ε ∈ parameters, selected = candidateFromParameter perturbation α ε := by
  have hsound := selectSpecialization?_sound p hselected
  refine ⟨hsound.1, ?_⟩
  obtain ⟨ε, hε, heq⟩ := List.mem_map.mp hsound.2
  exact ⟨ε, hε, heq.symm⟩

omit [Fact (Nat.Prime p)] [CharP F p] in
/-- The scan succeeds exactly when the supplied parameter list contains a
moment-curve specialization passing the explicit guard. -/
theorem selectParameter?_exists_iff
    (perturbation : CMvPolynomial (n + 1) F) (α : F)
    (expectedDegree : ℕ) (parameters : List F) :
    (∃ selected,
      selectParameter? p perturbation α expectedDegree parameters = some selected) ↔
      ∃ ε ∈ parameters,
        HasExpectedSupportDegree p n expectedDegree
          (candidateFromParameter perturbation α ε) := by
  rw [selectParameter?, selectSpecialization?_exists_iff]
  constructor
  · rintro ⟨candidate, hcandidate, hvalid⟩
    obtain ⟨ε, hε, rfl⟩ := List.mem_map.mp hcandidate
    exact ⟨ε, hε, hvalid⟩
  · rintro ⟨ε, hε, hvalid⟩
    exact ⟨candidateFromParameter perturbation α ε,
      List.mem_map.mpr ⟨ε, hε, rfl⟩, hvalid⟩

end ArkLib.Rojas
