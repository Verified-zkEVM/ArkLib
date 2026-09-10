/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.UnivariateRepresentation.Basic
public import ArkLib.Data.Polynomial.GCDSplit
public import ArkLib.Data.Polynomial.ModularInverse

/-!
# Postprocessing rational univariate maps

This file is the executable consumer for a rational univariate map supplied by
an isolated-root solver. It filters roots where the denominator vanishes,
sequentially imposes the requested zero equations, inverts the denominator on
the retained squarefree modulus, and reduces every coordinate.

Constructing the input univariate map, including the deterministic Rojas
perturbation/resultant algorithm and its isolated-root coverage proof, remains
outside this module.
-/

@[expose] public section

namespace ArkLib.UnivariateRepresentation

open CompPoly CompPoly.CPolynomial
open ArkLib.PolynomialQuotient

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Reduce all numerator-times-inverse coordinates modulo the retained modulus. -/
def materialize (modulus inverse : CPolynomial F)
    (numerators : List (CPolynomial F)) : Representation (F := F) :=
  {
    modulus
    coordinates := numerators.map fun numerator ↦ reduce modulus (numerator * inverse) }

/-- Retain exactly the roots of `h` where `denominator` does not vanish. -/
def filterNonzero? (h denominator : CPolynomial F) : Option (CPolynomial F) :=
  let retained := gcdComplement h denominator
  if retained == 0 then none else some retained

/-- Sequentially retain the roots satisfying every polynomial equation. -/
def filterZeros? : CPolynomial F → List (CPolynomial F) → Option (CPolynomial F)
  | h, [] => some h
  | h, equation :: equations =>
      let retained := gcdFactor h equation
      if retained == 0 then none else filterZeros? retained equations

/-- Combine the denominator-nonzero filter with all zero-equation filters. -/
def filterDomain? (h denominator : CPolynomial F)
    (zeroEquations : List (CPolynomial F)) : Option (CPolynomial F) := do
  let nonzeroPart ← filterNonzero? h denominator
  filterZeros? nonzeroPart zeroEquations

/-- Apply all domain filters, then invert the denominator and reduce the
coordinate numerators modulo the retained modulus. -/
def postprocess? (input : MapData (F := F)) (zeroEquations : List (CPolynomial F)) :
    Option (Representation (F := F)) := do
  let retained ← filterDomain? input.modulus input.denominator zeroEquations
  let inverse ← inverseMod? input.denominator retained
  return materialize retained inverse input.numerators

theorem filterNonzero?_eq_some_iff {h denominator retained : CPolynomial F} :
    filterNonzero? h denominator = some retained ↔
      gcdComplement h denominator ≠ 0 ∧ retained = gcdComplement h denominator := by
  by_cases hzero : gcdComplement h denominator = 0
  · simp [filterNonzero?, hzero]
  · rw [filterNonzero?, if_neg (by simpa only [beq_iff_eq] using hzero)]
    simp only [Option.some.injEq]
    constructor
    · intro hresult
      exact ⟨hzero, hresult.symm⟩
    · rintro ⟨_, hresult⟩
      exact hresult.symm

theorem filterNonzero?_exists (h denominator : CPolynomial F) (hh : h ≠ 0) :
    ∃ retained, filterNonzero? h denominator = some retained := by
  have hretained : gcdComplement h denominator ≠ 0 := by
    intro hzero
    have hfactor := gcdFactor_mul_gcdComplement (h := h) (e := denominator) hh
    rw [hzero, CPolynomial.mul_zero] at hfactor
    exact hh hfactor.symm
  exact ⟨gcdComplement h denominator,
    filterNonzero?_eq_some_iff.mpr ⟨hretained, rfl⟩⟩

theorem filterNonzero?_ne_zero {h denominator retained : CPolynomial F}
    (hresult : filterNonzero? h denominator = some retained) : retained ≠ 0 := by
  exact ((filterNonzero?_eq_some_iff.mp hresult).2.symm ▸
    (filterNonzero?_eq_some_iff.mp hresult).1)

theorem filterNonzero?_monic {h denominator retained : CPolynomial F}
    (hresult : filterNonzero? h denominator = some retained) (hh : h.monic) :
    retained.monic := by
  obtain ⟨_, rfl⟩ := filterNonzero?_eq_some_iff.mp hresult
  exact gcdComplement_monic hh

theorem filterNonzero?_squarefree {h denominator retained : CPolynomial F}
    (hresult : filterNonzero? h denominator = some retained) (hh : h ≠ 0)
    (hfree : Squarefree h.toPoly) : Squarefree retained.toPoly := by
  obtain ⟨_, rfl⟩ := filterNonzero?_eq_some_iff.mp hresult
  exact gcdComplement_squarefree hh hfree

theorem filterNonzero?_isCoprime {h denominator retained : CPolynomial F}
    (hresult : filterNonzero? h denominator = some retained) (hh : h ≠ 0)
    (hfree : Squarefree h.toPoly) : IsCoprime retained.toPoly denominator.toPoly := by
  obtain ⟨_, rfl⟩ := filterNonzero?_eq_some_iff.mp hresult
  exact gcdComplement_isCoprime_right hh hfree

theorem filterNonzero?_dvd {h denominator retained : CPolynomial F}
    (hresult : filterNonzero? h denominator = some retained) (hh : h ≠ 0) :
    retained.toPoly ∣ h.toPoly := by
  obtain ⟨_, rfl⟩ := filterNonzero?_eq_some_iff.mp hresult
  refine ⟨(gcdFactor h denominator).toPoly, ?_⟩
  have hfactor := congrArg (CPolynomial.toPoly (R := F))
    (gcdFactor_mul_gcdComplement (h := h) (e := denominator) hh)
  rw [toPoly_mul] at hfactor
  simpa only [mul_comm] using hfactor.symm

theorem eval₂_filterNonzero?_eq_zero_iff
    {K : Type*} [Field K] (ι : F →+* K) (θ : K)
    {h denominator retained : CPolynomial F}
    (hresult : filterNonzero? h denominator = some retained) (hh : h ≠ 0)
    (hfree : Squarefree h.toPoly) :
    retained.toPoly.eval₂ ι θ = 0 ↔
      h.toPoly.eval₂ ι θ = 0 ∧ denominator.toPoly.eval₂ ι θ ≠ 0 := by
  obtain ⟨_, rfl⟩ := filterNonzero?_eq_some_iff.mp hresult
  exact eval₂_gcdComplement_eq_zero_iff_left_and_right_ne_zero ι θ hh hfree

theorem filterZeros?_ne_zero {h retained : CPolynomial F}
    {equations : List (CPolynomial F)} (hresult : filterZeros? h equations = some retained)
    (hh : h ≠ 0) : retained ≠ 0 := by
  induction equations generalizing h with
  | nil =>
      simp only [filterZeros?, Option.some.injEq] at hresult
      subst retained
      exact hh
  | cons equation equations ih =>
      by_cases hnext : gcdFactor h equation = 0
      · simp [filterZeros?, hnext] at hresult
      · simp only [filterZeros?, beq_iff_eq, hnext, if_false] at hresult
        exact ih hresult hnext

theorem filterZeros?_exists (h : CPolynomial F) (equations : List (CPolynomial F))
    (hh : h ≠ 0) : ∃ retained, filterZeros? h equations = some retained := by
  induction equations generalizing h with
  | nil => exact ⟨h, rfl⟩
  | cons equation equations ih =>
      have hnext : gcdFactor h equation ≠ 0 :=
        (toPoly_eq_zero_iff _).not.mp
          ((monic_toPoly_iff _).mp (gcdFactor_monic hh)).ne_zero
      obtain ⟨retained, hretained⟩ := ih (gcdFactor h equation) hnext
      refine ⟨retained, ?_⟩
      simp only [filterZeros?, beq_iff_eq, hnext, if_false]
      exact hretained

theorem filterZeros?_monic {h retained : CPolynomial F}
    {equations : List (CPolynomial F)} (hresult : filterZeros? h equations = some retained)
    (hh : h.monic) : retained.monic := by
  induction equations generalizing h with
  | nil =>
      simp only [filterZeros?, Option.some.injEq] at hresult
      subst retained
      exact hh
  | cons equation equations ih =>
      have hhNe : h ≠ 0 :=
        (toPoly_eq_zero_iff h).not.mp ((monic_toPoly_iff h).mp hh).ne_zero
      by_cases hnext : gcdFactor h equation = 0
      · simp [filterZeros?, hnext] at hresult
      · simp only [filterZeros?, beq_iff_eq, hnext, if_false] at hresult
        exact ih hresult (gcdFactor_monic hhNe)

theorem filterZeros?_squarefree {h retained : CPolynomial F}
    {equations : List (CPolynomial F)} (hresult : filterZeros? h equations = some retained)
    (hh : Squarefree h.toPoly) : Squarefree retained.toPoly := by
  induction equations generalizing h with
  | nil =>
      simp only [filterZeros?, Option.some.injEq] at hresult
      subst retained
      exact hh
  | cons equation equations ih =>
      by_cases hnext : gcdFactor h equation = 0
      · simp [filterZeros?, hnext] at hresult
      · simp only [filterZeros?, beq_iff_eq, hnext, if_false] at hresult
        exact ih hresult (gcdFactor_squarefree hh)

theorem filterZeros?_dvd {h retained : CPolynomial F}
    {equations : List (CPolynomial F)} (hresult : filterZeros? h equations = some retained) :
    retained.toPoly ∣ h.toPoly := by
  induction equations generalizing h with
  | nil =>
      simp only [filterZeros?, Option.some.injEq] at hresult
      subst retained
      exact dvd_rfl
  | cons equation equations ih =>
      by_cases hnext : gcdFactor h equation = 0
      · simp [filterZeros?, hnext] at hresult
      · simp only [filterZeros?, beq_iff_eq, hnext, if_false] at hresult
        exact (ih hresult).trans (gcdFactor_dvd_left h equation)

theorem eval₂_filterZeros?_eq_zero_iff
    {K : Type*} [Field K] (ι : F →+* K) (θ : K)
    {h retained : CPolynomial F} {equations : List (CPolynomial F)}
    (hresult : filterZeros? h equations = some retained) (hh : h ≠ 0) :
    retained.toPoly.eval₂ ι θ = 0 ↔
      h.toPoly.eval₂ ι θ = 0 ∧
        ∀ equation ∈ equations, equation.toPoly.eval₂ ι θ = 0 := by
  induction equations generalizing h with
  | nil =>
      simp only [filterZeros?, Option.some.injEq] at hresult
      subst retained
      simp
  | cons equation equations ih =>
      by_cases hnext : gcdFactor h equation = 0
      · simp [filterZeros?, hnext] at hresult
      · simp only [filterZeros?, beq_iff_eq, hnext, if_false] at hresult
        rw [ih hresult hnext]
        rw [eval₂_gcdFactor_eq_zero_iff_left_right ι θ]
        simp only [List.forall_mem_cons]
        tauto

theorem filterDomain?_eq_some_iff {h denominator retained : CPolynomial F}
    {zeroEquations : List (CPolynomial F)} :
    filterDomain? h denominator zeroEquations = some retained ↔
      ∃ nonzeroPart, filterNonzero? h denominator = some nonzeroPart ∧
        filterZeros? nonzeroPart zeroEquations = some retained := by
  unfold filterDomain?
  cases hnonzero : filterNonzero? h denominator <;> simp_all

theorem filterDomain?_exists (h denominator : CPolynomial F)
    (zeroEquations : List (CPolynomial F)) (hh : h ≠ 0) :
    ∃ retained, filterDomain? h denominator zeroEquations = some retained := by
  obtain ⟨nonzeroPart, hnonzero⟩ := filterNonzero?_exists h denominator hh
  obtain ⟨retained, hretained⟩ := filterZeros?_exists nonzeroPart zeroEquations
    (filterNonzero?_ne_zero hnonzero)
  exact ⟨retained, filterDomain?_eq_some_iff.mpr
    ⟨nonzeroPart, hnonzero, hretained⟩⟩

theorem filterDomain?_ne_zero {h denominator retained : CPolynomial F}
    {zeroEquations : List (CPolynomial F)}
    (hresult : filterDomain? h denominator zeroEquations = some retained) : retained ≠ 0 := by
  rw [filterDomain?_eq_some_iff] at hresult
  obtain ⟨nonzeroPart, hnonzero, hzeros⟩ := hresult
  exact filterZeros?_ne_zero hzeros (filterNonzero?_ne_zero hnonzero)

theorem filterDomain?_monic {h denominator retained : CPolynomial F}
    {zeroEquations : List (CPolynomial F)}
    (hresult : filterDomain? h denominator zeroEquations = some retained)
    (hh : h.monic) : retained.monic := by
  rw [filterDomain?_eq_some_iff] at hresult
  obtain ⟨nonzeroPart, hnonzero, hzeros⟩ := hresult
  exact filterZeros?_monic hzeros (filterNonzero?_monic hnonzero hh)

theorem filterDomain?_squarefree {h denominator retained : CPolynomial F}
    {zeroEquations : List (CPolynomial F)}
    (hresult : filterDomain? h denominator zeroEquations = some retained)
    (hh : h ≠ 0) (hfree : Squarefree h.toPoly) : Squarefree retained.toPoly := by
  rw [filterDomain?_eq_some_iff] at hresult
  obtain ⟨nonzeroPart, hnonzero, hzeros⟩ := hresult
  exact filterZeros?_squarefree hzeros (filterNonzero?_squarefree hnonzero hh hfree)

theorem filterDomain?_isCoprime {h denominator retained : CPolynomial F}
    {zeroEquations : List (CPolynomial F)}
    (hresult : filterDomain? h denominator zeroEquations = some retained)
    (hh : h ≠ 0) (hfree : Squarefree h.toPoly) :
    IsCoprime retained.toPoly denominator.toPoly := by
  rw [filterDomain?_eq_some_iff] at hresult
  obtain ⟨nonzeroPart, hnonzero, hzeros⟩ := hresult
  exact (filterNonzero?_isCoprime hnonzero hh hfree).mono
    (filterZeros?_dvd hzeros) dvd_rfl

theorem filterDomain?_dvd {h denominator retained : CPolynomial F}
    {zeroEquations : List (CPolynomial F)}
    (hresult : filterDomain? h denominator zeroEquations = some retained)
    (hh : h ≠ 0) : retained.toPoly ∣ h.toPoly := by
  rw [filterDomain?_eq_some_iff] at hresult
  obtain ⟨nonzeroPart, hnonzero, hzeros⟩ := hresult
  exact (filterZeros?_dvd hzeros).trans (filterNonzero?_dvd hnonzero hh)

theorem eval₂_filterDomain?_eq_zero_iff
    {K : Type*} [Field K] (ι : F →+* K) (θ : K)
    {h denominator retained : CPolynomial F} {zeroEquations : List (CPolynomial F)}
    (hresult : filterDomain? h denominator zeroEquations = some retained)
    (hh : h ≠ 0) (hfree : Squarefree h.toPoly) :
    retained.toPoly.eval₂ ι θ = 0 ↔
      h.toPoly.eval₂ ι θ = 0 ∧ denominator.toPoly.eval₂ ι θ ≠ 0 ∧
        ∀ equation ∈ zeroEquations, equation.toPoly.eval₂ ι θ = 0 := by
  rw [filterDomain?_eq_some_iff] at hresult
  obtain ⟨nonzeroPart, hnonzero, hzeros⟩ := hresult
  rw [eval₂_filterZeros?_eq_zero_iff ι θ hzeros
    (filterNonzero?_ne_zero hnonzero)]
  rw [eval₂_filterNonzero?_eq_zero_iff ι θ hnonzero hh hfree]
  tauto

theorem eval₂_reduce_eq_of_root
    {K : Type*} [Field K] (ι : F →+* K) (θ : K)
    {modulus : CPolynomial F} (hmonic : modulus.monic)
    (hroot : modulus.toPoly.eval₂ ι θ = 0) (p : CPolynomial F) :
    (reduce modulus p).toPoly.eval₂ ι θ = p.toPoly.eval₂ ι θ := by
  have hdivision := modByMonic_add_mul_divByMonic p modulus hmonic
  have heval := congrArg (fun q : CPolynomial F ↦ q.toPoly.eval₂ ι θ) hdivision
  simpa [reduce, toPoly_add, toPoly_mul, hroot] using heval

/-- Pointwise interpretation of a list of rational coordinates. -/
def CoordinatesSpecializeAt
    {K : Type*} [Field K] (ι : F →+* K) (θ : K) (denominator : CPolynomial F) :
    List (CPolynomial F) → List (CPolynomial F) → Prop :=
  List.Forall₂ fun numerator coordinate ↦
    coordinate.toPoly.eval₂ ι θ =
      numerator.toPoly.eval₂ ι θ / denominator.toPoly.eval₂ ι θ

/-- Complete proof-facing contract of a successful postprocessing result. -/
structure CorrectOutput (input : MapData (F := F))
    (zeroEquations : List (CPolynomial F)) (output : Representation (F := F)) : Prop where
  modulus_ne_zero : output.modulus ≠ 0
  modulus_monic : output.modulus.monic
  modulus_squarefree : Squarefree output.modulus.toPoly
  modulus_natDegree_le : output.modulus.natDegree ≤ input.modulus.natDegree
  coordinate_degree_lt : ∀ coordinate ∈ output.coordinates,
    coordinate.toPoly.degree < output.modulus.toPoly.degree
  roots : ∀ {K : Type*} [Field K] (ι : F →+* K) (θ : K),
    output.modulus.toPoly.eval₂ ι θ = 0 ↔
      input.modulus.toPoly.eval₂ ι θ = 0 ∧
        input.denominator.toPoly.eval₂ ι θ ≠ 0 ∧
        ∀ equation ∈ zeroEquations, equation.toPoly.eval₂ ι θ = 0
  coordinates : ∀ {K : Type*} [Field K] (ι : F →+* K) (θ : K),
    output.modulus.toPoly.eval₂ ι θ = 0 →
      CoordinatesSpecializeAt ι θ input.denominator input.numerators output.coordinates

theorem materialize_coordinates_specialize
    {K : Type*} [Field K] (ι : F →+* K) (θ : K)
    {modulus denominator inverse : CPolynomial F} (hmonic : modulus.monic)
    (hroot : modulus.toPoly.eval₂ ι θ = 0)
    (hinverse : inverseMod? denominator modulus = some inverse)
    (numerators : List (CPolynomial F)) :
    CoordinatesSpecializeAt ι θ denominator numerators
      (materialize modulus inverse numerators).coordinates := by
  have hinverseEval := eval₂_mul_inverseMod_eq_one ι θ hroot hinverse
  have hinverseValue : inverse.toPoly.eval₂ ι θ =
      (denominator.toPoly.eval₂ ι θ)⁻¹ :=
    eq_inv_of_mul_eq_one_right hinverseEval
  induction numerators with
  | nil => exact .nil
  | cons numerator numerators ih =>
      apply List.Forall₂.cons
      · rw [eval₂_reduce_eq_of_root ι θ hmonic hroot]
        simp only [toPoly_mul, Polynomial.eval₂_mul, div_eq_mul_inv, hinverseValue]
      · exact ih

theorem materialize_coordinate_degree_lt {modulus inverse : CPolynomial F}
    (hmonic : modulus.monic) (numerators : List (CPolynomial F)) :
    ∀ coordinate ∈ (materialize modulus inverse numerators).coordinates,
      coordinate.toPoly.degree < modulus.toPoly.degree := by
  intro coordinate hcoordinate
  simp only [materialize, List.mem_map] at hcoordinate
  obtain ⟨numerator, _, rfl⟩ := hcoordinate
  exact degree_reduce_lt hmonic _

theorem postprocess?_eq_some_iff
    {input : MapData (F := F)} {zeroEquations : List (CPolynomial F)}
    {output : Representation (F := F)} :
    postprocess? input zeroEquations = some output ↔
      ∃ retained inverse,
        filterDomain? input.modulus input.denominator zeroEquations = some retained ∧
        inverseMod? input.denominator retained = some inverse ∧
        output = materialize retained inverse input.numerators := by
  unfold postprocess?
  change (filterDomain? input.modulus input.denominator zeroEquations).bind
      (fun retained ↦ (inverseMod? input.denominator retained).bind
        fun inverse ↦ some (materialize retained inverse input.numerators)) = some output ↔ _
  simp only [Option.bind_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨retained, hdomain, inverse, hinverse, houtput⟩
    exact ⟨retained, inverse, hdomain, hinverse, houtput.symm⟩
  · rintro ⟨retained, inverse, hdomain, hinverse, rfl⟩
    exact ⟨retained, hdomain, inverse, hinverse, rfl⟩

/-- Once domain filtering retains a factor, denominator inversion cannot fail. -/
theorem postprocess?_exists_of_filterDomain
    {input : MapData (F := F)} {zeroEquations : List (CPolynomial F)}
    {retained : CPolynomial F}
    (hdomain : filterDomain? input.modulus input.denominator zeroEquations = some retained)
    (hmodulus : input.modulus ≠ 0) (hfree : Squarefree input.modulus.toPoly) :
    ∃ output, postprocess? input zeroEquations = some output := by
  obtain ⟨inverse, hinverse⟩ :=
    (inverseMod_exists_iff_coprime input.denominator retained).mpr
      (filterDomain?_isCoprime hdomain hmodulus hfree).symm
  refine ⟨materialize retained inverse input.numerators, ?_⟩
  apply postprocess?_eq_some_iff.mpr
  exact ⟨retained, inverse, hdomain, hinverse, rfl⟩

theorem postprocess?_modulus_ne_zero
    {input : MapData (F := F)} {zeroEquations : List (CPolynomial F)}
    {output : Representation (F := F)}
    (hresult : postprocess? input zeroEquations = some output) : output.modulus ≠ 0 := by
  obtain ⟨retained, inverse, hdomain, _, rfl⟩ := postprocess?_eq_some_iff.mp hresult
  exact filterDomain?_ne_zero hdomain

theorem postprocess?_modulus_monic
    {input : MapData (F := F)} {zeroEquations : List (CPolynomial F)}
    {output : Representation (F := F)}
    (hresult : postprocess? input zeroEquations = some output)
    (hmonic : input.modulus.monic) : output.modulus.monic := by
  obtain ⟨retained, inverse, hdomain, _, rfl⟩ := postprocess?_eq_some_iff.mp hresult
  exact filterDomain?_monic hdomain hmonic

theorem postprocess?_modulus_squarefree
    {input : MapData (F := F)} {zeroEquations : List (CPolynomial F)}
    {output : Representation (F := F)}
    (hresult : postprocess? input zeroEquations = some output)
    (hmodulus : input.modulus ≠ 0) (hfree : Squarefree input.modulus.toPoly) :
    Squarefree output.modulus.toPoly := by
  obtain ⟨retained, inverse, hdomain, _, rfl⟩ := postprocess?_eq_some_iff.mp hresult
  exact filterDomain?_squarefree hdomain hmodulus hfree

theorem postprocess?_modulus_dvd
    {input : MapData (F := F)} {zeroEquations : List (CPolynomial F)}
    {output : Representation (F := F)}
    (hresult : postprocess? input zeroEquations = some output)
    (hmodulus : input.modulus ≠ 0) : output.modulus.toPoly ∣ input.modulus.toPoly := by
  obtain ⟨retained, inverse, hdomain, _, rfl⟩ := postprocess?_eq_some_iff.mp hresult
  exact filterDomain?_dvd hdomain hmodulus

theorem postprocess?_modulus_natDegree_le
    {input : MapData (F := F)} {zeroEquations : List (CPolynomial F)}
    {output : Representation (F := F)}
    (hresult : postprocess? input zeroEquations = some output)
    (hmodulus : input.modulus ≠ 0) : output.modulus.natDegree ≤ input.modulus.natDegree := by
  have hdegree := Polynomial.natDegree_le_of_dvd
    (postprocess?_modulus_dvd hresult hmodulus)
    ((toPoly_eq_zero_iff input.modulus).not.mpr hmodulus)
  simpa only [← natDegree_toPoly] using hdegree

theorem eval₂_postprocess?_modulus_eq_zero_iff
    {K : Type*} [Field K] (ι : F →+* K) (θ : K)
    {input : MapData (F := F)} {zeroEquations : List (CPolynomial F)}
    {output : Representation (F := F)}
    (hresult : postprocess? input zeroEquations = some output)
    (hmodulus : input.modulus ≠ 0) (hfree : Squarefree input.modulus.toPoly) :
    output.modulus.toPoly.eval₂ ι θ = 0 ↔
      input.modulus.toPoly.eval₂ ι θ = 0 ∧
        input.denominator.toPoly.eval₂ ι θ ≠ 0 ∧
        ∀ equation ∈ zeroEquations, equation.toPoly.eval₂ ι θ = 0 := by
  obtain ⟨retained, inverse, hdomain, _, rfl⟩ := postprocess?_eq_some_iff.mp hresult
  exact eval₂_filterDomain?_eq_zero_iff ι θ hdomain hmodulus hfree

theorem postprocess?_coordinate_degree_lt
    {input : MapData (F := F)} {zeroEquations : List (CPolynomial F)}
    {output : Representation (F := F)}
    (hresult : postprocess? input zeroEquations = some output)
    (hmonic : input.modulus.monic) :
    ∀ coordinate ∈ output.coordinates,
      coordinate.toPoly.degree < output.modulus.toPoly.degree := by
  obtain ⟨retained, inverse, hdomain, _, rfl⟩ := postprocess?_eq_some_iff.mp hresult
  exact materialize_coordinate_degree_lt (filterDomain?_monic hdomain hmonic) _

theorem postprocess?_coordinates_specialize
    {K : Type*} [Field K] (ι : F →+* K) (θ : K)
    {input : MapData (F := F)} {zeroEquations : List (CPolynomial F)}
    {output : Representation (F := F)}
    (hresult : postprocess? input zeroEquations = some output)
    (hmonic : input.modulus.monic) (hroot : output.modulus.toPoly.eval₂ ι θ = 0) :
    CoordinatesSpecializeAt ι θ input.denominator input.numerators output.coordinates := by
  obtain ⟨retained, inverse, hdomain, hinverse, rfl⟩ := postprocess?_eq_some_iff.mp hresult
  exact materialize_coordinates_specialize ι θ
    (filterDomain?_monic hdomain hmonic) hroot hinverse input.numerators

theorem postprocess?_correct
    {input : MapData (F := F)} {zeroEquations : List (CPolynomial F)}
    {output : Representation (F := F)}
    (hresult : postprocess? input zeroEquations = some output)
    (hmonic : input.modulus.monic) (hfree : Squarefree input.modulus.toPoly) :
    CorrectOutput input zeroEquations output := by
  have hmodulus : input.modulus ≠ 0 :=
    (toPoly_eq_zero_iff input.modulus).not.mp
      ((monic_toPoly_iff input.modulus).mp hmonic).ne_zero
  refine {
    modulus_ne_zero := postprocess?_modulus_ne_zero hresult
    modulus_monic := postprocess?_modulus_monic hresult hmonic
    modulus_squarefree := postprocess?_modulus_squarefree hresult hmodulus hfree
    modulus_natDegree_le := postprocess?_modulus_natDegree_le hresult hmodulus
    coordinate_degree_lt := postprocess?_coordinate_degree_lt hresult hmonic
    roots := fun ι θ ↦
      eval₂_postprocess?_modulus_eq_zero_iff ι θ hresult hmodulus hfree
    coordinates := fun ι θ hroot ↦
      postprocess?_coordinates_specialize ι θ hresult hmonic hroot }

/-- A monic squarefree input always produces a fully certified result; no filter-success
or inverse-success premise is exposed to the caller. -/
theorem postprocess?_exists_correct
    (input : MapData (F := F)) (zeroEquations : List (CPolynomial F))
    (hmonic : input.modulus.monic) (hfree : Squarefree input.modulus.toPoly) :
    ∃ output, postprocess? input zeroEquations = some output ∧
      CorrectOutput input zeroEquations output := by
  have hmodulus : input.modulus ≠ 0 :=
    (toPoly_eq_zero_iff input.modulus).not.mp
      ((monic_toPoly_iff input.modulus).mp hmonic).ne_zero
  obtain ⟨retained, hdomain⟩ := filterDomain?_exists
    input.modulus input.denominator zeroEquations hmodulus
  obtain ⟨output, houtput⟩ :=
    postprocess?_exists_of_filterDomain hdomain hmodulus hfree
  exact ⟨output, houtput, postprocess?_correct houtput hmonic hfree⟩

end ArkLib.UnivariateRepresentation
