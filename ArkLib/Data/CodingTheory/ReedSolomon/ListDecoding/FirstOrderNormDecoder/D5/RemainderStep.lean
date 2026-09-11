/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5.LeadingCoefficient
-- The coefficient theorem for ArkLib's `ofFn` adapter unfolds its exposed implementation.
import all ArkLib.ToCompPoly.Univariate.Basic

/-!
# One dynamic-evaluation remainder step

This file represents a bounded-fiber polynomial by its coefficient list in descending fiber
degree.  On each base branch produced by `splitLeading`, the retained leading coefficient has a
computed inverse.  Multiplying all retained coefficients by that inverse and reducing modulo the
branch modulus gives an executable monic divisor, so `CPolynomial.modByMonic` computes one
Euclidean remainder.

The specifications below compare this computation with ordinary polynomial remainder after every
coefficient-field extension and every geometric root of the branch modulus.  The zero-polynomial
branches produced by leading-coefficient descent remain explicit and perform no division.  This
is one Euclidean step, not the complete D5 gcd recursion or tower materialization.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5

open CompPoly Polynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

local instance : DecidableEq F := instDecidableEqOfLawfulBEq
local instance : DecidableEq (CPolynomial F) := instDecidableEqOfLawfulBEq

/-- Executable bounded-fiber polynomial, with coefficients ordered from highest to lowest degree. -/
structure FiberPolynomial where
  coefficients : List (CPolynomial F)

/-- Convert descending coefficients to an executable `CPolynomial` over coefficient
representatives. -/
def ofDescending : List (CPolynomial F) → CPolynomial (CPolynomial F)
  | [] => 0
  | coefficient :: coefficients =>
      CPolynomial.monomial coefficients.length coefficient + ofDescending coefficients

/-- The nested computable polynomial represented by a bounded-fiber coefficient list. -/
def FiberPolynomial.toCPolynomial (p : FiberPolynomial (F := F)) :
    CPolynomial (CPolynomial F) :=
  ofDescending p.coefficients

/-- Evaluate a coefficient representative at one geometric base point. -/
noncomputable def coefficientEval
    {K : Type*} [Field K] (phi : F →+* K) (x : K) : CPolynomial F →+* K :=
  (Polynomial.eval₂RingHom phi x).comp CPolynomial.toPolyRingHom

@[simp] theorem coefficientEval_apply
    {K : Type*} [Field K] (phi : F →+* K) (x : K) (coefficient : CPolynomial F) :
    coefficientEval phi x coefficient = coefficient.toPoly.eval₂ phi x := by
  simp [coefficientEval, CPolynomial.toPolyRingHom_apply]

/-- Proof-facing specialization of a nested computable fiber polynomial. -/
noncomputable def specializeFiberCPolynomial
    {K : Type*} [Field K] (p : CPolynomial (CPolynomial F))
    (phi : F →+* K) (x : K) : K[X] :=
  p.toPoly.map (coefficientEval phi x)

/-- Specialize all coefficients of a bounded-fiber polynomial at one geometric base point. -/
noncomputable def FiberPolynomial.specialize
    {K : Type*} [Field K] (p : FiberPolynomial (F := F))
    (phi : F →+* K) (x : K) : K[X] :=
  specializeFiberCPolynomial p.toCPolynomial phi x

/-- Coefficientwise canonical reduction modulo a monic base polynomial. -/
def reduceFiberCoefficients (g : CPolynomial F) (p : CPolynomial (CPolynomial F)) :
    CPolynomial (CPolynomial F) :=
  CPolynomial.ofFn fun i : Fin (p.natDegree + 1) =>
    (p.coeff i).modByMonic g

/-- Normalize a nonzero descending coefficient list by a supplied quotient inverse. -/
def normalizedDivisor (g inverse : CPolynomial F)
    (coefficients : List (CPolynomial F)) : CPolynomial (CPolynomial F) :=
  match coefficients with
  | [] => 0
  | _ :: lower =>
      CPolynomial.X ^ lower.length +
        ofDescending (lower.map fun coefficient =>
          (coefficient * inverse).modByMonic g)

/-- One branch of a normalized Euclidean remainder step.  `none` records the zero-divisor
polynomial branch; `some r` records the computed remainder on a unit-leading branch. -/
structure RemainderBranch where
  leading : LeadingBranch (F := F)
  remainder : Option (CPolynomial (CPolynomial F))

/-- Compute the remainder payload for one regularized leading-coefficient branch. -/
def makeRemainderBranch (dividend : FiberPolynomial (F := F))
    (branch : LeadingBranch (F := F)) : RemainderBranch (F := F) :=
  match branch.coefficients, branch.leadingInverse with
  | [], none => ⟨branch, none⟩
  | _ :: _, some inverse =>
      let monicDivisor := normalizedDivisor branch.modulus inverse branch.coefficients
      let rawRemainder := dividend.toCPolynomial.modByMonic monicDivisor
      ⟨branch, some (reduceFiberCoefficients branch.modulus rawRemainder)⟩
  | _, _ => ⟨branch, none⟩

@[simp] theorem makeRemainderBranch_leading (dividend : FiberPolynomial (F := F))
    (branch : LeadingBranch (F := F)) :
    (makeRemainderBranch dividend branch).leading = branch := by
  cases hcoefficients : branch.coefficients <;>
    cases hinverse : branch.leadingInverse <;>
    simp [makeRemainderBranch, hcoefficients, hinverse]

/-- Compute one normalized remainder on every base branch. -/
def remainderStep (g : CPolynomial F) (dividend divisor : FiberPolynomial (F := F)) :
    List (RemainderBranch (F := F)) :=
  (splitLeading divisor.coefficients g).map (makeRemainderBranch dividend)

/-- `ofDescending` has fiber degree strictly below the physical coefficient width. -/
theorem degree_ofDescending_lt (coefficients : List (CPolynomial F)) :
    (ofDescending coefficients).toPoly.degree < coefficients.length := by
  induction coefficients with
  | nil => simp [ofDescending, CPolynomial.toPoly_zero]
  | cons coefficient coefficients ih =>
      rw [ofDescending, CPolynomial.toPoly_add, CPolynomial.toPoly_monomial]
      apply lt_of_le_of_lt (Polynomial.degree_add_le _ _)
      rw [max_lt_iff]
      exact ⟨(Polynomial.degree_monomial_le _ _).trans_lt
          (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self coefficients.length)),
        ih.trans (WithBot.coe_lt_coe.mpr (Nat.lt_succ_self coefficients.length))⟩

/-- Every nonempty normalized divisor is monic, independently of its lower coefficients. -/
theorem normalizedDivisor_monic (g inverse leading : CPolynomial F)
    (lower : List (CPolynomial F)) :
    (normalizedDivisor g inverse (leading :: lower)).toPoly.Monic := by
  rw [normalizedDivisor, CPolynomial.toPoly_add, CPolynomial.toPoly_pow,
    CPolynomial.X_toPoly]
  apply Polynomial.monic_X_pow_add
  simpa only [List.length_map] using
    degree_ofDescending_lt (lower.map fun coefficient =>
      (coefficient * inverse).modByMonic g)

@[simp] theorem specialize_ofDescending_nil
    {K : Type*} [Field K] (phi : F →+* K) (x : K) :
    specializeFiberCPolynomial (ofDescending []) phi x = 0 := by
  simp [specializeFiberCPolynomial, ofDescending, CPolynomial.toPoly_zero]

theorem specialize_ofDescending_cons
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (coefficient : CPolynomial F) (coefficients : List (CPolynomial F)) :
    specializeFiberCPolynomial (ofDescending (coefficient :: coefficients)) phi x =
      Polynomial.monomial coefficients.length (coefficient.toPoly.eval₂ phi x) +
        specializeFiberCPolynomial (ofDescending coefficients) phi x := by
  simp [specializeFiberCPolynomial, ofDescending, CPolynomial.toPoly_add,
    CPolynomial.toPoly_monomial, coefficientEval_apply]

/-- Specialization cannot exceed the physical width of a descending coefficient list. -/
theorem degree_specialize_ofDescending_lt
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (coefficients : List (CPolynomial F)) :
    (specializeFiberCPolynomial (ofDescending coefficients) phi x).degree <
      coefficients.length :=
  (Polynomial.degree_map_le).trans_lt (degree_ofDescending_lt coefficients)

/-- A nonvanishing head coefficient is the leading coefficient after specialization. -/
theorem leadingCoeff_specialize_ofDescending_cons
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (leading : CPolynomial F) (lower : List (CPolynomial F))
    (hleading : leading.toPoly.eval₂ phi x ≠ 0) :
    (specializeFiberCPolynomial (ofDescending (leading :: lower)) phi x).leadingCoeff =
      leading.toPoly.eval₂ phi x := by
  rw [specialize_ofDescending_cons,
    Polynomial.leadingCoeff_add_of_degree_lt'
      ((degree_specialize_ofDescending_lt phi x lower).trans_le
        (le_of_eq (Polynomial.degree_monomial lower.length hleading).symm)),
    Polynomial.leadingCoeff_monomial]

/-- Deleting a leading prefix that vanishes at a geometric base point preserves the specialized
fiber polynomial. -/
theorem specialize_ofDescending_eq_of_prefix_zero
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (dropped retained : List (CPolynomial F))
    (hdropped : ∀ coefficient ∈ dropped, coefficient.toPoly.eval₂ phi x = 0) :
    specializeFiberCPolynomial (ofDescending (dropped ++ retained)) phi x =
      specializeFiberCPolynomial (ofDescending retained) phi x := by
  induction dropped with
  | nil => rfl
  | cons coefficient dropped ih =>
      rw [List.cons_append, specialize_ofDescending_cons,
        hdropped coefficient (by simp), Polynomial.monomial_zero_right, zero_add]
      exact ih (fun next hnext => hdropped next (List.mem_cons_of_mem _ hnext))

/-- Coefficient reduction modulo a rooted monic base modulus does not change specialization. -/
theorem coefficientEval_modByMonic_eq
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    {g : CPolynomial F} (hgmonic : g.monic)
    (hroot : g.toPoly.eval₂ phi x = 0) (coefficient : CPolynomial F) :
    coefficientEval phi x (coefficient.modByMonic g) = coefficientEval phi x coefficient := by
  rw [coefficientEval_apply, coefficientEval_apply,
    CPolynomial.modByMonic_toPoly_eq_modByMonic coefficient g hgmonic]
  exact Polynomial.eval₂_modByMonic_eq_self_of_root hroot

@[simp] theorem coeff_reduceFiberCoefficients (g : CPolynomial F)
    (p : CPolynomial (CPolynomial F)) (i : ℕ) :
    (reduceFiberCoefficients g p).coeff i =
      if _ : i < p.natDegree + 1 then (p.coeff i).modByMonic g else 0 := by
  rw [reduceFiberCoefficients]
  change (CPolynomial.Raw.mk (Array.ofFn fun j : Fin (p.natDegree + 1) =>
    (p.coeff j).modByMonic g)).trim.coeff i = _
  rw [CPolynomial.Raw.Trim.coeff_eq_coeff]
  by_cases _hi : i < p.natDegree + 1
  · simp [CPolynomial.Raw.coeff, _hi]
  · simp [CPolynomial.Raw.coeff, _hi]

/-- Coefficientwise reduction preserves a nested polynomial at every root of the base modulus. -/
theorem specialize_reduceFiberCoefficients
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    {g : CPolynomial F} (hgmonic : g.monic)
    (hroot : g.toPoly.eval₂ phi x = 0) (p : CPolynomial (CPolynomial F)) :
    specializeFiberCPolynomial (reduceFiberCoefficients g p) phi x =
      specializeFiberCPolynomial p phi x := by
  ext i
  rw [specializeFiberCPolynomial, specializeFiberCPolynomial,
    Polynomial.coeff_map, Polynomial.coeff_map,
    ← CPolynomial.coeff_toPoly, ← CPolynomial.coeff_toPoly]
  rw [coeff_reduceFiberCoefficients]
  split_ifs with hi
  · exact coefficientEval_modByMonic_eq phi x hgmonic hroot _
  · have hpcoeff : p.coeff i = 0 := by
      by_contra hcoeff
      have hle := CPolynomial.le_natDegree_of_ne_zero hcoeff
      omega
    rw [hpcoeff, map_zero]

/-- Every coefficient emitted by canonical base reduction has degree strictly below the monic
base modulus.  This is the bounded-representative invariant consumed by later D5 recursion. -/
theorem degree_coeff_reduceFiberCoefficients_lt
    {g : CPolynomial F} (hgmonic : g.monic)
    (p : CPolynomial (CPolynomial F)) (i : ℕ) :
    ((reduceFiberCoefficients g p).coeff i).toPoly.degree < g.toPoly.degree := by
  rw [coeff_reduceFiberCoefficients]
  split_ifs
  · rw [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hgmonic]
    exact Polynomial.degree_modByMonic_lt _ ((CPolynomial.monic_toPoly_iff g).mp hgmonic)
  · rw [CPolynomial.toPoly_zero]
    exact WithBot.bot_lt_iff_ne_bot.mpr
      (Polynomial.degree_ne_bot.mpr
        ((CPolynomial.monic_toPoly_iff g).mp hgmonic).ne_zero)

/-- Multiplying descending coefficients by a representative and reducing modulo a rooted base
modulus specializes to scalar multiplication by that representative. -/
theorem specialize_ofDescending_map_mul_modByMonic
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    {g : CPolynomial F} (hgmonic : g.monic)
    (hroot : g.toPoly.eval₂ phi x = 0) (coefficients : List (CPolynomial F))
    (inverse : CPolynomial F) :
    specializeFiberCPolynomial
        (ofDescending (coefficients.map fun coefficient =>
          (coefficient * inverse).modByMonic g)) phi x =
      specializeFiberCPolynomial (ofDescending coefficients) phi x *
        Polynomial.C (inverse.toPoly.eval₂ phi x) := by
  induction coefficients with
  | nil => simp [specialize_ofDescending_nil]
  | cons coefficient coefficients ih =>
      have hcoefficient :
          ((coefficient * inverse).modByMonic g).toPoly.eval₂ phi x =
            (coefficient * inverse).toPoly.eval₂ phi x := by
        simpa only [coefficientEval_apply] using
          coefficientEval_modByMonic_eq phi x hgmonic hroot (coefficient * inverse)
      rw [List.map_cons, specialize_ofDescending_cons, specialize_ofDescending_cons,
        hcoefficient]
      simp only [CPolynomial.toPoly_mul, Polynomial.eval₂_mul, ih,
        List.length_map, add_mul, Polynomial.monomial_mul_C]

/-- On a rooted unit-leading branch, the executable normalized divisor specializes to the
ordinary divisor multiplied by the inverse of its leading coefficient. -/
theorem specialize_normalizedDivisor
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    {g : CPolynomial F} (hgmonic : g.monic)
    (hroot : g.toPoly.eval₂ phi x = 0)
    (leading inverse : CPolynomial F) (lower : List (CPolynomial F))
    (hinverse : leading.toPoly.eval₂ phi x * inverse.toPoly.eval₂ phi x = 1) :
    specializeFiberCPolynomial (normalizedDivisor g inverse (leading :: lower)) phi x =
      specializeFiberCPolynomial (ofDescending (leading :: lower)) phi x *
        Polynomial.C (inverse.toPoly.eval₂ phi x) := by
  rw [normalizedDivisor, specializeFiberCPolynomial, CPolynomial.toPoly_add,
    CPolynomial.toPoly_pow, CPolynomial.X_toPoly, Polynomial.map_add, Polynomial.map_pow,
    Polynomial.map_X]
  change X ^ lower.length +
      specializeFiberCPolynomial
        (ofDescending (lower.map fun coefficient =>
          (coefficient * inverse).modByMonic g)) phi x = _
  rw [specialize_ofDescending_map_mul_modByMonic phi x hgmonic hroot,
    specialize_ofDescending_cons, add_mul]
  simp [Polynomial.X_pow_eq_monomial, hinverse]

/-- A followed leading branch represents exactly the original specialized divisor after the
vanishing leading prefix is deleted. -/
theorem specialize_ofDescending_eq_of_follows
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    {input : List (CPolynomial F)} {branch : LeadingBranch (F := F)}
    (hfollows : branch.Follows input phi x) :
    specializeFiberCPolynomial (ofDescending input) phi x =
      specializeFiberCPolynomial (ofDescending branch.coefficients) phi x := by
  obtain ⟨dropped, rfl, hdropped, _⟩ := hfollows
  exact specialize_ofDescending_eq_of_prefix_zero phi x dropped branch.coefficients hdropped

/-- A unit branch of the executable step is present with its normalized remainder payload. -/
theorem unitBranch_mem_remainderStep (g : CPolynomial F)
    (dividend divisor : FiberPolynomial (F := F))
    (modulus leading inverse : CPolynomial F) (lower : List (CPolynomial F))
    (hbranch : (⟨modulus, leading :: lower, some inverse⟩ : LeadingBranch (F := F)) ∈
      splitLeading divisor.coefficients g) :
    (⟨⟨modulus, leading :: lower, some inverse⟩,
      some (reduceFiberCoefficients modulus
        (dividend.toCPolynomial.modByMonic
          (normalizedDivisor modulus inverse (leading :: lower))))⟩ :
        RemainderBranch (F := F)) ∈ remainderStep g dividend divisor := by
  simpa [remainderStep, makeRemainderBranch] using
    List.mem_map_of_mem hbranch

/-- On every rooted unit-leading branch, the executable nested remainder specializes to the
ordinary field-polynomial remainder by the original divisor. -/
theorem specialize_unitBranch_remainder_eq_mod
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    {g : CPolynomial F} (hg : g ≠ 0) (hgmonic : g.monic)
    (hgfree : Squarefree g.toPoly)
    (dividend divisor : FiberPolynomial (F := F))
    (modulus leading inverse : CPolynomial F) (lower : List (CPolynomial F))
    (hbranch : (⟨modulus, leading :: lower, some inverse⟩ : LeadingBranch (F := F)) ∈
      splitLeading divisor.coefficients g)
    (hroot : modulus.toPoly.eval₂ phi x = 0) :
    specializeFiberCPolynomial
        (reduceFiberCoefficients modulus
          (dividend.toCPolynomial.modByMonic
            (normalizedDivisor modulus inverse (leading :: lower)))) phi x =
      dividend.specialize phi x % divisor.specialize phi x := by
  let branch : LeadingBranch (F := F) :=
    ⟨modulus, leading :: lower, some inverse⟩
  have hbranch' : branch ∈ splitLeading divisor.coefficients g := hbranch
  obtain ⟨hmodulusMonic, _⟩ :=
    splitLeading_monic_squarefree divisor.coefficients hg hgmonic hgfree branch hbranch'
  change modulus.monic at hmodulusMonic
  have hfollows :=
    (splitLeading_branch_root divisor.coefficients hg hgfree phi x branch hbranch' hroot).2
  obtain ⟨dropped, hcoefficients, hdropped, hinverse⟩ := hfollows
  change divisor.coefficients = dropped ++ leading :: lower at hcoefficients
  change leading.toPoly.eval₂ phi x * inverse.toPoly.eval₂ phi x = 1 at hinverse
  have hleading : leading.toPoly.eval₂ phi x ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hinverse
    exact zero_ne_one hinverse
  have hinverseValue : inverse.toPoly.eval₂ phi x =
      (leading.toPoly.eval₂ phi x)⁻¹ :=
    eq_inv_of_mul_eq_one_right hinverse
  have hdivisor : divisor.specialize phi x =
      specializeFiberCPolynomial (ofDescending (leading :: lower)) phi x := by
    rw [FiberPolynomial.specialize, FiberPolynomial.toCPolynomial, hcoefficients]
    exact specialize_ofDescending_eq_of_prefix_zero phi x dropped (leading :: lower) hdropped
  have hleadingCoeff : (divisor.specialize phi x).leadingCoeff =
      leading.toPoly.eval₂ phi x := by
    rw [hdivisor]
    exact leadingCoeff_specialize_ofDescending_cons phi x leading lower hleading
  have hnormalizedMonic :
      (normalizedDivisor modulus inverse (leading :: lower)).monic :=
    (CPolynomial.monic_toPoly_iff _).mpr
      (normalizedDivisor_monic modulus inverse leading lower)
  rw [specialize_reduceFiberCoefficients phi x hmodulusMonic hroot,
    specializeFiberCPolynomial,
    CPolynomial.modByMonic_toPoly_eq_modByMonic _ _
      hnormalizedMonic,
    Polynomial.map_modByMonic _
      (normalizedDivisor_monic modulus inverse leading lower)]
  change dividend.specialize phi x %ₘ
      specializeFiberCPolynomial
        (normalizedDivisor modulus inverse (leading :: lower)) phi x = _
  rw [specialize_normalizedDivisor phi x hmodulusMonic hroot leading inverse lower hinverse,
    ← hdivisor, hinverseValue, ← hleadingCoeff]
  exact Polynomial.mod_def.symm

/-- The specialized remainder on every unit-leading branch has strictly smaller fiber degree
than the specialized original divisor. -/
theorem degree_specialize_unitBranch_remainder_lt
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    {g : CPolynomial F} (hg : g ≠ 0) (hgmonic : g.monic)
    (hgfree : Squarefree g.toPoly)
    (dividend divisor : FiberPolynomial (F := F))
    (modulus leading inverse : CPolynomial F) (lower : List (CPolynomial F))
    (hbranch : (⟨modulus, leading :: lower, some inverse⟩ : LeadingBranch (F := F)) ∈
      splitLeading divisor.coefficients g)
    (hroot : modulus.toPoly.eval₂ phi x = 0) :
    (specializeFiberCPolynomial
        (reduceFiberCoefficients modulus
          (dividend.toCPolynomial.modByMonic
            (normalizedDivisor modulus inverse (leading :: lower)))) phi x).degree <
      (divisor.specialize phi x).degree := by
  rw [specialize_unitBranch_remainder_eq_mod phi x hg hgmonic hgfree dividend divisor
    modulus leading inverse lower hbranch hroot]
  apply Polynomial.degree_mod_lt
  let branch : LeadingBranch (F := F) :=
    ⟨modulus, leading :: lower, some inverse⟩
  have hfollows :=
    (splitLeading_branch_root divisor.coefficients hg hgfree phi x branch hbranch hroot).2
  obtain ⟨dropped, hcoefficients, hdropped, hinverse⟩ := hfollows
  change divisor.coefficients = dropped ++ leading :: lower at hcoefficients
  change leading.toPoly.eval₂ phi x * inverse.toPoly.eval₂ phi x = 1 at hinverse
  have hleading : leading.toPoly.eval₂ phi x ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hinverse
    exact zero_ne_one hinverse
  rw [FiberPolynomial.specialize, FiberPolynomial.toCPolynomial, hcoefficients,
    specialize_ofDescending_eq_of_prefix_zero phi x dropped (leading :: lower) hdropped]
  exact (Polynomial.leadingCoeff_ne_zero.mp
    (by simpa [leadingCoeff_specialize_ofDescending_cons phi x leading lower hleading]
      using hleading))

/-- A rooted terminal zero branch certifies that the original specialized divisor is zero; the
step leaves this degree-drop leaf explicit instead of attempting division. -/
theorem zeroBranch_specialize_divisor_eq_zero
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    {g : CPolynomial F} (hg : g ≠ 0) (hgfree : Squarefree g.toPoly)
    (divisor : FiberPolynomial (F := F)) (modulus : CPolynomial F)
    (hbranch : (⟨modulus, [], none⟩ : LeadingBranch (F := F)) ∈
      splitLeading divisor.coefficients g)
    (hroot : modulus.toPoly.eval₂ phi x = 0) :
    divisor.specialize phi x = 0 := by
  let branch : LeadingBranch (F := F) := ⟨modulus, [], none⟩
  have hfollows :=
    (splitLeading_branch_root divisor.coefficients hg hgfree phi x branch hbranch hroot).2
  rw [FiberPolynomial.specialize, FiberPolynomial.toCPolynomial,
    specialize_ofDescending_eq_of_follows phi x hfollows,
    specialize_ofDescending_nil]

/-- A terminal zero branch is retained in the executable output with no attempted division. -/
theorem zeroBranch_mem_remainderStep (g : CPolynomial F)
    (dividend divisor : FiberPolynomial (F := F)) (modulus : CPolynomial F)
    (hbranch : (⟨modulus, [], none⟩ : LeadingBranch (F := F)) ∈
      splitLeading divisor.coefficients g) :
    (⟨⟨modulus, [], none⟩, none⟩ : RemainderBranch (F := F)) ∈
      remainderStep g dividend divisor := by
  simpa [remainderStep, makeRemainderBranch] using
    List.mem_map_of_mem hbranch

/-- Leading-coefficient descent only removes a prefix, so every returned fiber width is bounded
by the input width. -/
theorem splitLeading_coefficients_length_le (coefficients : List (CPolynomial F))
    (g : CPolynomial F) :
    ∀ branch ∈ splitLeading coefficients g,
      branch.coefficients.length ≤ coefficients.length := by
  induction coefficients generalizing g with
  | nil => simp [splitLeading]
  | cons coefficient coefficients ih =>
      cases hsplit : coefficientSplit? g coefficient with
      | none => simp [splitLeading, hsplit]
      | some split =>
          intro branch hbranch
          simp only [splitLeading, hsplit, List.mem_cons] at hbranch
          rcases hbranch with rfl | hbranch
          · simp
          · exact (ih split.zeroModulus branch hbranch).trans (Nat.le_succ _)

/-- The total base-degree-times-fiber-width budget cannot increase during leading regularization
and one remainder step. -/
theorem remainderStep_baseDegree_mul_width_sum_le (g : CPolynomial F)
    (dividend divisor : FiberPolynomial (F := F))
    (hg : g ≠ 0) (hgfree : Squarefree g.toPoly) :
    ((remainderStep g dividend divisor).map fun branch =>
      branch.leading.modulus.natDegree * branch.leading.coefficients.length).sum ≤
        g.natDegree * divisor.coefficients.length := by
  rw [remainderStep, List.map_map]
  have hmaps :
      (splitLeading divisor.coefficients g).map
          ((fun branch => branch.leading.modulus.natDegree *
              branch.leading.coefficients.length) ∘ makeRemainderBranch dividend) =
        (splitLeading divisor.coefficients g).map fun branch =>
          branch.modulus.natDegree * branch.coefficients.length := by
    apply List.map_congr_left
    intro branch _
    simp only [Function.comp_apply, makeRemainderBranch_leading]
  rw [hmaps]
  calc
    _ ≤ ((splitLeading divisor.coefficients g).map fun branch =>
        branch.modulus.natDegree * divisor.coefficients.length).sum :=
      List.sum_le_sum fun branch hbranch =>
        Nat.mul_le_mul_left branch.modulus.natDegree
          (splitLeading_coefficients_length_le divisor.coefficients g branch hbranch)
    _ = g.natDegree * divisor.coefficients.length := by
      rw [List.sum_map_mul_right,
        splitLeading_natDegree_sum divisor.coefficients hg hgfree]

/-- The remainder-step branch family inherits the exact base-degree budget from
leading-coefficient regularization. -/
theorem remainderStep_natDegree_sum (g : CPolynomial F)
    (dividend divisor : FiberPolynomial (F := F))
    (hg : g ≠ 0) (hgfree : Squarefree g.toPoly) :
    ((remainderStep g dividend divisor).map fun branch =>
      branch.leading.modulus.natDegree).sum = g.natDegree := by
  rw [remainderStep, List.map_map]
  have hmaps :
      (splitLeading divisor.coefficients g).map
          ((fun branch => branch.leading.modulus.natDegree) ∘
            makeRemainderBranch dividend) =
        (splitLeading divisor.coefficients g).map fun branch => branch.modulus.natDegree := by
    apply List.map_congr_left
    intro branch _
    simp only [Function.comp_apply, makeRemainderBranch_leading]
  rw [hmaps]
  exact splitLeading_natDegree_sum divisor.coefficients hg hgfree

/-- Multiplying each branch width by a common recursion weight preserves the corresponding
weighted base-degree budget. -/
theorem remainderStep_weighted_natDegree_sum (g : CPolynomial F)
    (dividend divisor : FiberPolynomial (F := F)) (weight : ℕ)
    (hg : g ≠ 0) (hgfree : Squarefree g.toPoly) :
    ((remainderStep g dividend divisor).map fun branch =>
      branch.leading.modulus.natDegree * weight).sum = g.natDegree * weight := by
  rw [List.sum_map_mul_right]
  exact congrArg (fun degree => degree * weight)
    (remainderStep_natDegree_sum g dividend divisor hg hgfree)

end ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5
