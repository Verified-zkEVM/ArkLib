/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

module

public import ArkLib.OracleReduction.OracleInterface
public import CompPoly.Univariate.Basic
public import CompPoly.Univariate.Linear
public import CompPoly.Multivariate.Basic
public import CompPoly.Multivariate.Restrict

/-!
# Computable OracleInterface instances backed by CompPoly

This module registers `OracleInterface` instances for CompPoly's `CPolynomial` and
`CPoly.CMvPolynomial`, together with degree-bounded subtypes.  These give a
computable counterpart to the Mathlib-backed `Polynomial.degreeLE` / `MvPolynomial.restrictDegree`
oracle interfaces in `OracleInterface.lean` and are used by the computable sum-check spec.

Note: this file is kept separate from `OracleInterface.lean` because importing
`CompPoly.Multivariate.CMvPolynomial` transitively exposes a high-priority `GetElem` instance
for `CPoly.Unlawful` that shadows `Vector`'s in existing proofs.  We limit the exposure by only
importing this module in modules that specifically need CompPoly-backed polynomial oracles.
-/

@[expose] public section

open OracleComp OracleSpec OracleQuery

/-- Computable univariate polynomials can be accessed via evaluation queries. -/
@[reducible, inline]
instance instCPolynomial (R : Type _) [Semiring R] : OracleInterface (CompPoly.CPolynomial R) where
  Query := R
  toOC.spec := R →ₒ R
  toOC.impl point := do return (← read).eval point

/-- Computable multivariate polynomials with individual degree at most `d` can be accessed via
evaluation queries. -/
@[reducible, inline]
instance instRestrictDegree (R : Type _) [CommSemiring R] [BEq R] [LawfulBEq R]
    (n d : ℕ) : OracleInterface (CPoly.restrictDegree R n d) where
  Query := (Fin n → R)
  toOC.spec := (Fin n → R) →ₒ R
  toOC.impl points := do return CPoly.CMvPolynomial.eval points (← read).1

instance (R : Type _) [CommSemiring R] [BEq R] [LawfulBEq R] [Fintype R] (n d : ℕ) :
    Fintype (OracleInterface.Query (CPoly.restrictDegree R n d)) :=
  inferInstanceAs (Fintype (Fin n → R))

/-- Bridge: at a `ℕ`-valued cutoff, the `Set`-valued `CompPoly.CPolynomial.degreeLE` agrees with
`natDegree`. -/
theorem CompPoly.CPolynomial.mem_degreeLE_iff_natDegree_le (R : Type _) [Semiring R] [BEq R]
    [LawfulBEq R] {d : ℕ} {p : CompPoly.CPolynomial R} :
    p ∈ CompPoly.CPolynomial.degreeLE (R := R) (d : WithBot ℕ) ↔ p.natDegree ≤ d := by
  rw [CompPoly.CPolynomial.mem_degreeLE]
  rcases eq_or_ne p 0 with rfl | hp
  · simp [CompPoly.CPolynomial.natDegree_zero]
  · rw [CompPoly.CPolynomial.degree_eq_natDegree p hp, Nat.cast_le]

/-- Computable univariate polynomials of degree at most `d`, in the `Set`-valued `degreeLE`
presentation, can be accessed via evaluation queries, inherited from the ambient
`instCPolynomial`. -/
@[reducible, inline]
instance instCPolynomialDegreeLESet (R : Type _) [Semiring R] (d : WithBot ℕ) :
    OracleInterface (CompPoly.CPolynomial.degreeLE (R := R) d) where
  Query := R
  toOC.spec := R →ₒ R
  toOC.impl point := (instCPolynomial R).toOC.impl point ∘ Subtype.val

/-- The zero polynomial witnesses `CompPoly.CPolynomial.degreeLE R d` since
`natDegree 0 = 0 ≤ d`. -/
instance (R : Type _) [Semiring R] [BEq R] [LawfulBEq R] (d : ℕ) :
    Inhabited (CompPoly.CPolynomial.degreeLE (R := R) (d : WithBot ℕ)) :=
  ⟨⟨0, (CompPoly.CPolynomial.mem_degreeLE_iff_natDegree_le R).mpr
    (by rw [CompPoly.CPolynomial.natDegree_zero]; exact Nat.zero_le _)⟩⟩

/-- A coefficient past `natDegree` vanishes: the contrapositive of `le_natDegree_of_ne_zero`. -/
theorem CompPoly.CPolynomial.coeff_eq_zero_of_natDegree_lt {R : Type _} [Semiring R] [BEq R]
    [LawfulBEq R] {p : CompPoly.CPolynomial R} {i : ℕ} (h : p.natDegree < i) :
    p.coeff i = 0 := by
  by_contra hne
  exact absurd (CompPoly.CPolynomial.le_natDegree_of_ne_zero hne) (not_le.mpr h)

/-- Reading off the coefficients on `Fin (d + 1)` injectively determines a polynomial in
`CompPoly.CPolynomial.degreeLE R d`: any coefficient outside that window is forced to be `0`. -/
theorem CompPolynomialDegreeLE.coeff_injective (R : Type _) [Semiring R] [BEq R] [LawfulBEq R]
    (d : ℕ) : Function.Injective
      (fun p : CompPoly.CPolynomial.degreeLE (R := R) (d : WithBot ℕ) =>
        fun i : Fin (d + 1) => p.1.coeff i) := by
  intro p q h
  have hp := (CompPoly.CPolynomial.mem_degreeLE_iff_natDegree_le R).mp p.2
  have hq := (CompPoly.CPolynomial.mem_degreeLE_iff_natDegree_le R).mp q.2
  refine Subtype.ext (CompPoly.CPolynomial.eq_iff_coeff.mpr fun i => ?_)
  by_cases hi : i ≤ d
  · exact congrFun h ⟨i, Nat.lt_succ_of_le hi⟩
  · rw [CompPoly.CPolynomial.coeff_eq_zero_of_natDegree_lt (hp.trans_lt (not_le.mp hi)),
      CompPoly.CPolynomial.coeff_eq_zero_of_natDegree_lt (hq.trans_lt (not_le.mp hi))]

/-- Computable univariate polynomials of degree at most `d` are finite whenever `R` is,
via the injective coefficient-vector map on `Fin (d + 1)`. -/
noncomputable instance (R : Type _) [Semiring R] [BEq R] [LawfulBEq R] [Fintype R] (d : ℕ) :
    Fintype (CompPoly.CPolynomial.degreeLE (R := R) (d : WithBot ℕ)) :=
  Fintype.ofInjective _ (CompPolynomialDegreeLE.coeff_injective R d)

/-- Uniform sampling of computable univariate polynomials of degree at most `d`, by enumeration. -/
noncomputable instance (R : Type _) [Semiring R] [BEq R] [LawfulBEq R] [Fintype R] (d : ℕ) :
    SampleableType (CompPoly.CPolynomial.degreeLE (R := R) (d : WithBot ℕ)) :=
  SampleableType.ofFintype _

/-- The zero polynomial witnesses `CPoly.restrictDegree R n d`: the zero element of any
`Submodule` lies in it. -/
instance (R : Type _) [CommSemiring R] [BEq R] [LawfulBEq R] (n d : ℕ) :
    Inhabited (CPoly.restrictDegree R n d) :=
  ⟨⟨0, Submodule.zero_mem _⟩⟩
