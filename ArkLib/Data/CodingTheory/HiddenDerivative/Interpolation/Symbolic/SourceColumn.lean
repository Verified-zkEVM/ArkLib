/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.SourceMonomial
public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Source columns and assembled interpolants

A `SourceColumn d` records the exponents `x`, `y₀` and `higher j` of a source monomial
`X^x Y₀^(y₀) ∏_j Y_(j+1)^(higher j)`. A family `columns : κ → SourceColumn d` of distinct
columns and a coefficient vector `v : κ → R` assemble the differential polynomial
`interpolant columns v = ∑_j v j X^(columns j)`. The coefficient of this polynomial at the
exponent of `columns j` is `v j`, so the interpolant determines its coefficient vector, and a
ring homomorphism applied to the interpolant is applied to the coefficient vector.

## Main statements

* `SourceColumn.exponent_injective`: distinct columns have distinct exponents.
* `SourceColumn.enumerate` and its exponent, injectivity, and membership lemmas: source columns
  enumerated from a finite set of exponent vectors.
* `SourceColumn.totalJetDegree_exponent`: the total jet degree of a column is
  `y₀ + ∑_j higher j`.
* `SourceColumn.polynomial_eq_sourceMonomial`: a column's monomial is the source monomial.
* `SourceColumn.coeff_interpolant`: the coefficient of the interpolant at `columns j` is `v j`.
* `SourceColumn.coeff_interpolant_natDegree_le`: distinct columns preserve coefficient height
  at every derivative order.
* `SourceColumn.map_interpolant_ne_zero`: the image of the interpolant under a ring
  homomorphism is nonzero when the image of the coefficient vector is.
* `SourceColumn.interpolant_totalJetDegree_le` and
  `SourceColumn.map_interpolant_jetTotalDegree_le`: jet-degree bounds for interpolants and their
  coefficient maps.

## References

* [DKT26]
* [DKTZ26]
-/

@[expose] public section

open PolynomialDifferential
open scoped Polynomial

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {d : ℕ}

/-- The exponents of a source monomial `X^x Y₀^(y₀) ∏_j Y_(j+1)^(higher j)`. -/
structure SourceColumn (d : ℕ) where
  /-- The exponent of `X`. -/
  x : ℕ
  /-- The exponent of `Y₀`. -/
  y₀ : ℕ
  /-- The exponent of `Y_(j+1)`, for `j : Fin d`. -/
  higher : Fin d → ℕ

namespace SourceColumn

/-- The exponent vector of the source monomial of a column. -/
def exponent (c : SourceColumn d) : JetVariable d →₀ ℕ :=
  Finsupp.single none c.x + Finsupp.single (some 0) c.y₀ +
    ∑ j, Finsupp.single (some j.succ) (c.higher j)

/-- The `X` exponent of a column's exponent vector is `x`. -/
@[simp]
theorem exponent_none (c : SourceColumn d) : c.exponent none = c.x := by
  simp [exponent]

/-- The `Y₀` exponent of a column's exponent vector is `y₀`. -/
@[simp]
theorem exponent_zero (c : SourceColumn d) : c.exponent (some 0) = c.y₀ := by
  simp [exponent]

/-- The `Y_(j+1)` exponent of a column's exponent vector is `higher j`. -/
@[simp]
theorem exponent_succ (c : SourceColumn d) (j : Fin d) :
    c.exponent (some j.succ) = c.higher j := by
  simp [exponent, Finsupp.single_apply]

/-- The weight of a column's exponent vector for a weight `w` on the jet variables. -/
theorem weight_exponent {M : Type*} [AddCommMonoid M] (w : JetVariable d → M)
    (c : SourceColumn d) :
    c.exponent.weight w =
      c.x • w none + c.y₀ • w (some 0) + ∑ j, c.higher j • w (some j.succ) := by
  simp [exponent, map_sum, Finsupp.weight_single]

/-- The total jet degree of a column is `y₀ + ∑_j higher j`. -/
@[simp]
theorem totalJetDegree_exponent (c : SourceColumn d) :
    totalJetDegree c.exponent = c.y₀ + ∑ j, c.higher j := by
  rw [totalJetDegree_eq_sum, Fin.sum_univ_succ]
  simp

/-- Distinct columns have distinct exponent vectors. -/
theorem exponent_injective :
    Function.Injective (exponent : SourceColumn d → JetVariable d →₀ ℕ) := by
  rintro ⟨x, y₀, higher⟩ ⟨x', y₀', higher'⟩ h
  have hx := congrArg (fun e => e none) h
  have hy₀ := congrArg (fun e => e (some 0)) h
  have hhigher : higher = higher' := funext fun j => by
    simpa using congrArg (fun e => e (some j.succ)) h
  simp only [exponent_none, exponent_zero] at hx hy₀
  subst hx hy₀ hhigher
  rfl

/-- Recover the source-column coordinates of an arbitrary exponent vector. -/
def ofExponent (u : JetVariable d →₀ ℕ) : SourceColumn d where
  x := u none
  y₀ := u (some 0)
  higher j := u (some j.succ)

/-- `SourceColumn.ofExponent` has the exponent vector it was given. -/
@[simp]
theorem exponent_ofExponent (u : JetVariable d →₀ ℕ) :
    (SourceColumn.ofExponent u).exponent = u := by
  ext v
  rcases v with _ | j
  · simp [SourceColumn.ofExponent, SourceColumn.exponent]
  · induction j using Fin.cases with
    | zero => simp [SourceColumn.ofExponent, SourceColumn.exponent]
    | succ j =>
      simp only [SourceColumn.ofExponent, SourceColumn.exponent, Finsupp.add_apply,
        Finsupp.single_apply, Option.some.injEq, reduceCtorEq,
        ite_false, zero_add]
      rw [ite_eq_right (by
        intro h
        have := congrArg Fin.val h
        simp at this), zero_add]
      change Finsupp.applyAddHom (some j.succ)
        (∑ k : Fin d, Finsupp.single (some k.succ) (u (some k.succ))) = _
      rw [map_sum]
      calc
        ∑ k : Fin d, Finsupp.applyAddHom (some j.succ)
            (Finsupp.single (some k.succ) (u (some k.succ))) =
            Finsupp.applyAddHom (some j.succ)
              (Finsupp.single (some j.succ) (u (some j.succ))) := by
          apply Fintype.sum_eq_single j
          intro k hkj
          simp [hkj]
        _ = u (some j.succ) := by simp

/-- Enumerate a finite set of exponent vectors as source columns. -/
def enumerate (s : Finset (JetVariable d →₀ ℕ)) :
    Fin (Fintype.card (↑s)) → SourceColumn d :=
  fun i => SourceColumn.ofExponent ((Fintype.equivFin (↑s)).symm i).1

/-- The exponent of an enumerated source column is its indexed exponent vector. -/
@[simp]
theorem exponent_enumerate (s : Finset (JetVariable d →₀ ℕ))
    (i : Fin (Fintype.card (↑s))) :
    (enumerate s i).exponent = ((Fintype.equivFin (↑s)).symm i).1 := by
  simp [enumerate]

/-- Distinct indices enumerate distinct source columns. -/
theorem enumerate_injective (s : Finset (JetVariable d →₀ ℕ)) :
    Function.Injective (enumerate s) := by
  intro i j hij
  apply (Fintype.equivFin (↑s)).symm.injective
  apply Subtype.ext
  rw [← exponent_enumerate s i, ← exponent_enumerate s j]
  exact congrArg SourceColumn.exponent hij

/-- Every enumerated source column has an exponent in the finite set. -/
theorem exponent_enumerate_mem (s : Finset (JetVariable d →₀ ℕ))
    (i : Fin (Fintype.card (↑s))) :
    (enumerate s i).exponent ∈ s := by
  rw [exponent_enumerate]
  exact ((Fintype.equivFin (↑s)).symm i).2

variable {R : Type*} [CommSemiring R]

/-- The source monomial of a column, with coefficient `1`. -/
def polynomial (c : SourceColumn d) : DifferentialPolynomial R d :=
  monomial c.exponent 1

/-- The monomial of a column is the source monomial with the same exponents. -/
theorem polynomial_eq_sourceMonomial (c : SourceColumn d) :
    (c.polynomial : DifferentialPolynomial R d) = sourceMonomial c.x c.y₀ c.higher := by
  rw [sourceMonomial, polynomial, exponent, X_pow_eq_monomial, X_pow_eq_monomial,
    monomial_mul_monomial, one_mul]
  simp_rw [X_pow_eq_monomial]
  rw [← monomial_sum_one, monomial_mul_monomial, one_mul]

variable {κ : Type*} [Fintype κ]

/-- The differential polynomial `∑_j v j X^(columns j)` assembled from the columns and a
coefficient vector. -/
def interpolant (columns : κ → SourceColumn d) (v : κ → R) : DifferentialPolynomial R d :=
  ∑ j, monomial (columns j).exponent (v j)

/-- The interpolant is the linear combination of the column monomials with coefficients `v`. -/
theorem interpolant_eq_sum_smul (columns : κ → SourceColumn d) (v : κ → R) :
    interpolant columns v = ∑ j, v j • (columns j).polynomial := by
  simp [interpolant, polynomial, smul_monomial]

/-- For distinct columns, the coefficient of the interpolant at the exponent of `columns j` is
`v j`. -/
theorem coeff_interpolant {columns : κ → SourceColumn d} (hcolumns : Function.Injective columns)
    (v : κ → R) (j : κ) :
    (interpolant columns v).coeff (columns j).exponent = v j := by
  classical
  rw [interpolant, coeff_sum, Finset.sum_eq_single j]
  · simp
  · intro k _ hkj
    rw [coeff_monomial, ite_eq_right_iff]
    exact fun h => absurd (hcolumns (exponent_injective h)) hkj
  · simp

/-- Distinct source columns preserve coefficient height at every derivative order. -/
theorem coeff_interpolant_natDegree_le {F : Type*} [CommSemiring F] {h : ℕ}
    (columns : κ → SourceColumn d) (hcolumns : Function.Injective columns)
    (v : κ → Polynomial F) (hv : ∀ j, (v j).natDegree ≤ h) :
    ∀ u, ((interpolant columns v).coeff u).natDegree ≤ h := by
  classical
  intro u
  by_cases hu : u ∈ Set.range (fun j ↦ (columns j).exponent)
  · obtain ⟨j, rfl⟩ := hu
    rw [coeff_interpolant hcolumns v j]
    exact hv j
  · have hcoeff : (interpolant columns v).coeff u = 0 := by
      rw [interpolant, MvPolynomial.coeff_sum]
      apply Finset.sum_eq_zero
      intro j _
      rw [MvPolynomial.coeff_monomial]
      split
      · rename_i heq
        exact (hu ⟨j, heq⟩).elim
      · rfl
    simp [hcoeff]

/-- Mapping the coefficients of the interpolant maps its coefficient vector. -/
theorem map_interpolant {S : Type*} [CommSemiring S] (ψ : R →+* S)
    (columns : κ → SourceColumn d) (v : κ → R) :
    MvPolynomial.map ψ (interpolant columns v) = interpolant columns (fun j => ψ (v j)) := by
  simp [interpolant, map_monomial]

/-- For distinct columns, the interpolant vanishes exactly when its coefficient vector does. -/
theorem interpolant_eq_zero_iff {columns : κ → SourceColumn d}
    (hcolumns : Function.Injective columns) {v : κ → R} :
    interpolant columns v = 0 ↔ v = 0 := by
  constructor
  · intro h
    funext j
    simpa [h] using (coeff_interpolant hcolumns v j).symm
  · rintro rfl
    simp [interpolant]

/-- For distinct columns, the image of the interpolant under a ring homomorphism `ψ` is nonzero
when the image `j ↦ ψ (v j)` of its coefficient vector is nonzero. -/
theorem map_interpolant_ne_zero {S : Type*} [CommSemiring S] {columns : κ → SourceColumn d}
    (hcolumns : Function.Injective columns) {v : κ → R} (ψ : R →+* S)
    (hv : (fun j => ψ (v j)) ≠ 0) :
    MvPolynomial.map ψ (interpolant columns v) ≠ 0 := by
  rwa [map_interpolant, Ne, interpolant_eq_zero_iff hcolumns]

/-- The total jet degree of an interpolant is bounded by the largest bound on its columns. -/
theorem interpolant_totalJetDegree_le (columns : κ → SourceColumn d)
    {ν : ℕ} (hdegree : ∀ j, totalJetDegree (columns j).exponent ≤ ν) (v : κ → R) :
    ∀ u ∈ (interpolant columns v).support, totalJetDegree u ≤ ν := by
  classical
  intro u hu
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hu)
  have heq : u = (columns j).exponent := by
    simpa using MvPolynomial.support_monomial_subset hj
  subst u
  exact hdegree j

/-- Mapping the coefficients of an interpolant preserves its total jet degree bound. -/
theorem map_interpolant_jetTotalDegree_le {S : Type*} [CommSemiring S]
    (ψ : R →+* S) (columns : κ → SourceColumn d) {ν : ℕ}
    (hdegree : ∀ j, totalJetDegree (columns j).exponent ≤ ν) (v : κ → R) :
    jetTotalDegree (MvPolynomial.map ψ (interpolant columns v)) ≤ ν := by
  rw [jetTotalDegree_le_iff]
  intro u hu
  exact interpolant_totalJetDegree_le columns hdegree v u
    (MvPolynomial.support_map_subset ψ _ hu)

end SourceColumn

end ReedSolomon.HiddenDerivative
