/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.JetPrefix
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-!
# Presentations at the highest active jet

A differential polynomial `Q` of ambient depth `d` whose jet variables are among `Y₀, ..., Y_s`
is the renaming, along `jetPrefixEmbedding s`, of a unique differential polynomial of depth `s`.
A `JetPrefixPresentation Q s` records that depth-`s` polynomial. The renaming is injective, so it
keeps every coefficient, every individual jet degree and the total jet degree, and it commutes
with separants, differential specialization, jet evaluation and regularity. The top variable of
the presentation corresponds to `Y_s`.

Every statement holds over a commutative semiring, and presentations map along any coefficient
homomorphism. In particular a presentation built over a coefficient ring `K[Z]` that contains an
unevaluated challenge `Z` specializes to a presentation of every evaluation `Z ↦ z`.

## Main statements

* `jetDegree_rename_jetPrefixEmbedding` and `jetTotalDegree_rename_jetPrefixEmbedding`: the prefix
  renaming keeps individual and total jet degrees.
* `JetPrefixPresentation` and `nonempty_jetPrefixPresentation`: presentations exist at the highest
  active jet, and there is at most one (`JetPrefixPresentation.instSubsingleton`).
* `exists_jetPrefixPresentation_of_vars_subset_range`: a polynomial supported on a jet prefix has
  a presentation at that prefix.
* `exists_jetPrefixPresentation_firstOrder_of_jetDegree_zero`: a first-order equation independent
  of `Y₁` has a presentation at depth zero.
* `JetPrefixPresentation.coeff_equation`, `JetPrefixPresentation.jetDegree_equation`,
  `JetPrefixPresentation.jetTotalDegree_equation`: coefficients and degrees of the presentation.
* `JetPrefixPresentation.isHighestActiveJet_last`: the top variable is the highest active jet of
  the presentation.
* `JetPrefixPresentation.differentialSpecialization_separant_equation` and
  `JetPrefixPresentation.isRegularJet_equation_iff`: the presentation has the same separant
  specializations and regular jets as `Q` at `Y_s`.
* `JetPrefixPresentation.map`: presentations along a coefficient homomorphism.
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open Polynomial

variable {R : Type*} [CommSemiring R] {d : ℕ}

/-! ### Degrees under the prefix renaming -/

/-- The prefix renaming keeps the degree in each retained jet variable. -/
theorem jetDegree_rename_jetPrefixEmbedding (s : Fin (d + 1))
    (Q : DifferentialPolynomial R s.val) (j : Fin (s.val + 1)) :
    jetDegree (MvPolynomial.rename (jetPrefixEmbedding s) Q) (Fin.castLE s.isLt j) =
      jetDegree Q j :=
  MvPolynomial.degreeOf_rename_of_injective (jetPrefixEmbedding s).injective (some j)

/-- The prefix renaming keeps the total jet degree. -/
theorem jetTotalDegree_rename_jetPrefixEmbedding (s : Fin (d + 1))
    (Q : DifferentialPolynomial R s.val) :
    jetTotalDegree (MvPolynomial.rename (jetPrefixEmbedding s) Q) = jetTotalDegree Q := by
  rw [jetTotalDegree, MvPolynomial.weightedTotalDegree_rename_of_injective
    (jetPrefixEmbedding s).injective, jetTotalDegree]
  congr 1
  funext v
  cases v <;> rfl

/-! ### Presentations -/

/-- A presentation of `Q` at depth `s`: a differential polynomial of depth `s` whose renaming
along `jetPrefixEmbedding s` is `Q`. -/
structure JetPrefixPresentation (Q : DifferentialPolynomial R d) (s : Fin (d + 1)) where
  /-- The depth-`s` differential polynomial. -/
  equation : DifferentialPolynomial R s.val
  /-- Renaming the depth-`s` polynomial into depth `d` gives `Q`. -/
  rename_equation : MvPolynomial.rename (jetPrefixEmbedding s) equation = Q

/-- A differential polynomial supported on a jet prefix has a presentation at that prefix. -/
theorem exists_jetPrefixPresentation_of_vars_subset_range (Q : DifferentialPolynomial R d)
    (s : Fin (d + 1))
    (hvars : (Q.vars : Set (JetVariable d)) ⊆ Set.range (jetPrefixEmbedding s)) :
    Nonempty (JetPrefixPresentation Q s) := by
  obtain ⟨equation, hequation⟩ := MvPolynomial.exists_rename_eq_of_vars_subset_range Q
    (jetPrefixEmbedding s) (jetPrefixEmbedding s).injective hvars
  exact ⟨⟨equation, hequation⟩⟩

/-- A first-order differential polynomial of degree zero in `Y₁` has a presentation at depth
zero. -/
theorem exists_jetPrefixPresentation_firstOrder_of_jetDegree_zero
    (Q : DifferentialPolynomial R 1) (hdegree : jetDegree Q (1 : Fin 2) = 0) :
    Nonempty (JetPrefixPresentation Q (0 : Fin 2)) := by
  classical
  have hvars : (Q.vars : Set (JetVariable 1)) ⊆
      Set.range (jetPrefixEmbedding (0 : Fin 2)) := by
    intro v hv
    rcases v with _ | j
    · exact ⟨none, rfl⟩
    · fin_cases j
      · exact ⟨some 0, rfl⟩
      · have hne : jetDegree Q (1 : Fin 2) ≠ 0 :=
          MvPolynomial.mem_vars_iff_degreeOf_ne_zero.mp hv
        exact (hne hdegree).elim
  exact exists_jetPrefixPresentation_of_vars_subset_range Q (0 : Fin 2) hvars

/-- `Q` has a presentation at its highest active jet. -/
theorem nonempty_jetPrefixPresentation (Q : DifferentialPolynomial R d) {s : Fin (d + 1)}
    (hs : IsHighestActiveJet Q s) : Nonempty (JetPrefixPresentation Q s) :=
  let ⟨equation, h⟩ := exists_prefixDifferentialPolynomial Q hs
  ⟨⟨equation, h⟩⟩

namespace JetPrefixPresentation

variable {Q : DifferentialPolynomial R d} {s : Fin (d + 1)}

/-- A presentation is unique, since the prefix renaming is injective. -/
instance instSubsingleton : Subsingleton (JetPrefixPresentation Q s) where
  allEq A B := by
    obtain ⟨a, ha⟩ := A
    obtain ⟨b, hb⟩ := B
    obtain rfl : a = b :=
      MvPolynomial.rename_injective _ (jetPrefixEmbedding s).injective (ha.trans hb.symm)
    rfl

/-- The presentation of a nonzero equation is nonzero. -/
theorem equation_ne_zero (A : JetPrefixPresentation Q s) (hQ : Q ≠ 0) : A.equation ≠ 0 :=
  fun hz ↦ hQ (by rw [← A.rename_equation, hz, map_zero])

/-- Each coefficient of the presentation is the coefficient of `Q` at the renamed exponent. -/
theorem coeff_equation (A : JetPrefixPresentation Q s) (u : JetVariable s.val →₀ ℕ) :
    A.equation.coeff u = Q.coeff (u.mapDomain (jetPrefixEmbedding s)) := by
  obtain ⟨e, rfl⟩ := A
  exact (MvPolynomial.coeff_rename_mapDomain _ (jetPrefixEmbedding s).injective e u).symm

/-- The degree of the presentation in `Y_j` is the degree of `Q` in `Y_j`. -/
theorem jetDegree_equation (A : JetPrefixPresentation Q s) (j : Fin (s.val + 1)) :
    jetDegree A.equation j = jetDegree Q (Fin.castLE s.isLt j) := by
  obtain ⟨e, rfl⟩ := A
  exact (jetDegree_rename_jetPrefixEmbedding s e j).symm

/-- The degree of the presentation in its top variable is the degree of `Q` in `Y_s`. -/
theorem jetDegree_equation_last (A : JetPrefixPresentation Q s) :
    jetDegree A.equation (Fin.last s.val) = jetDegree Q s :=
  A.jetDegree_equation (Fin.last s.val)

/-- The presentation has the total jet degree of `Q`. -/
theorem jetTotalDegree_equation (A : JetPrefixPresentation Q s) :
    jetTotalDegree A.equation = jetTotalDegree Q := by
  obtain ⟨e, rfl⟩ := A
  exact (jetTotalDegree_rename_jetPrefixEmbedding s e).symm

/-- If `Q` depends on `Y_s`, the top variable is the highest active jet of the presentation. -/
theorem isHighestActiveJet_last (A : JetPrefixPresentation Q s) (hs : DependsOnJet Q s) :
    IsHighestActiveJet A.equation (Fin.last s.val) :=
  ⟨show 0 < jetDegree A.equation (Fin.last s.val) by rw [A.jetDegree_equation_last]; exact hs,
    fun j hj ↦ absurd (Fin.le_last j) (not_le_of_gt hj)⟩

/-- Renaming the separant of the presentation in its top variable gives the separant of `Q` in
`Y_s`. -/
theorem rename_separant_equation (A : JetPrefixPresentation Q s) :
    MvPolynomial.rename (jetPrefixEmbedding s) (separant A.equation (Fin.last s.val)) =
      separant Q s := by
  obtain ⟨e, rfl⟩ := A
  exact (separant_rename_jetPrefixEmbedding s e).symm

/-- The presentation and `Q` have the same differential specializations. -/
theorem differentialSpecialization_equation (A : JetPrefixPresentation Q s) (P : R[X]) :
    differentialSpecialization A.equation P = differentialSpecialization Q P := by
  obtain ⟨e, rfl⟩ := A
  exact (differentialSpecialization_rename_jetPrefixEmbedding s e P).symm

/-- Evaluating the presentation on the restriction of a scalar jet is evaluating `Q` on the jet. -/
theorem jetEvaluation_equation (A : JetPrefixPresentation Q s) (center : R)
    (jet : Fin (d + 1) → R) :
    jetEvaluation A.equation center (restrictJet s jet) = jetEvaluation Q center jet := by
  obtain ⟨e, rfl⟩ := A
  exact (jetEvaluation_rename_jetPrefixEmbedding s e center jet).symm

/-- The separant of the presentation in its top variable and the separant of `Q` in `Y_s` have
the same differential specializations. -/
theorem differentialSpecialization_separant_equation (A : JetPrefixPresentation Q s) (P : R[X]) :
    differentialSpecialization (separant A.equation (Fin.last s.val)) P =
      differentialSpecialization (separant Q s) P := by
  rw [← A.rename_separant_equation, differentialSpecialization_rename_jetPrefixEmbedding]

/-- The Hasse jet of `P` is regular for the presentation in its top variable exactly when it is
regular for `Q` in `Y_s`. -/
theorem isRegularJet_equation_iff (A : JetPrefixPresentation Q s) (center : R) (P : R[X]) :
    IsRegularJet A.equation (Fin.last s.val) center (polynomialJet center P) ↔
      IsRegularJet Q s center (polynomialJet center P) := by
  obtain ⟨e, rfl⟩ := A
  exact (isRegularJet_rename_jetPrefixEmbedding_iff s e center P).symm

/-- Mapping coefficients along `φ` maps a presentation of `Q` to a presentation of `Q.map φ`. -/
def map {S : Type*} [CommSemiring S] (φ : R →+* S) (A : JetPrefixPresentation Q s) :
    JetPrefixPresentation (MvPolynomial.map φ Q) s where
  equation := MvPolynomial.map φ A.equation
  rename_equation := by rw [← MvPolynomial.map_rename, A.rename_equation]

/-- The mapped presentation is the mapped depth-`s` polynomial. -/
@[simp]
theorem map_equation {S : Type*} [CommSemiring S] (φ : R →+* S) (A : JetPrefixPresentation Q s) :
    (A.map φ).equation = MvPolynomial.map φ A.equation :=
  rfl

/-- Over `R[X]`, if every coefficient of `Q` has degree at most `h`, so does every coefficient of
its presentation. -/
theorem natDegree_coeff_equation_le {Q : DifferentialPolynomial R[X] d}
    (A : JetPrefixPresentation Q s) {h : ℕ} (hQ : ∀ u, (Q.coeff u).natDegree ≤ h)
    (u : JetVariable s.val →₀ ℕ) : (A.equation.coeff u).natDegree ≤ h := by
  rw [A.coeff_equation]
  exact hQ _

end JetPrefixPresentation

end

end PolynomialDifferential
