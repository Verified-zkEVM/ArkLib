/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.DerivativeDescent
public import Mathlib.RingTheory.Polynomial.Basic

/-!
# Changing the coefficient ring of a differential equation

Let `f : F →+* E` be a ring homomorphism and `Q` a differential polynomial over `F`. Mapping
coefficients commutes with differential specialization,

  `(Q(X, P, D¹P, ..., DᵈP)).map f = (Q.map f)(X, P.map f, D¹(P.map f), ...)`,

so every solution of `Q = 0` of degree at most `D` maps to a solution of `Q.map f = 0` of degree at
most `D`. When `f` is injective this map of solutions is injective, the individual jet degrees of
`Q` are unchanged, and so is the cast hypothesis `JetDegreeCastsNeZero`. Over a finite `E` this
gives `Nat.card (BoundedSolution Q D) ≤ Nat.card (BoundedSolution (Q.map f) D)`: a root count
proved over a larger finite field, such as `FiniteField.Extension F p n`, bounds the root count
over `F`. The inequality is one-way: the equation `0 = 0` with `D = 0` has `2` constant solutions
over `ZMod 2` and `4` over the field with four elements.

Passing to an extension field `E` of `F` does not change the characteristic
(`Algebra.ringChar_eq`), so it does not weaken the characteristic hypotheses of the root counts.
The root counts over extension fields that use these transports are in
`ArkLib.Data.Polynomial.Differential.TotalJetDegreeCount`.

## Main statements

* `map_differentialSpecialization`, `map_separant`: naturality of specialization and separants.
* `jetDegree_map_eq`, `jetTotalDegree_map_eq`, `jetDegreeCastsNeZero_map_iff`: injective
  coefficient maps preserve individual and total jet degrees and the cast hypothesis.
* `jetDegree_map_le`, `highestActiveJet_map_eq_none`: any coefficient map does not increase jet
  degrees, so it keeps an equation with no active jet free of jet variables.
* `BoundedSolution.instFinite`: over a finite coefficient semiring there are finitely many
  solutions of degree at most `D`.
* `BoundedSolution.map`, `BoundedSolution.map_injective`, `BoundedSolution.natCard_le_natCard_map`:
  transport of bounded solutions and the cardinality comparison.
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open Polynomial

variable {F E : Type*} {d : ℕ}

/-! ### Naturality -/

/-- Differential specialization commutes with mapping coefficients along a ring homomorphism:
mapping `Q(X, P, D¹P, ..., DᵈP)` along `f` gives `Q.map f` specialized at `P.map f`. This uses
that Hasse derivatives commute with `Polynomial.map`. -/
theorem map_differentialSpecialization [CommSemiring F] [CommSemiring E] (f : F →+* E)
    (Q : DifferentialPolynomial F d) (P : F[X]) :
    (differentialSpecialization Q P).map f =
      differentialSpecialization (MvPolynomial.map f Q) (P.map f) := by
  change Polynomial.mapRingHom f (MvPolynomial.eval₂Hom Polynomial.C _ Q) =
    MvPolynomial.eval₂Hom Polynomial.C _ (MvPolynomial.map f Q)
  rw [MvPolynomial.map_eval₂Hom, MvPolynomial.eval₂Hom_map_hom]
  refine MvPolynomial.eval₂Hom_congr (RingHom.ext fun a ↦ by simp) (funext fun v ↦ ?_) rfl
  cases v <;> simp

/-- Separants commute with mapping coefficients: the partial derivative in `Y_j` of `Q.map f` is
the map of the partial derivative of `Q`. -/
theorem map_separant [CommSemiring F] [CommSemiring E] (f : F →+* E)
    (Q : DifferentialPolynomial F d) (j : Fin (d + 1)) :
    MvPolynomial.map f (separant Q j) = separant (MvPolynomial.map f Q) j :=
  MvPolynomial.pderiv_map.symm

/-- An injective coefficient map preserves every individual jet degree. Injectivity is needed:
the map `ℤ →+* ZMod 2` sends `2 * Y₀` to `0`. -/
theorem jetDegree_map_eq [CommSemiring F] [CommSemiring E] {f : F →+* E}
    (hf : Function.Injective f) (Q : DifferentialPolynomial F d) (j : Fin (d + 1)) :
    jetDegree (MvPolynomial.map f Q) j = jetDegree Q j := by
  unfold jetDegree MvPolynomial.degreeOf
  rw [MvPolynomial.degrees_map_of_injective Q hf]

/-- An injective coefficient map preserves the total jet degree, since it preserves the support.
-/
theorem jetTotalDegree_map_eq [CommSemiring F] [CommSemiring E] {f : F →+* E}
    (hf : Function.Injective f) (Q : DifferentialPolynomial F d) :
    jetTotalDegree (MvPolynomial.map f Q) = jetTotalDegree Q := by
  unfold jetTotalDegree MvPolynomial.weightedTotalDegree
  rw [MvPolynomial.support_map_of_injective Q hf]

/-- Any coefficient map, injective or not, does not increase an individual jet degree. -/
theorem jetDegree_map_le [CommSemiring F] [CommSemiring E] (f : F →+* E)
    (Q : DifferentialPolynomial F d) (j : Fin (d + 1)) :
    jetDegree (MvPolynomial.map f Q) j ≤ jetDegree Q j :=
  MvPolynomial.degreeOf_le_iff.mpr fun _ hu ↦
    MvPolynomial.monomial_le_degreeOf (some j) (MvPolynomial.support_map_subset f Q hu)

/-- Any coefficient map sends an equation with no active jet to an equation with no active jet. -/
theorem highestActiveJet_map_eq_none [CommSemiring F] [CommSemiring E] (f : F →+* E)
    {Q : DifferentialPolynomial F d} (hQ : highestActiveJet Q = none) :
    highestActiveJet (MvPolynomial.map f Q) = none := by
  refine (highestActiveJet_eq_none_iff _).mpr fun j hj ↦ ?_
  have hlt : 0 < jetDegree Q j :=
    (show 0 < jetDegree (MvPolynomial.map f Q) j from hj).trans_le (jetDegree_map_le f Q j)
  exact (highestActiveJet_eq_none_iff Q).mp hQ j hlt

/-- An injective coefficient map preserves the cast hypothesis `JetDegreeCastsNeZero`: the jet
degree is unchanged, and `(k : E) = f k` vanishes exactly when `(k : F)` does. In particular,
passing from a field to an extension field cannot make the hypothesis true when it was false. -/
theorem jetDegreeCastsNeZero_map_iff [CommSemiring F] [CommSemiring E] {f : F →+* E}
    (hf : Function.Injective f) (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) :
    JetDegreeCastsNeZero (MvPolynomial.map f Q) s ↔ JetDegreeCastsNeZero Q s := by
  simp only [JetDegreeCastsNeZero, jetDegree_map_eq hf, ← map_natCast f, ne_eq,
    map_eq_zero_iff f hf]

/-! ### Bounded solutions -/

/-- Over a finite commutative semiring there are finitely many solutions of degree at most `D`:
a solution is determined by its `D + 1` coefficients. The degree bound is needed, since `F[X]`
is infinite whenever `F` is nontrivial. -/
instance BoundedSolution.instFinite [CommSemiring F] [Finite F] (Q : DifferentialPolynomial F d)
    (D : ℕ) : Finite (BoundedSolution Q D) :=
  have : Finite (Polynomial.degreeLT F (D + 1)) :=
    Finite.of_equiv _ (Polynomial.degreeLTEquiv F (D + 1)).toEquiv.symm
  Subtype.finite

/-- Map a solution of `Q = 0` of degree at most `D` along `f` to a solution of `Q.map f = 0` of
degree at most `D`. -/
def BoundedSolution.map [CommSemiring F] [CommSemiring E] (f : F →+* E)
    {Q : DifferentialPolynomial F d} {D : ℕ} (P : BoundedSolution Q D) :
    BoundedSolution (MvPolynomial.map f Q) D :=
  ⟨⟨P.polynomial.map f, Polynomial.mem_degreeLT.mpr
      (Polynomial.degree_map_le.trans_lt (Polynomial.mem_degreeLT.mp P.1.2))⟩, by
    change differentialSpecialization (MvPolynomial.map f Q) (P.polynomial.map f) = 0
    rw [← map_differentialSpecialization, P.equation, Polynomial.map_zero]⟩

/-- The polynomial of a mapped solution is the mapped polynomial. -/
@[simp]
theorem BoundedSolution.map_polynomial [CommSemiring F] [CommSemiring E] (f : F →+* E)
    {Q : DifferentialPolynomial F d} {D : ℕ} (P : BoundedSolution Q D) :
    (P.map f).polynomial = P.polynomial.map f :=
  rfl

/-- Mapping bounded solutions along an injective coefficient map is injective. -/
theorem BoundedSolution.map_injective [CommSemiring F] [CommSemiring E] {f : F →+* E}
    (hf : Function.Injective f) {Q : DifferentialPolynomial F d} {D : ℕ} :
    Function.Injective (BoundedSolution.map f : BoundedSolution Q D →
      BoundedSolution (MvPolynomial.map f Q) D) :=
  fun _ _ h ↦ Subtype.ext <| Subtype.ext <| Polynomial.map_injective f hf <|
    congrArg BoundedSolution.polynomial h

/-- `BoundedSolution.map` as an embedding, for an injective coefficient map. -/
def BoundedSolution.mapEmbedding [CommSemiring F] [CommSemiring E] {f : F →+* E}
    (hf : Function.Injective f) (Q : DifferentialPolynomial F d) (D : ℕ) :
    BoundedSolution Q D ↪ BoundedSolution (MvPolynomial.map f Q) D :=
  ⟨BoundedSolution.map f, BoundedSolution.map_injective hf⟩

/-- Along an injective map into a finite commutative semiring, `Q = 0` has at most as many
solutions of degree at most `D` as `Q.map f = 0`. Any bound on the solutions over a finite
extension field therefore bounds the solutions over the base field. The inequality can be strict:
`0 = 0` has more constant solutions over a larger field. -/
theorem BoundedSolution.natCard_le_natCard_map [CommSemiring F] [CommSemiring E] [Finite E]
    {f : F →+* E} (hf : Function.Injective f) (Q : DifferentialPolynomial F d) (D : ℕ) :
    Nat.card (BoundedSolution Q D) ≤ Nat.card (BoundedSolution (MvPolynomial.map f Q) D) :=
  Nat.card_le_card_of_injective _ (BoundedSolution.map_injective hf)

end

end PolynomialDifferential
