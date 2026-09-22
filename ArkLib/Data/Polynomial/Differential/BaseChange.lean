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

## Main statements

* `map_differentialSpecialization`, `map_separant`: naturality of specialization and separants.
* `jetDegree_map_eq`, `jetDegreeCastsNeZero_map_iff`: injective coefficient maps preserve jet
  degrees and the cast hypothesis.
* `BoundedSolution.instFinite`: over a finite coefficient semiring there are finitely many
  solutions of degree at most `D`.
* `BoundedSolution.map`, `BoundedSolution.map_injective`, `BoundedSolution.natCard_le_natCard_map`:
  transport of bounded solutions and the cardinality comparison.

## References

Ported from `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/FiniteField/
Extension.lean` at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d. Nothing in it
mentions a code, so it lives in `PolynomialDifferential`.

* `map_differentialSpecialization`, `BoundedSolution.map`, `BoundedSolution.map_polynomial` and
  `BoundedSolution.map_injective` keep their statements. `mapDegreeLT` and
  `mapDegreeLT_polynomial` are inlined into `BoundedSolution.map`.
* `jetDegree_map_eq` keeps its statement. `isBelowCharacteristic_map_iff` becomes
  `jetDegreeCastsNeZero_map_iff`, since `IsBelowCharacteristic` was replaced by
  `JetDegreeCastsNeZero` in P1; it holds for any injective map of commutative semirings instead
  of an algebra map of fields. The degree part `D < ringChar F` of the source guard is replaced in
  the root counts by binomial-cast hypotheses, which transport along any injective ring
  homomorphism by `map_natCast`.
* `BoundedSolution.instFinite` is generalized from finite fields to finite commutative semirings.
* `BoundedSolution.algebraMapEmbedding` and `BoundedSolution.natCard_le_extension` become
  `BoundedSolution.mapEmbedding` and `BoundedSolution.natCard_le_natCard_map` for any injective
  ring homomorphism into a finite commutative semiring. `natCard_le_of_extension_bound` and
  `finset_card_le_extension` are one-line consequences (of `Nat.le_trans` and
  `Finset.card_le_card_of_injOn` with `BoundedSolution.map_injective`) and are derived in the
  tests rather than restated.
* The source's `ArkLib/ToMathlib/FieldTheory/FiniteExtension.lean` is not ported. Mathlib's
  `FiniteField.Extension`, `FiniteField.natCard_extension`, `FiniteField.finrank_extension`,
  `Algebra.ringChar_eq` and `charP_of_injective_algebraMap` cover its facts, and its
  bound-dependent choice `ExtensionAbove` has no consumer at that revision: the extension root
  counts use `FiniteField.Extension F (ringChar F) e` for a fixed degree `e`.

Deferred: the root counts over extension fields that consume these transports.
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
