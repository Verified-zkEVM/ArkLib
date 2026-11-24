/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound
public import ArkLib.ProofSystem.Sumcheck.Spec.PolynomialInterface
public import ArkLib.ProofSystem.Sumcheck.Impl.IndexedProjection

/-!
# Computable honest sum-check round polynomials for injective domains

`Sumcheck.Impl.IndexedProjection` owns the enumeration of suffix domain indices on CompPoly's
carriers. This module specializes it to an injective domain `D : Fin m ↪ R`, where the indexed sum
equals the finite-set sum of `Sumcheck.Spec`, and relates the result to the legacy specification.

The mathematical polynomial maps appear only in the correspondence proofs.
-/

@[expose] public section

open CPoly CompPoly Finset Polynomial MvPolynomial
open CPoly.CMvPolynomial

namespace Sumcheck.Impl.Computable

variable {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
  {n m : ℕ}

/-- Enumerate suffixes by their domain indices, avoiding any choice of preimages. -/
def suffixEmbedding (D : Fin m ↪ R) (k : ℕ) : (Fin k → Fin m) ↪ (Fin k → R) where
  toFun x := D ∘ x
  inj' := by
    intro x y h
    funext j
    exact D.injective (congrFun h j)

omit [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R] in
/-- The explicit enumeration covers exactly the finite domain power in the specification. -/
theorem suffixDomain_eq (D : Fin m ↪ R) (k : ℕ) :
    (Finset.univ.map (suffixEmbedding D k)) = (Finset.univ.map D) ^ᶠ k := by
  classical
  ext x
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Fintype.mem_piFinset]
  constructor
  · rintro ⟨y, rfl⟩ j
    exact ⟨y j, rfl⟩
  · intro h
    choose y hy using h
    exact ⟨y, funext hy⟩

/-- The honest round polynomial for an injective domain: the indexed enumeration
`indexedRoundPolynomial` at the embedding's underlying map. -/
def projectedRoundPolynomial (D : Fin m ↪ R) (i : Fin (n + 1))
    (challenges : Fin i.castSucc → R) (poly : CMvPolynomial (n + 1) R) : CPolynomial R :=
  indexedRoundPolynomial D i challenges poly

/-- The computational finite sum agrees with the mathematical finite-domain construction. -/
theorem projectedRoundPolynomial_toPoly_sum (D : Fin m ↪ R) (i : Fin (n + 1))
    (challenges : Fin i.castSucc → R) (poly : CMvPolynomial (n + 1) R) :
    (projectedRoundPolynomial D i challenges poly).toPoly =
      (∑ x ∈ (Finset.univ.map D) ^ᶠ (n - i),
        (CPoly.fromCMvPolynomial poly).evalExcept i
          (Spec.SingleRound.roundSuffix R (n + 1) i challenges x)) := by
  classical
  rw [projectedRoundPolynomial, indexedRoundPolynomial_toPoly, ← suffixDomain_eq D (n - i),
    Finset.sum_map]
  rfl

/-- Exact correspondence to the existing honest projected-round polynomial. -/
theorem projectedRoundPolynomial_toPoly (D : Fin m ↪ R) (i : Fin (n + 1))
    (challenges : Fin i.castSucc → R) (poly : CMvPolynomial (n + 1) R)
    {deg : ℕ} (specPoly : R⦃≤ deg⦄[X Fin (n + 1)])
    (hpoly : CPoly.fromCMvPolynomial poly = specPoly.val) :
    (projectedRoundPolynomial D i challenges poly).toPoly =
      (Spec.SingleRound.projectedRoundPolynomial R (n + 1) deg D i challenges specPoly).val := by
  rw [projectedRoundPolynomial_toPoly_sum, hpoly]
  rfl

/-- Individual degree bounds on the input bound the degree of each honest round message. -/
theorem projectedRoundPolynomial_natDegree_le (D : Fin m ↪ R) (i : Fin (n + 1))
    (challenges : Fin i.castSucc → R) (poly : CMvPolynomial (n + 1) R)
    {deg : ℕ} (hpoly : ∀ j, poly.degreeOf j ≤ deg) :
    (projectedRoundPolynomial D i challenges poly).natDegree ≤ deg :=
  indexedRoundPolynomial_natDegree_le D i challenges poly hpoly

/-- Individual degree bounds also bound the extended natural degree used by messages. -/
theorem projectedRoundPolynomial_degree_le (D : Fin m ↪ R) (i : Fin (n + 1))
    (challenges : Fin i.castSucc → R) (poly : CMvPolynomial (n + 1) R)
    {deg : ℕ} (hpoly : ∀ j, poly.degreeOf j ≤ deg) :
    (projectedRoundPolynomial D i challenges poly).degree ≤ (deg : WithBot ℕ) :=
  indexedRoundPolynomial_degree_le D i challenges poly hpoly

/-- Package the actual finite-enumeration result as a degree-bounded native message. -/
def projectedRoundMessage (D : Fin m ↪ R) (i : Fin (n + 1))
    (challenges : Fin i.castSucc → R) (poly : CMvPolynomial (n + 1) R)
    {deg : ℕ} (hpoly : ∀ j, poly.degreeOf j ≤ deg) : Representation.Message R deg :=
  indexedRoundMessage D i challenges poly hpoly

/-- The bounded native message is exactly the honest message of the existing specification. -/
theorem projectedRoundMessage_toMessage (D : Fin m ↪ R) (i : Fin (n + 1))
    (challenges : Fin i.castSucc → R) (poly : CMvPolynomial (n + 1) R)
    {deg : ℕ} (hpoly : ∀ j, poly.degreeOf j ≤ deg)
    (specPoly : R⦃≤ deg⦄[X Fin (n + 1)])
    (hinterpret : CPoly.fromCMvPolynomial poly = specPoly.val) :
    Representation.toMessage R deg (projectedRoundMessage D i challenges poly hpoly) =
        Spec.SingleRound.projectedRoundPolynomial R (n + 1) deg D i challenges specPoly := by
  apply Subtype.ext
  rw [Representation.toMessage_val]
  exact projectedRoundPolynomial_toPoly D i challenges poly specPoly hinterpret

/-- Runtime Horner evaluation of the constructed message agrees with the honest spec answer. -/
theorem projectedRoundMessage_evaluate (D : Fin m ↪ R) (i : Fin (n + 1))
    (challenges : Fin i.castSucc → R) (poly : CMvPolynomial (n + 1) R)
    {deg : ℕ} (hpoly : ∀ j, poly.degreeOf j ≤ deg)
    (specPoly : R⦃≤ deg⦄[X Fin (n + 1)])
    (hinterpret : CPoly.fromCMvPolynomial poly = specPoly.val) (r : R) :
    Representation.evaluate R deg (projectedRoundMessage D i challenges poly hpoly) r =
      (Spec.SingleRound.projectedRoundPolynomial R (n + 1) deg D i challenges
        specPoly).val.eval r := by
  rw [Representation.evaluate_eq,
    projectedRoundMessage_toMessage D i challenges poly hpoly specPoly hinterpret]

omit [Nontrivial R] in
/-- Construct computational input data from the explicitly supported bounded polynomial. -/
def fromOracleStatement {deg : ℕ} (poly : Spec.OracleStatement R n deg ()) :
    CMvPolynomial n R :=
  poly.val.coeff.support.sum fun mon =>
    CMvPolynomial.monomial (CMvMonomial.ofFinsupp mon) (poly.val.coeff.toFun mon)

omit [Nontrivial R] in
/-- The computational input has exactly the specified polynomial interpretation. -/
theorem fromOracleStatement_interpretation {deg : ℕ}
    (poly : Spec.OracleStatement R n deg ()) :
    CPoly.fromCMvPolynomial (fromOracleStatement poly) = poly.val := by
  classical
  unfold fromOracleStatement
  rw [fromCMvPolynomial_sum]
  simp_rw [fromCMvPolynomial_monomial, CMvMonomial.toFinsupp_ofFinsupp]
  exact MvPolynomial.support_sum_monomial_coeff poly.val

omit [Nontrivial R] in
/-- The computational input inherits every individual degree bound of its statement. -/
theorem fromOracleStatement_degreeOf_le {deg : ℕ}
    (poly : Spec.OracleStatement R n deg ()) (j : Fin n) :
    (fromOracleStatement poly).degreeOf j ≤ deg := by
  rw [congrFun (CPoly.degreeOf_equiv (S := R) (p := fromOracleStatement poly)) j,
    fromOracleStatement_interpretation]
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro mon hmon
  exact (MvPolynomial.mem_restrictDegree (Fin n) _ deg).mp poly.property mon hmon j

omit [Nontrivial R] in
/-- Mathematical interpretation of a computational polynomial with an individual degree bound,
as the specification's oracle statement. -/
def toOracleStatement (poly : CMvPolynomial n R) {deg : ℕ}
    (hpoly : ∀ j, poly.degreeOf j ≤ deg) : Spec.OracleStatement R n deg () :=
  toRestrictDegree poly hpoly

/-- Total round-message construction for an arbitrary variable count: `indexedMessage` at the
embedding's underlying map. -/
def projectedMessage (D : Fin m ↪ R) {n : ℕ} (i : Fin n)
    (challenges : Fin i.castSucc → R) (poly : CMvPolynomial n R)
    {deg : ℕ} (hpoly : ∀ j, poly.degreeOf j ≤ deg) : Representation.Message R deg :=
  indexedMessage D i challenges poly hpoly

/-- The total constructor interprets to exactly the existing projected honest message. -/
theorem projectedMessage_toMessage (D : Fin m ↪ R) {n : ℕ} (i : Fin n)
    (challenges : Fin i.castSucc → R) (poly : CMvPolynomial n R)
    {deg : ℕ} (hpoly : ∀ j, poly.degreeOf j ≤ deg) :
    Representation.toMessage R deg (projectedMessage D i challenges poly hpoly) =
      Spec.SingleRound.projectedRoundPolynomial R n deg D i challenges
        (toOracleStatement poly hpoly) := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    exact projectedRoundMessage_toMessage D i challenges poly hpoly
      (toOracleStatement poly hpoly) rfl

/-- The total constructor answers each query as the corresponding mathematical honest message. -/
theorem projectedMessage_evaluate (D : Fin m ↪ R) {n : ℕ} (i : Fin n)
    (challenges : Fin i.castSucc → R) (poly : CMvPolynomial n R)
    {deg : ℕ} (hpoly : ∀ j, poly.degreeOf j ≤ deg) (r : R) :
    Representation.evaluate R deg (projectedMessage D i challenges poly hpoly) r =
      (Spec.SingleRound.projectedRoundPolynomial R n deg D i challenges
        (toOracleStatement poly hpoly)).val.eval r := by
  rw [Representation.evaluate_eq, projectedMessage_toMessage]

omit [BEq R] [LawfulBEq R] [Nontrivial R] in
/-- Direct original-polynomial oracle behavior. Every answer evaluates the computational
multivariate data; no mathematical polynomial is reconstructed at runtime. -/
def inputImpl (poly : CMvPolynomial n R) (deg : ℕ) :
    (Spec.polynomialFamily R n deg).Behavior :=
  fun query => (poly.eval query.2 : R)

omit [BEq R] [LawfulBEq R] [Nontrivial R] in
/-- The direct original handler realizes exactly the mathematical interpretation of its data. -/
theorem inputImpl_eq_behavior (poly : CMvPolynomial n R) {deg : ℕ}
    (hpoly : ∀ j, poly.degreeOf j ≤ deg) :
    inputImpl poly deg =
      (Spec.polynomialFamily R n deg).behaviorOfRealizations
        (fun _ => toOracleStatement poly hpoly) := by
  funext query
  change poly.eval query.2 = MvPolynomial.eval query.2 (CPoly.fromCMvPolynomial poly)
  exact eval_equiv

end Sumcheck.Impl.Computable
