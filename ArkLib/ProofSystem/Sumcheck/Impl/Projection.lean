/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound
public import ArkLib.ProofSystem.Sumcheck.Interaction.MultivariateRound
public import ArkLib.ProofSystem.Sumcheck.Impl.Representation
public import CompPoly.Multivariate.FinSuccEquiv
public import CompPoly.Multivariate.Eval
public import CompPoly.Univariate.ToPoly.RingHom

/-!
# Computable honest sum-check round polynomials

The honest message is constructed directly on CompPoly's polynomial carriers by splitting the
round variable, evaluating the coefficients, and summing over an explicit finite enumeration of
suffix domain indices. The construction supports arbitrary individual degree bounds and arbitrary
finite domains. It is a direct enumeration and makes no running-time claim.

The mathematical polynomial maps appear only in the correspondence proofs.
-/

@[expose] public section

open CPoly CompPoly Finset Polynomial MvPolynomial
open CPoly.CMvPolynomial

namespace Sumcheck.Impl.Computable

variable {R : Type} [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
  {n m : ℕ}

/-- Append prior challenges to a domain suffix after omitting the round's pivot. -/
def roundSuffix (i : Fin (n + 1)) (challenges : Fin i.castSucc → R)
    (x : Fin (n - i) → R) : Fin n → R :=
  Fin.append challenges x ∘ Fin.cast (by simp; omega)

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

/-- Direct finite enumeration of the honest round polynomial on computable polynomial data.
This construction accepts arbitrary individual degrees and arbitrary finite domains. -/
def projectedRoundPolynomial (D : Fin m ↪ R) (i : Fin (n + 1))
    (challenges : Fin i.castSucc → R) (poly : CMvPolynomial (n + 1) R) : CPolynomial R :=
  ∑ x : Fin (n - i) → Fin m,
    CPolynomial.mapRingHom (evalHom (roundSuffix i challenges (D ∘ x)))
      (finSuccEquivNth i poly)

omit [Nontrivial R] in
/-- Transport coefficient evaluation to mathematical multivariate evaluation. -/
theorem evalHom_transport (v : Fin n → R) :
    evalHom v = (MvPolynomial.eval v).comp (CPoly.polyRingEquiv (n := n) (R := R)).toRingHom := by
  ext p
  simp [eval_equiv, CPoly.coe_polyRingEquiv]

/-- Each computational summand has precisely the polynomial interpretation used by the spec. -/
theorem projectedSummand_toPoly (i : Fin (n + 1)) (poly : CMvPolynomial (n + 1) R)
    (v : Fin n → R) :
    (CPolynomial.mapRingHom (evalHom v) (finSuccEquivNth i poly)).toPoly =
      Polynomial.map (MvPolynomial.eval v)
        (MvPolynomial.finSuccEquivNth R i (CPoly.fromCMvPolynomial poly)) := by
  rw [CPolynomial.toPoly_mapRingHom, evalHom_transport, ← Polynomial.map_map]
  rw [CPoly.CMvPolynomial.finSuccEquivNth_apply, map_polyRingEquiv_toPoly_finSuccEquivNth]

/-- Interpretation commutes with a finite sum of computational messages. -/
theorem toPoly_sum {ι : Type*} (s : Finset ι) (f : ι → CPolynomial R) :
    (∑ x ∈ s, f x).toPoly = ∑ x ∈ s, (f x).toPoly := by
  simpa only [CPolynomial.toPolyRingHom_apply] using
    map_sum (CPolynomial.toPolyRingHom (R := R)) f s

/-- The computational finite sum agrees with the mathematical finite-domain construction. -/
theorem projectedRoundPolynomial_toPoly_sum (D : Fin m ↪ R) (i : Fin (n + 1))
    (challenges : Fin i.castSucc → R) (poly : CMvPolynomial (n + 1) R) :
    (projectedRoundPolynomial D i challenges poly).toPoly =
      ∑ x ∈ (Finset.univ.map D) ^ᶠ (n - i),
        Polynomial.map (MvPolynomial.eval (Spec.SingleRound.roundSuffix R n i challenges x))
          (MvPolynomial.finSuccEquivNth R i (CPoly.fromCMvPolynomial poly)) := by
  classical
  unfold projectedRoundPolynomial
  rw [toPoly_sum]
  simp_rw [projectedSummand_toPoly]
  rw [← suffixDomain_eq D (n - i), Finset.sum_map]
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
    (projectedRoundPolynomial D i challenges poly).natDegree ≤ deg := by
  classical
  rw [CPolynomial.natDegree_toPoly]
  unfold projectedRoundPolynomial
  rw [toPoly_sum]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro x _
  rw [← CPolynomial.natDegree_toPoly]
  exact (CPolynomial.natDegree_mapRingHom_le _ _).trans
    (by simpa only [CPoly.CMvPolynomial.finSuccEquivNth_apply] using
      natDegree_finSuccEquivNthHom_le i poly hpoly)

/-- Individual degree bounds also bound the extended natural degree used by messages. -/
theorem projectedRoundPolynomial_degree_le (D : Fin m ↪ R) (i : Fin (n + 1))
    (challenges : Fin i.castSucc → R) (poly : CMvPolynomial (n + 1) R)
    {deg : ℕ} (hpoly : ∀ j, poly.degreeOf j ≤ deg) :
    (projectedRoundPolynomial D i challenges poly).degree ≤ (deg : WithBot ℕ) := by
  rw [CPolynomial.degree_toPoly]
  apply Polynomial.natDegree_le_iff_degree_le.mp
  rw [← CPolynomial.natDegree_toPoly]
  exact projectedRoundPolynomial_natDegree_le D i challenges poly hpoly

/-- Package the actual finite-enumeration result as a degree-bounded native message. -/
def projectedRoundMessage (D : Fin m ↪ R) (i : Fin (n + 1))
    (challenges : Fin i.castSucc → R) (poly : CMvPolynomial (n + 1) R)
    {deg : ℕ} (hpoly : ∀ j, poly.degreeOf j ≤ deg) : Representation.Message R deg :=
  ⟨projectedRoundPolynomial D i challenges poly,
    projectedRoundPolynomial_degree_le D i challenges poly hpoly⟩

/-- The bounded native message is exactly the honest message of the existing specification. -/
theorem projectedRoundMessage_toMessage (D : Fin m ↪ R) (i : Fin (n + 1))
    (challenges : Fin i.castSucc → R) (poly : CMvPolynomial (n + 1) R)
    {deg : ℕ} (hpoly : ∀ j, poly.degreeOf j ≤ deg)
    (specPoly : R⦃≤ deg⦄[X Fin (n + 1)])
    (hinterpret : CPoly.fromCMvPolynomial poly = specPoly.val) :
    Representation.toMessage R deg (projectedRoundMessage D i challenges poly hpoly) =
      Spec.SingleRound.projectedRoundPolynomial R (n + 1) deg D i challenges specPoly := by
  apply Subtype.ext
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
/-- Mathematical interpretation of a computational polynomial with an individual degree bound.
This map is used only in proofs; it is never part of the honest prover's runtime computation. -/
noncomputable def toOracleStatement (poly : CMvPolynomial n R) {deg : ℕ}
    (hpoly : ∀ j, poly.degreeOf j ≤ deg) : Spec.OracleStatement R n deg () :=
  ⟨CPoly.fromCMvPolynomial poly, by
    apply (MvPolynomial.mem_restrictDegree (Fin n) _ deg).mpr
    intro mon hmon j
    apply MvPolynomial.degreeOf_le_iff.mp _ mon hmon
    rw [← congrFun (CPoly.degreeOf_equiv (S := R) (p := poly)) j]
    exact hpoly j⟩

/-- Total round-message construction for an arbitrary variable count. There is no round at zero
variables, so the empty case is eliminated by its impossible round index. -/
def projectedMessage (D : Fin m ↪ R) {n : ℕ} (i : Fin n)
    (challenges : Fin i.castSucc → R) (poly : CMvPolynomial n R)
    {deg : ℕ} (hpoly : ∀ j, poly.degreeOf j ≤ deg) : Representation.Message R deg :=
  match n, i, challenges, poly, hpoly with
  | 0, i, _, _, _ => i.elim0
  | _ + 1, i, challenges, poly, hpoly => projectedRoundMessage D i challenges poly hpoly

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
    (Interaction.MultivariateRound.polynomialFamily R n deg).Behavior :=
  fun query => (poly.eval query.2 : R)

omit [BEq R] [LawfulBEq R] [Nontrivial R] in
/-- The direct original handler realizes exactly the mathematical interpretation of its data. -/
theorem inputImpl_eq_behavior (poly : CMvPolynomial n R) {deg : ℕ}
    (hpoly : ∀ j, poly.degreeOf j ≤ deg) :
    inputImpl poly deg =
      (Interaction.MultivariateRound.polynomialFamily R n deg).behaviorOfRealizations
        (fun _ => toOracleStatement poly hpoly) := by
  funext query
  change poly.eval query.2 = MvPolynomial.eval query.2 (CPoly.fromCMvPolynomial poly)
  exact eval_equiv

end Sumcheck.Impl.Computable
