/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Ordinary.QuotientLift.Semantics
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FiniteRepresentation
public import ArkLib.Data.Polynomial.CoefficientList
public import CompPoly.Univariate.Deriv

/-!
# Materializing a quotient lift for agreement recovery

The lifting variable is centered: a recovered branch is `p(center+T)`. Recovery expects the
original message `p(X)`. We therefore shift by `-center`, extract exactly `k` ascending
coefficients, reduce each modulo `h`, and reverse them into the output convention.

Reduction includes the constant coefficient. This matters even for linear moduli, where the
initial parameter polynomial `U` is not itself reduced. Specialization at a root of `h` is
unchanged by every reduction, so the resulting finite representation still covers the message.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.Ordinary.QuotientLift
open CompPoly CompPoly.CPolynomial
variable {E : Type*} [Field E] [BEq E] [LawfulBEq E]

/-- Shift back to the message variable and store exactly `k` reduced descending coefficients. -/
def materialize (modulus : CPolynomial E) (center : E) (k : ℕ) (series : Series E) :
    ReedSolomon.ListDecoding.FiniteRepresentation E :=
  let : DecidableEq (CPolynomial E) := instDecidableEqOfLawfulBEq
  let unshifted := CPolynomial.taylor (-CPolynomial.C center) series
  ⟨modulus, (List.ofFn fun i : Fin k => (unshifted.coeff i).modByMonic modulus).reverse⟩

/-- Monic squarefree moduli yield well-formed representation data after materialization. -/
theorem materialize_wellFormed (modulus : CPolynomial E) (center : E) (k : ℕ)
    (series : Series E) (hmonic : modulus.toPoly.Monic) (hfree : Squarefree modulus.toPoly) :
    (materialize modulus center k series).WellFormed k := by
  refine ⟨hmonic, hfree, ?_, ?_⟩
  · simp [materialize]
  · intro c hc
    simp only [materialize, List.mem_reverse, List.mem_ofFn] at hc
    obtain ⟨i, rfl⟩ := hc
    rw [modByMonic_toPoly_eq_modByMonic _ _ ((monic_toPoly_iff _).mpr hmonic)]
    exact Polynomial.degree_modByMonic_lt _ hmonic

noncomputable section
variable {L : Type*} [Field L]

/-- Specializing the parameter commutes with the executable shift back to the message variable. -/
theorem specialize_taylor (ι : E →+* L) (θ : L) (series : Series E) (center : E) :
    let : DecidableEq (CPolynomial E) := instDecidableEqOfLawfulBEq
    specialize ι θ (CPolynomial.taylor (-CPolynomial.C center) series) =
      Polynomial.taylor (-ι center) (specialize ι θ series) := by
  let : DecidableEq (CPolynomial E) := instDecidableEqOfLawfulBEq
  change Polynomial.map _ _ = Polynomial.taylor _ (Polynomial.map _ _)
  simp only [CPolynomial.toPolyRingHom_apply]
  rw [CPolynomial.taylor_toPoly, Polynomial.map_taylor]
  congr 1
  simp [toPoly_neg, CPolynomial.C_toPoly]

/-- A centered lift of a degree-`< k` message becomes precisely that message after shifting,
coefficient materialization, and reduction. No extension-field coefficients are extracted. -/
theorem materialize_specialize (ι : E →+* L) (θ : L) (modulus : CPolynomial E)
    (center : E) (k : ℕ) (series : Series E) (P : Polynomial L)
    (hmonic : modulus.toPoly.Monic) (hroot : modulus.toPoly.eval₂ ι θ = 0)
    (hseries : specialize ι θ series = Polynomial.taylor (ι center) P)
    (hdegree : P.degree < k) :
    (materialize modulus center k series).specialize ι θ = P := by
  let : DecidableEq (CPolynomial E) := instDecidableEqOfLawfulBEq
  let unshifted := CPolynomial.taylor (-CPolynomial.C center) series
  have hunshift : specialize ι θ unshifted = P := by
    rw [specialize_taylor, hseries, Polynomial.taylor_taylor, neg_add_cancel,
      Polynomial.taylor_zero]
  change Polynomial.JetHornerMachine.coefficientPolynomial
    (((List.ofFn fun i : Fin k => (unshifted.coeff i).modByMonic modulus).reverse).map
      (fun c => c.toPoly.eval₂ ι θ)) = P
  rw [List.map_reverse]
  change Polynomial.CoefficientList.ascendingPolynomial
    ((List.ofFn fun i : Fin k => (unshifted.coeff i).modByMonic modulus).map
      (fun c => c.toPoly.eval₂ ι θ)) = P
  rw [List.map_ofFn]
  have hcoeff : (fun i : Fin k =>
      ((unshifted.coeff i).modByMonic modulus).toPoly.eval₂ ι θ) =
        (fun i : Fin k => P.coeff i) := by
    funext i
    rw [modByMonic_toPoly_eq_modByMonic _ _ ((monic_toPoly_iff _).mpr hmonic),
      Polynomial.eval₂_modByMonic_eq_self_of_root hroot, ← coeff_specialize, hunshift]
  change Polynomial.CoefficientList.ascendingPolynomial (List.ofFn
    (fun i : Fin k => ((unshifted.coeff i).modByMonic modulus).toPoly.eval₂ ι θ)) = P
  rw [hcoeff]
  exact Polynomial.CoefficientList.ascendingPolynomial_ofFn k P hdegree

end
end ReedSolomon.HiddenDerivative.Ordinary.QuotientLift
