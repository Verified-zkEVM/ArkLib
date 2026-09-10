/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Ordinary.QuotientLift.Materialize
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Ordinary.QuotientLift.NewtonProof
public import ArkLib.Data.Polynomial.GCDSplit

-- The specialization bridge reduces the computable-polynomial semantic conversion.
import all CompPoly.Univariate.ToPoly.Core
import all CompPoly.Univariate.ToPoly.Equiv

/-!
# Initial slices of an ordinary bivariate equation

At a chosen center `c`, the univariate slice `Q(c,U)` contains every initial value `p(c)` of
a polynomial solution `Q(X,p(X))=0`. The slice is computed from the supplied sparse equation.
The accompanying identities relate its roots and the centered lifting equation to the original
polynomial substitution, so a constructor can establish coverage from its actual data.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.Ordinary.QuotientLift
open CompPoly CompPoly.CPolynomial
variable {E : Type*} [Field E] [BEq E] [LawfulBEq E]

/-- Compute the univariate initial-value equation `Q(center,U)`. -/
def sectionPolynomial (Q : CPoly.CMvPolynomial 2 E) (center : E) : CPolynomial E :=
  CPoly.CMvPolynomial.eval₂ CPolynomial.CHom ![CPolynomial.C center, CPolynomial.X] Q

noncomputable section
variable {L : Type*} [Field L]

/-- Specialization of the computed slice is evaluation of `Q` at the same center and value. -/
theorem eval₂_sectionPolynomial (ι : E →+* L) (θ : L)
    (Q : CPoly.CMvPolynomial 2 E) (center : E) :
    (sectionPolynomial Q center).toPoly.eval₂ ι θ =
      MvPolynomial.eval₂ ι ![ι center, θ] (CPoly.fromCMvPolynomial Q) := by
  change ((Polynomial.eval₂RingHom ι θ).comp CPolynomial.toPolyRingHom)
    (sectionPolynomial Q center) = _
  rw [sectionPolynomial, CPoly.eval₂_equiv, MvPolynomial.eval₂_comp_left]
  congr 1
  · ext a
    simp [CPolynomial.C_toPoly]
  · funext i
    fin_cases i <;> simp [CPolynomial.C_toPoly, CPolynomial.X_toPoly]

omit [BEq E] [LawfulBEq E] in
/-- Translating a polynomial solution to the chosen center gives the equation used by lifting. -/
theorem centered_solution (ι : E →+* L) (q : MvPolynomial (Fin 2) E)
    (P : Polynomial L) (center : L)
    (hsolution : MvPolynomial.eval₂ (Polynomial.C.comp ι) ![Polynomial.X, P] q = 0) :
    MvPolynomial.eval₂ (Polynomial.C.comp ι)
      ![Polynomial.X + Polynomial.C center, Polynomial.taylor center P] q = 0 := by
  have h := congrArg (Polynomial.taylorAlgHom center) hsolution
  change (Polynomial.taylorAlgHom center).toRingHom
    (MvPolynomial.eval₂ (Polynomial.C.comp ι) ![Polynomial.X, P] q) = _ at h
  rw [MvPolynomial.eval₂_comp_left] at h
  have hconst : (Polynomial.taylorAlgHom center).toRingHom.comp (Polynomial.C.comp ι) =
      Polynomial.C.comp ι := by
    ext a
    simp
  have hvariables : (Polynomial.taylorAlgHom center).toRingHom ∘ ![Polynomial.X, P] =
      ![Polynomial.X + Polynomial.C center, Polynomial.taylor center P] := by
    funext i
    fin_cases i <;> simp [Polynomial.taylor_X]
  simpa only [hconst, hvariables, map_zero] using h

omit [BEq E] [LawfulBEq E] in
/-- Every polynomial solution supplies a root of the initial-value slice at each center. -/
theorem solution_at_center (ι : E →+* L) (q : MvPolynomial (Fin 2) E)
    (P : Polynomial L) (center : L)
    (hsolution : MvPolynomial.eval₂ (Polynomial.C.comp ι) ![Polynomial.X, P] q = 0) :
    MvPolynomial.eval₂ ι ![center, P.eval center] q = 0 := by
  have h := congrArg (Polynomial.evalRingHom center) hsolution
  rw [MvPolynomial.eval₂_comp_left] at h
  have hconst : (Polynomial.evalRingHom center).comp (Polynomial.C.comp ι) = ι := by
    ext a
    simp
  have hvariables : Polynomial.evalRingHom center ∘ ![Polynomial.X, P] =
      ![center, P.eval center] := by
    funext i
    fin_cases i <;> simp
  simpa only [hconst, hvariables, map_zero] using h

/-- A polynomial solution whose initial value is a modulus root is represented by the actual
successful lift after materialization. This composes slice semantics, centered lifting, and
shift-back, without choosing or enumerating any other roots of the modulus. -/
theorem newtonLifted_represents_solution
    (ι : E →+* L) (Q : CPoly.CMvPolynomial 2 E) (center : E)
    (modulus : CPolynomial E) (hmonic : modulus.toPoly.Monic)
    (k : ℕ) (out : Series E)
    (hrun : newtonLift? Q center modulus k = some out)
    (P : Polynomial L) (hdegree : P.degree < k)
    (hroot : modulus.toPoly.eval₂ ι (P.eval (ι center)) = 0)
    (hsolution : MvPolynomial.eval₂ (Polynomial.C.comp ι) ![Polynomial.X, P]
      (CPoly.fromCMvPolynomial Q) = 0) :
    (materialize modulus center k out).Represents ι (P.eval (ι center)) P := by
  have hcentered := centered_solution ι (CPoly.fromCMvPolynomial Q) P (ι center) hsolution
  have hseries := newtonLift_specializes ι (P.eval (ι center)) Q center modulus
    ((CPolynomial.monic_toPoly_iff _).mpr hmonic) hroot k out hrun
    (Polynomial.taylor (ι center) P) (by simpa only [Polynomial.degree_taylor] using hdegree)
    (Polynomial.taylor_coeff_zero _ _) hcentered
  exact ⟨hroot, materialize_specialize ι (P.eval (ι center)) modulus center k out P
    hmonic hroot hseries hdegree⟩

end
end ReedSolomon.HiddenDerivative.Ordinary.QuotientLift
