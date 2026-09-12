/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerRepresentation
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Tower agreement residuals and descent

The `RecoverAgreement` residual is computed from the stored coefficients without selecting
geometric points. Its interpretation tests agreement at every point simultaneously. Once a
component records `k` positions, polynomial interpolation proves descent to the original field.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.TowerRepresentation

open CompPoly Polynomial Polynomial.JetHornerMachine
open FirstOrderNormDecoder.D5

variable {E : Type*} [Field E] [BEq E] [LawfulBEq E]

/-- Evaluate the descending message coefficient vector at a supplied field element. The result
is a nested polynomial; the splitter subsequently reduces it in the current quotient tower. -/
def evaluateCoefficients (x : E) : List (CPolynomial (CPolynomial E)) →
    CPolynomial (CPolynomial E)
  | [] => 0
  | c :: cs => c * CPolynomial.C (CPolynomial.C (x ^ cs.length)) + evaluateCoefficients x cs

/-- Compute `C(x)-y` as a nested polynomial representative for the agreement scan. -/
def residual (r : TowerRepresentation (F := E)) (x y : E) :
    CPolynomial (CPolynomial E) :=
  evaluateCoefficients x r.coefficients - CPolynomial.C (CPolynomial.C y)

noncomputable section

variable {L : Type*} [Field L]

/-- Nested evaluation is a ring homomorphism, so arithmetic on stored representatives has its
ordinary value at every geometric point. -/
def evaluationHom (ι : E →+* L) (u v : L) : CPolynomial (CPolynomial E) →+* L :=
  (Polynomial.evalRingHom v).comp
    ((Polynomial.mapRingHom (coefficientEval ι u)).comp CPolynomial.toPolyRingHom)

/-- The ring-homomorphism presentation is exactly the tower's existing point evaluation. -/
theorem evaluationHom_apply (ι : E →+* L) (u v : L)
    (p : CPolynomial (CPolynomial E)) :
    evaluationHom ι u v p = evalNested p ι u v := by
  simp [evaluationHom, evalNested, specializeFiberCPolynomial,
    CPolynomial.toPolyRingHom_apply]

/-- Coefficient width bounds every specialized message, including zero and leading cancellation. -/
theorem degree_specialize_lt (r : TowerRepresentation (F := E)) (ι : E →+* L)
    (u v : L) {k : ℕ} (hw : r.coefficients.length = k) :
    (r.specialize ι u v).degree < k := by
  simpa only [specialize, List.length_map, hw] using
    degree_coefficientPolynomial_lt_length
      (r.coefficients.map fun c => evalNested c ι u v)

/-- Evaluating in the message variable commutes with evaluation at a tower point. -/
theorem evaluateCoefficients_specialize (cs : List (CPolynomial (CPolynomial E)))
    (ι : E →+* L) (u v : L) (x : E) :
    evalNested (evaluateCoefficients x cs) ι u v =
      (coefficientPolynomial (cs.map fun c => evalNested c ι u v)).eval (ι x) := by
  induction cs with
  | nil =>
      simp [evaluateCoefficients, evalNested, specializeFiberCPolynomial,
        coefficientPolynomial, CPolynomial.toPoly_zero]
  | cons c cs ih =>
      simp only [evaluateCoefficients, ← evaluationHom_apply, map_add, map_mul]
      rw [evaluationHom_apply _ _ _ (evaluateCoefficients x cs), ih]
      simp [evaluationHom, coefficientEval, CPolynomial.toPolyRingHom_apply,
        coefficientPolynomial_cons, evalNested, specializeFiberCPolynomial,
        CPolynomial.C_toPoly, Polynomial.eval₂_pow]

/-- A raw residual has the expected agreement value; reduction and tower restriction can
therefore be proved separately from message evaluation. -/
theorem residual_specialize (r : TowerRepresentation (F := E)) (ι : E →+* L)
    (u v : L) (x y : E) :
    evalNested (r.residual x y) ι u v = (r.specialize ι u v).eval (ι x) - ι y := by
  rw [residual, ← evaluationHom_apply, map_sub, evaluationHom_apply,
    evaluateCoefficients_specialize]
  simp [specialize, evaluationHom, coefficientEval, CPolynomial.toPolyRingHom_apply,
    CPolynomial.C_toPoly]

/-- Zero/unit splitting by this residual tests exactly agreement with the received pair. -/
theorem residual_eq_zero_iff (r : TowerRepresentation (F := E)) (ι : E →+* L)
    (u v : L) (x y : E) :
    evalNested (r.residual x y) ι u v = 0 ↔ (r.specialize ι u v).eval (ι x) = ι y := by
  rw [residual_specialize, sub_eq_zero]

/-- At `k` distinct shared positions, every specialized tower message equals the interpolation
polynomial over the original base field. This is the descent step in `RecoverAgreement`; no
extension-field coefficient membership test or root extraction is executed. -/
theorem specialize_eq_base_map_of_shared_agreements {F I : Type*} [Field F]
    (r : TowerRepresentation (F := E)) (base : F →+* E) (ι : E →+* L) (u v : L)
    (positions : Finset I) (domain received : I → F)
    (hdomain : Set.InjOn domain positions)
    (hwidth : r.coefficients.length = positions.card) (p : F[X])
    (hdegree : p.degree < positions.card)
    (hp : ∀ i ∈ positions, p.eval (domain i) = received i)
    (hpoint : ∀ i ∈ positions,
      (r.specialize ι u v).eval (ι (base (domain i))) = ι (base (received i))) :
    r.specialize ι u v = p.map (ι.comp base) := by
  apply Polynomial.eq_of_degrees_lt_of_eval_index_eq positions
    (v := fun i => (ι.comp base) (domain i))
  · intro i hi j hj heq
    exact hdomain hi hj ((ι.comp base).injective heq)
  · exact degree_specialize_lt r ι u v hwidth
  · exact Polynomial.degree_map_le.trans_lt hdegree
  · intro i hi
    rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hp i hi]
    exact hpoint i hi

/-- Every retained positive-dimensional tower has a geometric point in an algebraically closed
extension. The witnesses are proof-only; recovery interpolates without computing either root. -/
theorem exists_point [IsAlgClosed L] (r : TowerRepresentation (F := E))
    (ι : E →+* L) {k : ℕ} (hr : r.WellFormed k) :
    ∃ u v : L, r.Point ι u v := by
  have hG : r.modulus.toPoly.degree ≠ 0 := by
    apply ne_of_gt
    rw [← Polynomial.natDegree_pos_iff_degree_pos]
    simpa only [CPolynomial.natDegree_toPoly] using hr.2.2.1
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_eval₂_eq_zero_of_injective
    ι ι.injective r.modulus.toPoly hG
  have hhmonic : r.fiber.toPoly.Monic := (CPolynomial.monic_toPoly_iff _).mp hr.2.2.2.1
  have hh : (specializeFiberCPolynomial r.fiber ι u).degree ≠ 0 := by
    apply ne_of_gt
    rw [← Polynomial.natDegree_pos_iff_degree_pos, specializeFiberCPolynomial,
      hhmonic.natDegree_map]
    simpa only [CPolynomial.natDegree_toPoly] using hr.2.2.2.2.1
  obtain ⟨v, hv⟩ := IsAlgClosed.exists_root (specializeFiberCPolynomial r.fiber ι u) hh
  exact ⟨u, v, hu, hv⟩

end
end ReedSolomon.ListDecoding.TowerRepresentation
