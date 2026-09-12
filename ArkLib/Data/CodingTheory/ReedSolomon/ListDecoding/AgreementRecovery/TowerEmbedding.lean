/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.TowerEvaluation

/-!
# Univariate families as towers

The original representation `E[U]/G` embeds as `(E[U]/G)[V]/V`. Coefficients become constants
in `V`. This adapter preserves represented messages and lets the common tower recovery consume
univariate Rojas parameter families without choosing a primitive element or extracting roots.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.TowerRepresentation

open CompPoly Polynomial Polynomial.JetHornerMachine FirstOrderNormDecoder.D5

variable {E : Type*} [Field E] [BEq E] [LawfulBEq E]

/-- Embed a univariate parameter family using the degree-one fiber `V`. Constant base moduli
remain empty and must be removed before forming a retained `WellFormed` tower. -/
def ofUnivariate (r : FiniteRepresentation E) : TowerRepresentation (F := E) :=
  ⟨r.modulus, CPolynomial.X, r.coefficients.map CPolynomial.C⟩

/-- The degree-one fiber specializes to the same variable over every extension field. -/
theorem specializeFiber_X {L : Type*} [Field L] (ι : E →+* L) (u : L) :
    specializeFiberCPolynomial (CPolynomial.X : CPolynomial (CPolynomial E)) ι u =
      Polynomial.X := by
  simp [specializeFiberCPolynomial, CPolynomial.X_toPoly]

/-- Points of the embedded tower are exactly the original base roots paired with `v = 0`. -/
theorem ofUnivariate_point_iff (r : FiniteRepresentation E)
    {L : Type*} [Field L] (ι : E →+* L) (u v : L) :
    (ofUnivariate r).Point ι u v ↔ r.modulus.toPoly.eval₂ ι u = 0 ∧ v = 0 := by
  simp [Point, ofUnivariate, evalNested, specializeFiber_X]

/-- Specializing embedded coefficients gives exactly the original univariate message. -/
theorem ofUnivariate_specialize (r : FiniteRepresentation E)
    {L : Type*} [Field L] (ι : E →+* L) (u v : L) :
    (ofUnivariate r).specialize ι u v = r.specialize ι u := by
  simp [specialize, ofUnivariate, FiniteRepresentation.specialize, List.map_map, Function.comp_def,
    evalNested, specializeFiberCPolynomial, CPolynomial.C_toPoly]

/-- The embedding preserves the represented polynomial and adds only the forced fiber root zero. -/
theorem ofUnivariate_represents_iff (r : FiniteRepresentation E)
    {L : Type*} [Field L] (ι : E →+* L) (u v : L) (p : L[X]) :
    (ofUnivariate r).Represents ι u v p ↔ r.Represents ι u p ∧ v = 0 := by
  rw [Represents, ofUnivariate_point_iff, ofUnivariate_specialize]
  simp only [FiniteRepresentation.Represents]
  tauto

/-- A positive-degree well-formed univariate family yields a well-formed degree-one tower. -/
theorem ofUnivariate_wellFormed (r : FiniteRepresentation E) {k : ℕ}
    (hr : r.WellFormed k) (hpositive : 0 < r.modulus.natDegree) :
    (ofUnivariate r).WellFormed k := by
  have hG : (0 : WithBot ℕ) < r.modulus.toPoly.degree := by
    rw [← Polynomial.natDegree_pos_iff_degree_pos]
    simpa only [CPolynomial.natDegree_toPoly] using hpositive
  have hX : (CPolynomial.X : CPolynomial (CPolynomial E)).monic := by
    rw [CPolynomial.monic_toPoly_iff, CPolynomial.X_toPoly]
    exact Polynomial.monic_X
  refine ⟨(CPolynomial.monic_toPoly_iff _).mpr hr.1, hr.2.1, hpositive,
    hX, ?_, ?_, ?_, ?_, ?_⟩
  · simp [ofUnivariate, CPolynomial.natDegree_toPoly, CPolynomial.X_toPoly]
  · intro i
    change ((CPolynomial.X : CPolynomial (CPolynomial E)).coeff i).toPoly.degree < _
    rw [CPolynomial.coeff_toPoly, CPolynomial.X_toPoly, Polynomial.coeff_X]
    by_cases hi : i = 1
    · subst i
      simpa [CPolynomial.toPoly_one, ofUnivariate] using hG
    · simpa [hi, CPolynomial.toPoly_zero, ofUnivariate, Ne.symm hi] using
        (bot_lt_of_lt hG)
  · intro L _ ι u _
    change Squarefree (specializeFiberCPolynomial CPolynomial.X ι u)
    rw [specializeFiber_X]
    exact Polynomial.irreducible_X.squarefree
  · simpa [ofUnivariate] using hr.2.2.1
  · intro c hc
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hc
    constructor
    · change (CPolynomial.C a).toPoly.degree < CPolynomial.X.toPoly.degree
      rw [CPolynomial.C_toPoly, CPolynomial.X_toPoly, Polynomial.degree_X]
      exact Polynomial.degree_C_le.trans_lt (by norm_num)
    · intro i
      by_cases hi : i = 0
      · subst i
        simpa [CPolynomial.coeff_C, ofUnivariate] using hr.2.2.2 a ha
      · simpa [CPolynomial.coeff_C, hi, CPolynomial.toPoly_zero, ofUnivariate] using
          (bot_lt_of_lt hG)

end ReedSolomon.ListDecoding.TowerRepresentation
