/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.SquarefreeSupport
public import ArkLib.Data.Polynomial.UnivariateRepresentation.Postprocess

/-!
# Postprocessing a raw finite-field eliminant

This wrapper first replaces a nonzero, possibly repeated or inseparable
eliminant by its monic squarefree support, then invokes the rational-univariate
map postprocessor. The characteristic prime remains explicit runtime data.
-/

@[expose] public section

namespace ArkLib.UnivariateRepresentation

open CompPoly CompPoly.CPolynomial

variable {F : Type*} [Field F] [Fintype F] [BEq F] [LawfulBEq F]
variable (p : ℕ) [Fact p.Prime] [CharP F p]

/-- Replace only the eliminant of a solver-produced rational map. -/
def normalizeModulus (input : MapData (F := F)) : MapData (F := F) :=
  {
    modulus := squarefreeSupport p input.modulus
    denominator := input.denominator
    numerators := input.numerators }

/-- Reject the zero eliminant, normalize every nonzero eliminant, and run the
complete rational-map postprocessor. -/
def postprocessRaw? (input : MapData (F := F))
    (zeroEquations : List (CPolynomial F)) : Option (Representation (F := F)) :=
  if input.modulus == 0 then none
  else postprocess? (normalizeModulus p input) zeroEquations

/-- Full contract stated against the raw eliminant. -/
structure RawCorrectOutput (input : MapData (F := F))
    (zeroEquations : List (CPolynomial F)) (output : Representation (F := F)) : Prop where
  modulus_ne_zero : output.modulus ≠ 0
  modulus_monic : output.modulus.monic
  modulus_squarefree : Squarefree output.modulus.toPoly
  modulus_natDegree_le : output.modulus.natDegree ≤ input.modulus.natDegree
  coordinate_degree_lt : ∀ coordinate ∈ output.coordinates,
    coordinate.toPoly.degree < output.modulus.toPoly.degree
  roots : ∀ {K : Type*} [Field K] (ι : F →+* K) (θ : K),
    output.modulus.toPoly.eval₂ ι θ = 0 ↔
      input.modulus.toPoly.eval₂ ι θ = 0 ∧
        input.denominator.toPoly.eval₂ ι θ ≠ 0 ∧
        ∀ equation ∈ zeroEquations, equation.toPoly.eval₂ ι θ = 0
  coordinates : ∀ {K : Type*} [Field K] (ι : F →+* K) (θ : K),
    output.modulus.toPoly.eval₂ ι θ = 0 →
      CoordinatesSpecializeAt ι θ input.denominator input.numerators output.coordinates

omit [Fact (Nat.Prime p)] [CharP F p] in
theorem postprocessRaw?_eq_postprocess_of_ne
    (input : MapData (F := F)) (zeroEquations : List (CPolynomial F))
    (hmodulus : input.modulus ≠ 0) :
    postprocessRaw? p input zeroEquations =
      postprocess? (normalizeModulus p input) zeroEquations := by
  simp [postprocessRaw?, beq_iff_eq, hmodulus]

theorem postprocessRaw?_correct
    {input : MapData (F := F)} {zeroEquations : List (CPolynomial F)}
    {output : Representation (F := F)} (hmodulus : input.modulus ≠ 0)
    (hresult : postprocessRaw? p input zeroEquations = some output) :
    RawCorrectOutput input zeroEquations output := by
  rw [postprocessRaw?_eq_postprocess_of_ne p input zeroEquations hmodulus] at hresult
  have hnormalized := postprocess?_correct hresult
    (squarefreeSupport_monic p hmodulus) (squarefreeSupport_squarefree p hmodulus)
  refine {
    modulus_ne_zero := hnormalized.modulus_ne_zero
    modulus_monic := hnormalized.modulus_monic
    modulus_squarefree := hnormalized.modulus_squarefree
    modulus_natDegree_le := hnormalized.modulus_natDegree_le.trans
      (natDegree_squarefreeSupport_le p hmodulus)
    coordinate_degree_lt := hnormalized.coordinate_degree_lt
    roots := ?_
    coordinates := hnormalized.coordinates }
  intro K _ ι θ
  rw [hnormalized.roots ι θ]
  change (squarefreeSupport p input.modulus).toPoly.eval₂ ι θ = 0 ∧
      input.denominator.toPoly.eval₂ ι θ ≠ 0 ∧
        (∀ equation ∈ zeroEquations, equation.toPoly.eval₂ ι θ = 0) ↔ _
  rw [eval₂_squarefreeSupport_eq_zero_iff p ι θ hmodulus]

/-- Every nonzero raw eliminant produces a certified result, including
repeated and zero-derivative inputs. -/
theorem postprocessRaw?_exists_correct
    (input : MapData (F := F)) (zeroEquations : List (CPolynomial F))
    (hmodulus : input.modulus ≠ 0) :
    ∃ output, postprocessRaw? p input zeroEquations = some output ∧
      RawCorrectOutput input zeroEquations output := by
  have hsupportNe := squarefreeSupport_ne_zero p hmodulus
  obtain ⟨retained, hdomain⟩ := filterDomain?_exists
    (squarefreeSupport p input.modulus) input.denominator zeroEquations hsupportNe
  obtain ⟨output, houtput⟩ := postprocess?_exists_of_filterDomain
    (input := normalizeModulus p input) (zeroEquations := zeroEquations)
    (retained := retained) hdomain hsupportNe
    (squarefreeSupport_squarefree p hmodulus)
  have hraw : postprocessRaw? p input zeroEquations = some output := by
    rw [postprocessRaw?_eq_postprocess_of_ne p input zeroEquations hmodulus]
    exact houtput
  exact ⟨output, hraw, postprocessRaw?_correct p hmodulus hraw⟩

end ArkLib.UnivariateRepresentation
