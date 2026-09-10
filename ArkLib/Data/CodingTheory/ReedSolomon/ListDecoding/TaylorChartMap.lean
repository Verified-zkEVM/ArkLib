/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.RationalRepresentationDecoder
public import ArkLib.Data.Polynomial.UnivariateRepresentation.Point

-- The chart-evaluation bridge reduces the computable-polynomial semantic conversion.
import all CompPoly.Univariate.ToPoly.Core
import all CompPoly.Univariate.ToPoly.Equiv

/-!
# Applying a Taylor chart to a rational univariate jet map

The isolated-root solver supplies rational jet coordinates `A_i(U)/B(U)`. First normalize its
eliminant, remove the roots with `B=0`, and materialize these coordinates as polynomials modulo
the surviving eliminant. Evaluating the computable chart polynomials at those coordinates then
produces one common Taylor denominator and the ascending Taylor numerators.

`fromJet?` passes this computed Taylor map to `RationalRepresentationDecoder.fromRational?`,
which removes zero chart denominators, imposes the degree-k tail constraints, and shifts the
result back to ordinary message coefficients. `fromJet?_covers` proves that a represented jet
whose chart ratios are the Taylor coefficients of a message survives the whole executable path.

The input jet map must already be in the original jet coordinates. A Rojas torus-chart inverse
translation belongs BEFORE this operation: translating every higher Taylor coefficient would
be incorrect. The `center` here is the message's Taylor expansion center, distinct from any
scalar used to translate the square system into a torus chart.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.TaylorChartMap
open CompPoly CompPoly.CPolynomial
open ArkLib.UnivariateRepresentation
universe u
variable {E : Type u} [Field E] [Fintype E] [BEq E] [LawfulBEq E] {s : ℕ}
variable (pchar : ℕ) [Fact pchar.Prime] [CharP E pchar]

/-- Substitute the materialized jet coordinates into a computable multivariate polynomial. -/
def evaluateAtCoordinates (coordinates : List (CPolynomial E))
    (polynomial : CPoly.CMvPolynomial s E) : CPolynomial E :=
  CPoly.CMvPolynomial.eval₂ CPolynomial.CHom (fun i => coordinates[i.val]?.getD 0) polynomial

/-- Evaluate every Taylor numerator and its common denominator over the retained parameter
algebra. -/
def rationalChartMap (jet : Representation (F := E))
    (numerators : List (CPoly.CMvPolynomial s E)) (denominator : CPoly.CMvPolynomial s E) :
    MapData (F := E) :=
  ⟨jet.modulus, evaluateAtCoordinates jet.coordinates denominator,
    numerators.map (evaluateAtCoordinates jet.coordinates)⟩

/-- Convert a raw rational jet map through its Taylor chart to one finite message representation. -/
def fromJet? (center : E) (k : ℕ) (input : MapData (F := E))
    (numerators : List (CPoly.CMvPolynomial s E)) (denominator : CPoly.CMvPolynomial s E) :
    Option (FiniteRepresentation E) := do
  let jet ← postprocessRaw? pchar input []
  RationalRepresentationDecoder.fromRational? pchar center k
    (rationalChartMap jet numerators denominator)

noncomputable section
variable {L : Type*} [Field L]
omit [Fintype E] [Fact pchar.Prime] [CharP E pchar] in
/-- Parameter specialization commutes with evaluating any computable chart polynomial. -/
theorem evaluateAtCoordinates_semantics (ι : E →+* L) (θ : L)
    (coordinates : List (CPolynomial E)) (point : Fin s → L)
    (hcoordinates : ∀ i : Fin s, (coordinates[i.val]?.getD 0).toPoly.eval₂ ι θ = point i)
    (polynomial : CPoly.CMvPolynomial s E) :
    (evaluateAtCoordinates coordinates polynomial).toPoly.eval₂ ι θ =
      MvPolynomial.eval₂ ι point (CPoly.fromCMvPolynomial polynomial) := by
  change ((Polynomial.eval₂RingHom ι θ).comp CPolynomial.toPolyRingHom)
    (evaluateAtCoordinates coordinates polynomial) = _
  rw [evaluateAtCoordinates, CPoly.eval₂_equiv, MvPolynomial.eval₂_comp_left]
  congr 1
  · ext a
    simp [CPolynomial.C_toPoly]
  · funext i
    exact hcoordinates i

/-- **Chart-to-message coverage.** A solver-represented jet survives whenever its common chart
denominator is nonzero and its Taylor ratios describe a degree-`< k` message. -/
theorem fromJet?_covers (center : E) (k : ℕ) (input : MapData (F := E))
    (numerators : List (CPoly.CMvPolynomial s E)) (denominator : CPoly.CMvPolynomial s E)
    -- A nonzero eliminant gives finitely many parameters; at least k Taylor slots are available.
    (hnonzero : input.modulus ≠ 0) (hwidth : k ≤ numerators.length)
    -- The parameter and jet may live in an extension even when the recovered message is over E.
    (ι : E →+* L) (θ : L) (point : Fin s → L) (P : Polynomial L)
    (hdegree : P.degree < k) (hpoint : MapData.RepresentsPoint input ι θ point)
    -- On the regular chart, the numerator/denominator ratios are exactly the Taylor coefficients.
    (hdenominator : MvPolynomial.eval₂ ι point (CPoly.fromCMvPolynomial denominator) ≠ 0)
    (hcoefficients : ∀ i : Fin numerators.length,
      MvPolynomial.eval₂ ι point (CPoly.fromCMvPolynomial numerators[i]) /
        MvPolynomial.eval₂ ι point (CPoly.fromCMvPolynomial denominator) =
          (Polynomial.taylor (ι center) P).coeff i) :
    ∃ r, fromJet? pchar center k input numerators denominator = some r ∧
      r.WellFormed k ∧ r.Represents ι θ P := by
  -- Materialize only the jet coordinates first; their rational denominator is a separate filter.
  obtain ⟨jet, hjet, hcorrect⟩ := postprocessRaw?_exists_correct pchar input [] hnonzero
  have hroot : jet.modulus.toPoly.eval₂ ι θ = 0 :=
    (hcorrect.roots ι θ).mpr ⟨hpoint.1, hpoint.2.1, by simp⟩
  have hcoords := hcorrect.coordinates ι θ hroot
  have hlength : jet.coordinates.length = s := hcoords.length_eq.symm.trans hpoint.2.2.1
  -- The postprocessor preserves coordinate order, so each polynomial still represents its jet
  -- entry.
  have hcoordinates : ∀ i : Fin s,
      (jet.coordinates[i.val]?.getD 0).toPoly.eval₂ ι θ = point i := by
    intro i
    have hi : i.val < input.numerators.length := by simpa only [hpoint.2.2.1] using i.isLt
    have hj : i.val < jet.coordinates.length := by simpa only [hlength] using i.isLt
    have hratio := hcoords.get hi hj
    have hp := hpoint.2.2.2 i
    simpa [hi, hj] using hratio.trans (by simpa [hi] using hp)
  -- Polynomial substitution now converts the literal chart identities into a rational Taylor map.
  have hrep : RationalRepresentationDecoder.Represents
      (rationalChartMap jet numerators denominator) ι θ (ι center) P := by
    refine ⟨hroot, ?_, ?_⟩
    · simpa [rationalChartMap, evaluateAtCoordinates_semantics ι θ _ point hcoordinates] using
        hdenominator
    · intro i
      have hi : i.val < numerators.length := by simpa [rationalChartMap] using i.isLt
      have hnum : (rationalChartMap jet numerators denominator).numerators[i] =
          evaluateAtCoordinates jet.coordinates numerators[i.val] := by
        change (numerators.map (evaluateAtCoordinates jet.coordinates))[i.val] = _
        exact List.getElem_map _
      rw [hnum]
      change (evaluateAtCoordinates jet.coordinates numerators[i.val]).toPoly.eval₂ ι θ /
        (evaluateAtCoordinates jet.coordinates denominator).toPoly.eval₂ ι θ = _
      rw [evaluateAtCoordinates_semantics ι θ _ point hcoordinates,
        evaluateAtCoordinates_semantics ι θ _ point hcoordinates]
      exact hcoefficients ⟨i.val, hi⟩
  obtain ⟨r, hr, hwell, hrep⟩ := RationalRepresentationDecoder.fromRational?_covers pchar center k
    (rationalChartMap jet numerators denominator) hcorrect.modulus_ne_zero
    (by simpa [rationalChartMap] using hwidth) ι θ P hdegree hrep
  exact ⟨r, by simp [fromJet?, hjet, hr], hwell, hrep⟩

/-- Every emitted result satisfies the common recovery contract and retains at most the raw
degree. -/
theorem fromJet?_properties (center : E) (k : ℕ) (input : MapData (F := E))
    (numerators : List (CPoly.CMvPolynomial s E)) (denominator : CPoly.CMvPolynomial s E)
    (r : FiniteRepresentation E)
    (hr : fromJet? pchar center k input numerators denominator = some r) :
    r.WellFormed k ∧ r.modulus.natDegree ≤ input.modulus.natDegree := by
  unfold fromJet? at hr
  cases hpost : postprocessRaw? pchar input [] with
  | none => simp [hpost] at hr
  | some jet =>
      rw [hpost] at hr
      change RationalRepresentationDecoder.fromRational? pchar center k
        (rationalChartMap jet numerators denominator) = some r at hr
      have hp := RationalRepresentationDecoder.fromRational?_properties pchar center k
        (rationalChartMap jet numerators denominator) r hr
      have hnonzero : input.modulus ≠ 0 := by
        intro hz
        simp [postprocessRaw?, hz] at hpost
      have hjet := postprocessRaw?_correct.{u, u, u} pchar hnonzero hpost
      exact ⟨hp.1, hp.2.trans hjet.modulus_natDegree_le⟩

end
end ReedSolomon.ListDecoding.TaylorChartMap
