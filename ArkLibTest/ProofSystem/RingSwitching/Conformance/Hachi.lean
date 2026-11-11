/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Commitments.Functional.Hachi.TraceHead.Basic
import ArkLib.Commitments.Functional.Hachi.TraceHead.Conformance
import ArkLibTest.Commitments.Functional.Hachi.TraceHead.Protocol

/-!
# Hachi §3.1 conformance to the shared packing layer

The conformance theorem `trace_head_conforms` states the trace head's accepting condition through
the shared packing layer of `RingSwitching.Packing`, at the packing data
`traceHeadData ψ = PackingData.ofBaseOpening ψ` and the claim layout `traceHeadLayout ψ`:
a passing check whose forwarded claim opens validly is exactly a valid weak opening such that

* the sent ring value is the single slice of the shared `packedMLE` of the layout's components of
  the decoded committed polynomial, in the shared `sliceRel` at the retained point; and
* the claimed scalar is the layout-weighted sum of `ψ⁻¹` of the sent value.

The statements it is built from are:

* `toMvPolynomialDeg1_eq_packedMLE`: every ring polynomial, in particular the committed one, is
  the shared `packedMLE` of the layout's components of its decoding;
* `traceHeadData_transpose`: at `ofBaseOpening` the shared transpose is `ψ` itself;
* `openingClaimRel_unpackCoefficients_iff`: the shared `openingClaimRel` of those components holds
  exactly when `ψ` of the claimed values is the ring evaluation;
* `eval_eq_iff_sliceRel`: a ring value is that evaluation exactly when it is the single shared
  slice (through the shared `openingClaimRel_iff_sliceRel`);
* `output_mem_relPolyEval_iff_sliceRel` and `check_iff_layout_weight`: the forwarded ring relation
  and the trace check in that vocabulary.

The layout has one opening coordinate and introduces no batching challenge or sumcheck.
The head's read-back `observation` is a `CheckedObservation`.

The concrete instances, stated through `trace_head_conforms`, show the honest side inhabited by a
nonconstant polynomial and that, for a false claim, no sent ring value satisfies the shared-layer
condition. The opening-relation fixtures accept exactly the honest component values, reject a
wrong one, and accept the distinct rows of a polynomial with distinct coefficients, so a row swap
would be caught. The check alone is not enough: for the false claim `0` the message `0` passes it.
-/

open CompPoly ArkLib.Lattices.CyclotomicModulus
open ArkLib.Lattices.Hachi ArkLib.Lattices.Hachi.TraceHead
open ArkLib.Lattices.Ajtai.InnerOuter ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding
open RingSwitching.Packing Module

namespace ArkLibTest.RingSwitchingConformance.Hachi

/-! The conformance theorem, the library identification and the head's read-back depend only on
the standard axioms. -/

/--
info: 'ArkLib.Lattices.Hachi.TraceHead.trace_head_conforms' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.Lattices.Hachi.TraceHead.trace_head_conforms

/--
info: 'ArkLib.Lattices.Hachi.TraceHead.toMvPolynomialDeg1_packCoefficients' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.Lattices.Hachi.TraceHead.toMvPolynomialDeg1_packCoefficients

/--
info: 'ArkLib.Lattices.Hachi.TraceHead.unpackCoefficients_eval' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.Lattices.Hachi.TraceHead.unpackCoefficients_eval

section Concrete

open HachiTraceHeadTest

private theorem hk : 2 * 2 ^ 0 ∣ 2 ^ 1 := by decide
private theorem h2 : (2 : ZMod 5) ≠ 0 := by decide

/-- The honest side is inhabited: for the committed nonconstant polynomial and the honest sent
value, the shared-layer accepting condition holds. -/
example : VerifiedOpening Φ 2 6 1 1 pp.toPublicParams s.u w ∧
    ((fun _ => honestMessage 1 0 2 s w), (traceHeadData (coefficientEquiv 5 1 0 h2 hk)).packedMLE
        ((traceHeadLayout (coefficientEquiv 5 1 0 h2 hk)).components
          (unpackCoefficients (coefficientEquiv 5 1 0 h2 hk) (extractedPoly Φ 2 w)))) ∈
      (traceHeadData (coefficientEquiv 5 1 0 h2 hk)).sliceRel (1 + 0) (s.xl ++ s.xh).get ∧
    s.value = ∑ j, (traceHeadLayout (n := 1 + 0) (coefficientEquiv 5 1 0 h2 hk)).weight
      (s.xl ++ s.xh, s.xp) j * (coefficientEquiv 5 1 0 h2 hk).symm (honestMessage 1 0 2 s w) j :=
  (trace_head_conforms 1 0 hk h2 pp 2 6 1 1 s _ w).1
    ((trace_head_accepts_iff 1 0 hk h2 pp 2 6 1 1 s _ w).2 ⟨source_valid.1, rfl⟩)

/-- For a false scalar claim, no sent ring value satisfies the shared-layer accepting condition
against the same commitment and weak opening. -/
example (Y : Rq Φ) : ¬ (VerifiedOpening Φ 2 6 1 1 pp.toPublicParams bad.u w ∧
    ((fun _ => Y), (traceHeadData (coefficientEquiv 5 1 0 h2 hk)).packedMLE
        ((traceHeadLayout (coefficientEquiv 5 1 0 h2 hk)).components
          (unpackCoefficients (coefficientEquiv 5 1 0 h2 hk) (extractedPoly Φ 2 w)))) ∈
      (traceHeadData (coefficientEquiv 5 1 0 h2 hk)).sliceRel (1 + 0) (bad.xl ++ bad.xh).get ∧
    bad.value = ∑ j, (traceHeadLayout (n := 1 + 0) (coefficientEquiv 5 1 0 h2 hk)).weight
      (bad.xl ++ bad.xh, bad.xp) j * (coefficientEquiv 5 1 0 h2 hk).symm Y j) := by
  intro h
  have hbad := ((trace_head_accepts_iff 1 0 hk h2 pp 2 6 1 1 bad Y w).1
    ((trace_head_conforms 1 0 hk h2 pp 2 6 1 1 bad Y w).2 h)).1
  have hz : s.value = 0 := source_valid.1.2.symm.trans hbad.2
  rw [claim_two] at hz
  exact HachiTraceHeadAlgebraTest.value_ne_zero (congrArg Subtype.val hz)

/-- The opening relation accepts exactly the honest component values: for `f = 1 + X + Y + XY`
at the retained point `0`, a claimed family is accepted iff it is `ψ⁻¹` of the ring evaluation. -/
theorem openingClaimRel_iff_honest (v : Fin 2 → B) :
    ((v, (#v[(0 : B)]).get),
      (traceHeadLayout (coefficientEquiv 5 1 0 h2 hk)).components
        (unpackCoefficients (coefficientEquiv 5 1 0 h2 hk)
          (packCoefficients (coefficientEquiv 5 1 0 h2 hk) f))) ∈
      (traceHeadData (coefficientEquiv 5 1 0 h2 hk)).openingClaimRel 1 ↔
    v = (coefficientEquiv 5 1 0 h2 hk).symm
      ((packCoefficients (n := 1) (t := 1) (coefficientEquiv 5 1 0 h2 hk) f).eval
        ((#v[(0 : B)]).map (algebraMap B A))) := by
  rw [openingClaimRel_unpackCoefficients_iff, LinearEquiv.eq_symm_apply]
  exact Iff.rfl

/-- A wrong component opening is rejected: for `f = 1 + X + Y + XY` at the retained point `0`,
the opening relation of the claimed values `0` fails, because `ψ 0` is not the ring evaluation. -/
example : ¬ ((0, (#v[(0 : B)]).get),
    (traceHeadLayout (coefficientEquiv 5 1 0 h2 hk)).components
      (unpackCoefficients (coefficientEquiv 5 1 0 h2 hk)
        (packCoefficients (coefficientEquiv 5 1 0 h2 hk) f))) ∈
      (traceHeadData (coefficientEquiv 5 1 0 h2 hk)).openingClaimRel 1 := by
  rw [openingClaimRel_unpackCoefficients_iff, map_zero]
  intro h
  have hF : (packCoefficients (n := 1) (t := 1) (coefficientEquiv 5 1 0 h2 hk) f).eval
      ((#v[(0 : B)]).map (algebraMap B A)) = coefficientEquiv 5 1 0 h2 hk (fun _ => 1) := by
    have hrow : (fun j => f.get (splitEquiv 1 1 (j, 0))) = fun _ => (1 : B) := by
      funext j
      fin_cases j <;> rfl
    simpa [CMlPolynomial.eval, Vector.dotProduct_eq_root_dotProduct, dotProduct, Fin.sum_univ_two,
      monomialBasis_get, packCoefficients] using congrArg (coefficientEquiv 5 1 0 h2 hk) hrow
  have h' := h.trans hF
  rw [← map_zero (coefficientEquiv 5 1 0 h2 hk), (coefficientEquiv 5 1 0 h2 hk).injective.eq_iff]
    at h'
  have h1 : (0 : A) = 1 := congrArg Subtype.val (congrFun h' 0)
  exact HachiTraceHeadAlgebraTest.value_ne_zero (by rw [← one_add_one_eq_two, ← h1, add_zero])

/-- The polynomial `1 + 2X + 3Y + 4XY` with distinct coefficients, `X` retained and `Y` packed. -/
noncomputable def fDistinct : CMlPolynomial B (1 + 1) := #v[1, 2, 3, 4]

/-- At the retained point `0`, the opening relation accepts the rows' constant coefficients in
order, `(1, 3)`; swapping the two monomial-coefficient rows would give `(3, 1)`. -/
example : ((![1, 3], (#v[(0 : B)]).get),
    (traceHeadLayout (coefficientEquiv 5 1 0 h2 hk)).components fDistinct) ∈
      (traceHeadData (coefficientEquiv 5 1 0 h2 hk)).openingClaimRel 1 := by
  intro j
  change _ = MvPolynomial.eval (#v[(0 : B)]).get
    (CMlPolynomial.toMvPolynomial (coefficientRows fDistinct j))
  rw [← CMlPolynomial.eval_eq_eval_toMvPolynomial]
  fin_cases j <;>
    simp [CMlPolynomial.eval, Vector.dotProduct_eq_root_dotProduct, dotProduct,
      monomialBasis_get, coefficientRows, toMatrix, fDistinct] <;> rfl

end Concrete

end ArkLibTest.RingSwitchingConformance.Hachi
