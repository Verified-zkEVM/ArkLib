/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Commitments.Functional.Hachi.TraceHead.Basic
import ArkLibTest.Commitments.Functional.Hachi.TraceHead.Protocol

/-!
# Hachi §3.1 conformance to the shared packing interfaces

Hachi's one-message trace head shares the following with `RingSwitching.Packing`.

* **Packed polynomial.** Under `CMlPolynomial.equivMvPolynomialDeg1`, the trace head's packed
  polynomial `packCoefficients ψ f` is the shared `packedMLE` of the components of
  `traceHeadLayout`, at the packing data `PackingData.ofBaseOpening` of `ψ`
  (`toMvPolynomialDeg1_packCoefficients`).
* **Packing/evaluation commutation.** The read-back commutes evaluation at the embedded retained
  point with packing by the shared `PackingData.packedMLE_eval_embedded`, the lemma Binius's
  profile layout uses. It gives the shared `openingClaimRel` of the scalar components: it holds
  exactly when `ψ` of the claimed values is the ring evaluation the prover sends
  (`openingClaimRel_iff_psi_eq_eval`, an instance of `openingClaimRel_unpackCoefficients_iff`).
  The read-back identity `unpackCoefficients_eval` follows from it and the layout's
  reconstruction.
* **Claim layout.** `traceHeadLayout` instantiates the `ScalarHead.ClaimLayout` contract; its
  `reconstruct` is Hachi's own proof (`evalSplit_eq_eval` and the evaluation bridge).
* **Checked observation.** `observation` is a `CheckedObservation` whose observation is the
  `ψ`-coordinate inner product, equivalent to the scaled trace check (`check_iff_observation`).
  It is written by hand, not derived from the layout.

The fixed subring is the opening algebra, so there is one opening coordinate (`ιE = Unit`) and the
coordinate transpose is trivial. The protocol relations `relScalarEval` and `relPolyEval`, and
`traceHead_conforms` below, do not mention the packing layer; they depend on it only through the
read-back identity.

The layout splits the **monomial coefficients** of the packed variables; it is not the
Boolean-restriction `packedSuffixLayout`.

The conformance theorem states the head's exact relation correspondence: a passing check with a
valid ring-level opening holds iff the scalar relation holds and the sent value is honest. It
applies the head's read-back and honest-check lemmas, which are the shared
`CheckedObservation.readback` and `CheckedObservation.honest_check` at Hachi's observation. The
concrete instances show the honest side inhabited by a nonconstant polynomial, and that for a
false claim no sent ring value both passes the check and opens validly against the same weak
opening. The check alone is not enough: for the false claim `0` the message `0` passes it.
-/

open CompPoly ArkLib.Lattices.CyclotomicModulus
open ArkLib.Lattices.Hachi ArkLib.Lattices.Hachi.TraceHead
open ArkLib.Lattices.Ajtai.InnerOuter

namespace ArkLibTest.RingSwitchingConformance.Hachi

section Universal

variable {q : ℕ} [Fact (Nat.Prime q)] [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (α κ : ℕ) {innerRows messageDigits outerRows innerDigits dRows m r : ℕ}
  (hk : 2 * 2 ^ κ ∣ 2 ^ α) (h2 : (2 : ZMod q) ≠ 0)

/-- **Hachi §3.1 conformance.** The trace head's check-and-forward step corresponds exactly to
the scalar relation. -/
theorem traceHead_conforms
    (pp : PublicParamsD (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (base : ZMod q) (βSq γ bound : ℕ)
    (s : Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (Y : Rq (powTwoCyclotomic (R := ZMod q) α))
    (w : QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :
    (check α κ hk s Y = true ∧ (output α κ s Y, w) ∈
        relPolyEval (powTwoCyclotomic (R := ZMod q) α) pp base βSq γ bound) ↔
      ((s, w) ∈ relScalarEval α κ hk h2 pp base βSq γ bound ∧ Y = honestMessage α κ base s w) := by
  constructor
  · rintro ⟨hc, hout⟩
    exact ⟨mem_relScalarEval_of_output α κ hk h2 pp base βSq γ bound s Y w hc hout,
      ((output_mem_relPolyEval_iff α κ hk h2 pp base βSq γ bound s Y w).1 hout).2⟩
  · rintro ⟨hin, rfl⟩
    exact ⟨check_honestMessage α κ hk h2 pp base βSq γ bound s w hin,
      output_mem_relPolyEval_of_mem_relScalarEval α κ hk h2 pp base βSq γ bound s w hin⟩

end Universal

section SharedPacking

open RingSwitching.Packing

variable {q : ℕ} [Fact (Nat.Prime q)] [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (α κ : ℕ) (hk : 2 * 2 ^ κ ∣ 2 ^ α) (h2 : (2 : ZMod q) ≠ 0) {n : ℕ}

/-- At `ψ`, the trace head's packed polynomial is the shared `packedMLE` of `traceHeadLayout`'s
components. -/
theorem toMvPolynomialDeg1_packCoefficients
    (f : CMlPolynomial (fixedSubring (R := ZMod q) α (2 ^ κ)) (n + (α - κ))) :
    CMlPolynomial.toMvPolynomialDeg1 (packCoefficients (coefficientEquiv q α κ h2 hk) f) =
      (traceHeadData (coefficientEquiv q α κ h2 hk)).packedMLE
        ((traceHeadLayout (coefficientEquiv q α κ h2 hk)).components f) :=
  TraceHead.toMvPolynomialDeg1_packCoefficients _ f

/-- At `ψ`, the shared opening relation of the scalar components says exactly that `ψ` of the
claimed values is the ring evaluation. -/
theorem openingClaimRel_iff_psi_eq_eval
    (F : CMlPolynomial (Rq (powTwoCyclotomic (R := ZMod q) α)) n)
    (x : Vector (fixedSubring (R := ZMod q) α (2 ^ κ)) n)
    (v : Fin (2 ^ (α - κ)) → fixedSubring (R := ZMod q) α (2 ^ κ)) :
    ((v, x.get), (traceHeadLayout (coefficientEquiv q α κ h2 hk)).components
        (unpackCoefficients (coefficientEquiv q α κ h2 hk) F)) ∈
        (traceHeadData (coefficientEquiv q α κ h2 hk)).openingClaimRel n ↔
      coefficientEquiv q α κ h2 hk v = F.eval (x.map (algebraMap _ _)) :=
  openingClaimRel_unpackCoefficients_iff _ F x v

end SharedPacking

/-! The library statements behind the wrappers above, and the read-back identity, depend only on
the standard axioms. -/

/--
info: 'ArkLib.Lattices.Hachi.TraceHead.toMvPolynomialDeg1_packCoefficients' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.Lattices.Hachi.TraceHead.toMvPolynomialDeg1_packCoefficients

/--
info: 'ArkLib.Lattices.Hachi.TraceHead.openingClaimRel_unpackCoefficients_iff' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.Lattices.Hachi.TraceHead.openingClaimRel_unpackCoefficients_iff

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

/-- The honest side is inhabited: the committed nonconstant polynomial passes the check and its
forwarded value carries a valid ring-level opening. -/
example : check 1 0 hk s (honestMessage 1 0 2 s w) = true ∧
    (output 1 0 s (honestMessage 1 0 2 s w), w) ∈ relPolyEval Φ pp 2 6 1 1 :=
  (traceHead_conforms 1 0 hk h2 pp 2 6 1 1 s _ w).2 ⟨source_valid.1, rfl⟩

/-- For a false scalar claim, no sent ring value both passes the check and opens validly against
the same commitment and weak opening. -/
example (Y : Rq Φ) :
    ¬ (check 1 0 hk bad Y = true ∧ (output 1 0 bad Y, w) ∈ relPolyEval Φ pp 2 6 1 1) := by
  intro h
  have hbad := ((traceHead_conforms 1 0 hk h2 pp 2 6 1 1 bad Y w).1 h).1
  have hz : s.value = 0 := source_valid.1.2.symm.trans hbad.2
  rw [claim_two] at hz
  exact HachiTraceHeadAlgebraTest.value_ne_zero (congrArg Subtype.val hz)

/-- A wrong component opening is rejected: for `f = 1 + X + Y + XY` at the retained point `0`,
the opening relation of the claimed values `0` fails, because `ψ 0` is not the ring evaluation. -/
example : ¬ ((0, (#v[(0 : B)]).get),
    (traceHeadLayout (coefficientEquiv 5 1 0 h2 hk)).components
      (unpackCoefficients (coefficientEquiv 5 1 0 h2 hk)
        (packCoefficients (coefficientEquiv 5 1 0 h2 hk) f))) ∈
      (traceHeadData (coefficientEquiv 5 1 0 h2 hk)).openingClaimRel 1 := by
  rw [openingClaimRel_iff_psi_eq_eval, map_zero]
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

end Concrete

end ArkLibTest.RingSwitchingConformance.Hachi
