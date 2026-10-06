/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Commitments.Functional.Hachi.TraceHead.Basic
import ArkLib.ProofSystem.RingSwitching.Packing.Relations
import ArkLibTest.Commitments.Functional.Hachi.TraceHead.Protocol

/-!
# Hachi §3.1 conformance to the shared packing layer

The conformance theorem `traceHead_conforms` states the trace head's accepting condition through
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

Hachi §3.1 exercises only the packing, evaluation and opening part of the shared layer (one
opening coordinate, no batching, multiplier or sumcheck), as in the paper, so its reuse is small
at the proof level and real at the statement level. The head's read-back `observation` is a
`CheckedObservation` written by hand.

The concrete instances, stated through `traceHead_conforms`, show the honest side inhabited by a
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

section SharedLayer

variable {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {n t : ℕ}
  (e : (Fin (2 ^ t) → B) ≃ₗ[B] A)

/-- At `ofBaseOpening`, the shared transpose of a family of opening values is its image under the
packing map. -/
theorem traceHeadData_transpose (v : Fin (2 ^ t) → B) :
    (traceHeadData e).transpose v () = e v := by
  rw [PackingData.transpose_apply]
  conv_rhs => rw [← (Basis.ofEquivFun e.symm).sum_repr (e v)]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [Basis.ofEquivFun_repr_apply]

/-- Every ring polynomial is the shared `packedMLE` of the layout's components of its decoding. -/
theorem toMvPolynomialDeg1_eq_packedMLE (F : CMlPolynomial A n) :
    CMlPolynomial.toMvPolynomialDeg1 F =
      (traceHeadData e).packedMLE ((traceHeadLayout e).components (unpackCoefficients e F)) := by
  rw [← toMvPolynomialDeg1_packCoefficients, packCoefficients_unpackCoefficients]

/-- The opening claims of the layout's components of a decoded polynomial hold exactly when `e`
maps the claimed values to the ring evaluation at the embedded retained point. -/
theorem openingClaimRel_unpackCoefficients_iff (F : CMlPolynomial A n) (x : Vector B n)
    (v : Fin (2 ^ t) → B) :
    ((v, x.get), (traceHeadLayout e).components (unpackCoefficients e F)) ∈
        (traceHeadData e).openingClaimRel n ↔
      e v = F.eval (x.map (algebraMap B A)) := by
  set ps := (traceHeadLayout e).components (unpackCoefficients e F)
  have h := (traceHeadData e).packedMLE_eval_embedded ps x.get
  rw [← toMvPolynomialDeg1_eq_packedMLE] at h
  have hx : (x.map (algebraMap B A)).get = fun j => algebraMap B A (x.get j) :=
    funext fun j => by simp [Vector.get_map]
  have hb : ∀ w : Fin (2 ^ t) → B,
      ∑ i, algebraMap B A (w i) * (Basis.ofEquivFun e.symm) i = e w := fun w => by
    simp only [← Algebra.smul_def, ← Basis.equivFun_symm_apply, Basis.equivFun_ofEquivFun,
      LinearEquiv.symm_symm]
  rw [CMlPolynomial.eval_eq_eval_toMvPolynomial, hx]
  change _ ↔ e v = MvPolynomial.eval _ (CMlPolynomial.toMvPolynomialDeg1 F).val
  rw [h, show (∑ i, algebraMap B A (MvPolynomial.eval x.get (ps i).val) *
      (Basis.ofEquivFun e.symm) i) = e (fun i => MvPolynomial.eval x.get (ps i).val) from hb _,
    e.injective.eq_iff, funext_iff]
  rfl

/-- A ring value is the evaluation of `F` at the embedded retained point exactly when it is the
single shared slice of the `packedMLE` of the layout's components of the decoding of `F`. -/
theorem eval_eq_iff_sliceRel (F : CMlPolynomial A n) (x : Vector B n) (Y : A) :
    Y = F.eval (x.map (algebraMap B A)) ↔
      ((fun _ => Y), (traceHeadData e).packedMLE
          ((traceHeadLayout e).components (unpackCoefficients e F))) ∈
        (traceHeadData e).sliceRel n x.get := by
  have hY : (fun _ : Unit => Y) = (traceHeadData e).transpose (e.symm Y) :=
    funext fun _ => by rw [traceHeadData_transpose, LinearEquiv.apply_symm_apply]
  rw [hY, ← (traceHeadData e).openingClaimRel_iff_sliceRel,
    openingClaimRel_unpackCoefficients_iff, LinearEquiv.apply_symm_apply]

end SharedLayer

section Protocol

variable {q : ℕ} [Fact (Nat.Prime q)] [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (α κ : ℕ) {innerRows messageDigits outerRows innerDigits dRows m r : ℕ}
  (hk : 2 * 2 ^ κ ∣ 2 ^ α) (h2 : (2 : ZMod q) ≠ 0)

/-- The forwarded ring claim opens validly exactly when the weak opening is valid and the sent
value is the single shared slice of the `packedMLE` of the decoded committed polynomial's layout
components. -/
theorem output_mem_relPolyEval_iff_sliceRel
    (pp : PublicParamsD (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (base : ZMod q) (βSq γ bound : ℕ)
    (s : Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (Y : Rq (powTwoCyclotomic (R := ZMod q) α))
    (w : QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :
    (output α κ s Y, w) ∈ relPolyEval (powTwoCyclotomic (R := ZMod q) α) pp base βSq γ bound ↔
      VerifiedOpening (powTwoCyclotomic (R := ZMod q) α) base βSq γ bound
          pp.toPublicParams s.u w ∧
        ((fun _ => Y), (traceHeadData (coefficientEquiv q α κ h2 hk)).packedMLE
            ((traceHeadLayout (coefficientEquiv q α κ h2 hk)).components
              (unpackCoefficients (coefficientEquiv q α κ h2 hk)
                (extractedPoly (powTwoCyclotomic (R := ZMod q) α) base w)))) ∈
          (traceHeadData (coefficientEquiv q α κ h2 hk)).sliceRel (r + m) (s.xl ++ s.xh).get := by
  rw [output_mem_relPolyEval_iff α κ hk h2 pp base βSq γ bound s Y w, ← eval_eq_iff_sliceRel]
  rfl

/-- The trace check says that the claimed scalar is the layout-weighted sum of the `ψ`-coordinates
of the sent value. -/
theorem check_iff_layout_weight (base : ZMod q)
    (s : Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (Y : Rq (powTwoCyclotomic (R := ZMod q) α)) :
    check α κ hk s Y = true ↔ s.value = ∑ j,
      (traceHeadLayout (n := r + m) (coefficientEquiv q α κ h2 hk)).weight (s.xl ++ s.xh, s.xp) j *
        (coefficientEquiv q α κ h2 hk).symm Y j := by
  rw [check_iff_observation α κ hk h2 base]
  change s.value = ∑ j, (coefficientEquiv q α κ h2 hk).symm Y j *
    (CMlPolynomial.monomialBasis s.xp).get j ↔ _
  exact Iff.of_eq (congrArg (s.value = ·) (Finset.sum_congr rfl fun j _ => mul_comm _ _))

/-- **Hachi §3.1 conformance.** The trace head accepts a sent ring value with a validly opening
forwarded claim exactly when the weak opening is valid, the sent value is the single shared slice
of the `packedMLE` of the decoded committed polynomial's layout components, and the claimed scalar
is the layout-weighted sum of its `ψ`-coordinates. -/
theorem traceHead_conforms
    (pp : PublicParamsD (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (base : ZMod q) (βSq γ bound : ℕ)
    (s : Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (Y : Rq (powTwoCyclotomic (R := ZMod q) α))
    (w : QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :
    (check α κ hk s Y = true ∧
        (output α κ s Y, w) ∈ relPolyEval (powTwoCyclotomic (R := ZMod q) α) pp base βSq γ bound) ↔
      VerifiedOpening (powTwoCyclotomic (R := ZMod q) α) base βSq γ bound
          pp.toPublicParams s.u w ∧
        ((fun _ => Y), (traceHeadData (coefficientEquiv q α κ h2 hk)).packedMLE
            ((traceHeadLayout (coefficientEquiv q α κ h2 hk)).components
              (unpackCoefficients (coefficientEquiv q α κ h2 hk)
                (extractedPoly (powTwoCyclotomic (R := ZMod q) α) base w)))) ∈
          (traceHeadData (coefficientEquiv q α κ h2 hk)).sliceRel (r + m) (s.xl ++ s.xh).get ∧
        s.value = ∑ j, (traceHeadLayout (n := r + m) (coefficientEquiv q α κ h2 hk)).weight
          (s.xl ++ s.xh, s.xp) j * (coefficientEquiv q α κ h2 hk).symm Y j := by
  rw [check_iff_layout_weight α κ hk h2 base,
    output_mem_relPolyEval_iff_sliceRel α κ hk h2 pp base βSq γ bound]
  tauto

/-- The accepting condition of `traceHead_conforms` holds exactly for a claim in the scalar
relation and the honest sent value. -/
theorem traceHead_accepts_iff
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

/-- The input relation through the shared layout: `relScalarEval` is a valid weak opening whose
decoded source reconstructs, via `traceHeadLayout.reconstruct`, as the layout-weighted sum of the
component evaluations at the retained point. -/
theorem mem_relScalarEval_iff_layout
    (pp : PublicParamsD (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (base : ZMod q) (βSq γ bound : ℕ)
    (s : Statement q α κ innerRows messageDigits outerRows innerDigits dRows m r)
    (w : QuadEvalWitness (powTwoCyclotomic (R := ZMod q) α)
      innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :
    (s, w) ∈ relScalarEval α κ hk h2 pp base βSq γ bound ↔
      VerifiedOpening (powTwoCyclotomic (R := ZMod q) α) base βSq γ bound
          pp.toPublicParams s.u w ∧
        s.value = ∑ j, (traceHeadLayout (n := r + m) (coefficientEquiv q α κ h2 hk)).weight
          (s.xl ++ s.xh, s.xp) j *
            MvPolynomial.aeval ((traceHeadLayout (n := r + m) (coefficientEquiv q α κ h2 hk)).point
              (s.xl ++ s.xh, s.xp))
            (((traceHeadLayout (coefficientEquiv q α κ h2 hk)).components
              (unpackCoefficients (coefficientEquiv q α κ h2 hk)
                (extractedPoly (powTwoCyclotomic (R := ZMod q) α) base w))) j).val := by
  refine and_congr_right fun _ => ?_
  exact eq_comm.trans (iff_of_eq (congrArg (s.value = ·)
    ((traceHeadLayout (coefficientEquiv q α κ h2 hk)).reconstruct (s.xl ++ s.xh, s.xp)
      (unpackCoefficients (coefficientEquiv q α κ h2 hk)
        (extractedPoly (powTwoCyclotomic (R := ZMod q) α) base w)))))

end Protocol

/-! The conformance theorem, the library identification and the head's read-back depend only on
the standard axioms. -/

/--
info: 'ArkLibTest.RingSwitchingConformance.Hachi.traceHead_conforms' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLibTest.RingSwitchingConformance.Hachi.traceHead_conforms

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
  (traceHead_conforms 1 0 hk h2 pp 2 6 1 1 s _ w).1
    ((traceHead_accepts_iff 1 0 hk h2 pp 2 6 1 1 s _ w).2 ⟨source_valid.1, rfl⟩)

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
  have hbad := ((traceHead_accepts_iff 1 0 hk h2 pp 2 6 1 1 bad Y w).1
    ((traceHead_conforms 1 0 hk h2 pp 2 6 1 1 bad Y w).2 h)).1
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
