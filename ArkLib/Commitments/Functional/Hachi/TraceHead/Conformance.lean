/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import ArkLib.Commitments.Functional.Hachi.TraceHead.Protocol
public import ArkLib.ProofSystem.RingSwitching.Packing.Relations

/-!
# Trace-head conformance to shared packing

These library lemmas identify the scalar trace head's production relations and accepting check
with the shared packing data and monomial claim layout. The protocol uses its trace check and
`CheckedObservation`; this equivalence does not provide a batching or sumcheck protocol.
-/

@[expose] public section

open CompPoly ArkLib.Lattices.CyclotomicModulus
open ArkLib.Lattices.Hachi
open ArkLib.Lattices.Ajtai.InnerOuter ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding
open RingSwitching.Packing Module

namespace ArkLib.Lattices.Hachi.TraceHead

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

end ArkLib.Lattices.Hachi.TraceHead
