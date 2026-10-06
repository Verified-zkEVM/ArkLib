/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.Commitments.Functional.Hachi.EvalSplit
public import ArkLib.ProofSystem.RingSwitching.Packing.Relations
public import ArkLib.ProofSystem.RingSwitching.Packing.ScalarHead.Layout
public import ArkLib.ToCompPoly.Multilinear.Basic

/-!
# Packing monomial coefficients along the final variables

The retained variables come first and the packed variables last. Indices use the existing
little-endian `Hachi.splitEquiv`; this is coefficient packing, not Boolean-table packing.

The packing is an instance of the shared packed-polynomial layer of `RingSwitching.Packing`.
`traceHeadData e` is `PackingData.ofBaseOpening` at the basis given by `e`: the base ring is also
the opening algebra, so there is one opening coordinate (`ιE = Unit`) and the coordinate
transpose is trivial. `traceHeadLayout e` is a `ScalarHead.ClaimLayout` whose components are the
monomial-coefficient rows of the packed variables (`coefficientRows`), transported to
`MvPolynomial` by `CMlPolynomial.equivMvPolynomialDeg1`; it is not the Boolean-restriction
`ScalarHead.packedSuffixLayout`. Its `reconstruct` is proved here, from `evalSplit_eq_eval` and
`CMlPolynomial.eval_eq_eval_toMvPolynomial`.

Under the transport `packCoefficients e` is the shared `packedMLE` of the layout's components
(`toMvPolynomialDeg1_packCoefficients`). Evaluating at an embedded retained point commutes with
packing by the shared `PackingData.packedMLE_eval_embedded`; this gives the opening relation of
the components (`openingClaimRel_unpackCoefficients_iff`), and with the layout's reconstruction
the read-back identity `unpackCoefficients_eval`.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
  Polynomial Commitments over Extension Fields*][NOZ26]
-/

@[expose] public section

open CompPoly

namespace ArkLib.Lattices.Hachi.TraceHead

section Coefficients

variable {B A : Type*} [CommRing B] [CommRing A] [Algebra B A] {n t : ℕ}
variable (e : (Fin (2 ^ t) → B) ≃ₗ[B] A)

/-- Pack each vector of coefficients in the final `t` variables. -/
def packCoefficients (f : CMlPolynomial B (n + t)) : CMlPolynomial A n :=
  Vector.ofFn fun i => e (fun j => f.get (splitEquiv n t (j, i)))

/-- Decode each ring coefficient in its packing coordinates. -/
def unpackCoefficients (F : CMlPolynomial A n) : CMlPolynomial B (n + t) :=
  Vector.ofFn fun k => e.symm (F.get ((splitEquiv n t).symm k).2)
    ((splitEquiv n t).symm k).1

/-- Packing and then decoding recovers every monomial coefficient. -/
@[simp] theorem unpackCoefficients_packCoefficients (f : CMlPolynomial B (n + t)) :
    unpackCoefficients e (packCoefficients e f) = f := by
  apply Vector.ext
  intro i hi
  simp [unpackCoefficients, packCoefficients]
  rfl

/-- Decoding and then packing recovers the ring polynomial. -/
@[simp] theorem packCoefficients_unpackCoefficients (F : CMlPolynomial A n) :
    packCoefficients e (unpackCoefficients e F) = F := by
  apply Vector.ext
  intro i hi
  simp [unpackCoefficients, packCoefficients]
  rfl

/-- The monomial-coefficient rows along the final `t` variables: row `j` holds the
coefficients of the monomials whose packed-variable exponents are the bits of `j`, that is,
column `j` of `toMatrix`. This splits coefficients, not Boolean restrictions. -/
def coefficientRows : CMlPolynomial B (n + t) ≃ (Fin (2 ^ t) → CMlPolynomial B n) where
  toFun f j := Vector.ofFn fun i => toMatrix f i j
  invFun rs := toPolynomial (Matrix.of fun i j => (rs j).get i)
  left_inv f := by
    simp only [Vector.get_ofFn]
    exact toPolynomial_toMatrix f
  right_inv rs := by
    funext j
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_ofFn, toMatrix_toPolynomial, Matrix.of_apply]
    rfl

end Coefficients

/-! ## The trace head as a shared packing layout -/

section Layout

open RingSwitching.Packing Module

variable {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {n t : ℕ}
variable (e : (Fin (2 ^ t) → B) ≃ₗ[B] A)

/-- Packing data with the basis given by `e` and opening points in `B` itself. -/
noncomputable abbrev traceHeadData : PackingData B :=
  PackingData.ofBaseOpening (Basis.ofEquivFun e.symm)

/-- The scalar source as a claim layout over `traceHeadData e`. The components are the
monomial-coefficient rows of the final `t` variables, transported to `MvPolynomial`; the weights
are the monomial basis at the packed suffix point. -/
noncomputable def traceHeadLayout : ScalarHead.ClaimLayout (traceHeadData e) n where
  Source := CMlPolynomial B (n + t)
  Query := Vector B n × Vector B t
  components := coefficientRows.trans
    (Equiv.piCongrRight fun _ => CMlPolynomial.equivMvPolynomialDeg1)
  point q := q.1.get
  weight q j := (CMlPolynomial.monomialBasis q.2).get j
  eval q f := f.eval (q.1 ++ q.2)
  reconstruct q f := by
    obtain ⟨x, xp⟩ := q
    change f.eval (x ++ xp) = ∑ j, (CMlPolynomial.monomialBasis xp).get j *
      MvPolynomial.eval x.get (CMlPolynomial.toMvPolynomial (coefficientRows f j))
    simp only [← CMlPolynomial.eval_eq_eval_toMvPolynomial]
    rw [← evalSplit_eq_eval]
    simp only [evalSplit, splitForm, dot_eq_sum, matVecMul_apply, Finset.mul_sum,
      CMlPolynomial.eval, Vector.dotProduct_eq_root_dotProduct, _root_.dotProduct]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    simp only [coefficientRows, Equiv.coe_fn_mk, Vector.get_ofFn]
    ring

/-- Transported to `MvPolynomial`, the coefficient packing is the shared `packedMLE` of the
layout's components. -/
theorem toMvPolynomialDeg1_packCoefficients (f : CMlPolynomial B (n + t)) :
    CMlPolynomial.toMvPolynomialDeg1 (packCoefficients e f) =
      (traceHeadData e).packedMLE ((traceHeadLayout e).components f) := by
  rw [← (traceHeadData e).packedMLE_unpack (CMlPolynomial.toMvPolynomialDeg1 _)]
  congr 1
  funext j
  refine Subtype.ext (MvPolynomial.ext _ _ fun d => ?_)
  rw [PackingData.unpack_coeff]
  change (Basis.ofEquivFun e.symm).repr
      ((CMlPolynomial.toMvPolynomial (packCoefficients e f)).coeff d) j =
    (CMlPolynomial.toMvPolynomial (coefficientRows f j)).coeff d
  rw [Basis.ofEquivFun_repr_apply,
    CMlPolynomial.coeff_of_toMvPolynomial_eq_coeff_of_CMlPolynomial,
    CMlPolynomial.coeff_of_toMvPolynomial_eq_coeff_of_CMlPolynomial]
  split_ifs
  · simp [packCoefficients, coefficientRows, toMatrix]
  · simp

/-- The opening claims of the layout's components of a decoded polynomial hold exactly when `e`
maps the claimed values to the ring evaluation at the embedded retained point. The ring
evaluation is the evaluation of the shared `packedMLE` of the components, which
`PackingData.packedMLE_eval_embedded` writes as the packing of the component evaluations. -/
theorem openingClaimRel_unpackCoefficients_iff (F : CMlPolynomial A n) (x : Vector B n)
    (v : Fin (2 ^ t) → B) :
    ((v, x.get), (traceHeadLayout e).components (unpackCoefficients e F)) ∈
        (traceHeadData e).openingClaimRel n ↔
      e v = F.eval (x.map (algebraMap B A)) := by
  set ps := (traceHeadLayout e).components (unpackCoefficients e F)
  have h := (traceHeadData e).packedMLE_eval_embedded ps x.get
  rw [← toMvPolynomialDeg1_packCoefficients, packCoefficients_unpackCoefficients] at h
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

/-- The scalar polynomial evaluation is the inner product of the decoded ring evaluation and the
monomial basis at the packed suffix.

The decoded ring evaluation is the family of component evaluations, by the opening relation at
the honest values (`openingClaimRel_unpackCoefficients_iff`, hence
`PackingData.packedMLE_eval_embedded`), and the layout's `reconstruct` assembles the scalar
evaluation from them. It is stated for `B A : Type` because `PackingData` lives in `Type`. -/
theorem unpackCoefficients_eval (F : CMlPolynomial A n) (x : Vector B n) (xp : Vector B t) :
    (unpackCoefficients e F).eval (x ++ xp) =
      ∑ j, e.symm (F.eval (x.map (algebraMap B A))) j *
        (CMlPolynomial.monomialBasis xp).get j := by
  set ps := (traceHeadLayout e).components (unpackCoefficients e F)
  have hcoord : e.symm (F.eval (x.map (algebraMap B A))) =
      fun j => MvPolynomial.aeval x.get (ps j).val :=
    e.symm_apply_eq.mpr ((openingClaimRel_unpackCoefficients_iff e F x _).mp fun _ => rfl).symm
  refine ((traceHeadLayout e).reconstruct (x, xp) (unpackCoefficients e F)).trans
    (Finset.sum_congr rfl fun j _ => ?_)
  rw [hcoord, mul_comm]
  rfl

end Layout

end ArkLib.Lattices.Hachi.TraceHead
