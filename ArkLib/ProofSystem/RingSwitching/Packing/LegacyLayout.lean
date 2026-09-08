/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.Prelude
import ArkLib.ProofSystem.RingSwitching.Packing.ProfileCoordinates
import ArkLib.ProofSystem.RingSwitching.Packing.ScalarHead.Layout
import ArkLib.ProofSystem.RingSwitching.Packing.Relations

/-!
# Native DP24 packing and the shared component layout

The native implementation stores the original dimension separately from the packed
dimension. The equalities here preserve its actual prefix/suffix index casts and identify
its Boolean-table packing with the shared polynomial packing of DP24 components.
-/

noncomputable section

namespace RingSwitching

open Module MvPolynomial Sumcheck.Structured

variable {K L : Type} [CommRing K] [CommRing L] [Algebra K L]
  {κ ℓ ℓ' : ℕ} [NeZero κ] [NeZero ℓ]
  (h_l : ℓ = ℓ' + κ) (β : Basis (Fin κ → Fin 2) K L)

/-- Preserve the native polynomial while identifying its dimension with packed prefix
followed by retained suffix. -/
def legacySourceEquiv : MultilinearPoly K ℓ ≃ MultilinearPoly K (κ + ℓ') :=
  Equiv.cast (congrArg (fun n => ↥(MultilinearPoly K n)) (h_l.trans (Nat.add_comm ℓ' κ)))

omit [NeZero κ] [NeZero ℓ] in
/-- The native concatenation agrees with the generic prefix/suffix concatenation. -/
theorem legacy_concat (v : Fin κ → Fin 2) (w : Fin ℓ' → Fin 2) :
    (fun i : Fin (κ + ℓ') =>
      if h : i.val < κ then v ⟨i.val, h⟩ else w ⟨i.val - κ, by omega⟩) =
        Fin.append v w := by
  funext i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [Fin.val_castAdd, j.isLt, ↓reduceDIte,
      Fin.append_left]
  · simp only [Fin.val_natAdd, Nat.not_lt_of_ge (Nat.le_add_right _ _), ↓reduceDIte,
      Nat.add_sub_cancel_left, Fin.append_right]

set_option backward.isDefEq.respectTransparency false in
/-- The actual Boolean-table packing equals shared packing of the actual DP24 components. -/
theorem packMLE_eq_packedMLE (t : MultilinearPoly K ℓ) :
    packMLE κ L K ℓ ℓ' h_l β t =
      (Packing.sameAlgebra β).packedMLE
        (splitFirst κ ℓ' (legacySourceEquiv h_l t)) := by
  have hdim : ℓ = κ + ℓ' := h_l.trans (Nat.add_comm ℓ' κ)
  cases hdim
  apply Subtype.ext
  apply eq_of_degreeOf_le_one_of_eval_zeroOne_eq _ _
    ((mem_restrictDegree_iff_degreeOf_le _ _).mp (packMLE κ L K _ ℓ' h_l β t).property)
    ((mem_restrictDegree_iff_degreeOf_le _ _).mp
      ((Packing.sameAlgebra β).packedMLE (splitFirst κ ℓ' (legacySourceEquiv h_l t))).property)
  intro w
  have hcast : (w : Fin ℓ' → L) = fun i => algebraMap K L ((w : Fin ℓ' → K) i) :=
    funext fun i => (map_natCast (algebraMap K L) _).symm
  rw [hcast]
  refine Eq.trans ?_ ((Packing.sameAlgebra β).packedMLE_eval_embedded
    (splitFirst κ ℓ' (legacySourceEquiv h_l t)) (w : Fin ℓ' → K)).symm
  simp only [packMLE, ← hcast, MLE_eval_zeroOne, Basis.equivFun_symm_apply,
    legacySourceEquiv, Equiv.cast_refl, Equiv.refl_apply,
    splitFirst_eval, Packing.sameAlgebra, Algebra.smul_def]
  apply Finset.sum_congr rfl
  intro v _
  have hpoint : (fun i : Fin (κ + ℓ') =>
      ((if h : i.val < κ then v ⟨i.val, h⟩ else w ⟨i.val - κ, by omega⟩ : Fin 2) : K)) =
        Fin.append (v : Fin κ → K) (w : Fin ℓ' → K) := by
    calc
      _ = (fun i => ((Fin.append v w i : Fin 2) : K)) :=
        congrArg (fun q : Fin (κ + ℓ') → Fin 2 => (q : Fin (κ + ℓ') → K))
          (legacy_concat (ℓ := κ + ℓ') v w)
      _ = _ := cast_append_bool κ ℓ' v w
  exact congrArg (fun q => algebraMap K L (eval q t.val) * β v) hpoint

/-- The native packing uses the published DP24 layout, including the original dimension cast. -/
theorem packMLE_eq_dp24Layout (t : MultilinearPoly K ℓ) :
    packMLE κ L K ℓ ℓ' h_l β t =
      (Packing.sameAlgebra β).packedMLE
        ((Packing.ScalarHead.dp24Layout (Packing.sameAlgebra β) ℓ' κ (Equiv.refl _)).components
          (legacySourceEquiv h_l t)) :=
  packMLE_eq_packedMLE h_l β t

omit [NeZero κ] in
set_option backward.isDefEq.respectTransparency false in
/-- Native unpacking equals coefficient-coordinate unpacking followed by the shared layout join. -/
theorem unpackMLE_eq_joinFirst (p : MultilinearPoly L ℓ') :
    legacySourceEquiv h_l (unpackMLE κ L K ℓ ℓ' h_l β p) =
      joinFirst κ ℓ' ((Packing.sameAlgebra β).unpack p) := by
  have hdim : ℓ = κ + ℓ' := h_l.trans (Nat.add_comm ℓ' κ)
  cases hdim
  apply Subtype.ext
  apply eq_of_degreeOf_le_one_of_eval_zeroOne_eq _ _
    ((mem_restrictDegree_iff_degreeOf_le _ _).mp
      (legacySourceEquiv h_l (unpackMLE κ L K _ ℓ' h_l β p)).property)
    ((mem_restrictDegree_iff_degreeOf_le _ _).mp
      (joinFirst κ ℓ' ((Packing.sameAlgebra β).unpack p)).property)
  intro z
  simp only [legacySourceEquiv, Equiv.cast_refl, Equiv.refl_apply, unpackMLE,
    joinFirst, MLE_eval_zeroOne, Packing.PackingData.unpack_eval_zeroOne,
    Packing.sameAlgebra]
  congr 2
  apply congrArg (fun r => eval r p.val)
  funext i
  apply congrArg (fun j : Fin (κ + ℓ') => ((z j : Fin 2) : L))
  exact Fin.ext (Nat.add_comm _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The actual native packer recovers every packed polynomial after native unpacking. -/
theorem packMLE_unpackMLE (p : MultilinearPoly L ℓ') :
    packMLE κ L K ℓ ℓ' h_l β (unpackMLE κ L K ℓ ℓ' h_l β p) = p := by
  rw [packMLE_eq_packedMLE, unpackMLE_eq_joinFirst, splitFirst_joinFirst]
  exact (Packing.sameAlgebra β).packedMLE_unpack p

set_option backward.isDefEq.respectTransparency false in
/-- The actual native unpacker recovers the original polynomial after native packing. -/
theorem unpackMLE_packMLE (t : MultilinearPoly K ℓ) :
    unpackMLE κ L K ℓ ℓ' h_l β (packMLE κ L K ℓ ℓ' h_l β t) = t := by
  apply (legacySourceEquiv h_l).injective
  rw [unpackMLE_eq_joinFirst, packMLE_eq_packedMLE,
    Packing.PackingData.unpack_packedMLE, joinFirst_splitFirst]

omit [NeZero κ] [NeZero ℓ] in
/-- The shared DP24 reconstruction uses exactly the native evaluation point's two blocks. -/
theorem legacy_aeval_split (t : MultilinearPoly K ℓ) (r : Fin ℓ → L) :
    aeval r t.val =
      ∑ v : Fin κ → Fin 2,
        eqTilde (v : Fin κ → L) (fun i => r ⟨i.val, by omega⟩) *
          aeval (getEvaluationPointSuffix κ L ℓ ℓ' h_l r)
            (splitFirst κ ℓ' (legacySourceEquiv h_l t) v).val := by
  have hdim : ℓ = κ + ℓ' := h_l.trans (Nat.add_comm ℓ' κ)
  cases hdim
  have hr : Fin.append (fun i : Fin κ => r ⟨i.val, by omega⟩)
      (getEvaluationPointSuffix κ L (κ + ℓ') ℓ' h_l r) = r := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [Fin.append_left]
      rfl
    · rw [Fin.append_right]
      apply congrArg r
      exact Fin.ext (Nat.add_comm _ _)
  have h := aeval_append_splitFirst κ ℓ' t
    (fun i => r ⟨i.val, by omega⟩) (getEvaluationPointSuffix κ L (κ + ℓ') ℓ' h_l r)
  rw [hr] at h
  simpa only [legacySourceEquiv, Equiv.cast_refl, Equiv.refl_apply] using h

end RingSwitching

end
