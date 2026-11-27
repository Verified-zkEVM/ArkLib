/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.BlockStructure
public import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Composition

/-!
  # Append of structures with a layout per round

  `BlockCWSSStructure.append` composes two structures with layouts along protocol append: the
  appended protocol's left challenge rounds carry the layouts of the left structure, and its right
  challenge rounds those of the right one. It is the counterpart of `CWSSStructure.append` in
  `Composition.lean` and follows the same construction, with `layout` and `decompose` in place of
  the coordinate count, the alphabet and the threshold.

  ## Main results

  - `BlockCWSSStructure.append_layout_inl`, `BlockCWSSStructure.append_layout_inr`: the layouts of
    the appended structure.
  - `BlockCWSSStructure.append_decompose_inl`, `BlockCWSSStructure.append_decompose_inr`: its
    identifications of challenges with points, up to the boundary cast.
  - `BlockCWSSStructure.toShape_append`: its tree shape is the generic append of the component
    shapes, so the composition theorems of `Composition.lean`, stated for shapes, apply to it.

  ## Computability

  The structure is computable data; the results are propositions.
-/

@[expose] public section

open ProtocolSpec CoordinateWise

namespace BlockCWSSStructure

variable {m n : ℕ} {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- The component identification selected by a sum tag, as in `CWSSStructure.appendDecomposeSum`:
the matcher branches mention only the bound index, and the boundary cast is applied once, in
`append`. -/
def appendDecomposeSum (D₁ : BlockCWSSStructure pSpec₁) (D₂ : BlockCWSSStructure pSpec₂) :
    (s : pSpec₁.ChallengeIdx ⊕ pSpec₂.ChallengeIdx) →
      s.elim (fun i₁ => pSpec₁.Challenge i₁ ≃ (D₁.layout i₁).Point)
        (fun i₂ => pSpec₂.Challenge i₂ ≃ (D₂.layout i₂).Point)
  | Sum.inl i₁ => D₁.decompose i₁
  | Sum.inr i₂ => D₂.decompose i₂

/-- Binary append of structures with layouts: the layouts of `D₁` on the left challenge rounds and
those of `D₂` on the right ones. -/
def append (D₁ : BlockCWSSStructure pSpec₁) (D₂ : BlockCWSSStructure pSpec₂) :
    BlockCWSSStructure (pSpec₁ ++ₚ pSpec₂) where
  layout := fun i =>
    match ChallengeIdx.sumEquiv.symm i with
    | Sum.inl i₁ => D₁.layout i₁
    | Sum.inr i₂ => D₂.layout i₂
  decompose := fun i => cast (by
      rcases h : ChallengeIdx.sumEquiv.symm i with i₁ | i₂
      · have hi : i = ChallengeIdx.inl i₁ := by
          have hi' : i = ChallengeIdx.sumEquiv (Sum.inl i₁) :=
            (Equiv.symm_apply_eq ChallengeIdx.sumEquiv).mp h
          simpa [ChallengeIdx.sumEquiv_apply] using hi'
        subst i
        simp [ProtocolSpec.append, ChallengeIdx.inl]
      · have hi : i = ChallengeIdx.inr i₂ := by
          have hi' : i = ChallengeIdx.sumEquiv (Sum.inr i₂) :=
            (Equiv.symm_apply_eq ChallengeIdx.sumEquiv).mp h
          simpa [ChallengeIdx.sumEquiv_apply] using hi'
        subst i
        simp [ProtocolSpec.append, ChallengeIdx.inr])
    (appendDecomposeSum D₁ D₂ (ChallengeIdx.sumEquiv.symm i))
  arity := ChallengeTree.appendArity D₁.arity D₂.arity
  arity_eq := by
    intro i
    rcases h : ChallengeIdx.sumEquiv.symm i with i₁ | i₂
    · simpa [ChallengeTree.appendArity, h] using D₁.arity_eq i₁
    · simpa [ChallengeTree.appendArity, h] using D₂.arity_eq i₂

/-- The arity of an appended structure is the generic appended arity. -/
theorem append_arity (D₁ : BlockCWSSStructure pSpec₁) (D₂ : BlockCWSSStructure pSpec₂) :
    (append D₁ D₂).arity = ChallengeTree.appendArity D₁.arity D₂.arity := rfl

section AppendChar

variable (D₁ : BlockCWSSStructure pSpec₁) (D₂ : BlockCWSSStructure pSpec₂)

/-- The layout of an appended structure at a left index is the left component's. -/
@[simp] theorem append_layout_inl (i₁ : pSpec₁.ChallengeIdx) :
    (append D₁ D₂).layout (ChallengeIdx.inl i₁) = D₁.layout i₁ := by
  simp only [append, ChallengeIdx.sumEquiv_symm_inl]

/-- The layout of an appended structure at a right index is the right component's. -/
@[simp] theorem append_layout_inr (i₂ : pSpec₂.ChallengeIdx) :
    (append D₁ D₂).layout (ChallengeIdx.inr i₂) = D₂.layout i₂ := by
  simp only [append, ChallengeIdx.sumEquiv_symm_inr]

/-- The identification of an appended structure at a left index is the left component's, up to
the boundary cast. -/
theorem append_decompose_heqL {i : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx} {i₁ : pSpec₁.ChallengeIdx}
    (h : ChallengeIdx.sumEquiv.symm i = Sum.inl i₁) :
    HEq ((append D₁ D₂).decompose i) (D₁.decompose i₁) := by
  simp only [append]
  refine (cast_heq _ _).trans ?_
  rw [h]
  exact HEq.rfl

/-- The identification of an appended structure at a right index is the right component's, up to
the boundary cast. -/
theorem append_decompose_heqR {i : (pSpec₁ ++ₚ pSpec₂).ChallengeIdx} {i₂ : pSpec₂.ChallengeIdx}
    (h : ChallengeIdx.sumEquiv.symm i = Sum.inr i₂) :
    HEq ((append D₁ D₂).decompose i) (D₂.decompose i₂) := by
  simp only [append]
  refine (cast_heq _ _).trans ?_
  rw [h]
  exact HEq.rfl

/-- The identification of an appended structure at a left index is the left component's, up to
cast. -/
theorem append_decompose_inl (i₁ : pSpec₁.ChallengeIdx) :
    HEq ((append D₁ D₂).decompose (ChallengeIdx.inl i₁)) (D₁.decompose i₁) :=
  append_decompose_heqL D₁ D₂ (ChallengeIdx.sumEquiv_symm_inl i₁)

/-- The identification of an appended structure at a right index is the right component's, up to
cast. -/
theorem append_decompose_inr (i₂ : pSpec₂.ChallengeIdx) :
    HEq ((append D₁ D₂).decompose (ChallengeIdx.inr i₂)) (D₂.decompose i₂) :=
  append_decompose_heqR D₁ D₂ (ChallengeIdx.sumEquiv_symm_inr i₂)

end AppendChar

/-- The shape of an appended structure is the generic append of the component shapes. -/
theorem toShape_append (D₁ : BlockCWSSStructure pSpec₁) (D₂ : BlockCWSSStructure pSpec₂) :
    (append D₁ D₂).toShape = D₁.toShape.append D₂.toShape := by
  refine ChallengeTreeShape.ext rfl (heq_of_eq ?_)
  funext i challenges
  simp only [toShape, ChallengeTreeShape.append]
  split
  · rename_i i₁ heq
    obtain rfl : i = ChallengeIdx.inl i₁ := by
      have := (Equiv.symm_apply_eq ChallengeIdx.sumEquiv).mp heq
      simpa [ChallengeIdx.sumEquiv_apply] using this
    unfold nodeOk
    refine propext (CoordinateWise.Layout.isTree_congr (append_layout_inl D₁ D₂ i₁) ?_)
    refine Function.hfunext (by rw [append_layout_inl]) (fun j j' hj => ?_)
    refine heq_equiv_apply (by simp [ProtocolSpec.append, ChallengeIdx.inl])
      (by rw [append_layout_inl]) (append_decompose_inl D₁ D₂ i₁) ?_
    refine HEq.trans (heq_of_eq (congrArg challenges (Fin.ext ?_))) (cast_heq _ _).symm
    change j.val = j'.val
    exact (Fin.heq_ext_iff (by rw [append_layout_inl])).mp hj
  · rename_i i₂ heq
    obtain rfl : i = ChallengeIdx.inr i₂ := by
      have := (Equiv.symm_apply_eq ChallengeIdx.sumEquiv).mp heq
      simpa [ChallengeIdx.sumEquiv_apply] using this
    unfold nodeOk
    refine propext (CoordinateWise.Layout.isTree_congr (append_layout_inr D₁ D₂ i₂) ?_)
    refine Function.hfunext (by rw [append_layout_inr]) (fun j j' hj => ?_)
    refine heq_equiv_apply (by simp [ProtocolSpec.append, ChallengeIdx.inr])
      (by rw [append_layout_inr]) (append_decompose_inr D₁ D₂ i₂) ?_
    refine HEq.trans (heq_of_eq (congrArg challenges (Fin.ext ?_))) (cast_heq _ _).symm
    change j.val = j'.val
    exact (Fin.heq_ext_iff (by rw [append_layout_inr])).mp hj

end BlockCWSSStructure
