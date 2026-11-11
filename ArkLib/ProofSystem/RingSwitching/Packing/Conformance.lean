/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

module

public import ArkLib.ProofSystem.RingSwitching.Packing.TensorPrefix
public import ArkLib.ProofSystem.RingSwitching.Packing.BatchingAlgebra
public import ArkLib.ProofSystem.RingSwitching.Packing.FinalAlgebra

/-!
# Profile coordinates and prefix packing

The embedded carrier evaluation represents exactly the component opening family of prefix
packing. Its columns reconstruct the scalar query; its rows are the transposed slices of the
same packed polynomial. The closing tensor equality value evaluates the same public multiplier.
The protocol and its verifier equations are defined in `Packing.TensorPrefix`.
-/

@[expose] public section

open Module MvPolynomial RingSwitching Sumcheck.Structured

noncomputable section

namespace RingSwitching.Packing.Conformance

section SharedLayer

variable {K L : Type} [CommRing K] [CommRing L] [Algebra K L] {κ ℓ ℓ' : ℕ}
  (P : RingSwitchingProfile K L κ) (h_l : ℓ = ℓ' + κ)

/-- The batching weights of a batching challenge: the equality weights of the Boolean cube. -/
abbrev batchingWeight (c : Fin κ → L) : (Fin κ → Fin 2) → L :=
  fun u => eqTilde (u : Fin κ → L) c

/-- The rows of a carrier are the shared slices of a packed polynomial exactly when its columns
are the opening values of the components: the row family is the shared transpose of the column
family. -/
theorem sliceRel_iff_openingClaimRel {m : ℕ} (z : P.A)
    (ps : (Fin κ → Fin 2) → K⦃≤ 1⦄[X Fin m]) (x : Fin m → L) :
    (P.decomposeRows z, (Packing.PackingData.ofBasis P.basis).packedMLE ps) ∈
        (Packing.PackingData.ofBasis P.basis).sliceRel m x ↔
      ((P.decomposeColumns z, x), ps) ∈
        (Packing.PackingData.ofBasis P.basis).openingClaimRel m := by
  rw [← P.transpose_decomposeColumns, ← Packing.PackingData.openingClaimRel_iff_sliceRel]

/-- A carrier is the honest tensor evaluation of the packed source exactly when its rows are the
shared slices of the `packedMLE` of the source's prefix-layout components. -/
theorem embedded_MLP_eval_packMLE_eq_iff_sliceRel (t : MultilinearPoly K ℓ) (r : Fin ℓ → L)
    (z : P.A) :
    embedded_MLP_eval κ L K P ℓ ℓ' h_l (packMLE κ L K ℓ ℓ' h_l P.basis t) r = z ↔
      (P.decomposeRows z, (Packing.PackingData.ofBasis P.basis).packedMLE
          ((TensorPrefix.layout P h_l).components t)) ∈
        (Packing.PackingData.ofBasis P.basis).sliceRel ℓ'
          ((TensorPrefix.layout P h_l).point r) := by
  rw [packMLE_eq_packedPrefixLayout]
  exact embedded_MLP_eval_eq_iff_sliceRel P h_l _ r z

/-- A carrier is the honest tensor evaluation of the packed source exactly when its columns are
the opening values of the source's prefix-layout components at the retained point. -/
theorem embedded_MLP_eval_packMLE_eq_iff_openingClaimRel (t : MultilinearPoly K ℓ)
    (r : Fin ℓ → L) (z : P.A) :
    embedded_MLP_eval κ L K P ℓ ℓ' h_l (packMLE κ L K ℓ ℓ' h_l P.basis t) r = z ↔
      ((P.decomposeColumns z, (TensorPrefix.layout P h_l).point r),
          (TensorPrefix.layout P h_l).components t) ∈
        (Packing.PackingData.ofBasis P.basis).openingClaimRel ℓ' := by
  rw [embedded_MLP_eval_packMLE_eq_iff_sliceRel, sliceRel_iff_openingClaimRel]

/-- The column check says that the claim is the layout-weighted sum of the carrier's column
family. -/
theorem check_iff_layout_weight [DecidableEq L] (s : L) (r : Fin ℓ → L) (z : P.A) :
    performCheckOriginalEvaluation κ L K P ℓ ℓ' h_l s r z = true ↔
      s = ∑ v, (TensorPrefix.layout P h_l).weight r v * P.decomposeColumns z v :=
  (TensorPrefix.check_iff P h_l r s z).symm

end SharedLayer

end RingSwitching.Packing.Conformance

end
