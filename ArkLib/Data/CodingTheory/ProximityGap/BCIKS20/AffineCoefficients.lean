/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.AffineSpaces

/-!
# Correlated agreement from uniformly sampled affine coefficients

Uniform coefficient vectors induce the uniform distribution on their affine image, even
when the directions are dependent. This gives a coefficient-form BCIKS20 bound for batching.
-/

@[expose] public section

namespace ProximityGap

open OracleComp Finset
open scoped NNReal ENNReal ProbabilityTheory

variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable (m : ℕ)

/-- Uniform coefficients induce the uniform distribution on their affine image, including
linearly dependent and zero directions. The fibers are translates of the kernel. -/
theorem uniform_affine_combination {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : Fin (m + 1) → ι → F) (P : (ι → F) → Prop) :
    Pr{let cs ← $ᵗ (Fin m → F)}[P (u 0 + ∑ i, cs i • u i.succ)] =
    Pr{let y ← $ᵗ ↥(Affine.affineSubspaceAtOrigin (F := F) (u 0) (Fin.tail u))}[
      P y.1] := by
  classical
  let L : (Fin m → F) →ₗ[F] (ι → F) :=
    { toFun := fun c ↦ ∑ i, c i • u i.succ
      map_add' := by intro a b; simp [add_smul, sum_add_distrib]
      map_smul' := by intro a b; simp [Finset.smul_sum, smul_smul] }
  let U := ↥(Affine.affineSubspaceAtOrigin (F := F) (u 0) (Fin.tail u))
  have lift_exists (y : U) : ∃ c, y.1 = u 0 + L c :=
    (Affine.mem_affineSubspaceFrom_iff _ _ _).mp y.2
  let t : U → (Fin m → F) := fun y ↦ (lift_exists y).choose
  have ht (y : U) : y.1 = u 0 + L (t y) := (lift_exists y).choose_spec
  let f : (Fin m → F) → U := fun c ↦
    ⟨u 0 + L c, (Affine.mem_affineSubspaceFrom_iff _ _ _).mpr ⟨c, rfl⟩⟩
  let e : (Fin m → F) ≃ U × L.ker :=
    { toFun := fun c ↦ (f c, ⟨c - t (f c), by
        change L (c - t (f c)) = 0
        rw [map_sub, sub_eq_zero]
        exact add_left_cancel (ht (f c))⟩)
      invFun := fun y ↦ t y.1 + y.2.1
      left_inv := by intro c; dsimp; abel
      right_inv := by
        rintro ⟨y, z⟩
        have hf : f (t y + z.1) = y := by
          apply Subtype.ext
          change u 0 + L (t y + z.1) = y.1
          rw [map_add, z.2, add_zero, ← ht]
        apply Prod.ext
        · exact hf
        · apply Subtype.ext
          change t y + z.1 - t (f (t y + z.1)) = z.1
          rw [hf]; abel }
  have h := SampleableType.prEvent_uniformSample_equiv e (fun y ↦ P y.1.1)
  change Pr{let c ← $ᵗ (Fin m → F)}[P (u 0 + L c)] = _
  change Pr{let c ← $ᵗ (Fin m → F)}[P (e c).1.1] = _
  rw [h, SampleableType.prEvent_uniformSample_prod]
  simp only [prEvent_norm]
  conv_rhs => rw [← bind_pure_comp]
  apply OracleComp.prEvent_bind_congr_of_support
  intro x _
  simpa only [bind_pure_comp] using
    OracleComp.prEvent_bind_const ($ᵗ L.ker : ProbComp _) (pure (P x.val))

/-- Coefficient-form affine-space correlated agreement, with the same radius and error
as `correlatedAgreement_affine_spaces`. No independence of the directions is required. -/
theorem correlatedAgreement_affine_coefficients
    {ι : Type} [Fintype ι] [Nonempty ι] [NeZero m]
    {deg : ℕ} {domain : ι ↪ F} {δ : ℝ≥0}
    (hdeg : 0 < deg) (hδ_pos : 0 < δ)
    (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
    (hRS : deg + 1 ≤ Fintype.card ι) (hε : errorBound δ deg domain < 1)
    (u : Fin (m + 1) → ι → F)
    (hprob : Pr{let cs ← $ᵗ (Fin m → F)}[Code.relDistFromCode
      (u 0 + ∑ i, cs i • u i.succ)
        (ReedSolomon.code domain deg).carrier ≤ δ] > errorBound δ deg domain) :
    Code.jointAgreement (ReedSolomon.code domain deg).carrier δ u := by
  classical
  apply correlatedAgreement_affine_spaces hdeg hδ_pos hδ hRS hε u
  exact lt_of_lt_of_eq hprob (uniform_affine_combination m u (fun f ↦
    Code.relDistFromCode f (ReedSolomon.code domain deg).carrier ≤ δ))

end ProximityGap
