/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.OracleComp.Vector
public import VCVio.OracleComp.Constructions.SampleableType.Measure
-- Exact traversal identities unfold the defining sampler body without changing its instance.
import all VCVio.OracleComp.Constructions.SampleableType.Basic

/-!
# Uniform sampling helpers

This file supplies opt-in uniform samplers for finite subtypes.  The instances are scoped because
many concrete types already have executable `SampleableType` instances, whose implementation
should remain canonical.  Opening `ProbabilityTheory` enables the noncomputable enumeration
fallback for a nonempty predicate subtype or finite-set subtype.
-/

@[expose] public section

namespace ProbabilityTheory

/-- A nonempty subtype of a finite type can be sampled uniformly by enumeration.

This is a low-priority scoped fallback so an executable `FinEnum`-based sampler wins whenever one
is available. -/
noncomputable scoped instance (priority := 50) instSampleableTypeSubtype
    {α : Type} [Fintype α] (p : α → Prop) [Nonempty {x // p x}] :
    SampleableType {x // p x} := by
  classical
  exact SampleableType.subtype α p

/-- A nonempty finite set can be sampled uniformly, even when its ambient type is infinite. -/
noncomputable scoped instance (priority := 100) instSampleableTypeFinsetCoe
    {α : Type} (U : Finset α) [Nonempty ↥U] : SampleableType ↥U := by
  let x : ↥U := Classical.choice (inferInstance : Nonempty ↥U)
  exact SampleableType.finsetCoe U ⟨x, x.property⟩

end ProbabilityTheory

/-! ## Executable canonical sampler structure

These exact program identities preserve the selected element sampler and do not open or change
any scoped enumeration fallback or instance. -/

open OracleComp
namespace SampleableType

variable {E : Type} [SampleableType E]

/-- The selected vector sampler is the standard ordered traversal of element samples. -/
theorem uniformSample_vector_eq_ofFnM (n : Nat) :
    ($ᵗ (Vector E n)) = Vector.ofFnM (fun _ : _root_.Fin n => ($ᵗ E)) := by
  change SampleableType.vector E n = _
  induction n with
  | zero => simp only [SampleableType.vector, Vector.ofFnM_zero]
  | succ n ih =>
    rw [SampleableType.vector, Vector.ofFnM_succ]
    simp [ih, seq_eq_bind_map, map_eq_bind_pure_comp, bind_assoc]

/-- The selected Fin-function sampler reuses its sampled coordinate vector. -/
theorem uniformSample_pi_fin_eq_ofFnM (n : Nat) :
    ($ᵗ (_root_.Fin n → E)) = (arrayVectorEquivFin E n <$>
      (Vector.ofFnM fun _ : _root_.Fin n => ($ᵗ E))) := by
  change (arrayVectorEquivFin E n <$> ($ᵗ (Vector E n))) = _
  rw [uniformSample_vector_eq_ofFnM]

/-- The selected joint function sampler draws the first coordinate vector before the second. -/
theorem uniformSample_pi_fin_prod_eq_ofFnM (n K : Nat) :
    ($ᵗ ((_root_.Fin n → E) × (_root_.Fin K → E))) = (do
      let z ← Vector.ofFnM (fun _ : _root_.Fin n => ($ᵗ E))
      let lambda ← Vector.ofFnM (fun _ : _root_.Fin K => ($ᵗ E))
      return (arrayVectorEquivFin E n z, arrayVectorEquivFin E K lambda)) := by
  rw [SampleableType.uniformSample_prod_eq_bind, uniformSample_pi_fin_eq_ofFnM,
    uniformSample_pi_fin_eq_ofFnM]
  simp [map_eq_bind_pure_comp, bind_assoc]

end SampleableType
