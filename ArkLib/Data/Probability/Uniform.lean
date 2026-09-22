/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import VCVio.OracleComp.Constructions.SampleableType.NativeMeasure

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
