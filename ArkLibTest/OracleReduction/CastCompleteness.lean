/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Cast

/-! Completeness casts accept distinct implementations of the same uniform challenge sampler. -/

open OracleComp OracleSpec ProtocolSpec

namespace CastCompletenessTest

/-- A single verifier challenge with a unique possible answer. -/
abbrev spec : ProtocolSpec 1 := ⟨!v[.V_to_P], fun _ => Unit⟩

/-- The standard singleton sampler returns without querying randomness. -/
abbrev pureSampler : SampleableType Unit where
  selectElem := pure ()
  evalDist_selectElem_eq_uniform := by
    intro _ _
    apply MeasureTheory.Measure.ext_of_singleton
    intro x
    rw [evalDist_pure, Unique.eq_default x,
      ProbabilityTheory.uniformOn_univ_apply_singleton]
    simp

/-- This singleton sampler performs a random query before returning its unique answer. -/
abbrev querySampler : SampleableType Unit where
  selectElem := (fun _ => ()) <$> ProbComp.uniformFin 0
  evalDist_selectElem_eq_uniform := by
    intro _ _
    rw [(EvalDistEq.map_const (ProbComp.uniformFin 0) ()).evalDist_eq]
    exact pureSampler.evalDist_selectElem_eq_uniform

/-- The challenge samplers really are different programs, despite having the same distribution. -/
theorem sampler_programs_differ : pureSampler.selectElem ≠ querySampler.selectElem := by
  change (pure () : ProbComp Unit) ≠ (fun _ => ()) <$> ProbComp.uniformFin 0
  intro h
  have hp := congrArg OracleComp.isPure h
  simp only [ProbComp.uniformFin_def, map_eq_bind_pure_comp, Function.comp_def,
    OracleComp.isPure_pure, OracleComp.isPure_query_bind, Bool.true_eq_false] at hp

/-- Completeness transfer needs no equality between the source and target sampler programs. -/
example {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (R : Reduction oSpec Unit Unit Unit Unit spec) (ε : NNReal)
    (h : @Reduction.completeness _ _ _ _ _ _ _ _ (fun _ => pureSampler)
      _ init impl Set.univ Set.univ R ε) :
    @Reduction.completeness _ _ _ _ _ _ _ _ (fun _ => querySampler)
      _ init impl Set.univ Set.univ (R.cast rfl rfl) ε := by
  exact Reduction.cast_completeness (pSpec₁ := spec) (pSpec₂ := spec)
    (inst₁ := fun _ => pureSampler) (inst₂ := fun _ => querySampler) rfl rfl R ε h

/-- Perfect completeness has the same sampler-independent public API. -/
example {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (R : Reduction oSpec Unit Unit Unit Unit spec)
    (h : @Reduction.perfectCompleteness _ _ _ _ _ _ _ _ (fun _ => pureSampler)
      _ init impl Set.univ Set.univ R) :
    @Reduction.perfectCompleteness _ _ _ _ _ _ _ _ (fun _ => querySampler)
      _ init impl Set.univ Set.univ (R.cast rfl rfl) := by
  exact Reduction.cast_perfectCompleteness (pSpec₁ := spec) (pSpec₂ := spec)
    (inst₁ := fun _ => pureSampler) (inst₂ := fun _ => querySampler) rfl rfl R h

end CastCompletenessTest
