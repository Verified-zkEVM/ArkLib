/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ArkLib.ToVCVio.EvalDist.Instances.OptionT
import ArkLib.ToVCVio.OracleComp.Coercions.SubSpec
import ArkLib.ToVCVio.ToMathlib.Control.StateT
import VCVio.EvalDist.Defs.NeverFails
import VCVio.OracleComp.SimSemantics.StateT

/-!
# Additions to VCV-io's `OracleComp.SimSemantics.SimulateQ`
-/

open OracleSpec OracleComp

lemma support_simulateQ_run'_subset
    {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp)) (oa : OracleComp spec α) (s : σ) :
    support ((simulateQ impl oa).run' s) ⊆ support oa := by
  intro y hy
  induction oa using OracleComp.inductionOn generalizing y s with
  | pure x =>
      simpa [simulateQ_pure, StateT.run'_eq, StateT.run_pure] using hy
  | query_bind t oa ih =>
      simp only [simulateQ_bind, simulateQ_query, OracleQuery.input_query,
        OracleQuery.cont_query, StateT.run'_eq, StateT.run_bind, support_map,
        Set.mem_image, support_bind, Set.mem_iUnion] at hy ⊢
      aesop

/-- If all outputs of the original `OracleComp` are successful and satisfy `P`, then the
    simulated `OptionT` computation satisfies `P` with probability one. -/
lemma OptionT.probEvent_eq_one_of_simulateQ_support
    {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec (Option α)) (s₀ : σ) (P : α → Prop)
    (h : ∀ x ∈ support oa, ∃ a, x = some a ∧ P a) :
    Pr[P | OptionT.mk ((simulateQ impl oa).run' s₀)] = 1 := by
  letI := Classical.decPred P
  rw [probEvent_eq_one_iff]
  constructor
  · rw [OptionT.probFailure_eq, OptionT.run_mk]
    have hfail : Pr[⊥ | (simulateQ impl oa).run' s₀] = 0 :=
      HasEvalPMF.probFailure_eq_zero _
    rw [hfail, _root_.zero_add]
    exact probOutput_eq_zero_of_not_mem_support fun hnone =>
      let hnone' := support_simulateQ_run'_subset impl oa s₀ hnone
      let ⟨_, hsome, _⟩ := h none hnone'
      by cases hsome
  · intro x hx
    rw [OptionT.mem_support_iff] at hx
    obtain ⟨a, ha, hP⟩ := h (some x) (support_simulateQ_run'_subset impl oa s₀ hx)
    cases ha
    exact hP

/-- Properties of `Option`-valued outputs of an underlying `OracleComp`
    propagate to elements in the support of the simulated, run, and `OptionT`-wrapped
    version. -/
lemma OptionT.aux_mem_support_simulateQ_run'
    {ι σ α : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec (Option α)) (s₀ : σ) (P : α → Prop)
    (h : ∀ x ∈ support oa, ∀ a, x = some a → P a)
    {x : α} (hx : x ∈ support (OptionT.mk ((simulateQ impl oa).run' s₀))) : P x := by
  rw [OptionT.mem_support_iff] at hx
  exact h (some x) (support_simulateQ_run'_subset impl oa s₀ hx) x rfl

lemma simulateQ_bind_map_eq_of_body
    {ι σ α β γ : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec α) (body₁ : α → OracleComp spec β)
    (body₂ : α → OracleComp spec γ) (f : γ → β)
    (hBody : ∀ a, simulateQ impl (body₁ a) = f <$> simulateQ impl (body₂ a)) :
    simulateQ impl (oa >>= body₁) = f <$> simulateQ impl (oa >>= body₂) := by
  rw [← simulateQ_map]
  simp only [map_eq_bind_pure_comp, simulateQ_bind, simulateQ_pure, bind_assoc,
    Function.comp]
  congr 1
  funext a
  exact hBody a

lemma StateT.run'_simulateQ_bind_map_eq_of_body
    {ι σ α β γ : Type} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (oa : OracleComp spec α) (body₁ : α → OracleComp spec β)
    (body₂ : α → OracleComp spec γ) (f : γ → β) (s : σ)
    (hBody : ∀ a, simulateQ impl (body₁ a) = f <$> simulateQ impl (body₂ a)) :
    (simulateQ impl (oa >>= body₁)).run' s =
      f <$> (simulateQ impl (oa >>= body₂)).run' s := by
  rw [← StateT.run'_map_comm f]
  exact congrArg (fun mx : StateT σ ProbComp β => mx.run' s)
    (simulateQ_bind_map_eq_of_body impl oa body₁ body₂ f hBody)

lemma StateT.run'_map_simulateQ_bind_eq_of_body
    {ι₀ ι σ α β γ δ : Type} {spec₀ : OracleSpec ι₀} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (impl₀ : QueryImpl spec₀ (StateT σ ProbComp))
    (oa : OracleComp spec α) (oa₀ : OracleComp spec₀ α)
    (body₁ : α → OracleComp spec β) (body₂ : α → OracleComp spec γ)
    (f : β → δ) (post : α → γ → δ) (s : σ)
    (hSample : simulateQ impl oa = simulateQ impl₀ oa₀)
    (hBody : ∀ a, f <$> simulateQ impl (body₁ a) =
      post a <$> simulateQ impl (body₂ a)) :
    (f <$> (simulateQ impl (oa >>= body₁)).run' s)
    =
    ((do
      let a ← simulateQ impl₀ oa₀
      let r ← simulateQ impl (body₂ a)
      pure (post a r)).run' s) := by
  rw [← StateT.run'_map_comm f]
  rw [← simulateQ_map]
  simp only [map_eq_bind_pure_comp, simulateQ_bind, simulateQ_pure, bind_assoc,
    Function.comp]
  rw [hSample]
  apply congrArg (fun mx : StateT σ ProbComp δ => mx.run' s)
  congr 1
  funext a
  exact hBody a

lemma OptionT.map_mk_run'_simulateQ_bind_eq_of_body
    {ι₀ ι σ α β γ δ : Type} {spec₀ : OracleSpec ι₀} {spec : OracleSpec ι}
    (impl : QueryImpl spec (StateT σ ProbComp))
    (impl₀ : QueryImpl spec₀ (StateT σ ProbComp))
    (oa : OracleComp spec α) (oa₀ : OracleComp spec₀ α)
    (body₁ : α → OracleComp spec (Option β))
    (body₂ : α → OracleComp spec (Option γ))
    (f : β → δ) (post : α → γ → δ) (s : σ)
    (hSample : simulateQ impl oa = simulateQ impl₀ oa₀)
    (hBody : ∀ a, Option.map f <$> simulateQ impl (body₁ a) =
      Option.map (post a) <$> simulateQ impl (body₂ a)) :
    f <$> OptionT.mk ((simulateQ impl (oa >>= body₁)).run' s)
    =
    OptionT.mk ((do
      let a ← simulateQ impl₀ oa₀
      let r ← simulateQ impl (body₂ a)
      pure (Option.map (post a) r)).run' s) := by
  apply OptionT.ext
  rw [OptionT.run_map]
  exact
    (StateT.run'_map_simulateQ_bind_eq_of_body
      (impl := impl) (impl₀ := impl₀) (oa := oa) (oa₀ := oa₀)
      (body₁ := body₁) (body₂ := body₂) (f := Option.map f)
      (post := fun a => Option.map (post a)) (s := s) hSample hBody)
