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

-- TODO: These lemmas (this and all following) are way too structured. Break them up into more generic, simpler lemmas.
lemma StateT.run'_simulateQ_liftComp_map_sample_bind
    {ι₀ ι σ α κ γ : Type} {spec₀ : OracleSpec ι₀} {spec : OracleSpec ι}
    [MonadLiftT (OracleQuery spec₀) (OracleQuery spec)]
    (impl : QueryImpl spec (StateT σ ProbComp))
    (sample : OracleComp spec₀ α) (mk : α → κ)
    (body : κ → OracleComp spec γ) (s : σ) :
    (simulateQ impl (do
      let k ← OracleComp.liftComp (do let a ← sample; pure (mk a)) spec
      body k)).run' s =
    (simulateQ impl (do
      let a ← OracleComp.liftComp sample spec
      body (mk a))).run' s := by
  simp only [liftComp_bind, liftComp_pure, bind_assoc, pure_bind]

lemma StateT.run'_simulateQ_liftComp_bind_project_of_body
    {ι₀ ι σ α β γ : Type} {spec₀ : OracleSpec ι₀} {spec : OracleSpec ι}
    [MonadLiftT (OracleQuery spec₀) (OracleQuery spec)]
    (impl : QueryImpl spec (StateT σ ProbComp))
    (sample : OracleComp spec₀ α)
    (bodyBase : α → OracleComp spec (Option β))
    (bodyExt : α → OracleComp spec (Option γ))
    (proj : γ → β) (s : σ)
    (hBody : ∀ a, simulateQ impl (bodyBase a) =
      Option.map proj <$> simulateQ impl (bodyExt a)) :
    (simulateQ impl (do
      let a ← OracleComp.liftComp sample spec
      bodyBase a)).run' s =
    Option.map proj <$> (simulateQ impl (do
      let a ← OracleComp.liftComp sample spec
      bodyExt a)).run' s := by
  rw [← StateT.run'_map_comm (Option.map proj)
    (simulateQ impl (do
      let a ← OracleComp.liftComp sample spec
      bodyExt a)) s]
  rw [← simulateQ_map]
  simp only [map_eq_bind_pure_comp, simulateQ_bind, simulateQ_pure, bind_assoc,
    Function.comp]
  apply congrArg (fun mx : StateT σ ProbComp (Option β) => mx.run' s)
  congr 1
  funext a
  exact hBody a

lemma StateT.run'_simulateQ_liftComp_bind_map_eq_of_body
    {ι₀ ι σ α β γ δ : Type} {spec₀ : OracleSpec ι₀} {spec : OracleSpec ι}
    [MonadLiftT (OracleQuery spec₀) (OracleQuery spec)]
    (impl : QueryImpl spec (StateT σ ProbComp))
    (impl₀ : QueryImpl spec₀ (StateT σ ProbComp))
    (sample : OracleComp spec₀ α)
    (body₁ : α → OracleComp spec (Option β))
    (body₂ : α → OracleComp spec (Option γ))
    (f : β → δ) (post : α → γ → δ) (s : σ)
    (hSample : simulateQ impl (OracleComp.liftComp sample spec) = simulateQ impl₀ sample)
    (hBody : ∀ a, Option.map f <$> simulateQ impl (body₁ a) =
      Option.map (post a) <$> simulateQ impl (body₂ a)) :
    (Option.map f <$> (simulateQ impl (do
      let a ← OracleComp.liftComp sample spec
      body₁ a)).run' s)
    =
    ((do
      let a ← simulateQ impl₀ sample
      let r ← simulateQ impl (body₂ a)
      pure (Option.map (post a) r)).run' s) := by
  rw [← StateT.run'_map_comm (Option.map f)
    (simulateQ impl (do
      let a ← OracleComp.liftComp sample spec
      body₁ a)) s]
  rw [← simulateQ_map]
  simp only [map_eq_bind_pure_comp, simulateQ_bind, simulateQ_pure, bind_assoc,
    Function.comp]
  rw [hSample]
  apply congrArg (fun mx : StateT σ ProbComp (Option δ) => mx.run' s)
  congr 1
  funext a
  exact hBody a

lemma OptionT.simulateQ_liftComp_bind_map_eq_of_body
    {ι₀ ι σ α β γ δ : Type} {spec₀ : OracleSpec ι₀} {spec : OracleSpec ι}
    [MonadLiftT (OracleQuery spec₀) (OracleQuery spec)]
    (impl : QueryImpl spec (StateT σ ProbComp))
    (impl₀ : QueryImpl spec₀ (StateT σ ProbComp))
    (sample : OracleComp spec₀ α)
    (body₁ : α → OracleComp spec (Option β))
    (body₂ : α → OracleComp spec (Option γ))
    (f : β → δ) (post : α → γ → δ) (s : σ)
    (hSample : simulateQ impl (OracleComp.liftComp sample spec) = simulateQ impl₀ sample)
    (hBody : ∀ a, Option.map f <$> simulateQ impl (body₁ a) =
      Option.map (post a) <$> simulateQ impl (body₂ a)) :
    f <$> OptionT.mk ((simulateQ impl (do
      let a ← OracleComp.liftComp sample spec
      body₁ a)).run' s)
    =
    OptionT.mk ((do
      let a ← simulateQ impl₀ sample
      let r ← simulateQ impl (body₂ a)
      pure (Option.map (post a) r)).run' s) := by
  apply OptionT.ext
  rw [OptionT.run_map]
  exact
    (StateT.run'_simulateQ_liftComp_bind_map_eq_of_body
      (impl := impl) (impl₀ := impl₀) (sample := sample) (body₁ := body₁)
      (body₂ := body₂) (f := f) (post := post) (s := s) hSample hBody)
