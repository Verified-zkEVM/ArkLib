/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Reduction
public import VCVio.EvalDist.ProbabilityBounds
public import VCVio.EvalDist.Monad.Measure

/-!
# Soundness of native sequential interaction

An arbitrary strategy on an appended interaction decomposes into its native prefix and the
actual suffix strategy returned by that prefix. Both execute with PolyFun's ordinary paired
runner. The exact equation requires only a lawful monad: choosing the already returned suffix is
pure, while its internal effects and its responses to challenges remain unrestricted.

The probability bounds apply to monads with lawful distribution semantics. They compose a
prefix truth-transition bound with soundness of the actual suffix counterpart. An admissibility
variant also charges for prefix outputs outside the suffix theorem's domain. These are ordinary
native interaction theorems, not soundness theorems for stateful oracle-world interpretations.
-/

@[expose] public section

universe u

namespace Interaction.TwoParty

open StrategyOver.TwoParty

section execution

variable {m : Type u → Type u} [Monad m] [LawfulMonad m]
  {s₁ : TypeTree} {s₂ : TypeTree.Path s₁ → TypeTree}
  {r₁ : RoleDecoration s₁} {r₂ : (t : TypeTree.Path s₁) → RoleDecoration (s₂ t)}
  {MidC : TypeTree.Path s₁ → Type u}
  {OutputP OutputC : TypeTree.Path (s₁.append s₂) → Type u}

/-- Split an arbitrary native adversary at the append boundary without changing execution order.
The prefix returns the adversary's actual suffix strategy, including all its private memory and
effectful continuations. No commutativity of the ambient effects is assumed. -/
theorem run_appendFlat_splitPrefix
    (prover : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.focal
      (s₁.append s₂) (r₁.append r₂) OutputP)
    (counterpart₁ : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.counterpart
      s₁ r₁ MidC)
    (counterpart₂ : (t : TypeTree.Path s₁) → MidC t →
      StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.counterpart
        (s₂ t) (r₂ t) (fun p => OutputC (PFunctor.FreeM.Path.append s₁ s₂ t p))) :
    run (s₁.append s₂) (r₁.append r₂) prover
      (Counterpart.appendFlat counterpart₁ counterpart₂) = (do
      let ⟨t, next, out⟩ ← run s₁ r₁ (Focal.splitPrefix prover) counterpart₁
      let ⟨p, outP, outC⟩ ← run (s₂ t) (r₂ t) next (counterpart₂ t out)
      pure ⟨PFunctor.FreeM.Path.append s₁ s₂ t p, outP, outC⟩) := by
  have h := run_compFlat_appendFlat_pure (Focal.splitPrefix prover)
    (fun _ next => next) counterpart₁ counterpart₂
  simpa only [Focal.compFlat_splitPrefix, pure_bind] using h

end execution

section probability

open scoped ENNReal

variable {m : Type → Type} [Monad m] [LawfulMonad m]
  [EvalDistSemantics m] [LawfulEvalDistSemantics m]
  {s₁ : TypeTree} {s₂ : TypeTree.Path s₁ → TypeTree}
  {r₁ : RoleDecoration s₁} {r₂ : (t : TypeTree.Path s₁) → RoleDecoration (s₂ t)}
  {MidC : TypeTree.Path s₁ → Type}
  {OutputP OutputC : TypeTree.Path (s₁.append s₂) → Type}

/-- The actual append boundary: prefix path, returned prover continuation, and counterpart
output. The continuation carries private memory and effects; this is just the runner's output
carrier, with no new execution or probability semantics. -/
abbrev AppendBoundary :=
  (t : TypeTree.Path s₁) ×
    StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.focal
      (s₂ t) (r₂ t) (fun p => OutputP (PFunctor.FreeM.Path.append s₁ s₂ t p)) × MidC t

open MeasureTheory

variable
    (prover : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.focal
      (s₁.append s₂) (r₁.append r₂) OutputP)
    (counterpart₁ : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.counterpart
      s₁ r₁ MidC)
    (counterpart₂ : (t : TypeTree.Path s₁) → MidC t →
      StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.counterpart
        (s₂ t) (r₂ t) (fun p => OutputC (PFunctor.FreeM.Path.append s₁ s₂ t p)))
    (Exceptional : AppendBoundary (m := m) (s₂ := s₂) (r₂ := r₂)
      (OutputP := OutputP) (MidC := MidC) → Prop)
    (Success : (t : TypeTree.Path (s₁.append s₂)) → OutputC t → Prop)

/-- For one whole prover, average the branch-dependent suffix errors over its actual prefix
outputs outside `Exceptional`, and charge the probability of `Exceptional`. The suffix premise
only holds almost everywhere, so it may fail even at a structurally supported boundary of zero
mass. The discrete measurable space makes all boundary observations measurable. Neither the
prefix nor the suffix must be lossless; no commutativity of effects is required. -/
theorem run_appendFlat_soundness_weighted_ae
    (error : AppendBoundary (m := m) (s₂ := s₂) (r₂ := r₂)
      (OutputP := OutputP) (MidC := MidC) → ENNReal)
    (hsuffix : letI : MeasurableSpace (AppendBoundary (m := m) (s₂ := s₂) (r₂ := r₂)
        (OutputP := OutputP) (MidC := MidC)) := ⊤
      ∀ᵐ b ∂𝒟[run s₁ r₁ (Focal.splitPrefix prover) counterpart₁], ¬ Exceptional b →
        Pr{let result ← run (s₂ b.1) (r₂ b.1) b.2.1 (counterpart₂ b.1 b.2.2)}[Success
          (PFunctor.FreeM.Path.append s₁ s₂ b.1 result.1) result.2.2] ≤ error b) :
    let : MeasurableSpace (AppendBoundary (m := m) (s₂ := s₂) (r₂ := r₂)
      (OutputP := OutputP) (MidC := MidC)) := ⊤
    Pr{let result ← (run (s₁.append s₂) (r₁.append r₂) prover
      (Counterpart.appendFlat counterpart₁ counterpart₂))}[Success result.1 result.2.2] ≤
      Pr{let b ← run s₁ r₁ (Focal.splitPrefix prover) counterpart₁}[Exceptional b] +
        ∫⁻ b in {b | ¬ Exceptional b}, error b
          ∂𝒟[run s₁ r₁ (Focal.splitPrefix prover) counterpart₁] := by
  classical
  let : MeasurableSpace (AppendBoundary (m := m) (s₂ := s₂) (r₂ := r₂)
    (OutputP := OutputP) (MidC := MidC)) := ⊤
  rw [run_appendFlat_splitPrefix, prEvent_bind_eq_lintegral_of_discrete,
    prEvent_eq_evalDist_of_discrete]
  have hpoint := hsuffix.mono (fun b hb => show
      Pr{let result ← (do
        let ⟨p, outP, outC⟩ ← run (s₂ b.1) (r₂ b.1) b.2.1 (counterpart₂ b.1 b.2.2)
        pure ⟨PFunctor.FreeM.Path.append s₁ s₂ b.1 p, outP, outC⟩ :
          m ((t : TypeTree.Path (s₁.append s₂)) × OutputP t × OutputC t))}[
        Success result.1 result.2.2] ≤
      {b | Exceptional b}.indicator (fun _ => (1 : ENNReal)) b +
        {b | ¬ Exceptional b}.indicator error b from by
    by_cases he : Exceptional b
    · simp only [Set.indicator_of_mem (show b ∈ {b | Exceptional b} from he),
        Set.indicator_of_notMem (show b ∉ {b | ¬ Exceptional b} from not_not.mpr he), add_zero]
      exact prEvent_le_one _ _
    · simp only [Set.indicator_of_notMem (show b ∉ {b | Exceptional b} from he),
        Set.indicator_of_mem (show b ∈ {b | ¬ Exceptional b} from he), zero_add]
      simpa only [bind_assoc, pure_bind] using hb he)
  refine (lintegral_mono_ae hpoint).trans_eq ?_
  rw [lintegral_add_left Measurable.of_discrete,
    lintegral_indicator MeasurableSet.of_discrete,
    lintegral_indicator MeasurableSet.of_discrete]
  simp only [setLIntegral_const, one_mul]

/-- The weighted bound only needs suffix security at structurally reachable outputs of this
whole prover's prefix. Reachability includes the actual returned continuation. Unlike the
almost-everywhere form, this premise also covers supported outputs with zero mass. -/
theorem run_appendFlat_soundness_weighted_of_support
    [MonadAttach m] [WeaklyLawfulMonadAttach m]
    (error : AppendBoundary (m := m) (s₂ := s₂) (r₂ := r₂)
      (OutputP := OutputP) (MidC := MidC) → ENNReal)
    (hsuffix : ∀ b ∈ support (run s₁ r₁ (Focal.splitPrefix prover) counterpart₁),
      ¬ Exceptional b →
        Pr{let result ← run (s₂ b.1) (r₂ b.1) b.2.1 (counterpart₂ b.1 b.2.2)}[Success
          (PFunctor.FreeM.Path.append s₁ s₂ b.1 result.1) result.2.2] ≤ error b) :
    let : MeasurableSpace (AppendBoundary (m := m) (s₂ := s₂) (r₂ := r₂)
      (OutputP := OutputP) (MidC := MidC)) := ⊤
    Pr{let result ← (run (s₁.append s₂) (r₁.append r₂) prover
      (Counterpart.appendFlat counterpart₁ counterpart₂))}[Success result.1 result.2.2] ≤
      Pr{let b ← run s₁ r₁ (Focal.splitPrefix prover) counterpart₁}[Exceptional b] +
        ∫⁻ b in {b | ¬ Exceptional b}, error b
          ∂𝒟[run s₁ r₁ (Focal.splitPrefix prover) counterpart₁] := by
  let : MeasurableSpace (AppendBoundary (m := m) (s₂ := s₂) (r₂ := r₂)
    (OutputP := OutputP) (MidC := MidC)) := ⊤
  apply run_appendFlat_soundness_weighted_ae prover counterpart₁ counterpart₂ Exceptional Success
  exact evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete hsuffix

/-- A fixed whole prover needs a prefix error bound only for its own prefix and a uniform
suffix bound only almost everywhere under that prefix's actual output distribution. -/
theorem run_appendFlat_soundness_ae
    (ε₁ ε₂ : ENNReal)
    (hprefix : Pr{let b ← run s₁ r₁ (Focal.splitPrefix prover) counterpart₁}[Exceptional b] ≤ ε₁)
    (hsuffix : letI : MeasurableSpace (AppendBoundary (m := m) (s₂ := s₂) (r₂ := r₂)
        (OutputP := OutputP) (MidC := MidC)) := ⊤
      ∀ᵐ b ∂𝒟[run s₁ r₁ (Focal.splitPrefix prover) counterpart₁], ¬ Exceptional b →
        Pr{let result ← run (s₂ b.1) (r₂ b.1) b.2.1 (counterpart₂ b.1 b.2.2)}[Success
          (PFunctor.FreeM.Path.append s₁ s₂ b.1 result.1) result.2.2] ≤ ε₂) :
    Pr{let result ← (run (s₁.append s₂) (r₁.append r₂) prover
      (Counterpart.appendFlat counterpart₁ counterpart₂))}[Success result.1 result.2.2] ≤
      ε₁ + ε₂ := by
  let : MeasurableSpace (AppendBoundary (m := m) (s₂ := s₂) (r₂ := r₂)
    (OutputP := OutputP) (MidC := MidC)) := ⊤
  refine (run_appendFlat_soundness_weighted_ae prover counterpart₁ counterpart₂ Exceptional
    Success (fun _ => ε₂) hsuffix).trans (add_le_add hprefix ?_)
  rw [setLIntegral_const]
  exact mul_le_of_le_one_right' ((measure_mono (Set.subset_univ _)).trans
    (evalDist_apply_univ_le_one _))

/-- A fixed whole prover needs uniform suffix security only on reachable boundary results. -/
theorem run_appendFlat_soundness_of_support
    [MonadAttach m] [WeaklyLawfulMonadAttach m]
    (ε₁ ε₂ : ENNReal)
    (hprefix : Pr{let b ← run s₁ r₁ (Focal.splitPrefix prover) counterpart₁}[Exceptional b] ≤ ε₁)
    (hsuffix : ∀ b ∈ support (run s₁ r₁ (Focal.splitPrefix prover) counterpart₁),
      ¬ Exceptional b →
        Pr{let result ← run (s₂ b.1) (r₂ b.1) b.2.1 (counterpart₂ b.1 b.2.2)}[Success
          (PFunctor.FreeM.Path.append s₁ s₂ b.1 result.1) result.2.2] ≤ ε₂) :
    Pr{let result ← (run (s₁.append s₂) (r₁.append r₂) prover
      (Counterpart.appendFlat counterpart₁ counterpart₂))}[Success result.1 result.2.2] ≤
      ε₁ + ε₂ := by
  let : MeasurableSpace (AppendBoundary (m := m) (s₂ := s₂) (r₂ := r₂)
    (OutputP := OutputP) (MidC := MidC)) := ⊤
  apply run_appendFlat_soundness_ae prover counterpart₁ counterpart₂ Exceptional Success
    ε₁ ε₂ hprefix
  exact evalDist.ae_of_forall_mem_support _ _ MeasurableSet.of_discrete hsuffix

/-- For one whole prover, require a bound only for its actual prefix. The suffix bound still
covers all boundary triples; the support and almost-everywhere variants restrict that premise. -/
theorem run_appendFlat_soundness_fixed
    (ε₁ ε₂ : ENNReal)
    (hprefix : Pr{let b ← run s₁ r₁ (Focal.splitPrefix prover) counterpart₁}[Exceptional b] ≤ ε₁)
    (hsuffix : ∀ b, ¬ Exceptional b →
        Pr{let result ← run (s₂ b.1) (r₂ b.1) b.2.1 (counterpart₂ b.1 b.2.2)}[Success
          (PFunctor.FreeM.Path.append s₁ s₂ b.1 result.1) result.2.2] ≤ ε₂) :
    Pr{let result ← (run (s₁.append s₂) (r₁.append r₂) prover
      (Counterpart.appendFlat counterpart₁ counterpart₂))}[Success result.1 result.2.2] ≤
      ε₁ + ε₂ := by
  apply run_appendFlat_soundness_ae prover counterpart₁ counterpart₂ Exceptional Success
    ε₁ ε₂ hprefix
  exact Filter.Eventually.of_forall hsuffix

/-- Prefix truth transitions and suffix soundness bound success of the actual composed
counterpart against every whole native adversary. Prefix outputs retain arbitrary suffix
strategies; suffix soundness therefore covers every private continuation the prefix can return.
The suffix hypothesis applies to all false prefix paths and outputs, not only reachable ones. -/
theorem run_appendFlat_soundness
    (prover : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.focal
      (s₁.append s₂) (r₁.append r₂) OutputP)
    (counterpart₁ : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.counterpart
      s₁ r₁ MidC)
    (counterpart₂ : (t : TypeTree.Path s₁) → MidC t →
      StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.counterpart
        (s₂ t) (r₂ t) (fun p => OutputC (PFunctor.FreeM.Path.append s₁ s₂ t p)))
    (Good : (t : TypeTree.Path s₁) → MidC t → Prop)
    (Success : (t : TypeTree.Path (s₁.append s₂)) → OutputC t → Prop)
    (ε₁ ε₂ : ENNReal)
    (hprefix : ∀ strategy : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m)
        Participant.focal s₁ r₁ (fun t =>
          StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.focal
            (s₂ t) (r₂ t) (fun p => OutputP (PFunctor.FreeM.Path.append s₁ s₂ t p))),
      Pr{let result ← run s₁ r₁ strategy counterpart₁}[Good result.1 result.2.2] ≤ ε₁)
    (hsuffix : ∀ (t : TypeTree.Path s₁) (out : MidC t), ¬ Good t out →
      ∀ strategy : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.focal
          (s₂ t) (r₂ t) (fun p => OutputP (PFunctor.FreeM.Path.append s₁ s₂ t p)),
        Pr{let result ← run (s₂ t) (r₂ t) strategy (counterpart₂ t out)}[
          Success (PFunctor.FreeM.Path.append s₁ s₂ t result.1) result.2.2] ≤ ε₂) :
    Pr{let result ← (run (s₁.append s₂) (r₁.append r₂) prover
      (Counterpart.appendFlat counterpart₁ counterpart₂))}[Success result.1 result.2.2] ≤
      ε₁ + ε₂ := by
  apply run_appendFlat_soundness_fixed prover counterpart₁ counterpart₂
    (fun b => Good b.1 b.2.2) Success ε₁ ε₂
    (hprefix (Focal.splitPrefix prover))
  intro b hfalse
  exact hsuffix b.1 b.2.2 hfalse b.2.1

/-- If suffix soundness applies only to admissible false prefix outputs, additionally charge
the probability of leaving that domain. The suffix hypothesis applies to all admissible false
prefix paths and outputs, not only reachable ones. All bounds concern actual native executions. -/
theorem run_appendFlat_soundness_of_admissible
    (prover : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.focal
      (s₁.append s₂) (r₁.append r₂) OutputP)
    (counterpart₁ : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.counterpart
      s₁ r₁ MidC)
    (counterpart₂ : (t : TypeTree.Path s₁) → MidC t →
      StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.counterpart
        (s₂ t) (r₂ t) (fun p => OutputC (PFunctor.FreeM.Path.append s₁ s₂ t p)))
    (Good Admissible : (t : TypeTree.Path s₁) → MidC t → Prop)
    (Success : (t : TypeTree.Path (s₁.append s₂)) → OutputC t → Prop)
    (ε₁ δ ε₂ : ENNReal)
    (hprefix : ∀ strategy : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m)
        Participant.focal s₁ r₁ (fun t =>
          StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.focal
            (s₂ t) (r₂ t) (fun p => OutputP (PFunctor.FreeM.Path.append s₁ s₂ t p))),
      Pr{let result ← run s₁ r₁ strategy counterpart₁}[Good result.1 result.2.2] ≤ ε₁)
    (hadmissible : ∀ strategy : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m)
        Participant.focal s₁ r₁ (fun t =>
          StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.focal
            (s₂ t) (r₂ t) (fun p => OutputP (PFunctor.FreeM.Path.append s₁ s₂ t p))),
      Pr{let result ← run s₁ r₁ strategy counterpart₁}[¬ Admissible result.1 result.2.2] ≤ δ)
    (hsuffix : ∀ (t : TypeTree.Path s₁) (out : MidC t), ¬ Good t out → Admissible t out →
      ∀ strategy : StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.focal
          (s₂ t) (r₂ t) (fun p => OutputP (PFunctor.FreeM.Path.append s₁ s₂ t p)),
        Pr{let result ← run (s₂ t) (r₂ t) strategy (counterpart₂ t out)}[
          Success (PFunctor.FreeM.Path.append s₁ s₂ t result.1) result.2.2] ≤ ε₂) :
    Pr{let result ← (run (s₁.append s₂) (r₁.append r₂) prover
      (Counterpart.appendFlat counterpart₁ counterpart₂))}[Success result.1 result.2.2] ≤
      ε₁ + δ + ε₂ := by
  classical
  apply run_appendFlat_soundness prover counterpart₁ counterpart₂
    (fun t out => Good t out ∨ ¬ Admissible t out) Success (ε₁ + δ) ε₂
  · intro strategy
    exact (prEvent_or_le (run s₁ r₁ strategy counterpart₁)
      (fun result => Good result.1 result.2.2)
      (fun result => ¬ Admissible result.1 result.2.2)).trans
      (add_le_add (hprefix strategy) (hadmissible strategy))
  · intro t out hfalse strategy
    exact hsuffix t out (fun hgood => hfalse (Or.inl hgood))
      (not_not.mp (fun hbad => hfalse (Or.inr hbad))) strategy

end probability

end Interaction.TwoParty
