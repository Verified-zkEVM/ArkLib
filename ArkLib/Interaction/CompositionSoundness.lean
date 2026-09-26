/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Reduction
public import VCVio.EvalDist.ProbabilityBounds

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
  rw [run_appendFlat_splitPrefix]
  let first := run s₁ r₁ (Focal.splitPrefix prover) counterpart₁
  let rest : _ → m ((t : TypeTree.Path (s₁.append s₂)) × OutputP t × OutputC t) :=
    fun result :
      (t : TypeTree.Path s₁) ×
        StrategyOver (SyntaxOver.TwoParty.pairedTypeTree m) Participant.focal
          (s₂ t) (r₂ t) (fun p => OutputP (PFunctor.FreeM.Path.append s₁ s₂ t p)) × MidC t => do
    let ⟨p, outP, outC⟩ ← run (s₂ result.1) (r₂ result.1) result.2.1
      (counterpart₂ result.1 result.2.2)
    pure ⟨PFunctor.FreeM.Path.append s₁ s₂ result.1 p, outP, outC⟩
  have h := prEvent_bind_le_prEvent_add first rest
    (fun result => Good result.1 result.2.2)
    (fun result => Success result.1 result.2.2) (ε := ε₂) (fun result hfalse => by
      simpa only [rest, bind_assoc, pure_bind] using
        hsuffix result.1 result.2.2 hfalse result.2.1)
  exact h.trans (add_le_add (hprefix (Focal.splitPrefix prover)) le_rfl)

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
