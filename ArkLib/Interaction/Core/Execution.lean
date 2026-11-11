/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Reduction
public import VCVio.EvalDist.ProbabilityNotation
public import ToMathlib.Control.StateT

/-!
# Plain execution

Execution uses PolyFun's focal-first runner, then calls the verifier decision. The observation
retains the transcript and prover output on rejection. Ambient failure remains a failure of the
oracle computation, distinct from a returned rejecting verdict.
-/

@[expose] public section

universe u uA v

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp

/-- A completed interaction, including a possibly rejecting verifier verdict. -/
abbrev Observation {P : PFunctor.{uA, u}} (l : PFunctor.Lens P rolePoly.{u})
    (s : FreeM P PUnit.{u + 1}) (Out : PathAlong l s → Type u) (StmtOut : Type u) :=
  (tr : PathAlong l s) × Out tr × Option StmtOut

/-- Run the interaction against an arbitrary focal strategy, and decide at its end. -/
def Verifier.run {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {s : Protocol.{u}} {S T : Type u} {Out : PathAlong plainSig s → Type u}
    (V : Verifier ambient s S T) (stmt : S) (p : Prover plainSig ambient s Out) :
    OracleComp (ambient + challengeSpec plainSig s) (Observation plainSig s Out T) := do
  let ⟨tr, out, _⟩ ← TwoParty.Lens.run s
    (p.simulate (fun q => liftM ((ambient + challengeSpec plainSig s).query (.inl q))))
    (sampler plainSig s (fun c =>
      liftM ((ambient + challengeSpec plainSig s).query (.inr c))))
  let verdict ← OracleComp.liftComp
    (V.decide stmt (projectPathAlong plainSig s tr) (toPlainView s tr)).run
    (ambient + challengeSpec plainSig s)
  pure ⟨tr, out, verdict⟩

/-- Every challenge action has the prescribed event marginals. By the lawful bind semantics,
these marginals hold after every history, independently of the earlier actions. Missing mass in
ambient actions is permitted; a challenge has exactly the mass of its specified draw. -/
def FreshChallenges {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {ι : Type} {ambient : OracleSpec ι} {P : PFunctor.{1, 0}}
    {l : PFunctor.Lens P rolePoly} {s : FreeM P PUnit}
    (handler : QueryImpl (ambient + challengeSpec l s) m)
    (draw : QueryImpl (challengeSpec l s) ProbComp) : Prop :=
  ∀ c (event : challengeSpec l s c → Prop),
    Pr{let x ← handler (.inr c)}[event x] = Pr{let x ← draw c}[event x]

/-- A stateful challenge has the prescribed event marginals from every current state.
The challenge may change the state; only its move distribution is fixed. -/
def FreshChallengesAt {m : Type → Type v} [Monad m] [EvalDistSemantics m]
    {ι σ : Type} {ambient : OracleSpec ι} {P : PFunctor.{1, 0}}
    {l : PFunctor.Lens P rolePoly} {s : FreeM P PUnit}
    (handler : QueryImpl (ambient + challengeSpec l s) (StateT σ m))
    (draw : QueryImpl (challengeSpec l s) ProbComp) : Prop :=
  ∀ st c (event : challengeSpec l s c → Prop),
    Pr{let x ← (handler (.inr c)).run' st}[event x] = Pr{let x ← draw c}[event x]

/-- Lifting a separate challenge draw into the ambient state gives fresh challenge marginals. -/
theorem freshChallengesAt_addLift {ι σ : Type} {ambient : OracleSpec ι}
    {P : PFunctor.{1, 0}} {l : PFunctor.Lens P rolePoly} {s : FreeM P PUnit}
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (draw : QueryImpl (challengeSpec l s) ProbComp) :
    FreshChallengesAt
      (impl.addLift draw : QueryImpl (ambient + challengeSpec l s) (StateT σ ProbComp)) draw := by
  intro st c event
  simp only [QueryImpl.addLift_def, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply,
    StateT.liftM_def, StateT.run'_lift']

/-- Every possible verdict of a run is a possible verdict of the decision on its transcript. -/
theorem Verifier.verdict_mem_support_run {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {s : Protocol.{u}} {S T : Type u} {Out : PathAlong plainSig s → Type u}
    (V : Verifier ambient s S T) (stmt : S) (p : Prover plainSig ambient s Out)
    {obs : Observation plainSig s Out T} (h : obs ∈ support (V.run stmt p)) :
    obs.2.2 ∈ support
      (V.decide stmt (projectPathAlong plainSig s obs.1) (toPlainView s obs.1)).run := by
  simp only [Verifier.run, mem_support_bind_iff, support_pure, Set.mem_singleton_iff] at h
  obtain ⟨⟨tr, out, _⟩, -, verdict, hv, rfl⟩ := h
  simpa only [mem_support_liftComp_iff] using hv

/-- Execute the honest prover and terminal decision, retaining explicit rejection. -/
def Reduction.observe {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {s : Protocol.{u}} {S W T : Type u} {Out : PathAlong plainSig s → Type u}
    (R : Reduction ambient s S W T Out) (stmt : S) (wit : W) :
    OracleComp (ambient + challengeSpec plainSig s) (Observation plainSig s Out T) :=
  R.verifier.run stmt (R.prover stmt wit)

/-- The accepting-result presentation of the same execution. -/
def Reduction.run {ι : Type u} {ambient : OracleSpec.{u, u} ι}
    {s : Protocol.{u}} {S W T : Type u} {Out : PathAlong plainSig s → Type u}
    (R : Reduction ambient s S W T Out) (stmt : S) (wit : W) :
    OptionT (OracleComp (ambient + challengeSpec plainSig s))
      ((tr : PathAlong plainSig s) × Out tr × T) :=
  OptionT.mk do
    let ⟨tr, out, verdict⟩ ← R.observe stmt wit
    pure (verdict.map fun t => ⟨tr, out, t⟩)

end Interaction.Core
