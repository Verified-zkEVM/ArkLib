/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Reduction

/-!
# Plain execution

Execution uses PolyFun's focal-first runner, then calls the verifier decision. The observation
retains the transcript and prover output on rejection. Ambient failure remains a failure of the
oracle computation, distinct from a returned rejecting verdict.
-/

@[expose] public section

universe u uA

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
