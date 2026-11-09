/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Security.Knowledge

/-!
# Logged execution of passive oracle verifiers

`OracleVerifier.runWithLog` records the prover's ambient queries and every query of the decision
before routing: ambient queries and queries to the input and message oracles, in order and with
repeats. Forgetting both logs gives `OracleVerifier.run` exactly.

Logging after substitution, VCVio's `OracleComp.withQueryLog_simulateQ`, records the target
queries each handler program makes, in order. A persistent `OracleRuntime` executes the logged run
directly as `runtime.run (V.runWithLog stmt data prover)`.
-/

@[expose] public section

namespace Interaction.Core
open PFunctor FreeM TwoParty.Lens OracleComp Oracle OracleSpec

namespace OracleVerifier
variable {ι I J S T : Type} {ambient : OracleSpec ι} {s : OracleProtocol}
  {A : I → Type} {B : J → Type} {inputs : OracleFamily I A} {outputs : OracleFamily J B}
  {Out : PathAlong oracleSig s → Type}

private theorem bind_run_withLogging {κ α β : Type} {spec : OracleSpec κ}
    {m : Type → Type} [Monad m] [LawfulMonad m] (impl : QueryImpl spec m)
    (program : OracleComp spec α) (next : α → m β) :
    simulateQ impl program >>= next =
      (simulateQ impl.withLogging program).run >>= fun z => next z.1 := by
  rw [← QueryImpl.fst_map_run_withLogging, bind_map_left]

/-- Forgetting both logs of the logged run gives the oracle verifier's run exactly. -/
theorem runWithLog_erase (V : OracleVerifier ambient s S T inputs outputs) (stmt : S)
    (data : ∀ i, A i) (prover : Prover oracleSig ambient s Out) :
    Sigma.fst <$> V.runWithLog stmt data prover = V.run stmt data prover := by
  simp only [runWithLog, run, _root_.map_bind]
  conv_rhs => rw [← simulateQ_id' (TwoParty.Lens.run s _ _),
    bind_run_withLogging (QueryImpl.id' (ambient + challengeSpec oracleSig s))]
  refine bind_congr fun x => ?_
  obtain ⟨⟨tr, out, _⟩, proveLog⟩ := x
  rw [bind_run_withLogging (QueryImpl.addLift _ _)]
  refine bind_congr fun y => ?_
  simp

end OracleVerifier
end Interaction.Core
