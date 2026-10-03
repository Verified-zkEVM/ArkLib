/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ProofSystem.Sumcheck.Interaction.RoundByRound

/-!
An ordinary-import invocation of the local-to-global theorem on full native Sumcheck.
The prover is an arbitrary whole native strategy; the final event observes its actual output.
-/

open Interaction.Oracle Interaction.TwoParty OracleComp OracleSpec
open Sumcheck.Interaction Sumcheck.Interaction.Native
open scoped ENNReal

namespace NativeSumcheckConsumer

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F] (n deg : ℕ)

example {m : ℕ} (D : Fin m ↪ F) (A : PFunctor)
    (originalOracle : VirtualOracle (ofPFunctor A) (MultivariateRound.polynomialFamily F n deg))
    (stmt : Sumcheck.Spec.StatementRound F n ⟨0, by omega⟩)
    (impl : QueryImpl (ofPFunctor A) Id)
    (prover : Prover.Strategy unifSpec (protocol F deg n).tree
      (protocol F deg n).roles (fun _ => Unit))
    (p : Sumcheck.Spec.OracleStatement F n deg ())
    (horiginal : originalOracle.eval impl =
      (MultivariateRound.polynomialFamily F n deg).behaviorOfRealizations (fun _ => p))
    (hfalse : ¬ MultivariateRound.closedRelation F n deg D ⟨0, by omega⟩
      ⟨stmt, originalOracle.eval impl⟩) :
    Pr{let result ← (execute F n deg unifSpec ($ᵗ F) (Finset.univ.map D).toList
      n 0 (by omega) A originalOracle stmt impl prover)}[
        result.map (outputRelation F n deg) = some True] ≤
      (n : ENNReal) * deg / Fintype.card F := by
  have bound := roundByRound_soundness F n deg D unifSpec (QueryImpl.id' unifSpec) ($ᵗ F)
    (fun _ => by rw [simulateQ_id']) n 0 (by omega) A originalOracle stmt impl prover p
    horiginal hfalse
  simpa only [simulateQ_id'] using bound

end NativeSumcheckConsumer
