/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Oracle.Security.Soundness
import VCVio.EvalDist.Defs.Measure.OptionT
import VCVio.EvalDist.Monad.Failure

/-!
This ordinary-import consumer checks the failure scope of the native soundness API.
A native prover performs an empty-response query. The existing interpreter handles that query
by OptionT failure, and the actual native executor has zero successful mass.
-/

open Interaction.Oracle OracleComp OracleSpec Interaction.TwoParty
open scoped ENNReal

namespace NativeFailure

abbrev ambient : OracleSpec (ℕ ⊕ Unit) := unifSpec + (Unit →ₒ Empty)

def handler : QueryImpl ambient (OptionT ProbComp) :=
  QueryImpl.add (fun q => OptionT.lift (QueryImpl.id' unifSpec q)) (fun _ => failure)

def protocol : Protocol := .public .sender Unit (fun _ => .done)

def prover : Prover.Strategy ambient protocol.tree protocol.roles (fun _ => Unit) := do
  let impossible ← liftM (ambient.query (.inr ()))
  nomatch impossible

def verifier : Verifier.Strategy ambient protocol.tree protocol.roles protocol.oracles 0
    (fun _ => Unit) := fun _ => pure (pure ())

def inputImpl : QueryImpl (ofPFunctor (0 : PFunctor)) Id := fun q => nomatch q

example : simulateQ handler prover =
    (failure : OptionT ProbComp ((_move : Unit) ×
      Prover.Strategy ambient TypeTree.done PUnit.unit (fun _ => Unit))) := by
  simp [prover, handler, simulateQ_bind, QueryImpl.add]
  rfl

set_option backward.isDefEq.respectTransparency false in
example : Pr{let _ ← (simulateQ handler (executeStrategies ambient protocol.tree protocol.roles
    protocol.oracles 0 inputImpl prover verifier))}[True] = 0 := by
  simp only [protocol, Protocol.public_tree, Protocol.public_roles,
    Protocol.public_oracles, Protocol.done_tree, Protocol.done_roles, Protocol.done_oracles]
  rw [executeStrategies_public_sender]
  simp [simulateQ_bind, prover, handler, QueryImpl.add]

end NativeFailure

#check Interaction.Oracle.Security.executeStrategies_soundness
#check Interaction.Oracle.Security.executeStrategies_soundness_uniform

#check Interaction.Oracle.Security.OrdinaryState.exists_verifier_escape
#check Interaction.Oracle.Security.LocalSoundness.random_prefix
