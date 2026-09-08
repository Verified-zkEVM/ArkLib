/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Richard Goodman
-/

import ArkLib.OracleReduction.Composition.Sequential.Append.Execution

/-!
# Raw execution can fail to factor at a challenge-opening seam

Adapted from Richard Goodman's historical counterexample in PR #643, commit
`1790361fef014f4d47821d86c6cbe20bd5ceae3d`. An empty left prover
queries the ambient oracle in its output; the right protocol starts with a challenge. The
appended machine samples that challenge before the output query, whereas sequential execution
performs the output query first. A head-query observer distinguishes the free programs.

This is a counterexample to unconditional raw execution factorization. It does not assert that
all challenge-opening protocols fail to factor after a particular oracle simulation.
-/

namespace ArkLib.AppendRunNecessity

open ProtocolSpec OracleSpec OracleComp

-- Minimal instance: empty left protocol, one V-round right protocol,
-- one Bool-oracle ambient spec, an output that queries it.
/-- The ambient Boolean oracle. -/
def oS : OracleSpec Unit := Unit →ₒ Bool
/-- The empty left protocol. -/
def pS1 : ProtocolSpec 0 := ⟨![], ![]⟩
/-- The challenge-opening right protocol. -/
def pS2 : ProtocolSpec 1 := ⟨![.V_to_P], ![Bool]⟩

/-- The left prover queries the ambient oracle during output. -/
def P1 : Prover oS Unit Unit Unit Unit pS1 where
  PrvState := fun _ => Unit
  input := fun _ => ()
  sendMessage := fun i => absurd i.1.isLt (by simp)
  receiveChallenge := fun i => absurd i.1.isLt (by simp)
  output := fun _ => do let _ ← (query (spec := oS) () : OracleComp oS Bool); pure ((), ())

/-- The right prover receives the opening challenge. -/
def P2 : Prover oS Unit Unit Unit Unit pS2 where
  PrvState := fun _ => Unit
  input := fun _ => ()
  sendMessage := fun i _ => absurd i.2 (by fin_cases i)
  receiveChallenge := fun _ _ => pure (fun _ => ())
  output := fun _ => pure ((), ())

/-- Head-query observer: `true` iff the computation's first action is a query
to the LEFT (ambient) component of a sum spec. Constructor-level: no rewriting
of lifted-query spellings needed — `congrArg headIsLeft` + kernel evaluation
discriminates the two effect orders. -/
def headIsLeft {ι₁ ι₂ : Type} {spec : OracleSpec (ι₁ ⊕ ι₂)} {α : Type} :
    OracleComp spec α → Bool
  | PFunctor.FreeM.liftBind (Sum.inl _) _ => true
  | _ => false

/-- Raw execution fails to factor for this effectful, challenge-opening seam. -/
theorem raw_factorization_fails :
    ¬ ((P1.append P2).run () () = (do
      let r₁ ← liftAppendLeft pS2 (P1.run () ())
      let r₂ ← liftAppendRight pS1 (P2.run r₁.2.1 r₁.2.2)
      pure (r₁.1 ++ₜ r₂.1, r₂.2))) := by
  intro h
  -- Kernel evaluation: the composed run's first action is the boundary
  -- challenge query (right/`Sum.inr` component); the sequential form's first
  -- action is the handoff output's ambient query (left/`Sum.inl`). The
  -- head-query observer maps them to `false` and `true` respectively.
  exact Bool.noConfusion (congrArg headIsLeft h)

/-- Effect-order witnesses, pinned as `rfl` probes: the composed machine's
first action is the boundary challenge (right component)... -/
example : headIsLeft ((P1.append P2).run () ()) = false := rfl

/-- ...while the sequential factorization's first action is the handoff
output's ambient oracle query (left component). -/
example : headIsLeft (do
    let r₁ ← liftAppendLeft pS2 (P1.run () ())
    let r₂ ← liftAppendRight pS1 (P2.run r₁.2.1 r₁.2.2)
    pure (r₁.1 ++ₜ r₂.1, r₂.2)) = true := rfl

end ArkLib.AppendRunNecessity

/--
info: 'ArkLib.AppendRunNecessity.raw_factorization_fails' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms ArkLib.AppendRunNecessity.raw_factorization_fails
