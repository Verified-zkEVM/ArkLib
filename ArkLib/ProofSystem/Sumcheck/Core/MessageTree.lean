/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.Types

/-! # Fixed message trees with explicit evaluation interfaces -/

@[expose] public section

namespace Sumcheck.Core.Interpreted
open PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec

/-- Evaluation access to an arbitrary message representation. -/
@[reducible] def messageInterface {R M : Type} (evaluate : M → R → R) : OracleInterface M where
  Query := R
  toOC := { spec := R →ₒ R, impl x := do return evaluate (← read) x }

/-- A fixed sequence of oracle messages and public challenges. -/
@[reducible] def protocol (R M : Type) (evaluate : M → R → R) : ℕ → OracleProtocol
  | 0 => .pure PUnit.unit
  | k + 1 => .liftBind (.oracle M (messageInterface evaluate)) fun _ =>
      .liftBind (.challenge R) fun _ => protocol R M evaluate k

/-- Splitting the fixed tree after its first round leaves the remaining fixed tree. -/
theorem protocol_succ_eq_append (R M : Type) (evaluate : M → R → R) (k : ℕ) :
    protocol R M evaluate (k + 1) =
      (protocol R M evaluate 1).append (fun _ => protocol R M evaluate k) := rfl

/-- Every challenge of the fixed tree is a ring element, so it can be sampled uniformly. Oracle
nodes are not challenge nodes, and each challenge node of one more round is the first round's
challenge or a challenge of the remaining rounds. -/
@[instance_reducible]
def challengeSampleable (R M : Type) [SampleableType R] (evaluate : M → R → R) :
    (k : ℕ) → (c : ChallengeNode oracleSig (protocol R M evaluate k)) →
      SampleableType (challengeSpec oracleSig (protocol R M evaluate k) c)
  | 0, ⟨n, _⟩ => nomatch n
  | _ + 1, ⟨.inl _, h⟩ => nomatch h
  | _ + 1, ⟨.inr ⟨_, .inl _⟩, _⟩ => inferInstanceAs (SampleableType R)
  | k + 1, ⟨.inr ⟨_, .inr ⟨_, c⟩⟩, h⟩ => challengeSampleable R M evaluate k ⟨c, h⟩

end Sumcheck.Core.Interpreted
