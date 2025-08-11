/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.OracleReduction.Security.RoundByRound

/-!
  # Simple Oracle Reduction - SendClaim

  The prover sends a claim to the verifier.

    - There is no witness (e.g. `Witness = Unit`), and there is a single `OStatement`.
   - The prover sends a message of the same type as `OStatement` to the verifier.
   - The verifier performs the check for `rel`, which can be expressed as an oracle computation.
   - The output data has no `Statement`, only two `OStatement`s: one from the beginning data,
     and the other is the message from the prover.
   - The output relation checks whether the two `OStatement`s are the same.

   TODO: Generalize
-/

open OracleSpec OracleComp OracleQuery

namespace SendClaim

variable {ι : Type} (oSpec : OracleSpec ι) (Statement : Type)
  {ιₛᵢ : Type} [Unique ιₛᵢ] (OStatement : ιₛᵢ → Type) [inst : ∀ i, OracleInterface (OStatement i)]

@[reducible]
def pSpec : ProtocolSpec 1 := ⟨!v[.P_to_V], !v[OStatement default]⟩

/--
The prover takes in the old oracle statement as input, and sends it as the protocol message.
-/
def oracleProver : OracleProver oSpec
    Statement OStatement Unit
    Unit (OStatement ⊕ᵥ OStatement) Unit
    (pSpec OStatement) where
  PrvState := fun _ => OStatement default

  input := fun ⟨⟨_, oStmt⟩, _⟩ => oStmt default

  sendMessage | ⟨0, _⟩ => fun st => pure (st, st)

  receiveChallenge | ⟨0, h⟩ => nomatch h

  output := fun st => pure
    (⟨(), fun x => match x with
      | .inl _ => by simpa [Unique.uniq] using st
      | .inr default => by simpa [Unique.uniq] using st⟩,
     ())

variable (relIn : Set ((Statement × (∀ i, OStatement i)) × Unit))
  (relComp : Statement → OracleComp [OStatement]ₒ Unit)
  -- (rel_eq : ∀ stmt oStmt, rel stmt oStmt ↔
  --   (OracleInterface.simOracle []ₒ (OracleInterface.oracle oStmt)).run = oStmt)

/--
The verifier checks that the relationship `rel oldStmt newStmt` holds.
It has access to the original and new `OStatement` via their oracle indices.
-/
def oracleVerifier : OracleVerifier oSpec Statement OStatement Unit (OStatement ⊕ᵥ OStatement)
    (pSpec OStatement) where

  verify := fun stmt _ => relComp stmt

  embed := sorry

  hEq := sorry

/--
Combine the prover and verifier into an oracle reduction.
The input has no statement or witness, but one `OStatement`.
The output is also no statement or witness, but two `OStatement`s.
-/
def oracleReduction : OracleReduction oSpec
      Statement OStatement Unit
      Unit (OStatement ⊕ᵥ OStatement) Unit (pSpec OStatement) where
  prover := oracleProver oSpec Statement OStatement
  verifier := oracleVerifier oSpec Statement OStatement relComp

def relOut : Set ((Unit × (∀ i, (Sum.elim OStatement OStatement) i)) × Unit) :=
  setOf (fun ⟨⟨(), oracles⟩, _⟩ => oracles (.inl default) = oracles (.inr default))

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

/--
Proof of perfect completeness: if `rel old new` holds in the real setting,
it also holds in the ideal setting, etc.
-/
theorem completeness : (oracleReduction oSpec Statement OStatement relComp).perfectCompleteness
    init impl relIn (relOut OStatement) := by
  sorry

end SendClaim
