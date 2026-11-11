/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.MessageTree

/-! # Paths, views and query lifts of interpreted message trees

The fixed message tree has one shape path. These definitions read the first round of a path,
a transcript or a verifier view, and lift queries of the remaining rounds. They are generic in
the message carrier; the polynomial Sumcheck tree and its indexed verifier use the instance at
polynomial evaluation.
-/

@[expose] public section

namespace Sumcheck.Core.Interpreted
open PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec

variable {R M : Type} {evaluate : M → R → R}

/-- The shape path of an interpreted-message protocol. -/
def shape : (k : ℕ) → Path (protocol R M evaluate k)
  | 0 => PUnit.unit
  | k + 1 => ⟨PUnit.unit, PUnit.unit, shape k⟩

/-- All message and challenge values project to the same shape. -/
theorem shape_unique : ∀ (k : ℕ) (p : Path (protocol R M evaluate k)), p = shape k
  | 0, ⟨⟩ => rfl
  | k + 1, ⟨⟨⟩, ⟨⟨⟩, p⟩⟩ => by rw [shape_unique k p]; rfl

/-- The head message of a completed interpreted transcript. -/
def message {k : ℕ} (tr : PathAlong oracleSig (protocol R M evaluate (k + 1))) : M := tr.1

/-- The head public challenge of a completed interpreted transcript. -/
def challenge {k : ℕ} (tr : PathAlong oracleSig (protocol R M evaluate (k + 1))) : R := tr.2.1

/-- The suffix of a completed interpreted transcript. -/
def tail {k : ℕ} (tr : PathAlong oracleSig (protocol R M evaluate (k + 1))) :
    PathAlong oracleSig (protocol R M evaluate k) := tr.2.2

/-- The shape path of the remaining rounds. -/
def tailPath {k : ℕ} : Path (protocol R M evaluate (k + 1)) → Path (protocol R M evaluate k)
  | ⟨⟨⟩, ⟨⟨⟩, p⟩⟩ => p

/-- A query to the first message's evaluation interface. -/
def headQuery {k : ℕ} : (p : Path (protocol R M evaluate (k + 1))) → R →
    OracleComp (oracles (protocol R M evaluate (k + 1)) p) R
  | ⟨⟨⟩, ⟨⟨⟩, p⟩⟩, r => liftM
      ((oracles (protocol R M evaluate (k + 1)) ⟨⟨⟩, ⟨⟨⟩, p⟩⟩).query ⟨.inl PUnit.unit, r⟩)

/-- A lifted query to the remaining messages. -/
def tailLift {k : ℕ} (p : Path (protocol R M evaluate (k + 1))) :
    QueryImpl (oracles (protocol R M evaluate k) (tailPath p))
      (OracleComp (oracles (protocol R M evaluate (k + 1)) p)) := by
  rcases p with ⟨⟨⟩, ⟨⟨⟩, p⟩⟩
  exact fun q => liftM ((oracles (protocol R M evaluate (k + 1))
    ⟨⟨⟩, ⟨⟨⟩, p⟩⟩).query ⟨.inr q.1, q.2⟩)

/-- The challenge read from a verifier view. -/
def viewChallenge {k : ℕ} {p : Path (protocol R M evaluate (k + 1))}
    (v : View (protocol R M evaluate (k + 1)) p) : R := v.1.2.1

/-- Restrict a verifier view to its remaining rounds. -/
def tailView {k : ℕ} {p : Path (protocol R M evaluate (k + 1))}
    (v : View (protocol R M evaluate (k + 1)) p) :
    View (protocol R M evaluate k) (tailPath p) :=
  ⟨v.1.2.2, (shape_unique k _).trans (shape_unique k _).symm⟩

/-- Answering the head query uses exactly the supplied message interpretation. -/
theorem simulate_head {k : ℕ} (tr : PathAlong oracleSig (protocol R M evaluate (k + 1)))
    (r : R) : simulateQ (payloadImpl _ tr) (headQuery (projectPathAlong oracleSig _ tr) r) =
      evaluate (message tr) r := by
  rcases tr with ⟨msg, r, tail⟩
  rfl

/-- Answering lifted suffix queries uses exactly the suffix's payloads. -/
theorem simulate_tail {k : ℕ} (tr : PathAlong oracleSig (protocol R M evaluate (k + 1)))
    {α : Type} (program : OracleComp (oracles (protocol R M evaluate k)
      (tailPath (projectPathAlong oracleSig _ tr))) α) :
    simulateQ (payloadImpl _ tr) (simulateQ (tailLift (projectPathAlong oracleSig _ tr)) program) =
      simulateQ (payloadImpl _ (tail tr)) program := by
  refine QueryImpl.simulateQ_simulateQ_eq_of_apply (fun q => ?_) program
  rcases tr with ⟨msg, r, tail⟩
  rfl

end Sumcheck.Core.Interpreted
