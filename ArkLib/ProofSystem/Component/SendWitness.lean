/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.OracleReduction.Security.Basic
import Mathlib.Data.FinEnum

/-!
# Simple Oracle Reduction - SendWitness

This file contains the (oracle) reduction for the trivial one-message protocol where the prover
sends the (entire) witness to the verifier. There are two variants:

1. For oracle reduction: the witness is an indexed family of types, and sent in a single oracle
  message to the verifier (using the derived indexed product instance for oracle interface).

  We also define a simpler variant where one sends a single witness (converted to be indexed by
  `Fin 1`).

2. For reduction: the witness is a type, and sent as a statement to the verifier.
-/

open OracleSpec OracleComp OracleQuery ProtocolSpec Function Equiv

variable {ι : Type} (oSpec : OracleSpec ι) (Statement : Type)

namespace SendWitness

/-!
  First, the reduction version (no oracle statements)
-/

section Reduction

variable (Witness : Type)

@[reducible, simp]
def pSpec : ProtocolSpec 1 := ![(.P_to_V, Witness)]

instance : ∀ i, VCVCompatible ((pSpec Witness).Challenge i) | ⟨0, h⟩ => nomatch h

@[inline, specialize]
def prover : Prover (pSpec Witness) oSpec Statement Witness (Statement × Witness) Unit where
  PrvState
  | 0 => Statement × Witness
  | 1 => Statement × Witness
  input := fun stmt wit => ⟨stmt, wit⟩
  sendMessage | ⟨0, _⟩ => fun ⟨stmt, wit⟩ => pure (wit, ⟨stmt, wit⟩)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun ⟨stmt, wit⟩ => (⟨stmt, wit⟩, ())

@[inline, specialize]
def verifier : Verifier (pSpec Witness) oSpec Statement (Statement × Witness) where
  verify := fun stmt transcript => pure ⟨stmt, transcript 0⟩

@[inline, specialize]
def reduction : Reduction (pSpec Witness) oSpec Statement Witness (Statement × Witness) Unit where
  prover := prover oSpec Statement Witness
  verifier := verifier oSpec Statement Witness

variable {Statement} {Witness} [oSpec.FiniteRange] (relIn : Statement → Witness → Prop)

@[reducible, simp]
def toRelOut : Statement × Witness → Unit → Prop :=
  fun ⟨stmt, wit⟩ _ => relIn stmt wit

/-- The `SendWitness` reduction satisfies perfect completeness. -/
@[simp]
theorem reduction_completeness :
    (reduction oSpec Statement Witness).perfectCompleteness relIn (toRelOut relIn) := by
  simp [Reduction.run, Prover.run, Prover.runToRound, Prover.processRound, Verifier.run,
    reduction, prover, verifier]
  aesop

theorem reduction_rbr_knowledge_soundness : True := sorry

end Reduction

/-!
  Now, the oracle reduction version
-/

section OracleReduction

variable {ιₛ : Type} (OStatement : ιₛ → Type) [∀ i, OracleInterface (OStatement i)]
  {ιw : Type} [FinEnum ιw] (Witness : ιw → Type) [∀ i, OracleInterface (Witness i)]

@[reducible, simp]
def oraclePSpec : ProtocolSpec 1 := ![(.P_to_V, ∀ i, Witness i)]

-- instance : IsEmpty (oraclePSpec Witness).ChallengeIdx where
--   false := by aesop
-- instance : ∀ i, OracleInterface ((oraclePSpec Witness).Message i)
--   | ⟨0, _⟩ => OracleInterface.instForall _
-- instance : ∀ i, VCVCompatible ((oraclePSpec Witness).Challenge i)
--   | ⟨0, _⟩ => by aesop

/-- The oracle prover for the `SendWitness` oracle reduction.

For each round `i : Fin (FinEnum.card ιw)`, the prover sends the witness
`wit (FinEnum.equiv.symm i)` to the verifier.
-/
@[inline, specialize]
def oracleProver : OracleProver (oraclePSpec Witness) oSpec
    Statement (∀ i, Witness i) Statement Unit
    OStatement (OStatement ⊕ᵥ Witness) where
  PrvState := fun _ => Statement × (∀ i, OStatement i) × (∀ i, Witness i)
  input := fun ⟨stmt, oStmt⟩ wit => ⟨stmt, oStmt, wit⟩
  sendMessage | ⟨0, _⟩ => fun ⟨stmt, oStmt, wit⟩ => pure (wit, ⟨stmt, oStmt, wit⟩)
  -- No challenge is sent to the prover
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun ⟨stmt, oStmt, wit⟩ => (⟨stmt, Sum.rec oStmt wit⟩, ())

-- /-- The oracle verifier for the `SendWitness` oracle reduction.

-- It receives the input statement `stmt` and returns it, and also specifying the combination of
-- `OStatement` and `Witness` as the output oracle statements.
-- -/
-- @[inline, specialize]
-- def oracleVerifier : OracleVerifier (oraclePSpec Witness) oSpec
--     Statement Statement OStatement (OStatement ⊕ᵥ Witness) where
--   verify := fun stmt _ => pure stmt
--   -- ιₛ ⊕ ιw ↪ ιₛ ⊕ (oraclePSpec Witness).MessageIdx
--   embed := Embedding.sumMap (.refl _)
--     -- ιw ↪ (oraclePSpec Witness).MessageIdx
--     (Equiv.toEmbedding
--       -- ιw ≃ (oraclePSpec Witness).MessageIdx
--       -- after unfolding : ιw ≃ { i : Fin (FinEnum.card ιw) // True }
--       (.trans FinEnum.equiv -- ιw ≃ Fin (FinEnum.card ιw)
--         <| .symm -- { i : Fin (FinEnum.card ιw) // True } ≃ Fin (FinEnum.card ιw)
--         <| .subtypeUnivEquiv (by simp)))
--   hEq := by intro i; rcases i <;> simp

-- @[inline, specialize]
-- def oracleReduction : OracleReduction (oraclePSpec Witness) oSpec
--     Statement (∀ i, Witness i) Statement Unit
--     OStatement (OStatement ⊕ᵥ Witness) where
--   prover := oracleProver oSpec Statement OStatement Witness
--   verifier := oracleVerifier oSpec Statement OStatement Witness

-- variable {Statement} {OStatement} {Witness} [oSpec.FiniteRange]
--   (oRelIn : Statement × (∀ i, OStatement i) → (∀ i, Witness i) → Prop)

-- @[reducible, simp]
-- def toORelOut : Statement × (∀ i, (OStatement ⊕ᵥ Witness) i) → Unit → Prop :=
--   fun ⟨stmt, oStmtAndWit⟩ _ =>
--     oRelIn ⟨stmt, fun i => oStmtAndWit (Sum.inl i)⟩ (fun i => oStmtAndWit (Sum.inr i))

-- /-- Running the oracle prover returns the expected result: `(stmt, Sum.rec oStmt wit)`. -/
-- theorem oracleProver_run {stmt : Statement} {oStmt : ∀ i, OStatement i} {wit : ∀ i, Witness i} :
--     (oracleProver oSpec Statement OStatement Witness).run ⟨stmt, oStmt⟩ wit =
--       pure ((stmt, Sum.rec oStmt wit), (), fun i => wit (FinEnum.equiv.symm i)) := by
--   simp [Prover.run, Prover.runToRound, Prover.processRound, oracleProver]
--   sorry

-- /-- The `SendWitness` oracle reduction satisfies perfect completeness. -/
-- @[simp]
-- theorem oracleReduction_completeness :
--     (oracleReduction oSpec Statement OStatement Witness).perfectCompleteness oRelIn
--     (toORelOut oRelIn) := by
--   simp [OracleReduction.perfectCompleteness, OracleReduction.toReduction,
--     OracleVerifier.toVerifier]
--   intro stmt oStmt wit hRelIn
--   unfold Reduction.run
--   sorry

-- theorem oracleReduction_rbr_knowledge_soundness : True := sorry

end OracleReduction

end SendWitness

namespace SendSingleWitness

/-!
  A special case of `SendWitness` oracle reduction where there is only one witness. We implicitly
  convert to `fun _ : Fin 1 => Witness`.
-/

variable {ιₛ : Type} (OStatement : ιₛ → Type) [∀ i, OracleInterface (OStatement i)]
  (Witness : Type) [OracleInterface Witness]

@[reducible, simp]
def oraclePSpec : ProtocolSpec 1 := ![(.P_to_V, Witness)]

/-- The oracle prover for the `SendSingleWitness` oracle reduction.

The prover sends the witness `wit` to the verifier as the only oracle message.
-/
@[inline, specialize]
def oracleProver : OracleProver (oraclePSpec Witness) oSpec
    Statement Witness Statement Unit
    OStatement (OStatement ⊕ᵥ (fun _ : Fin 1 => Witness)) where
  PrvState := fun _ => Statement × (∀ i, OStatement i) × Witness
  input := fun ⟨stmt, oStmt⟩ wit => ⟨stmt, oStmt, wit⟩
  sendMessage | ⟨0, _⟩ => fun state => pure (state.2.2, state)
  receiveChallenge | ⟨0, h⟩ => nomatch h
  output := fun ⟨stmt, oStmt, wit⟩ => (⟨stmt, Sum.rec oStmt (fun _ => wit)⟩, ())

/-- The oracle verifier for the `SendSingleWitness` oracle reduction.

The verifier receives the input statement `stmt` and returns it, and also specifying the oracle
message as the output oracle statement.
-/
@[inline, specialize]
def oracleVerifier : OracleVerifier (oraclePSpec Witness) oSpec
    Statement Statement OStatement (OStatement ⊕ᵥ (fun _ : Fin 1 => Witness)) where
  verify := fun stmt _ => pure stmt
  embed := .sumMap (.refl _)
    <| Equiv.toEmbedding
    <|.symm (subtypeUnivEquiv (by simp))
  hEq := by intro i; rcases i <;> simp

@[inline, specialize]
def oracleReduction : OracleReduction (oraclePSpec Witness) oSpec
    Statement Witness Statement Unit
    OStatement (OStatement ⊕ᵥ (fun _ : Fin 1 => Witness)) where
  prover := oracleProver oSpec Statement OStatement Witness
  verifier := oracleVerifier oSpec Statement OStatement Witness

variable {Statement} {OStatement} {Witness}

omit [(i : ιₛ) → OracleInterface (OStatement i)] [OracleInterface Witness] in
theorem oracleProver_run {stmt : Statement} {oStmt : ∀ i, OStatement i} {wit : Witness}:
    (oracleProver oSpec Statement OStatement Witness).run ⟨stmt, oStmt⟩ wit =
      pure (⟨stmt, Sum.rec oStmt (fun _ => wit)⟩, (), fun i => by simpa using wit) := by
  simp [Prover.run, Prover.runToRound, Prover.processRound, oracleProver, Transcript.concat]
  ext i; fin_cases i; simp [Fin.snoc]

theorem oracleVerifier_toVerifier_run {stmt : Statement} {oStmt : ∀ i, OStatement i}
    {tr : (oraclePSpec Witness).FullTranscript}:
    (oracleVerifier oSpec Statement OStatement Witness).toVerifier.run ⟨stmt, oStmt⟩ tr =
      pure ⟨stmt, Sum.rec oStmt (fun i => by simpa using tr i)⟩ := by
  simp [Verifier.run, OracleVerifier.toVerifier, oracleVerifier]
  ext i; rcases i <;> simp

variable [oSpec.FiniteRange] (oRelIn : Statement × (∀ i, OStatement i) → Witness → Prop)

@[reducible, simp]
def toORelOut : Statement × (∀ i, (Sum.elim OStatement fun _ : Fin 1 => Witness) i) → Unit → Prop :=
  fun ⟨stmt, oStmtAndWit⟩ _ =>
    oRelIn ⟨stmt, fun i => oStmtAndWit (Sum.inl i)⟩ (oStmtAndWit (Sum.inr 0))

/-- The `SendSingleWitness` oracle reduction satisfies perfect completeness. -/
@[simp]
theorem oracleReduction_completeness :
    (oracleReduction oSpec Statement OStatement Witness).perfectCompleteness oRelIn
    (toORelOut oRelIn) := by
  simp [OracleReduction.perfectCompleteness, OracleReduction.toReduction]
  simp_rw [Reduction.run, oracleReduction, oracleVerifier_toVerifier_run, oracleProver_run]
  aesop

theorem oracleReduction_rbr_knowledge_soundness : True := sorry

end SendSingleWitness
