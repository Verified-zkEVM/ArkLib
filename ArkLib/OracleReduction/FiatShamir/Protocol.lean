/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.Execution
public import VCVio.OracleComp.SimSemantics.StateT.Measure

/-!
# Protocol interfaces for Fiat–Shamir

An interactive prover has input and round algorithms, but no terminal output. A public-coin
verifier decides whether to accept the statement and transcript. A non-interactive argument
prover returns only a NARG string, and its verifier returns a decision bit, as in [CO25].
These interfaces reuse `ProtocolSpec` and `ProverRound` without imposing reduction outputs.

## References

* [Chiesa, A. and Orrù, M., *A Fiat–Shamir Transformation From Duplex Sponges*][CO25]
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

/-- An honest interactive prover with an input statement and witness, and no terminal output. -/
structure InteractiveProver {ι : Type} (oSpec : OracleSpec ι)
    (Statement Witness : Type) {n : ℕ} (pSpec : ProtocolSpec n) extends
    ProverRound oSpec pSpec, ProverInput Statement Witness (PrvState 0)

/-- A public-coin verifier's decision algorithm.
Random verifier messages are supplied in the transcript. -/
structure InteractiveVerifier {ι : Type} (oSpec : OracleSpec ι)
    (Statement : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  verify : Statement → pSpec.FullTranscript → OracleComp oSpec Bool

/-- A public-coin interactive protocol, with a decision bit as its only public output. -/
structure InteractiveProtocol {ι : Type} (oSpec : OracleSpec ι)
    (Statement Witness : Type) {n : ℕ} (pSpec : ProtocolSpec n) where
  prover : InteractiveProver oSpec Statement Witness pSpec
  verifier : InteractiveVerifier oSpec Statement pSpec

/-- A non-interactive argument consists of NARG string generation and a decision algorithm.
No reduced statement or witness is computed or returned. -/
structure NonInteractiveArgument {ι : Type} (oSpec : OracleSpec ι)
    (Statement Witness NARGString : Type) where
  prover : Statement → Witness → OracleComp oSpec NARGString
  verifier : Statement → NARGString → OracleComp oSpec Bool

variable {ι : Type} {oSpec : OracleSpec ι} {Statement Witness NARGString : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}

/-- Forget the output algorithm of a reduction prover when using it in an interactive protocol. -/
def Prover.toInteractiveProver {StmtOut WitOut : Type}
    (P : Prover oSpec Statement Witness StmtOut WitOut pSpec) :
    InteractiveProver oSpec Statement Witness pSpec where
  toProverRound := P.toProverRound
  input := P.input

/-- Interpret an aborting Boolean verifier as a decision algorithm, treating abort as rejection. -/
def Verifier.toInteractiveVerifier (V : Verifier oSpec Statement Bool pSpec) :
    InteractiveVerifier oSpec Statement pSpec where
  verify := fun stmt transcript => do
    return (← (V.verify stmt transcript).run).getD false

/-- Internal compatibility adapter for the existing reduction-based execution proofs.
The terminal output is dummy data and is not executed by the NARG-string constructors. -/
def InteractiveProver.toReductionProver
    (P : InteractiveProver oSpec Statement Witness pSpec) :
    Prover oSpec Statement Witness Bool Unit pSpec where
  toProverRound := P.toProverRound
  input := P.input
  output := fun _ => pure (true, ())

/-- Embed a decision algorithm into the existing verifier proof machinery without changing
its oracle effects. A rejection bit stays `some false`, distinct from an abort. -/
def InteractiveVerifier.toReductionVerifier
    (V : InteractiveVerifier oSpec Statement pSpec) :
    Verifier oSpec Statement Bool pSpec where
  verify := fun stmt transcript => OptionT.lift (V.verify stmt transcript)

/-- Compatibility view for the existing security predicates and theorems. -/
def InteractiveProtocol.toReduction
    (protocol : InteractiveProtocol oSpec Statement Witness pSpec) :
    Proof oSpec Statement Witness pSpec where
  prover := protocol.prover.toReductionProver
  verifier := protocol.verifier.toReductionVerifier

@[simp] theorem InteractiveProver.toReductionProver_toInteractiveProver
    (P : InteractiveProver oSpec Statement Witness pSpec) :
    P.toReductionProver.toInteractiveProver = P := rfl

@[simp] theorem InteractiveVerifier.toReductionVerifier_run
    (V : InteractiveVerifier oSpec Statement pSpec)
    (stmt : Statement) (transcript : pSpec.FullTranscript) :
    (V.toReductionVerifier.verify stmt transcript).run = some <$> V.verify stmt transcript := by
  simp [InteractiveVerifier.toReductionVerifier, OptionT.lift]

/-- Execute the honest interaction and return the verifier's decision.
The established round executor fixes query ordering; no terminal prover output is executed. -/
def InteractiveProtocol.run (protocol : InteractiveProtocol oSpec Statement Witness pSpec)
    (stmt : Statement) (wit : Witness) : OracleComp (oSpec + [pSpec.Challenge]ₒ) Bool := do
  let (transcript, _) ← protocol.prover.toReductionProver.runToRound (Fin.last n) stmt wit
  (protocol.verifier.verify stmt transcript).liftComp _

/-- The compatibility view returns the same decision
and performs exactly the same oracle queries. -/
theorem InteractiveProtocol.toReduction_verdict
    (protocol : InteractiveProtocol oSpec Statement Witness pSpec)
    (stmt : Statement) (wit : Witness) :
    (protocol.toReduction.verdict stmt wit).run = some <$> protocol.run stmt wit := by
  simp [Reduction.verdict, Reduction.run, Prover.run, Verifier.run,
    InteractiveProtocol.toReduction, InteractiveProver.toReductionProver,
    InteractiveVerifier.toReductionVerifier, InteractiveProtocol.run,
    Option.getM, ← monadLift_liftM_OptionT]

/-- Generate a NARG string and verify it in the same oracle world. -/
def NonInteractiveArgument.run
    (argument : NonInteractiveArgument oSpec Statement Witness NARGString)
    (stmt : Statement) (wit : Witness) : OracleComp oSpec Bool := do
  argument.verifier stmt (← argument.prover stmt wit)

open scoped NNReal

/-- Completeness requires acceptance for every valid input, with the stated error bound. -/
def NonInteractiveArgument.completeness {σ : Type}
    (argument : NonInteractiveArgument oSpec Statement Witness NARGString)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (relation : Set (Statement × Witness)) (error : ℝ≥0) : Prop :=
  ∀ stmt wit, (stmt, wit) ∈ relation →
    Pr{let accepted ← (simulateQ impl (argument.run stmt wit)).run' (← init)}[
      accepted = true] ≥ 1 - error

/-- Interactive completeness samples a fresh uniform verifier message at each verifier round. -/
def InteractiveProtocol.completeness {σ : Type}
    [∀ i, SampleableType (pSpec.Challenge i)]
    (protocol : InteractiveProtocol oSpec Statement Witness pSpec)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (relation : Set (Statement × Witness)) (error : ℝ≥0) : Prop :=
  ∀ stmt wit, (stmt, wit) ∈ relation →
    let roundImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
      QueryImpl.addLift impl challengeQueryImpl
    Pr{let accepted ← (simulateQ roundImpl (protocol.run stmt wit)).run' (← init)}[
      accepted = true] ≥ 1 - error
