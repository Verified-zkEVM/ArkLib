/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.NonInteractiveArgument.FiatShamir.Protocol.Serialization
public import ArkLib.NonInteractiveArgument.FiatShamir.Canonical

/-!
# Canonical Fiat–Shamir for interactive protocols

The application interface returns only the NARG string and a Boolean decision. The existing
reduction-based compiler remains the internal proof interface. Computation equalities below
preserve oracle effects, so its security results refer to the same algorithms.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec OracleReduction

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {Statement Witness Salt U : Type}
  [VCVCompatible Statement] [∀ i, VCVCompatible (pSpec.Challenge i)]

/-- Generate a canonical NARG string with one ambient-only salt sample.
No terminal reduction output is executed. -/
def InteractiveProver.compileFiatShamir [VCVCompatible Salt]
    (P : InteractiveProver oSpec Statement Witness pSpec)
    (sampleSalt : OracleComp oSpec Salt) (stmt : Statement) (wit : Witness) :
    OracleComp (oSpec + fsChallengeOracle (Statement × Salt) pSpec)
      (FSSaltedNARGString pSpec Salt) := do
  let salt ← sampleSalt
  let (messages, _, _) ← P.toReductionProver.runToRoundFSSalted salt (Fin.last n)
    stmt (P.input (stmt, wit))
  return (salt, messages)

/-- Derive the interactive transcript and return its acceptance decision. -/
def InteractiveVerifier.compileFiatShamir [VCVCompatible Salt]
    (V : InteractiveVerifier oSpec Statement pSpec)
    (stmt : Statement) (nargString : FSSaltedNARGString pSpec Salt) :
    OracleComp (oSpec + fsChallengeOracle (Statement × Salt) pSpec) Bool := do
  let transcript ← nargString.2.deriveTranscriptFS (oSpec := oSpec) (stmt, nargString.1)
  (V.verify stmt transcript).liftComp _

/-- Canonical FS with an abstract salt type, used for encoding correspondence. -/
def InteractiveProtocol.compileFiatShamir [VCVCompatible Salt]
    (protocol : InteractiveProtocol oSpec Statement Witness pSpec)
    (sampleSalt : OracleComp oSpec Salt) :
    NonInteractiveArgument (oSpec + fsChallengeOracle (Statement × Salt) pSpec)
      Statement Witness (FSSaltedNARGString pSpec Salt) where
  prover := protocol.prover.compileFiatShamir sampleSalt
  verifier := protocol.verifier.compileFiatShamir

/-- Canonical FS generates one NARG string using a salt of the configured length. -/
def InteractiveProver.fiatShamirTyped [VCVCompatible U] (saltLength : Nat)
    (P : InteractiveProver oSpec Statement Witness pSpec)
    (sampleSalt : OracleComp oSpec (Vector U saltLength)) :
    Statement → Witness →
      OracleComp (oSpec + canonicalFSOracle Statement pSpec U saltLength)
        (FiatShamirNARGString pSpec U saltLength) :=
  P.compileFiatShamir sampleSalt

/-- Canonical FS verification returns a decision bit. -/
def InteractiveVerifier.fiatShamirTyped [VCVCompatible U] (saltLength : Nat)
    (V : InteractiveVerifier oSpec Statement pSpec) :
    Statement → FiatShamirNARGString pSpec U saltLength →
      OracleComp (oSpec + canonicalFSOracle Statement pSpec U saltLength) Bool :=
  V.compileFiatShamir

/-- Compile a public-coin protocol to a NARG-string generator and decision algorithm. -/
def InteractiveProtocol.fiatShamirTyped [VCVCompatible U] (saltLength : Nat)
    (protocol : InteractiveProtocol oSpec Statement Witness pSpec)
    (sampleSalt : OracleComp oSpec (Vector U saltLength)) :
    NonInteractiveArgument (oSpec + canonicalFSOracle Statement pSpec U saltLength)
      Statement Witness (FiatShamirNARGString pSpec U saltLength) :=
  protocol.compileFiatShamir sampleSalt

/-- Generate the canonical byte encoding of the salt and prover messages. -/
def InteractiveProver.fiatShamir [VCVCompatible U] (saltLength : Nat)
    (P : InteractiveProver oSpec Statement Witness pSpec)
    (serializer : Serializer (FiatShamirNARGString pSpec U saltLength))
    (sampleSalt : OracleComp oSpec (Vector U saltLength))
    (stmt : Statement) (wit : Witness) :
    OracleComp (oSpec + canonicalFSOracle Statement pSpec U saltLength) ByteArray :=
  serializer.serialize <$> P.fiatShamirTyped saltLength sampleSalt stmt wit

/-- Parse the entire NARG string before reconstructing and checking the transcript. -/
def InteractiveVerifier.fiatShamir [VCVCompatible U] (saltLength : Nat)
    (V : InteractiveVerifier oSpec Statement pSpec)
    (serializer : Serializer (FiatShamirNARGString pSpec U saltLength))
    (stmt : Statement) (bytes : ByteArray) :
    OracleComp (oSpec + canonicalFSOracle Statement pSpec U saltLength) Bool :=
  match serializer.deserialize bytes with
  | none => pure false
  | some nargString => V.fiatShamirTyped saltLength stmt nargString

/-- Compile a public-coin protocol to a byte-valued NARG and decision algorithm. -/
def InteractiveProtocol.fiatShamir [VCVCompatible U] (saltLength : Nat)
    (protocol : InteractiveProtocol oSpec Statement Witness pSpec)
    (serializer : Serializer (FiatShamirNARGString pSpec U saltLength))
    (sampleSalt : OracleComp oSpec (Vector U saltLength)) :
    NonInteractiveArgument (oSpec + canonicalFSOracle Statement pSpec U saltLength)
      Statement Witness ByteArray :=
  (protocol.fiatShamirTyped saltLength sampleSalt).serialize serializer

omit [VCVCompatible Statement] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- The byte-valued compiler exposes the serialized prover algorithm. -/
@[simp] theorem InteractiveProtocol.fiatShamir_prover [VCVCompatible U] (saltLength : Nat)
    (protocol : InteractiveProtocol oSpec Statement Witness pSpec)
    (serializer : Serializer (FiatShamirNARGString pSpec U saltLength))
    (sampleSalt : OracleComp oSpec (Vector U saltLength)) :
    (protocol.fiatShamir saltLength serializer sampleSalt).prover =
      protocol.prover.fiatShamir saltLength serializer sampleSalt := rfl

omit [VCVCompatible Statement] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- The byte-valued compiler exposes parsing followed by typed verification. -/
@[simp] theorem InteractiveProtocol.fiatShamir_verifier [VCVCompatible U] (saltLength : Nat)
    (protocol : InteractiveProtocol oSpec Statement Witness pSpec)
    (serializer : Serializer (FiatShamirNARGString pSpec U saltLength))
    (sampleSalt : OracleComp oSpec (Vector U saltLength)) :
    (protocol.fiatShamir saltLength serializer sampleSalt).verifier =
      protocol.verifier.fiatShamir saltLength serializer := by
  funext stmt bytes
  cases h : serializer.deserialize bytes <;>
    simp [InteractiveProtocol.fiatShamir, NonInteractiveArgument.serialize,
      InteractiveVerifier.fiatShamir, h, InteractiveProtocol.fiatShamirTyped,
      InteractiveProtocol.compileFiatShamir, InteractiveVerifier.fiatShamirTyped]

omit [VCVCompatible Statement] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- The new generator is exactly the NARG string sent by the compatibility compiler,
including every oracle effect and excluding its terminal output. -/
theorem InteractiveProver.compileFiatShamir_eq_sendMessage [VCVCompatible Salt]
    (P : InteractiveProver oSpec Statement Witness pSpec)
    (sampleSalt : OracleComp oSpec Salt) (stmt : Statement) (wit : Witness) :
    P.compileFiatShamir sampleSalt stmt wit =
      Prod.fst <$> (P.toReductionProver.compileFiatShamir sampleSalt).sendMessage ⟨0, rfl⟩
        ((P.toReductionProver.compileFiatShamir sampleSalt).input (stmt, wit)) := by
  simp [InteractiveProver.compileFiatShamir, Prover.compileFiatShamir,
    InteractiveProver.toReductionProver]

omit [VCVCompatible Statement] [∀ i, VCVCompatible (pSpec.Challenge i)] in
/-- Verification has the same oracle computation as the established security interface.
A rejected NARG string returns `some false`; it is not confused with abort. -/
theorem InteractiveVerifier.compileFiatShamir_eq_verify [VCVCompatible Salt]
    (V : InteractiveVerifier oSpec Statement pSpec)
    (stmt : Statement) (nargString : FSSaltedNARGString pSpec Salt) :
    ((V.toReductionVerifier.compileFiatShamir).verify stmt
      (Fin.cons nargString (fun i => i.elim0))).run =
      some <$> V.compileFiatShamir stmt nargString := by
  simp only [ChallengeIdx, Challenge, Nat.reduceAdd, Fin.vcons_fin_zero,
    Verifier.compileFiatShamir, Fin.isValue, InteractiveVerifier.toReductionVerifier,
    OptionT.lift, bind_pure_comp, OptionT.run_mk, liftM_map, bind_map_left,
    Option.getM_some, bind_pure, Fin.cons_zero, OptionT.run_bind, OptionT.run_monadLift,
    monadLift_self, Option.elimM_map, Option.elim_some,
    InteractiveVerifier.compileFiatShamir, liftComp_eq_liftM, map_bind]
  congr 1
  funext transcript
  rw [← OracleComp.monadLift_liftM_OptionT]
  simp only [OptionT.run_monadLift, monadLift_self]
