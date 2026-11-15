/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.OracleReduction.FiatShamir.Protocol.Canonical
public import ArkLib.NonInteractiveArgument.Legacy.Serialization

/-!
# Security of byte-valued non-interactive arguments

The compatibility verifier embeds the decision bit as `some Bool`; only `true` is accepting.
Serialization preserves soundness and knowledge soundness, including public-query budgets and
the extractor's oracle permissions. Failed parses return `some false`, without oracle queries.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped ENNReal

namespace NonInteractiveArgument

variable {ι κE : Type} {oSpec : OracleSpec ι} {extractorSpec : OracleSpec κE}
  {Stmt Wit Payload σ : Type}

/-- Embed a decision algorithm in the adaptive NARG security games; rejection remains a bit. -/
def toVerifier (argument : NonInteractiveArgument oSpec Stmt Wit Payload) :
    NonInteractiveVerifier Payload oSpec Stmt Bool where
  verify stmt messages := OptionT.lift (argument.verifier stmt (messages 0))

/-- The serialized decision algorithm is the parsing adapter with `false` as rejection. -/
theorem serialize_toVerifier (argument : NonInteractiveArgument oSpec Stmt Wit Payload)
    (serializer : Serializer Payload) :
    (argument.serialize serializer).toVerifier =
      NARGSerialization.verifier serializer argument.toVerifier (some false) := by
  apply Verifier.ext
  funext stmt messages
  apply OptionT.ext
  cases h : serializer.deserialize (messages 0) <;>
    simp [toVerifier, serialize, NARGSerialization.verifier, OptionT.lift, h]

/-- Canonical byte serialization preserves adaptive soundness and public-query budgets. -/
theorem serialize_soundnessQueryBounded
    (argument : NonInteractiveArgument oSpec Stmt Wit Payload)
    (serializer : Serializer Payload) (fallback : Payload)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (language : Set Stmt) (counts : ι → Prop) [DecidablePred counts] (t : ℕ) (error : ENNReal)
    (h : argument.toVerifier.adaptiveNARGSoundnessQueryBounded
      init impl language {true} counts t error) :
    (argument.serialize serializer).toVerifier.adaptiveNARGSoundnessQueryBounded
      init impl language {true} counts t error := by
  rw [serialize_toVerifier]
  exact NARGSerialization.soundnessQueryBounded serializer fallback init impl
    argument.toVerifier (some false) language {true} (by simp) counts t error h

/-- A single byte-facing extractor preserves the typed argument's knowledge-soundness bound. -/
theorem serialize_knowledgeSoundnessQueryBounded
    (argument : NonInteractiveArgument oSpec Stmt Wit Payload)
    (serializer : Serializer Payload) (fallback : Payload)
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (extractorImpl : QueryImpl extractorSpec (StateT σ ProbComp))
    (relation : Set (Stmt × Wit)) (counts : ι → Prop) [DecidablePred counts]
    (error : ℕ → ENNReal)
    (h : argument.toVerifier.adaptiveNARGKnowledgeSoundnessQueryBounded
      init impl extractorImpl relation {true} counts error) :
    (argument.serialize serializer).toVerifier.adaptiveNARGKnowledgeSoundnessQueryBounded
      init impl extractorImpl relation {true} counts error := by
  rw [serialize_toVerifier]
  exact NARGSerialization.knowledgeSoundnessQueryBounded serializer fallback init impl
    extractorImpl argument.toVerifier (some false) relation {true} (by simp) counts error h

end NonInteractiveArgument

variable {n : ℕ} {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
  {Stmt Wit Salt : Type}

/-- The typed protocol's security verifier is exactly the legacy basic-FS verifier. -/
theorem InteractiveProtocol.compileFiatShamir_toVerifier [VCVCompatible Salt]
    (P : InteractiveProtocol oSpec Stmt Wit pSpec) (sampleSalt : OracleComp oSpec Salt) :
    (P.compileFiatShamir sampleSalt).toVerifier =
      P.verifier.toReductionVerifier.compileFiatShamir := by
  apply Verifier.ext
  funext stmt messages
  apply OptionT.ext
  have hm : messages = Fin.cons (messages 0) (fun i => i.elim0) := by
    funext i
    fin_cases i
    rfl
  rw [hm]
  simpa [NonInteractiveArgument.toVerifier, InteractiveProtocol.compileFiatShamir, OptionT.lift]
    using (P.verifier.compileFiatShamir_eq_verify stmt (messages 0)).symm
