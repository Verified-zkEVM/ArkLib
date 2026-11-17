/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.Data.Encoding.Serializer
public import ArkLib.NonInteractiveArgument.FiatShamir.Protocol

/-!
# Canonical byte serialization of non-interactive arguments

Serialization and parsing are pure. Malformed, noncanonical, and trailing-byte inputs reject
before any verifier oracle query. Valid inputs run exactly the structured verifier, preserving
its oracle effects. The payload type must encode all required mathematical validity conditions.
Resource checks on untrusted lengths and counts remain implementation obligations; the serializer
laws do not establish time or allocation bounds.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped NNReal

namespace NonInteractiveArgument

variable {ι : Type} {oSpec : OracleSpec ι} {Statement Witness Payload : Type}
  (argument : NonInteractiveArgument oSpec Statement Witness Payload)
  (serializer : Serializer Payload)

/-- Serialize the prover's payload and parse the verifier's entire input before verification. -/
def serialize : NonInteractiveArgument oSpec Statement Witness ByteArray where
  prover stmt wit := serializer.serialize <$> argument.prover stmt wit
  verifier stmt bytes := match serializer.deserialize bytes with
    | none => pure false
    | some payload => argument.verifier stmt payload

/-- Verification of an encoded payload has exactly the original oracle computation. -/
@[simp] theorem serialize_verifier (stmt : Statement) (payload : Payload) :
    (argument.serialize serializer).verifier stmt (serializer.serialize payload) =
      argument.verifier stmt payload := by
  simp [serialize, serializer.deserialize_serialize]

/-- Every accepted parse invokes exactly the verifier on the parsed valid payload. -/
theorem serialize_verifier_of_deserialize (stmt : Statement) (bytes : ByteArray)
    (payload : Payload) (h : serializer.deserialize bytes = some payload) :
    (argument.serialize serializer).verifier stmt bytes = argument.verifier stmt payload := by
  simp [serialize, h]

/-- Malformed and noncanonical inputs reject without oracle queries. -/
theorem serialize_verifier_reject (stmt : Statement) (bytes : ByteArray)
    (h : serializer.deserialize bytes = none) :
    (argument.serialize serializer).verifier stmt bytes = pure false := by
  simp [serialize, h]

/-- Appending nonempty bytes to a complete encoding rejects without oracle queries. -/
theorem serialize_verifier_append (stmt : Statement) (payload : Payload)
    (suffix : ByteArray) (h : suffix.size ≠ 0) :
    (argument.serialize serializer).verifier stmt (serializer.serialize payload ++ suffix) =
      pure false :=
  argument.serialize_verifier_reject serializer stmt _ (serializer.deserialize_append_eq_none _ _ h)

/-- Honest execution, including all oracle effects, is unchanged by serialization. -/
@[simp] theorem serialize_run (stmt : Statement) (wit : Witness) :
    (argument.serialize serializer).run stmt wit = argument.run stmt wit := by
  simp [run, serialize, bind_map_left, serializer.deserialize_serialize]

/-- The serialization wrapper preserves completeness with exactly the same error bound. -/
@[simp] theorem serialize_completeness_iff {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (relation : Set (Statement × Witness)) (error : ℝ≥0) :
    (argument.serialize serializer).completeness init impl relation error ↔
      argument.completeness init impl relation error := by
  simp [completeness]

end NonInteractiveArgument
