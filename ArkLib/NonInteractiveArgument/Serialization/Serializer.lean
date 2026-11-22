/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import Mathlib.Data.Vector.Basic

/-!
# Canonical byte serializers

A serializer parses a whole byte array into a valid value, with a unique encoding and no trailing
bytes. Validity conditions must be represented by the value type (for example a subgroup or
canonical-range subtype). Prefix freedom is separate from the two inverse laws: those laws alone
would allow an encoding with an appended suffix to encode a different value.

Implementation guidance: untrusted lengths and counts must be checked against remaining input
and resource limits before indexing, allocating, or performing potentially overflowing arithmetic.
The laws below do not establish resource bounds or the ordering of such checks.
-/

@[expose] public section

/-- An executable, whole-input byte serializer with canonical, prefix-free encodings. -/
structure Serializer (α : Type) where
  /-- Encode a valid value. -/
  serialize : α → ByteArray
  /-- Parse the entire input, rejecting invalid or noncanonical encodings. -/
  deserialize : ByteArray → Option α
  /-- Every valid value round-trips. -/
  deserialize_serialize : ∀ a, deserialize (serialize a) = some a
  /-- Every accepted input is exactly the encoding of its parsed value. -/
  serialize_deserialize : ∀ b a, deserialize b = some a → serialize a = b
  /-- No complete encoding is a proper prefix of another complete encoding. -/
  prefix_free : ∀ a b suffix, serialize a ++ suffix = serialize b → suffix.size = 0

namespace Serializer

variable {α β : Type} (c : Serializer α)

/-- Parsing succeeds exactly on canonical encodings of valid values. -/
theorem deserialize_eq_some_iff (bytes : ByteArray) (a : α) :
    c.deserialize bytes = some a ↔ c.serialize a = bytes := by
  constructor
  · exact c.serialize_deserialize bytes a
  · rintro rfl
    exact c.deserialize_serialize a

/-- Bytes outside the image of serialization are rejected. -/
theorem deserialize_eq_none_iff (bytes : ByteArray) :
    c.deserialize bytes = none ↔ ∀ a, c.serialize a ≠ bytes := by
  constructor
  · intro h a ha
    have := c.deserialize_eq_some_iff bytes a |>.mpr ha
    simp [h] at this
  · intro h
    cases he : c.deserialize bytes with
    | none => rfl
    | some a => exact False.elim (h a (c.serialize_deserialize bytes a he))

/-- Any nonempty suffix after a complete encoding causes rejection. -/
theorem deserialize_append_eq_none (a : α) (suffix : ByteArray) (h : suffix.size ≠ 0) :
    c.deserialize (c.serialize a ++ suffix) = none := by
  apply (c.deserialize_eq_none_iff _).mpr
  intro b hb
  exact h (c.prefix_free a b suffix hb.symm)

/-- Build a canonical serializer whose valid encodings all have a fixed byte length. -/
def ofFixedSize (size : Nat) (encode : α → ByteArray) (decode : ByteArray → Option α)
    (roundtrip : ∀ a, decode (encode a) = some a)
    (canonical : ∀ b a, decode b = some a → encode a = b)
    (encoded_size : ∀ a, (encode a).size = size) : Serializer α where
  serialize := encode
  deserialize := decode
  deserialize_serialize := roundtrip
  serialize_deserialize := canonical
  prefix_free := by
    intro a b suffix h
    have hs := congrArg ByteArray.size h
    simp only [ByteArray.size_append, encoded_size] at hs
    omega

/-- Fixed-length byte vectors have their direct byte-array encoding; length is checked first. -/
def vector (size : Nat) : Serializer (Vector UInt8 size) :=
  ofFixedSize size (fun v => ⟨v.toArray⟩)
    (fun b => if h : b.size = size then some ⟨b.data, h⟩ else none)
    (by intro v; simp [ByteArray.size])
    (by
      intro b v h
      split at h
      · cases Option.some.inj h
        rfl
      · contradiction)
    (by intro v; exact v.size_toArray)

/-- Transport a byte format along an executable equivalence of valid value types. -/
def ofEquiv (e : β ≃ α) : Serializer β where
  serialize b := c.serialize (e b)
  deserialize bytes := e.symm <$> c.deserialize bytes
  deserialize_serialize b := by simp [c.deserialize_serialize]
  serialize_deserialize bytes b h := by
    cases he : c.deserialize bytes with
    | none => simp [he] at h
    | some a =>
      have hab : e.symm a = b := by simpa [he] using h
      subst b
      simpa using c.serialize_deserialize bytes a he
  prefix_free a b suffix h := c.prefix_free (e a) (e b) suffix h

/-- Add a decidable validity condition, rejecting encodings of values that fail it. -/
def subtype (valid : α → Prop) [DecidablePred valid] : Serializer {a // valid a} where
  serialize a := c.serialize a.val
  deserialize bytes := do
    let a ← c.deserialize bytes
    if h : valid a then some ⟨a, h⟩ else none
  deserialize_serialize a := by simp [c.deserialize_serialize, a.property]
  serialize_deserialize bytes a h := by
    cases he : c.deserialize bytes with
    | none => simp [he] at h
    | some v =>
      simp only [he, bind, Option.bind] at h
      split at h
      · have hv := congrArg (Option.map Subtype.val) h
        have hva : v = a.val := by simpa using hv
        exact c.serialize_deserialize bytes a.val (hva ▸ he)
      · contradiction
  prefix_free a b suffix h := c.prefix_free a.val b.val suffix h

end Serializer
