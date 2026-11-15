/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/

import ArkLib.Data.Encoding.Serializer

/-! Regression tests for canonical byte serializers, range validity, and whole-input parsing. -/

namespace SerializerRegression

/-- A canonical integer in the range [0, 17), encoded as one byte. -/
def rangeSerializer := (Serializer.vector 1).subtype (fun v => v[0].toNat < 17)

-- These execute the parser and serializer, including values just outside the canonical range.
run_cmd do
  let valid := ByteArray.mk #[16]
  match rangeSerializer.deserialize valid with
  | none => throwError "Canonical in-range integer was rejected"
  | some v =>
    unless rangeSerializer.serialize v == valid do
      throwError "Canonical integer did not round-trip"
  for bytes in [ByteArray.empty, ByteArray.mk #[17], ByteArray.mk #[255],
      ByteArray.mk #[16, 0]] do
    if (rangeSerializer.deserialize bytes).isSome then
      throwError "Invalid range, length, or trailing bytes were accepted"
  unless ((Serializer.vector 0).deserialize ByteArray.empty).isSome do
    throwError "Empty fixed-length vector should be valid"
  if ((Serializer.vector 0).deserialize (ByteArray.mk #[0])).isSome then
    throwError "Zero-length serializer accepted trailing bytes"

end SerializerRegression
