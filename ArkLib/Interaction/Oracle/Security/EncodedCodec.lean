/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestorationStoppedBudget

/-!
# Strict encodings of restoration query keys

A decoder recognizes exactly the encoded image. Inputs decoded to `none` form the domain that
an arbitrary external adversary can also query. Both inverse laws are necessary: a left inverse
alone would allow a decoder to identify unrelated external strings with a native key.
-/

@[expose] public section

namespace Interaction.Oracle.Security.StateRestoration

/-- A computable key encoding with a strict partial inverse on the entire external domain. -/
structure StrictCodec (K D : Type) where
  encode : K → D
  decode : D → Option K
  decode_encode : ∀ key, decode (encode key) = some key
  encode_decode : ∀ d key, decode d = some key → encode key = d

namespace StrictCodec

variable {K D : Type} (codec : StrictCodec K D)

/-- Strict decoding makes the encoding injective. -/
theorem encode_injective : Function.Injective codec.encode := by
  intro first second h
  have := congrArg codec.decode h
  simpa only [codec.decode_encode, Option.some.injEq] using this

/-- External inputs that are not native images. -/
def OffImage : Type := {d : D // codec.decode d = none}

theorem decode_none_of_not_image (d : D)
    (h : ∀ key, codec.encode key ≠ d) : codec.decode d = none := by
  cases hdecode : codec.decode d with
  | none => rfl
  | some key => exact (h key (codec.encode_decode d key hdecode)).elim

theorem not_image_of_decode_none (d : D) (hdecode : codec.decode d = none) :
    ∀ key, codec.encode key ≠ d := by
  intro key heq
  subst d
  simp only [codec.decode_encode] at hdecode
  contradiction

/-- Classify an external key by its strict decoder result. -/
def classify (d : D) : K ⊕ codec.OffImage :=
  match h : codec.decode d with
    | some key => .inl key
    | none => .inr ⟨d, h⟩

theorem classify_some (d : D) (key : K) (h : codec.decode d = some key) :
    codec.classify d = .inl key := by
  unfold classify
  split
  · rename_i value hvalue
    have heq : value = key := Option.some.inj (hvalue.symm.trans h)
    subst value
    rfl
  · rename_i hnone
    cases hnone.symm.trans h

theorem classify_none (d : D) (h : codec.decode d = none) :
    codec.classify d = .inr ⟨d, h⟩ := by
  unfold classify
  split
  · rename_i value hvalue
    cases hvalue.symm.trans h
  · rename_i hnone
    rfl

/-- Every external key is uniquely either an encoded native key or an off-image key. -/
def split : D ≃ K ⊕ codec.OffImage where
  toFun := codec.classify
  invFun := fun
    | .inl key => codec.encode key
    | .inr d => d.1
  left_inv d := by
    cases h : codec.decode d with
    | some key =>
        rw [codec.classify_some d key h]
        exact codec.encode_decode d key h
    | none =>
        rw [codec.classify_none d h]
  right_inv x := by
    cases x with
    | inl key =>
        exact codec.classify_some (codec.encode key) key (codec.decode_encode key)
    | inr off =>
        rcases off with ⟨d, h⟩
        exact codec.classify_none d h

@[simp] theorem split_encode (key : K) : codec.split (codec.encode key) = .inl key := by
  exact codec.classify_some (codec.encode key) key (codec.decode_encode key)

@[simp] theorem split_off (off : codec.OffImage) :
    codec.split off.1 = .inr off := by
  rcases off with ⟨d, h⟩
  exact codec.classify_none d h

end StrictCodec

end Interaction.Oracle.Security.StateRestoration
