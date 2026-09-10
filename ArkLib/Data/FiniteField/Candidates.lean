/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Data.List.Nodup
public import Mathlib.Data.Nat.Digits.Lemmas
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Explicit finite-field candidate prefixes

This file constructs duplicate-free parameter lists without enumerating an
entire field.  The prime-field prefix consists of the casts of
`0, ..., bound - 1`; it is duplicate-free whenever `bound` does not exceed the
characteristic.

For an extension field, `RadixBasis` packages an explicitly supplied basis
list together with the exact injectivity property needed of its base-`p`
digit expansions.  This module does not claim to construct such a basis.
-/

@[expose] public section

namespace ArkLib.FiniteFieldCandidates

/-- The first `bound` elements of the prime subfield, in their natural order. -/
def primeFieldPrefix (F : Type*) [AddMonoidWithOne F] (bound : ℕ) : List F :=
  (List.range bound).map fun i : ℕ ↦ (i : F)

@[simp]
theorem length_primeFieldPrefix (F : Type*) [AddMonoidWithOne F] (bound : ℕ) :
    (primeFieldPrefix F bound).length = bound := by
  simp [primeFieldPrefix]

/-- Natural casts below the characteristic are distinct. -/
theorem nodup_primeFieldPrefix_of_le_char
    (F : Type*) [AddMonoidWithOne F] [IsRightCancelAdd F]
    (p bound : ℕ) [CharP F p]
    (hbound : bound ≤ p) :
    (primeFieldPrefix F bound).Nodup := by
  rw [primeFieldPrefix, List.nodup_map_iff_inj_on List.nodup_range]
  intro left hleft right hright hequal
  exact CharP.natCast_injOn_Iio F p
    (lt_of_lt_of_le (List.mem_range.mp hleft) hbound)
    (lt_of_lt_of_le (List.mem_range.mp hright) hbound) hequal

/-- Evaluate a little-endian digit list against a same-length basis prefix.
`List.zipWith` makes this definition executable for ordinary list-backed field
implementations. -/
def digitExpansion {F : Type*} [Semiring F]
    (basis : List F) (digits : List ℕ) : F :=
  (List.zipWith (fun digit : ℕ ↦ fun vector : F ↦ (digit : F) * vector)
    digits basis).sum

private theorem list_eq_ofFn_get_cast {A : Type*}
    (values : List A) {length : ℕ} (hlength : values.length = length) :
    values = List.ofFn fun i : Fin length =>
      values.get (Fin.cast hlength.symm i) := by
  subst length
  exact (List.ofFn_get values).symm

private theorem digitExpansion_ofFn {F : Type*} [Semiring F] {length : ℕ}
    (vectors : Fin length → F) (digits : Fin length → ℕ) :
    digitExpansion (List.ofFn vectors) (List.ofFn digits) =
      ∑ i, (digits i : F) * vectors i := by
  rw [digitExpansion]
  have hzip :
      List.zipWith (fun digit : ℕ ↦ fun vector : F ↦ (digit : F) * vector)
          (List.ofFn digits) (List.ofFn vectors) =
        List.ofFn fun i => (digits i : F) * vectors i := by
    apply List.ext_get
    · simp
    · intro index hleft hright
      simp only [List.get_eq_getElem, List.getElem_zipWith, List.getElem_ofFn]
  rw [hzip, List.sum_ofFn]

/-- A supplied computable basis with unique base-`p` digit expansions.
The property is stated only on length-`extensionDegree` digit lists whose
entries lie below `p`, which is exactly the domain used by `radixEncode`. -/
structure RadixBasis (F : Type*) [Semiring F]
    (p extensionDegree : ℕ) where
  vectors : List F
  vectors_length : vectors.length = extensionDegree
  digitExpansion_injective : Set.InjOn (digitExpansion vectors)
    {digits : List ℕ |
      digits.length = extensionDegree ∧ ∀ digit ∈ digits, digit < p}

/-- Construct the radix-basis contract from an ordinary linearly independent
family over the prime field.  This removes the need for callers with a standard
basis to prove digit-expansion injectivity separately. -/
def RadixBasis.ofLinearIndependent
    {F : Type*} [Field F] {p extensionDegree : ℕ} [Fact p.Prime]
    [CharP F p] [Algebra (ZMod p) F]
    (vectors : Fin extensionDegree → F)
    (hlinear : LinearIndependent (ZMod p) vectors) :
    RadixBasis F p extensionDegree where
  vectors := List.ofFn vectors
  vectors_length := by simp
  digitExpansion_injective := by
    intro left hleft right hright hequal
    let leftCoefficients : Fin extensionDegree → ZMod p := fun i =>
      left.get (Fin.cast hleft.1.symm i)
    let rightCoefficients : Fin extensionDegree → ZMod p := fun i =>
      right.get (Fin.cast hright.1.symm i)
    have hleftEq := list_eq_ofFn_get_cast left hleft.1
    have hrightEq := list_eq_ofFn_get_cast right hright.1
    have hsum : ∑ i, leftCoefficients i • vectors i =
        ∑ i, rightCoefficients i • vectors i := by
      rw [hleftEq, hrightEq, digitExpansion_ofFn, digitExpansion_ofFn] at hequal
      simpa [leftCoefficients, rightCoefficients, Algebra.smul_def] using hequal
    have hcoefficients : leftCoefficients = rightCoefficients := by
      apply funext
      intro i
      have hzero : ∑ j, (leftCoefficients j - rightCoefficients j) • vectors j = 0 := by
        simp_rw [sub_smul]
        rw [Finset.sum_sub_distrib, hsum, sub_self]
      exact sub_eq_zero.mp ((Fintype.linearIndependent_iff.mp hlinear _ hzero) i)
    have hlength : left.length = right.length := hleft.1.trans hright.1.symm
    apply List.ext_get hlength
    intro index hindexLeft hindexRight
    let i : Fin extensionDegree := ⟨index, hleft.1 ▸ hindexLeft⟩
    have hcoefficient := congr_fun hcoefficients i
    apply CharP.natCast_injOn_Iio (ZMod p) p
    · exact hleft.2 _ (List.get_mem left ⟨index, hindexLeft⟩)
    · exact hright.2 _ (List.get_mem right ⟨index, hindexRight⟩)
    · simpa [leftCoefficients, rightCoefficients, i] using hcoefficient

/-- Encode an index using its padded little-endian base-`p` digits and a
supplied extension-field basis. -/
def radixEncode {F : Type*} [Semiring F] {p extensionDegree : ℕ}
    (basis : RadixBasis F p extensionDegree) (index : ℕ) : F :=
  digitExpansion basis.vectors (Nat.digitsAppend p extensionDegree index)

/-- The first `bound` radix encodings for a supplied extension-field basis. -/
def extensionFieldPrefix {F : Type*} [Semiring F] {p extensionDegree : ℕ}
    (basis : RadixBasis F p extensionDegree) (bound : ℕ) : List F :=
  (List.range bound).map (radixEncode basis)

@[simp]
theorem length_extensionFieldPrefix {F : Type*} [Semiring F]
    {p extensionDegree : ℕ} (basis : RadixBasis F p extensionDegree)
    (bound : ℕ) :
    (extensionFieldPrefix basis bound).length = bound := by
  simp [extensionFieldPrefix]

/-- Radix encoding gives a duplicate-free prefix of any requested length at
most `p ^ extensionDegree`. -/
theorem nodup_extensionFieldPrefix_of_le
    {F : Type*} [Semiring F] {p extensionDegree bound : ℕ}
    [CharP F p] (basis : RadixBasis F p extensionDegree)
    (hp : 1 < p) (hbound : bound ≤ p ^ extensionDegree) :
    (extensionFieldPrefix basis bound).Nodup := by
  rw [extensionFieldPrefix, List.nodup_map_iff_inj_on List.nodup_range]
  intro left hleft right hright hequal
  apply (Nat.bijOn_digitsAppend hp extensionDegree).injOn
  · exact lt_of_lt_of_le (List.mem_range.mp hleft) hbound
  · exact lt_of_lt_of_le (List.mem_range.mp hright) hbound
  · apply basis.digitExpansion_injective
    · exact Nat.mapsTo_digitsAppend hp extensionDegree
        (lt_of_lt_of_le (List.mem_range.mp hleft) hbound)
    · exact Nat.mapsTo_digitsAppend hp extensionDegree
        (lt_of_lt_of_le (List.mem_range.mp hright) hbound)
    · exact hequal

end ArkLib.FiniteFieldCandidates
