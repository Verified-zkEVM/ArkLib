/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BinaryWordMachine
public import Mathlib.Tactic.SplitIfs

/-!
# Binary-word values and actual local-bit executions

Natural-number operations below are specifications and proof-side bounds. The executed successor
is the Boolean/local-cell controller in `BinaryWordMachine`. Inputs may contain high zero padding;
addition produces canonical output with at most one extra bit and includes carry-in explicitly.
-/

@[expose] public section

namespace Computation.BinaryWordMachine

/-- Proof-side value of one Boolean bit. -/
def bitValue (b : Bool) : ℕ := if b then 1 else 0

/-- Proof-side little-endian decoding, never executed by a machine instruction. -/
def value : Word → ℕ
  | [] => 0
  | b :: bs => bitValue b + 2 * value bs

/-- No redundant high zeros; the unique zero representation is empty. -/
def Canonical (bits : Word) : Prop := bits = [] ∨ bits.getLast? = some true

/-- Physical width bounds the decoded value, even for noncanonical inputs. -/
theorem value_lt_width (bits : Word) : value bits < 2 ^ bits.length := by
  induction bits with
  | nil => decide
  | cons b bs ih =>
    have hb : bitValue b ≤ 1 := by cases b <;> decide
    simp only [value, List.length_cons, Nat.pow_succ]
    omega

/-- The Boolean full adder has the exact carry equation. -/
theorem carry_equation (x y carry : Bool) :
    bitValue (sumBit x y carry) + 2 * bitValue (carryBit x y carry) =
      bitValue x + bitValue y + bitValue carry := by
  cases x <;> cases y <;> cases carry <;> decide

/-- Proof-side unnormalized sum, with the same finite Boolean truth table as the controller. -/
def rawAdd : Word → Word → Bool → Word
  | [], [], carry => if carry then [true] else []
  | x :: xs, [], carry => sumBit x false carry :: rawAdd xs [] (carryBit x false carry)
  | [], y :: ys, carry => sumBit false y carry :: rawAdd [] ys (carryBit false y carry)
  | x :: xs, y :: ys, carry => sumBit x y carry :: rawAdd xs ys (carryBit x y carry)
termination_by xs ys _ => xs.length + ys.length

/-- The emitted bits and final carry decode to addition with carry-in. -/
theorem rawAdd_value (xs ys : Word) (carry : Bool) :
    value (rawAdd xs ys carry) = value xs + value ys + bitValue carry := by
  fun_induction rawAdd xs ys carry with
  | case1 => rfl
  | case2 c hc => simp [value, bitValue, hc]
  | case3 x xs c ih =>
    have hc := carry_equation x false c
    simp only [value, bitValue, Bool.false_eq_true, if_false] at ih hc ⊢
    omega
  | case4 y ys c ih =>
    have hc := carry_equation false y c
    simp only [value, bitValue, Bool.false_eq_true, if_false] at ih hc ⊢
    omega
  | case5 x xs y ys c ih =>
    have hc := carry_equation x y c
    simp only [value] at ih hc ⊢
    omega

/-- A carry can increase physical width by at most one bit. -/
theorem rawAdd_length (xs ys : Word) (carry : Bool) :
    (rawAdd xs ys carry).length ≤ max xs.length ys.length + 1 := by
  fun_induction rawAdd xs ys carry with
  | case1 => simp
  | case2 c hc => simp
  | case3 x xs c ih => simpa [rawAdd] using Nat.succ_le_succ ih
  | case4 y ys c ih => simpa [rawAdd] using Nat.succ_le_succ ih
  | case5 x xs y ys c ih => simpa [rawAdd] using Nat.succ_le_succ ih

/-- Proof-side trimming of a most-significant-first temporary tape. -/
def trimSpec : Word → Word
  | false :: bs => trimSpec bs
  | bs => bs

theorem value_append_false (xs : Word) : value (xs ++ [false]) = value xs := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp [value, ih]

theorem trimSpec_value (saved : Word) : value (trimSpec saved).reverse = value saved.reverse := by
  induction saved with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [trimSpec, List.reverse_cons, value_append_false, ih]

theorem trimSpec_length (saved : Word) : (trimSpec saved).length ≤ saved.length := by
  induction saved with
  | nil => exact Nat.le_refl _
  | cons b bs ih =>
    cases b
    · simp only [trimSpec, List.length_cons]
      omega
    · exact Nat.le_refl _

theorem trimSpec_canonical (saved : Word) : Canonical (trimSpec saved).reverse := by
  induction saved with
  | nil => exact Or.inl rfl
  | cons b bs ih =>
    cases b
    · exact ih
    · exact Or.inr (by simp [trimSpec])

/-- Every saved bit is moved individually; the final transition emits the output tape. -/
theorem reverse_trace (saved out : Word) :
    Trace (saved.length + 1) (.reverse saved out) (.word (saved.reverse ++ out)) := by
  induction saved generalizing out with
  | nil => exact Trace.cons rfl (Trace.nil _)
  | cons b bs ih =>
    simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (b :: out))

/-- Normalization is an actual linear tape run, including explicit removal of zero padding. -/
theorem trim_trace (saved : Word) :
    ∃ n ≤ saved.length + 2, Trace n (.trim saved) (.word (trimSpec saved).reverse) := by
  induction saved with
  | nil => exact ⟨1, by decide, Trace.cons rfl (Trace.nil _)⟩
  | cons b bs ih =>
    cases b
    · obtain ⟨n, hn, ht⟩ := ih
      exact ⟨n + 1, by simp only [List.length_cons]; omega, Trace.cons rfl ht⟩
    · refine ⟨(true :: bs).length + 2, Nat.le_refl _, ?_⟩
      simpa [trimSpec, Nat.add_assoc] using Trace.cons (by rfl) (reverse_trace (true :: bs) [])

/-- The actual carry scan produces the specification's bits on its reversed temporary tape. -/
theorem add_scan_trace (xs ys : Word) (carry : Bool) (saved : Word) :
    Trace (max xs.length ys.length + 1) (.add xs ys carry saved)
      (.trim ((rawAdd xs ys carry).reverse ++ saved)) := by
  fun_induction rawAdd xs ys carry generalizing saved with
  | case1 => exact Trace.cons rfl (Trace.nil _)
  | case2 c hc =>
    have h : c = false := by cases c <;> simp_all
    subst c
    exact Trace.cons rfl (Trace.nil _)
  | case3 x xs c ih =>
    simpa [rawAdd, List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (sumBit x false c :: saved))
  | case4 y ys c ih =>
    simpa [rawAdd, List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (sumBit false y c :: saved))
  | case5 x xs y ys c ih =>
    simpa [rawAdd, List.reverse_cons, List.append_assoc, Nat.add_assoc] using
      Trace.cons (by rfl) (ih (sumBit x y c :: saved))

/-- Same-trace addition with carry, canonical output and a linear physical-width bound. -/
theorem add_correct (xs ys : Word) (carry : Bool) :
    ∃ n ≤ 2 * max xs.length ys.length + 5, ∃ out : Word,
      Trace n (.startAdd xs ys carry) (.word out) ∧
      runFuel n (.startAdd xs ys carry) = .word out ∧
      value out = value xs + value ys + bitValue carry ∧ Canonical out ∧
      out.length ≤ max xs.length ys.length + 1 := by
  obtain ⟨n, hn, ht⟩ := trim_trace (rawAdd xs ys carry).reverse
  have hs := add_scan_trace xs ys carry []
  simp only [List.append_nil] at hs
  have hstart : step (.startAdd xs ys carry) = some (.add xs ys carry []) := rfl
  have h := Trace.cons hstart (hs.append ht)
  have hw := rawAdd_length xs ys carry
  refine ⟨_, ?_, _, h, h.runFuel_eq, ?_, trimSpec_canonical _, ?_⟩
  · simp only [List.length_reverse] at hn
    omega
  · rw [trimSpec_value, List.reverse_reverse, rawAdd_value]
  · have := trimSpec_length (rawAdd xs ys carry).reverse
    simp only [List.length_reverse] at this ⊢
    omega

/-- An input-width-only observation budget returns the same normalized sum and preserved RAM. -/
theorem add_runFuel (mem : AddressedBits.Memory) (xs ys : Word) (carry : Bool) :
    ∃ out : Word,
      ramRunFuel (2 * max xs.length ys.length + 5) (mem, .startAdd xs ys carry) =
        (mem, .word out) ∧
      value out = value xs + value ys + bitValue carry ∧ Canonical out ∧
      out.length ≤ max xs.length ys.length + 1 := by
  obtain ⟨n, hn, out, ht, _hr, hv, hc, hw⟩ := add_correct xs ys carry
  have h := ht.runFuel_done rfl (2 * max xs.length ys.length + 5 - n)
  rw [Nat.add_sub_of_le hn] at h
  exact ⟨out, by rw [ramRunFuel_eq, h], hv, hc, hw⟩

/-- Proof-side natural comparison; not executed by the local controller. -/
def natOrder (x y : ℕ) : Ordering := if x < y then .lt else if y < x then .gt else .eq

/-- Higher bits determine order unless they agree, in which case the lower bit decides. -/
theorem order_bit (x y : Bool) (a b : ℕ) (previous : Ordering) :
    (if a = b then compareBit x y previous else natOrder a b) =
      if bitValue x + 2 * a = bitValue y + 2 * b then previous
      else natOrder (bitValue x + 2 * a) (bitValue y + 2 * b) := by
  cases x <;> cases y <;> simp only [compareBit, bitValue, Bool.false_eq_true,
    Bool.true_eq_false, if_false, if_true]
  all_goals unfold natOrder
  all_goals split_ifs <;> first | rfl | omega

/-- Proof-side result of scanning increasingly significant input bits. -/
def comparison : Word → Word → Ordering → Ordering
  | [], [], previous => previous
  | x :: xs, [], previous => comparison xs [] (compareBit x false previous)
  | [], y :: ys, previous => comparison [] ys (compareBit false y previous)
  | x :: xs, y :: ys, previous => comparison xs ys (compareBit x y previous)
termination_by xs ys _ => xs.length + ys.length

theorem comparison_value (xs ys : Word) (previous : Ordering) :
    comparison xs ys previous =
      if value xs = value ys then previous else natOrder (value xs) (value ys) := by
  fun_induction comparison xs ys previous with
  | case1 p => simp [value]
  | case2 x xs p ih =>
    rw [ih]
    convert order_bit x false (value xs) (value []) p using 1
    simp [value, bitValue]
  | case3 y ys p ih =>
    rw [ih]
    convert order_bit false y (value []) (value ys) p using 1
    simp [value, bitValue]
    split_ifs <;> rfl
  | case4 x xs y ys p ih =>
    rw [ih]
    exact order_bit x y (value xs) (value ys) p

/-- Comparison consumes at most one bit from each input per successor and then emits its order. -/
theorem compare_scan_trace (xs ys : Word) (previous : Ordering) :
    Trace (max xs.length ys.length + 1) (.compare xs ys previous)
      (.ordering (comparison xs ys previous)) := by
  fun_induction comparison xs ys previous with
  | case1 p => exact Trace.cons rfl (Trace.nil _)
  | case2 x xs p ih =>
    simpa using Trace.cons (by rfl) ih
  | case3 y ys p ih =>
    simpa using Trace.cons (by rfl) ih
  | case4 x xs y ys p ih =>
    simpa using Trace.cons (by rfl) ih

/-- The same literal comparison run computes natural order, even with high zero padding. -/
theorem compare_correct (xs ys : Word) :
    Trace (max xs.length ys.length + 2) (.startCompare xs ys)
      (.ordering (natOrder (value xs) (value ys))) ∧
    runFuel (max xs.length ys.length + 2) (.startCompare xs ys) =
      .ordering (natOrder (value xs) (value ys)) := by
  have hs := compare_scan_trace xs ys .eq
  have he : comparison xs ys .eq = natOrder (value xs) (value ys) := by
    rw [comparison_value]
    split_ifs with h
    · simp [h, natOrder]
    · rfl
  rw [he] at hs
  have hstart : step (.startCompare xs ys) = some (.compare xs ys .eq) := rfl
  have ht := Trace.cons hstart hs
  exact ⟨ht, ht.runFuel_eq⟩

end Computation.BinaryWordMachine
