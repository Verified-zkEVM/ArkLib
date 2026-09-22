/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.BinaryTrace
public import Mathlib.Algebra.CharP.Two
public import Mathlib.FieldTheory.Finite.Trace

/-!
# The absolute trace of a finite binary field

For a field `F` of size `2^m`, `binaryTrace m x` is the explicit Frobenius sum
`x + x² + ⋯ + x^(2^(m-1))`, valued in `F`. This intrinsic representation avoids choosing an
embedding of the two-element field and keeps polynomial evaluation identities literal.

## Main results

* `binaryTrace_eq_algebraMap_trace` identifies the sum with the canonical algebraic trace.
* `binaryTrace_eq_zero_or_one` identifies the image with the prime subfield.
* `exists_binaryTrace_eq_one` supplies a trace-one parameter when `m > 0`.
* `binaryTraceFiber_card` counts either trace fiber: each has exactly `|F| / 2` points.
* `quadratic_ne_zero_of_binaryTrace_eq_one` excludes `τ z² + z + 1 = 0`
  when the trace of `τ` is one.
  The trace-line construction uses this exclusion to control its separately assigned value at zero.

The cardinality hypothesis is explicit in each finite-field result. The formal sum and its
polynomial exist over more general coefficient types; no finite-field claim is made at `m = 0`.
The nonvanishing proof uses the polynomial root bound, and translation by a trace-one element
then pairs the zero and one fibers. `BinaryTraceQuotient` builds the low-degree quotients from
these facts.
-/

@[expose] public section

open scoped BigOperators

namespace FiniteField

/-- The intrinsic Frobenius-sum trace on a binary field. -/
def binaryTrace {F : Type*} [Semiring F] (m : ℕ) (x : F) : F :=
  ∑ i ∈ Finset.range m, x ^ (2 ^ i)

@[simp]
lemma binaryTrace_zero {F : Type*} [Semiring F] (x : F) : binaryTrace 0 x = 0 := by
  simp [binaryTrace]

lemma binaryTrace_succ {F : Type*} [Semiring F] (m : ℕ) (x : F) :
    binaryTrace (m + 1) x = binaryTrace m x + x ^ (2 ^ m) := by
  simp [binaryTrace, Finset.sum_range_succ]

end FiniteField

namespace Polynomial

open FiniteField

@[simp]
lemma eval_binaryTracePoly {F : Type*} [Semiring F] (m : ℕ) (x : F) :
    (binaryTracePoly m).eval x = binaryTrace m x := by
  classical
  rw [binaryTracePoly, binaryTrace, eval_finsetSum]
  simp_rw [eval_X_pow]

end Polynomial

namespace FiniteField

open _root_.Polynomial

section CharacteristicTwo

variable {F : Type*} [Field F] [CharP F 2]

omit [CharP F 2] in
@[simp]
lemma binaryTrace_zero_apply (m : ℕ) : binaryTrace m (0 : F) = 0 := by
  simp [binaryTrace]

lemma binaryTrace_add (m : ℕ) (x y : F) :
    binaryTrace m (x + y) = binaryTrace m x + binaryTrace m y := by
  simp only [binaryTrace, add_pow_char_pow, Finset.sum_add_distrib]

lemma binaryTrace_sq (m : ℕ) (x : F) :
    binaryTrace m x ^ 2 = binaryTrace m x + x + x ^ (2 ^ m) := by
  induction m with
  | zero => simpa using (CharTwo.add_self_eq_zero x).symm
  | succ m ih =>
      rw [binaryTrace_succ, add_pow_char]
      rw [ih]
      have hpow : (x ^ (2 ^ m)) ^ 2 = x ^ (2 ^ (m + 1)) := by
        rw [← pow_mul]
        congr 1
      rw [hpow]
      abel

lemma binaryTrace_pow_two (m : ℕ) (x : F) :
    binaryTrace m (x ^ 2) = binaryTrace m x ^ 2 := by
  classical
  rw [binaryTrace, binaryTrace, sum_pow_char]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← pow_mul, ← pow_mul]
  congr 1
  simp [Nat.mul_comm]

variable [Fintype F]

omit [CharP F 2] in
/-- The explicit binary Frobenius sum is the absolute algebraic trace, viewed in `F`. -/
lemma binaryTrace_eq_algebraMap_trace [Algebra (ZMod 2) F] {m : ℕ}
    (hcard : Fintype.card F = 2 ^ m) (x : F) :
    binaryTrace m x = algebraMap (ZMod 2) F (Algebra.trace (ZMod 2) F x) := by
  have hdim : Module.finrank (ZMod 2) F = m := by
    have hpow := FiniteField.pow_finrank_eq_card 2 F
    rw [hcard] at hpow
    exact (Nat.pow_right_injective (by omega : 2 ≤ 2)) hpow
  rw [FiniteField.algebraMap_trace_eq_sum_pow, hdim]
  simp [binaryTrace]

/-- On a field of size `2^m`, the Frobenius sum is fixed by squaring. -/
lemma binaryTrace_sq_eq_self {m : ℕ} (hcard : Fintype.card F = 2 ^ m) (x : F) :
    binaryTrace m x ^ 2 = binaryTrace m x := by
  rw [binaryTrace_sq, ← hcard, FiniteField.pow_card]
  simpa only [add_assoc, add_zero] using
    congrArg (fun y : F ↦ binaryTrace m x + y) (CharTwo.add_self_eq_zero x)

/-- The intrinsic trace of a binary field takes values in its two-element prime subfield. -/
lemma binaryTrace_eq_zero_or_one {m : ℕ} (hcard : Fintype.card F = 2 ^ m) (x : F) :
    binaryTrace m x = 0 ∨ binaryTrace m x = 1 := by
  exact eq_zero_or_one_of_sq_eq_self (binaryTrace_sq_eq_self hcard x)

/-- There is an element of absolute trace one. -/
lemma exists_binaryTrace_eq_one {m : ℕ} (hm : 0 < m)
    (hcard : Fintype.card F = 2 ^ m) : ∃ τ : F, binaryTrace m τ = 1 := by
  -- A nonzero trace polynomial has fewer roots than there are field elements.
  have hdegree : (binaryTracePoly (R := F) m).natDegree < Fintype.card F := by
    rw [natDegree_binaryTracePoly (F := F) hm, hcard]
    exact Nat.pow_lt_pow_right (by omega) (Nat.sub_lt hm Nat.one_pos)
  obtain ⟨τ, hτ⟩ := Polynomial.exists_eval_ne_zero_of_natDegree_lt_card
    (binaryTracePoly (R := F) m) (binaryTracePoly_ne_zero (F := F) hm) (by
      simpa only [Cardinal.mk_fintype, Nat.cast_lt] using hdegree)
  refine ⟨τ, (binaryTrace_eq_zero_or_one hcard τ).resolve_left ?_⟩
  simpa using hτ

variable [DecidableEq F]

/-- The finite fiber of a specified intrinsic trace value. -/
noncomputable def binaryTraceFiber (m : ℕ) (b : F) : Finset F := by
  classical
  exact Finset.univ.filter fun x ↦ binaryTrace m x = b

omit [CharP F 2] in
@[simp]
lemma mem_binaryTraceFiber {m : ℕ} {b x : F} :
    x ∈ binaryTraceFiber m b ↔ binaryTrace m x = b := by
  classical
  simp [binaryTraceFiber]

private lemma binaryTraceFiber_zero_card_eq_one_card {m : ℕ} {τ : F}
    (hτ : binaryTrace m τ = 1) :
    (binaryTraceFiber m (0 : F)).card = (binaryTraceFiber m (1 : F)).card := by
  classical
  apply Finset.card_bij (fun x _ ↦ x + τ)
  · intro x hx
    simp only [mem_binaryTraceFiber] at hx ⊢
    rw [binaryTrace_add, hx, hτ, zero_add]
  · intro x₁ _ x₂ _ h
    exact add_right_cancel h
  · intro y hy
    refine ⟨y + τ, ?_, ?_⟩
    · simp only [mem_binaryTraceFiber] at hy ⊢
      rw [binaryTrace_add, hy, hτ]
      exact CharTwo.add_self_eq_zero 1
    · rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

private lemma binaryTraceFiber_not_zero_eq_one {m : ℕ}
    (hcard : Fintype.card F = 2 ^ m) :
    Finset.univ.filter (fun x : F ↦ ¬binaryTrace m x = 0) = binaryTraceFiber m 1 := by
  classical
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, mem_binaryTraceFiber]
  constructor
  · intro hx
    exact (binaryTrace_eq_zero_or_one hcard x).resolve_left hx
  · intro hx hzero
    rw [hzero] at hx
    exact zero_ne_one hx

/-- Each of the two trace fibers contains exactly half of the field. -/
lemma binaryTraceFiber_card {m : ℕ} (hm : 0 < m)
    (hcard : Fintype.card F = 2 ^ m) (b : F) (hb : b = 0 ∨ b = 1) :
    (binaryTraceFiber m b).card = Fintype.card F / 2 := by
  classical
  -- Translation by a trace-one element pairs the two fibers.
  obtain ⟨τ, hτ⟩ := exists_binaryTrace_eq_one (F := F) hm hcard
  have heq := binaryTraceFiber_zero_card_eq_one_card (F := F) hτ
  have hsum := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset F)) (p := fun x : F ↦ binaryTrace m x = 0)
  change (binaryTraceFiber m 0).card +
    (Finset.univ.filter (fun x : F ↦ ¬binaryTrace m x = 0)).card = Fintype.card F at hsum
  rw [binaryTraceFiber_not_zero_eq_one hcard] at hsum
  have htwo : 2 * (binaryTraceFiber m (0 : F)).card = Fintype.card F := by
    simpa [two_mul, heq] using hsum
  have hzero : (binaryTraceFiber m (0 : F)).card = Fintype.card F / 2 :=
    Nat.eq_div_of_mul_eq_left (by omega) (by simpa [Nat.mul_comm] using htwo)
  rcases hb with rfl | rfl
  · exact hzero
  · rw [← heq]
    exact hzero

lemma binaryTraceFiber_zero_card {m : ℕ} (hm : 0 < m)
    (hcard : Fintype.card F = 2 ^ m) :
    (binaryTraceFiber m (0 : F)).card = Fintype.card F / 2 :=
  binaryTraceFiber_card hm hcard 0 (Or.inl rfl)

lemma binaryTraceFiber_one_card {m : ℕ} (hm : 0 < m)
    (hcard : Fintype.card F = 2 ^ m) :
    (binaryTraceFiber m (1 : F)).card = Fintype.card F / 2 :=
  binaryTraceFiber_card hm hcard 1 (Or.inr rfl)

omit [DecidableEq F] in
/-- An element of trace one cannot satisfy `τ z² + z + 1 = 0`. -/
lemma quadratic_ne_zero_of_binaryTrace_eq_one {m : ℕ} (hcard : Fintype.card F = 2 ^ m)
    {τ z : F} (hτ : binaryTrace m τ = 1) : τ * z ^ 2 + z + 1 ≠ 0 := by
  intro hquad
  by_cases hz : z = 0
  · simp [hz] at hquad
  -- A quadratic root would express τ as an Artin–Schreier value, whose trace is zero.
  have hτeq : τ = z⁻¹ ^ 2 + z⁻¹ := by
    have hmul : τ * z ^ 2 = z + 1 := by
      calc
        τ * z ^ 2 = -(z + 1) :=
          eq_neg_of_add_eq_zero_left (by simpa [add_assoc] using hquad)
        _ = z + 1 := CharTwo.neg_eq _
    calc
      τ = (τ * z ^ 2) * z⁻¹ ^ 2 := by field_simp
      _ = (z + 1) * z⁻¹ ^ 2 := by rw [hmul]
      _ = z⁻¹ ^ 2 + z⁻¹ := by field_simp; ac_rfl
  have htrace_inv_add : binaryTrace m (z⁻¹ ^ 2 + z⁻¹) = 0 := by
    rw [binaryTrace_add, binaryTrace_pow_two, binaryTrace_sq_eq_self hcard]
    exact CharTwo.add_self_eq_zero _
  rw [hτeq, htrace_inv_add] at hτ
  exact zero_ne_one hτ

end CharacteristicTwo

end FiniteField
