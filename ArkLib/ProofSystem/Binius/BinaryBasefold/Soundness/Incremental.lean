/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/

import ArkLib.Data.CodingTheory.ProximityGap.DG25
import ArkLib.ProofSystem.Binius.BinaryBasefold.Compliance
import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Lift
import CompPoly.Fields.Binary.Tower.Prelude

/-!
## Binary Basefold Soundness Incremental Argument

Incremental quotient-map and proximity lemmas for the refined Binary Basefold soundness proof.
The incremental bad-event, even/odd reduction, doom-preservation arguments, and the full
incremental Proposition 4.21.2 development in this file are formalization-specific
contributions of this development.
This file packages:
1. preliminary split and affine-line proximity lemmas used in the incremental far case
2. the full incremental Proposition 4.21.2 argument, including the even/odd reduction and both
   close/far branches
3. fold-to-affine-line bridges used by the incremental bad-event analysis
-/

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable {𝓑 : Fin 2 ↪ L}
noncomputable section
variable [SampleableType L]
variable [hdiv : Fact (ϑ ∣ ℓ)]

open scoped NNReal ProbabilityTheory

section Prelims

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [SampleableType L] in
/-- **Splitting a WordStack preserves non-closeness.**
If `U : WordStack L (Fin (2^{s+1})) ι` is NOT `e`-close to `C^{2^{s+1}}`, then
the interleaved pair `(⋈|U₀, ⋈|U₁)` is NOT `e`-close to `(C^{2^s})^⋈(Fin 2)`,
where `(U₀, U₁) := splitHalfRowWiseInterleavedWords(U)`.

The key is that `mergeHalfRowWiseInterleavedWords(U₀, U₁) = U` and the
column-wise Hamming distance is preserved under the split/merge. -/
lemma not_jointProximityNat_of_not_jointProximityNat_split
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {s : ℕ} (C : Set (ι → L))
    (U : WordStack (A := L) (κ := Fin (2 ^ (s + 1))) (ι := ι))
    (e : ℕ) (h_far : ¬ jointProximityNat (C := C) (u := U) (e := e)) :
    let U₀ := (splitHalfRowWiseInterleavedWords (ϑ := s) U).1
    let U₁ := (splitHalfRowWiseInterleavedWords (ϑ := s) U).2
    ¬ jointProximityNat₂ (A := InterleavedSymbol L (Fin (2^s)))
      (C := (C ^⋈ (Fin (2^s))))
      (u₀ := ⋈|U₀) (u₁ := ⋈|U₁) (e := e) := by
  exact fun h_close => h_far (CA_split_rowwise_implies_CA C U e h_close)

open Classical in
/-- **Affine proximity gap bound for RS interleaved codes (contrapositive form).**
If the pair `(u₀, u₁)` is NOT `e`-close to the interleaved code, then the
affine line `(1-r)·u₀ + r·u₁` is `e`-close to `C` for at most `|S|` values
of `r ∈ L`, giving `Pr_r[close] ≤ |S|/|L|`.

This follows from the contrapositive of:
- DG25 Thm 2.2 (RS codes exhibit affine line proximity gaps with `ε = |S|`), and
- DG25 Thm 3.1 (affine line proximity gaps lift to interleaved codes). -/
lemma affineProximityGap_RS_interleaved_contrapositive
    {m : ℕ} (hm : m ≥ 1) {destIdx : Fin r} (h_destIdx_le : destIdx ≤ ℓ)
    (u₀ u₁ : Word (InterleavedSymbol L (Fin m))
      (AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx))
    (e : ℕ) (he : e ≤ Code.uniqueDecodingRadius
      (ι := AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ) (R_rate := 𝓡)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) (F := L)
      (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx))
    (h_far : ¬ jointProximityNat₂ (A := InterleavedSymbol L (Fin m))
      (C := ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) ^⋈ (Fin m)))
      (u₀ := u₀) (u₁ := u₁) (e := e)) :
    Pr_{let r ← $ᵖ L}[
      Δ₀(affineLineEvaluation (F := L) u₀ u₁ r,
        ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) ^⋈ (Fin m))) ≤ e]
    ≤ (Fintype.card (AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
        (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) : ℝ≥0) / (Fintype.card L) := by
  sorry
end Prelims

open Classical in
/-- **Proposition 4.21.2 (Case 1: FiberwiseClose)**.
Incremental bad-event bound for a fixed block start and fixed consumed prefix, under the
block-level close branch.

The fresh event at step `k` is
`ℰ_{i+k} = ¬ E(i, k) ∧ E(i, k+1)` where `E := incrementalFoldingBadEvent`.

#### **Case 1: FiberwiseClose**

**Hypothesis:** `d^{(i)}(f^{(i)}, C^{(i)}) < d_{i+ϑ} / 2`.
**Condition:** We assume the bad event has *not* happened up to step `k` (i.e., `¬ E(i, k)` holds). This implies:
`Δ^{(i)}(f^{(i)}, f_bar^{(i)}) ⊆ Δ^{(i+k)}(fold_k(f^{(i)}), fold_k(f_bar^{(i)}))`
where `Δ^{(i+k)}` is the disagreement set projected to the destination domain `S^{i+ϑ}`.

We must bound the probability that a quotient point `y ∈ Δ^{(i+k)}` "vanishes" from the disagreement set in the next step `k+1`, i.e. `y ∉ Δ^{(i+k+1)}(fold(fold_k(f^{(i)}), r), fold(fold_k(f_bar^{(i)}), r))`. Let `f_k := fold_k(f^{(i)})` and `f_bar_k := fold_k(f_bar^{(i)})`.

Fix any `y ∈ Δ^{(i+k)}`.

* By definition, there exists at least one point `z` in the fiber of `y` (within the current domain `S^{i+k}`) such that `f_k(z) ≠ f_bar_k(z)` (by definition of `Δ^{(i+k)}`).

Consider the folding step `S^{i+k} → S^{i+k+1}`. The map `q` pairs points in `S^{i+k}` (say `x₀, x₁`) to a single point `w` in `S^{i+k+1}`.
The folded value at `w` is defined as (Definition 4.6):
`fold(f_k, r)(w) = [1-r, r] · M · [f_k(x₀), f_k(x₁)]ᵀ`
where `M = [[x₁, -x₀], [-1, 1]]` is an invertible matrix.

Let `E_y(r)(w)` (where `y ∈ Δ^{(i+k)}(fold_k(f^{(i)}), fold_k(f_bar^{(i)}))`) be the difference between the folded values of `f_k` and `f_bar_k` in `S^{i+k+1}` at `w`:
`E_y(r)(w) := fold(f_k, r)(w) - fold(f_bar_k, r)(w)`

Linearity allows us to rewrite this as:
`E_y(r)(w) = [1-r, r] · M · [f_k(x₀) - f_bar_k(x₀), f_k(x₁) - f_bar_k(x₁)]ᵀ`

Since `y ∈ Δ^{(i+k)} ⊂ S^{i+ϑ}`, the difference vector `v_vec = [f_k(x₀) - f_bar_k(x₀), f_k(x₁) - f_bar_k(x₁)]ᵀ` is non-zero for at least one pair `(x₀, x₁)` in the fiber of `y` (otherwise `f_k` is equal to `f_bar_k` at all points in `S^{i+k}`, contradicting the definition of `Δ^{(i+k)}`).

Because `M` is invertible, the vector `v_vec' = M · v_vec` is also **non-zero**. Let `v_vec' = [a, b]ᵀ`. Then:
`E_y(r)(w) = a(1-r) + br = a + (b-a)r`

This is a polynomial in `r` of degree at most 1. Since `v_vec' ≠ 0`, the **coefficients `a` and `b` cannot both be zero**.

* If `b ≠ a`, `E_y(r)(w)` has exactly one root.
* If `b = a ≠ 0`, `E_y(r)(w) = a ≠ 0`, so it has no roots.

Thus, `E_y(r)(w) = 0` (i.e. **the case where the point `y` disappears from `Δ^{i+k+1}`, though it was assumed to be in `Δ^{i+k}**`) with probability at most `1 / |L|` (**Schwartz-Zippel Lemma**).

If `E_y(r)(w) ≠ 0`, then `w ∈ Δ^{(i+k+1)}`, meaning `y` is preserved in the projected disagreement set, so it's not the case we care.

Applying the Union Bound over all `y ∈ Δ^{(i)} ⊆ S^{i+ϑ}` (noting that `|Δ^{(i)}| ≤ |S^{i+ϑ}|`):
`Pr[∃ y ∈ Δ^{(i)}, y ∉ Δ^{(i+k+1)}] ≤ ∑_{y ∈ Δ^{(i)}} 1 / |L| ≤ |S^{i+ϑ}| / |L|`

This completes the proof for Case 1.
-/
lemma prop_4_21_2_case_1_fiberwise_close_incremental
    (block_start_idx : Fin r) {midIdx_i midIdx_i_succ destIdx : Fin r} (k : ℕ) (h_k_lt : k < ϑ)
    (h_midIdx_i : midIdx_i = block_start_idx + k) (h_midIdx_i_succ : midIdx_i_succ = block_start_idx + k + 1)
    (h_destIdx : destIdx = block_start_idx + ϑ) (h_destIdx_le : destIdx ≤ ℓ)
    (f_block_start : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx)
    (r_prefix : Fin k → L)
    (h_block_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := block_start_idx) (steps := ϑ) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (f := f_block_start)) :
    let domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    Pr_{ let r_new ← $ᵖ L }[
      ¬ incrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (block_start_idx := block_start_idx) (midIdx := midIdx_i) (destIdx := destIdx) (k := k)
          (h_k_le := Nat.le_of_lt h_k_lt) (h_midIdx := h_midIdx_i) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
          (f_block_start := f_block_start) (r_challenges := r_prefix)
      ∧
      incrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (block_start_idx := block_start_idx) (midIdx := midIdx_i_succ) (destIdx := destIdx) (k := k + 1)
        (h_k_le := Nat.succ_le_of_lt h_k_lt) (h_midIdx := h_midIdx_i_succ) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (f_block_start := f_block_start)
        (r_challenges := Fin.snoc r_prefix r_new)
    ] ≤
    (domain_size / Fintype.card L) := by
  sorry
section EvenOddSplit
/-! **Even/odd split for Binius folding**

The Binius protocol folds out the **least significant bit** (dimension `i`) first.
`splitHalfRowWiseInterleavedWords` splits by the **most significant bit**, which
corresponds to factoring the last challenge. For the fold-to-affineLineEvaluation
equivalence we need an **even/odd split** that factors the **first** challenge:
- `U_even[j] = U[2j]` (rows with LSB = 0)
- `U_odd[j] = U[2j+1]` (rows with LSB = 1)

Then `affineLineEvaluation(U_even, U_odd, r_new)` correctly folds dimension `i` first. -/

variable {A : Type*} [AddCommMonoid A] [Module L A] {ι : Type*}

/-- Even/odd split: separate rows by LSB. `U_even[j] = U[2j]`, `U_odd[j] = U[2j+1]`. -/
def splitEvenOddRowWiseInterleavedWords {ϑ : ℕ}
    (u : (Fin (2 ^ (ϑ + 1))) → ι → A) :
    ((Fin (2 ^ ϑ)) → ι → A) × ((Fin (2 ^ ϑ)) → ι → A) := by
  have h : ∀ j : Fin (2 ^ ϑ), 2 * j.val < 2 ^ (ϑ + 1) := fun j => by omega
  let u_even : (Fin (2 ^ ϑ)) → ι → A := fun j => u ⟨2 * j.val, h j⟩
  let u_odd : (Fin (2 ^ ϑ)) → ι → A := fun j =>
    u ⟨2 * j.val + 1, by calc 2 * j.val + 1 < 2 * (2 ^ ϑ) := by omega
      _ = 2 ^ (ϑ + 1) := by ring⟩
  exact ⟨u_even, u_odd⟩

/-- Factor the **first** challenge (LSB): `multilinearCombine u r` equals
`multilinearCombine (affineLineEval U_even U_odd (r 0)) (fun j => r (j+1))`. -/
lemma multilinearCombine_recursive_form_first {ϑ : ℕ}
    (u : (Fin (2 ^ (ϑ + 1))) → ι → A) (r_challenges : Fin (ϑ + 1) → L) :
    let U_even := (splitEvenOddRowWiseInterleavedWords (r := r) (ℓ := ℓ) (𝓡 := 𝓡)
      (ϑ := ϑ) u).1
    let U_odd := (splitEvenOddRowWiseInterleavedWords (r := r) (ℓ := ℓ) (𝓡 := 𝓡)
      (ϑ := ϑ) u).2
    let r_tail : Fin ϑ → L := fun j => r_challenges (Fin.succ j)
    multilinearCombine (F := L) u r_challenges =
    multilinearCombine (F := L) (affineLineEvaluation (F := L) U_even U_odd (r_challenges 0)) r_tail := by
  intro U_even U_odd r_tail
  funext colIdx
  unfold multilinearCombine
  let f : ℕ → A := fun j =>
    if hj : j < 2 ^ (ϑ + 1) then
      multilinearWeight r_challenges ⟨j, hj⟩ • u ⟨j, hj⟩ colIdx
    else 0
  have h_lhs_as_f :
      (∑ rowIdx : Fin (2 ^ (ϑ + 1)),
        multilinearWeight r_challenges rowIdx • u rowIdx colIdx)
      = ∑ rowIdx : Fin (2 ^ (ϑ + 1)), f rowIdx := by
    apply Finset.sum_congr rfl
    intro rowIdx _
    simp [f]
  rw [h_lhs_as_f]
  rw [← Fin.sum_univ_odd_even (n := ϑ) (f := f)]
  simp [f]
  simp only [U_even, U_odd, splitEvenOddRowWiseInterleavedWords]
  have h_tensor_even : ∀ i : Fin (2 ^ ϑ),
      multilinearWeight r_challenges ⟨2 * i, by omega⟩ =
      multilinearWeight r_tail i * (1 - r_challenges 0) := by
    intro i
    unfold multilinearWeight
    rw [Fin.prod_univ_succ]
    have h_bit0 : (2 * i.val).testBit 0 = false := by
      rw [Nat.testBit_false_eq_getBit_eq_0]
      exact Nat.getBit_zero_of_two_mul (n := i.val)
    have h_bit0' : (2 * i.val).testBit (↑(0 : Fin (ϑ + 1))) = false := by
      change (2 * i.val).testBit 0 = false
      exact h_bit0
    have h_prod :
        (∏ x : Fin ϑ,
          if (2 * i.val).testBit x.succ = true then r_challenges x.succ else 1 - r_challenges x.succ)
        = ∏ j : Fin ϑ, if i.val.testBit j.val = true then r_tail j else 1 - r_tail j := by
      apply Finset.prod_congr rfl
      intro j _
      have h_test :
          ((2 * i.val).testBit (↑j.succ) = true) = (i.val.testBit j.val = true) := by
        rw [Nat.testBit_true_eq_getBit_eq_1, Nat.testBit_true_eq_getBit_eq_1]
        have h_getBit :
            Nat.getBit (j.val + 1) (2 * i.val) = Nat.getBit j.val i.val := by
          exact Nat.getBit_eq_succ_getBit_of_mul_two (n := i.val) (k := j.val)
        change (Nat.getBit (j.val + 1) (2 * i.val) = 1) = (Nat.getBit j.val i.val = 1)
        exact congrArg (fun t : ℕ => t = 1) h_getBit
      have h_succ : (↑j.succ : ℕ) = ↑j + 1 := by simp [Fin.succ]
      have h_test' :
          ((2 * i.val).testBit (↑j + 1) = true) = (i.val.testBit j.val = true) := by
        rw [← h_succ]
        exact h_test
      by_cases hcond : (2 * i.val).testBit (↑j + 1) = true
      · have hcond' : i.val.testBit j.val = true := h_test'.mp hcond
        simp [hcond, hcond', r_tail]
      · have hcond' : ¬ i.val.testBit j.val = true := by
          intro hbit
          exact hcond (h_test'.mpr hbit)
        simp [hcond, hcond', r_tail]
    rw [h_prod]
    simp [h_bit0']
    ring
  have h_tensor_odd : ∀ i : Fin (2 ^ ϑ),
      multilinearWeight r_challenges ⟨2 * i + 1, by omega⟩ =
      multilinearWeight r_tail i * (r_challenges 0) := by
    intro i
    unfold multilinearWeight
    rw [Fin.prod_univ_succ]
    have h_bit0 : (2 * i.val + 1).testBit 0 = true := by
      rw [Nat.testBit_true_eq_getBit_eq_1]
      unfold Nat.getBit
      simp [Nat.and_one_is_mod]
    have h_bit0' : (2 * i.val + 1).testBit (↑(0 : Fin (ϑ + 1))) = true := by
      change (2 * i.val + 1).testBit 0 = true
      exact h_bit0
    have h_prod :
        (∏ x : Fin ϑ,
          if (2 * i.val + 1).testBit x.succ = true then r_challenges x.succ else 1 - r_challenges x.succ)
        = ∏ j : Fin ϑ, if i.val.testBit j.val = true then r_tail j else 1 - r_tail j := by
      apply Finset.prod_congr rfl
      intro j _
      have h_test :
          ((2 * i.val + 1).testBit (↑j.succ) = true) = (i.val.testBit j.val = true) := by
        rw [Nat.testBit_true_eq_getBit_eq_1, Nat.testBit_true_eq_getBit_eq_1]
        have h_test := congrArg (fun t : ℕ => t = 1)
          (Nat.getBit_eq_succ_getBit_of_mul_two_add_one (n := i.val) (k := j.val))
        simp only [Fin.succ, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] at h_test ⊢
        exact h_test
      have h_succ : (↑j.succ : ℕ) = ↑j + 1 := by simp [Fin.succ]
      have h_test' :
          ((2 * i.val + 1).testBit (↑j + 1) = true) = (i.val.testBit j.val = true) := by
        rw [← h_succ]
        exact h_test
      simp only [Fin.val_succ, h_test', r_tail]
    rw [h_prod]
    simp [h_bit0']
    ring
  simp_rw [h_tensor_even, h_tensor_odd]
  have h_even_lt : ∀ x : Fin (2 ^ ϑ), 2 * x.val < 2 ^ (ϑ + 1) := by
    intro x; omega
  have h_odd_lt : ∀ x : Fin (2 ^ ϑ), 2 * x.val + 1 < 2 ^ (ϑ + 1) := by
    intro x; omega
  simp [h_even_lt, h_odd_lt]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  rw [affineLineEvaluation, Pi.add_apply, Pi.smul_apply]
  simp only [Word, Pi.smul_apply, Pi.add_apply, smul_add]
  rw [←smul_assoc, ←smul_assoc]
  rw [smul_eq_mul, smul_eq_mul]

end EvenOddSplit

/-- Even/odd split preserves non-closeness (bridge lemma for Binius first-step fold flow).
If `U` is not close to `C^⋈(Fin (2^(s+1)))`, then the even/odd split pair is not
jointly close to `C^⋈(Fin (2^s))`. -/
lemma not_jointProximityNat_of_not_jointProximityNat_evenOdd_split
    {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {s : ℕ} (C : Set (ι → L))
    (U : WordStack (A := L) (κ := Fin (2 ^ (s + 1))) (ι := ι))
    (e : ℕ)
    (U_even : WordStack (A := L) (κ := Fin (2 ^ s)) (ι := ι))
    (U_odd : WordStack (A := L) (κ := Fin (2 ^ s)) (ι := ι))
    (hU_even : U_even =
      (splitEvenOddRowWiseInterleavedWords (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := s) U).1 := by rfl)
    (hU_odd : U_odd =
      (splitEvenOddRowWiseInterleavedWords (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := s) U).2 := by rfl)
    (h_far : ¬ jointProximityNat (C := C) (u := U) (e := e)) :
    ¬ jointProximityNat₂ (A := InterleavedSymbol L (Fin (2^s)))
      (C := (C ^⋈ (Fin (2^s))))
      (u₀ := interleaveWordStack U_even) (u₁ := interleaveWordStack U_odd) (e := e) := by
  sorry
lemma fold_preTensorCombine_eq_affineLineEvaluation_split
    (i : Fin ℓ) (steps : ℕ) [NeZero steps] {midIdx destIdx : Fin r}
    (h_midIdx : midIdx.val = i.val + 1)
    (h_destIdx : destIdx.val = i.val + (steps + 1))
    (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i, by omega⟩)
    (r_new : L) :
    let h_midIdx_lt_ℓ : midIdx.val < ℓ := by
      have := NeZero.pos steps; omega
    let U := preTensorCombine_WordStack 𝔽q β i (steps + 1)
      (destIdx := destIdx) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) f_i
    let U_even := (splitEvenOddRowWiseInterleavedWords (r := r) (ℓ := ℓ) (𝓡 := 𝓡)
      (ϑ := steps) U).1
    let U_odd := (splitEvenOddRowWiseInterleavedWords (r := r) (ℓ := ℓ) (𝓡 := 𝓡)
      (ϑ := steps) U).2
    let fold_1_f := fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i, by omega⟩ (destIdx := midIdx) (h_destIdx := h_midIdx)
      (h_destIdx_le := by omega) f_i r_new
    let midIdx_fin_ℓ : Fin ℓ := ⟨midIdx.val, h_midIdx_lt_ℓ⟩
    let V := preTensorCombine_WordStack 𝔽q β midIdx_fin_ℓ steps
      (destIdx := destIdx)
      (h_destIdx := by simp [midIdx_fin_ℓ]; omega)
      (h_destIdx_le := h_destIdx_le) (by exact fold_1_f)
    interleaveWordStack V =
      affineLineEvaluation (F := L)
        (interleaveWordStack U_even) (interleaveWordStack U_odd) r_new := by
  sorry

section Fin1Interleaving
variable {A : Type*} [DecidableEq A] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] [SampleableType L]
  [Field L] [Fintype L] [DecidableEq L] [Field 𝔽q] [Fintype 𝔽q] h_Fq_char_prime [Algebra 𝔽q L]
  hβ_lin_indep h_ℓ_add_R_rate in
/-- For `κ = Fin 1`, the Hamming distance between two interleaved words equals the
Hamming distance between their row-0 projections. -/
lemma hammingDist_fin1_eq [DecidableEq (Fin 1 → A)] {u v : ι → Fin 1 → A} :
    hammingDist u v = hammingDist (fun y => u y 0) (fun y => v y 0) := by
  simp only [hammingDist]
  congr 1; ext y; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h heq; exact h (funext fun k => by rwa [show k = 0 from Subsingleton.elim k 0])
  · intro h heq; exact h (congr_fun heq 0)

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [NeZero 𝓡] [SampleableType L]
  [Field L] [Fintype L] [DecidableEq L] [Field 𝔽q] [Fintype 𝔽q] h_Fq_char_prime [Algebra 𝔽q L]
  hβ_lin_indep h_ℓ_add_R_rate in
/-- For `κ = Fin 1`, the distance from an interleaved word to an interleaved code equals
the distance from its row-0 projection to the base code. -/
lemma distFromCode_fin1_eq [DecidableEq (Fin 1 → A)] (u : ι → Fin 1 → A) (C : Set (ι → A)) :
    Δ₀(u, interleavedCodeSet (κ := Fin 1) C) = Δ₀((fun y => u y 0), C) := by
  simp only [distFromCode]
  congr 1; ext d; simp only [Set.mem_setOf_eq]; constructor
  · rintro ⟨v, hv_mem, hv_dist⟩
    refine ⟨fun y => v y 0, hv_mem 0, ?_⟩
    rwa [←hammingDist_fin1_eq (u := u) (v := v)]
  · rintro ⟨w, hw_mem, hw_dist⟩
    refine ⟨fun y _ => w y,
      fun k => by rwa [show k = 0 from Subsingleton.elim k 0], ?_⟩
    rwa [hammingDist_fin1_eq (A := A) (u := u) (v := fun y _ => w y)]

end Fin1Interleaving

/-- Single-step fold equals multilinearCombine on the corresponding preTensorCombine stack. -/
lemma fold_eq_multilinearCombine_preTensorCombine_step1
    (i : Fin ℓ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + 1) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (r_new : L) :
    let U := preTensorCombine_WordStack 𝔽q β i 1
      (destIdx := destIdx) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) f_i
    fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := ⟨i, by omega⟩)
      (destIdx := destIdx) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le) f_i r_new
    = multilinearCombine (F := L) U (fun (_ : Fin 1) => r_new) := by
  sorry
lemma fiberwiseClose_fold_implies_affineLineEval_close
    (i : Fin r) (h_i_lt_ℓ : i.val < ℓ) (s : ℕ)
    {midIdx destIdx : Fin r}
    (h_midIdx : midIdx.val = i.val + 1)
    (h_destIdx : destIdx.val = i.val + (s + 1))
    (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)
    (r_new : L)
    (h_fw_close : fiberwiseClose 𝔽q β midIdx s
      (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
      (fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        i (destIdx := midIdx) (h_destIdx := h_midIdx)
        (h_destIdx_le := by omega) f_i r_new)) :
    let i_ℓ : Fin ℓ := ⟨i.val, h_i_lt_ℓ⟩
    let U := preTensorCombine_WordStack 𝔽q β i_ℓ (s + 1)
      (destIdx := destIdx) (h_destIdx := by simp [i_ℓ]; omega)
      (h_destIdx_le := h_destIdx_le) f_i
    let U_even := (splitEvenOddRowWiseInterleavedWords (r := r) (ℓ := ℓ) (𝓡 := 𝓡)
      (ϑ := s) U).1
    let U_odd := (splitEvenOddRowWiseInterleavedWords (r := r) (ℓ := ℓ) (𝓡 := 𝓡)
      (ϑ := s) U).2
    let C_dest : Set (AdditiveNTT.Comp.sDomain (𝔽q := 𝔽q) (β := β) (ℓ := ℓ)
      (R_rate := 𝓡) (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx → L) :=
      BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
    Δ₀(affineLineEvaluation (F := L)
      (interleaveWordStack U_even) (interleaveWordStack U_odd) r_new,
      (C_dest ^⋈ (Fin (2^s)))) ≤
    Code.uniqueDecodingRadius (C := C_dest) := by
  sorry

lemma prop_4_21_2_case_2_fiberwise_far_incremental
    (block_start_idx : Fin r) {midIdx_i midIdx_i_succ destIdx : Fin r} (k : ℕ) (h_k_lt : k < ϑ)
    (h_midIdx_i : midIdx_i = block_start_idx + k) (h_midIdx_i_succ : midIdx_i_succ = block_start_idx + k + 1)
    (h_destIdx : destIdx = block_start_idx + ϑ) (h_destIdx_le : destIdx ≤ ℓ)
    (f_block_start : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx)
    (r_prefix : Fin k → L)
    (h_block_far : ¬ fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := block_start_idx) (steps := ϑ) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (f := f_block_start)) :
    let domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    Pr_{ let r_new ← $ᵖ L }[
      ¬ incrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (block_start_idx := block_start_idx) (midIdx := midIdx_i) (destIdx := destIdx) (k := k)
          (h_k_le := Nat.le_of_lt h_k_lt) (h_midIdx := h_midIdx_i) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
          (f_block_start := f_block_start) (r_challenges := r_prefix)
      ∧
      incrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (block_start_idx := block_start_idx) (midIdx := midIdx_i_succ) (destIdx := destIdx) (k := k + 1)
        (h_k_le := Nat.succ_le_of_lt h_k_lt) (h_midIdx := h_midIdx_i_succ) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (f_block_start := f_block_start)
        (r_challenges := Fin.snoc r_prefix r_new)
    ] ≤
    (domain_size / Fintype.card L) := by
  sorry
lemma prop_4_21_2_incremental_bad_event_probability
    (block_start_idx : Fin r) {midIdx_i midIdx_i_succ destIdx : Fin r} (k : ℕ) (h_k_lt : k < ϑ)
    (h_midIdx_i : midIdx_i = block_start_idx + k) (h_midIdx_i_succ : midIdx_i_succ = block_start_idx + k + 1)
    (h_destIdx : destIdx = block_start_idx + ϑ) (h_destIdx_le : destIdx ≤ ℓ)
    (f_block_start : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx)
    (r_prefix : Fin k → L) :
    let domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    Pr_{ let r_new ← $ᵖ L }[
      ¬ incrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (block_start_idx := block_start_idx) (midIdx := midIdx_i) (destIdx := destIdx) (k := k)
          (h_k_le := Nat.le_of_lt h_k_lt) (h_midIdx := h_midIdx_i) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
          (f_block_start := f_block_start) (r_challenges := r_prefix)
      ∧
      incrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (block_start_idx := block_start_idx) (midIdx := midIdx_i_succ) (destIdx := destIdx) (k := k + 1)
        (h_k_le := Nat.succ_le_of_lt h_k_lt) (h_midIdx := h_midIdx_i_succ) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (f_block_start := f_block_start)
        (r_challenges := Fin.snoc r_prefix r_new)
    ] ≤
    (domain_size / Fintype.card L) := by
  by_cases h_block_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := block_start_idx) (steps := ϑ) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
    (f := f_block_start)
  · exact prop_4_21_2_case_1_fiberwise_close_incremental 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (block_start_idx := block_start_idx)
      (midIdx_i := midIdx_i) (midIdx_i_succ := midIdx_i_succ) (destIdx := destIdx) (k := k) (h_k_lt := h_k_lt) (h_midIdx_i := h_midIdx_i) (h_midIdx_i_succ := h_midIdx_i_succ) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f_block_start := f_block_start)
      (r_prefix := r_prefix) (h_block_close := h_block_close)
  · exact prop_4_21_2_case_2_fiberwise_far_incremental 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (block_start_idx := block_start_idx)
      (midIdx_i := midIdx_i) (midIdx_i_succ := midIdx_i_succ) (destIdx := destIdx) (k := k) (h_k_lt := h_k_lt) (h_midIdx_i := h_midIdx_i) (h_midIdx_i_succ := h_midIdx_i_succ) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f_block_start := f_block_start)
      (r_prefix := r_prefix) (h_block_far := h_block_close)

end

end Binius.BinaryBasefold
