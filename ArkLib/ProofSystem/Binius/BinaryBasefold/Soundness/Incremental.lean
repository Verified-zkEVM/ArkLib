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
Proposition 4.20.2 development in this file are formalization-specific contributions of this
development.
This file packages:
1. preliminary split and affine-line proximity lemmas used in the incremental far case
2. the full Proposition 4.20.2 argument, including the even/odd reduction and both close/far
   branches
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
omit [CharP L 2] [DecidableEq 𝔽q] h_β₀_eq_1 [NeZero ℓ] [SampleableType L] in
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
      (sDomain 𝔽q β h_ℓ_add_R_rate destIdx))
    (e : ℕ) (he : e ≤ Code.uniqueDecodingRadius
      (ι := sDomain 𝔽q β h_ℓ_add_R_rate destIdx) (F := L)
      (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx))
    (h_far : ¬ jointProximityNat₂ (A := InterleavedSymbol L (Fin m))
      (C := ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) ^⋈ (Fin m)))
      (u₀ := u₀) (u₁ := u₁) (e := e)) :
    Pr_{let r ← $ᵖ L}[
      Δ₀(affineLineEvaluation (F := L) u₀ u₁ r,
        ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) ^⋈ (Fin m))) ≤ e]
    ≤ (Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) : ℝ≥0) / (Fintype.card L) := by
  by_contra h_prob_gt_bound
  apply h_far
  let S_dest := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
  let α := Embedding.subtype fun (x : L) ↦ x ∈ S_dest
  let C_dest := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
  let RS_dest := ReedSolomon.code α (2^(ℓ - destIdx.val))
  letI : Nontrivial RS_dest := by infer_instance
  let h_RS_affine := ReedSolomon_ProximityGapAffineLines_UniqueDecoding
    (A := L) (ι := S_dest) (α := α) (k := 2^(ℓ - destIdx.val))
    (hk := by
      rw [sDomain_card 𝔽q β h_ℓ_add_R_rate (i := destIdx)
        (h_i := Sdomain_bound (by exact h_destIdx_le))]
      calc 2 ^ (ℓ - destIdx.val) ≤ 2 ^ (ℓ + 𝓡 - destIdx.val) :=
            Nat.pow_le_pow_right (by omega) (by omega)
        _ = Fintype.card 𝔽q ^ (ℓ + 𝓡 - destIdx.val) := by rw [hF₂.out])
    e (by exact he)
  let h_lifted := affine_gaps_lifted_to_interleaved_codes (A := L)
    (F := L) (ι := S_dest) (MC := RS_dest) (m := m)
    (e := e) (he := he) (ε := Fintype.card S_dest)
    (hε := by
      have h_dist_pos : 0 < ‖(C_dest : Set (S_dest → L))‖₀ := by
        have h_pos : 0 <
            BBF_CodeDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx := by
          simp [BBF_CodeDistance_eq (L := L) 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := destIdx) (h_i := h_destIdx_le)]
        have h_dist_pos := h_pos
        simp only [C_dest, BBF_CodeDistance] at h_dist_pos ⊢
        exact h_dist_pos
      haveI : NeZero ‖(C_dest : Set (S_dest → L))‖₀ := NeZero.of_pos h_dist_pos
      have h_2e_lt_d : 2 * e < ‖(C_dest : Set (S_dest → L))‖₀ := by
        exact (Code.UDRClose_iff_two_mul_proximity_lt_d_UDR
          (C := (C_dest : Set (S_dest → L))) (e := e)).1 (by
            exact he)
      have h_e_add_one_le_d : e + 1 ≤ ‖(C_dest : Set (S_dest → L))‖₀ := by
        omega
      have h_d_le_card : ‖(C_dest : Set (S_dest → L))‖₀ ≤ Fintype.card S_dest := by
        exact Code.dist_le_card (C := (C_dest : Set (S_dest → L)))
      exact le_trans h_e_add_one_le_d h_d_le_card)
    h_RS_affine
  exact h_lifted u₀ u₁ (by
    rw [ENNReal.coe_natCast]
    rw [not_le] at h_prob_gt_bound
    exact h_prob_gt_bound)

end Prelims

open Classical in
/-- **Proposition 4.20.2 (Case 1: FiberwiseClose)**.
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
lemma prop_4_20_2_case_1_fiberwise_close_incremental
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
  -- ────────────────────────────────────────────────────────
  -- Step 0: Simplify incrementalFoldingBadEvent using h_block_close
  -- ────────────────────────────────────────────────────────
  dsimp only [incrementalFoldingBadEvent]
  have h_k_succ_ne_0 : ¬(k + 1 = 0) := by omega
  simp only [h_block_close, ↓reduceDIte]
  -- ────────────────────────────────────────────────────────
  -- Step 1: Name the key objects
  -- ────────────────────────────────────────────────────────
  let f_i := f_block_start
  let f_bar_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx :=
    UDRCodeword 𝔽q β (i := block_start_idx) (h_i := by omega)
      (f := f_i) (h_within_radius := UDRClose_of_fiberwiseClose 𝔽q β block_start_idx ϑ h_destIdx h_destIdx_le f_i h_block_close)
  let Δ_fiber : Finset (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) :=
    fiberwiseDisagreementSet 𝔽q β (i := block_start_idx) ϑ h_destIdx h_destIdx_le f_i f_bar_i
  -- The k-step folds (fixed, no r_new dependency)
  let fold_k_f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := block_start_idx) (steps := k) (h_destIdx := h_midIdx_i) (h_destIdx_le := by omega)
    (f := f_i) (r_challenges := r_prefix)
  let fold_k_f_bar := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := block_start_idx) (steps := k) (h_destIdx := h_midIdx_i) (h_destIdx_le := by omega)
    (f := f_bar_i) (r_challenges := r_prefix)
  -- ────────────────────────────────────────────────────────
  -- Step 2: Factor out the deterministic ¬E(k) conjunct.
  --   ¬E(k) = (Δ_fiber ⊆ disagr_set_at_k) does NOT depend on r_new,
  --   so we case-split: if false, Pr = 0; if true, use it as hypothesis.
  -- ────────────────────────────────────────────────────────
  -- The ¬E(k) predicate (subset condition at step k)
  let not_Ek := Δ_fiber ⊆ fiberwiseDisagreementSet 𝔽q β
    midIdx_i (ϑ - k) (by omega) h_destIdx_le fold_k_f fold_k_f_bar
  by_cases h_not_Ek : not_Ek
  swap
  · -- Case: ¬not_Ek, i.e. ¬(Δ_fiber ⊆ D_k). Then ¬¬(Δ ⊆ D_k) = False, so conjunction always False.
    -- Pr[always False] = 0 ≤ bound.
    apply le_trans (Pr_le_Pr_of_implies ($ᵖ L) _ (fun _ => False) (fun r_new h => absurd (not_not.mp h.1) h_not_Ek))
    simp only [PMF.monad_pure_eq_pure, PMF.monad_bind_eq_bind, PMF.bind_const, PMF.pure_apply,
      eq_iff_iff, iff_false, not_true_eq_false, ↓reduceIte, _root_.zero_le];
  · -- pos case
    -- From here: h_not_Ek : Δ_fiber ⊆ fiberwiseDisagreementSet(midIdx_i, ϑ-k, fold_k_f, fold_k_f_bar)
    -- Use prob_mono to drop the ¬E(k) conjunct (it's deterministically true).
    apply le_trans (Pr_le_Pr_of_implies ($ᵖ L) _ _ (fun r_new h => h.2))
    -- ────────────────────────────────────────────────────────
    -- Step 3: Bound Pr_{r_new}[E(k+1)] ≤ |S^{destIdx}| / |L|
    -- ────────────────────────────────────────────────────────
    -- E(k+1) = ¬(Δ_fiber ⊆ fiberwiseDisagreementSet(midIdx_i_succ, ϑ-(k+1),
    --            fold_{k+1}(f, snoc r_prefix r_new), fold_{k+1}(f̄, snoc r_prefix r_new)))
    --
    -- Strategy: Union Bound + single-step Schwartz-Zippel (degree ≤ 1 in r_new).
    --
    -- (3a) E(k+1) = ∃ y ∈ Δ_fiber, y ∉ disagreement set at step k+1.
    -- (3b) By union bound: Pr[∃ y dropped] ≤ ∑_{y ∈ Δ_fiber} Pr[y dropped].
    -- (3c) Per-point bound: Pr[y dropped] ≤ 1/|L|.
    --      fold_{k+1} = fold(fold_k, r_new) by iterated_fold_last.
    --      The fold difference at any fiber point w is a + (b-a)·r_new (degree ≤ 1).
    --      By non-degeneracy (butterfly matrix invertible), the polynomial is non-zero
    --      for any y with disagreeing fiber values. By Schwartz-Zippel, ≤ 1/|L|.
    -- (3d) Sum: |Δ_fiber| · (1/|L|) ≤ |S^{destIdx}| / |L|.
    let L_card := Fintype.card L
    -- Convert probability to cardinality ratio
    rw [prob_uniform_eq_card_filter_div_card]
    -- ── 3d: Per-point Schwartz-Zippel + union bound ──
    -- Per-point Schwartz-Zippel: |{r_new : y dropped}| ≤ 1 for each y,
    -- because fold difference is degree-1 in r_new with at most 1 root.
    have h_per_point_card : ∀ y ∈ Δ_fiber, -- y must be in Δ_fiber to ensure non-trivial fiber disagreement
      (Finset.filter (fun r_new =>
        y ∉ fiberwiseDisagreementSet 𝔽q β
            midIdx_i_succ (ϑ - (k + 1)) (by omega) h_destIdx_le
            (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := block_start_idx) (steps := k + 1)
              (h_destIdx := h_midIdx_i_succ) (h_destIdx_le := by omega)
              (f := f_i) (r_challenges := Fin.snoc r_prefix r_new))
            (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := block_start_idx) (steps := k + 1)
              (h_destIdx := h_midIdx_i_succ) (h_destIdx_le := by omega)
              (f := f_bar_i) (r_challenges := Fin.snoc r_prefix r_new)))
        Finset.univ).card ≤ 1 := by
      intro y hy_in_Δ
      -- ════════════════════════════════════════════════════════
      -- A. Decompose iterated_fold(k+1, Fin.snoc r_prefix r_new)
      --    = fold(fold_k, r_new)   via iterated_fold_last
      -- ════════════════════════════════════════════════════════
      -- A1. iterated_fold(k+1, snoc r_prefix r_new) pointwise equals
      --     fold(iterated_fold(k, Fin.init (snoc r_prefix r_new)), snoc r_prefix r_new (Fin.last k))
      have h_decomp_f : ∀ r_new : L,
          iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := block_start_idx) (steps := k + 1)
            (h_destIdx := h_midIdx_i_succ) (h_destIdx_le := by omega)
            (f := f_i) (r_challenges := Fin.snoc r_prefix r_new)
          = fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx_i)
              (destIdx := midIdx_i_succ) (h_destIdx := by omega) (h_destIdx_le := by omega)
              (f := fold_k_f) (r_chal := r_new) := by
        intro r_new
        have := iterated_fold_last 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := block_start_idx) (steps := k) (midIdx := midIdx_i) (destIdx := midIdx_i_succ)
          (h_midIdx := h_midIdx_i) (h_destIdx := h_midIdx_i_succ) (h_destIdx_le := by omega)
          (f := f_i) (r_challenges := Fin.snoc r_prefix r_new)
        simp only [Fin.init_snoc, Fin.snoc_last] at this
        exact this
      have h_decomp_f_bar : ∀ r_new : L,
          iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := block_start_idx) (steps := k + 1)
            (h_destIdx := h_midIdx_i_succ) (h_destIdx_le := by omega)
            (f := f_bar_i) (r_challenges := Fin.snoc r_prefix r_new)
          = fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := midIdx_i)
              (destIdx := midIdx_i_succ) (h_destIdx := by omega) (h_destIdx_le := by omega)
              (f := fold_k_f_bar) (r_chal := r_new) := by
        intro r_new
        have := iterated_fold_last 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := block_start_idx) (steps := k) (midIdx := midIdx_i) (destIdx := midIdx_i_succ)
          (h_midIdx := h_midIdx_i) (h_destIdx := h_midIdx_i_succ) (h_destIdx_le := by omega)
          (f := f_bar_i) (r_challenges := Fin.snoc r_prefix r_new)
        simp only [Fin.init_snoc, Fin.snoc_last] at this
        exact this
      -- ════════════════════════════════════════════════════════
      -- B. Identify a witness fiber point w ∈ S^{i+k+1} where
      --    the fold_k values disagree in the fiber of y
      -- ════════════════════════════════════════════════════════
      -- B1. y ∈ Δ_fiber means ∃ x in fiber of y at level block_start_idx
      --     where f_i(x) ≠ f̄_i(x).  We need to lift this to level i+k+1.
      -- B2. Construct w ∈ S^{i+k+1} such that:
      --     (a) w is in the fiber of y (from midIdx_i_succ to destIdx), and
      --     (b) in the fiber of w at level i+k, fold_k values disagree.
      have h_exists_disagreeing_w :
          ∃ w : sDomain 𝔽q β h_ℓ_add_R_rate midIdx_i_succ,
            (iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
              (i := midIdx_i_succ) (k := ϑ - (k + 1))
              (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le) w = y) ∧
            (let fiberMap := qMap_total_fiber 𝔽q β (i := midIdx_i) (steps := 1)
              (h_destIdx := by omega) (h_destIdx_le := by omega) (y := w)
            let x₀ := fiberMap 0
            let x₁ := fiberMap 1
            (fold_k_f x₀ ≠ fold_k_f_bar x₀ ∨ fold_k_f x₁ ≠ fold_k_f_bar x₁)) := by
        -- From h_not_Ek and hy_in_Δ, extract z in the fiber at level midIdx_i
        have hy_in_disagr := h_not_Ek hy_in_Δ
        simp only [fiberwiseDisagreementSet, Finset.mem_filter, Finset.mem_univ,
          true_and] at hy_in_disagr
        obtain ⟨z, hz_quotient, hz_ne⟩ := hy_in_disagr
        -- Set w := iteratedQuotientMap(z, midIdx_i → midIdx_i_succ)
        let w : sDomain 𝔽q β h_ℓ_add_R_rate midIdx_i_succ :=
          iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
            (i := midIdx_i) (k := 1) (h_destIdx := by omega)
            (h_destIdx_le := by omega) z
        refine ⟨w, ?_, ?_⟩
        · -- iteratedQuotientMap(w, midIdx_i_succ → destIdx) = y
          have h_factor := iteratedQuotientMap_succ_comp 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := midIdx_i) (midIdx := midIdx_i_succ) (destIdx := destIdx)
            (steps := ϑ - k - 1) (h_midIdx := by omega)
            (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le) z
          rw [←hz_quotient]
          have h_factor_congr := iteratedQuotientMap_congr_k 𝔽q β
            (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := midIdx_i) (k₁ := (ϑ - k - 1) + 1) (k₂ := ϑ - k)
            (hk := by omega) (h_destIdx₁ := by omega) (h_destIdx₂ := by omega)
            (h_destIdx_le := h_destIdx_le) z
          rw [← h_factor_congr, h_factor]
        · -- z is one of x₀ or x₁ in the fiber of w, hence fold_k disagreement
          intro fiberMap x₀ x₁
          have h_midIdx_i_succ_le : midIdx_i_succ.val ≤ ℓ := by omega
          have hw_eq : w = iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
              (i := midIdx_i) (k := 1) (h_destIdx := by omega)
              (h_destIdx_le := h_midIdx_i_succ_le) z := rfl
          have hz_fiber := (is_fiber_iff_generates_quotient_point 𝔽q β
            (i := midIdx_i) (steps := 1) (h_destIdx := by omega)
            (h_destIdx_le := h_midIdx_i_succ_le)
            z w).mp hw_eq
          set idx := pointToIterateQuotientIndex 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
            (i := midIdx_i) (steps := 1) (h_destIdx := by omega)
            (h_destIdx_le := h_midIdx_i_succ_le) z with h_idx_def
          have hz_eq : fiberMap idx = z := hz_fiber
          by_cases h0 : idx = 0
          · left; rw [h0] at hz_eq
            change fold_k_f (fiberMap 0) ≠ fold_k_f_bar (fiberMap 0)
            rw [hz_eq]; exact hz_ne
          · right; have h1 : idx = 1 := Fin.eq_one_of_ne_zero idx h0
            rw [h1] at hz_eq
            change fold_k_f (fiberMap 1) ≠ fold_k_f_bar (fiberMap 1)
            rw [hz_eq]; exact hz_ne
      obtain ⟨w, hw_in_fiber, hw_disagree⟩ := h_exists_disagreeing_w
      -- ════════════════════════════════════════════════════════
      -- C. The fold difference at w is a degree-≤1 polynomial in r_new.
      --    fold(fold_k_f, r)(w) - fold(fold_k_f̄, r)(w)
      --    = Δ₀ · ((1-r)·x₁ - r) + Δ₁ · (r - (1-r)·x₀)
      --    where Δ_j = fold_k_f(x_j) - fold_k_f̄(x_j).
      -- ════════════════════════════════════════════════════════
      let fiberMap_w := qMap_total_fiber 𝔽q β (i := midIdx_i) (steps := 1)
        (h_destIdx := by omega) (h_destIdx_le := by omega) (y := w)
      let x₀ := fiberMap_w 0
      let x₁ := fiberMap_w 1
      let Δ₀ := fold_k_f x₀ - fold_k_f_bar x₀
      let Δ₁ := fold_k_f x₁ - fold_k_f_bar x₁
      -- C1. The fold difference equals the affine polynomial
      have h_fold_diff : ∀ r_new : L,
          fold 𝔽q β (i := midIdx_i) (h_destIdx := by omega) (h_destIdx_le := by omega)
            (f := fold_k_f) (r_chal := r_new) w
          - fold 𝔽q β (i := midIdx_i) (h_destIdx := by omega) (h_destIdx_le := by omega)
            (f := fold_k_f_bar) (r_chal := r_new) w
          = Δ₀ * ((1 - r_new) * x₁.val - r_new)
          + Δ₁ * (r_new - (1 - r_new) * x₀.val) := by
        intro r_new
        simp only [fold, Δ₀, Δ₁, x₀, x₁, fiberMap_w]
        ring
      -- C2. (Δ₀, Δ₁) ≠ (0, 0) from hw_disagree
      have h_Δ_ne_zero : Δ₀ ≠ 0 ∨ Δ₁ ≠ 0 := by
        rcases hw_disagree with h0 | h1
        · left; exact sub_ne_zero.mpr h0
        · right; exact sub_ne_zero.mpr h1
      -- ════════════════════════════════════════════════════════
      -- D. The polynomial a + (b-a)·r has at most 1 root.
      --    Here a = Δ₀·x₁ - Δ₁·x₀ and (b-a) involves the
      --    butterfly matrix coefficients.  Since the butterfly
      --    matrix [[x₁, -x₀],[-1,1]] is invertible (det = x₁-x₀ ≠ 0)
      --    and (Δ₀,Δ₁) ≠ 0, we get (a,b) ≠ (0,0), so the
      --    polynomial is non-trivial → ≤ 1 root.
      -- ════════════════════════════════════════════════════════
      -- The polynomial P(r) = Δ₀·((1-r)·x₁-r) + Δ₁·(r-(1-r)·x₀) can be rewritten as:
      --   P(r) = (Δ₀·x₁ - Δ₁·x₀) + r·(Δ₁·(1+x₀) - Δ₀·(1+x₁))
      -- This corresponds to [1-r, r] · M · [Δ₀, Δ₁]ᵀ where M = [[x₁,-x₀],[-1,1]].
      -- det(M) = x₁ - x₀ ≠ 0 (distinct NTT points in the fiber).
      -- Since (Δ₀,Δ₁) ≠ 0 and M invertible, M·[Δ₀,Δ₁]ᵀ ≠ 0.
      -- P has at most 1 root → P(r₁) = P(r₂) = 0 ⟹ r₁ = r₂.
      have h_x₀_ne_x₁ : (x₀ : L) ≠ (x₁ : L) := by
        have h_inj := qMap_total_fiber_injective 𝔽q β midIdx_i 1
          (by omega) (by omega : midIdx_i_succ.val ≤ ℓ) w
        have h_ne : (0 : Fin (2 ^ 1)) ≠ 1 := by decide
        exact Subtype.val_injective.ne (h_inj.ne h_ne)
      -- In char 2: sub = add, neg = id.  So P(r) simplifies to:
      -- P(r) = Δ₀·((1+r)·x₁ + r) + Δ₁·(r + (1+r)·x₀)
      --       = (Δ₀·x₁ + Δ₁·x₀) + r·(Δ₀·(x₁+1) + Δ₁·(x₀+1))
      -- Let a := Δ₀·x₁ + Δ₁·x₀, c := Δ₀·(x₁+1) + Δ₁·(x₀+1).
      -- Then P(r) = a + c·r.  If c ≠ 0, exactly 1 root.  If c = 0, then a ≠ 0
      -- (by butterfly invertibility + (Δ₀,Δ₁) ≠ 0), so no roots.
      -- Either way, P(r₁)=P(r₂)=0 ⟹ r₁=r₂.
      -- Char-2 rewrite of the polynomial
      have h_poly_char2 : ∀ r_val : L,
          Δ₀ * ((1 - r_val) * x₁.val - r_val) + Δ₁ * (r_val - (1 - r_val) * x₀.val) =
          (Δ₀ * x₁.val + Δ₁ * x₀.val) +
          r_val * (Δ₀ * (x₁.val + 1) + Δ₁ * (x₀.val + 1)) := by
        intro r_val
        simp only [CharTwo.sub_eq_add]
        ring
      -- Helper: in char 2, u + v = 0 ↔ u = v
      have char2_add_zero : ∀ (u v : L), u + v = 0 ↔ u = v :=
        sum_zero_iff_eq_of_self_sum_zero (F := L) (h_self_sum_eq_zero := by
          intro x; exact CharTwo.add_self_eq_zero x)
      have h_at_most_one_root : ∀ r₁ r₂ : L,
          (Δ₀ * ((1 - r₁) * x₁.val - r₁) + Δ₁ * (r₁ - (1 - r₁) * x₀.val) = 0) →
          (Δ₀ * ((1 - r₂) * x₁.val - r₂) + Δ₁ * (r₂ - (1 - r₂) * x₀.val) = 0) →
          r₁ = r₂ := by
        intro r₁ r₂ h1 h2
        rw [h_poly_char2] at h1 h2
        -- h1 : A + r₁*C = 0, h2 : A + r₂*C = 0  where A,C are the constant/linear coeffs
        -- From h1,h2: A = r₁*C and A = r₂*C, so r₁*C = r₂*C, so (r₁+r₂)*C = 0
        have h_sub : (r₁ + r₂) * (Δ₀ * (↑x₁ + 1) + Δ₁ * (↑x₀ + 1)) = 0 := by
          have h1' := (char2_add_zero _ _).mp h1
          have h2' := (char2_add_zero _ _).mp h2
          rw [add_mul, ← h1', ← h2', CharTwo.add_self_eq_zero]
        rcases mul_eq_zero.mp h_sub with h_diff | h_coeff
        · exact (char2_add_zero r₁ r₂).mp h_diff
        · exfalso
          have h_a_eq_0 : Δ₀ * ↑x₁ + Δ₁ * ↑x₀ = 0 := by
            rw [h_coeff, mul_zero, add_zero] at h1; exact h1
          have h_Δ_eq : Δ₀ = Δ₁ := by
            have hc : Δ₀ * (↑x₁ + 1) + Δ₁ * (↑x₀ + 1) =
              (Δ₀ * ↑x₁ + Δ₁ * ↑x₀) + (Δ₀ + Δ₁) := by ring
            rw [h_a_eq_0, zero_add] at hc
            rw [hc] at h_coeff
            exact (char2_add_zero Δ₀ Δ₁).mp h_coeff
          have h_Δ₀_mul : Δ₀ * (↑x₁ + ↑x₀) = 0 := by
            have : Δ₀ * ↑x₁ + Δ₀ * ↑x₀ = 0 := h_Δ_eq ▸ h_a_eq_0
            rwa [← mul_add] at this
          have h_sum_ne : (↑x₁ : L) + ↑x₀ ≠ 0 := by
            rwa [Ne, ← CharTwo.sub_eq_add, sub_eq_zero, eq_comm]
          have h_Δ₀_zero := (mul_eq_zero.mp h_Δ₀_mul).resolve_right h_sum_ne
          exact h_Δ_ne_zero.elim (absurd h_Δ₀_zero) (absurd (h_Δ_eq ▸ h_Δ₀_zero))
      -- ════════════════════════════════════════════════════════
      -- E. Conclude |{r_new : y dropped}| ≤ 1
      -- ════════════════════════════════════════════════════════
      -- E1. If y is NOT in the (k+1)-step disagreement set, then in particular
      --     fold_{k+1}(f) and fold_{k+1}(f̄) agree at w, hence the fold
      --     difference polynomial evaluated at r_new is 0.
      -- E2. By h_at_most_one_root, this can happen for ≤ 1 value of r_new.
      rw [Finset.card_le_one]
      intro a ha b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      -- ha : y ∉ fiberwiseDisagreementSet(…, fold_{k+1}(f, snoc … a), …)
      -- hb : y ∉ fiberwiseDisagreementSet(…, fold_{k+1}(f, snoc … b), …)
      -- Need: a = b
      -- Extract that fold difference = 0 at w for both a and b,
      -- then apply h_at_most_one_root.
      -- E3. Connect "y ∉ fiberwiseDisagreementSet(k+1)" to fold agreement at w
      -- Helper: extract pointwise agreement from non-membership in disagreement set
      have h_agree_at_w : ∀ (r_val : L),
          y ∉ fiberwiseDisagreementSet 𝔽q β
            midIdx_i_succ (ϑ - (k + 1)) (by omega) h_destIdx_le
            (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := block_start_idx) (steps := k + 1)
              (h_destIdx := h_midIdx_i_succ) (h_destIdx_le := by omega)
              (f := f_i) (r_challenges := Fin.snoc r_prefix r_val))
            (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := block_start_idx) (steps := k + 1)
              (h_destIdx := h_midIdx_i_succ) (h_destIdx_le := by omega)
              (f := f_bar_i) (r_challenges := Fin.snoc r_prefix r_val)) →
          fold 𝔽q β (i := midIdx_i) (h_destIdx := by omega) (h_destIdx_le := by omega)
            (f := fold_k_f) (r_chal := r_val) w
          = fold 𝔽q β (i := midIdx_i) (h_destIdx := by omega) (h_destIdx_le := by omega)
            (f := fold_k_f_bar) (r_chal := r_val) w := by
        intro r_val h_not_in
        -- y ∉ fiberwiseDisagreementSet means: no z in fiber of y has disagreeing values.
        -- In particular, w is in y's fiber (by hw_in_fiber), so values agree at w.
        -- Rewrite iterated_fold(k+1) as fold(fold_k, r_val)
        rw [h_decomp_f r_val, h_decomp_f_bar r_val] at h_not_in
        -- h_not_in : y ∉ fiberwiseDisagreementSet(midIdx_i_succ, ϑ-(k+1), ..., fold(fold_k_f, r_val), fold(fold_k_f̄, r_val))
        -- Unfold fiberwiseDisagreementSet
        simp only [fiberwiseDisagreementSet, Finset.mem_filter, Finset.mem_univ,
          true_and, not_exists, not_and] at h_not_in
        -- h_not_in : ∀ z, iteratedQuotientMap z = y → fold(fold_k_f, r_val)(z) = fold(fold_k_f̄, r_val)(z)
        exact not_not.mp (h_not_in w hw_in_fiber)
      -- E4. From fold agreement → polynomial = 0 → apply injectivity
      have h_agree_a := h_agree_at_w a ha
      have h_agree_b := h_agree_at_w b hb
      have h_poly_zero_a : Δ₀ * ((1 - a) * x₁.val - a) + Δ₁ * (a - (1 - a) * x₀.val) = 0 := by
        rw [← h_fold_diff a, sub_eq_zero]; exact h_agree_a
      have h_poly_zero_b : Δ₀ * ((1 - b) * x₁.val - b) + Δ₁ * (b - (1 - b) * x₀.val) = 0 := by
        rw [← h_fold_diff b, sub_eq_zero]; exact h_agree_b
      exact h_at_most_one_root a b h_poly_zero_a h_poly_zero_b
    -- The bad set {r_new : ¬(Δ ⊆ ...)} ⊆ ⋃_{y ∈ Δ_fiber} {r_new : y dropped}
    have h_bad_subset : (Finset.filter (fun r_new =>
        ¬(↑Δ_fiber ⊆ ↑(fiberwiseDisagreementSet 𝔽q β
            midIdx_i_succ (ϑ - (k + 1)) (by omega) h_destIdx_le
            (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := block_start_idx) (steps := k + 1)
              (h_destIdx := h_midIdx_i_succ) (h_destIdx_le := by omega)
              (f := f_i) (r_challenges := Fin.snoc r_prefix r_new))
            (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := block_start_idx) (steps := k + 1)
              (h_destIdx := h_midIdx_i_succ) (h_destIdx_le := by omega)
              (f := f_bar_i) (r_challenges := Fin.snoc r_prefix r_new)))))
        Finset.univ) ⊆
      Δ_fiber.biUnion (fun y =>
        Finset.filter (fun r_new =>
          y ∉ fiberwiseDisagreementSet 𝔽q β
            midIdx_i_succ (ϑ - (k + 1)) (by omega) h_destIdx_le
            (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := block_start_idx) (steps := k + 1)
              (h_destIdx := h_midIdx_i_succ) (h_destIdx_le := by omega)
              (f := f_i) (r_challenges := Fin.snoc r_prefix r_new))
            (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
              (i := block_start_idx) (steps := k + 1)
              (h_destIdx := h_midIdx_i_succ) (h_destIdx_le := by omega)
              (f := f_bar_i) (r_challenges := Fin.snoc r_prefix r_new)))
        Finset.univ) := by
      intro r_new hr
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
      rw [Finset.not_subset] at hr
      rcases hr with ⟨y, hy_mem, hy_not_in⟩
      simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨y, hy_mem, hy_not_in⟩
    -- |bad set| ≤ |⋃ per-y sets| ≤ ∑_{y ∈ Δ_fiber} |per-y set| ≤ |Δ_fiber| ≤ |S^{destIdx}|
    calc ((Finset.filter _ Finset.univ).card : ENNReal) / (L_card : ENNReal)
        _ ≤ (Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) : ENNReal) / L_card := by
          gcongr
          calc (Finset.filter _ Finset.univ).card
              _ ≤ (Δ_fiber.biUnion _).card := Finset.card_le_card h_bad_subset
              _ ≤ ∑ y ∈ Δ_fiber, (Finset.filter _ Finset.univ).card := Finset.card_biUnion_le
              _ ≤ ∑ _ ∈ Δ_fiber, 1 := Finset.sum_le_sum (fun y hy => h_per_point_card y hy)
              _ = Δ_fiber.card := by simp
              _ ≤ Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) := Finset.card_le_univ _

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
  subst hU_even hU_odd
  intro h_close
  apply h_far
  unfold jointProximityNat₂ jointProximityNat at h_close
  simp only at h_close
  rw [Code.closeToCode_iff_closeToCodeword_of_minDist] at h_close
  rcases h_close with ⟨vSplit, hvSplit_mem, hvSplit_dist_le_e⟩
  rw [closeToWord_iff_exists_possibleDisagreeCols] at hvSplit_dist_le_e
  rcases hvSplit_dist_le_e with ⟨D, hD_card_le_e, h_agree_outside_D⟩
  unfold jointProximityNat
  rw [Code.closeToCode_iff_closeToCodeword_of_minDist
    (u := ⋈|U) (e := e) (C := interleavedCodeSet (κ := Fin (2 ^ (s + 1))) C)]
  simp_rw [closeToWord_iff_exists_possibleDisagreeCols]
  let VSplit_rowwise := Matrix.transpose vSplit
  let VSplit_even_rowwise := Matrix.transpose (VSplit_rowwise 0)
  let VSplit_odd_rowwise := Matrix.transpose (VSplit_rowwise 1)
  let v_rowwise_finmap : WordStack L (Fin (2 ^ (s + 1))) ι := fun rowIdx =>
    if h_even : rowIdx.val % 2 = 0 then
      VSplit_even_rowwise ⟨rowIdx.val / 2, by omega⟩
    else
      VSplit_odd_rowwise ⟨rowIdx.val / 2, by omega⟩
  let v_IC := ⋈|v_rowwise_finmap
  use v_IC
  constructor
  · intro rowIdx
    have h_vSplit_rows_mem : ∀ (i : Fin 2) (j : Fin (2 ^ s)), (fun col ↦ vSplit col i j) ∈ C := by
      intro i j
      exact hvSplit_mem i j
    dsimp only [v_IC]
    by_cases h_even : rowIdx.val % 2 = 0
    · let j : Fin (2 ^ s) := ⟨rowIdx.val / 2, by omega⟩
      have hRes := h_vSplit_rows_mem 0 j
      change (fun col => v_rowwise_finmap rowIdx col) ∈ C
      have h_fun : (fun col => v_rowwise_finmap rowIdx col) = fun col => vSplit col 0 j := by
        funext col
        dsimp [v_rowwise_finmap, VSplit_even_rowwise, VSplit_rowwise, j]
        rw [dif_pos h_even]
        rfl
      rw [h_fun]
      exact hRes
    · let j : Fin (2 ^ s) := ⟨rowIdx.val / 2, by omega⟩
      have hRes := h_vSplit_rows_mem 1 j
      change (fun col => v_rowwise_finmap rowIdx col) ∈ C
      have h_fun : (fun col => v_rowwise_finmap rowIdx col) = fun col => vSplit col 1 j := by
        funext col
        dsimp [v_rowwise_finmap, VSplit_odd_rowwise, VSplit_rowwise, j]
        rw [dif_neg h_even]
        rfl
      rw [h_fun]
      exact hRes
  · use D
    constructor
    · exact hD_card_le_e
    · intro colIdx h_colIdx_notin_D
      funext rowIdx
      dsimp only [v_IC]
      have hRes0 :
          interleaveWordStack
              ((splitEvenOddRowWiseInterleavedWords (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := s) U).1)
              colIdx
            = vSplit colIdx 0 := by
        exact congrFun (h_agree_outside_D colIdx h_colIdx_notin_D) 0
      have hRes1 :
          interleaveWordStack
              ((splitEvenOddRowWiseInterleavedWords (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (ϑ := s) U).2)
              colIdx
            = vSplit colIdx 1 := by
        exact congrFun (h_agree_outside_D colIdx h_colIdx_notin_D) 1
      by_cases h_even : rowIdx.val % 2 = 0
      · have h_row_val : rowIdx.val = 2 * (rowIdx.val / 2) := by
          have h_divmod := Nat.mod_add_div rowIdx.val 2
          omega
        have h_row_eq :
            (⟨2 * (rowIdx.val / 2), by omega⟩ : Fin (2 ^ (s + 1))) = rowIdx := by
          apply Fin.eq_of_val_eq
          exact h_row_val.symm
        have hRes₀ := congrFun hRes0 ⟨rowIdx.val / 2, by omega⟩
        dsimp [splitEvenOddRowWiseInterleavedWords] at hRes₀
        simp [v_rowwise_finmap, h_even, VSplit_even_rowwise, VSplit_rowwise]
        have hRes₀' := hRes₀
        simp only [h_row_eq] at hRes₀' ⊢
        exact hRes₀'
      · have h_row_val : rowIdx.val = 2 * (rowIdx.val / 2) + 1 := by
          have h_divmod := Nat.mod_add_div rowIdx.val 2
          omega
        have h_row_eq :
            (⟨2 * (rowIdx.val / 2) + 1, by omega⟩ : Fin (2 ^ (s + 1))) = rowIdx := by
          apply Fin.eq_of_val_eq
          exact h_row_val.symm
        have hRes₁ := congrFun hRes1 ⟨rowIdx.val / 2, by omega⟩
        dsimp [splitEvenOddRowWiseInterleavedWords] at hRes₁
        simp [v_rowwise_finmap, h_even, VSplit_odd_rowwise, VSplit_rowwise]
        have hRes₁' := hRes₁
        simp only [h_row_eq] at hRes₁' ⊢
        exact hRes₁'

/-- **One fold step on preTensorCombine = affine line evaluation on even/odd split.**
Given `f_i : S^i → L` and its preTensorCombine WordStack `U` of height `2^(steps+1)`,
using the **even/odd split** (LSB-first, see `splitEvenOddRowWiseInterleavedWords`):
`U_even[j] = U[2j]`, `U_odd[j] = U[2j+1]`. Folding dimension `i` first gives:
```
⋈|preTensorCombine(i+1, steps, destIdx, fold(f_i, r_new))
  = affineLineEvaluation(⋈|U_even, ⋈|U_odd, r_new)
``` -/
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
  intro h_midIdx_lt_ℓ U U_even U_odd fold_1_f midIdx_fin_ℓ V
  have h_fold_eq_U : ∀ r_chal : Fin (steps + 1) → L,
      (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
        (steps := steps + 1) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        f_i r_chal) = multilinearCombine U r_chal := by
    intro r_chal; ext y'
    rw [iterated_fold_eq_matrix_form]
    unfold localized_fold_matrix_form single_point_localized_fold_matrix_form multilinearCombine
    simp only [dotProduct, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => rfl
  have h_fold_eq_V : ∀ r_chal : Fin steps → L,
      (iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) midIdx
        (steps := steps) (h_destIdx := by omega) (h_destIdx_le := h_destIdx_le)
        fold_1_f r_chal) = multilinearCombine V r_chal := by
    intro r_chal; ext y'
    rw [iterated_fold_eq_matrix_form]
    unfold localized_fold_matrix_form single_point_localized_fold_matrix_form multilinearCombine
    simp only [dotProduct, smul_eq_mul]
    exact Finset.sum_congr rfl fun _ _ => rfl
  have h_indicator : ∀ (W : WordStack L (Fin (2 ^ steps))
      (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)) (j' : Fin (2 ^ steps))
      (y' : sDomain 𝔽q β h_ℓ_add_R_rate destIdx),
      multilinearCombine (F := L) W (bitsOfIndex j') y' = W j' y' := by
    intro W' j' y'
    simp only [multilinearCombine, smul_eq_mul]
    rw [show (∑ rowIdx, multilinearWeight (bitsOfIndex j') rowIdx * W' rowIdx y') =
      ∑ rowIdx, (if rowIdx = j' then 1 else 0) * W' rowIdx y' from by
        apply Finset.sum_congr rfl; intro k _
        congr 1
        have := congr_fun
          (challengeTensorExpansion_bitsOfIndex_is_eq_indicator (L := L) j') k
        simp only [challengeTensorExpansion, multilinearWeight] at this
        exact this]
    simp only [boole_mul, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  have h_recursive : ∀ r_chal : Fin (steps + 1) → L,
      multilinearCombine U r_chal =
      multilinearCombine (affineLineEvaluation (F := L) U_even U_odd (r_chal 0))
        (fun k => r_chal (Fin.succ k)) := by
    intro r_chal
    dsimp [U_even, U_odd]
    exact multilinearCombine_recursive_form_first (u := U) (r_challenges := r_chal)
  ext y j
  change V j y = affineLineEvaluation U_even U_odd r_new j y
  rw [←h_indicator V j y]
  conv_lhs => rw [←h_fold_eq_V (bitsOfIndex j)]
  have h_first :
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (steps := steps + 1) (h_destIdx := h_destIdx)
        (h_destIdx_le := h_destIdx_le) (f := f_i)
        (r_challenges := Fin.cons r_new (bitsOfIndex j)) =
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := midIdx) (steps := steps) (h_destIdx := by omega)
        (h_destIdx_le := h_destIdx_le) (f := fold_1_f)
        (r_challenges := bitsOfIndex j) := by
    change
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := ⟨i, by omega⟩) (steps := steps + 1) (h_destIdx := h_destIdx)
        (h_destIdx_le := h_destIdx_le) (f := f_i)
        (r_challenges := Fin.cons r_new (bitsOfIndex j)) =
      iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := midIdx) (steps := steps) (h_destIdx := by omega)
        (h_destIdx_le := h_destIdx_le)
        (f := fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (i := ⟨i, by omega⟩) (destIdx := midIdx) (h_destIdx := h_midIdx)
          (h_destIdx_le := by omega) f_i r_new)
        (r_challenges := bitsOfIndex j)
    have h_first_raw :=
      iterated_fold_first 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        ⟨i, by omega⟩ (steps := steps) h_midIdx h_destIdx h_destIdx_le f_i
        (Fin.cons r_new (bitsOfIndex j))
    exact h_first_raw
  rw [←h_first]
  rw [h_fold_eq_U (Fin.cons r_new (bitsOfIndex j))]
  rw [h_recursive (Fin.cons r_new (bitsOfIndex j))]
  simp only [Fin.cons_zero, Fin.cons_succ]
  rw [h_indicator (affineLineEvaluation (F := L) U_even U_odd r_new) j y]

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
  intro U
  ext y
  rw [fold_eval_single_matrix_mul_form 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := ⟨i, by omega⟩) (destIdx := destIdx) (h_destIdx := by omega)
    (h_destIdx_le := h_destIdx_le) (f := f_i) (r_challenge := r_new)]
  unfold fold_single_matrix_mul_form multilinearCombine
  dsimp [U]
  have h_blk :
      blockDiagMatrix (L := L) (r := r) (ℓ := ℓ) (𝓡 := 𝓡) (n := 0)
        (Mz₀ := (1 : Matrix (Fin (2 ^ 0)) (Fin (2 ^ 0)) L))
        (Mz₁ := (1 : Matrix (Fin (2 ^ 0)) (Fin (2 ^ 0)) L))
      = (1 : Matrix (Fin (2 ^ 1)) (Fin (2 ^ 1)) L) := by
    ext a b <;> fin_cases a <;> fin_cases b <;>
      simp [blockDiagMatrix, reindexSquareMatrix, Matrix.from4Blocks]
  simp [preTensorCombine_WordStack, foldMatrix, challengeTensorExpansion, h_blk]
  have h_w0 :
      vecHead (multilinearWeight (F := L) (r := fun _ : Fin 1 => r_new)) =
        multilinearWeight (F := L) (r := fun _ : Fin 1 => r_new) 0 := by
    rfl
  have h_w1 :
      vecHead (vecTail (multilinearWeight (F := L) (r := fun _ : Fin 1 => r_new))) =
        multilinearWeight (F := L) (r := fun _ : Fin 1 => r_new) 1 := by
    rfl
  rw [h_w0, h_w1]

/-- **Connecting fiberwiseClose of a folded function to affine line evaluation proximity.**
Given `f_i : S^i → L` with preTensorCombine `U := preTensorCombine(i, s+1, destIdx, f_i)` of
height `2^{s+1}`, and `r_new : L`, if
`fiberwiseClose(iterated_fold(i, s+1, destIdx, f_i, snoc r r_new), ...)` holds, then
`Δ₀(affineLineEval(⋈|U_even, ⋈|U_odd, r_new), C^⋈(2^s)) ≤ UDR(C)`.

**Proof sketch:**
1. By `iterated_fold_last`: the folded function is `fold(f_i, r_new)`.
2. `fiberwiseClose(fold(f_i,r_new), s) → jointProximityNat(V)` where
   `V = preTensorCombine(midIdx, s, destIdx, fold(f_i,r_new))`
   (by `preTensorCombine_jointProximityNat_of_fiberwiseClose`).
3. `⋈|V = affineLineEval(⋈|U_even, ⋈|U_odd, r_new)`
   (by `fold_preTensorCombine_eq_affineLineEvaluation_split`).
4. Combine 2 and 3 to get the distance bound. -/
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
    let C_dest : Set (sDomain 𝔽q β h_ℓ_add_R_rate destIdx → L) :=
      BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
    Δ₀(affineLineEvaluation (F := L)
      (interleaveWordStack U_even) (interleaveWordStack U_odd) r_new,
      (C_dest ^⋈ (Fin (2^s)))) ≤
    Code.uniqueDecodingRadius (C := C_dest) := by
  classical
  intro i_ℓ U U_even U_odd C_dest
  have h_midIdx_le_ℓ : midIdx.val ≤ ℓ := by omega
  let fold_1_f := fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    i (destIdx := midIdx) (h_destIdx := h_midIdx)
    (h_destIdx_le := by omega) f_i r_new
  by_cases hs : s = 0
  · subst hs
    have h_midIdx_eq_destIdx : midIdx = destIdx := Fin.eq_of_val_eq (by omega)
    have h_udr_close : UDRClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        midIdx (h_i := h_midIdx_le_ℓ) fold_1_f := by
      rw [←fiberwiseClose_steps_zero_iff_UDRClose]
      exact h_fw_close
    rw [UDRClose_iff_within_UDR_radius] at h_udr_close
    subst h_midIdx_eq_destIdx
    change Δ₀(affineLineEvaluation (F := L)
      (interleaveWordStack U_even) (interleaveWordStack U_odd) r_new,
      interleavedCodeSet (κ := Fin (2 ^ 0)) C_dest) ≤
      Code.uniqueDecodingRadius (C := C_dest)
    rw [distFromCode_fin1_eq]
    suffices h_eq : (fun y => affineLineEvaluation
        (interleaveWordStack U_even) (interleaveWordStack U_odd) r_new y
        (0 : Fin (2 ^ 0))) =
        fold_1_f by
      rw [h_eq]; exact h_udr_close
    have h_rhs : fold_1_f = multilinearCombine (F := L) U (fun (_ : Fin 1) => r_new) := by
      have h_rhs := fold_eq_multilinearCombine_preTensorCombine_step1 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i_ℓ)
        (destIdx := midIdx) (h_destIdx := by simp [i_ℓ]; omega)
        (h_destIdx_le := h_midIdx_le_ℓ) (f_i := f_i) (r_new := r_new)
      simp only [fold_1_f, i_ℓ] at h_rhs ⊢
      exact h_rhs
    have h_affine_eq_mc :
        (fun y => affineLineEvaluation
          (interleaveWordStack U_even) (interleaveWordStack U_odd) r_new y
          (0 : Fin (2 ^ 0))) =
        multilinearCombine (F := L) U (fun (_ : Fin 1) => r_new) := by
      ext y
      simp [U_even, U_odd, splitEvenOddRowWiseInterleavedWords, affineLineEvaluation,
        interleaveWordStack, multilinearCombine, multilinearWeight, smul_eq_mul]
    have h_fn_eq : (fun y => affineLineEvaluation
        (interleaveWordStack U_even) (interleaveWordStack U_odd) r_new y
        (0 : Fin (2 ^ 0))) = fold_1_f := by
      rw [h_affine_eq_mc, h_rhs]
    rw [h_fn_eq]
  · have h_midIdx_lt_ℓ : midIdx.val < ℓ := by omega
    let midIdx_ℓ : Fin ℓ := ⟨midIdx.val, h_midIdx_lt_ℓ⟩
    haveI : NeZero s := ⟨hs⟩
    have h_joint := preTensorCombine_jointProximityNat_of_fiberwiseClose 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := midIdx_ℓ) (steps := s)
      (h_destIdx := by simp only [midIdx_ℓ]; omega)
      (h_destIdx_le := h_destIdx_le)
      (f_i := fold_1_f)
      (h_close := h_fw_close)
    have h_eq := fold_preTensorCombine_eq_affineLineEvaluation_split 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i_ℓ) (steps := s)
      (midIdx := midIdx) (destIdx := destIdx)
      (h_midIdx := by simp only [i_ℓ]; omega)
      (h_destIdx := by simp only [i_ℓ]; omega)
      (h_destIdx_le := h_destIdx_le)
      (f_i := f_i) (r_new := r_new)
    have h_eq' :
        interleaveWordStack
            (preTensorCombine_WordStack 𝔽q β
              (i := ⟨midIdx.val, h_midIdx_lt_ℓ⟩) (steps := s)
              (destIdx := destIdx)
              (h_destIdx := by simp [h_midIdx_lt_ℓ]; omega)
              (h_destIdx_le := h_destIdx_le) fold_1_f) =
          affineLineEvaluation (F := L)
            (interleaveWordStack U_even) (interleaveWordStack U_odd) r_new := by
      have h_eq' := h_eq
      simp only [U_even, U_odd] at h_eq' ⊢
      exact h_eq'
    unfold jointProximityNat at h_joint
    rw [← h_eq']
    exact h_joint

/--
#### **Case 2: FiberwiseFar (Incremental)**

**Proof outline (see infrastructure lemmas above for details):**
1. Build `U := preTensorCombine(midIdx_i, ϑ-k, destIdx, fold_k_f)` of height `2^{ϑ-k}`.
2. By Lemma 4.21: `¬fiberwiseClose(fold_k_f) → ¬jointProximityNat(U, e)`.
3. Split `U` into even/odd stacks `(U_even, U_odd) = splitEvenOdd(U)`,
   each of height `2^{ϑ-k-1}`.
   By `not_jointProximityNat_of_not_jointProximityNat_evenOdd_split`:
   `¬jointProximityNat₂(U_even, U_odd, e)` for `C_dest^{2^{ϑ-k-1}}`.
4. Fold step gives affine combination:
   `preTensorCombine(fold_{k+1}_f) = affineLineEval(U_even, U_odd, r_new)`
   (by `fold_preTensorCombine_eq_affineLineEvaluation_split`).
5. `fiberwiseClose(fold_{k+1}_f) → jointProximityNat(preTensorCombine(fold_{k+1}_f), e)`
   (by `preTensorCombine_jointProximityNat_of_fiberwiseClose`).
6. Contrapositive of DG25 affine proximity gap
   (by `affineProximityGap_RS_interleaved_contrapositive`):
   `Pr_r[close] ≤ |S|/|L|`.
-/
lemma prop_4_20_2_case_2_fiberwise_far_incremental
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
  classical
  dsimp only [incrementalFoldingBadEvent]
  simp only [h_block_far, not_false_eq_true, ↓reduceDIte, dite_false]
  let fold_k_f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := block_start_idx) (steps := k) (h_destIdx := h_midIdx_i) (h_destIdx_le := by omega)
    (f := f_block_start) (r_challenges := r_prefix)
  let Ek_close := fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := midIdx_i) (steps := ϑ - k) (h_destIdx := by omega)
    (h_destIdx_le := h_destIdx_le) (f := fold_k_f)
  by_cases h_Ek_close : Ek_close
  · apply le_trans (Pr_le_Pr_of_implies ($ᵖ L) _ _ (fun r_new h => h.1))
    have : Pr_{ let r_new ← $ᵖ L }[¬Ek_close] = 0 := by
      rw [prob_uniform_eq_card_filter_div_card]
      simp only [not_not.mpr h_Ek_close, filter_False, card_empty, CharP.cast_eq_zero,
        ENNReal.coe_zero, ENNReal.coe_natCast, ENNReal.zero_div]
    rw [this]; exact zero_le _
  · apply le_trans (Pr_le_Pr_of_implies ($ᵖ L) _ _ (fun r_new h => h.2))
    have h_midIdx_i_lt_ℓ : midIdx_i.val < ℓ := by omega
    let s := ϑ - k - 1
    have h_steps_eq : ϑ - k = s + 1 := by omega
    haveI : NeZero (s + 1) := ⟨by omega⟩
    let S_dest := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
    let C_dest : Set (S_dest → L) :=
      BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
    let e_prox := Code.uniqueDecodingRadius (C := C_dest)
    let i_ℓ : Fin ℓ := ⟨midIdx_i.val, h_midIdx_i_lt_ℓ⟩
    let U := preTensorCombine_WordStack 𝔽q β i_ℓ (s + 1)
      (destIdx := destIdx)
      (h_destIdx := by simp [i_ℓ]; omega)
      (h_destIdx_le := h_destIdx_le)
      fold_k_f
    have h_U_far : ¬jointProximityNat (C := C_dest) (u := U)
        (e := e_prox) := by
      apply lemma_4_21_interleaved_word_UDR_far 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i_ℓ) (steps := s + 1)
        (h_destIdx := by simp [i_ℓ]; omega)
        (h_destIdx_le := h_destIdx_le)
        (f_i := fold_k_f)
        (h_far := by convert h_Ek_close using 2; omega)
    let U_even := (splitEvenOddRowWiseInterleavedWords (r := r) (ℓ := ℓ) (𝓡 := 𝓡)
      (ϑ := s) U).1
    let U_odd := (splitEvenOddRowWiseInterleavedWords (r := r) (ℓ := ℓ) (𝓡 := 𝓡)
      (ϑ := s) U).2
    let u_even := interleaveWordStack U_even
    let u_odd := interleaveWordStack U_odd
    have h_pair_far : ¬ jointProximityNat₂
        (A := InterleavedSymbol L (Fin (2^s)))
        (C := (C_dest ^⋈ (Fin (2^s))))
        (u₀ := u_even) (u₁ := u_odd) (e := e_prox) :=
      not_jointProximityNat_of_not_jointProximityNat_evenOdd_split
        (s := s) (C := C_dest) (U := U) (e := e_prox)
        (U_even := U_even) (U_odd := U_odd)
        (hU_even := by rfl) (hU_odd := by rfl)
        (h_far := h_U_far)
    have h_affine_bound :
        Pr_{let r ← $ᵖ L}[
          Δ₀(affineLineEvaluation (F := L) u_even u_odd r,
            (C_dest ^⋈ (Fin (2^s)))) ≤ e_prox]
        ≤ (Fintype.card S_dest : ℝ≥0) / (Fintype.card L) :=
      affineProximityGap_RS_interleaved_contrapositive
        𝔽q β (hm := Nat.one_le_two_pow) (h_destIdx_le := h_destIdx_le)
        (e := e_prox) (he := le_refl _) (h_far := h_pair_far)
    apply le_trans _ h_affine_bound
    apply Pr_le_Pr_of_implies ($ᵖ L) _ _
    intro r_new h_fw_close
    exact fiberwiseClose_fold_implies_affineLineEval_close 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := midIdx_i) (h_i_lt_ℓ := h_midIdx_i_lt_ℓ) (s := s)
      (midIdx := midIdx_i_succ) (destIdx := destIdx)
      (h_midIdx := by omega)
      (h_destIdx := by omega)
      (h_destIdx_le := h_destIdx_le)
      (f_i := fold_k_f) (r_new := r_new)
      (h_fw_close := by
        rw [iterated_fold_last 𝔽q β
          (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          block_start_idx (steps := k)
          (h_midIdx := h_midIdx_i) (h_destIdx := h_midIdx_i_succ)
          (h_destIdx_le := by omega)
          f_block_start (Fin.snoc r_prefix r_new)] at h_fw_close
        simp only [Fin.init_snoc, Fin.snoc_last] at h_fw_close
        convert h_fw_close using 1)

lemma prop_4_20_2_incremental_bad_event_probability
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
  · exact prop_4_20_2_case_1_fiberwise_close_incremental 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (block_start_idx := block_start_idx)
      (midIdx_i := midIdx_i) (midIdx_i_succ := midIdx_i_succ) (destIdx := destIdx) (k := k) (h_k_lt := h_k_lt) (h_midIdx_i := h_midIdx_i) (h_midIdx_i_succ := h_midIdx_i_succ) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f_block_start := f_block_start)
      (r_prefix := r_prefix) (h_block_close := h_block_close)
  · exact prop_4_20_2_case_2_fiberwise_far_incremental 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (block_start_idx := block_start_idx)
      (midIdx_i := midIdx_i) (midIdx_i_succ := midIdx_i_succ) (destIdx := destIdx) (k := k) (h_k_lt := h_k_lt) (h_midIdx_i := h_midIdx_i) (h_midIdx_i_succ := h_midIdx_i_succ) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f_block_start := f_block_start)
      (r_prefix := r_prefix) (h_block_far := h_block_close)

end

end Binius.BinaryBasefold
