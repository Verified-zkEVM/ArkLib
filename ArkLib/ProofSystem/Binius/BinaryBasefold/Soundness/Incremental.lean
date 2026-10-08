/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module


public import ArkLib.Data.CodingTheory.ProximityGap.DG25.ReedSolomon
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Compliance
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Soundness.Lift

/-!
# Binary Basefold: the per-challenge bound on the incremental folding bad event

`incrementalFoldingBadEvent` (`Compliance`) is the folding bad event of a block of `ϑ` folds,
restricted to the first `k` challenges of the block. The main statement,
`prob_incrementalFoldingBadEvent_fresh_le`, bounds, for a fixed block start, a fixed oracle and a
fixed prefix of `k < ϑ` challenges, the probability over one fresh uniform challenge that the
event holds at `k + 1` but not at `k`, by `|S⁽ⁱ⁺ᶿ⁾| / |L|`. The fold step's round-by-round
knowledge soundness consumes it one challenge at a time.

## Main statements

* `prob_incrementalFoldingBadEvent_fresh_le_of_fiberwiseClose`: the case where the block's oracle
  is fiberwise close. A fold step can drop a point of the fiberwise disagreement set only at a
  root of a nonzero polynomial of degree at most one in the fresh challenge; a union bound over
  the destination domain finishes.
* `prob_incrementalFoldingBadEvent_fresh_le_of_not_fiberwiseClose`: the far case. The
  tensor-combine stack of the current fold is far from the interleaved code
  (`preTensorCombine_not_jointProximityNat_of_not_fiberwiseClose`), hence so is the pair of its
  even and odd rows (`jointProximityNat_of_jointProximityNat₂_splitEvenOdd`); one fold step is
  the affine line through that pair
  (`preTensorCombine_fold_eq_affineLineEvaluation_splitEvenOdd`), and the affine-line
  proximity gap of Reed–Solomon codes, lifted to interleaved codes, bounds the probability
  (`prob_affineLineEvaluation_close_le_of_not_jointProximityNat₂`).
* `prob_incrementalFoldingBadEvent_fresh_le`: the two cases together.

## Relation to [DP24]

[DP24] Proposition 4.21 bounds the probability mass of the whole bad set `Eᵢ ⊂ Lᶿ`
(Definition 4.20) by `ϑ · |S⁽ⁱ⁺ᶿ⁾| / |L|`. The incremental event is `False` at `k = 0` and is the
folding bad event at `k = ϑ` (`Compliance`), so summing the per-challenge bound over the `ϑ`
challenges of a block recovers that bound, for `ℓ + 𝓡 < r` as everywhere in Binius ([DP24] §4.1
also allows `ℓ + R = r`; the strict bound comes from CompPoly's `Fin r`-indexed subspaces `U`
behind `sDomain`). The per-challenge statement itself is not in [DP24]; it is specific to this
development. Its two cases follow the
two cases of the paper's proof, one challenge at a time: the paper applies the Schwartz–Zippel
lemma to all `ϑ` challenges in the close case, and the tensor proximity gap ([DP24] Theorem 2.4)
after Lemma 4.22 in the far case; here the far case uses the affine-line gap ([DP24] Theorem 2.3)
lifted to interleaved codes ([DG25], `affine_gaps_lifted_to_interleaved_codes`).

## References

* [Diamond, B.E. and Posen, J., *Polylogarithmic proofs for multilinears over binary towers*][DP24]
  Numbering follows the archived revision of [DP24].
* [Diamond, B.E. and Gruen, A., *Proximity Gaps in Interleaved Codes*][DG25]
-/

@[expose] public section




namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open ReedSolomon Code BerlekampWelch Function
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix
open ProbabilityTheory
open Probability

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable {𝓑 : Fin 2 ↪ L}
noncomputable section
variable [SampleableType L]
variable [hdiv : Fact (ϑ ∣ ℓ)]

open scoped NNReal ProbabilityTheory

section Prelims

open Classical in
omit [CharP L 2] [DecidableEq 𝔽q] h_β₀_eq_1 [NeZero ℓ] in
/-- If the pair `(u₀, u₁)` is not `e`-close to the interleaved destination code, with `e` within
the unique-decoding radius, then the affine line `(1 - r) • u₀ + r • u₁` is `e`-close to that
code with probability at most `|S| / |L|` over a uniform `r`. This is the contrapositive of the
affine-line proximity gap of Reed–Solomon codes
(`ReedSolomon_ProximityGapAffineLines_UniqueDecoding`, with false-witness bound `|S|`) lifted
to interleaved codes
(`affine_gaps_lifted_to_interleaved_codes`). -/
lemma prob_affineLineEvaluation_close_le_of_not_jointProximityNat₂
    {m : ℕ} (_hm : m ≥ 1) {destIdx : Fin r} (h_destIdx_le : destIdx ≤ ℓ)
    (u₀ u₁ : Word (InterleavedSymbol L (Fin m))
      (sDomain 𝔽q β h_ℓ_add_R_rate destIdx))
    (e : ℕ) (he : e ≤ Code.uniqueDecodingRadius
      (ι := sDomain 𝔽q β h_ℓ_add_R_rate destIdx) (F := L)
      (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx))
    (h_far : ¬ jointProximityNat₂ (A := InterleavedSymbol L (Fin m))
      (C := ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) ^⋈ (Fin m)))
      (u₀ := u₀) (u₁ := u₁) (e := e)) :
    Pr{let r ← $ᵗ L}[
      Δ₀(affineLineEvaluation (F := L) u₀ u₁ r,
        ((BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx) ^⋈ (Fin m))) ≤ e]
    ≤ (Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx) : ℝ≥0) / (Fintype.card L) := by
  by_contra h_prob_gt_bound
  apply h_far
  let S_dest := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
  let α := Embedding.subtype fun (x : L) ↦ x ∈ S_dest
  let C_dest := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
  let RS_dest := ReedSolomon.code α (2^(ℓ - destIdx.val))
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
      have : NeZero ‖(C_dest : Set (S_dest → L))‖₀ := NeZero.of_pos h_dist_pos
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
omit [NeZero ℓ] hdiv in
omit [DecidableEq 𝔽q] in
/-- The per-challenge bound on the incremental folding bad event when the block's oracle
`f⁽ⁱ⁾` is fiberwise close, with decoded codeword `f̄⁽ⁱ⁾`. Write `fₖ`, `f̄ₖ` for their folds at
the fixed prefix of `k` challenges.

The event at `k` fails when the fiberwise disagreement set `Δ` of `f⁽ⁱ⁾` and `f̄⁽ⁱ⁾` is contained
in that of `fₖ` and `f̄ₖ`; it holds at `k + 1` when some `y ∈ Δ` leaves the disagreement set after
one more fold with the fresh challenge `r`. For such `y`, the difference `fₖ - f̄ₖ` is nonzero
somewhere on the fiber of `y`, and on each pair of points of the next fiber the difference of
the folds is `a + (b - a) · r`, where `(a, b)` is the image of the nonzero difference vector under
the invertible fold matrix. This vanishes for at most one `r`, so `y` drops out with probability
at most `1 / |L|`, and a union bound over `Δ ⊆ S⁽ⁱ⁺ᶿ⁾` gives `|S⁽ⁱ⁺ᶿ⁾| / |L|`. -/
lemma prob_incrementalFoldingBadEvent_fresh_le_of_fiberwiseClose
    (block_start_idx : Fin r) {midIdx_i midIdx_i_succ destIdx : Fin r} (k : ℕ) (h_k_lt : k < ϑ)
    (h_midIdx_i : midIdx_i = block_start_idx + k)
    (h_midIdx_i_succ : midIdx_i_succ = block_start_idx + k + 1)
    (h_destIdx : destIdx = block_start_idx + ϑ) (h_destIdx_le : destIdx ≤ ℓ)
    (f_block_start : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx)
    (r_prefix : Fin k → L)
    (h_block_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := block_start_idx) (steps := ϑ) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (f := f_block_start)) :
    let domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    Pr{ let r_new ← $ᵗ L }[
      ¬ incrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (block_start_idx := block_start_idx) (midIdx := midIdx_i) (destIdx := destIdx) (k := k)
          (h_k_le := Nat.le_of_lt h_k_lt) (h_midIdx := h_midIdx_i)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
          (f_block_start := f_block_start) (r_challenges := r_prefix)
      ∧
      incrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (block_start_idx := block_start_idx) (midIdx := midIdx_i_succ)
        (destIdx := destIdx) (k := k + 1)
        (h_k_le := Nat.succ_le_of_lt h_k_lt) (h_midIdx := h_midIdx_i_succ)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (f_block_start := f_block_start)
        (r_challenges := Fin.snoc r_prefix r_new)
    ] ≤
    (domain_size / Fintype.card L) := by
  classical
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
      (f := f_i) (h_within_radius := UDRClose_of_fiberwiseClose 𝔽q β
        block_start_idx ϑ h_destIdx h_destIdx_le f_i h_block_close)
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
    apply le_trans (prEvent_mono ($ᵗ L) _ (fun _ => False)
      (fun r_new h => absurd (not_not.mp h.1) h_not_Ek))
    simp
  · -- pos case
    -- From here: h_not_Ek : Δ_fiber ⊆ fiberwiseDisagreementSet(midIdx_i, ϑ-k, fold_k_f,
    -- fold_k_f_bar)
    -- Use prob_mono to drop the ¬E(k) conjunct (it's deterministically true).
    apply le_trans (prEvent_mono ($ᵗ L) _ _ (fun r_new h => h.2))
    -- ────────────────────────────────────────────────────────
    -- Step 3: Bound Pr{r_new}[E(k+1)] ≤ |S^{destIdx}| / |L|
    -- ────────────────────────────────────────────────────────
    -- E(k+1) = ¬(Δ_fiber ⊆ fiberwiseDisagreementSet(midIdx_i_succ, ϑ-(k+1),
    --            fold_{k+1}(f, snoc r_prefix r_new), fold_{k+1}(f̄, snoc r_prefix r_new)))
    --
    -- Strategy: union bound, and a nonzero polynomial of degree ≤ 1 in r_new has ≤ 1 root.
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
    rw [SampleableType.prEvent_uniformSample]
    -- ── 3d: Per-point Schwartz-Zippel + union bound ──
    -- Per-point Schwartz-Zippel: |{r_new : y dropped}| ≤ 1 for each y,
    -- because fold difference is degree-1 in r_new with at most 1 root.
    -- Membership in Δ_fiber ensures non-trivial fiber disagreement.
    have h_per_point_card : ∀ y ∈ Δ_fiber,
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
      -- fold(iterated_fold(k, Fin.init (snoc r_prefix r_new)), snoc r_prefix r_new (Fin.last k))
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
        -- h_not_in : y ∉ fiberwiseDisagreementSet(midIdx_i_succ, ϑ-(k+1), ..., fold(fold_k_f,
        -- r_val), fold(fold_k_f̄, r_val))
        -- Unfold fiberwiseDisagreementSet
        simp only [fiberwiseDisagreementSet, Finset.mem_filter, Finset.mem_univ,
          true_and, not_exists, not_and] at h_not_in
        -- h_not_in : ∀ z, iteratedQuotientMap z = y → fold(fold_k_f, r_val)(z) = fold(fold_k_f̄,
        -- r_val)(z)
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

omit [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [CharP L 2] [NeZero ℓ] in
omit [SampleableType L] in
/-- One fold step on a tensor-combine stack is the affine line through its even and odd rows.
If `U` is the stack of `f_i` over `steps + 1` folds, with even rows `U_even` and odd rows
`U_odd` (`splitEvenOddRowWiseInterleavedWords`), then the stack over the remaining `steps` folds
of `fold f_i r_new` is `affineLineEvaluation (⋈|U_even) (⋈|U_odd) r_new`: folding
consumes the first challenge, which pairs rows `2j` and `2j + 1`. -/
lemma preTensorCombine_fold_eq_affineLineEvaluation_splitEvenOdd
    (i : Fin ℓ) (steps : ℕ) [NeZero steps] {midIdx destIdx : Fin r}
    (h_midIdx : midIdx.val = i.val + 1)
    (h_destIdx : destIdx.val = i.val + (steps + 1))
    (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i, by omega⟩)
    (r_new : L) :
    let h_midIdx_lt_ℓ : midIdx.val < ℓ := by
      have := NeZero.pos steps; omega
    let U := preTensorCombine 𝔽q β i (steps + 1)
      (destIdx := destIdx) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) f_i
    let U_even := (splitEvenOddRowWiseInterleavedWords (ϑ := steps) U).1
    let U_odd := (splitEvenOddRowWiseInterleavedWords (ϑ := steps) U).2
    let fold_1_f := fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i, by omega⟩ (destIdx := midIdx) (h_destIdx := h_midIdx)
      (h_destIdx_le := by omega) f_i r_new
    let midIdx_fin_ℓ : Fin ℓ := ⟨midIdx.val, h_midIdx_lt_ℓ⟩
    let V := preTensorCombine 𝔽q β midIdx_fin_ℓ steps
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
          (challengeTensorExpansion_bitsOfIndex (L := L) j') k
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

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] [SampleableType L] in
/-- A single fold of `f_i` is the multilinear combination, at the fold challenge, of the
two-row tensor-combine stack of `f_i`. -/
lemma fold_eq_multilinearCombine_preTensorCombine
    (i : Fin ℓ) {destIdx : Fin r}
    (h_destIdx : destIdx.val = i.val + 1) (h_destIdx_le : destIdx ≤ ℓ)
    (f_i : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
    (r_new : L) :
    let U := preTensorCombine 𝔽q β i 1
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
    ext a b; fin_cases a <;> fin_cases b <;>
      simp [blockDiagMatrix, reindexSquareMatrix, from4Blocks]
  simp only [challengeTensorExpansion, Fin.isValue, butterflyMatrix_zero_apply, cons_mulVec,
    cons_dotProduct, neg_mul, dotProduct_of_isEmpty, add_zero, one_mul, empty_mulVec,
    Matrix.dotProduct_cons, preTensorCombine, reducePow, foldMatrix, reduceAdd,
    Nat.add_zero, h_blk, mul_one, Fin.sum_univ_two, cons_val_zero, cons_val_one, cons_val_fin_one]
  have h_w0 :
      vecHead (multilinearWeight (F := L) (r := fun _ : Fin 1 => r_new)) =
        multilinearWeight (F := L) (r := fun _ : Fin 1 => r_new) 0 := by
    rfl
  have h_w1 :
      vecHead (vecTail (multilinearWeight (F := L) (r := fun _ : Fin 1 => r_new))) =
        multilinearWeight (F := L) (r := fun _ : Fin 1 => r_new) 1 := by
    rfl
  rw [h_w0, h_w1]

omit [DecidableEq 𝔽q] in
omit [CharP L 2] [NeZero ℓ] in
omit [SampleableType L] in
/-- If the single fold `fold f_i r_new` is fiberwise close over the remaining `s` folds, then the
affine line at `r_new` through the even and odd rows of the stack of `f_i` over `s + 1` folds is
within the unique-decoding radius of the interleaved destination code. -/
lemma distFromCode_affineLineEvaluation_le_of_fiberwiseClose_fold
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
    let U := preTensorCombine 𝔽q β i_ℓ (s + 1)
      (destIdx := destIdx) (h_destIdx := by simp [i_ℓ]; omega)
      (h_destIdx_le := h_destIdx_le) f_i
    let U_even := (splitEvenOddRowWiseInterleavedWords (ϑ := s) U).1
    let U_odd := (splitEvenOddRowWiseInterleavedWords (ϑ := s) U).2
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
        midIdx (_h_i := h_midIdx_le_ℓ) fold_1_f := by
      rw [←fiberwiseClose_steps_zero_iff_UDRClose]
      exact h_fw_close
    rw [UDRClose_iff_within_UDR_radius] at h_udr_close
    subst h_midIdx_eq_destIdx
    change Δ₀(affineLineEvaluation (F := L)
      (interleaveWordStack U_even) (interleaveWordStack U_odd) r_new,
      interleavedCodeSet (κ := Fin (2 ^ 0)) C_dest) ≤
      Code.uniqueDecodingRadius (C := C_dest)
    rw [distFromCode_interleavedCodeSet_fin_one]
    suffices h_eq : (fun y => affineLineEvaluation
        (interleaveWordStack U_even) (interleaveWordStack U_odd) r_new y
        (0 : Fin (2 ^ 0))) =
        fold_1_f by
      rw [h_eq]; exact h_udr_close
    have h_rhs : fold_1_f = multilinearCombine (F := L) U (fun (_ : Fin 1) => r_new) := by
      have h_rhs := fold_eq_multilinearCombine_preTensorCombine 𝔽q β
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
      change (1 - r_new) * U 0 y + r_new * U 1 y = multilinearCombine U (fun _ => r_new) y
      simp [multilinearCombine, multilinearWeight]
    have h_fn_eq : (fun y => affineLineEvaluation
        (interleaveWordStack U_even) (interleaveWordStack U_odd) r_new y
        (0 : Fin (2 ^ 0))) = fold_1_f := by
      rw [h_affine_eq_mc, h_rhs]
    rw [h_fn_eq]
  · have h_midIdx_lt_ℓ : midIdx.val < ℓ := by omega
    let midIdx_ℓ : Fin ℓ := ⟨midIdx.val, h_midIdx_lt_ℓ⟩
    have : NeZero s := ⟨hs⟩
    have h_joint := preTensorCombine_jointProximityNat_of_fiberwiseClose 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := midIdx_ℓ) (steps := s)
      (h_destIdx := by simp only [midIdx_ℓ]; omega)
      (h_destIdx_le := h_destIdx_le)
      (f_i := fold_1_f)
      (h_close := h_fw_close)
    have h_eq := preTensorCombine_fold_eq_affineLineEvaluation_splitEvenOdd 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := i_ℓ) (steps := s)
      (midIdx := midIdx) (destIdx := destIdx)
      (h_midIdx := by simp only [i_ℓ]; omega)
      (h_destIdx := by simp only [i_ℓ]; omega)
      (h_destIdx_le := h_destIdx_le)
      (f_i := f_i) (r_new := r_new)
    have h_eq' :
        interleaveWordStack
            (preTensorCombine 𝔽q β
              (i := ⟨midIdx.val, h_midIdx_lt_ℓ⟩) (steps := s)
              (destIdx := destIdx)
              (h_destIdx := by simp; omega)
              (h_destIdx_le := h_destIdx_le) fold_1_f) =
          affineLineEvaluation (F := L)
            (interleaveWordStack U_even) (interleaveWordStack U_odd) r_new := by
      have h_eq' := h_eq
      simp only [U_even, U_odd] at h_eq' ⊢
      exact h_eq'
    unfold jointProximityNat at h_joint
    rw [← h_eq']
    exact h_joint

omit hdiv in
omit [DecidableEq 𝔽q] in
omit [CharP L 2] [NeZero ℓ] in
/-- The per-challenge bound on the incremental folding bad event when the block's oracle is not
fiberwise close. Write `fₖ` for its fold at the fixed prefix of `k` challenges and `U` for the
tensor-combine stack of `fₖ` over the remaining `ϑ - k` folds.

If `fₖ` is already fiberwise close, the event holds at `k` and there is nothing to bound.
Otherwise `U` is far from the interleaved destination code
(`preTensorCombine_not_jointProximityNat_of_not_fiberwiseClose`), so the pair of its even and
odd rows is far as well (`jointProximityNat_of_jointProximityNat₂_splitEvenOdd`). The stack of
the next fold is the affine line through that pair at the fresh challenge
(`preTensorCombine_fold_eq_affineLineEvaluation_splitEvenOdd`), and it is close whenever the
next fold is fiberwise close (`preTensorCombine_jointProximityNat_of_fiberwiseClose`); the
affine-line proximity gap (`prob_affineLineEvaluation_close_le_of_not_jointProximityNat₂`)
bounds that probability by `|S⁽ⁱ⁺ᶿ⁾| / |L|`. -/
lemma prob_incrementalFoldingBadEvent_fresh_le_of_not_fiberwiseClose
    (block_start_idx : Fin r) {midIdx_i midIdx_i_succ destIdx : Fin r} (k : ℕ) (h_k_lt : k < ϑ)
    (h_midIdx_i : midIdx_i = block_start_idx + k)
    (h_midIdx_i_succ : midIdx_i_succ = block_start_idx + k + 1)
    (h_destIdx : destIdx = block_start_idx + ϑ) (h_destIdx_le : destIdx ≤ ℓ)
    (f_block_start : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx)
    (r_prefix : Fin k → L)
    (h_block_far : ¬ fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      (i := block_start_idx) (steps := ϑ) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
      (f := f_block_start)) :
    let domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    Pr{ let r_new ← $ᵗ L }[
      ¬ incrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (block_start_idx := block_start_idx) (midIdx := midIdx_i) (destIdx := destIdx) (k := k)
          (h_k_le := Nat.le_of_lt h_k_lt) (h_midIdx := h_midIdx_i)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
          (f_block_start := f_block_start) (r_challenges := r_prefix)
      ∧
      incrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (block_start_idx := block_start_idx) (midIdx := midIdx_i_succ)
        (destIdx := destIdx) (k := k + 1)
        (h_k_le := Nat.succ_le_of_lt h_k_lt) (h_midIdx := h_midIdx_i_succ)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (f_block_start := f_block_start)
        (r_challenges := Fin.snoc r_prefix r_new)
    ] ≤
    (domain_size / Fintype.card L) := by
  classical
  dsimp only [incrementalFoldingBadEvent]
  simp only [h_block_far, ↓reduceDIte]
  let fold_k_f := iterated_fold 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := block_start_idx) (steps := k) (h_destIdx := h_midIdx_i) (h_destIdx_le := by omega)
    (f := f_block_start) (r_challenges := r_prefix)
  let Ek_close := fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := midIdx_i) (steps := ϑ - k) (h_destIdx := by omega)
    (h_destIdx_le := h_destIdx_le) (f := fold_k_f)
  by_cases h_Ek_close : Ek_close
  · apply le_trans (prEvent_mono ($ᵗ L) _ _ (fun r_new h => h.1))
    have : Pr{ let r_new ← $ᵗ L }[¬Ek_close] = 0 := by
      rw [SampleableType.prEvent_uniformSample]
      simp only [not_not.mpr h_Ek_close, Finset.filter_false, card_empty, CharP.cast_eq_zero,
        ENNReal.zero_div]
    rw [this]; exact bot_le
  · apply le_trans (prEvent_mono ($ᵗ L) _ _ (fun r_new h => h.2))
    have h_midIdx_i_lt_ℓ : midIdx_i.val < ℓ := by omega
    let s := ϑ - k - 1
    have h_steps_eq : ϑ - k = s + 1 := by omega
    have : NeZero (s + 1) := ⟨by omega⟩
    let S_dest := sDomain 𝔽q β h_ℓ_add_R_rate destIdx
    let C_dest : Set (S_dest → L) :=
      BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) destIdx
    let e_prox := Code.uniqueDecodingRadius (C := C_dest)
    let i_ℓ : Fin ℓ := ⟨midIdx_i.val, h_midIdx_i_lt_ℓ⟩
    let U := preTensorCombine 𝔽q β i_ℓ (s + 1)
      (destIdx := destIdx)
      (h_destIdx := by simp [i_ℓ]; omega)
      (h_destIdx_le := h_destIdx_le)
      fold_k_f
    have h_U_far : ¬jointProximityNat (C := C_dest) (u := U)
        (e := e_prox) := by
      apply preTensorCombine_not_jointProximityNat_of_not_fiberwiseClose 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (i := i_ℓ) (steps := s + 1)
        (h_destIdx := by simp [i_ℓ]; omega)
        (h_destIdx_le := h_destIdx_le)
        (f_i := fold_k_f)
        (h_far := by convert h_Ek_close using 2; omega)
    let U_even := (splitEvenOddRowWiseInterleavedWords (ϑ := s) U).1
    let U_odd := (splitEvenOddRowWiseInterleavedWords (ϑ := s) U).2
    let u_even := interleaveWordStack U_even
    let u_odd := interleaveWordStack U_odd
    have h_pair_far : ¬ jointProximityNat₂
        (A := InterleavedSymbol L (Fin (2^s)))
        (C := (C_dest ^⋈ (Fin (2^s))))
        (u₀ := u_even) (u₁ := u_odd) (e := e_prox) :=
      fun h_close => h_U_far
        (jointProximityNat_of_jointProximityNat₂_splitEvenOdd C_dest U e_prox h_close)
    have h_affine_bound :
        Pr{let r ← $ᵗ L}[
          Δ₀(affineLineEvaluation (F := L) u_even u_odd r,
            (C_dest ^⋈ (Fin (2^s)))) ≤ e_prox]
        ≤ (Fintype.card S_dest : ℝ≥0) / (Fintype.card L) :=
      prob_affineLineEvaluation_close_le_of_not_jointProximityNat₂
        𝔽q β Nat.one_le_two_pow h_destIdx_le
        (e := e_prox) (he := le_refl _) (h_far := h_pair_far)
    apply le_trans _ h_affine_bound
    apply prEvent_mono ($ᵗ L) _ _
    intro r_new h_fw_close
    exact distFromCode_affineLineEvaluation_le_of_fiberwiseClose_fold 𝔽q β
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

omit [DecidableEq 𝔽q] hdiv in
omit [NeZero ℓ] in
/-- For a block starting at `block_start_idx`, an oracle `f_block_start` and a fixed prefix of
`k < ϑ` challenges, the probability over a fresh uniform challenge `r_new` that the incremental
folding bad event holds after `k + 1` challenges but not after `k` is at most
`|S⁽ⁱ⁺ᶿ⁾| / |L|`. -/
lemma prob_incrementalFoldingBadEvent_fresh_le
    (block_start_idx : Fin r) {midIdx_i midIdx_i_succ destIdx : Fin r} (k : ℕ) (h_k_lt : k < ϑ)
    (h_midIdx_i : midIdx_i = block_start_idx + k)
    (h_midIdx_i_succ : midIdx_i_succ = block_start_idx + k + 1)
    (h_destIdx : destIdx = block_start_idx + ϑ) (h_destIdx_le : destIdx ≤ ℓ)
    (f_block_start : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) block_start_idx)
    (r_prefix : Fin k → L) :
    let domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate destIdx)
    Pr{ let r_new ← $ᵗ L }[
      ¬ incrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
          (block_start_idx := block_start_idx) (midIdx := midIdx_i) (destIdx := destIdx) (k := k)
          (h_k_le := Nat.le_of_lt h_k_lt) (h_midIdx := h_midIdx_i)
          (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
          (f_block_start := f_block_start) (r_challenges := r_prefix)
      ∧
      incrementalFoldingBadEvent 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
        (block_start_idx := block_start_idx) (midIdx := midIdx_i_succ)
        (destIdx := destIdx) (k := k + 1)
        (h_k_le := Nat.succ_le_of_lt h_k_lt) (h_midIdx := h_midIdx_i_succ)
        (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
        (f_block_start := f_block_start)
        (r_challenges := Fin.snoc r_prefix r_new)
    ] ≤
    (domain_size / Fintype.card L) := by
  classical
  by_cases h_block_close : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := block_start_idx) (steps := ϑ) (h_destIdx := h_destIdx) (h_destIdx_le := h_destIdx_le)
    (f := f_block_start)
  · exact prob_incrementalFoldingBadEvent_fresh_le_of_fiberwiseClose 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (block_start_idx := block_start_idx)
      (midIdx_i := midIdx_i) (midIdx_i_succ := midIdx_i_succ) (destIdx := destIdx)
      (k := k) (h_k_lt := h_k_lt) (h_midIdx_i := h_midIdx_i)
      (h_midIdx_i_succ := h_midIdx_i_succ) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f_block_start := f_block_start)
      (r_prefix := r_prefix) (h_block_close := h_block_close)
  · exact prob_incrementalFoldingBadEvent_fresh_le_of_not_fiberwiseClose 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (block_start_idx := block_start_idx)
      (midIdx_i := midIdx_i) (midIdx_i_succ := midIdx_i_succ) (destIdx := destIdx)
      (k := k) (h_k_lt := h_k_lt) (h_midIdx_i := h_midIdx_i)
      (h_midIdx_i_succ := h_midIdx_i_succ) (h_destIdx := h_destIdx)
      (h_destIdx_le := h_destIdx_le) (f_block_start := f_block_start)
      (r_prefix := r_prefix) (h_block_far := h_block_close)

end

end Binius.BinaryBasefold
