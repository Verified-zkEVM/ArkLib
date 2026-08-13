/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Folded
import ArkLib.Data.CodingTheory.ReedSolomon.Multiplicity
import ArkLib.Data.Polynomial.ClassicalWronskian
import ArkLib.Data.Polynomial.FoldedWronskian
import ArkLib.ToMathlib.LinearAlgebra.FiniteDimensional
import ArkLib.ToMathlib.Polynomial.RootMultiplicity

/-!
# Subspace designs

A code over the alphabet `F^s`, presented as an `F`-subspace `C` of `ι → Fin s → F`, is a
*`τ`-subspace design* when every subspace `A ≤ C` of dimension at most `r` satisfies

  `(∑ i, dim {a ∈ A | a i = 0}) / n ≤ dim A * τ r` ,

where `n = |ι|` is the block length. Equivalently: no low-dimensional subspace of `C` can
have many of its codewords vanish at many positions.

## Main definitions

* `CodingTheory.IsSubspaceDesign` — the design property, for a profile `τ : ℕ → ℝ`.

## Main statements

* `CodingTheory.subspaceDesign_tau_lower` — every subspace-design profile obeys
  `τ r ≥ ρ - 1/n` for `r ≥ 1`, where `ρ` is the alphabet-normalized rate.
* `CodingTheory.sum_finrank_inf_ker_le` — a nonzero subspace loses a dimension at some
  block, `(∑ i, dim Aᵢ) + 1 ≤ n * dim A`. This is the slack that separates the two profile
  levels below.
* `CodingTheory.isSubspaceDesign_frsCode_sub_one` and
  `CodingTheory.isSubspaceDesign_umCode_sub_one` — folded Reed-Solomon codes and univariate
  multiplicity codes are subspace designs for the `(k-1)`-level profile
  `τ r = (s * ρ - 1/n) / (s - r + 1)` on `1 ≤ r ≤ s`, which is [CZ25, Definition B.2]'s and
  what the Wronskian count actually proves.
* `CodingTheory.isSubspaceDesign_frsCode` and `CodingTheory.isSubspaceDesign_umCode` — the
  `1/n`-relaxations at [ABF26] Theorem 2.18's printed profile `τ r = s * ρ / (s - r + 1)`,
  each a one-line `mono_tau` corollary of the sharp form. **Consumers proving list
  decodability up to capacity need the sharp form**: at the relaxed level
  [CZ25, Theorem B.5] is false, see `CodingTheory.subspaceDesign_lambda_le`.

The two code-family results are proved by a Wronskian root count, using
`Polynomial.foldedWronskian` and `Polynomial.classicalWronskian` respectively.

## References

* [Guruswami, V., and Xing, C., *List decoding Reed-Solomon, Algebraic-Geometric, and
    Gabidulin subcodes up to the Singleton bound*][GX13]
* [Goyal, R., and Guruswami, V., *Optimal Proximity Gaps for Subspace-Design Codes and
    (Random) Reed-Solomon Codes*][GG25]
* [Guruswami, V., and Kopparty, S., *Explicit subspace designs*][GK16]
* [Guruswami, V., and Rudra, A., *Explicit Codes Achieving List Decoding Capacity:
    Error-Correction With Optimal Redundancy*][GR08]
* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
    Agreement*][ABF26]
-/

namespace CodingTheory

open scoped NNReal

/-- A code `C` over the alphabet `F^s`, presented as an `F`-subspace of `ι → Fin s → F`, is
`τ`-**subspace design** if for every `r` and every subspace `A ≤ C` with `dim A ≤ r`,

  `(∑ i, dim Aᵢ) / n ≤ dim A * τ r` ,

where `n = |ι|` and `Aᵢ := {a ∈ A | a i = 0}` is the subspace of `A` vanishing at position
`i`, realised as `A ⊓ ker (LinearMap.proj i)` (see `ker_proj_eq_vanish_at`). -/
def IsSubspaceDesign {ι : Type*} [Fintype ι]
    {F : Type*} [Field F] (s : ℕ) (τ : ℕ → ℝ)
    (C : Submodule F (ι → Fin s → F)) : Prop :=
  ∀ r : ℕ, ∀ A : Submodule F (ι → Fin s → F), A ≤ C →
    Module.finrank F A ≤ r →
    (∑ i : ι,
        (Module.finrank F (↥(A ⊓
            (LinearMap.ker
              (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
            Submodule F (ι → Fin s → F))) : ℝ)) /
        Fintype.card ι ≤
      Module.finrank F A * τ r

/-- A `τ₁`-subspace design is a `τ₂`-subspace design for every pointwise-larger profile
`τ₂`: the design bound is monotone in `τ r`, since `dim A ≥ 0`. -/
theorem IsSubspaceDesign.mono_tau {ι : Type*} [Fintype ι]
    {F : Type*} [Field F] {s : ℕ} {τ₁ τ₂ : ℕ → ℝ}
    {C : Submodule F (ι → Fin s → F)}
    (h : IsSubspaceDesign s τ₁ C) (hτ : ∀ r, τ₁ r ≤ τ₂ r) :
    IsSubspaceDesign s τ₂ C := fun r A hAC hAr =>
  (h r A hAC hAr).trans (mul_le_mul_of_nonneg_left (hτ r) (Nat.cast_nonneg _))

/-- The kernel of the `i`-th projection is the set of words vanishing at `i`. This is the
comprehension form of the subspace `Aᵢ` appearing in `IsSubspaceDesign`. -/
lemma ker_proj_eq_vanish_at {ι : Type*} {F : Type*} [Semiring F] {s : ℕ} (i : ι) :
    (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) :
        Set (ι → Fin s → F)) =
      {a | a i = 0} := by
  ext a
  simp [LinearMap.mem_ker, LinearMap.proj_apply]

/-- **A nonzero subspace loses a dimension at some block.** For `A ≠ ⊥`,

  `(∑ i, dim Aᵢ) + 1 ≤ n * dim A` ,

where `Aᵢ = A ⊓ ker (proj i)`: the trivial bound `dim Aᵢ ≤ dim A` is strict at any block where some
nonzero element of `A` does not vanish, and such a block exists.

This is exactly the slack that separates the two design levels in play. The bound
`∑ i, dim Aᵢ ≤ n * dim A` is enough for [ABF26] Theorem 2.18's profile
`s * ρ / (s - r + 1)`, but one short of the `(k-1)`-level profile of [CZ25, Definition B.2] at
`τ r = 1 - 1/(n * s)`; see `isSubspaceDesign_frsCode_sub_one`. -/
theorem sum_finrank_inf_ker_le {ι : Type*} [Fintype ι] {F : Type*} [Field F] {s : ℕ}
    (A : Submodule F (ι → Fin s → F)) (hA : A ≠ ⊥) :
    (∑ i : ι, Module.finrank F (↥(A ⊓ (LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
          Submodule F (ι → Fin s → F)))) + 1
      ≤ Fintype.card ι * Module.finrank F A := by
  classical
  set σ := Module.finrank F A with hσ
  obtain ⟨a, haA, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hA
  obtain ⟨i₀, hi₀⟩ : ∃ i₀ : ι, a i₀ ≠ 0 := by
    by_contra h
    push Not at h
    exact ha0 (funext h)
  have hle : ∀ i : ι, Module.finrank F (↥(A ⊓ (LinearMap.ker
      (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
        Submodule F (ι → Fin s → F))) ≤ σ :=
    fun i => Submodule.finrank_mono inf_le_left
  have hlt : Module.finrank F (↥(A ⊓ (LinearMap.ker
      (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀)) :
        Submodule F (ι → Fin s → F))) + 1 ≤ σ := by
    have hne : A ⊓ (LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀)) ≠ A := by
      intro heq
      have hmem : a ∈ A ⊓ LinearMap.ker
          (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i₀) := by
        rw [heq]; exact haA
      exact hi₀ (by simpa using hmem.2)
    have := Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left hne)
    omega
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset ι)
    (fun i => Module.finrank F (↥(A ⊓ (LinearMap.ker
      (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
        Submodule F (ι → Fin s → F)))) (Finset.mem_univ i₀)
  have hrest : ∑ i ∈ (Finset.univ : Finset ι).erase i₀,
      Module.finrank F (↥(A ⊓ (LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
          Submodule F (ι → Fin s → F))) ≤ (Fintype.card ι - 1) * σ := by
    calc ∑ i ∈ (Finset.univ : Finset ι).erase i₀, _
        ≤ ∑ _i ∈ (Finset.univ : Finset ι).erase i₀, σ := Finset.sum_le_sum fun i _ => hle i
      _ = (Fintype.card ι - 1) * σ := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i₀),
            Finset.card_univ, smul_eq_mul]
  have hn1 : 1 ≤ Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i₀⟩
  have hcard : (Fintype.card ι - 1) * σ + σ = Fintype.card ι * σ := by
    have hsub : Fintype.card ι - 1 + 1 = Fintype.card ι := Nat.sub_add_cancel hn1
    calc (Fintype.card ι - 1) * σ + σ = (Fintype.card ι - 1 + 1) * σ := by ring
      _ = Fintype.card ι * σ := by rw [hsub]
  omega

/-- The profile of a nontrivial `τ`-subspace design of alphabet-normalized rate `ρ` is
bounded below by `ρ - 1/n` at every `r ≥ 1`.

Here `ρ = dim_F C / (s * n)`, the rate relative to the alphabet `F^s`; the subtracted
term `1/n` divides by the block length alone.

The range `1 ≤ r` is sharp: at `r = 0` the design condition only ever compares `0 ≤ 0`,
since `A ≤ C` and `dim A ≤ 0` force `A = ⊥`, so `τ 0` is unconstrained. Some
non-degeneracy hypothesis is likewise unavoidable, since for `C = ⊥` every design
inequality also reads `0 ≤ 0`: at `n = 2` the profile `τ ≡ -1` is a design profile for
`⊥` yet violates the conclusion. Here that hypothesis is `C ≠ ⊥`; see
`subspaceDesign_tau_lower` for the variant that guards the profile instead.

The proof applies the design condition to `span {u - v}` for a distance-attaining pair
`u ≠ v` in `C`, which has at least `n - d` vanishing blocks, and then converts `d` into
`ρ` with the module-alphabet Singleton bound `LinearCode.singleton_bound_module`. -/
theorem subspaceDesign_tau_lower_of_ne_bot
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {F : Type*} [Field F] [Finite F]
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h_design : IsSubspaceDesign s τ C) (hs : 1 ≤ s) (hCne : C ≠ ⊥) :
    ∀ r, 1 ≤ r →
      τ r ≥ (Module.finrank F C : ℝ) / (s * Fintype.card ι) - 1 / Fintype.card ι := by
  classical
  intro r hr1
  have hn_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hs_pos : (0 : ℝ) < s := by exact_mod_cast hs
  -- Run the GG25 argument at the span of a distance-attaining word.
  -- Step 1: a distance-attaining pair, hence a nonzero codeword `a` of block-weight ≤ d.
  obtain ⟨x, hxC, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hCne
  set d := Code.dist (C : Set (ι → Fin s → F)) with hd
  have hS_ne : {m | ∃ u ∈ (C : Set (ι → Fin s → F)), ∃ v ∈ (C : Set (ι → Fin s → F)),
      u ≠ v ∧ hammingDist u v ≤ m}.Nonempty :=
    ⟨hammingDist x 0, x, hxC, 0, C.zero_mem, hx0, le_rfl⟩
  obtain ⟨u, huC, v, hvC, huv, hΔ⟩ : ∃ u ∈ (C : Set (ι → Fin s → F)),
      ∃ v ∈ (C : Set (ι → Fin s → F)), u ≠ v ∧ hammingDist u v ≤ d :=
    Nat.sInf_mem hS_ne
  set a := u - v with ha_def
  have haC : a ∈ C := C.sub_mem huC hvC
  have ha0 : a ≠ 0 := sub_ne_zero.mpr huv
  -- Block-weight of `a` equals `hammingDist u v` (which is `≤ d`).
  have hwt : (Finset.univ.filter (fun i => a i ≠ 0)).card = hammingDist u v := by
    unfold hammingDist
    congr 1
    ext i
    simp [ha_def, sub_eq_zero]
  -- Step 2: the design inequality at `A := span {a}` (1-dimensional, and `1 ≤ r`).
  set A : Submodule F (ι → Fin s → F) := Submodule.span F {a} with hA
  have hAC : A ≤ C := (Submodule.span_singleton_le_iff_mem a C).mpr haC
  have hA1 : Module.finrank F A = 1 := finrank_span_singleton ha0
  have hdesign := h_design r A hAC (by rw [hA1]; exact hr1)
  -- Step 3: per-position dimension of `A ⊓ ker (proj i)` is the zero-block indicator.
  have hper : ∀ i : ι,
      Module.finrank F (↥(A ⊓
          (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
          Submodule F (ι → Fin s → F))) = if a i = 0 then 1 else 0 := by
    intro i
    by_cases hai : a i = 0
    · rw [if_pos hai]
      have hle : A ≤ LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) := by
        rw [hA, Submodule.span_le, Set.singleton_subset_iff]
        simpa [LinearMap.mem_ker] using hai
      rw [inf_eq_left.mpr hle]
      exact hA1
    · rw [if_neg hai]
      have hbot : A ⊓ LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)
          = ⊥ := by
        rw [eq_bot_iff]
        rintro y ⟨hyA, hyk⟩
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hyA
        have hc0 : c • a i = 0 := by simpa [LinearMap.mem_ker] using hyk
        rcases smul_eq_zero.mp hc0 with hc | hzero
        · simp [hc]
        · exact absurd hzero hai
      rw [hbot]
      exact finrank_bot F _
  -- Step 4: the design sum counts the zero blocks of `a`.
  have hsum : (∑ i : ι,
      (Module.finrank F (↥(A ⊓
          (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) :
          Submodule F (ι → Fin s → F))) : ℝ)) =
      ((Finset.univ.filter (fun i => a i = 0)).card : ℝ) := by
    rw [← Finset.sum_boole]
    exact Finset.sum_congr rfl fun i _ => by
      rw [hper i]; by_cases hai : a i = 0 <;> simp [hai]
  -- Step 5: Singleton bound at the block alphabet: `k ≤ s · (n − (d − 1))`.
  have hsingleton := LinearCode.singleton_bound_module (F := F) (C := C)
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at hsingleton
  -- Numeric bookkeeping over ℕ.
  have hwt_le_d : (Finset.univ.filter (fun i => a i ≠ 0)).card ≤ d := hwt ▸ hΔ
  have hwt_le_n : (Finset.univ.filter (fun i => a i ≠ 0)).card ≤ Fintype.card ι :=
    Finset.card_filter_le _ _
  have hd1 : 1 ≤ d := by
    rcases Nat.eq_zero_or_pos d with h0 | h
    · exact absurd (hammingDist_eq_zero.mp (Nat.le_zero.mp (h0 ▸ hΔ))) huv
    · exact h
  have hd_le_n : d ≤ Fintype.card ι := by
    have hmem : hammingDist u v ∈ {m | ∃ u ∈ (C : Set (ι → Fin s → F)),
        ∃ v ∈ (C : Set (ι → Fin s → F)), u ≠ v ∧ hammingDist u v ≤ m} :=
      ⟨u, huC, v, hvC, huv, le_rfl⟩
    exact le_trans (Nat.sInf_le hmem) (hwt ▸ hwt_le_n)
  have hcards : (Finset.univ.filter (fun i => a i = 0)).card
      = Fintype.card ι - (Finset.univ.filter (fun i => a i ≠ 0)).card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := (Finset.univ : Finset ι)) (p := fun i => a i = 0)
    simp only [Finset.card_univ, ne_eq] at h ⊢
    omega
  -- Step 6: cast the Singleton bound to ℝ: `k ≤ s (n − d + 1)`.
  have hcast : (Module.finrank F C : ℝ) ≤ s * ((Fintype.card ι : ℝ) - d + 1) := by
    have h1 : d - 1 ≤ Fintype.card ι := le_trans (Nat.sub_le d 1) hd_le_n
    calc (Module.finrank F C : ℝ)
        ≤ ((s * (Fintype.card ι - (d - 1)) : ℕ) : ℝ) := by exact_mod_cast hsingleton
      _ = s * ((Fintype.card ι : ℝ) - d + 1) := by
          rw [Nat.cast_mul, Nat.cast_sub h1, Nat.cast_sub hd1]
          push_cast
          ring
  -- Step 7: chain everything over ℝ.
  have hτ_ge : ((Finset.univ.filter (fun i => a i = 0)).card : ℝ) / Fintype.card ι ≤ τ r := by
    calc ((Finset.univ.filter (fun i => a i = 0)).card : ℝ) / Fintype.card ι
        ≤ Module.finrank F A * τ r := by rw [← hsum]; exact hdesign
      _ = τ r := by rw [hA1]; push_cast; ring
  have hzeros : ((Fintype.card ι : ℝ) - d) ≤
      ((Finset.univ.filter (fun i => a i = 0)).card : ℝ) := by
    rw [hcards, Nat.cast_sub hwt_le_n]
    have : ((Finset.univ.filter (fun i => a i ≠ 0)).card : ℝ) ≤ d := by exact_mod_cast hwt_le_d
    linarith
  have hkey : (Module.finrank F C : ℝ) / (s * Fintype.card ι) - 1 / Fintype.card ι ≤
      ((Fintype.card ι : ℝ) - d) / Fintype.card ι := by
    have hdiv : (Module.finrank F C : ℝ) / (s * Fintype.card ι) ≤
        ((Fintype.card ι : ℝ) - d + 1) / Fintype.card ι := by
      rw [div_le_div_iff₀ (by positivity) hn_pos]
      calc (Module.finrank F C : ℝ) * Fintype.card ι
          ≤ (s * ((Fintype.card ι : ℝ) - d + 1)) * Fintype.card ι :=
            mul_le_mul_of_nonneg_right hcast hn_pos.le
        _ = ((Fintype.card ι : ℝ) - d + 1) * (s * Fintype.card ι) := by ring
    have hsplit : ((Fintype.card ι : ℝ) - d + 1) / Fintype.card ι - 1 / Fintype.card ι =
        ((Fintype.card ι : ℝ) - d) / Fintype.card ι := by
      rw [div_sub_div_same]
      ring_nf
    linarith
  calc (Module.finrank F C : ℝ) / (s * Fintype.card ι) - 1 / Fintype.card ι
      ≤ ((Fintype.card ι : ℝ) - d) / Fintype.card ι := hkey
    _ ≤ ((Finset.univ.filter (fun i => a i = 0)).card : ℝ) / Fintype.card ι := by gcongr
    _ ≤ τ r := hτ_ge

/-- The profile of a `τ`-subspace design of alphabet-normalized rate `ρ` with `τ ≥ 0` is
bounded below by `ρ - 1/n` at every `r ≥ 1`.

This is `subspaceDesign_tau_lower_of_ne_bot` with the non-degeneracy hypothesis moved from
the code to the profile, making the statement total in `C`. Since a design profile bounds
a ratio of dimensions, `0 ≤ τ` holds for every profile arising from a construction; use
the `_of_ne_bot` form when the profile is unknown but the code is known to be nontrivial.
See that declaration for the rate convention and for why `r ≥ 1` is needed. -/
theorem subspaceDesign_tau_lower
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {F : Type*} [Field F] [Finite F]
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h_design : IsSubspaceDesign s τ C) (hs : 1 ≤ s)
    (hτ_nonneg : ∀ r, 0 ≤ τ r) :
    ∀ r, 1 ≤ r →
      τ r ≥ (Module.finrank F C : ℝ) / (s * Fintype.card ι) - 1 / Fintype.card ι := by
  intro r hr1
  by_cases hCne : C = ⊥
  · -- Degenerate code: the bound is `-1/n ≤ 0 ≤ τ r`.
    have hC0 : Module.finrank F C = 0 := by rw [hCne]; exact finrank_bot F _
    rw [hC0]
    have hb : ((0 : ℕ) : ℝ) / (s * Fintype.card ι) - 1 / Fintype.card ι ≤ 0 := by
      simp only [Nat.cast_zero, zero_div, zero_sub]
      exact neg_nonpos.mpr (by positivity)
    exact le_trans hb (hτ_nonneg r)
  · exact subspaceDesign_tau_lower_of_ne_bot s τ C h_design hs hCne r hr1

/-- Base change for the folded Wronskian: replacing the polynomials by the `F`-linear
combinations with coefficient matrix `U` multiplies the folded Wronskian by `det U`. -/
private lemma foldedWronskian_of_linearComb {F : Type*} [Field F] {σ : ℕ} {ω : F}
    (P c : Fin σ → Polynomial F) (U : Matrix (Fin σ) (Fin σ) F)
    (hc : ∀ j, c j = ∑ i, U i j • P i) :
    Polynomial.foldedWronskian σ ω c
      = Polynomial.foldedWronskian σ ω P * Polynomial.C U.det := by
  classical
  have hM : (Matrix.of fun i j : Fin σ =>
        (c j).comp (Polynomial.C (ω ^ (i : ℕ)) * Polynomial.X))
      = (Matrix.of fun i j : Fin σ => (P j).comp (Polynomial.C (ω ^ (i : ℕ)) * Polynomial.X))
        * ((Polynomial.C : F →+* Polynomial F).mapMatrix U) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.of_apply, Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply]
    rw [hc j, Polynomial.sum_comp]
    exact Finset.sum_congr rfl fun i' _ => by
      rw [Polynomial.smul_comp, Polynomial.smul_eq_C_mul, mul_comm]
  unfold Polynomial.foldedWronskian
  rw [hM, Matrix.det_mul, ← RingHom.map_det]

/-- If every polynomial in a subspace `N ≤ B` has all of its `ω`-twists divisible by
`X - C p`, then `(X - C p) ^ dim N` divides the folded Wronskian of any basis of `B`.

Passing to a basis of `B` adapted to `N` makes `dim N` whole columns of the folded
Wronskian matrix divisible by `X - C p`; base change only rescales the determinant by a
nonzero constant. -/
private lemma pow_dvd_foldedWronskian {F : Type*} [Field F] {σ : ℕ} {ω : F}
    (B : Submodule F (Polynomial F)) (bas : Module.Basis (Fin σ) F B)
    (N : Submodule F (Polynomial F)) (hN : N ≤ B) (p : F)
    (hcol : ∀ q ∈ N, ∀ i : Fin σ, (Polynomial.X - Polynomial.C p) ∣
        q.comp (Polynomial.C (ω ^ (i : ℕ)) * Polynomial.X)) :
    (Polynomial.X - Polynomial.C p) ^ (Module.finrank F N)
      ∣ Polynomial.foldedWronskian σ ω (fun j => (bas j : Polynomial F)) := by
  classical
  haveI : Module.Finite F B := Module.Finite.of_basis bas
  have hrkB : Module.finrank F B = σ := by
    rw [Module.finrank_eq_card_basis bas, Fintype.card_fin]
  set N' : Submodule F B := N.comap B.subtype with hN'
  have hmap : N'.map B.subtype = N := by
    ext x
    simp only [hN', Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype,
      Subtype.exists]
    exact ⟨by rintro ⟨y, hy, hyx, rfl⟩; exact hyx, fun hx => ⟨x, hN hx, hx, rfl⟩⟩
  have hrkN' : Module.finrank F N' = Module.finrank F N := by
    rw [← hmap, Submodule.finrank_map_subtype_eq]
  obtain ⟨cb, hcb⟩ := N'.exists_adapted_basis hrkB
  set t := Module.finrank F N with htdef
  have hts : t ≤ σ := by
    rw [← hrkN', ← hrkB]
    exact Submodule.finrank_le N'
  set U : Matrix (Fin σ) (Fin σ) F := bas.toMatrix (⇑cb) with hU
  set c : Fin σ → Polynomial F := fun j => ((cb j : B) : Polynomial F) with hc
  have hcomb : ∀ j, c j = ∑ i, U i j • ((bas i : B) : Polynomial F) := by
    intro j
    have h1 : ∑ i, U i j • bas i = cb j :=
      Module.Basis.sum_toMatrix_smul_self bas (⇑cb) j
    have h2 : B.subtype (∑ i, U i j • bas i) = B.subtype (cb j) := by rw [h1]
    rw [map_sum] at h2
    simp only [map_smul, Submodule.coe_subtype] at h2
    exact h2.symm
  have hdetU : U.det ≠ 0 := by
    have h := congrArg Matrix.det (Module.Basis.toMatrix_mul_toMatrix_flip bas cb)
    rw [Matrix.det_mul, Matrix.det_one] at h
    intro h0
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  have hW := foldedWronskian_of_linearComb (ω := ω) (fun j => ((bas j : B) : Polynomial F)) c U
    hcomb
  set T : Finset (Fin σ) := Finset.image (Fin.castLE hts) Finset.univ with hT
  have hTcard : T.card = t := by
    rw [hT, Finset.card_image_of_injective _ (fun a b hab => Fin.ext (by
      simpa using congrArg Fin.val hab)), Finset.card_univ, Fintype.card_fin]
  have hdvd : (Polynomial.X - Polynomial.C p) ^ t ∣ Polynomial.foldedWronskian σ ω c := by
    rw [← hTcard]
    refine Matrix.pow_dvd_det_of_forall_mem_col_dvd _ _ T ?_
    intro j hj i
    obtain ⟨j', -, rfl⟩ := Finset.mem_image.mp hj
    have hjlt : ((Fin.castLE hts j' : Fin σ) : ℕ) < Module.finrank F N' := by
      rw [hrkN']; simp
    exact hcol _ (by simpa [hc, hN'] using hcb _ hjlt) i
  rw [hW] at hdvd
  exact (IsUnit.dvd_mul_right (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hdetU))).mp hdvd

/-- If every polynomial in a subspace `N ≤ B` has a root of multiplicity at least `s` at
`p`, then the classical Wronskian of a `σ`-element basis of `B` has a root at `p` of
multiplicity at least `(s - σ + 1) * dim N`.

After changing to a basis adapted to `N`, the entries in each of the `dim N` distinguished
columns are iterated derivatives, hence divisible by the common factor
`(X - C p) ^ (s - σ + 1)`; determinant divisibility and the inverse base change conclude. -/
private lemma pow_dvd_classicalWronskian {F : Type*} [Field F] {σ s : ℕ}
    (B : Submodule F (Polynomial F)) (bas : Module.Basis (Fin σ) F B)
    (N : Submodule F (Polynomial F)) (hN : N ≤ B) (p : F) (hσs : σ ≤ s)
    (hcol : ∀ q ∈ N, (Polynomial.X - Polynomial.C p) ^ s ∣ q) :
    (Polynomial.X - Polynomial.C p) ^
        ((s - σ + 1) * Module.finrank F N) ∣
      Polynomial.classicalWronskian σ (fun j => (bas j : Polynomial F)) := by
  classical
  haveI : Module.Finite F B := Module.Finite.of_basis bas
  have hrkB : Module.finrank F B = σ := by
    rw [Module.finrank_eq_card_basis bas, Fintype.card_fin]
  set N' : Submodule F B := N.comap B.subtype with hN'
  have hmap : N'.map B.subtype = N := by
    ext x
    simp only [hN', Submodule.mem_map, Submodule.mem_comap, Submodule.coe_subtype,
      Subtype.exists]
    exact ⟨by rintro ⟨y, hy, hyx, rfl⟩; exact hyx,
      fun hx => ⟨x, hN hx, hx, rfl⟩⟩
  have hrkN' : Module.finrank F N' = Module.finrank F N := by
    rw [← hmap, Submodule.finrank_map_subtype_eq]
  obtain ⟨cb, hcb⟩ := N'.exists_adapted_basis hrkB
  set t := Module.finrank F N with htdef
  have htσ : t ≤ σ := by
    rw [← hrkN', ← hrkB]
    exact Submodule.finrank_le N'
  set U : Matrix (Fin σ) (Fin σ) F := bas.toMatrix (⇑cb) with hU
  set c : Fin σ → Polynomial F := fun j => ((cb j : B) : Polynomial F) with hc
  have hcomb : ∀ j, c j = ∑ i, U i j • ((bas i : B) : Polynomial F) := by
    intro j
    have h1 : ∑ i, U i j • bas i = cb j :=
      Module.Basis.sum_toMatrix_smul_self bas (⇑cb) j
    have h2 : B.subtype (∑ i, U i j • bas i) = B.subtype (cb j) := by rw [h1]
    rw [map_sum] at h2
    simp only [map_smul, Submodule.coe_subtype] at h2
    exact h2.symm
  have hdetU : U.det ≠ 0 := by
    have h := congrArg Matrix.det (Module.Basis.toMatrix_mul_toMatrix_flip bas cb)
    rw [Matrix.det_mul, Matrix.det_one] at h
    intro h0
    rw [h0, zero_mul] at h
    exact zero_ne_one h
  have hW := Polynomial.classicalWronskian_of_linearComb
    (fun j => ((bas j : B) : Polynomial F)) c U hcomb
  set T : Finset (Fin σ) := Finset.image (Fin.castLE htσ) Finset.univ with hT
  have hTcard : T.card = t := by
    rw [hT, Finset.card_image_of_injective _ (fun a b hab => Fin.ext (by
      simpa using congrArg Fin.val hab)), Finset.card_univ, Fintype.card_fin]
  have hdvd : (Polynomial.X - Polynomial.C p) ^ ((s - σ + 1) * t) ∣
      Polynomial.classicalWronskian σ c := by
    have hdetdvd := Matrix.pow_dvd_det_of_forall_mem_col_dvd
      (Matrix.of fun i j : Fin σ => Polynomial.derivative^[i.val] (c j))
      ((Polynomial.X - Polynomial.C p) ^ (s - σ + 1)) T (by
        intro j hj i
        obtain ⟨j', -, rfl⟩ := Finset.mem_image.mp hj
        have hjlt : ((Fin.castLE htσ j' : Fin σ) : ℕ) < Module.finrank F N' := by
          rw [hrkN']; simp
        have hcN : c (Fin.castLE htσ j') ∈ N := by
          simpa [hc, hN'] using hcb _ hjlt
        have hder := Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd
          i.val (hcol _ hcN)
        exact (pow_dvd_pow (Polynomial.X - Polynomial.C p) (by omega)).trans hder)
    simpa [Polynomial.classicalWronskian, hTcard, pow_mul] using hdetdvd
  rw [hW] at hdvd
  exact (IsUnit.dvd_mul_right
    (Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hdetU))).mp hdvd

/-- Folded Reed-Solomon codes are subspace designs for the profile

  `τ r = s * ρ / (s - r + 1)` for `1 ≤ r ≤ s`, and `τ r = 1` otherwise,

where `ρ` is the alphabet-normalized rate `LinearCode.alphabetRate (frsCode domain k s ω)`.
Note `τ 1 = ρ` and `τ s = s * ρ`.

Since `dim (frsCode domain k s ω) = min k (s * n)`, the profile reads
`τ r = (k / n) / (s - r + 1)` in the intended regime `k ≤ s * n`. Beyond it the rate
saturates at `ρ = 1`, and the statement becomes vacuous: a profile that is at least `1`
throughout `[1, s]` is a design profile for every code.

Both hypotheses on `ω` are necessary.

* `hω_gen`, that `ω` generates `Fˣ`, is used once, through
  `Polynomial.foldedWronskian_ne_zero_of_linearIndependent`. Without an order condition the
  statement fails: over `𝔽₁₀₁` with `s = 2`, `ω = -1`, `k = 3` and evaluation points
  `{1, …, 7}`, admissibility still holds, but the encodings of `1` and `X²` span a subspace
  with `∑ i, dim Aᵢ = 7 > 6 = dim A * τ 2 * n`, since `(-x)² = x²`.
* Admissibility of `ω` is used to make `(i, m) ↦ domain i * ω ^ m` injective. Its
  intra-orbit clause `α * ω ^ i ≠ α` for `0 < i < s` forces `0 ∉ L` once `s ≥ 2`, and this
  is needed even under `hω_gen`: over `ZMod 5` with `domain = (0, 1)`, `s = 3`, `k = 2`,
  `ω = 2`, the `s`-orbit of `0` collapses to `{0}`, so the encoding of `X` spans a subspace
  with `(∑ i, dim Aᵢ) / n = 1/2 > 1/3 = dim A * τ 1`.

Admissibility is hypothesised at the canonical point set `Finset.univ.map domain`, as in
the other `frsCode` statements; restrict it from a larger ambient point set with
`ReedSolomon.Folded.Admissible.subset`.

The proof is a Wronskian root count. Outside the main regime the bound is bookkeeping:
every block dimension is at most `σ := dim A`, which settles `σ = 0` and `τ r ≥ 1`. In the
remaining regime `1 ≤ r ≤ s` and `k < n * (s - r + 1)`, so the `n * s` folded evaluation
points are distinct and nonzero, the encoder is injective on `degreeLT F k`, and `A`
together with each `A ⊓ ker (proj i)` lifts to message-side subspaces `B` and `Nᵢ ≤ B` of
the same dimension, the latter consisting of polynomials vanishing on the whole orbit
`{domain i * ω ^ j | j < s}`. The `ω`-folded Wronskian `W` of a basis of `B` is nonzero and
has `deg W ≤ σ * (k - 1)`, while each of the `n * (s - σ + 1)` distinct points
`domain i * ω ^ m` with `m ≤ s - σ` is a root of `W` of multiplicity at least `dim Nᵢ`.
Comparing the two gives `(s - σ + 1) * ∑ i, dim (A ⊓ ker (proj i)) ≤ σ * (k - 1)`, and
`σ ≤ r` turns this into the design bound. -/
theorem isSubspaceDesign_frsCode_sub_one
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {F : Type*} [Field F] [Fintype F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hFn : Fintype.card ι < Fintype.card F)
    (hω_adm : ReedSolomon.Folded.Admissible (Finset.univ.map domain) s ω)
    (hω_gen : orderOf ω = Fintype.card F - 1) :
    let τ : ℕ → ℝ := fun r ↦
      if r ∈ Finset.Icc 1 s then
        (s * (LinearCode.alphabetRate (ReedSolomon.Folded.frsCode domain k s ω) : ℝ)
            - 1 / Fintype.card ι) /
          (s - r + 1)
      else 1
    IsSubspaceDesign s τ (ReedSolomon.Folded.frsCode domain k s ω) := by
  classical
  intro τ r A hAC hAr
  have hτdef : ∀ x : ℕ, τ x =
      if x ∈ Finset.Icc 1 s then
        (s * (LinearCode.alphabetRate (ReedSolomon.Folded.frsCode domain k s ω) : ℝ)
            - 1 / Fintype.card ι) /
          (s - x + 1)
      else 1 := fun _ => rfl
  have hn_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hω0 : ω ≠ 0 := by
    intro hzero
    rw [hzero, orderOf_zero] at hω_gen
    have hcard2 : 2 ≤ Fintype.card F := by
      have hn1 : 1 ≤ Fintype.card ι := Fintype.card_pos
      omega
    omega
  have hadm : ReedSolomon.Folded.Admissible (Finset.univ.map domain) s ω := hω_adm
  set σ := Module.finrank F ↥A with hσdef
  -- Every block dimension is at most `σ`, hence the design sum is at most `σ`.
  have hsum_le : (∑ i : ι, (Module.finrank F ↥(A ⊓
      (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))) : ℝ)) /
        Fintype.card ι ≤ σ := by
    rw [div_le_iff₀ hn_pos]
    calc (∑ i : ι, (Module.finrank F ↥(A ⊓
            (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))) : ℝ))
        ≤ ∑ _i : ι, (σ : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact_mod_cast Submodule.finrank_mono (inf_le_left : A ⊓ _ ≤ A)
      _ = σ * Fintype.card ι := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  -- Trivial branch 0: `A = ⊥`.
  by_cases hσ0 : σ = 0
  · rw [hσ0] at hsum_le ⊢
    simpa using hsum_le
  have hσ1 : 1 ≤ σ := by omega
  -- Outside `[1, s]` the profile is `1`, which `hsum_le` already discharges.
  by_cases hrmem : r ∈ Finset.Icc 1 s
  case neg =>
    rw [hτdef r, if_neg hrmem]
    simpa using hsum_le
  obtain ⟨hr1, hrs⟩ := Finset.mem_Icc.mp hrmem
  have hs_pos : (0 : ℝ) < s := by
    exact_mod_cast (show 0 < s by omega)
  have hσs : σ ≤ s := le_trans hAr hrs
  have hσs_real : (σ : ℝ) ≤ s := by exact_mod_cast hσs
  have hσ1_real : (1 : ℝ) ≤ σ := by exact_mod_cast hσ1
  -- The sharper block count: a nonzero `A` loses a dimension at some block, so the design sum
  -- is at most `n * σ - 1`. This is what the `(k-1)`-level profile needs and the `k`-level one
  -- did not: at `τ r = 1 - 1/(n*s)` the bound `∑ ≤ n * σ` is exactly one too weak.
  have hsum_le' : (∑ i : ι, (Module.finrank F ↥(A ⊓
      (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))) : ℝ)) /
        Fintype.card ι ≤ (σ : ℝ) - 1 / Fintype.card ι := by
    have hA_ne : A ≠ ⊥ := by
      intro h
      exact hσ0 (by rw [hσdef, h]; exact finrank_bot F _)
    have hnat := sum_finrank_inf_ker_le A hA_ne
    have hcast : (∑ i : ι, (Module.finrank F ↥(A ⊓
        (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))) : ℝ)) + 1
        ≤ (Fintype.card ι : ℝ) * σ := by
      rw [← Nat.cast_sum]
      exact_mod_cast hnat
    rw [div_le_iff₀ hn_pos, sub_mul, div_mul_cancel₀ _ (ne_of_gt hn_pos)]
    linarith
  -- Near-saturation escape: for `τ r ≥ 1 - 1/(n*s)` the sharper count already suffices.
  by_cases hτnear : 1 - 1 / ((Fintype.card ι : ℝ) * s) ≤ τ r
  case pos =>
    refine hsum_le'.trans (le_trans ?_ (mul_le_mul_of_nonneg_left hτnear (by positivity)))
    rw [mul_sub, mul_one]
    have hkey : (σ : ℝ) * (1 / ((Fintype.card ι : ℝ) * s)) ≤ 1 / Fintype.card ι := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) hn_pos]
      nlinarith
    linarith
  rw [not_le] at hτnear
  have hτ1 : τ r < 1 := by
    have : (0 : ℝ) < 1 / ((Fintype.card ι : ℝ) * s) := by positivity
    linarith
  have hτrate : τ r =
      ((s : ℝ) * (LinearCode.alphabetRate (ReedSolomon.Folded.frsCode domain k s ω) : ℝ)
          - 1 / Fintype.card ι) /
        ((s : ℝ) - r + 1) := by
    rw [hτdef r, if_pos hrmem]
  have hb_pos : (0 : ℝ) < (s : ℝ) - r + 1 := by
    have : (r : ℝ) ≤ s := by exact_mod_cast hrs
    linarith
  have hcast_b : (((s - r + 1 : ℕ)) : ℝ) = (s : ℝ) - r + 1 := by
    push_cast [Nat.cast_sub hrs]; ring
  have hk_le : k ≤ s * Fintype.card ι := by
    by_contra hk
    have hdim : Module.finrank F (ReedSolomon.Folded.frsCode domain k s ω) =
        s * Fintype.card ι := by
      rw [ReedSolomon.Folded.dim_frsCode_eq_min domain k s ω hadm hω0,
        min_eq_right (by omega)]
    have hrate :
        (LinearCode.alphabetRate (ReedSolomon.Folded.frsCode domain k s ω) : ℝ) = 1 := by
      rw [LinearCode.alphabetRate_cast_eq, hdim]
      rw [Nat.cast_mul]
      exact div_self (mul_ne_zero (ne_of_gt hs_pos) (ne_of_gt hn_pos))
    -- At saturation the sharp profile is still at least `1 - 1/(n*s)`, since `s - r + 1 ≤ s`,
    -- so the near-saturation escape above would already have fired.
    rw [hτrate, hrate] at hτnear
    have hden_le : (s : ℝ) - r + 1 ≤ s := by
      have : (1 : ℝ) ≤ r := by exact_mod_cast hr1
      linarith
    have hfac_nonneg : (0 : ℝ) ≤ 1 - 1 / ((Fintype.card ι : ℝ) * s) := by
      have hn1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
      have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
      rw [sub_nonneg, div_le_one (by positivity)]
      nlinarith
    have hid : (1 - 1 / ((Fintype.card ι : ℝ) * s)) * s
        = (s : ℝ) - 1 / Fintype.card ι := by
      field_simp
    rw [div_lt_iff₀ hb_pos] at hτnear
    nlinarith [mul_le_mul_of_nonneg_left hden_le hfac_nonneg]
  have hdim : Module.finrank F (ReedSolomon.Folded.frsCode domain k s ω) = k :=
    ReedSolomon.Folded.dim_frsCode domain k s ω hadm hω0 hk_le
  have hτval : τ r = ((k : ℝ) - 1) / Fintype.card ι / ((s : ℝ) - r + 1) := by
    rw [hτrate, ReedSolomon.Folded.alphabetRate_frsCode domain k s ω hadm hω0 hk_le]
    field_simp [ne_of_gt hs_pos]
  have hpt_inj := ReedSolomon.Folded.admissible_foldedPoints_injective domain ω hadm hω0
  -- `k ≥ 1` (otherwise `frsCode = ⊥` and `σ = 0`).
  have hk1 : 1 ≤ k := by
    by_contra h
    refine hσ0 ?_
    have hk0 : k = 0 := by omega
    have hAbot : A = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      obtain ⟨p, hp, hpa⟩ := (ReedSolomon.Folded.mem_frsCode_iff _ _ _ _ _).mp (hAC ha)
      rw [hk0, Polynomial.degreeLT_zero, Submodule.mem_bot] at hp
      rw [Submodule.mem_bot]
      ext x j
      rw [hpa x j, hp]
      simp
    rw [hσdef, hAbot]
    exact finrank_bot F _
  haveI : NeZero k := ⟨by omega⟩
  -- `k ≤ q − 1`: the `n·s` folded points are distinct and nonzero (for `s ≥ 2`);
  -- for `s = 1` this is `hFn` directly.
  have hns_q : Fintype.card ι * s ≤ Fintype.card F - 1 := by
    rcases Nat.lt_or_ge s 2 with hs2 | hs2
    · have hs1 : s = 1 := by omega
      rw [hs1, Nat.mul_one]
      omega
    · have hzero : ∀ x : ι, domain x ≠ 0 := by
        intro x hx
        -- The two side conditions of the intra-orbit clause are `0 < 1` and `1 < s`;
        -- both are discharged by `omega`, so this is insensitive to their order.
        exact hω_adm.2 (domain x) (Finset.mem_map_of_mem _ (Finset.mem_univ x)) 1
          (by omega) (by omega) (by rw [hx]; ring)
      have himg : (Finset.univ : Finset (ι × Fin s)).image
          (fun xi => domain xi.1 * ω ^ (xi.2 : ℕ)) ⊆ Finset.univ.erase 0 := by
        intro y hy
        obtain ⟨xi, -, rfl⟩ := Finset.mem_image.mp hy
        exact Finset.mem_erase.mpr ⟨mul_ne_zero (hzero _) (pow_ne_zero _ hω0),
          Finset.mem_univ _⟩
      have hcard := Finset.card_le_card himg
      rw [Finset.card_image_of_injective _ hpt_inj, Finset.card_univ, Fintype.card_prod,
        Fintype.card_fin, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
        at hcard
      exact hcard
  have hk_ns : k ≤ Fintype.card ι * s := by rw [Nat.mul_comm]; exact hk_le
  have hkq : k ≤ Fintype.card F - 1 := by omega
  -- The FRS encoder and its injectivity on `degreeLT F k`.
  set enc := ReedSolomon.Folded.frsEvalOnPoints domain s ω with henc
  have hencinj := ReedSolomon.Folded.frsEvalOnPoints_domRestrict_injective
    (k := k) (s := s) domain ω hadm hω0 hk_le
  have hker : ∀ p ∈ Polynomial.degreeLT F k, enc p = 0 → p = 0 := by
    intro p hp hp0
    have h : (⟨p, hp⟩ : ↥(Polynomial.degreeLT F k)) = 0 := by
      apply hencinj
      simp only [LinearMap.domRestrict_apply, map_zero]
      exact hp0
    exact congrArg Subtype.val h
  -- The message-side lift `B` of `A`.
  set B : Submodule F (Polynomial F) :=
    Polynomial.degreeLT F k ⊓ Submodule.comap enc A with hBdef
  have hBmem : ∀ p : Polynomial F, p ∈ B ↔ (p ∈ Polynomial.degreeLT F k ∧ enc p ∈ A) := by
    intro p
    simp only [hBdef, Submodule.mem_inf, Submodule.mem_comap]
  have hBmap : Submodule.map enc B = A := by
    ext a
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ((hBmem p).mp hp).2
    · intro ha
      have haC := hAC ha
      rw [ReedSolomon.Folded.frsCode, ← henc, Submodule.mem_map] at haC
      obtain ⟨p, hp, hpa⟩ := haC
      exact ⟨p, (hBmem p).mpr ⟨hp, by rw [hpa]; exact ha⟩, hpa⟩
  have hrkB : Module.finrank F ↥B = σ := by
    rw [hσdef]
    exact LinearMap.finrank_eq_of_map_eq enc B A
      (fun p hp h0 => hker p ((hBmem p).mp hp).1 h0) hBmap
  haveI : FiniteDimensional F ↥(Polynomial.degreeLT F k) :=
    FiniteDimensional.of_injective (Polynomial.degreeLTEquiv F k).toLinearMap
      (Polynomial.degreeLTEquiv F k).injective
  haveI : FiniteDimensional F ↥B := Submodule.finiteDimensional_of_le
      (S₂ := Polynomial.degreeLT F k) (by rw [hBdef]; exact inf_le_left)
  -- A basis of `B`, viewed as a family of low-degree polynomials.
  set bas : Module.Basis (Fin σ) F ↥B := (Module.finBasis F ↥B).reindex (finCongr hrkB) with hbas
  set P : Fin σ → Polynomial F := fun j => ((bas j : ↥B) : Polynomial F) with hPdef
  have hPdeg : ∀ j, P j ∈ Polynomial.degreeLT F k := fun j => ((hBmem _).mp (bas j).2).1
  have hPind : LinearIndependent F P :=
    bas.linearIndependent.map' B.subtype (Submodule.ker_subtype B)
  -- The folded Wronskian of that basis.
  set W := Polynomial.foldedWronskian σ ω P with hWdef
  have hWne : W ≠ 0 :=
    Polynomial.foldedWronskian_ne_zero_of_linearIndependent hω_gen hkq P hPdeg hPind
  have hWdegle : W.natDegree ≤ σ * (k - 1) :=
    Polynomial.natDegree_foldedWronskian_le σ ω P (k - 1) (fun j => by
      have := ReedSolomon.natDegree_lt_of_mem_degreeLT (hPdeg j)
      omega)
  -- The message-side lift of the block subspaces `A ⊓ ker (proj i)`.
  set N : ι → Submodule F (Polynomial F) := fun i =>
    B ⊓ Submodule.comap enc
      (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) with hNdef
  have hNle : ∀ i, N i ≤ B := fun i => inf_le_left
  have hNmem : ∀ (i : ι) (p : Polynomial F), p ∈ N i ↔
      (p ∈ B ∧ ∀ j : Fin s, p.eval (domain i * ω ^ (j : ℕ)) = 0) := by
    intro i p
    constructor
    · intro hp
      obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hp
      exact ⟨h1, fun j => congrFun (LinearMap.mem_ker.mp (Submodule.mem_comap.mp h2)) j⟩
    · rintro ⟨h1, h2⟩
      refine Submodule.mem_inf.mpr ⟨h1, Submodule.mem_comap.mpr (LinearMap.mem_ker.mpr ?_)⟩
      funext j
      exact h2 j
  have hNmap : ∀ i : ι, Submodule.map enc (N i) =
      A ⊓ (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) := by
    intro i
    ext a
    simp only [Submodule.mem_map, Submodule.mem_inf]
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hp
      exact ⟨((hBmem p).mp h1).2, Submodule.mem_comap.mp h2⟩
    · rintro ⟨haA, hak⟩
      rw [← hBmap] at haA
      obtain ⟨p, hpB, hpa⟩ := Submodule.mem_map.mp haA
      exact ⟨p, Submodule.mem_inf.mpr ⟨hpB, Submodule.mem_comap.mpr (by rw [hpa]; exact hak)⟩, hpa⟩
  have hNrk : ∀ i : ι, Module.finrank F ↥(N i) = Module.finrank F ↥(A ⊓
      (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))) :=
    fun i => LinearMap.finrank_eq_of_map_eq enc (N i) _
      (fun p hp h0 => hker p ((hBmem p).mp ((hNmem i p).mp hp).1).1 h0) (hNmap i)
  -- Each block contributes a root of multiplicity `≥ dim` at each of `s − σ + 1` points.
  have hmult : ∀ (i : ι) (m : ℕ), m < s - σ + 1 →
      (Polynomial.X - Polynomial.C (domain i * ω ^ m)) ^ (Module.finrank F ↥(A ⊓
        (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)))) ∣ W := by
    intro i m hm
    rw [← hNrk i, hWdef]
    refine pow_dvd_foldedWronskian B bas (N i) (hNle i) _ ?_
    intro Q hQ i'
    rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def, Polynomial.eval_comp]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    have hidx : (i' : ℕ) + m < s := by have := i'.isLt; omega
    have hv := ((hNmem i Q).mp hQ).2 ⟨(i' : ℕ) + m, hidx⟩
    rw [show ω ^ ((i' : ℕ)) * (domain i * ω ^ m) = domain i * ω ^ ((i' : ℕ) + m) by
      rw [pow_add]; ring]
    exact hv
  -- Count: the `n(s − σ + 1)` distinct roots against `deg W ≤ σ(k − 1)`.
  set T : Finset (ι × ℕ) := Finset.univ ×ˢ Finset.range (s - σ + 1) with hTdef
  have hTmem : ∀ x ∈ T, x.2 < s - σ + 1 := by
    intro x hx
    exact Finset.mem_range.mp (Finset.mem_product.mp hx).2
  have hfinj : Set.InjOn (fun x : ι × ℕ => domain x.1 * ω ^ x.2) ↑T := by
    rintro ⟨a, m⟩ ha ⟨b, m'⟩ hb hab
    have hm := hTmem (a, m) (Finset.mem_coe.mp ha)
    have hm' := hTmem (b, m') (Finset.mem_coe.mp hb)
    have hms : m < s := by simp only at hm; omega
    have hms' : m' < s := by simp only at hm'; omega
    have h := hpt_inj (a₁ := (a, (⟨m, hms⟩ : Fin s))) (a₂ := (b, (⟨m', hms'⟩ : Fin s)))
      (by simpa using hab)
    simp only [Prod.mk.injEq, Fin.mk.injEq] at h
    exact Prod.ext h.1 h.2
  have hcount : ∑ x ∈ T, Module.finrank F ↥(A ⊓
      (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) x.1))) ≤
      W.natDegree := by
    calc ∑ x ∈ T, Module.finrank F ↥(A ⊓
          (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) x.1)))
        ≤ ∑ x ∈ T, W.rootMultiplicity (domain x.1 * ω ^ x.2) := by
          refine Finset.sum_le_sum fun x hx => ?_
          exact (Polynomial.le_rootMultiplicity_iff hWne).mpr (hmult x.1 x.2 (hTmem x hx))
      _ = ∑ a ∈ T.image (fun x : ι × ℕ => domain x.1 * ω ^ x.2), W.rootMultiplicity a :=
          (Finset.sum_image (f := fun a : F => W.rootMultiplicity a)
            (g := fun x : ι × ℕ => domain x.1 * ω ^ x.2) (s := T) hfinj).symm
      _ ≤ W.natDegree := Polynomial.sum_rootMultiplicity_le_natDegree _
  have hprod : ∑ x ∈ T, Module.finrank F ↥(A ⊓
      (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) x.1))) =
      (s - σ + 1) * ∑ i : ι, Module.finrank F ↥(A ⊓
        (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))) := by
    rw [hTdef, Finset.sum_product, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    change (∑ _y ∈ Finset.range (s - σ + 1), Module.finrank F ↥(A ⊓
        (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)))) = _
    rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hS_nat : (s - σ + 1) * ∑ i : ι, Module.finrank F ↥(A ⊓
      (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))) ≤
      σ * (k - 1) := by
    rw [← hprod]
    exact le_trans hcount hWdegle
  -- Real-arithmetic chain (as in `subspaceDesign_tau_lower`, Steps 6–7).
  set S : ℝ := ∑ i : ι, (Module.finrank F ↥(A ⊓
    (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))) : ℝ) with hSdef
  have hcast_a : (((s - σ + 1 : ℕ)) : ℝ) = (s : ℝ) - σ + 1 := by
    push_cast [Nat.cast_sub hσs]; ring
  have hcast_k : (((k - 1 : ℕ)) : ℝ) = (k : ℝ) - 1 := by
    push_cast [Nat.cast_sub hk1]; ring
  have hS_real : ((s : ℝ) - σ + 1) * S ≤ σ * ((k : ℝ) - 1) := by
    have h2 : (((s - σ + 1 : ℕ)) : ℝ) * ((∑ i : ι, Module.finrank F ↥(A ⊓
        (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))) : ℕ) : ℝ)
        ≤ (σ : ℝ) * (((k - 1 : ℕ)) : ℝ) := by exact_mod_cast hS_nat
    rw [hcast_a, hcast_k, Nat.cast_sum] at h2
    exact h2
  have hS_nonneg : (0 : ℝ) ≤ S := Finset.sum_nonneg fun i _ => by positivity
  have hσr : (σ : ℝ) ≤ r := by exact_mod_cast hAr
  have hSb : S * ((s : ℝ) - r + 1) ≤ σ * ((k : ℝ) - 1) := by
    have h1 : S * ((s : ℝ) - r + 1) ≤ S * ((s : ℝ) - σ + 1) := by nlinarith
    have h2 : (0 : ℝ) ≤ σ := by positivity
    nlinarith
  rw [hτval, div_le_iff₀ hn_pos]
  have hrw : (σ : ℝ) * (((k : ℝ) - 1) / Fintype.card ι / ((s : ℝ) - r + 1)) * Fintype.card ι
      = σ * ((k : ℝ) - 1) / ((s : ℝ) - r + 1) := by
    field_simp
  rw [hrw, le_div_iff₀ hb_pos]
  exact hSb

/-- Folded Reed-Solomon codes are subspace designs for [ABF26] Theorem 2.18's printed profile

  `τ r = s * ρ / (s - r + 1)` for `1 ≤ r ≤ s`, and `τ r = 1` otherwise.

This is the `1/n`-relaxation of `isSubspaceDesign_frsCode_sub_one`, which is what the Wronskian
count actually proves. **Consumers proving list-decodability up to capacity need the sharp
version**: [CZ25, Theorem B.5] assumes the design property at the `(k-1)` level and its proof
derives a contradiction from a design sum of exactly `ℓk/(s-ℓ+1)`, so at this profile there is no
contradiction to derive — see `CodingTheory.subspaceDesign_lambda_le`. -/
theorem isSubspaceDesign_frsCode
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {F : Type*} [Field F] [Fintype F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (hFn : Fintype.card ι < Fintype.card F)
    (hω_adm : ReedSolomon.Folded.Admissible (Finset.univ.map domain) s ω)
    (hω_gen : orderOf ω = Fintype.card F - 1) :
    let τ : ℕ → ℝ := fun r ↦
      if r ∈ Finset.Icc 1 s then
        s * (LinearCode.alphabetRate (ReedSolomon.Folded.frsCode domain k s ω) : ℝ) /
          (s - r + 1)
      else 1
    IsSubspaceDesign s τ (ReedSolomon.Folded.frsCode domain k s ω) := by
  intro τ
  have hτdef : ∀ x : ℕ, τ x =
      if x ∈ Finset.Icc 1 s then
        s * (LinearCode.alphabetRate (ReedSolomon.Folded.frsCode domain k s ω) : ℝ) /
          (s - x + 1)
      else 1 := fun _ => rfl
  refine (isSubspaceDesign_frsCode_sub_one domain k s ω hFn hω_adm hω_gen).mono_tau fun r => ?_
  rw [hτdef r]
  by_cases hr : r ∈ Finset.Icc 1 s
  · simp only [hr, if_true]
    have hb_pos : (0 : ℝ) < (s : ℝ) - r + 1 := by
      have : (r : ℝ) ≤ s := by exact_mod_cast (Finset.mem_Icc.mp hr).2
      linarith
    have hn_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    rw [sub_div]
    have hdrop : (0 : ℝ) ≤ (1 / (Fintype.card ι : ℝ)) / ((s : ℝ) - r + 1) := by positivity
    linarith
  · simp [hr]

/-- Univariate multiplicity codes are subspace designs for the profile

  `τ r = s * ρ / (s - r + 1)` for `1 ≤ r ≤ s`, and `τ r = 1` otherwise,

where `ρ` is the alphabet-normalized rate `LinearCode.alphabetRate (umCode domain k s)`.

As in `isSubspaceDesign_frsCode`, `dim (umCode domain k s) = min k (s * n)`, so the
statement stays exact in the saturated regime `k > s * n`, where `ρ = 1` makes it vacuous.

The characteristic hypothesis is what makes `d !` a unit for every `d < k`, so that the
classical Wronskian of a basis of a space of polynomials of degree `< k` is nonzero. It is
phrased as the disjunction `ringChar F = 0 ∨ k ≤ ringChar F` so that characteristic zero,
where the argument is unchanged, is not excluded by `ringChar F = 0` forcing `k = 0`.

No relation between `s` and `k` is needed: if `s > k` then every polynomial of degree `< k`
with a root of multiplicity at least `s` is zero, so every lifted block kernel is `⊥` and
the design sum vanishes.

This is the `(k-1)`-level profile of [CZ25, Definition B.2] — one notch sharper than [ABF26]
Theorem 2.18's printed `s * ρ / (s - r + 1)`, which `isSubspaceDesign_umCode` derives from it
by `mono_tau`. The Wronskian root count below produces the sharp bound directly, and
[CZ25, Theorem B.5] needs exactly it: see `CodingTheory.subspaceDesign_lambda_le`, which is
false at the relaxed level.

The proof lifts a test subspace and each of its block kernels through the injective
multiplicity encoder. The classical Wronskian `W` of a basis of the resulting polynomial
space is nonzero, and a lifted block kernel of dimension `t` contributes a root of `W` at
its block point of multiplicity at least `(s - σ + 1) * t`, by
`pow_dvd_classicalWronskian`. Summing over the distinct evaluation points and comparing
with `deg W ≤ σ * (k - 1)` gives the design bound. -/
theorem isSubspaceDesign_umCode_sub_one
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ) (hchar : ringChar F = 0 ∨ k ≤ ringChar F) :
    let τ : ℕ → ℝ := fun r ↦
      if r ∈ Finset.Icc 1 s then
        (s * (LinearCode.alphabetRate
          (ReedSolomon.Multiplicity.umCode domain k s) : ℝ) - 1 / Fintype.card ι) / (s - r + 1)
      else 1
    IsSubspaceDesign s τ (ReedSolomon.Multiplicity.umCode domain k s) := by
  classical
  intro τ r A hAC hAr
  have hτdef : ∀ x : ℕ, τ x =
      if x ∈ Finset.Icc 1 s then
        (s * (LinearCode.alphabetRate
          (ReedSolomon.Multiplicity.umCode domain k s) : ℝ) - 1 / Fintype.card ι) / (s - x + 1)
      else 1 := fun _ => rfl
  have hn_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  set σ := Module.finrank F ↥A with hσdef
  have hsum_le : (∑ i : ι, (Module.finrank F ↥(A ⊓
      (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))) : ℝ)) /
        Fintype.card ι ≤ σ := by
    rw [div_le_iff₀ hn_pos]
    calc (∑ i : ι, (Module.finrank F ↥(A ⊓
            (LinearMap.ker (LinearMap.proj (R := F)
              (φ := fun _ : ι ↦ Fin s → F) i))) : ℝ))
        ≤ ∑ _i : ι, (σ : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          exact_mod_cast Submodule.finrank_mono (inf_le_left : A ⊓ _ ≤ A)
      _ = σ * Fintype.card ι := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]
  by_cases hσ0 : σ = 0
  · rw [hσ0] at hsum_le ⊢
    simpa using hsum_le
  have hσ1 : 1 ≤ σ := by omega
  -- Outside `[1, s]` the profile is `1`, which `hsum_le` already discharges.
  by_cases hrmem : r ∈ Finset.Icc 1 s
  case neg =>
    rw [hτdef r, if_neg hrmem]
    simpa using hsum_le
  obtain ⟨hr1, hrs⟩ := Finset.mem_Icc.mp hrmem
  have hs_pos : (0 : ℝ) < s := by
    exact_mod_cast (show 0 < s by omega)
  have hσs : σ ≤ s := le_trans hAr hrs
  have hσs_real : (σ : ℝ) ≤ s := by exact_mod_cast hσs
  have hσ1_real : (1 : ℝ) ≤ σ := by exact_mod_cast hσ1
  -- The sharper block count: a nonzero `A` loses a dimension at some block.
  have hsum_le' : (∑ i : ι, (Module.finrank F ↥(A ⊓
      (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))) : ℝ)) /
        Fintype.card ι ≤ (σ : ℝ) - 1 / Fintype.card ι := by
    have hA_ne : A ≠ ⊥ := by
      intro h
      exact hσ0 (by rw [hσdef, h]; exact finrank_bot F _)
    have hnat := sum_finrank_inf_ker_le A hA_ne
    have hcast : (∑ i : ι, (Module.finrank F ↥(A ⊓
        (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i))) : ℝ)) + 1
        ≤ (Fintype.card ι : ℝ) * σ := by
      rw [← Nat.cast_sum]
      exact_mod_cast hnat
    rw [div_le_iff₀ hn_pos, sub_mul, div_mul_cancel₀ _ (ne_of_gt hn_pos)]
    linarith
  -- Near-saturation escape: for `τ r ≥ 1 - 1/(n*s)` the sharper count already suffices.
  by_cases hτnear : 1 - 1 / ((Fintype.card ι : ℝ) * s) ≤ τ r
  case pos =>
    refine hsum_le'.trans (le_trans ?_ (mul_le_mul_of_nonneg_left hτnear (by positivity)))
    rw [mul_sub, mul_one]
    have hkey : (σ : ℝ) * (1 / ((Fintype.card ι : ℝ) * s)) ≤ 1 / Fintype.card ι := by
      rw [mul_one_div, div_le_div_iff₀ (by positivity) hn_pos]
      nlinarith
    linarith
  rw [not_le] at hτnear
  have hτ1 : τ r < 1 := by
    have : (0 : ℝ) < 1 / ((Fintype.card ι : ℝ) * s) := by positivity
    linarith
  have hτrate : τ r =
      ((s : ℝ) * (LinearCode.alphabetRate
        (ReedSolomon.Multiplicity.umCode domain k s) : ℝ) - 1 / Fintype.card ι) /
        ((s : ℝ) - r + 1) := by
    rw [hτdef r, if_pos hrmem]
  have hb_pos : (0 : ℝ) < (s : ℝ) - r + 1 := by
    have : (r : ℝ) ≤ s := by exact_mod_cast hrs
    linarith
  have hk_le : k ≤ s * Fintype.card ι := by
    by_contra hk
    have hdim : Module.finrank F (ReedSolomon.Multiplicity.umCode domain k s) =
        s * Fintype.card ι := by
      rw [ReedSolomon.Multiplicity.dim_umCode_eq_min domain k s hchar,
        min_eq_right (by omega)]
    have hrate :
        (LinearCode.alphabetRate
          (ReedSolomon.Multiplicity.umCode domain k s) : ℝ) = 1 := by
      rw [LinearCode.alphabetRate_cast_eq, hdim]
      rw [Nat.cast_mul]
      exact div_self (mul_ne_zero (ne_of_gt hs_pos) (ne_of_gt hn_pos))
    -- At saturation the sharp profile is still at least `1 - 1/(n*s)`, since `s - r + 1 ≤ s`,
    -- so the near-saturation escape above would already have fired.
    rw [hτrate, hrate] at hτnear
    have hden_le : (s : ℝ) - r + 1 ≤ s := by
      have : (1 : ℝ) ≤ r := by exact_mod_cast hr1
      linarith
    have hfac_nonneg : (0 : ℝ) ≤ 1 - 1 / ((Fintype.card ι : ℝ) * s) := by
      have hn1 : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
      have hs1 : (1 : ℝ) ≤ s := by exact_mod_cast (show 1 ≤ s by omega)
      rw [sub_nonneg, div_le_one (by positivity)]
      nlinarith
    have hid : (1 - 1 / ((Fintype.card ι : ℝ) * s)) * s
        = (s : ℝ) - 1 / Fintype.card ι := by
      field_simp
    rw [div_lt_iff₀ hb_pos] at hτnear
    nlinarith [mul_le_mul_of_nonneg_left hden_le hfac_nonneg]
  have hdim : Module.finrank F (ReedSolomon.Multiplicity.umCode domain k s) = k :=
    ReedSolomon.Multiplicity.dim_umCode domain hchar hk_le
  have hτval : τ r = ((k : ℝ) - 1) / Fintype.card ι / ((s : ℝ) - r + 1) := by
    rw [hτrate, LinearCode.alphabetRate_cast_eq, hdim]
    field_simp [ne_of_gt hs_pos]
  have hk1 : 1 ≤ k := by
    by_contra h
    refine hσ0 ?_
    have hk0 : k = 0 := by omega
    have hAbot : A = ⊥ := by
      rw [eq_bot_iff]
      intro a ha
      have haC := hAC ha
      rw [ReedSolomon.Multiplicity.umCode, Submodule.mem_map] at haC
      obtain ⟨p, hp, hpa⟩ := haC
      rw [hk0, Polynomial.degreeLT_zero, Submodule.mem_bot] at hp
      rw [Submodule.mem_bot, ← hpa, hp, map_zero]
    rw [hσdef, hAbot]
    exact finrank_bot F _
  haveI : NeZero k := ⟨by omega⟩
  set enc := ReedSolomon.Multiplicity.umEvalOnPoints domain s with henc
  have hencinj := ReedSolomon.Multiplicity.umEvalOnPoints_domRestrict_injective
    (k := k) (s := s) domain hchar hk_le
  have hker : ∀ p ∈ Polynomial.degreeLT F k, enc p = 0 → p = 0 := by
    intro p hp hp0
    have h : (⟨p, hp⟩ : ↥(Polynomial.degreeLT F k)) = 0 := by
      apply hencinj
      simp only [LinearMap.domRestrict_apply, map_zero]
      exact hp0
    exact congrArg Subtype.val h
  set B : Submodule F (Polynomial F) :=
    Polynomial.degreeLT F k ⊓ Submodule.comap enc A with hBdef
  have hBmem : ∀ p : Polynomial F, p ∈ B ↔
      (p ∈ Polynomial.degreeLT F k ∧ enc p ∈ A) := by
    intro p
    simp only [hBdef, Submodule.mem_inf, Submodule.mem_comap]
  have hBmap : Submodule.map enc B = A := by
    ext a
    simp only [Submodule.mem_map]
    constructor
    · rintro ⟨p, hp, rfl⟩
      exact ((hBmem p).mp hp).2
    · intro ha
      have haC := hAC ha
      rw [ReedSolomon.Multiplicity.umCode, ← henc, Submodule.mem_map] at haC
      obtain ⟨p, hp, hpa⟩ := haC
      exact ⟨p, (hBmem p).mpr ⟨hp, by rw [hpa]; exact ha⟩, hpa⟩
  have hrkB : Module.finrank F ↥B = σ := by
    rw [hσdef]
    exact LinearMap.finrank_eq_of_map_eq enc B A
      (fun p hp h0 => hker p ((hBmem p).mp hp).1 h0) hBmap
  haveI : FiniteDimensional F ↥(Polynomial.degreeLT F k) :=
    FiniteDimensional.of_injective (Polynomial.degreeLTEquiv F k).toLinearMap
      (Polynomial.degreeLTEquiv F k).injective
  haveI : FiniteDimensional F ↥B := Submodule.finiteDimensional_of_le
      (S₂ := Polynomial.degreeLT F k) (by rw [hBdef]; exact inf_le_left)
  set bas : Module.Basis (Fin σ) F ↥B :=
    (Module.finBasis F ↥B).reindex (finCongr hrkB) with hbas
  set P : Fin σ → Polynomial F := fun j => ((bas j : ↥B) : Polynomial F) with hPdef
  have hPdeg : ∀ j, P j ∈ Polynomial.degreeLT F k :=
    fun j => ((hBmem _).mp (bas j).2).1
  have hPnatDegree : ∀ j, (P j).natDegree < k :=
    fun j => ReedSolomon.natDegree_lt_of_mem_degreeLT (hPdeg j)
  set W := Polynomial.classicalWronskian σ P with hWdef
  have hWne : W ≠ 0 := by
    rw [hWdef, hPdef]
    exact Polynomial.classicalWronskian_ne_zero_of_basis bas
      (fun j => hPnatDegree j) hchar
  have hWdegle : W.natDegree ≤ σ * (k - 1) :=
    Polynomial.natDegree_classicalWronskian_le σ P (k - 1) (fun j => by
      have := hPnatDegree j
      omega)
  set N : ι → Submodule F (Polynomial F) := fun i =>
    B ⊓ Submodule.comap enc
      (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) with hNdef
  have hNle : ∀ i, N i ≤ B := fun i => inf_le_left
  have hNmem : ∀ (i : ι) (p : Polynomial F), p ∈ N i ↔
      (p ∈ B ∧ ∀ j : Fin s, (Polynomial.derivative^[j.val] p).eval (domain i) = 0) := by
    intro i p
    constructor
    · intro hp
      obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hp
      exact ⟨h1, fun j => congrFun (LinearMap.mem_ker.mp (Submodule.mem_comap.mp h2)) j⟩
    · rintro ⟨h1, h2⟩
      refine Submodule.mem_inf.mpr ⟨h1, Submodule.mem_comap.mpr (LinearMap.mem_ker.mpr ?_)⟩
      funext j
      exact h2 j
  have hNmap : ∀ i : ι, Submodule.map enc (N i) =
      A ⊓ (LinearMap.ker
        (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i)) := by
    intro i
    ext a
    simp only [Submodule.mem_map, Submodule.mem_inf]
    constructor
    · rintro ⟨p, hp, rfl⟩
      obtain ⟨h1, h2⟩ := Submodule.mem_inf.mp hp
      exact ⟨((hBmem p).mp h1).2, Submodule.mem_comap.mp h2⟩
    · rintro ⟨haA, hak⟩
      rw [← hBmap] at haA
      obtain ⟨p, hpB, hpa⟩ := Submodule.mem_map.mp haA
      exact ⟨p, Submodule.mem_inf.mpr
        ⟨hpB, Submodule.mem_comap.mpr (by rw [hpa]; exact hak)⟩, hpa⟩
  have hNrk : ∀ i : ι, Module.finrank F ↥(N i) = Module.finrank F ↥(A ⊓
      (LinearMap.ker (LinearMap.proj (R := F)
        (φ := fun _ : ι ↦ Fin s → F) i))) :=
    fun i => LinearMap.finrank_eq_of_map_eq enc (N i) _
      (fun p hp h0 => hker p ((hBmem p).mp ((hNmem i p).mp hp).1).1 h0) (hNmap i)
  have hmult : ∀ i : ι,
      (Polynomial.X - Polynomial.C (domain i)) ^
        ((s - σ + 1) * Module.finrank F ↥(A ⊓
          (LinearMap.ker (LinearMap.proj (R := F)
            (φ := fun _ : ι ↦ Fin s → F) i)))) ∣ W := by
    intro i
    rw [← hNrk i, hWdef]
    refine pow_dvd_classicalWronskian B bas (N i) (hNle i) _ hσs ?_
    intro q hq
    apply ReedSolomon.Multiplicity.pow_dvd_of_eval_iterate_derivative_eq_zero
      ((hBmem q).mp ((hNmem i q).mp hq).1).1 hchar
    exact ((hNmem i q).mp hq).2
  have hcount : ∑ i : ι, (s - σ + 1) * Module.finrank F ↥(A ⊓
      (LinearMap.ker (LinearMap.proj (R := F)
        (φ := fun _ : ι ↦ Fin s → F) i))) ≤ W.natDegree := by
    calc ∑ i : ι, (s - σ + 1) * Module.finrank F ↥(A ⊓
          (LinearMap.ker (LinearMap.proj (R := F)
            (φ := fun _ : ι ↦ Fin s → F) i)))
        ≤ ∑ a ∈ Finset.univ.map domain, W.rootMultiplicity a := by
          rw [Finset.sum_map]
          refine Finset.sum_le_sum fun i _ => ?_
          exact (Polynomial.le_rootMultiplicity_iff hWne).mpr (hmult i)
      _ ≤ W.natDegree := Polynomial.sum_rootMultiplicity_le_natDegree _
  have hS_nat : (s - σ + 1) * ∑ i : ι, Module.finrank F ↥(A ⊓
      (LinearMap.ker (LinearMap.proj (R := F)
        (φ := fun _ : ι ↦ Fin s → F) i))) ≤ σ * (k - 1) := by
    rw [Finset.mul_sum]
    exact hcount.trans hWdegle
  set S : ℝ := ∑ i : ι, (Module.finrank F ↥(A ⊓
    (LinearMap.ker (LinearMap.proj (R := F)
      (φ := fun _ : ι ↦ Fin s → F) i))) : ℝ) with hSdef
  have hcast_a : (((s - σ + 1 : ℕ)) : ℝ) = (s : ℝ) - σ + 1 := by
    push_cast [Nat.cast_sub hσs]; ring
  have hcast_k : (((k - 1 : ℕ)) : ℝ) = (k : ℝ) - 1 := by
    push_cast [Nat.cast_sub hk1]; ring
  have hS_real : ((s : ℝ) - σ + 1) * S ≤ σ * ((k : ℝ) - 1) := by
    have h2 : (((s - σ + 1 : ℕ)) : ℝ) * ((∑ i : ι, Module.finrank F ↥(A ⊓
        (LinearMap.ker (LinearMap.proj (R := F)
          (φ := fun _ : ι ↦ Fin s → F) i))) : ℕ) : ℝ)
        ≤ (σ : ℝ) * (((k - 1 : ℕ)) : ℝ) := by exact_mod_cast hS_nat
    rw [hcast_a, hcast_k, Nat.cast_sum] at h2
    exact h2
  have hS_nonneg : (0 : ℝ) ≤ S := Finset.sum_nonneg fun i _ => by positivity
  have hσr : (σ : ℝ) ≤ r := by exact_mod_cast hAr
  have hSb : S * ((s : ℝ) - r + 1) ≤ σ * ((k : ℝ) - 1) := by
    have h1 : S * ((s : ℝ) - r + 1) ≤ S * ((s : ℝ) - σ + 1) := by nlinarith
    have h2 : (0 : ℝ) ≤ σ := by positivity
    nlinarith
  rw [hτval, div_le_iff₀ hn_pos]
  have hrw : (σ : ℝ) * (((k : ℝ) - 1) / Fintype.card ι / ((s : ℝ) - r + 1)) *
      Fintype.card ι = σ * ((k : ℝ) - 1) / ((s : ℝ) - r + 1) := by
    field_simp
  rw [hrw, le_div_iff₀ hb_pos]
  exact hSb

/-- Univariate multiplicity codes are subspace designs for [ABF26] Theorem 2.18's printed
profile

  `τ r = s * ρ / (s - r + 1)` for `1 ≤ r ≤ s`, and `τ r = 1` otherwise.

This is the `1/n`-relaxation of `isSubspaceDesign_umCode_sub_one`, which is what the Wronskian
count actually proves; consumers proving list-decodability up to capacity need the sharp
version. See `isSubspaceDesign_frsCode` for the folded Reed-Solomon counterpart. -/
theorem isSubspaceDesign_umCode
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {F : Type*} [Field F]
    (domain : ι ↪ F) (k s : ℕ) (hchar : ringChar F = 0 ∨ k ≤ ringChar F) :
    let τ : ℕ → ℝ := fun r ↦
      if r ∈ Finset.Icc 1 s then
        s * (LinearCode.alphabetRate
          (ReedSolomon.Multiplicity.umCode domain k s) : ℝ) / (s - r + 1)
      else 1
    IsSubspaceDesign s τ (ReedSolomon.Multiplicity.umCode domain k s) := by
  intro τ
  have hτdef : ∀ x : ℕ, τ x =
      if x ∈ Finset.Icc 1 s then
        s * (LinearCode.alphabetRate
          (ReedSolomon.Multiplicity.umCode domain k s) : ℝ) / (s - x + 1)
      else 1 := fun _ => rfl
  refine (isSubspaceDesign_umCode_sub_one domain k s hchar).mono_tau fun r => ?_
  rw [hτdef r]
  by_cases hr : r ∈ Finset.Icc 1 s
  · simp only [hr, if_true]
    have hb_pos : (0 : ℝ) < (s : ℝ) - r + 1 := by
      have : (r : ℝ) ≤ s := by exact_mod_cast (Finset.mem_Icc.mp hr).2
      linarith
    have hn_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
    rw [sub_div]
    have hdrop : (0 : ℝ) ≤ (1 / (Fintype.card ι : ℝ)) / ((s : ℝ) - r + 1) := by positivity
    linarith
  · simp [hr]

end CodingTheory
