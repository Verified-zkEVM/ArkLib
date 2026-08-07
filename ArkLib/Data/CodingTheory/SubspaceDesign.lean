/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Folded

/-!
# Subspace-design codes (ABF26 §2.5)

ABF26 Definition 2.16 [GX13]: the τ-subspace-design property for an F-additive code
`C : F^k → (F^s)^n`. Lemma 2.17 [GG25] is **proved in-tree** (via the module-alphabet
Singleton bound `LinearCode.singleton_bound_module`); Theorem 2.18 [GK16] is stated as
an external admit.

## Main definitions

- `CodingTheory.IsSubspaceDesign` — ABF26 Definition 2.16.

## Main statements

- `CodingTheory.ker_proj_eq_vanish_at` — bridge between `ker(proj i)` and `{a | a i = 0}`
  (proved in-tree).
- `CodingTheory.subspaceDesign_tau_lower` — ABF26 Lemma 2.17 [GG25]: τ-subspace-design
  code of rate `ρ` has `min_r τ(r) ≥ ρ - 1/n` (**proved**, sorry-free).
- `CodingTheory.frs_is_subspaceDesign_gk16` — ABF26 Theorem 2.18 [GK16]: folded RS codes
  are τ-subspace-design for explicit τ (external admit; carries GK16's `ω`-generator
  hypothesis that the tex omits; the omission has been reported to the paper's authors —
  see the audit's T2.18 row for the 2026-07-21 correction record).

## Deferred

- Univariate multiplicity codes `UM[F, L, k, s]` are referenced in T2.18 but require a
  separate `D_ux` (derivative-of-x) operation; tracked under ABF26-D2.19 / DA.7.

## References

- [ABF26] Arnon-Boneh-Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026. §2.5 Definition 2.16, Lemma 2.17, Theorem 2.18.
- [GX13] Guruswami-Xing. (Original subspace-design definition.)
- [GG25] Goyal-Guruswami. (Cited for L2.17.)
- [GK16] Guruswami-Kopparty. (Cited for T2.18.)
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal

/-- **ABF26 Definition 2.16 [GX13].** A code `C : F^k → (F^s)^n` (here represented as a
subspace of `(ι → Fin s → F)` over `F`) is **τ-subspace-design** if for every `r ∈ ℕ`
and every F-linear subspace `A` of `C` with `dim A ≤ r`,

  `(Σ_{i ∈ [n]} dim A_i) / n ≤ dim A · τ(r)`

where `A_i := { a ∈ A : a_i = 0^s }` is the subspace of `A` whose codewords vanish at
position `i`. Here `A_i` is realised as `A ⊓ ker(eval_i)`, the intersection of `A`
with the kernel of the linear map evaluating the `i`-th coordinate. -/
def IsSubspaceDesign {ι : Type} [Fintype ι]
    {F : Type} [Field F] (s : ℕ) (τ : ℕ → ℝ)
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

/-- **Bridge: kernel of the `i`-th projection equals the comprehension `{a | a i = 0}`.**

The subspace `A_i := {a ∈ A : a_i = 0^s}` from the paper's `IsSubspaceDesign` definition
is `A ⊓ ker(LinearMap.proj i)`. This lemma confirms the underlying set: a word
`a : ι → Fin s → F` lies in `ker(proj i)` iff `a i = 0`. Combined with `Submodule.inf_*`
this lets downstream proofs rewrite freely between the technical `ker(proj i)` form (used
in the `IsSubspaceDesign` definition for type-class reasons) and the paper's
comprehension form. -/
lemma ker_proj_eq_vanish_at {ι : Type*} {F : Type*} [Semiring F] {s : ℕ} (i : ι) :
    (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) :
        Set (ι → Fin s → F)) =
      {a | a i = 0} := by
  ext a
  simp [LinearMap.mem_ker, LinearMap.proj_apply]

/-- **ABF26 Lemma 2.17 [GG25].** For any τ-subspace-design code of rate `ρ`, the
profile `τ` is lower-bounded by `ρ - 1/n` on the range `r ∈ [s] = {1, …, s}`:

  `min_{r ∈ [s]} τ(r) ≥ ρ - 1/n` .

**Range narrowed vs the sources (2026-07-21 note).** Both the tex
(`lemma:subspace-design-limitation`, `min_{r ∈ ℕ} τ(r)`) and GG25 Lemma 2.16 state the
bound for **all** `r ∈ ℕ`; the restriction to `[s]` here is ours. `r = 0` is genuinely
excluded (see below); `r > s` is dropped only because no in-tree consumer needs it (the
proof below works verbatim for any `r ≥ 1` once `s ≥ 1` is known — the membership
`r ∈ Icc 1 s` supplies both facts here).

**Rate convention.** Per ABF26 Definition 2.5, the rate of a code over alphabet `Σ` is
`log_{|Σ|}|C| / n`; for an `F`-additive code `C ⊆ (F^s)^n` this is
`ρ = dim_F(C) / (s·n)` — the alphabet is `F^s`, so the `finrank` is divided by `s·n`,
**not** by `n`. The subtracted `1/n` term, by contrast, divides by the block length `n`
only (paper: `min_r τ(r) ≥ ρ − 1/n`).

The quantifier is restricted to `r ∈ Finset.Icc 1 s` (a narrowing of the sources' `r ∈ ℕ`
range, per the note above): at `r = 0` the `IsSubspaceDesign` predicate places no
constraint on `τ`, so the bound there is unprovable (`A ≤ C` with
`finrank A ≤ 0` forces `A = ⊥`, making the design inequality `0 ≤ 0 · τ(0)`
trivially satisfied by any `τ(0)` including ones violating the lower bound).

**Non-negative profile (`hτ_nonneg`, 2026-06-10 re-review).** A design profile
is a fraction of a dimension, so `τ ≥ 0` is implicit in the paper. It is
load-bearing here: for the trivial code `C = ⊥` the `IsSubspaceDesign`
inequalities are all `0 ≤ 0`, placing no constraint on `τ`, and a *negative*
profile (e.g. `τ ≡ -1` at `n = 2`) falsified the unguarded bound
(`-1 ≥ 0 - 1/2`). With `τ ≥ 0` the degenerate case is consistent
(`τ r ≥ 0 ≥ 0 - 1/n`).

**Proof** (GG25's argument, uniform in `r`): pick a distance-attaining pair
`u ≠ v ∈ C` and set `a := u − v`, a nonzero codeword with at least `n − d` zero
blocks (`d = Code.dist`). The design inequality at the 1-dimensional subspace
`span {a}` (valid for every `r ≥ 1`) gives `τ(r) ≥ #zero-blocks / n ≥ (n − d)/n`,
and the module-alphabet Singleton bound `LinearCode.singleton_bound_module`
(`k ≤ s(n − d + 1)`) turns this into `τ(r) ≥ ρ − 1/n`. Formerly an external
admit; proved in-tree 2026-08-07. -/
theorem subspaceDesign_tau_lower
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (h_design : IsSubspaceDesign s τ C)
    (hτ_nonneg : ∀ r, 0 ≤ τ r) :
    ∀ r ∈ Finset.Icc 1 s,
      τ r ≥ (Module.finrank F C : ℝ) / (s * Fintype.card ι) - 1 / Fintype.card ι := by
  classical
  intro r hr
  obtain ⟨hr1, hrs⟩ := Finset.mem_Icc.mp hr
  have hn_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hs1 : 1 ≤ s := hr1.trans hrs
  have hs_pos : (0 : ℝ) < s := by exact_mod_cast hs1
  by_cases hC0 : Module.finrank F C = 0
  · -- Degenerate code: the bound is `-1/n ≤ 0 ≤ τ r`.
    rw [hC0]
    have hb : ((0 : ℕ) : ℝ) / (s * Fintype.card ι) - 1 / Fintype.card ι ≤ 0 := by
      simp only [Nat.cast_zero, zero_div, zero_sub]
      exact neg_nonpos.mpr (by positivity)
    exact le_trans hb (hτ_nonneg r)
  · -- Nontrivial code: run the GG25 argument at the span of a distance-attaining word.
    -- Step 1: a distance-attaining pair, hence a nonzero codeword `a` of block-weight ≤ d.
    have hCbot : C ≠ ⊥ := fun h => hC0 (by rw [h]; exact finrank_bot F _)
    obtain ⟨x, hxC, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hCbot
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

/-- **ABF26 Theorem 2.18 [GK16].** Both folded Reed-Solomon codes and univariate
multiplicity codes are τ-subspace-design for an explicit τ:

  `τ(r) := s · ρ / (s - r + 1)` for `r ∈ [s] = {1, …, s}`, and `τ(r) := 1` otherwise.

**Rate convention.** As in L2.17, the FRS code `FRS[F, L, k, s, ω] ⊆ (F^s)^n` has rate
`ρ = k / (s·n)` (alphabet `F^s`, per ABF26 Definition 2.5). Hence the profile simplifies:
`τ(r) = s·ρ/(s - r + 1) = (k/n) / (s - r + 1)`, which is how it is spelled below.

Note: `[s]` in the paper denotes `{1, …, s}` (one-based), which we encode in Lean as
`Finset.Icc 1 s`. With this convention `τ(1) = s·ρ/s = ρ` and `τ(s) = s·ρ`, matching
the paper's boundary values.

The pinned tex (`thm:folded-rs-are-subspace-design`) states `|F| > n` as a shared
precondition for both the FRS and the multiplicity cases; the FRS case additionally
requires `(L, s)`-admissibility of `ω` (with `ω ≠ 0`), while the multiplicity case
additionally requires `char(F) > m`. We state only the FRS half here (hypotheses
`_hFn : |F| > n`, `_hω : Admissible …`, `_hω0 : ω ≠ 0`); the multiplicity half is gated
on `D2.19 / DA.7` (univariate-multiplicity definition), tracked separately. Admitted as
an external result.

**Source hypothesis restored (2026-07-21 Phase-A merge audit): `ω` generates `F×`.**
The statement WITHOUT an order condition on `ω` is **false**: with `F = 𝔽₁₀₁`, `s = 2`,
`ω = -1` (order 2), `k = 3`, `L = {1,…,7}` every previous hypothesis holds (admissibility
only forces `ord(ω) ≥ s`), yet for `A := span{enc 1, enc X²}` the encodings collapse to
repeated-entry vectors (since `(-x)² = x²` and `ω² = 1`), giving
`∑ᵢ dim(A ⊓ ker projᵢ) = n = 7 > 6 = finrank A · τ(2) · n`. The load-bearing source fact
is [GK16 Lemma 12]'s folded-Wronskian criterion, stated for **`γ` a generator of `F×`**
(`W_γ(1, X^d) = X^d(γ^d − 1)` vanishes when `γ^d = 1`, `d < k`). The pinned tex
(`thm:folded-rs-are-subspace-design`, L1263–1277) omits any order condition, and GG25's
own restatement (Def 2.18 / Thm 2.19, `q > sn` only) is falsified by the same
counterexample; the omission has been reported to the paper's authors (2026-07-21, see
the audit's T2.18 row). We carry GK16's own generator hypothesis `_hω_gen` — not a
weaker `ord(ω) ≥ k` guard: that would block the known counterexample but is not
licensed by the cited source, and an admit must state exactly what its source proves,
never an unlicensed hybrid strengthening.

Boundary note: for `k ≥ s·|ι|` (rate ≥ 1) the profile satisfies `τ(r) ≥ 1` on all of
`[1, s]` and `IsSubspaceDesign s τ C` holds for *every* code, so in that regime this
admit is contentless; its content lives in the intended `k < s·|ι|` regime (where the
hypotheses are jointly satisfiable — e.g. `F = ZMod 5`, `ι = Fin 2`, `s = 2`, `k = 1`,
`ω = 2`). -/
theorem frs_is_subspaceDesign_gk16
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (L : Finset F) (_hL_dom : ∀ i : ι, domain i ∈ L)
    (_hFn : Fintype.card ι < Fintype.card F)
    (_hω : ReedSolomon.Folded.Admissible L s ω) (_hω0 : ω ≠ 0)
    (_hω_gen : orderOf ω = Fintype.card F - 1) :
    let τ : ℕ → ℝ := fun r ↦
      if r ∈ Finset.Icc 1 s then
        (k : ℝ) / Fintype.card ι / (s - r + 1)
      else 1
    IsSubspaceDesign s τ (ReedSolomon.Folded.frsCode domain k s ω) := by
  sorry -- ABF26-T2.18 (FRS half); external admit [GK16].

end CodingTheory
