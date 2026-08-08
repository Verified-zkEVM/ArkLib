/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Folded
import ArkLib.Data.Polynomial.FoldedWronskian

/-!
# Subspace-design codes (ABF26 §2.5)

ABF26 Definition 2.16 [GX13]: the τ-subspace-design property for an F-additive code
`C : F^k → (F^s)^n`. Lemma 2.17 [GG25] is **proved in-tree** (via the module-alphabet
Singleton bound `LinearCode.singleton_bound_module`); the folded Reed-Solomon half of
Theorem 2.18 [GK16] is **proved in-tree** too, via the folded-Wronskian toolkit of
`ArkLib.Data.Polynomial.FoldedWronskian`.

## Main definitions

- `CodingTheory.IsSubspaceDesign` — ABF26 Definition 2.16.

## Main statements

- `CodingTheory.ker_proj_eq_vanish_at` — bridge between `ker(proj i)` and `{a | a i = 0}`,
  the carrier-level faithfulness witness for `IsSubspaceDesign`.
- `CodingTheory.subspaceDesign_tau_lower_of_ne_bot` — ABF26 Lemma 2.17 [GG25] under GG25's
  own non-triviality assumption `C ≠ ⊥`: `τ(r) ≥ ρ - 1/n` for every `r ≥ 1`.
- `CodingTheory.subspaceDesign_tau_lower` — the same bound for an arbitrary code, under the
  (implicit-in-the-sources) hypothesis that `τ` is non-negative.
- `CodingTheory.frs_is_subspaceDesign_gk16` — ABF26 Theorem 2.18 [GK16], folded RS half:
  folded RS codes are τ-subspace-design for an explicit τ.

Both L2.17 and T2.18 carry hypotheses their sources omit, and in each case the unguarded
statement is false; the counterexamples are recorded in the declaration docstrings and
cross-referenced to `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md`
and `docs/kb/queries/abf26-split-pr1-review-2026-08-07/`.

Three auxiliary results here are generic linear algebra / polynomial facts with no
coding-theory content — `sum_rootMultiplicity_le_natDegree`, `finrank_eq_of_map_eq`,
`exists_adapted_basis`. They are stated publicly rather than `private` because they are
reusable, and are intended to move to `ArkLib/ToMathlib/` once a home is chosen.

## Deferred

- The univariate-multiplicity half of Theorem 2.18 is **not proved here, and is open**. The
  code family itself is available — `ReedSolomon.Multiplicity.umCode` in
  `ArkLib/Data/CodingTheory/ReedSolomon/Multiplicity.lean` supplies the derivative-based
  evaluation map that the multiplicity half needs — but GK16's argument for that half
  requires a multiplicity-code analogue of the folded Wronskian, which
  `ArkLib.Data.Polynomial.FoldedWronskian` does not provide.

## References

- [ABF26] Arnon-Boneh-Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026. §2.5 Definition 2.16, Lemma 2.17, Theorem 2.18.
- [GX13] Guruswami-Xing. (Original subspace-design definition.)
- [GG25] Goyal-Guruswami. (Cited for L2.17; Definition 2.15, Lemma 2.16.)
- [GK16] Guruswami-Kopparty. (Cited for T2.18; Definition 11, Lemma 12, Theorem 14.)
- [GR08] Guruswami-Rudra. (Folded RS evaluation-point injectivity condition, the source
  shape of `ReedSolomon.Folded.Admissible`.)
-/

namespace CodingTheory

open scoped NNReal

/-- **ABF26 Definition 2.16 [GX13].** A code `C : F^k → (F^s)^n` (here represented as a
subspace of `(ι → Fin s → F)` over `F`) is **τ-subspace-design** if for every `r ∈ ℕ`
and every F-linear subspace `A` of `C` with `dim A ≤ r`,

  `(Σ_{i ∈ [n]} dim A_i) / n ≤ dim A · τ(r)`

where `A_i := { a ∈ A : a_i = 0^s }` is the subspace of `A` whose codewords vanish at
position `i`. Here `A_i` is realised as `A ⊓ ker(eval_i)`, the intersection of `A`
with the kernel of the linear map evaluating the `i`-th coordinate. -/
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

/-- **Bridge: kernel of the `i`-th projection equals the comprehension `{a | a i = 0}`.**

The subspace `A_i := {a ∈ A : a_i = 0^s}` from the paper's `IsSubspaceDesign` definition
is `A ⊓ ker(LinearMap.proj i)`. This lemma confirms the underlying set: a word
`a : ι → Fin s → F` lies in `ker(proj i)` iff `a i = 0`. Combined with `Submodule.inf_*`
this lets downstream proofs rewrite freely between the technical `ker(proj i)` form (used
in the `IsSubspaceDesign` definition for type-class reasons) and the paper's
comprehension form.

It has no consumer in this file: both `subspaceDesign_tau_lower` and
`frs_is_subspaceDesign_gk16` work with `LinearMap.mem_ker` pointwise instead. It is
exported as the faithfulness witness for the definition, and for downstream readability. -/
lemma ker_proj_eq_vanish_at {ι : Type*} {F : Type*} [Semiring F] {s : ℕ} (i : ι) :
    (LinearMap.ker (LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i) :
        Set (ι → Fin s → F)) =
      {a | a i = 0} := by
  ext a
  simp [LinearMap.mem_ker, LinearMap.proj_apply]

/-- **ABF26 Lemma 2.17 [GG25], non-trivial-code form.** For a τ-subspace-design code
`C ≠ ⊥` of rate `ρ`, the profile `τ` is lower-bounded by `ρ - 1/n` at every `r ≥ 1`:

  `τ(r) ≥ ρ - 1/n`  for every `r ≥ 1` .

**Rate convention.** Per ABF26 Definition 2.5, the rate of a code over alphabet `Σ` is
`log_{|Σ|}|C| / n`; for an `F`-additive code `C ⊆ (F^s)^n` this is
`ρ = dim_F(C) / (s·n)` — the alphabet is `F^s`, so the `finrank` is divided by `s·n`,
**not** by `n`. The subtracted `1/n` term, by contrast, divides by the block length `n`
only (paper: `min_r τ(r) ≥ ρ − 1/n`).

**`r = 0` is excluded because the sources' `∀ r ∈ ℕ` form is literally false there.**
Both ABF26 Lemma 2.17 (`min_{r ∈ ℕ} τ(r) ≥ ρ − 1/n`) and GG25 Lemma 2.16 (*"for all
`r ∈ ℕ`"*) assert the bound at `r = 0` as well. But at `r = 0` the `IsSubspaceDesign`
predicate constrains `τ 0` not at all: `A ≤ C` together with `finrank A ≤ 0` forces
`A = ⊥`, so the design inequality reads `0 ≤ 0 · τ(0)` and is satisfied by *every* value
of `τ 0`, including values far below `ρ − 1/n`. GG25's own proof concedes the point ("we
just need to prove the result for `r = 1`, since we can just take `A` of dimension 1"). So
`1 ≤ r` is the largest honest range, and for `r ≥ 1` this is exactly the sources' claim —
there is no further narrowing (in particular no `r ≤ s` restriction; `1 ≤ s` is needed
only because `s = 0` forces the ambient module, hence `C`, to be trivial).

**Which non-degeneracy guard.** GG25's proof opens by picking a non-zero codeword, i.e. it
tacitly assumes the code is non-trivial; `hCne : C ≠ ⊥` is that assumption, and it imposes
nothing on `τ`. The sibling `subspaceDesign_tau_lower` trades it for `0 ≤ τ`, which also
covers `C = ⊥`. *Some* guard is unavoidable: for `C = ⊥` every `IsSubspaceDesign`
inequality reads `0 ≤ 0`, so the negative profile `τ ≡ −1` at `n = 2` satisfies the
hypothesis while violating the conclusion (`−1 ≥ 0 − 1/2` is false).

**Proof** (GG25's argument, uniform in `r`): pick a distance-attaining pair
`u ≠ v ∈ C` and set `a := u − v`, a nonzero codeword with at least `n − d` zero
blocks (`d = Code.dist`). The design inequality at the 1-dimensional subspace
`span {a}` (valid for every `r ≥ 1`) gives `τ(r) ≥ #zero-blocks / n ≥ (n − d)/n`,
and the module-alphabet Singleton bound `LinearCode.singleton_bound_module`
(`k ≤ s(n − d + 1)`) turns this into `τ(r) ≥ ρ − 1/n`. -/
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

/-- **ABF26 Lemma 2.17 [GG25].** For any τ-subspace-design code of rate `ρ` with a
non-negative profile, `τ` is lower-bounded by `ρ - 1/n` at every `r ≥ 1`:

  `τ(r) ≥ ρ - 1/n`  for every `r ≥ 1` .

This is `subspaceDesign_tau_lower_of_ne_bot` with the non-triviality guard moved from the
code to the profile, which makes the statement total in `C`. See that declaration for the
rate convention, for why `r = 0` must be excluded (the sources state the bound for all
`r ∈ ℕ`, and at `r = 0` it is false), and for why *some* guard is needed at all.

**Which form to use.** `hτ_nonneg` is an ArkLib addition: neither ABF26 Definition
2.16 / Lemma 2.17 nor GG25 Definition 2.15 / Lemma 2.16 asserts `τ ≥ 0` (GG25 constrains
the other side, `τ : ℕ → ℝ_{≤1}`), though it is implicit — a design profile bounds a ratio
of dimensions. It is discharged for free by every profile arising in practice, including
the one produced by `frs_is_subspaceDesign_gk16`, so this is the more convenient form. Use
`subspaceDesign_tau_lower_of_ne_bot` when the profile is unknown but the code is known to
be non-trivial; that is the shape GG25's own proof assumes. -/
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

/-- **Root multiplicities at finitely many points are bounded by the degree.** Packing, for
each `a ∈ S`, `rootMultiplicity a W` copies of `a` into a multiset gives a sub-multiset of
`W.roots` (the points of `S` are distinct), whose cardinality is at most `natDegree W`.

Generic (no coding theory); intended home is `ArkLib/ToMathlib/Polynomial/`. Verified absent
from Mathlib. -/
lemma sum_rootMultiplicity_le_natDegree {F : Type*} [Field F]
    {W : Polynomial F} (S : Finset F) :
    ∑ a ∈ S, W.rootMultiplicity a ≤ W.natDegree := by
  classical
  have hle : (∑ a ∈ S, Multiset.replicate (W.rootMultiplicity a) a) ≤ W.roots := by
    rw [Multiset.le_iff_count]
    intro b
    rw [Multiset.count_sum', Polynomial.count_roots]
    calc ∑ a ∈ S, Multiset.count b (Multiset.replicate (W.rootMultiplicity a) a)
        = ∑ a ∈ S, (if a = b then W.rootMultiplicity a else 0) :=
          Finset.sum_congr rfl fun a _ => by rw [Multiset.count_replicate]
      _ ≤ W.rootMultiplicity b := by
          rw [Finset.sum_ite_eq' S b]
          split <;> simp
  have hcard := Multiset.card_le_card hle
  rw [Multiset.card_sum] at hcard
  simp only [Multiset.card_replicate] at hcard
  exact hcard.trans (Polynomial.card_roots' W)

/-- **Dimension transfer along an injective-on-`B` linear map.** If `f` is injective on the
submodule `B` and maps it onto `A`, then `B` and `A` have the same dimension. This is the
bookkeeping behind the message-side lift of a subspace of an FRS code.

Generic (no coding theory); intended home is `ArkLib/ToMathlib/`. For the special case
`f = p.subtype` use Mathlib's `Submodule.finrank_map_subtype_eq` instead; this lemma is for
maps that are injective only on `B`, such as an encoder restricted to low-degree
polynomials. -/
lemma finrank_eq_of_map_eq {F M N : Type*} [Field F] [AddCommGroup M] [Module F M]
    [AddCommGroup N] [Module F N] (f : M →ₗ[F] N) (B : Submodule F M) (A : Submodule F N)
    (hinj : ∀ p ∈ B, f p = 0 → p = 0) (hmap : B.map f = A) :
    Module.finrank F B = Module.finrank F A := by
  have hg : Function.Injective (f.domRestrict B) := by
    rw [← LinearMap.ker_eq_bot]
    ext p
    simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply, Submodule.mem_bot]
    exact ⟨fun h => Subtype.ext (hinj p.1 p.2 h), fun h => by rw [h]; simp⟩
  rw [← LinearMap.finrank_range_of_inj hg, LinearMap.range_domRestrict, hmap]

/-- **A basis adapted to a subspace.** Any finite-dimensional space `M` of dimension `σ` has a
basis indexed by `Fin σ` whose first `dim N` vectors lie in a prescribed subspace `N`; obtained
by splitting `M` along a complement of `N`.

Generic (no coding theory); intended home is `ArkLib/ToMathlib/`. Verified absent from
Mathlib, which has the ingredients (`Submodule.exists_isCompl`, `Module.Basis.prod`,
`Submodule.prodEquivOfIsCompl`) but not the packaged statement. -/
lemma exists_adapted_basis {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
    [FiniteDimensional F M] (N : Submodule F M) {σ : ℕ} (hσ : Module.finrank F M = σ) :
    ∃ b : Module.Basis (Fin σ) F M,
      ∀ j : Fin σ, (j : ℕ) < Module.finrank F N → b j ∈ N := by
  classical
  obtain ⟨K, hK⟩ := N.exists_isCompl
  set t := Module.finrank F N with ht
  set u := Module.finrank F K with hu
  have htu : t + u = σ := by rw [ht, hu, Submodule.finrank_add_eq_of_isCompl hK, hσ]
  set b0 : Module.Basis (Fin t ⊕ Fin u) F M :=
    ((Module.finBasis F N).prod (Module.finBasis F K)).map (N.prodEquivOfIsCompl K hK) with hb0
  set e : Fin t ⊕ Fin u ≃ Fin σ := finSumFinEquiv.trans (finCongr htu) with he
  refine ⟨b0.reindex e, fun j hj => ?_⟩
  have hsymm : e.symm j = Sum.inl ⟨(j : ℕ), hj⟩ := by
    rw [Equiv.symm_apply_eq, he]
    simp [finSumFinEquiv_apply_left]
  rw [Module.Basis.reindex_apply, hsymm, hb0]
  simp only [Module.Basis.map_apply]
  rw [Submodule.coe_prodEquivOfIsCompl', Module.Basis.prod_apply_inl_snd]
  simp only [ZeroMemClass.coe_zero, add_zero]
  rw [Module.Basis.prod_apply_inl_fst]
  exact ((Module.finBasis F N) ⟨(j : ℕ), hj⟩).2

/-- **Base change for the folded Wronskian.** Replacing the polynomials by `F`-linear
combinations multiplies the folded Wronskian by the (constant) determinant of the coefficient
matrix: the folded Wronskian matrix gets right-multiplied by the constant matrix `C U`. -/
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

/-- **The multiplicity engine of [GK16, Theorem 14].** If a subspace `N` of `B` consists of
polynomials all of whose `ω`-twists are divisible by `X − C p`, then `(X − C p) ^ dim N` divides
the folded Wronskian of any basis of `B`: pass to a basis of `B` adapted to `N`
(`exists_adapted_basis`), where `dim N` whole columns of the folded Wronskian matrix are
divisible by `X − C p` (`Matrix.pow_dvd_det_of_forall_mem_col_dvd`); base change only
multiplies the determinant by a nonzero constant (`foldedWronskian_of_linearComb`). -/
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
  obtain ⟨cb, hcb⟩ := exists_adapted_basis N' hrkB
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

/-- **ABF26 Theorem 2.18 [GK16], folded Reed-Solomon half.** ABF26 Theorem 2.18 asserts
that both folded Reed-Solomon codes and univariate multiplicity codes are τ-subspace-design
for an explicit τ:

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
additionally requires `char(F) > m`. Only the FRS half is proved here (hypotheses
`hFn : |F| > n`, `hω_adm : Admissible …`, `hω0 : ω ≠ 0`); the multiplicity half is open —
the code family exists (`ReedSolomon.Multiplicity.umCode`) but GK16's argument for it needs
a multiplicity analogue of the folded Wronskian that the toolkit does not provide.

**Proof** (GK16's Theorem 14 argument).
Outside the main regime the bound is bookkeeping: every block dimension is at most
`σ := dim A`, so the design sum is at most `σ`, which settles both `σ = 0` and `τ(r) ≥ 1`
(in particular `r ∉ [s]`, where `τ(r) = 1`). In the remaining regime `r ∈ [s]` and
`k < n(s − r + 1)`, so `k < n·s ≤ |F| − 1` — the `n·s` folded evaluation points are
distinct (`admissible_foldedPoints_injective`) and nonzero (for `s ≥ 2`; for `s = 1` this
is `hFn`). The encoder is then injective on `degreeLT F k`
(`frsEvalOnPoints_domRestrict_injective`), so `A` and each `A ⊓ ker(proj i)` lift to
message-side subspaces `B` and `Nᵢ ≤ B` of the same dimension, with `Nᵢ` consisting of
polynomials vanishing on the whole `i`-th orbit `{domain i · ω^j : j < s}`. Fix a basis
`P₁, …, P_σ` of `B` and let `W` be its `ω`-folded Wronskian [GK16 Definition 11]. Then
`W ≠ 0` (`Polynomial.foldedWronskian_ne_zero_of_linearIndependent`, GK16 Lemma 12 — this
is where `hω_gen` is used) and `deg W ≤ σ(k − 1)`
(`Polynomial.natDegree_foldedWronskian_le`), while for every block `i` and every
`0 ≤ m ≤ s − σ` the point `domain i · ω^m` is a root of `W` of multiplicity at least
`dim Nᵢ` (base-change to a basis of `B` adapted to `Nᵢ`, then
`Matrix.pow_dvd_det_of_forall_mem_col_dvd`; the twist `ω^{i'}` of row `i' < σ` keeps
the exponent `i' + m < s` inside the orbit). Counting these `n(s − σ + 1)` distinct roots
against `deg W` gives `(s − σ + 1)·∑ᵢ dim(A ⊓ ker projᵢ) ≤ σ(k − 1)`, and `σ ≤ r` turns
this into the claimed `∑ᵢ dim(A ⊓ ker projᵢ) / n ≤ σ · τ(r)`.

**Two source hypotheses are missing from the printed statement.** ABF26 Theorem 2.18 and
GG25's restatement (Definition 2.18 / Theorem 2.19, which asks only `q > sn`) are both
**false as printed**, for two independent reasons. Each is repaired below by a hypothesis
that the ultimate source, GK16, does impose. Recorded in
`docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md` (rows `D2.14`,
`T2.18`, and Existing Inconsistencies #6) and in
`docs/kb/queries/abf26-split-pr1-review-2026-08-07/`.

*(1) No order condition on `ω` — repaired by `hω_gen`.* The statement without one is
**false**: with `F = 𝔽₁₀₁`, `s = 2`, `ω = -1` (order 2), `k = 3`, `L = {1,…,7}` every other
hypothesis holds (admissibility only forces `ord(ω) ≥ s`), yet for
`A := span{enc 1, enc X²}` the encodings collapse to repeated-entry vectors (since
`(-x)² = x²` and `ω² = 1`), giving
`∑ᵢ dim(A ⊓ ker projᵢ) = n = 7 > 6 = finrank A · τ(2) · n`. The load-bearing source fact is
[GK16 Lemma 12]'s folded-Wronskian criterion, stated for **`γ` a generator of `F×`**
(`W_γ(1, X^d) = X^d(γ^d − 1)` vanishes when `γ^d = 1`, `d < k`). The pinned tex
(`thm:folded-rs-are-subspace-design`) omits any order condition. We carry GK16's own
generator hypothesis `hω_gen` — not a weaker `ord(ω) ≥ k` guard: that would block the known
counterexample but is not licensed by the cited source, and a transcription must state
exactly what its source proves, never an unlicensed hybrid strengthening. (The hypothesis is
used exactly once, in `Polynomial.foldedWronskian_ne_zero_of_linearIndependent`.)

*(2) `0 ∈ L` is permitted — repaired by the intra-orbit clause of `Admissible`.* This
omission is independent of (1): the theorem is false with `0 ∈ L` **even when `hω_gen`
holds**. ABF26 Definition 2.14 quantifies its admissibility condition only over *distinct*
pairs `{α, β} ∈ (L choose 2)`, and GG25 Definition 2.18 likewise asks only `αᵢγᵗ ≠ αⱼ` for
`i ≠ j`; neither excludes `0 ∈ L`. Counterexample: `F = ZMod 5`, `domain = (0, 1)`,
`s = 3`, `k = 2`, `ω = 2` (a generator of `(ZMod 5)ˣ`, so `hω_gen` holds, and the paper's
inter-orbit clause holds). Take `A := span{enc X}`, of dimension 1. The whole `s`-orbit of
the point `0` degenerates to `{0}`, so the block at `0` is identically zero and contributes
`dim = 1`, while the block at `1` contributes `0`; hence `∑ᵢ dim Aᵢ / n = 1/2`, whereas
`dim A · τ(1) = (k/n)/(s − 1 + 1) = 1/3`. What fails in the proof is exactly `hfinj`, the
injectivity of `(i, m) ↦ domain i · ω^m`, i.e. the root count over-counts.
`ReedSolomon.Folded.Admissible` is deliberately **stronger** than ABF26 Definition 2.14: it
adds the intra-orbit clause `α · ωⁱ ≠ α` for `0 < i < s`, which forces `0 ∉ L` whenever
`s ≥ 2` (take `i = 1`). That clause is therefore **load-bearing for this theorem**, not
merely a hedge protecting the folded-RS distance formula; it is what makes `Admissible`
GR08's evaluation-point injectivity condition (see `docs/kb/papers/GR08.md`), and GK16 §4.2
excludes `α = 0` for the same reason. Consequence for readers: this theorem is *weaker* than
ABF26's printed claim, because it assumes more of `L` and `ω`.

Boundary note: for `k ≥ s·|ι|` (rate ≥ 1) the profile satisfies `τ(r) ≥ 1` on all of
`[1, s]` and `IsSubspaceDesign s τ C` holds for *every* code, so in that regime the
statement is contentless; its content lives in the intended `k < s·|ι|` regime (where the
hypotheses are jointly satisfiable — e.g. `F = ZMod 5`, `ι = Fin 2`, `s = 2`, `k = 1`,
`ω = 2`). -/
theorem frs_is_subspaceDesign_gk16
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {F : Type*} [Field F] [Fintype F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (L : Finset F) (hL_dom : ∀ i : ι, domain i ∈ L)
    (hFn : Fintype.card ι < Fintype.card F)
    (hω_adm : ReedSolomon.Folded.Admissible L s ω) (hω0 : ω ≠ 0)
    (hω_gen : orderOf ω = Fintype.card F - 1) :
    let τ : ℕ → ℝ := fun r ↦
      if r ∈ Finset.Icc 1 s then
        (k : ℝ) / Fintype.card ι / (s - r + 1)
      else 1
    IsSubspaceDesign s τ (ReedSolomon.Folded.frsCode domain k s ω) := by
  classical
  intro τ r A hAC hAr
  have hτdef : ∀ x : ℕ, τ x =
      if x ∈ Finset.Icc 1 s then (k : ℝ) / Fintype.card ι / (s - x + 1) else 1 := fun _ => rfl
  have hn_pos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
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
  -- Trivial branch 1: `τ r ≥ 1`.
  by_cases hτ1 : (1 : ℝ) ≤ τ r
  · exact hsum_le.trans (le_mul_of_one_le_right (by positivity) hτ1)
  rw [not_le] at hτ1
  -- Trivial branch 0: `A = ⊥`.
  by_cases hσ0 : σ = 0
  · rw [hσ0] at hsum_le ⊢
    simpa using hsum_le
  have hσ1 : 1 ≤ σ := by omega
  -- Main branch: `r ∈ [1, s]` and `k < n (s − r + 1)`.
  have hrmem : r ∈ Finset.Icc 1 s := by
    by_contra h
    rw [hτdef r, if_neg h] at hτ1
    linarith
  obtain ⟨hr1, hrs⟩ := Finset.mem_Icc.mp hrmem
  have hσs : σ ≤ s := le_trans hAr hrs
  have hτval : τ r = (k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1) := by
    rw [hτdef r, if_pos hrmem]
  have hb_pos : (0 : ℝ) < (s : ℝ) - r + 1 := by
    have : (r : ℝ) ≤ s := by exact_mod_cast hrs
    linarith
  have hcast_b : (((s - r + 1 : ℕ)) : ℝ) = (s : ℝ) - r + 1 := by
    push_cast [Nat.cast_sub hrs]; ring
  have hk_lt : k < Fintype.card ι * (s - r + 1) := by
    rw [hτval] at hτ1
    have h1 : (k : ℝ) < Fintype.card ι * ((s : ℝ) - r + 1) := by
      rw [div_div, div_lt_one (by positivity)] at hτ1
      linarith
    rw [← hcast_b] at h1
    exact_mod_cast h1
  have hk_ns : k < Fintype.card ι * s := by
    have : s - r + 1 ≤ s := by omega
    calc k < Fintype.card ι * (s - r + 1) := hk_lt
      _ ≤ Fintype.card ι * s := Nat.mul_le_mul_left _ this
  have hk_le : k ≤ s * Fintype.card ι := by
    rw [Nat.mul_comm] at hk_ns; omega
  -- Admissibility transported from `L` to the image of `domain`.
  have hadm : ReedSolomon.Folded.Admissible (Finset.univ.map domain) s ω := by
    obtain ⟨h1, h2⟩ := hω_adm
    refine ⟨fun α hα β hβ hαβ i hi => ?_, fun α hα i hi his => ?_⟩
    · obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hα
      obtain ⟨b, -, rfl⟩ := Finset.mem_map.mp hβ
      exact h1 _ (hL_dom a) _ (hL_dom b) hαβ i hi
    · obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hα
      exact h2 _ (hL_dom a) i hi his
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
        exact hω_adm.2 (domain x) (hL_dom x) 1 (by omega) (by omega) (by rw [hx]; ring)
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
    exact finrank_eq_of_map_eq enc B A (fun p hp h0 => hker p ((hBmem p).mp hp).1 h0) hBmap
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
    fun i => finrank_eq_of_map_eq enc (N i) _
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
      _ ≤ W.natDegree := sum_rootMultiplicity_le_natDegree _
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
  have hSb : S * ((s : ℝ) - r + 1) ≤ σ * k := by
    have h1 : S * ((s : ℝ) - r + 1) ≤ S * ((s : ℝ) - σ + 1) := by nlinarith
    have h2 : (0 : ℝ) ≤ σ := by positivity
    nlinarith
  rw [hτval, div_le_iff₀ hn_pos]
  have hrw : (σ : ℝ) * ((k : ℝ) / Fintype.card ι / ((s : ℝ) - r + 1)) * Fintype.card ι
      = σ * k / ((s : ℝ) - r + 1) := by
    field_simp
  rw [hrw, le_div_iff₀ hb_pos]
  exact hSb

end CodingTheory
