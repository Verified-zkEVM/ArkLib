/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Data.Probability.Instances

/-!
# Numeric ε-error functions: ε_ca and ε_mca

Numeric versions of the proximity gap, correlated agreement (CA), and mutual correlated
agreement (MCA) error functions as defined in
*Open Problems in List Decoding and Correlated Agreement*
(Arnon, Boneh, Fenzi; April 8, 2026), Section 4.

This file implements the **numeric error-function API** for CA and MCA. It coexists with the
predicate-style API in [`Basic.lean`](Basic.lean); each predicate has a bridging
`*_iff_eps*_le` lemma elsewhere in this directory.

## Main definitions

- `ProximityGap.epsPG` — proximity gap error, introduced informally in paper §4.1.
- `ProximityGap.epsCA` — ABF26 Definition 4.1: correlated agreement error
  `ε_ca(C, δ_fld, δ_int)` (affine-line case, `Fin 2` stacks).
- `ProximityGap.epsCA'` — Convenience alias for the no-proximity-loss case
  `ε_ca(C, δ) := ε_ca(C, δ, δ)`.
- `ProximityGap.epsCA_curves` — `Fin (k+1)`-stack variant: worst-case probability over
  polynomial curves `∑ i, r^i · f_i`. Generalises `epsCA` (the `k = 1` case).
- `ProximityGap.epsCA_affineSpaces` — `Fin (k+1)`-stack variant: worst-case probability
  over random points in the affine subspace `f₀ + span{f₁, ..., f_k}`.
- `ProximityGap.epsMCA` — ABF26 Definition 4.3: mutual correlated agreement error.

## Note on MCA with proximity loss (ABF26 Remark 4.4)

The paper intentionally does **not** define a proximity-loss variant of `ε_mca` analogous to
`ε_ca(C, δ_fld, δ_int)`. Per Remark 4.4 this remains to be thoroughly explored, so this file
exposes only the no-loss `ε_mca(C, δ)`.

## Open follow-ups

The following items from ABF26 Section 4 are tracked in `docs/kb/ABF26_PLAN.md` §7 and remain to be
added on top of this file's definitions. Each is in scope for Phase 1 of the plan:

- **Monotonicity / antitonicity of `epsCA`** (ABF26-D4.1 sub-tasks 4–5). `epsCA` is
  *monotone* in `δ_fld` (larger fold-distance ⇒ more `γ` in the event) and **antitone**
  in `δ_int` (larger interleaved-distance ⇒ stricter `Δ_joint > δ_int` condition).
- **ABF26 Remark 4.2** — discretization: `epsCA C δ (δ + β) = epsCA C δ (δ + β')` for
  `β, β' ∈ [0, 1/n)`. Follows from `Δ ∈ {0, 1/n, ..., 1}`.
- **ABF26 Fact 4.5** — `ε_pg ≤ ε_ca ≤ ε_mca`. Requires defining `epsPG` first.
- **ABF26 Lemma 4.6** — `ε_mca = ε_ca` below `δ_min(C)/2`. Proof leans on the helper
  predicates `pairJointAgreesOn` and `mcaEvent` defined here.
- **ABF26 Lemma 4.7** — `ε_mca(C^≡t, δ) ≤ t · ε_mca(C, δ)` via union bound.
- **Bridging lemmas**: `δ_ε_correlatedAgreementAffineLines C δ ε ↔ epsCA C δ δ ≤ ε` (and
  similar for `Curves`, `AffineSpaces`) connecting the predicate API in `Basic.lean` to the
  numeric API here.

## Design notes worth flagging

- **`epsCA` / `epsMCA` take `C : Set (ι → A)` and not `Submodule F (ι → A)`** by design.
  The definitions are pure predicates over a set of codewords — neither uses the linear
  structure. Theorems that *need* `C` to be a `ModuleCode` add the `Submodule` hypothesis
  separately (e.g. F4.5 takes `C : Submodule F (ι → A)`). Linear callers pass their
  `Submodule` via the implicit coercion `(C : Set _)`. We keep the definitions
  Set-based to:
  1. Avoid narrowing the API — `epsCA` is meaningful for non-linear codes too.
  2. Match the paper's `C ⊆ Σ^n` shape, which is also Set-based.
  3. Avoid a deep refactor of every `epsCA` / `epsMCA` call site for a one-character
     win at each one.
- **`F` is implicit in `epsCA` but does not appear in its return type**, so callers that
  invoke `epsCA` without an explicit pair `(f₁, f₂)` (e.g. inside `epsCA'`) need
  `epsCA (F := F) C δ δ` to thread `F` through. If this becomes painful in proofs,
  switching `epsCA` to take `F` as an explicit argument is a cheap refactor.
- **`epsMCA` and `mcaEvent` are `Fin 2`-only** (the affine-line case). Paper Section 4
  considers more general interleavings; generalizing to `Fin ℓ` is a future extension,
  not required for F4.5 or L4.6.
- **`pairJointAgreesOn` and `mcaEvent` are intentionally public**, exposed as named
  anchors for the planned L4.6 proof and bridging lemmas. If they prove unhelpful in
  practice they can be inlined / marked `private`.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*. 2026.
-/

-- The definitions and proofs below all take the variables `ι`, `F`, `A` from a single section
-- (PMF forces them into `Type 0`). Several theorems use `Fintype`/`DecidableEq` instances at
-- proof-time but not in their types; suppressing the noisy `unused...InType` linter warnings
-- file-wide here, matching the idiom used in `ReedSolomon/FftDomain.lean` and similar files.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace ProximityGap

open NNReal Code
open scoped ProbabilityTheory BigOperators
open Probability

section

-- Universe constraints: `PMF` (used by the `Pr_{...}` notation) is universe-monomorphic at
-- `Type 0`, so `ι`, `F`, and `A` must live in `Type`, matching the existing predicate-style API
-- in `Basic.lean` (`δ_ε_correlatedAgreementAffineLines` and friends).
variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- **ABF26 Section 4.1 (proximity gap error).** Worst-case "bad fraction" of `γ`-points
for which a line `f₁ + γ·f₂` is `δ`-close to `C` while the line is *not* entirely `δ`-close.

Paper §4.1 page 17 introduces this informally: a code has proximity gap `ε_pg(C, δ)` if
every line is either entirely `δ`-close to `C` (i.e. every `γ ∈ F` gives a δ-close point)
or at most `ε_pg` fraction of it is — a dichotomy. The strict comparison with `ε_ca`
(`epsPG ≤ epsCA`, paper Fact 4.5) is that the "bad" set for `epsPG` (`¬ ∀ γ, line close`)
is contained in the "bad" set for `epsCA` (`¬ jointProximity`) when `C` is closed under
linear combination, since any joint codeword pair `(v₀, v₁)` produces a line of codewords
`v₀ + γ·v₁ ∈ C`. -/
noncomputable def epsPG (C : Set (ι → A)) (δ : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin 2) ι,
    if (∀ γ : F, δᵣ(u 0 + γ • u 1, C) ≤ δ) then (0 : ENNReal)
    else Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ]

open Classical in
/-- **ABF26 Definition 4.1.** Correlated agreement (CA) error of an `F`-additive code `C`
with respect to fold-distance `δ_fld` and interleaved-distance `δ_int`.

The worst-case probability over pairs of words `(f₁, f₂)` and over `γ ← $ᵖ F` that

- the line `f₁ + γ·f₂` is `δ_fld`-close to `C`, **and**
- the pair `(f₁, f₂)` is **not** `δ_int`-close to the interleaved code `C^⋈ (Fin 2)`.

The second condition is `γ`-independent, so the formula simplifies to `0` when `(f₁, f₂)`
is jointly close, and to the line probability otherwise. Cf. paper Section 4.1. -/
noncomputable def epsCA (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin 2) ι,
    if jointProximity C (u := u) δ_int then (0 : ENNReal)
    else Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ_fld]

/-- No-proximity-loss specialization: `ε_ca(C, δ) := ε_ca(C, δ, δ)`. Matches the paper's
short-form notation when both fold-distance and interleaved-distance coincide.

By definition `epsCA C δ δ ≡ epsCA' C δ`; no explicit `epsCA_self` simp lemma is needed
because the two forms are definitionally equal.

Currently unused inside this file — F4.5 and downstream theorems state things in terms of
`epsCA C δ δ` directly to keep the two `δ` arguments visible. Kept exported because external
callers (and future bridging lemmas) may prefer the short form. -/
noncomputable def epsCA' (C : Set (ι → A)) (δ : ℝ≥0) : ENNReal :=
  epsCA (F := F) C δ δ

open Classical in
/-- **ABF26 Definition 4.1, curves variant.** Worst-case probability over `(k+1)`-stacks
`u = (f₀, ..., f_k)` and `r ← $ᵖ F` that the polynomial curve `∑ i, r^i · f_i` is
`δ_fld`-close to `C` while the stack is *not* `δ_int`-close to the interleaved code
`C^⋈ (Fin (k+1))`.

For `k = 1` this collapses to `epsCA` (the affine-line case), modulo the syntactic
difference between `∑ i : Fin 2, r^i · u i` and `u 0 + r · u 1` (they are mathematically
equal). -/
noncomputable def epsCA_curves
    (C : Set (ι → A)) (k : ℕ) (δ_fld δ_int : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin (k + 1)) ι,
    if jointProximity C (u := u) δ_int then (0 : ENNReal)
    else Pr_{let r ← $ᵖ F}[δᵣ(∑ i : Fin (k + 1), (r ^ (i : ℕ)) • u i, C) ≤ δ_fld]

open Classical in
/-- **ABF26 Definition 4.1, affine-spaces variant.** Worst-case probability over
`(k+1)`-stacks `u = (f₀, ..., f_k)` and a uniformly random point `y` in the affine
subspace `f₀ + span{f₁, ..., f_k}` (≡ `Affine.affineSubspaceAtOrigin (u 0) (Fin.tail u)`)
that `y` is `δ_fld`-close to `C` while the stack is *not* `δ_int`-close to the interleaved
code `C^⋈ (Fin (k+1))`. Parallels `epsCA` and `epsCA_curves`. -/
noncomputable def epsCA_affineSpaces
    (C : Set (ι → A)) (k : ℕ) (δ_fld δ_int : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin (k + 1)) ι,
    if jointProximity C (u := u) δ_int then (0 : ENNReal)
    else Pr_{let y ← $ᵖ ↥(Affine.affineSubspaceAtOrigin (F := F) (u 0) (Fin.tail u))}[
      δᵣ(y.1, C) ≤ δ_fld]

/-- The pair `(u₀, u₁)` jointly agrees with two codewords of `C` on every position in `S`.
Equivalent in spirit to `Δ_S((u₀, u₁), C^≡2) = 0` from the paper.

This is a fixed-`S`, pair building block; `InterleavedCode.jointAgreement` is the corresponding
`κ`-indexed *event* (it bundles `∃ S` with the size bound `S.card ≥ (1-δ)·n`). `jointAgreement` is
already alphabet-generic — `{F : Type*} [DecidableEq F]`, invoked with `(F := A)` elsewhere — so the
two differ only structurally, and `pairJointAgreesOn` deliberately avoids the `DecidableEq`
requirement by phrasing agreement as `∀ i ∈ S, … = …` rather than `S ⊆ Finset.filter …`. The
two are tied together by `exists_pairJointAgreesOn_iff_jointAgreement` below, so they cannot
drift apart. -/
def pairJointAgreesOn (C : Set (ι → A)) (S : Finset ι) (u₀ u₁ : ι → A) : Prop :=
  ∃ v₀ ∈ C, ∃ v₁ ∈ C, ∀ i ∈ S, v₀ i = u₀ i ∧ v₁ i = u₁ i

/-- **Bridge: the fixed-`S` pair predicate ↔ the `κ`-indexed event.** Quantifying
`pairJointAgreesOn` over a large-enough set `S` is exactly `InterleavedCode.jointAgreement`
for the two-word stack `![u₀, u₁]`. This pins the fixed-`S` pair building block to the general
event so the two notions never drift apart. -/
lemma exists_pairJointAgreesOn_iff_jointAgreement (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) :
    (∃ S : Finset ι, S.card ≥ (1 - δ) * (Fintype.card ι) ∧ pairJointAgreesOn C S u₀ u₁) ↔
      jointAgreement (F := A) (κ := Fin 2) (C := C) (δ := δ) (W := ![u₀, u₁]) := by
  simp only [pairJointAgreesOn, jointAgreement, Finset.subset_iff, Finset.mem_filter,
    Finset.mem_univ, true_and]
  refine exists_congr fun S => and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨v₀, hv₀, v₁, hv₁, hagree⟩
    refine ⟨![v₀, v₁], fun i => ?_⟩
    fin_cases i
    · exact ⟨hv₀, fun a ha => by simpa using (hagree a ha).1⟩
    · exact ⟨hv₁, fun a ha => by simpa using (hagree a ha).2⟩
  · rintro ⟨v, hv⟩
    exact ⟨v 0, (hv 0).1, v 1, (hv 1).1,
      fun j hj => ⟨by simpa using (hv 0).2 hj, by simpa using (hv 1).2 hj⟩⟩

/-- The "bad" event in ABF26 Definition 4.3: there is a witness set `S` of size at least
`(1-δ)·n` on which the line `u₀ + γ • u₁` exactly equals some codeword of `C`, but no
joint pair of codewords agrees with `(u₀, u₁)` on `S`. -/
def mcaEvent (C : Set (ι → A)) (δ : ℝ≥0) (u₀ u₁ : ι → A) (γ : F) : Prop :=
  ∃ S : Finset ι, (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
    (∃ w ∈ C, ∀ i ∈ S, w i = u₀ i + γ • u₁ i) ∧
    ¬ pairJointAgreesOn C S u₀ u₁

open Classical in
/-- **ABF26 Definition 4.3.** Mutual correlated agreement (MCA) error.

The worst-case probability over pairs `(f₁, f₂)` and over `γ ← $ᵖ F` of the
`mcaEvent`: a single set `S` of size `≥ (1-δ)·n` witnesses both that the line
`f₁ + γ·f₂` exactly equals some codeword of `C` on `S` **and** that no joint pair
of codewords agrees with `(f₁, f₂)` on `S`. MCA strengthens CA (Definition 4.1)
by requiring the witness set for closeness and non-agreement to coincide.

Per Remark 4.4, the paper intentionally does not define a proximity-loss variant. -/
noncomputable def epsMCA (C : Set (ι → A)) (δ : ℝ≥0) : ENNReal :=
  ⨆ u : WordStack A (Fin 2) ι,
    Pr_{let γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ]

/-! ## Monotonicity of `epsCA` (ABF26 Definition 4.1 sub-tasks 4–5)

These two lemmas, together with `epsCA_eq_of_floor_eq`, characterize how `epsCA` varies
with its two distance arguments.

- `epsCA` is **monotone** in `δ_fld`: a larger fold-distance means more `γ` satisfy the
  "line `δ_fld`-close" event, so the inner `Pr` grows.
- `epsCA` is **antitone** in `δ_int`: a larger interleaved-distance is a *weaker* condition
  for `jointProximity`, so *more* pairs `(f₁, f₂)` are jointly close and contribute `0`
  rather than a non-zero `Pr`, decreasing the supremum.

The direction of the second one was a recurring confusion in the original plan; the proof
makes it concrete. -/

/-- **ABF26 Definition 4.1, sub-task 5.** `epsCA` is monotone in `δ_fld`. -/
theorem epsCA_mono_δ_fld
    (C : Set (ι → A)) {δ_fld δ_fld' : ℝ≥0} (δ_int : ℝ≥0) (h : δ_fld ≤ δ_fld') :
    epsCA (F := F) C δ_fld δ_int ≤ epsCA (F := F) C δ_fld' δ_int := by
  classical
  unfold epsCA
  apply iSup_mono
  intro u
  by_cases hjp : jointProximity (C := C) (u := u) δ_int
  · rw [if_pos hjp, if_pos hjp]
  · rw [if_neg hjp, if_neg hjp]
    -- `Pr_γ[Δ ≤ δ_fld] ≤ Pr_γ[Δ ≤ δ_fld']` by event implication.
    apply Pr_le_Pr_of_implies
    intro _ h_close
    exact le_trans h_close (by exact_mod_cast h)

/-- **ABF26 Definition 4.1, sub-task 4.** `epsCA` is **antitone** in `δ_int`. -/
theorem epsCA_antitone_δ_int
    (C : Set (ι → A)) (δ_fld : ℝ≥0) {δ_int δ_int' : ℝ≥0} (h : δ_int ≤ δ_int') :
    epsCA (F := F) C δ_fld δ_int' ≤ epsCA (F := F) C δ_fld δ_int := by
  classical
  unfold epsCA
  apply iSup_mono
  intro u
  -- `jointProximity` is monotone in `δ` (the relative distance comparison `δᵣ ≤ δ`
  -- becomes easier when `δ` grows), so `jointProximity_δ_int → jointProximity_δ_int'`.
  have h_jp_mono :
      jointProximity (C := C) (u := u) δ_int →
      jointProximity (C := C) (u := u) δ_int' := by
    intro h_jp
    exact le_trans h_jp (by exact_mod_cast h)
  by_cases hjp' : jointProximity (C := C) (u := u) δ_int'
  · rw [if_pos hjp']; exact zero_le
  · -- Contrapositive of `h_jp_mono`: `¬jointProximity_δ_int' → ¬jointProximity_δ_int`.
    have hjp : ¬ jointProximity (C := C) (u := u) δ_int := fun h_jp ↦ hjp' (h_jp_mono h_jp)
    rw [if_neg hjp', if_neg hjp]

/-- **`epsMCA` is monotone in `δ`.** A larger proximity radius `δ` only *weakens* the
size constraint `|S| ≥ (1 - δ)·n` of `mcaEvent` (the other two clauses — a codeword
agreeing with the line on `S`, and the absence of a joint codeword pair on `S` — do not
mention `δ`), so the bad event holds for at least as many witness sets `S`. The per-`u`
probability therefore grows pointwise, and so does the supremum.

This is the `epsMCA` analogue of `epsCA_mono_δ_fld`; it is the monotonicity fact behind the
maximality clause of the ABF26 §1 Grand MCA Challenge (a threshold `δ*` with `ε_mca ≤ ε*`
below and `> ε*` above only makes sense because `ε_mca` is non-decreasing in `δ`). -/
theorem epsMCA_mono
    (C : Set (ι → A)) {δ δ' : ℝ≥0} (h : δ ≤ δ') :
    epsMCA (F := F) C δ ≤ epsMCA (F := F) C δ' := by
  classical
  unfold epsMCA
  apply iSup_mono
  intro u
  apply Pr_le_Pr_of_implies
  intro γ h_event
  obtain ⟨S, hS_card, hline, hpair⟩ := h_event
  -- The size clause `(1 - δ')·n ≤ (1 - δ)·n ≤ |S|` survives; `hline`/`hpair` are δ-free.
  exact ⟨S, le_trans (mul_le_mul_of_nonneg_right (tsub_le_tsub_left h 1) (zero_le)) hS_card,
    hline, hpair⟩

/-! ## Helpers toward ABF26 Fact 4.5

Fact 4.5 says `ε_pg ≤ ε_ca ≤ ε_mca`. The first inequality requires the underlying code to
be closed under linear combination, so we state the helper lemmas with a `Submodule F (ι → A)`
hypothesis. -/

/-- **Helper for ABF26 Fact 4.5.** If the pair `(u 0, u 1)` is jointly `δ`-close to the
interleaved code from a `Submodule` `MC`, then for *every* scalar `γ`, the line
`u 0 + γ • u 1` is `δ`-close to `MC`. The proof uses the witness codeword pair
`(v 0, v 1)` to build a single line of codewords `v 0 + γ • v 1 ∈ MC`. -/
theorem jointProximity_imp_line_close
    (MC : Submodule F (ι → A)) (u : WordStack A (Fin 2) ι) (δ : ℝ≥0)
    (h : jointProximity (C := (MC : Set (ι → A))) (u := u) δ) :
    ∀ γ : F, δᵣ(u 0 + γ • u 1, (MC : Set (ι → A))) ≤ δ := by
  rw [← jointAgreement_iff_jointProximity] at h
  obtain ⟨S, hS_card, v, hv⟩ := h
  -- Common: pointwise agreement of `v i` and `u i` on `S`.
  have h_agree : ∀ j ∈ S, v 0 j = u 0 j ∧ v 1 j = u 1 j := by
    intro j hj
    refine ⟨?_, ?_⟩
    · have : j ∈ Finset.filter (fun k ↦ v 0 k = u 0 k) Finset.univ := (hv 0).2 hj
      exact (Finset.mem_filter.mp this).2
    · have : j ∈ Finset.filter (fun k ↦ v 1 k = u 1 k) Finset.univ := (hv 1).2 hj
      exact (Finset.mem_filter.mp this).2
  intro γ
  have hv_γ_mem : (v 0 + γ • v 1) ∈ (MC : Set (ι → A)) :=
    MC.add_mem (hv 0).1 (MC.smul_mem γ (hv 1).1)
  rw [relCloseToCode_iff_relCloseToCodeword_of_minDist]
  refine ⟨v 0 + γ • v 1, hv_γ_mem, ?_⟩
  rw [relCloseToWord_iff_exists_agreementCols]
  refine ⟨S, (relDist_floor_bound_iff_complement_bound _ _ _).mpr hS_card, ?_⟩
  intro j
  refine ⟨fun hj_in ↦ ?_, fun hne hj_in ↦ ?_⟩
  · obtain ⟨h0, h1⟩ := h_agree j hj_in
    simp [Pi.add_apply, Pi.smul_apply, h0, h1]
  · obtain ⟨h0, h1⟩ := h_agree j hj_in
    exact hne (by simp [Pi.add_apply, Pi.smul_apply, h0, h1])

/-- **ABF26 Fact 4.5, first inequality.** `ε_pg ≤ ε_ca` for a `Submodule F (ι → A)`.

Pointwise on `u : WordStack A (Fin 2) ι`:

- If `jointProximity` holds, every `γ` gives a δ-close line (by
  `jointProximity_imp_line_close`), so the `epsPG` contribution is 0; `epsCA`'s contribution
  is also 0 (its `if jointProximity` branch).
- Otherwise both contributions collapse to the same `Pr_γ[line δ-close]` because the inner
  expression is syntactically identical and the bad-set conditions both fail or both hold. -/
theorem epsPG_le_epsCA (MC : Submodule F (ι → A)) (δ : ℝ≥0) :
    epsPG (F := F) (MC : Set (ι → A)) δ ≤ epsCA (F := F) (MC : Set (ι → A)) δ δ := by
  unfold epsPG epsCA
  apply iSup_mono
  intro u
  by_cases hjp : jointProximity (C := (MC : Set (ι → A))) (u := u) δ
  · -- jointProximity ⇒ ∀ γ close (via the helper), so both `if`s pick the 0 branch.
    -- `rw` closes the residual `0 ≤ 0` goal automatically via its built-in `rfl` step.
    have h_all : ∀ γ : F, δᵣ(u 0 + γ • u 1, (MC : Set (ι → A))) ≤ δ :=
      jointProximity_imp_line_close MC u δ hjp
    rw [if_pos h_all, if_pos hjp]
  · by_cases h_all : ∀ γ : F, δᵣ(u 0 + γ • u 1, (MC : Set (ι → A))) ≤ δ
    · -- `epsPG` picks 0; `epsCA` picks Pr ≥ 0.
      rw [if_pos h_all, if_neg hjp]
      exact zero_le
    · -- Both pick the same `Pr_γ[line δ-close]` (same expression inside the `Pr`).
      rw [if_neg h_all, if_neg hjp]

/-- **ABF26 Fact 4.5, second inequality.** `ε_ca ≤ ε_mca` for a `Submodule F (ι → A)`.

Pointwise on `u`:

- If `jointProximity`, `epsCA`'s contribution is 0, ≤ anything.
- Otherwise we apply `Pr_le_Pr_of_implies` with the fact that "line δ-close to `MC`" implies
  `mcaEvent MC δ (u 0) (u 1) γ` (in the `¬jointProximity` regime): the witness set `S` for
  the line-close fact has size `≥ (1-δ)·n` and is automatically *not* a joint-agreement
  set (because if it were, `jointProximity` would hold via the equivalence
  `jointAgreement_iff_jointProximity`). -/
theorem epsCA_le_epsMCA (MC : Submodule F (ι → A)) (δ : ℝ≥0) :
    epsCA (F := F) (MC : Set (ι → A)) δ δ ≤ epsMCA (F := F) (MC : Set (ι → A)) δ := by
  unfold epsCA epsMCA
  apply iSup_mono
  intro u
  by_cases hjp : jointProximity (C := (MC : Set (ι → A))) (u := u) δ
  · rw [if_pos hjp]; exact zero_le
  · rw [if_neg hjp]
    -- Probability monotonicity: `Pr_γ[line close] ≤ Pr_γ[mcaEvent]` because, in the
    -- `¬jointProximity` regime, "line δ-close to MC" implies `mcaEvent`. The implication
    -- is proved per γ below.
    apply Pr_le_Pr_of_implies
    intro γ h_line
    -- Step 1: unfold the line-close witness. `h_line : δᵣ(line, MC) ≤ δ` gives a codeword `w`
    -- and a finite set `S` on which `line = w` pointwise.
    rw [relCloseToCode_iff_relCloseToCodeword_of_minDist] at h_line
    obtain ⟨w, hw_mem, hw_close⟩ := h_line
    rw [relCloseToWord_iff_exists_agreementCols] at hw_close
    obtain ⟨S, hS_card_nat, h_word_agree⟩ := hw_close
    have hS_card_real : (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι :=
      (relDist_floor_bound_iff_complement_bound _ _ _).mp hS_card_nat
    -- Step 2: assemble `mcaEvent` with witness `S`, codeword `w` for the line-side, and the
    -- still-to-prove negation on the pair-side.
    refine ⟨S, hS_card_real, ⟨w, hw_mem, fun i hi ↦ ((h_word_agree i).1 hi).symm⟩, ?_⟩
    -- Step 3: ¬ pairJointAgreesOn MC S (u 0) (u 1). Argue by contradiction with `hjp`:
    -- if there were a joint codeword pair agreeing on `S`, `finMapTwoWords` would build a
    -- jointAgreement witness, which `jointAgreement_iff_jointProximity` would lift to
    -- `jointProximity`, contradicting the hypothesis `¬jointProximity`.
    intro h_pair
    apply hjp
    rw [← jointAgreement_iff_jointProximity]
    obtain ⟨v₀, hv₀_mem, v₁, hv₁_mem, h_pair_agree⟩ := h_pair
    refine ⟨S, hS_card_real, finMapTwoWords v₀ v₁, ?_⟩
    intro i
    refine ⟨?_, ?_⟩
    · -- `(finMapTwoWords v₀ v₁) i ∈ MC` by cases on `i : Fin 2`.
      fin_cases i
      · exact hv₀_mem
      · exact hv₁_mem
    · -- `S ⊆ filter (· = u i)` by cases on `i`.
      intro j hj
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      fin_cases i
      · exact (h_pair_agree j hj).1
      · exact (h_pair_agree j hj).2

/-- **ABF26 Fact 4.5.** For an `F`-additive code (here: a `Submodule F (ι → A)`):
`ε_pg(C, δ) ≤ ε_ca(C, δ, δ) ≤ ε_mca(C, δ)`. -/
theorem epsPG_le_epsCA_le_epsMCA (MC : Submodule F (ι → A)) (δ : ℝ≥0) :
    epsPG (F := F) (MC : Set (ι → A)) δ ≤ epsCA (F := F) (MC : Set (ι → A)) δ δ ∧
    epsCA (F := F) (MC : Set (ι → A)) δ δ ≤ epsMCA (F := F) (MC : Set (ι → A)) δ :=
  ⟨epsPG_le_epsCA MC δ, epsCA_le_epsMCA MC δ⟩

/-- **ABF26 Remark 4.2 (level-set form).** Because relative Hamming distance only takes
values in `{0, 1/n, ..., 1}`, the predicate `jointProximity C u δ_int` (which is
`δᵣ(⋈|u, C^⋈ 2) ≤ δ_int`) depends on `δ_int` only through `⌊δ_int · n⌋`. Hence
`epsCA C δ_fld δ_int` is constant on every "level set" `[k/n, (k+1)/n)` of `δ_int`.

The paper states this with a "shift by `β, β' ∈ [0, 1/n)`" idiom (`ε_ca(C, δ, δ + β) =
ε_ca(C, δ, δ + β')`); that form follows from this lemma whenever the interval
`[δ + min β β', δ + max β β']` does not cross a multiple of `1/n` — in particular when
`δ` is itself such a multiple. -/
theorem epsCA_eq_of_floor_eq (C : Set (ι → A)) (δ_fld δ_int δ_int' : ℝ≥0)
    (h : Nat.floor (δ_int * Fintype.card ι) = Nat.floor (δ_int' * Fintype.card ι)) :
    epsCA (F := F) C δ_fld δ_int = epsCA (F := F) C δ_fld δ_int' := by
  unfold epsCA
  apply iSup_congr
  intro u
  -- `jointProximity` is determined by `Δ₀ ≤ ⌊δ · n⌋` via
  -- `relDistFromCode_le_iff_distFromCode_le`, so it agrees on `δ_int` and `δ_int'`
  -- whenever the floors agree.
  have h_iff : jointProximity (C := C) (u := u) δ_int ↔
               jointProximity (C := C) (u := u) δ_int' := by
    unfold jointProximity
    rw [relDistFromCode_le_iff_distFromCode_le, relDistFromCode_le_iff_distFromCode_le, h]
  by_cases hjp : jointProximity (C := C) (u := u) δ_int
  · rw [if_pos hjp, if_pos (h_iff.mp hjp)]
  · rw [if_neg hjp, if_neg (mt h_iff.mpr hjp)]

/-! ## Bridging the predicate-style API in `Basic.lean` to the numeric API here

These iff-lemmas let downstream code that was written against `δ_ε_correlatedAgreement*`
predicates migrate to the numeric `eps*` form (or vice versa) without rewriting proofs. -/

/-- **Bridge.** The predicate `δ_ε_correlatedAgreementAffineLines C δ ε` (from `Basic.lean`)
is equivalent to the numeric inequality `epsCA C δ δ ≤ ε`.

Forward: assume the predicate. For each `u`, the `epsCA` body is either `0` (when
`jointProximity`) or `Pr_γ[line δ-close]`; in the latter case `¬jointAgreement`, so the
predicate's contrapositive gives `Pr ≤ ε`. `iSup_le` concludes.

Backward: assume `epsCA ≤ ε`. For any `u` with `Pr > ε`, the contribution `body u` is at most
`epsCA ≤ ε`. If `¬jointProximity`, `body u = Pr > ε` is a contradiction; so
`jointProximity`, hence `jointAgreement` via the existing equivalence. -/
theorem δ_ε_correlatedAgreementAffineLines_iff_epsCA_le
    (C : Set (ι → A)) (δ ε : ℝ≥0) :
    δ_ε_correlatedAgreementAffineLines (F := F) C δ ε ↔
    epsCA (F := F) C δ δ ≤ (ε : ENNReal) := by
  classical
  constructor
  · intro h_pred
    refine iSup_le fun u ↦ ?_
    by_cases hjp : jointProximity (C := C) (u := u) δ
    · rw [if_pos hjp]; exact zero_le
    · rw [if_neg hjp]
      have h_not_ja : ¬ jointAgreement (C := C) (W := u) δ := by
        rw [jointAgreement_iff_jointProximity]; exact hjp
      by_contra h_gt
      push Not at h_gt
      exact h_not_ja (h_pred u h_gt)
  · intro h_eps u h_pr
    unfold epsCA at h_eps
    -- `iSup_le_iff` turns `⨆ u, body u ≤ ε` into `∀ u, body u ≤ ε`,
    -- then we specialize at this `u`.
    have h_term_le := iSup_le_iff.mp h_eps u
    by_cases hjp : jointProximity (C := C) (u := u) δ
    · rw [jointAgreement_iff_jointProximity]; exact hjp
    · rw [if_neg hjp] at h_term_le
      exact absurd h_pr (not_lt.mpr h_term_le)

/-- **Bridge for curves.** The predicate `δ_ε_correlatedAgreementCurves C δ ε` (from
`Basic.lean`, threshold `k · ε`) is equivalent to the numeric inequality
`epsCA_curves C k δ δ ≤ k · ε`. Same proof recipe as the `AffineLines` bridge. -/
theorem δ_ε_correlatedAgreementCurves_iff_epsCA_curves_le {k : ℕ}
    (C : Set (ι → A)) (δ ε : ℝ≥0) :
    δ_ε_correlatedAgreementCurves (F := F) (k := k) C δ ε ↔
    epsCA_curves (F := F) C k δ δ ≤ ((k * ε : ℝ≥0) : ENNReal) := by
  classical
  constructor
  · intro h_pred
    refine iSup_le fun u ↦ ?_
    by_cases hjp : jointProximity (C := C) (u := u) δ
    · rw [if_pos hjp]; exact zero_le
    · rw [if_neg hjp]
      have h_not_ja : ¬ jointAgreement (C := C) (W := u) δ := by
        rw [jointAgreement_iff_jointProximity]; exact hjp
      by_contra h_gt
      push Not at h_gt
      exact h_not_ja (h_pred u h_gt)
  · intro h_eps u h_pr
    unfold epsCA_curves at h_eps
    have h_term_le := iSup_le_iff.mp h_eps u
    by_cases hjp : jointProximity (C := C) (u := u) δ
    · rw [jointAgreement_iff_jointProximity]; exact hjp
    · rw [if_neg hjp] at h_term_le
      exact absurd h_pr (not_lt.mpr h_term_le)

/-- **Probability union bound for finitely-indexed existentials.** For a `Fin t`-indexed
family of predicates `f k : α → Prop`:

  `Pr_{D}[∃ k, f k r] ≤ ∑ k : Fin t, Pr_{D}[f k r]`.

Used in the proof of ABF26 Lemma 4.7. Local to this file; could be promoted to
`ArkLib/Data/Probability/Instances.lean` if reused elsewhere. -/
theorem Pr_exists_Fin_le_sum {α : Type} (D : PMF α) {t : ℕ} (f : Fin t → α → Prop) :
    Pr_{ let r ← D }[ ∃ k, f k r ] ≤ ∑ k, Pr_{ let r ← D }[ f k r ] := by
  classical
  rw [prob_tsum_form_singleton]
  have h_rhs : (∑ k : Fin t, Pr_{ let r ← D }[ f k r ]) =
               ∑ k : Fin t, ∑' r, D r * (if f k r then (1 : ENNReal) else 0) := by
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    exact prob_tsum_form_singleton _ _
  rw [h_rhs]
  -- Swap finite sum with tsum (Fubini for ENNReal, where summability is automatic).
  rw [← Summable.tsum_finsetSum (fun _ _ ↦ ENNReal.summable)]
  -- Pull D r out of the inner finite sum.
  have h_mul : ∀ r, (∑ k : Fin t, D r * (if f k r then (1 : ENNReal) else 0)) =
                    D r * (∑ k : Fin t, if f k r then (1 : ENNReal) else 0) :=
    fun r ↦ Finset.mul_sum _ _ _ |>.symm
  rw [tsum_congr (fun r ↦ h_mul r)]
  -- Pointwise bound: `D r * I[∃ k, f k r] ≤ D r * ∑ k, I[f k r]`.
  apply ENNReal.tsum_le_tsum
  intro r
  apply mul_le_mul_of_nonneg_left _ (zero_le)
  by_cases h : ∃ k, f k r
  · rw [if_pos h]
    obtain ⟨k₀, hk₀⟩ := h
    calc (1 : ENNReal)
        = if f k₀ r then 1 else 0 := by rw [if_pos hk₀]
      _ ≤ ∑ k : Fin t, if f k r then (1 : ENNReal) else 0 :=
          Finset.single_le_sum (f := fun k ↦ if f k r then (1 : ENNReal) else 0)
            (fun _ _ ↦ zero_le) (Finset.mem_univ k₀)
  · rw [if_neg h]
    exact zero_le

/-- **ABF26 Lemma 4.6.** In the unique-decoding regime `δ < δ_min(C)/2`, `ε_mca` and `ε_ca`
coincide: `ε_mca(C, δ) = ε_ca(C, δ)`.

The unique-decoding hypothesis is expressed as `2 · δ · n < δ_min(C) · n = ‖C‖₀` to avoid
fractional arithmetic in ℕ — equivalent to the paper's `δ < δ_min(C)/2`.

**Status: external admit.** Proof is in [ACFY25, Lemma 4.10] (footnote 6 in ABF26 notes
the proof is for linear codes but generalises to F-additive codes). The argument is not
the obvious case-split: `mcaEvent` *can* hold at specific `γ`-values when `jointProximity`
holds (line agrees with the unique close codeword `v₀ + γ v₁` on `S_pair ∪ {i*}` for an
extra position `i*`, requiring `γ` to satisfy a specific equation per `i*`), and the
equality only follows from a dominance argument over the choice of `u`. Formalising
this in Lean is out of scope for Phase 1; tracked in `docs/kb/ABF26_PLAN.md` §6
conjecture ledger. -/
theorem epsMCA_eq_epsCA_below_udr
    (C : Submodule F (ι → A)) (δ : ℝ≥0)
    (_h_udr : 2 * δ * (Fintype.card ι : ℝ≥0) <
              (Code.dist ((C : Set (ι → A))) : ℝ≥0)) :
    epsMCA (F := F) (A := A) ((C : Set (ι → A))) δ =
    epsCA (F := F) (A := A) ((C : Set (ι → A))) δ δ := by
  sorry -- ABF26-L4.6; external admit [ACFY25 Lem 4.10].

/-- Row-extraction: the `k`-th row of a `Fin t → A`-valued word, as an `A`-valued word. -/
private def row_of {ι : Type} {A : Type} {t : ℕ}
    (w : ι → (Fin t → A)) (k : Fin t) : ι → A :=
  fun j ↦ w j k

/-- **ABF26 Lemma 4.7.** For any F-additive code `C` (here: a `Submodule F (ι → A)`) and
`t : ℕ`: `ε_mca(C^≡t, δ) ≤ t · ε_mca(C, δ)`.

Proof recipe:
1. `mcaEvent` for the interleaved code at `γ` implies `∃ k`, `mcaEvent` for the `k`-th row
   restriction (witness set `S` is shared; if every row admitted a joint codeword pair
   on `S`, assembling them column-by-column would produce a joint codeword pair in
   `C^⋈ (Fin t)` agreeing on `S`, contradicting the interleaved's "no joint pair" clause).
2. `Pr_le_Pr_of_implies` lifts the per-`γ` implication to a probability bound.
3. `Pr_exists_Fin_le_sum` (union bound) splits into a sum over rows.
4. Each row's probability is bounded by `epsMCA C δ` via `le_iSup`.
5. Sum-of-constants reduces to `t · epsMCA C δ`. -/
theorem epsMCA_interleaved_le (C : Submodule F (ι → A)) (t : ℕ) (δ : ℝ≥0) :
    epsMCA (F := F) (A := Fin t → A) ((C : Set (ι → A))^⋈ (Fin t)) δ ≤
    (t : ENNReal) * epsMCA (F := F) (A := A) (C : Set (ι → A)) δ := by
  classical
  unfold epsMCA
  apply iSup_le
  intro u
  -- Step 1: row-decomposition implication.
  have h_imp : ∀ γ : F, mcaEvent ((C : Set (ι → A))^⋈ (Fin t)) δ (u 0) (u 1) γ →
               ∃ k : Fin t,
                 mcaEvent (C : Set (ι → A)) δ (row_of (u 0) k) (row_of (u 1) k) γ := by
    intro γ h_int
    obtain ⟨S, hS_card, ⟨w, hw_mem, hw_eq⟩, h_no_pair_int⟩ := h_int
    by_contra h_all
    push Not at h_all
    -- For each k, ¬ mcaEvent C row k. Specialize at the inherited witness `S`,
    -- noting that the size and line-agreement clauses hold for every row, so the
    -- only way mcaEvent fails for row k is via a joint codeword pair on `S`.
    have h_row_pair :
        ∀ k : Fin t, ∃ v₀ ∈ (C : Set (ι → A)), ∃ v₁ ∈ (C : Set (ι → A)),
                     ∀ j ∈ S, v₀ j = row_of (u 0) k j ∧ v₁ j = row_of (u 1) k j := by
      intro k
      have h_k := h_all k
      -- h_k : ¬ ∃ S', size ∧ line-agree-on-S' ∧ ¬ pair-on-S'.
      -- Specialize at S: ¬ (size_S ∧ line_S ∧ ¬ pair_S). With size_S and line_S
      -- holding (inherited from interleaved), `¬ pair_S` must fail, i.e., pair_S holds.
      have h_neg :
          ¬ ((S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι ∧
             (∃ w' ∈ (C : Set (ι → A)),
                ∀ j ∈ S, w' j = row_of (u 0) k j + γ • row_of (u 1) k j) ∧
             ¬ pairJointAgreesOn (C : Set (ι → A)) S (row_of (u 0) k) (row_of (u 1) k)) :=
        fun h ↦ h_k ⟨S, h.1, h.2.1, h.2.2⟩
      -- size_S inherited from `hS_card`.
      -- line_S: the row-k version of w is in C and agrees on S.
      have h_size : (S.card : ℝ≥0) ≥ (1 - δ) * Fintype.card ι := hS_card
      have h_line : ∃ w' ∈ (C : Set (ι → A)),
                    ∀ j ∈ S, w' j = row_of (u 0) k j + γ • row_of (u 1) k j := by
        refine ⟨row_of w k, hw_mem k, ?_⟩
        intro j hj
        have := hw_eq j hj
        -- this : w j = u 0 j + γ • u 1 j (as (Fin t → A)). Apply at k.
        have h_pt : w j k = (u 0 j + γ • u 1 j) k := congrArg (· k) this
        -- `(u 0 j + γ • u 1 j) k = u 0 j k + γ • u 1 j k`, which unfolds to
        -- `row_of (u 0) k j + γ • row_of (u 1) k j`.
        simp only [row_of, Pi.add_apply, Pi.smul_apply] at h_pt ⊢
        exact h_pt
      -- So `¬ ¬ pair_S` must hold, i.e., `pair_S` holds (Classical: decidable).
      have h_pair_or :
          pairJointAgreesOn (C : Set (ι → A)) S (row_of (u 0) k) (row_of (u 1) k) := by
        by_contra h_no_pair
        exact h_neg ⟨h_size, h_line, h_no_pair⟩
      obtain ⟨v₀, hv₀_mem, v₁, hv₁_mem, h_agree⟩ := h_pair_or
      exact ⟨v₀, hv₀_mem, v₁, hv₁_mem, h_agree⟩
    -- Assemble row-witnesses into a joint codeword pair in `C^⋈ (Fin t)`, contradicting
    -- the interleaved's "no joint pair" clause.
    apply h_no_pair_int
    choose V₀_fn hV₀_mem V₁_fn hV₁_mem h_V_agree using h_row_pair
    -- V₀_fn : Fin t → ι → A,  V₀_fn k j = row k's first witness at j
    refine ⟨fun j k ↦ V₀_fn k j, ?_, fun j k ↦ V₁_fn k j, ?_, ?_⟩
    · intro k; exact hV₀_mem k
    · intro k; exact hV₁_mem k
    · intro j hj
      refine ⟨?_, ?_⟩
      · funext k; exact (h_V_agree k j hj).1
      · funext k; exact (h_V_agree k j hj).2
  -- Step 2 + 3: chain through Pr_le_Pr_of_implies and the union bound.
  refine le_trans (Pr_le_Pr_of_implies _ _ _ h_imp) ?_
  refine le_trans (Pr_exists_Fin_le_sum _ _) ?_
  -- Step 4: each summand ≤ epsMCA C δ.
  refine le_trans (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin t)))
    (fun k _ ↦ le_iSup
      (fun v : WordStack A (Fin 2) ι ↦
        Pr_{let γ ← $ᵖ F}[mcaEvent (C : Set (ι → A)) δ (v 0) (v 1) γ])
      (fun i j ↦ row_of (u i) k j))) ?_
  -- Step 5: sum-of-constants reduces to t * (epsMCA C δ).
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  exact le_of_eq (nsmul_eq_mul _ _)

/-- **ABF26 `lemma:interleaving-mca` [Jo26].** The MCA error of an interleaved code is
*exactly* the MCA error of the base code: for any `F`-additive code `C`, `t ∈ ℕ` and
`δ ∈ (0, 1)`,

  `ε_mca(C^≡t, δ) = ε_mca(C, δ)` .

The canonical ABF26 `.tex` (around lines 1718–1724) states this as a theorem of [Jo26]
("The following theorem, which resolves a previous open question in this document,
shows that the MCA error of an interleaved code is exactly the MCA error of the base
code"). It **supersedes** the proven inequality `epsMCA_interleaved_le`
(`ε_mca(C^≡t, δ) ≤ t · ε_mca(C, δ)`, the paper's earlier L4.7) above: that lemma stays
because it is true and machine-checked in-tree, but this equality is strictly stronger
in both directions (no factor `t`, plus the `≥` direction) and resolves what was
previously an open question in the survey.

**Guards (2026-06-10 re-review).** `0 < t`: at `t = 0` the `Fin 0`-interleaved
alphabet is a singleton, every stack vacuously agrees, and the LHS is provably
`0` (the proven `epsMCA_interleaved_le` already gives `≤ 0·ε`) while the RHS can
be positive — the unguarded equality was refutable. `δ ∈ (0, 1)`: the paper's
Johnson functions/`ε` quantities are defined on `(0,1)` (`.tex` 1346) and [Jo26]
does not cover the endpoints.

Admitted as an external result.

TODO(bib): `[Jo26]` (Sunghyeon Jo, *Interleaving Stability for Mutual Correlated
Agreement and Curve Decodability*, ePrint 2026/891) has no entry in
`blueprint/src/references.bib` yet; add it during the references.bib cleanup pass. -/
theorem epsMCA_interleaved_eq (C : Submodule F (ι → A)) (t : ℕ) (δ : ℝ≥0)
    (_ht : 0 < t) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1) :
    epsMCA (F := F) (A := Fin t → A) ((C : Set (ι → A))^⋈ (Fin t)) δ =
    epsMCA (F := F) (A := A) (C : Set (ι → A)) δ := by
  sorry -- ABF26-L4.7 (equality form); external admit [Jo26].

/-- **Bridge for affine spaces.** The predicate `δ_ε_correlatedAgreementAffineSpaces C δ ε`
(from `Basic.lean`, threshold `ε`) is equivalent to `epsCA_affineSpaces C k δ δ ≤ ε`. Same
proof recipe as the `AffineLines` and `Curves` bridges. -/
theorem δ_ε_correlatedAgreementAffineSpaces_iff_epsCA_affineSpaces_le {k : ℕ}
    (C : Set (ι → A)) (δ ε : ℝ≥0) :
    δ_ε_correlatedAgreementAffineSpaces (F := F) (k := k) C δ ε ↔
    epsCA_affineSpaces (F := F) C k δ δ ≤ (ε : ENNReal) := by
  classical
  constructor
  · intro h_pred
    refine iSup_le fun u ↦ ?_
    by_cases hjp : jointProximity (C := C) (u := u) δ
    · rw [if_pos hjp]; exact zero_le
    · rw [if_neg hjp]
      have h_not_ja : ¬ jointAgreement (C := C) (W := u) δ := by
        rw [jointAgreement_iff_jointProximity]; exact hjp
      by_contra h_gt
      push Not at h_gt
      exact h_not_ja (h_pred u h_gt)
  · intro h_eps u h_pr
    unfold epsCA_affineSpaces at h_eps
    have h_term_le := iSup_le_iff.mp h_eps u
    by_cases hjp : jointProximity (C := C) (u := u) δ
    · rw [jointAgreement_iff_jointProximity]; exact hjp
    · rw [if_neg hjp] at h_term_le
      exact absurd h_pr (not_lt.mpr h_term_le)

end

end ProximityGap
