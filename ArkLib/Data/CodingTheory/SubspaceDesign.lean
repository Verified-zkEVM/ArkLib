/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Folded

/-!
# Subspace-design codes (ABF26 §2.5)

ABF26 Definition 2.16 [GX13]: the τ-subspace-design property for an F-additive code
`C : F^k → (F^s)^n`. Lemmas 2.17 [GG25] and Theorem 2.18 [GK16] are stated as external
admits.

## Main definitions

- `CodingTheory.IsSubspaceDesign` — ABF26 Definition 2.16.

## Main statements

- `CodingTheory.ker_proj_eq_vanish_at` — bridge between `ker(proj i)` and `{a | a i = 0}`
  (proved in-tree).
- `CodingTheory.subspaceDesign_tau_lower` — ABF26 Lemma 2.17 [GG25]: τ-subspace-design
  code of rate `ρ` has `min_r τ(r) ≥ ρ - 1/n` (external admit).
- `CodingTheory.frs_is_subspaceDesign_gk16` — ABF26 Theorem 2.18 [GK16]: folded RS codes
  are τ-subspace-design for explicit τ (external admit; carries GK16's `ω`-generator
  hypothesis that the tex omits, see PAPER_REVS #13).

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
bound for **all** `r ∈ ℕ`; the restriction to `[s]` here is ours, in the safe (weaker-admit)
direction. `r = 0` is genuinely excluded (see below); `r > s` is dropped only because no
in-tree consumer needs it.

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

**Non-negative profile (`_hτ_nonneg`, 2026-06-10 re-review).** A design profile
is a fraction of a dimension, so `τ ≥ 0` is implicit in the paper. It is
load-bearing here: for the trivial code `C = ⊥` the `IsSubspaceDesign`
inequalities are all `0 ≤ 0`, placing no constraint on `τ`, and a *negative*
profile (e.g. `τ ≡ -1` at `n = 2`) falsified the unguarded bound
(`-1 ≥ 0 - 1/2`). With `τ ≥ 0` the degenerate case is consistent
(`τ r ≥ 0 ≥ 0 - 1/n`).

Admitted as an external result. -/
theorem subspaceDesign_tau_lower
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (s : ℕ) (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (_h : IsSubspaceDesign s τ C)
    (_hτ_nonneg : ∀ r, 0 ≤ τ r) :
    ∀ r ∈ Finset.Icc 1 s,
      τ r ≥ (Module.finrank F C : ℝ) / (s * Fintype.card ι) - 1 / Fintype.card ι := by
  sorry -- ABF26-L2.17; external admit [GG25].

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
counterexample — recorded upstream as `PAPER_REVS.md` finding #13. We carry GK16's own
generator hypothesis `_hω_gen` (not a weaker `ord(ω) ≥ k` guard, which blocks the known
counterexample but is not licensed by the cited source — cf. the PAPER_REVS #12 lesson
on unlicensed hybrid strengthenings). -/
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
