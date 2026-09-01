/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ListDecodability.Bounds.Basic
import ArkLib.Data.CodingTheory.ListDecodability.Bounds.AgreementHypergraph
import ArkLib.Data.CodingTheory.SubspaceDesign
import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.Finiteness

/-!
# The subspace-design upper bound, and the code families that satisfy it

[CZ25]'s theorem that a code carrying a subspace-design profile is list-decodable up to a relaxed
generalized Singleton radius, its real-radius and `η`-parameterized reformulations, and the two
code-family corollaries it exists to serve: folded Reed-Solomon codes and univariate multiplicity
codes achieve list-decoding capacity.

See `ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean` for the family overview, the
quantification conventions, and the references.

## References

The keys cited here — [ABF26], [CZ25] — are resolved in the reference list of
`ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean`, which every file in this directory shares.
-/

namespace CodingTheory

open scoped NNReal
open Code

section SubspaceDesignUpperBounds

/-- **Subspace-design codes are list-decodable up to capacity** — [CZ25, Theorem B.5], the
one-integer-parameter form at [CZ25]'s `(k−1)`-level design premise. This is the engine behind
[ABF26] Theorem 3.4 and Corollary 3.5, but it is **not** [ABF26] Theorem 3.4 as printed; see the
last paragraph.

[CZ25, Theorem B.5] verbatim, in its own variables: "Given a `F`-linear code `C ⊆ (F^s)^n` of block
length `n` and rate `R = k/sn`. Assume that `C ⊆ (F^s)^n` is a `(ℓ, ℓ(k−1)/(s−ℓ+1))`-strong
subspace designable code for all `ℓ ≤ s`. Then, `C` is `(L/(L+1) · (1 − sR/(s−L+1)), L)`
(average-radius) list-decodable for any `L ≤ s`." The `IsSubspaceDesign` condition is
`(∑ᵢ dim Aᵢ)/n ≤ dim A · τ(r)`, i.e. a budget of `n · dim A · τ(r)`, so [CZ25]'s
`(ℓ, ℓ(k−1)/(s−ℓ+1))` premise is exactly the profile `τ(ℓ) = (sR − 1/n)/(s−ℓ+1)` — the `(k−1)`
level, since `sR − 1/n = (k−1)/n`. For every integer `1 ≤ L ≤ s`,

  `|Λ(C, L/(L+1) · (1 − sR/(s−L+1)))| ≤ L` .

**Two weakenings of this premise are each FALSE, and both were caught by compiled
counterexamples.** The statement is brittle in exactly one direction, so both are recorded.

*Arbitrary `τ`.* An early version quantified over an arbitrary `τ : ℕ → ℝ` while asserting [CZ25]'s
sharp `L/(L+1)` radius. Over `𝔽₂` with `ι = Fin 2`, `s = 1` and `C = span {(1,1)}`, the profile
`τ ≡ 0` *is* a legitimate subspace design — no nonzero codeword vanishes anywhere, so
`A ⊓ ker (proj i) = ⊥` and every design sum is `0` — yet at `L = s = 1` the radius `1/2 · (1 − 0)`
has absolute radius `⌊1/2 · 2⌋ = 1`, and the ball around `(0,1)` holds both codewords, giving
`Λ ≥ 2 > 1`. `τ ≡ 0` is monotone and non-negative, so **neither monotonicity nor non-negativity
rescues the arbitrary-`τ` form**; what fails is decoupling `τ` from the rate.

*The `k` level.* Pinning `τ` to the rate is still not enough. The profile `sR/(s−r+1)` — [ABF26]
Theorem 2.18's printed profile, one notch weaker than [CZ25]'s — also makes this statement
**false**. Over `𝔽₂` with `ι = Fin 3`, `s = 1` and `C = span {(1,1,0)}` (so `k = 1`, `n = 3`,
`R = 1/3`) the `k`-level condition holds *with equality*: the single vanishing coordinate gives
`(∑ᵢ dim Cᵢ)/n = 1/3 = 1 · τ(1)`. But at `L = 1` the radius `1/2 · (1 − 1/3) = 1/3` has absolute
radius `1`, and `(1,0,0)` is at distance `1` from both `(0,0,0)` and `(1,1,0)`, so `Λ ≥ 2 > 1`. An
exhaustive sweep over `𝔽₂` finds 385 such code/`L` pairs at `(s,n) ∈ {(1,3),(1,4),(2,3)}` — so this
is not an `s = 1` artefact — and every one of them fails the `(k−1)` premise, placing the falsity
exactly and only in that notch. Structurally, at `s = 1` the `k` level says only `d ≥ n − k`, while
unique decoding at `(1−ρ)/2` needs `d ≥ n − k + 1` whenever `n − k` is even.

**Why the level is load-bearing rather than a fidelity nicety.** [CZ25]'s Lemma B.4 derives
`∑ᵢ dim(Hᵢ ∩ W) ≥ ℓk/(s−ℓ+1)` and concludes "this contradicts the assumption that `C` is a
`(ℓ, ℓ(k−1)/(s−ℓ+1))`-strong subspace designable code". At the `k` level the derived bound and the
premise coincide, so there is no contradiction to derive and the argument collapses. Nothing
compensates: `R` is the code's own rate and occurs identically in premise and conclusion, so the `k`
level is unambiguously the weaker premise, hence unambiguously the stronger — and false — claim.

`isSubspaceDesign_frsCode_sub_one` supplies this `(k−1)` premise for folded Reed-Solomon codes; its
Wronskian count derives it directly, `isSubspaceDesign_frsCode` being its `1/n`-relaxation.

The rate is carried as a parameter `R` with its defining equation `_hR`, following
`mds_johnson_lambda_le_of_rate_distance`. The equation is an **equality**, not `≤`: a larger `R`
weakens the design premise *and* the conclusion, so the `≤` form is not implied by the source. `R`
is the alphabet-normalized rate `k/(s·n)` of [ABF26] Definition 2.5, the alphabet being `F^s`.

The `if r ∈ Finset.Icc 1 s` guard is the shape `isSubspaceDesign_frsCode_sub_one` produces, and is
necessary: outside `[1, s]` the expression `(sR − 1/n)/(s−r+1)` is negative, which no code
satisfies.

`1 ≤ L` is implicit in [CZ25] (the proof derives a contradiction from `L + 1 ≥ 2` distinct
polynomials; at `L = 0` the claim fails for any word equal to a codeword), and `L ≤ s` is the stated
range.

**What [ABF26] Theorem 3.4 says, and why it is not this.** The paper prints
`Λ(C, 1 − τ(1/η) − η) ≤ (1 − τ(1/η))/η` for a `τ`-subspace-design code at an **arbitrary** `τ` — no
integer parameter, no rate pin, and `τ` applied to the real argument `1/η`. That is an abstraction
of [CZ25] which [CZ25] does not prove, and it is *not* refuted by either counterexample above: at
`τ ≡ 0` it asserts only `Λ(C, 1−η) ≤ 1/η`, which the length-`n` repetition code satisfies for every
`η`. It remains an open generalization. `subspaceDesign_lambda_le_of_eta` is its shape at the pinned
profile. -/
theorem subspaceDesign_lambda_le
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Finite F]
    (s : ℕ) (R : ℝ) (C : Submodule F (ι → Fin s → F))
    (_hR : (LinearCode.alphabetRate C : ℝ) = R)
    (_h : IsSubspaceDesign s
      (fun r => if r ∈ Finset.Icc 1 s then
        (s * R - 1 / Fintype.card ι) / (s - r + 1) else 1) C)
    (L : ℕ) (_hL_pos : 1 ≤ L) (_hL_le : L ≤ s) :
    Lambda ((C : Set (ι → Fin s → F)))
        ((L : ℝ) / (L + 1) * (1 - s * R / (s - L + 1))) ≤ (L : ℕ∞) := by
  classical
  let : DecidableEq (Fin s → F) := Classical.decEq _
  apply Lambda_le_of_forall_finset_card_le
  intro y T hT
  by_contra hTL
  have hbig : L + 1 ≤ T.card := by omega
  obtain ⟨U, hUT, hUcard⟩ := Finset.exists_subset_card_eq hbig
  have hUC : ∀ c ∈ U, c ∈ C := by
    intro c hc
    exact (hT c (hUT hc)).1
  have hUclose : ∀ c ∈ U,
      (Code.relHammingDist y c : ℝ) ≤
        (L : ℝ) / (L + 1) * (1 - s * R / ((s : ℝ) - L + 1)) := by
    intro c hc
    have hcball := (hT c (hUT hc)).2
    simpa only [Code.relHammingBall, Set.mem_ofPred_eq] using hcball
  have hupper0 := agreementWeight_lt_of_subspaceDesign_rate
    _hR _h L _hL_pos _hL_le y U hUcard hUC
  have hupper : (agreementWeight y U : ℝ) <
      (Fintype.card ι : ℝ) * L * (s * R / ((s : ℝ) - L + 1)) := by
    convert hupper0 using 1
    congr
  have hlower : (Fintype.card ι : ℝ) * L *
      (s * R / ((s : ℝ) - L + 1)) ≤ (agreementWeight y U : ℝ) := by
    have hn : (0 : ℝ) < Fintype.card ι := by
      exact_mod_cast Fintype.card_pos
    have hdist : ∀ c ∈ U, (hammingDist c y : ℝ) ≤
        ((L : ℝ) / (L + 1) * (1 - s * R / ((s : ℝ) - L + 1))) * Fintype.card ι := by
      intro c hc
      have hclose := hUclose c hc
      unfold Code.relHammingDist at hclose
      simp only [NNRat.cast_div, NNRat.cast_natCast] at hclose
      rw [div_le_iff₀ hn] at hclose
      rw [hammingDist_comm]
      exact hclose
    have hgen := agreementWeight_ge_of_hammingDist_le
      ((L : ℝ) / (L + 1) * (1 - s * R / ((s : ℝ) - L + 1))) y U hdist
    rw [hUcard] at hgen
    refine le_trans (le_of_eq ?_) hgen
    have hL1 : (L : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  exact (not_lt_of_ge hlower) hupper

/-- **Real-radius form of the subspace-design bound**, derived in-tree from
`subspaceDesign_lambda_le`. If `t` dominates the rate-derived profile on the integers
`1 ≤ L ≤ 1/η` (and `1/η ≤ s` keeps the chosen integer inside [CZ25]'s range), then

  `|Λ(C, 1 − t − η)| ≤ (1 − t)/η` .

This is the engine behind both the real-argument `η`-form (`subspaceDesign_lambda_le_of_eta`) and
the folded-RS corollary (`frs_lambda_le_capacity`, where `t` is the profile evaluated at `1/η`).
The proof instantiates the integer theorem at `L := ⌊(1 − t)/η⌋` and uses
monotonicity of `Λ` in the radius: `L + 1 > (1 − t)/η` makes the integer radius
`L/(L+1)·(1 − sR/(s−L+1))` at least `1 − t − η`, and `L ≤ (1 − t)/η` is the claimed list bound. This
mirrors [CZ25]'s own derivation of its Corollary 2.21 from its Theorem 1.3.

Note this is generic in the *dominating value* `t`, not in the profile: the profile stays pinned,
for the reason spelled out on `subspaceDesign_lambda_le`. -/
theorem subspaceDesign_lambda_le_of_profile_le
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Finite F]
    (s : ℕ) (R : ℝ) (C : Submodule F (ι → Fin s → F))
    (hR : (LinearCode.alphabetRate C : ℝ) = R)
    (h : IsSubspaceDesign s
      (fun r => if r ∈ Finset.Icc 1 s then
        (s * R - 1 / Fintype.card ι) / (s - r + 1) else 1) C)
    (η t : ℝ) (hη_pos : 0 < η) (ht_nonneg : 0 ≤ t)
    (hτ_le : ∀ L : ℕ, 1 ≤ L → (L : ℝ) ≤ 1 / η → s * R / (s - L + 1) ≤ t)
    (hs : 1 / η ≤ (s : ℝ)) :
    (Lambda ((C : Set (ι → Fin s → F))) (1 - t - η) : ENNReal) ≤
      ENNReal.ofReal ((1 - t) / η) := by
  by_cases hquot : (1 : ℝ) ≤ (1 - t) / η
  · -- Main case: `L := ⌊(1 − t)/η⌋ ≥ 1`.
    set L : ℕ := ⌊(1 - t) / η⌋₊ with hL_def
    have hL_pos : 1 ≤ L := Nat.floor_pos.mpr hquot
    have hquot_nonneg : (0 : ℝ) ≤ (1 - t) / η := zero_le_one.trans hquot
    have hLle : (L : ℝ) ≤ (1 - t) / η := Nat.floor_le hquot_nonneg
    have hL_inv : (L : ℝ) ≤ 1 / η := hLle.trans (by gcongr; linarith)
    have hτL : s * R / ((s : ℝ) - L + 1) ≤ t := hτ_le L hL_pos hL_inv
    have hLs : L ≤ s := by exact_mod_cast hL_inv.trans hs
    have key := subspaceDesign_lambda_le s R C hR h L hL_pos hLs
    -- Radius comparison: `1 − t − η ≤ L/(L+1) · (1 − sR/(s−L+1))`.
    have hfloor : (1 - t) / η < (L : ℝ) + 1 := Nat.lt_floor_add_one _
    have h1t : 1 - t < η * ((L : ℝ) + 1) := by
      rw [div_lt_iff₀ hη_pos] at hfloor
      linarith
    have hrad : 1 - t - η ≤ (L : ℝ) / (L + 1) * (1 - s * R / ((s : ℝ) - L + 1)) := by
      have hL1 : (0 : ℝ) < (L : ℝ) + 1 := by positivity
      rw [div_mul_eq_mul_div, le_div_iff₀ hL1]
      have hmul : (L : ℝ) * (s * R / ((s : ℝ) - L + 1)) ≤ (L : ℝ) * t :=
        mul_le_mul_of_nonneg_left hτL (by positivity)
      nlinarith [hmul, h1t]
    have hchain : Lambda ((C : Set (ι → Fin s → F))) (1 - t - η) ≤ (L : ℕ∞) :=
      (Lambda_mono hrad).trans key
    calc (Lambda ((C : Set (ι → Fin s → F))) (1 - t - η) : ENNReal)
        ≤ ((L : ℕ∞) : ENNReal) := ENat.toENNReal_le.mpr hchain
      _ = (L : ENNReal) := ENat.toENNReal_coe L
      _ ≤ ENNReal.ofReal ((1 - t) / η) := by
          rw [← ENNReal.ofReal_natCast]
          exact ENNReal.ofReal_le_ofReal hLle
  · -- Degenerate case: `(1 − t)/η < 1` forces a negative radius and an empty list.
    have hrad_neg : 1 - t - η < 0 := by
      rw [not_le, div_lt_one hη_pos] at hquot
      linarith
    have hempty : ∀ f : ι → Fin s → F,
        closeCodewordsRel ((C : Set (ι → Fin s → F))) f (1 - t - η) = ∅ := by
      intro f
      ext c
      simp only [closeCodewordsRel, Code.relHammingBall, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false, not_and]
      intro _ hball
      exact absurd (hball.trans_lt hrad_neg) (not_lt.mpr (by positivity))
    have hzero : Lambda ((C : Set (ι → Fin s → F))) (1 - t - η) = 0 := by
      simp [Lambda, hempty]
    rw [hzero]
    simp

/-- **The `η`-form of the subspace-design bound**, derived in-tree from
`subspaceDesign_lambda_le`. This is the shape of [ABF26] Theorem 3.4 at the pinned profile: for a
code carrying the `(k−1)`-level design profile and any `η > 0` with `1/η ≤ s`,

  `|Λ(C, 1 − sR/(s−1/η+1) − η)| ≤ (1 − sR/(s−1/η+1))/η` .

**No rounding is involved.** [ABF26] prints the profile at the real argument `1/η`, which is
ill-typed for a `τ : ℕ → ℝ` indexed by a dimension. It does not need to be rounded to be reproduced:
`subspaceDesign_lambda_le_of_profile_le` is generic in the *dominating value*, so instantiating it
at `t := sR/(s − 1/η + 1)` — the profile expression at the real argument — gives the paper's display
verbatim, with the domination hypothesis immediate from `L ≤ 1/η ⇒ s − L + 1 ≥ s − 1/η + 1`.
An earlier version instead rounded `1/η` down in both the radius and the bound; the two roundings
pull in opposite directions (the profile is increasing, so a smaller argument enlarges the radius
but also enlarges the bound), so that statement neither implied nor followed from the paper's. It
also needed `η ≤ 1` to keep `⌊1/η⌋ ≥ 1`, which the real-argument form does not.

Non-negativity of `R` is *proved* rather than hypothesised (`LinearCode.alphabetRate` lands in
`ℚ≥0`). `1/η ≤ s` keeps the instantiation point inside [CZ25]'s range `L ≤ s`; it is the hypothesis
the abstract statement omits and its only instantiation carries as `1/η < s`. -/
theorem subspaceDesign_lambda_le_of_eta
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Finite F]
    (s : ℕ) (R : ℝ) (C : Submodule F (ι → Fin s → F))
    (hR : (LinearCode.alphabetRate C : ℝ) = R)
    (h : IsSubspaceDesign s
      (fun r => if r ∈ Finset.Icc 1 s then
        (s * R - 1 / Fintype.card ι) / (s - r + 1) else 1) C)
    (η : ℝ) (hη_pos : 0 < η) (hηs : 1 / η ≤ (s : ℝ)) :
    (Lambda ((C : Set (ι → Fin s → F)))
        (1 - s * R / ((s : ℝ) - 1 / η + 1) - η) : ENNReal) ≤
      ENNReal.ofReal ((1 - s * R / ((s : ℝ) - 1 / η + 1)) / η) := by
  -- `R ≥ 0`: it is a rate, and `alphabetRate` lands in `ℚ≥0`.
  have hR_nonneg : 0 ≤ R := by rw [← hR]; positivity
  have hden_pos : (0 : ℝ) < (s : ℝ) - 1 / η + 1 := by linarith
  have hsR_nonneg : (0 : ℝ) ≤ s * R := by positivity
  refine subspaceDesign_lambda_le_of_profile_le s R C hR h η
    (s * R / ((s : ℝ) - 1 / η + 1)) hη_pos
    (div_nonneg hsR_nonneg hden_pos.le) (fun L hL1 hLle => ?_) hηs
  -- Profile domination: `L ≤ 1/η` shrinks the denominator, so the value only grows.
  exact div_le_div_of_nonneg_left hsR_nonneg hden_pos (by linarith)

/-- **Folded Reed-Solomon codes are list-decodable up to capacity** ([ABF26] Corollary 3.5, after
[CZ25, Corollary 2.21]). For `C := FRS[F, L, k, s, ω]` of rate `ρ` and any `η > 0` with `1/η < s`:

  `|Λ(C, 1 - ρ·s/(s - 1/η + 1) - η)| ≤ (s·(1-ρ) + 1 - 1/η) / (η·(s + 1 - 1/η))` .

When `η ≥ √(3/s)` the bound simplifies to `|Λ(C, 1 - ρ - η)| ≤ 1/η`.

**Derived in-tree**, not a separate admit: from `subspaceDesign_lambda_le` (via
`subspaceDesign_lambda_le_of_profile_le` at the real-argument profile value
`t := ρ·s/(s − 1/η + 1)`) together with `isSubspaceDesign_frsCode_sub_one`, whose Wronskian count
delivers exactly the `(k−1)`-level profile this chain needs. The `1/n`-relaxed
`isSubspaceDesign_frsCode` does **not** suffice: at that level `subspaceDesign_lambda_le` is false.
This is the route [CZ25] use for their Corollary 2.21 and [ABF26] for this one. The bound equals
`(1 − t)/η` verbatim, since
`1 − sρ/(s−1/η+1) = (s(1−ρ)+1−1/η)/(s+1−1/η)`.

**Rate convention.** `FRS[F, L, k, s, ω] ⊆ (F^s)^n` has rate `ρ = k / (s·n)`, the alphabet being
`F^s`, **not** `k/n`. With this `ρ` both the radius and the list bound are the source's expressions
verbatim; the radius numerator `ρ·s` is `k/n`.

**Why `_hk_le : k ≤ s·n` is needed.** It is what makes the paper's `ρ = k/(s·n)` equal to
`LinearCode.alphabetRate`, which is `min k (s·n)/(s·n)`. An earlier version avoided this hypothesis
by using only `alphabetRate ≤ ρ` and letting profile domination absorb the gap — but that route
depended on `subspaceDesign_lambda_le` holding at an arbitrary profile, which is **false** (see its
docstring). With the profile pinned to the rate by an equality, the rate must match exactly, so the
below-saturation hypothesis is genuine. It is harmless: the capacity regime has `ρ < 1` anyway.

**Admissibility.** [ABF26] Definition 2.15 bakes `(L, s)`-admissibility of `ω` into the code;
ArkLib's `frsCode` deliberately does not, so it is carried here as `_hadm`. Without it the fold
degenerates — at `ω = 1` all folds collapse — and the capacity bound is false.

**Generator hypothesis.** `_hω_gen : ω` generates `F×` is inherited from
`isSubspaceDesign_frsCode_sub_one`, whose unguarded form is FALSE for low-order `ω` (counterexample
`ω = -1` over `𝔽₁₀₁`; see that declaration's docstring). It is also the classical folded-RS setting
of [CZ25] and Guruswami–Rudra, where the fold element is primitive. `ω ≠ 0` is not a separate
hypothesis, being derivable from it. -/
theorem frs_lambda_le_capacity
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Fintype F]
    (domain : ι ↪ F) (k s : ℕ) (ω : F)
    (_hs_pos : 0 < s)
    (_hFn : Fintype.card ι < Fintype.card F)
    (_hk_le : k ≤ s * Fintype.card ι)
    (_hadm : ReedSolomon.Folded.Admissible (Finset.univ.map domain) s ω)
    (_hω_gen : orderOf ω = Fintype.card F - 1)
    (η : ℝ) (_hη_pos : 0 < η) (_hη_lt_s : 1 / η < s) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / (s * n)
    let δ : ℝ := 1 - ρ * s / (s - 1 / η + 1) - η
    let bound : ℝ := (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
    (Lambda ((ReedSolomon.Folded.frsCode domain k s ω : Set (ι → Fin s → F))) δ :
        ENNReal) ≤
      ENNReal.ofReal bound := by
  intro n ρ δ bound
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr Fintype.card_pos
  have hs_posR : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr _hs_pos
  have hdenom_pos : (0 : ℝ) < (s : ℝ) - 1 / η + 1 := by linarith
  -- `ω ≠ 0`, from the generator hypothesis: `|F| ≥ 2` makes `orderOf ω ≠ 0`.
  have hω0 : ω ≠ 0 := by
    intro hzero
    rw [hzero, orderOf_zero] at _hω_gen
    have hn1 : 1 ≤ Fintype.card ι := Fintype.card_pos
    omega
  -- FRS carries the rate-derived design profile.
  have hdesign := isSubspaceDesign_frsCode_sub_one domain k s ω _hFn _hadm _hω_gen
  -- Below saturation, `alphabetRate = k/(s·n) = ρ`.
  have hrate : (LinearCode.alphabetRate
      (ReedSolomon.Folded.frsCode domain k s ω) : ℝ) = ρ := by
    rw [LinearCode.alphabetRate_cast_eq,
      ReedSolomon.Folded.dim_frsCode domain k s ω _hadm hω0 _hk_le]
  have hρ_nonneg : (0 : ℝ) ≤ ρ := by rw [← hrate]; positivity
  have hρs_nonneg : (0 : ℝ) ≤ ρ * s := by positivity
  have ht_nonneg : 0 ≤ ρ * s / ((s : ℝ) - 1 / η + 1) := div_nonneg hρs_nonneg hdenom_pos.le
  have key := subspaceDesign_lambda_le_of_profile_le s ρ
    (ReedSolomon.Folded.frsCode domain k s ω) hrate (hrate ▸ hdesign) η
    (ρ * s / ((s : ℝ) - 1 / η + 1)) _hη_pos ht_nonneg
    (fun L hL1 hLle => ?_) _hη_lt_s.le
  · -- Convert `key` to the source-display radius and bound.
    have hδ_eq : δ = 1 - ρ * s / ((s : ℝ) - 1 / η + 1) - η := rfl
    have hbound_eq : bound = (1 - ρ * s / ((s : ℝ) - 1 / η + 1)) / η := by
      have hd2 : ((s : ℝ) - 1 / η + 1) ≠ 0 := hdenom_pos.ne'
      have hη0 : η ≠ 0 := _hη_pos.ne'
      -- The `1/η` nested inside `s ± 1/η ± 1` clears to `s·η + η − 1`; `field_simp` needs
      -- *that* nonzero to fully cancel, so supply it (from `hdenom_pos · η`).
      have hd3 : (-1 + (s : ℝ) * η + η) ≠ 0 := by
        have hmul := mul_pos hdenom_pos _hη_pos
        have heq : ((s : ℝ) - 1 / η + 1) * η = -1 + (s : ℝ) * η + η := by
          field_simp; ring
        rw [heq] at hmul; exact hmul.ne'
      change (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
        = (1 - ρ * s / ((s : ℝ) - 1 / η + 1)) / η
      have hkey : (-1 + (s : ℝ) * η + η) * (-1 + (s : ℝ) * η + η)⁻¹ = 1 :=
        mul_inv_cancel₀ hd3
      field_simp
      linear_combination hkey
    rw [hδ_eq, hbound_eq]
    exact key
  · -- Profile domination on `1 ≤ L ≤ 1/η`: a smaller `L` only shrinks the denominator.
    have hLs : (L : ℝ) < (s : ℝ) := lt_of_le_of_lt hLle _hη_lt_s
    have hstep : (s : ℝ) * ρ = ρ * s := by ring
    rw [hstep]
    exact div_le_div_of_nonneg_left hρs_nonneg hdenom_pos (by linarith)

/-- **Univariate multiplicity codes are list-decodable up to capacity** — the corollary [ABF26]
asserts exists without stating it: "*Since folded Reed-Solomon codes are subspace-design codes the
above theorem implies that they are list decodable up to capacity (**a similar corollary can be
derived for univariate multiplicity codes**)*". For `C := UM[F, L, k, s]` of rate `ρ` and any
`η > 0` with `1/η < s`, the same display as Corollary 3.5:

  `|Λ(C, 1 - ρ·s/(s - 1/η + 1) - η)| ≤ (s·(1-ρ) + 1 - 1/η) / (η·(s + 1 - 1/η))` .

**Derived in-tree, sorry-free and axiom-clean** by the same chain as `frs_lambda_le_capacity`:
`subspaceDesign_lambda_le` via `subspaceDesign_lambda_le_of_profile_le` at
`t := ρ·s/(s − 1/η + 1)`, with the `(k−1)`-level design premise supplied by
`isSubspaceDesign_umCode_sub_one`.

[CZ25] prove the multiplicity case directly too, as their Theorem 1.5 — "*Let `p` be a prime number.
For any integers `s, n, L ≥ 1`, `k ∈ [n]`, and distinct `α₁, …, α_n ∈ F_p`, the code
`MULT^{(s)}_{n,k}(α₁, …, α_n)` over the alphabet `F_p^s` is `(L/(L+1)(1 − sR/(s−L+1)), L)`
list-decodable*" — with Corollary 1.6 / A.10 as the `(1 − R − ε, O(1/ε))` form. Going through the
field-generic Theorem B.5 instead gives this for **any** field satisfying the characteristic
condition, not only prime fields.

**Hypotheses.** `_hchar` is inherited from `isSubspaceDesign_umCode_sub_one`; it is [ABF26] Theorem
2.18's `char(F) > k`, relaxed to `k ≤ ringChar F`, which is all the Wronskian argument needs (`d!`
must be a unit for `d < k`) and which the disjunction with `ringChar F = 0` keeps from forcing
`k = 0` in characteristic zero. `_hk_le : k ≤ s·n` is what makes the paper's `ρ = k/(s·n)` equal
`LinearCode.alphabetRate`; unlike the folded case there is no admissibility or generator
hypothesis, multiplicity codes needing neither. -/
theorem um_lambda_le_capacity
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Finite F]
    (domain : ι ↪ F) (k s : ℕ)
    (_hs_pos : 0 < s)
    (_hchar : ringChar F = 0 ∨ k ≤ ringChar F)
    (_hk_le : k ≤ s * Fintype.card ι)
    (η : ℝ) (_hη_pos : 0 < η) (_hη_lt_s : 1 / η < s) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / (s * n)
    let δ : ℝ := 1 - ρ * s / (s - 1 / η + 1) - η
    let bound : ℝ := (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
    (Lambda ((ReedSolomon.Multiplicity.umCode domain k s : Set (ι → Fin s → F))) δ : ENNReal) ≤
      ENNReal.ofReal bound := by
  intro n ρ δ bound
  have hn_pos : (0 : ℝ) < n := Nat.cast_pos.mpr Fintype.card_pos
  have hs_posR : (0 : ℝ) < (s : ℝ) := Nat.cast_pos.mpr _hs_pos
  have hdenom_pos : (0 : ℝ) < (s : ℝ) - 1 / η + 1 := by linarith
  -- Multiplicity codes carry the `(k-1)`-level design profile.
  have hdesign := isSubspaceDesign_umCode_sub_one domain k s _hchar
  -- Below saturation, `alphabetRate = k/(s·n) = ρ`.
  have hrate : (LinearCode.alphabetRate (ReedSolomon.Multiplicity.umCode domain k s) : ℝ) = ρ := by
    rw [LinearCode.alphabetRate_cast_eq,
      ReedSolomon.Multiplicity.dim_umCode domain _hchar _hk_le]
  have hρ_nonneg : (0 : ℝ) ≤ ρ := by rw [← hrate]; positivity
  have hρs_nonneg : (0 : ℝ) ≤ ρ * s := by positivity
  have ht_nonneg : 0 ≤ ρ * s / ((s : ℝ) - 1 / η + 1) := div_nonneg hρs_nonneg hdenom_pos.le
  have key := subspaceDesign_lambda_le_of_profile_le s ρ
    (ReedSolomon.Multiplicity.umCode domain k s) hrate (hrate ▸ hdesign) η
    (ρ * s / ((s : ℝ) - 1 / η + 1)) _hη_pos ht_nonneg
    (fun L hL1 hLle => ?_) _hη_lt_s.le
  · -- Convert `key` to the source-display radius and bound, as in `frs_lambda_le_capacity`.
    have hδ_eq : δ = 1 - ρ * s / ((s : ℝ) - 1 / η + 1) - η := rfl
    have hbound_eq : bound = (1 - ρ * s / ((s : ℝ) - 1 / η + 1)) / η := by
      have hd2 : ((s : ℝ) - 1 / η + 1) ≠ 0 := hdenom_pos.ne'
      have hη0 : η ≠ 0 := _hη_pos.ne'
      have hd3 : (-1 + (s : ℝ) * η + η) ≠ 0 := by
        have hmul := mul_pos hdenom_pos _hη_pos
        have heq : ((s : ℝ) - 1 / η + 1) * η = -1 + (s : ℝ) * η + η := by
          field_simp; ring
        rw [heq] at hmul; exact hmul.ne'
      change (s * (1 - ρ) + 1 - 1 / η) / (η * (s + 1 - 1 / η))
        = (1 - ρ * s / ((s : ℝ) - 1 / η + 1)) / η
      have hkey : (-1 + (s : ℝ) * η + η) * (-1 + (s : ℝ) * η + η)⁻¹ = 1 :=
        mul_inv_cancel₀ hd3
      field_simp
      linear_combination hkey
    rw [hδ_eq, hbound_eq]
    exact key
  · -- Profile domination on `1 ≤ L ≤ 1/η`.
    have hLs : (L : ℝ) < (s : ℝ) := lt_of_le_of_lt hLle _hη_lt_s
    have hstep : (s : ℝ) * ρ = ρ * s := by ring
    rw [hstep]
    exact div_le_div_of_nonneg_left hρs_nonneg hdenom_pos (by linarith)

end SubspaceDesignUpperBounds

end CodingTheory
