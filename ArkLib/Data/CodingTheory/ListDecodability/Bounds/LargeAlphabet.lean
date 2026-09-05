/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ListDecodability.Bounds.LargeAlphabet.Barrier

/-!
# The large-alphabet barrier

Attaining the generalized Singleton bound forces an exponentially large alphabet: for a fixed list
size `ℓ ≥ 2` and rate `ρ`, a linear code that is `ℓ`-list-decodable at radius
`ℓ/(ℓ+1)·(1 − ρ − η)` must have `|F| ≥ 2^(α/η)`. That is `large_alphabet_lambda_lower`, after
[BDG24] for `ℓ = 2` and [AGL23] in general, and `large_alphabet_card_ge_exp_of_inv_length` is the
consequence [ABF26] draws from it — at `η = Θ(1/n)`, `|F| ≥ 2^{Ω(n)}`.

The argument runs through `Bounds/LargeAlphabet/`: bound the local neighbourhood of a centre from
`Λ ≤ ℓ`, greedily extract a large *separated* subcode, and contradict a robust minimum-distance
barrier built from sparse large-union families and a pigeonhole count. The source argues
probabilistically at that last step; here it is a counting argument, so no distribution over codes
is needed.

See `ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean` for the family overview and references.

## References

The keys cited here — [ABF26], [AGL23], [BDG24] — are resolved in the reference list of
`ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean`, which every file in this directory shares.
-/

namespace CodingTheory

open scoped NNReal
open Code
open LargeAlphabetBarrier

section LargeAlphabetBarrier

/-- **Attaining the generalized Singleton bound forces a large alphabet** ([ABF26] Theorem 3.10,
after [BDG24] and [AGL23]). For every `ℓ ≥ 2` and `ρ ∈ (0, 1)` there is a constant `α > 0` such
that for every `η > 0` and every sufficiently large `n`, every linear code `C ⊆ F^n` of rate `ρ`
with `|Λ(C, ℓ/(ℓ+1) · (1-ρ-η))| ≤ ℓ` satisfies

  `|F| ≥ 2^{α / η}` ,

so approaching the generalized Singleton bound to within `η` costs alphabet size exponential in
`1/η`. Per [AGL23, Theorem 1.1] the length threshold is `n ≥ Ω_{ℓ,ρ}(1/η)`, which is why `n₀` is
bound *inside* the `∀ η`.

**The rate is pinned by equality, which is faithful but partly vacuous.** [AGL23] states the
barrier for a code "of rate `R`" — Theorem 1.1 as *printed* omits the rate hypothesis altogether,
which is a defect in that paper; the hypothesis appears in its abstract and in the worked
Propositions 3.2/3.3 — and [BDG24] (the `ℓ = 2` progenitor) is stated for `[n, k]`-MDS codes of
fixed dimension. Equality is therefore the faithful reading. The price is that at irrational `ρ` the
statement is vacuous, and at rational `ρ = a/b` it is inhabited only for `b ∣ n`; instantiate at
`ρ = finrank/n`.

A two-sided band `ρ ≤ finrank/n ≤ ρ + 1/n`, as `random_linear_lambda_lower` uses and this file's
own quantification convention prescribes, would remove that vacuity and is supported by [AGL23]'s
*proof*: it rounds `R` down to a multiple of `3/n` and passes to a subcode ("Taking `C′` to be any
subcode of `C` of rate `R′`", Prop. 3.2; "Subcode `C′` has rate at least `R′ = R − (1/n)`",
Prop. 3.3). It is not implied by the printed equality form, though — recovering rate exactly `ρ·n`
from a code of rate in the band needs `ρ·n ∈ ℤ` — so it would be a mild strengthening, and the
choice is left as recorded rather than made.

**The length threshold is the source's, and the quantifier order is load-bearing.** [AGL23] state
`n ≥ Ω_{ℓ,ρ}(1/η)`, i.e. one threshold constant for all `η`; their Theorem 4.3 spells it out as
"there exists `n₀ = n₀(L,R)` such that the following holds for all `n ≥ n₀` **and `ε ≥ 1/n`**". Both
conditions are reproduced below, with `n₀` bound *outside* `∀ η` and `1/η ≤ n` as a hypothesis. A
weaker `∃ n₀` *inside* `∀ η` — letting the threshold depend on `η` arbitrarily — would be the safe
direction, but it would make this theorem's only intended consequence unreachable: instantiating at
`η := c/n` fixes `n` first and then needs `n₀(c/n) ≤ n`, which nothing supplies. That consequence is
`large_alphabet_card_ge_exp_of_inv_length`, and it is the reason this theorem exists in [ABF26] —
the paper never cross-references the theorem itself.

**Two further divergences, both recorded rather than repaired.** (i) [ABF26] states this for an
arbitrary code `C : Σ^k → Σ^n`, and dropping linearity is precisely [AGL23]'s headline advance over
[BDG24]; the theorem below is the linear-over-a-field case, so it does not capture the cited result
in full. (ii) `η` is unguarded, and for `η > 1 − ρ` the radius `ℓ/(ℓ+1)·(1−ρ−η)` is negative, so
`Λ = 0 ≤ ℓ` holds for every code and the statement demands `|F| ≥ 2^(α/η)` unconditionally. Letting
`η ↓ (1−ρ)` therefore forces `α ≤ 1 − ρ`, since `𝔽₂` carries rate-`ρ` codes of every admissible
length. That does not make the statement false — `α := min (α_source) (1−ρ)` still works, shrinking
`α` only weakening the conclusion — but a prover will meet the constraint, and the sources plainly
intend `η` in the meaningful range. -/
theorem large_alphabet_lambda_lower
    (ℓ : ℕ) (_hℓ_ge : 2 ≤ ℓ) (ρ : ℝ) (_hρ_pos : 0 < ρ) (_hρ_lt : ρ < 1) :
    ∃ α : ℝ, 0 < α ∧ ∃ n₀ : ℕ,
      ∀ (η : ℝ), 0 < η →
          ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
            {F : Type} [Field F] [Fintype F] [DecidableEq F]
            (C : Submodule F (ι → F)),
            n₀ ≤ Fintype.card ι →
            1 / η ≤ (Fintype.card ι : ℝ) →
            (Module.finrank F C : ℝ) = ρ * Fintype.card ι →
            Lambda ((C : Set (ι → F))) ((ℓ : ℝ) / (ℓ + 1) * (1 - ρ - η)) ≤ (ℓ : ℕ∞) →
            (Fintype.card F : ℝ) ≥ (2 : ℝ) ^ (α / η) := by
  classical
  let p₀ : ℝ := smallRadius ℓ ρ
  let B₀ : ℕ := neighborhoodCap ℓ ρ
  let Nlocal : ℕ := localLengthThreshold ℓ ρ
  have hp₀ : 0 < p₀ := by
    dsimp only [p₀, smallRadius]
    have hℓpos : (0 : ℝ) < ℓ := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) _hℓ_ge)
    have hgap : 0 < 1 - ρ := by linarith
    positivity
  have hB₀ : 0 < B₀ := by
    dsimp only [B₀, neighborhoodCap]
    omega
  obtain ⟨αsep, hαsep, nsep, hsep⟩ :=
    robust_minimum_distance_barrier
      ℓ _hℓ_ge ρ _hρ_pos _hρ_lt B₀ hB₀
  refine ⟨min αsep ((1 - ρ) / 2), ?_, max Nlocal nsep, ?_⟩
  · exact lt_min hαsep (by linarith)
  · intro η hη ι _ _ _ F _ _ _ C hn hηn hrate hLambda
    by_cases hlarge : (1 - ρ) / 2 ≤ η
    · exact alphabet_card_ge_rpow_of_alpha_le_eta _ _ hη
        ((min_le_right _ _).trans hlarge) Fintype.one_lt_card
    · have hsmall : η < (1 - ρ) / 2 := lt_of_not_ge hlarge
      let p : ℝ := relRadius ℓ ρ η
      have hℓpos : (0 : ℝ) < ℓ := by
        exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) _hℓ_ge)
      have hfacpos : 0 < (ℓ : ℝ) / (ℓ + 1) := by positivity
      have hfaclt : (ℓ : ℝ) / (ℓ + 1) < 1 := by
        apply (div_lt_one (by positivity)).2
        linarith
      have hp₀p : p₀ ≤ p := by
        dsimp only [p₀, p, smallRadius, relRadius]
        apply mul_le_mul_of_nonneg_left _ hfacpos.le
        linarith
      have hp : 0 < p := lt_of_lt_of_le hp₀ hp₀p
      have hplt : p < 1 := by
        dsimp only [p, relRadius]
        have hgaplt : 1 - ρ - η < 1 := by linarith
        have hmul : (ℓ : ℝ) / (ℓ + 1) * (1 - ρ - η) <
            (ℓ : ℝ) / (ℓ + 1) * 1 :=
          mul_lt_mul_of_pos_left hgaplt hfacpos
        nlinarith
      have hnlocal : Nlocal ≤ Fintype.card ι :=
        le_trans (le_max_left Nlocal nsep) hn
      have hnsep : nsep ≤ Fintype.card ι :=
        le_trans (le_max_right Nlocal nsep) hn
      have hdiv : 8 * (ℓ : ℝ) / p₀ ^ ℓ ≤ (Fintype.card ι : ℝ) := by
        calc
          8 * (ℓ : ℝ) / p₀ ^ ℓ ≤
              (Nat.ceil (8 * (ℓ : ℝ) / p₀ ^ ℓ) : ℝ) := Nat.le_ceil _
          _ = (Nlocal : ℝ) := by rfl
          _ ≤ (Fintype.card ι : ℝ) := by exact_mod_cast hnlocal
      have hlocalLength : 8 * (ℓ : ℝ) ≤
          p ^ ℓ * Fintype.card ι := by
        have hp₀pow : 0 < p₀ ^ ℓ := pow_pos hp₀ _
        have hbase : 8 * (ℓ : ℝ) ≤
            p₀ ^ ℓ * Fintype.card ι := by
          apply (div_le_iff₀ hp₀pow).mp at hdiv
          nlinarith
        have hpow : p₀ ^ ℓ ≤ p ^ ℓ :=
          pow_le_pow_left₀ hp₀.le hp₀p ℓ
        have hnnonneg : (0 : ℝ) ≤ Fintype.card ι := by positivity
        nlinarith [mul_le_mul_of_nonneg_right hpow hnnonneg]
      have hlocal := local_neighborhood_bound ℓ _hℓ_ge p hp hplt
        (C : Set (ι → F))
        (by simpa only [p, relRadius] using hLambda) hlocalLength
      have hcap : ∀ c ∈ (C : Set (ι → F)),
          ({x : ι → F | x ∈ (C : Set (ι → F)) ∧
            hammingDist c x ≤
              Nat.floor (boostedRadius ℓ p * Fintype.card ι)} :
            Set (ι → F)).ncard ≤ B₀ := by
        intro c hc
        have hnum : 0 ≤ 4 * ((ℓ : ℝ) ^ 2) := by positivity
        have hfrac : 4 * ((ℓ : ℝ) ^ 2) / p ≤
            4 * ((ℓ : ℝ) ^ 2) / p₀ :=
          div_le_div_of_nonneg_left hnum hp₀ hp₀p
        have hceil := Nat.ceil_mono hfrac
        have hc0 := hlocal c hc
        dsimp only [B₀, neighborhoodCap]
        exact hc0.trans (Nat.add_le_add_left hceil ℓ)
      obtain ⟨D, hDC, hDfin, hDsep, hcard⟩ :=
        greedy_separated_extraction
          (C : Set (ι → F))
          (Nat.floor (boostedRadius ℓ p * Fintype.card ι)) B₀
          (Set.toFinite _) hcap
      have hDsep' : separated D
          (Nat.ceil (boostedRadius ℓ p * Fintype.card ι)) := by
        intro u hu v hv huv
        exact (Nat.ceil_le_floor_add_one
          (boostedRadius ℓ p * Fintype.card ι)).trans
          (hDsep hu hv huv)
      have hDlambda : Lambda D p ≤ (ℓ : ℕ∞) := by
        exact (Lambda_mono_code hDC p).trans
          (by simpa only [p, relRadius] using hLambda)
      have hcardR : ((C : Set (ι → F)).ncard : ℝ) ≤
          (B₀ : ℝ) * (D.ncard : ℝ) := by
        exact_mod_cast hcard
      have hrateCard : (Fintype.card F : ℝ) ^
          (ρ * Fintype.card ι) ≤ (B₀ : ℝ) * (D.ncard : ℝ) := by
        calc
          (Fintype.card F : ℝ) ^ (ρ * Fintype.card ι) =
              (Fintype.card F : ℝ) ^ (Module.finrank F C : ℝ) := by
            rw [hrate]
          _ = ((C : Set (ι → F)).ncard : ℝ) :=
            (submodule_ncard_eq_rpow_finrank C).symm
          _ ≤ (B₀ : ℝ) * (D.ncard : ℝ) := hcardR
      have hFcard : 2 ≤ Fintype.card F := by
        have h := Fintype.one_lt_card (α := F)
        omega
      have hbar := hsep η hη D hFcard hnsep hηn hrateCard hDsep'
        (by simpa only [p, relRadius] using hDlambda)
      have hexp : min αsep ((1 - ρ) / 2) / η ≤ αsep / η :=
        (div_le_div_iff_of_pos_right hη).2 (min_le_left _ _)
      have hpow : (2 : ℝ) ^
          (min αsep ((1 - ρ) / 2) / η) ≤
            (2 : ℝ) ^ (αsep / η) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
      exact hpow.trans hbar

/-- **Attaining the generalized Singleton bound exactly forces an exponentially large alphabet** —
the consequence [ABF26] draws from Theorem 3.10, and the only use it puts that theorem to: "*this
shows that achieving exactly the generalized singleton bound (which implies the case when
`η = Θ(1/n)`) requires an alphabet of exponential size, which is undesirable.*"

At `η := c/n` the barrier's `2^{α/η}` becomes `2^{(α/c)·n}`, so for every `ℓ ≥ 2`, `ρ ∈ (0,1)` and
`c ≥ 1` there is `α > 0` with

  `|Λ(C, ℓ/(ℓ+1) · (1 − ρ − c/n))| ≤ ℓ  ⟹  |F| ≥ 2^{α·n}`

for every rate-`ρ` linear code of sufficiently large length `n`.

**Derived in-tree, sorry-free and axiom-clean** from `large_alphabet_lambda_lower`. `1 ≤ c` is
exactly [AGL23]'s `ε ≥ 1/n` at `η = c/n`, and it is the meaningful range: relative radii are
`1/n`-quantised, so `η < 1/n` asks for a radius finer than the lattice the list size lives on. -/
theorem large_alphabet_card_ge_exp_of_inv_length
    (ℓ : ℕ) (hℓ_ge : 2 ≤ ℓ) (ρ : ℝ) (hρ_pos : 0 < ρ) (hρ_lt : ρ < 1)
    (c : ℝ) (hc : 1 ≤ c) :
    ∃ α : ℝ, 0 < α ∧ ∃ n₀ : ℕ,
      ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
        {F : Type} [Field F] [Fintype F] [DecidableEq F]
        (C : Submodule F (ι → F)),
        n₀ ≤ Fintype.card ι →
        (Module.finrank F C : ℝ) = ρ * Fintype.card ι →
        Lambda ((C : Set (ι → F)))
            ((ℓ : ℝ) / (ℓ + 1) * (1 - ρ - c / Fintype.card ι)) ≤ (ℓ : ℕ∞) →
        (Fintype.card F : ℝ) ≥ (2 : ℝ) ^ (α * Fintype.card ι) := by
  obtain ⟨α, hα_pos, n₀, hmain⟩ := large_alphabet_lambda_lower ℓ hℓ_ge ρ hρ_pos hρ_lt
  have hc_pos : (0 : ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  refine ⟨α / c, div_pos hα_pos hc_pos, n₀, fun {ι} _ _ _ {F} _ _ _ C hn hrate hΛ => ?_⟩
  have hn_pos : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  -- Instantiate the barrier at `η := c/n`, whose two length conditions are `n₀ ≤ n` and `1/η ≤ n`.
  have hη_pos : (0 : ℝ) < c / Fintype.card ι := div_pos hc_pos hn_pos
  have hinv : 1 / (c / (Fintype.card ι : ℝ)) ≤ (Fintype.card ι : ℝ) := by
    rw [one_div_div, div_le_iff₀ hc_pos]
    nlinarith
  have hkey := hmain (c / Fintype.card ι) hη_pos C hn hinv hrate hΛ
  -- `α / (c/n) = (α/c) · n`.
  rwa [show α / (c / (Fintype.card ι : ℝ)) = α / c * Fintype.card ι by
    field_simp] at hkey

end LargeAlphabetBarrier

end CodingTheory
