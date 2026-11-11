/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, XC0R
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability.Bounds.RandomLinear.Main
public import Mathlib.FieldTheory.Finite.Basic

/-!
# The random-linear-code list-size lower bound

[ABF26] Theorem 3.11, after [GLMRSW22, Theorem 4.1]: a uniformly random linear code of rate just
below capacity has a large list, except with exponentially small probability, in counting form
(`random_linear_lambda_lower`), and its existence form (`random_linear_lambda_lower_exists`).
The proof is in `Bounds/RandomLinear/`.

## References

The keys cited here — [ABF26], [GLMRSW22] — are resolved in the reference list of
`ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean`.
-/

@[expose] public section

namespace CodingTheory

open Code

section RandomLinear

/-- **A random linear code of near-capacity rate has a large list** ([ABF26] Theorem 3.11, after
[GLMRSW22, Theorem 4.1]).

The source, verbatim in its own variables: "Fix a prime power `q`, fix `p ∈ (0, 1 − 1/q)`, and fix
`δ ∈ (0, 1)`. There exists `ε_{p,q,δ} > 0` such that for all `ε ∈ (0, ε_{p,q,δ})` and `n`
sufficiently large, a random linear code in `F_q^n` of rate `1 − h_q(p) − ε` is not
`(p, ⌊h_q(p)/ε − δ⌋)`-list-decodable with probability `1 − q^{−Ω(n)}`." Its random model, from §1.1,
is "a random linear code is a uniformly random subspace of `F_q^n` of certain dimension" — so the
counting form below is the source's probability exactly, not an approximation of it. Its §1.2
working model is the code of a uniformly random parity-check tuple. The proof transfers from that
model to uniform subspaces by counting: every code of dimension `n - m` has the same number of
independent parity-check tuples (`card_fiber_pcCode`), at least half of all tuples are independent
(`card_linIndep_ge`), so the fraction of `k`-dimensional codes with a property is at most twice the
fraction of tuples whose code has it (`ncard_subspace_le_of_pc`).

**Endpoint.** [GLMRSW22] define `(p, L)`-list-decodable with the **strict** condition
"`|{c ∈ C : δ(c,z) ≤ p}| < L`" (§1). Consequently, their "not
`(p, ⌊h_q(p)/ε − δ⌋)`-list-decodable" means `Λ ≥ ⌊·⌋`. The bad event below is therefore
`Λ < ⌊·⌋`, whose complement gives exactly the source-supported weak lower bound. [ABF26]
Theorem 3.11 prints a strict `>`, one integer stronger than its cited source; that printing is not
followed here.

Variable map into the form below: the source's radius `p` is our `δ`, its slack `δ` is our `ε`,
its `ε_{p,q,δ}` is our `γ`, and its rate `1 − h_q(p) − ε` is our `ρ` — so its `ε` is
`1 − H_q(δ) − ρ`, giving the list bound `⌊H_q(δ)/(1 − H_q(δ) − ρ) − ε⌋`.

**Probability as counting.** ArkLib has no probability distribution over linear codes, so the
`1 − q^{−Ω(n)}` statement is carried in its equivalent finite counting form over the uniform
family `{C : Submodule F (ι → F) | finrank C = k}`:

  `#{C : finrank C = k ∧ |Λ(C, δ)| < ⌊…⌋} ≤ q^{−c·n} · #{C : finrank C = k}`

with `c > 0` the `Ω(n)` constant, whose dependence on `q, δ, ε, ρ` is licensed by its binder
position. This is deliberately stronger than bare existence of one witness code, which loses the
high-probability content; that weaker form is *derived* below as
`random_linear_lambda_lower_exists`.

**Dimension pin.** The source's code has rate exactly `ρ`, with dimension `ρ·n` treated as an
integer for exposition. Exact real equality is unsatisfiable at irrational `ρ`, so the dimension is
pinned two-sidedly into `ρ ≤ k/n ≤ ρ + 1/n`, admitting `k = ⌈ρ·n⌉` up to the boundary case.
The proof uses only `ρ ≤ k/n`. The upper bound stays so that the family's rate is `ρ`.

**Proof.** The bad distribution is not implicitly rare
(`RandomLinearInternal.entQ_badLaw_mulVec_lower`). A second-moment count over parity-check matrices
turns this into the counting bound (`RandomLinearInternal.random_linear_contains_list`). -/
theorem random_linear_lambda_lower
    (q : ℕ) (hq_pp : IsPrimePow q)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1 - 1 / q)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ ρ : ℝ, 1 - qEntropy q δ - γ < ρ → ρ < 1 - qEntropy q δ →
        ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ,
          ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
            {F : Type} [Field F] [Fintype F] [DecidableEq F],
            Fintype.card F = q → n₀ ≤ Fintype.card ι →
            ∀ k : ℕ,
              ρ ≤ (k : ℝ) / Fintype.card ι →
              (k : ℝ) / Fintype.card ι ≤ ρ + 1 / Fintype.card ι →
              (({C : Submodule F (ι → F) | Module.finrank F C = k ∧
                  Lambda ((C : Set (ι → F))) δ <
                    ((Nat.floor (qEntropy q δ / (1 - qEntropy q δ - ρ) - ε) : ℕ) :
                      ℕ∞)}.ncard : ℝ))
                ≤ (q : ℝ) ^ (-(c * (Fintype.card ι : ℝ))) *
                    (({C : Submodule F (ι → F) | Module.finrank F C = k}.ncard : ℝ)) := by
  have hq2 : 2 ≤ q := hq_pp.two_le
  -- The bad distribution is not implicitly rare, with slack `ε/2`.
  obtain ⟨L₀, hL₀⟩ :=
    RandomLinearInternal.entQ_badLaw_mulVec_lower q hq2 δ hδ_pos hδ_lt (ε / 2) (by positivity)
  -- `γ := min (h/(L₀+1)) ((1-h)/2)` with `h = H_q(δ)`.
  obtain ⟨γ, hγ_pos, hγ⟩ :=
    RandomLinearInternal.exists_rate_margin q hq2 δ hδ_pos hδ_lt ε hε_pos hε_lt L₀
  refine ⟨γ, hγ_pos, fun ρ hργ hρH => ?_⟩
  obtain ⟨hρ_pos, hL_ge, hβρ⟩ := hγ ρ hργ hρH
  obtain ⟨c, hc, n₀, hmain⟩ := RandomLinearInternal.random_linear_contains_list q hq2 δ hδ_pos hδ_lt
    (Nat.floor (qEntropy q δ / (1 - qEntropy q δ - ρ) - ε))
    (qEntropy q δ + qEntropy q δ /
      ((Nat.floor (qEntropy q δ / (1 - qEntropy q δ - ρ) - ε) : ℕ) + ε / 2))
    (fun hF s hs A hA => hL₀ _ hL_ge hF s hs A hA) ρ hρ_pos hβρ
  exact ⟨c, hc, n₀, fun {ι} _ _ _ {F} _ _ _ hF hn k hk₁ _hk₂ => hmain hF hn k hk₁⟩

/-- **Existence form of the random-linear-code lower bound**, derived in-tree from the
high-probability counting form `random_linear_lambda_lower`: some linear code `C ⊆ F^n` with
dimension in the band `ρ ≤ finrank/n ≤ ρ + 1/n` satisfies

  `|Λ(C, δ)| ≥ ⌊H_q(δ) / (1 - H_q(δ) - ρ) - ε⌋` .

The bad-event count is below the whole family's, the family `{C | finrank C = ⌈ρ·n⌉}` is nonempty
(a coordinate-kernel subspace realises any dimension `≤ n`), so a good code exists.

For a prime power `q`, `γ` is at most `(1 − H_q(δ))/2`, which is positive by `qEntropy_lt_one`,
so every admissible rate `ρ` is positive. -/
theorem random_linear_lambda_lower_exists
    (q : ℕ)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1 - 1 / q)
    (ε : ℝ) (hε_pos : 0 < ε) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ ρ : ℝ, 1 - qEntropy q δ - γ < ρ → ρ < 1 - qEntropy q δ →
        ∃ n₀ : ℕ,
          ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
            {F : Type} [Field F] [Fintype F] [DecidableEq F],
            Fintype.card F = q → n₀ ≤ Fintype.card ι →
            ∃ C : Submodule F (ι → F),
              ρ ≤ (Module.finrank F C : ℝ) / Fintype.card ι ∧
              (Module.finrank F C : ℝ) / Fintype.card ι ≤ ρ + 1 / Fintype.card ι ∧
              ((Nat.floor (qEntropy q δ / (1 - qEntropy q δ - ρ) - ε) : ℕ) : ℕ∞) ≤
                Lambda ((C : Set (ι → F))) δ := by
  by_cases hq_pp : IsPrimePow q
  swap
  · refine ⟨1, zero_lt_one, fun ρ _ _ ↦ ⟨0, ?_⟩⟩
    intro ι _ _ _ F _ _ _ hcard _
    exact (hq_pp (hcard ▸ FiniteField.isPrimePow_card F)).elim
  let ε' := min ε (1 / 2)
  have hε' : 0 < ε' := lt_min hε_pos (by norm_num)
  have hε'1 : ε' < 1 := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨γ, hγ_pos, hmain⟩ :=
    random_linear_lambda_lower q hq_pp δ hδ_pos hδ_lt ε' hε' hε'1
  have hH1 : qEntropy q δ < 1 := qEntropy_lt_one hq_pp.two_le hδ_pos.le hδ_lt
  refine ⟨min γ ((1 - qEntropy q δ) / 2), lt_min hγ_pos (by linarith), fun ρ hργ hρH => ?_⟩
  have hρ0 : 0 ≤ ρ := by linarith [min_le_right γ ((1 - qEntropy q δ) / 2)]
  obtain ⟨c, hc_pos, n₀, hbound⟩ :=
    hmain ρ (by linarith [min_le_left γ ((1 - qEntropy q δ) / 2)]) hρH
  refine ⟨n₀, fun {ι} _ _ _ {F} _ _ _ hcard hn => ?_⟩
  have hn_pos : 0 < Fintype.card ι := Fintype.card_pos
  have hn_posR : (0 : ℝ) < (Fintype.card ι : ℝ) := Nat.cast_pos.mpr hn_pos
  -- `ρ ≤ 1` via `0 ≤ H_q(δ)`.
  have hH_nonneg : 0 ≤ qEntropy q δ := by
    rw [qEntropy_eq_qaryEntropy_div_log]
    have hδ1 : δ ≤ 1 := by
      have hq_inv : (0 : ℝ) ≤ 1 / (q : ℝ) := by positivity
      linarith
    exact div_nonneg
      (Real.qaryEntropy_nonneg hδ_pos.le hδ1)
      (Real.log_natCast_nonneg q)
  have hρ1 : ρ ≤ 1 := hρH.le.trans (by linarith)
  -- The source's dimension: `k = ⌈ρ·n⌉`, which sits in the band.
  set k : ℕ := ⌈ρ * (Fintype.card ι : ℝ)⌉₊ with hk_def
  have hband1 : ρ ≤ (k : ℝ) / (Fintype.card ι : ℝ) := by
    rw [le_div_iff₀ hn_posR]
    exact Nat.le_ceil _
  have hband2 : (k : ℝ) / (Fintype.card ι : ℝ) ≤ ρ + 1 / (Fintype.card ι : ℝ) := by
    rw [div_le_iff₀ hn_posR]
    have h1 : (k : ℝ) < ρ * (Fintype.card ι : ℝ) + 1 :=
      Nat.ceil_lt_add_one (by positivity)
    have h2 : (ρ + 1 / (Fintype.card ι : ℝ)) * (Fintype.card ι : ℝ)
        = ρ * (Fintype.card ι : ℝ) + 1 := by
      field_simp
    rw [h2]
    linarith
  have hkn : k ≤ Fintype.card ι := Nat.ceil_le.mpr (by nlinarith)
  -- The family `{C | finrank C = k}` is nonempty: a coordinate-kernel subspace works.
  obtain ⟨t, -, htcard⟩ := Finset.exists_subset_card_eq
    (show Fintype.card ι - k ≤ (Finset.univ : Finset ι).card by
      simp only [Finset.card_univ]; omega)
  have hwitness : ∃ C₀ : Submodule F (ι → F), Module.finrank F C₀ = k := by
    refine ⟨LinearMap.ker (LinearMap.funLeft F F (fun x : ↥t => (x : ι))), ?_⟩
    have hsurj : Function.Surjective (LinearMap.funLeft F F (fun x : ↥t => (x : ι))) :=
      LinearMap.funLeft_surjective_of_injective F F _ Subtype.val_injective
    have h1 := LinearMap.finrank_range_add_finrank_ker
      (LinearMap.funLeft F F (fun x : ↥t => (x : ι)))
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_pi,
      Module.finrank_pi, Fintype.card_coe, htcard] at h1
    omega
  -- Bad-event count is strictly below the family count, so a good code exists.
  set B : ℕ∞ :=
    ((Nat.floor (qEntropy q δ / (1 - qEntropy q δ - ρ) - ε') : ℕ) : ℕ∞) with hB_def
  set bad : Set (Submodule F (ι → F)) :=
    {C | Module.finrank F C = k ∧ Lambda ((C : Set (ι → F))) δ < B} with hbad_def
  set full : Set (Submodule F (ι → F)) := {C | Module.finrank F C = k} with hfull_def
  have hsub : bad ⊆ full := fun C hC => hC.1
  have hfull_pos : 0 < full.ncard := by
    obtain ⟨C₀, hC₀⟩ := hwitness
    exact (Set.ncard_pos (Set.toFinite full)).mpr ⟨C₀, hC₀⟩
  have hlt : (bad.ncard : ℝ) < (full.ncard : ℝ) := by
    have hkey := hbound hcard hn k hband1 hband2
    have hq1 : (1 : ℝ) < (q : ℝ) := by exact_mod_cast lt_of_lt_of_le one_lt_two hq_pp.two_le
    have hrpow : (q : ℝ) ^ (-(c * (Fintype.card ι : ℝ))) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg hq1 (by nlinarith)
    calc (bad.ncard : ℝ)
        ≤ (q : ℝ) ^ (-(c * (Fintype.card ι : ℝ))) * (full.ncard : ℝ) := hkey
      _ < 1 * (full.ncard : ℝ) :=
          mul_lt_mul_of_pos_right hrpow (by exact_mod_cast hfull_pos)
      _ = (full.ncard : ℝ) := one_mul _
  have hssub : bad ⊂ full := by
    refine ⟨hsub, fun habs => ?_⟩
    have : full.ncard ≤ bad.ncard := Set.ncard_le_ncard habs (Set.toFinite bad)
    have : (full.ncard : ℝ) ≤ (bad.ncard : ℝ) := by exact_mod_cast this
    linarith
  obtain ⟨C, hCfull, hCbad⟩ := Set.exists_of_ssubset hssub
  have hCk : Module.finrank F C = k := hCfull
  refine ⟨C, ?_, ?_, ?_⟩
  · rw [hCk]; exact hband1
  · rw [hCk]; exact hband2
  · have hgood : B ≤ Lambda ((C : Set (ι → F))) δ := by
      by_contra hle
      exact hCbad ⟨hCk, lt_of_not_ge hle⟩
    apply le_trans (b := B) _ hgood
    dsimp only [B, ε']
    exact_mod_cast Nat.floor_le_floor
      (sub_le_sub_left (min_le_left ε (1 / 2)) (qEntropy q δ / (1 - qEntropy q δ - ρ)))

end RandomLinear

end CodingTheory
