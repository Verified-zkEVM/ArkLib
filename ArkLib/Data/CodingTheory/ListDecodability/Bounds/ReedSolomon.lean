/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ListDecodability.Bounds.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Nat.Totient
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finiteness

/-!
# List-size bounds specific to Reed-Solomon codes

The three Reed-Solomon separations of `[ABF26]` §3 — superpolynomial lists over extension fields
`[BKR06]`, large lists over prime fields `[GHSZ02]`, and the high-rate obstruction `[JH01]` — and,
in the opposite direction, the one probabilistic upper bound: a Reed-Solomon code on a *uniformly
random* evaluation domain is list-decodable near capacity with high probability `[AGL24]`.

See `ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean` for the family overview, the
quantification conventions, and the references.
-/

-- All three are load-bearing, verified by removing them and rebuilding: the statements below carry
-- `[Fintype ι]` / `[DecidableEq F]` and section variables that their *proofs* do not use, which the
-- corresponding linters each report.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open ListDecodable

section ReedSolomonBounds

/-- **Reed-Solomon codes over extension fields have superpolynomial lists** ([ABF26] Theorem 3.12,
after [BKR06, Corollary 2.2]). Fix `0 < α < β < 1`. For infinitely many prime powers `q` there is a
Reed-Solomon code `C := RS[F_q, F_q, ⌊q^α⌋]` and a word `w : F_q → F_q` with

  `|Λ(C, 1 - q^{β-1}, w)| ≥ q^{(α - β²) · log₂ q}` .

**Log base.** The source's logs are base 2: its display continues
`q^{(α-β²)·log q} = 2^{(α-β²)·(log q)²}`, an identity precisely when `log = log₂`, since
`q^x = 2^{x·log₂ q}`. Hence `Real.logb 2 q`; a natural log here would weaken the exponent by a
factor `1/ln 2`.

**Two divergences from [BKR06], both introduced by [ABF26] and followed here** (the paper is the
designated ground truth, so the Lean tracks it rather than the original): [BKR06] defines
`RS[N, K]` by degree **≤ K** and its witnessing family has degree exactly `K = N^δ`, whereas
[ABF26]'s `RS[F, L, k]` is degree **< k** (its own footnote defines it so) and instantiates
`k = ⌊q^α⌋`. Under [ABF26]'s convention — which `ReedSolomon.code domain k` matches exactly — the
witnesses of the cited construction sit one degree above the code. And [BKR06, Corollary 2.2]
requires `α, β` **rational**; [ABF26] states it for real `α, β`. The statement here is faithful to
[ABF26], but the two divergences are of different weights.

The degree convention is **harmless**: [BKR06]'s family consists of monic subspace polynomials
`∏_{a ∈ L}(X − a)` of degree exactly `K`, so subtracting any fixed member gives `|P|` distinct
polynomials of degree `< K` — inside the degree-`< k` code — all agreeing with the shifted word
`w − P₀` on the same `≥ q^v` points. So the cited construction does transfer.

The rationality gap is **not** harmless and may make the real-`α, β` statement false. [BKR06]
Theorem 2.1 gives `|P| ≥ q^{(u+1)m − v²}` for *integers* `0 ≤ u ≤ v ≤ m`, which at exact
`u = αm, v = βm` beats the target `2^{m²(α−β²)}` by a slack of exactly `+m`; rounding to
`u = ⌊αm⌋, v = ⌈βm⌉` costs `−2βm − 1`, the same order, so the naive approximation *falls short
polynomially* rather than merely failing to be tight. It looks recoverable — "for infinitely many
`q`" lets one choose the subsequence of `m`, and by Weyl equidistribution there are infinitely many
`m` with `{αm}` and `{βm}` both near `0` — but that is a Diophantine argument the source does not
contain. Consider taking `α β : ℚ` instead. -/
theorem rs_lambda_superpoly_extension
    (α β : ℝ) (_hα_pos : 0 < α) (_hα_lt : α < β) (_hβ_lt : β < 1) :
    ∃ qs : ℕ → ℕ, StrictMono qs ∧ (∀ i, IsPrimePow (qs i)) ∧
      ∀ i : ℕ,
        ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
          {F : Type} [Field F] [Fintype F] [DecidableEq F],
          Fintype.card F = qs i → Fintype.card ι = qs i →
          ∃ (domain : ι ↪ F) (w : ι → F),
            let q : ℕ := qs i
            let k : ℕ := Nat.floor ((q : ℝ) ^ α)
            let δ : ℝ := 1 - (q : ℝ) ^ (β - 1)
            let C := ReedSolomon.code domain k
            ((closeCodewordsRel ((C : Set (ι → F))) w δ).ncard : ℝ) ≥
              (q : ℝ) ^ ((α - β ^ 2) * Real.logb 2 q) := by
  sorry -- external admit: [BKR06, Corollary 2.2].

/-- **Reed-Solomon codes over prime fields have large lists** ([ABF26] Theorem 3.13, after
[GHSZ02, Corollary 20]). Fix `0 < α, β < 1`. For all sufficiently large primes `p` there is a code
`C := RS[F_p, F_p, ⌊p^α⌋]` and a word `w : F_p → F_p` with

  `|Λ(C, 1 - ((1-β)/α) · p^{α-1}, w)| > Ω(p^{p^α · β/2})` .

**Source statement and variable map.** [GHSZ02, Corollary 20] is stated for their asymptotic
quantity `L_q^{poly}` in the variables `ε, γ > 0`; the map is `ε ↦ α`, `γ ↦ β`. Its proof is what
[ABF26] renders: "Use an MDS `[n,k]_q` code with `n = q` and `k = n^ε`, such as a Reed-Solomon
code … Letting `a = (1−γ)n^ε/ε` … the expected number of codewords in a ball of radius `n − a` is
`Ω(n^{(γ/2)·n^ε})`." So the per-`n`, single-code form [ABF26] prints — and which is formalized here
— lives in the source's *proof*, not in its statement, which bounds the asymptotic quantity instead.
The local copy of [GHSZ02] is a scanned two-column paper whose text layer drops relation symbols, so
Corollary 20's own display could not be transcribed verbatim; the proof text above could.

**`_hαβ_le_one` is a source hypothesis [ABF26] drops.** The averaging bound the proof rests on
([GHSZ02] Lemma 19: for an MDS `[n,k]_q` code and `a ≥ k`,
`(1/e)·C(n,a)·q^{k−a} ≤ E_x[|B(x, n−a) ∩ C|] ≤ C(n,a)·q^{k−a}`) requires `a ≥ k`, i.e.
`(1−β)/α ≥ 1`, i.e. `α + β ≤ 1`. It is carried here rather than dropped. (Dropping it looks
harmless — `α + β > 1` gives `a < k`, hence a *larger* ball and a longer list — but the cited
inequality is then outside its stated range, so the admit would no longer follow from the source.)

**Quantifier encoding.** `Ω(·)` is the explicit constant `c > 0` bound *outside* the `∀ p`, and "all
sufficiently large primes" is the explicit threshold `p₀`; `Nat.Prime p` is a conjunct of the
implication's premises, not an antecedent that a non-prime could satisfy vacuously. The list is the
*point* list at the exhibited `w`, as in the source, rather than `Lambda`. -/
theorem rs_lambda_large_prime
    (α β : ℝ) (_hα_pos : 0 < α) (_hα_lt : α < 1) (_hβ_pos : 0 < β) (_hβ_lt : β < 1)
    (_hαβ_le_one : α + β ≤ 1) :
    ∃ (c : ℝ) (_ : 0 < c) (p₀ : ℕ),
      ∀ p : ℕ, Nat.Prime p → p₀ ≤ p →
        ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
          {F : Type} [Field F] [Fintype F] [DecidableEq F],
          Fintype.card F = p → Fintype.card ι = p →
          ∃ (domain : ι ↪ F) (w : ι → F),
            let k : ℕ := Nat.floor ((p : ℝ) ^ α)
            let δ : ℝ := 1 - ((1 - β) / α) * (p : ℝ) ^ (α - 1)
            let C := ReedSolomon.code domain k
            ((closeCodewordsRel ((C : Set (ι → F))) w δ).ncard : ℝ) >
              c * (p : ℝ) ^ ((p : ℝ) ^ α * β / 2) := by
  sorry -- external admit: [GHSZ02, Corollary 20].

/-- **High-rate Reed-Solomon codes cannot be list-decoded past `1/(j+1)`** ([ABF26] Theorem 3.14,
after [JH01, Theorem 2]). Fix an integer `j ≥ 2`. For infinitely many prime powers `q` with
`q ≡ 1 (mod j+1)` there is a code `C := RS[F_q, L, k]` with `|L| = j + 1` and rate `≈ (j-1)/(j+1)`
together with a word `w : L → F_q` such that

  `|Λ(C, 1/(j+1), w)| > j` .

**Encoding of the source's parameters.** Its `|L| = j + 1` is the block length, encoded as
`Fintype.card ι = j + 1`. The dimension is pinned to `k := j` in ArkLib's `ReedSolomon.code domain
k` convention (polynomials of degree `< k`, so dimension `k`). The pin matters in *both*
directions:

* `k = j - 1` (dimension `j - 1`) is **unsatisfiable**: the minimum distance is `n - k + 1 = 3`
  while radius `1/(j+1)` permits a single error, so two list members would be within distance
  `2 < 3` and the list size is at most `1`, never `> j`;
* an unconstrained `∃ k` would let degenerate dimensions (e.g. `k = j + 1`, `C = F^L`) satisfy the
  conclusion trivially.

**The printed rate does not match, and this is a paper defect, not a convention difference.** With
block length `j + 1`, dimension `j` gives rate `j/(j+1)`, whereas [ABF26] prints
`ρ ≈ (j−1)/(j+1)`. No degree convention reconciles the two: degree-`≤ (j−1)` *is* dimension `j`, so
it also yields `j/(j+1)`, and the only dimension yielding `(j−1)/(j+1)` is `j − 1`, which the
argument above shows is unsatisfiable. At `j = 2` the discrepancy is `2/3` versus `1/3`, well
outside "≈". Note [JH01] itself is **not** in the local reference cache, so this could not be
checked against the original.

**The conclusion at this dimension is elementary, and the source's conjuncts are inert.** With
`k = j` the minimum distance is `2`, and radius `1/(j+1)` admits one error. For any `w ∉ C` the
`j + 1` drop-one-coordinate interpolants are codewords within distance `1` of `w`, and they are
pairwise distinct (two coinciding would agree with `w` everywhere, forcing `w ∈ C`), so the list has
`j + 1 > j` elements. This uses **neither** `IsPrimePow (qs i)` **nor** `qs i % (j + 1) = 1`: it
holds for every `q ≥ j + 2`, and `q ≡ 1 (mod j+1)` with `q ≥ 2` already forces `q ≥ j + 2`. So the
statement is elementary rather than external — it is proved in-tree below — and correspondingly it
does not capture whatever [JH01] Theorem 2 proves at rate `(j−1)/(j+1)`: the modular condition is
exactly the existence condition for `μ_{j+1} ⊆ F_q^×`, suggesting [JH01] pins `L = μ_{j+1}` and
concludes something sharper.

**The sequence comes from Euler, not Dirichlet.** `qs i = p^(φ(j+1)·(i+1))` for any prime
`p > j + 1` is strictly monotone, a prime power by construction, and `≡ 1 (mod j+1)` by
`Nat.ModEq.pow_totient`. This avoids needing primes in an arithmetic progression
(`Nat.exists_prime_gt_modEq_one`) for a statement that only asks for prime *powers*. The
interpolants are `Lagrange.interpolate (Finset.univ.erase a) domain w`, in `C` by
`Lagrange.degree_interpolate_lt`. -/
theorem rs_lambda_high_rate
    (j : ℕ) (_hj_ge : 2 ≤ j) :
    ∃ qs : ℕ → ℕ, StrictMono qs ∧
      (∀ i, IsPrimePow (qs i)) ∧ (∀ i, qs i % (j + 1) = 1) ∧
      ∀ i : ℕ,
        ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
          {F : Type} [Field F] [Fintype F] [DecidableEq F],
          Fintype.card F = qs i → Fintype.card ι = j + 1 →
          ∃ (domain : ι ↪ F) (w : ι → F),
            let C := ReedSolomon.code domain j
            (j : ℕ∞) < (closeCodewordsRel ((C : Set (ι → F))) w (1 / (j + 1 : ℝ))).ncard := by
  classical
  let m := j + 1
  obtain ⟨p, hp_ge, hp⟩ := Nat.exists_infinite_primes (m + 1)
  have hm_pos : 0 < m := by simp [m]
  have hm_one : 1 < m := by simp [m]; omega
  have hm_lt_p : m < p := by omega
  have hcop : Nat.Coprime p m := Nat.coprime_of_lt_prime (by omega) hm_lt_p hp
  have heuler : p ^ Nat.totient m ≡ 1 [MOD m] := Nat.ModEq.pow_totient hcop
  let qs : ℕ → ℕ := fun i => p ^ (Nat.totient m * (i + 1))
  have hqs_mono : StrictMono qs := by
    intro a b hab
    apply pow_right_strictMono₀ hp.one_lt
    have htot : 0 < Nat.totient m := Nat.totient_pos.mpr hm_pos
    exact (Nat.mul_lt_mul_left htot).mpr (Nat.add_lt_add_right hab 1)
  have hqs_pp : ∀ i, IsPrimePow (qs i) := by
    intro i
    apply hp.isPrimePow.pow
    have htot : 0 < Nat.totient m := Nat.totient_pos.mpr hm_pos
    positivity
  have hqs_mod : ∀ i, qs i % (j + 1) = 1 := by
    intro i
    have hcong : qs i ≡ 1 [MOD m] := by
      rw [show qs i = (p ^ Nat.totient m) ^ (i + 1) by simp [qs, pow_mul]]
      simpa using heuler.pow (i + 1)
    change qs i % m = 1
    exact Nat.mod_eq_of_modEq hcong hm_one
  refine ⟨qs, hqs_mono, hqs_pp, hqs_mod, ?_⟩
  intro i ι _ _ _ F _ _ _ hF hι
  have hexp_pos : 0 < Nat.totient m * (i + 1) := by
    have htot : 0 < Nat.totient m := Nat.totient_pos.mpr hm_pos
    positivity
  have hp_le_qs : p ≤ qs i := by
    change p ≤ p ^ (Nat.totient m * (i + 1))
    exact Nat.le_pow hexp_pos
  have hcard_le : Fintype.card ι ≤ Fintype.card F := by
    rw [hι, hF]
    change m ≤ qs i
    omega
  let domain : ι ↪ F := Classical.choice (Function.Embedding.nonempty_of_card_le hcard_le)
  let C : Submodule F (ι → F) := ReedSolomon.code domain j
  have hdimC : Module.finrank F C = j := by
    change LinearCode.dim (ReedSolomon.code domain j) = j
    exact ReedSolomon.dim_eq_deg_of_le (by omega)
  have hdimV : Module.finrank F (ι → F) = j + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, hι]
  obtain ⟨w, hw⟩ := Submodule.exists_of_finrank_lt C (by omega)
  have hwC : w ∉ C := by
    simpa only [one_smul] using hw (1 : F) one_ne_zero
  let poly : ι → Polynomial F := fun a =>
    Lagrange.interpolate (Finset.univ.erase a) domain w
  let c : ι → (ι → F) := fun a => ReedSolomon.evalOnPoints domain (poly a)
  have hdeg : ∀ a, (poly a).degree < (j : WithBot ℕ) := by
    intro a
    have hd := Lagrange.degree_interpolate_lt (s := Finset.univ.erase a)
      (v := domain) (r := w) domain.injective.injOn
    have hcard : (Finset.univ.erase a).card = j := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, hι]
      omega
    rw [hcard] at hd
    exact hd
  have hc : ∀ a, c a ∈ C := by
    intro a
    exact ReedSolomon.evalOnPoints_mem_code_of_degree_lt (hdeg a)
  have hagree : ∀ a x, x ≠ a → c a x = w x := by
    intro a x hxa
    change Polynomial.eval (domain x)
      (Lagrange.interpolate (Finset.univ.erase a) domain w) = w x
    exact Lagrange.eval_interpolate_at_node w domain.injective.injOn (by simp [hxa])
  have cinj : Function.Injective c := by
    intro a b hab
    by_contra hne
    have hcaw : c a = w := by
      funext x
      by_cases hxa : x = a
      · have hxb : x ≠ b := by
          intro hxb
          apply hne
          exact hxa.symm.trans hxb
        calc
          c a x = c b x := congrFun hab x
          _ = w x := hagree b x hxb
      · exact hagree a x hxa
    exfalso
    apply hwC
    rw [← hcaw]
    exact hc a
  refine ⟨domain, w, ?_⟩
  have hprod : (1 / (j + 1 : ℝ)) * (Fintype.card ι : ℝ) = 1 := by
    rw [hι]
    push_cast
    field_simp
  have hfloor : ⌊(1 / (j + 1 : ℝ)) * Fintype.card ι⌋₊ = 1 := by
    rw [hprod]
    norm_num
  have hclose : ∀ a, c a ∈
      _root_.ListDecodable.closeCodewordsRel ((C : Set (ι → F))) w
        (1 / (j + 1 : ℝ)) := by
    intro a
    rw [CodingTheory.closeCodewordsRel_eq_setOf C _ (by positivity) w]
    simp only [Set.mem_setOf_eq]
    refine ⟨hc a, ?_⟩
    rw [hfloor]
    unfold hammingDist
    calc
      (Finset.filter (fun x => c a x ≠ w x) Finset.univ).card ≤
          ({a} : Finset ι).card := by
        apply Finset.card_le_card
        intro x hx
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
        simp only [Finset.mem_singleton]
        by_contra hxa
        exact hx (hagree a x hxa)
      _ = 1 := Finset.card_singleton a
  let S : Set (ι → F) :=
    _root_.ListDecodable.closeCodewordsRel ((C : Set (ι → F))) w
      (1 / (j + 1 : ℝ))
  have hcount : (Set.univ : Set ι).ncard ≤ S.ncard := by
    apply Set.ncard_le_ncard_of_injOn c
    · intro a _
      exact hclose a
    · intro a _ b _ hab
      exact cinj hab
  have hcount' : Fintype.card ι ≤ S.ncard := by
    simpa only [Set.ncard_univ, Nat.card_eq_fintype_card] using hcount
  have hjlt : j < S.ncard := by omega
  change (j : ℕ∞) < (S.ncard : ℕ∞)
  exact_mod_cast hjlt

end ReedSolomonBounds

section RandomReedSolomon

open scoped ProbabilityTheory

/-- **Reed-Solomon codes on a random evaluation domain are list-decodable near capacity**
([ABF26] Theorem 3.6, after [AGL24, Theorem 1.1]).

The source statement, in its own variables: for `ℓ ≥ 2`, `η ∈ (0,1)`, `k, n ∈ ℕ` and a finite field
with `|F| ≥ n + k · 2^{10ℓ/η}`,

  `Pr[ |Λ(C, ℓ/(ℓ+1) · (1 − ρ − η))| ≤ ℓ ] ≥ 1 − 2^{−ℓn}` ,

where the evaluation domain `L` is drawn uniformly from the size-`n` subsets of `F`, the code is
`C := RS[F, L, k]`, and `ρ := k/n`.

**The random domain is the source's, not a reformulation.** The sample space is literally
`\binom{F}{n}` — the subtype of `Finset F` of cardinality `n`, sampled with `$ᵖ`, and the code is
indexed by that subset itself (`↥S → F`), so no ordering is chosen and no push-forward argument is
needed. An earlier assessment recorded this row as blocked on missing infrastructure for a uniform
distribution over size-`n` subsets; that gap is closed — `Finset F` is a `Fintype`, so the subtype
is one too, and `PMF.uniformOfFintype` applies directly.

`[Nonempty {S : Finset F // S.card = n}]` is what `$ᵖ` needs, and it is implied by the field-size
hypothesis (which forces `n ≤ |F|`, whence `Finset.exists_subset_card_eq` supplies a witness); it is
taken as an instance argument only because a statement cannot discharge an instance from one of its
own hypotheses.

The source's stated consequence — at `ℓ = 2(1−ρ−η)/η` and `|F| ≥ n + k·2^{20(1−ρ−η)/η²}` the code
has `|Λ(C, 1 − ρ − η)| ≤ 2(1−ρ−η)/η` with probability `1 − 2^{−2n(1−ρ−η)/η}` — is not stated
separately: its `ℓ` is real-valued, so it needs a rounding the source does not fix, exactly the
issue [ABF26] Theorem 3.4 raises in its `η`-form. Derive it at a call site with an explicit choice.

[BGM23] (exponential alphabet) and [GZ23] (polynomial-size alphabet) are the preceding results, and
[AGGLZ25] combines them; [ABF26] cites all three as context for this theorem, and none is
formalised. -/
theorem rs_random_domain_lambda_le
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (ℓ : ℕ) (_hℓ_ge : 2 ≤ ℓ) (η : ℝ) (_hη_pos : 0 < η) (_hη_lt : η < 1)
    (k n : ℕ) (_hn_pos : 0 < n)
    (_hF : (n : ℝ) + (k : ℝ) * 2 ^ ((10 * ℓ : ℝ) / η) ≤ Fintype.card F)
    [Nonempty {S : Finset F // S.card = n}] :
    ENNReal.ofReal (1 - 2 ^ (-(ℓ * n : ℝ))) ≤
      Pr_{ let S ← $ᵖ {S : Finset F // S.card = n} }[
        Lambda ((ReedSolomon.code
              (Function.Embedding.subtype (fun x : F => x ∈ (S : Finset F))) k :
            Set (↥(S : Finset F) → F)))
            ((ℓ : ℝ) / (ℓ + 1) * (1 - (k : ℝ) / n - η)) ≤ (ℓ : ℕ∞)] := by
  sorry -- external admit: [AGL24, Theorem 1.1].

end RandomReedSolomon

end CodingTheory
