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
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finiteness

/-!
# List-size bounds specific to Reed-Solomon codes

Two Reed-Solomon separations from [ABF26] §3 — superpolynomial lists over extension fields [BKR06]
and large lists over prime fields [GHSZ02] — plus an internal codimension-one interpolation lemma.
The distinct high-rate result attributed to [JH01] remains an explicit coverage gap. In the opposite
direction, the file also contains the one probabilistic upper bound: a Reed-Solomon code on a
*uniformly random* evaluation domain is list-decodable near capacity with high probability [AGL24].

See `ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean` for the family overview, the
quantification conventions, and the references.

## References

The keys cited here — [ABF26], [BKR06], [GHSZ02], [JH01], [AGL24], [BGM23], [GZ23], [AGGLZ25] — are
resolved in the reference list of `ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean`, which
every file in this directory shares.
-/

-- All three are load-bearing, verified by removing them and rebuilding: the statements below carry
-- `[Fintype ι]` / `[DecidableEq F]` and section variables that their *proofs* do not use, which the
-- corresponding linters each report.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open Code

section ReedSolomonBounds

/-- **Reed-Solomon codes over extension fields have superpolynomial lists** ([ABF26] Theorem 3.12,
after [BKR06, Corollary 2.2]). Fix `0 < α < β < 1`. For infinitely many prime powers `q` there is a
Reed-Solomon code `C := RS[F_q, F_q, ⌊q^α⌋]` and a word `w : F_q → F_q` with

  `|Λ(C, 1 - q^{β-1}, w)| ≥ q^{(α - β²) · log₂ q}` .

**Log base.** The source's logs are base 2: its display continues
`q^{(α-β²)·log q} = 2^{(α-β²)·(log q)²}`, an identity precisely when `log = log₂`, since
`q^x = 2^{x·log₂ q}`. Hence `Real.logb 2 q`; a natural log here would weaken the exponent by a
factor `1/ln 2`.

**Parameter domain.** [BKR06, Corollary 2.2] assumes rational `α, β`; its proof chooses an extension
degree on which `αm` and `βm` are integers. These binders therefore have type `ℚ` below, with
explicit coercions to `ℝ` only in the real-power and logarithmic expressions. [ABF26] Theorem 3.12
prints arbitrary real parameters, an extension not supplied by the cited source. On the source's
subsequence `q = 2^m`, integrality of `αm` also makes `q^α = 2^(αm)` a natural number, so
`⌊q^α⌋ = q^α` exactly; the rational restriction removes a potential dimension-rounding mismatch.

**Degree convention.** [BKR06] defines `RS[N, K]` by degree **≤ K** and its witnessing family has
degree exactly `K = N^δ`, whereas [ABF26]'s `RS[F, L, k]` is degree **< k** (as its footnote
defines it) and instantiates `k = ⌊q^α⌋`. Under that convention — which
`ReedSolomon.code domain k` matches exactly — the witnesses of the cited construction sit one
degree above the code.

The degree convention is **harmless**: [BKR06]'s family consists of monic subspace polynomials
`∏_{a ∈ L}(X − a)` of degree exactly `K`, so subtracting any fixed member gives `|P|` distinct
polynomials of degree `< K` — inside the degree-`< k` code — all agreeing with the shifted word
`w − P₀` on the same `≥ q^v` points. So the cited construction does transfer.

The rational restriction is separate from that degree translation: subtracting a fixed monic
witness justifies the latter, but says nothing about extending the source from rational to real
parameters. -/
theorem rs_lambda_superpoly_extension
    (α β : ℚ) (_hα_pos : 0 < α) (_hα_lt : α < β) (_hβ_lt : β < 1) :
    ∃ qs : ℕ → ℕ, StrictMono qs ∧ (∀ i, IsPrimePow (qs i)) ∧
      ∀ i : ℕ,
        ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
          {F : Type} [Field F] [Fintype F] [DecidableEq F],
          Fintype.card F = qs i → Fintype.card ι = qs i →
          ∃ (domain : ι ↪ F) (w : ι → F),
            let q : ℕ := qs i
            let k : ℕ := Nat.floor ((q : ℝ) ^ (α : ℝ))
            let δ : ℝ := 1 - (q : ℝ) ^ ((β : ℝ) - 1)
            let C := ReedSolomon.code domain k
            ((closeCodewordsRel ((C : Set (ι → F))) w δ).ncard : ℝ) ≥
              (q : ℝ) ^ (((α : ℝ) - (β : ℝ) ^ 2) * Real.logb 2 q) := by
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
  classical
  let A : ℝ := (1 - β) / α
  have hA : 0 < A := div_pos (sub_pos.mpr _hβ_lt) _hα_pos
  have hAeq : α * A = 1 - β := by
    dsimp [A]
    field_simp [_hα_pos.ne']
  let s : ℝ := β / (4 * (A + 1))
  have hs : 0 < s := div_pos _hβ_pos (mul_pos (by norm_num) (by linarith))
  have hsA : s * A ≤ β / 4 := by
    dsimp [s]
    have hden : 0 < 4 * (A + 1) := mul_pos (by norm_num) (by linarith)
    rw [div_mul_eq_mul_div, div_le_iff₀ hden]
    nlinarith
  have hxTop : Filter.Tendsto (fun p : ℕ => (p : ℝ) ^ α) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop _hα_pos).comp tendsto_natCast_atTop_atTop
  have hsTop : Filter.Tendsto (fun p : ℕ => (p : ℝ) ^ s) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop hs).comp tendsto_natCast_atTop_atTop
  have hhalfTop : Filter.Tendsto (fun p : ℕ => (p : ℝ) ^ (1 - α)) Filter.atTop Filter.atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr _hα_lt)).comp tendsto_natCast_atTop_atTop
  have hEA : ∀ᶠ p : ℕ in Filter.atTop, A ≤ (p : ℝ) ^ (1 - α) :=
    hhalfTop.eventually (Filter.eventually_ge_atTop A)
  have hE2 : ∀ᶠ p : ℕ in Filter.atTop, 2 ≤ p := Filter.eventually_ge_atTop 2
  have hEbound : ∀ᶠ p : ℕ in Filter.atTop, A * (p : ℝ) ^ α ≤ (p : ℝ) := by
    filter_upwards [hEA, hE2] with p hAp hp2
    have hpR : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hp2)
    calc
      A * (p : ℝ) ^ α ≤ (p : ℝ) ^ (1 - α) * (p : ℝ) ^ α :=
        mul_le_mul_of_nonneg_right hAp (Real.rpow_nonneg hpR.le _)
      _ = (p : ℝ) := by
        rw [← Real.rpow_add hpR]
        convert Real.rpow_one (p : ℝ) using 2
        ring
  have hparams : ∀ᶠ p : ℕ in Filter.atTop,
      let x : ℝ := (p : ℝ) ^ α
      let k : ℕ := Nat.floor x
      let a : ℕ := ⌈A * x⌉₊
      let δ : ℝ := 1 - A * (p : ℝ) ^ (α - 1)
      2 ≤ p ∧ k ≤ p ∧ a ≤ p ∧ 0 ≤ δ ∧ p - a ≤ ⌊δ * p⌋₊ := by
    filter_upwards [hEbound, hE2] with p hbound hp2
    dsimp only
    have hpR : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hp2)
    have hx0 : 0 ≤ (p : ℝ) ^ α := Real.rpow_nonneg hpR.le _
    have hxle : (p : ℝ) ^ α ≤ (p : ℝ) := by
      calc
        (p : ℝ) ^ α ≤ (p : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ p by omega)) _hα_lt.le
        _ = (p : ℝ) := Real.rpow_one _
    have hk : Nat.floor ((p : ℝ) ^ α) ≤ p := by
      exact_mod_cast (Nat.floor_le hx0).trans hxle
    have ha : ⌈A * (p : ℝ) ^ α⌉₊ ≤ p := Nat.ceil_le.mpr hbound
    have hpowid : (p : ℝ) ^ (α - 1) * (p : ℝ) = (p : ℝ) ^ α := by
      calc
        (p : ℝ) ^ (α - 1) * (p : ℝ) =
            (p : ℝ) ^ (α - 1) * (p : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
        _ = (p : ℝ) ^ ((α - 1) + 1) := (Real.rpow_add hpR (α - 1) 1).symm
        _ = (p : ℝ) ^ α := by congr 1; ring
    have hsmall : A * (p : ℝ) ^ (α - 1) ≤ 1 := by
      apply (mul_le_mul_iff_of_pos_right hpR).mp
      rw [mul_assoc, hpowid, one_mul]
      exact hbound
    have hδ : 0 ≤ 1 - A * (p : ℝ) ^ (α - 1) := sub_nonneg.mpr hsmall
    have hδmul : (1 - A * (p : ℝ) ^ (α - 1)) * (p : ℝ) =
        (p : ℝ) - A * (p : ℝ) ^ α := by
      rw [sub_mul, one_mul, mul_assoc, hpowid]
    have hradius : p - ⌈A * (p : ℝ) ^ α⌉₊ ≤
        ⌊(1 - A * (p : ℝ) ^ (α - 1)) * p⌋₊ := by
      apply Nat.le_floor
      rw [Nat.cast_sub ha, hδmul]
      have hceil := Nat.le_ceil (A * (p : ℝ) ^ α)
      linarith
    exact ⟨hp2, hk, ha, hδ, hradius⟩
  have hEx : ∀ᶠ p : ℕ in Filter.atTop,
      1 ≤ (p : ℝ) ^ α ∧ 4 * (α + s + 1) / β ≤ (p : ℝ) ^ α := by
    filter_upwards [hxTop.eventually (Filter.eventually_ge_atTop 1),
      hxTop.eventually (Filter.eventually_ge_atTop (4 * (α + s + 1) / β))] with p h1 h2
    exact ⟨h1, h2⟩
  have hEs : ∀ᶠ p : ℕ in Filter.atTop, 2 * (A + 1) ≤ (p : ℝ) ^ s :=
    hsTop.eventually (Filter.eventually_ge_atTop (2 * (A + 1)))
  have hEhalf : ∀ᶠ p : ℕ in Filter.atTop, 2 * (A + 1) ≤ (p : ℝ) ^ (1 - α) :=
    hhalfTop.eventually (Filter.eventually_ge_atTop (2 * (A + 1)))
  have hcore : ∀ᶠ p : ℕ in Filter.atTop,
      let x : ℝ := (p : ℝ) ^ α
      let k : ℕ := Nat.floor x
      let a : ℕ := ⌈A * x⌉₊
      a ≤ p / 2 ∧
      (α + s) * (a : ℝ) + β * x / 2 < (k : ℝ) ∧
      (2 * a : ℝ) ≤ (p : ℝ) ^ (α + s) := by
    filter_upwards [hEx, hEs, hEhalf, hE2] with p hx hps hphalf hp2
    dsimp only
    have hpR : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hp2)
    have hxpos : 0 < (p : ℝ) ^ α := Real.rpow_pos_of_pos hpR _
    have hceil : (⌈A * (p : ℝ) ^ α⌉₊ : ℝ) < A * (p : ℝ) ^ α + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg hA.le hxpos.le)
    have haAx : (⌈A * (p : ℝ) ^ α⌉₊ : ℝ) ≤ (A + 1) * (p : ℝ) ^ α := by
      nlinarith only [hceil, hx.1]
    have hpowprod : (p : ℝ) ^ s * (p : ℝ) ^ α = (p : ℝ) ^ (α + s) := by
      rw [mul_comm, ← Real.rpow_add hpR]
    have haPow : (2 * ⌈A * (p : ℝ) ^ α⌉₊ : ℝ) ≤ (p : ℝ) ^ (α + s) := by
      calc
        (2 * ⌈A * (p : ℝ) ^ α⌉₊ : ℝ) ≤ 2 * ((A + 1) * (p : ℝ) ^ α) := by
          exact mul_le_mul_of_nonneg_left haAx (by norm_num)
        _ = (2 * (A + 1)) * (p : ℝ) ^ α := by ring
        _ ≤ (p : ℝ) ^ s * (p : ℝ) ^ α :=
          mul_le_mul_of_nonneg_right hps hxpos.le
        _ = _ := hpowprod
    have hak : (α + s) * (⌈A * (p : ℝ) ^ α⌉₊ : ℝ) +
        β * (p : ℝ) ^ α / 2 < (Nat.floor ((p : ℝ) ^ α) : ℝ) := by
      have hk := Nat.lt_floor_add_one ((p : ℝ) ^ α)
      have hx2 := hx.2
      have hscale : α + s + 1 ≤ β * (p : ℝ) ^ α / 4 := by
        have hh := (div_le_iff₀ _hβ_pos).mp hx2
        linarith only [hh]
      have hmul := mul_lt_mul_of_pos_left hceil (add_pos _hα_pos hs)
      have hsAx := mul_le_mul_of_nonneg_right hsA hxpos.le
      have hAeqx := congrArg (fun z : ℝ => z * (p : ℝ) ^ α) hAeq
      nlinarith only [hk, hscale, hmul, hsAx, hAeqx]
    have hpowhalf : (p : ℝ) ^ α * (p : ℝ) ^ (1 - α) = (p : ℝ) := by
      rw [← Real.rpow_add hpR]
      convert Real.rpow_one (p : ℝ) using 2
      ring
    have hap2R : (2 * ⌈A * (p : ℝ) ^ α⌉₊ : ℝ) ≤ (p : ℝ) := by
      calc
        (2 * ⌈A * (p : ℝ) ^ α⌉₊ : ℝ) ≤ 2 * ((A + 1) * (p : ℝ) ^ α) := by
          exact mul_le_mul_of_nonneg_left haAx (by norm_num)
        _ = (2 * (A + 1)) * (p : ℝ) ^ α := by ring
        _ ≤ (p : ℝ) ^ (1 - α) * (p : ℝ) ^ α :=
          mul_le_mul_of_nonneg_right hphalf hxpos.le
        _ = (p : ℝ) := by rw [mul_comm, hpowhalf]
    have hap2 : 2 * ⌈A * (p : ℝ) ^ α⌉₊ ≤ p := by exact_mod_cast hap2R
    have hapHalf : ⌈A * (p : ℝ) ^ α⌉₊ ≤ p / 2 := by omega
    exact ⟨hapHalf, hak, haPow⟩
  have hshell (p a k : ℕ) (x : ℝ) (hp2 : 2 ≤ p) (ha0 : 0 < a)
      (haHalf : a ≤ p / 2)
      (hak : (α + s) * (a : ℝ) + β * x / 2 < (k : ℝ))
      (haPow : (2 * a : ℝ) ≤ (p : ℝ) ^ (α + s)) :
      (p : ℝ) ^ p * ((Real.exp (-2) / 2) * (p : ℝ) ^ (β * x / 2)) <
        (p : ℝ) ^ k * ((p.choose a : ℝ) * (((p - 1 : ℕ) : ℝ) ^ (p - a))) := by
    have hp1R : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
    have hpR : (0 : ℝ) < p := by linarith
    have hap : a ≤ p := by omega
    have hdenpos : 0 < (2 * a : ℝ) ^ a := by positivity
    have hden : (2 * a : ℝ) ^ a < (p : ℝ) ^ ((k : ℝ) - β * x / 2) := by
      calc
        (2 * a : ℝ) ^ a ≤ ((p : ℝ) ^ (α + s)) ^ a :=
          pow_le_pow_left₀ (by positivity) haPow a
        _ = (p : ℝ) ^ ((α + s) * (a : ℝ)) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        _ < (p : ℝ) ^ ((k : ℝ) - β * x / 2) := by
          apply Real.rpow_lt_rpow_of_exponent_lt hp1R
          linarith
    have hquot : (p : ℝ) ^ (β * x / 2) <
        (p : ℝ) ^ k / (2 * a : ℝ) ^ a := by
      rw [lt_div_iff₀ hdenpos]
      calc
        (p : ℝ) ^ (β * x / 2) * (2 * a : ℝ) ^ a <
            (p : ℝ) ^ (β * x / 2) * (p : ℝ) ^ ((k : ℝ) - β * x / 2) :=
          mul_lt_mul_of_pos_left hden (Real.rpow_pos_of_pos hpR _)
        _ = (p : ℝ) ^ k := by
          rw [← Real.rpow_add hpR, ← Real.rpow_natCast]
          congr 1
          ring
    have hchoose : (p : ℝ) ^ a / (2 * a : ℝ) ^ a ≤ (p.choose a : ℝ) := by
      have hbase : (p : ℝ) / 2 ≤ (p + 1 - a : ℕ) := by
        rw [Nat.cast_sub (by omega : a ≤ p + 1)]
        push_cast
        have ha2 : 2 * a ≤ p := by omega
        have ha2R : (2 : ℝ) * a ≤ p := by exact_mod_cast ha2
        linarith only [ha2R]
      have hnum : ((p : ℝ) / 2) ^ a ≤ ((p + 1 - a : ℕ) : ℝ) ^ a :=
        pow_le_pow_left₀ (by positivity) hbase a
      have hfac : ((a.factorial : ℕ) : ℝ) ≤ (a : ℝ) ^ a := by
        exact_mod_cast Nat.factorial_le_pow a
      have hraw : ((p : ℝ) / 2) ^ a / (a : ℝ) ^ a ≤ (p.choose a : ℝ) := by
        calc
          ((p : ℝ) / 2) ^ a / (a : ℝ) ^ a ≤
              (((p + 1 - a : ℕ) : ℝ) ^ a) / (a.factorial : ℝ) := by
            exact div_le_div₀ (by positivity) hnum (by exact_mod_cast Nat.factorial_pos a) hfac
          _ ≤ (p.choose a : ℝ) := Nat.pow_le_choose a p
      have hid : ((p : ℝ) / 2) ^ a / (a : ℝ) ^ a =
          (p : ℝ) ^ a / (2 * a : ℝ) ^ a := by
        rw [div_pow, mul_pow]
        field_simp
      rw [← hid]
      exact hraw
    have hfactor : Real.exp (-2) * (p : ℝ) ^ (p - a) ≤
        ((p - 1 : ℕ) : ℝ) ^ (p - a) := by
      have hp2R : (2 : ℝ) ≤ p := by exact_mod_cast hp2
      have hp1subR : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have hrpos : 0 < 1 - 1 / (p : ℝ) := by
        rw [sub_pos, div_lt_one hpR]
        linarith
      have hrle : 1 - 1 / (p : ℝ) ≤ 1 := by
        have : 0 ≤ 1 / (p : ℝ) := by positivity
        linarith
      have hlog0 := Real.one_sub_inv_le_log_of_pos hrpos
      have hcalc : -2 ≤ (p : ℝ) * (1 - (1 - 1 / (p : ℝ))⁻¹) := by
        field_simp
        nlinarith only [hp2R]
      have hlog : -2 ≤ (p : ℝ) * Real.log (1 - 1 / (p : ℝ)) :=
        hcalc.trans (mul_le_mul_of_nonneg_left hlog0 hpR.le)
      have hratio : Real.exp (-2) ≤ (1 - 1 / (p : ℝ)) ^ p := by
        calc
          Real.exp (-2) ≤ Real.exp ((p : ℝ) * Real.log (1 - 1 / (p : ℝ))) :=
            Real.exp_le_exp.mpr hlog
          _ = Real.exp (Real.log ((1 - 1 / (p : ℝ)) ^ p)) := by rw [Real.log_pow]
          _ = (1 - 1 / (p : ℝ)) ^ p := Real.exp_log (pow_pos hrpos p)
      have hratio' : Real.exp (-2) ≤ (1 - 1 / (p : ℝ)) ^ (p - a) :=
        hratio.trans (pow_le_pow_of_le_one hrpos.le hrle (Nat.sub_le p a))
      calc
        Real.exp (-2) * (p : ℝ) ^ (p - a) ≤
            (1 - 1 / (p : ℝ)) ^ (p - a) * (p : ℝ) ^ (p - a) :=
          mul_le_mul_of_nonneg_right hratio' (by positivity)
        _ = ((1 - 1 / (p : ℝ)) * (p : ℝ)) ^ (p - a) := by rw [mul_pow]
        _ = (((p - 1 : ℕ) : ℝ)) ^ (p - a) := by
          congr 1
          rw [Nat.cast_sub (by omega : 1 ≤ p)]
          push_cast
          field_simp
    have hprod : Real.exp (-2) * ((p : ℝ) ^ p / (2 * a : ℝ) ^ a) ≤
        (p.choose a : ℝ) * (((p - 1 : ℕ) : ℝ) ^ (p - a)) := by
      have hm := mul_le_mul hchoose hfactor (by positivity) (by positivity)
      calc
        Real.exp (-2) * ((p : ℝ) ^ p / (2 * a : ℝ) ^ a) =
            ((p : ℝ) ^ a / (2 * a : ℝ) ^ a) *
              (Real.exp (-2) * (p : ℝ) ^ (p - a)) := by
          field_simp
          rw [← pow_add]
          congr 2
          omega
        _ ≤ _ := hm
    calc
      (p : ℝ) ^ p * ((Real.exp (-2) / 2) * (p : ℝ) ^ (β * x / 2)) <
          (p : ℝ) ^ p * (Real.exp (-2) *
            ((p : ℝ) ^ k / (2 * a : ℝ) ^ a)) := by
        apply mul_lt_mul_of_pos_left _ (by positivity)
        have he : 0 < Real.exp (-2) := Real.exp_pos _
        calc
          Real.exp (-2) / 2 * (p : ℝ) ^ (β * x / 2) <
              Real.exp (-2) * (p : ℝ) ^ (β * x / 2) := by
            apply mul_lt_mul_of_pos_right _ (Real.rpow_pos_of_pos hpR _)
            linarith
          _ < Real.exp (-2) * ((p : ℝ) ^ k / (2 * a : ℝ) ^ a) :=
            mul_lt_mul_of_pos_left hquot he
      _ = (p : ℝ) ^ k *
          (Real.exp (-2) * ((p : ℝ) ^ p / (2 * a : ℝ) ^ a)) := by ring
      _ ≤ (p : ℝ) ^ k *
          ((p.choose a : ℝ) * (((p - 1 : ℕ) : ℝ) ^ (p - a))) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
  rcases (Filter.eventually_atTop.1 hparams) with ⟨p₁, hp₁⟩
  rcases (Filter.eventually_atTop.1 hcore) with ⟨p₂, hp₂⟩
  refine ⟨Real.exp (-2) / 2, div_pos (Real.exp_pos _) (by norm_num), max p₁ p₂, ?_⟩
  intro p _hpprime hp ι _ _ _ F _ _ _ hFp hιp
  let x : ℝ := (p : ℝ) ^ α
  let k : ℕ := Nat.floor x
  let a : ℕ := ⌈A * x⌉₊
  let δ : ℝ := 1 - A * (p : ℝ) ^ (α - 1)
  obtain ⟨hp2, hkp, hap, hδ, hradius⟩ := hp₁ p (le_trans (le_max_left _ _) hp)
  obtain ⟨haHalf, hak, haPow⟩ := hp₂ p (le_trans (le_max_right _ _) hp)
  have hpR : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hp2)
  have hxpos : 0 < x := Real.rpow_pos_of_pos hpR _
  have ha0 : 0 < a := by
    have hax : 0 < A * x := mul_pos hA hxpos
    have hceil := Nat.le_ceil (A * x)
    exact_mod_cast (lt_of_lt_of_le hax hceil)
  have hbig := hshell p a k x hp2 ha0 haHalf hak haPow
  have hp1 : 1 ≤ p := by omega
  let domain : ι ↪ F := (Fintype.equivOfCardEq (hιp.trans hFp.symm)).toEmbedding
  let C := ReedSolomon.code domain k
  have hdim : Module.finrank F C = k := by
    apply ReedSolomon.dim_eq_deg_of_le
    simpa only [hιp] using hkp
  have hcardC : (C : Set (ι → F)).ncard = p ^ k := by
    rw [submodule_ncard_eq_pow_finrank, hFp, hdim]
  have hvolterm : p.choose a * (p - 1) ^ (p - a) ≤ hammingBallVolume p δ p := by
    unfold hammingBallVolume
    rw [← Nat.choose_symm hap]
    exact Finset.single_le_sum_of_canonicallyOrdered
      (f := fun i => p.choose i * (p - 1) ^ i)
      (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hradius))
  let cnt : (ι → F) → ℕ := fun w => (closeCodewordsRel ((C : Set (ι → F))) w δ).ncard
  have hsum : ∑ w : ι → F, cnt w = p ^ k * hammingBallVolume p δ p := by
    dsimp [cnt]
    rw [sum_ncard_closeCodewordsRel_eq C δ hδ, hcardC, hFp, hιp]
  have hcardwords : Fintype.card (ι → F) = p ^ p := by
    rw [Fintype.card_fun, hFp, hιp]
  have hw : ∃ w : ι → F,
      (Real.exp (-2) / 2) * (p : ℝ) ^ (x * β / 2) < (cnt w : ℝ) := by
    by_contra hn
    push Not at hn
    have hsumle : (∑ w : ι → F, (cnt w : ℝ)) ≤
        ∑ _w : ι → F, ((Real.exp (-2) / 2) * (p : ℝ) ^ (x * β / 2)) := by
      exact Finset.sum_le_sum fun w _ => hn w
    have hsumcast : (∑ w : ι → F, (cnt w : ℝ)) =
        (p : ℝ) ^ k * (hammingBallVolume p δ p : ℝ) := by
      exact_mod_cast hsum
    rw [hsumcast, Finset.sum_const, Finset.card_univ, hcardwords, nsmul_eq_mul] at hsumle
    push_cast at hsumle
    have htermcast : ((p.choose a * (p - 1) ^ (p - a) : ℕ) : ℝ) ≤
        (hammingBallVolume p δ p : ℝ) := by exact_mod_cast hvolterm
    have hpnonneg : (0 : ℝ) ≤ p ^ k := by positivity
    have hlow := mul_le_mul_of_nonneg_left htermcast hpnonneg
    push_cast at hlow
    have hbig' : (p : ℝ) ^ p *
          ((Real.exp (-2) / 2) * (p : ℝ) ^ (x * β / 2)) <
        (p : ℝ) ^ k * ((p.choose a : ℝ) * ((p - 1 : ℕ) : ℝ) ^ (p - a)) := by
      simpa only [mul_comm x β] using hbig
    exact (not_lt_of_ge (hlow.trans hsumle)) hbig'
  obtain ⟨w, hw⟩ := hw
  refine ⟨domain, w, ?_⟩
  dsimp only
  change ((closeCodewordsRel ((C : Set (ι → F))) w δ).ncard : ℝ) >
    (Real.exp (-2) / 2) * (p : ℝ) ^ ((p : ℝ) ^ α * β / 2)
  simpa only [cnt, x] using hw

/-- **A codimension-one Reed-Solomon code has `j + 1` nearby interpolants.** Let the block length be
`j + 1` and the message dimension be `j`. Over any field large enough to contain an evaluation
domain of that length, there is a received word whose radius-`1/(j+1)` list has more than `j`
codewords.

This is an internal elementary lemma, not a formalization of [JH01, Theorem 2]. Choose `w` outside
the codimension-one code. For each coordinate `a`, interpolate `w` on all coordinates except `a`.
The resulting `j + 1` degree-`< j` codewords are within Hamming distance one of `w` and are pairwise
distinct: if the interpolants omitting `a` and `b` coincided, they would agree with `w` everywhere,
contrary to `w ∉ C`.

An earlier version wrapped this lemma in prime-power and congruence quantifiers and named it
`rs_lambda_high_rate`, following [ABF26] Theorem 3.14. Those hypotheses were unused, and the code's
actual rate `j/(j+1)` did not match ABF26's printed `≈(j−1)/(j+1)`. The exact JH01 article is closed
access and was not available for primary-source verification, so JH01 coverage remains explicitly
open rather than being attributed to this different result. -/
theorem rs_codimension_one_list_size
    (j : ℕ)
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hcard_le : Fintype.card ι ≤ Fintype.card F)
    (hι : Fintype.card ι = j + 1) :
    ∃ (domain : ι ↪ F) (w : ι → F),
      let C := ReedSolomon.code domain j
      (j : ℕ∞) < (closeCodewordsRel ((C : Set (ι → F))) w (1 / (j + 1 : ℝ))).ncard := by
  classical
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
      Code.closeCodewordsRel ((C : Set (ι → F))) w
        (1 / (j + 1 : ℝ)) := by
    intro a
    rw [CodingTheory.closeCodewordsRel_eq_setOf C _ (by positivity) w]
    simp only [Set.mem_ofPred_eq]
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
    Code.closeCodewordsRel ((C : Set (ι → F))) w
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
