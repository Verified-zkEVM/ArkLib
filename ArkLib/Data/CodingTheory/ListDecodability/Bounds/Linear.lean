/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ListDecodability.Bounds.Basic
import ArkLib.Data.CodingTheory.Basic.Entropy
import ArkLib.Data.Probability.Notation
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.FieldTheory.Finiteness

/-!
# Bounds that hold for every linear code

The family's alphabet-generic half: the volume/averaging lower bound [Eli57] and its entropy form,
the arithmetic rate–radius cardinality bound, the generalized Singleton bound of [ST20], and the
random-linear-code lower bound of [GLMRSW22]. Nothing here is specific to a code family.

The large-alphabet barrier that attaining the generalized Singleton bound forces ([AGL23], [BDG24])
is in `Bounds/LargeAlphabet.lean`, over its own directory of machinery.

See `ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean` for the family overview, the
quantification conventions, and the references.

## References

The keys cited here — [ABF26], [Eli57], [MS77], [ST20], [AGL23], [BDG24], [GLMRSW22], [DG25dist] —
are resolved in the reference list of `ArkLib/Data/CodingTheory/ListDecodability/Bounds.lean`, which
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

section LowerBounds_General

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The volume lower bound on list size** ([ABF26] Lemma 3.7, after [Eli57]), at the source's
generality: for any code `C ⊆ A^n` over a finite alphabet `A` with `|C| = q^k`,

  `|Λ(C, δ)| ≥ Vol_q(δ, n) / q^(n-k)`

where `q = |A|` and `n = |ι|`.

Proved by the source's averaging argument: the mean over uniformly random centres `f` of the
point-list size `|Λ(C, δ, f)|` is `|C| · Vol / q^n = Vol / q^{n-k}`
(`sum_ncard_closeCodewordsRel_eq_of_set`), so some centre attains at least the mean, and `Lambda`
is the supremum over centres. No entropy estimate is involved — for that see
`lambda_ge_entropy_volume`.

The codeword count enters only as the hypothesis `hcard`, so linear, module-alphabet and
interleaved codes can all instantiate this with their own cardinality argument;
`linear_lambda_ge_elias_volume` is the field-linear case. `[Nonempty A]` is needed for the
positivity of `q` that the averaging step rests on. -/
theorem lambda_ge_elias_volume {A : Type} [Fintype A] [Nonempty A] [DecidableEq A]
    (C : Set (ι → A)) (k : ℕ) (hcard : C.ncard = Fintype.card A ^ k)
    (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1) :
    ENNReal.ofReal
        ((hammingBallVolume (Fintype.card A) δ (Fintype.card ι) : ℝ)
          / (Fintype.card A : ℝ) ^ ((Fintype.card ι : ℝ) - k))
      ≤ (Lambda C δ : ENNReal) := by
  classical
  set q : ℕ := Fintype.card A with hq
  set n : ℕ := Fintype.card ι with hn
  set Vol : ℕ := hammingBallVolume q δ n with hVol
  have hq_pos : 0 < q := Fintype.card_pos
  have hq_pos_real : (0 : ℝ) < q := by exact_mod_cast hq_pos
  have hδ_nonneg : 0 ≤ δ := le_of_lt _hδ_pos
  set cnt : (ι → A) → ℕ := fun f => (closeCodewordsRel C f δ).ncard with hcnt
  -- Total count over all centres `= |C| · Vol = q^k · Vol`.
  have hsum : ∑ f : ι → A, cnt f = q ^ k * Vol := by
    rw [hcnt]
    rw [sum_ncard_closeCodewordsRel_eq_of_set C δ hδ_nonneg, hcard]
  -- Number of centres is `q ^ n`.
  have hcard_univ : (Finset.univ : Finset (ι → A)).card = q ^ n := by
    rw [Finset.card_univ, hq, hn, Fintype.card_fun]
  -- Real arithmetic identity `q^n · (Vol / q^(n-k)) = q^k · Vol`.
  have h_arith : (q : ℝ) ^ n * ((Vol : ℝ) / (q : ℝ) ^ ((n : ℝ) - k)) = (q : ℝ) ^ k * Vol := by
    rw [Real.rpow_sub hq_pos_real, Real.rpow_natCast, Real.rpow_natCast]
    field_simp
  -- A centre `f₀` whose point list realises at least the mean.
  have hmean_le : ∃ f₀ : ι → A,
      ((Vol : ℝ) / (q : ℝ) ^ ((n : ℝ) - k)) ≤ (cnt f₀ : ℝ) := by
    by_contra hcon
    push Not at hcon
    have hsum_real : (∑ f : ι → A, (cnt f : ℝ)) = (q : ℝ) ^ k * Vol := by
      have : ((∑ f : ι → A, cnt f : ℕ) : ℝ) = ((q ^ k * Vol : ℕ) : ℝ) := by exact_mod_cast hsum
      push_cast at this ⊢
      convert this using 2
    have hlt : (∑ f : ι → A, (cnt f : ℝ))
        < ∑ _f : ι → A, ((Vol : ℝ) / (q : ℝ) ^ ((n : ℝ) - k)) := by
      apply Finset.sum_lt_sum_of_nonempty
      · exact Finset.univ_nonempty
      · intro f _; exact hcon f
    rw [Finset.sum_const, hcard_univ, hsum_real] at hlt
    have : (q : ℝ) ^ k * Vol < (q : ℝ) ^ k * Vol := by
      calc (q : ℝ) ^ k * Vol < (q ^ n : ℕ) • ((Vol : ℝ) / (q : ℝ) ^ ((n : ℝ) - k)) := hlt
        _ = (q : ℝ) ^ n * ((Vol : ℝ) / (q : ℝ) ^ ((n : ℝ) - k)) := by
              rw [nsmul_eq_mul]; push_cast; ring
        _ = (q : ℝ) ^ k * Vol := h_arith
    exact lt_irrefl _ this
  obtain ⟨f₀, hf₀⟩ := hmean_le
  -- Conclude: `Lambda ≥ |Λ(C, δ, f₀)| ≥ ofReal(mean)`.
  have hfin : (closeCodewordsRel C f₀ δ).Finite := Set.toFinite _
  have hLam : ((cnt f₀ : ℕ∞) : ENNReal) ≤ (Lambda C δ : ENNReal) := by
    apply ENat.toENNReal_mono
    calc ((cnt f₀ : ℕ) : ℕ∞)
        = (closeCodewordsRel C f₀ δ).encard := hfin.cast_ncard_eq
      _ ≤ Lambda C δ := encard_closeCodewordsRel_le_Lambda C δ f₀
  calc ENNReal.ofReal ((Vol : ℝ) / (q : ℝ) ^ ((n : ℝ) - k))
      ≤ ENNReal.ofReal (cnt f₀ : ℝ) := ENNReal.ofReal_le_ofReal hf₀
    _ = ((cnt f₀ : ℕ∞) : ENNReal) := by rw [ENNReal.ofReal_natCast, ENat.toENNReal_coe]
    _ ≤ (Lambda C δ : ENNReal) := hLam

/-- **The volume lower bound on list size** for a field-linear code ([ABF26] Lemma 3.7):

  `|Λ(C, δ)| ≥ Vol_q(δ, n) / q^(n-k)`

where `q = |F|`, `n = |ι|`, and `k = dim C`, so `|C| = q^k`.

This is the field-linear specialization of `lambda_ge_elias_volume`, which states the source's
arbitrary-alphabet form; linearity enters only through `submodule_ncard_eq_pow_finrank`, supplying
the codeword count `|C| = q^k` that the generic core takes as a hypothesis. -/
theorem linear_lambda_ge_elias_volume
    (C : Submodule F (ι → F)) (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1) :
    ENNReal.ofReal
        ((hammingBallVolume (Fintype.card F) δ (Fintype.card ι) : ℝ)
          / (Fintype.card F : ℝ) ^
              ((Fintype.card ι : ℝ) - Module.finrank F C))
      ≤ (Lambda ((C : Set (ι → F))) δ : ENNReal) :=
  lambda_ge_elias_volume (C : Set (ι → F)) (Module.finrank F C)
    (submodule_ncard_eq_pow_finrank C) δ _hδ_pos _hδ_lt

/-- `stirlingSeq 1 ^ 2 = 2 · stirlingSeq 2`, the base case of the two-term comparison
`stirlingSeq_mul_le_two_mul_add`. -/
theorem stirlingSeq_one_sq :
    Stirling.stirlingSeq 1 * Stirling.stirlingSeq 1 =
      2 * Stirling.stirlingSeq 2 := by
  unfold Stirling.stirlingSeq
  norm_num [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  field_simp [Real.exp_ne_zero]
  ring_nf
  rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2),
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- Positivity of Stirling's sequence at a positive index, in `0 < n` form. -/
theorem stirlingSeq_pos_of_pos (n : ℕ) (hn : 0 < n) :
    0 < Stirling.stirlingSeq n := by
  unfold Stirling.stirlingSeq
  positivity

set_option maxHeartbeats 1000000 in
-- `field_simp`/`ring_nf` on the four-factorial identity below exceeds the default budget.
/-- **The central binomial mass, exactly, in terms of Stirling's sequence.** For `d, m > 0`,

`C(d+m, d) · (d/(d+m))^d · (m/(d+m))^m
  = stirlingSeq (d+m) / (stirlingSeq d · stirlingSeq m) · √(2(d+m)) / (√(2d) · √(2m))`.

The left side is the probability that a binomial on `d + m` trials takes its mean value. -/
theorem binomial_mean_mass_eq_stirlingSeq
    (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    (((d + m).choose d : ℕ) : ℝ) *
        ((d : ℝ) / ((d + m : ℕ) : ℝ)) ^ d *
        ((m : ℝ) / ((d + m : ℕ) : ℝ)) ^ m =
      Stirling.stirlingSeq (d + m) /
          (Stirling.stirlingSeq d * Stirling.stirlingSeq m) *
        (Real.sqrt (2 * ((d + m : ℕ) : ℝ)) /
          (Real.sqrt (2 * (d : ℝ)) * Real.sqrt (2 * (m : ℝ)))) := by
  rw [show (((d + m).choose d : ℕ) : ℝ) = (Nat.factorial (d + m) : ℝ) /
        ((Nat.factorial d : ℝ) * (Nat.factorial m : ℝ)) from by
      simpa only [Nat.add_sub_cancel_left] using
        (Nat.cast_choose (K := ℝ) (show d ≤ d + m by omega))]
  unfold Stirling.stirlingSeq
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdmR : (0 : ℝ) < d + m := by positivity
  have hsd : Real.sqrt (2 * (d : ℝ)) ≠ 0 := by positivity
  have hsm : Real.sqrt (2 * (m : ℝ)) ≠ 0 := by positivity
  have hsdm : Real.sqrt (2 * ((d + m : ℕ) : ℝ)) ≠ 0 := by positivity
  have hfd : (Nat.factorial d : ℝ) ≠ 0 := by positivity
  have hfm : (Nat.factorial m : ℝ) ≠ 0 := by positivity
  have hfdm : (Nat.factorial (d + m) : ℝ) ≠ 0 := by positivity
  rw [pow_add, div_pow, div_pow, div_pow]
  field_simp [hdR.ne', hmR.ne', hdmR.ne', hsd, hsm, hsdm,
    hfd, hfm, hfdm, Real.exp_ne_zero]
  have hcancel :
      Real.exp 1 ^ d * (Real.exp 1)⁻¹ ^ d = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ (Real.exp_ne_zero 1), one_pow]
  linear_combination
    (-((d : ℝ) ^ d * (m : ℝ) ^ m * ((d + m : ℕ) : ℝ) ^ m *
      (Real.exp 1)⁻¹ ^ m)) * hcancel

/-- With `δ ∈ (0,1)` and `δ · n` an integer `d`, that integer is a genuine interior radius:
`0 < d < n` and `⌊δ · n⌋ = d`. -/
theorem entropy_radius_integer_bounds (n d : ℕ) (δ : ℝ) (hn : 0 < n)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1) (hd : (d : ℝ) = δ * n) :
    0 < d ∧ d < n ∧ ⌊δ * n⌋₊ = d := by
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  have hd_real_pos : (0 : ℝ) < d := by rw [hd]; positivity
  have hd_pos : 0 < d := by exact_mod_cast hd_real_pos
  have hd_real_lt : (d : ℝ) < n := by rw [hd]; nlinarith
  have hd_lt : d < n := by exact_mod_cast hd_real_lt
  refine ⟨hd_pos, hd_lt, ?_⟩
  rw [← hd, Nat.floor_natCast]

/-- `½ · √(2(d+m)) / (√(2d) · √(2m)) = 1 / √(8dm/(d+m))`. At `d = δn` and `m = n − δn` the right
side is `1 / √(8nδ(1−δ))`. -/
theorem entropy_sqrt_factor_identity
    (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    (1 : ℝ) / 2 *
        (Real.sqrt (2 * ((d + m : ℕ) : ℝ)) /
          (Real.sqrt (2 * (d : ℝ)) * Real.sqrt (2 * (m : ℝ)))) =
      1 / Real.sqrt
        (8 * (d : ℝ) * (m : ℝ) / ((d + m : ℕ) : ℝ)) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hdmR : (0 : ℝ) < d + m := by positivity
  have hsd : 0 < Real.sqrt (2 * (d : ℝ)) := by positivity
  have hsm : 0 < Real.sqrt (2 * (m : ℝ)) := by positivity
  have hsdm : 0 < Real.sqrt (2 * ((d + m : ℕ) : ℝ)) := by positivity
  have hx : 0 < 8 * (d : ℝ) * (m : ℝ) / ((d + m : ℕ) : ℝ) := by
    positivity
  have hsx : 0 < Real.sqrt
      (8 * (d : ℝ) * (m : ℝ) / ((d + m : ℕ) : ℝ)) := by
    positivity
  have hleft : 0 ≤ (1 : ℝ) / 2 *
      (Real.sqrt (2 * ((d + m : ℕ) : ℝ)) /
        (Real.sqrt (2 * (d : ℝ)) * Real.sqrt (2 * (m : ℝ)))) := by
    positivity
  have hright : 0 ≤ 1 / Real.sqrt
      (8 * (d : ℝ) * (m : ℝ) / ((d + m : ℕ) : ℝ)) := by
    positivity
  have hleft_sq :
      ((1 : ℝ) / 2 *
        (Real.sqrt (2 * ((d + m : ℕ) : ℝ)) /
          (Real.sqrt (2 * (d : ℝ)) * Real.sqrt (2 * (m : ℝ))))) ^ 2 =
        ((d + m : ℕ) : ℝ) / (8 * (d : ℝ) * (m : ℝ)) := by
    field_simp [hsd.ne', hsm.ne']
    rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * d),
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * m),
      Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * ((d + m : ℕ) : ℝ))]
    ring
  have hright_sq :
      (1 / Real.sqrt
        (8 * (d : ℝ) * (m : ℝ) / ((d + m : ℕ) : ℝ))) ^ 2 =
        ((d + m : ℕ) : ℝ) / (8 * (d : ℝ) * (m : ℝ)) := by
    field_simp [hsx.ne', hdR.ne', hmR.ne', hdmR.ne']
    rw [Real.sq_sqrt hx.le]
    field_simp [hdmR.ne']
  nlinarith

/-- The successive-log *difference* `log (stirlingSeq (m+1)) − log (stirlingSeq (m+2))` is antitone:
the decrements of `log ∘ stirlingSeq` shrink. Distinct from
`Stirling.log_stirlingSeq'_antitone`, which is antitonicity of the sequence itself. -/
theorem log_stirlingSeq_diff_antitone :
    Antitone (fun m : ℕ =>
      Real.log (Stirling.stirlingSeq (m + 1)) -
        Real.log (Stirling.stirlingSeq (m + 2))) := by
  intro a b hab
  apply hasSum_le (fun k => ?_)
    (Stirling.log_stirlingSeq_sdiff_hasSum b)
    (Stirling.log_stirlingSeq_sdiff_hasSum a)
  have habR : (a : ℝ) ≤ b := by exact_mod_cast hab
  gcongr

/-- The ratio `stirlingSeq (n+1) / stirlingSeq n` is monotone in `n`. -/
theorem stirlingSeq_succ_ratio_mono
    (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    Stirling.stirlingSeq (a + 1) / Stirling.stirlingSeq a ≤
      Stirling.stirlingSeq (b + 1) / Stirling.stirlingSeq b := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hab' : a - 1 ≤ b - 1 := Nat.sub_le_sub_right hab 1
  have hdiff := log_stirlingSeq_diff_antitone hab'
  dsimp only at hdiff
  have ha1 : a - 1 + 1 = a := by omega
  have ha2 : a - 1 + 2 = a + 1 := by omega
  have hb1 : b - 1 + 1 = b := by omega
  have hb2 : b - 1 + 2 = b + 1 := by omega
  rw [ha1, ha2, hb1, hb2] at hdiff
  have hleft : 0 < Stirling.stirlingSeq (a + 1) / Stirling.stirlingSeq a :=
    div_pos (stirlingSeq_pos_of_pos (a + 1) (by omega))
      (stirlingSeq_pos_of_pos a ha)
  have hright : 0 < Stirling.stirlingSeq (b + 1) / Stirling.stirlingSeq b :=
    div_pos (stirlingSeq_pos_of_pos (b + 1) (by omega))
      (stirlingSeq_pos_of_pos b hb)
  apply (Real.log_le_log_iff hleft hright).mp
  rw [Real.log_div (stirlingSeq_pos_of_pos (a + 1) (by omega)).ne'
      (stirlingSeq_pos_of_pos a ha).ne',
    Real.log_div (stirlingSeq_pos_of_pos (b + 1) (by omega)).ne'
      (stirlingSeq_pos_of_pos b hb).ne']
  linarith

/-- **Sub-multiplicativity up to a factor of two**:
`stirlingSeq d · stirlingSeq m ≤ 2 · stirlingSeq (d+m)`. -/
theorem stirlingSeq_mul_le_two_mul_add
    (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    Stirling.stirlingSeq d * Stirling.stirlingSeq m ≤
      2 * Stirling.stirlingSeq (d + m) := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  induction r with
  | zero =>
      have hratio := stirlingSeq_succ_ratio_mono 1 d
        Nat.zero_lt_one (by omega)
      have hS1 := stirlingSeq_pos_of_pos 1 Nat.zero_lt_one
      have hSd := stirlingSeq_pos_of_pos d hd
      have hbase :
          Stirling.stirlingSeq d * Stirling.stirlingSeq 1 ≤
            2 * Stirling.stirlingSeq (d + 1) := by
        calc
          Stirling.stirlingSeq d * Stirling.stirlingSeq 1 =
              2 * Stirling.stirlingSeq d *
                (Stirling.stirlingSeq 2 / Stirling.stirlingSeq 1) := by
                  field_simp [hS1.ne']
                  nlinarith [stirlingSeq_one_sq]
          _ ≤ 2 * Stirling.stirlingSeq d *
                (Stirling.stirlingSeq (d + 1) / Stirling.stirlingSeq d) := by
                  gcongr
          _ = 2 * Stirling.stirlingSeq (d + 1) := by
                  field_simp [hSd.ne']
      simpa using hbase
  | succ r ih =>
      let t : ℕ := r + 1
      have ht : 0 < t := by simp [t]
      have ih' :
          Stirling.stirlingSeq d * Stirling.stirlingSeq t ≤
            2 * Stirling.stirlingSeq (d + t) := by
        simpa [t, Nat.succ_eq_add_one] using ih
      have hratio := stirlingSeq_succ_ratio_mono t (d + t) ht (by omega)
      have hSt := stirlingSeq_pos_of_pos t ht
      have hSt1 := stirlingSeq_pos_of_pos (t + 1) (by omega)
      have hSdt := stirlingSeq_pos_of_pos (d + t) (by omega)
      have hstep :
          Stirling.stirlingSeq d * Stirling.stirlingSeq (t + 1) ≤
            2 * Stirling.stirlingSeq (d + (t + 1)) := by
        calc
          Stirling.stirlingSeq d * Stirling.stirlingSeq (t + 1) =
              (Stirling.stirlingSeq d * Stirling.stirlingSeq t) *
                (Stirling.stirlingSeq (t + 1) / Stirling.stirlingSeq t) := by
                  field_simp [hSt.ne']
          _ ≤ (2 * Stirling.stirlingSeq (d + t)) *
                (Stirling.stirlingSeq (t + 1) / Stirling.stirlingSeq t) := by
                  gcongr
          _ ≤ (2 * Stirling.stirlingSeq (d + t)) *
                (Stirling.stirlingSeq (d + t + 1) /
                  Stirling.stirlingSeq (d + t)) := by
                  gcongr
          _ = 2 * Stirling.stirlingSeq (d + t + 1) := by
                  field_simp [hSdt.ne']
      simpa [t, Nat.succ_eq_add_one, Nat.add_assoc] using hstep

/-- **Lower bound on the binomial mass at the mean**: it is at least `1 / √(8dm/(d+m))`. -/
theorem binomial_mean_mass_ge
    (d m : ℕ) (hd : 0 < d) (hm : 0 < m) :
    1 / Real.sqrt
        (8 * (d : ℝ) * (m : ℝ) / ((d + m : ℕ) : ℝ)) ≤
      (((d + m).choose d : ℕ) : ℝ) *
        ((d : ℝ) / ((d + m : ℕ) : ℝ)) ^ d *
        ((m : ℝ) / ((d + m : ℕ) : ℝ)) ^ m := by
  have hSd := stirlingSeq_pos_of_pos d hd
  have hSm := stirlingSeq_pos_of_pos m hm
  have hprod : 0 < Stirling.stirlingSeq d * Stirling.stirlingSeq m :=
    mul_pos hSd hSm
  have hcross := stirlingSeq_mul_le_two_mul_add d m hd hm
  have hratio :
      (1 : ℝ) / 2 ≤
        Stirling.stirlingSeq (d + m) /
          (Stirling.stirlingSeq d * Stirling.stirlingSeq m) := by
    apply (le_div_iff₀ hprod).2
    nlinarith
  have hsqrt : 0 ≤
      Real.sqrt (2 * ((d + m : ℕ) : ℝ)) /
        (Real.sqrt (2 * (d : ℝ)) * Real.sqrt (2 * (m : ℝ))) := by
    positivity
  have hmul := mul_le_mul_of_nonneg_right hratio hsqrt
  rw [entropy_sqrt_factor_identity d m hd hm] at hmul
  rw [← binomial_mean_mass_eq_stirlingSeq d m hd hm] at hmul
  exact hmul

/-- The previous bound in radius coordinates: for integral `d = δ · n`,
`1 / √(8nδ(1−δ)) ≤ C(n,d) · δ^d · (1−δ)^(n−d)`. -/
theorem binomial_integral_mean_mass_ge
    (n d : ℕ) (δ : ℝ) (hn : 0 < n)
    (hδpos : 0 < δ) (hδlt : δ < 1)
    (hd : (d : ℝ) = δ * n) :
    1 / Real.sqrt (8 * (n : ℝ) * δ * (1 - δ)) ≤
      (n.choose d : ℝ) * δ ^ d * (1 - δ) ^ (n - d) := by
  obtain ⟨hdpos, hdlt, _⟩ :=
    entropy_radius_integer_bounds n d δ hn hδpos hδlt hd
  let m : ℕ := n - d
  have hmpos : 0 < m := by
    dsimp [m]
    omega
  have hsum : d + m = n := by
    dsimp [m]
    omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hδeq : δ = (d : ℝ) / (n : ℝ) := by
    apply (eq_div_iff hnR.ne').2
    exact hd.symm
  have hcomp : 1 - δ = (m : ℝ) / (n : ℝ) := by
    rw [hδeq]
    dsimp [m]
    rw [Nat.cast_sub (Nat.le_of_lt hdlt)]
    field_simp [hnR.ne']
  have hmean := binomial_mean_mass_ge d m hdpos hmpos
  calc
    1 / Real.sqrt (8 * (n : ℝ) * δ * (1 - δ)) =
        1 / Real.sqrt
          (8 * (d : ℝ) * (m : ℝ) / ((d + m : ℕ) : ℝ)) := by
      rw [hsum, hcomp, hδeq]
      field_simp [hnR.ne']
    _ ≤ (((d + m).choose d : ℕ) : ℝ) *
          ((d : ℝ) / ((d + m : ℕ) : ℝ)) ^ d *
          ((m : ℝ) / ((d + m : ℕ) : ℝ)) ^ m := hmean
    _ = (n.choose d : ℝ) * δ ^ d * (1 - δ) ^ (n - d) := by
      rw [hcomp, hδeq, hsum]

/-- `q`-ary entropy against the binomial mass: `q^(n · H_q(δ)) · (δ^d · (1−δ)^(n−d)) = (q−1)^d`
when `d = δ · n`. -/
theorem qEntropy_power_mul_mass_eq
    (q n d : ℕ) (δ : ℝ) (hq : 2 ≤ q) (hn : 0 < n)
    (hδpos : 0 < δ) (hδlt : δ < 1)
    (hd : (d : ℝ) = δ * n) :
    (q : ℝ) ^ ((n : ℝ) * qEntropy q δ) *
        (δ ^ d * (1 - δ) ^ (n - d)) =
      (((q - 1 : ℕ) : ℝ) ^ d) := by
  obtain ⟨_, hdlt, _⟩ :=
    entropy_radius_integer_bounds n d δ hn hδpos hδlt hd
  have hqR : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_two hq)
  have hq1R : (1 : ℝ) < q := by exact_mod_cast (show 1 < q by omega)
  have hqne : (q : ℝ) ≠ 1 := ne_of_gt hq1R
  have hqm1R : (0 : ℝ) < (q : ℝ) - 1 := sub_pos.mpr hq1R
  have hqsub : (((q - 1 : ℕ) : ℝ)) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ q by omega)]
    norm_num
  have hcomp : (0 : ℝ) < 1 - δ := sub_pos.mpr hδlt
  have hmcast : (((n - d : ℕ) : ℝ)) = (1 - δ) * (n : ℝ) := by
    rw [Nat.cast_sub (Nat.le_of_lt hdlt), hd]
    ring
  have hexp :
      (n : ℝ) * qEntropy q δ =
        (d : ℝ) * Real.logb q ((q : ℝ) - 1) -
          (d : ℝ) * Real.logb q δ -
            ((n - d : ℕ) : ℝ) * Real.logb q (1 - δ) := by
    rw [qEntropy_eq_logb_form, hd, hmcast]
    ring
  have hpow (x : ℝ) (hx : 0 < x) (r : ℕ) :
      (q : ℝ) ^ ((r : ℝ) * Real.logb q x) = x ^ r := by
    rw [mul_comm, Real.rpow_mul hqR.le,
      Real.rpow_logb hqR hqne hx, Real.rpow_natCast]
  have hδpow : δ ^ d ≠ 0 := pow_ne_zero d hδpos.ne'
  have hcomppow : (1 - δ) ^ (n - d) ≠ 0 :=
    pow_ne_zero (n - d) hcomp.ne'
  rw [hexp, Real.rpow_sub hqR, Real.rpow_sub hqR,
    hpow ((q : ℝ) - 1) hqm1R d,
    hpow δ hδpos d, hpow (1 - δ) hcomp (n - d), hqsub]
  field_simp [hδpow, hcomppow]

/-- **The single-shell entropy bound**:

`q^(n · H_q(δ)) / √(8nδ(1−δ)) ≤ C(n, δn) · (q−1)^(δn)`.

The right side is a single shell of the Hamming ball, so the volume — the sum over all shells at
radius at most `δn` — is at least as large. -/
theorem qary_shell_entropy_lower
    (q n d : ℕ) (δ : ℝ) (hq : 2 ≤ q) (hn : 0 < n)
    (hδpos : 0 < δ) (hδlt : δ < 1)
    (hd : (d : ℝ) = δ * n) :
    (q : ℝ) ^ ((n : ℝ) * qEntropy q δ) /
        (8 * (n : ℝ) * δ * (1 - δ)) ^ ((1 : ℝ) / 2) ≤
      ((Nat.choose n d * (q - 1) ^ d : ℕ) : ℝ) := by
  have hbin :=
    binomial_integral_mean_mass_ge n d δ hn hδpos hδlt hd
  have hQ : 0 ≤ (q : ℝ) ^ ((n : ℝ) * qEntropy q δ) :=
    Real.rpow_nonneg (by positivity) _
  have hscaled := mul_le_mul_of_nonneg_left hbin hQ
  rw [← Real.sqrt_eq_rpow]
  calc
    (q : ℝ) ^ ((n : ℝ) * qEntropy q δ) /
        Real.sqrt (8 * (n : ℝ) * δ * (1 - δ)) =
      (q : ℝ) ^ ((n : ℝ) * qEntropy q δ) *
        (1 / Real.sqrt (8 * (n : ℝ) * δ * (1 - δ))) := by ring
    _ ≤ (q : ℝ) ^ ((n : ℝ) * qEntropy q δ) *
        ((n.choose d : ℝ) * δ ^ d * (1 - δ) ^ (n - d)) := hscaled
    _ = (n.choose d : ℝ) *
        ((q : ℝ) ^ ((n : ℝ) * qEntropy q δ) *
          (δ ^ d * (1 - δ) ^ (n - d))) := by ring
    _ = (n.choose d : ℝ) * (((q - 1 : ℕ) : ℝ) ^ d) := by
      rw [qEntropy_power_mul_mass_eq q n d δ hq hn hδpos hδlt hd]
    _ = ((Nat.choose n d * (q - 1) ^ d : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_pow]

open _root_.Code in
/-- **The entropy form of the volume lower bound** ([ABF26] Corollary 3.8). Feeding the
[MS77] binary binomial-coefficient estimate into `lambda_ge_elias_volume`, dividing by `q^{n-k}`
and writing `ρ := k/n`, gives

  `|Λ(C, δ)| ≥ q^{n·(ρ - 1 + H_q(δ))} / √(8·n·δ·(1-δ))`.

Precisely, [MS77] Chapter 10, §11, Lemma 7, equation (16), printed page 309 states for
`0 < δ < 1` and integer `δn` the binary shell estimate
`2^{n·H₂(δ)} / √(8nδ(1−δ)) ≤ C(n,δn)`. It is not stated there as a q-ary ball bound. The in-tree
proof first derives that same single-shell estimate from finite Stirling bounds, then multiplies by
`(q−1)^{δn}` and uses the q-entropy identity to obtain the displayed q-ary shell bound; the ball is
at least that shell. Thus the q-ary result is a proved algebraic generalisation, not a verbatim
[MS77] theorem. [DG25dist] gives refinements. This is the arbitrary-alphabet form stated by
[ABF26]; `linear_lambda_ge_entropy_volume` below is its field-linear specialization.

The hypothesis `_hδn_int` is exactly [MS77]'s `δn`-integrality condition. It is not decoration:
without it the bound is **false** at small `δ`, since for `0 < δ·n < 1` the relative ball collapses
to Hamming
radius `0`, so the list is `{f} ∩ C` while the entropy-volume right-hand side can exceed `1`. -/
theorem lambda_ge_entropy_volume {A : Type} [Fintype A] [Nontrivial A] [DecidableEq A]
    (C : Set (ι → A)) (k : ℕ) (hcard : C.ncard = Fintype.card A ^ k)
    (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (_hδn_int : ∃ d : ℕ, (d : ℝ) = δ * Fintype.card ι) :
    let q : ℕ := Fintype.card A
    let n : ℕ := Fintype.card ι
    let ρ : ℝ := k / n
    ENNReal.ofReal
        ((q : ℝ) ^ ((n : ℝ) * (ρ - 1 + qEntropy q δ))
          / (8 * n * δ * (1 - δ)) ^ ((1 : ℝ) / 2))
      ≤ (Lambda C δ : ENNReal) := by
  classical
  dsimp
  let q : ℕ := Fintype.card A
  let n : ℕ := Fintype.card ι
  obtain ⟨d, hd⟩ := _hδn_int
  have hn_pos : 0 < n := Fintype.card_pos
  have hq_two : 2 ≤ q := by
    dsimp [q]
    exact Fintype.one_lt_card
  have hd_lt_real : (d : ℝ) < n := by
    rw [hd]
    have hnR : (0 : ℝ) < n := by positivity
    nlinarith
  have hd_lt : d < n := by exact_mod_cast hd_lt_real
  have hfloor : ⌊δ * (n : ℝ)⌋₊ = d := by
    rw [← hd]
    simp only [Nat.floor_natCast]
  have hshell_nat : Nat.choose n d * (q - 1) ^ d ≤
      hammingBallVolume q δ n := by
    unfold hammingBallVolume
    exact Finset.single_le_sum
      (s := Finset.range (⌊δ * (n : ℝ)⌋₊ + 1))
      (f := fun i => Nat.choose n i * (q - 1) ^ i)
      (fun i _ => Nat.zero_le _)
      (by simp only [Finset.mem_range, hfloor]; omega)
  have hshell_real : ((Nat.choose n d * (q - 1) ^ d : ℕ) : ℝ) ≤
      (hammingBallVolume q δ n : ℝ) := by
    exact_mod_cast hshell_nat
  have hvol : (q : ℝ) ^ ((n : ℝ) * qEntropy q δ) /
      (8 * n * δ * (1 - δ)) ^ ((1 : ℝ) / 2) ≤
      (hammingBallVolume q δ n : ℝ) :=
    le_trans (qary_shell_entropy_lower q n d δ hq_two hn_pos
      _hδ_pos _hδ_lt (by simpa only [n] using hd)) hshell_real
  have hq_posR : (0 : ℝ) < q := by positivity
  have hElias := lambda_ge_elias_volume C k hcard δ _hδ_pos _hδ_lt
  apply le_trans ?_ hElias
  apply ENNReal.ofReal_le_ofReal
  change (q : ℝ) ^ ((n : ℝ) * ((k : ℝ) / n - 1 + qEntropy q δ)) /
      (8 * n * δ * (1 - δ)) ^ ((1 : ℝ) / 2) ≤
    (hammingBallVolume q δ n : ℝ) / (q : ℝ) ^ ((n : ℝ) - k)
  have hexp : (n : ℝ) * ((k : ℝ) / n - 1 + qEntropy q δ) =
      (n : ℝ) * qEntropy q δ - ((n : ℝ) - k) := by
    have hn0 : (n : ℝ) ≠ 0 := by positivity
    field_simp
    ring
  rw [hexp, Real.rpow_sub hq_posR]
  calc
    (q : ℝ) ^ ((n : ℝ) * qEntropy q δ) /
        (q : ℝ) ^ ((n : ℝ) - k) /
        (8 * n * δ * (1 - δ)) ^ ((1 : ℝ) / 2) =
      ((q : ℝ) ^ ((n : ℝ) * qEntropy q δ) /
        (8 * n * δ * (1 - δ)) ^ ((1 : ℝ) / 2)) /
          (q : ℝ) ^ ((n : ℝ) - k) := by ring
    _ ≤ (hammingBallVolume q δ n : ℝ) /
        (q : ℝ) ^ ((n : ℝ) - k) :=
      div_le_div_of_nonneg_right hvol (Real.rpow_nonneg hq_posR.le _)

/-- **The entropy form of the volume lower bound** for a field-linear code ([ABF26] Corollary
3.8), specialized from `lambda_ge_entropy_volume`. -/
theorem linear_lambda_ge_entropy_volume
    (C : Submodule F (ι → F)) (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (_hδn_int : ∃ d : ℕ, (d : ℝ) = δ * Fintype.card ι) :
    let q : ℕ := Fintype.card F
    let n : ℕ := Fintype.card ι
    let k : ℕ := Module.finrank F C
    let ρ : ℝ := k / n
    ENNReal.ofReal
        ((q : ℝ) ^ ((n : ℝ) * (ρ - 1 + qEntropy q δ))
          / (8 * n * δ * (1 - δ)) ^ ((1 : ℝ) / 2))
      ≤ (Lambda ((C : Set (ι → F))) δ : ENNReal) :=
  lambda_ge_entropy_volume (C : Set (ι → F)) (Module.finrank F C)
    (submodule_ncard_eq_pow_finrank C) δ _hδ_pos _hδ_lt _hδn_int

/-- **The cardinality bound from the rate–radius relation** — the arithmetic half of [ABF26]
Theorem 3.9. Given `δ ≤ ℓ/(ℓ+1) · (1-ρ)` for a linear code `C ⊆ F^n` of rate `ρ`,

  `|C| ≤ |F|^{n - ⌊(ℓ+1)/ℓ · δ · n⌋}` ,

by `|C| = |F|^{dim C}` and `⌊(ℓ+1)/ℓ·δ·n⌋ ≤ n - dim C`.

This is deliberately *not* named for [ST20] Theorem 1.2: that theorem's content is the implication
from `ℓ`-list-decodability to the cardinality bound, proved by
`linear_card_le_generalized_singleton` below. Splitting the two keeps this lemma honest about what
it proves — the arithmetic step from the rate–radius relation, with no list-decoding premise. -/
theorem linear_card_le_of_rate_radius
    (C : Submodule F (ι → F)) (ℓ : ℕ) (δ : ℝ)
    (_hℓ_pos : 0 < ℓ)
    (hδ_bound : δ ≤ (ℓ : ℝ) / (ℓ + 1) *
      (1 - (Module.finrank F C : ℝ) / Fintype.card ι)) :
    (Set.ncard ((C : Set (ι → F))) : ℝ)
      ≤ (Fintype.card F : ℝ) ^
          ((Fintype.card ι : ℝ)
            - (Nat.floor (((ℓ : ℝ) + 1) / ℓ * δ * Fintype.card ι) : ℝ)) := by
  classical
  set q : ℕ := Fintype.card F with hq
  set n : ℕ := Fintype.card ι with hn
  set k : ℕ := Module.finrank F C with hk
  -- `|C| = q ^ k` (linearity).
  have hcard_C : (C : Set (ι → F)).ncard = q ^ k := by
    rw [submodule_ncard_eq_pow_finrank, hq, hk]
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by
    have : 1 < q := hq ▸ Fintype.one_lt_card
    exact_mod_cast this.le
  have hnpos : (0 : ℝ) < n := by rw [hn]; exact_mod_cast Fintype.card_pos
  have hℓpos : (0 : ℝ) < ℓ := by exact_mod_cast _hℓ_pos
  -- `k ≤ n` (rank of a subspace of `F^n` is at most `n`).
  have hkn : k ≤ n := by
    rw [hk, hn]
    have h := Submodule.finrank_le C
    rwa [Module.finrank_fintype_fun_eq_card] at h
  -- From `hδ_bound`, `(ℓ+1)/ℓ · δ ≤ 1 - k/n`, hence `(ℓ+1)/ℓ · δ · n ≤ n - k`.
  have hmid : ((ℓ : ℝ) + 1) / ℓ * δ ≤ 1 - (k : ℝ) / n := by
    have hfac : (0 : ℝ) < ((ℓ : ℝ) + 1) / ℓ := by positivity
    calc ((ℓ : ℝ) + 1) / ℓ * δ
        ≤ ((ℓ : ℝ) + 1) / ℓ * ((ℓ : ℝ) / ((ℓ : ℝ) + 1) * (1 - (k : ℝ) / n)) :=
          mul_le_mul_of_nonneg_left hδ_bound (le_of_lt hfac)
      _ = 1 - (k : ℝ) / n := by field_simp
  have hstep : ((ℓ : ℝ) + 1) / ℓ * δ * n ≤ (n : ℝ) - k := by
    calc ((ℓ : ℝ) + 1) / ℓ * δ * n
        = (((ℓ : ℝ) + 1) / ℓ * δ) * n := by ring
      _ ≤ (1 - (k : ℝ) / n) * n := mul_le_mul_of_nonneg_right hmid (le_of_lt hnpos)
      _ = (n : ℝ) - k := by field_simp
  have hfloor : Nat.floor (((ℓ : ℝ) + 1) / ℓ * δ * n) ≤ n - k := by
    rw [← Nat.cast_sub hkn] at hstep
    calc Nat.floor (((ℓ : ℝ) + 1) / ℓ * δ * n)
        ≤ Nat.floor (((n - k : ℕ) : ℝ)) := Nat.floor_le_floor hstep
      _ = n - k := Nat.floor_natCast _
  -- Conclude: `q^k ≤ q^(n - ⌊…⌋)` since the exponent is `≥ k`.
  have hexp : (k : ℝ) ≤ (n : ℝ) - (Nat.floor (((ℓ : ℝ) + 1) / ℓ * δ * n) : ℝ) := by
    have hle : (Nat.floor (((ℓ : ℝ) + 1) / ℓ * δ * n) : ℝ) ≤ (n : ℝ) - k := by
      have := hfloor
      rw [← Nat.cast_sub hkn]
      exact_mod_cast this
    linarith
  rw [hcard_C]
  calc ((q ^ k : ℕ) : ℝ)
      = (q : ℝ) ^ (k : ℝ) := by rw [Nat.cast_pow, Real.rpow_natCast]
    _ ≤ (q : ℝ) ^ ((n : ℝ) - (Nat.floor (((ℓ : ℝ) + 1) / ℓ * δ * n) : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le hq1 hexp

/-- **The generalized Singleton bound for list decoding** ([ABF26] Theorem 3.9, after
[ST20, Theorem 1.2]). For a finite field `F`, `0 < ℓ < |F|`, `δ ∈ (0, 1)` with `δ·n` an integer, and
a linear code `C ⊆ F^n` with `|Λ(C, δ)| ≤ ℓ`:

  `|C| ≤ |F|^{n - ⌊(ℓ+1)/ℓ · δ · n⌋}` ,

whence `δ ≤ ℓ/(ℓ+1) · (1-ρ)` via `linear_card_le_of_rate_radius`'s converse arithmetic. The content
is the *implication* from list decodability; the arithmetic step is `linear_card_le_of_rate_radius`.

**`_hδn_int` is [ST20]'s own hypothesis, not an ArkLib convenience.** Their proof of Theorem 1.2
opens "Let `a := ⌊(L+1)rn/L⌋ = rn + ⌊rn/L⌋` (**assuming `rn` is an integer**)", and the identity it
records is false otherwise. [ABF26]'s printing drops the hypothesis, and without it the statement is
**false**: the ternary length-3 repetition code `C = {000, 111, 222}` over `𝔽₃` is
`(δ = 1/2, ℓ = 1)`-list-decodable — its minimum distance is `3`, so the radius-`⌊δn⌋ = 1` balls are
disjoint — yet `⌊(ℓ+1)/ℓ·δ·n⌋ = ⌊3⌋ = 3` forces the right-hand side to `3^0 = 1 < 3 = |C|`. ([ST20]
separately assume `rn/L ∈ ℤ` "for ease of presentation", which only removes the floor.)

**`_hexp_nonneg` is a second hypothesis both papers omit, and it is also necessary.** [ST20]'s
pigeonhole needs `a ≤ n`, there being `q^{n−a}` prefixes only then. Without it the statement is
false for the zero code: `C = ⊥` with `n = 10`, `δ = 9/10` and `ℓ = 1` has `Λ(C, δ) = 1 ≤ ℓ` and
`δ·n = 9 ∈ ℕ`, while `a = ⌊2·9⌋ = 18 > n` makes the right-hand side `q^{−8} < 1 = |C|`. The same
omission voids [ABF26]'s "Consequently `δ ≤ ℓ/(ℓ+1)·(1−ρ)`" for `C = ⊥`.

**Narrower than [ST20] in one direction.** Their Theorem 1.2 has a first, alphabet-generic half
`|C| ≤ L·q^{n−a}` for arbitrary `C ⊆ Q^n`; the `L`-free form below is their linear refinement, which
is what `_hℓ_lt : ℓ < |F|` buys and what [ABF26] prints. -/
theorem linear_card_le_generalized_singleton
    (C : Submodule F (ι → F)) (ℓ : ℕ) (δ : ℝ)
    (_hℓ_pos : 0 < ℓ) (_hℓ_lt : ℓ < Fintype.card F)
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (_hδn_int : ∃ e : ℕ, (e : ℝ) = δ * Fintype.card ι)
    (_hexp_nonneg : Nat.floor (((ℓ : ℝ) + 1) / ℓ * δ * Fintype.card ι) ≤ Fintype.card ι)
    (_hΛ : Lambda ((C : Set (ι → F))) δ ≤ (ℓ : ℕ∞)) :
    (Set.ncard ((C : Set (ι → F))) : ℝ)
      ≤ (Fintype.card F : ℝ) ^
          ((Fintype.card ι : ℝ)
            - (Nat.floor (((ℓ : ℝ) + 1) / ℓ * δ * Fintype.card ι) : ℝ)) := by
  classical
  rcases _hδn_int with ⟨e, he⟩
  set q : ℕ := Fintype.card F with hq
  set n : ℕ := Fintype.card ι with hn
  set k : ℕ := Module.finrank F C with hk
  set a : ℕ := Nat.floor (((ℓ : ℝ) + 1) / ℓ * δ * n) with ha
  have hℓ0 : ℓ ≠ 0 := Nat.ne_of_gt _hℓ_pos
  have hnpos : 0 < n := hn ▸ Fintype.card_pos
  have hepos : 0 < e := by
    have : (0 : ℝ) < e := by rw [he]; positivity
    exact_mod_cast this
  have harg : ((ℓ : ℝ) + 1) / ℓ * δ * n = (e : ℝ) + (e : ℝ) / ℓ := by
    calc
      ((ℓ : ℝ) + 1) / ℓ * δ * n = ((ℓ : ℝ) + 1) / ℓ * (δ * n) := by ring
      _ = ((ℓ : ℝ) + 1) / ℓ * e := by rw [← he]
      _ = (e : ℝ) + (e : ℝ) / ℓ := by field_simp
  have haeq : a = e + e / ℓ := by
    rw [ha, harg]
    calc
      Nat.floor ((e : ℝ) + (e : ℝ) / ℓ) = Nat.floor ((e : ℝ) / ℓ + (e : ℝ)) := by rw [add_comm]
      _ = Nat.floor ((e : ℝ) / ℓ) + e := Nat.floor_add_natCast (by positivity) e
      _ = e / ℓ + e := by rw [Nat.floor_div_natCast, Nat.floor_natCast]
      _ = e + e / ℓ := Nat.add_comm _ _
  have hka : k + a ≤ n := by
    by_contra hnot
    have hlt : n < k + a := by omega
    obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq
      (show n - a ≤ (Finset.univ : Finset ι).card by simp only [Finset.card_univ]; omega)
    let p : C →ₗ[F] (↥T → F) :=
      (LinearMap.funLeft F F (fun x : ↥T => (x : ι))).comp C.subtype
    have hrange : Module.finrank F p.range ≤ n - a := by
      calc
        Module.finrank F p.range ≤ Module.finrank F (↥T → F) := Submodule.finrank_le _
        _ = Fintype.card ↥T := Module.finrank_pi F
        _ = T.card := Fintype.card_coe T
        _ = n - a := hTcard
    have hkerpos : 0 < Module.finrank F p.ker := by
      have hdim := LinearMap.finrank_range_add_finrank_ker p
      rw [← hk] at hdim
      omega
    have hker_card : Fintype.card p.ker = q ^ Module.finrank F p.ker := by
      rw [← Nat.card_eq_fintype_card, hq, ← Nat.card_eq_fintype_card (α := F)]
      exact Module.natCard_eq_pow_finrank (K := F) (V := p.ker)
    have hq1 : 1 ≤ q := by rw [hq]; exact Fintype.card_pos
    have hq_le_ker : q ≤ Fintype.card p.ker := by
      rw [hker_card]
      exact le_self_pow hq1 (Nat.ne_of_gt hkerpos)
    have hm_le_ker : ℓ + 1 ≤ Fintype.card p.ker := by omega
    let cemb : Fin (ℓ + 1) ↪ p.ker := Classical.choice
      (Function.Embedding.nonempty_of_card_le (by simpa using hm_le_ker))
    let c : Fin (ℓ + 1) → C := fun i => (cemb i).1
    have hc_zero : ∀ (i : Fin (ℓ + 1)) (x : ↥T), (c i : ι → F) x = 0 := by
      intro i x
      have hz := (cemb i).2
      change (fun z : ↥T => (c i : ι → F) z) = 0 at hz
      exact congrFun hz x
    have hc_inj : Function.Injective c := by
      intro i j hij
      apply cemb.injective
      apply Subtype.ext
      exact hij
    let U : Finset ι := Finset.univ \ T
    have hUcard : U.card = a := by
      dsimp [U]
      rw [Finset.card_sdiff]
      simp only [Finset.inter_univ, Finset.card_univ, hTcard]
      omega
    let d : ℕ := a / (ℓ + 1)
    have hgd : Fintype.card (Fin (ℓ + 1) × Fin d) ≤ Fintype.card ↥U := by
      simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, hUcard]
      dsimp [d]
      simpa [mul_comm] using Nat.div_mul_le_self a (ℓ + 1)
    let g : (Fin (ℓ + 1) × Fin d) ↪ ↥U := Classical.choice
      (Function.Embedding.nonempty_of_card_le hgd)
    let owner : ι → Fin (ℓ + 1) := fun x =>
      if h : ∃ z : Fin (ℓ + 1) × Fin d, (g z : ι) = x then
        (Classical.choose h).1
      else 0
    have howner : ∀ (i : Fin (ℓ + 1)) (j : Fin d), owner (g (i, j) : ι) = i := by
      intro i j
      dsimp [owner]
      rw [dif_pos ⟨(i, j), rfl⟩]
      let hex : ∃ z : Fin (ℓ + 1) × Fin d, (g z : ι) = (g (i, j) : ι) := ⟨(i, j), rfl⟩
      have heq : Classical.choose hex = (i, j) :=
        g.injective (Subtype.ext (Classical.choose_spec hex))
      exact congrArg Prod.fst heq
    let y : ι → F := fun x => if x ∈ T then 0 else (c (owner x) : ι → F) x
    let B : Fin (ℓ + 1) → Finset ι := fun i => Finset.univ.image fun j : Fin d => (g (i, j) : ι)
    have hBcard : ∀ i, (B i).card = d := by
      intro i
      have hinj : Set.InjOn (fun j : Fin d => (g (i, j) : ι)) (Finset.univ : Finset (Fin d)) := by
        intro x _ z _ hxz
        have : (i, x) = (i, z) := g.injective (Subtype.ext hxz)
        exact congrArg Prod.snd this
      dsimp [B]
      rw [Finset.card_image_iff.mpr hinj]
      exact Fintype.card_fin d
    have hBsub : ∀ i, B i ⊆ U := by
      intro i x hx
      simp only [B, Finset.mem_image, Finset.mem_univ, true_and] at hx
      obtain ⟨j, rfl⟩ := hx
      exact (g (i, j)).2
    have hdist : ∀ i, hammingDist (c i : ι → F) y ≤ a - d := by
      intro i
      rw [Code.hammingDist_eq_disagreementCols_card]
      apply le_trans (Finset.card_le_card (show Code.disagreementCols (c i : ι → F) y ⊆ U \ B i by
        intro x hx
        have hxne : (c i : ι → F) x ≠ y x := Code.mem_disagreementCols.mp hx
        have hxT : x ∉ T := by
          intro hxmem
          have hci : (c i : ι → F) x = 0 := hc_zero i ⟨x, hxmem⟩
          have hy : y x = 0 := by simp only [y, hxmem, ↓reduceIte]
          exact hxne (hci.trans hy.symm)
        have hxU : x ∈ U := Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, hxT⟩
        refine Finset.mem_sdiff.mpr ⟨hxU, ?_⟩
        intro hxmem
        simp only [B, Finset.mem_image, Finset.mem_univ, true_and] at hxmem
        obtain ⟨j, hj⟩ := hxmem
        apply hxne
        simp only [y, hxT, ↓reduceIte]
        rw [← hj, howner]))
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (hBsub i), hUcard, hBcard]
    have hradius : a - d ≤ e := by
      dsimp [d]
      rw [haeq]
      have hmul : e / ℓ * ℓ ≤ e := Nat.div_mul_le_self e ℓ
      have hdiv : e / ℓ ≤ (e + e / ℓ) / (ℓ + 1) := by
        apply (Nat.le_div_iff_mul_le (by omega : 0 < ℓ + 1)).2
        calc
          e / ℓ * (ℓ + 1) = e / ℓ * ℓ + e / ℓ := by
            rw [Nat.mul_add, Nat.mul_one]
          _ ≤ e + e / ℓ := Nat.add_le_add_right hmul _
      omega
    have hdist_e : ∀ i, hammingDist (c i : ι → F) y ≤ e := fun i => (hdist i).trans hradius
    have hfloor_e : Nat.floor (δ * Fintype.card ι) = e := by
      rw [← he, Nat.floor_natCast]
    have hclose : ∀ i, (c i : ι → F) ∈ closeCodewordsRel ((C : Set (ι → F))) y δ := by
      intro i
      rw [closeCodewordsRel_eq_setOf C δ (le_of_lt _hδ_pos) y]
      exact ⟨(c i).2, by rw [hfloor_e]; exact hdist_e i⟩
    have hlist := Lambda_le_iff_forall_ncard_le.mp _hΛ y
    have hlower : ℓ + 1 ≤ (closeCodewordsRel ((C : Set (ι → F))) y δ).ncard := by
      apply Set.le_ncard_of_inj_on_range
        (fun r : ℕ => if hr : r < ℓ + 1 then (c ⟨r, hr⟩ : ι → F) else 0)
      · intro r hr
        rw [dif_pos hr]
        exact hclose ⟨r, hr⟩
      · intro r hr s hs hrs
        simp only [dif_pos hr, dif_pos hs] at hrs
        have hij : (⟨r, hr⟩ : Fin (ℓ + 1)) = ⟨s, hs⟩ := by
          apply hc_inj
          apply Subtype.ext
          exact hrs
        exact Fin.ext_iff.mp hij
    omega
  have hcard_C : (C : Set (ι → F)).ncard = q ^ k := by
    rw [submodule_ncard_eq_pow_finrank, hq, hk]
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by
    have : 1 < q := hq ▸ Fintype.one_lt_card
    exact_mod_cast this.le
  have hkle : k ≤ n - a := by omega
  have hexp : (k : ℝ) ≤ (n : ℝ) - (a : ℝ) := by
    rw [← Nat.cast_sub _hexp_nonneg]
    exact_mod_cast hkle
  rw [hcard_C]
  calc
    ((q ^ k : ℕ) : ℝ) = (q : ℝ) ^ (k : ℝ) := by rw [Nat.cast_pow, Real.rpow_natCast]
    _ ≤ (q : ℝ) ^ ((n : ℝ) - (a : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hq1R hexp

end LowerBounds_General

section RandomLinear

/-- **A random linear code of near-capacity rate has a large list** ([ABF26] Theorem 3.11, after
[GLMRSW22, Theorem 4.1]).

The source, verbatim in its own variables: "Fix a prime power `q`, fix `p ∈ (0, 1 − 1/q)`, and fix
`δ ∈ (0, 1)`. There exists `ε_{p,q,δ} > 0` such that for all `ε ∈ (0, ε_{p,q,δ})` and `n`
sufficiently large, a random linear code in `F_q^n` of rate `1 − h_q(p) − ε` is not
`(p, ⌊h_q(p)/ε − δ⌋)`-list-decodable with probability `1 − q^{−Ω(n)}`." Its random model, from §1.1,
is "a random linear code is a uniformly random subspace of `F_q^n` of certain dimension" — so the
counting form below is the source's probability exactly, not an approximation of it. (Its §1.2
working model is the kernel of a uniformly random parity-check matrix, which conditioned on full
rank is the same uniform distribution over dimension-`k` subspaces, by `GL_n`-invariance.)

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
pinned two-sidedly into `ρ ≤ k/n ≤ ρ + 1/n`, admitting `k = ⌈ρ·n⌉` up to the boundary case. -/
theorem random_linear_lambda_lower
    (q : ℕ) (_hq_pp : IsPrimePow q)
    (δ : ℝ) (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1 - 1 / q)
    (ε : ℝ) (_hε_pos : 0 < ε) (_hε_lt : ε < 1) :
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
  sorry -- external admit: [GLMRSW22, Theorem 4.1].

/-- **Existence form of the random-linear-code lower bound**, derived in-tree from the
high-probability counting form `random_linear_lambda_lower`: some linear code `C ⊆ F^n` with
dimension in the band `ρ ≤ finrank/n ≤ ρ + 1/n` satisfies

  `|Λ(C, δ)| ≥ ⌊H_q(δ) / (1 - H_q(δ) - ρ) - ε⌋` .

The bad-event count is below the whole family's, the family `{C | finrank C = ⌈ρ·n⌉}` is nonempty
(a coordinate-kernel subspace realises any dimension `≤ n`), so a good code exists.

The hypothesis `hρ0 : 0 ≤ ρ` is trivially true in the source's regime, where rates approach
capacity `1 − H_q(δ)` from below with small `γ`. It is needed here only because
`Basic/Entropy.lean` does not yet prove `H_q(δ) < 1` for `δ < 1 − 1/q`, which would let `γ` be
shrunk below `1 − H_q(δ)`. -/
theorem random_linear_lambda_lower_exists
    (q : ℕ) (hq_pp : IsPrimePow q)
    (δ : ℝ) (hδ_pos : 0 < δ) (hδ_lt : δ < 1 - 1 / q)
    (ε : ℝ) (hε_pos : 0 < ε) (hε_lt : ε < 1) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ ρ : ℝ, 0 ≤ ρ → 1 - qEntropy q δ - γ < ρ → ρ < 1 - qEntropy q δ →
        ∃ n₀ : ℕ,
          ∀ {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
            {F : Type} [Field F] [Fintype F] [DecidableEq F],
            Fintype.card F = q → n₀ ≤ Fintype.card ι →
            ∃ C : Submodule F (ι → F),
              ρ ≤ (Module.finrank F C : ℝ) / Fintype.card ι ∧
              (Module.finrank F C : ℝ) / Fintype.card ι ≤ ρ + 1 / Fintype.card ι ∧
              ((Nat.floor (qEntropy q δ / (1 - qEntropy q δ - ρ) - ε) : ℕ) : ℕ∞) ≤
                Lambda ((C : Set (ι → F))) δ := by
  obtain ⟨γ, hγ_pos, hmain⟩ :=
    random_linear_lambda_lower q hq_pp δ hδ_pos hδ_lt ε hε_pos hε_lt
  refine ⟨γ, hγ_pos, fun ρ hρ0 hργ hρH => ?_⟩
  obtain ⟨c, hc_pos, n₀, hbound⟩ := hmain ρ hργ hρH
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
    ((Nat.floor (qEntropy q δ / (1 - qEntropy q δ - ρ) - ε) : ℕ) : ℕ∞) with hB_def
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
  · by_contra hle
    exact hCbad ⟨hCk, lt_of_not_ge hle⟩

end RandomLinear

end CodingTheory
