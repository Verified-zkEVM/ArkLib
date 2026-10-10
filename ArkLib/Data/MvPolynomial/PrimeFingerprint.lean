/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import Mathlib.Algebra.BigOperators.Associated
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Log
public import Mathlib.Data.ZMod.Basic
public import Mathlib.FieldTheory.Finite.Basic

/-!
# Fingerprinting an integer polynomial modulo a random prime

*Fingerprinting* ([CHA24], and [BGKLSW26, Lemma 4.8] for several variables) replaces a claim
`h = 0` about an integer polynomial `h ∈ ℤ[X₁, …, Xₘ]` by the claim that `h` vanishes modulo a
random prime `q` at a random point `α ∈ 𝔽_qᵐ`. If `h ≠ 0` has total degree `≤ d` and all its
coefficients have absolute value `≤ M`, the claim is false with high probability:

* the primes `q` that divide *every* coefficient of `h` all divide one fixed nonzero coefficient,
  so there are at most `log_{q_min} M` of them in a set `P` of primes `≥ q_min`
  (`MvPolynomial.card_filter_map_eq_zero_le_log`);
* for every other prime `q`, `h mod q` is a nonzero polynomial of degree `≤ d` over `𝔽_q`, which
  by Schwartz–Zippel vanishes at a uniform point with probability `≤ d / q ≤ d / q_min`
  (`MvPolynomial.zeroCountMod_div_le`).

`MvPolynomial.avg_zeroCountMod_div_le` combines the two: for a uniform prime `q ∈ P` and a uniform
`α ∈ 𝔽_qᵐ`, `Pr[h(α) ≡ 0 (mod q)] ≤ log_{q_min} M / |P| + d / q_min`. The form in terms of
`⌊log₂ q_min⌋` stated in [BGKLSW26] is `MvPolynomial.avg_zeroCountMod_div_le_logb`.

## References

* [CHA24] M. Campanelli, M. Hall-Andersen. *Fully succinct arguments over the integers from first
  principles*. ePrint 2024/1548.
* [BGKLSW26] R. Bloemen, A. Garreta, M. Kostrzewa, S. Londhe, L. Soukhanov, J. Wu.
  *BitZ: proofs and commitments in arbitrary rings through binary fields*. ePrint 2026/2141.
-/

@[expose] public section

open Finset

namespace MvPolynomial

variable {m : ℕ}

/-- The number of zeros in `𝔽_qᵐ` of the reduction modulo `q` of an integer polynomial `h`. -/
noncomputable def zeroCountMod (h : MvPolynomial (Fin m) ℤ) (q : ℕ) : ℕ :=
  Nat.card {α : Fin m → ZMod q // eval α (map (Int.castRingHom (ZMod q)) h) = 0}

/-- If `q` divides every coefficient of `h`, every point of `𝔽_qᵐ` is a zero of `h mod q`. -/
theorem zeroCountMod_eq_of_map_eq_zero {h : MvPolynomial (Fin m) ℤ} {q : ℕ} (hq : q ≠ 0)
    (h0 : map (Int.castRingHom (ZMod q)) h = 0) : zeroCountMod h q = q ^ m := by
  have : NeZero q := ⟨hq⟩
  unfold zeroCountMod
  rw [h0]
  simp [Nat.card_eq_fintype_card]

/-- **Schwartz–Zippel modulo a prime.** If `h mod q ≠ 0` for a prime `q` and `h` has total degree
`≤ d`, a uniform point of `𝔽_qᵐ` is a zero of `h mod q` with probability `≤ d / q`. -/
theorem zeroCountMod_div_le {h : MvPolynomial (Fin m) ℤ} {q d : ℕ} (hq : q.Prime)
    (hne : map (Int.castRingHom (ZMod q)) h ≠ 0) (hd : h.totalDegree ≤ d) :
    (zeroCountMod h q : ℝ) / (q : ℝ) ^ m ≤ d / q := by
  have : Fact q.Prime := ⟨hq⟩
  have hdeg : (map (Int.castRingHom (ZMod q)) h).totalDegree ≤ d :=
    le_trans (Finset.sup_mono (support_map_subset (Int.castRingHom (ZMod q)) h)) hd
  have key := schwartz_zippel_totalDegree hne (Finset.univ : Finset (ZMod q))
  have hcard : zeroCountMod h q =
      #{f ∈ Fintype.piFinset fun _ : Fin m => (Finset.univ : Finset (ZMod q)) |
        eval f (map (Int.castRingHom (ZMod q)) h) = 0} := by
    unfold zeroCountMod
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Fintype.piFinset_univ]
  rw [hcard]
  have key' : ((#{f ∈ Fintype.piFinset fun _ : Fin m => (Finset.univ : Finset (ZMod q)) |
        eval f (map (Int.castRingHom (ZMod q)) h) = 0} : ℕ) : ℝ) / (q : ℝ) ^ m ≤
      ((map (Int.castRingHom (ZMod q)) h).totalDegree : ℝ) / q := by
    have h2 := (NNRat.cast_le (K := ℝ)).2 key
    simp only [Finset.card_univ, ZMod.card] at h2
    push_cast at h2
    exact h2
  refine key'.trans ?_
  gcongr

/-- The primes of `P` (all `≥ q_min ≥ 2`) that divide every coefficient of a nonzero integer
polynomial whose coefficients are bounded by `M` number at most `log_{q_min} M`. -/
theorem card_filter_map_eq_zero_le_log {h : MvPolynomial (Fin m) ℤ} (hh : h ≠ 0) {M qmin : ℕ}
    (hM : ∀ s, (h.coeff s).natAbs ≤ M) {P : Finset ℕ} (hP : ∀ q ∈ P, q.Prime) (hq2 : 2 ≤ qmin)
    (hqmin : ∀ q ∈ P, qmin ≤ q) :
    #{q ∈ P | map (Int.castRingHom (ZMod q)) h = 0} ≤ Nat.log qmin M := by
  obtain ⟨s, hs⟩ := ne_zero_iff.1 hh
  set B := P.filter fun q => map (Int.castRingHom (ZMod q)) h = 0 with hB
  have hdvd : ∀ q ∈ B, q ∣ (h.coeff s).natAbs := by
    intro q hq
    have hq' := (mem_filter.1 hq).2
    have hc : ((h.coeff s : ℤ) : ZMod q) = 0 := by
      have := congrArg (fun p : MvPolynomial (Fin m) (ZMod q) => p.coeff s) hq'
      simpa [coeff_map] using this
    exact Int.natCast_dvd.1 ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hc)
  have hprod : ∏ q ∈ B, q ∣ (h.coeff s).natAbs :=
    Finset.prod_primes_dvd _ (fun q hq => (hP q (mem_filter.1 hq).1).prime) hdvd
  have hpos : 0 < (h.coeff s).natAbs := Int.natAbs_pos.2 hs
  have hle : ∏ q ∈ B, q ≤ M := (Nat.le_of_dvd hpos hprod).trans (hM s)
  have hpow : qmin ^ #B ≤ ∏ q ∈ B, q := by
    calc qmin ^ #B = ∏ _q ∈ B, qmin := by simp
      _ ≤ ∏ q ∈ B, q := Finset.prod_le_prod fun q hq => hqmin q (mem_filter.1 hq).1
  exact Nat.le_log_of_pow_le (by omega) (hpow.trans hle)

/-- **Fingerprinting.** Let `h ∈ ℤ[X₁, …, Xₘ]` be nonzero with total degree `≤ d` and all
coefficients of absolute value `≤ M`. For a nonempty set `P` of primes, all `≥ q_min ≥ 2`, a
uniform `q ∈ P` and a uniform `α ∈ 𝔽_qᵐ`,
`Pr[(h mod q)(α) = 0] ≤ log_{q_min} M / |P| + d / q_min`. -/
theorem avg_zeroCountMod_div_le {h : MvPolynomial (Fin m) ℤ} (hh : h ≠ 0) {d M qmin : ℕ}
    (hd : h.totalDegree ≤ d) (hM : ∀ s, (h.coeff s).natAbs ≤ M) {P : Finset ℕ}
    (hP : ∀ q ∈ P, q.Prime) (hPne : P.Nonempty) (hq2 : 2 ≤ qmin) (hqmin : ∀ q ∈ P, qmin ≤ q) :
    (∑ q ∈ P, (zeroCountMod h q : ℝ) / (q : ℝ) ^ m) / #P ≤
      (Nat.log qmin M : ℝ) / #P + (d : ℝ) / qmin := by
  have hPpos : (0 : ℝ) < #P := by exact_mod_cast hPne.card_pos
  have hqpos : (0 : ℝ) < qmin := by exact_mod_cast (by omega : 0 < qmin)
  set B := P.filter fun q => map (Int.castRingHom (ZMod q)) h = 0 with hB
  have hterm : ∀ q ∈ P, (zeroCountMod h q : ℝ) / (q : ℝ) ^ m ≤
      (if q ∈ B then 1 else 0) + (d : ℝ) / qmin := by
    intro q hq
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (hP q hq).ne_zero
    have hdq : (d : ℝ) / q ≤ (d : ℝ) / qmin := by
      gcongr
      exact_mod_cast hqmin q hq
    by_cases hqB : q ∈ B
    · rw [zeroCountMod_eq_of_map_eq_zero (hP q hq).ne_zero (mem_filter.1 hqB).2]
      simp only [hqB, ↓reduceIte]
      push_cast
      rw [div_self (pow_ne_zero _ hq0)]
      have : (0 : ℝ) ≤ (d : ℝ) / qmin := by positivity
      linarith
    · simp only [hqB, ↓reduceIte, zero_add]
      have hne : map (Int.castRingHom (ZMod q)) h ≠ 0 := fun h0 => hqB (mem_filter.2 ⟨hq, h0⟩)
      exact (zeroCountMod_div_le (hP q hq) hne hd).trans hdq
  have hsum : ∑ q ∈ P, (zeroCountMod h q : ℝ) / (q : ℝ) ^ m ≤ #B + #P * ((d : ℝ) / qmin) := by
    calc ∑ q ∈ P, (zeroCountMod h q : ℝ) / (q : ℝ) ^ m
        ≤ ∑ q ∈ P, ((if q ∈ B then 1 else 0) + (d : ℝ) / qmin) := sum_le_sum hterm
      _ = #B + #P * ((d : ℝ) / qmin) := by
          have hfilter : P.filter (· ∈ B) = B := by
            ext q
            simp only [mem_filter]
            exact ⟨fun hq => hq.2, fun hq => ⟨(mem_filter.1 hq).1, hq⟩⟩
          rw [sum_add_distrib, sum_boole, hfilter, sum_const, nsmul_eq_mul]
  have hBle : (#B : ℝ) ≤ Nat.log qmin M := by
    exact_mod_cast card_filter_map_eq_zero_le_log hh hM hP hq2 hqmin
  rw [div_le_iff₀ hPpos]
  calc ∑ q ∈ P, (zeroCountMod h q : ℝ) / (q : ℝ) ^ m
      ≤ #B + #P * ((d : ℝ) / qmin) := hsum
    _ ≤ Nat.log qmin M + #P * ((d : ℝ) / qmin) := by linarith
    _ = ((Nat.log qmin M : ℝ) / #P + (d : ℝ) / qmin) * #P := by
        field_simp

/-- The prime-divisor term in the form of [BGKLSW26]: `log₂ M / (⌊log₂ q_min⌋ · |P|)`. -/
theorem avg_zeroCountMod_div_le_logb {h : MvPolynomial (Fin m) ℤ} (hh : h ≠ 0) {d M qmin : ℕ}
    (hd : h.totalDegree ≤ d) (hM : ∀ s, (h.coeff s).natAbs ≤ M) (hM1 : 1 ≤ M) {P : Finset ℕ}
    (hP : ∀ q ∈ P, q.Prime) (hPne : P.Nonempty) (hq2 : 2 ≤ qmin) (hqmin : ∀ q ∈ P, qmin ≤ q) :
    (∑ q ∈ P, (zeroCountMod h q : ℝ) / (q : ℝ) ^ m) / #P ≤
      Real.logb 2 M / (Nat.log 2 qmin * #P) + (d : ℝ) / qmin := by
  refine (avg_zeroCountMod_div_le hh hd hM hP hPne hq2 hqmin).trans ?_
  have hPpos : (0 : ℝ) < #P := by exact_mod_cast hPne.card_pos
  have hlog1 : 1 ≤ Nat.log 2 qmin := Nat.log_pos (by norm_num) hq2
  have hlogpos : (0 : ℝ) < Nat.log 2 qmin := by exact_mod_cast hlog1
  have hnat : (Nat.log qmin M : ℝ) ≤ Real.logb 2 M / Nat.log 2 qmin := by
    have h1 : (Nat.log qmin M : ℝ) ≤ Real.logb qmin M := Real.natLog_le_logb _ _
    have h2 : (Nat.log 2 qmin : ℝ) ≤ Real.logb 2 qmin := Real.natLog_le_logb _ _
    have hMpos : (0 : ℝ) < M := by exact_mod_cast hM1
    have hlogq : (0 : ℝ) < Real.logb 2 qmin :=
      Real.logb_pos (by norm_num) (by exact_mod_cast hq2)
    have hlogM : 0 ≤ Real.logb 2 M := Real.logb_nonneg (by norm_num) (by exact_mod_cast hM1)
    have h3 : Real.logb qmin M = Real.logb 2 M / Real.logb 2 qmin := by
      rw [Real.logb, Real.logb, Real.logb, div_div_div_cancel_right₀]
      exact (Real.log_pos (by norm_num)).ne'
    rw [h3] at h1
    exact h1.trans (div_le_div_of_nonneg_left hlogM hlogpos h2)
  have : (Nat.log qmin M : ℝ) / #P ≤ Real.logb 2 M / (Nat.log 2 qmin * #P) := by
    rw [← div_div]
    gcongr
  linarith

end MvPolynomial
