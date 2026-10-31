/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import ArkLib.Data.MvPolynomial.PrimeFingerprint
public import ArkLib.Data.Probability.Uniform

/-!
# The fingerprinting bound as a probability

`ArkLib/Data/MvPolynomial/PrimeFingerprint.lean` bounds the fraction of zeros of `h mod q` averaged
over the primes `q ∈ P`. The challenge of the fingerprinting step ([BGKLSW26, Lemma 4.3 and
Lemma 4.8]) is sampled in two stages: first a prime `q` uniform in `P`, then a point `α` uniform in
`𝔽_qᵐ`. This file states the bound for that sampler, so that the counting module stays independent
of VCVio.

The order of the stages matters. A uniform draw from the dependent type of *all* pairs `(q, α)`
weights each prime by the size of its field, and it differs from the two-stage draw as soon as the
fibres `𝔽_qᵐ` have different sizes (see the test).

## Main statements

* `MvPolynomial.modPointSample` is the sampler of a point of `𝔽_qᵐ`, for a prime `q ∈ P`;
* `MvPolynomial.prEvent_fingerprint_eq_average` identifies the probability that `h mod q` vanishes
  at the sampled point with the average of `MvPolynomial.zeroCountMod`;
* `MvPolynomial.prEvent_modPointSample_mono` compares two events of the two-stage sampler: if one
  implies the other at every prime and point, its probability is at most that of the other.
* `MvPolynomial.prEvent_fingerprint_le` is the bound of `MvPolynomial.avg_zeroCountMod_div_le` as a
  probability.

Paper-specific correspondence and remaining formalization work are recorded in the
[BitZ KB](https://github.com/Verified-zkEVM/ArkLib/blob/main/docs/kb/papers/BGKLSW26.md).

## References

* [Bloemen, R., Garreta, A., Kostrzewa, M., Londhe, S., Soukhanov, L., and Wu, J.,
    *BitZ: proofs and commitments in arbitrary rings through binary fields*][BGKLSW26]
-/

@[expose] public section

open Finset
open scoped BigOperators ProbabilityTheory

namespace MvPolynomial

/-- A uniform point of `𝔽_qᵐ`, for a prime `q ∈ P`. -/
def modPointSample {m : ℕ} {P : Finset ℕ} (hP : ∀ q ∈ P, q.Prime) (q : ↥P) :
    ProbComp (Fin m → ZMod q.val) := by
  let : NeZero q.val := ⟨(hP q.val q.property).ne_zero⟩
  exact $ᵗ (Fin m → ZMod q.val)

/-- For a prime `q ∈ P`, the probability that `h mod q` vanishes at a uniform point of `𝔽_qᵐ` is
the fraction of its zeros. -/
theorem prEvent_modPointSample {m : ℕ} (h : MvPolynomial (Fin m) ℤ) {P : Finset ℕ}
    (hP : ∀ q ∈ P, q.Prime) (q : ↥P) :
    Pr{let α ← modPointSample hP q}[
      eval α (MvPolynomial.map (Int.castRingHom (ZMod q.val)) h) = 0] =
      ENNReal.ofReal ((zeroCountMod h q.val : ℝ) / (q.val : ℝ) ^ m) := by
  classical
  let : NeZero q.val := ⟨(hP q.val q.property).ne_zero⟩
  rw [modPointSample, SampleableType.prEvent_uniformSample_eq_ofReal]
  congr 1
  simp [zeroCountMod, Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- **The two-stage sampler.** For `q` uniform in `P` and then `α` uniform in `𝔽_qᵐ`, the
probability that `h mod q` vanishes at `α` is the average of the fractions of zeros. -/
theorem prEvent_fingerprint_eq_average {m : ℕ} (h : MvPolynomial (Fin m) ℤ) {P : Finset ℕ}
    [SampleableType ↥P] (hP : ∀ q ∈ P, q.Prime) :
    Pr{let q ← $ᵗ ↥P; let α ← modPointSample hP q}[
      eval α (MvPolynomial.map (Int.castRingHom (ZMod q.val)) h) = 0] =
      ENNReal.ofReal (𝔼 q ∈ P, (zeroCountMod h q : ℝ) / (q : ℝ) ^ m) := by
  classical
  change Pr{let b ← ($ᵗ ↥P >>= fun q =>
    (fun α => eval α (MvPolynomial.map (Int.castRingHom (ZMod q.val)) h) = 0) <$>
      modPointSample hP q)}[b] = _
  have hsum := prEvent_bind_eq_sum_fintype ($ᵗ ↥P)
    (fun q => (fun α => eval α (MvPolynomial.map (Int.castRingHom (ZMod q.val)) h) = 0) <$>
      modPointSample hP q) id
  simp only [id_map] at hsum
  rw [hsum]
  simp only [SampleableType.prEvent_uniformSample_eq_singleton, prEvent_modPointSample]
  rw [Finset.expect_eq_sum_div_card]
  have hpos : (0 : ℝ) < #P := by
    exact_mod_cast (show 0 < #P by simpa only [Fintype.card_coe] using Fintype.card_pos (α := ↥P))
  rw [ENNReal.ofReal_div_of_pos hpos]
  rw [ENNReal.ofReal_sum_of_nonneg (by intros; positivity)]
  simp only [ENNReal.ofReal_natCast, Fintype.card_coe]
  rw [← Finset.mul_sum, mul_comm, ← div_eq_mul_inv]
  exact congrArg (fun x : ENNReal => x / #P)
    (Finset.sum_coe_sort P (fun q => ENNReal.ofReal ((zeroCountMod h q : ℝ) / (q : ℝ) ^ m)))

/-- **Monotonicity for the two-stage sampler.** If the event `p q α` implies `r q α` at every prime
`q ∈ P` and every point `α` of `𝔽_qᵐ`, then for `q` uniform in `P` and then `α` uniform in `𝔽_qᵐ`,
`p q α` is no more likely than `r q α`. -/
theorem prEvent_modPointSample_mono {m : ℕ} {P : Finset ℕ} [SampleableType ↥P]
    (hP : ∀ q ∈ P, q.Prime) (p r : (q : ↥P) → (Fin m → ZMod q.val) → Prop)
    (h : ∀ q α, p q α → r q α) :
    Pr{let q ← $ᵗ ↥P; let α ← modPointSample hP q}[p q α] ≤
      Pr{let q ← $ᵗ ↥P; let α ← modPointSample hP q}[r q α] := by
  classical
  change Pr{let b ← ($ᵗ ↥P >>= fun q => (fun α => p q α) <$> modPointSample hP q)}[b] ≤
    Pr{let b ← ($ᵗ ↥P >>= fun q => (fun α => r q α) <$> modPointSample hP q)}[b]
  have hp := prEvent_bind_eq_sum_fintype ($ᵗ ↥P)
    (fun q => (fun α => p q α) <$> modPointSample hP q) id
  have hr := prEvent_bind_eq_sum_fintype ($ᵗ ↥P)
    (fun q => (fun α => r q α) <$> modPointSample hP q) id
  simp only [id_map] at hp hr
  rw [hp, hr]
  refine Finset.sum_le_sum fun q _ => ?_
  gcongr
  exact prEvent_mono _ _ _ (h q)

/-- **Fingerprinting for the two-stage sampler.** Let `h ∈ ℤ[X₁, …, Xₘ]` be nonzero with total
degree `≤ d` and all coefficients of absolute value `≤ M`, and let `P` be a set of primes, all
`≥ q_min ≥ 2`. For `q` uniform in `P` and then `α` uniform in `𝔽_qᵐ`, the probability that `h mod q`
vanishes at `α` is at most `⌊log_{q_min} M⌋ / |P| + d / q_min`. -/
theorem prEvent_fingerprint_le {m : ℕ} {h : MvPolynomial (Fin m) ℤ} (hh : h ≠ 0)
    {d M qmin : ℕ} (hd : h.totalDegree ≤ d) (hM : ∀ s, (h.coeff s).natAbs ≤ M)
    {P : Finset ℕ} [SampleableType ↥P] (hP : ∀ q ∈ P, q.Prime)
    (hq2 : 2 ≤ qmin) (hqmin : ∀ q ∈ P, qmin ≤ q) :
    Pr{let q ← $ᵗ ↥P; let α ← modPointSample hP q}[
      eval α (MvPolynomial.map (Int.castRingHom (ZMod q.val)) h) = 0] ≤
      ENNReal.ofReal ((Nat.log qmin M : ℝ) / #P + (d : ℝ) / qmin) := by
  rw [prEvent_fingerprint_eq_average]
  exact ENNReal.ofReal_le_ofReal (avg_zeroCountMod_div_le hh hd hM hP hq2 hqmin)

end MvPolynomial
