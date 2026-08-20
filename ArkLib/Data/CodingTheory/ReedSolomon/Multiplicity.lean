/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.ToMathlib.Polynomial.RootMultiplicity
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Nat.Factorial.NatCast

/-!
# Univariate multiplicity codes

The univariate multiplicity code packs the evaluations of a polynomial of degree `< k`
*and of its first `s - 1` formal derivatives* at each domain point into a single symbol of
the alphabet `Fin s → F`:

  `umCode domain k s = { f | ∃ p, deg p < k ∧ ∀ x j, f x j = (derivative^[j] p).eval (domain x) }` .

At `s = 1` it is the plain Reed-Solomon code (`mem_umCode_one_iff_mem_rsCode`).

## Main definitions

* `ReedSolomon.Multiplicity.umEvalOnPoints` — the encoder, as an `F`-linear map.
* `ReedSolomon.Multiplicity.umCode` — the code, as an `F`-submodule of `ι → Fin s → F`.

## Main statements

* `ReedSolomon.Multiplicity.pow_dvd_of_eval_iterate_derivative_eq_zero` — vanishing of the
  first `s` derivatives at a point gives a root of multiplicity `s` there.
* `ReedSolomon.Multiplicity.umEvalOnPoints_domRestrict_injective` — the encoder is injective
  on `Polynomial.degreeLT F k`.
* `ReedSolomon.Multiplicity.dim_umCode_eq_min`, `ReedSolomon.Multiplicity.dim_umCode` — the
  dimension is `min k (s * |ι|)`, hence `k` below saturation.

## The derivative is the ordinary one

The derivatives here are iterates of the ordinary formal derivative `Polynomial.derivative`,
not Hasse derivatives. Correspondingly, the results above assume `ringChar F = 0` or
`k ≤ ringChar F`, phrased as a disjunction so that characteristic zero is not excluded by
`ringChar F = 0` forcing `k = 0`.

That hypothesis is what makes the two agree up to the units `j !`, and it cannot be dropped:
in characteristic `p ≤ k` one has `derivative^[p] (X ^ p) = 0`, so the encoder loses
information and the dimension statement fails. A small-characteristic variant should
therefore be a separate definition built on `Polynomial.hasseDeriv`, not a substitution
here.

## References

* [Guruswami, V., and Wang, C., *Linear-Algebraic List Decoding for Variants of
    Reed-Solomon Codes*][GW13]
* [Kopparty, S., Saraf, S., and Yekhanin, S., *High-rate codes with sublinear-time
    decoding*][KSY14]
* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
    Agreement*][ABF26]
-/
namespace ReedSolomon

namespace Multiplicity

variable {ι : Type*}
variable {F : Type*}

section CommSemiring

variable [CommSemiring F]

/-- The multiplicity-code evaluation map, sending a polynomial `p` to the matrix
`(derivative^[j] p).eval (domain x)` indexed by `x : ι` and `j : Fin s`.

It is `F`-linear because iterated `Polynomial.derivative` and `Polynomial.eval` both are. -/
noncomputable def umEvalOnPoints (domain : ι ↪ F) (s : ℕ) :
    Polynomial F →ₗ[F] (ι → Fin s → F) where
  toFun p := fun x j ↦ (Polynomial.derivative^[j.val] p).eval (domain x)
  map_add' p q := by
    ext x j
    simp [Polynomial.eval_add]
  map_smul' c p := by
    ext x j
    simp [Polynomial.eval_smul]

/-- The univariate multiplicity code: the image of `Polynomial.degreeLT F k` under
`umEvalOnPoints`, an `F`-submodule of `ι → Fin s → F`. -/
noncomputable def umCode (domain : ι ↪ F) (k s : ℕ) :
    Submodule F (ι → Fin s → F) :=
  (Polynomial.degreeLT F k).map (umEvalOnPoints domain s)

end CommSemiring

section Field

variable [Field F]

/-- If the first `s` ordinary derivatives of a polynomial of degree `< k` vanish at `a`,
then `a` is a root of multiplicity at least `s`, provided `F` has characteristic zero or
characteristic at least `k`.

The characteristic hypothesis is what makes the ordinary and Hasse derivatives differ by a
unit `j !` throughout the relevant degree range; Mathlib's root-multiplicity criterion is
stated for the latter. -/
lemma pow_dvd_of_eval_iterate_derivative_eq_zero
    {p : Polynomial F} {a : F} {s k : ℕ}
    (hp : p ∈ Polynomial.degreeLT F k) (hchar : ringChar F = 0 ∨ k ≤ ringChar F)
    (hzero : ∀ j : Fin s, (Polynomial.derivative^[j.val] p).eval a = 0) :
    (Polynomial.X - Polynomial.C a) ^ s ∣ p := by
  rw [Polynomial.X_sub_C_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
  intro d hd
  change (Polynomial.taylor a p).coeff d = 0
  rw [Polynomial.taylor_coeff]
  by_cases hdk : d < k
  · have hfac : IsUnit (d.factorial : F) := by
      rcases hchar with hchar0 | hcharpos
      · letI : CharZero F := (CharP.ringChar_zero_iff_CharZero F).mp hchar0
        exact IsUnit.natCast_factorial_of_algebra F d
      · letI : NeZero (ringChar F) :=
          ⟨Nat.ne_zero_of_lt ((Nat.zero_le d).trans_lt (hdk.trans_le hcharpos))⟩
        letI : Fact (Nat.Prime (ringChar F)) := CharP.char_is_prime_of_pos F _
        exact (IsUnit.natCast_factorial_iff_of_charP (ringChar F)).2 (hdk.trans_le hcharpos)
    have hder := hzero ⟨d, hd⟩
    change (Polynomial.derivative^[d] p).eval a = 0 at hder
    have hscale := congrFun (Polynomial.factorial_smul_hasseDeriv (R := F) d) p
    rw [← hscale] at hder
    simp only [LinearMap.smul_apply, Polynomial.eval_smul] at hder
    rw [nsmul_eq_mul] at hder
    exact (mul_eq_zero.mp hder).resolve_left hfac.ne_zero
  · by_cases hp0 : p = 0
    · simp [hp0]
    · have hpdeg : p.degree < (k : WithBot ℕ) := Polynomial.mem_degreeLT.mp hp
      have hdeg : p.natDegree < k :=
        (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hpdeg
      rw [Polynomial.hasseDeriv_eq_zero_of_lt_natDegree p d (hdeg.trans_le (not_lt.mp hdk))]
      simp

/-- The univariate-multiplicity encoder is injective on degree-`< k` polynomials whenever
the message dimension does not exceed the `s · n` scalar coordinates and the characteristic
is either zero or at least `k`. -/
lemma umEvalOnPoints_domRestrict_injective
    {ι : Type*} [Fintype ι] {k s : ℕ}
    (domain : ι ↪ F) (hchar : ringChar F = 0 ∨ k ≤ ringChar F)
    (hk : k ≤ s * Fintype.card ι) :
    Function.Injective
      ((umEvalOnPoints domain s).domRestrict (Polynomial.degreeLT F k)) := by
  classical
  rw [← LinearMap.ker_eq_bot]
  ext p
  simp only [LinearMap.mem_ker, LinearMap.domRestrict_apply, Submodule.mem_bot]
  constructor
  · intro hfp
    apply Subtype.ext
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · have hdeg := Polynomial.mem_degreeLT.mp p.2
      rw [Nat.cast_zero, Nat.WithBot.lt_zero_iff, Polynomial.degree_eq_bot] at hdeg
      exact hdeg
    · haveI : NeZero k := ⟨by omega⟩
      by_contra hp0
      have hpow : ∀ i : ι,
          (Polynomial.X - Polynomial.C (domain i)) ^ s ∣ p.val := by
        intro i
        apply pow_dvd_of_eval_iterate_derivative_eq_zero p.2 hchar
        intro j
        exact congrFun (congrFun hfp i) j
      have hmult : ∀ i : ι, s ≤ p.val.rootMultiplicity (domain i) := by
        intro i
        exact (Polynomial.le_rootMultiplicity_iff hp0).mpr (hpow i)
      have hsumlow : Fintype.card ι * s ≤
          ∑ a ∈ Finset.univ.map domain, p.val.rootMultiplicity a := by
        rw [Finset.sum_map]
        simpa [Finset.sum_const, nsmul_eq_mul] using
          (Finset.sum_le_sum fun i (_hi : i ∈ (Finset.univ : Finset ι)) => hmult i)
      have hsumhigh := Polynomial.sum_rootMultiplicity_le_natDegree
        (W := p.val) (Finset.univ.map domain)
      have hpdeg := ReedSolomon.natDegree_lt_of_mem_degreeLT p.2
      rw [Nat.mul_comm] at hk
      omega
  · intro hp
    simp [hp]

/-- Monotonicity of univariate multiplicity codes in their message-degree parameter. -/
lemma umCode_mono {ι : Type*} {k l s : ℕ} (hkl : k ≤ l) (domain : ι ↪ F) :
    umCode domain k s ≤ umCode domain l s :=
  Submodule.map_mono (Polynomial.degreeLT_mono hkl)

/-- In the unsaturated range `k ≤ s · n`, a univariate multiplicity code has dimension
exactly `k`. -/
lemma dim_umCode {ι : Type*} [Fintype ι] {k s : ℕ}
    (domain : ι ↪ F) (hchar : ringChar F = 0 ∨ k ≤ ringChar F)
    (hk : k ≤ s * Fintype.card ι) :
    Module.finrank F (umCode domain k s) = k := by
  rw [umCode]
  have hrange : (Polynomial.degreeLT F k).map (umEvalOnPoints domain s) =
      LinearMap.range ((umEvalOnPoints domain s).domRestrict (Polynomial.degreeLT F k)) := by
    ext x
    simp [Submodule.mem_map]
  rw [hrange, LinearMap.finrank_range_of_inj
    (umEvalOnPoints_domRestrict_injective domain hchar hk), Polynomial.finrank_degreeLT_n]

/-- The exact dimension of a univariate multiplicity code, including saturation at the
ambient scalar dimension `s · n`. -/
lemma dim_umCode_eq_min {ι : Type*} [Fintype ι]
    (domain : ι ↪ F) (k s : ℕ) (hchar : ringChar F = 0 ∨ k ≤ ringChar F) :
    Module.finrank F (umCode domain k s) = min k (s * Fintype.card ι) := by
  classical
  by_cases hk : k ≤ s * Fintype.card ι
  · rw [dim_umCode domain hchar hk, min_eq_left hk]
  · have hnsk : s * Fintype.card ι ≤ k := by omega
    have hchar' : ringChar F = 0 ∨ s * Fintype.card ι ≤ ringChar F :=
      hchar.imp_right hnsk.trans
    have hdimsmall : Module.finrank F
        (umCode domain (s * Fintype.card ι) s) = s * Fintype.card ι :=
      dim_umCode domain hchar' le_rfl
    have hle := umCode_mono hnsk domain (s := s)
    have hdimle := Submodule.finrank_mono hle
    have hamb : Module.finrank F (ι → Fin s → F) = s * Fintype.card ι := by
      simp [Module.finrank_pi_fintype, Nat.mul_comm]
    have hdimhigh : Module.finrank F (umCode domain k s) = s * Fintype.card ι := by
      apply le_antisymm
      · rw [← hamb]
        exact Submodule.finrank_le _
      · rw [← hdimsmall]
        exact hdimle
    rw [hdimhigh, min_eq_right hnsk]

end Field

end Multiplicity

/-- At `s = 1` the multiplicity code collapses to the plain Reed-Solomon code: the only
index is `0 : Fin 1` and `Polynomial.derivative^[0]` is the identity. Stated as an
equivalence of memberships, the two codes living in the distinct types `ι → Fin 1 → F` and
`ι → F`. -/
lemma Multiplicity.mem_umCode_one_iff_mem_rsCode
    {ι : Type*} {F : Type*} [CommSemiring F]
    (domain : ι ↪ F) (k : ℕ) (f : ι → Fin 1 → F) :
    f ∈ Multiplicity.umCode domain k 1 ↔
      (fun i ↦ f i 0) ∈ ReedSolomon.code domain k :=
  ReedSolomon.mem_map_degreeLT_one_iff_mem_code domain k
    (Multiplicity.umEvalOnPoints domain 1)
    (fun p x => by simp [Multiplicity.umEvalOnPoints]) f

end ReedSolomon
