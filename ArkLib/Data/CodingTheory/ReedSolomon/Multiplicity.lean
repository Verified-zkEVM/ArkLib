/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon
public import ArkLib.ToMathlib.Polynomial.RootMultiplicity
public import Mathlib.Algebra.CharP.Lemmas
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Taylor
public import Mathlib.Data.Nat.Factorial.NatCast

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
* `ReedSolomon.Multiplicity.hammingDist_umCode_ge`, `ReedSolomon.Multiplicity.dist_umCode_eq` —
  distinct codewords differ on at least `|ι| - (k - 1) / s` positions, with equality for the
  minimum distance below saturation.

## The derivative is the ordinary one

The derivatives here are iterates of the ordinary formal derivative `Polynomial.derivative`,
not Hasse derivatives. Correspondingly, the results above assume `ringChar F = 0` or
`k ≤ ringChar F`, phrased as a disjunction so that characteristic zero is not excluded by
`ringChar F = 0` forcing `k = 0`.

That hypothesis is what makes the two agree up to the units `j !`. Dropping it can cause
information loss: in characteristic `p`, on the singleton domain `{0}` with `k = s = p + 1`,
the messages `X ^ p` and `0` have the same value and all ordinary derivatives at `0`. The
boundary `k = p` is covered by the hypothesis, since `X ^ p` is outside the message space.
A small-characteristic variant should be a separate definition built on
`Polynomial.hasseDeriv`, not a substitution here.

## References

* [Guruswami, V., and Wang, C., *Linear-Algebraic List Decoding for Variants of
    Reed-Solomon Codes*][GW13]
* [Kopparty, S., Saraf, S., and Yekhanin, S., *High-rate codes with sublinear-time
    decoding*][KSY14]
* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
    Agreement*][ABF26]
-/

@[expose] public section
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
      · let : CharZero F := (CharP.ringChar_zero_iff_CharZero F).mp hchar0
        exact IsUnit.natCast_factorial_of_algebra F d
      · let : NeZero (ringChar F) :=
          ⟨Nat.ne_zero_of_lt ((Nat.zero_le d).trans_lt (hdk.trans_le hcharpos))⟩
        let : Fact (Nat.Prime (ringChar F)) := CharP.char_is_prime_of_pos F _
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
    · have : NeZero k := ⟨by omega⟩
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

/-- Two distinct codewords of a univariate multiplicity code differ on at least
`n - (k - 1) / s` positions: each position where they agree is a root of multiplicity `s` of
the difference of their messages, whose degree is below `k`. -/
theorem hammingDist_umCode_ge {ι : Type*} [Fintype ι] [DecidableEq F]
    (domain : ι ↪ F) {k s : ℕ} (hchar : ringChar F = 0 ∨ k ≤ ringChar F)
    {c c' : ι → Fin s → F} (hc : c ∈ umCode domain k s) (hc' : c' ∈ umCode domain k s)
    (hne : c ≠ c') :
    Fintype.card ι - (k - 1) / s ≤ hammingDist c c' := by
  classical
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hc
  obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hc'
  have hr : p - q ∈ Polynomial.degreeLT F k := sub_mem hp hq
  have hr0 : p - q ≠ 0 := fun h ↦ hne (by rw [sub_eq_zero.mp h])
  have hrdeg : (p - q).natDegree < k :=
    (Polynomial.natDegree_lt_iff_degree_lt hr0).mpr (Polynomial.mem_degreeLT.mp hr)
  let A : Finset ι := Finset.univ.filter
    fun i ↦ umEvalOnPoints domain s p i = umEvalOnPoints domain s q i
  have hmult : ∀ i ∈ A, s ≤ (p - q).rootMultiplicity (domain i) := by
    intro i hi
    refine (Polynomial.le_rootMultiplicity_iff hr0).mpr ?_
    refine pow_dvd_of_eval_iterate_derivative_eq_zero hr hchar fun j ↦ ?_
    have hagree := congrFun (Finset.mem_filter.mp hi).2 j
    change (Polynomial.derivative^[j.val] p).eval (domain i) =
      (Polynomial.derivative^[j.val] q).eval (domain i) at hagree
    rw [Polynomial.iterate_derivative_sub, Polynomial.eval_sub, hagree, sub_self]
  have hsum : A.card * s ≤ (p - q).natDegree := by
    calc A.card * s = ∑ _i ∈ A, s := by simp
      _ ≤ ∑ i ∈ A, (p - q).rootMultiplicity (domain i) := Finset.sum_le_sum hmult
      _ = ∑ a ∈ A.map domain, (p - q).rootMultiplicity a := by rw [Finset.sum_map]
      _ ≤ (p - q).natDegree := Polynomial.sum_rootMultiplicity_le_natDegree _
  have hA : A.card ≤ (k - 1) / s := by
    have hs : 0 < s := by
      by_contra h
      obtain rfl := Nat.eq_zero_of_not_pos h
      exact hne (Subsingleton.elim _ _)
    exact (Nat.le_div_iff_mul_le hs).mpr (by omega)
  have hsplit : hammingDist (umEvalOnPoints domain s p) (umEvalOnPoints domain s q) + A.card =
      Fintype.card ι := by
    rw [hammingDist, add_comm]
    exact Finset.card_filter_add_card_filter_not _
  omega

/-- A codeword attaining the distance bound: the evaluations of the product of `(X - a) ^ s`
over `(k - 1) / s` domain points, which vanishes to order `s` on exactly those points. This
direction needs no assumption on the characteristic. -/
lemma exists_mem_umCode_hammingDist_zero_eq {ι : Type*} [Fintype ι] [DecidableEq F]
    (domain : ι ↪ F) {k s : ℕ} (hk : 0 < k) (hks : k ≤ s * Fintype.card ι) :
    ∃ c ∈ umCode domain k s, c ≠ 0 ∧
      hammingDist c (0 : ι → Fin s → F) = Fintype.card ι - (k - 1) / s := by
  classical
  have hm : (k - 1) / s < Fintype.card ι := Nat.div_lt_of_lt_mul (by omega)
  obtain ⟨T, -, hT⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset ι)) (n := (k - 1) / s) (by simpa using hm.le)
  let P : Polynomial F := ∏ i ∈ T, (Polynomial.X - Polynomial.C (domain i)) ^ s
  have hPdeg : P.natDegree = (k - 1) / s * s := by
    rw [Polynomial.natDegree_prod_of_monic _ _
      fun i _ ↦ (Polynomial.monic_X_sub_C (domain i)).pow s]
    simp [hT]
  have hP : P ∈ Polynomial.degreeLT F k := by
    refine Polynomial.mem_degreeLT.mpr
      (lt_of_le_of_lt Polynomial.degree_le_natDegree (Nat.cast_lt.mpr ?_))
    have := Nat.div_mul_le_self (k - 1) s
    omega
  have hzero : ∀ i ∈ T, umEvalOnPoints domain s P i = 0 := by
    intro i hi
    ext j
    have hdvd : (Polynomial.X - Polynomial.C (domain i)) ^ s ∣ P := Finset.dvd_prod_of_mem _ hi
    obtain ⟨g, hg⟩ := Polynomial.pow_sub_dvd_iterate_derivative_of_pow_dvd j.val hdvd
    change (Polynomial.derivative^[j.val] P).eval (domain i) = 0
    rw [hg, Polynomial.eval_mul, Polynomial.eval_pow]
    simp [Nat.sub_ne_zero_of_lt j.isLt]
  have hne : ∀ i ∉ T, umEvalOnPoints domain s P i ≠ 0 := by
    intro i hi h0
    have hs : 0 < s := by
      by_contra h
      have hs0 : s = 0 := Nat.eq_zero_of_not_pos h
      simp [hs0] at hks
      omega
    have h := congrFun h0 ⟨0, hs⟩
    change P.eval (domain i) = 0 at h
    rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h
    obtain ⟨t, ht, h⟩ := h
    have hti : t ≠ i := fun e ↦ hi (e ▸ ht)
    simp only [Polynomial.eval_pow, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
      pow_eq_zero_iff hs.ne'] at h
    exact hti (domain.injective (sub_eq_zero.mp h)).symm
  have hdist : hammingDist (umEvalOnPoints domain s P) (0 : ι → Fin s → F) =
      Fintype.card ι - (k - 1) / s := by
    have hfilter : (Finset.univ.filter
        fun i ↦ umEvalOnPoints domain s P i ≠ (0 : ι → Fin s → F) i) = Tᶜ := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl, Pi.zero_apply]
      exact ⟨fun h hi ↦ h (hzero i hi), hne i⟩
    rw [hammingDist, hfilter, Finset.card_compl, hT]
  refine ⟨_, Submodule.mem_map_of_mem hP, ?_, hdist⟩
  intro h0
  rw [h0, hammingDist_self] at hdist
  omega

/-- The minimum distance of a univariate multiplicity code in the unsaturated range. -/
theorem dist_umCode_eq {ι : Type*} [Fintype ι] [DecidableEq F]
    (domain : ι ↪ F) {k s : ℕ} (hchar : ringChar F = 0 ∨ k ≤ ringChar F)
    (hk : 0 < k) (hks : k ≤ s * Fintype.card ι) :
    Code.dist (umCode domain k s : Set (ι → Fin s → F)) = Fintype.card ι - (k - 1) / s := by
  obtain ⟨c, hc, hc0, hcd⟩ := exists_mem_umCode_hammingDist_zero_eq domain hk hks
  have hmem : Fintype.card ι - (k - 1) / s ∈ {d | ∃ u ∈ (umCode domain k s : Set _), ∃ v ∈
      (umCode domain k s : Set (ι → Fin s → F)), u ≠ v ∧ hammingDist u v ≤ d} :=
    ⟨c, hc, 0, Submodule.zero_mem _, hc0, hcd.le⟩
  refine le_antisymm (Nat.sInf_le hmem) (le_csInf ⟨_, hmem⟩ ?_)
  rintro d ⟨u, hu, v, hv, huv, hd⟩
  exact (hammingDist_umCode_ge domain hchar hu hv huv).trans hd

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
