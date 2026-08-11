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
# Univariate multiplicity codes (ABF26 Definition A.7)

The univariate multiplicity code packs the evaluations of a polynomial
**and its first `s − 1` formal derivatives** at each domain point into
a length-`s` symbol, mirroring how folded Reed-Solomon codes pack
`s` consecutive evaluations on a multiplicative orbit. Originally
introduced in [GW13] and analysed in detail in [KSY14]; ABF26 §A.2
records the definition in the context of the toy-problem
parametrisations.

## Which derivative? — ordinary, *not* Hasse

**ABF26 Definition A.6 defines `f̂^{(j)}` by iterating the ORDINARY formal derivative**
`f̂'(X) = ∑_{i=1}^{k-1} (a_i · i) · X^{i-1}`, i.e. `Polynomial.derivative^[j]`, and pairs
that with the global side condition `char(F) ≥ k` (see "Characteristic condition" below).
It does **not** use the Hasse (divided) derivative `f̂^{(j)}/j!`. So
`Polynomial.derivative^[j.val]` in `umEvalOnPoints` is a faithful transcription, and
`Mathlib.Polynomial.hasseDeriv` is deliberately **not** used here.

This is worth stating explicitly because in small characteristic the two differ and the
ordinary iterate is the *wrong* choice: over `char(F) = p ≤ k` one has
`derivative^[p] (X^p) = 0`, the encoder loses information, and the multiplicity-code
dimension claim collapses — which is exactly why ABF26 imposes `char(F) ≥ k` rather than
switching derivatives. A future small-characteristic variant of these codes therefore
needs `Polynomial.hasseDeriv j` (whose coefficients are the binomial `C(i, j)`, integral
and generically nonzero mod `p`) as a **separate definition**, not as a "fix" to this one:
replacing `derivative^[j]` by `hasseDeriv j` here would silently change which paper
statement is being formalised (the codes agree only up to the units `j!`, which are units
precisely when `char(F) > s − 1`).

## Notation

For `f̂ ∈ F^{<k}[X]`, write `f̂^(j)` for the `j`-th ordinary formal derivative.
Then

  `UM[F, L, k, s] := { f : L → F^s | ∃ f̂ ∈ F^{<k}[X],`
  `                     ∀ x ∈ L, f(x) = (f̂^{(0)}(x), …, f̂^{(s-1)}(x)) }`.

For `s = 1`, this degenerates to the plain Reed-Solomon code
`RS[F, L, k]` (see `mem_umCode_one_iff_mem_rsCode`).

**Characteristic condition.** For `s ≥ 2`, the paper's A.7 requires
`char(F) ≥ k` so that the derivative-of-monomial coefficients
`(a_i · i)` do not vanish below degree `k` (without this, multiple
distinct polynomials of degree `< k` can fold to the same multiplicity
codeword, and the dimension claim collapses). The bare encoder
`umEvalOnPoints` is well-typed in any `CommSemiring F` — we keep the
hypothesis as a downstream caller's responsibility rather than baking
it into the definition, since the `s = 1` collapse lemma below works
unconditionally.

## Layout

* `umEvalOnPoints` — the encoder, as an `F`-linear map from polynomials
  to multiplicity codewords.
* `umCode` — the multiplicity code as an `F`-submodule of `ι → Fin s → F`.

Sanity lemmas:

* `mem_umCode_one_iff_mem_rsCode` — `UM[F, L, k, 1]` collapses to
  `RS[F, L, k]` (modulo the `Fin 1 → F` ≃ `F` reshaping). This is a
  one-line corollary of the encoder-generic
  `ReedSolomon.mem_map_degreeLT_one_iff_mem_code` (in `ReedSolomon.lean`),
  which this file shares with `ReedSolomon.Folded`.

## References

* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
    Agreement*][ABF26] (§A.2: Definitions A.6, A.7)
* [Guruswami, V., and Wang, C., *Linear-Algebraic List Decoding for Variants of
    Reed-Solomon Codes*][GW13]
* [Kopparty, S., Saraf, S., and Yekhanin, S., *High-rate codes with sublinear-time
    decoding*][KSY14]
-/

namespace ReedSolomon

namespace Multiplicity

variable {ι : Type*}
variable {F : Type*}

section CommSemiring

variable [CommSemiring F]

/-- The univariate multiplicity-code evaluation map: send a polynomial
`p` to the matrix `(p^{(j)}(domain x))_{x ∈ ι, j ∈ Fin s}` packaging the
first `s` formal derivatives of `p` evaluated on the domain.

`F`-linear by construction: each entry is `c ↦ (derivative^[j] c).eval (domain x)`,
and both `Polynomial.derivative` (iterated) and `Polynomial.eval ·` are
`F`-linear (the latter as a function of the polynomial).

Mirrors `ReedSolomon.evalOnPoints` (the `s = 1` case) and the FRS encoder
`ReedSolomon.Folded.frsEvalOnPoints`. -/
noncomputable def umEvalOnPoints (domain : ι ↪ F) (s : ℕ) :
    Polynomial F →ₗ[F] (ι → Fin s → F) where
  toFun p := fun x j ↦ (Polynomial.derivative^[j.val] p).eval (domain x)
  map_add' p q := by
    ext x j
    simp [Polynomial.eval_add]
  map_smul' c p := by
    ext x j
    simp [Polynomial.eval_smul]

/-- **ABF26 Definition A.7 [GW13, KSY14]** — the univariate multiplicity
code `UM[F, L, k, s]`.

Defined as the image of `Polynomial.degreeLT F k` under
`umEvalOnPoints`, exactly mirroring the structure of `ReedSolomon.code`
and `ReedSolomon.Folded.frsCode`. This makes `umCode` an
`F`-submodule of `ι → Fin s → F`. -/
noncomputable def umCode (domain : ι ↪ F) (k s : ℕ) :
    Submodule F (ι → Fin s → F) :=
  (Polynomial.degreeLT F k).map (umEvalOnPoints domain s)

end CommSemiring

section Field

variable [Field F]

/-- If the first `s` ordinary derivatives of a degree-`< k` polynomial vanish at `a`,
then `a` is a root of multiplicity at least `s`, provided `k ≤ ringChar F`.

Mathlib states the root-multiplicity criterion using Hasse derivatives. Ordinary and Hasse
derivatives differ by the unit `j!` throughout the degree range in question, which is
exactly where the characteristic hypothesis is used. -/
lemma pow_dvd_of_eval_iterate_derivative_eq_zero
    {p : Polynomial F} {a : F} {s k : ℕ}
    (hp : p ∈ Polynomial.degreeLT F k) (hchar : k ≤ ringChar F)
    (hzero : ∀ j : Fin s, (Polynomial.derivative^[j.val] p).eval a = 0) :
    (Polynomial.X - Polynomial.C a) ^ s ∣ p := by
  rw [Polynomial.X_sub_C_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
  intro d hd
  change (Polynomial.taylor a p).coeff d = 0
  rw [Polynomial.taylor_coeff]
  by_cases hdk : d < k
  · letI : NeZero (ringChar F) :=
      ⟨Nat.ne_zero_of_lt ((Nat.zero_le d).trans_lt (hdk.trans_le hchar))⟩
    letI : Fact (Nat.Prime (ringChar F)) := CharP.char_is_prime_of_pos F _
    have hfac : IsUnit (d.factorial : F) :=
      (IsUnit.natCast_factorial_iff_of_charP (ringChar F)).2 (hdk.trans_le hchar)
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
is at least `k`. -/
lemma umEvalOnPoints_domRestrict_injective
    {ι : Type*} [Fintype ι] {k s : ℕ}
    (domain : ι ↪ F) (hchar : k ≤ ringChar F)
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
    (domain : ι ↪ F) (hchar : k ≤ ringChar F)
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
    (domain : ι ↪ F) (k s : ℕ) (hchar : k ≤ ringChar F) :
    Module.finrank F (umCode domain k s) = min k (s * Fintype.card ι) := by
  classical
  by_cases hk : k ≤ s * Fintype.card ι
  · rw [dim_umCode domain hchar hk, min_eq_left hk]
  · have hnsk : s * Fintype.card ι ≤ k := by omega
    have hchar' : s * Fintype.card ι ≤ ringChar F := hnsk.trans hchar
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

/-- **Sanity check: `UM[F, L, k, 1]` ↔ `RS[F, L, k]`.** With `s = 1`,
the only fold index is `0 : Fin 1`, and `Polynomial.derivative^[0]` is
the identity, so each multiplicity codeword reduces to a plain RS
codeword. Stated as an iff between memberships (the LHS lives in
`ι → Fin 1 → F`, the RHS in `ι → F`, avoiding the cross-type equality
issue).

Proved as a corollary of the encoder-generic
`ReedSolomon.mem_map_degreeLT_one_iff_mem_code`, shared with
`ReedSolomon.Folded.mem_frsCode_one_iff_mem_rsCode`, at that lemma's own
`[CommSemiring F]` generality. -/
lemma Multiplicity.mem_umCode_one_iff_mem_rsCode
    {ι : Type*} {F : Type*} [CommSemiring F]
    (domain : ι ↪ F) (k : ℕ) (f : ι → Fin 1 → F) :
    f ∈ Multiplicity.umCode domain k 1 ↔
      (fun i ↦ f i 0) ∈ ReedSolomon.code domain k :=
  ReedSolomon.mem_map_degreeLT_one_iff_mem_code domain k
    (Multiplicity.umEvalOnPoints domain 1)
    (fun p x => by simp [Multiplicity.umEvalOnPoints]) f

end ReedSolomon
