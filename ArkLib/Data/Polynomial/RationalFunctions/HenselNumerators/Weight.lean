/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov
-/

import ArkLib.Data.Polynomial.Bivariate
import ArkLib.Data.Polynomial.Prelims
import Mathlib.FieldTheory.RatFunc.Defs
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.PowerSeries.Substitution

import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import ArkLib.Data.Polynomial.RationalFunctions.Weight
import ArkLib.Data.Polynomial.RationalFunctions.HenselNumerators.Hensel
/-!
# Claim A.2 Weight Bounds

Appendix A.4 of [BCIKS20], the quantitative half of Claim A.2: the `RegularWeightLe`
certificate calculus on `𝕃 H`, the sharp per-step budget
`numeratorShapeSharp = 1 + (t+1)Λ(W) + eₜΛ(ξ)`, its weakening to the paper's `(2t+1)·d·D`, and the
induction transporting them along the cleared Hensel residual.

One summand of `henselClearedTerm_weight` is still open; the in-proof comment there explains why the
paper's `(A.1)`-recursion route cannot close it.

## References

[BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.

-/


open Polynomial Polynomial.Bivariate ToRatFunc Ideal

namespace RationalFunctions
noncomputable section
section
variable {F : Type} [CommRing F] [IsDomain F]

omit [IsDomain F] in
/-- `Λ` is subadditive under multiplication of bivariate polynomials (bound form). -/
lemma weight_mul_le' {f g H : F[X][Y]} {D bf bg : ℕ}
    (hf : weight f H D ≤ (WithBot.some bf : WithBot ℕ))
    (hg : weight g H D ≤ (WithBot.some bg : WithBot ℕ)) :
    weight (f * g) H D ≤ (WithBot.some (bf + bg) : WithBot ℕ) := by
  classical
  rw [weight_le_iff]
  rw [weight_le_iff] at hf hg
  intro n hn
  set m := D + 1 - Bivariate.natDegreeY H with hm
  have hcoeff_ne : (f * g).coeff n ≠ 0 := Polynomial.mem_support_iff.mp hn
  have hexists : ∃ x ∈ Finset.antidiagonal n, f.coeff x.1 * g.coeff x.2 ≠ 0 := by
    by_contra h
    push Not at h
    exact hcoeff_ne (by rw [Polynomial.coeff_mul]; exact Finset.sum_eq_zero h)
  obtain ⟨x0, hx0mem, hx0ne⟩ := hexists
  have hx0sum : x0.1 + x0.2 = n := Finset.mem_antidiagonal.mp hx0mem
  have hfb0 := hf x0.1 (Polynomial.mem_support_iff.mpr (left_ne_zero_of_mul hx0ne))
  have hgb0 := hg x0.2 (Polynomial.mem_support_iff.mpr (right_ne_zero_of_mul hx0ne))
  have hnm_le : n * m ≤ bf + bg := by
    have : n * m = x0.1 * m + x0.2 * m := by rw [← hx0sum, Nat.add_mul]
    omega
  have hdeg : ((f * g).coeff n).natDegree ≤ bf + bg - n * m := by
    rw [Polynomial.coeff_mul]
    refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
    intro x hx
    have hxsum : x.1 + x.2 = n := Finset.mem_antidiagonal.mp hx
    by_cases hxz : f.coeff x.1 * g.coeff x.2 = 0
    · simp [hxz]
    · have hfb := hf x.1 (Polynomial.mem_support_iff.mpr (left_ne_zero_of_mul hxz))
      have hgb := hg x.2 (Polynomial.mem_support_iff.mpr (right_ne_zero_of_mul hxz))
      have hprod : (f.coeff x.1 * g.coeff x.2).natDegree ≤
          (f.coeff x.1).natDegree + (g.coeff x.2).natDegree := Polynomial.natDegree_mul_le
      have hnm : n * m = x.1 * m + x.2 * m := by rw [← hxsum, Nat.add_mul]
      omega
  omega

end

namespace HenselNumerators
variable {F : Type} [Field F] {R : F[X][X][X]} {H : F[X][Y]}
  [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]

omit H_irreducible H_natDegree_pos in
/-- The `𝒪`-weight is invariant under negation. -/
lemma regularWeight_neg {hH : 0 < H.natDegree} (a : 𝒪 H) (D : ℕ) :
    regularWeight hH (-a) D = regularWeight hH a D := by
  classical
  have hrep : (-a) = (Ideal.Quotient.mk (Ideal.span {monicize H})
      (-(canonicalRepOf𝒪 hH a)) : 𝒪 H) := by
    rw [map_neg, mk_canonicalRepOf𝒪]
  have hdeg : (-(canonicalRepOf𝒪 hH a)).degree < (monicize H).degree := by
    rw [Polynomial.degree_neg]; exact canonicalRepOf𝒪_degree_lt hH a
  rw [hrep, regularWeight_mk_eq_self_of_degree_lt hH hdeg, weight_neg]
  rfl

omit H_irreducible H_natDegree_pos in
/-- `𝒪`-weight is subadditive under multiplication (bound form). -/
lemma regularWeight_mul_le' {D : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hH : 0 < H.natDegree) {a b : 𝒪 H} {ba bb : ℕ}
    (ha : regularWeight hH a D ≤ (WithBot.some ba : WithBot ℕ))
    (hb : regularWeight hH b D ≤ (WithBot.some bb : WithBot ℕ)) :
    regularWeight hH (a * b) D ≤ (WithBot.some (ba + bb) : WithBot ℕ) := by
  classical
  have hab : a * b = (Ideal.Quotient.mk (Ideal.span {monicize H})
      (canonicalRepOf𝒪 hH a * canonicalRepOf𝒪 hH b) : 𝒪 H) := by
    rw [map_mul, mk_canonicalRepOf𝒪, mk_canonicalRepOf𝒪]
  rw [hab]
  exact (regularWeight_mk_le hD hH _).trans (weight_mul_le' ha hb)

/-- `RegularWeightLe hH a D B`: the element `a : 𝕃 H` is regular (in the image of `𝒪 H`) with a
witness whose `Λ`-weight is at most `B`. Bundles regularity together with a weight certificate so
that the Hensel-clearing expansion can be carried out with `Λ`-bookkeeping. -/
def RegularWeightLe {H : F[X][Y]} (hH : 0 < H.natDegree) (a : 𝕃 H) (D B : ℕ) : Prop :=
  ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 H b ∧
    regularWeight hH b D ≤ (WithBot.some B : WithBot ℕ)

omit H_irreducible H_natDegree_pos in
lemma RegularWeightLe.mono {hH : 0 < H.natDegree} {a : 𝕃 H} {D B B' : ℕ}
    (h : RegularWeightLe hH a D B) (hBB : B ≤ B') : RegularWeightLe hH a D B' := by
  obtain ⟨b, hb, hw⟩ := h
  exact ⟨b, hb, hw.trans (by exact_mod_cast hBB)⟩

omit H_irreducible H_natDegree_pos in
lemma RegularWeightLe.mul {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) {hH : 0 < H.natDegree}
    {a b : 𝕃 H} {Ba Bb : ℕ}
    (ha : RegularWeightLe hH a D Ba) (hb : RegularWeightLe hH b D Bb) :
    RegularWeightLe hH (a * b) D (Ba + Bb) := by
  obtain ⟨a', ha', hwa⟩ := ha
  obtain ⟨b', hb', hwb⟩ := hb
  exact ⟨a' * b', by rw [ha', hb', map_mul], regularWeight_mul_le' hD hH hwa hwb⟩

omit H_irreducible H_natDegree_pos in
lemma RegularWeightLe.add {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) {hH : 0 < H.natDegree}
    {a b : 𝕃 H} {B : ℕ}
    (ha : RegularWeightLe hH a D B) (hb : RegularWeightLe hH b D B) :
    RegularWeightLe hH (a + b) D B := by
  obtain ⟨a', ha', hwa⟩ := ha
  obtain ⟨b', hb', hwb⟩ := hb
  exact ⟨a' + b', by rw [ha', hb', map_add],
    (regularWeight_add_le hD hH a' b').trans (max_le hwa hwb)⟩

omit H_irreducible H_natDegree_pos in
lemma RegularWeightLe.neg {hH : 0 < H.natDegree} {a : 𝕃 H} {D B : ℕ}
    (ha : RegularWeightLe hH a D B) : RegularWeightLe hH (-a) D B := by
  obtain ⟨a', ha', hwa⟩ := ha
  exact ⟨-a', by rw [ha', map_neg], by rwa [regularWeight_neg]⟩

omit H_irreducible H_natDegree_pos in
lemma RegularWeightLe.pow {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) {hH : 0 < H.natDegree}
    {a : 𝕃 H} {Ba : ℕ} (ha : RegularWeightLe hH a D Ba) (k : ℕ) :
    RegularWeightLe hH (a ^ k) D (k * Ba) := by
  induction k with
  | zero =>
      simp only [pow_zero, Nat.zero_mul]
      refine ⟨1, by rw [map_one], ?_⟩
      rw
          [show (1 : 𝒪 H) = (Ideal.Quotient.mk (Ideal.span {monicize H}) (1 : F[X][Y]) : 𝒪 H) by
              simp]
      refine (regularWeight_mk_le hD hH _).trans ?_
      rw [show (1 : F[X][Y]) = Polynomial.C 1 by simp]
      exact (weight_C_le H D 1).trans (by simp)
  | succ k ih =>
      rw [pow_succ]
      refine (RegularWeightLe.mul hD ih ha).mono ?_
      ring_nf; omega

omit H_irreducible H_natDegree_pos in
lemma RegularWeightLe.sum {ι : Type} (s : Finset ι) (f : ι → 𝕃 H)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) {hH : 0 < H.natDegree} {B : ℕ}
    (hf : ∀ i ∈ s, RegularWeightLe hH (f i) D B) :
    RegularWeightLe hH (∑ i ∈ s, f i) D B := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, by rw [map_zero, Finset.sum_empty], ?_⟩
      rw [regularWeight_zero]; exact bot_le
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact RegularWeightLe.add hD (hf a (Finset.mem_insert_self a s))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

omit H_irreducible H_natDegree_pos in
lemma RegularWeightLe.prod {ι : Type} (s : Finset ι) (f : ι → 𝕃 H) (B : ι → ℕ)
    {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) {hH : 0 < H.natDegree}
    (hf : ∀ i ∈ s, RegularWeightLe hH (f i) D (B i)) :
    RegularWeightLe hH (∏ i ∈ s, f i) D (∑ i ∈ s, B i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Finset.sum_empty]
      refine ⟨1, by rw [map_one], ?_⟩
      rw
          [show (1 : 𝒪 H) = (Ideal.Quotient.mk (Ideal.span {monicize H}) (1 : F[X][Y]) : 𝒪 H) by
              simp]
      refine (regularWeight_mk_le hD hH _).trans ?_
      rw [show (1 : F[X][Y]) = Polynomial.C 1 by simp]
      exact (weight_C_le H D 1).trans (by simp)
  | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact RegularWeightLe.mul hD (hf a (Finset.mem_insert_self a s))
        (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

omit H_irreducible H_natDegree_pos in
/-- Coefficient embeddings are regular with `Λ`-weight at most their `X`-degree. -/
lemma regularWeightLe_liftToFunctionField {D : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hH : 0 < H.natDegree)
    (c : F[X]) : RegularWeightLe hH (liftToFunctionField (H := H) c) D c.natDegree := by
  refine ⟨(Ideal.Quotient.mk (Ideal.span {monicize H}) (Polynomial.C c) : 𝒪 H), ?_, ?_⟩
  · rw [embeddingOf𝒪Into𝕃_mk]; rfl
  · exact (regularWeight_mk_le hD hH _).trans (weight_C_le H D c)

omit H_irreducible H_natDegree_pos in
/-- The leading coefficient lift `W` is regular with `Λ`-weight at most `D`. -/
lemma regularWeightLe_leadingCoeff {D : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hH : 0 < H.natDegree) :
    RegularWeightLe hH (liftToFunctionField (H := H) H.leadingCoeff) D D := by
  refine (regularWeightLe_liftToFunctionField hD hH H.leadingCoeff).mono ?_
  by_cases hHz : H = 0
  · simp [hHz]
  · have hH_in : H.natDegree ∈ H.support :=
      Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hHz)
    have h1 : (H.coeff H.natDegree).natDegree + H.natDegree ≤ Bivariate.totalDegree H :=
      Bivariate.coeff_totalDegree_le H hH_in
    rw [Polynomial.leadingCoeff]; omega

omit H_irreducible H_natDegree_pos in
/-- The power-series variable's coefficients are regular with weight `0`. -/
lemma regularWeightLe_functionFieldT_pow {D : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hH : 0 < H.natDegree) (n : ℕ) :
    RegularWeightLe hH (PowerSeries.coeff n (PowerSeries.X : PowerSeries (𝕃 H))) D 0 := by
  rw [PowerSeries.coeff_X]
  split
  · rw [show (1 : 𝕃 H) = liftToFunctionField (H := H) 1 by simp]
    exact (regularWeightLe_liftToFunctionField hD hH 1).mono (by simp)
  · rw [show (0 : 𝕃 H) = liftToFunctionField (H := H) 0 by simp]
    exact (regularWeightLe_liftToFunctionField hD hH 0).mono (by simp)

omit H_irreducible H_natDegree_pos in
/-- The field constant embedding has weight `0`. -/
lemma regularWeightLe_fieldTo𝕃 {D : ℕ} (hD : Bivariate.totalDegree H ≤ D) (hH : 0 < H.natDegree)
    (x₀ : F) : RegularWeightLe hH (fieldTo𝕃 (H := H) x₀) D 0 := by
  rw [show fieldTo𝕃 (H := H) x₀ = liftToFunctionField (H := H) (Polynomial.C x₀) from rfl]
  exact (regularWeightLe_liftToFunctionField hD hH _).mono (by simp [Polynomial.natDegree_C])

omit H_irreducible H_natDegree_pos in
/-- Coefficients of the local-coordinate binomial `(x₀ + S)^s` are weight-`0` regular. -/
lemma regularWeightLe_natCast_choose {D : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hH : 0 < H.natDegree)
    (x₀ : F) (s : ℕ) : ∀ n,
    RegularWeightLe hH (PowerSeries.coeff n
      ((PowerSeries.C (fieldTo𝕃 (H := H) x₀) + PowerSeries.X) ^ s)) D 0 := by
  induction s with
  | zero =>
      intro n
      rw [pow_zero, PowerSeries.coeff_one]
      split
      · rw [show (1 : 𝕃 H) = liftToFunctionField (H := H) 1 by simp]
        exact (regularWeightLe_liftToFunctionField hD hH 1).mono (by simp)
      · rw [show (0 : 𝕃 H) = liftToFunctionField (H := H) 0 by simp]
        exact (regularWeightLe_liftToFunctionField hD hH 0).mono (by simp)
  | succ s ih =>
      intro n
      rw [pow_succ, PowerSeries.coeff_mul]
      refine RegularWeightLe.sum _ _ hD ?_
      intro pr _
      have h2 : RegularWeightLe hH
          (PowerSeries.coeff pr.2 (PowerSeries.C (fieldTo𝕃 (H := H) x₀) + PowerSeries.X)) D 0 := by
        rw [map_add]
        refine RegularWeightLe.add hD ?_ (regularWeightLe_functionFieldT_pow hD hH pr.2)
        rw [PowerSeries.coeff_C]
        split
        · exact regularWeightLe_fieldTo𝕃 hD hH x₀
        · rw [show (0 : 𝕃 H) = liftToFunctionField (H := H) 0 by simp]
          exact (regularWeightLe_liftToFunctionField hD hH 0).mono (by simp)
      exact (RegularWeightLe.mul hD (ih pr.1) h2).mono (by simp)

omit H_irreducible H_natDegree_pos in
/-- Each coefficient of `liftCoeffToPowerSeries x₀ H p` is regular with weight at most the
total degree of `p`. -/
lemma regularWeightLe_coeff_liftCoeffToPowerSeries {D : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hH : 0 < H.natDegree)
    (x₀ : F) (p : F[X][X]) (n : ℕ) :
    RegularWeightLe hH (PowerSeries.coeff n (liftCoeffToPowerSeries x₀ H p)) D
      (Bivariate.totalDegree p) := by
  classical
  unfold liftCoeffToPowerSeries
  rw [coe_eval₂RingHom, Polynomial.eval₂_eq_sum_range, map_sum]
  refine RegularWeightLe.sum _ _ hD ?_
  intro s _
  rw [RingHom.comp_apply, PowerSeries.coeff_C_mul]
  refine (RegularWeightLe.mul hD (regularWeightLe_liftToFunctionField hD hH (p.coeff s))
    (regularWeightLe_natCast_choose hD hH x₀ s n)).mono ?_
  rw [Nat.add_zero]
  rcases Bivariate.coeff_totalDegree_le' p s with h | h0
  · omega
  · rw [h0]; simp

omit H_irreducible H_natDegree_pos in
/-- Sharp `Λ`-weight bound on the leading-coefficient lift `W`: `Λ(W) ≤ D - dH`.
This is the per-`W`-factor budget used in the sharp telescoping of [BCIKS20] A.4 (pp. 52–53);
the looser `Λ(W) ≤ D` of `regularWeightLe_leadingCoeff` is not enough for the constant term to
telescope. -/
lemma regularWeightLe_leadingCoeff_sharp {D : ℕ} (hD : Bivariate.totalDegree H ≤ D)
    (hH : 0 < H.natDegree) :
    RegularWeightLe hH (liftToFunctionField (H := H) H.leadingCoeff) D
      (D - H.natDegree) := by
  refine (regularWeightLe_liftToFunctionField hD hH H.leadingCoeff).mono ?_
  by_cases hHz : H = 0
  · simp [hHz]
  · have hH_in : H.natDegree ∈ H.support :=
      Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hHz)
    have h1 : (H.coeff H.natDegree).natDegree + H.natDegree ≤ Bivariate.totalDegree H :=
      Bivariate.coeff_totalDegree_le H hH_in
    rw [Polynomial.leadingCoeff]; omega

/-- The sharp per-step `Λ`-weight budget of [BCIKS20] A.4 (the bound on `Λ(βₜ)`):
`sharp t = 1 + (t+1)·(D - dH) + eₜ·((dY-1)·(D - dH + 1))`, where `dH = natDegreeY H`,
`dY = natDegreeY R`, and `eₜ = henselDenominatorExponent t`.  The `1` is the constant from the
leading-coefficient divisibility, `(t+1)·(D-dH)` is the `W`-power contribution, and the last term
is the `ξ`-power contribution.  This bound telescopes linearly in `t`, unlike the loose
multiplicative `(2t+1)·dY·D`. -/
def numeratorShapeSharp (R : F[X][X][Y]) (H : F[X][Y]) (D t : ℕ) : ℕ :=
  1 + (t + 1) * (D - Bivariate.natDegreeY H) +
    henselDenominatorExponent t *
      ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1))

/-- The sharp bound weakens to the loose paper bound consumed by the final assembly:
`sharp t ≤ (2t+1)·dY·D`.  Pure arithmetic, using `dH ≥ 1`, `dH ≤ dY`, `dH ≤ D`, and
`eₜ ≤ 2t`. -/
lemma numeratorShapeSharp_le_loose (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D) (t : ℕ) :
    numeratorShapeSharp R H D t ≤ (2 * t + 1) * Bivariate.natDegreeY R * D := by
  -- Translate the degree facts into the bare numeric hypotheses needed by the arithmetic.
  have hdH_dY : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R :=
    natDegree_H_le_natDegree_R_of_hypotheses hHyp
  have hdH_pos : 1 ≤ Bivariate.natDegreeY H := hH
  have hdH_D : Bivariate.natDegreeY H ≤ D := by
    have hH_in : H.natDegree ∈ H.support :=
      Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr
        (by rintro rfl; simp at hH))
    have h1 : (H.coeff H.natDegree).natDegree + H.natDegree ≤ Bivariate.totalDegree H :=
      Bivariate.coeff_totalDegree_le H hH_in
    rw [show Bivariate.natDegreeY H = H.natDegree from rfl]; omega
  have het : henselDenominatorExponent t ≤ 2 * t := by
    unfold henselDenominatorExponent; split <;> omega
  unfold numeratorShapeSharp
  set D' := D
  set dH := Bivariate.natDegreeY H with hdHdef
  set dY := Bivariate.natDegreeY R with hdYdef
  set et := henselDenominatorExponent t with hetdef
  clear_value D' dH dY et
  obtain ⟨a, rfl⟩ : ∃ a, D' = dH + a := ⟨D' - dH, by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, dY = dH + b := ⟨dY - dH, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, dH = c + 1 := ⟨dH - 1, by omega⟩
  simp only [Nat.add_sub_cancel_left] at *
  rw [show c + 1 + b - 1 = c + b by omega]
  have hA : et * ((c + b) * (a + 1)) ≤ 2 * t * ((c + b) * (a + 1)) :=
    Nat.mul_le_mul_right _ (by omega)
  have hRHS : (2 * t + 1) * ((c + b) + 1) * (a + 1) ≤
      (2 * t + 1) * (c + 1 + b) * (c + 1 + a) := by
    apply Nat.mul_le_mul
    · rw [show c + 1 + b = (c + b) + 1 by ring]
    · omega
  nlinarith [hA, hRHS]

omit H_irreducible H_natDegree_pos in
/-- `RegularWeightLe`-version of the bridge from the embedded `𝒪`-witness back to the `𝒪`-weight:
if `embeddingOf𝒪Into𝕃 H b` is regular with `Λ`-witness of weight `≤ B`, then so is the canonical
witness `b` itself (by injectivity of the embedding). -/
lemma regularWeight_le_of_regularWeightLe {hH : 0 < H.natDegree} {D B : ℕ} (b : 𝒪 H)
    (h : RegularWeightLe hH (embeddingOf𝒪Into𝕃 H b) D B) :
    regularWeight hH b D ≤ (WithBot.some B : WithBot ℕ) := by
  obtain ⟨b', heq, hw⟩ := h
  rwa [embeddingOf𝒪Into𝕃_injective hH heq]

/-- Bridge identity for the weight induction: the embedded `(t+1)`-st numerator equals the negated
cleared residual.  This is the same algebraic computation as in `regular_numerator_shape_succ`
(using `hshape` to identify `αseq(t+1)` with `embedding βₜ₊₁ / Dfull` and `hroot` to kill the
`coeff (t+1)` term), repackaged as an equation so the weight bound can be transported through it. -/
lemma betaSucc_eq_neg_clearedResidual (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H)
    (αseq : ℕ → 𝕃 H) (βseq : ℕ → 𝒪 H)
    (hroot : evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq) = 0)
    (hshape : HasNumeratorShape x₀ R H hHyp αseq βseq)
    (t : ℕ) :
    embeddingOf𝒪Into𝕃 H (βseq (t + 1)) =
      -(henselCoeffResidual x₀ R H αseq t *
        (liftToFunctionField (H := H) H.leadingCoeff ^ (t + 1 + 1) *
          (embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp)) ^ (henselDenominatorExponent (t + 1) - 1) *
          liftToFunctionField (H := H) H.leadingCoeff ^ (R.natDegree - 2))) := by
  classical
  set W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff with hWdef
  set eta : 𝕃 H := embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp) with hetadef
  set E : ℕ := henselDenominatorExponent (t + 1) with hEdef
  set Ddiv : 𝕃 H := W ^ (t + 1 + 1) * eta ^ (E - 1) * W ^ (R.natDegree - 2) with hDdivdef
  set Dfull : 𝕃 H := W ^ (t + 1 + 1) * eta ^ E with hDfulldef
  have hzeta : zeta R x₀ H ≠ 0 := zeta_ne_zero_of_hypotheses x₀ R H hHyp
  have hW : W ≠ 0 := liftToFunctionField_leadingCoeff_ne_zero (H := H)
  have heta : eta ≠ 0 := by
    rw [hetadef, embeddingOf𝒪Into𝕃_xi]
    exact mul_ne_zero (pow_ne_zero _ hW) hzeta
  have hDfull : Dfull ≠ 0 := mul_ne_zero (pow_ne_zero _ hW) (pow_ne_zero _ heta)
  have hsh := hshape (t + 1)
  have hsh2 : embeddingOf𝒪Into𝕃 H (βseq (t + 1)) / Dfull = αseq (t + 1) := by
    rw [hDfulldef, hWdef, hetadef, hEdef]; exact hsh
  have hsh' : embeddingOf𝒪Into𝕃 H (βseq (t + 1)) = αseq (t + 1) * Dfull := by
    rw [← hsh2]; field_simp
  rw [hsh']
  have hcoeff : PowerSeries.coeff (t + 1)
      (evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq)) = 0 := by
    simpa using congrArg (fun p : PowerSeries (𝕃 H) =>
      PowerSeries.coeff (t + 1) p) hroot
  have hres : henselCoeffResidual x₀ R H αseq t = - zeta R x₀ H * αseq (t + 1) := by
    unfold henselCoeffResidual; rw [hcoeff]; ring
  have hEpos : 0 < E := by rw [hEdef, henselDenominatorExponent_succ]; omega
  have hpeta : eta ^ E = eta ^ (E - 1) * eta := by
    conv_lhs => rw [show E = (E - 1) + 1 by omega, pow_succ]
  have heta_eq : eta = W ^ (R.natDegree - 2) * zeta R x₀ H := by
    rw [hetadef, hWdef]; exact embeddingOf𝒪Into𝕃_xi x₀ R H hHyp
  have hDfull_eq : Dfull = zeta R x₀ H * Ddiv := by
    rw [hDfulldef, hpeta, hDdivdef]
    rw [show eta ^ (E - 1) * eta = eta ^ (E - 1) * (W ^ (R.natDegree - 2) * zeta R x₀ H) by
      rw [← heta_eq]]
    ring
  rw [hres, hDfull_eq]; ring

set_option maxHeartbeats 2000000 in
-- The `Finset.finsuppAntidiag` case split below expands one `PowerSeries.coeff` of a
-- `d`-fold product into a sum over compositions, and each summand carries a `RegularWeightLe`
-- certificate assembled from seven `.mul`/`.pow`/`.sum` steps; the default heartbeat budget is
-- exhausted by the resulting `ring`/`omega` normalisations.
/-- Weight-tracking per-degree clearing lemma: the `Λ`-graded analogue of
`henselClearedTerm_regular`.  Each degree-`j` summand of the cleared `(t+1)`-st residual is
regular with sharp `Λ`-weight at most `numeratorShapeSharp R H D (t+1)`.  The non-boundary
branch is fully proven; the single boundary summand (`p.1 = 0`, `j = d ≥ 2`, `p.2 = t+1`) is
the remaining gap (see the in-proof comment). -/
lemma henselClearedTerm_weight (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (t : ℕ) (αtrunc : ℕ → 𝕃 H)
    (ihNum : ∀ i, i ≤ t →
      RegularWeightLe hH
        (αtrunc i * (liftToFunctionField (H := H) H.leadingCoeff ^ (i + 1) *
          (embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp)) ^ henselDenominatorExponent i))
        D (numeratorShapeSharp R H D i))
    (hαzero : ∀ i, t < i → αtrunc i = 0)
    (j : ℕ) (hj : j ∈ Finset.range (R.natDegree + 1)) :
    RegularWeightLe hH
      (PowerSeries.coeff (t + 1)
        (liftCoeffToPowerSeries x₀ H (R.coeff j) * (PowerSeries.mk αtrunc) ^ j) *
        (liftToFunctionField (H := H) H.leadingCoeff ^ (t + 1 + 1) *
          (embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp)) ^ (henselDenominatorExponent (t + 1) - 1) *
          liftToFunctionField (H := H) H.leadingCoeff ^ (R.natDegree - 2)))
      D (numeratorShapeSharp R H D (t + 1)) := by
  classical
  set W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff with hWdef
  set eta : 𝕃 H := embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp) with hetadef
  -- abbreviations for the sharp weight atoms
  set ΛW : ℕ := D - Bivariate.natDegreeY H with hΛWdef
  set Λξ : ℕ := (Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1) with hΛξdef
  -- base RegularWeightLe certificates for W and ξ at the SHARP weights
  have hRWLW : RegularWeightLe hH W D ΛW := by
    rw [hWdef, hΛWdef]
    exact regularWeightLe_leadingCoeff_sharp hD_H hH
  have hRWLeta : RegularWeightLe hH eta D Λξ := by
    rw [hetadef, hΛξdef]
    -- ξ as an 𝒪-element
    obtain ⟨b, hb⟩ : ∃ b : 𝒪 H, embeddingOf𝒪Into𝕃 H b = eta := ⟨xi x₀ R H hHyp, rfl⟩
    refine ⟨xi x₀ R H hHyp, rfl, ?_⟩
    exact xi_weight_le x₀ hH hHyp hRdeg hD_H hD_Rx0
  have hjle : j ≤ R.natDegree := by rw [Finset.mem_range] at hj; omega
  have hdH_le_R : Bivariate.natDegreeY H ≤ Bivariate.natDegreeY R :=
    natDegree_H_le_natDegree_R_of_hypotheses hHyp
  have hdY : Bivariate.natDegreeY R = R.natDegree := rfl
  have hdH : Bivariate.natDegreeY H = H.natDegree := rfl
  -- distribute coeff_mul and coeff_pow into a sum over (p, l)
  rw [PowerSeries.coeff_mul, Finset.sum_mul]
  apply RegularWeightLe.sum _ _ hD_H
  intro p _hp
  rw [PowerSeries.coeff_pow]
  simp only [PowerSeries.coeff_mk]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply RegularWeightLe.sum _ _ hD_H
  intro l hl
  rw [Finset.mem_finsuppAntidiag] at hl
  have hbsum : (∑ i ∈ Finset.range j, l i) = p.2 := hl.1
  have hab : p.1 + p.2 = t + 1 := Finset.mem_antidiagonal.mp _hp
  -- Case A: some part exceeds t ⇒ a zero factor ⇒ weight 0.
  by_cases hbig : ∃ i ∈ Finset.range j, t < l i
  · obtain ⟨i₀, hi₀, hi₀t⟩ := hbig
    have hz : (∏ i ∈ Finset.range j, αtrunc (l i)) = 0 :=
      Finset.prod_eq_zero hi₀ (hαzero _ hi₀t)
    rw [hz]
    refine ⟨0, by simp, ?_⟩
    rw [regularWeight_zero]; exact bot_le
  · -- Case B: all parts ≤ t.
    push Not at hbig
    have hle : ∀ i ∈ Finset.range j, l i ≤ t := hbig
    -- product-clearing weight: ∏ αtrunc(l i) · W^Pw · eta^Pe  has weight ≤ ∑ sharp(l i)
    set Pw : ℕ := (∑ i ∈ Finset.range j, (l i + 1)) with hPwdef
    set Pe : ℕ := (∑ i ∈ Finset.range j, henselDenominatorExponent (l i)) with hPedef
    set E1 : ℕ := henselDenominatorExponent (t + 1) - 1 with hE1def
    have hPweq : Pw = p.2 + j := by rw [hPwdef, Finset.sum_add_distrib, hbsum]; simp
    have hprodW : RegularWeightLe hH
        ((∏ i ∈ Finset.range j, αtrunc (l i)) * (W ^ Pw * eta ^ Pe)) D
        (∑ i ∈ Finset.range j, numeratorShapeSharp R H D (l i)) := by
      rw [hPwdef, hPedef, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_pow_eq_pow_sum,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine RegularWeightLe.prod _ _ _ hD_H ?_
      intro i hi
      have := ihNum (l i) (hle i hi)
      -- rearrange W^(l i+1)*eta^e to match
      have hrw : αtrunc (l i) * (W ^ (l i + 1) * eta ^ henselDenominatorExponent (l i)) =
          αtrunc (l i) * (W ^ (l i + 1) * eta ^ henselDenominatorExponent (l i)) := rfl
      rw [hWdef, hetadef] at this ⊢
      exact this
    -- the eta exponent bound Pe ≤ E1 = 2t
    have hPe_le : Pe ≤ E1 := by
      rw [hE1def, hPedef]
      set Pe' := (∑ i ∈ Finset.range j, henselDenominatorExponent (l i)) with hPe'def
      set S1 := (∑ i ∈ Finset.range j, (if l i = 0 then 0 else 1)) with hS1def
      have h2b : 2 * p.2 = Pe' + S1 := by
        rw [hPe'def, hS1def, ← hbsum, Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by
          unfold henselDenominatorExponent; split <;> omega
      have hbS1 : p.2 ≤ t * S1 := by
        rw [← hbsum, hS1def, Finset.mul_sum]
        refine Finset.sum_le_sum fun i hi => ?_
        split
        · next h => rw [h]; simp
        · next h => rw [Nat.mul_one]; exact hle i hi
      have hE1' : henselDenominatorExponent (t + 1) - 1 = 2 * t := by
        rw [henselDenominatorExponent_succ]; omega
      rw [hE1']
      rcases Nat.lt_or_ge p.2 (t + 1) with hbt | hbt
      · omega
      · have hS1ge : 2 ≤ S1 := by
          by_contra h; push Not at h; interval_cases S1 <;> omega
        omega
    -- sharp-sum identity: ∑ sharp(l i) = j + Pw*ΛW + Pe*Λξ
    have hsharpSum : (∑ i ∈ Finset.range j, numeratorShapeSharp R H D (l i)) =
        j + Pw * ΛW + Pe * Λξ := by
      have hexpand : ∀ i, numeratorShapeSharp R H D (l i) =
          1 + (l i + 1) * ΛW + henselDenominatorExponent (l i) * Λξ := by
        intro i; rw [numeratorShapeSharp, hΛWdef, hΛξdef]
      simp only [hexpand]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      rw [Finset.sum_const, Finset.card_range, smul_eq_mul, Nat.mul_one]
      rw [← Finset.sum_mul, ← Finset.sum_mul, ← hPwdef, ← hPedef]
    -- W exponent budget (NON-boundary): wb = (t+2)+(d-2).
    -- E1 leftover: eta^(E1 - Pe).
    -- coefficient weight ≤ totalDegree (R.coeff j) ≤ D - j
    have hcoeffW : RegularWeightLe hH
        (PowerSeries.coeff p.1 (liftCoeffToPowerSeries x₀ H (R.coeff j))) D
        (Bivariate.totalDegree (R.coeff j)) := regularWeightLe_coeff_liftCoeffToPowerSeries hD_H hH
            x₀ (R.coeff j) p.1
    have htd_le : Bivariate.totalDegree (R.coeff j) ≤ D - j := by
      by_cases hjs : j ∈ R.support
      · have := hD_R j hjs; omega
      · have hz : R.coeff j = 0 := by
          by_contra hne; exact hjs (Polynomial.mem_support_iff.mpr hne)
        rw [hz]; simp [Bivariate.totalDegree]
    -- key arithmetic facts
    have hkey : D ≤ R.natDegree + ΛW := by
      rw [hΛWdef]
      have : Bivariate.natDegreeY H ≤ R.natDegree := by rw [← hdY]; exact hdH_le_R
      rw [hdH] at this
      omega
    have hjd : j ≤ R.natDegree := hjle
    have hdD : R.natDegree ≤ D := by
      by_cases hRz : R = 0
      · simp [hRz]
      · have hmem : R.natDegree ∈ R.support :=
          Polynomial.mem_support_iff.mpr (Polynomial.leadingCoeff_ne_zero.mpr hRz)
        have := hD_R R.natDegree hmem; omega
    have hjD : j ≤ D := le_trans hjd hdD
    -- boundary detection
    by_cases hbdry : p.2 = t + 1 ∧ j = R.natDegree ∧ 2 ≤ R.natDegree
    · -- BOUNDARY CASE: `p.1 = 0`, `j = d = R.natDegree ≥ 2`, `p.2 = t+1`.
      --
      -- This is the one summand the (A.1)-recursion route of [BCIKS20] A.4 does not reach, and the
      -- obstruction is *tightness*, not bookkeeping.  Accounting, with `x` the `W`-charge and `Z`
      -- the `ξ`-charge of `numeratorShapeSharp`:
      --
      --   available `W`-power  : `wb = (t+2) + (d-2) = t+d`
      --   consumed by the `d` part-certificates : `Pw = p.2 + j = t+d+1`   (one more than `wb`)
      --
      -- The missing `W` is supplied by the leading-coefficient divisibility
      -- `W ∣ coeff 0 (liftCoeff (R.coeff d))` (`leadingCoeff_dvd_evalX_coeff_natDegree`, as in
      -- `henselClearedTerm_regular`'s boundary branch): writing that coefficient as `W * c`
      -- pays the deficit and charges `Λ(c) = c.natDegree` instead of `D - d`.  Summing,
      --
      --   total  = c.natDegree + d + (t+d+1)·x + 2t·Z
      --   target = 1 + (t+2)·x + (2t+1)·Z
      --   target - total = Z - (d-1)·x - (d-1) - c.natDegree,
      --
      -- so the branch closes iff `Z ≥ (d-1)(x+1) + c.natDegree`.  With the charges forced
      -- elsewhere in the induction — `x = D - dH` (forced by the base case, since
      -- `Λ(β₀) = Λ(T) = D - dH + 1` by the very definition of the `Λ`-grading) and
      -- `Z = (d-1)(D - dH + 1)` (forced by `xi_weight_le`) — this demands `c.natDegree ≤ 0`,
      -- which is false in general: `R(x₀,·,Z) = H · q` gives `c = leadingCoeff q`, an arbitrary
      -- polynomial.  So this *per-summand* budget is very likely not merely hard but too strong;
      -- `numerator_shape_weight_sharp` can still hold, since `Λ` of the sum over `j` only has to
      -- bound the max after the cancellations that the recursion (A.1) produces.  Closing the gap
      -- therefore means weakening this lemma and recovering the total elsewhere, not grinding this
      -- case.
      --
      -- Raising `Z` by `D - d - W.natDegree` (the true bound on `c.natDegree`) closes this branch
      -- and keeps the non-boundary branch, but then breaks `numeratorShapeSharp_le_loose`: e.g.
      -- `d = 2, dH = 1, D = 100, W.natDegree = 0, t = 5` gives `sharp 5 = 2377 > 2200 = (2t+1)dD`,
      -- and `(2t+1)dD` is the bound [BCIKS20] itself quotes and Claim 5.10 consumes.  The same
      -- tightness is visible in the paper's own quantities: expanding (A.1) for the `i₁ = 0` terms
      -- gives `Λ(βₜ) ≤ D + (t+d-1)Λ(W) + (2t-2)Λ(ξ)`, which meets the claimed
      -- `1 + (t+1)Λ(W) + eₜΛ(ξ)` only when `Λ(ξ) = (D-1) + (d-2)Λ(W)`, i.e. only when `Λ(ξ)`
      -- attains its upper bound.
      --
      -- Consistently, [BCIKS20] does not carry out this induction: it says the bound "can be shown
      -- by induction using the recursion (A.1), but an easier way ... is by considering the weight
      -- of `αₜ`", and then argues `Λ(αₜ) = Λ(Y) = 1` because `γ` solves `R(X,Y,Z) = 0`.  That
      -- second argument is a different (and informal) route: it needs a weight function on the
      -- function field `𝕃`, not just on `𝒪`, together with the fact that the Hensel coefficients
      -- lie in the same graded piece as `Y`.  Formalizing it is the natural way to close this gap.
      --
      -- Everything else in Claim A.2 is proven: existence and uniqueness of the lift, regularity
      -- of every `βₜ` and of `ξ`, the bound on `Λ(ξ)`, the clearing/expansion, the residual
      -- assembly, and the non-boundary branch below.  Nothing that this `sorry` reaches is used to
      -- *define* anything: see `exists_hensel_numerator_sequence`.
      sorry
    · -- NON-BOUNDARY: budget Pw ≤ (t+2)+(d-2) covers everything.
      have hbudget : Pw ≤ (t + 1 + 1) + (R.natDegree - 2) := by
        rw [hPweq, Finset.mem_range] at *
        rcases Nat.lt_or_ge R.natDegree 2 with hd | hd
        · omega
        · rcases not_and_or.mp hbdry with h1 | h2
          · omega
          · rcases not_and_or.mp h2 with h3 | h4
            · omega
            · exact absurd hd h4
      -- reassociate to isolate W^(wb-Pw) and eta^(E1-Pe)
      have hreassoc :
          PowerSeries.coeff p.1 (liftCoeffToPowerSeries x₀ H (R.coeff j)) *
              (∏ i ∈ Finset.range j, αtrunc (l i)) *
                (W ^ (t + 1 + 1) * eta ^ E1 * W ^ (R.natDegree - 2)) =
          PowerSeries.coeff p.1 (liftCoeffToPowerSeries x₀ H (R.coeff j)) *
            ((∏ i ∈ Finset.range j, αtrunc (l i)) * (W ^ Pw * eta ^ Pe)) *
            (W ^ (((t + 1 + 1) + (R.natDegree - 2)) - Pw) * eta ^ (E1 - Pe)) := by
        have hwsplit : ((t + 1 + 1) + (R.natDegree - 2)) =
            Pw + (((t + 1 + 1) + (R.natDegree - 2)) - Pw) := by omega
        have hesplit : E1 = Pe + (E1 - Pe) := by omega
        rw [show PowerSeries.coeff p.1 (liftCoeffToPowerSeries x₀ H (R.coeff j)) *
              (∏ i ∈ Finset.range j, αtrunc (l i)) *
                (W ^ (t + 1 + 1) * eta ^ E1 * W ^ (R.natDegree - 2)) =
            PowerSeries.coeff p.1 (liftCoeffToPowerSeries x₀ H (R.coeff j)) *
              ((∏ i ∈ Finset.range j, αtrunc (l i)) *
                (W ^ ((t + 1 + 1) + (R.natDegree - 2)) * eta ^ E1)) by ring]
        conv_lhs => rw [hwsplit, hesplit, pow_add, pow_add]
        ring
      rw [hreassoc]
      refine (RegularWeightLe.mul hD_H
        (RegularWeightLe.mul hD_H (hcoeffW.mono htd_le) hprodW)
        (RegularWeightLe.mul hD_H (hRWLW.pow hD_H _) (hRWLeta.pow hD_H _))).mono ?_
      -- weight: (D-j) + (j + Pw*ΛW + Pe*Λξ) + ((wb-Pw)*ΛW + (E1-Pe)*Λξ) ≤ sharp(t+1)
      rw [hsharpSum]
      -- sharp(t+1) expansion
      have hsharpSucc : numeratorShapeSharp R H D (t + 1) =
          1 + (t + 2) * ΛW + (2 * t + 1) * Λξ := by
        rw [numeratorShapeSharp, ← hΛWdef, ← hΛξdef, henselDenominatorExponent_succ]
        rw [show 2 * (t + 1) - 1 = 2 * t + 1 by omega, show t + 1 + 1 = t + 2 by omega]
      rw [hsharpSucc]
      -- now pure arithmetic (verified separately)
      set wb := (t + 1 + 1) + (R.natDegree - 2) with hwbdef
      have hE1val : E1 = 2 * t := by rw [hE1def, henselDenominatorExponent_succ]; omega
      have hwb_le : wb ≤ t + R.natDegree := by
        rcases Nat.lt_or_ge R.natDegree 2 with hd | hd
        · -- d < 2: then not boundary forces nothing, but budget? wb = (t+2)+0 = t+2
          rw [hwbdef]; omega
        · rw [hwbdef]; omega
      -- reduce via cancellations
      have hAcancel : Pw * ΛW + (wb - Pw) * ΛW = wb * ΛW := by
        rw [← Nat.add_mul]; congr 1; omega
      have hBcancel : Pe * Λξ + (E1 - Pe) * Λξ = E1 * Λξ := by
        rw [← Nat.add_mul]; congr 1; omega
      have hjDj : D - j + j = D := Nat.sub_add_cancel hjD
      -- Final: (D-j) + (j + Pw ΛW + Pe Λξ) + ((wb-Pw)ΛW + (E1-Pe)Λξ) = D + wb*ΛW + E1*Λξ
      have hΛξval : Λξ = (R.natDegree - 1) * (ΛW + 1) := by
        rw [hΛξdef, hΛWdef, hdY]
      -- prove ≤
      have hfin : (D - j) + (j + Pw * ΛW + Pe * Λξ) +
          ((wb - Pw) * ΛW + (E1 - Pe) * Λξ) ≤ 1 + (t + 2) * ΛW + (2 * t + 1) * Λξ := by
        have e1 : (D - j) + (j + Pw * ΛW + Pe * Λξ) + ((wb - Pw) * ΛW + (E1 - Pe) * Λξ)
            = D + wb * ΛW + E1 * Λξ := by
          rw [← hjDj] at *
          -- use cancellations
          have := hAcancel; have := hBcancel
          omega
        rw [e1, hE1val, hΛξval]
        -- D + wb*ΛW + 2t*((d-1)(ΛW+1)) ≤ 1 + (t+2)ΛW + (2t+1)((d-1)(ΛW+1))
        obtain ⟨gap, hgap⟩ : ∃ g, t + R.natDegree = wb + g := ⟨t + R.natDegree - wb, by omega⟩
        obtain ⟨dm, hdmeq⟩ : ∃ dm, R.natDegree = dm + 1 := ⟨R.natDegree - 1, by
          rcases Nat.lt_or_ge R.natDegree 2 with h | h
          · -- d < 2 ⇒ d ≤ 1; need d ≥ 1: R.natDegree ≥ natDegreeY H ≥ 1
            have : 1 ≤ R.natDegree := by rw [← hdY]; rw [← hdH] at *; omega
            omega
          · omega⟩
        rw [hdmeq] at hkey ⊢
        rw [show dm + 1 - 1 = dm by omega]
        nlinarith [hkey, hwb_le, hgap, Nat.mul_le_mul_right ΛW hwb_le]
      exact hfin



/-- The cleared `(t+1)`-st Hensel residual `henselCoeffResidual · Ddiv` (with `Ddiv` the global
clearing denominator `W^{t+2}·η^{E-1}·W^{d-2}`) is regular with sharp `Λ`-weight at most
`numeratorShapeSharp R H D (t+1)`, given that every previous numerator `βseq s` (`s ≤ t`) has
sharp weight `≤ numeratorShapeSharp R H D s`.

This is the quantitative (weight-tracking) heart of [BCIKS20] A.4 (pp. 52–53): it is the `Λ`-graded
analogue of `henselCoeffResidual_regular_after_clearing`, refining mere regularity to the sharp
per-step weight budget that telescopes linearly in `t`. -/
lemma henselClearedResidual_weight (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree) {D : ℕ}
    (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R))
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (αseq : ℕ → 𝕃 H) (βseq : ℕ → 𝒪 H)
    (hα0 : αseq 0 = functionFieldT (H := H) /
      liftToFunctionField (H := H) H.leadingCoeff)
    (_hroot : evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq) = 0)
    (hshape : HasNumeratorShape x₀ R H hHyp αseq βseq)
    (t : ℕ)
    (ihAll : ∀ s ≤ t,
      RegularWeightLe hH (embeddingOf𝒪Into𝕃 H (βseq s)) D (numeratorShapeSharp R H D s)) :
    RegularWeightLe hH
      (henselCoeffResidual x₀ R H αseq t *
        (liftToFunctionField (H := H) H.leadingCoeff ^ (t + 1 + 1) *
          (embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp)) ^ (henselDenominatorExponent (t + 1) - 1) *
          liftToFunctionField (H := H) H.leadingCoeff ^ (R.natDegree - 2)))
      D (numeratorShapeSharp R H D (t + 1)) := by
  classical
  set αtrunc : ℕ → 𝕃 H := fun i => if i ≤ t then αseq i else 0 with hαtrunc
  rw [henselCoeffResidual_eq_trunc x₀ R H αseq hα0 t]
  -- shape of αtrunc
  have hshapeT : ∀ i : ℕ, αtrunc i =
      if h : i ≤ t then
        embeddingOf𝒪Into𝕃 H (βseq i) /
          (liftToFunctionField (H := H) H.leadingCoeff ^ (i + 1) *
            (embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp)) ^ henselDenominatorExponent i)
      else 0 := by
    intro i
    by_cases h : i ≤ t
    · have hval : αtrunc i = αseq i := by rw [hαtrunc]; simp only [if_pos h]
      rw [hval, dif_pos h]
      have := hshape i
      unfold alphaOfNumerators at this
      rw [← this]
    · have hval : αtrunc i = 0 := by rw [hαtrunc]; simp only [if_neg h]
      rw [hval, dif_neg h]
  -- ihNum: clearing each αtrunc
  have ihNum : ∀ i, i ≤ t →
      RegularWeightLe hH
        (αtrunc i * (liftToFunctionField (H := H) H.leadingCoeff ^ (i + 1) *
          (embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp)) ^ henselDenominatorExponent i))
        D (numeratorShapeSharp R H D i) := by
    intro i hi
    have hW : liftToFunctionField (H := H) H.leadingCoeff ≠ 0 :=
      liftToFunctionField_leadingCoeff_ne_zero (H := H)
    have hetane : embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp) ≠ 0 := by
      rw [embeddingOf𝒪Into𝕃_xi]
      exact mul_ne_zero (pow_ne_zero _ hW) (zeta_ne_zero_of_hypotheses x₀ R H hHyp)
    rw [hshapeT i, dif_pos hi,
      div_mul_cancel₀ _ (mul_ne_zero (pow_ne_zero _ hW) (pow_ne_zero _ hetane))]
    exact ihAll i hi
  have hαzero : ∀ i, t < i → αtrunc i = 0 := by
    intro i hi; simp only [hαtrunc, if_neg (show ¬ i ≤ t by omega)]
  -- expand evalRAtPowerSeries
  unfold evalRAtPowerSeries
  rw [Polynomial.eval₂_eq_sum_range, map_sum, Finset.sum_mul]
  apply RegularWeightLe.sum _ _ hD_H
  intro j hj
  exact henselClearedTerm_weight x₀ R H hHyp hH hD_H hD_R hD_Rx0 hRdeg t αtrunc ihNum hαzero j hj

/-- Sharp `Λ`-weight bound on every Hensel numerator: `Λ(βₜ) ≤ numeratorShapeSharp R H D t`,
i.e. `1 + (t+1)(D-dH) + eₜ(dY-1)(D-dH+1)` ([BCIKS20] A.4, pp. 52–53).  Proved by strong induction,
the successor step being `henselClearedResidual_weight` together with the identity
`embeddingOf𝒪Into𝕃 (βₜ₊₁) = -(henselCoeffResidual · Ddiv)`.

The hypothesis `2 ≤ dY` is [BCIKS20]'s own standing assumption in A.4, where `ξ = W^{d-2}·ζ` is
asserted to lie in `𝒪`: for `d < 2` that expression carries a negative power of `W` and the
claim's `Λ(ξ) ≤ (D-1) + (d-2)Λ(W) ≤ (d-1)(D-dH+1)` degenerates to `Λ(ξ) ≤ 0`, which fails unless
`Λ(W) = D - dH` exactly.  In Lean the truncated subtraction silently reads `W^{d-2}` as `1` for
`d ≤ 2`, so without this hypothesis the statement would be *stronger* than the paper's and false:
with `dY = dH = 1` one has `ξ = ζ` of weight up to `D - 1 > 0`, while `(dY-1) = 0` erases the
`ξ`-contribution from `numeratorShapeSharp`.  Accordingly `xi_weight_le` also assumes `2 ≤ dY`. -/
theorem numerator_shape_weight_sharp (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (αseq : ℕ → 𝕃 H) (βseq : ℕ → 𝒪 H)
    (hα0 : αseq 0 = functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
    (hroot : evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq) = 0)
    (hshape : HasNumeratorShape x₀ R H hHyp αseq βseq) :
    ∀ t : ℕ, RegularWeightLe hH (embeddingOf𝒪Into𝕃 H (βseq t)) D
      (numeratorShapeSharp R H D t) := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    cases t with
    | zero =>
        -- `β₀ = X`; sharp(0) = 1 + (D-dH), and `Λ(X) ≤ D + 1 - dH`.
        have hβ0 := beta_zero_eq_X_of_shape x₀ R H hHyp hH hD_H hD_R αseq βseq hα0 hroot hshape
        refine ⟨βseq 0, rfl, ?_⟩
        rw [hβ0]
        refine (regularWeight_mk_le (H := H) (D := D) hD_H hH (Polynomial.X : F[X][Y])).trans ?_
        have hX : weight (Polynomial.X : F[X][Y]) H D ≤
            (WithBot.some (D + 1 - Bivariate.natDegreeY H) : WithBot ℕ) := by
          simpa only [pow_one, one_mul] using (weight_X_pow_le (H := H) (D := D) (k := 1))
        refine hX.trans ?_
        rw [WithBot.coe_le_coe]
        unfold numeratorShapeSharp
        rw [henselDenominatorExponent_zero]
        omega
    | succ t =>
        -- Successor: bridge `embedding βseq(t+1) = -(residual · Ddiv)`, then use the weight core.
        have hD_Rx0 : D ≥ Bivariate.totalDegree (Bivariate.evalX (Polynomial.C x₀) R) :=
          evalX_totalDegree_le_of_coeff_bound x₀ R hD_R
        have hbridge : embeddingOf𝒪Into𝕃 H (βseq (t + 1)) =
            -(henselCoeffResidual x₀ R H αseq t *
              (liftToFunctionField (H := H) H.leadingCoeff ^ (t + 1 + 1) *
                (embeddingOf𝒪Into𝕃 H (xi x₀ R H hHyp)) ^ (henselDenominatorExponent (t + 1) - 1) *
                liftToFunctionField (H := H) H.leadingCoeff ^ (R.natDegree - 2))) := by
          exact betaSucc_eq_neg_clearedResidual x₀ R H hHyp αseq βseq hroot hshape t
        rw [hbridge]
        refine RegularWeightLe.neg ?_
        exact henselClearedResidual_weight x₀ R H hHyp hH hD_H hD_R hD_Rx0 hRdeg αseq βseq hα0
          hroot hshape t (fun s hs => ih s (Nat.lt_succ_of_le hs))

theorem numerator_shape_weight_bound (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    (αseq : ℕ → 𝕃 H) (βseq : ℕ → 𝒪 H)
    (hα0 : αseq 0 = functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff)
    (hroot : evalRAtPowerSeries x₀ H R (gammaFromAlpha H αseq) = 0)
    (hshape : HasNumeratorShape x₀ R H hHyp αseq βseq) :
    ∀ t : ℕ,
      regularWeight hH (βseq t) D ≤
        (WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) : WithBot ℕ) := by
  intro t
  have hsharp :=
    numerator_shape_weight_sharp x₀ R H hHyp hH hD_H hD_R hRdeg αseq βseq hα0 hroot hshape t
  refine (regularWeight_le_of_regularWeightLe (βseq t) hsharp).trans ?_
  rw [WithBot.coe_le_coe]
  exact numeratorShapeSharp_le_loose x₀ R H hHyp hH hD_H t

/-- A sequence with the Hensel-lift semantics of Claim A.2 has the numerator shape witnessed by
its own induced coefficients: `αₜ := βₜ / (W^{t+1} ξ^{eₜ})` is the tautological choice, so
`HasNumeratorShape` holds by `rfl` and `IsHenselNumeratorSequence` supplies `hα0`/`hroot`.

This is the bridge that lets the weight bounds be stated about *any* Hensel numerator sequence,
rather than being bundled into the existential that defines one. -/
lemma hasNumeratorShape_alphaOfNumerators (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (βseq : ℕ → 𝒪 H) :
    HasNumeratorShape x₀ R H hHyp (alphaOfNumerators x₀ R H hHyp βseq) βseq :=
  fun _ => rfl

/-- The **sharp** Claim A.2 weight bound of [BCIKS20] A.4, for an arbitrary Hensel numerator
sequence: `Λ(βₜ) ≤ 1 + (t+1)Λ(W) + eₜΛ(ξ)` (with the paper's bounds `Λ(W) ≤ D - dH` and
`Λ(ξ) ≤ (dY-1)(D - dH + 1)` substituted).

This is the form consumed by [BCIKS20] Claim 5.10, which needs the bound to telescope across
`t = 0, …, k`:
`max_t (Λ(βₜ) + (k-t)Λ(W) + (e_k-eₜ)Λ(ξ)) = 1 + (k+1)Λ(W) + e_kΛ(ξ) ≤ (2k+1)dD`.
The loose bound `numerator_shape_weight_bound` does *not* suffice there. -/
theorem hensel_numerator_weight_sharp_le (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    {βseq : ℕ → 𝒪 H} (hβ : IsHenselNumeratorSequence x₀ R H hHyp βseq) :
    ∀ t : ℕ,
      regularWeight hH (βseq t) D ≤
        (WithBot.some (numeratorShapeSharp R H D t) : WithBot ℕ) := by
  intro t
  exact regularWeight_le_of_regularWeightLe (βseq t)
    (numerator_shape_weight_sharp x₀ R H hHyp hH hD_H hD_R hRdeg
      (alphaOfNumerators x₀ R H hHyp βseq) βseq hβ.1 hβ.2
      (hasNumeratorShape_alphaOfNumerators x₀ R H hHyp βseq) t)

/-- The loose Claim A.2 weight bound `Λ(βₜ) ≤ (2t+1)·dY·D` of [BCIKS20] A.4, for an arbitrary
Hensel numerator sequence.  Weakening of `hensel_numerator_weight_sharp_le`. -/
theorem hensel_numerator_weight_le (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [_H_irreducible : Fact (Irreducible H)] [_H_natDegree_pos : Fact (0 < H.natDegree)]
    (hHyp : Hypotheses x₀ R H) (hH : 0 < H.natDegree)
    {D : ℕ} (hD_H : Bivariate.totalDegree H ≤ D)
    (hD_R : ∀ i ∈ R.support, Bivariate.totalDegree (R.coeff i) + i ≤ D)
    (hRdeg : 2 ≤ Bivariate.natDegreeY R)
    {βseq : ℕ → 𝒪 H} (hβ : IsHenselNumeratorSequence x₀ R H hHyp βseq) :
    ∀ t : ℕ,
      regularWeight hH (βseq t) D ≤
        (WithBot.some ((2 * t + 1) * Bivariate.natDegreeY R * D) : WithBot ℕ) := by
  intro t
  refine (hensel_numerator_weight_sharp_le x₀ R H hHyp hH hD_H hD_R hRdeg hβ t).trans ?_
  rw [WithBot.coe_le_coe]
  exact numeratorShapeSharp_le_loose x₀ R H hHyp hH hD_H t


end HenselNumerators
end
end RationalFunctions
