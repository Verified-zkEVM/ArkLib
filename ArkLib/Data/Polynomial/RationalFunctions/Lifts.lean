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
import ArkLib.Data.Polynomial.RationalFunctions.FunctionField
/-!
# Regular Lifts into Function Fields

Appendix A.1 of [BCIKS20]: the coefficient and bivariate lifts `F[Z] → 𝕃 H` and
`F[Z][Y] → 𝕃 H`, the image `T` of the polynomial variable, and the denominator-clearing lemmas
that exhibit `W^k · P(T/W)` as a regular element — the tool A.4 uses to keep the Hensel-lift
coefficients inside `𝒪`.

## References

[BCIKS20] Eli Ben-Sasson, Dan Carmon, Yuval Ishai, Swastik Kopparty, and Shubhangi Saraf.
  Proximity gaps for Reed-Solomon codes. In 2020 IEEE 61st Annual Symposium on Foundations of
  Computer Science (FOCS), 2020. Full paper: https://eprint.iacr.org/2020/654,
  version 20210703:203025.

-/


open Polynomial Polynomial.Bivariate ToRatFunc Ideal

namespace RationalFunctions
section RegularLifts

variable {F : Type} [CommRing F] [IsDomain F]

/-- The embedding of the coefficients of a bivariate polynomial into the bivariate polynomial ring
with rational coefficients. -/
noncomputable def coeffAsRatFunc : F[X] →+* Polynomial (RatFunc F) :=
  RingHom.comp bivPolyHom Polynomial.C

/-- The embedding of coefficient polynomials into the function field `𝕃`. -/
noncomputable def liftToFunctionField {H : F[X][Y]} : F[X] →+* 𝕃 H :=
  RingHom.comp (Ideal.Quotient.mk (Ideal.span {monicizeRatFunc H})) coeffAsRatFunc

/-- The embedding of bivariate polynomials into the function field `𝕃`. -/
noncomputable def liftBivariate {H : F[X][Y]} : F[X][Y] →+* 𝕃 H :=
  RingHom.comp (Ideal.Quotient.mk (Ideal.span {monicizeRatFunc H})) bivPolyHom

/-- The image of the polynomial variable `T` in the function field `𝕃 H`. -/
noncomputable def functionFieldT {H : F[X][Y]} : 𝕃 H :=
  Ideal.Quotient.mk (Ideal.span {monicizeRatFunc H}) Polynomial.X

/-- Quotient constructors in `𝒪` embed by applying the bivariate lift. -/
@[simp]
lemma embeddingOf𝒪Into𝕃_mk (H : F[X][Y]) (p : F[X][Y]) :
    embeddingOf𝒪Into𝕃 H (Ideal.Quotient.mk (Ideal.span {monicize H}) p : 𝒪 H) =
      liftBivariate (H := H) p := by
  rfl

/-- Every bivariate polynomial representative gives a regular element of the function field. -/
lemma regular_liftBivariate (H : F[X][Y]) (p : F[X][Y]) :
    ∃ pre : 𝒪 H, embeddingOf𝒪Into𝕃 H pre = liftBivariate (H := H) p :=
  ⟨Ideal.Quotient.mk (Ideal.span {monicize H}) p, by simp⟩

/-- Bivariate-polynomial images are regular elements of the function field. -/
lemma regularElementsSet_liftBivariate (H : F[X][Y]) (p : F[X][Y]) :
    liftBivariate (H := H) p ∈ regularElementsSet H := by
  rcases regular_liftBivariate H p with ⟨pre, hpre⟩
  exact ⟨pre, hpre.symm⟩


/-- Coefficient-polynomial images are regular elements of the function field. -/
lemma regularElementsSet_liftToFunctionField (H : F[X][Y]) (p : F[X]) :
    liftToFunctionField (H := H) p ∈ regularElementsSet H := by
  change liftBivariate (H := H) (Polynomial.C p) ∈ regularElementsSet H
  exact regularElementsSet_liftBivariate H (Polynomial.C p)

/-- Nonzero coefficient polynomials remain nonzero after embedding into the function field. -/
lemma liftToFunctionField_ne_zero {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {p : F[X]} (hp : p ≠ 0) :
    liftToFunctionField (H := H) p ≠ 0 := by
  intro hzero
  have hmem :
      coeffAsRatFunc p ∈ Ideal.span ({monicizeRatFunc H} : Set (Polynomial (RatFunc F))) := by
    simpa [liftToFunctionField] using (Ideal.Quotient.eq_zero_iff_mem.mp hzero)
  rw [Ideal.mem_span_singleton] at hmem
  have hp_map : univPolyHom (F := F) p ≠ 0 := by
    intro hp_zero
    exact hp (univPolyHom_injective (F := F) (by simpa using hp_zero))
  have hunit : IsUnit (coeffAsRatFunc p) := by
    have hunitC : IsUnit (Polynomial.C (univPolyHom (F := F) p) :
        Polynomial (RatFunc F)) :=
      Polynomial.isUnit_C.mpr (Ne.isUnit hp_map)
    simpa only [coeffAsRatFunc, RingHom.comp_apply, ToRatFunc.bivPolyHom,
      Polynomial.coe_mapRingHom, Polynomial.map_C] using hunitC
  exact (irreducible_monicizeRatFunc_of_natDegree_pos H_natDegree_pos.out
    H_irreducible.out).not_dvd_isUnit hunit hmem

/-- The leading coefficient `W` of a positive-`Y`-degree `H` is nonzero in the function field. -/
lemma liftToFunctionField_leadingCoeff_ne_zero {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)] :
    liftToFunctionField (H := H) H.leadingCoeff ≠ 0 := by
  exact liftToFunctionField_ne_zero
    (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt H_natDegree_pos.out))

/-- If `q ∣ p` in `F[X]`, then `p / q` is regular after embedding into `𝕃`. -/
lemma regularElementsSet_liftToFunctionField_div_of_dvd {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {p q : F[X]} (hq : q ≠ 0) (hdiv : q ∣ p) :
    liftToFunctionField (H := H) p / liftToFunctionField (H := H) q ∈ regularElementsSet H := by
  rcases hdiv with ⟨r, rfl⟩
  have hq_lift : liftToFunctionField (H := H) q ≠ 0 := liftToFunctionField_ne_zero hq
  have heq :
      liftToFunctionField (H := H) (q * r) / liftToFunctionField (H := H) q =
        liftToFunctionField (H := H) r := by
    rw [map_mul]
    field_simp [hq_lift]
  rw [heq]
  exact regularElementsSet_liftToFunctionField H r

/-- If `W = H.leadingCoeff` divides `p`, then `p / W` is regular after embedding into `𝕃`. -/
lemma regularElementsSet_liftToFunctionField_div_leadingCoeff_of_dvd {F : Type} [Field F]
    {H : F[X][Y]} [H_irreducible : Fact (Irreducible H)]
    [H_natDegree_pos : Fact (0 < H.natDegree)] {p : F[X]}
    (hdiv : H.leadingCoeff ∣ p) :
    liftToFunctionField (H := H) p / liftToFunctionField (H := H) H.leadingCoeff ∈
      regularElementsSet H := by
  exact regularElementsSet_liftToFunctionField_div_of_dvd
    (Polynomial.leadingCoeff_ne_zero.mpr (Polynomial.ne_zero_of_natDegree_gt H_natDegree_pos.out))
    hdiv

private lemma mul_pow_mul_div_pow_eq_lower {K : Type} [Field K] {W T a : K}
    (hW : W ≠ 0) {k i : ℕ} (hi : i ≤ k) :
    W ^ k * (a * (T / W) ^ i) = a * (T ^ i * W ^ (k - i)) := by
  rw [div_pow]
  have hk : k = k - i + i := (Nat.sub_add_cancel hi).symm
  calc
    W ^ k * (a * (T ^ i / W ^ i)) = a * (T ^ i * (W ^ k / W ^ i)) := by
      ring
    _ = a * (T ^ i * W ^ (k - i)) := by
      rw [hk, pow_add]
      field_simp [hW]
      have hsub : k - i + i - i = k - i := by omega
      rw [hsub]

private lemma mul_pow_mul_div_pow_succ_eq_top {K : Type} [Field K] {W T a : K}
    (hW : W ≠ 0) (k : ℕ) :
    W ^ k * (a * (T / W) ^ (k + 1)) = (a / W) * T ^ (k + 1) := by
  rw [div_pow, pow_succ]
  field_simp [hW]
  ring

/-- Clearing denominators in `W^k · P(T/W)` as an explicit sum: if `P.natDegree ≤ k + 1`, then
`W^k * eval₂ lift (T/W) P` decomposes into a low-degree polynomial sum plus a single
`(P.coeff(k+1)/W) · T^(k+1)` term. The divisibility `W ∣ P.coeff(k+1)` is not needed here -
the formula holds in `𝕃 H` directly via field division. -/
lemma leadingCoeff_pow_mul_eval₂_div_eq_sum {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {P : F[X][Y]} {k : ℕ} (hP : P.natDegree ≤ k + 1) :
    liftToFunctionField (H := H) H.leadingCoeff ^ k *
      Polynomial.eval₂ liftToFunctionField
        (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) P =
      (∑ i ∈ Finset.range (k + 1),
          liftToFunctionField (H := H) (P.coeff i) *
            (functionFieldT (H := H) ^ i *
              liftToFunctionField (H := H) H.leadingCoeff ^ (k - i))) +
        (liftToFunctionField (H := H) (P.coeff (k + 1)) /
            liftToFunctionField (H := H) H.leadingCoeff) *
          functionFieldT (H := H) ^ (k + 1) := by
  set W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff with hW_def
  set T : 𝕃 H := functionFieldT (H := H) with hT_def
  have hW : W ≠ 0 := by
    simpa [W] using (liftToFunctionField_leadingCoeff_ne_zero (H := H))
  have hP_lt : P.natDegree < k + 2 := by omega
  rw [Polynomial.eval₂_eq_sum_range' liftToFunctionField hP_lt (T / W)]
  rw [Finset.mul_sum]
  rw [show k + 2 = k + 1 + 1 by omega, Finset.sum_range_succ]
  congr 1
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi_le : i ≤ k := by
      have hi_lt := Finset.mem_range.mp hi
      omega
    exact mul_pow_mul_div_pow_eq_lower (W := W) (T := T)
      (a := liftToFunctionField (H := H) (P.coeff i)) hW hi_le
  · exact mul_pow_mul_div_pow_succ_eq_top (W := W) (T := T)
      (a := liftToFunctionField (H := H) (P.coeff (k + 1))) hW k

/-- The bivariate variable maps to the function-field variable `T`. -/
@[simp]
lemma liftBivariate_X {H : F[X][Y]} :
    liftBivariate (H := H) (Polynomial.X : F[X][Y]) = functionFieldT (H := H) := by
  simp [liftBivariate, functionFieldT, bivPolyHom]

/-- The function-field variable `T` is regular. -/
lemma regularElementsSet_functionFieldT (H : F[X][Y]) :
    functionFieldT (H := H) ∈ regularElementsSet H := by
  simpa using regularElementsSet_liftBivariate H (Polynomial.X : F[X][Y])

/-- A linear polynomial evaluated at `T / W` is regular when its linear coefficient is divisible by
`W = H.leadingCoeff`. -/
lemma regularElementsSet_eval₂_linear_of_coeff_one_dvd {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {P : F[X][Y]} (hP : P.natDegree ≤ 1) (hdiv : H.leadingCoeff ∣ P.coeff 1) :
    Polynomial.eval₂ liftToFunctionField
      (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) P ∈
      regularElementsSet H := by
  rw [Polynomial.eq_X_add_C_of_natDegree_le_one hP]
  simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_C,
    Polynomial.eval₂_X]
  have hterm :
      liftToFunctionField (H := H) (P.coeff 1) *
          (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) =
        (liftToFunctionField (H := H) (P.coeff 1) /
            liftToFunctionField (H := H) H.leadingCoeff) * functionFieldT (H := H) := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    ring
  rw [hterm]
  exact regularElementsSet_add
    (regularElementsSet_mul
      (regularElementsSet_liftToFunctionField_div_leadingCoeff_of_dvd hdiv)
      (regularElementsSet_functionFieldT H))
    (regularElementsSet_liftToFunctionField H (P.coeff 0))

/-- Clearing denominators in `P(T / W)`: if `P` has degree at most `k + 1` and its top
coefficient is divisible by `W = H.leadingCoeff`, then `W^k * P(T/W)` is regular. -/
lemma regularElementsSet_mul_pow_eval₂_div_of_natDegree_le_succ_of_coeff_succ_dvd
    {F : Type} [Field F] {H : F[X][Y]}
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]
    {P : F[X][Y]} {k : ℕ} (hP : P.natDegree ≤ k + 1)
    (hdiv : H.leadingCoeff ∣ P.coeff (k + 1)) :
    liftToFunctionField (H := H) H.leadingCoeff ^ k *
      Polynomial.eval₂ liftToFunctionField
        (functionFieldT (H := H) / liftToFunctionField (H := H) H.leadingCoeff) P ∈
      regularElementsSet H := by
  let W : 𝕃 H := liftToFunctionField (H := H) H.leadingCoeff
  let T : 𝕃 H := functionFieldT (H := H)
  have hW : W ≠ 0 := by
    simpa [W] using (liftToFunctionField_leadingCoeff_ne_zero (H := H))
  have hP_lt : P.natDegree < k + 2 := by omega
  change W ^ k * Polynomial.eval₂ liftToFunctionField (T / W) P ∈ regularElementsSet H
  rw [Polynomial.eval₂_eq_sum_range' liftToFunctionField hP_lt (T / W)]
  rw [Finset.mul_sum]
  rw [show k + 2 = k + 1 + 1 by omega, Finset.sum_range_succ]
  refine regularElementsSet_add ?_ ?_
  · refine regularElementsSet_sum (Finset.range (k + 1)) ?_
    intro i hi
    have hi_lt : i < k + 1 := Finset.mem_range.mp hi
    have hi_le : i ≤ k := by omega
    rw [mul_pow_mul_div_pow_eq_lower (W := W) (T := T)
      (a := liftToFunctionField (H := H) (P.coeff i)) hW hi_le]
    exact regularElementsSet_mul
      (regularElementsSet_liftToFunctionField H (P.coeff i))
      (regularElementsSet_mul
        (by simpa [T] using regularElementsSet_pow (regularElementsSet_functionFieldT H) i)
        (by
          simpa [W] using
            regularElementsSet_pow
              (regularElementsSet_liftToFunctionField H H.leadingCoeff) (k - i)))
  · rw [mul_pow_mul_div_pow_succ_eq_top (W := W) (T := T)
      (a := liftToFunctionField (H := H) (P.coeff (k + 1))) hW k]
    exact regularElementsSet_mul
      (by
        simpa [W] using
          regularElementsSet_liftToFunctionField_div_leadingCoeff_of_dvd (H := H) hdiv)
      (by simpa [T] using regularElementsSet_pow (regularElementsSet_functionFieldT H) (k + 1))

/-- Constant bivariate polynomials map through the coefficient embedding. -/
@[simp]
lemma liftBivariate_C {H : F[X][Y]} (p : F[X]) :
    liftBivariate (H := H) (Polynomial.C p : F[X][Y]) = liftToFunctionField (H := H) p := by
  rfl

/-- The embedding of scalars into the function field `𝕃`. -/
noncomputable def fieldTo𝕃 {H : F[X][Y]} : F →+* 𝕃 H :=
  RingHom.comp liftToFunctionField Polynomial.C

/-- View a bivariate polynomial as a power series over `𝕃 H` by lifting its coefficients. -/
noncomputable def polyToPowerSeries𝕃 (H : F[X][Y]) (P : F[X][Y]) : PowerSeries (𝕃 H) :=
  PowerSeries.mk <| fun n => liftToFunctionField (P.coeff n)

section RationalSubstitutionOfQuotients

variable {F : Type} [Field F] {H : F[X][Y]}


/-- The extension of the rational substitution `π_z` from `𝒪` to those elements of `𝕃` for which
`z` is not a pole: elements of the form `β / C(Z)` with `β ∈ 𝒪 H` and `C(z) ≠ 0`, sent to
`π_z(β) / C(z)`.

The value is given on the *presentation* `(β, C)`; `piZOfDiv_congr` shows it depends only on the
quotient `β / C` in `𝕃`, so this really is a function on that subring of `𝕃`.  Hensel-lift
coefficients have exactly this shape — their denominators are powers of `W` and `ξ` — which is why
the extension is needed. -/
noncomputable def piZOfDiv {H : F[X][Y]} (z : F) (root : rationalRoot (monicize H) z)
    (β : 𝒪 H) (C : F[X]) : F :=
  piZ z root β / C.eval z

/-- `piZOfDiv` extends `piZ`: denominator `1` gives the original substitution. -/
@[simp]
lemma piZOfDiv_one {H : F[X][Y]} (z : F) (root : rationalRoot (monicize H) z) (β : 𝒪 H) :
    piZOfDiv z root β 1 = piZ z root β := by
  simp [piZOfDiv]

/-- The substitution of a coefficient polynomial is its evaluation. -/
lemma piZ_mk_C {H : F[X][Y]} (z : F) (root : rationalRoot (monicize H) z) (C : F[X]) :
    piZ z root (Ideal.Quotient.mk (Ideal.span {monicize H}) (Polynomial.C C) : 𝒪 H) =
      C.eval z := by
  simp [piZ, piZLift, Polynomial.evalEval]

variable [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (0 < H.natDegree)]

/-- `piZOfDiv` is well defined on `𝕃`: it depends only on the quotient `β / C`, not on the chosen
presentation.  This is what makes the extension of A.3 legitimate. -/
lemma piZOfDiv_congr (z : F) (root : rationalRoot (monicize H) z) {β β' : 𝒪 H} {C C' : F[X]}
    (hC : C ≠ 0) (hC' : C' ≠ 0) (hCz : C.eval z ≠ 0) (hC'z : C'.eval z ≠ 0)
    (heq : embeddingOf𝒪Into𝕃 H β / liftToFunctionField (H := H) C =
      embeddingOf𝒪Into𝕃 H β' / liftToFunctionField (H := H) C') :
    piZOfDiv z root β C = piZOfDiv z root β' C' := by
  -- clear denominators in `𝕃`
  have hCl : liftToFunctionField (H := H) C ≠ 0 := liftToFunctionField_ne_zero hC
  have hC'l : liftToFunctionField (H := H) C' ≠ 0 := liftToFunctionField_ne_zero hC'
  rw [div_eq_div_iff hCl hC'l] at heq
  -- rewrite the two coefficient lifts as embedded `𝒪`-elements, then use injectivity
  set bC : 𝒪 H := Ideal.Quotient.mk (Ideal.span {monicize H}) (Polynomial.C C) with hbC
  set bC' : 𝒪 H := Ideal.Quotient.mk (Ideal.span {monicize H}) (Polynomial.C C') with hbC'
  have hbCe : embeddingOf𝒪Into𝕃 H bC = liftToFunctionField (H := H) C := by
    rw [hbC, embeddingOf𝒪Into𝕃_mk, liftBivariate_C]
  have hbC'e : embeddingOf𝒪Into𝕃 H bC' = liftToFunctionField (H := H) C' := by
    rw [hbC', embeddingOf𝒪Into𝕃_mk, liftBivariate_C]
  rw [← hbC'e, ← hbCe, ← map_mul, ← map_mul] at heq
  have hmul : β * bC' = β' * bC :=
    embeddingOf𝒪Into𝕃_injective H_natDegree_pos.out heq
  -- apply the substitution and divide
  have hsub := congrArg (piZ z root) hmul
  rw [map_mul, map_mul, hbC, hbC', piZ_mk_C, piZ_mk_C] at hsub
  rw [piZOfDiv, piZOfDiv, div_eq_div_iff hCz hC'z]
  exact hsub

omit H_irreducible H_natDegree_pos in
/-- A quotient with a nonvanishing denominator vanishes under `π_z` exactly when its numerator
does.  Combined with `embedding_eq_zero_of_many_rational_roots`, this is how a bound on the number
of substitutions killing `β / C` becomes a bound on `Λ(β)`. -/
@[simp]
lemma piZOfDiv_eq_zero_iff (z : F) (root : rationalRoot (monicize H) z) (β : 𝒪 H) {C : F[X]}
    (hCz : C.eval z ≠ 0) :
    piZOfDiv z root β C = 0 ↔ piZ z root β = 0 := by
  rw [piZOfDiv, div_eq_zero_iff]
  simp [hCz]

end RationalSubstitutionOfQuotients

end RegularLifts

end RationalFunctions
