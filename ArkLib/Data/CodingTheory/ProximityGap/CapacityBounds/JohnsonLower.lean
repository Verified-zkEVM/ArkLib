/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.Basic.Entropy
import ArkLib.Data.CodingTheory.HammingBallVolume
import ArkLib.Data.CodingTheory.SubspaceDesign
import Mathlib.Analysis.SpecialFunctions.Pow.Real

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.LinearAlgebra.Pi
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Algebra.ZMod
import ArkLib.Data.CodingTheory.Basic.RelativeDistance
import ArkLib.Data.CodingTheory.ListDecodability.Bounds.KKH26

/-!
# Reed--Solomon lower bound at the Johnson radius

This file proves the characteristic-two BCHKS25 construction using binary graph subspaces,
linearized polynomials, and Schwartz--Zippel.

## Main result

- `exists_rs_epsCa_large_at_johnson_radius` is [BCHKS25, Corollary 1.7].

## References

- [BCHKS25] Corollary 1.7.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal
open CoreDefinitions ProximityGap


section ReedSolomon

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

private def IsBinaryLinearized {K : Type} [Field K] (P : Polynomial K) : Prop :=
  ∀ n ∈ P.support, ∃ i : ℕ, n = 2 ^ i

open scoped NNReal in
private noncomputable def agreementCard_gt_twoMul_of_lt_sevenEighths
    {ι : Type} [Fintype ι]
    (d : ℕ) (hd : 0 < d) (δ : ℝ≥0) (S : Finset ι)
    (hcard : Fintype.card ι = 16 * d)
    (hS : (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0))
    (hδ : (δ : ℝ) < 7 / 8) :
    2 * d < S.card := by
  have hδle : δ ≤ 1 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    linarith
  have hSco := NNReal.coe_le_coe.mpr hS
  rw [NNReal.coe_mul, NNReal.coe_sub hδle] at hSco
  rw [hcard] at hSco
  push_cast at hSco
  by_contra hnot
  have hle : S.card ≤ 2 * d := Nat.le_of_not_gt hnot
  have hleR : (S.card : ℝ) ≤ ((2 * d : ℕ) : ℝ) := by
    exact_mod_cast hle
  push_cast at hleR
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  nlinarith

private def binaryBasisVector {b : ℕ} (i : Fin b) : Fin b → ZMod 2 :=
  fun i' => if i' = i then 1 else 0

open scoped BigOperators in
private noncomputable def binaryBasisVector_sum {b : ℕ}
    (x : Fin b → ZMod 2) :
    (∑ i : Fin b, x i • binaryBasisVector i) = x := by
  classical
  funext j
  simp [binaryBasisVector]

private noncomputable def binaryFunctionalKerNatCard {b : ℕ}
    (h : (Fin b → ZMod 2) →ₗ[ZMod 2] ZMod 2) (hh : h ≠ 0) :
    Nat.card (LinearMap.ker h) = 2 ^ (b - 1) := by
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hh
  have hamb : Module.finrank (ZMod 2) (Fin b → ZMod 2) = b := by
    simp
  rw [hamb] at hdim
  have hker : Module.finrank (ZMod 2) (LinearMap.ker h) = b - 1 := by omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker h), hker]
  norm_num [ZMod.card]

private noncomputable def binaryFunctionalFiberCard {b : ℕ}
    (h : (Fin b → ZMod 2) →ₗ[ZMod 2] ZMod 2) (hh : h ≠ 0)
    (z : ZMod 2) : Fintype.card {x : Fin b → ZMod 2 // h x = z} = 2 ^ (b - 1) := by
  have hsurj : Function.Surjective h := LinearMap.surjective hh
  rcases hsurj z with ⟨a, ha⟩
  rw [← Nat.card_eq_fintype_card]
  calc
    Nat.card {x : Fin b → ZMod 2 // h x = z} =
        Nat.card (LinearMap.ker h) := by
      apply Nat.card_congr
      exact
        { toFun := fun x => ⟨x.1 - a, by
              change h (x.1 - a) = 0
              rw [LinearMap.map_sub, x.2, ha, sub_self]⟩
          invFun := fun x => ⟨x.1 + a, by
              rw [LinearMap.map_add, x.2, ha, zero_add]⟩
          left_inv := by
            intro x
            apply Subtype.ext
            simp only [sub_add_cancel]
          right_inv := by
            intro x
            apply Subtype.ext
            simp only [add_sub_cancel_right] }
    _ = 2 ^ (b - 1) := binaryFunctionalKerNatCard h hh

open scoped BigOperators in
private noncomputable def binaryFunctionalRootPolynomial {b : ℕ}
    (h : (Fin b → ZMod 2) →ₗ[ZMod 2] ZMod 2) : Polynomial (ZMod 2) := by
  classical
  exact ∏ x : Fin b → ZMod 2, (Polynomial.X - Polynomial.C (h x))

open scoped BigOperators in
private noncomputable def binaryFunctionalRootPolynomialOfNeZero {b : ℕ}
    (h : (Fin b → ZMod 2) →ₗ[ZMod 2] ZMod 2) (hh : h ≠ 0) :
    binaryFunctionalRootPolynomial h =
      Polynomial.X ^ (2 ^ (b - 1)) *
        (Polynomial.X - Polynomial.C 1) ^ (2 ^ (b - 1)) := by
  classical
  unfold binaryFunctionalRootPolynomial
  calc
    Finset.univ.prod (fun x : (Fin b → ZMod 2) =>
        Polynomial.X - Polynomial.C (h x)) =
      Finset.univ.prod (fun z : ZMod 2 =>
        Finset.univ.prod (fun _x : {x : Fin b → ZMod 2 // h x = z} =>
          Polynomial.X - Polynomial.C z)) := by
      symm
      exact Fintype.prod_fiberwise' h (fun z => Polynomial.X - Polynomial.C z)
    _ = Finset.univ.prod (fun z : ZMod 2 =>
        (Polynomial.X - Polynomial.C z) ^ (2 ^ (b - 1))) := by
      apply Finset.prod_congr rfl
      intro z hz
      rw [Finset.prod_const, Finset.card_univ, binaryFunctionalFiberCard h hh z]
    _ = Polynomial.X ^ (2 ^ (b - 1)) *
        (Polynomial.X - Polynomial.C 1) ^ (2 ^ (b - 1)) := by
      rw [← Fintype.prod_equiv (ZMod.finEquiv 2).toEquiv
        (fun i : Fin 2 =>
          (Polynomial.X - Polynomial.C ((ZMod.finEquiv 2) i)) ^ (2 ^ (b - 1)))
        (fun z : ZMod 2 => (Polynomial.X - Polynomial.C z) ^ (2 ^ (b - 1)))
        (by intro i; rfl)]
      rw [Fin.prod_univ_two]
      norm_num

private noncomputable def binaryFunctionalLambdaOne {b : ℕ}
    (h : (Fin b → ZMod 2) →ₗ[ZMod 2] ZMod 2) (hh : h ≠ 0) :
    (binaryFunctionalRootPolynomial h).coeff (2 ^ (b - 1)) = 1 := by
  rw [binaryFunctionalRootPolynomialOfNeZero h hh]
  have hshift := Polynomial.coeff_X_pow_mul
    (((Polynomial.X - Polynomial.C 1) ^ (2 ^ (b - 1))) : Polynomial (ZMod 2))
    (2 ^ (b - 1)) 0
  rw [zero_add] at hshift
  rw [hshift, Polynomial.coeff_zero_eq_eval_zero]
  norm_num
  decide

open scoped BigOperators in
private noncomputable def binaryFunctionalRootPolynomialZero (b : ℕ) :
    binaryFunctionalRootPolynomial
      (0 : (Fin b → ZMod 2) →ₗ[ZMod 2] ZMod 2) = Polynomial.X ^ (2 ^ b) := by
  classical
  unfold binaryFunctionalRootPolynomial
  simp [ZMod.card]

open scoped BigOperators in
private noncomputable def binaryFunctionalLambdaZero (b : ℕ) (hb : 0 < b) :
    (binaryFunctionalRootPolynomial
      (0 : (Fin b → ZMod 2) →ₗ[ZMod 2] ZMod 2)).coeff (2 ^ (b - 1)) = 0 := by
  rw [binaryFunctionalRootPolynomialZero]
  rw [Polynomial.coeff_X_pow]
  have hsub : b - 1 < b := by omega
  have hpow : 2 ^ (b - 1) < 2 ^ b := pow_right_strictMono₀ (by omega) hsub
  rw [if_neg (ne_of_lt hpow)]

private def binaryGraphEmbeddingProd {b : ℕ}
    (φ : (Fin b → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2)) :
    (Fin b → ZMod 2) →ₗ[ZMod 2]
      ((Fin b → ZMod 2) × (Fin 2 → ZMod 2)) :=
  LinearMap.prod LinearMap.id φ

private def binaryGraphEmbeddingProdInjective {b : ℕ}
    (φ : (Fin b → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2)) :
    Function.Injective (binaryGraphEmbeddingProd φ) := by
  intro x y hxy
  exact congrArg Prod.fst hxy

private def binaryGraphSubspaceProd {b : ℕ}
    (φ : (Fin b → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2)) :
    Submodule (ZMod 2) ((Fin b → ZMod 2) × (Fin 2 → ZMod 2)) :=
  LinearMap.range (binaryGraphEmbeddingProd φ)

private def binaryGraphSubspaceProdFinrank {b : ℕ}
    (φ : (Fin b → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2)) :
    Module.finrank (ZMod 2) (binaryGraphSubspaceProd φ) = b := by
  rw [binaryGraphSubspaceProd, LinearMap.finrank_range_of_inj
    (binaryGraphEmbeddingProdInjective φ)]
  simp

private def binaryGraphSubspaceProdInjective {b : ℕ} :
    Function.Injective (binaryGraphSubspaceProd (b := b)) := by
  intro φ ψ hφψ
  apply LinearMap.ext
  intro x
  funext j
  have hx : binaryGraphEmbeddingProd φ x ∈ binaryGraphSubspaceProd ψ := by
    rw [← hφψ]
    exact ⟨x, rfl⟩
  rcases hx with ⟨y, hy⟩
  have hyx : y = x := congrArg Prod.fst hy
  subst y
  exact congrFun (congrArg Prod.snd hy).symm j

private def binaryMatrixDistinguishingTuple {b : ℕ}
    (N : Fin 2 → Fin b → ZMod 2) (j : Fin 2) : Fin (b + 2) → ZMod 2 :=
  Fin.append (fun i => -N j i) (fun j' => if j' = j then 1 else 0)

open scoped BigOperators in
private noncomputable def binaryMatrixLinearMap {b : ℕ}
    (M : Fin 2 → Fin b → ZMod 2) :
    (Fin b → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2) where
  toFun x j := ∑ i : Fin b, M j i * x i
  map_add' x y := by
    funext j
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    funext j
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i hi
    ring

private noncomputable def binaryMatrixGraphPoint {b : ℕ}
    (M : Fin 2 → Fin b → ZMod 2) (x : Fin b → ZMod 2) :
    (Fin b → ZMod 2) × (Fin 2 → ZMod 2) :=
  (x, binaryMatrixLinearMap M x)

private noncomputable def binaryMatrixGraphFinset {b : ℕ}
    (M : Fin 2 → Fin b → ZMod 2) :
    Finset ((Fin b → ZMod 2) × (Fin 2 → ZMod 2)) := by
  classical
  exact Finset.univ.image (binaryMatrixGraphPoint M)

private noncomputable def binaryMatrixGraphPoint_injective {b : ℕ}
    (M : Fin 2 → Fin b → ZMod 2) :
    Function.Injective (binaryMatrixGraphPoint M) := by
  intro x y hxy
  exact congrArg Prod.fst hxy

private noncomputable def binaryMatrixGraphFinset_card {b : ℕ}
    (M : Fin 2 → Fin b → ZMod 2) :
    (binaryMatrixGraphFinset M).card = 2 ^ b := by
  classical
  unfold binaryMatrixGraphFinset
  rw [Finset.card_image_of_injective Finset.univ
    (binaryMatrixGraphPoint_injective M), Finset.card_univ]
  simp [ZMod.card]

private noncomputable def binaryMatrixGraphFinset_card_addTwo (r : ℕ)
    (M : Fin 2 → Fin (r + 2) → ZMod 2) :
    (binaryMatrixGraphFinset M).card = 4 * 2 ^ r := by
  rw [binaryMatrixGraphFinset_card]
  rw [pow_add]
  norm_num
  ring

private noncomputable def binaryMatrixGraphSubspace {b : ℕ}
    (M : Fin 2 → Fin b → ZMod 2) :
    Submodule (ZMod 2) ((Fin b → ZMod 2) × (Fin 2 → ZMod 2)) :=
  binaryGraphSubspaceProd (binaryMatrixLinearMap M)

private def binaryMatrixParameterCard (b : ℕ) :
    Fintype.card (Fin 2 → Fin b → ZMod 2) = 2 ^ (2 * b) := by
  simp [ZMod.card, ← pow_mul, Nat.mul_comm]

private noncomputable def binaryMatrixRowDifferenceFunctional {b : ℕ}
    (M N : Fin 2 → Fin b → ZMod 2) (j : Fin 2) :
    (Fin b → ZMod 2) →ₗ[ZMod 2] ZMod 2 :=
  (LinearMap.proj j : (Fin 2 → ZMod 2) →ₗ[ZMod 2] ZMod 2).comp
    (binaryMatrixLinearMap M - binaryMatrixLinearMap N)

open scoped BigOperators in
private noncomputable def binaryMatrixRowDifferenceFunctional_apply_basis {b : ℕ}
    (A N : Fin 2 → Fin b → ZMod 2) (j : Fin 2) (i : Fin b) :
    binaryMatrixRowDifferenceFunctional A N j (binaryBasisVector i) =
      A j i - N j i := by
  classical
  unfold binaryMatrixRowDifferenceFunctional binaryMatrixLinearMap binaryBasisVector
  simp

private noncomputable def binaryMatrixRowDifferenceFunctional_ne_zero {b : ℕ}
    (A N : Fin 2 → Fin b → ZMod 2) (j : Fin 2) (hrow : A j ≠ N j) :
    binaryMatrixRowDifferenceFunctional A N j ≠ 0 := by
  rcases Function.ne_iff.mp hrow with ⟨i, hi⟩
  intro hzero
  have hval := congrArg (fun f => f (binaryBasisVector i)) hzero
  rw [binaryMatrixRowDifferenceFunctional_apply_basis] at hval
  simp only [LinearMap.zero_apply] at hval
  exact hi (sub_eq_zero.mp hval)

private noncomputable def binaryMatrixRowDifferenceFunctional_self {b : ℕ}
    (M : Fin 2 → Fin b → ZMod 2) (j : Fin 2) :
    binaryMatrixRowDifferenceFunctional M M j = 0 := by
  ext x
  simp [binaryMatrixRowDifferenceFunctional]

open scoped NNReal in
private noncomputable def binaryMatrix_exponent_real_le
    (ε : ℝ≥0) (r : ℕ)
    (hscale : (2 : ℝ) ≤ (ε : ℝ) * (r + 4)) :
    ((r + 4 : ℕ) : ℝ) * (2 * ((1 : ℝ) - ε)) ≤
      ((2 * (r + 2) : ℕ) : ℝ) := by
  push_cast
  nlinarith

open scoped NNReal ENNReal in
private noncomputable def binaryMatrix_exponent_ennreal_le
    (ε : ℝ≥0) (r : ℕ)
    (hscale : (2 : ℝ) ≤ (ε : ℝ) * (r + 4)) :
    (((16 * 2 ^ r : ℕ) : ENNReal) ^ (2 * ((1 : ℝ) - ε))) ≤
      ((2 ^ (2 * (r + 2)) : ℕ) : ENNReal) := by
  have hexp := binaryMatrix_exponent_real_le ε r hscale
  have hbase : 16 * 2 ^ r = 2 ^ (r + 4) := by
    rw [pow_add]
    norm_num
    ring
  rw [hbase]
  push_cast
  rw [← ENNReal.rpow_natCast_mul (2 : ENNReal) (r + 4)
    (2 * ((1 : ℝ) - ε))]
  rw [← ENNReal.rpow_natCast (2 : ENNReal) (2 * (r + 2))]
  exact ENNReal.rpow_le_rpow_of_exponent_le (by norm_num) hexp

private def binaryProductIndexCard (b : ℕ) :
    Fintype.card ((Fin b → ZMod 2) × (Fin 2 → ZMod 2)) = 2 ^ (b + 2) := by
  simp [Fintype.card_prod, ZMod.card, pow_add]

private def binaryProductIndexCard_addTwo (r : ℕ) :
    Fintype.card ((Fin (r + 2) → ZMod 2) × (Fin 2 → ZMod 2)) =
      16 * 2 ^ r := by
  rw [binaryProductIndexCard]
  have h : r + 2 + 2 = r + 4 := by omega
  rw [h, pow_add]
  norm_num
  ring

private def binaryProductLeftBasisTuple {b : ℕ} (i : Fin b) :
    Fin (b + 2) → ZMod 2 :=
  Fin.append (fun i' => if i' = i then 1 else 0) (fun _ => 0)

open scoped BigOperators in
private noncomputable def binaryProductLinearFormMv {b : ℕ}
    (w : (Fin b → ZMod 2) × (Fin 2 → ZMod 2)) :
    MvPolynomial (Fin (b + 2)) (ZMod 2) :=
  (∑ i : Fin b, MvPolynomial.C (w.1 i) * MvPolynomial.X (Fin.castAdd 2 i)) +
    ∑ j : Fin 2, MvPolynomial.C (w.2 j) * MvPolynomial.X (Fin.natAdd b j)

open scoped BigOperators in
private noncomputable def binaryMatrixLambdaMv {b : ℕ}
    (M : Fin 2 → Fin b → ZMod 2) : MvPolynomial (Fin (b + 2)) (ZMod 2) := by
  classical
  exact (∏ x : Fin b → ZMod 2,
    (Polynomial.X - Polynomial.C
      (binaryProductLinearFormMv (x, binaryMatrixLinearMap M x)))).coeff
        (2 ^ (b - 1))

open scoped BigOperators in
private noncomputable def binaryMatrixDirectConfigurationSeparator (b : ℕ) :
    MvPolynomial (Fin (b + 2)) (ZMod 2) := by
  classical
  exact
    (∏ w : (Fin b → ZMod 2) × (Fin 2 → ZMod 2),
      if w = 0 then 1 else binaryProductLinearFormMv w) *
    (∏ M : Fin 2 → Fin b → ZMod 2, ∏ N : Fin 2 → Fin b → ZMod 2,
      if M = N then 1 else binaryMatrixLambdaMv M - binaryMatrixLambdaMv N)

private noncomputable def binaryMatrixGoodCoefficients
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {b : ℕ} (t : Fin (b + 2) → K) : Finset K := by
  classical
  exact Finset.univ.image (fun M : Fin 2 → Fin b → ZMod 2 =>
    MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t (binaryMatrixLambdaMv M))

private noncomputable def binaryMatrixGoodCoefficients_card
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {b : ℕ} (t : Fin (b + 2) → K)
    (hinj : Function.Injective (fun M : Fin 2 → Fin b → ZMod 2 =>
      MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t (binaryMatrixLambdaMv M))) :
    (binaryMatrixGoodCoefficients t).card = 2 ^ (2 * b) := by
  classical
  unfold binaryMatrixGoodCoefficients
  rw [Finset.card_image_of_injective Finset.univ hinj,
    Finset.card_univ, binaryMatrixParameterCard]

private noncomputable def binaryMatrixGoodCoefficients_mem
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {b : ℕ} (t : Fin (b + 2) → K) (γ : K) :
    γ ∈ binaryMatrixGoodCoefficients t ↔
      ∃ M : Fin 2 → Fin b → ZMod 2,
        MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t
          (binaryMatrixLambdaMv M) = γ := by
  classical
  unfold binaryMatrixGoodCoefficients
  simp only [Finset.mem_image, Finset.mem_univ, true_and]

private noncomputable def binaryMatrixSeparatorThreshold (b : ℕ) : ℕ :=
  (binaryMatrixDirectConfigurationSeparator b).totalDegree + 1

open scoped BigOperators in
private noncomputable def binaryProductLinearFormMv_eval_distinguishingTuple {b : ℕ}
    (A N : Fin 2 → Fin b → ZMod 2) (j : Fin 2) (x : Fin b → ZMod 2) :
    MvPolynomial.eval (binaryMatrixDistinguishingTuple N j)
      (binaryProductLinearFormMv (x, binaryMatrixLinearMap A x)) =
        binaryMatrixRowDifferenceFunctional A N j x := by
  classical
  have hcomm (r : Fin 2) :
      (∑ i : Fin b, x i * N r i) = ∑ i : Fin b, N r i * x i := by
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_comm _ _
  unfold binaryProductLinearFormMv binaryMatrixDistinguishingTuple
    binaryMatrixRowDifferenceFunctional binaryMatrixLinearMap
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, ZMod.neg_eq_self_mod_two, LinearMap.coe_mk,
      AddHom.coe_mk, map_sum, Fin.sum_univ_two, map_add, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X, Fin.append_left, Fin.append_right,
      ↓reduceIte, mul_one, one_ne_zero, mul_zero, add_zero, LinearMap.coe_comp,
      LinearMap.coe_proj, Function.comp_apply, Function.eval, LinearMap.sub_apply,
      Pi.sub_apply]
    rw [CharTwo.sub_eq_add, hcomm]
    ac_rfl
  · simp only [Fin.mk_one, Fin.isValue, ZMod.neg_eq_self_mod_two, LinearMap.coe_mk,
      AddHom.coe_mk, map_sum, Fin.sum_univ_two, map_add, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X, Fin.append_left, Fin.append_right,
      zero_ne_one, ↓reduceIte, mul_zero, mul_one, zero_add, LinearMap.coe_comp,
      LinearMap.coe_proj, Function.comp_apply, Function.eval, LinearMap.sub_apply,
      Pi.sub_apply]
    rw [CharTwo.sub_eq_add, hcomm]
    ac_rfl

open scoped BigOperators in
private noncomputable def binaryMatrixLambdaMv_eval_distinguishingTuple {b : ℕ}
    (A N : Fin 2 → Fin b → ZMod 2) (j : Fin 2) :
    MvPolynomial.eval (binaryMatrixDistinguishingTuple N j)
        (binaryMatrixLambdaMv A) =
      (binaryFunctionalRootPolynomial
        (binaryMatrixRowDifferenceFunctional A N j)).coeff (2 ^ (b - 1)) := by
  classical
  unfold binaryMatrixLambdaMv binaryFunctionalRootPolynomial
  rw [← MvPolynomial.coeff_eval_eq_eval_coeff (Fin (b + 2))
    (binaryMatrixDistinguishingTuple N j)]
  apply congrArg (fun p : Polynomial (ZMod 2) => p.coeff (2 ^ (b - 1)))
  rw [Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro x hx
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  rw [binaryProductLinearFormMv_eval_distinguishingTuple]

open scoped BigOperators in
private noncomputable def binaryMatrixLambdaMv_injective {b : ℕ} (hb : 0 < b) :
    Function.Injective (binaryMatrixLambdaMv (b := b)) := by
  intro A N hEq
  by_contra hAN
  have hrowEx : ∃ j : Fin 2, A j ≠ N j := by
    by_contra hnone
    apply hAN
    funext j
    by_contra hrow
    exact hnone ⟨j, hrow⟩
  rcases hrowEx with ⟨j, hrow⟩
  have hne : binaryMatrixRowDifferenceFunctional A N j ≠ 0 :=
    binaryMatrixRowDifferenceFunctional_ne_zero A N j hrow
  have hEvalA :
      MvPolynomial.eval (binaryMatrixDistinguishingTuple N j)
        (binaryMatrixLambdaMv A) = 1 := by
    rw [binaryMatrixLambdaMv_eval_distinguishingTuple,
      binaryFunctionalLambdaOne _ hne]
  have hEvalN :
      MvPolynomial.eval (binaryMatrixDistinguishingTuple N j)
        (binaryMatrixLambdaMv N) = 0 := by
    rw [binaryMatrixLambdaMv_eval_distinguishingTuple,
      binaryMatrixRowDifferenceFunctional_self, binaryFunctionalLambdaZero b hb]
  have hcongr := congrArg
    (fun p => MvPolynomial.eval (binaryMatrixDistinguishingTuple N j) p) hEq
  rw [hEvalA, hEvalN] at hcongr
  exact one_ne_zero hcongr

open scoped BigOperators in
private noncomputable def binaryProductLinearFormMv_eval_leftBasis {b : ℕ}
    (w : (Fin b → ZMod 2) × (Fin 2 → ZMod 2)) (i : Fin b) :
    MvPolynomial.eval (binaryProductLeftBasisTuple i)
      (binaryProductLinearFormMv w) = w.1 i := by
  classical
  unfold binaryProductLinearFormMv binaryProductLeftBasisTuple
  simp [Fin.append_left, Fin.append_right]

private def binaryProductRightBasisTuple {b : ℕ} (j : Fin 2) :
    Fin (b + 2) → ZMod 2 :=
  Fin.append (fun _ => 0) (fun j' => if j' = j then 1 else 0)

open scoped BigOperators in
private noncomputable def binaryProductLinearFormMv_eval_rightBasis {b : ℕ}
    (w : (Fin b → ZMod 2) × (Fin 2 → ZMod 2)) (j : Fin 2) :
    MvPolynomial.eval (binaryProductRightBasisTuple (b := b) j)
      (binaryProductLinearFormMv w) = w.2 j := by
  classical
  unfold binaryProductLinearFormMv binaryProductRightBasisTuple
  fin_cases j <;> simp [Fin.append_left, Fin.append_right]

open scoped BigOperators in
private noncomputable def binaryProductLinearFormMvNeZero {b : ℕ}
    (w : (Fin b → ZMod 2) × (Fin 2 → ZMod 2)) (hw : w ≠ 0) :
    binaryProductLinearFormMv w ≠ 0 := by
  classical
  by_cases hleft : w.1 = 0
  · have hright : w.2 ≠ 0 := by
      intro h
      apply hw
      apply Prod.ext
      · exact hleft
      · exact h
    rcases Function.ne_iff.mp hright with ⟨j, hj⟩
    intro hzero
    have heval := congrArg
      (fun p => MvPolynomial.eval (binaryProductRightBasisTuple (b := b) j) p) hzero
    rw [binaryProductLinearFormMv_eval_rightBasis] at heval
    simp only [map_zero] at heval
    exact hj heval
  · rcases Function.ne_iff.mp hleft with ⟨i, hi⟩
    intro hzero
    have heval := congrArg
      (fun p => MvPolynomial.eval (binaryProductLeftBasisTuple i) p) hzero
    rw [binaryProductLinearFormMv_eval_leftBasis] at heval
    simp only [map_zero] at heval
    exact hi heval

open scoped BigOperators in
private noncomputable def binaryMatrixConfigurationSeparatorLeftNeZero (b : ℕ) :
    (∏ w : (Fin b → ZMod 2) × (Fin 2 → ZMod 2),
      if w = 0 then (1 : MvPolynomial (Fin (b + 2)) (ZMod 2))
      else binaryProductLinearFormMv w) ≠ 0 := by
  classical
  rw [Finset.prod_ne_zero_iff]
  intro w hw
  by_cases hzero : w = 0
  · rw [if_pos hzero]
    exact one_ne_zero
  · rw [if_neg hzero]
    exact binaryProductLinearFormMvNeZero w hzero

open scoped BigOperators in
private noncomputable def binaryMatrixDirectConfigurationSeparatorNeZeroOfInjective (b : ℕ)
    (hinj : Function.Injective (binaryMatrixLambdaMv (b := b))) :
    binaryMatrixDirectConfigurationSeparator b ≠ 0 := by
  classical
  unfold binaryMatrixDirectConfigurationSeparator
  apply mul_ne_zero
  · exact binaryMatrixConfigurationSeparatorLeftNeZero b
  · rw [Finset.prod_ne_zero_iff]
    intro M hM
    rw [Finset.prod_ne_zero_iff]
    intro N hN
    by_cases hMN : M = N
    · rw [if_pos hMN]
      exact one_ne_zero
    · rw [if_neg hMN]
      exact sub_ne_zero.mpr (hinj.ne hMN)

open scoped BigOperators in
private noncomputable def binaryMatrixDirectConfigurationSeparatorNeZero
    (b : ℕ) (hb : 0 < b) :
    binaryMatrixDirectConfigurationSeparator b ≠ 0 :=
  binaryMatrixDirectConfigurationSeparatorNeZeroOfInjective b
    (binaryMatrixLambdaMv_injective hb)

open scoped BigOperators in
private noncomputable def binaryProductSubspaceLambdaMv {b : ℕ} (d : ℕ)
    (W : Submodule (ZMod 2) ((Fin b → ZMod 2) × (Fin 2 → ZMod 2))) :
    MvPolynomial (Fin (b + 2)) (ZMod 2) := by
  classical
  exact (∏ w : W, (Polynomial.X - Polynomial.C
    ((∑ i : Fin b, MvPolynomial.C (w.1.1 i) * MvPolynomial.X (Fin.castAdd 2 i)) +
      ∑ j : Fin 2, MvPolynomial.C (w.1.2 j) * MvPolynomial.X (Fin.natAdd b j)))).coeff
        (2 ^ (d - 1))

open scoped BigOperators in
private noncomputable def binaryMatrixConfigurationSeparator (b : ℕ) :
    MvPolynomial (Fin (b + 2)) (ZMod 2) := by
  classical
  exact
    (∏ w : (Fin b → ZMod 2) × (Fin 2 → ZMod 2),
      if w = 0 then 1 else binaryProductLinearFormMv w) *
    (∏ M : Fin 2 → Fin b → ZMod 2, ∏ N : Fin 2 → Fin b → ZMod 2,
      if M = N then 1 else
        binaryProductSubspaceLambdaMv b (binaryMatrixGraphSubspace M) -
          binaryProductSubspaceLambdaMv b (binaryMatrixGraphSubspace N))

open scoped BigOperators in
private noncomputable def binaryMatrixConfigurationSeparatorNeZeroOfLambda (b : ℕ)
    (hlambda : ∀ M N : Fin 2 → Fin b → ZMod 2, M ≠ N →
      binaryProductSubspaceLambdaMv b (binaryMatrixGraphSubspace M) ≠
        binaryProductSubspaceLambdaMv b (binaryMatrixGraphSubspace N)) :
    binaryMatrixConfigurationSeparator b ≠ 0 := by
  classical
  unfold binaryMatrixConfigurationSeparator
  apply mul_ne_zero
  · exact binaryMatrixConfigurationSeparatorLeftNeZero b
  · rw [Finset.prod_ne_zero_iff]
    intro M hM
    rw [Finset.prod_ne_zero_iff]
    intro N hN
    by_cases hMN : M = N
    · rw [if_pos hMN]
      exact one_ne_zero
    · rw [if_neg hMN]
      exact sub_ne_zero.mpr (hlambda M N hMN)

private noncomputable def binaryProductSubspaceLambdaOnTuple {K : Type} [Field K] [CharP K 2]
    [Algebra (ZMod 2) K] {b : ℕ} (t : Fin (b + 2) → K) (d : ℕ)
    (W : Submodule (ZMod 2) ((Fin b → ZMod 2) × (Fin 2 → ZMod 2))) : K :=
  MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t
    (binaryProductSubspaceLambdaMv d W)

open scoped BigOperators in
private noncomputable def binaryProductTupleLinearMap {K : Type} [Field K] [CharP K 2]
    [Algebra (ZMod 2) K] {b : ℕ} (t : Fin (b + 2) → K) :
    ((Fin b → ZMod 2) × (Fin 2 → ZMod 2)) →ₗ[ZMod 2] K where
  toFun w :=
    (∑ i : Fin b, w.1 i • t (Fin.castAdd 2 i)) +
      ∑ j : Fin 2, w.2 j • t (Fin.natAdd b j)
  map_add' x y := by
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul,
      Finset.sum_add_distrib]
    abel
  map_smul' c x := by
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply]
    rw [smul_add, Finset.smul_sum, Finset.smul_sum]
    apply congrArg₂ (· + ·)
    · apply Finset.sum_congr rfl
      intro i hi
      rw [smul_smul]
      rfl
    · apply Finset.sum_congr rfl
      intro j hj
      rw [smul_smul]
      rfl

private noncomputable def binaryMatrixGraphBasis
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {b : ℕ} (t : Fin (b + 2) → K)
    (M : Fin 2 → Fin b → ZMod 2) (i : Fin b) : K :=
  binaryProductTupleLinearMap t
    (binaryBasisVector i, binaryMatrixLinearMap M (binaryBasisVector i))

open scoped BigOperators in
private noncomputable def binaryMatrixGraphBasis_sum
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {b : ℕ} (t : Fin (b + 2) → K)
    (M : Fin 2 → Fin b → ZMod 2) (x : Fin b → ZMod 2) :
    (∑ i : Fin b, x i • binaryMatrixGraphBasis t M i) =
      binaryProductTupleLinearMap t (x, binaryMatrixLinearMap M x) := by
  classical
  change (∑ i : Fin b, x i •
      binaryProductTupleLinearMap t
        (binaryGraphEmbeddingProd (binaryMatrixLinearMap M) (binaryBasisVector i))) =
    binaryProductTupleLinearMap t
      (binaryGraphEmbeddingProd (binaryMatrixLinearMap M) x)
  calc
    (∑ i : Fin b, x i •
        binaryProductTupleLinearMap t
          (binaryGraphEmbeddingProd (binaryMatrixLinearMap M) (binaryBasisVector i))) =
      ∑ i : Fin b, binaryProductTupleLinearMap t
        (x i • binaryGraphEmbeddingProd (binaryMatrixLinearMap M) (binaryBasisVector i)) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [LinearMap.map_smul]
    _ = binaryProductTupleLinearMap t
        (∑ i : Fin b,
          x i • binaryGraphEmbeddingProd (binaryMatrixLinearMap M) (binaryBasisVector i)) := by
          rw [map_sum]
    _ = binaryProductTupleLinearMap t
        (binaryGraphEmbeddingProd (binaryMatrixLinearMap M)
          (∑ i : Fin b, x i • binaryBasisVector i)) := by
          congr 1
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro i hi
          rw [LinearMap.map_smul]
    _ = binaryProductTupleLinearMap t
        (binaryGraphEmbeddingProd (binaryMatrixLinearMap M) x) := by
          rw [binaryBasisVector_sum]

open scoped BigOperators in
private noncomputable def binaryProductLinearFormMv_eval₂
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {b : ℕ} (t : Fin (b + 2) → K)
    (w : (Fin b → ZMod 2) × (Fin 2 → ZMod 2)) :
    MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t
      (binaryProductLinearFormMv w) = binaryProductTupleLinearMap t w := by
  classical
  unfold binaryProductLinearFormMv binaryProductTupleLinearMap
  simp only [MvPolynomial.eval₂_add, MvPolynomial.eval₂_sum,
    MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X,
    Algebra.smul_def]
  rfl

open scoped BigOperators in
private noncomputable def binaryMatrixGenericTupleOfSeparatorEvalNeZero
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {b : ℕ} (t : Fin (b + 2) → K)
    (heval : MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t
      (binaryMatrixDirectConfigurationSeparator b) ≠ 0) :
    Function.Injective (binaryProductTupleLinearMap t) ∧
      Function.Injective (fun M : Fin 2 → Fin b → ZMod 2 =>
        MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t (binaryMatrixLambdaMv M)) := by
  classical
  unfold binaryMatrixDirectConfigurationSeparator at heval
  simp only [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_prod] at heval
  rcases mul_ne_zero_iff.mp heval with ⟨hleft, hright⟩
  rw [Finset.prod_ne_zero_iff] at hleft hright
  constructor
  · intro x y hxy
    by_contra hne
    have hsub : x - y ≠ 0 := sub_ne_zero.mpr hne
    have hfactor := hleft (x - y) (Finset.mem_univ _)
    rw [if_neg hsub, binaryProductLinearFormMv_eval₂] at hfactor
    apply hfactor
    rw [LinearMap.map_sub, hxy, sub_self]
  · intro M N hMNval
    by_contra hMN
    have hinner := hright M (Finset.mem_univ _)
    rw [Finset.prod_ne_zero_iff] at hinner
    have hfactor := hinner N (Finset.mem_univ _)
    rw [if_neg hMN] at hfactor
    apply hfactor
    rw [MvPolynomial.eval₂_sub]
    exact sub_eq_zero.mpr hMNval

open scoped BigOperators in
private noncomputable def binarySpanFactor
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {d : ℕ} (v : Fin d → K) (c : Fin d → ZMod 2) : Polynomial K :=
  Polynomial.X - Polynomial.C (∑ i : Fin d, c i • v i)

open scoped BigOperators in
private noncomputable def binarySpanFactor_comp_sub_C
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {d : ℕ} (v : Fin d → K) (c : Fin d → ZMod 2) (a : K) :
    (binarySpanFactor v c).comp (Polynomial.X - Polynomial.C a) =
      Polynomial.X - Polynomial.C ((∑ i : Fin d, c i • v i) + a) := by
  unfold binarySpanFactor
  simp only [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp,
    Polynomial.C_add]
  ring

open scoped BigOperators in
private noncomputable def binarySpanFactor_snoc
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {d : ℕ} (v : Fin d → K) (a : K)
    (c : Fin d → ZMod 2) (z : ZMod 2) :
    binarySpanFactor (Fin.snoc v a) (Fin.snoc c z) =
      Polynomial.X - Polynomial.C ((∑ i : Fin d, c i • v i) + z • a) := by
  unfold binarySpanFactor
  congr 2
  rw [Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]

open scoped BigOperators in
private noncomputable def binarySpanPolynomial {K : Type} [Field K] [CharP K 2]
    [Algebra (ZMod 2) K] {d : ℕ} (v : Fin d → K) : Polynomial K := by
  classical
  exact ∏ a : Fin d → ZMod 2,
    (Polynomial.X - Polynomial.C (∑ i : Fin d, a i • v i))

open scoped BigOperators in
private noncomputable def binaryMatrixLambda_eval_eq_span_coeff
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {b : ℕ} (t : Fin (b + 2) → K)
    (M : Fin 2 → Fin b → ZMod 2) :
    MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t (binaryMatrixLambdaMv M) =
      (binarySpanPolynomial (binaryMatrixGraphBasis t M)).coeff (2 ^ (b - 1)) := by
  classical
  unfold binaryMatrixLambdaMv binarySpanPolynomial
  rw [MvPolynomial.eval₂_eq_eval_map]
  rw [← Polynomial.coeff_map]
  rw [← MvPolynomial.coeff_eval_eq_eval_coeff (Fin (b + 2)) t]
  apply congrArg (fun p : Polynomial K => p.coeff (2 ^ (b - 1)))
  rw [Polynomial.map_prod, Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro x hx
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    MvPolynomial.eval_map, binaryProductLinearFormMv_eval₂,
    ← binaryMatrixGraphBasis_sum]

open scoped BigOperators in
private noncomputable def binarySpanPolynomial_eq_prod_factor
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {d : ℕ} (v : Fin d → K) :
    binarySpanPolynomial v = ∏ c : Fin d → ZMod 2, binarySpanFactor v c := by
  rfl

open scoped BigOperators in
private noncomputable def binarySpanPolynomial_graph_root
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {b : ℕ} (t : Fin (b + 2) → K)
    (M : Fin 2 → Fin b → ZMod 2) (x : Fin b → ZMod 2) :
    (binarySpanPolynomial (binaryMatrixGraphBasis t M)).eval
      (binaryProductTupleLinearMap t (x, binaryMatrixLinearMap M x)) = 0 := by
  classical
  unfold binarySpanPolynomial
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ x)
  rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
    ← binaryMatrixGraphBasis_sum, sub_self]

open scoped BigOperators in
private noncomputable def binarySpanPolynomial_monic
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {d : ℕ} (v : Fin d → K) : (binarySpanPolynomial v).Monic := by
  classical
  unfold binarySpanPolynomial
  simpa using (Polynomial.monic_prod_X_sub_C
    (fun c : Fin d → ZMod 2 => ∑ i : Fin d, c i • v i) Finset.univ)

open scoped BigOperators in
private noncomputable def binarySpanPolynomial_natDegree
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {d : ℕ} (v : Fin d → K) :
    (binarySpanPolynomial v).natDegree = 2 ^ d := by
  classical
  unfold binarySpanPolynomial
  rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
  simp [ZMod.card]

open scoped BigOperators in
private noncomputable def binarySpanPolynomial_snoc_reindex
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {d : ℕ} (v : Fin d → K) (a : K) :
    binarySpanPolynomial (Fin.snoc v a) =
      ∏ z : ZMod 2, ∏ c : Fin d → ZMod 2,
        binarySpanFactor (Fin.snoc v a) (Fin.snoc c z) := by
  classical
  rw [binarySpanPolynomial_eq_prod_factor]
  calc
    (∏ c : Fin (d + 1) → ZMod 2,
        binarySpanFactor (Fin.snoc v a) c) =
      ∏ p : ZMod 2 × (Fin d → ZMod 2),
        binarySpanFactor (Fin.snoc v a) (Fin.snoc p.2 p.1) := by
      exact (Fintype.prod_equiv
        (Fin.snocEquiv (fun _ : Fin (d + 1) => ZMod 2))
        (fun p : ZMod 2 × (Fin d → ZMod 2) =>
          binarySpanFactor (Fin.snoc v a) (Fin.snoc p.2 p.1))
        (fun c : Fin (d + 1) → ZMod 2 =>
          binarySpanFactor (Fin.snoc v a) c)
        (by intro p; rfl)).symm
    _ = ∏ z : ZMod 2, ∏ c : Fin d → ZMod 2,
        binarySpanFactor (Fin.snoc v a) (Fin.snoc c z) := by
      rw [Fintype.prod_prod_type]

open scoped BigOperators in
private noncomputable def binarySpanPolynomial_snoc_split
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {d : ℕ} (v : Fin d → K) (a : K) :
    binarySpanPolynomial (Fin.snoc v a) =
      binarySpanPolynomial v *
        (binarySpanPolynomial v).comp (Polynomial.X - Polynomial.C a) := by
  classical
  rw [binarySpanPolynomial_snoc_reindex, binarySpanPolynomial_eq_prod_factor]
  simp_rw [binarySpanFactor_snoc]
  calc
    (∏ z : ZMod 2, ∏ c : Fin d → ZMod 2,
        (Polynomial.X - Polynomial.C
          ((∑ i : Fin d, c i • v i) + z • a))) =
      (∏ c : Fin d → ZMod 2,
        (Polynomial.X - Polynomial.C (∑ i : Fin d, c i • v i))) *
      (∏ c : Fin d → ZMod 2,
        (Polynomial.X - Polynomial.C ((∑ i : Fin d, c i • v i) + a))) := by
      rw [← Fintype.prod_equiv (ZMod.finEquiv 2).toEquiv
        (fun z : Fin 2 => ∏ c : Fin d → ZMod 2,
          (Polynomial.X - Polynomial.C
            ((∑ i : Fin d, c i • v i) + ((ZMod.finEquiv 2) z) • a)))
        (fun z : ZMod 2 => ∏ c : Fin d → ZMod 2,
          (Polynomial.X - Polynomial.C
            ((∑ i : Fin d, c i • v i) + z • a)))
        (by intro z; rfl)]
      rw [Fin.prod_univ_two]
      norm_num
    _ =
      (∏ c : Fin d → ZMod 2, binarySpanFactor v c) *
      (∏ c : Fin d → ZMod 2, binarySpanFactor v c).comp
        (Polynomial.X - Polynomial.C a) := by
      congr 1
      rw [Polynomial.prod_comp]
      apply Finset.prod_congr rfl
      intro c hc
      rw [binarySpanFactor_comp_sub_C]

open scoped BigOperators in
private noncomputable def binarySpanPolynomial_zero
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    (v : Fin 0 → K) : binarySpanPolynomial v = Polynomial.X := by
  unfold binarySpanPolynomial
  simp

open scoped BigOperators in
private noncomputable def binarySpanPolynomial_translate
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {d : ℕ} (v : Fin d → K) (y : K) :
    (binarySpanPolynomial v).comp (Polynomial.X - Polynomial.C y) =
      binarySpanPolynomial v -
        Polynomial.C ((binarySpanPolynomial v).eval y) := by
  refine Fin.snocInduction (motive := fun {d} v => ∀ y : K,
    (binarySpanPolynomial v).comp (Polynomial.X - Polynomial.C y) =
      binarySpanPolynomial v - Polynomial.C ((binarySpanPolynomial v).eval y))
    ?_ ?_ v y
  · intro y
    rw [binarySpanPolynomial_zero]
    simp only [Polynomial.X_comp, Polynomial.eval_X]
  · intro d v a ih y
    have hrec :
        binarySpanPolynomial (Fin.snoc v a) =
          (binarySpanPolynomial v) ^ 2 -
            Polynomial.C ((binarySpanPolynomial v).eval a) *
              binarySpanPolynomial v := by
      rw [binarySpanPolynomial_snoc_split, ih a]
      ring
    rw [hrec]
    simp only [Polynomial.sub_comp, Polynomial.pow_comp, Polynomial.mul_comp,
      Polynomial.C_comp, ih y, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.C_sub,
      Polynomial.C_pow, Polynomial.C_mul]
    repeat rw [CharTwo.sub_eq_add]
    ring_nf
    rw [CharTwo.two_eq_zero]
    simp only [mul_zero, zero_add]

open scoped BigOperators in
private noncomputable def binarySpanPolynomial_snoc_recurrence
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {d : ℕ} (v : Fin d → K) (a : K) :
    binarySpanPolynomial (Fin.snoc v a) =
      (binarySpanPolynomial v) ^ 2 -
        Polynomial.C ((binarySpanPolynomial v).eval a) * binarySpanPolynomial v := by
  rw [binarySpanPolynomial_snoc_split, binarySpanPolynomial_translate]
  ring

open scoped BigOperators in
private noncomputable def binarySubspaceLambdaMv {a : ℕ} (b : ℕ)
    (W : Submodule (ZMod 2) (Fin a → ZMod 2)) : MvPolynomial (Fin a) (ZMod 2) := by
  classical
  exact (∏ w : W, (Polynomial.X - Polynomial.C
    (∑ i : Fin a, MvPolynomial.C (w.1 i) * MvPolynomial.X i))).coeff (2 ^ (b - 1))

private noncomputable def binarySubspaceLambdaOnTuple {K : Type} [Field K] [CharP K 2]
    [Algebra (ZMod 2) K] {a : ℕ} (t : Fin a → K) (b : ℕ)
    (W : Submodule (ZMod 2) (Fin a → ZMod 2)) : K :=
  MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t (binarySubspaceLambdaMv b W)

open scoped BigOperators in
private noncomputable def binarySubspacePolynomial {K : Type} [Field K] [Fintype K]
    [CharP K 2] [Algebra (ZMod 2) K]
    (W : Submodule (ZMod 2) K) : Polynomial K := by
  classical
  exact ∏ x : W, (Polynomial.X - Polynomial.C (x : K))

private noncomputable def binarySubspaceLambda {K : Type} [Field K] [Fintype K]
    [CharP K 2] [Algebra (ZMod 2) K]
    (b : ℕ) (W : Submodule (ZMod 2) K) : K :=
  (binarySubspacePolynomial W).coeff (2 ^ (b - 1))

private def binarySubspaceLambdaSet {K : Type} [Field K] [Fintype K]
    [CharP K 2] [Algebra (ZMod 2) K]
    (V : Submodule (ZMod 2) K) (b : ℕ) : Set K :=
  {z | ∃ W : Submodule (ZMod 2) K,
    W ≤ V ∧ Module.finrank (ZMod 2) W = b ∧ binarySubspaceLambda b W = z}

open scoped BigOperators in
private noncomputable def binarySubspacePolynomialBasic
    {K : Type} [Field K] [Fintype K] [CharP K 2] [Algebra (ZMod 2) K]
    (W : Submodule (ZMod 2) K) :
    (binarySubspacePolynomial W).Monic ∧
      (binarySubspacePolynomial W).natDegree = 2 ^ Module.finrank (ZMod 2) W ∧
      (∀ x : K, (binarySubspacePolynomial W).eval x = 0 ↔ x ∈ W) := by
  classical
  constructor
  · unfold binarySubspacePolynomial
    simpa using (Polynomial.monic_prod_X_sub_C (fun w : W => (w.1 : K)) Finset.univ)
  constructor
  · unfold binarySubspacePolynomial
    rw [Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
    simpa using (Module.card_eq_pow_finrank (K := ZMod 2) (V := W))
  · intro x
    unfold binarySubspacePolynomial
    simp only [Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C, Finset.prod_eq_zero_iff, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨w, hw⟩
      have hxw : x = (w.1 : K) := sub_eq_zero.mp hw
      rw [hxw]
      exact w.2
    · intro hx
      exact ⟨⟨x, hx⟩, sub_self x⟩

open scoped BigOperators in
private noncomputable def binaryTupleLinearMap {K : Type} [Field K] [CharP K 2]
    [Algebra (ZMod 2) K] {a : ℕ} (t : Fin a → K) :
    (Fin a → ZMod 2) →ₗ[ZMod 2] K where
  toFun w := ∑ i : Fin a, w i • t i
  map_add' x y := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, mul_smul, RingHom.id_apply]

open scoped NNReal ProbabilityTheory in
private noncomputable def epsCaLowerOfFinsetWitness
    {ι F A : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]
    (C : Set (ι → A)) (δ_fld δ_int : ℝ≥0)
    (u : Code.WordStack A (Fin 2) ι) (S : Finset F)
    (hnot : ¬ Code.jointProximity C (u := u) δ_int)
    (hclose : ∀ γ ∈ S, δᵣ(u 0 + γ • u 1, C) ≤ (δ_fld : ENNReal)) :
    (S.card : ENNReal) / (Fintype.card F : ENNReal) ≤
      ProximityGap.epsCa (F := F) (A := A) C δ_fld δ_int := by
  classical
  unfold ProximityGap.epsCa
  refine le_trans ?_ (le_iSup _ u)
  rw [if_neg hnot]
  rw [Probability.prob_uniform_eq_card_filter_div_card]
  apply ENNReal.div_le_div_right
  exact_mod_cast Finset.card_le_card (by
    intro γ hγ
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, hclose γ hγ⟩)

open scoped NNReal in
private noncomputable def exists_binaryMatrix_scale_parameter
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ r : ℕ, (2 : ℝ) ≤ (ε : ℝ) * (r + 4) := by
  have hεR : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  obtain ⟨r, hr⟩ := Archimedean.arch (2 : ℝ) hεR
  refine ⟨r, ?_⟩
  simp only [nsmul_eq_mul] at hr
  have hεnonneg : (0 : ℝ) ≤ (ε : ℝ) := by positivity
  nlinarith

open scoped NNReal ENNReal in
private noncomputable def exists_binaryMatrix_exponent_parameter
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ r : ℕ,
      (((16 * 2 ^ r : ℕ) : ENNReal) ^ (2 * ((1 : ℝ) - ε))) ≤
        ((2 ^ (2 * (r + 2)) : ℕ) : ENNReal) := by
  obtain ⟨r, hr⟩ := exists_binaryMatrix_scale_parameter ε hε
  exact ⟨r, binaryMatrix_exponent_ennreal_le ε r hr⟩

private noncomputable def isBinaryLinearized_C_mul
    {K : Type} [Field K] (c : K) (P : Polynomial K)
    (hP : IsBinaryLinearized P) :
    IsBinaryLinearized (Polynomial.C c * P) := by
  unfold IsBinaryLinearized
  intro n hn
  rw [Polynomial.mem_support_iff, Polynomial.coeff_C_mul] at hn
  have hp : P.coeff n ≠ 0 := by
    intro hp0
    apply hn
    rw [hp0, mul_zero]
  exact hP n (Polynomial.mem_support_iff.mpr hp)

private noncomputable def isBinaryLinearized_X
    {K : Type} [Field K] :
    IsBinaryLinearized (Polynomial.X : Polynomial K) := by
  unfold IsBinaryLinearized
  intro n hn
  rw [Polynomial.support_X] at hn
  have hn1 : n = 1 := Finset.mem_singleton.mp hn
  exact ⟨0, by simp [hn1]⟩

private noncomputable def isBinaryLinearized_sq
    {K : Type} [Field K] [CharP K 2] (P : Polynomial K)
    (hP : IsBinaryLinearized P) :
    IsBinaryLinearized (P ^ 2) := by
  unfold IsBinaryLinearized
  intro n hn
  have hncoeff : (P ^ 2).coeff n ≠ 0 :=
    Polynomial.mem_support_iff.mp hn
  rw [← Polynomial.map_frobenius_expand 2 P, Polynomial.coeff_map,
    Polynomial.coeff_expand (by omega) P n] at hncoeff
  by_cases hd : 2 ∣ n
  · rw [if_pos hd] at hncoeff
    have hpcoeff : P.coeff (n / 2) ≠ 0 := by
      intro hp0
      apply hncoeff
      rw [hp0, map_zero]
    obtain ⟨i, hi⟩ := hP (n / 2) (Polynomial.mem_support_iff.mpr hpcoeff)
    refine ⟨i + 1, ?_⟩
    have heven : Even n := even_iff_two_dvd.mpr hd
    calc
      n = 2 * (n / 2) := (Nat.two_mul_div_two_of_even heven).symm
      _ = 2 * 2 ^ i := by rw [hi]
      _ = 2 ^ (i + 1) := by rw [pow_succ]; omega
  · rw [if_neg hd, map_zero] at hncoeff
    exact False.elim (hncoeff rfl)

private noncomputable def isBinaryLinearized_sub
    {K : Type} [Field K] (P Q : Polynomial K)
    (hP : IsBinaryLinearized P) (hQ : IsBinaryLinearized Q) :
    IsBinaryLinearized (P - Q) := by
  unfold IsBinaryLinearized
  intro n hn
  rw [Polynomial.mem_support_iff] at hn
  by_cases hp : P.coeff n = 0
  · have hq : Q.coeff n ≠ 0 := by
      intro hq0
      apply hn
      rw [Polynomial.coeff_sub, hp, hq0, sub_self]
    exact hQ n (Polynomial.mem_support_iff.mpr hq)
  · exact hP n (Polynomial.mem_support_iff.mpr hp)

open scoped BigOperators in
private noncomputable def binarySpanPolynomial_isBinaryLinearized
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    {d : ℕ} (v : Fin d → K) :
    IsBinaryLinearized (binarySpanPolynomial v) := by
  refine Fin.snocInduction
    (motive := fun {d} v => IsBinaryLinearized (binarySpanPolynomial v))
    ?_ ?_ v
  · rw [binarySpanPolynomial_zero]
    exact isBinaryLinearized_X
  · intro d v a ih
    rw [binarySpanPolynomial_snoc_recurrence]
    exact isBinaryLinearized_sub _ _
      (isBinaryLinearized_sq _ ih)
      (isBinaryLinearized_C_mul _ _ ih)

private noncomputable def mappedBinaryMatrixConfigurationSeparator
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K] (b : ℕ) :
    MvPolynomial (Fin (b + 2)) K :=
  MvPolynomial.map (algebraMap (ZMod 2) K) (binaryMatrixConfigurationSeparator b)

open scoped BigOperators in
private noncomputable def mappedBinaryMatrixConfigurationSeparatorNeZeroOfLambda
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K] (b : ℕ)
    (hlambda : ∀ M N : Fin 2 → Fin b → ZMod 2, M ≠ N →
      binaryProductSubspaceLambdaMv b (binaryMatrixGraphSubspace M) ≠
        binaryProductSubspaceLambdaMv b (binaryMatrixGraphSubspace N)) :
    mappedBinaryMatrixConfigurationSeparator (K := K) b ≠ 0 := by
  intro hzero
  apply binaryMatrixConfigurationSeparatorNeZeroOfLambda b hlambda
  apply MvPolynomial.map_injective (f := algebraMap (ZMod 2) K)
    (RingHom.injective (algebraMap (ZMod 2) K))
  unfold mappedBinaryMatrixConfigurationSeparator at hzero
  simpa only [map_zero] using hzero

private noncomputable def mappedBinaryMatrixDirectConfigurationSeparator
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K] (b : ℕ) :
    MvPolynomial (Fin (b + 2)) K :=
  MvPolynomial.map (algebraMap (ZMod 2) K)
    (binaryMatrixDirectConfigurationSeparator b)

open scoped BigOperators in
private noncomputable def mappedBinaryMatrixDirectConfigurationSeparatorNeZeroOfInjective
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K] (b : ℕ)
    (hinj : Function.Injective (binaryMatrixLambdaMv (b := b))) :
    mappedBinaryMatrixDirectConfigurationSeparator (K := K) b ≠ 0 := by
  intro hzero
  apply binaryMatrixDirectConfigurationSeparatorNeZeroOfInjective b hinj
  apply MvPolynomial.map_injective (f := algebraMap (ZMod 2) K)
    (RingHom.injective (algebraMap (ZMod 2) K))
  unfold mappedBinaryMatrixDirectConfigurationSeparator at hzero
  simpa only [map_zero] using hzero

open scoped BigOperators in
private noncomputable def mappedBinaryMatrixDirectConfigurationSeparatorNeZero
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    (b : ℕ) (hb : 0 < b) :
    mappedBinaryMatrixDirectConfigurationSeparator (K := K) b ≠ 0 :=
  mappedBinaryMatrixDirectConfigurationSeparatorNeZeroOfInjective b
    (binaryMatrixLambdaMv_injective hb)

private noncomputable def mvPolynomial_fin_exists_eval_ne_zero_of_totalDegree_lt_card
    {n : ℕ} {K : Type} [Field K] [Fintype K] [DecidableEq K]
    (p : MvPolynomial (Fin n) K) (hp : p ≠ 0)
    (hdeg : p.totalDegree < Fintype.card K) :
    ∃ t : Fin n → K, MvPolynomial.eval t p ≠ 0 := by
  by_contra hall
  push Not at hall
  have hsz := MvPolynomial.schwartz_zippel_totalDegree hp (Finset.univ : Finset K)
  have hone : (1 : ℚ≥0) ≤
      (p.totalDegree : ℚ≥0) / (Fintype.card K : ℚ≥0) := by
    simpa [hall, Fintype.card_ne_zero] using hsz
  have hcardpos : (0 : ℚ≥0) < (Fintype.card K : ℚ≥0) := by
    exact_mod_cast Fintype.card_pos
  have hdeg' : (p.totalDegree : ℚ≥0) < (Fintype.card K : ℚ≥0) := by
    exact_mod_cast hdeg
  have hlt : (p.totalDegree : ℚ≥0) / (Fintype.card K : ℚ≥0) < 1 :=
    (div_lt_one hcardpos).2 hdeg'
  exact (not_le_of_gt hlt) hone

private noncomputable def mvPolynomial_totalDegree_map_le
    {R S σ : Type} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (p : MvPolynomial σ R) :
    (MvPolynomial.map f p).totalDegree ≤ p.totalDegree := by
  rw [MvPolynomial.totalDegree_eq, MvPolynomial.totalDegree_eq]
  exact Finset.sup_mono (MvPolynomial.support_map_subset f p)

open scoped BigOperators in
private noncomputable def exists_binaryMatrixDirectConfigurationSeparator_eval_ne_zero
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [CharP K 2] [Algebra (ZMod 2) K]
    (b : ℕ) (hb : 0 < b)
    (hcard : binaryMatrixSeparatorThreshold b ≤ Fintype.card K) :
    ∃ t : Fin (b + 2) → K,
      MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t
        (binaryMatrixDirectConfigurationSeparator b) ≠ 0 := by
  have horig :
      (binaryMatrixDirectConfigurationSeparator b).totalDegree < Fintype.card K := by
    unfold binaryMatrixSeparatorThreshold at hcard
    omega
  have hdeg :
      (mappedBinaryMatrixDirectConfigurationSeparator (K := K) b).totalDegree <
        Fintype.card K := by
    unfold mappedBinaryMatrixDirectConfigurationSeparator
    exact lt_of_le_of_lt
      (mvPolynomial_totalDegree_map_le (algebraMap (ZMod 2) K)
        (binaryMatrixDirectConfigurationSeparator b)) horig
  obtain ⟨t, ht⟩ :=
    mvPolynomial_fin_exists_eval_ne_zero_of_totalDegree_lt_card
      (mappedBinaryMatrixDirectConfigurationSeparator (K := K) b)
      (mappedBinaryMatrixDirectConfigurationSeparatorNeZero b hb) hdeg
  refine ⟨t, ?_⟩
  unfold mappedBinaryMatrixDirectConfigurationSeparator at ht
  simpa only [MvPolynomial.eval_map] using ht

open scoped BigOperators in
private noncomputable def exists_binaryMatrixGenericTuple
    {K : Type} [Field K] [Fintype K] [DecidableEq K]
    [CharP K 2] [Algebra (ZMod 2) K]
    (b : ℕ) (hb : 0 < b)
    (hcard : binaryMatrixSeparatorThreshold b ≤ Fintype.card K) :
    ∃ t : Fin (b + 2) → K,
      Function.Injective (binaryProductTupleLinearMap t) ∧
      Function.Injective (fun M : Fin 2 → Fin b → ZMod 2 =>
        MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t (binaryMatrixLambdaMv M)) := by
  obtain ⟨t, ht⟩ :=
    exists_binaryMatrixDirectConfigurationSeparator_eval_ne_zero b hb hcard
  exact ⟨t, binaryMatrixGenericTupleOfSeparatorEvalNeZero t ht⟩

private def pow_two_gap_addTwo (r i : ℕ)
    (hlow : 2 ^ r < 2 ^ i) (hhigh : 2 ^ i ≤ 2 ^ (r + 2)) :
    i = r + 1 ∨ i = r + 2 := by
  have hmono : StrictMono ((2 : ℕ) ^ ·) :=
    pow_right_strictMono₀ (by omega)
  have hri : r < i := by
    by_contra h
    have hir : i ≤ r := Nat.le_of_not_gt h
    have hp : 2 ^ i ≤ 2 ^ r := hmono.monotone hir
    omega
  have hir2 : i ≤ r + 2 := by
    by_contra h
    have hr2i : r + 2 < i := Nat.lt_of_not_ge h
    have hp : 2 ^ (r + 2) < 2 ^ i := hmono hr2i
    omega
  omega

open scoped BigOperators in
private noncomputable def binarySpanPolynomial_topGap_addTwo
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    (r : ℕ) (v : Fin (r + 2) → K) :
    ∃ R : Polynomial K,
      binarySpanPolynomial v =
        Polynomial.X ^ (2 ^ (r + 2)) +
          Polynomial.C ((binarySpanPolynomial v).coeff (2 ^ (r + 1))) *
            Polynomial.X ^ (2 ^ (r + 1)) + R ∧
      R.natDegree ≤ 2 ^ r := by
  let P : Polynomial K := binarySpanPolynomial v
  let N : ℕ := 2 ^ (r + 2)
  let M : ℕ := 2 ^ (r + 1)
  let R : Polynomial K :=
    P - Polynomial.X ^ N - Polynomial.C (P.coeff M) * Polynomial.X ^ M
  refine ⟨R, ?_, ?_⟩
  · dsimp only [R, P, N, M]
    ring
  · apply (Polynomial.natDegree_le_iff_coeff_eq_zero).2
    intro n hn
    have hMN : M < N := by
      dsimp only [M, N]
      exact pow_right_strictMono₀ (by omega) (by omega)
    by_cases hnN : n = N
    · subst n
      have hlead : P.coeff N = 1 := by
        have h := (binarySpanPolynomial_monic v).coeff_natDegree
        rw [binarySpanPolynomial_natDegree] at h
        exact h
      dsimp only [R]
      rw [Polynomial.coeff_sub, Polynomial.coeff_sub,
        Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
        Polynomial.coeff_X_pow, hlead, if_pos rfl,
        if_neg (ne_of_gt hMN), mul_zero, sub_zero, sub_self]
    · by_cases hnM : n = M
      · subst n
        dsimp only [R]
        rw [Polynomial.coeff_sub, Polynomial.coeff_sub,
          Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow, if_neg (ne_of_lt hMN), if_pos rfl]
        ring
      · have hpzero : P.coeff n = 0 := by
          by_contra hp
          have hmem : n ∈ P.support := Polynomial.mem_support_iff.mpr hp
          obtain ⟨i, hi⟩ := binarySpanPolynomial_isBinaryLinearized v n hmem
          have hnle : n ≤ N := by
            dsimp only [N, P]
            rw [← binarySpanPolynomial_natDegree v]
            exact Polynomial.le_natDegree_of_ne_zero hp
          have hcases : i = r + 1 ∨ i = r + 2 := by
            apply pow_two_gap_addTwo r i
            · simpa only [hi] using hn
            · simpa only [hi] using hnle
          rcases hcases with hi1 | hi2
          · apply hnM
            dsimp only [M]
            rw [hi, hi1]
          · apply hnN
            dsimp only [N]
            rw [hi, hi2]
        dsimp only [R]
        rw [Polynomial.coeff_sub, Polynomial.coeff_sub,
          Polynomial.coeff_X_pow, Polynomial.coeff_C_mul,
          Polynomial.coeff_X_pow, hpzero, if_neg hnN, if_neg hnM]
        ring

open scoped BigOperators in
private noncomputable def binaryMatrixSpanPolynomial_decomposition
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    (r : ℕ) (t : Fin (r + 4) → K)
    (M : Fin 2 → Fin (r + 2) → ZMod 2) :
    ∃ R : Polynomial K,
      binarySpanPolynomial (binaryMatrixGraphBasis t M) =
        Polynomial.X ^ (2 ^ (r + 2)) +
          Polynomial.C
            (MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t
              (binaryMatrixLambdaMv M)) *
            Polynomial.X ^ (2 ^ (r + 1)) + R ∧
      R.natDegree ≤ 2 ^ r := by
  obtain ⟨R, hR, hdeg⟩ :=
    binarySpanPolynomial_topGap_addTwo r (binaryMatrixGraphBasis t M)
  refine ⟨R, ?_, hdeg⟩
  have hsub : r + 2 - 1 = r + 1 := by omega
  rw [binaryMatrixLambda_eval_eq_span_coeff, hsub]
  exact hR

open scoped BigOperators in
private noncomputable def binaryMatrixGraphAgreement
    {K : Type} [Field K] [CharP K 2] [Algebra (ZMod 2) K]
    (r : ℕ) (t : Fin (r + 4) → K)
    (M : Fin 2 → Fin (r + 2) → ZMod 2) :
    ∃ S : Finset ((Fin (r + 2) → ZMod 2) × (Fin 2 → ZMod 2)),
      S.card = 4 * 2 ^ r ∧
      ∃ p : Polynomial K,
        p.natDegree < 2 ^ r + 1 ∧
        ∀ i ∈ S,
          p.eval (binaryProductTupleLinearMap t i) =
            (binaryProductTupleLinearMap t i) ^ (2 ^ (r + 2)) +
              MvPolynomial.eval₂ (algebraMap (ZMod 2) K) t
                (binaryMatrixLambdaMv M) *
                (binaryProductTupleLinearMap t i) ^ (2 ^ (r + 1)) := by
  classical
  obtain ⟨R, hR, hdeg⟩ := binaryMatrixSpanPolynomial_decomposition r t M
  refine ⟨binaryMatrixGraphFinset M,
    binaryMatrixGraphFinset_card_addTwo r M, -R, ?_, ?_⟩
  · rw [Polynomial.natDegree_neg]
    omega
  · intro i hi
    rcases Finset.mem_image.mp hi with ⟨x, hx, hxi⟩
    subst i
    have hroot := binarySpanPolynomial_graph_root t M x
    rw [hR] at hroot
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.eval_pow, Polynomial.eval_X] at hroot
    unfold binaryMatrixGraphPoint
    rw [Polynomial.eval_neg, CharTwo.neg_eq]
    exact (CharTwo.add_eq_zero.mp hroot).symm

open scoped BigOperators NNReal ENNReal in
private noncomputable def binaryMatrix_johnson_raw
    (ε : ℝ≥0) (hε : 0 < ε) :
    ∃ q₀ : ℕ,
    ∀ {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC] [CharP FC 2],
      q₀ ≤ Fintype.card FC →
      ∃ (ιC : Type) (_ : Fintype ιC) (_ : Nonempty ιC) (_ : DecidableEq ιC)
        (domain : ιC ↪ FC) (d : ℕ) (G : Finset FC),
        0 < d ∧
        Fintype.card ιC = 16 * d ∧
        ((Fintype.card ιC : ENNReal) ^ (2 * ((1 : ℝ) - ε))) ≤
          (G.card : ENNReal) ∧
        ∀ γ ∈ G,
          ∃ S : Finset ιC, ∃ p : Polynomial FC,
            S.card = 4 * d ∧
            p.natDegree < d + 1 ∧
            ∀ i ∈ S,
              p.eval (domain i) =
                domain i ^ (4 * d) + γ * domain i ^ (2 * d) := by
  obtain ⟨r, hrpow⟩ := exists_binaryMatrix_exponent_parameter ε hε
  refine ⟨binaryMatrixSeparatorThreshold (r + 2), ?_⟩
  intro FC _ _ _ _ hFC
  letI : Algebra (ZMod 2) FC := ZMod.algebra FC 2
  obtain ⟨t, htinj, hcoeffinj⟩ :=
    exists_binaryMatrixGenericTuple (K := FC) (r + 2) (by omega) hFC
  let ιC : Type :=
    (Fin (r + 2) → ZMod 2) × (Fin 2 → ZMod 2)
  let domain : ιC ↪ FC :=
    ⟨binaryProductTupleLinearMap t, htinj⟩
  let d : ℕ := 2 ^ r
  let G : Finset FC := binaryMatrixGoodCoefficients t
  refine ⟨ιC, inferInstance, inferInstance, inferInstance, domain, d, G,
    ?_, ?_, ?_, ?_⟩
  · dsimp only [d]
    positivity
  · dsimp only [ιC, d]
    exact binaryProductIndexCard_addTwo r
  · dsimp only [ιC, G]
    rw [binaryProductIndexCard_addTwo,
      binaryMatrixGoodCoefficients_card t hcoeffinj]
    exact hrpow
  · intro γ hγ
    have hγ' : γ ∈ binaryMatrixGoodCoefficients t := by
      simpa only [G] using hγ
    obtain ⟨M, hM⟩ :=
      (binaryMatrixGoodCoefficients_mem t γ).mp hγ'
    obtain ⟨S, hScard, p, hpdeg, hagree⟩ :=
      binaryMatrixGraphAgreement r t M
    refine ⟨S, p, ?_, ?_, ?_⟩
    · dsimp only [d]
      exact hScard
    · dsimp only [d]
      exact hpdeg
    · intro i hi
      have h4 : 2 ^ (r + 2) = 4 * 2 ^ r := by
        rw [pow_add]
        norm_num
        ring
      have h2 : 2 ^ (r + 1) = 2 * 2 ^ r := by
        rw [pow_add]
        norm_num
        ring
      change p.eval (binaryProductTupleLinearMap t i) =
        (binaryProductTupleLinearMap t i) ^ (4 * 2 ^ r) +
          γ * (binaryProductTupleLinearMap t i) ^ (2 * 2 ^ r)
      simpa only [h4, h2, hM] using hagree i hi

open scoped NNReal in
private noncomputable def rsFoldClose_of_graphAgreement
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (d : ℕ)
    (hcard : Fintype.card ι = 16 * d)
    (γ : F) (S : Finset ι) (p : Polynomial F)
    (hScard : S.card = 4 * d)
    (hpdeg : p.natDegree < d + 1)
    (hagree : ∀ i ∈ S,
      p.eval (domain i) = domain i ^ (4 * d) + γ * domain i ^ (2 * d)) :
    δᵣ((fun i => domain i ^ (4 * d)) +
        γ • (fun i => domain i ^ (2 * d)),
      (ReedSolomon.code domain (d + 1) : Set (ι → F))) ≤ (3 / 4 : ℝ≥0) := by
  classical
  let w : ι → F := fun i => p.eval (domain i)
  have hw : w ∈ (ReedSolomon.code domain (d + 1) : Set (ι → F)) :=
    ReedSolomon.mem_code_of_polynomial_of_natDegree_lt_of_eval p hpdeg
      (fun _ => rfl)
  have hfloor :
      ⌊(3 / 4 : ℝ≥0) * (Fintype.card ι : ℝ≥0)⌋₊ = 12 * d := by
    rw [hcard]
    push_cast
    have heq :
        (3 / 4 : ℝ≥0) * (16 * (d : ℝ≥0)) =
          ((12 * d : ℕ) : ℝ≥0) := by
      norm_num
      ring
    rw [heq, Nat.floor_natCast]
  rw [Code.relCloseToCode_iff_relCloseToCodeword_of_minDist]
  refine ⟨w, hw, ?_⟩
  rw [Code.relCloseToWord_iff_exists_agreementCols]
  refine ⟨S, ?_, ?_⟩
  · rw [hfloor, hcard, hScard]
    omega
  · intro i
    constructor
    · intro hi
      dsimp only [w]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact (hagree i hi).symm
    · intro hne hi
      apply hne
      dsimp only [w]
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact (hagree i hi).symm

private noncomputable def rsMonomialAgreement_card_le_two_mul
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (d : ℕ) (hd : 0 < d)
    (v : ι → F)
    (hv : v ∈ (ReedSolomon.code domain (d + 1) : Set (ι → F)))
    (S : Finset ι)
    (hagree : ∀ i ∈ S, v i = domain i ^ (2 * d)) :
    S.card ≤ 2 * d := by
  classical
  letI : NeZero (d + 1) := ⟨by omega⟩
  obtain ⟨p, hpdeg, hpeval⟩ :=
    ReedSolomon.mem_code_iff_eval_of_ne_zero.mp hv
  let Q : Polynomial F := Polynomial.X ^ (2 * d) - p
  have hpdeg' : p.natDegree < 2 * d := by omega
  have hQnat : Q.natDegree = 2 * d := by
    unfold Q
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt]
    · rw [Polynomial.natDegree_X_pow]
    · simpa only [Polynomial.natDegree_X_pow] using hpdeg'
  have hQne : Q ≠ 0 := by
    apply Polynomial.ne_zero_of_natDegree_gt (n := 0)
    rw [hQnat]
    omega
  have hsub : S ⊆ Finset.univ.filter (fun i => Q.eval (domain i) = 0) := by
    intro i hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ i, ?_⟩
    unfold Q
    rw [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      hpeval i, hagree i hi, sub_self]
  calc
    S.card ≤ (Finset.univ.filter (fun i => Q.eval (domain i) = 0)).card :=
      Finset.card_le_card hsub
    _ ≤ Q.natDegree :=
      AdditiveSetListDecoding.card_filter_eval_eq_zero_le_natDegree domain hQne
    _ = 2 * d := hQnat

open scoped NNReal in
private noncomputable def binaryMonomialStack_not_joint
    {ι F : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F) (d : ℕ) (hd : 0 < d)
    (hcard : Fintype.card ι = 16 * d)
    (δ_int : ℝ≥0) (hδ : (δ_int : ℝ) < 7 / 8) :
    ¬ Code.jointProximity
      (ReedSolomon.code domain (d + 1) : Set (ι → F))
      (u := Code.finMapTwoWords
        (fun i => domain i ^ (4 * d))
        (fun i => domain i ^ (2 * d))) δ_int := by
  classical
  intro hj
  rw [← Code.jointAgreement_iff_jointProximity] at hj
  obtain ⟨S, hScard, v, hv⟩ := hj
  have hSgt : 2 * d < S.card :=
    agreementCard_gt_twoMul_of_lt_sevenEighths d hd δ_int S hcard hScard hδ
  have hv1 : v 1 ∈ (ReedSolomon.code domain (d + 1) : Set (ι → F)) :=
    (hv 1).1
  have hagree : ∀ i ∈ S, v 1 i = domain i ^ (2 * d) := by
    intro i hi
    have hmem := (hv 1).2 hi
    have heq := (Finset.mem_filter.mp hmem).2
    simpa only [Code.finMapTwoWords] using heq
  have hSle :=
    rsMonomialAgreement_card_le_two_mul domain d hd (v 1) hv1 S hagree
  omega

private noncomputable def rsRelativeMinDistFifteenSixteen
    {ι K : Type} [Fintype ι] [Nonempty ι]
    [Field K] [Fintype K] [DecidableEq K]
    (domain : ι ↪ K) (t : ℕ) (ht : 0 < t)
    (hcard : Fintype.card ι = 16 * t) :
    (Code.minDist ((ReedSolomon.code domain (t + 1) : Set (ι → K))) : ℝ) /
        Fintype.card ι = (15 : ℝ) / 16 := by
  have hkpos : 0 < t + 1 := by omega
  letI : NeZero (t + 1) := ⟨hkpos.ne'⟩
  have hk : t + 1 ≤ Fintype.card ι := by
    rw [hcard]
    omega
  rw [ReedSolomon.minDist_of_le hk, hcard]
  have hnat : 16 * t - (t + 1) + 1 = 15 * t := by omega
  rw [hnat]
  push_cast
  field_simp

open scoped BigOperators NNReal ENNReal ProbabilityTheory in
/-- For every `ε ∈ (0,1)` and every sufficiently large characteristic-two field, there is a
Reed--Solomon code of relative minimum distance `15/16` for which

  `ε_ca(C, 3/4, δ_int) ≥ n^{2(1-ε)}/|F|`

for every `δ_int < 7/8`. The strict endpoint follows from a joint-distance witness equal to
`7/8`, and the existential `q₀` records the asymptotic field threshold. -/
theorem exists_rs_epsCa_large_at_johnson_radius
    (ε : ℝ≥0) (_hε : 0 < ε) (_hε_lt : (ε : ℝ) < 1) :
    ∃ q₀ : ℕ,
    ∀ {FC : Type} [Field FC] [Fintype FC] [DecidableEq FC] [CharP FC 2],
      q₀ ≤ Fintype.card FC →
      ∃ (ιC : Type) (_ : Fintype ιC) (_ : Nonempty ιC) (_ : DecidableEq ιC)
        (domain : ιC ↪ FC) (k : ℕ),
        (Code.minDist ((ReedSolomon.code domain k : Set (ιC → FC))) : ℝ)
            / Fintype.card ιC = (15 : ℝ) / 16 ∧
        ∀ δ_int : ℝ≥0, (δ_int : ℝ) < 7 / 8 →
          epsCa (F := FC) (A := FC) ((ReedSolomon.code domain k : Set (ιC → FC)))
              (3 / 4 : ℝ≥0) δ_int ≥
            ((Fintype.card ιC : ENNReal) ^ (2 * ((1 : ℝ) - ε)))
              / (Fintype.card FC : ENNReal) := by
  classical
  obtain ⟨q₀, hraw⟩ := binaryMatrix_johnson_raw ε _hε
  refine ⟨q₀, ?_⟩
  intro FC _ _ _ _ hFC
  obtain ⟨ιC, instι, neι, decι, domain, d, G,
    hd, hcard, hG, hagree⟩ := hraw hFC
  letI : Fintype ιC := instι
  letI : Nonempty ιC := neι
  letI : DecidableEq ιC := decι
  refine ⟨ιC, inferInstance, inferInstance, inferInstance,
    domain, d + 1, rsRelativeMinDistFifteenSixteen domain d hd hcard, ?_⟩
  intro δ_int hδ
  let u : Code.WordStack FC (Fin 2) ιC :=
    Code.finMapTwoWords
      (fun i => domain i ^ (4 * d))
      (fun i => domain i ^ (2 * d))
  have hnot : ¬ Code.jointProximity
      (ReedSolomon.code domain (d + 1) : Set (ιC → FC))
      (u := u) δ_int := by
    simpa only [u] using
      (binaryMonomialStack_not_joint domain d hd hcard δ_int hδ)
  have hclose : ∀ γ ∈ G,
      δᵣ(u 0 + γ • u 1,
        (ReedSolomon.code domain (d + 1) : Set (ιC → FC))) ≤
          (3 / 4 : ℝ≥0) := by
    intro γ hγ
    obtain ⟨S, p, hScard, hpdeg, hpAgree⟩ := hagree γ hγ
    have hc := rsFoldClose_of_graphAgreement
      domain d hcard γ S p hScard hpdeg hpAgree
    simpa only [u, Code.finMapTwoWords] using hc
  exact le_trans (ENNReal.div_le_div_right hG _)
    (epsCaLowerOfFinsetWitness
      (ReedSolomon.code domain (d + 1) : Set (ιC → FC))
      (3 / 4 : ℝ≥0) δ_int u G hnot hclose)

end ReedSolomon

end CodingTheory

set_option linter.style.longFile 1800
