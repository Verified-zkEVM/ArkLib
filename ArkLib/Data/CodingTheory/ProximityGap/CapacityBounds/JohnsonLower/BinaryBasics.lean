/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.ListDecodability.Bounds.KKH26
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.FieldTheory.Finite.Basic

/-!
# Binary foundations for the Reed--Solomon Johnson lower bound

This internal module develops binary linearized polynomials, functionals, and graph subspaces
used by `CapacityBounds.JohnsonLower`.

## References

- [BCHKS25] Corollary 1.7.
-/

namespace CodingTheory

open scoped NNReal
open CoreDefinitions ProximityGap

section ReedSolomon

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/- Internal binary-algebra infrastructure for the Johnson-radius lower bound. -/
namespace JohnsonLowerInternal

def IsBinaryLinearized {K : Type} [Field K] (P : Polynomial K) : Prop :=
  ∀ n ∈ P.support, ∃ i : ℕ, n = 2 ^ i

open scoped NNReal in
theorem agreement_card_gt_two_mul_of_lt_seven_eighths
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

def binary_basis_vector {b : ℕ} (i : Fin b) : Fin b → ZMod 2 :=
  fun i' => if i' = i then 1 else 0

open scoped BigOperators in
theorem binary_basis_vector_sum {b : ℕ}
    (x : Fin b → ZMod 2) :
    (∑ i : Fin b, x i • binary_basis_vector i) = x := by
  classical
  funext j
  simp [binary_basis_vector]

private theorem binary_functional_ker_nat_card {b : ℕ}
    (h : (Fin b → ZMod 2) →ₗ[ZMod 2] ZMod 2) (hh : h ≠ 0) :
    Nat.card (LinearMap.ker h) = 2 ^ (b - 1) := by
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero hh
  have hamb : Module.finrank (ZMod 2) (Fin b → ZMod 2) = b := by
    simp
  rw [hamb] at hdim
  have hker : Module.finrank (ZMod 2) (LinearMap.ker h) = b - 1 := by omega
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := LinearMap.ker h), hker]
  norm_num [ZMod.card]

private theorem binary_functional_fiber_card {b : ℕ}
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
    _ = 2 ^ (b - 1) := binary_functional_ker_nat_card h hh

open scoped BigOperators in
noncomputable def binary_functional_root_polynomial {b : ℕ}
    (h : (Fin b → ZMod 2) →ₗ[ZMod 2] ZMod 2) : Polynomial (ZMod 2) := by
  classical
  exact ∏ x : Fin b → ZMod 2, (Polynomial.X - Polynomial.C (h x))

open scoped BigOperators in
private theorem binary_functional_root_polynomial_of_ne_zero {b : ℕ}
    (h : (Fin b → ZMod 2) →ₗ[ZMod 2] ZMod 2) (hh : h ≠ 0) :
    binary_functional_root_polynomial h =
      Polynomial.X ^ (2 ^ (b - 1)) *
        (Polynomial.X - Polynomial.C 1) ^ (2 ^ (b - 1)) := by
  classical
  unfold binary_functional_root_polynomial
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
      rw [Finset.prod_const, Finset.card_univ, binary_functional_fiber_card h hh z]
    _ = Polynomial.X ^ (2 ^ (b - 1)) *
        (Polynomial.X - Polynomial.C 1) ^ (2 ^ (b - 1)) := by
      rw [← Fintype.prod_equiv (ZMod.finEquiv 2).toEquiv
        (fun i : Fin 2 =>
          (Polynomial.X - Polynomial.C ((ZMod.finEquiv 2) i)) ^ (2 ^ (b - 1)))
        (fun z : ZMod 2 => (Polynomial.X - Polynomial.C z) ^ (2 ^ (b - 1)))
        (by intro i; rfl)]
      rw [Fin.prod_univ_two]
      norm_num

theorem binary_functional_lambda_one {b : ℕ}
    (h : (Fin b → ZMod 2) →ₗ[ZMod 2] ZMod 2) (hh : h ≠ 0) :
    (binary_functional_root_polynomial h).coeff (2 ^ (b - 1)) = 1 := by
  rw [binary_functional_root_polynomial_of_ne_zero h hh]
  have hshift := Polynomial.coeff_X_pow_mul
    (((Polynomial.X - Polynomial.C 1) ^ (2 ^ (b - 1))) : Polynomial (ZMod 2))
    (2 ^ (b - 1)) 0
  rw [zero_add] at hshift
  rw [hshift, Polynomial.coeff_zero_eq_eval_zero]
  norm_num
  decide

open scoped BigOperators in
private theorem binary_functional_root_polynomial_zero (b : ℕ) :
    binary_functional_root_polynomial
      (0 : (Fin b → ZMod 2) →ₗ[ZMod 2] ZMod 2) = Polynomial.X ^ (2 ^ b) := by
  classical
  unfold binary_functional_root_polynomial
  simp [ZMod.card]

open scoped BigOperators in
theorem binary_functional_lambda_zero (b : ℕ) (hb : 0 < b) :
    (binary_functional_root_polynomial
      (0 : (Fin b → ZMod 2) →ₗ[ZMod 2] ZMod 2)).coeff (2 ^ (b - 1)) = 0 := by
  rw [binary_functional_root_polynomial_zero]
  rw [Polynomial.coeff_X_pow]
  have hsub : b - 1 < b := by omega
  have hpow : 2 ^ (b - 1) < 2 ^ b := pow_right_strictMono₀ (by omega) hsub
  rw [if_neg (ne_of_lt hpow)]

def binary_graph_embedding_prod {b : ℕ}
    (φ : (Fin b → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2)) :
    (Fin b → ZMod 2) →ₗ[ZMod 2]
      ((Fin b → ZMod 2) × (Fin 2 → ZMod 2)) :=
  LinearMap.prod LinearMap.id φ

private theorem binary_graph_embedding_prod_injective {b : ℕ}
    (φ : (Fin b → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2)) :
    Function.Injective (binary_graph_embedding_prod φ) := by
  intro x y hxy
  exact congrArg Prod.fst hxy

def binary_graph_subspace_prod {b : ℕ}
    (φ : (Fin b → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2)) :
    Submodule (ZMod 2) ((Fin b → ZMod 2) × (Fin 2 → ZMod 2)) :=
  LinearMap.range (binary_graph_embedding_prod φ)

private theorem binary_graph_subspace_prod_finrank {b : ℕ}
    (φ : (Fin b → ZMod 2) →ₗ[ZMod 2] (Fin 2 → ZMod 2)) :
    Module.finrank (ZMod 2) (binary_graph_subspace_prod φ) = b := by
  rw [binary_graph_subspace_prod, LinearMap.finrank_range_of_inj
    (binary_graph_embedding_prod_injective φ)]
  simp

private theorem binary_graph_subspace_prod_injective {b : ℕ} :
    Function.Injective (binary_graph_subspace_prod (b := b)) := by
  intro φ ψ hφψ
  apply LinearMap.ext
  intro x
  funext j
  have hx : binary_graph_embedding_prod φ x ∈ binary_graph_subspace_prod ψ := by
    rw [← hφψ]
    exact ⟨x, rfl⟩
  rcases hx with ⟨y, hy⟩
  have hyx : y = x := congrArg Prod.fst hy
  subst y
  exact congrFun (congrArg Prod.snd hy).symm j


end JohnsonLowerInternal

end ReedSolomon

end CodingTheory
