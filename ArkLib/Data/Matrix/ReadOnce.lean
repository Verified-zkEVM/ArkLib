/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.Data.MvPolynomial.Multilinear
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Interpolating read-once matrix programs

A program applies one square matrix per input coordinate to its state, in index order. Replacing
each Boolean layer by its affine interpolation evaluates the multilinear extension of the original
Boolean program. The final observation is an arbitrary linear map, with no multiplicativity law.
-/

noncomputable section

namespace Matrix.ReadOnce

open MvPolynomial

variable {C : Type*} [CommRing C] {ι : Type*} [Fintype ι]

/-- Apply each matrix to the state, reading the layers from first to last. -/
def run : {m : ℕ} → (Fin m → Matrix ι ι C) → (ι → C) →ₗ[C] (ι → C)
  | 0, _ => LinearMap.id
  | _ + 1, layers => (run (fun i => layers i.succ)).comp (Matrix.mulVecBilin C C (layers 0))

@[simp]
theorem run_zero (layers : Fin 0 → Matrix ι ι C) (s : ι → C) : run layers s = s := rfl

@[simp]
theorem run_succ {m : ℕ} (layers : Fin (m + 1) → Matrix ι ι C) (s : ι → C) :
    run layers s = run (fun i => layers i.succ) (layers 0 *ᵥ s) := rfl

/-- The affine interpolation of a two-branch matrix layer. -/
def interpolate (a : Fin 2 → Matrix ι ι C) (z : C) : Matrix ι ι C :=
  (1 - z) • a 0 + z • a 1

private theorem eqTilde_cons {m : ℕ} (b : Fin 2) (y : Fin m → Fin 2)
    (z : Fin (m + 1) → C) :
    eqTilde
      (fun i : Fin (m + 1) =>
        ((Fin.cons (α := fun _ : Fin (m + 1) => Fin 2) b y i : Fin 2) : C)) z =
      (if b = 0 then 1 - z 0 else z 0) * eqTilde (y : Fin m → C) (fun i => z i.succ) := by
  simp only [eqTilde_eq_prod, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]
  fin_cases b <;> simp

/-- Layer interpolation agrees with the equality-weighted Boolean expansion of the entire state. -/
theorem run_interpolate {m : ℕ} (layers : Fin m → Fin 2 → Matrix ι ι C)
    (z : Fin m → C) (s : ι → C) :
    run (fun i => interpolate (layers i) (z i)) s =
      ∑ y : Fin m → Fin 2, eqTilde (y : Fin m → C) z • run (fun i => layers i (y i)) s := by
  induction m generalizing s with
  | zero => simp [eqTilde_eq_prod]
  | succ m ih =>
    rw [run_succ]
    simp only [interpolate, add_mulVec, smul_mulVec, map_add, map_smul]
    change (1 - z 0) • run (fun i => interpolate (layers i.succ) (z i.succ))
      (layers 0 0 *ᵥ s) + z 0 • run (fun i => interpolate (layers i.succ) (z i.succ))
      (layers 0 1 *ᵥ s) = _
    rw [ih, ih]
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => Fin 2)).sum_comp]
    simp only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk, eqTilde_cons,
      Fin.sum_univ_two, Fin.isValue, ↓reduceIte, run_succ, Fin.cons_zero, Fin.cons_succ]
    simp only [Finset.smul_sum, smul_smul, show (1 : Fin 2) ≠ 0 by decide, if_false]

/-- Any linear observation of the interpolated program evaluates its Boolean multilinear
extension. -/
theorem observe_interpolate {m : ℕ} (layers : Fin m → Fin 2 → Matrix ι ι C)
    (z : Fin m → C) (s : ι → C) (observe : (ι → C) →ₗ[C] C) :
    observe (run (fun i => interpolate (layers i) (z i)) s) =
      eval z (MLE (fun y : Fin m → Fin 2 => observe (run (fun i => layers i (y i)) s))) := by
  rw [run_interpolate, map_sum, MLE_eval]
  exact Finset.sum_congr rfl fun y _ => observe.map_smul _ _

/-- The same evaluator instrumented with a counter incremented at each matrix-vector action. -/
def runCounted : {m : ℕ} → (Fin m → Matrix ι ι C) → (ι → C) → (ι → C) × ℕ
  | 0, _, s => (s, 0)
  | _ + 1, layers, s =>
    let result := runCounted (fun i => layers i.succ) (layers 0 *ᵥ s)
    (result.1, result.2 + 1)

/-- Instrumentation preserves the state and counts exactly the number of layers. -/
theorem runCounted_eq {m : ℕ} (layers : Fin m → Matrix ι ι C) (s : ι → C) :
    runCounted layers s = (run layers s, m) := by
  induction m generalizing s with
  | zero => rfl
  | succ m ih => simp only [runCounted, ih, run_succ]

end Matrix.ReadOnce

end
