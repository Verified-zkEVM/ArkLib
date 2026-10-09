/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.Data.MvPolynomial.Multilinear

/-!
# Interpolating read-once matrix programs

A program applies one square matrix per input coordinate to its state, in index order. Replacing
each Boolean layer by its affine interpolation evaluates the multilinear extension of the original
Boolean program. The final observation is an arbitrary linear map, with no multiplicativity law.
-/

@[expose] public section

noncomputable section

namespace Matrix.ReadOnce

open MvPolynomial

variable {C : Type*} [CommRing C] {ι : Type*} [Fintype ι]

/-- Apply each matrix to the state, reading the layers from first to last. -/
def run : {m : ℕ} → (Fin m → Matrix ι ι C) → (ι → C) →ₗ[C] (ι → C)
  | 0, _ => LinearMap.id
  | _ + 1, layers => (run (fun i => layers i.succ)).comp (Matrix.mulVecBilin C C (layers 0))

/-- The empty program is the identity. -/
@[simp]
theorem run_zero (layers : Fin 0 → Matrix ι ι C) (s : ι → C) : run layers s = s := rfl

/-- A nonempty program applies its first layer, then runs the remaining layers. -/
@[simp]
theorem run_succ {m : ℕ} (layers : Fin (m + 1) → Matrix ι ι C) (s : ι → C) :
    run layers s = run (fun i => layers i.succ) (layers 0 *ᵥ s) := rfl

/-- The affine interpolation of a two-branch matrix layer. -/
def interpolate (a : Fin 2 → Matrix ι ι C) (z : C) : Matrix ι ι C :=
  (1 - z) • a 0 + z • a 1

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
    have hcons (b : Fin 2) (y : Fin m → Fin 2) :
        eqTilde (fun i : Fin (m + 1) =>
          ((Fin.cons (α := fun _ : Fin (m + 1) => Fin 2) b y i : Fin 2) : C)) z =
          (if b = 0 then 1 - z 0 else z 0) * eqTilde (y : Fin m → C) (fun i => z i.succ) := by
      rw [show z = Fin.cons (z 0) (fun i => z i.succ) from (Fin.cons_self_tail z).symm]
      rw [show (fun i : Fin (m + 1) => ((Fin.cons (α := fun _ : Fin (m + 1) => Fin 2) b y i :
          Fin 2) : C)) = Fin.cons ((b : Fin 2) : C) (fun i => ((y i : Fin 2) : C)) from
        funext fun i => Fin.cases rfl (fun _ => rfl) i, eqTilde_cons]
      fin_cases b <;> simp
    simp only [Fintype.sum_prod_type, Fin.consEquiv, Equiv.coe_fn_mk, hcons,
      Fin.sum_univ_two, Fin.isValue, ↓reduceIte, run_succ, Fin.cons_zero, Fin.cons_succ]
    simp only [Finset.smul_sum, smul_smul, show (1 : Fin 2) ≠ 0 by decide, ite_false]

/-- Any linear observation of the interpolated program evaluates its Boolean multilinear
extension. -/
theorem observe_interpolate {m : ℕ} (layers : Fin m → Fin 2 → Matrix ι ι C)
    (z : Fin m → C) (s : ι → C) (observe : (ι → C) →ₗ[C] C) :
    observe (run (fun i => interpolate (layers i) (z i)) s) =
      eval z (MLE (fun y : Fin m → Fin 2 => observe (run (fun i => layers i (y i)) s))) := by
  rw [run_interpolate, map_sum, MLE_eval]
  exact Finset.sum_congr rfl fun y _ => observe.map_smul _ _

end Matrix.ReadOnce

end
