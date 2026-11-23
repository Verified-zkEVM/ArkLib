/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/

import ArkLib.Data.CodingTheory.ListDecodability.Bounds.ReedSolomon.IntersectionMatrix
import Mathlib.Data.Rat.Defs

/-! # Intersection matrix acceptance tests

Two vertices, degree `k = 2`, evaluation points `0, 1` over `ℚ`. With both coordinates joining
both vertices, a degree-`< 2` polynomial vanishing at `0` and `1` is zero, so the hypergraph is
rigid; with the second coordinate joining only one vertex, the codewords `(0, 1)` and `(0, 0)`
witness that it is not.
-/

open Polynomial ReedSolomon

private def points : Fin 2 ↪ ℚ :=
  ⟨![0, 1], fun a b h ↦ by fin_cases a <;> fin_cases b <;> simp_all⟩

private theorem points_apply (i : Fin 2) : points i = ![0, 1] i :=
  rfl

private def bothEdges : Fin 2 → Finset (Fin 2) := fun _ ↦ Finset.univ

private theorem min_univ_fin_two : (Finset.univ : Finset (Fin 2)).min = (0 : Fin 2) := by
  decide

private def secondRows : Fin 1 × Fin 2 → IntersectionRow bothEdges := fun c ↦
  ⟨(c.2, 1), Finset.mem_univ _, by simp only [bothEdges]; decide⟩

-- The two rows `(0, 1)` and `(1, 1)` evaluate to the Vandermonde matrix `!![1, 0; 1, 1]`.
example : IsRigid bothEdges 2 points :=
  (isRigid_iff_exists_aeval_det_ne_zero (R := ℚ)).2 ⟨secondRows, by
    rw [AlgHom.map_det, ← Matrix.det_submatrix_equiv_self (Equiv.uniqueProd (Fin 2) (Fin 1)).symm,
      Matrix.det_fin_two]
    simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply,
      intersectionMatrix_apply]
    simp [secondRows, bothEdges, min_univ_fin_two, points_apply]⟩

-- Each variable occurs in one row of degree at most `1`.
example (i : Fin 2) :
    ((intersectionMatrix ℚ bothEdges 2).submatrix secondRows id).det.degreeOf i ≤ 1 :=
  degreeOf_det_submatrix_le secondRows i

private def oneEdge : Fin 1 → Finset (Fin 2) := fun _ ↦ Finset.univ

-- From the definition: a constant tuple vanishing at the last vertex that agrees at `0` is zero.
private theorem oneEdge_isRigid : IsRigid oneEdge 1 fun _ ↦ (0 : ℚ) := by
  intro f hf hlast hagree
  have hconst := eq_C_of_degree_le_zero
    (Nat.WithBot.lt_one_iff_le_zero.1 (mem_degreeLT.1 (hf 0)))
  have h0 := hagree 0 0 (Finset.mem_univ _) (Fin.last 1) (Finset.mem_univ _)
  rw [hlast, hconst, eval_C, eval_zero] at h0
  funext j
  fin_cases j
  · change f 0 = 0
    rw [hconst, h0, map_zero]
  · exact hlast

-- Rigidity gives a `1 × 1` minor that does not vanish at the evaluation point.
example : ∃ ρ : Fin 1 × Fin 1 → IntersectionRow oneEdge,
    MvPolynomial.aeval (fun _ ↦ (0 : ℚ)) ((intersectionMatrix ℚ oneEdge 1).submatrix ρ id).det ≠
      0 :=
  (isRigid_iff_exists_aeval_det_ne_zero (R := ℚ)).1 oneEdge_isRigid

private def agreementEdges : Fin 2 → Finset (Fin 2) := ![Finset.univ, {1}]

private def codewords : Fin 2 → Fin 2 → ℚ := ![![0, 1], 0]

-- `agreementEdges` is the agreement hypergraph of the codewords `X` and `0` with the word `0`.
example : ¬IsRigid agreementEdges 2 points := by
  refine not_isRigid_of_mem_code (c := codewords) (fun j ↦ ?_)
    ⟨0, 1, fun h ↦ by simpa [codewords] using congrFun h 1⟩ fun i j hj j' hj' ↦ ?_
  · fin_cases j
    · exact mem_code_of_polynomial_of_natDegree_lt_of_eval X (by simp)
        fun x ↦ by fin_cases x <;> simp [codewords, points_apply]
    · simp [codewords]
  · fin_cases i
    · fin_cases j <;> fin_cases j' <;> simp [codewords]
    · simp only [agreementEdges, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero,
        Finset.mem_singleton] at hj hj'
      rw [hj, hj']
