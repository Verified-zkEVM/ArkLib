/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.Polynomial.CosetChunks
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.ComputeDegree
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-!
# Coset-chunk acceptance examples

A shifted two-chunk decomposition reconstructs a cubic, and a three-chunk example exercises
mask cancellation beyond the dyadic case. The tests cover one chunk and the excluded degree
boundary. The formal polynomials are mathematical views; ordinary executable callers below
check the scalar normalization weights at runtime.
-/

open Polynomial Finset Polynomial.CosetChunks

namespace ArkLibTest.CosetChunks

-- The public theorem supplies the verifier's evaluation identity at any point.
example {K : Type*} [Field K] {s w : K} {c m : ℕ}
    (hw : IsPrimitiveRoot w (c * m)) (hs : s ≠ 0) (hc : 0 < c) (hm : 0 < m)
    (Q : K[X]) (hQ : Q.degree < (c * m : ℕ)) (z : K) :
    ∑ i ∈ range c, (chunkL s w c m i).eval z * (chunkInterp s w c m Q i).eval z = Q.eval z := by
  have h := congrArg (eval z) (sum_chunkL_mul_chunkInterp hw hs hc hm Q hQ)
  simpa [eval_finsetSum, eval_mul] using h

instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance : Fact (Nat.Prime 13) := ⟨by decide⟩

private lemma primitive_root_two_zmod_five : IsPrimitiveRoot (2 : ZMod 5) 4 := by
  apply IsPrimitiveRoot.mk_of_lt _ (by decide) (by decide)
  intro l hl hlt
  interval_cases l <;> decide

private lemma primitive_root_four_zmod_thirteen : IsPrimitiveRoot (4 : ZMod 13) 6 := by
  apply IsPrimitiveRoot.mk_of_lt _ (by decide) (by decide)
  intro l hl hlt
  interval_cases l <;> decide

-- Non-unit shift, two chunks with two points each; degree reaches the allowed maximum.
private noncomputable def cubic : (ZMod 5)[X] := X ^ 3 + X ^ 2 + 1

private lemma interp_degree (i : ℕ) (hi : i < 2) :
    (chunkInterp (3 : ZMod 5) 2 2 2 cubic i).degree < 2 := by
  have h := natDegree_chunkInterp_le primitive_root_two_zmod_five (by decide : (3 : ZMod 5) ≠ 0)
    (by decide : 0 < 2) (by decide : 0 < 2) cubic hi
  apply degree_le_natDegree.trans_lt
  exact_mod_cast (show (chunkInterp (3 : ZMod 5) 2 2 2 cubic i).natDegree < 2 by omega)

private lemma interp_zero : chunkInterp (3 : ZMod 5) 2 2 2 cubic 0 = C 4 * X := by
  refine eq_of_degrees_lt_of_eval_index_eq (s := (univ : Finset (Fin 2)))
    (v := fun t : Fin 2 => point (3 : ZMod 5) 2 2 0 t)
    (point_injective (s := (3 : ZMod 5)) (c := 2) (m := 2) primitive_root_two_zmod_five
      (by decide) (by decide) (by decide : 0 < 2)).injOn
    (by simpa using interp_degree 0 (by decide))
    (by rw [degree_mul, degree_C (by decide : (4 : ZMod 5) ≠ 0), degree_X]; norm_num) ?_
  intro t _
  unfold chunkInterp
  rw [Lagrange.eval_interpolate_at_node _
    (point_injective (s := (3 : ZMod 5)) (c := 2) (m := 2) primitive_root_two_zmod_five
      (by decide) (by decide) (by decide : 0 < 2)).injOn (mem_univ _)]
  fin_cases t <;> norm_num [cubic, point] <;> decide

private lemma interp_one : chunkInterp (3 : ZMod 5) 2 2 2 cubic 1 = X + C 2 := by
  refine eq_of_degrees_lt_of_eval_index_eq (s := (univ : Finset (Fin 2)))
    (v := fun t : Fin 2 => point (3 : ZMod 5) 2 2 1 t)
    (point_injective (s := (3 : ZMod 5)) (c := 2) (m := 2) primitive_root_two_zmod_five
      (by decide) (by decide) (by decide : 1 < 2)).injOn
    (by simpa using interp_degree 1 (by decide)) (by simp) ?_
  intro t _
  unfold chunkInterp
  rw [Lagrange.eval_interpolate_at_node _
    (point_injective (s := (3 : ZMod 5)) (c := 2) (m := 2) primitive_root_two_zmod_five
      (by decide) (by decide) (by decide : 1 < 2)).injOn (mem_univ _)]
  fin_cases t <;> norm_num [cubic, point] <;> decide

-- The two low-degree interpolants reconstruct the cubic as a polynomial identity.
example : chunkL (3 : ZMod 5) 2 2 2 0 * (C 4 * X) +
    chunkL (3 : ZMod 5) 2 2 2 1 * (X + C 2) = cubic := by
  have h := sum_chunkL_mul_chunkInterp primitive_root_two_zmod_five (by decide : (3 : ZMod 5) ≠ 0)
    (by decide : 0 < 2) (by decide : 0 < 2) cubic (by unfold cubic; compute_degree; norm_num)
  simpa [sum_range_succ, interp_zero, interp_one] using h

-- The last mask has the correct sign and includes all earlier chunks.
example (t : ℕ → (ZMod 5)[X]) : mask (3 : ZMod 5) 2 2 2 t 1 = -t 0 := by
  have hw0 : chunkWeight (3 : ZMod 5) 2 2 2 0 = 2 := by decide +kernel
  have hw1 : chunkWeight (3 : ZMod 5) 2 2 2 1 = 2 := by decide +kernel
  simp [mask, hw0, hw1, show (2 : ZMod 5) ≠ 0 by decide]

example (t : ℕ → (ZMod 13)[X]) : mask (2 : ZMod 13) 4 3 2 t 2 = -(t 0 + t 1) := by
  have hw0 : chunkWeight (2 : ZMod 13) 4 3 2 0 = 9 := by decide +kernel
  have hw1 : chunkWeight (2 : ZMod 13) 4 3 2 1 = 9 := by decide +kernel
  have hw2 : chunkWeight (2 : ZMod 13) 4 3 2 2 = 9 := by decide +kernel
  simp [mask, sum_range_succ, hw0, hw1, hw2, show (9 : ZMod 13) ≠ 0 by decide]

-- A nontrivial three-chunk caller preserves the weighted polynomial identity.
example :
    ∑ i ∈ range 3, chunkL (2 : ZMod 13) 4 3 2 i *
      (C (i : ZMod 13) + chunkZ 2 4 2 i * mask 2 4 3 2 (fun j => X ^ (j + 1)) i) =
    ∑ i ∈ range 3, chunkL (2 : ZMod 13) 4 3 2 i * C (i : ZMod 13) := by
  exact sum_chunkL_mul_masked primitive_root_four_zmod_thirteen (by decide : (2 : ZMod 13) ≠ 0)
    (by decide : 0 < 3) (by decide : 0 < 2) (fun i => C (i : ZMod 13)) (fun j => X ^ (j + 1))

-- m = 0 degenerates to the zero polynomial; positivity belongs in the overview assumptions.
example {K : Type*} [Field K] (s w : K) (i : ℕ) : chunkZ s w 0 i = 0 := by simp [chunkZ]

-- c = 1 has one interpolant and a zero final mask.
example {K : Type*} [Field K] (s w : K) (m : ℕ) (t : ℕ → K[X]) :
    mask s w 1 m t 0 = 0 := by simp [mask]

-- The single-chunk boundary also works for a nonconstant polynomial.
example : chunkInterp (3 : ZMod 5) (-1) 1 2 (X + 1) 0 = X + 1 := by
  have hw : IsPrimitiveRoot (-1 : ZMod 5) (1 * 2) := IsPrimitiveRoot.neg_one 5 (by decide)
  have h := sum_chunkL_mul_chunkInterp (c := 1) (m := 2) hw
    (by decide : (3 : ZMod 5) ≠ 0) (by decide) (by decide) (X + 1)
    (by compute_degree; norm_num)
  simpa [sum_range_succ, chunkL] using h

-- At the excluded degree boundary, the full-domain vanisher has zero chunk interpolants.
private lemma interp_vanisher (i : Fin 2) :
    chunkInterp (3 : ZMod 5) 2 2 2 (X ^ 4 - 1) i = 0 := by
  have hz : (fun t : Fin 2 => (X ^ 4 - 1 : (ZMod 5)[X]).eval
      (point (3 : ZMod 5) 2 2 i t)) = 0 := by
    funext t
    fin_cases i <;> fin_cases t <;> norm_num [point] <;> decide
  unfold chunkInterp
  rw [hz, map_zero]

example : ∑ i ∈ range 2, chunkL (3 : ZMod 5) 2 2 2 i *
    chunkInterp (3 : ZMod 5) 2 2 2 (X ^ 4 - 1) i ≠ X ^ 4 - 1 := by
  have hzero : ∑ i ∈ range 2, chunkL (3 : ZMod 5) 2 2 2 i *
      chunkInterp (3 : ZMod 5) 2 2 2 (X ^ 4 - 1) i = 0 := by
    apply sum_eq_zero
    intro i hi
    rw [interp_vanisher ⟨i, mem_range.mp hi⟩, mul_zero]
  rw [hzero]
  intro h
  have he := congrArg (eval (0 : ZMod 5)) h
  norm_num at he

-- This ordinary caller requires generated code for the public scalar API.
private def weightRuntimeChecks : IO Unit := do
  unless List.ofFn (fun i : Fin 2 => chunkWeight (3 : ZMod 5) 2 2 2 i) = [2, 2] do
    throw (IO.userError "Incorrect normalization weights for the shifted two-chunk domain")
  unless List.ofFn (fun i : Fin 3 => chunkWeight (2 : ZMod 13) 4 3 2 i) = [9, 9, 9] do
    throw (IO.userError "Incorrect normalization weights for the three-chunk domain")
  unless chunkWeight (1 : ZMod 5) 1 1 1 0 = 1 do
    throw (IO.userError "Incorrect normalization weight for the single-chunk domain")
  IO.println "Coset-chunk runtime checks passed."

/-- info: Coset-chunk runtime checks passed. -/
#guard_msgs in
#eval weightRuntimeChecks

end ArkLibTest.CosetChunks
