/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
/-!
# Evaluation-and-tail coordinates for square-system capture

A polynomial with `K` centered coefficients is determined by its values at `k` distinct points
and its coefficient tail in degrees `k, ..., K - 1`. This is the characteristic-free
Vandermonde-plus-tail input to the Reed--Solomon square-subsystem argument. The formulation keeps
the ambient chart precision `K` separate from the actual message dimension `k`, including
`K = k` where the tail is empty.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.SquareSystems

open Polynomial
open scoped BigOperators

variable {F : Type*} [Field F]

/-- The ambient coefficient index belonging to a tail offset. -/
def tailIndex {K k : ℕ} (hk : k ≤ K) (j : Fin (K - k)) : Fin K :=
  ⟨k + j, by omega⟩

/-- Values at `k` centered nodes, followed by all ambient coefficients from degree `k` onward. -/
def evaluationTailMap (K k : ℕ) (hk : k ≤ K) (center : F) (points : Fin k ↪ F) :
    (Fin K → F) →ₗ[F] ((Fin k → F) × (Fin (K - k) → F)) where
  toFun c :=
    (fun i ↦ ∑ j : Fin K, c j * (points i - center) ^ (j : ℕ),
      fun j ↦ c (tailIndex hk j))
  map_add' c c' := by
    ext i <;> simp [Finset.sum_add_distrib, add_mul]
  map_smul' a c := by
    ext i <;> simp [Finset.mul_sum, mul_assoc]

@[simp]
theorem evaluationTailMap_fst (K k : ℕ) (hk : k ≤ K) (center : F) (points : Fin k ↪ F)
    (c : Fin K → F) (i : Fin k) :
    (evaluationTailMap K k hk center points c).1 i =
      ∑ j : Fin K, c j * (points i - center) ^ (j : ℕ) := rfl

@[simp]
theorem evaluationTailMap_snd (K k : ℕ) (hk : k ≤ K) (center : F) (points : Fin k ↪ F)
    (c : Fin K → F) (j : Fin (K - k)) :
    (evaluationTailMap K k hk center points c).2 j = c (tailIndex hk j) := rfl

/-- The evaluation-and-tail coordinate map is injective. Equivalently, a degree-`< K`
polynomial with zero tail has degree `< k`, and `k` distinct zeroes then force it to vanish. -/
theorem evaluationTailMap_injective (K k : ℕ) (hk : k ≤ K) (center : F)
    (points : Fin k ↪ F) : Function.Injective (evaluationTailMap K k hk center points) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro c hc
  let pK : Polynomial.degreeLT F K := (Polynomial.degreeLTEquiv F K).symm c
  let P : F[X] := pK
  have htail : ∀ j : Fin (K - k), c (tailIndex hk j) = 0 := by
    intro j
    have h := congrFun (congrArg Prod.snd hc) j
    simpa using h
  have hdegree : P.degree < k := by
    rw [Polynomial.degree_lt_iff_coeff_zero]
    intro j hj
    by_cases hjK : j < K
    · let jK : Fin K := ⟨j, hjK⟩
      let tail : Fin (K - k) := ⟨j - k, by omega⟩
      have hcoeff := congrFun ((Polynomial.degreeLTEquiv F K).apply_symm_apply c) jK
      have htail' := htail tail
      change P.coeff j = 0
      change P.coeff j = c jK at hcoeff
      rw [hcoeff]
      simpa [tail, tailIndex, Nat.add_sub_of_le hj] using htail'
    · exact ((Polynomial.degree_lt_iff_coeff_zero P K).mp
        (Polynomial.mem_degreeLT.mp pK.property) j (by omega))
  have heval : ∀ i : Fin k, P.eval (points i - center) = 0 := by
    intro i
    have h := congrFun (congrArg Prod.fst hc) i
    rw [Polynomial.eval_eq_sum_degreeLTEquiv pK.property]
    simpa [pK] using h
  have hP : P = 0 := by
    let shiftedPoints : Fin k ↪ F :=
      ⟨fun i ↦ points i - center, fun _ _ h ↦ points.injective (sub_left_inj.mp h)⟩
    apply Polynomial.eq_zero_of_degree_lt_of_eval_index_eq_zero (Finset.univ : Finset (Fin k))
      shiftedPoints.injective.injOn
    · simpa using hdegree
    · intro i _
      change P.eval (points i - center) = 0
      exact heval i
  apply (Polynomial.degreeLTEquiv F K).symm.injective
  apply Subtype.ext
  simpa [P, pK] using hP

/-- Evaluation-and-tail coordinates give a linear equivalence. The codomain has dimension
`k + (K-k) = K`, so injectivity supplies surjectivity. -/
noncomputable def evaluationTailLinearEquiv (K k : ℕ) (hk : k ≤ K) (center : F)
    (points : Fin k ↪ F) : (Fin K → F) ≃ₗ[F] ((Fin k → F) × (Fin (K - k) → F)) :=
  (evaluationTailMap K k hk center points).linearEquivOfInjective
    (evaluationTailMap_injective K k hk center points) (by
      rw [Module.finrank_prod, Module.finrank_pi, Module.finrank_pi]
      simp [Nat.add_sub_of_le hk])

@[simp]
theorem evaluationTailLinearEquiv_apply (K k : ℕ) (hk : k ≤ K) (center : F)
    (points : Fin k ↪ F) (c : Fin K → F) :
    evaluationTailLinearEquiv K k hk center points c = evaluationTailMap K k hk center points c :=
  rfl

end ReedSolomon.HiddenDerivative.SquareSystems
