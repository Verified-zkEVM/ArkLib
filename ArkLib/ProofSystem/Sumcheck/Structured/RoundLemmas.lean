/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Sumcheck.Structured.SingleRound
public import ArkLib.Data.Probability.Instances
public import ArkLib.Data.MvPolynomial.RestrictDegree

/-!
# Algebra of a structured sum-check round

The facts a structured sum-check round argument needs about prefix fixing and round polynomials.
The prefix-fixing algebra itself (`MvPolynomial.fixFirstVariablesOfMQP_eq_bind₁`,
`MvPolynomial.eval_fixFirstVariablesOfMQP`, `MvPolynomial.fixFirstVariablesOfMQP_succ`) lives with
`fixFirstVariablesOfMQP` in `ArkLib/Data/MvPolynomial/RestrictDegree.lean`.

* `projectToMidSumcheckPolyWithParam_succ`: the projected round polynomial at the next round is
  the current one with its first variable fixed to the challenge, and
  `getRoundProverFinalOutput_H` identifies the honest prover's next witness with that fixing.
* `sum_getSumcheckRoundPoly_uniform` and `eval_getSumcheckRoundPoly_uniform`: over a uniform
  domain, the univariate round polynomial sums to the round claim and evaluates at a challenge to
  the next round claim.
* `prob_eval_eq_le`: distinct univariate polynomials of degree at most `d` agree at a uniform
  point with probability at most `d / |L|`, the round error `roundKnowledgeError`. It is the
  degree-bounded form of the root bound `Probability.prob_polynomial_eval_eq_le`.
-/

@[expose] public section

noncomputable section

open Finset MvPolynomial
open scoped NNReal ENNReal ProbabilityTheory Polynomial

namespace Sumcheck.Structured

variable {L : Type} [CommRing L] (ℓ : ℕ)

/-- The projected round polynomial at round `i + 1` is the round-`i` projection with its first
variable fixed to the new challenge. The renaming identifies `ℓ - i - 1` with `ℓ - (i + 1)`. -/
theorem projectToMidSumcheckPolyWithParam_succ {Context : Type}
    (param : SumcheckMultiplierParam L ℓ Context) (ctx : Context) (t : MultilinearPoly L ℓ)
    (i : Fin ℓ) (challenges : Fin i.castSucc → L) (c : L) (h : ℓ - i - 1 = ℓ - i.succ) :
    rename (Fin.cast h) (fixFirstVariablesOfMQP (ℓ - i) ⟨1, by omega⟩
        (projectToMidSumcheckPolyWithParam ℓ param ctx t i.castSucc challenges).val
        (fun _ => c)) =
      (projectToMidSumcheckPolyWithParam ℓ param ctx t i.succ (Fin.snoc challenges c)).val :=
  fixFirstVariablesOfMQP_succ i _ challenges c h

variable {Context : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} {d : ℕ}

/-- The honest prover's next round polynomial is its current one with the first variable fixed to
the challenge. -/
theorem getRoundProverFinalOutput_H (i : Fin ℓ)
    (stmt : Statement (L := L) (ℓ := ℓ) Context i.castSucc) (oStmt : ∀ j, OStmtIn j)
    (wit : SumcheckWitness L ℓ i.castSucc d) (h : L⦃≤ d⦄[X]) (c : L)
    (hdim : ℓ - i - 1 = ℓ - i.succ) :
    (getRoundProverFinalOutput ℓ Context (OStmtIn := OStmtIn) d i
      (stmt, oStmt, wit, h, c)).2.H.val =
      rename (Fin.cast hdim) (fixFirstVariablesOfMQP (ℓ - i) ⟨1, by omega⟩ wit.H.val
        (fun _ => c)) :=
  cast_eq_rename_finCast hdim (congrArg (fun k => MvPolynomial (Fin k) L) hdim) _

/-- Evaluating the univariate round polynomial at `c` sums the round polynomial over the remaining
domain with its first variable set to `c`. -/
theorem eval_getSumcheckRoundPoly (D : SumcheckDomain L ℓ) (i : Fin ℓ)
    (H : L⦃≤ d⦄[X Fin (ℓ - i.castSucc)]) (c : L)
    (hm : ℓ - i.castSucc = (ℓ - i.castSucc - 1) + 1) :
    (getSumcheckRoundPoly ℓ D i H).val.eval c =
      ∑ x ∈ (D.drop (i.castSucc + 1)).cube,
        MvPolynomial.eval (Fin.cons c x ∘ Fin.cast hm) H.val := by
  unfold getSumcheckRoundPoly
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_map]
  apply Finset.sum_congr rfl
  intro x _
  let ψ : Fin (ℓ - ↑i.castSucc) ≃ Fin ((ℓ - ↑i.castSucc - 1) + 1) :=
    { toFun := Fin.cast hm
      invFun := Fin.cast hm.symm
      left_inv := fun _ => Fin.ext (by simp)
      right_inv := fun _ => Fin.ext (by simp) }
  have h_eval_eq : MvPolynomial.eval (Fin.cons c x ∘ Fin.cast hm) H.val =
      MvPolynomial.eval (Fin.cons c x) (MvPolynomial.rename ψ H.val) := by
    rw [MvPolynomial.eval_rename]
    rfl
  rw [h_eval_eq]
  trans MvPolynomial.eval (Fin.insertNth 0 c x) (MvPolynomial.rename ψ H.val)
  swap
  · rw [Fin.insertNth_zero]
    rfl
  · rw [MvPolynomial.eval_eq_eval_mv_eval_finSuccEquivNth (p := 0)]
    have h_eval_append :
        MvPolynomial.eval (Fin.append (fun j : Fin 0 => j.elim0) x ∘
          Fin.cast (Nat.zero_add _).symm) = MvPolynomial.eval x := by
      ext j
      · simp only [RingHom.comp_apply, Fin.elim0_append, MvPolynomial.eval_C]
      · simp only [Fin.elim0_append, MvPolynomial.eval_X, Function.comp_apply, Fin.cast_cast]
        rfl
    rw [h_eval_append]
    simp only [Polynomial.eval_map]
    have h_cast_eq : cast (congrArg (fun k => L[X Fin k]) hm) H.val =
        MvPolynomial.rename ψ H.val :=
      cast_eq_rename_finCast hm _ _
    exact congrArg
      (fun p => Polynomial.eval₂ (MvPolynomial.eval x) c ((MvPolynomial.finSuccEquivNth L 0) p))
      h_cast_eq

section Uniform

variable {m : ℕ} (D₀ : Fin m ↪ L)

/-- Over a uniform domain, summing the univariate round polynomial over the domain gives the sum
of the round polynomial over the remaining cube: the honest round check. -/
theorem sum_getSumcheckRoundPoly_uniform (i : Fin ℓ) (H : L⦃≤ d⦄[X Fin (ℓ - i.castSucc)]) :
    ∑ b ∈ (SumcheckDomain.uniform D₀ ℓ).points i,
        (getSumcheckRoundPoly ℓ (SumcheckDomain.uniform D₀ ℓ) i H).val.eval b =
      ∑ x ∈ (SumcheckDomain.uniform D₀ (ℓ - i.castSucc)).cube, H.val.eval x := by
  have hm : ℓ - i.castSucc = (ℓ - i.castSucc - 1) + 1 := by
    have := i.isLt
    simp only [Fin.val_castSucc]
    omega
  simp_rw [eval_getSumcheckRoundPoly ℓ _ i H _ hm]
  let e : (Fin (ℓ - i.castSucc) → L) ≃ (Fin ((ℓ - i.castSucc - 1) + 1) → L) :=
    Equiv.piCongrLeft' (fun _ => L) (finCongr hm)
  have hcube : (SumcheckDomain.uniform D₀ ((ℓ - i.castSucc - 1) + 1)).cube =
      (SumcheckDomain.uniform D₀ (ℓ - i.castSucc)).cube.map e.toEmbedding := by
    ext y
    simp only [SumcheckDomain.mem_cube, SumcheckDomain.points_uniform, Finset.mem_map,
      Equiv.toEmbedding_apply]
    constructor
    · intro hy
      refine ⟨e.symm y, fun j => hy _, by simp⟩
    · rintro ⟨x, hx, rfl⟩ j
      exact hx _
  have hsum : ∑ x ∈ (SumcheckDomain.uniform D₀ (ℓ - i.castSucc)).cube, H.val.eval x =
      ∑ y ∈ (SumcheckDomain.uniform D₀ ((ℓ - i.castSucc - 1) + 1)).cube,
        MvPolynomial.eval (y ∘ Fin.cast hm) H.val := by
    rw [hcube, Finset.sum_map]
    refine Finset.sum_congr rfl fun x _ => ?_
    congr 1
  rw [hsum, SumcheckDomain.sum_cube_succ]
  rfl

/-- Over a uniform domain, the univariate round polynomial evaluates at the challenge to the sum of
the next round polynomial over the remaining cube: the honest next-round claim. -/
theorem eval_getSumcheckRoundPoly_uniform (i : Fin ℓ) (H : L⦃≤ d⦄[X Fin (ℓ - i.castSucc)])
    (c : L) (hdim : ℓ - i - 1 = ℓ - i.succ) :
    (getSumcheckRoundPoly ℓ (SumcheckDomain.uniform D₀ ℓ) i H).val.eval c =
      ∑ x ∈ (SumcheckDomain.uniform D₀ (ℓ - i.succ)).cube,
        (rename (Fin.cast hdim) (fixFirstVariablesOfMQP (ℓ - i) ⟨1, by omega⟩ H.val
          (fun _ => c))).eval x := by
  have hm : ℓ - i.castSucc = (ℓ - i.castSucc - 1) + 1 := by
    have := i.isLt
    simp only [Fin.val_castSucc]
    omega
  rw [eval_getSumcheckRoundPoly ℓ _ i H c hm]
  let e : (Fin (ℓ - i.succ) → L) ≃ (Fin (ℓ - i.castSucc - 1) → L) :=
    Equiv.piCongrLeft' (fun _ => L) (finCongr hdim.symm)
  have hcube : ((SumcheckDomain.uniform D₀ ℓ).drop (i.castSucc + 1)).cube =
      (SumcheckDomain.uniform D₀ (ℓ - i.succ)).cube.map e.toEmbedding := by
    ext y
    simp only [SumcheckDomain.drop_uniform, SumcheckDomain.mem_cube,
      SumcheckDomain.points_uniform, Finset.mem_map, Equiv.toEmbedding_apply]
    constructor
    · intro hy
      refine ⟨e.symm y, fun j => hy _, by simp⟩
    · rintro ⟨x, hx, rfl⟩ j
      exact hx _
  rw [hcube, Finset.sum_map]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [eval_rename]
  erw [eval_fixFirstVariablesOfMQP]
  refine congrArg (fun f => eval f H.val) (funext fun j => ?_)
  by_cases hj : j.val < 1
  · have hj0 : Fin.cast hm j = 0 := Fin.ext (by simp only [Fin.val_cast, Fin.val_zero]; omega)
    simp only [hj, ↓reduceDIte, Function.comp_apply, hj0, Fin.cons_zero]
  · obtain ⟨k, hk⟩ : ∃ k : Fin (ℓ - i.castSucc - 1), Fin.cast hm j = k.succ :=
      ⟨⟨j.val - 1, by have := j.isLt; simp only [Fin.val_castSucc] at *; omega⟩,
        Fin.ext (by simp only [Fin.val_cast, Fin.val_succ]; omega)⟩
    simp only [hj, ↓reduceDIte, Function.comp_apply, hk, Fin.cons_succ]
    simp only [e, Equiv.toEmbedding_apply, Equiv.piCongrLeft'_apply]
    congr 1
    apply Fin.ext
    have := congrArg Fin.val hk
    simp only [Fin.val_cast, Fin.val_succ] at this ⊢
    simp only [Fin.val_castSucc, finCongr_symm, finCongr_apply, Fin.val_cast]
    omega

end Uniform

/-- Two distinct univariate polynomials of degree at most `d` agree at a uniform point with
probability at most `d / |L|`, the round error `roundKnowledgeError`. The degree-bounded form of
`Probability.prob_polynomial_eval_eq_le`. -/
theorem prob_eval_eq_le [IsDomain L] [Fintype L] [SampleableType L] {p q : L⦃≤ d⦄[X]}
    (hne : p ≠ q) :
    Pr{let c ← $ᵗ L}[p.val.eval c = q.val.eval c] ≤ ((d : ℝ≥0) / Fintype.card L : ℝ≥0) := by
  rw [ENNReal.coe_div (by simp), ENNReal.coe_natCast, ENNReal.coe_natCast]
  exact Probability.prob_polynomial_eval_eq_le (fun h => hne (Subtype.ext h))
    (Polynomial.natDegree_le_of_degree_le (Polynomial.mem_degreeLE.mp p.property))
    (Polynomial.natDegree_le_of_degree_le (Polynomial.mem_degreeLE.mp q.property))

end Sumcheck.Structured
