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
* `coe_projectToNextSumcheckPoly`: the next round polynomial `projectToNextSumcheckPoly` is the
  current one with its first variable fixed, renamed along `ℓ - i - 1 = ℓ - (i + 1)`; and
  `sum_projectToNextSumcheckPoly_uniform`: over a uniform domain, its sum over the remaining cube is
  the univariate round polynomial at the challenge.
* `eval_add_eval_getSumcheckRoundPoly`: over a two-point uniform domain, the univariate round
  polynomial's values at the two points sum to the round claim.
* `projectToMidSumcheckPoly_succ`, `coe_projectToMidSumcheckPoly`,
  `eval_projectToMidSumcheckPoly_last`, `coe_projectToMidSumcheckPoly_last`: the
  identity-combinator projection `projectToMidSumcheckPoly` at the next round, as a product of
  prefix fixings, and at the last round, where it is the constant `m(r) · t(r)`.
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

/-- The next round polynomial `projectToNextSumcheckPoly` is the current one with its first variable
fixed to the challenge, renamed along `ℓ - i - 1 = ℓ - (i + 1)`. -/
theorem coe_projectToNextSumcheckPoly (i : Fin ℓ) (H : MultiquadraticPoly L (ℓ - i)) (c : L)
    (hdim : ℓ - i - 1 = ℓ - i.succ) :
    (projectToNextSumcheckPoly ℓ i H c).val =
      rename (Fin.cast hdim) (fixFirstVariablesOfMQP (ℓ - i) ⟨1, by omega⟩ H.val (fun _ => c)) := by
  unfold projectToNextSumcheckPoly projectToNextSumcheckPolyWithDegree
  simp only [eq_mpr_eq_cast]
  rw [← cast_eq_rename_finCast hdim (congrArg (fun k => MvPolynomial (Fin k) L) hdim)]
  generalize_proofs h₁ h₂
  revert h₁ h₂
  generalize ℓ - i.succ = k at *
  intro h₁ h₂
  subst hdim
  intro _
  rfl

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

/-- Over a uniform domain, summing the next round polynomial `projectToNextSumcheckPoly` over the
remaining cube is evaluating the univariate round polynomial at the challenge: the honest
next-round claim, stated through the next round polynomial itself. -/
theorem sum_projectToNextSumcheckPoly_uniform (i : Fin ℓ) (H : MultiquadraticPoly L (ℓ - i))
    (c : L) :
    ∑ x ∈ (SumcheckDomain.uniform D₀ (ℓ - i.succ)).cube,
        (projectToNextSumcheckPoly ℓ i H c).val.eval x =
      (getSumcheckRoundPoly ℓ (SumcheckDomain.uniform D₀ ℓ) i H).val.eval c := by
  have hdim : ℓ - i - 1 = ℓ - i.succ := by simp only [Fin.val_succ]; omega
  rw [eval_getSumcheckRoundPoly_uniform ℓ D₀ i H c hdim, coe_projectToNextSumcheckPoly ℓ i H c hdim]

end Uniform

/-- Over a two-point uniform domain `D₀`, the univariate round polynomial's values at the two points
sum to the sum of the round polynomial over the remaining cube: the two-point form of
`sum_getSumcheckRoundPoly_uniform`. -/
theorem eval_add_eval_getSumcheckRoundPoly (D₀ : Fin 2 ↪ L) (i : Fin ℓ)
    (H : L⦃≤ d⦄[X Fin (ℓ - i.castSucc)]) :
    (getSumcheckRoundPoly ℓ (SumcheckDomain.uniform D₀ ℓ) i H).val.eval (D₀ 0) +
        (getSumcheckRoundPoly ℓ (SumcheckDomain.uniform D₀ ℓ) i H).val.eval (D₀ 1) =
      ∑ x ∈ (SumcheckDomain.uniform D₀ (ℓ - i.castSucc)).cube, H.val.eval x := by
  rw [← sum_getSumcheckRoundPoly_uniform ℓ D₀ i H, SumcheckDomain.points_uniform, Finset.sum_map,
    Fin.sum_univ_two]

/-- The projected round polynomial at round `i + 1` is the round-`i` projection with its first
variable fixed to the new challenge, for the identity-combinator projection
`projectToMidSumcheckPoly`. -/
theorem projectToMidSumcheckPoly_succ (t m : MultilinearPoly L ℓ) (i : Fin ℓ)
    (challenges : Fin i.castSucc → L) (c : L) :
    projectToMidSumcheckPoly ℓ t m i.succ (Fin.snoc challenges c) =
      projectToNextSumcheckPoly ℓ i (projectToMidSumcheckPoly ℓ t m i.castSucc challenges) c := by
  have hdim : ℓ - i - 1 = ℓ - (i + 1) := by omega
  refine Subtype.ext ?_
  rw [coe_projectToNextSumcheckPoly ℓ i _ c hdim]
  exact (fixFirstVariablesOfMQP_succ i _ challenges c hdim).symm

/-- The identity-combinator projection is the product of the multiplier and the witness polynomial,
each with its first `i` variables fixed to the challenges. -/
theorem coe_projectToMidSumcheckPoly (t m : MultilinearPoly L ℓ) (i : Fin (ℓ + 1))
    (challenges : Fin i → L) :
    (projectToMidSumcheckPoly ℓ t m i challenges).val =
      fixFirstVariablesOfMQP ℓ i m.val challenges *
        fixFirstVariablesOfMQP ℓ i t.val challenges := by
  simp only [projectToMidSumcheckPoly, computeInitialSumcheckPoly, fixFirstVariablesOfMQP_eq_bind₁,
    map_mul]

/-- With every variable fixed, the identity-combinator projection evaluates to the product of the
multiplier and the witness polynomial at the challenges. -/
theorem eval_projectToMidSumcheckPoly_last (t m : MultilinearPoly L ℓ)
    (challenges : Fin ℓ → L) (x : Fin (ℓ - (Fin.last ℓ : Fin (ℓ + 1))) → L) :
    (projectToMidSumcheckPoly ℓ t m (Fin.last ℓ) challenges).val.eval x =
      m.val.eval challenges * t.val.eval challenges := by
  rw [coe_projectToMidSumcheckPoly, map_mul, eval_fixFirstVariablesOfMQP_last,
    eval_fixFirstVariablesOfMQP_last]

/-- With every variable fixed, the identity-combinator projection is the constant polynomial at the
product of the multiplier and the witness polynomial evaluated at the challenges. -/
theorem coe_projectToMidSumcheckPoly_last (t m : MultilinearPoly L ℓ) (challenges : Fin ℓ → L) :
    (projectToMidSumcheckPoly ℓ t m (Fin.last ℓ) challenges).val =
      C (m.val.eval challenges * t.val.eval challenges) := by
  have : IsEmpty (Fin (ℓ - (Fin.last ℓ : Fin (ℓ + 1)))) := by
    rw [Fin.val_last, Nat.sub_self]
    infer_instance
  rw [eq_C_of_isEmpty (projectToMidSumcheckPoly ℓ t m (Fin.last ℓ) challenges).val,
    ← constantCoeff_eq, ← eval_zero]
  exact congrArg C (eval_projectToMidSumcheckPoly_last ℓ t m challenges 0)

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
