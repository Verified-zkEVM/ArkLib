/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Elias Judin
-/

import ArkLib.Data.MvPolynomial.SchwartzZippelCounting
import ArkLib.ProofSystem.Stacking.Basic
import CompPoly.Multilinear.Next

/-!
# Selector rewriting and batching

This file proves selector-based claim rewriting and the soundness bound for
batching claims with a random scalar.

## References

* [leanVM specification, Section 5.1](https://github.com/leanEthereum/leanVM/releases)
-/

open scoped BigOperators ProbabilityTheory NNReal ENNReal
open CompPoly MvPolynomial

namespace Stacking

variable {R : Type*}

/-- A claim `P̂ᵢ(z) = c` on block `i` is equivalent to its selector-weighted sum over
the stacked polynomial, in little-endian coordinates. -/
theorem claim_iffLE [CommRing R] (bs : List (Block R)) (i : Fin bs.length)
    (hle : (bs.get i).1 ≤ stackVars bs) (haligned : AlignedAt bs i)
    (z : Vector R (bs.get i).1) (c : R) :
    (bs.get i).2.eval z = c ↔
      (∑ w : Fin (2 ^ stackVars bs),
        CompPoly.Multilinear.eqHat (selPointLE bs i hle z)
          (CompPoly.Multilinear.cubePointLE (stackVars bs) w) * (stack bs)[w]) = c := by
  rw [← selector_eval_eqLE bs i hle haligned z]
  rw [CompPoly.Multilinear.eqHat_interpolationLE]

/-- Paper-facing normal-claim rewriting in big-endian coordinates. -/
theorem claim_iff [CommRing R] (bs : List (Block R)) (i : Fin bs.length)
    (hle : (bs.get i).1 ≤ stackVars bs) (haligned : AlignedAt bs i)
    (z : Vector R (bs.get i).1) (c : R) :
    CompPoly.Multilinear.mleEval (bs.get i).2 z = c ↔
      (∑ w : Fin (2 ^ stackVars bs),
        CompPoly.Multilinear.eqHat (selPoint bs i hle z)
          (CompPoly.Multilinear.cubePoint (stackVars bs) w) * (stack bs)[w]) = c := by
  rw [← selector_eval_eq bs i hle haligned z]
  rw [CompPoly.Multilinear.eqHat_interpolation]

/-- Rewrites a shifted claim on block `i` as a weighted sum over the stack.
The high-coordinate factor selects block `i`, while `nextHat` supplies the
low-coordinate factor. -/
theorem shift_claim_eq [CommRing R] (bs : List (Block R)) (i : Fin bs.length)
    (hle : (bs.get i).1 ≤ stackVars bs) (haligned : AlignedAt bs i)
    (z : Vector R (bs.get i).1) :
    CompPoly.Multilinear.mleEval (CompPoly.Multilinear.shiftColumn (bs.get i).2) z =
      ∑ w : Fin (2 ^ stackVars bs),
        CompPoly.Multilinear.eqHat
            (CompPoly.Multilinear.cubePoint (stackVars bs - (bs.get i).1)
              (selectorIndex bs i hle haligned))
            (CompPoly.Multilinear.cubePoint (stackVars bs - (bs.get i).1)
              (highIndex bs i hle w)) *
          CompPoly.Multilinear.nextHat z
            (CompPoly.Multilinear.cubePoint (bs.get i).1 (lowIndex bs i w)) *
          (stack bs)[w] := by
  rw [CompPoly.Multilinear.shift_eq_sum]
  let selected : Finset (Fin (2 ^ stackVars bs)) :=
    Finset.image (selectedIndex bs i haligned)
      (Finset.univ : Finset (Fin (2 ^ (bs.get i).1)))
  let localWeight : Fin (2 ^ (bs.get i).1) → R := fun x ↦
    CompPoly.Multilinear.nextHat z (CompPoly.Multilinear.cubePoint (bs.get i).1 x) * (bs.get i).2[x]
  let stackedWeight : Fin (2 ^ stackVars bs) → R := fun w ↦
    CompPoly.Multilinear.eqHat
        (CompPoly.Multilinear.cubePoint (stackVars bs - (bs.get i).1)
          (selectorIndex bs i hle haligned))
        (CompPoly.Multilinear.cubePoint (stackVars bs - (bs.get i).1)
          (highIndex bs i hle w)) *
      CompPoly.Multilinear.nextHat z
        (CompPoly.Multilinear.cubePoint (bs.get i).1 (lowIndex bs i w)) *
      (stack bs)[w]
  change (∑ x : Fin (2 ^ (bs.get i).1), localWeight x) =
    ∑ w : Fin (2 ^ stackVars bs), stackedWeight w
  have hselected : ∀ x : Fin (2 ^ (bs.get i).1),
      stackedWeight (selectedIndex bs i haligned x) = localWeight x := by
    intro x
    dsimp only [stackedWeight, localWeight]
    rw [highIndex_selectedIndex, lowIndex_selectedIndex,
      CompPoly.Multilinear.eqHat_cubePoint_delta, if_pos rfl, one_mul,
      stack_selectedIndex]
  have hzero : ∀ w : Fin (2 ^ stackVars bs), w ∉ selected → stackedWeight w = 0 := by
    intro w hw
    have hne : highIndex bs i hle w ≠ selectorIndex bs i hle haligned := by
      intro heq
      apply hw
      apply mem_selectedIndex_image_of_highBits_eq (R := R) bs i haligned w
      simpa [highIndex, selectorIndex] using congrArg Fin.val heq
    have hne' : selectorIndex bs i hle haligned ≠ highIndex bs i hle w := Ne.symm hne
    dsimp only [stackedWeight]
    rw [CompPoly.Multilinear.eqHat_cubePoint_delta, if_neg hne', zero_mul, zero_mul]
  symm
  calc
    (∑ w : Fin (2 ^ stackVars bs), stackedWeight w) =
        ∑ w ∈ selected, stackedWeight w := by
      rw [Finset.sum_subset (Finset.subset_univ selected)]
      intro w _ hw
      exact hzero w hw
    _ = ∑ x : Fin (2 ^ (bs.get i).1),
        stackedWeight (selectedIndex bs i haligned x) := by
      rw [Finset.sum_image]
      intro x _ y _ hxy
      exact selectedIndex_injective (R := R) bs i haligned hxy
    _ = ∑ x : Fin (2 ^ (bs.get i).1), localWeight x := by
      exact Finset.sum_congr rfl fun x _ ↦ hselected x

/-- Shift-claim equivalence with an explicit claimed value. -/
theorem shift_claim_iff [CommRing R] (bs : List (Block R)) (i : Fin bs.length)
    (hle : (bs.get i).1 ≤ stackVars bs) (haligned : AlignedAt bs i)
    (z : Vector R (bs.get i).1) (c : R) :
    CompPoly.Multilinear.mleEval (CompPoly.Multilinear.shiftColumn (bs.get i).2) z = c ↔
      (∑ w : Fin (2 ^ stackVars bs),
        CompPoly.Multilinear.eqHat
            (CompPoly.Multilinear.cubePoint (stackVars bs - (bs.get i).1)
              (selectorIndex bs i hle haligned))
            (CompPoly.Multilinear.cubePoint (stackVars bs - (bs.get i).1)
              (highIndex bs i hle w)) *
          CompPoly.Multilinear.nextHat z
            (CompPoly.Multilinear.cubePoint (bs.get i).1 (lowIndex bs i w)) *
          (stack bs)[w]) = c := by
  rw [shift_claim_eq bs i hle haligned z]

/-! ### The univariate batching polynomial -/

section BatchPoly

variable {F : Type} [Field F]

/-- The paper's univariate batching polynomial
`A(λ) = ∑_j a_j · X₀^(j + 1)`, encoded as a one-variable `MvPolynomial`. -/
noncomputable def batchPoly {J : ℕ} (a : Fin J → F) : MvPolynomial (Fin 1) F :=
  ∑ j : Fin J,
    MvPolynomial.C (a j) * (MvPolynomial.X (0 : Fin 1)) ^ ((j : ℕ) + 1)

/-- Evaluating the batching polynomial at the constant point `fun _ ↦ lam`
recovers the paper's one-based combination `∑_j a_j · lam^(j + 1)`. -/
theorem batchPoly_eval {J : ℕ} (a : Fin J → F) (lam : F) :
    MvPolynomial.eval (fun _ ↦ lam) (batchPoly a)
      = ∑ j : Fin J, a j * lam ^ ((j : ℕ) + 1) := by
  simp [batchPoly, map_sum, map_mul, map_pow, MvPolynomial.eval_C, MvPolynomial.eval_X]

/-- The batching polynomial has total degree at most `J`. -/
theorem batchPoly_totalDegree_le {J : ℕ} (a : Fin J → F) :
    (batchPoly a).totalDegree ≤ J := by
  apply le_trans (MvPolynomial.totalDegree_finsetSum _ _)
  apply Finset.sup_le
  intro j _
  rw [MvPolynomial.C_mul_X_pow_eq_monomial]
  apply le_trans (MvPolynomial.totalDegree_monomial_le _ _)
  have hsum :
      (Finsupp.single (0 : Fin 1) ((j : ℕ) + 1)).sum (fun _ ↦ id) =
        (j : ℕ) + 1 := by
    exact Finsupp.sum_single_index (h := fun _ ↦ id) rfl
  rw [hsum]
  exact j.isLt

/-- If some coefficient is nonzero, the batching polynomial is nonzero. -/
theorem batchPoly_ne_zero {J : ℕ} (a : Fin J → F) (h : ∃ j, a j ≠ 0) :
    batchPoly a ≠ 0 := by
  obtain ⟨j0, hj0⟩ := h
  intro hzero
  apply hj0
  have hco :
      MvPolynomial.coeff (Finsupp.single (0 : Fin 1) ((j0 : ℕ) + 1)) (batchPoly a)
        = a j0 := by
    rw [batchPoly, MvPolynomial.coeff_sum, Finset.sum_eq_single j0]
    · rw [MvPolynomial.C_mul_X_pow_eq_monomial, MvPolynomial.coeff_monomial]
      simp
    · intro b _ hb
      rw [MvPolynomial.C_mul_X_pow_eq_monomial, MvPolynomial.coeff_monomial, if_neg]
      intro hcontra
      apply hb
      have hval : (b : ℕ) + 1 = (j0 : ℕ) + 1 := by
        have := congrArg (fun f ↦ f (0 : Fin 1)) hcontra
        simpa only [Finsupp.single_eq_same] using this
      exact Fin.ext (Nat.add_right_cancel hval)
    · intro hb
      simp at hb
  rw [hzero, MvPolynomial.coeff_zero] at hco
  exact hco.symm

end BatchPoly

/-- Sampling `λ` uniformly from `F` and testing `P(λ,...,λ) = 0` has the same
probability as sampling a whole point `x` uniformly from `Fin 1 → F` and testing
`eval x P = 0`, because `Fin 1 → F` is in bijection with `F`. -/
theorem pr_const_eq {F : Type} [Field F] [Fintype F]
    (P : MvPolynomial (Fin 1) F) :
    Pr_{let lam ←$ᵖ F}[MvPolynomial.eval (fun _ ↦ lam) P = 0]
      = Pr_{let x ←$ᵖ (Fin 1 → F)}[MvPolynomial.eval x P = 0] := by
  classical
  rw [uniform_prob_eq_card_div, uniform_prob_eq_card_div]
  have hcard : Fintype.card (Fin 1 → F) = Fintype.card F := by
    simp
  have key : ∀ x : Fin 1 → F, (fun _ : Fin 1 ↦ x 0) = x := by
    intro x
    funext i
    fin_cases i
    rfl
  have hcardeq :
      (Finset.univ.filter (fun lam : F ↦ MvPolynomial.eval (fun _ ↦ lam) P = 0)).card
        = (Finset.univ.filter (fun x : Fin 1 → F ↦ MvPolynomial.eval x P = 0)).card := by
    apply Finset.card_nbij' (fun lam _ ↦ lam) (fun x ↦ x 0)
    · intro lam h
      simp_all
    · intro x h
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at h ⊢
      rw [key x]
      exact h
    · intro lam _
      rfl
    · intro x _
      exact key x
  rw [hcard, hcardeq]

/-- If one of `J` weighted claims is false, their one-based `λ`-batch vanishes for a
uniformly sampled `λ` with probability at most `J / #F`.

The bound includes the root at `λ = 0` introduced by the common factor `λ`. -/
theorem batch_sound {F : Type} [Field F] [Fintype F]
    {ν : ℕ} (S : CMlPolynomialEval F ν) (J : ℕ)
    (W : Fin J → Fin (2 ^ ν) → F) (c : Fin J → F)
    (hfalse : ∃ j, (∑ w : Fin (2 ^ ν), W j w * S[w]) ≠ c j) :
    Pr_{let lam ←$ᵖ F}[
        (∑ j : Fin J,
          lam ^ ((j : ℕ) + 1) * ((∑ w : Fin (2 ^ ν), W j w * S[w]) - c j)) = 0]
      ≤ (J : ℝ≥0∞) / (Fintype.card F) := by
  classical
  set a : Fin J → F := fun j ↦ (∑ w : Fin (2 ^ ν), W j w * S[w]) - c j with ha
  have hfalse' : ∃ j, a j ≠ 0 := by
    obtain ⟨j, hj⟩ := hfalse
    exact ⟨j, sub_ne_zero.mpr hj⟩
  have hcond : ∀ lam : F,
      (∑ j : Fin J,
        lam ^ ((j : ℕ) + 1) * ((∑ w : Fin (2 ^ ν), W j w * S[w]) - c j))
        = MvPolynomial.eval (fun _ ↦ lam) (batchPoly a) := by
    intro lam
    rw [batchPoly_eval]
    exact Finset.sum_congr rfl (fun j _ ↦ by rw [mul_comm])
  calc
    Pr_{let lam ←$ᵖ F}[
        (∑ j : Fin J,
          lam ^ ((j : ℕ) + 1) * ((∑ w : Fin (2 ^ ν), W j w * S[w]) - c j)) = 0]
        = Pr_{let lam ←$ᵖ F}[MvPolynomial.eval (fun _ ↦ lam) (batchPoly a) = 0] := by
          simp only [hcond]
      _ = Pr_{let x ←$ᵖ (Fin 1 → F)}[MvPolynomial.eval x (batchPoly a) = 0] :=
          pr_const_eq _
      _ ≤ (J : ℝ≥0∞) / (Fintype.card F) :=
          prob_eval_zero_uniform_le_div _ (batchPoly_ne_zero a hfalse') J
            (batchPoly_totalDegree_le a)

end Stacking
