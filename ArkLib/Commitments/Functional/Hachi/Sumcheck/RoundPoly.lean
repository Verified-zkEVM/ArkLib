/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.ZeroCheck.Constraints

/-!
  # The round-polynomial layer of the Hachi sumcheck

  The partial hypercube sums of `ZeroCheck/Constraints.lean` are `F`-valued: `hypercubeSum`
  *evaluates*. The round soundness argument needs more than the value — the partial sum, as a
  function of the free coordinate, must be a univariate polynomial of bounded degree, because
  that is what upgrades "the sum agrees with the prover's message `gᵢ` at the `k` sibling
  challenges" to "it agrees with `gᵢ` everywhere", and in particular at `0` and `1`. This
  file builds that polynomial and the cube-split identity that consumes it.

  ## Contents

  * `hypercubeSum_succ` — the cube split: the round-`i` partial sum is the sum of the two
    round-`(i+1)` partial sums at the Boolean extensions of the challenge prefix. With the
    round check `gᵢ(0) + gᵢ(1) = targetᵢ₋₁` this is what carries a round's claim back one
    round.
  * `roundPoly` — the partial sum as a `Polynomial F`, with `roundPoly_eval` (its values are
    the partial sums) and `roundPoly_degree_le` (it inherits the summand's per-variable
    degree).
  * `roundPoly_degree_le_sumcheckPolyZero` / `…Alpha` — the two instances at Hachi's
    summands, with degree bounds `roundDegZero b = 2b` and `roundDegAlpha = 2`.

  ## Computability

  `roundPoly` is a proof-side object: it is `noncomputable` and lives in Mathlib's
  `Polynomial`, because its only role is to witness that the partial sum *is* polynomial.
  Nothing the protocol computes depends on it — the wire object is the computable
  `RoundMsg = CPolynomial.degreeLE (2b) × CPolynomial.degreeLE 2` of `Sumcheck/Rounds.lean`,
  and the honest prover's round message (still to be built, with the completeness layer) must
  be a `CPolynomial`. Keeping the two apart lets the soundness argument use Mathlib's degree
  API without making any executable definition noncomputable.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly CPoly ArkLib.Lattices.CyclotomicModulus
open MvPolynomial

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ} {F : Type} [Field F] [BEq F] [LawfulBEq F]
variable (m₀ m₁ : ℕ)

/-! ### The round-polynomial layer

Everything in this section is stated at arity `M + 1`. That is no loss: a round only exists
when there is a coordinate left to fold, so `0 < m₀` holds at every call site, and
destructing it (`obtain ⟨M, rfl⟩`) is what lets `MvPolynomial (Fin m₀)` meet the
`Fin (n + 1)` shape that `finSuccEquivNth` is stated at, without a dependent cast. -/

section RoundPoly

variable {M : ℕ}

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- Peeling the leading free coordinate: prepending `b` to the summation index of the
round-`(i+1)` cube is the same as appending `b` to the round-`i` challenge prefix — both name
the same point of `F^{M+1}`. -/
theorem hypercubePoint_cons (i : Fin (M + 1)) (cs : Fin i → F) (b : Fin 2)
    (y : Fin (M + 1 - ((i : ℕ) + 1)) → Fin 2) :
    hypercubePoint (M + 1) i cs (Fin.cons b y ∘ finCongr (by omega)) =
      hypercubePoint (M + 1) ((i : ℕ) + 1) (Fin.snoc cs ((b : ℕ) : F)) y := by
  funext j
  simp only [hypercubePoint, Function.comp_apply]
  by_cases h1 : (j : ℕ) < (i : ℕ)
  · rw [dif_pos h1, dif_pos (show (j : ℕ) < (i : ℕ) + 1 by omega),
      show (⟨(j : ℕ), by omega⟩ : Fin ((i : ℕ) + 1)) = Fin.castSucc ⟨(j : ℕ), h1⟩ from rfl,
      Fin.snoc_castSucc]
  · rw [dif_neg h1]
    by_cases h2 : (j : ℕ) = (i : ℕ)
    · rw [dif_pos (show (j : ℕ) < (i : ℕ) + 1 by omega),
        show (finCongr (by omega) ⟨(j : ℕ) - (i : ℕ), by omega⟩ :
            Fin ((M + 1 - ((i : ℕ) + 1)) + 1)) = 0 from Fin.ext (by simp; omega),
        Fin.cons_zero,
        show (⟨(j : ℕ), by omega⟩ : Fin ((i : ℕ) + 1)) = Fin.last (i : ℕ) from
          Fin.ext (by simp; omega),
        Fin.snoc_last]
    · rw [dif_neg (show ¬ (j : ℕ) < (i : ℕ) + 1 by omega),
        show (finCongr (by omega) ⟨(j : ℕ) - (i : ℕ), by omega⟩ :
            Fin ((M + 1 - ((i : ℕ) + 1)) + 1))
          = Fin.succ ⟨(j : ℕ) - ((i : ℕ) + 1), by omega⟩ from Fin.ext (by simp; omega),
        Fin.cons_succ]

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- The cube split — the identity every sumcheck round turns on: the round-`i` partial sum is
the sum of the two round-`(i+1)` partial sums at the two Boolean extensions of the challenge
prefix. Together with the round check `g(0) + g(1) = targetᵢ₋₁` this is what carries a
round's claim back to the previous round. -/
theorem hypercubeSum_succ (H : CMvPolynomial (M + 1) F) (i : Fin (M + 1)) (cs : Fin i → F) :
    hypercubeSum (M + 1) H i cs =
      hypercubeSum (M + 1) H ((i : ℕ) + 1) (Fin.snoc cs 0) +
        hypercubeSum (M + 1) H ((i : ℕ) + 1) (Fin.snoc cs 1) := by
  have hsplit : (M + 1) - (i : ℕ) = (M + 1 - ((i : ℕ) + 1)) + 1 := by omega
  let e : Fin 2 × (Fin (M + 1 - ((i : ℕ) + 1)) → Fin 2) ≃ (Fin ((M + 1) - (i : ℕ)) → Fin 2) :=
    (Fin.consEquiv (fun _ => Fin 2)).trans
      (Equiv.arrowCongr (finCongr hsplit.symm) (Equiv.refl (Fin 2)))
  have hstep : hypercubeSum (M + 1) H i cs
      = ∑ p : Fin 2 × (Fin (M + 1 - ((i : ℕ) + 1)) → Fin 2),
          H.eval (hypercubePoint (M + 1) i cs (Fin.cons p.1 p.2 ∘ finCongr hsplit)) := by
    rw [hypercubeSum]
    exact (Fintype.sum_equiv e _ _ fun _ => rfl).symm
  rw [hstep, Fintype.sum_prod_type, Fin.sum_univ_two]
  congr 1 <;>
    · rw [hypercubeSum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [hypercubePoint_cons]
      norm_num

/-- The round polynomial of a partial hypercube sum: the univariate whose value at `T` is the
round-`(i+1)` partial sum at the challenge prefix extended by `T` (`roundPoly_eval`), with
the per-variable degree of `H` as its degree bound (`roundPoly_degree_le`).

This is what the honest prover sends. For soundness it plays the central role: it is the
object that upgrades "the sum agrees with the prover's `g` at `k` challenges" to "it agrees
with `g` everywhere". -/
noncomputable def roundPoly (H : CMvPolynomial (M + 1) F) (i : Fin (M + 1)) (cs : Fin i → F) :
    Polynomial F :=
  ∑ y : Fin (M + 1 - ((i : ℕ) + 1)) → Fin 2,
    Polynomial.map
      (MvPolynomial.eval (Fin.append cs (fun j => ((y j : ℕ) : F)) ∘ Fin.cast (by omega)))
      (MvPolynomial.finSuccEquivNth F i (fromCMvPolynomial H))

omit [NeZero q] [IsCyclotomic Φ] [BEq F] [LawfulBEq F] in
/-- The point `roundPoly`'s summand evaluates at: the challenge prefix, then the free coordinate,
then the Boolean tail — which is exactly the round-`(i+1)` cube point. -/
theorem insertNth_eq_hypercubePoint (i : Fin (M + 1)) (cs : Fin i → F) (T : F)
    (y : Fin (M + 1 - ((i : ℕ) + 1)) → Fin 2) :
    Fin.insertNth i T (Fin.append cs (fun j => ((y j : ℕ) : F)) ∘ Fin.cast (by omega))
      = hypercubePoint (M + 1) ((i : ℕ) + 1) (Fin.snoc cs T) y := by
  funext j
  refine Fin.succAboveCases i ?_ ?_ j
  · rw [Fin.insertNth_apply_same]
    simp only [hypercubePoint]
    rw [dif_pos (by omega : (i : ℕ) < (i : ℕ) + 1),
      show (⟨(i : ℕ), by omega⟩ : Fin ((i : ℕ) + 1)) = Fin.last (i : ℕ) from Fin.ext rfl,
      Fin.snoc_last]
  · intro k
    rw [Fin.insertNth_apply_succAbove]
    simp only [hypercubePoint, Function.comp_apply]
    by_cases hk : (k : ℕ) < (i : ℕ)
    · have hsa : ((i.succAbove k : Fin (M + 1)) : ℕ) = (k : ℕ) := by
        rw [Fin.succAbove_of_castSucc_lt _ _ (by exact Fin.lt_def.mpr (by simpa using hk))]
        rfl
      have hlt : ((i.succAbove k : Fin (M + 1)) : ℕ) < (i : ℕ) + 1 := by omega
      rw [dif_pos hlt,
        show (⟨((i.succAbove k : Fin (M + 1)) : ℕ), hlt⟩ : Fin ((i : ℕ) + 1))
          = Fin.castSucc ⟨(k : ℕ), hk⟩ from Fin.ext hsa,
        Fin.snoc_castSucc]
      exact (congrArg (Fin.append cs (fun j => ((y j : ℕ) : F)))
        (Fin.ext rfl : (Fin.cast (by omega) k : Fin ((i : ℕ) + (M + 1 - ((i : ℕ) + 1))))
          = Fin.castAdd _ ⟨(k : ℕ), hk⟩)).trans (Fin.append_left _ _ _)
    · have hsa : ((i.succAbove k : Fin (M + 1)) : ℕ) = (k : ℕ) + 1 := by
        rw [Fin.succAbove_of_le_castSucc _ _ (by exact Fin.le_def.mpr (by simpa using hk))]
        rfl
      rw [dif_neg (by omega : ¬ ((i.succAbove k : Fin (M + 1)) : ℕ) < (i : ℕ) + 1)]
      refine (congrArg (Fin.append cs (fun j => ((y j : ℕ) : F)))
        (Fin.ext (by simp; omega) :
          (Fin.cast (by omega) k : Fin ((i : ℕ) + (M + 1 - ((i : ℕ) + 1))))
            = Fin.natAdd _ ⟨(k : ℕ) - (i : ℕ), by omega⟩)).trans ?_
      rw [Fin.append_right]
      have hidx : (k : ℕ) - (i : ℕ)
          = ((i.succAbove k : Fin (M + 1)) : ℕ) - ((i : ℕ) + 1) := by omega
      exact congrArg (fun z : Fin 2 => ((z : ℕ) : F)) (congrArg y (Fin.ext hidx))

omit [NeZero q] [IsCyclotomic Φ] [BEq (ZMod q)] [LawfulBEq (ZMod q)] [BEq F] [LawfulBEq F] in
/-- The round polynomial computes the partial sum: its value at any `T` is the round-`(i+1)`
partial hypercube sum at the prefix extended by `T`. -/
theorem roundPoly_eval (H : CMvPolynomial (M + 1) F) (i : Fin (M + 1)) (cs : Fin i → F) (T : F) :
    Polynomial.eval T (roundPoly H i cs)
      = hypercubeSum (M + 1) H ((i : ℕ) + 1) (Fin.snoc cs T) := by
  rw [roundPoly, Polynomial.eval_finsetSum, hypercubeSum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← MvPolynomial.eval_eq_eval_mv_eval_finSuccEquivNth, insertNth_eq_hypercubePoint,
    ← CPoly.eval_equiv]

omit [NeZero q] [IsCyclotomic Φ] [BEq (ZMod q)] [LawfulBEq (ZMod q)] [BEq F] [LawfulBEq F] in
/-- The round polynomial inherits `H`'s per-variable degree bound: each summand is a
one-variable specialization of `H`, whose degree is `H`'s degree in the free coordinate, and
a finite sum does not raise it. -/
theorem roundPoly_degree_le (H : CMvPolynomial (M + 1) F) (i : Fin (M + 1)) (cs : Fin i → F)
    {D : ℕ} (hH : ∀ j, (fromCMvPolynomial H).degreeOf j ≤ D) :
    (roundPoly H i cs).degree ≤ (D : WithBot ℕ) := by
  refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le fun y _ => ?_)
  refine Polynomial.degree_map_le.trans (Polynomial.natDegree_le_iff_degree_le.mp ?_)
  rw [MvPolynomial.natDegree_finSuccEquivNth]
  exact hH i

end RoundPoly

/-! ### The round polynomials of the two Hachi summands

The two corollaries the round soundness consumes: each summand's partial sum is a univariate
of the degree its `RoundMsg` component is bounded by, so a defect vanishing at
`k = max (2b) 2 + 1` distinct challenges is identically zero. -/

section RoundPolyHachi

variable {M : ℕ}

omit [NeZero q] [IsCyclotomic Φ] in
/-- The range summand's round polynomial has degree `≤ roundDegZero b = 2b`. -/
theorem roundPoly_degree_le_sumcheckPolyZero {b : ℕ} (hb : 0 < b) (φF : ZMod q →+* F)
    (τ₀ : Fin (M + 1) → F) (w : LiftedWitness Φ μ n) (i : Fin (M + 1)) (cs : Fin i → F) :
    (roundPoly (sumcheckPolyZero Φ (M + 1) φF b τ₀ w) i cs).degree
      ≤ (roundDegZero b : WithBot ℕ) :=
  roundPoly_degree_le _ _ _ fun j => degreeOf_sumcheckPolyZero Φ (M + 1) hb φF τ₀ w j

omit [NeZero q] [IsCyclotomic Φ] in
/-- The linear summand's round polynomial has degree `≤ roundDegAlpha = 2`. -/
theorem roundPoly_degree_le_sumcheckPolyAlpha (φF : ZMod q →+* F) (b : ℕ)
    (s : RlinStatement Φ n μ) (α : F) (m₁ : ℕ) (τ₁ : Fin m₁ → F) (w : LiftedWitness Φ μ n)
    (i : Fin (M + 1)) (cs : Fin i → F) :
    (roundPoly (sumcheckPolyAlpha Φ (M + 1) m₁ φF b s α τ₁ w) i cs).degree
      ≤ (roundDegAlpha : WithBot ℕ) :=
  roundPoly_degree_le _ _ _ fun j =>
    degreeOf_sumcheckPolyAlpha Φ (M + 1) m₁ φF b s α τ₁ w j

end RoundPolyHachi

end ArkLib.Lattices.Ajtai.InnerOuter
