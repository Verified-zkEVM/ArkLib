/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas, ArkLib Contributors
-/
import ArkLib.Data.MvPolynomial.Multilinear
import CompPoly.ToMathlib.MvPolynomial.Equiv

/-!
# Hypercube sums and their round polynomials over commutative rings

These ordinary-polynomial identities generalize the coordinate splitting used by Hachi's
round-polynomial layer. They require only a commutative ring and include the empty cube.
-/

noncomputable section
namespace MvPolynomial
open MvPolynomial
variable {F : Type*} [CommRing F] {M : ℕ}

/-- Assemble a full point from a fixed prefix and a Boolean suffix. -/
def hypercubePoint (m i : ℕ) (cs : Fin i → F) (x : Fin (m - i) → Fin 2) : Fin m → F :=
  fun j => if h : j.val < i then cs ⟨j, h⟩ else (x ⟨j.val - i, by omega⟩ : F)

/-- Sum a polynomial over Boolean completions of a fixed challenge prefix. -/
def hypercubeSum (m : ℕ) (H : MvPolynomial (Fin m) F) (i : ℕ) (cs : Fin i → F) : F :=
  ∑ x : Fin (m - i) → Fin 2, H.eval (hypercubePoint m i cs x)

/-- The initial sum is the ordinary Boolean sum. -/
theorem hypercubeSum_zero (m : ℕ) (H : MvPolynomial (Fin m) F) :
    hypercubeSum m H 0 Fin.elim0 = ∑ x : Fin m → Fin 2, H.eval (x : Fin m → F) := rfl

/-- After the last challenge the cube has one point, including when the original arity is zero. -/
theorem hypercubeSum_last (m : ℕ) (H : MvPolynomial (Fin m) F) (cs : Fin m → F) :
    hypercubeSum m H m cs = H.eval cs := by
  have hp : ∀ x : Fin (m - m) → Fin 2, hypercubePoint m m cs x = cs := by
    intro x
    funext j
    simp [hypercubePoint, j.isLt]
  simp [hypercubeSum, hp]

/--
Prepending the first free coordinate to a Boolean completion equals appending it to the fixed
prefix.
-/
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

/-- The Boolean cube sum splits into the sums at the two Boolean extensions of the fixed prefix. -/
theorem hypercubeSum_succ (H : MvPolynomial (Fin (M + 1)) F) (i : Fin (M + 1)) (cs : Fin i → F) :
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

This is what the honest prover sends. Over an integral domain, agreement with a degree-bounded
prover message at sufficiently many distinct challenges implies equality of the polynomials. -/
noncomputable def roundPoly (H : MvPolynomial (Fin (M + 1)) F) (i : Fin (M + 1)) (cs : Fin i → F) :
    Polynomial F :=
  ∑ y : Fin (M + 1 - ((i : ℕ) + 1)) → Fin 2,
    Polynomial.map
      (MvPolynomial.eval (Fin.append cs (fun j => ((y j : ℕ) : F)) ∘ Fin.cast (by omega)))
      (MvPolynomial.finSuccEquivNth F i H)

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

/-- The round polynomial computes the partial sum: its value at any `T` is the round-`(i+1)`
partial hypercube sum at the prefix extended by `T`. -/
theorem roundPoly_eval (H : MvPolynomial (Fin (M + 1)) F) (i : Fin (M + 1))
    (cs : Fin i → F) (T : F) :
    Polynomial.eval T (roundPoly H i cs)
      = hypercubeSum (M + 1) H ((i : ℕ) + 1) (Fin.snoc cs T) := by
  rw [roundPoly, Polynomial.eval_finsetSum, hypercubeSum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [← MvPolynomial.eval_eq_eval_mv_eval_finSuccEquivNth, insertNth_eq_hypercubePoint]

/-- The round polynomial inherits the per-variable degree bound of its multivariate polynomial. -/
theorem roundPoly_degree_le (H : MvPolynomial (Fin (M + 1)) F) (i : Fin (M + 1)) (cs : Fin i → F)
    {D : ℕ} (hH : ∀ j, H.degreeOf j ≤ D) :
    (roundPoly H i cs).degree ≤ (D : WithBot ℕ) := by
  refine (Polynomial.degree_sum_le _ _).trans (Finset.sup_le fun y _ => ?_)
  refine Polynomial.degree_map_le.trans (Polynomial.natDegree_le_iff_degree_le.mp ?_)
  rw [MvPolynomial.natDegree_finSuccEquivNth]
  exact hH i


end MvPolynomial
