/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas, ArkLib Contributors
-/
module

public import ArkLib.Data.MvPolynomial.Multilinear
public import ArkLib.Data.MvPolynomial.RoundPolynomial

/-!
# Hypercube sums and their round polynomials over commutative semirings

Coordinate splitting expresses a Boolean hypercube sum as the sum of its two faces.
`roundPoly` sums the remaining coordinates after substituting the challenge prefix;
its evaluation and degree bounds describe a sumcheck prover message.
-/

@[expose] public section

noncomputable section
namespace MvPolynomial
open MvPolynomial
variable {F : Type*} [CommSemiring F] {M : ℕ}

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

/-- Boolean points use the prefix/suffix concatenation of arbitrary-domain round polynomials. -/
theorem hypercubePoint_eq_append (m i : ℕ) (hi : i ≤ m)
    (cs : Fin i → F)
    (x : Fin (m - i) → Fin 2) :
    hypercubePoint m i cs x =
      Fin.append cs (fun j => ((x j : ℕ) : F)) ∘ Fin.cast (by omega) := by
  funext j
  simp only [hypercubePoint, Fin.append, Fin.addCases, Function.comp_apply, Fin.val_cast]
  split <;> first | rfl | simp [Fin.subNat]

/-- Prepending a Boolean coordinate is appending it to the fixed prefix. -/
theorem hypercubePoint_cons (i : Fin (M + 1)) (cs : Fin i → F) (b : Fin 2)
    (y : Fin (M + 1 - ((i : ℕ) + 1)) → Fin 2) :
    hypercubePoint (M + 1) i cs (Fin.cons b y ∘ finCongr (by omega)) =
      hypercubePoint (M + 1) ((i : ℕ) + 1) (Fin.snoc cs ((b : ℕ) : F)) y := by
  rw [hypercubePoint_eq_append (M + 1) i (by omega),
    hypercubePoint_eq_append (M + 1) (i + 1) (by omega), Fin.append_left_snoc]
  have hc : (fun j : Fin (M + 1 - i) =>
      (((Fin.cons b y ∘ finCongr (by omega)) j : ℕ) : F)) =
      Fin.cons ((b : ℕ) : F) (fun j => ((y j : ℕ) : F)) ∘ Fin.cast (by omega) := by
    funext j
    simpa only [Function.comp_def, finCongr_apply] using
      congrFun (Fin.comp_cons (fun z : Fin 2 => ((z : ℕ) : F)) b y)
        (Fin.cast (by omega) j)
  rw [hc, Fin.append_cast_right]
  rfl

/-- The Boolean cube sum splits into the sums at the two Boolean extensions of the fixed prefix. -/
theorem hypercubeSum_succ (H : MvPolynomial (Fin (M + 1)) F) (i : Fin (M + 1)) (cs : Fin i → F) :
    hypercubeSum (M + 1) H i cs =
      hypercubeSum (M + 1) H ((i : ℕ) + 1) (Fin.snoc cs 0) +
        hypercubeSum (M + 1) H ((i : ℕ) + 1) (Fin.snoc cs 1) := by
  have hsplit : (M + 1) - (i : ℕ) = (M + 1 - ((i : ℕ) + 1)) + 1 := by omega
  unfold hypercubeSum
  rw [show (∑ x : Fin ((M + 1) - (i : ℕ)) → Fin 2,
      H.eval (hypercubePoint (M + 1) i cs x)) =
      ∑ x ∈ Fintype.piFinset (fun _ : Fin ((M + 1) - (i : ℕ)) => Finset.univ),
        H.eval (hypercubePoint (M + 1) i cs x) by simp]
  rw [Fin.sum_piFinset_cast _ hsplit, Fin.sum_piFinset_cons]
  simp only [Fin.sum_univ_two]
  congr 1
  · refine Finset.sum_congr rfl fun y _ => ?_
    simpa only [Function.comp_def, finCongr_apply, Fin.val_zero, Nat.cast_zero] using
      congrArg (fun x => H.eval x) (hypercubePoint_cons i cs 0 y)
  · refine Finset.sum_congr rfl fun y _ => ?_
    simpa only [Function.comp_def, finCongr_apply, Fin.val_one, Nat.cast_one] using
      congrArg (fun x => H.eval x) (hypercubePoint_cons i cs 1 y)

/-- The round polynomial of a partial hypercube sum: the univariate whose value at `T` is the
round-`(i+1)` partial sum at the challenge prefix extended by `T` (`roundPoly_eval`), with
the per-variable degree of `H` as its degree bound (`roundPoly_degree_le`). -/
noncomputable def roundPoly (H : MvPolynomial (Fin (M + 1)) F) (i : Fin (M + 1)) (cs : Fin i → F) :
    Polynomial F :=
  ∑ y : Fin (M + 1 - ((i : ℕ) + 1)) → Fin 2,
    Polynomial.map
      (MvPolynomial.eval (Fin.append cs (fun j => ((y j : ℕ) : F)) ∘ Fin.cast (by omega)))
      (MvPolynomial.finSuccEquivNth F i H)

/-- The round polynomial computes the partial sum: its value at any `T` is the round-`(i+1)`
partial hypercube sum at the prefix extended by `T`. -/
theorem roundPoly_eval (H : MvPolynomial (Fin (M + 1)) F) (i : Fin (M + 1))
    (cs : Fin i → F) (T : F) :
    Polynomial.eval T (roundPoly H i cs)
      = hypercubeSum (M + 1) H ((i : ℕ) + 1) (Fin.snoc cs T) := by
  change (sumRoundPolynomial _ _ i H).eval T = _
  rw [sumRoundPolynomial_eval, hypercubeSum]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Fin.insertNth_append_cast (l := M + 1 - (i + 1)) i cs _ T (by omega),
    hypercubePoint_eq_append (M + 1) (i + 1) (by omega) (Fin.snoc cs T) y]

/-- The Boolean values of the round polynomial sum to the previous residual claim. -/
theorem roundPoly_sum (H : MvPolynomial (Fin (M + 1)) F) (i : Fin (M + 1)) (cs : Fin i → F) :
    (roundPoly H i cs).eval 0 + (roundPoly H i cs).eval 1 = hypercubeSum (M + 1) H i cs := by
  rw [roundPoly_eval, roundPoly_eval, hypercubeSum_succ]

/-- The round polynomial inherits the per-variable degree bound of its multivariate polynomial. -/
theorem roundPoly_degree_le (H : MvPolynomial (Fin (M + 1)) F) (i : Fin (M + 1)) (cs : Fin i → F)
    {D : ℕ} (hH : ∀ j, H.degreeOf j ≤ D) :
    (roundPoly H i cs).degree ≤ (D : WithBot ℕ) := by
  exact Polynomial.natDegree_le_iff_degree_le.mp
    ((sumRoundPolynomial_natDegree_le _ _ i H).trans (hH i))

end MvPolynomial
