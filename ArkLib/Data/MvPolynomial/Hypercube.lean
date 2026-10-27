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
`hypercubeSuffix` assembles the assignments for the Boolean specialization of
`sumRoundPolynomial`; its evaluation and degree bounds describe a sumcheck prover message.
Cube sums use `Fintype.piFinset`.
-/

@[expose] public section

noncomputable section
namespace MvPolynomial
open MvPolynomial
variable {F : Type*} [CommSemiring F] {M : ℕ}

/-- Assign every coordinate except the round's free coordinate: a challenge prefix followed
by a Boolean suffix. Shared by the mathematical and computable round polynomials. -/
def hypercubeSuffix {m : ℕ} (i : Fin m) (cs : Fin i → F)
    (y : Fin (m - (i + 1)) → Fin 2) : Fin (m - 1) → F :=
  Fin.append cs (fun j => ((y j : ℕ) : F)) ∘ Fin.cast (by have := i.isLt; omega)

/-- Assemble a full point from a fixed prefix and a Boolean suffix. -/
def hypercubePoint (m i : ℕ) (cs : Fin i → F) (x : Fin (m - i) → Fin 2) : Fin m → F :=
  fun j => if h : j.val < i then cs ⟨j, h⟩ else (x ⟨j.val - i, by omega⟩ : F)

/-- Sum a polynomial over Boolean completions of a fixed challenge prefix. -/
def hypercubeSum (m : ℕ) (H : MvPolynomial (Fin m) F) (i : ℕ) (cs : Fin i → F) : F :=
  ∑ x ∈ Fintype.piFinset (fun _ : Fin (m - i) => (Finset.univ : Finset (Fin 2))),
    H.eval (hypercubePoint m i cs x)

/-- The initial sum is the ordinary Boolean sum. -/
theorem hypercubeSum_zero (m : ℕ) (H : MvPolynomial (Fin m) F) :
    hypercubeSum m H 0 Fin.elim0 = ∑ x : Fin m → Fin 2, H.eval (x : Fin m → F) := by
  simp only [hypercubeSum, Fintype.piFinset_univ]
  rfl

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
  rw [Fin.sum_piFinset_cast _ hsplit, Fin.sum_piFinset_cons]
  simp only [Fintype.piFinset_univ, Fin.sum_univ_two]
  congr 1
  · refine Finset.sum_congr rfl fun y _ => ?_
    simpa only [Function.comp_def, finCongr_apply, Fin.val_zero, Nat.cast_zero] using
      congrArg (fun x => H.eval x) (hypercubePoint_cons i cs 0 y)
  · refine Finset.sum_congr rfl fun y _ => ?_
    simpa only [Function.comp_def, finCongr_apply, Fin.val_one, Nat.cast_one] using
      congrArg (fun x => H.eval x) (hypercubePoint_cons i cs 1 y)

/-- The round polynomial computes the partial sum: its value at any `T` is the round-`(i+1)`
partial hypercube sum at the prefix extended by `T`. -/
theorem sumRoundPolynomial_eval_hypercube (H : MvPolynomial (Fin (M + 1)) F) (i : Fin (M + 1))
    (cs : Fin i → F) (T : F) :
    Polynomial.eval T (sumRoundPolynomial (m := M + 1)
      (Finset.univ : Finset (Fin (M + 1 - (i + 1)) → Fin 2))
      (hypercubeSuffix i cs) i H)
      = hypercubeSum (M + 1) H ((i : ℕ) + 1) (Fin.snoc cs T) := by
  rw [sumRoundPolynomial_eval, hypercubeSum]
  unfold hypercubeSuffix
  simp only [Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Fin.insertNth_append_cast (l := M + 1 - (i + 1)) i cs _ T (by omega),
    hypercubePoint_eq_append (M + 1) (i + 1) (by omega) (Fin.snoc cs T) y]

/-- The Boolean values of the round polynomial sum to the previous residual claim. -/
theorem sumRoundPolynomial_sum_hypercube (H : MvPolynomial (Fin (M + 1)) F)
    (i : Fin (M + 1)) (cs : Fin i → F) :
    (sumRoundPolynomial (m := M + 1) (Finset.univ : Finset (Fin (M + 1 - (i + 1)) → Fin 2))
      (hypercubeSuffix i cs) i H).eval 0 +
    (sumRoundPolynomial (m := M + 1) (Finset.univ : Finset (Fin (M + 1 - (i + 1)) → Fin 2))
      (hypercubeSuffix i cs) i H).eval 1 =
        hypercubeSum (M + 1) H i cs := by
  rw [sumRoundPolynomial_eval_hypercube, sumRoundPolynomial_eval_hypercube, hypercubeSum_succ]

end MvPolynomial
