/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.Data.MvPolynomial.Hypercube

/-!
# Hypercube partial sums

Round evaluation over commutative semirings, including natural-number coefficients.
-/

namespace Tests.Hypercube

open MvPolynomial

example {S : Type*} [CommSemiring S] (a : S) :
    hypercubeSum 0 (C a) 0 Fin.elim0 = a := by
  simpa using hypercubeSum_last 0 (C a) Fin.elim0

example :
    Polynomial.eval 3 (∑ _x : Fin 0 → Fin 2,
      (X (0 : Fin 1) + C (2 : ℕ)).evalExcept 0 Fin.elim0) = 5 := by
  norm_num [Polynomial.eval_finsetSum, eval_evalExcept, Fin.insertNth_zero]


example {S : Type*} [CommSemiring S] {m : ℕ}
    (H : MvPolynomial (Fin (m + 1)) S) (i : Fin (m + 1)) (cs : Fin i → S)
    {d : ℕ} (hH : ∀ j, H.degreeOf j ≤ d) :
    (∑ x : Fin (m + 1 - (i + 1)) → Fin 2,
      H.evalExcept i (hypercubeSuffix i cs x)).degree ≤
        (d : WithBot ℕ) :=
  Polynomial.natDegree_le_iff_degree_le.mp
    (Polynomial.natDegree_sum_le_of_forall_le _ _ fun _ _ =>
      (natDegree_evalExcept_le i _ H).trans (hH i))

/--
info: 'MvPolynomial.hypercubeSum_last' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.hypercubeSum_last

/--
info: 'MvPolynomial.eval_sum_evalExcept_hypercube' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.eval_sum_evalExcept_hypercube

/--
info: 'MvPolynomial.natDegree_evalExcept_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.natDegree_evalExcept_le

end Tests.Hypercube
