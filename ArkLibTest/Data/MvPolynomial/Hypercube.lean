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
    Polynomial.eval 3 (sumRoundPolynomial (Finset.univ : Finset (Fin 0 → Fin 2))
      (fun _ => Fin.elim0) 0 (X (0 : Fin 1) + C (2 : ℕ))) = 5 := by
  norm_num [sumRoundPolynomial_eval, Fin.insertNth_zero]


example {S : Type*} [CommSemiring S] {m : ℕ}
    (H : MvPolynomial (Fin (m + 1)) S) (i : Fin (m + 1)) (cs : Fin i → S)
    {d : ℕ} (hH : ∀ j, H.degreeOf j ≤ d) :
    (sumRoundPolynomial (Finset.univ : Finset (Fin (m + 1 - (i + 1)) → Fin 2))
      (hypercubeSuffix i cs) i H).degree ≤
        (d : WithBot ℕ) :=
  Polynomial.natDegree_le_iff_degree_le.mp
    ((sumRoundPolynomial_natDegree_le _ _ i H).trans (hH i))

/--
info: 'MvPolynomial.hypercubeSum_last' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.hypercubeSum_last

/--
info: 'MvPolynomial.sumRoundPolynomial_eval_hypercube' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.sumRoundPolynomial_eval_hypercube

/--
info: 'MvPolynomial.sumRoundPolynomial_natDegree_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.sumRoundPolynomial_natDegree_le

end Tests.Hypercube
