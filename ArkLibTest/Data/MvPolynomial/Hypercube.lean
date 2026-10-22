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
    Polynomial.eval 3 (roundPoly (X (0 : Fin 1) + C (2 : ℕ)) 0 Fin.elim0) = 5 := by
  rw [roundPoly_eval]
  change hypercubeSum 1 (X (0 : Fin 1) + C (2 : ℕ)) 1 (Fin.snoc Fin.elim0 3) = 5
  rw [hypercubeSum_last]
  norm_num [Fin.snoc]

example {S : Type*} [CommSemiring S] {m : ℕ}
    (H : MvPolynomial (Fin (m + 1)) S) (i : Fin (m + 1)) (cs : Fin i → S)
    {d : ℕ} (hH : ∀ j, H.degreeOf j ≤ d) :
    (roundPoly H i cs).degree ≤ (d : WithBot ℕ) :=
  roundPoly_degree_le H i cs hH

/--
info: 'MvPolynomial.hypercubeSum_last' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.hypercubeSum_last

/--
info: 'MvPolynomial.roundPoly_eval' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.roundPoly_eval

/--
info: 'MvPolynomial.roundPoly_degree_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms MvPolynomial.roundPoly_degree_le

end Tests.Hypercube
