/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.MvPolynomial.FirstOrderTaylor

/-!
# First-order Taylor expansion acceptance tests

* Over `ℤ`, the pivot form applied to `x³` gives `t² ∣ (a + t)³ - a³ - 3 a² t` for all
  integers `a` and `t`.
* The hypothesis `0 < k` is needed: with `p = x²`, `a = 0`, `d = 1`, `u = 0` and `k = 0`, the
  first-order error is `1`, which `0 ^ 1 = 0` does not divide.
* The zero-order congruence gives `5 ∣ p(7) - p(2)` for every integer polynomial `p`.
-/

open MvPolynomial

/-- The pivot form applied to `x³` over `ℤ`, with `u = t` and `k = 1`. -/
example (a t : ℤ) : t ^ 2 ∣ (a + t) ^ 3 - a ^ 3 - 3 * a ^ 2 * t := by
  have h := pow_succ_dvd_eval₂Hom_add_sub_pderiv (RingHom.id ℤ) (fun _ : Fin 1 ↦ a)
    (fun _ ↦ t) Finset.univ (X 0 ^ 3) 0 t 1 one_pos (Finset.mem_univ 0) (by simp)
    (fun i _ hi ↦ absurd (Subsingleton.elim i 0) hi) (fun i hi ↦ absurd (Finset.mem_univ i) hi)
  convert h using 1
  simp [Derivation.leibniz_pow]

/-- The conclusion of `pow_succ_dvd_eval₂Hom_add_sub_firstOrderIncrement` fails at `k = 0`. -/
example : ¬(0 : ℤ) ^ (0 + 1) ∣
    eval₂Hom (RingHom.id ℤ) ((fun _ : Fin 1 ↦ (0 : ℤ)) + fun _ ↦ 1) (X 0 ^ 2) -
      eval₂Hom (RingHom.id ℤ) (fun _ ↦ 0) (X 0 ^ 2 : MvPolynomial (Fin 1) ℤ) -
      firstOrderIncrement (RingHom.id ℤ) (fun _ ↦ 0) (fun _ ↦ 1) Finset.univ
        (X 0 ^ 2 : MvPolynomial (Fin 1) ℤ) := by
  simp [firstOrderIncrement, Derivation.leibniz_pow]

/-- The zero-order congruence: `7 ≡ 2 (mod 5)` gives `p(7) ≡ p(2) (mod 5)`. -/
example (p : MvPolynomial (Fin 1) ℤ) :
    (5 : ℤ) ∣ eval₂Hom (RingHom.id ℤ) (fun _ ↦ 7) p - eval₂Hom (RingHom.id ℤ) (fun _ ↦ 2) p :=
  dvd_eval₂Hom_sub_eval₂Hom _ _ _ 5 (fun _ ↦ by norm_num) p
