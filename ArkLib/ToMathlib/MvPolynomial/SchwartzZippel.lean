/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-!
# The Schwartz–Zippel bound as a zero count

Mathlib's `MvPolynomial.schwartz_zippel_totalDegree` bounds the proportion of zeros of a nonzero
polynomial in `n` variables over a domain on a grid `Sⁿ` by `totalDegree / #S`, in `ℚ≥0`. For
`n + 1` variables this is equivalent to the division-free count

  `#{x ∈ Sⁿ⁺¹ | p(x) = 0} ≤ totalDegree p * #S ^ n`,

which is `card_filter_eval_eq_zero_le`. The empty grid needs no special hypothesis: it has no
points.
-/

@[expose] public section

namespace MvPolynomial

open Finset

variable {R : Type*} [CommRing R] [IsDomain R] [DecidableEq R]

/-- **Schwartz–Zippel, division-free.** A nonzero polynomial `p` in `n + 1` variables over a domain
has at most `p.totalDegree * #S ^ n` zeros on the grid `Sⁿ⁺¹`. -/
theorem card_filter_eval_eq_zero_le {n : ℕ} {p : MvPolynomial (Fin (n + 1)) R} (hp : p ≠ 0)
    (S : Finset R) :
    #{x ∈ Fintype.piFinset fun _ ↦ S | eval x p = 0} ≤ p.totalDegree * #S ^ n := by
  obtain rfl | hS := S.eq_empty_or_nonempty
  · simp
  have h := schwartz_zippel_totalDegree hp S
  have hpos : (0 : ℚ≥0) < #S := by exact_mod_cast hS.card_pos
  rw [div_le_div_iff₀ (pow_pos hpos _) hpos, pow_succ, ← mul_assoc] at h
  exact_mod_cast le_of_mul_le_mul_right h hpos

end MvPolynomial
