import Mathlib.RingTheory.Polynomial.Basic

/-!
# `Polynomial.degreeLT` boundary facts

Lemmas about `Polynomial.degreeLT R n` (the submodule of polynomials of degree `< n`) at
the boundary `n = 0`, where it collapses to the zero submodule.

These are reusable for any construction that maps `degreeLT` through a linear map — e.g.
Reed-Solomon codes (`ReedSolomon.code α n = (degreeLT F n).map (evalOnPoints α)`), folded
RS codes, and similar code families. Candidate for upstream PR to Mathlib.
-/

namespace Polynomial

variable {R : Type*} [Semiring R]

/-- `Polynomial.degreeLT R 0 = ⊥`: the only polynomial with degree strictly less than `0`
(in `WithBot ℕ`) is the zero polynomial.

Not `@[simp]` to avoid disrupting existing simp-based proofs that unfold `degreeLT` directly. -/
theorem degreeLT_zero : degreeLT R 0 = ⊥ := by
  rw [eq_bot_iff]
  intro p hp
  rw [Polynomial.mem_degreeLT, Nat.cast_zero, Nat.WithBot.lt_zero_iff,
      Polynomial.degree_eq_bot] at hp
  exact hp ▸ Submodule.zero_mem _

end Polynomial
