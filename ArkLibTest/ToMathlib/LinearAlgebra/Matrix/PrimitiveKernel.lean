/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.LinearAlgebra.Matrix.PrimitiveKernel
import Mathlib.Algebra.EuclideanDomain.Int
import Mathlib.Data.ZMod.Basic

/-!
# Acceptance client for primitive kernel vectors

The examples derive zero-coordinate preservation from the factorization `v = g • u`, use the gcd
criterion to show that the integer vector `(2, 3)` survives reduction modulo every `n > 1`, and use
nonvanishing under a ring homomorphism with an infinite index type.
-/

open Matrix

/-- Normalization keeps every zero coordinate: `v j = g * u j` with `g ≠ 0` forces `u j = 0`
whenever `v j = 0`. -/
example {m n R : Type*} [Fintype n] [CommRing R] [IsBezout R] [NormalizedGCDMonoid R]
    (M : Matrix m n R) {v : n → R} (hv : v ≠ 0) (hMv : M *ᵥ v = 0) :
    ∃ u : n → R, u ≠ 0 ∧ M *ᵥ u = 0 ∧ Ideal.span (Set.range u) = ⊤ ∧
      ∀ j, v j = 0 → u j = 0 := by
  obtain ⟨g, u, hg, rfl, hu, hMu, hspan⟩ := M.exists_primitive_kernel_vector_eq_smul hv hMv
  refine ⟨u, hu, hMu, hspan, fun j hj ↦ ?_⟩
  rw [Pi.smul_apply, smul_eq_mul] at hj
  exact (mul_eq_zero.mp hj).resolve_left hg

/-- The coordinates of `(2, 3)` have gcd `1`, so no reduction modulo `n > 1` sends both to zero,
although reduction modulo `2` or modulo `3` sends one of them to zero. -/
example (n : ℕ) [Fact (1 < n)] : (fun j ↦ ((![2, 3] j : ℤ) : ZMod n)) ≠ 0 := by
  have hgcd : Finset.univ.gcd ![(2 : ℤ), 3] = 1 := by decide
  exact Ideal.comp_ne_zero_of_span_range_eq_top
    (Ideal.span_range_eq_top_iff_univ_gcd_eq_one.mpr hgcd) (Int.castRingHom (ZMod n))

/-- The primes generate the unit ideal of `ℤ`, so for every `n > 1` some prime is nonzero modulo
`n`. The index type `Nat.Primes` is infinite. -/
example (n : ℕ) [Fact (1 < n)] : ∃ p : Nat.Primes, ((p : ℕ) : ZMod n) ≠ 0 := by
  have hspan : Ideal.span (Set.range fun p : Nat.Primes ↦ ((p : ℕ) : ℤ)) = ⊤ := by
    rw [Ideal.eq_top_iff_one]
    have h2 : ((2 : ℕ) : ℤ) ∈ Ideal.span (Set.range fun p : Nat.Primes ↦ ((p : ℕ) : ℤ)) :=
      Ideal.subset_span ⟨⟨2, Nat.prime_two⟩, rfl⟩
    have h3 : ((3 : ℕ) : ℤ) ∈ Ideal.span (Set.range fun p : Nat.Primes ↦ ((p : ℕ) : ℤ)) :=
      Ideal.subset_span ⟨⟨3, Nat.prime_three⟩, rfl⟩
    simpa using Ideal.sub_mem _ h3 h2
  obtain ⟨p, hp⟩ :=
    Function.ne_iff.mp (Ideal.comp_ne_zero_of_span_range_eq_top hspan (Int.castRingHom (ZMod n)))
  exact ⟨p, by simpa using hp⟩

/--
info: 'Finset.span_gcd' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Finset.span_gcd

/--
info: 'Ideal.span_range_eq_top_iff_univ_gcd_eq_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ideal.span_range_eq_top_iff_univ_gcd_eq_one

/--
info: 'Ideal.comp_ne_zero_of_span_range_eq_top' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Ideal.comp_ne_zero_of_span_range_eq_top

/--
info: 'Matrix.exists_primitive_kernel_vector_eq_smul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Matrix.exists_primitive_kernel_vector_eq_smul
