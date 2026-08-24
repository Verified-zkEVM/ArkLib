/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Finiteness

/-!
# A Kummer irreducibility criterion over a finite field

Over a finite field `F` of order `q`, the polynomial `X ^ (q - 1) - C ω` is irreducible
whenever `ω` generates `Fˣ`, together with the Frobenius identities used to prove it.

## Main statements

* `Polynomial.aeval_pow_card_pow` — `aeval (y ^ q ^ i) f = aeval y f ^ q ^ i`.
* `FiniteField.pow_card_pow_eq_mul` — if `x ^ (q - 1) = ω` in an `F`-algebra, then
  `x ^ q ^ i = ω ^ i * x`.
* `Polynomial.X_pow_card_sub_one_sub_C_irreducible` — the irreducibility criterion.

Generic facts intended as candidates for upstreaming to Mathlib.
-/

namespace Polynomial

variable {F : Type*} [Field F] [Fintype F]

private lemma expand_card_pow (i : ℕ) (f : F[X]) :
    expand F (Fintype.card F ^ i) f = f ^ (Fintype.card F ^ i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [pow_succ, expand_mul, FiniteField.expand_card, map_pow, ih, ← pow_mul]

/-- Frobenius transport for evaluation of a polynomial over a finite field. -/
lemma aeval_pow_card_pow {K : Type*} [CommSemiring K] [Algebra F K]
    (y : K) (f : F[X]) (i : ℕ) :
    aeval (y ^ (Fintype.card F ^ i)) f = (aeval y f) ^ (Fintype.card F ^ i) := by
  rw [← expand_aeval, expand_card_pow, map_pow]

end Polynomial

namespace FiniteField

variable {F : Type*} [Field F] [Fintype F]

/-- If `x ^ (q - 1) = ω` in an `F`-algebra, where `q = |F|`, then `x ^ q ^ i = ω ^ i * x`. -/
lemma pow_card_pow_eq_mul {K : Type*} [CommRing K] [Algebra F K] {ω : F} {x : K}
    (hx : x ^ (Fintype.card F - 1) = algebraMap F K ω) (i : ℕ) :
    x ^ (Fintype.card F ^ i) = algebraMap F K (ω ^ i) * x := by
  have hcard : Fintype.card F = (Fintype.card F - 1) + 1 :=
    (Nat.succ_pred_eq_of_pos Fintype.card_pos).symm
  have hxq : x ^ Fintype.card F = algebraMap F K ω * x := by
    conv_lhs => rw [hcard]
    rw [pow_succ, hx]
  induction i with
  | zero => simp
  | succ i ih =>
    calc x ^ (Fintype.card F ^ (i + 1))
        = (x ^ (Fintype.card F ^ i)) ^ Fintype.card F := by rw [← pow_mul, ← pow_succ]
      _ = algebraMap F K ((ω ^ i) ^ Fintype.card F) * x ^ Fintype.card F := by
          rw [ih, mul_pow, ← map_pow]
      _ = algebraMap F K (ω ^ i) * (algebraMap F K ω * x) := by rw [FiniteField.pow_card, hxq]
      _ = algebraMap F K (ω ^ (i + 1)) * x := by rw [← mul_assoc, ← map_mul, ← pow_succ]

end FiniteField

namespace Polynomial

variable {F : Type*} [Field F] [Fintype F]

/-- For a generator `ω` of the multiplicative group of a finite field `F` of order `q`, the
polynomial `X ^ (q - 1) - C ω` is irreducible. -/
theorem X_pow_card_sub_one_sub_C_irreducible {ω : F}
    (hω : orderOf ω = Fintype.card F - 1) :
    Irreducible ((X : F[X]) ^ (Fintype.card F - 1) - C ω) := by
  classical
  have hq2 : 1 < Fintype.card F := Fintype.one_lt_card
  have hq1 : Fintype.card F - 1 ≠ 0 := by omega
  have hEmonic : ((X : F[X]) ^ (Fintype.card F - 1) - C ω).Monic := monic_X_pow_sub_C ω hq1
  have hE0 : ((X : F[X]) ^ (Fintype.card F - 1) - C ω) ≠ 0 := hEmonic.ne_zero
  have hEdeg : ((X : F[X]) ^ (Fintype.card F - 1) - C ω).natDegree = Fintype.card F - 1 :=
    natDegree_X_pow_sub_C
  have hEnu : ¬ IsUnit ((X : F[X]) ^ (Fintype.card F - 1) - C ω) :=
    not_isUnit_of_natDegree_pos _ (by omega)
  obtain ⟨g, hg, hgd⟩ := WfDvdMonoid.exists_irreducible_factor hEnu hE0
  haveI : Fact (Irreducible g) := ⟨hg⟩
  have hd0 : 0 < g.natDegree := hg.natDegree_pos
  have hdle : g.natDegree ≤ Fintype.card F - 1 := hEdeg ▸ natDegree_le_of_dvd hgd hE0
  haveI : Module.Finite F (AdjoinRoot g) := PowerBasis.finite (AdjoinRoot.powerBasis hg.ne_zero)
  haveI : Finite (AdjoinRoot g) := Module.finite_of_finite F
  haveI : Fintype (AdjoinRoot g) := Fintype.ofFinite _
  have hcardK : Fintype.card (AdjoinRoot g) = Fintype.card F ^ g.natDegree := by
    rw [Module.card_eq_pow_finrank (K := F)]
    congr 1
    exact ((AdjoinRoot.powerBasis hg.ne_zero).finrank).trans (AdjoinRoot.powerBasis_dim _)
  have hx : (AdjoinRoot.root g) ^ (Fintype.card F - 1) = algebraMap F (AdjoinRoot g) ω := by
    have h0 : aeval (AdjoinRoot.root g) ((X : F[X]) ^ (Fintype.card F - 1) - C ω) = 0 := by
      rw [AdjoinRoot.aeval_eq]; exact AdjoinRoot.mk_eq_zero.mpr hgd
    simpa [sub_eq_zero] using h0
  have hω0 : ω ≠ 0 := by
    intro h
    have h1 := pow_orderOf_eq_one ω
    rw [hω, h, zero_pow hq1] at h1
    exact zero_ne_one h1
  have hx0 : (AdjoinRoot.root g) ≠ 0 := by
    intro h
    rw [h, zero_pow hq1] at hx
    exact hω0 ((map_eq_zero (algebraMap F (AdjoinRoot g))).mp hx.symm)
  have hfix : (AdjoinRoot.root g) ^ (Fintype.card F ^ g.natDegree) = AdjoinRoot.root g := by
    rw [← hcardK]; exact FiniteField.pow_card _
  have hωd : ω ^ g.natDegree = 1 := by
    have h1 : algebraMap F (AdjoinRoot g) (ω ^ g.natDegree) * AdjoinRoot.root g =
        algebraMap F (AdjoinRoot g) 1 * AdjoinRoot.root g := by
      rw [map_one, one_mul, ← FiniteField.pow_card_pow_eq_mul hx g.natDegree]
      exact hfix
    exact (algebraMap F (AdjoinRoot g)).injective (mul_right_cancel₀ hx0 h1)
  have hdvd : Fintype.card F - 1 ∣ g.natDegree := hω ▸ orderOf_dvd_of_pow_eq_one hωd
  have hdeq : g.natDegree = Fintype.card F - 1 := le_antisymm hdle (Nat.le_of_dvd hd0 hdvd)
  obtain ⟨h, hh⟩ := hgd
  have hh0 : h ≠ 0 := by rintro rfl; rw [mul_zero] at hh; exact hE0 hh
  have hhdeg : h.natDegree = 0 := by
    have := natDegree_mul hg.ne_zero hh0
    rw [← hh, hEdeg, hdeq] at this
    omega
  have hhu : IsUnit h :=
    isUnit_iff_degree_eq_zero.mpr (by rw [degree_eq_natDegree hh0, hhdeg]; rfl)
  exact (Associated.irreducible ⟨hhu.unit, by rw [IsUnit.unit_spec]; exact hh.symm⟩ hg)

end Polynomial
