/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import CompPoly.ToMathlib.Polynomial.Roots
public import ArkLib.Data.Probability.Instances

/-!
# Quotient zero tests on finite domains

Vanishing on a finite set is equivalent to divisibility by Mathlib's `Lagrange.nodal S id`.
Monic division gives the unique quotient, including for the zero polynomial and empty domain.
For a false vanishing claim, a fixed quotient of degree at most `d - S.card` passes a uniform
evaluation check with probability at most `d / |F|`, provided `S.card ≤ d`.

The polynomial and quotient use Mathlib's mathematical representation. Evaluation of the nodal
polynomial is the computable finite product in `Lagrange.eval_nodal`; for multiplicative subgroups
it is the power expression `x ^ n - 1`.
-/

@[expose] public section

namespace Polynomial

variable {F : Type*} [Field F]

/-- A polynomial vanishes on every point of a finite domain. -/
def ZeroOn (S : Finset F) (f : F[X]) : Prop := ∀ x ∈ S, f.eval x = 0

/-- Vanishing on a finite domain is divisibility by its nodal polynomial. -/
theorem zeroOn_iff_nodal_dvd {S : Finset F} {f : F[X]} :
    ZeroOn S f ↔ Lagrange.nodal S id ∣ f := by
  constructor
  · intro h
    simpa only [Lagrange.nodal] using
      Polynomial.prod_X_sub_C_dvd S id Function.injective_id.injOn f h
  · rintro ⟨q, rfl⟩ x hx
    have hz : (Lagrange.nodal S id).eval x = 0 :=
      Lagrange.eval_nodal_at_node (v := id) hx
    rw [eval_mul, hz, zero_mul]

/-- The unique quotient has natural degree `f.natDegree - S.card`.
For `f = 0`, this uses the convention `natDegree 0 = 0`. -/
theorem ZeroOn.existsUnique_quotient {S : Finset F} {f : F[X]} (hf : ZeroOn S f) :
    ∃! q : F[X], f = q * Lagrange.nodal S id ∧
      q.natDegree = f.natDegree - S.card := by
  obtain ⟨q, hq⟩ := zeroOn_iff_nodal_dvd.mp hf
  have hdiv : f /ₘ Lagrange.nodal S id = q := by
    rw [hq, mul_divByMonic_cancel_left _ Lagrange.nodal_monic]
  refine ⟨q, ⟨by simpa [mul_comm] using hq, ?_⟩, ?_⟩
  · rw [← hdiv, natDegree_divByMonic _ Lagrange.nodal_monic, Lagrange.natDegree_nodal]
  · intro r hr
    exact mul_right_cancel₀ Lagrange.nodal_ne_zero (hr.1.symm.trans (by
      simpa [mul_comm] using hq))

/-- A degree budget on the dividend gives a unique quotient within the remaining budget. -/
theorem zeroOn_iff_existsUnique_quotient_natDegree_le {S : Finset F} {f : F[X]} {d : ℕ}
    (hfdeg : f.natDegree ≤ d) :
    ZeroOn S f ↔ ∃! q : F[X], f = q * Lagrange.nodal S id ∧
      q.natDegree ≤ d - S.card := by
  constructor
  · intro hf
    obtain ⟨q, ⟨hq, hdeg⟩, _⟩ := hf.existsUnique_quotient
    refine ⟨q, ⟨hq, hdeg ▸ Nat.sub_le_sub_right hfdeg _⟩, ?_⟩
    intro r hr
    exact mul_right_cancel₀ Lagrange.nodal_ne_zero (hr.1.symm.trans hq)
  · rintro ⟨q, hq, _⟩
    exact zeroOn_iff_nodal_dvd.mpr ⟨q, by simpa [mul_comm] using hq.1⟩

/-- Every candidate quotient for a false vanishing claim leaves a nonzero residual. -/
theorem sub_mul_nodal_ne_zero {S : Finset F} {f : F[X]} (hf : ¬ ZeroOn S f)
    (q : F[X]) : f - q * Lagrange.nodal S id ≠ 0 := by
  intro h
  exact hf (zeroOn_iff_nodal_dvd.mpr ⟨q, by
    simpa [mul_comm] using sub_eq_zero.mp h⟩)

/-- The cardinality condition makes the truncated quotient budget a valid residual budget. -/
theorem natDegree_sub_mul_nodal_le {S : Finset F} {f q : F[X]} {d : ℕ}
    (hcard : S.card ≤ d) (hf : f.natDegree ≤ d) (hq : q.natDegree ≤ d - S.card) :
    (f - q * Lagrange.nodal S id).natDegree ≤ d := by
  refine (natDegree_sub_le _ _).trans (max_le hf ?_)
  refine (natDegree_mul_le.trans ?_)
  rw [Lagrange.natDegree_nodal]
  omega

open ProbabilityTheory
open scoped ProbabilityTheory ENNReal

/-- A false finite-domain zero claim passes the quotient identity check at a uniform point
with probability at most `d / |F|`. The candidate quotient is fixed before sampling. -/
theorem prob_eval_eq_mul_nodal_le {F : Type} [Field F] [Fintype F] [SampleableType F]
    {S : Finset F} {f q : F[X]} {d : ℕ} (hcard : S.card ≤ d)
    (hf : ¬ ZeroOn S f) (hfdeg : f.natDegree ≤ d)
    (hqdeg : q.natDegree ≤ d - S.card) :
    Pr{let x ← $ᵗ F}[f.eval x = q.eval x * (Lagrange.nodal S id).eval x] ≤
      (d : ℝ≥0∞) / Fintype.card F := by
  have h := Probability.prob_polynomial_eval_eq_le
    (sub_mul_nodal_ne_zero hf q) (natDegree_sub_mul_nodal_le hcard hfdeg hqdeg)
    (show (0 : F[X]).natDegree ≤ d by simp)
  simpa only [eval_sub, eval_mul, eval_zero, sub_eq_zero] using h

end Polynomial

namespace Lagrange

/-- Evaluation on a multiplicative subgroup of order `n` uses only powering and subtraction. -/
theorem eval_nodal_subgroup {F : Type*} [Field F] (H : Subgroup Fˣ) [Fintype H] (x : F) :
    (nodal (H : Set Fˣ).toFinset ((↑) : Fˣ → F)).eval x =
      x ^ Fintype.card H - 1 := by
  rw [nodal_subgroup_eq_X_pow_card_sub_one]
  simp

end Lagrange
