/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import CompPoly.ToMathlib.Polynomial.Roots
public import CompPoly.Univariate.DivisionCorrectness
public import ArkLib.Data.Probability.Instances

/-!
# Quotient zero tests on finite domains

Vanishing on a finite set is equivalent to divisibility by Mathlib's `Lagrange.nodal S id`.
Monic division gives the unique quotient, including for the zero polynomial and empty domain.
For a false vanishing claim, a fixed quotient of degree at most `d - S.card` passes a uniform
evaluation check with probability at most `d / |F|`, provided `S.card ≤ d`.

Bounded computable polynomials and monic division provide an executable quotient. Their
mathematical specifications use Mathlib's polynomial representation. Evaluation of the nodal
polynomial is the finite product in `Lagrange.eval_nodal`; for multiplicative subgroups it is
the power expression `x ^ n - 1`.
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

namespace FiniteDomainQuotient

open CompPoly

variable (F : Type*) [Field F] [BEq F] [LawfulBEq F]

/-- A computable polynomial within an inclusive natural-degree budget. -/
abbrev Poly (d : ℕ) := {p : CPolynomial F // p.toPoly.natDegree ≤ d}

variable {F} {d : ℕ}

/-- Horner evaluation of a bounded polynomial. -/
def eval (p : Poly F d) (z : F) : F := CPolynomial.evalHorner z p.val

/-- Computable evaluation agrees with the mathematical polynomial. -/
theorem eval_eq (p : Poly F d) (z : F) : eval p z = p.val.toPoly.eval z := by
  rw [eval, CPolynomial.eval_horner_eq_eval, CPolynomial.eval_toPoly]

/-- The nodal polynomial as a computable product of monic linear factors. -/
def nodal (S : Finset F) : CPolynomial F :=
  ∏ x ∈ S, (CPolynomial.X - CPolynomial.C x)

/-- The computable nodal product represents Mathlib's nodal polynomial. -/
theorem nodal_toPoly (S : Finset F) : (nodal S).toPoly = Lagrange.nodal S id := by
  classical
  simp [nodal, Lagrange.nodal]

/-- Monic division computes a quotient within the remaining degree budget. -/
def quotient (S : Finset F) (f : Poly F d) : Poly F (d - S.card) :=
  ⟨f.val.divByMonic (nodal S), by
    rw [CPolynomial.divByMonic_toPoly_eq_divByMonic _ _ (by
      rw [CPolynomial.monic_toPoly_iff, nodal_toPoly]
      exact Lagrange.nodal_monic), nodal_toPoly,
      Polynomial.natDegree_divByMonic _ Lagrange.nodal_monic, Lagrange.natDegree_nodal]
    exact Nat.sub_le_sub_right f.property _⟩

/-- A vanishing polynomial equals the computed quotient times its nodal polynomial. -/
theorem quotient_identity (S : Finset F) (f : Poly F d)
    (hf : Polynomial.ZeroOn S f.val.toPoly) :
    f.val.toPoly = (quotient S f).val.toPoly * Lagrange.nodal S id := by
  obtain ⟨q, hq⟩ := Polynomial.zeroOn_iff_nodal_dvd.mp hf
  change f.val.toPoly = (f.val.divByMonic (nodal S)).toPoly * Lagrange.nodal S id
  rw [CPolynomial.divByMonic_toPoly_eq_divByMonic _ _ (by
    rw [CPolynomial.monic_toPoly_iff, nodal_toPoly]
    exact Lagrange.nodal_monic), nodal_toPoly, hq,
    Polynomial.mul_divByMonic_cancel_left _ Lagrange.nodal_monic, mul_comm]

end FiniteDomainQuotient

namespace Lagrange

/-- A multiplicative subgroup embeds into the field by forgetting its unit structure. -/
def subgroupEmbedding {F : Type*} [Field F] (H : Subgroup Fˣ) : H ↪ F where
  toFun h := (h.val : F)
  inj' _ _ h := Subtype.ext (Units.val_injective h)

/-- The image of a finite multiplicative subgroup has nodal evaluation `z ^ |H| - 1`. -/
theorem eval_nodal_image_subgroup {F : Type*} [Field F] (H : Subgroup Fˣ)
    [Fintype H] (z : F) :
    (nodal (Finset.univ.map (subgroupEmbedding H)) id).eval z =
      z ^ Fintype.card H - 1 := by
  classical
  have hprod : nodal (Finset.univ.map (subgroupEmbedding H)) id =
      nodal (H : Set Fˣ).toFinset ((↑) : Fˣ → F) := by
    simp only [nodal, Finset.prod_map, id_eq,
      subgroupEmbedding]
    exact Finset.prod_set_coe (f := fun h : Fˣ => Polynomial.X - Polynomial.C (h : F))
      (H : Set Fˣ)
  rw [hprod, eval_nodal_subgroup]

end Lagrange
