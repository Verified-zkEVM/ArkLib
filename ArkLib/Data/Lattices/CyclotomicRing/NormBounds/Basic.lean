/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Rq
import ArkLib.Data.Lattices.CyclotomicRing.Vectors
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.ValMinAbs

/-!
# Centered Norms And Norm-Growth Bounds on `Rq Φ` (Common Layer)

The centered `ℓ₁` / squared-`ℓ₂` norms of a cyclotomic-ring element `a : Rq Φ` over
`ZMod q` (sums of `ZMod.valMinAbs` representatives of its coefficients), their vector
lifts, the bound expressions, and the genuinely-proven norm-growth fact:

* `sub_l2NormSq_le` — `‖v - w‖₂² ≤ 4·b` whenever `‖v‖₂², ‖w‖₂² ≤ b`,

which lets the Module-SIS shortness predicate be instantiated concretely (see
`Ajtai.Simple.Security`). The foundational fact is the minimality of the centered
representative (`valMinAbs_natAbs_le`).

There are two more complicated norm-lemmas in sibling files:
* `NormBounds.MicciancioYoung` — the product bound `scalarVecMul_mul_l2NormSq_le`;
* `NormBounds.LyubashevskySeiler` — short-element invertibility `isUnit_of_l1Norm_le`.

## References

* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open scoped BigOperators

namespace ArkLib.Lattices.CyclotomicModulus

variable {q : ℕ} [NeZero q]

/-! ## Minimality and triangle inequality for the centered representative -/

/-- The centered representative `valMinAbs` has the least absolute value among all
integer representatives of a residue class. -/
theorem valMinAbs_natAbs_le {a : ZMod q} (m : ℤ) (h : (m : ZMod q) = a) :
    a.valMinAbs.natAbs ≤ m.natAbs := by
  have hmem := ZMod.valMinAbs_mem_Ioc a
  rw [Set.mem_Ioc] at hmem
  have hcast : (m : ZMod q) = ((a.valMinAbs : ℤ) : ZMod q) := by rw [h, ZMod.coe_valMinAbs]
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hcast
  obtain ⟨t, ht⟩ := hcast
  have hq : (1 : ℤ) ≤ (q : ℤ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  rcases eq_or_ne t 0 with ht0 | ht0
  · subst ht0; simp only [mul_zero] at ht; omega
  · have habs : q ≤ ((q : ℤ) * t).natAbs := by
      have ht1 : 1 ≤ t.natAbs := Int.natAbs_pos.mpr ht0
      rw [Int.natAbs_mul]; simp only [Int.natAbs_natCast]; nlinarith [ht1]
    revert ht habs
    generalize (q : ℤ) * t = k
    intro ht habs
    omega

/-- Centered representative of a difference: bounded by the sum of the centered
representatives' absolute values. -/
theorem valMinAbs_sub_natAbs_le (a b : ZMod q) :
    (a - b).valMinAbs.natAbs ≤ a.valMinAbs.natAbs + b.valMinAbs.natAbs := by
  have h : ((a.valMinAbs - b.valMinAbs : ℤ) : ZMod q) = a - b := by
    rw [Int.cast_sub, ZMod.coe_valMinAbs, ZMod.coe_valMinAbs]
  exact le_trans (valMinAbs_natAbs_le _ h) (Int.natAbs_sub_le _ _)

variable [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]

/-! ## The centered norms -/

/-- Centered squared-`ℓ₂` norm of a ring element: `Σₖ |cₖ|²` over the centered
representatives of its coefficients (summed over the degree range of the modulus). -/
def Rq.l2NormSq (a : Rq Φ) : ℕ :=
  ∑ k ∈ Finset.range Φ.φ.natDegree, (a.1.coeff k).valMinAbs.natAbs ^ 2

/-- Centered `ℓ₁` norm of a ring element: `Σₖ |cₖ|` over the centered representatives. -/
def Rq.l1Norm (a : Rq Φ) : ℕ :=
  ∑ k ∈ Finset.range Φ.φ.natDegree, (a.1.coeff k).valMinAbs.natAbs

/-- Centered `ℓ∞` norm of a ring element: `maxₖ |cₖ|` over the centered representatives
of its coefficients (over the degree range of the modulus). -/
def Rq.lInftyNorm (a : Rq Φ) : ℕ :=
  (Finset.range Φ.φ.natDegree).sup (fun k => (a.1.coeff k).valMinAbs.natAbs)

/-- Centered squared-`ℓ₂` norm of a vector: the sum of entrywise norms. -/
def vecL2NormSq {cols : ℕ} (z : PolyVec (Rq Φ) cols) : ℕ :=
  ∑ i : Fin cols, Rq.l2NormSq Φ (z i)

/-- Centered `ℓ∞` norm of a vector: the largest entrywise `ℓ∞` norm. -/
def vecLInftyNorm {cols : ℕ} (z : PolyVec (Rq Φ) cols) : ℕ :=
  (Finset.univ : Finset (Fin cols)).sup (fun i => Rq.lInftyNorm Φ (z i))

omit [NeZero q] in
/-- The underlying polynomial of `1 : Rq Φ` is the constant `1` (no reduction occurs, as
`deg 1 = 0 < deg φ`). -/
theorem Rq.one_val (h : 1 ≤ Φ.φ.natDegree) : (1 : Rq Φ).1 = 1 := by
  change Φ.reduce 1 = 1
  apply Φ.reduce_eq_self_of_degree_lt
  rw [CompPoly.CPolynomial.toPoly_one, Polynomial.degree_one]
  have hnd : 0 < Φ.φ.toPoly.natDegree := by
    rw [← CompPoly.CPolynomial.natDegree_toPoly]; omega
  exact Polynomial.natDegree_pos_iff_degree_pos.mp hnd

omit [NeZero q] in
/-- The centered `ℓ₁` norm of `1 : Rq Φ` is `1` (when `1 ≤ deg φ`): the trivial challenge `c = 1`
used by the honest committer is nonzero and `ℓ₁`-short. -/
theorem Rq.l1Norm_one (h : 1 ≤ Φ.φ.natDegree) : Rq.l1Norm Φ (1 : Rq Φ) = 1 := by
  have hq2 : 2 ≤ q := (Fact.out (p := Nat.Prime q)).two_le
  unfold Rq.l1Norm
  rw [Finset.sum_eq_single (0 : ℕ)]
  · rw [Rq.one_val Φ h, CompPoly.CPolynomial.coeff_one, if_pos rfl,
      show (1 : ZMod q) = ((1 : ℕ) : ZMod q) by norm_cast,
      ZMod.valMinAbs_natCast_of_le_half (by omega)]
    norm_num
  · intro k _ hk
    rw [Rq.one_val Φ h, CompPoly.CPolynomial.coeff_one, if_neg hk]
    simp
  · intro h0
    exact absurd (Finset.mem_range.mpr (by omega)) h0

omit [NeZero q] [IsCyclotomic Φ] in
/-- The `ℓ∞` norm of a flattened block vector is bounded by `γ` as soon as every block is: the
`ℓ∞` norm of `flattenBlocks` is the supremum of the per-block `ℓ∞` norms. -/
theorem vecLInftyNorm_flattenBlocks_le {blocks width : Nat} {γ : ℕ}
    (xs : PolyVec (PolyVec (Rq Φ) width) blocks)
    (h : ∀ i, vecLInftyNorm Φ (xs i) ≤ γ) :
    vecLInftyNorm Φ (PolyVec.flattenBlocks xs) ≤ γ := by
  unfold vecLInftyNorm
  refine Finset.sup_le (fun j _ => ?_)
  simp only [PolyVec.flattenBlocks]
  calc Rq.lInftyNorm Φ
          (xs (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2)
      ≤ (Finset.univ : Finset (Fin width)).sup
          (fun j' => Rq.lInftyNorm Φ (xs (finProdFinEquiv.symm j).1 j')) :=
        Finset.le_sup (f := fun j' => Rq.lInftyNorm Φ (xs (finProdFinEquiv.symm j).1 j'))
          (Finset.mem_univ _)
    _ ≤ γ := h _

/-! ## The growth-bound expressions -/

/-- The squared-`ℓ₂` bound for a difference of two vectors within `boundSq`: `4·boundSq`. -/
def subL2NormSqBound (boundSq : ℕ) : ℕ := 4 * boundSq

/-- The `ℓ∞` bound for a difference of two vectors within `bound`: `2·bound` (the `ℓ∞`
triangle inequality, no squaring). -/
def subLInftyNormBound (bound : ℕ) : ℕ := 2 * bound

/-- Squared-`ℓ₂` growth bound for scaling an already-scaled vector by a further scalar of
bounded `ℓ₁` norm: `κ² · β²`. -/
def scalarVecMulMulL2NormSqBound (κ βSq : ℕ) : ℕ := κ ^ 2 * βSq

/-! ## The subtraction bound (proven) -/

/-- Per-element subtraction bound: `‖a - b‖₂² ≤ 2·(‖a‖₂² + ‖b‖₂²)`. -/
theorem Rq.l2NormSq_sub_le (a b : Rq Φ) :
    Rq.l2NormSq Φ (a - b) ≤ 2 * (Rq.l2NormSq Φ a + Rq.l2NormSq Φ b) := by
  unfold Rq.l2NormSq
  rw [← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_le_sum (fun k _ => ?_)
  have hcoeff : (a - b).1.coeff k = a.1.coeff k - b.1.coeff k := by
    rw [Rq.sub_val, CompPoly.CPolynomial.coeff_sub]
  rw [hcoeff]
  have htri := valMinAbs_sub_natAbs_le (a.1.coeff k) (b.1.coeff k)
  have htriZ : ((a.1.coeff k - b.1.coeff k).valMinAbs.natAbs : ℤ)
      ≤ (a.1.coeff k).valMinAbs.natAbs + (b.1.coeff k).valMinAbs.natAbs := by exact_mod_cast htri
  have key : ((a.1.coeff k - b.1.coeff k).valMinAbs.natAbs : ℤ) ^ 2
      ≤ 2 * (((a.1.coeff k).valMinAbs.natAbs : ℤ) ^ 2
        + ((b.1.coeff k).valMinAbs.natAbs : ℤ) ^ 2) := by
    nlinarith [htriZ, Int.natCast_nonneg (a.1.coeff k - b.1.coeff k).valMinAbs.natAbs,
      sq_nonneg (((a.1.coeff k).valMinAbs.natAbs : ℤ) - (b.1.coeff k).valMinAbs.natAbs)]
  exact_mod_cast key

/-- **Subtraction bound.** The squared `ℓ₂` norm of a difference of two vectors, each
within `boundSq`, is within `subL2NormSqBound boundSq = 4·boundSq`. -/
theorem sub_l2NormSq_le {cols : ℕ} (v w : PolyVec (Rq Φ) cols) {boundSq : ℕ}
    (hv : vecL2NormSq Φ v ≤ boundSq) (hw : vecL2NormSq Φ w ≤ boundSq) :
    vecL2NormSq Φ (v - w) ≤ subL2NormSqBound boundSq := by
  have hstep : vecL2NormSq Φ (v - w) ≤ 2 * (vecL2NormSq Φ v + vecL2NormSq Φ w) := by
    unfold vecL2NormSq
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_le_sum (fun i _ => ?_)
    simp only [Pi.sub_apply]
    exact Rq.l2NormSq_sub_le Φ (v i) (w i)
  unfold subL2NormSqBound
  omega

/-! ## The `ℓ∞` subtraction bound (proven) -/

/-- Per-element `ℓ∞` triangle inequality: `‖a - b‖∞ ≤ ‖a‖∞ + ‖b‖∞`. -/
theorem Rq.lInftyNorm_sub_le (a b : Rq Φ) :
    Rq.lInftyNorm Φ (a - b) ≤ Rq.lInftyNorm Φ a + Rq.lInftyNorm Φ b := by
  unfold Rq.lInftyNorm
  refine Finset.sup_le (fun k hk => ?_)
  have hcoeff : (a - b).1.coeff k = a.1.coeff k - b.1.coeff k := by
    rw [Rq.sub_val, CompPoly.CPolynomial.coeff_sub]
  rw [hcoeff]
  calc (a.1.coeff k - b.1.coeff k).valMinAbs.natAbs
      ≤ (a.1.coeff k).valMinAbs.natAbs + (b.1.coeff k).valMinAbs.natAbs :=
        valMinAbs_sub_natAbs_le _ _
    _ ≤ (Finset.range Φ.φ.natDegree).sup (fun k => (a.1.coeff k).valMinAbs.natAbs)
          + (Finset.range Φ.φ.natDegree).sup (fun k => (b.1.coeff k).valMinAbs.natAbs) :=
        add_le_add
          (Finset.le_sup (f := fun k => (a.1.coeff k).valMinAbs.natAbs) hk)
          (Finset.le_sup (f := fun k => (b.1.coeff k).valMinAbs.natAbs) hk)

/-- **`ℓ∞` subtraction bound.** The `ℓ∞` norm of a difference of two vectors, each within
`bound`, is within `subLInftyNormBound bound = 2·bound`. -/
theorem sub_lInftyNorm_le {cols : ℕ} (v w : PolyVec (Rq Φ) cols) {bound : ℕ}
    (hv : vecLInftyNorm Φ v ≤ bound) (hw : vecLInftyNorm Φ w ≤ bound) :
    vecLInftyNorm Φ (v - w) ≤ subLInftyNormBound bound := by
  have hstep : vecLInftyNorm Φ (v - w) ≤ vecLInftyNorm Φ v + vecLInftyNorm Φ w := by
    unfold vecLInftyNorm
    refine Finset.sup_le (fun i _ => ?_)
    simp only [Pi.sub_apply]
    calc Rq.lInftyNorm Φ (v i - w i)
        ≤ Rq.lInftyNorm Φ (v i) + Rq.lInftyNorm Φ (w i) := Rq.lInftyNorm_sub_le Φ _ _
      _ ≤ (Finset.univ : Finset (Fin cols)).sup (fun i => Rq.lInftyNorm Φ (v i))
            + (Finset.univ : Finset (Fin cols)).sup (fun i => Rq.lInftyNorm Φ (w i)) :=
          add_le_add
            (Finset.le_sup (f := fun i => Rq.lInftyNorm Φ (v i)) (Finset.mem_univ i))
            (Finset.le_sup (f := fun i => Rq.lInftyNorm Φ (w i)) (Finset.mem_univ i))
  unfold subLInftyNormBound
  omega

end ArkLib.Lattices.CyclotomicModulus
