/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Rq
import ArkLib.Data.Lattices.Vectors
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

/-- Centered representative of a product: submultiplicative. Note there is **no wraparound
condition**: `valMinAbs` is minimal among all integer representatives
(`valMinAbs_natAbs_le`), and `a.valMinAbs * b.valMinAbs` is one, so the bound survives however
much `a * b` wraps. -/
theorem valMinAbs_natAbs_mul_le (a b : ZMod q) :
    (a * b).valMinAbs.natAbs ≤ a.valMinAbs.natAbs * b.valMinAbs.natAbs := by
  have h : ((a.valMinAbs * b.valMinAbs : ℤ) : ZMod q) = a * b := by
    rw [Int.cast_mul, ZMod.coe_valMinAbs, ZMod.coe_valMinAbs]
  exact le_of_le_of_eq (valMinAbs_natAbs_le _ h) (Int.natAbs_mul _ _)

/-- Centered representative of a finite sum: triangle inequality. Again no wraparound condition is
needed, for the same reason as `valMinAbs_natAbs_mul_le`. -/
theorem valMinAbs_natAbs_sum_le {ι : Type*} (s : Finset ι) (f : ι → ZMod q) :
    (∑ i ∈ s, f i).valMinAbs.natAbs ≤ ∑ i ∈ s, (f i).valMinAbs.natAbs := by
  have h : ((∑ i ∈ s, (f i).valMinAbs : ℤ) : ZMod q) = ∑ i ∈ s, f i := by
    rw [Int.cast_sum]
    exact Finset.sum_congr rfl fun i _ => ZMod.coe_valMinAbs (f i)
  refine le_trans (valMinAbs_natAbs_le _ h) ?_
  calc (∑ i ∈ s, (f i).valMinAbs).natAbs
      ≤ ∑ i ∈ s, (f i).valMinAbs.natAbs := Int.natAbs_sum_le s _
    _ = ∑ i ∈ s, (f i).valMinAbs.natAbs := rfl

/-- Uniform bound on a finite sum of centered representatives: `card · β`. The shape most norm
arguments need (`Finset.sum_le_card_nsmul` at a constant bound). -/
theorem valMinAbs_natAbs_sum_le_card_mul {ι : Type*} (s : Finset ι) (f : ι → ZMod q) {β : ℕ}
    (hf : ∀ i ∈ s, (f i).valMinAbs.natAbs ≤ β) :
    (∑ i ∈ s, f i).valMinAbs.natAbs ≤ s.card * β :=
  le_trans (valMinAbs_natAbs_sum_le s f)
    (le_trans (Finset.sum_le_sum hf) (by rw [Finset.sum_const, smul_eq_mul]))

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

/-! ### Norm notation

Notation for the centered norms, with the modulus `Φ` left implicit (inferred from the
argument's type). `‖·‖₂²` is overloaded for both ring elements (`Rq.l2NormSq`) and vectors
(`vecL2NormSq`); elaboration disambiguates by the argument type. -/

/-- Centered `ℓ₁` norm `‖a‖₁` of a ring element (`Φ` inferred). -/
notation "‖" a "‖₁" => Rq.l1Norm _ a
/-- Centered squared-`ℓ₂` norm `‖a‖₂²` of a ring element (`Φ` inferred). -/
notation "‖" a "‖₂²" => Rq.l2NormSq _ a
/-- Centered squared-`ℓ₂` norm `‖z‖₂²` of a vector (`Φ` inferred). -/
notation "‖" z "‖₂²" => vecL2NormSq _ z

omit [NeZero q] [IsCyclotomic Φ] in
/-- Read a coefficient bound off an `ℓ∞` bound: every coefficient in the modulus' degree range has
centered absolute value at most the `ℓ∞` norm. The elimination counterpart of the `Finset.sup_le`
introductions used throughout this file. -/
theorem Rq.valMinAbs_natAbs_coeff_le_of_lInftyNorm_le {B : ℕ} {a : Rq Φ}
    (h : Rq.lInftyNorm Φ a ≤ B) {k : ℕ} (hk : k < Φ.φ.natDegree) :
    ((a.1.coeff k).valMinAbs).natAbs ≤ B :=
  le_trans (Finset.le_sup (f := fun k => ((a.1.coeff k).valMinAbs).natAbs)
    (Finset.mem_range.mpr hk)) h

omit [NeZero q] [IsCyclotomic Φ] in
/-- Read an entrywise `ℓ∞` bound off a vector `ℓ∞` bound. -/
theorem Rq.lInftyNorm_le_of_vecLInftyNorm_le {cols B : ℕ} {z : PolyVec (Rq Φ) cols}
    (h : vecLInftyNorm Φ z ≤ B) (i : Fin cols) : Rq.lInftyNorm Φ (z i) ≤ B :=
  le_trans (Finset.le_sup (f := fun i => Rq.lInftyNorm Φ (z i)) (Finset.mem_univ i)) h

omit [NeZero q] [IsCyclotomic Φ] in
/-- Coefficientwise form of a vector `ℓ∞` bound: every coefficient of every entry has centered
absolute value at most the bound. -/
theorem Rq.valMinAbs_natAbs_coeff_le_of_vecLInftyNorm_le {cols B : ℕ} {z : PolyVec (Rq Φ) cols}
    (h : vecLInftyNorm Φ z ≤ B) (i : Fin cols) {k : ℕ} (hk : k < Φ.φ.natDegree) :
    (((z i).1.coeff k).valMinAbs).natAbs ≤ B :=
  Rq.valMinAbs_natAbs_coeff_le_of_lInftyNorm_le Φ
    (Rq.lInftyNorm_le_of_vecLInftyNorm_le Φ h i) hk

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
theorem Rq.l1Norm_one (h : 1 ≤ Φ.φ.natDegree) : ‖(1 : Rq Φ)‖₁ = 1 := by
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
    ‖a - b‖₂² ≤ 2 * (‖a‖₂² + ‖b‖₂²) := by
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
    (hv : ‖v‖₂² ≤ boundSq) (hw : ‖w‖₂² ≤ boundSq) :
    ‖v - w‖₂² ≤ subL2NormSqBound boundSq := by
  have hstep : ‖v - w‖₂² ≤ 2 * (‖v‖₂² + ‖w‖₂²) := by
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

/-! ## `ℓ₁` triangle inequality for subtraction -/

/-- **`ℓ₁` subtraction triangle inequality** (ring element): `‖a - b‖₁ ≤ ‖a‖₁ + ‖b‖₁`. -/
theorem Rq.l1Norm_sub_le (a b : Rq Φ) : ‖a - b‖₁ ≤ ‖a‖₁ + ‖b‖₁ := by
  unfold Rq.l1Norm
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun k _ => ?_)
  have hcoeff : (a - b).1.coeff k = a.1.coeff k - b.1.coeff k := by
    rw [Rq.sub_val, CompPoly.CPolynomial.coeff_sub]
  rw [hcoeff]
  exact valMinAbs_sub_natAbs_le _ _

/-! ## `ℓ₁` positivity (the `hpos` bridge for `isUnit_of_l1Norm_le`) -/

omit [NeZero q] in
/-- A ring element with zero centered `ℓ₁` norm is `0`: every centered coefficient
representative below `deg φ` vanishes (`ZMod.valMinAbs_eq_zero`), and the representative is
reduced (degree `< deg φ`), so the underlying polynomial is `0`. -/
theorem Rq.eq_zero_of_l1Norm_eq_zero {x : Rq Φ} (h : ‖x‖₁ = 0) : x = 0 := by
  unfold Rq.l1Norm at h
  -- Each centered coefficient below `deg φ` is zero.
  have hlt : ∀ k, k < Φ.φ.natDegree → x.1.coeff k = 0 := by
    intro k hk
    have hz0 : (x.1.coeff k).valMinAbs.natAbs = 0 :=
      (Finset.sum_eq_zero_iff.mp h) k (Finset.mem_range.mpr hk)
    rw [← ZMod.valMinAbs_eq_zero, ← Int.natAbs_eq_zero]
    exact hz0
  -- Hence the underlying polynomial is `0` (coeffs below `deg φ` by the above, coeffs at or
  -- above `deg φ` by reducedness).
  have htoP : x.1.toPoly = 0 := by
    apply Polynomial.ext
    intro k
    rw [Polynomial.coeff_zero]
    by_cases hk : k < Φ.φ.natDegree
    · rw [← CompPoly.CPolynomial.coeff_toPoly]; exact hlt k hk
    · rw [not_lt] at hk
      have hdeg : x.1.toPoly.degree < Φ.φ.toPoly.degree := Φ.degree_toPoly_lt_of_reduced x.2
      have hφne : Φ.φ.toPoly ≠ 0 := (IsCyclotomic.monic (Φ := Φ)).ne_zero
      have hdegφ : Φ.φ.toPoly.degree = (Φ.φ.natDegree : WithBot ℕ) := by
        rw [Polynomial.degree_eq_natDegree hφne, CompPoly.CPolynomial.natDegree_toPoly]
      have hle' : Φ.φ.toPoly.degree ≤ (k : WithBot ℕ) := by
        rw [hdegφ]; exact_mod_cast hk
      exact Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hdeg hle')
  have hx1 : x.1 = 0 := (CompPoly.CPolynomial.toPoly_eq_zero_iff x.1).mp htoP
  exact Subtype.ext (by rw [Rq.zero_val]; exact hx1)

omit [NeZero q] in
/-- **`ℓ₁` positivity.** A nonzero ring element has positive centered `ℓ₁` norm — the `hpos`
input to `isUnit_of_l1Norm_le` for the extracted difference challenge `c̄ⱼ ≠ 0`. -/
theorem Rq.l1Norm_pos_of_ne_zero {x : Rq Φ} (hx : x ≠ 0) : 0 < ‖x‖₁ :=
  Nat.pos_of_ne_zero fun h0 => hx (Rq.eq_zero_of_l1Norm_eq_zero Φ h0)

/-! ## `ℓ∞ → ℓ₂²` aggregation bridge -/

omit [NeZero q] [IsCyclotomic Φ] in
/-- **`ℓ∞ → ℓ₂²` bridge** (ring element): `‖x‖₂² ≤ deg φ · ‖x‖∞²` — each of the `deg φ`
centered coefficients contributes at most `‖x‖∞²`. -/
theorem Rq.l2NormSq_le_natDegree_mul_lInftyNorm_sq (x : Rq Φ) :
    ‖x‖₂² ≤ Φ.φ.natDegree * (Rq.lInftyNorm Φ x) ^ 2 := by
  unfold Rq.l2NormSq
  calc ∑ k ∈ Finset.range Φ.φ.natDegree, (x.1.coeff k).valMinAbs.natAbs ^ 2
      ≤ ∑ _k ∈ Finset.range Φ.φ.natDegree, (Rq.lInftyNorm Φ x) ^ 2 :=
        Finset.sum_le_sum fun k hk =>
          Nat.pow_le_pow_left
            (Finset.le_sup (f := fun k => (x.1.coeff k).valMinAbs.natAbs) hk) 2
    _ = Φ.φ.natDegree * (Rq.lInftyNorm Φ x) ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

omit [NeZero q] [IsCyclotomic Φ] in
/-- **`ℓ∞ → ℓ₂²` bridge** (vector): `‖v‖₂² ≤ cols · (deg φ · ‖v‖∞²)`. -/
theorem vecL2NormSq_le_card_mul_lInftyNorm_sq {cols : ℕ} (v : PolyVec (Rq Φ) cols) :
    ‖v‖₂² ≤ cols * (Φ.φ.natDegree * (vecLInftyNorm Φ v) ^ 2) := by
  unfold vecL2NormSq
  calc ∑ i : Fin cols, Rq.l2NormSq Φ (v i)
      ≤ ∑ _i : Fin cols, Φ.φ.natDegree * (vecLInftyNorm Φ v) ^ 2 :=
        Finset.sum_le_sum fun i _ =>
          le_trans (Rq.l2NormSq_le_natDegree_mul_lInftyNorm_sq Φ (v i))
            (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
              (Finset.le_sup (f := fun i => Rq.lInftyNorm Φ (v i)) (Finset.mem_univ i)) 2))
    _ = cols * (Φ.φ.natDegree * (vecLInftyNorm Φ v) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

/-! ## The recomposition growth bound -/

/-- Squared-`ℓ₂` bound for a base-`b` gadget **recomposition** `z = J·ẑ` of an
`ℓ∞`-range-checked decomposed vector (`‖ẑ‖∞ ≤ γ`): each of the `cols` entries of `z` is a
`τ`-digit base-`b` weighted sum, so its centered coefficients are at most `(∑_{u<τ} bᵘ)·γ`,
and squaring/summing over `d = deg φ` coefficients and `cols` entries gives
`cols · (d · ((∑_{u<τ} bᵘ)·γ)²)`. -/
def zRecomposeL2SqBound (γ b τ d cols : ℕ) : ℕ :=
  cols * (d * ((∑ u ∈ Finset.range τ, b ^ u) * γ) ^ 2)

end ArkLib.Lattices.CyclotomicModulus
