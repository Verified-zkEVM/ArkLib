/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Counting
public import ArkLib.ToMathlib.MeasureTheory.Integral.PositivePart
public import ArkLib.ToMathlib.Combinatorics.QuadraticStaircase

/-!
# A quadratic lower bound on the dimension of the partition support space

Fix a tuple `c` of exponents of `Y₁, ..., Y_d` of derivative-order weight at most `W`. The
remaining exponents `(x, b₀)` of `X` and `Y₀` satisfy `x + D (b₀ + ∑_i c_i) < L`, and for
`0 < D` their number is the real-cutoff staircase count
`QuadraticStaircase.count D (L / D - ∑_i c_i)`
(`QuadraticStaircase.count_div_sub_eq_sum`). Hence the dimension of the partition support space at
the natural cutoff `L` is exactly

```text
∑_{c} QuadraticStaircase.count D (L / D - ∑_i c_i)
  ≥ ∑_{c} D (max (L / D - ∑_i c_i) 0) ^ 2 / 2,
```

with no tuple discarded near the boundary. For a code of length `n` and an upper rate bound
`D ≤ rate * n`, a level with `level * n ≤ L` gives the rate form
`n / (2 rate) * ∑_c (max (level - rate ∑_i c_i) 0) ^ 2 ≤ dim`.

Both bounds hold at a real cutoff `L`: the space at `L` is the space at `⌈L⌉₊`
(`partitionSupportSpace_natCeil`), and each term of the lower bound increases with the cutoff.

## Main statements

* `finrank_partitionSupportSpace_eq_sum_count`: the dimension as a sum of staircase counts.
* `partitionSupport_dimension_ge_quadratic_sum`: the positive-part square lower bound.
* `partition_quadratic_rate_lower`: the comparison of one term with its rate form.
* `partitionSupport_dimension_ge_rate_sum`: the rate form of the lower bound.
* `partitionSupport_dimension_ge_quadratic_sum_real` and
  `partitionSupport_dimension_ge_rate_sum_real`: both bounds at a real cutoff.
* `PartitionSupportAreaSlot` and `partitionSupportAreaSlotExponent`: encode staircase slots as
  distinct eligible exponents of the partition support.

## References

* [DKT26]
-/

@[expose] public section

open PolynomialDifferential Finset

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {d D W : ℕ}

/-- For `0 < D`, the dimension of the partition support space at the natural cutoff `L` is the sum,
over the tuples `c` of derivative-order weight at most `W`, of the staircase counts
`QuadraticStaircase.count D (L / D - ∑_i c_i)` of the pairs `(x, b₀)` with
`x + D (b₀ + ∑_i c_i) < L`. -/
theorem finrank_partitionSupportSpace_eq_sum_count (F : Type*) [Field F] (hD : 0 < D) (L : ℕ) :
    Module.finrank F (partitionSupportSpace F D d W (L : ℝ) hD) =
      ∑ c ∈ natWeightedSimplex (fun i : Fin d => i.val + 1) W,
        QuadraticStaircase.count D ((L : ℝ) / D - ((∑ i, c i : ℕ) : ℝ)) := by
  rw [finrank_partitionSupportSpace_eq_partitionSourceCount, partitionSourceCount]
  exact sum_congr rfl fun c _ => (QuadraticStaircase.count_div_sub_eq_sum hD L _).symm

/-- The quadratic lower bound on the dimension of the partition support space: for `0 < D`, the
sum over the tuples `c` of derivative-order weight at most `W` of
`D * (max (L / D - ∑_i c_i) 0) ^ 2 / 2` is at most the dimension at the natural cutoff `L`. Each
term bounds one staircase count from below (`QuadraticStaircase.count_ge_quadratic`); tuples with
`L / D ≤ ∑_i c_i` contribute zero. -/
theorem partitionSupport_dimension_ge_quadratic_sum (F : Type*) [Field F] (hD : 0 < D) (L : ℕ) :
    ∑ c ∈ natWeightedSimplex (fun i : Fin d => i.val + 1) W,
        (D : ℝ) * (max ((L : ℝ) / D - ((∑ i, c i : ℕ) : ℝ)) 0) ^ 2 / 2 ≤
      (Module.finrank F (partitionSupportSpace F D d W (L : ℝ) hD) : ℝ) := by
  rw [finrank_partitionSupportSpace_eq_sum_count, Nat.cast_sum]
  exact sum_le_sum fun c _ => QuadraticStaircase.count_ge_quadratic _ _

/-- A derivative-order tuple and a staircase slot for the exponents of `X` and `Y₀` at cutoff
`L`. -/
abbrev PartitionSupportAreaSlot (D d W : ℕ) (L : ℝ) :=
  Σ c : ↥(natWeightedSimplex (fun i : Fin d => i.val + 1) W),
    QuadraticStaircase.Slot D (L / D - ((∑ i, c.val i : ℕ) : ℝ))

/-- Interpret an area slot as the exponent of a monomial in the partition support. -/
def partitionSupportAreaSlotExponent {D d W : ℕ} {L : ℝ}
    (p : PartitionSupportAreaSlot D d W L) : JetVariable d →₀ ℕ :=
  partitionSourceExponent p.2.exponents.1 p.2.exponents.2 p.1.val

/-- Every area slot gives an exponent eligible for the partition support at cutoff `L`. -/
theorem partitionSupportAreaSlotExponent_eligible {D d W : ℕ} {L : ℝ}
    (hD : 0 < D) (p : PartitionSupportAreaSlot D d W L) :
    PartitionSupportEligible D d W L (partitionSupportAreaSlotExponent p) := by
  have hD0 : (D : ℝ) ≠ 0 := by positivity
  have hcancel : (D : ℝ) * (L / D - ((∑ i, p.1.val i : ℕ) : ℝ)) =
      L - D * ((∑ i, p.1.val i : ℕ) : ℝ) := by field_simp
  have hslot := QuadraticStaircase.Slot.weighted_degree_lt p.2
  rw [hcancel] at hslot
  change PartitionSupportEligible D d W L
    (partitionSourceExponent p.2.exponents.1 p.2.exponents.2 p.1.val)
  rw [partitionSupportEligible_partitionSourceExponent_iff]
  constructor
  · exact (mem_natWeightedSimplex (fun i : Fin d => Nat.succ_ne_zero i.val)).mp p.1.2
  · push_cast at hslot ⊢
    nlinarith

/-- Distinct area slots give distinct partition-support exponents. -/
theorem partitionSupportAreaSlotExponent_injective {D d W : ℕ} {L : ℝ} :
    Function.Injective (partitionSupportAreaSlotExponent (D := D) (d := d) (W := W) (L := L)) := by
  rintro ⟨c, p⟩ ⟨b, q⟩ h
  have hc : c = b := by
    apply Subtype.ext
    funext i
    exact congrArg (fun e => e (some i.succ)) h
  subst b
  apply congrArg (Sigma.mk c)
  apply QuadraticStaircase.Slot.exponents_injective
  exact Prod.ext (congrArg (fun e => e none) h) (congrArg (fun e => e (some 0)) h)

/-- One term of the quadratic lower bound in rate form. If `0 < D ≤ rate * n` and
`level * n ≤ L`, then for every natural `deg`,
`n / (2 rate) * (max (level - rate * deg) 0) ^ 2 ≤ D * (max (L / D - deg) 0) ^ 2 / 2`.
Multiplying `level - rate * deg` by `n` gives at most `L - D * deg`, and `2 D ≤ 2 rate n`. The
hypothesis `D ≤ rate * n` may be strict: the ambient dimension `D` can be smaller than `rate * n`.
It also forces `0 < rate` and `0 < n`, so neither is assumed. -/
theorem partition_quadratic_rate_lower {n L deg : ℕ} {rate level : ℝ} (hD : 0 < D)
    (hupper : (D : ℝ) ≤ rate * n) (hlevel : level * n ≤ L) :
    (n : ℝ) / (2 * rate) * (max (level - rate * deg) 0) ^ 2 ≤
      (D : ℝ) * (max ((L : ℝ) / D - deg) 0) ^ 2 / 2 := by
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hnR : (0 : ℝ) < n := by
    by_contra hn
    have hn0 : (n : ℝ) = 0 := le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg n)
    rw [hn0, mul_zero] at hupper
    linarith
  calc
    (n : ℝ) / (2 * rate) * (max (level - rate * deg) 0) ^ 2 ≤
        (D : ℝ) / 2 * (max ((L : ℝ) / D - deg) 0) ^ 2 :=
      max_sub_zero_sq_scaled_le hDR hnR (Nat.cast_nonneg deg) hupper
        (by simpa [mul_comm] using hlevel)
    _ = (D : ℝ) * (max ((L : ℝ) / D - deg) 0) ^ 2 / 2 := by ring

/-- The rate form of the quadratic lower bound: if `0 < D ≤ rate * n` and `level * n ≤ L`, then
`n / (2 rate) * ∑_c (max (level - rate * ∑_i c_i) 0) ^ 2` is at most the dimension of the
partition support space at the natural cutoff `L`, the sum running over the tuples `c` of
derivative-order weight at most `W`. -/
theorem partitionSupport_dimension_ge_rate_sum (F : Type*) [Field F] {n L : ℕ} {rate level : ℝ}
    (hD : 0 < D) (hupper : (D : ℝ) ≤ rate * n) (hlevel : level * n ≤ L) :
    (n : ℝ) / (2 * rate) *
        ∑ c ∈ natWeightedSimplex (fun i : Fin d => i.val + 1) W,
          (max (level - rate * ((∑ i, c i : ℕ) : ℝ)) 0) ^ 2 ≤
      (Module.finrank F (partitionSupportSpace F D d W (L : ℝ) hD) : ℝ) := by
  rw [mul_sum]
  exact (sum_le_sum fun c _ => partition_quadratic_rate_lower hD hupper hlevel).trans
    (partitionSupport_dimension_ge_quadratic_sum F hD L)

/-! ### Real cutoffs -/

/-- The quadratic lower bound on the dimension of the partition support space at a real cutoff
`L`: for `0 < D`, the sum over the tuples `c` of derivative-order weight at most `W` of
`D * (max (L / D - ∑_i c_i) 0) ^ 2 / 2` is at most the dimension. It follows from the
natural-cutoff bound `partitionSupport_dimension_ge_quadratic_sum` at `⌈L⌉₊`, since
`L ≤ ⌈L⌉₊` and both cutoffs give the same space. -/
theorem partitionSupport_dimension_ge_quadratic_sum_real (F : Type*) [Field F] (hD : 0 < D)
    (L : ℝ) :
    ∑ c ∈ natWeightedSimplex (fun i : Fin d => i.val + 1) W,
        (D : ℝ) * (max (L / D - ((∑ i, c i : ℕ) : ℝ)) 0) ^ 2 / 2 ≤
      (Module.finrank F (partitionSupportSpace F D d W L hD) : ℝ) := by
  rw [← partitionSupportSpace_natCeil]
  refine (sum_le_sum fun c _ => ?_).trans
    (partitionSupport_dimension_ge_quadratic_sum F hD ⌈L⌉₊)
  gcongr
  exact Nat.le_ceil L

/-- The rate form of the quadratic lower bound at a real cutoff: if `0 < D ≤ rate * n` and
`level * n ≤ L`, then `n / (2 rate) * ∑_c (max (level - rate * ∑_i c_i) 0) ^ 2` is at most the
dimension of the partition support space at `L`, the sum running over the tuples `c` of
derivative-order weight at most `W`. The hypothesis `D ≤ rate * n` forces `0 < rate` and `0 < n`,
so neither is assumed. -/
theorem partitionSupport_dimension_ge_rate_sum_real (F : Type*) [Field F] {n : ℕ}
    {rate level L : ℝ} (hD : 0 < D) (hupper : (D : ℝ) ≤ rate * n) (hlevel : level * n ≤ L) :
    (n : ℝ) / (2 * rate) *
        ∑ c ∈ natWeightedSimplex (fun i : Fin d => i.val + 1) W,
          (max (level - rate * ((∑ i, c i : ℕ) : ℝ)) 0) ^ 2 ≤
      (Module.finrank F (partitionSupportSpace F D d W L hD) : ℝ) := by
  rw [← partitionSupportSpace_natCeil]
  exact partitionSupport_dimension_ge_rate_sum F hD hupper (hlevel.trans (Nat.le_ceil L))

end ReedSolomon.HiddenDerivative
