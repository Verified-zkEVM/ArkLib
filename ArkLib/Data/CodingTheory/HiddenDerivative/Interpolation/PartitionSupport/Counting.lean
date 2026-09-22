/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.PartitionSupport.Basic

/-!
# The dimension of the partition support space

Write an exponent on `X, Y₀, ..., Y_d` as `(x, b₀, c)`, where `x` is the exponent of `X`, `b₀` that
of `Y₀`, and `c : Fin d → ℕ` holds the exponents of `Y₁, ..., Y_d` (coordinate `i` is the exponent
of `Y_(i+1)`). The derivative-order weight is `∑_i (i + 1) c_i` and the total jet degree is
`b₀ + ∑_i c_i`, so for a natural cutoff `L` the partition-support conditions read

```text
∑_i (i + 1) c_i ≤ W,
x + D (b₀ + ∑_i c_i) < L.
```

The first condition says that `c` lies in the lattice simplex
`Finset.natWeightedSimplex (fun i ↦ i + 1) W`. Given `c` and `b₀`, there are
`L - D (b₀ + ∑_i c_i)` choices of `x` (natural subtraction). For `0 < D` every eligible exponent
has `b₀ < L`, so the number of eligible exponents, which is the dimension of the partition support
space, is exactly

```text
partitionSourceCount D d W L = ∑_{c} ∑_{b₀ < L} (L - D (b₀ + ∑_i c_i)).
```

No hypothesis on `d` is needed; for `d = 0` the only tuple is empty. A real cutoff `L'` gives the
same space as the natural cutoff `⌈L'⌉₊`, since `n < L' ↔ n < ⌈L'⌉₊` for natural `n`.

## Main statements

* `partitionSourceExponent`: the exponent with coordinates `(x, b₀, c)`, with
  `partitionSourceExponent_eta`, `fullDerivativeJetWeight_eq_sum_succ` and
  `totalJetDegree_eq_zero_add_sum_succ`.
* `partitionSupportEligible_partitionSourceExponent_iff`: eligibility in coordinates.
* `partitionSourceCount`, `card_partitionSupportExponents` and
  `finrank_partitionSupportSpace_eq_partitionSourceCount`: the exact dimension.
* `finrank_partitionSupportSpace_eq_partitionSourceCount_natCeil`: the exact dimension at a real
  cutoff `L`, which is the count at `⌈L⌉₊`.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient Decoding
  and Smaller Cryptographic Proofs*][DKT26], Section 6.1, (70)–(71)
-/

@[expose] public section

open PolynomialDifferential Finset

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {d D W : ℕ}

/-! ### Coordinates -/

/-- The exponent `X^x Y₀^b₀ Y₁^(c₀) ⋯ Y_d^(c_(d-1))`: coordinate `i` of `c` is the exponent of
`Y_(i+1)`. -/
def partitionSourceExponent (x b₀ : ℕ) (c : Fin d → ℕ) : JetVariable d →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm fun
    | none => x
    | some j => Fin.cases b₀ c j

/-- The exponent of `X` is `x`. -/
@[simp]
theorem partitionSourceExponent_none (x b₀ : ℕ) (c : Fin d → ℕ) :
    partitionSourceExponent x b₀ c none = x := rfl

/-- The exponent of `Y₀` is `b₀`. -/
@[simp]
theorem partitionSourceExponent_zero (x b₀ : ℕ) (c : Fin d → ℕ) :
    partitionSourceExponent x b₀ c (some 0) = b₀ := rfl

/-- The exponent of `Y_(i+1)` is `c i`. -/
@[simp]
theorem partitionSourceExponent_succ (x b₀ : ℕ) (c : Fin d → ℕ) (i : Fin d) :
    partitionSourceExponent x b₀ c (some i.succ) = c i := rfl

/-- Every exponent is the exponent of its own coordinates. -/
theorem partitionSourceExponent_eta (u : JetVariable d →₀ ℕ) :
    partitionSourceExponent (u none) (u (some 0)) (fun i => u (some i.succ)) = u := by
  ext v
  rcases v with _ | j
  · rfl
  · induction j using Fin.cases <;> rfl

/-- The derivative-order weight is `∑_i (i + 1) u(Y_(i+1))`; `Y₀` has weight zero. -/
theorem fullDerivativeJetWeight_eq_sum_succ (u : JetVariable d →₀ ℕ) :
    fullDerivativeJetWeight u = ∑ i : Fin d, (i.val + 1) * u (some i.succ) := by
  simp only [fullDerivativeJetWeight, Finsupp.weight_apply, Finsupp.sum_fintype, smul_eq_mul,
    Fintype.sum_option, jetDerivativeWeight, zero_mul, implies_true]
  rw [Fin.sum_univ_succ]
  simp [mul_comm]

/-- The total jet degree is the exponent of `Y₀` plus `∑_i u(Y_(i+1))`. -/
theorem totalJetDegree_eq_zero_add_sum_succ (u : JetVariable d →₀ ℕ) :
    totalJetDegree u = u (some 0) + ∑ i : Fin d, u (some i.succ) := by
  rw [totalJetDegree_eq_sum, Fin.sum_univ_succ]

/-- Partition-support eligibility of the exponent with coordinates `(x, b₀, c)`: the
derivative-order weight `∑_i (i + 1) c_i` is at most `W` and the coarse weight
`x + D (b₀ + ∑_i c_i)` is below `L`. -/
theorem partitionSupportEligible_partitionSourceExponent_iff {L : ℝ} (x b₀ : ℕ)
    (c : Fin d → ℕ) :
    PartitionSupportEligible D d W L (partitionSourceExponent x b₀ c) ↔
      ∑ i : Fin d, (i.val + 1) * c i ≤ W ∧ ((x + D * (b₀ + ∑ i, c i) : ℕ) : ℝ) < L := by
  rw [PartitionSupportEligible, fullDerivativeJetWeight_eq_sum_succ,
    totalJetDegree_eq_zero_add_sum_succ]
  simp

/-! ### The exact count -/

/-- The number of partition-support eligible exponents at the natural cutoff `L`: for each tuple
`c` of derivative-order weight at most `W` and each `b₀ < L`, there are
`L - D (b₀ + ∑_i c_i)` exponents `x` of `X` (natural subtraction). -/
def partitionSourceCount (D d W L : ℕ) : ℕ :=
  ∑ c ∈ natWeightedSimplex (fun i : Fin d => i.val + 1) W,
    ∑ b₀ ∈ range L, (L - D * (b₀ + ∑ i, c i))

/-- For `0 < D`, the number of partition-support eligible exponents at the natural cutoff `L` is
exactly `partitionSourceCount D d W L`. The hypothesis `0 < D` is used twice: it makes the set
finite, and it gives `b₀ ≤ D * b₀ < L`, so that the range `b₀ < L` in the count omits no exponent.
-/
theorem card_partitionSupportExponents (hD : 0 < D) (L : ℕ) :
    #(partitionSupportExponents D d W (L : ℝ) hD) = partitionSourceCount D d W L := by
  have hw : ∀ i : Fin d, i.val + 1 ≠ 0 := fun i => Nat.succ_ne_zero _
  let s := (natWeightedSimplex (fun i : Fin d => i.val + 1) W).sigma fun c =>
    (range L).sigma fun b₀ => range (L - D * (b₀ + ∑ i, c i))
  have hs : #s = partitionSourceCount D d W L := by
    simp only [s, card_sigma, card_range, partitionSourceCount]
  rw [← hs]
  symm
  refine card_nbij' (fun p => partitionSourceExponent p.2.2 p.2.1 p.1)
    (fun u => ⟨fun i : Fin d => u (some i.succ), u (some 0), u none⟩) ?_ ?_ ?_ ?_
  · rintro ⟨c, b₀, x⟩ hp
    simp only [s, coe_sigma, Set.mem_sigma_iff, mem_coe, mem_range,
      mem_natWeightedSimplex hw] at hp
    rw [mem_coe, mem_partitionSupportExponents,
      partitionSupportEligible_partitionSourceExponent_iff]
    exact ⟨hp.1, by exact_mod_cast (by omega : x + D * (b₀ + ∑ i, c i) < L)⟩
  · intro u hu
    have hu' := mem_partitionSupportExponents.mp (mem_coe.mp hu)
    rw [← partitionSourceExponent_eta u, partitionSupportEligible_partitionSourceExponent_iff]
      at hu'
    obtain ⟨hweight, hcost⟩ := hu'
    have hcost' : u none + D * (u (some 0) + ∑ i : Fin d, u (some i.succ)) < L := by
      exact_mod_cast hcost
    have hb₀ : u (some 0) ≤ D * (u (some 0) + ∑ i : Fin d, u (some i.succ)) :=
      (Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_left _ hD)
    simp only [s, coe_sigma, Set.mem_sigma_iff, mem_coe, mem_range, mem_natWeightedSimplex hw]
    exact ⟨hweight, by omega, by omega⟩
  · rintro ⟨c, b₀, x⟩ -
    rfl
  · intro u _
    exact partitionSourceExponent_eta u

/-- For `0 < D`, the dimension of the partition support space at the natural cutoff `L` over a
field is exactly `partitionSourceCount D d W L`. -/
theorem finrank_partitionSupportSpace_eq_partitionSourceCount (F : Type*) [Field F] (hD : 0 < D)
    (L : ℕ) :
    Module.finrank F (partitionSupportSpace F D d W (L : ℝ) hD) = partitionSourceCount D d W L := by
  rw [finrank_partitionSupportSpace_eq_card, card_partitionSupportExponents]

/-- For `0 < D`, the dimension of the partition support space at the real cutoff `L` over a field
is `partitionSourceCount D d W ⌈L⌉₊`. For `L ≤ 0` both sides are zero. -/
theorem finrank_partitionSupportSpace_eq_partitionSourceCount_natCeil (F : Type*) [Field F]
    (hD : 0 < D) (L : ℝ) :
    Module.finrank F (partitionSupportSpace F D d W L hD) = partitionSourceCount D d W ⌈L⌉₊ := by
  rw [← partitionSupportSpace_natCeil, finrank_partitionSupportSpace_eq_partitionSourceCount]

end ReedSolomon.HiddenDerivative
