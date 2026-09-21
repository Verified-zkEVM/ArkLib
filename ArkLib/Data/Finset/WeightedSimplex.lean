/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Pratyush Mishra, Quang Dao
-/
module

public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Counting weighted discrete simplices

`natWeightedSimplex w W` enumerates nonnegative integer vectors whose weighted sum is at most
`W`. A finite coordinate box makes this an executable finset even when a weight is zero. For
positive weights, quotient and remainder in each coordinate compare its cardinality with an
ordinary simplex. Stars and bars and factorial bounds then give a two-sided integer estimate and
an ordered-field upper bound.

The empty index type has one vector, including when `W = 0`. A zero weight does not constrain its
coordinate, so the finite box matters and the lower estimate requires positive weights.

## References

Generalizes `ordinaryToExact`, `ordinarySimplexEquivSym`, and `card_ordinarySimplex` from
`ToMathlib/Combinatorics/DiscreteSimplex/Basic.lean`, and `ordinaryToScaledWithResidue`,
`scaledWithResidueToOrdinary`, and `scaledExponentCount_factorial_sq_sandwich` from
`HiddenDerivative/Parameters/Lattice/ScaledLattice.lean`, all at ArkLib revision
`a5aa2677fee4e3a79d6bb05136631cce4a08587d`. The source adapts `kz99/rs-ld-mca`
revision `9699ee7a6143f6efe1d8cfed84998a4f8c79c40f` with permission.
`weightedHigherJetTuples` and `ratePartitionTupleCount_le_volume` motivate the finite set and
ordered-field bound. Public exact-simplex equivalences, shell counts, the `Finsupp` count bridge,
continuous volumes, floor cells, and moments are deferred.
-/

@[expose] public section

namespace Finset

open scoped BigOperators

/-- The finite box of nonnegative vectors of weighted sum at most `W`. A zero-weight coordinate
still ranges from `0` to `W`; at an empty index type there is exactly one vector. -/
def natWeightedSimplex {σ : Type*} [Fintype σ] [DecidableEq σ]
    (w : σ → ℕ) (W : ℕ) : Finset (σ → ℕ) :=
  (Fintype.piFinset fun _ ↦ range (W + 1)).filter fun c ↦ ∑ i, w i * c i ≤ W

/-- Membership always implies the weighted budget, including with zero weights and `W = 0`. -/
theorem weightedSum_le_of_mem_natWeightedSimplex {σ : Type*} [Fintype σ] [DecidableEq σ]
    {w : σ → ℕ} {W : ℕ} {c : σ → ℕ} (hc : c ∈ natWeightedSimplex w W) :
    ∑ i, w i * c i ≤ W :=
  (mem_filter.mp hc).2

/-- With every weight positive, the weighted budget itself enforces the finite coordinate box.
For a zero weight this equivalence fails when that coordinate exceeds `W`. -/
theorem mem_natWeightedSimplex {σ : Type*} [Fintype σ] [DecidableEq σ]
    {w : σ → ℕ} (hw : ∀ i, w i ≠ 0) {W : ℕ} {c : σ → ℕ} :
    c ∈ natWeightedSimplex w W ↔ ∑ i, w i * c i ≤ W := by
  refine ⟨weightedSum_le_of_mem_natWeightedSimplex, fun hc ↦ mem_filter.mpr ⟨?_, hc⟩⟩
  rw [Fintype.mem_piFinset]
  intro i
  rw [mem_range]
  have hterm : w i * c i ≤ ∑ j, w j * c j :=
    single_le_sum (f := fun j ↦ w j * c j) (fun j _ ↦ Nat.zero_le _) (mem_univ i)
  have hcoord : c i ≤ w i * c i := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero (hw i))
  omega

private def ordinarySimplex (σ : Type*) [Fintype σ] (W : ℕ) :=
  {c : σ → ℕ // ∑ i, c i ≤ W}

private def exactSimplex (σ : Type*) [Fintype σ] (W : ℕ) :=
  {c : Option σ → ℕ // ∑ i, c i = W}

private def ordinaryToExact {σ : Type*} [Fintype σ] (W : ℕ)
    (c : ordinarySimplex σ W) : exactSimplex σ W :=
  ⟨fun i ↦ i.elim (W - ∑ j, c.1 j) c.1, by
    rw [Fintype.sum_option]
    simp only [Option.elim_none, Option.elim_some]
    exact Nat.sub_add_cancel c.2⟩

private def exactToOrdinary {σ : Type*} [Fintype σ] (W : ℕ)
    (c : exactSimplex σ W) : ordinarySimplex σ W :=
  ⟨fun i ↦ c.1 (some i), by
    have hc := c.2
    rw [Fintype.sum_option] at hc
    change c.1 none + (∑ i, c.1 (some i)) = W at hc
    change (∑ i, c.1 (some i)) ≤ W
    omega⟩

private noncomputable def ordinaryEquivSym {σ : Type*} [Fintype σ] (W : ℕ) :
    ordinarySimplex σ W ≃ Sym (Option σ) W := by
  classical
  exact (Equiv.trans {
    toFun := ordinaryToExact W
    invFun := exactToOrdinary W
    left_inv := fun c ↦ by
      apply Subtype.ext
      funext i
      rfl
    right_inv := fun c ↦ by
      apply Subtype.ext
      funext i
      cases i with
      | none =>
          have hc := c.2
          rw [Fintype.sum_option] at hc
          change W - (∑ j, c.1 (some j)) = c.1 none
          omega
      | some i => rfl
  } (Sym.equivNatSumOfFintype _ _).symm)

private noncomputable instance ordinarySimplexFintype {σ : Type*} [Fintype σ] (W : ℕ) :
    Fintype (ordinarySimplex σ W) := by
  classical
  exact Fintype.ofEquiv (Sym (Option σ) W) (ordinaryEquivSym W).symm

private theorem card_ordinarySimplex {σ : Type*} [Fintype σ] (W : ℕ) :
    Fintype.card (ordinarySimplex σ W) =
      (W + Fintype.card σ).choose (Fintype.card σ) := by
  classical
  rw [Fintype.card_congr (ordinaryEquivSym W), Sym.card_sym_eq_choose,
    Fintype.card_option]
  have hbase : Fintype.card σ + 1 + W - 1 = W + Fintype.card σ := by omega
  rw [hbase]
  exact Nat.choose_symm_add

private theorem card_natWeightedSimplex_one_aux {σ : Type*} [Fintype σ] [DecidableEq σ]
    (W : ℕ) :
    (natWeightedSimplex (fun _ : σ ↦ 1) W).card =
      Fintype.card (ordinarySimplex σ W) := by
  rw [← Fintype.card_coe]
  apply Fintype.card_congr
  exact {
    toFun := fun c ↦ ⟨c.1, by
      simpa only [one_mul] using
        (weightedSum_le_of_mem_natWeightedSimplex c.2)⟩
    invFun := fun c ↦ ⟨c.1, by
      exact (mem_natWeightedSimplex (fun _ ↦ one_ne_zero)).mpr
        (by simpa only [one_mul] using c.2)⟩
    left_inv := fun _ ↦ rfl
    right_inv := fun _ ↦ rfl }

/-- Bounded stars and bars: with unit weights, the box counts precisely the tuples of total
degree at most `W`. At an empty index type this equals one, also for `W = 0`. -/
theorem card_natWeightedSimplex_one {σ : Type*} [Fintype σ] [DecidableEq σ]
    (W : ℕ) :
    (natWeightedSimplex (fun _ : σ ↦ 1) W).card =
      (W + Fintype.card σ).choose (Fintype.card σ) := by
  rw [card_natWeightedSimplex_one_aux, card_ordinarySimplex]

private abbrev weightedResidue {σ : Type*} (w : σ → ℕ) :=
  (i : σ) → Fin (w i)

private theorem card_weightedResidue {σ : Type*} [Fintype σ] [DecidableEq σ] (w : σ → ℕ) :
    Fintype.card (weightedResidue w) = ∏ i, w i := by
  classical
  rw [Fintype.card_pi]
  simp

private def ordinaryToWeightedWithResidue {σ : Type*} [Fintype σ] [DecidableEq σ]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (W : ℕ) (a : ordinarySimplex σ W) :
    ↥(natWeightedSimplex w W) × weightedResidue w :=
  ⟨⟨fun i ↦ a.1 i / w i, (mem_natWeightedSimplex hw).mpr <| by
      calc
        (∑ i, w i * (a.1 i / w i)) ≤ ∑ i, a.1 i :=
          sum_le_sum fun i _ ↦ by simpa [Nat.mul_comm] using Nat.mul_div_le (a.1 i) (w i)
        _ ≤ W := a.2⟩,
    fun i ↦ ⟨a.1 i % w i, Nat.mod_lt _ (Nat.pos_of_ne_zero (hw i))⟩⟩

private theorem ordinaryToWeightedWithResidue_injective {σ : Type*} [Fintype σ]
    [DecidableEq σ] (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (W : ℕ) :
    Function.Injective (ordinaryToWeightedWithResidue w hw W) := by
  intro a b hab
  apply Subtype.ext
  funext i
  have hdiv : a.1 i / w i = b.1 i / w i :=
    congrArg (fun p ↦ p.1.1 i) hab
  have hmod : a.1 i % w i = b.1 i % w i :=
    congrArg (fun p ↦ (p.2 i).val) hab
  calc
    a.1 i = a.1 i % w i + w i * (a.1 i / w i) := (Nat.mod_add_div _ _).symm
    _ = b.1 i % w i + w i * (b.1 i / w i) := by rw [hdiv, hmod]
    _ = b.1 i := Nat.mod_add_div _ _

private def weightedWithResidueToOrdinary {σ : Type*} [Fintype σ] [DecidableEq σ]
    (w : σ → ℕ) (W : ℕ) (p : ↥(natWeightedSimplex w W) × weightedResidue w) :
    ordinarySimplex σ (W + ∑ i, (w i - 1)) :=
  ⟨fun i ↦ w i * p.1.1 i + (p.2 i).val, by
    change (∑ i, (w i * p.1.1 i + (p.2 i).val)) ≤ _
    rw [sum_add_distrib]
    apply Nat.add_le_add
    · exact weightedSum_le_of_mem_natWeightedSimplex p.1.2
    · exact sum_le_sum fun i _ ↦ Nat.le_sub_one_of_lt (p.2 i).2⟩

private theorem weightedWithResidueToOrdinary_injective {σ : Type*} [Fintype σ]
    [DecidableEq σ] (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (W : ℕ) :
    Function.Injective (weightedWithResidueToOrdinary w W) := by
  rintro ⟨c, r⟩ ⟨c', r'⟩ h
  have hfun : (weightedWithResidueToOrdinary w W (c, r)).1 =
      (weightedWithResidueToOrdinary w W (c', r')).1 := congrArg Subtype.val h
  apply Prod.ext
  · apply Subtype.ext
    funext i
    have hi := congrFun hfun i
    have hp : (c.1 i, r i) = (c'.1 i, r' i) := by
      apply (@Nat.divModEquiv (w i) ⟨hw i⟩).symm.injective
      simpa [weightedWithResidueToOrdinary, Nat.divModEquiv_symm_apply, Nat.mul_comm]
        using hi
    exact congrArg Prod.fst hp
  · funext i
    have hi := congrFun hfun i
    have hp : (c.1 i, r i) = (c'.1 i, r' i) := by
      apply (@Nat.divModEquiv (w i) ⟨hw i⟩).symm.injective
      simpa [weightedWithResidueToOrdinary, Nat.divModEquiv_symm_apply, Nat.mul_comm]
        using hi
    exact congrArg Prod.snd hp

private theorem card_ordinary_le_weighted_mul {σ : Type*} [Fintype σ] [DecidableEq σ]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (W : ℕ) :
    Fintype.card (ordinarySimplex σ W) ≤
      (natWeightedSimplex w W).card * ∏ i, w i := by
  calc
    Fintype.card (ordinarySimplex σ W) ≤
        Fintype.card (↥(natWeightedSimplex w W) × weightedResidue w) :=
      Fintype.card_le_of_injective _ (ordinaryToWeightedWithResidue_injective w hw W)
    _ = (natWeightedSimplex w W).card * ∏ i, w i := by
      rw [Fintype.card_prod, card_weightedResidue]
      simp only [Fintype.card_coe]

private theorem weighted_mul_le_card_ordinary {σ : Type*} [Fintype σ] [DecidableEq σ]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (W : ℕ) :
    (natWeightedSimplex w W).card * ∏ i, w i ≤
      Fintype.card (ordinarySimplex σ (W + ∑ i, (w i - 1))) := by
  calc
    (natWeightedSimplex w W).card * ∏ i, w i =
        Fintype.card (↥(natWeightedSimplex w W) × weightedResidue w) := by
      rw [Fintype.card_prod, card_weightedResidue]
      simp only [Fintype.card_coe]
    _ ≤ Fintype.card (ordinarySimplex σ (W + ∑ i, (w i - 1))) :=
      Fintype.card_le_of_injective _ (weightedWithResidueToOrdinary_injective w hw W)

/-- The positive-weight simplex has at least `(W+n).choose n / ∏ w_i` points, in the
integer-multiplied form. At an empty index type both sides are one, including when `W = 0`. -/
theorem choose_le_card_natWeightedSimplex_mul_prod
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (W : ℕ) :
    (W + Fintype.card σ).choose (Fintype.card σ) ≤
      (natWeightedSimplex w W).card * ∏ i, w i := by
  simpa only [card_ordinarySimplex] using card_ordinary_le_weighted_mul w hw W

private theorem sum_weight_sub_one_add_card {σ : Type*} [Fintype σ]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) :
    (∑ i, (w i - 1)) + Fintype.card σ = ∑ i, w i := by
  calc
    (∑ i, (w i - 1)) + Fintype.card σ =
        ∑ i, ((w i - 1) + 1) := by simp [sum_add_distrib]
    _ = ∑ i, w i := by
      apply sum_congr rfl
      intro i _
      exact Nat.sub_add_cancel (Nat.pos_of_ne_zero (hw i))

/-- The reverse residue injection gives a sharper binomial upper count, including when `W = 0`.
With a zero weight its left side is zero; with no indices it reads `1 ≤ 1`. -/
theorem card_natWeightedSimplex_mul_prod_le_choose
    {σ : Type*} [Fintype σ] [DecidableEq σ] (w : σ → ℕ) (W : ℕ) :
    (natWeightedSimplex w W).card * ∏ i, w i ≤
      (W + ∑ i, w i).choose (Fintype.card σ) := by
  by_cases hw : ∀ i, w i ≠ 0
  · have h := weighted_mul_le_card_ordinary w hw W
    rw [card_ordinarySimplex] at h
    simpa only [Nat.add_assoc, sum_weight_sub_one_add_card w hw] using h
  · push Not at hw
    obtain ⟨i, hi⟩ := hw
    have hprod : (∏ j, w j) = 0 := prod_eq_zero (mem_univ i) hi
    simp [hprod]

private theorem succ_pow_le_factorial_mul_card_ordinary {σ : Type*} [Fintype σ]
    (W : ℕ) :
    (W + 1) ^ Fintype.card σ ≤
      (Fintype.card σ).factorial * Fintype.card (ordinarySimplex σ W) := by
  rw [card_ordinarySimplex, ← Nat.ascFactorial_eq_factorial_mul_choose]
  exact Nat.pow_succ_le_ascFactorial (W + 1) _

private theorem factorial_mul_card_ordinary_le_pow {σ : Type*} [Fintype σ]
    (W : ℕ) :
    (Fintype.card σ).factorial * Fintype.card (ordinarySimplex σ W) ≤
      (W + Fintype.card σ) ^ Fintype.card σ := by
  rw [card_ordinarySimplex, ← Nat.ascFactorial_eq_factorial_mul_choose]
  exact Nat.ascFactorial_le_pow_add W _

/-- A positive-weight simplex contains enough quotient vectors to dominate an ordinary simplex:
`(W+1)^n ≤ n! (∏ w_i) #simplex`. The statement includes `W = 0` and the empty index type.
Positivity is needed because a zero weight makes the product zero. -/
theorem succ_pow_le_factorial_mul_prod_mul_card_natWeightedSimplex
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (W : ℕ) :
    (W + 1) ^ Fintype.card σ ≤
      (Fintype.card σ).factorial * (∏ i, w i) * (natWeightedSimplex w W).card := by
  calc
    _ ≤ (Fintype.card σ).factorial * Fintype.card (ordinarySimplex σ W) :=
      succ_pow_le_factorial_mul_card_ordinary W
    _ ≤ (Fintype.card σ).factorial *
          ((natWeightedSimplex w W).card * ∏ i, w i) :=
      Nat.mul_le_mul_left _ (card_ordinary_le_weighted_mul w hw W)
    _ = _ := by ac_rfl

/-- The reverse quotient/remainder injection gives the upper factorial sandwich. If a weight
vanishes the left side is zero, so this bound needs no positivity hypothesis. It also covers the
empty index type and `W = 0`. -/
theorem factorial_mul_prod_mul_card_natWeightedSimplex_le
    {σ : Type*} [Fintype σ] [DecidableEq σ] (w : σ → ℕ) (W : ℕ) :
    (Fintype.card σ).factorial * (∏ i, w i) * (natWeightedSimplex w W).card ≤
      (W + ∑ i, w i) ^ Fintype.card σ := by
  by_cases hw : ∀ i, w i ≠ 0
  · calc
      _ = (natWeightedSimplex w W).card * (∏ i, w i) *
            (Fintype.card σ).factorial := by ac_rfl
      _ ≤ Fintype.card (ordinarySimplex σ (W + ∑ i, (w i - 1))) *
            (Fintype.card σ).factorial :=
        Nat.mul_le_mul_right _ (weighted_mul_le_card_ordinary w hw W)
      _ = (Fintype.card σ).factorial *
            Fintype.card (ordinarySimplex σ (W + ∑ i, (w i - 1))) := by ac_rfl
      _ ≤ (W + ∑ i, (w i - 1) + Fintype.card σ) ^ Fintype.card σ :=
        factorial_mul_card_ordinary_le_pow _
      _ = (W + ∑ i, w i) ^ Fintype.card σ := by
        rw [← sum_weight_sub_one_add_card w hw, Nat.add_assoc]
  · push Not at hw
    obtain ⟨i, hi⟩ := hw
    have hprod : (∏ j, w j) = 0 := prod_eq_zero (mem_univ i) hi
    simp [hprod]

/-- The integer upper estimate divided by its positive factorial and weight product, over any
ordered field. The formula is valid at `W = 0` and for an empty index type; a zero weight would
make its denominator zero and is therefore excluded. -/
theorem card_natWeightedSimplex_le {K σ : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Fintype σ] [DecidableEq σ]
    (w : σ → ℕ) (hw : ∀ i, w i ≠ 0) (W : ℕ) :
    ((natWeightedSimplex w W).card : K) ≤
      ((W : K) + ∑ i, (w i : K)) ^ Fintype.card σ /
        ((Fintype.card σ).factorial * ∏ i, (w i : K)) := by
  have h := factorial_mul_prod_mul_card_natWeightedSimplex_le w W
  have hcast : ((Fintype.card σ).factorial : K) * (∏ i, (w i : K)) *
      ((natWeightedSimplex w W).card : K) ≤
      ((W : K) + ∑ i, (w i : K)) ^ Fintype.card σ := by
    exact_mod_cast h
  have hpos : 0 < ((Fintype.card σ).factorial : K) * ∏ i, (w i : K) := by
    apply mul_pos (Nat.cast_pos.mpr (Nat.factorial_pos _))
    exact prod_pos fun i _ ↦ Nat.cast_pos.mpr (Nat.pos_of_ne_zero (hw i))
  apply (le_div_iff₀ hpos).mpr
  calc
    _ = ((Fintype.card σ).factorial : K) * (∏ i, (w i : K)) *
          ((natWeightedSimplex w W).card : K) := by ring
    _ ≤ _ := hcast

/-- For weights `1, …, n`, the residue product is `n!` and the total weight is
`(n+1).choose 2`. This specialization avoids natural division and includes `n = 0` and `W = 0`. -/
theorem natWeightedSimplex_succ_sandwich (n W : ℕ) :
    (W + 1) ^ n ≤ n.factorial ^ 2 *
        (natWeightedSimplex (fun i : Fin n ↦ i.val + 1) W).card ∧
      n.factorial ^ 2 *
        (natWeightedSimplex (fun i : Fin n ↦ i.val + 1) W).card ≤
        (W + (n + 1).choose 2) ^ n := by
  have hsum : (∑ i : Fin n, (i.val + 1)) = (n + 1).choose 2 := by
    calc
      (∑ i : Fin n, (i.val + 1)) = ∑ i ∈ range n, (i + 1) :=
        Fin.sum_univ_eq_sum_range (fun i : ℕ ↦ i + 1) n
      _ = (n + 1).choose 2 := by
        induction n with
        | zero => simp
        | succ n ih =>
            rw [sum_range_succ, ih]
            simp [Nat.choose_succ_succ, Nat.choose_one_right]
            omega
  have hprod : (∏ i : Fin n, (i.val + 1)) = n.factorial := by
    rw [← Finset.prod_range_add_one_eq_factorial]
    exact Fin.prod_univ_eq_prod_range (fun i : ℕ ↦ i + 1) n
  constructor
  · simpa only [Fintype.card_fin, hprod, pow_two, ← mul_assoc] using
      succ_pow_le_factorial_mul_prod_mul_card_natWeightedSimplex
        (fun i : Fin n ↦ i.val + 1) (fun i ↦ Nat.succ_ne_zero _) W
  · simpa only [Fintype.card_fin, hprod, hsum, pow_two, ← mul_assoc] using
      factorial_mul_prod_mul_card_natWeightedSimplex_le
        (fun i : Fin n ↦ i.val + 1) W

end Finset
