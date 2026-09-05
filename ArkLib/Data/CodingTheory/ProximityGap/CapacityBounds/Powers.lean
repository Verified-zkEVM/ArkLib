/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.Powers.Incidence

/-!
# MCA bounds for univariate powers

This file proves the univariate-powers MCA bound from [BCGM25, Theorem 8.2 and Definition 8.1].
The argument encodes a bad challenge by a large agreement domain, reconstructs compatible
codewords from interpolation seeds, and bounds the exceptional seeds by double counting.

The witness construction, collision bounds, and initial incidence estimates live in
`Powers.Incidence`; this module contains the compatible-anchor argument and public bound.

## Main result

- `linear_mcaError_powers_le` bounds `mcaError` for `univariatePowersGenerator`.

## References

- [BCGM25] Bafna, Choudhary, Guruswami, and Mardia. Theorem 8.2 and Definition 8.1.
-/

namespace CodingTheory

open scoped NNReal
open CoreDefinitions ProximityGap
open PowersInternal

open scoped BigOperators in
private theorem powers_middle_outside_incidence_card_le
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Finite F]
    {A : Type} [DecidableEq A] [AddCommGroup A] [Module F A]
    (k : ℕ) (U cstar : Fin (k + 1) → ι → A)
    (Bgood : Finset F) (Bx : F → Finset ι)
    (heq : ∀ x ∈ Bgood, ∀ i ∈ Bx x,
      (∑ j : Fin (k + 1), (x ^ (j : ℕ)) • U j i) =
        ∑ j : Fin (k + 1), (x ^ (j : ℕ)) • cstar j i) :
    ∑ x ∈ Bgood, (Bx x \ powers_common_domain k U cstar).card ≤
      (Finset.univ \ powers_common_domain k U cstar).card * k := by
  classical
  let := Fintype.ofFinite F
  let T : Finset ι := Finset.univ \ powers_common_domain k U cstar
  let R : F → ι → Prop := fun x i => i ∈ Bx x
  have habove (x : F) : T.bipartiteAbove R x =
      Bx x \ powers_common_domain k U cstar := by
    ext i
    simp only [Finset.mem_bipartiteAbove, T, R, Finset.mem_sdiff,
      Finset.mem_univ, true_and]
    exact and_comm
  have hright : ∀ i ∈ T, (Bgood.bipartiteBelow R i).card ≤ k := by
    intro i hi
    have hiout : i ∉ powers_common_domain k U cstar := (Finset.mem_sdiff.mp hi).2
    apply le_trans (Finset.card_le_card ?_)
      (powers_coordinate_agreement_seeds_card_le (F := F) k U cstar i hiout)
    intro x hx
    have hxdata : x ∈ Bgood ∧ i ∈ Bx x := by
      simpa only [Finset.mem_bipartiteBelow, R] using hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact heq x hxdata.1 i hxdata.2
  calc
    ∑ x ∈ Bgood, (Bx x \ powers_common_domain k U cstar).card =
        ∑ x ∈ Bgood, (T.bipartiteAbove R x).card := by
          apply Finset.sum_congr rfl
          intro x _
          rw [habove x]
    _ = ∑ i ∈ T, (Bgood.bipartiteBelow R i).card :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R
    _ ≤ ∑ _i ∈ T, k := Finset.sum_le_sum fun i hi => hright i hi
    _ = (Finset.univ \ powers_common_domain k U cstar).card * k := by
      simp [T]

open scoped BigOperators in
private theorem powers_middle_outside_incidence_card_le_embedding
    {ι S : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Finite F]
    {A : Type} [DecidableEq A] [AddCommGroup A] [Module F A]
    (e : S ↪ F) (k : ℕ) (U cstar : Fin (k + 1) → ι → A)
    (Bgood : Finset S) (Bx : S → Finset ι)
    (heq : ∀ x ∈ Bgood, ∀ i ∈ Bx x,
      (∑ j : Fin (k + 1), ((e x) ^ (j : ℕ)) • U j i) =
        ∑ j : Fin (k + 1), ((e x) ^ (j : ℕ)) • cstar j i) :
    ∑ x ∈ Bgood, (Bx x \ powers_common_domain k U cstar).card ≤
      (Finset.univ \ powers_common_domain k U cstar).card * k := by
  classical
  let := Fintype.ofFinite F
  let T : Finset ι := Finset.univ \ powers_common_domain k U cstar
  let R : S → ι → Prop := fun x i => i ∈ Bx x
  have habove (x : S) : T.bipartiteAbove R x =
      Bx x \ powers_common_domain k U cstar := by
    ext i
    simp only [Finset.mem_bipartiteAbove, T, R, Finset.mem_sdiff,
      Finset.mem_univ, true_and]
    exact and_comm
  have hright : ∀ i ∈ T, (Bgood.bipartiteBelow R i).card ≤ k := by
    intro i hi
    have hiout : i ∉ powers_common_domain k U cstar := (Finset.mem_sdiff.mp hi).2
    let Roots : Finset F := Finset.univ.filter fun y : F =>
      (∑ j : Fin (k + 1), (y ^ (j : ℕ)) • U j i) =
        ∑ j : Fin (k + 1), (y ^ (j : ℕ)) • cstar j i
    calc
      (Bgood.bipartiteBelow R i).card =
          ((Bgood.bipartiteBelow R i).map e).card :=
        (Finset.card_map e).symm
      _ ≤ Roots.card := by
        apply Finset.card_le_card
        intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
        have hxdata : x ∈ Bgood ∧ i ∈ Bx x := by
          simpa only [Finset.mem_bipartiteBelow, R] using hx
        simp only [Roots, Finset.mem_filter, Finset.mem_univ, true_and]
        exact heq x hxdata.1 i hxdata.2
      _ ≤ k := by
        simpa only [Roots] using
          powers_coordinate_agreement_seeds_card_le (F := F) k U cstar i hiout
  calc
    ∑ x ∈ Bgood, (Bx x \ powers_common_domain k U cstar).card =
        ∑ x ∈ Bgood, (T.bipartiteAbove R x).card := by
          apply Finset.sum_congr rfl
          intro x _
          rw [habove x]
    _ = ∑ i ∈ T, (Bgood.bipartiteBelow R i).card :=
      Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R
    _ ≤ ∑ _i ∈ T, k := Finset.sum_le_sum fun i hi => hright i hi
    _ = (Finset.univ \ powers_common_domain k U cstar).card * k := by
      simp [T]

private theorem powers_noninjective_tuple_card_le
    {S : Type} [Fintype S] [DecidableEq S] (t : ℕ) :
    (Finset.univ.filter fun xs : Fin (t + 1) → S => ¬ Function.Injective xs).card ≤
      Nat.choose (t + 1) 2 * (Fintype.card S) ^ t := by
  classical
  let P : Finset (Finset (Fin (t + 1))) :=
    (Finset.univ : Finset (Fin (t + 1))).powersetCard 2
  let collision : Finset (Fin (t + 1)) → Finset (Fin (t + 1) → S) := fun p =>
    Finset.univ.filter fun xs =>
      ∃ i ∈ p, ∃ j ∈ p, i ≠ j ∧ xs i = xs j
  have hcollision : ∀ p ∈ P, (collision p).card ≤ (Fintype.card S) ^ t := by
    intro p hp
    have hp2 : p.card = 2 := (Finset.mem_powersetCard.mp hp).2
    obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hp2
    simpa [collision, hij, ne_comm, eq_comm] using
      (powers_collision_tuple_card_le (S := S) t i j hij)
  have hsubset :
      (Finset.univ.filter fun xs : Fin (t + 1) → S => ¬ Function.Injective xs) ⊆
        P.biUnion collision := by
    intro xs hxs
    have hbad := (Finset.mem_filter.mp hxs).2
    obtain ⟨i, j, heq, hij⟩ := Function.not_injective_iff.mp hbad
    have hp : ({i, j} : Finset (Fin (t + 1))) ∈ P := by
      simp [P, hij]
    apply Finset.mem_biUnion.mpr
    refine ⟨{i, j}, hp, ?_⟩
    simp [collision, heq, hij]
  calc
    (Finset.univ.filter fun xs : Fin (t + 1) → S => ¬ Function.Injective xs).card ≤
        (P.biUnion collision).card := Finset.card_le_card hsubset
    _ ≤ P.card * (Fintype.card S) ^ t :=
      Finset.card_biUnion_le_card_mul P collision ((Fintype.card S) ^ t) hcollision
    _ = Nat.choose (t + 1) 2 * (Fintype.card S) ^ t := by
      simp [P, Finset.card_powersetCard]

private theorem powers_normalized_power_identity
    (n b α : ℝ) (k : ℕ) (hn : n ≠ 0) :
    n * b ^ (k + 2) * α ^ (k + 2) =
      (b * n * α) ^ (k + 2) / n ^ (k + 1) := by
  field_simp
  rw [mul_pow, mul_pow, show k + 2 = (k + 1) + 1 by omega, pow_succ]
  ring

open scoped BigOperators in
private theorem powers_point_degree_sum_eq
    {ι S : Type} [Fintype ι] [DecidableEq ι]
    (B : Finset S) (T : S → Finset ι) :
    (∑ i : ι, powers_point_degree B T i) =
      ∑ x ∈ B, (T x).card := by
  classical
  let R : S → ι → Prop := fun x i => i ∈ T x
  simpa [powers_point_degree, R, Finset.bipartiteBelow, Finset.bipartiteAbove] using
    (Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow R
      (s := B) (t := (Finset.univ : Finset ι))).symm

open scoped BigOperators in
private theorem powers_point_degree_moment_lower
    {ι S : Type} [Fintype ι] [Fintype S] [DecidableEq ι]
    (T : S → Finset ι) (k : ℕ) :
    (∑ x : S, ((T x).card : ℝ)) ^ (k + 2) /
        (Fintype.card ι : ℝ) ^ (k + 1) ≤
      ∑ i : ι,
        ((powers_point_degree (Finset.univ : Finset S) T i : ℕ) : ℝ) ^ (k + 2) := by
  classical
  have hincNat := powers_point_degree_sum_eq (B := (Finset.univ : Finset S)) T
  have hincReal :
      (∑ i : ι, ((powers_point_degree (Finset.univ : Finset S) T i : ℕ) : ℝ)) =
        ∑ x : S, ((T x).card : ℝ) := by
    exact_mod_cast hincNat
  have hpow := pow_sum_div_card_le_sum_pow
    (s := (Finset.univ : Finset ι))
    (f := fun i => ((powers_point_degree (Finset.univ : Finset S) T i : ℕ) : ℝ))
    (fun i hi => by positivity) (k + 1)
  simpa only [Finset.card_univ, hincReal, Nat.add_assoc] using hpow

private theorem powers_power_difference_pos (r : ℝ) (k : ℕ)
    (hr0 : 0 < r) (hr1 : r < 1) :
    0 < r ^ ((1 : ℝ) / (k + 2)) - r ^ ((1 : ℝ) / (k + 1)) := by
  rw [sub_pos]
  exact Real.rpow_lt_rpow_of_exponent_gt hr0 hr1 (powers_exponent_strict k)

private theorem powers_middle_bound_nonneg (n q k : ℕ) (δmin η : ℝ)
    (hq : 0 < q) (hη : 0 < η)
    (hr0 : 0 < powers_radius_base δmin η)
    (hr1 : powers_radius_base δmin η < 1) :
    0 ≤ powers_middle_bound n q k δmin η := by
  have hexp : 0 < (1 : ℝ) / (k + 1) := by positivity
  have hpowlt : powers_radius_base δmin η ^ ((1 : ℝ) / (k + 1)) < 1 :=
    Real.rpow_lt_one hr0.le hr1 hexp
  have hgamma : 0 ≤ 1 - powers_radius_base δmin η ^ ((1 : ℝ) / (k + 1)) :=
    (sub_pos.mpr hpowlt).le
  have hdiff := powers_power_difference_pos (powers_radius_base δmin η) k hr0 hr1
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  unfold powers_middle_bound
  positivity

private theorem powers_power_difference_pos_of_module_code
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Semiring F]
    {A : Type} [AddCommMonoid A] [Module F A] [DecidableEq A]
    (C : ModuleCode ι F A) (k : ℕ) (δmin η : NNReal)
    (hδmin : (δmin : ℝ) =
      (Code.minDist (C : Set (ι → A)) : ℝ) / Fintype.card ι)
    (hη : 0 < η) (hηlt : η < δmin) :
    0 < powers_radius_base (δmin : ℝ) (η : ℝ) ^ ((1 : ℝ) / (k + 2)) -
      powers_radius_base (δmin : ℝ) (η : ℝ) ^ ((1 : ℝ) / (k + 1)) := by
  have hr := powers_radius_base_mem_ioo_of_module_code C δmin η hδmin hη hηlt
  exact powers_power_difference_pos _ k hr.1 hr.2

open scoped BigOperators in
private theorem powers_sum_over_snoc
    {S : Type} [Fintype S] (t : ℕ)
    (f : (Fin (t + 1) → S) → ℝ) :
    (∑ ys : Fin (t + 1) → S, f ys) =
      ∑ xs : Fin t → S, ∑ x : S, f (Fin.snoc xs x) := by
  classical
  let e : S × (Fin t → S) ≃ (Fin (t + 1) → S) :=
    Fin.snocEquiv (fun _ : Fin (t + 1) => S)
  calc
    (∑ ys : Fin (t + 1) → S, f ys) =
        ∑ p : S × (Fin t → S), f (e p) :=
      (Equiv.sum_comp e f).symm
    _ = ∑ p : S × (Fin t → S), f (Fin.snoc p.2 p.1) := by
      apply Fintype.sum_congr
      intro p
      congr 1
    _ = ∑ x : S, ∑ xs : Fin t → S, f (Fin.snoc xs x) :=
      Fintype.sum_prod_type (fun p : S × (Fin t → S) =>
        f (Fin.snoc p.2 p.1))
    _ = ∑ xs : Fin t → S, ∑ x : S, f (Fin.snoc xs x) :=
      Finset.sum_comm

private theorem powers_tuple_intersection_snoc_subset_last
    {ι S : Type} [Fintype ι] [DecidableEq ι]
    (T : S → Finset ι) (t : ℕ) (xs : Fin t → S) (x : S) :
    powers_tuple_intersection (t + 1) T (Fin.snoc xs x) ⊆ T x := by
  intro i hi
  have hall : ∀ s : Fin (t + 1),
      i ∈ T ((Fin.snoc xs x : Fin (t + 1) → S) s) := by
    simpa only [powers_tuple_intersection, Finset.mem_filter, Finset.mem_univ,
      true_and] using hi
  have hlast := hall (Fin.last t)
  simpa only [Fin.snoc_last] using hlast

private theorem powers_tuple_intersection_snoc_subset_prefix
    {ι S : Type} [Fintype ι] [DecidableEq ι]
    (T : S → Finset ι) (t : ℕ) (xs : Fin t → S) (x : S) :
    powers_tuple_intersection (t + 1) T (Fin.snoc xs x) ⊆
      powers_tuple_intersection t T xs := by
  intro i hi
  simp only [powers_tuple_intersection, Finset.mem_filter, Finset.mem_univ,
    true_and] at hi ⊢
  intro s
  have hs := hi s.castSucc
  simpa only [Fin.snoc_castSucc] using hs

open scoped BigOperators in
open scoped Matrix.Module in
private theorem powers_interpolate_compatible_anchors
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Finite F]
    {A : Type} [DecidableEq A] [AddCommGroup A] [Module F A]
    {S : Type} [Finite S]
    (C : ModuleCode ι F A) (k : ℕ)
    (U : Fin (k + 1) → ι → A) (δ : ℝ)
    (e : S ↪ F)
    (bw : (x : S) → PowersBadWitness C k U (e x) δ)
    (xs : Fin (k + 1) → S) (hxs : Function.Injective xs)
    (Bgood : Finset S)
    (hgood : ∀ x ∈ Bgood,
      (powers_tuple_intersection (k + 2) (fun y => (bw y).T)
          (Fin.snoc xs x)).card >
        Fintype.card ι - Code.minDist (C : Set (ι → A))) :
    ∃ cstar : Fin (k + 1) → ι → A,
      (∀ j, cstar j ∈ C) ∧
      powers_tuple_intersection (k + 1) (fun y => (bw y).T) xs ⊆
        powers_common_domain k U cstar ∧
      ∀ x ∈ Bgood,
        (bw x).w = fun i =>
          ∑ j : Fin (k + 1), ((e x) ^ (j : ℕ)) • cstar j i := by
  classical
  let := Fintype.ofFinite F
  let := Fintype.ofFinite S
  let xF : Fin (k + 1) → F := fun s => e (xs s)
  have hxF : Function.Injective xF := e.injective.comp hxs
  obtain ⟨cstar, hcstar, hinterp⟩ :=
    powers_interpolate_module_codewords C k xF hxF
      (fun s => (bw (xs s)).w) (fun s => (bw (xs s)).w_mem)
  have hAnchor :
      powers_tuple_intersection (k + 1) (fun y => (bw y).T) xs ⊆
        powers_common_domain k U cstar := by
    intro i hi
    have hiAll : ∀ s : Fin (k + 1), i ∈ (bw (xs s)).T := by
      simpa only [powers_tuple_intersection, Finset.mem_filter, Finset.mem_univ,
        true_and] using hi
    have hrows : ∀ j : Fin (k + 1), U j i = cstar j i := by
      apply powers_coefficients_eq_on_anchor_intersection
        C k U δ xF hxF (fun s => bw (xs s)) cstar
      · intro s i
        simpa only [xF, Finset.sum_apply, Pi.smul_apply] using
          congrFun (hinterp s) i
      · exact hiAll
    simpa only [powers_common_domain, Finset.mem_filter, Finset.mem_univ,
      true_and] using hrows
  refine ⟨cstar, hcstar, hAnchor, ?_⟩
  intro x hx
  let Tfull : Finset ι :=
    powers_tuple_intersection (k + 2) (fun y => (bw y).T) (Fin.snoc xs x)
  have hTlarge : Tfull.card >
      Fintype.card ι - Code.minDist (C : Set (ι → A)) := by
    simpa only [Tfull] using hgood x hx
  have hTbw : Tfull ⊆ (bw x).T := by
    simpa only [Tfull] using
      powers_tuple_intersection_snoc_subset_last
        (fun y => (bw y).T) (k + 1) xs x
  have hTprefix : Tfull ⊆
      powers_tuple_intersection (k + 1) (fun y => (bw y).T) xs := by
    simpa only [Tfull] using
      powers_tuple_intersection_snoc_subset_prefix
        (fun y => (bw y).T) (k + 1) xs x
  have hTcommon : Tfull ⊆ powers_common_domain k U cstar :=
    fun i hi => hAnchor (hTprefix hi)
  exact powers_good_witness_eq_interpolated_of_large_intersection
    C k U (e x) δ (bw x) cstar hcstar Tfull hTlarge hTbw hTcommon

open scoped BigOperators in
private theorem powers_tuple_intersection_sum_eq
    {ι S : Type} [Fintype ι] [Fintype S] [DecidableEq ι]
    (T : S → Finset ι) (t : ℕ) :
    (∑ xs : Fin t → S, (powers_tuple_intersection t T xs).card) =
      ∑ i : ι, (powers_point_degree (Finset.univ : Finset S) T i) ^ t := by
  classical
  unfold powers_tuple_intersection powers_point_degree
  simp_rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Fintype.sum_pow]
  apply Finset.sum_congr rfl
  intro xs hxs
  rw [Finset.prod_boole]
  simp

open scoped BigOperators in
private theorem powers_tuple_intersection_sum_lower
    {ι S : Type} [Fintype ι] [Nonempty ι] [Fintype S] [DecidableEq ι]
    (T : S → Finset ι) (k : ℕ) (α : ℝ) (hα : 0 ≤ α)
    (hT : ∀ x : S,
      (Fintype.card ι : ℝ) * α ≤ ((T x).card : ℝ)) :
    (Fintype.card ι : ℝ) * (Fintype.card S : ℝ) ^ (k + 2) * α ^ (k + 2) ≤
      ∑ xs : Fin (k + 2) → S,
        ((powers_tuple_intersection (k + 2) T xs).card : ℝ) := by
  classical
  have hnpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hn : (Fintype.card ι : ℝ) ≠ 0 := hnpos.ne'
  have hsum :
      (Fintype.card S : ℝ) * (Fintype.card ι : ℝ) * α ≤
        ∑ x : S, ((T x).card : ℝ) := by
    calc
      (Fintype.card S : ℝ) * (Fintype.card ι : ℝ) * α =
          ∑ _x : S, (Fintype.card ι : ℝ) * α := by simp; ring
      _ ≤ ∑ x : S, ((T x).card : ℝ) :=
        Finset.sum_le_sum fun x hx => hT x
  have hbase_nonneg :
      0 ≤ (Fintype.card S : ℝ) * (Fintype.card ι : ℝ) * α := by positivity
  have hpow :
      ((Fintype.card S : ℝ) * (Fintype.card ι : ℝ) * α) ^ (k + 2) ≤
        (∑ x : S, ((T x).card : ℝ)) ^ (k + 2) :=
    pow_le_pow_left₀ hbase_nonneg hsum (k + 2)
  have hmoment := powers_point_degree_moment_lower T k
  have hdoubleNat := powers_tuple_intersection_sum_eq T (k + 2)
  have hdoubleReal :
      (∑ i : ι,
          ((powers_point_degree (Finset.univ : Finset S) T i : ℕ) : ℝ) ^ (k + 2)) =
        ∑ xs : Fin (k + 2) → S,
          ((powers_tuple_intersection (k + 2) T xs).card : ℝ) := by
    exact_mod_cast hdoubleNat.symm
  rw [powers_normalized_power_identity
    (Fintype.card ι : ℝ) (Fintype.card S : ℝ) α k hn]
  calc
    (((Fintype.card S : ℝ) * (Fintype.card ι : ℝ) * α) ^ (k + 2)) /
          (Fintype.card ι : ℝ) ^ (k + 1) ≤
        (∑ x : S, ((T x).card : ℝ)) ^ (k + 2) /
          (Fintype.card ι : ℝ) ^ (k + 1) :=
      div_le_div_of_nonneg_right hpow (by positivity)
    _ ≤ ∑ i : ι,
          ((powers_point_degree (Finset.univ : Finset S) T i : ℕ) : ℝ) ^ (k + 2) := hmoment
    _ = ∑ xs : Fin (k + 2) → S,
          ((powers_tuple_intersection (k + 2) T xs).card : ℝ) := hdoubleReal

open scoped BigOperators in
private theorem powers_compatible_tuple_card_lower
    {ι S : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype S]
    (T : S → Finset ι) (k D : ℕ) (α η : ℝ)
    (hα : 0 ≤ α) (_hD : D ≤ Fintype.card ι)
    (hT : ∀ x : S,
      (Fintype.card ι : ℝ) * α ≤ ((T x).card : ℝ))
    (hrel : (Fintype.card ι : ℝ) * α ^ (k + 2) =
      ((Fintype.card ι - D : ℕ) : ℝ) + (Fintype.card ι : ℝ) * η) :
    η * (Fintype.card S : ℝ) ^ (k + 2) ≤
      ((Finset.univ.filter fun xs : Fin (k + 2) → S =>
        (powers_tuple_intersection (k + 2) T xs).card >
          Fintype.card ι - D).card : ℝ) := by
  classical
  let Good : Finset (Fin (k + 2) → S) :=
    Finset.univ.filter fun xs =>
      (powers_tuple_intersection (k + 2) T xs).card > Fintype.card ι - D
  have hnpos : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hlower := powers_tuple_intersection_sum_lower T k α hα hT
  have hupper :
      (∑ xs : Fin (k + 2) → S,
          ((powers_tuple_intersection (k + 2) T xs).card : ℝ)) ≤
        (Fintype.card S : ℝ) ^ (k + 2) *
            ((Fintype.card ι - D : ℕ) : ℝ) +
          (Good.card : ℝ) * (Fintype.card ι : ℝ) := by
    calc
      (∑ xs : Fin (k + 2) → S,
          ((powers_tuple_intersection (k + 2) T xs).card : ℝ)) ≤
          ∑ xs : Fin (k + 2) → S,
            (((Fintype.card ι - D : ℕ) : ℝ) +
              if xs ∈ Good then (Fintype.card ι : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro xs hxs
        by_cases hgood : xs ∈ Good
        · have hcard : (powers_tuple_intersection (k + 2) T xs).card ≤
              Fintype.card ι := by
            simpa only [← Finset.card_univ] using
              Finset.card_le_univ (powers_tuple_intersection (k + 2) T xs)
          have hcardR :
              ((powers_tuple_intersection (k + 2) T xs).card : ℝ) ≤
                (Fintype.card ι : ℝ) := by exact_mod_cast hcard
          have hsub : 0 ≤ ((Fintype.card ι - D : ℕ) : ℝ) := by positivity
          simp only [if_pos hgood]
          linarith
        · have hnot : ¬ (powers_tuple_intersection (k + 2) T xs).card >
              Fintype.card ι - D := by
            simpa only [Good, Finset.mem_filter, Finset.mem_univ, true_and] using hgood
          have hcard : (powers_tuple_intersection (k + 2) T xs).card ≤
              Fintype.card ι - D := Nat.le_of_not_lt hnot
          simp only [if_neg hgood, add_zero]
          exact_mod_cast hcard
      _ = (Fintype.card S : ℝ) ^ (k + 2) *
            ((Fintype.card ι - D : ℕ) : ℝ) +
          (Good.card : ℝ) * (Fintype.card ι : ℝ) := by
        rw [Finset.sum_add_distrib]
        rw [Fintype.sum_ite_mem Good (fun _ => (Fintype.card ι : ℝ))]
        simp
  have hcompare := le_trans hlower hupper
  have hrewrite :
      (Fintype.card ι : ℝ) * (Fintype.card S : ℝ) ^ (k + 2) * α ^ (k + 2) =
        (Fintype.card S : ℝ) ^ (k + 2) *
            ((Fintype.card ι - D : ℕ) : ℝ) +
          (Fintype.card ι : ℝ) *
            (η * (Fintype.card S : ℝ) ^ (k + 2)) := by
    calc
      (Fintype.card ι : ℝ) * (Fintype.card S : ℝ) ^ (k + 2) * α ^ (k + 2) =
          (Fintype.card S : ℝ) ^ (k + 2) *
            ((Fintype.card ι : ℝ) * α ^ (k + 2)) := by ring
      _ = (Fintype.card S : ℝ) ^ (k + 2) *
            (((Fintype.card ι - D : ℕ) : ℝ) +
              (Fintype.card ι : ℝ) * η) := by rw [hrel]
      _ = (Fintype.card S : ℝ) ^ (k + 2) *
            ((Fintype.card ι - D : ℕ) : ℝ) +
          (Fintype.card ι : ℝ) *
            (η * (Fintype.card S : ℝ) ^ (k + 2)) := by ring
  rw [hrewrite] at hcompare
  have hcancel :
      (Fintype.card ι : ℝ) *
          (η * (Fintype.card S : ℝ) ^ (k + 2)) ≤
        (Fintype.card ι : ℝ) * (Good.card : ℝ) := by
    nlinarith
  have hfinal :
      η * (Fintype.card S : ℝ) ^ (k + 2) ≤ (Good.card : ℝ) :=
    le_of_mul_le_mul_of_pos_left hcancel hnpos
  simpa only [Good] using hfinal

open scoped BigOperators in
private theorem powers_injective_compatible_tuple_card_lower
    {ι S : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Fintype S] [DecidableEq S]
    (T : S → Finset ι) (k D : ℕ) (α η : ℝ)
    (hα : 0 ≤ α) (hD : D ≤ Fintype.card ι)
    (hT : ∀ x : S,
      (Fintype.card ι : ℝ) * α ≤ ((T x).card : ℝ))
    (hrel : (Fintype.card ι : ℝ) * α ^ (k + 2) =
      ((Fintype.card ι - D : ℕ) : ℝ) + (Fintype.card ι : ℝ) * η) :
    (Fintype.card S : ℝ) ^ (k + 1) *
        (η * (Fintype.card S : ℝ) - (Nat.choose (k + 2) 2 : ℝ)) ≤
      ((Finset.univ.filter fun xs : Fin (k + 2) → S =>
        (powers_tuple_intersection (k + 2) T xs).card >
            Fintype.card ι - D ∧ Function.Injective xs).card : ℝ) := by
  classical
  let G : Finset (Fin (k + 2) → S) :=
    Finset.univ.filter fun xs =>
      (powers_tuple_intersection (k + 2) T xs).card > Fintype.card ι - D
  let I : Finset (Fin (k + 2) → S) :=
    Finset.univ.filter fun xs =>
      (powers_tuple_intersection (k + 2) T xs).card > Fintype.card ι - D ∧
        Function.Injective xs
  let N : Finset (Fin (k + 2) → S) :=
    Finset.univ.filter fun xs => ¬ Function.Injective xs
  have hG : η * (Fintype.card S : ℝ) ^ (k + 2) ≤ (G.card : ℝ) := by
    simpa only [G] using
      powers_compatible_tuple_card_lower T k D α η hα hD hT hrel
  have hNnat : N.card ≤ Nat.choose (k + 2) 2 * (Fintype.card S) ^ (k + 1) := by
    simpa only [N] using powers_noninjective_tuple_card_le (S := S) (k + 1)
  have hN : (N.card : ℝ) ≤
      (Nat.choose (k + 2) 2 : ℝ) * (Fintype.card S : ℝ) ^ (k + 1) := by
    exact_mod_cast hNnat
  have hcover : G ⊆ I ∪ N := by
    intro xs hxs
    have hcompat :
        (powers_tuple_intersection (k + 2) T xs).card > Fintype.card ι - D := by
      simpa only [G, Finset.mem_filter, Finset.mem_univ, true_and] using hxs
    by_cases hinj : Function.Injective xs
    · apply Finset.mem_union_left
      simpa only [I, Finset.mem_filter, Finset.mem_univ, true_and] using
        And.intro hcompat hinj
    · apply Finset.mem_union_right
      simpa only [N, Finset.mem_filter, Finset.mem_univ, true_and] using hinj
  have hcoverNat : G.card ≤ I.card + N.card :=
    le_trans (Finset.card_le_card hcover) (Finset.card_union_le I N)
  have hcoverR : (G.card : ℝ) ≤ (I.card : ℝ) + (N.card : ℝ) := by
    exact_mod_cast hcoverNat
  have hpow : (Fintype.card S : ℝ) ^ (k + 2) =
      (Fintype.card S : ℝ) ^ (k + 1) * (Fintype.card S : ℝ) := by
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
  rw [hpow] at hG
  have hfinal :
      (Fintype.card S : ℝ) ^ (k + 1) *
          (η * (Fintype.card S : ℝ) - (Nat.choose (k + 2) 2 : ℝ)) ≤
        (I.card : ℝ) := by
    nlinarith
  simpa only [I] using hfinal

open scoped BigOperators in
private theorem powers_select_compatible_anchors
    {ι S : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    [Fintype S] [DecidableEq S]
    (T : S → Finset ι) (k D : ℕ) (α η : ℝ)
    (hα : 0 ≤ α) (hD : D ≤ Fintype.card ι)
    (hT : ∀ x : S,
      (Fintype.card ι : ℝ) * α ≤ ((T x).card : ℝ))
    (hrel : (Fintype.card ι : ℝ) * α ^ (k + 2) =
      ((Fintype.card ι - D : ℕ) : ℝ) + (Fintype.card ι : ℝ) * η)
    (hlarge : (Nat.choose (k + 2) 2 : ℝ) <
      η * (Fintype.card S : ℝ)) :
    ∃ xs : Fin (k + 1) → S,
      Function.Injective xs ∧
      η * (Fintype.card S : ℝ) - (Nat.choose (k + 2) 2 : ℝ) ≤
        ((Finset.univ.filter fun x : S =>
          (powers_tuple_intersection (k + 2) T (Fin.snoc xs x)).card >
              Fintype.card ι - D ∧
            Function.Injective (Fin.snoc xs x)).card : ℝ) := by
  classical
  let a : ℝ :=
    η * (Fintype.card S : ℝ) - (Nat.choose (k + 2) 2 : ℝ)
  let P : (Fin (k + 2) → S) → Prop := fun ys =>
    (powers_tuple_intersection (k + 2) T ys).card > Fintype.card ι - D ∧
      Function.Injective ys
  let Bgood : (Fin (k + 1) → S) → Finset S := fun xs =>
    Finset.univ.filter fun x => P (Fin.snoc xs x)
  have ha : 0 < a := by
    dsimp [a]
    linarith
  have hSposR : 0 < (Fintype.card S : ℝ) := by
    by_contra hnot
    have hSle : (Fintype.card S : ℝ) ≤ 0 := le_of_not_gt hnot
    have hS0 : (Fintype.card S : ℝ) = 0 :=
      le_antisymm hSle (by positivity)
    have hc : 0 ≤ (Nat.choose (k + 2) 2 : ℝ) := by positivity
    rw [hS0, mul_zero] at hlarge
    exact (not_lt_of_ge hc) hlarge
  have hSpos : 0 < Fintype.card S := by exact_mod_cast hSposR
  let : Nonempty S := Fintype.card_pos_iff.mp hSpos
  have hmass :
      (Fintype.card S : ℝ) ^ (k + 1) * a ≤
        ((Finset.univ.filter P).card : ℝ) := by
    simpa only [a, P] using
      powers_injective_compatible_tuple_card_lower T k D α η hα hD hT hrel
  have hdecomp :
      ((Finset.univ.filter P).card : ℝ) =
        ∑ xs : Fin (k + 1) → S, ((Bgood xs).card : ℝ) := by
    calc
      ((Finset.univ.filter P).card : ℝ) =
          ∑ ys : Fin (k + 2) → S, if P ys then (1 : ℝ) else 0 := by
        simpa using
          (Finset.natCast_card_filter (R := ℝ) P
            (Finset.univ : Finset (Fin (k + 2) → S)))
      _ = ∑ xs : Fin (k + 1) → S,
            ∑ x : S, if P (Fin.snoc xs x) then (1 : ℝ) else 0 :=
        powers_sum_over_snoc (S := S) (k + 1)
          (fun ys => if P ys then (1 : ℝ) else 0)
      _ = ∑ xs : Fin (k + 1) → S, ((Bgood xs).card : ℝ) := by
        apply Fintype.sum_congr
        intro xs
        symm
        simpa only [Bgood] using
          (Finset.natCast_card_filter (R := ℝ)
            (fun x : S => P (Fin.snoc xs x)) (Finset.univ : Finset S))
  have hmassSum :
      (Fintype.card (Fin (k + 1) → S) : ℝ) * a ≤
        ∑ xs : Fin (k + 1) → S, ((Bgood xs).card : ℝ) := by
    rw [← hdecomp]
    simpa only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] using hmass
  have havg : ∃ xs : Fin (k + 1) → S, a ≤ ((Bgood xs).card : ℝ) := by
    by_contra hnone
    push Not at hnone
    have huniv : (Finset.univ : Finset (Fin (k + 1) → S)).Nonempty :=
      Finset.univ_nonempty
    have hsumlt :
        (∑ xs : Fin (k + 1) → S, ((Bgood xs).card : ℝ)) <
          ∑ _xs : Fin (k + 1) → S, a := by
      apply Finset.sum_lt_sum_of_nonempty huniv
      intro xs hxs
      exact hnone xs
    have hconst :
        (∑ _xs : Fin (k + 1) → S, a) =
          (Fintype.card (Fin (k + 1) → S) : ℝ) * a := by
      simp
    rw [hconst] at hsumlt
    linarith
  obtain ⟨xs, hxsCard⟩ := havg
  have hBposR : 0 < ((Bgood xs).card : ℝ) := lt_of_lt_of_le ha hxsCard
  have hBpos : 0 < (Bgood xs).card := by exact_mod_cast hBposR
  obtain ⟨x, hx⟩ := Finset.card_pos.mp hBpos
  have hxP : P (Fin.snoc xs x) := by
    simpa only [Bgood, Finset.mem_filter, Finset.mem_univ, true_and] using hx
  have hxsInj : Function.Injective xs :=
    powers_injective_prefix_of_snoc xs x hxP.2
  refine ⟨xs, hxsInj, ?_⟩
  simpa only [a, Bgood, P] using hxsCard

open scoped BigOperators in
private theorem powers_witness_card_mul_le_outside_incidence_add
    {ι S : Type} [DecidableEq ι]
    (m : ℕ) (Bgood : Finset S) (Bx : S → Finset ι) (T : Finset ι)
    (hcard : ∀ x ∈ Bgood, m ≤ (Bx x).card) :
    Bgood.card * m ≤
      (∑ x ∈ Bgood, (Bx x \ T).card) + Bgood.card * T.card := by
  calc
    Bgood.card * m = ∑ _x ∈ Bgood, m := by simp
    _ ≤ ∑ x ∈ Bgood, ((Bx x \ T).card + T.card) := by
      apply Finset.sum_le_sum
      intro x hx
      exact le_trans (hcard x hx) Finset.card_le_card_sdiff_add_card
    _ = (∑ x ∈ Bgood, (Bx x \ T).card) + Bgood.card * T.card := by
      rw [Finset.sum_add_distrib]
      simp

private theorem powers_witness_outside_real_card_lower
    {ι : Type} [DecidableEq ι]
    (Bx T : Finset ι) (n α β : ℝ)
    (hBx : n * α ≤ (Bx.card : ℝ))
    (hT : (T.card : ℝ) ≤ n * β) :
    n * (α - β) ≤ ((Bx \ T).card : ℝ) := by
  have hnat : Bx.card ≤ (Bx \ T).card + T.card :=
    Finset.card_le_card_sdiff_add_card
  have hreal : (Bx.card : ℝ) ≤
      ((Bx \ T).card : ℝ) + (T.card : ℝ) := by
    exact_mod_cast hnat
  linarith

open scoped BigOperators in
private theorem powers_common_domain_card_gt_of_many_good_seeds
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Finite F]
    {A : Type} [DecidableEq A] [AddCommGroup A] [Module F A]
    (k : ℕ) (U cstar : Fin (k + 1) → ι → A)
    (α β : ℝ) (Bgood : Finset F) (Bx : F → Finset ι)
    (hBx : ∀ x ∈ Bgood,
      (Fintype.card ι : ℝ) * α ≤ ((Bx x).card : ℝ))
    (hgap : (k : ℝ) < (Bgood.card : ℝ) * (α - β))
    (heq : ∀ x ∈ Bgood, ∀ i ∈ Bx x,
      (∑ j : Fin (k + 1), (x ^ (j : ℕ)) • U j i) =
        ∑ j : Fin (k + 1), (x ^ (j : ℕ)) • cstar j i) :
    (Fintype.card ι : ℝ) * β <
      ((powers_common_domain k U cstar).card : ℝ) := by
  classical
  let := Fintype.ofFinite F
  by_contra hnot
  have hcommon : ((powers_common_domain k U cstar).card : ℝ) ≤
      (Fintype.card ι : ℝ) * β := le_of_not_gt hnot
  have hsumLower :
      (∑ x ∈ Bgood, (Fintype.card ι : ℝ) * (α - β)) ≤
        ∑ x ∈ Bgood,
          (((Bx x \ powers_common_domain k U cstar).card : ℕ) : ℝ) := by
    apply Finset.sum_le_sum
    intro x hx
    exact powers_witness_outside_real_card_lower
      (Bx x) (powers_common_domain k U cstar)
      (Fintype.card ι : ℝ) α β (hBx x hx) hcommon
  have hincNat :=
    powers_middle_outside_incidence_card_le
      (F := F) k U cstar Bgood Bx heq
  have hincReal :
      (∑ x ∈ Bgood,
          (((Bx x \ powers_common_domain k U cstar).card : ℕ) : ℝ)) ≤
        (((Finset.univ \ powers_common_domain k U cstar).card : ℕ) : ℝ) *
          (k : ℝ) := by
    exact_mod_cast hincNat
  have hcompNat :
      (Finset.univ \ powers_common_domain k U cstar).card ≤ Fintype.card ι := by
    simpa only [← Finset.card_univ] using
      Finset.card_le_univ (Finset.univ \ powers_common_domain k U cstar)
  have hcompReal :
      (((Finset.univ \ powers_common_domain k U cstar).card : ℕ) : ℝ) ≤
        (Fintype.card ι : ℝ) := by
    exact_mod_cast hcompNat
  have hupper :
      (((Finset.univ \ powers_common_domain k U cstar).card : ℕ) : ℝ) *
          (k : ℝ) ≤ (Fintype.card ι : ℝ) * (k : ℝ) :=
    mul_le_mul_of_nonneg_right hcompReal (Nat.cast_nonneg k)
  have htotal :
      (Bgood.card : ℝ) * ((Fintype.card ι : ℝ) * (α - β)) ≤
        (Fintype.card ι : ℝ) * (k : ℝ) := by
    calc
      (Bgood.card : ℝ) * ((Fintype.card ι : ℝ) * (α - β)) =
          ∑ x ∈ Bgood, (Fintype.card ι : ℝ) * (α - β) := by simp
      _ ≤ ∑ x ∈ Bgood,
          (((Bx x \ powers_common_domain k U cstar).card : ℕ) : ℝ) := hsumLower
      _ ≤ (((Finset.univ \ powers_common_domain k U cstar).card : ℕ) : ℝ) *
          (k : ℝ) := hincReal
      _ ≤ (Fintype.card ι : ℝ) * (k : ℝ) := hupper
  have hnpos : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have hmul :
      (Fintype.card ι : ℝ) * ((Bgood.card : ℝ) * (α - β)) ≤
        (Fintype.card ι : ℝ) * (k : ℝ) := by
    calc
      (Fintype.card ι : ℝ) * ((Bgood.card : ℝ) * (α - β)) =
          (Bgood.card : ℝ) * ((Fintype.card ι : ℝ) * (α - β)) := by ring
      _ ≤ (Fintype.card ι : ℝ) * (k : ℝ) := htotal
  have hcancel : (Bgood.card : ℝ) * (α - β) ≤ (k : ℝ) :=
    le_of_mul_le_mul_left hmul hnpos
  exact (not_lt_of_ge hcancel) hgap

open scoped BigOperators in
private theorem powers_common_domain_card_gt_of_many_good_seeds_embedding
    {ι S : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Finite F]
    {A : Type} [DecidableEq A] [AddCommGroup A] [Module F A]
    (e : S ↪ F) (k : ℕ) (U cstar : Fin (k + 1) → ι → A)
    (α β : ℝ) (Bgood : Finset S) (Bx : S → Finset ι)
    (hBx : ∀ x ∈ Bgood,
      (Fintype.card ι : ℝ) * α ≤ ((Bx x).card : ℝ))
    (hgap : (k : ℝ) < (Bgood.card : ℝ) * (α - β))
    (heq : ∀ x ∈ Bgood, ∀ i ∈ Bx x,
      (∑ j : Fin (k + 1), ((e x) ^ (j : ℕ)) • U j i) =
        ∑ j : Fin (k + 1), ((e x) ^ (j : ℕ)) • cstar j i) :
    (Fintype.card ι : ℝ) * β <
      ((powers_common_domain k U cstar).card : ℝ) := by
  classical
  let := Fintype.ofFinite F
  by_contra hnot
  have hcommon : ((powers_common_domain k U cstar).card : ℝ) ≤
      (Fintype.card ι : ℝ) * β := le_of_not_gt hnot
  have hsumLower :
      (∑ x ∈ Bgood, (Fintype.card ι : ℝ) * (α - β)) ≤
        ∑ x ∈ Bgood,
          (((Bx x \ powers_common_domain k U cstar).card : ℕ) : ℝ) := by
    apply Finset.sum_le_sum
    intro x hx
    exact powers_witness_outside_real_card_lower
      (Bx x) (powers_common_domain k U cstar)
      (Fintype.card ι : ℝ) α β (hBx x hx) hcommon
  have hincNat :=
    powers_middle_outside_incidence_card_le_embedding
      e k U cstar Bgood Bx heq
  have hincReal :
      (∑ x ∈ Bgood,
          (((Bx x \ powers_common_domain k U cstar).card : ℕ) : ℝ)) ≤
        (((Finset.univ \ powers_common_domain k U cstar).card : ℕ) : ℝ) *
          (k : ℝ) := by
    exact_mod_cast hincNat
  have hcompNat :
      (Finset.univ \ powers_common_domain k U cstar).card ≤ Fintype.card ι := by
    simpa only [← Finset.card_univ] using
      Finset.card_le_univ (Finset.univ \ powers_common_domain k U cstar)
  have hcompReal :
      (((Finset.univ \ powers_common_domain k U cstar).card : ℕ) : ℝ) ≤
        (Fintype.card ι : ℝ) := by
    exact_mod_cast hcompNat
  have hupper :
      (((Finset.univ \ powers_common_domain k U cstar).card : ℕ) : ℝ) *
          (k : ℝ) ≤ (Fintype.card ι : ℝ) * (k : ℝ) :=
    mul_le_mul_of_nonneg_right hcompReal (Nat.cast_nonneg k)
  have htotal :
      (Bgood.card : ℝ) * ((Fintype.card ι : ℝ) * (α - β)) ≤
        (Fintype.card ι : ℝ) * (k : ℝ) := by
    calc
      (Bgood.card : ℝ) * ((Fintype.card ι : ℝ) * (α - β)) =
          ∑ x ∈ Bgood, (Fintype.card ι : ℝ) * (α - β) := by simp
      _ ≤ ∑ x ∈ Bgood,
          (((Bx x \ powers_common_domain k U cstar).card : ℕ) : ℝ) := hsumLower
      _ ≤ (((Finset.univ \ powers_common_domain k U cstar).card : ℕ) : ℝ) *
          (k : ℝ) := hincReal
      _ ≤ (Fintype.card ι : ℝ) * (k : ℝ) := hupper
  have hnpos : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have hmul :
      (Fintype.card ι : ℝ) * ((Bgood.card : ℝ) * (α - β)) ≤
        (Fintype.card ι : ℝ) * (k : ℝ) := by
    calc
      (Fintype.card ι : ℝ) * ((Bgood.card : ℝ) * (α - β)) =
          (Bgood.card : ℝ) * ((Fintype.card ι : ℝ) * (α - β)) := by ring
      _ ≤ (Fintype.card ι : ℝ) * (k : ℝ) := htotal
  have hcancel : (Bgood.card : ℝ) * (α - β) ≤ (k : ℝ) :=
    le_of_mul_le_mul_left hmul hnpos
  exact (not_lt_of_ge hcancel) hgap

open scoped NNReal in
open scoped BigOperators in
open scoped Matrix.Module in
private theorem powers_bad_seed_finset_card_le
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Fintype F]
    {A : Type} [Finite A] [DecidableEq A] [AddCommGroup A] [Module F A]
    (C : ModuleCode ι F A) (k : ℕ) (δmin η : ℝ≥0)
    (U : Fin (k + 1) → ι → A) (B : Finset F)
    (hB : ∀ x : F, x ∈ B ↔
      CoreDefinitions.IsMCA (CoreDefinitions.univariatePowersGenerator F k) C x U
        (1 - (1 - (δmin : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / (k + 2))))
    (_hk : 1 ≤ k) (_hcard : k + 1 ≤ Fintype.card F)
    (hδmin : (δmin : ℝ) =
      (Code.minDist (C : Set (ι → A)) : ℝ) / Fintype.card ι)
    (hη : 0 < η) (hηlt : η < δmin) :
    (B.card : ℝ) ≤
      (((Fintype.card ι : ℝ) *
            (1 - (1 - (δmin : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / (k + 1))) /
            (η : ℝ)) * (k : ℝ)) +
        max
          (2 * (k : ℝ) /
            ((η : ℝ) *
              ((1 - (δmin : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / (k + 2)) -
               (1 - (δmin : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / (k + 1)))))
          (((k : ℝ) + 1) * ((k : ℝ) + 2) / (η : ℝ)) := by
  classical
  let := Fintype.ofFinite A
  let r : ℝ := powers_radius_base (δmin : ℝ) (η : ℝ)
  let α : ℝ := r ^ ((1 : ℝ) / (k + 2))
  let β : ℝ := r ^ ((1 : ℝ) / (k + 1))
  let Δ : ℝ := α - β
  let c : ℝ := Nat.choose (k + 2) 2
  let M : ℝ :=
    max (2 * (k : ℝ) / ((η : ℝ) * Δ))
      (((k : ℝ) + 1) * ((k : ℝ) + 2) / (η : ℝ))
  have hηR : (0 : ℝ) < (η : ℝ) := by exact_mod_cast hη
  have hr := powers_radius_base_mem_ioo_of_module_code C δmin η hδmin hη hηlt
  have hΔ : 0 < Δ := by
    simpa only [Δ, α, β, r] using
      powers_power_difference_pos_of_module_code C k δmin η hδmin hη hηlt
  have hα0 : 0 ≤ α := by
    dsimp only [α]
    exact Real.rpow_nonneg hr.1.le _
  have hβlt : β < 1 := by
    dsimp only [β]
    apply Real.rpow_lt_one hr.1.le hr.2
    positivity
  have hγ0 : 0 ≤ 1 - β := (sub_pos.mpr hβlt).le
  have hD : Code.minDist (C : Set (ι → A)) ≤ Fintype.card ι := by
    rw [← Code.dist_eq_minDist]
    exact Code.dist_le_card _
  have hrel :
      (Fintype.card ι : ℝ) * α ^ (k + 2) =
        ((Fintype.card ι - Code.minDist (C : Set (ι → A)) : ℕ) : ℝ) +
          (Fintype.card ι : ℝ) * (η : ℝ) := by
    simpa only [α, r] using
      powers_alpha_pow_relation C k δmin η hδmin hη hηlt
  let S := {x : F // x ∈ B}
  let e : S ↪ F := powers_bad_seed_embedding B
  have hBα : ∀ x : F, x ∈ B ↔
      CoreDefinitions.IsMCA (CoreDefinitions.univariatePowersGenerator F k) C x U
        (1 - α) := by
    intro x
    simpa only [α, r, powers_radius_base] using hB x
  let bw : (x : S) → PowersBadWitness C k U (e x) (1 - α) := fun x =>
    powers_bad_witness_of_bad_seed_subtype C k U (1 - α) B hBα x
  have hScard : Fintype.card S = B.card := by
    exact Fintype.card_of_subtype B (fun x => Iff.rfl)
  have hT : ∀ x : S,
      (Fintype.card ι : ℝ) * α ≤ (((bw x).T.card : ℕ) : ℝ) := by
    intro x
    calc
      (Fintype.card ι : ℝ) * α =
          (Fintype.card ι : ℝ) * (1 - (1 - α)) := by ring
      _ ≤ (((bw x).T.card : ℕ) : ℝ) := (bw x).card_ge
  change (B.card : ℝ) ≤
    ((Fintype.card ι : ℝ) * (1 - β) / (η : ℝ)) * (k : ℝ) + M
  by_cases hsmall : (B.card : ℝ) ≤ M
  · have hmain0 : 0 ≤
        ((Fintype.card ι : ℝ) * (1 - β) / (η : ℝ)) * (k : ℝ) := by
      positivity
    linarith
  · have hlarge : M < (B.card : ℝ) := lt_of_not_ge hsmall
    have hfirst : 2 * (k : ℝ) / ((η : ℝ) * Δ) < (B.card : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) hlarge
    have hsecondRaw :
        (((k : ℝ) + 1) * ((k : ℝ) + 2) / (η : ℝ)) < (B.card : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hlarge
    have hchoose : 2 * c = ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
      simpa only [c] using powers_choose_two_cast k
    have hsecond : 2 * c / (η : ℝ) < (B.card : ℝ) := by
      rw [hchoose]
      exact hsecondRaw
    have hc0 : 0 ≤ c := by positivity
    have hsecondMul : 2 * c < (B.card : ℝ) * (η : ℝ) :=
      (div_lt_iff₀ hηR).mp hsecond
    have hcLargeB : c < (η : ℝ) * (B.card : ℝ) := by
      rw [mul_comm (B.card : ℝ) (η : ℝ)] at hsecondMul
      linarith
    have hcLargeS : c < (η : ℝ) * (Fintype.card S : ℝ) := by
      rw [hScard]
      exact hcLargeB
    obtain ⟨xs, hxs, hselected⟩ :=
      powers_select_compatible_anchors
        (T := fun x : S => (bw x).T) k
        (Code.minDist (C : Set (ι → A))) α (η : ℝ)
        hα0 hD hT hrel hcLargeS
    let Bgood : Finset S := Finset.univ.filter fun x : S =>
      (powers_tuple_intersection (k + 2) (fun y : S => (bw y).T)
          (Fin.snoc xs x)).card >
            Fintype.card ι - Code.minDist (C : Set (ι → A)) ∧
        Function.Injective (Fin.snoc xs x)
    have hlowerS :
        (η : ℝ) * (Fintype.card S : ℝ) - c ≤ (Bgood.card : ℝ) := by
      simpa only [Bgood, c] using hselected
    have hlowerB :
        (η : ℝ) * (B.card : ℝ) - c ≤ (Bgood.card : ℝ) := by
      simpa only [hScard] using hlowerS
    have harith := powers_large_branch_arithmetic
      (k : ℝ) c (η : ℝ) Δ (B.card : ℝ) (Bgood.card : ℝ)
      hηR hΔ hc0 hfirst hsecond hlowerB
    have hgap : (k : ℝ) < (Bgood.card : ℝ) * (α - β) := by
      simpa only [Δ] using harith.2
    have hgoodLarge : ∀ x ∈ Bgood,
        (powers_tuple_intersection (k + 2) (fun y : S => (bw y).T)
          (Fin.snoc xs x)).card >
            Fintype.card ι - Code.minDist (C : Set (ι → A)) := by
      intro x hx
      exact (Finset.mem_filter.mp hx).2.1
    obtain ⟨cstar, hcstar, _hAnchor, hinterp⟩ :=
      powers_interpolate_compatible_anchors
        C k U (1 - α) e bw xs hxs Bgood hgoodLarge
    have heq : ∀ x ∈ Bgood, ∀ i ∈ (bw x).T,
        (∑ j : Fin (k + 1), ((e x) ^ (j : ℕ)) • U j i) =
          ∑ j : Fin (k + 1), ((e x) ^ (j : ℕ)) • cstar j i := by
      intro x hx i hi
      calc
        (∑ j : Fin (k + 1), ((e x) ^ (j : ℕ)) • U j i) =
            (bw x).w i := (bw x).combination_eq_on i hi
        _ = ∑ j : Fin (k + 1), ((e x) ^ (j : ℕ)) • cstar j i :=
          congrFun (hinterp x hx) i
    have hcommonStrict :
        (Fintype.card ι : ℝ) * β <
          ((powers_common_domain k U cstar).card : ℝ) :=
      powers_common_domain_card_gt_of_many_good_seeds_embedding
        e k U cstar α β Bgood (fun x : S => (bw x).T)
        (fun x _ => hT x) hgap heq
    have hcommon :
        ((powers_common_domain k U cstar).card : ℝ) ≥
          (Fintype.card ι : ℝ) * (1 - (1 - β)) := by
      nlinarith
    have hext : ∀ x ∈ Bgood,
        ∃ i, i ∈ (bw x).T ∧ i ∉ powers_common_domain k U cstar := by
      intro x _
      exact powers_bad_witness_exists_mem_not_common_domain
        C k U (e x) (1 - α) (bw x) cstar hcstar
    have hupper : (Bgood.card : ℝ) ≤
        (Fintype.card ι : ℝ) * (1 - β) * (k : ℝ) :=
      powers_middle_good_seeds_real_card_le_embedding
        e k U cstar (1 - β) Bgood (fun x : S => (bw x).T)
        hcommon hext heq
    have hcM : c / (η : ℝ) ≤ M := by
      have hcTwo : c / (η : ℝ) ≤ 2 * c / (η : ℝ) := by
        apply div_le_div_of_nonneg_right
        · linarith
        · exact hηR.le
      apply le_trans hcTwo
      rw [hchoose]
      exact le_max_right _ _
    have hfinal := powers_bad_seed_final_arithmetic
      (η : ℝ) (B.card : ℝ) c (Bgood.card : ℝ)
      ((Fintype.card ι : ℝ) * (1 - β) * (k : ℝ)) M
      hηR hlowerB hupper hcM
    calc
      (B.card : ℝ) ≤
          ((Fintype.card ι : ℝ) * (1 - β) * (k : ℝ)) / (η : ℝ) + M := hfinal
      _ = ((Fintype.card ι : ℝ) * (1 - β) / (η : ℝ)) * (k : ℝ) + M := by
        ring

open scoped NNReal in
open scoped BigOperators in
open scoped Matrix.Module in
private theorem linear_mca_error_powers_bad_seed_card_le
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Fintype F]
    {A : Type} [Finite A] [DecidableEq A] [AddCommGroup A] [Module F A]
    (C : ModuleCode ι F A) (k : ℕ) (δmin η : ℝ≥0)
    (U : Fin (k + 1) → ι → A)
    (_hk : 1 ≤ k) (_hcard : k + 1 ≤ Fintype.card F)
    (hδmin : (δmin : ℝ) =
      (Code.minDist (C : Set (ι → A)) : ℝ) / Fintype.card ι)
    (hη : 0 < η) (hηlt : η < δmin) :
    (Nat.card {x : F //
      CoreDefinitions.IsMCA (CoreDefinitions.univariatePowersGenerator F k) C x U
        (1 - (1 - (δmin : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / (k + 2)))} : ℝ) ≤
      (((Fintype.card ι : ℝ) *
            (1 - (1 - (δmin : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / (k + 1))) /
            (η : ℝ)) * (k : ℝ)) +
        max
          (2 * (k : ℝ) /
            ((η : ℝ) *
              ((1 - (δmin : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / (k + 2)) -
               (1 - (δmin : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / (k + 1)))))
          (((k : ℝ) + 1) * ((k : ℝ) + 2) / (η : ℝ)) := by
  classical
  let := Fintype.ofFinite A
  let P : F → Prop := fun x =>
    CoreDefinitions.IsMCA (CoreDefinitions.univariatePowersGenerator F k) C x U
      (1 - (1 - (δmin : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / (k + 2)))
  let B : Finset F := Finset.univ.filter P
  have hfin := powers_bad_seed_finset_card_le C k δmin η U B
    (fun x => by simp only [B, P, Finset.mem_filter, Finset.mem_univ, true_and])
    _hk _hcard hδmin hη hηlt
  have hcount : (B.card : ℝ) = (Nat.card {x : F // P x} : ℝ) := by
    norm_cast
    rw [← Fintype.card_subtype]
    exact Fintype.card_eq_nat_card
  change (Nat.card {x : F // P x} : ℝ) ≤ _
  rw [← hcount]
  exact hfin

private theorem univariate_powers_generator_code_eq_rs
    {F : Type} [Field F] [Fintype F] (k : ℕ) :
    LinearCode.fromColGenMat (CoreDefinitions.M_G (CoreDefinitions.univariatePowersGenerator F k)) =
      ReedSolomon.code (Function.Embedding.refl F) (k + 1) := by
  simpa [CoreDefinitions.M_G, CoreDefinitions.univariatePowersGenerator,
    Vandermonde.nonsquare] using
    (ReedSolomon.genMatIsVandermonde (F := F) (m := k + 1)
      (α := Function.Embedding.refl F))

private theorem univariate_powers_generator_code_dim
    {F : Type} [Field F] [Fintype F] (k : ℕ)
    (hcard : k + 1 ≤ Fintype.card F) :
    LinearCode.dim
        (LinearCode.fromColGenMat
          (CoreDefinitions.M_G (CoreDefinitions.univariatePowersGenerator F k))) = k + 1 := by
  rw [univariate_powers_generator_code_eq_rs]
  exact ReedSolomon.dim_eq_deg_of_le hcard

private theorem univariate_powers_is_mds_generator
    {F : Type} [Field F] [Fintype F] [DecidableEq F] (k : ℕ) :
    CoreDefinitions.IsMDSGenerator (CoreDefinitions.univariatePowersGenerator F k) := by
  unfold CoreDefinitions.IsMDSGenerator
  rw [univariate_powers_generator_code_eq_rs]
  let : Inhabited F := ⟨0⟩
  exact ReedSolomon.isMDS_code

/-- Bounds the MCA error of the univariate-powers generator below its generalized Johnson
radius. The maximum on the right combines the two nontrivial branches of the source bound. -/
theorem linear_mcaError_powers_le
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Fintype F]
    {A : Type} [Finite A] [DecidableEq A] [AddCommGroup A] [Module F A]
    (C : ModuleCode ι F A) (k : ℕ) (δ_min η δ : ℝ≥0)
    (_hk : 1 ≤ k)
    (_hcard : k + 1 ≤ Fintype.card F)
    (_h_δ_min : (δ_min : ℝ) = (Code.minDist (C : Set (ι → A)) : ℝ) / Fintype.card ι)
    (_hη : 0 < η) (_hη_lt_δ_min : η < δ_min)
    (_hδ : (δ : ℝ) ≤ 1 - (1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / (k + 2))) :
    mcaError (univariatePowersGenerator F k) C (δ : ℝ) ≤
      ENNReal.ofReal
        (((Fintype.card ι : ℝ)
              * (1 - (1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / (k + 1))) / η)
            * ((k : ℝ) / Fintype.card F)
          + max
              (2 * (k : ℝ) /
                ((η : ℝ)
                  * ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / (k + 2))
                      - (1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / (k + 1)))
                  * Fintype.card F))
              (((k : ℝ) + 1) * ((k : ℝ) + 2) / ((η : ℝ) * Fintype.card F))) := by
  classical
  let := Fintype.ofFinite A
  refine le_trans
    (CoreDefinitions.mcaError_mono (univariatePowersGenerator F k) C _hδ) ?_
  unfold mcaError
  refine iSup_le fun U => ?_
  let P : F → Prop := fun x =>
    IsMCA (univariatePowersGenerator F k) C x U
      (1 - (1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / (k + 2)))
  have hcard := linear_mca_error_powers_bad_seed_card_le C k δ_min η U
    _hk _hcard _h_δ_min _hη _hη_lt_δ_min
  change (Nat.card {x : F // P x} : ℝ) ≤ _ at hcard
  have hprob :
      (do
        let x ← PMF.uniformOfFintype F
        pure (P x)) True ≤
        ENNReal.ofReal
          (((((Fintype.card ι : ℝ) *
                (1 - (1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / (k + 1))) /
                (η : ℝ)) * (k : ℝ)) +
              max
                (2 * (k : ℝ) /
                  ((η : ℝ) *
                    ((1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / (k + 2)) -
                     (1 - (δ_min : ℝ) + (η : ℝ)) ^ ((1 : ℝ) / (k + 1)))))
                (((k : ℝ) + 1) * ((k : ℝ) + 2) / (η : ℝ))) /
            (Fintype.card F : ℝ)) := by
    rw [Probability.prob_uniform_eq_ofReal]
    apply ENNReal.ofReal_le_ofReal
    have hcount : ((Finset.univ.filter P).card : ℝ) =
        (Nat.card {x : F // P x} : ℝ) := by
      norm_cast
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    rw [hcount]
    exact div_le_div_of_nonneg_right hcard (by positivity)
  change (do
    let x ← PMF.uniformOfFintype F
    pure (P x)) True ≤ _
  refine le_trans hprob ?_
  apply ENNReal.ofReal_le_ofReal
  apply le_of_eq
  rw [add_div, ← max_div_div_right
    (show (0 : ℝ) ≤ (Fintype.card F : ℝ) by positivity)]
  congr 1
  · ring
  · apply congrArg₂ max <;> rw [div_div]

end CodingTheory
