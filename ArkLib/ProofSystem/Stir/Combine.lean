/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov, Mirco Richter, Poulami Das (Least Authority),
  Aristotle (Harmonic)
-/

import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Cases
import Mathlib.Tactic.LinearCombinationPrime

import ArkLib.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.Curves
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation
import ArkLib.ProofSystem.Stir.ProximityBound
import ArkLib.ToMathlib.Polynomial.EvalExt


/-! Section 4.5 from STIR [ACFY24stir]

## References

* [Arnon, G., Chiesa, A., Fenzi, G., and Yogev, E., *STIR: Reed-Solomon proximity testing
    with fewer queries*][ACFY24stir]
-/

open BigOperators Finset NNReal Code

namespace Combine
variable {m : ℕ}
         {F : Type*} [Field F] [DecidableEq F]
         {ι : Type*}

/-- Fact 4.10
  Geometric series formula in a field, for a unit `r : F`. -/
lemma geometric_sum_units {r : Fˣ} {a : ℕ} :
    ∑ j ∈ range (a + 1), (r ^ j : F) =
    if r = 1 then (a + 1 : F)
    else (1 - r ^ (a + 1)) / (1 - r) := by
  have h_geo_series : ∀ r : F, r ≠ 1 → ∑ j ∈ Finset.range (a + 1), r ^ j =
    (1 - r ^ (a + 1)) / (1 - r) :=
    fun r hr ↦ by
      rw [←neg_div_neg_eq, geom_sum_eq hr]
      ring
  aesop

def ri (dstar : ℕ) (degs : Fin m → ℕ) (r : F) (i : Fin m) : F :=
  let exp := i + ∑ j < i, (dstar - degs j)
  r ^ exp

/-- Definition 4.11.1: `Combine(d*, r, (f_0, d_0), …, (f_{m-1}, d_{m-1}))(x)` is
`sum_{i < m} r_i * f_i(x) * (sum_{l < (d* - d_i + 1)} (r * φ(x))^l)`. -/
def combine
    (φ : ι ↪ F) (dstar : ℕ) (r : F) (fs : Fin m → ι → F) (degs : Fin m → ℕ) (x : ι) : F :=
    ∑ i, (ri dstar degs r i) * (fs i x) * (∑ l ∈ range (dstar - degs i + 1), ((φ x) * r)^l)

omit [DecidableEq F] in
@[simp]
lemma combine_dstar_zero
    {φ : ι ↪ F} {r : F} {fs : Fin m → ι → F} {degs : Fin m → ℕ} :
  combine φ 0 r fs degs =
    ∑ i, (r ^ i.val) • fs i := by aesop (add simp [combine, ri])

private lemma geom_sum_cases (q : F) (n : ℕ) :
  ∑ l ∈ range (n + 1), q ^ l =
    if q ≠ 1 then (1 - q ^ (n + 1)) / (1 - q)
    else (↑(n + 1) : F) := by
  split_ifs with hq
  · rw [←neg_div_neg_eq, geom_sum_eq] <;> aesop
  · aesop

/-- Definition 4.11.2
    Combine(d*, r, (f_0, d_0), …, (f_{m-1}, d_{m-1}))(x) :=
      if (r * φ(x)) = 1 then sum_{i < m} r_i * f_i(x) * (dstar - degree + 1)
      else sum_{i < m} r_i * f_i(x) * (1 - r * φ(x)^(dstar - degree + 1)) / (1 - r * φ(x))
-/
lemma combine_eq_cases {F ι : Type*} [Field F] [DecidableEq F]
    (φ : ι ↪ F) (dstar : ℕ) (r : F) (fs : Fin m → ι → F) (degs : Fin m → ℕ)
    (hdegs : ∀ i, degs i ≤ dstar) :
  combine φ dstar r fs degs =
    fun x ↦
      let q := φ x * r
      if q ≠ 1
      then ∑ i, (ri dstar degs r i) * (fs i x) * (1 - q^(dstar - degs i + 1)) / (1 - q)
      else ∑ i, (ri dstar degs r i) * (fs i x) *  (dstar - degs i + 1) := by
  funext x
  simp only [combine]
  split_ifs with hq
  · simp_rw [geom_sum_cases, if_pos hq]
    apply Finset.sum_congr rfl
    intro i _
    ring
  · simp_rw [geom_sum_cases, if_neg hq]
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.cast_add, Nat.cast_sub (hdegs i), Nat.cast_one]

open Finset
open BigOperators

private def block_size (dstar : ℕ) (degs : Fin m → ℕ) (i : Fin m) := dstar - degs i + 1
private def block_start (dstar : ℕ) (degs : Fin m → ℕ) (i : Fin m) :=
  ∑ j ∈ univ.filter (· < i), block_size dstar degs j
private def total_terms (dstar : ℕ) (degs : Fin m → ℕ) := ∑ i, block_size dstar degs i

private lemma block_start_monotone
  {dstar : ℕ} {degs : Fin m → ℕ} {i j : Fin m} (h : i ≤ j) :
  block_start dstar degs i ≤ block_start dstar degs j := by
  have h_subset :
    Finset.filter (· < i) Finset.univ ⊆ Finset.filter (· < j) Finset.univ := by
      grind
  exact Finset.sum_le_sum_of_subset h_subset

private lemma block_start_zero
  {dstar : ℕ} {degs : Fin m.succ → ℕ} :
  block_start dstar degs 0 = 0 := by simp [block_start]

private lemma block_end_le_block_start
  {dstar : ℕ} {degs : Fin m → ℕ} {i j : Fin m} (hij : i < j) :
  block_start dstar degs i + block_size dstar degs i ≤ block_start dstar degs j := by
  unfold block_start
  rw [add_comm, ← Finset.sum_insert (by simp)]
  apply Finset.sum_le_sum_of_subset
  intro k hk
  simp only [mem_insert, mem_filter, mem_univ, true_and] at hk ⊢
  exact hk.elim (fun hki ↦ hki ▸ hij) (fun hki ↦ lt_trans hki hij)

private lemma block_start_filter_nonempty
  {dstar : ℕ} {degs : Fin m.succ → ℕ} {l : ℕ} :
  (univ.filter (fun j ↦ block_start dstar degs j ≤ l)).Nonempty := by
  exists 0
  simp [block_start]

private lemma block_idx_eq_max
  {dstar : ℕ} {degs : Fin m → ℕ}
  {i : Fin m} {j : Fin (block_size dstar degs i)} :
  Finset.max
    {x | block_start dstar degs x ≤ block_start dstar degs i + j} = i :=
  Function.swap le_antisymm (by norm_num [Finset.le_max]) <| by
  norm_num [Finset.le_max]
  intro a ha
  contrapose! ha
  exact lt_of_lt_of_le (Nat.add_lt_add_left (Fin.is_lt j) _)
    (block_end_le_block_start ha)

omit [DecidableEq F] in
private lemma combine_eq_flat
  (φ : ι ↪ F) (dstar : ℕ) (r : F)
  (fs : Fin m → ι → F) (degs : Fin m → ℕ) :
  combine φ dstar r fs degs = fun x ↦
    ∑ L ∈ range (total_terms dstar degs),
      let i_opt := Finset.max (univ.filter (fun j => block_start dstar degs j ≤ L))
      match i_opt with
      | none => 0
      | some i =>
        let k := L - block_start dstar degs i
        ri dstar degs r i * fs i x * (φ x * r) ^ k := by
  have h_sum_reorganized : ∀ x : ι,
    ∑ L ∈ Finset.range (total_terms dstar degs),
      (let i_opt := Finset.max (Finset.univ.filter (block_start dstar degs · ≤ L))
      match i_opt with
      | Option.none => 0
      | Option.some i =>
        let k := L - block_start dstar degs i
        ri dstar degs r i * fs i x * ((φ x) * r) ^ k) =
          ∑ i : Fin m, ∑ L ∈ Finset.range (block_size dstar degs i),
            ri dstar degs r i * fs i x * ((φ x) * r) ^ L := by
    intro x
    have h_partition : Finset.range (total_terms dstar degs) =
      Finset.biUnion
        Finset.univ
        (fun i =>
          Finset.Ico
            (block_start dstar degs i)
            (block_start dstar degs i + block_size dstar degs i)) := by
      ext L
      simp only [total_terms, block_size, mem_range, block_start,
                  mem_biUnion, mem_univ, mem_Ico, true_and]
      constructor
      · induction m with
        | zero => aesop
        | succ m ih =>
          intro hL
          by_cases h : L < ∑ x : Fin m, (dstar - degs (Fin.castSucc x) + 1)
          · obtain ⟨ a, ha₁, ha₂ ⟩ := ih
              (fun i x => fs i.castSucc x)
              (fun i => degs i.castSucc)
              h
            exists (Fin.castSucc a)
            constructor
            · simp_all only [forall_const, Fin.sum_univ_castSucc]
              convert ha₁ using 1
              simp only [sum_filter, Fin.sum_univ_castSucc, Fin.castSucc_lt_castSucc_iff,
                Nat.add_eq_left, ite_eq_right_iff, Nat.add_eq_zero_iff, one_ne_zero, and_false,
                imp_false, not_lt]
              exact Fin.le_last _
            · aesop
                (add simp [Fin.sum_univ_castSucc, Finset.sum_filter])
                (add safe (by grind))
          · exists (Fin.last m)
            constructor
            · simp_all only [forall_const, Fin.sum_univ_castSucc, not_lt]
              rw [Finset.sum_filter, Fin.sum_univ_castSucc]
              aesop
            · simp_all [Fin.sum_univ_castSucc, Finset.sum_filter]
      · rintro ⟨i, hi⟩
        exact lt_of_lt_of_le hi.2 <| by
          rw [←Finset.sum_sdiff
                (Finset.subset_univ (Finset.filter (· < i) Finset.univ)),
              add_comm]
          simp only [add_le_add_iff_right, Order.add_one_le_iff]
          exact Nat.lt_of_succ_le <| by
            rw [Nat.succ_eq_add_one]
            exact Finset.single_le_sum
              (fun x _ => Nat.zero_le (dstar - degs x + 1)) (by simp)
    rw [h_partition, Finset.sum_biUnion]
    · exact Finset.sum_congr rfl (by {
        intro i _
        apply Finset.sum_bij (fun L hL => L - block_start dstar degs i)
        · simp only [mem_Ico, mem_range, and_imp]
          exact fun a ha₁ ha₂ => by
            rw [tsub_lt_iff_left ha₁]
            exact ha₂
        · simp only [mem_Ico, and_imp]
          intros
          omega
        · simp only [mem_range, mem_Ico, exists_prop]
          exact fun b hb =>
            ⟨block_start dstar degs i + b,
              ⟨by linarith, by linarith⟩,
              by simp +decide⟩
        · simp only [mem_Ico, and_imp]
          intro a ha₁ ha₂
          have hk : a - block_start dstar degs i < block_size dstar degs i := by omega
          have hmax := block_idx_eq_max
            (dstar := dstar) (degs := degs) (i := i)
            (j := ⟨a - block_start dstar degs i, hk⟩)
          rw [show block_start dstar degs i + (a - block_start dstar degs i) = a by omega] at hmax
          rw [hmax]
      })
    · intro i _ j _ hij
      have h_disjoint :
        block_start dstar degs j ≥
          block_start dstar degs i + block_size dstar degs i ∨
        block_start dstar degs i ≥
          block_start dstar degs j + block_size dstar degs j := by
        rcases lt_or_gt_of_ne hij with hij | hji
        · exact Or.inl (block_end_le_block_start hij)
        · exact Or.inr (block_end_le_block_start hji)
      cases h_disjoint
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ ↦ by
          linarith [Finset.mem_Ico.mp hx₁, Finset.mem_Ico.mp hx₂]
      · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ ↦ by
          linarith [ Finset.mem_Ico.mp hx₁, Finset.mem_Ico.mp hx₂ ];
  ext x
  exact (by
    convert h_sum_reorganized x |> Eq.symm using 2
    simp [combine, Finset.mul_sum _ _ _]
    ring!)

omit [DecidableEq F] in
private lemma combine_eq_flat'
  (φ : ι ↪ F) (dstar : ℕ) (r : F)
  (fs : Fin m.succ → ι → F) (degs : Fin m.succ → ℕ) :
  combine φ dstar r fs degs = fun x ↦
    ∑ l : Fin (total_terms dstar degs),
      let i := Finset.max'
          (univ.filter (block_start dstar degs · ≤ l))
          block_start_filter_nonempty
      let k := l - block_start dstar degs i
      ri dstar degs r i * fs i x * (φ x * r) ^ k := by
  rw [combine_eq_flat]
  ext x
  rw [Finset.sum_fin_eq_sum_range]
  exact Finset.sum_equiv (Equiv.refl _) (by simp) <| fun i hi ↦ by
    have h : Finset.max {j | block_start dstar degs j ≤ i} =
      Finset.max' {j | block_start dstar degs j ≤ i} block_start_filter_nonempty := by
      exact (Finset.coe_max' block_start_filter_nonempty).symm
    rw [h]
    simp [Finset.mem_range.mp hi]
    rfl

omit [DecidableEq F] in
private lemma combine_eq_flat''
  (φ : ι ↪ F) (dstar : ℕ) (r : F)
  (fs : Fin m.succ → ι → F) (degs : Fin m.succ → ℕ) :
  combine φ dstar r fs degs = fun x ↦
    ∑ l : Fin (total_terms dstar degs),
      let i := Finset.max'
          (univ.filter (block_start dstar degs · ≤ l))
          block_start_filter_nonempty
      let k := l - block_start dstar degs i
      r ^ (i + ∑ j < i, (dstar - degs j)) *
        fs i x * (φ x * r) ^ k := by
  simpa only [ri] using combine_eq_flat' φ dstar r fs degs

omit [DecidableEq F] in
private lemma combine_eq_flat'''
  (φ : ι ↪ F) (dstar : ℕ) (r : F)
  (fs : Fin m.succ → ι → F) (degs : Fin m.succ → ℕ) :
  combine φ dstar r fs degs = fun x ↦
    ∑ l : Fin (total_terms dstar degs),
      (r ^ l.val) *
      (let i := Finset.max'
          (univ.filter (block_start dstar degs · ≤ l))
          block_start_filter_nonempty
      let k := l - block_start dstar degs i
      fs i x * (φ x) ^ k) := by
  have h_block :
    ∀ l : Fin (Combine.total_terms dstar degs),
      ∃ i : Fin m.succ,
        Combine.block_start dstar degs i ≤ l ∧
          ∀ j : Fin m.succ, Combine.block_start dstar degs j ≤ l → j ≤ i :=
        fun l ↦ by
        use (Finset.max'
          (Finset.univ.filter (Combine.block_start dstar degs · ≤ l))
          ⟨0, by simp [block_start]⟩)
        constructor
        · exact Finset.mem_filter.mp
            (Finset.max'_mem (Finset.univ.filter
              (Combine.block_start dstar degs · ≤ l)) _) |>.2
        · intro j hj
          exact Finset.le_max' _ j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)
  convert Combine.combine_eq_flat'' φ dstar r fs degs using 1
  funext x
  exact Finset.sum_congr rfl <| fun l _ ↦ by
    obtain ⟨i, hi, hi'⟩ := h_block l
    have hi_eq : (Finset.max'
        (filter (Combine.block_start dstar degs · ≤ l) Finset.univ)
        Combine.block_start_filter_nonempty) = i := by
      apply le_antisymm
      · apply Finset.max'_le
        intro j hj
        exact hi' j (Finset.mem_filter.mp hj).2
      · exact Finset.le_max' _ i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
    rw [hi_eq, ←Nat.add_sub_of_le hi]
    ring_nf
    simp only [block_start, Nat.succ_eq_add_one, block_size, sum_add_distrib, sum_const,
      smul_eq_mul, mul_comm, one_mul, add_tsub_cancel_left, mul_assoc, mul_left_comm,
      mul_eq_mul_left_iff]
    rw [show filter _ _ = Finset.Iio i by
      ext j
      simp only [mem_filter, mem_univ, true_and, mem_Iio]]
    left
    simp only [Fin.card_Iio]
    ring

omit [DecidableEq F] in
private lemma combine_eq_flat_final
  (φ : ι ↪ F) (dstar : ℕ) (r : F) (fs : Fin m → ι → F) (degs : Fin m → ℕ) :
  combine φ dstar r fs degs =
    ∑ l : Fin (total_terms dstar degs),
      r ^ (l : ℕ) • fun (x : ι) ↦ (
        let i : WithBot (Fin m) := Finset.max (univ.filter (block_start dstar degs · ≤ l))
        i.elim (0 : F) fun i ↦
          let k := l - block_start dstar degs i
          fs i x * (φ x) ^ k) :=
  match m with
  | 0 => by
    have htotal : total_terms dstar degs = 0 := by simp [total_terms]
    rw [combine_eq_flat, htotal]
    simp [Option.elim]
    rfl
  | Nat.succ m => by
    have h {l : Fin (total_terms dstar degs)} :
      Finset.max {j | block_start dstar degs j ≤ ↑l} =
        Finset.max' {j | block_start dstar degs j ≤ ↑l}
          block_start_filter_nonempty := by
      exact (Finset.coe_max' block_start_filter_nonempty).symm
    rw [combine_eq_flat''' φ dstar r fs degs]
    funext x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun l _ ↦ by
      rw [h]
      rfl

-- def DegCor

/-- Definition 4.12.1
    DegCor(d*, r, f, degree)(x) := f(x) * ( sum_{ l < d* - d + 1 } (r * φ(x))^l ) -/
def degCor
    (φ : ι ↪ F) (dstar degree : ℕ) (r : F) (f : ι → F) (x : ι) : F :=
    f x * ∑ l ∈ range (dstar - degree + 1), ((φ x) * r) ^ l

/-- Definition 4.12.2
    DegCor(d*, r, f, d)(x) := f(x) * conditionalExp(x) -/
lemma degreeCor_eq {F : Type u_1} [Field F] [DecidableEq F] {ι : Type u_2} (φ : ι ↪ F)
    (dstar degree : ℕ) (r : F) (f : ι → F) (hd : degree ≤ dstar) (x : ι) :
  let q := φ x * r
  degCor φ dstar degree r f x =
    if q ≠ 1
    then f x * (1 - q^(dstar - degree + 1)) / (1 - q)
    else f x * (dstar - degree + 1) := by
  convert congr_arg _ (geom_sum_cases (φ x * r) (dstar - degree)) using 1
  · rfl
  · rw [Nat.cast_add, Nat.cast_sub hd, Nat.cast_one]
    split_ifs <;> ring

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι]

open scoped NNReal NNRat in
private lemma glorious_lemma
  {n m : ℕ}
  {δ : ℝ≥0} {rho : ℚ≥0}
  (hδLt : δ < (min (1 - NNReal.sqrt rho)
    (1 - rho - 1 / (↑m))))
  (hrho : rho = n / (↑m : ℚ≥0)) :
  ↑rho + 1 / ↑(m) < 1 - δ := by
  all_goals first | infer_instance | simp_all +decide [lt_tsub_iff_left]
  ring_nf at *
  exact hδLt.2.trans_le' (by norm_cast)

private lemma even_more_glorious_lemma
  {n m : ℕ}
  {δ : ℝ≥0}
  (hm : 0 < m)
  (h : ↑n / ↑(m) + (↑(m))⁻¹ < 1 - δ) : ↑(n + 1) < (1 - δ) * m := by
 rw [← div_lt_iff₀ (by positivity)]
 convert h using 1
 push_cast
 ring

omit [DecidableEq F] [Fintype F] in
open LinearCode Classical ProbabilityTheory ReedSolomon STIR in
lemma master_lemma
    [Nonempty ι]
  {φ : ι ↪ F} {dstar m : ℕ}
  {fs : Fin m → ι → F} {degs : Fin m → ℕ} (hdegs : ∀ i, degs i ≤ dstar)
  {δ : ℝ≥0}
  (hδLt : δ < (min (1 - (ReedSolomon.sqrtRate dstar φ))
    (1 - (rate (code φ dstar)) - 1 / Fintype.card ι)))
  {S : Finset ι}
  (hS_card : (1 - δ) * (Fintype.card ι) ≤ S.card)
  {v : (i : Fin m) → Fin (block_size dstar degs i) → Polynomial F}
  (hv_deg : ∀ i j, (v i j).degree < dstar)
  (hv_eval : ∀ i j, ∀ x ∈ S, (v i j).eval (φ x) = (φ x) ^ j.val * (fs i x))
  (i : Fin m)
  (j : Fin (block_size dstar degs i)) :
  (v i j).degree < degs i + j := by
  have hlt : dstar < Fintype.card ι := by
    by_contra contra
    aesop
      (add simp [ReedSolomon.rateOfLinearCode_eq_min_div, min_eq_right])
  rcases j with ⟨j, hj⟩
  simp only [block_size] at hj
  simp only [gt_iff_lt]
  generalize hj': (dstar - degs i) - j = j'
  revert j
  induction j' with
  | zero =>
    intro j hj hj'
    conv_rhs =>
      rw [show j = (dstar - degs i) by omega]
    rw [←WithBot.coe_natCast,
        show WithBot.some (dstar - degs i) = Nat.cast (dstar - degs i) by rfl,
        ←WithBot.coe_natCast, ←WithBot.coe_add, ←Nat.cast_add,
        Nat.add_sub_of_le (hdegs _)]
    exact hv_deg i ⟨j, hj⟩
  | succ j' ih =>
    intro j hj hj'
    have hj' : j = dstar - degs i - j' - 1 := by omega
    have h_fin : j + 1 < dstar - degs i + 1 := by omega
    specialize ih (j + 1) h_fin (by omega)
    let q : Polynomial F := Polynomial.X * v i ⟨j, hj⟩
    have hq_deg : q.degree < dstar + 1 := by
      simp only [q]
      rw [Polynomial.degree_mul, Polynomial.degree_X, add_comm 1]
      exact WithBot.add_lt_add_right (by simp) (hv_deg i ⟨j, hj⟩)
    have hq_coincide :
      ∀ x ∈ S, q.eval (φ x) = (v i ⟨j + 1, h_fin⟩).eval (φ x) := by
      intro x hx
      simp only [q, Polynomial.eval_mul, Polynomial.eval_X]
      rw [hv_eval i ⟨j, hj⟩ x hx, hv_eval i ⟨j + 1, h_fin⟩ x hx]
      ring
    have hq_coincide :=
      Polynomial.eq_of_eval_eq_degree
        (q := v i ⟨j + 1, h_fin⟩)
        hq_deg (lt_trans (hv_deg _ _) <| by
          rw [WithBot.lt_def]
          right
          exists dstar, (dstar + 1)
          aesop
        ) (Finset.image φ S) (by {
          simp only [Nat.cast_id, ge_iff_le, Order.add_one_le_iff]
          rw [Finset.card_image_of_injective _ φ.injective]
          have h : ↑(rate (code φ dstar)) + 1 / ↑(Fintype.card ι) < 1 - δ :=
            glorious_lemma
              (by simpa using hδLt)
              (by {
                simp only [rate]
                rfl
              })
          have h :=
            le_trans
              (le_of_lt <|
                even_more_glorious_lemma (m := Fintype.card ι)
                  (by simp) (by {
                    rw [ReedSolomon.rateOfLinearCode_eq_min_div,
                        min_eq_left (by omega)] at h
                    simpa using h
                  }))
              hS_card
          norm_cast at h
        })
        (by
          intro y hy
          obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hy
          exact hq_coincide x hx)
    simp only [q] at hq_coincide
    rw [←hq_coincide] at ih
    simp only [Polynomial.degree_mul, Polynomial.degree_X, WithBot.coe_add, WithBot.coe_one] at ih
    rw [←add_assoc, add_comm 1] at ih
    exact (WithBot.add_lt_add_iff_right (by simp)).mp ih

open LinearCode Classical ProbabilityTheory ReedSolomon STIR in
/-- Lemma 4.13
  Let `dstar` be the target degree, `f₁,...,f_{m-1} : ι → F`,
  `0 < degs₁,...,degs_{m-1} < dstar` be degrees and
  `δ ∈ (0, min{(1-BStar(ρ)), (1-ρ-1/|ι|)})` be a distance parameter, then
      Pr_{r ← F} [δᵣ(Combine(dstar,r,(f₁,degs₁),...,(fₘ,degsₘ)))]
                   > err' (dstar, ρ, δ, m * (dstar + 1) - ∑ i degsᵢ) -/
theorem combine_theorem
    {φ : ι ↪ F} {dstar m : ℕ}
  (fs : Fin m → ι → F) (degs : Fin m → ℕ) (hdegs : ∀ i, degs i ≤ dstar)
  (δ : ℝ≥0) (hδPos : δ > 0)
  (hδLt : δ < (min (1 - (ReedSolomon.sqrtRate dstar φ))
                   (1 - (rate (code φ dstar)) - 1 / Fintype.card ι)))
  (hProb : Pr_{ let r ← $ᵖ F}[δᵣ((combine φ dstar r fs degs), (code φ dstar)) ≤ δ] >
    (m * (dstar + 1) - ∑ i, degs i - 1) * ProximityGap.errorBound δ dstar φ) :
    ∃ S : Finset ι, S.card ≥ (1 - δ) * (Fintype.card ι) ∧
      ∃ v : Fin m → ι → F, ∀ i,
        v i ∈ (code φ (degs i)) ∧
          S ⊆ Finset.filter (fun j => v i j = fs i j) Finset.univ := by
  by_cases hempty : Fintype.card ι = 0
  · exists ∅
    simp only [card_empty, CharP.cast_eq_zero, hempty, mul_zero, ge_iff_le, Std.le_refl,
      empty_subset, and_true, true_and]
    rw [Fintype.card_eq_zero_iff] at hempty
    exists (fun i j => False.elim <| hempty.1 j)
    intro i
    simp only [code, Submodule.mem_map]
    exists 0
    simp only [zero_mem, map_zero, true_and]
    ext j
    exact (False.elim <| hempty.1 j)
  · generalize htotal: total_terms dstar degs = total
    rw [Fintype.card_eq_zero_iff, not_isEmpty_iff] at hempty
    rcases total with _ | total
    · rcases m with _ | m
      · aesop
          (add simp [total_terms, block_size])
          (add safe (by exists Finset.univ))
      · aesop (add simp [total_terms, block_size])
    · have proximity_gap :=
        @ProximityGap.correlatedAgreement_affine_curves ι _ _ F _ _ _
          (total_terms dstar degs - 1) dstar φ δ hδPos (by
            aesop (add simp [lt_min_iff, ReedSolomon.sqrtRate]))
      simp only [ProximityGap.δ_ε_correlatedAgreementCurves] at proximity_gap
      specialize proximity_gap
          (fun l (x : ι) ↦ (
            let i : WithBot (Fin m) :=
              Finset.max (univ.filter (block_start dstar degs · ≤ l))
            i.elim (0 : F) fun i ↦
              let k := l - block_start dstar degs i
              fs i x * (φ x) ^ k
          ))
          (by {
            simp only [bind_pure_comp, Functor.map, PMF.bind_apply,
              PMF.uniformOfFintype_apply,
              tsum_fintype, Function.comp_apply, PMF.pure_apply,
              eq_iff_iff, true_iff, mul_ite, mul_one,
              mul_zero, gt_iff_lt] at hProb
            conv at hProb =>
              rhs
              rhs
              ext x
              rw [combine_eq_flat_final φ dstar x]
            simp only [bind_pure_comp, Functor.map, PMF.bind_apply,
              PMF.uniformOfFintype_apply,
              tsum_fintype, Function.comp_apply, PMF.pure_apply,
              eq_iff_iff, true_iff, mul_ite, mul_one,
              mul_zero, gt_iff_lt]
            apply lt_of_le_of_lt
              (b := ((↑m : ENNReal) * (↑dstar + 1) - ↑(∑ i, degs i) - 1) *
                      ↑(ProximityGap.errorBound δ dstar φ))
            · apply mul_le_mul_left
              rw [htotal, add_tsub_cancel_right,
                  Nat.cast_sum, mul_add, mul_one,
                  show (↑m : ENNReal) * ↑dstar
                    = ∑ x : Fin m, ↑dstar by simp,
                  show (↑m : ENNReal) = ∑ x : Fin m, 1 by simp,
                  ←Finset.sum_add_distrib,
                  show ∑ x : Fin m, ((↑dstar : ENNReal) + 1) - ∑ x, ↑(degs x)
                    = ↑(∑ x : Fin m, (dstar + 1)) - ↑(∑ x, degs x)
                      by simp; ring_nf,
                  ←ENNReal.natCast_sub,
                  ←Finset.sum_tsub_distrib _ (fun x _ ↦
                    le_trans (hdegs x) (by omega))]
              conv =>
                rhs
                lhs
                rhs
                rhs
                ext x
                rw [Nat.sub_add_comm (hdegs x)]
              rw [show ∑ x, (dstar - degs x + 1) = total + 1 by
                simpa only [total_terms, block_size] using htotal]
              simp
            · exact lt_of_lt_of_le hProb <| le_of_eq <| by
                congr
                ext x
                congr <;> try (rw [htotal]; omega)
                refine (Fin.heq_fun_iff ?_).mpr ?_
                · aesop (add safe (by omega))
                · aesop
      })
      simp only [jointAgreement, ge_iff_le, SetLike.mem_coe] at proximity_gap
      have proximity_gap :
        ∃ S : Finset ι,
          ↑(#S) ≥ (1 - δ) * ↑(Fintype.card ι)
            ∧ ∃ v : Π i : Fin m, (Fin (block_size dstar degs i) → Polynomial F),
                ∀ i j, (v i j).degree < dstar ∧
                  ∀ x ∈ S, (v i j).eval (φ x) = (φ x) ^ j.val * (fs i x) := by
          obtain ⟨S, hcard, hagr⟩ := proximity_gap
          exists S
          obtain ⟨v, hagr⟩ := hagr
          simp only [ge_iff_le, hcard, true_and]
          simp only [code, Submodule.mem_map, forall_and] at hagr
          rcases hagr with ⟨hagr1, hagr2⟩
          let vaux (i : Fin m) (j : Fin (block_size dstar degs i)) :
            Fin (total_terms dstar degs - 1 + 1) :=
            ⟨block_start dstar degs i + j.val,
            by {
            rw [htotal, add_tsub_cancel_right, ←htotal]
            simp only [block_start, block_size, total_terms]
            rcases i with ⟨i, hi⟩
            rcases j with ⟨j, hj⟩
            apply lt_of_lt_of_le
            · apply Nat.add_lt_add_left (m := dstar - degs ⟨i, hi⟩ + 1)
                (by aesop (add simp [block_size]) (add safe (by omega)))
            · rw [Finset.sum_equiv
                (t := Finset.erase {x : Fin _ | x ≤ ⟨i, hi⟩} ⟨i, hi⟩)
                (g := fun x => (dstar - degs x + 1))
                (Equiv.refl _)
                (by aesop (add safe (by omega)))
                (by aesop), Finset.sum_erase_add _ _ (by simp)]
              exact Finset.sum_le_sum_of_subset (by simp)
          }⟩
          simp only [Polynomial.degreeLT, ge_iff_le, Submodule.mem_iInf, LinearMap.mem_ker,
            Polynomial.lcoeff_apply, evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk] at hagr1
          exists (fun i j => Classical.choose
            (hagr1 (vaux i j)))
          intro i j
          have h_spec := Classical.choose_spec (hagr1 (vaux i j))
          constructor
          · rw [Polynomial.degree_lt_iff_coeff_zero]
            intro m hm
            rw [h_spec.1 m hm]
          · intro x hx
            rw [congrFun h_spec.2 x]
            specialize hagr2 (vaux i j) hx
            simp only [mem_filter, mem_univ, true_and] at hagr2
            rw [hagr2, block_idx_eq_max]
            simp only [Option.elim]
            rw [add_tsub_cancel_left, mul_comm]
      rcases proximity_gap with ⟨S, ⟨hS_card, ⟨v, hv⟩⟩⟩
      have master_lemma :=
        @master_lemma _ _ _ _ hempty
          _ _ _ _ hdegs _
          hδLt _ hS_card (v := v) (fs := fs)
          (fun i j => (hv i j).1)
          (fun i j x hx => (hv i j).2 x hx)
      exists S
      simp only [ge_iff_le, hS_card, true_and]
      have hf : ∀ i, 0 < block_size dstar degs i := by simp [block_size]
      exists (fun i => evalOnPoints φ <| v i (⟨0, hf i⟩))
      intro i
      constructor
      · simp only [code, evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk, Submodule.mem_map]
        exists (v i ⟨0, hf i⟩)
        simp only [Polynomial.degreeLT, ge_iff_le, Submodule.mem_iInf, LinearMap.mem_ker,
          Polynomial.lcoeff_apply, and_true]
        intro j hj
        specialize master_lemma i ⟨0, hf i⟩
        simp only [WithBot.coe_zero, add_zero] at master_lemma
        rw [Polynomial.degree_lt_iff_coeff_zero] at master_lemma
        exact (master_lemma _ hj)
      · intro x hx
        specialize (hv i ⟨0, hf i⟩)
        have hv := hv.2 x hx
        simp only [pow_zero, one_mul] at hv
        apply mem_filter.mpr
        refine ⟨mem_univ x, ?_⟩
        simpa only [evalOnPoints, LinearMap.coe_mk, AddHom.coe_mk] using hv

end Combine
