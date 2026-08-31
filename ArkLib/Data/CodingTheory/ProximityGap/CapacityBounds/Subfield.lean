/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Subfield lower bound for Reed--Solomon correlated agreement

This file proves the CS25 extension-field lower bound by a reciprocal-stack construction and
a first/second-moment estimate over subfield interpolation data.

## Main result

- `subfield_epsCa_lower_bound` is [CS25, Theorem 3].

## References

- [CS25] Crites--Stewart, Theorem 3.
-/

-- Elaborate the legacy proximity API through its public Matrix aliases under Lean 4.33.
set_option backward.isDefEq.respectTransparency false

namespace CodingTheory

open scoped NNReal
open CoreDefinitions ProximityGap

section ReedSolomon

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The piecewise analytic factor in `subfield_epsCa_lower_bound`:
`exp x` for `x ≤ 3/2`, and `exp (2√x) / √(2π⌊√x⌋)` otherwise. -/
noncomputable def subfieldCaFactor (x : ℝ) : ℝ :=
  if x ≤ 3 / 2 then Real.exp x
  else Real.exp (2 * Real.sqrt x) / Real.sqrt (2 * Real.pi * ⌊Real.sqrt x⌋₊)

private def subfield_ca_divisible_degree_lt
    (B : Subfield F) (k : ℕ) (H : Polynomial B) :=
  {r : Polynomial.degreeLT B k // H ∣ (r.1 : Polynomial B)}

private structure SubfieldCaPairWitness
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (a : F)
    (S T : Finset ι) where
  y : ι → B
  α : F
  p : Polynomial.degreeLT B k
  q : Polynomial.degreeLT B k
  p_agree : ∀ i, i ∉ S → p.1.eval (domainB i) = y i
  q_agree : ∀ i, i ∉ T → q.1.eval (domainB i) = y i
  p_value : Polynomial.aeval a p.1 = α
  q_value : Polynomial.aeval a q.1 = α

private structure SubfieldCaWitnessData
    (domain : ι ↪ F) (k : ℕ) (δ : NNReal) (B : Subfield F)
    (u : Fin 2 → ι → F) (G : Finset F) : Prop where
  not_joint : ¬ Code.jointProximity
    (C := (ReedSolomon.code domain k : Set (ι → F))) (u := u) δ
  good_subset : G ⊆ Finset.univ.filter (fun γ : F =>
    Code.relDistFromCode (u 0 + γ • u 1)
      (ReedSolomon.code domain k : Set (ι → F)) ≤ δ)
  card_lower :
    ENNReal.ofReal
      (1 - (Fintype.card F * (Nat.card B : ℝ) ^
          ((Fintype.card ι : ℝ) *
            (1 - (k : ℝ) / Fintype.card ι - (δ : ℝ)))
          * subfieldCaFactor
            ((δ : ℝ) * (1 - δ) * (Fintype.card ι) ^ 2 / Nat.card B)) /
        Nat.choose (Fintype.card ι)
          ⌊(δ : ℝ) * Fintype.card ι⌋₊) ≤
      ((((G.card : NNReal) / (Fintype.card F : NNReal)) : NNReal) : ENNReal)

omit [Fintype F] [DecidableEq F] in
private theorem exists_not_mem_proper_subfield (B : Subfield F) (hB : B < ⊤) :
    ∃ a : F, a ∉ B := by
  obtain ⟨a, _ha_top, ha_not⟩ := SetLike.exists_of_lt hB
  exact ⟨a, ha_not⟩

omit [Fintype F] [DecidableEq F] in
private theorem exists_subfield_multiplicative_generator [Finite F] :
    ∃ g : Fˣ, ∀ y : Fˣ, y ∈ Submonoid.powers g := by
  exact IsCyclic.exists_monoid_generator

omit [Fintype F] [DecidableEq F] in
private theorem exists_subfield_primitive_element [Finite F] (B : Subfield F) :
    ∃ a : F, IntermediateField.adjoin B ({a} : Set F) = ⊤ := by
  exact Field.exists_primitive_element_of_finite_top B F

open scoped BigOperators in
private theorem finite_support_second_moment
    {Ω : Type} [Fintype Ω] (X : Ω → ℕ) :
    (∑ ω : Ω, (X ω : ℝ)) ^ 2 ≤
      ((Finset.univ.filter (fun ω : Ω => 0 < X ω)).card : ℝ) *
        ∑ ω : Ω, (X ω : ℝ) ^ 2 := by
  classical
  let s : Finset Ω := Finset.univ.filter (fun ω => 0 < X ω)
  have hsum : (∑ ω ∈ s, (X ω : ℝ)) = ∑ ω : Ω, (X ω : ℝ) := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro ω _ hω
    have hz : X ω = 0 := Nat.eq_zero_of_not_pos (by
      simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hω)
    simp only [hz, Nat.cast_zero]
  have hsq : (∑ ω ∈ s, (X ω : ℝ) ^ 2) = ∑ ω : Ω, (X ω : ℝ) ^ 2 := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro ω _ hω
    have hz : X ω = 0 := Nat.eq_zero_of_not_pos (by
      simpa only [s, Finset.mem_filter, Finset.mem_univ, true_and] using hω)
    simp only [hz, Nat.cast_zero]
    norm_num
  rw [← hsum, ← hsq]
  exact sq_sum_le_card_mul_sum_sq

omit [Nonempty ι] [DecidableEq ι] in
private theorem fold_density_le_eps_ca_of_not_joint_proximity
    (C : Set (ι → F)) (δ_fld δ_int : NNReal) (u : Fin 2 → ι → F)
    (hnot : ¬ Code.jointProximity (C := C) (u := u) δ_int) :
    ((((Finset.univ.filter (fun γ : F =>
        Code.relDistFromCode (u 0 + γ • u 1) C ≤ δ_fld)).card : NNReal) /
      (Fintype.card F : NNReal) : NNReal) : ENNReal) ≤
      _root_.ProximityGap.epsCa (F := F) (A := F) C δ_fld δ_int := by
  classical
  have hcardF_ne : (Fintype.card F : NNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [ENNReal.coe_div hcardF_ne]
  rw [← Probability.prob_uniform_eq_card_filter_div_card]
  unfold _root_.ProximityGap.epsCa
  calc
    (do
      let γ ← PMF.uniformOfFintype F
      pure (Code.relDistFromCode (u 0 + γ • u 1) C ≤ δ_fld)) True =
        (if Code.jointProximity (C := C) (u := u) δ_int then (0 : ENNReal)
        else (do
          let γ ← PMF.uniformOfFintype F
          pure (Code.relDistFromCode (u 0 + γ • u 1) C ≤ δ_fld)) True) :=
      (if_neg hnot).symm
    _ ≤ ⨆ w : Fin 2 → ι → F,
        if Code.jointProximity (C := C) (u := w) δ_int then (0 : ENNReal)
        else (do
          let γ ← PMF.uniformOfFintype F
          pure (Code.relDistFromCode (w 0 + γ • w 1) C ≤ δ_fld)) True :=
      @le_iSup ENNReal (Fin 2 → ι → F)
        ENNReal.instCompleteLinearOrder.toCompleteLattice _ u

open scoped BigOperators in
private noncomputable def subfield_ca_bessel_partial (x : ℝ) (m : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (m + 1), x ^ s / ((s.factorial : ℝ) ^ 2)

open scoped BigOperators in
private noncomputable def subfield_ca_collision_divisor
    (B : Subfield F) (domainB : ι ↪ B) (a : F)
    (S T : Finset ι) : Polynomial B :=
  minpoly B a *
    ∏ i ∈ (Finset.univ \ (S ∪ T)),
      (Polynomial.X - Polynomial.C (domainB i))

private def subfield_ca_pair_parameters
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (a : F)
    (S T : Finset ι) :=
  Polynomial.degreeLT B k ×
    subfield_ca_divisible_degree_lt B k
      (subfield_ca_collision_divisor B domainB a S T) ×
    (↥(S ∩ T) → B)

private noncomputable def subfield_ca_error_sets (δ : NNReal) : Finset (Finset ι) :=
  (Finset.univ : Finset ι).powersetCard ⌊(δ : ℝ) * Fintype.card ι⌋₊

omit [Nonempty ι] [DecidableEq ι] in
private theorem subfield_ca_error_sets_card (δ : NNReal) :
    (subfield_ca_error_sets (ι := ι) δ).card =
      Nat.choose (Fintype.card ι) ⌊(δ : ℝ) * Fintype.card ι⌋₊ := by
  classical
  simp only [subfield_ca_error_sets, Finset.card_powersetCard, Finset.card_univ]

omit [Nonempty ι] [DecidableEq ι] in
private theorem subfield_ca_error_sets_mem_iff_card (δ : NNReal) (S : Finset ι) :
    S ∈ subfield_ca_error_sets (ι := ι) δ ↔
      S.card = ⌊(δ : ℝ) * Fintype.card ι⌋₊ := by
  classical
  simp only [subfield_ca_error_sets, Finset.mem_powersetCard, Finset.subset_univ, true_and]

private def subfield_ca_event (B : Subfield F) (domainB : ι ↪ B)
    (k : ℕ) (a : F) (S : Finset ι) (y : ι → B) (α : F) : Prop :=
  ∃ p : Polynomial B,
    p.degree < k ∧
    (∀ i, i ∉ S → p.eval (domainB i) = y i) ∧
    Polynomial.aeval a p = α

private noncomputable def subfield_ca_event_fiber
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (a : F) (S : Finset ι) :
    Finset ((ι → B) × F) := by
  classical
  letI := Fintype.ofFinite B
  exact Finset.univ.filter
    (fun z => subfield_ca_event B domainB k a S z.1 z.2)

private noncomputable def subfield_ca_event_indicator
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (a : F)
    (S : Finset ι) (y : ι → B) (α : F) : ℝ := by
  classical
  exact if subfield_ca_event B domainB k a S y α then 1 else 0

private theorem subfield_ca_factor_nonneg (x : ℝ) : 0 ≤ subfieldCaFactor x := by
  rw [subfieldCaFactor]
  split_ifs
  · exact Real.exp_nonneg x
  · exact div_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg _)

private noncomputable def subfield_ca_multiplicity
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (δ : NNReal)
    (a : F) (y : ι → B) (α : F) : ℕ := by
  classical
  exact (subfield_ca_error_sets (ι := ι) δ).filter
    (fun S => subfield_ca_event B domainB k a S y α) |>.card

open scoped BigOperators in
private noncomputable def subfield_ca_first_moment
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (δ : NNReal)
    (a : F) : ℕ := by
  classical
  letI := Fintype.ofFinite B
  exact ∑ y : ι → B, ∑ α : F,
    subfield_ca_multiplicity B domainB k δ a y α

private noncomputable def subfield_ca_good_scalars
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (δ : NNReal)
    (a : F) (y : ι → B) : Finset F := by
  classical
  exact Finset.univ.filter
    (fun α : F => 0 < subfield_ca_multiplicity B domainB k δ a y α)

open scoped BigOperators in
private noncomputable def subfield_ca_overlap_sum (n f b : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (f + 1),
    ((Nat.choose f s : ℝ) * (Nat.choose (n - f) s : ℝ)) / (b : ℝ) ^ s

private noncomputable def subfield_ca_pair_event_fiber
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (a : F)
    (S T : Finset ι) : Finset ((ι → B) × F) := by
  classical
  letI := Fintype.ofFinite B
  exact Finset.univ.filter (fun z =>
    subfield_ca_event B domainB k a S z.1 z.2 ∧
      subfield_ca_event B domainB k a T z.1 z.2)

private noncomputable def subfield_ca_pair_fiber_to_witness
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (a : F)
    (S T : Finset ι) :
    ↥(subfield_ca_pair_event_fiber B domainB k a S T) →
      SubfieldCaPairWitness B domainB k a S T := by
  classical
  letI := Fintype.ofFinite B
  intro z
  have hz :
      subfield_ca_event B domainB k a S z.1.1 z.1.2 ∧
        subfield_ca_event B domainB k a T z.1.1 z.1.2 := by
    simpa only [subfield_ca_pair_event_fiber, Finset.mem_filter,
      Finset.mem_univ, true_and] using z.2
  let p : Polynomial B := Classical.choose hz.1
  let q : Polynomial B := Classical.choose hz.2
  have hp := Classical.choose_spec hz.1
  have hq := Classical.choose_spec hz.2
  exact
    { y := z.1.1
      α := z.1.2
      p := ⟨p, Polynomial.mem_degreeLT.mpr hp.1⟩
      q := ⟨q, Polynomial.mem_degreeLT.mpr hq.1⟩
      p_agree := hp.2.1
      q_agree := hq.2.1
      p_value := hp.2.2
      q_value := hq.2.2 }

omit [Nonempty ι] [DecidableEq F] in
private theorem subfield_ca_pair_fiber_to_witness_injective
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (a : F)
    (S T : Finset ι) :
    Function.Injective
      (subfield_ca_pair_fiber_to_witness B domainB k a S T) := by
  classical
  let := Fintype.ofFinite B
  intro z w hzw
  have hcoords := congrArg
    (fun u : SubfieldCaPairWitness B domainB k a S T => (u.y, u.α)) hzw
  change (z.1.1, z.1.2) = (w.1.1, w.1.2) at hcoords
  apply Subtype.ext
  exact hcoords

private def subfield_ca_reciprocal_stack (domain : ι ↪ F) (B : Subfield F)
    (a : F) (y : ι → B) : Fin 2 → ι → F :=
  fun j i =>
    if j = 0 then (y i : F) / (domain i - a)
    else -(1 : F) / (domain i - a)

omit [DecidableEq ι] in
private theorem subfield_ca_good_scalars_subset_fold_close
    (B : Subfield F) (domain : ι ↪ F) (domainB : ι ↪ B)
    (k : ℕ) (δ : NNReal) (a : F) (y : ι → B)
    (_hint : ((⌊(δ : ℝ) * Fintype.card ι⌋₊ : ℝ)) =
      (δ : ℝ) * Fintype.card ι)
    (ha : a ∉ B)
    (hdom : ∀ i, (domainB i : F) = domain i) :
    subfield_ca_good_scalars B domainB k δ a y ⊆
      Finset.univ.filter (fun α : F =>
        Code.relDistFromCode
          ((subfield_ca_reciprocal_stack domain B a y) 0 +
            α • (subfield_ca_reciprocal_stack domain B a y) 1)
          (ReedSolomon.code domain k : Set (ι → F)) ≤ δ) := by
  classical
  let := Fintype.ofFinite B
  intro α hα
  have hαpos : 0 < subfield_ca_multiplicity B domainB k δ a y α := by
    simpa only [subfield_ca_good_scalars, Finset.mem_filter,
      Finset.mem_univ, true_and] using hα
  unfold subfield_ca_multiplicity at hαpos
  obtain ⟨S, hS⟩ := Finset.card_pos.mp hαpos
  have hSerr : S ∈ subfield_ca_error_sets (ι := ι) δ :=
    (Finset.mem_filter.mp hS).1
  have hSevent : subfield_ca_event B domainB k a S y α :=
    (Finset.mem_filter.mp hS).2
  obtain ⟨p, hpdeg, hpagree, hpa⟩ := hSevent
  have hScard : S.card = ⌊(δ : ℝ) * Fintype.card ι⌋₊ :=
    (subfield_ca_error_sets_mem_iff_card δ S).mp hSerr
  let pF : Polynomial F := p.map B.subtype
  have hpFa : pF.eval a = α := by
    change (p.map B.subtype).eval a = α
    rw [Polynomial.eval_map, ← Subfield.algebraMap_ofSubfield B]
    exact hpa
  let r : Polynomial F := pF - Polynomial.C α
  let q : Polynomial F := r /ₘ (Polynomial.X - Polynomial.C a)
  have hreval : r.eval a = 0 := by
    simp only [r, Polynomial.eval_sub, hpFa, Polynomial.eval_C, sub_self]
  have hroot : Polynomial.IsRoot r a := hreval
  have hfactor : (Polynomial.X - Polynomial.C a) * q = r := by
    change (Polynomial.X - Polynomial.C a) *
      (r /ₘ (Polynomial.X - Polynomial.C a)) = r
    exact Polynomial.mul_divByMonic_eq_iff_isRoot.mpr hroot
  have hqdeg : q.degree < k := by
    by_cases hr0 : r = 0
    · have hq0 : q = 0 := by
        change r /ₘ (Polynomial.X - Polynomial.C a) = 0
        rw [hr0, Polynomial.zero_divByMonic]
      rw [hq0, Polynomial.degree_zero]
      exact WithBot.bot_lt_coe k
    · have hpFpos : (0 : WithBot ℕ) < pF.degree := by
        by_contra hnpos
        have hpFle : pF.degree ≤ 0 := le_of_not_gt hnpos
        have hpFC : pF = Polynomial.C (pF.coeff 0) :=
          Polynomial.degree_le_zero_iff.mp hpFle
        have hcoeff : pF.coeff 0 = α := by
          rw [hpFC, Polynomial.eval_C] at hpFa
          exact hpFa
        apply hr0
        calc
          r = pF - Polynomial.C α := rfl
          _ = Polynomial.C (pF.coeff 0) - Polynomial.C α :=
            congrArg (fun z : Polynomial F => z - Polynomial.C α) hpFC
          _ = 0 := by rw [hcoeff, sub_self]
      have hq_lt_r : q.degree < r.degree := by
        exact Polynomial.degree_divByMonic_lt r
          (Polynomial.X - Polynomial.C a) hr0
          (by rw [Polynomial.degree_X_sub_C]; exact WithBot.coe_pos.mpr Nat.zero_lt_one)
      have hrdeg : r.degree = pF.degree :=
        Polynomial.degree_sub_C hpFpos
      have hpFdeg : pF.degree = p.degree :=
        Polynomial.degree_map_eq_of_injective B.subtype_injective p
      rw [hrdeg, hpFdeg] at hq_lt_r
      exact hq_lt_r.trans hpdeg
  let u : Fin 2 → ι → F := subfield_ca_reciprocal_stack domain B a y
  let c : ι → F := ReedSolomon.evalOnPoints domain q
  have hc : c ∈ ReedSolomon.code domain k :=
    ReedSolomon.evalOnPoints_mem_code_of_degree_lt hqdeg
  have hden (i : ι) : domain i - a ≠ 0 := by
    intro hz
    have heq : domain i = a := sub_eq_zero.mp hz
    apply ha
    rw [← heq, ← hdom i]
    exact (domainB i).property
  have hpFeval (i : ι) (hi : i ∉ S) : pF.eval (domain i) = (y i : F) := by
    rw [← hdom i]
    change (p.map B.subtype).eval (domainB i : F) = (y i : F)
    rw [Polynomial.eval_map]
    change p.eval₂ B.subtype (B.subtype (domainB i)) = B.subtype (y i)
    rw [Polynomial.eval₂_at_apply]
    exact congrArg Subtype.val (hpagree i hi)
  have hqeval (i : ι) (hi : i ∉ S) :
      q.eval (domain i) = ((y i : F) - α) / (domain i - a) := by
    have heval := congrArg (fun z : Polynomial F => z.eval (domain i)) hfactor
    have heval' : (domain i - a) * q.eval (domain i) = (y i : F) - α := by
      simpa only [Polynomial.eval_mul, Polynomial.eval_sub,
        Polynomial.eval_X, Polynomial.eval_C, hpFeval i hi,
        r] using heval
    apply (eq_div_iff (hden i)).2
    simpa only [mul_comm] using heval'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  apply le_trans (Code.relDistFromCode_le_relDist_to_mem
    (u 0 + α • u 1) c hc)
  have hpair : Code.relHammingDist (u 0 + α • u 1) c ≤ δ := by
    rw [Code.pairRelDist_le_iff_pairDist_le]
    rw [Code.hammingDist_eq_disagreementCols_card]
    calc
      (Code.disagreementCols (u 0 + α • u 1) c).card ≤ S.card := by
        apply Finset.card_le_card
        intro i hi
        by_contra hiS
        apply (Code.mem_disagreementCols.mp hi)
        change subfield_ca_reciprocal_stack domain B a y 0 i +
            α * subfield_ca_reciprocal_stack domain B a y 1 i =
          q.eval (domain i)
        unfold subfield_ca_reciprocal_stack
        rw [if_pos rfl, if_neg (by decide : (1 : Fin 2) ≠ 0)]
        rw [hqeval i hiS]
        field_simp [hden i]
        ring
      _ = ⌊(δ : ℝ) * Fintype.card ι⌋₊ := hScard
  exact_mod_cast hpair

omit [DecidableEq ι] [Fintype F] in
private theorem subfield_ca_reciprocal_stack_not_joint
    (domain : ι ↪ F) (B : Subfield F) (k : ℕ) (δ : NNReal)
    (a : F) (y : ι → B) (ha : a ∉ B)
    (hdom : ∀ i, domain i ∈ B)
    (hint : ((⌊(δ : ℝ) * Fintype.card ι⌋₊ : ℝ)) =
      (δ : ℝ) * Fintype.card ι)
    (hδ_one : (δ : ℝ) < 1)
    (hkf : k + ⌊(δ : ℝ) * Fintype.card ι⌋₊ < Fintype.card ι) :
    ¬ Code.jointProximity
      (C := (ReedSolomon.code domain k : Set (ι → F)))
      (u := subfield_ca_reciprocal_stack domain B a y) δ := by
  classical
  let u : Fin 2 → ι → F := subfield_ca_reciprocal_stack domain B a y
  intro hjoint
  rw [← Code.jointAgreement_iff_jointProximity] at hjoint
  obtain ⟨T, hTcard, v, hv⟩ := hjoint
  have hδle : δ ≤ 1 := le_of_lt (by exact_mod_cast hδ_one)
  have hTcardR0 : ((((1 - δ) * (Fintype.card ι : NNReal)) : NNReal) : ℝ) ≤
      (T.card : ℝ) := by
    exact_mod_cast hTcard
  have hTcardR : (1 - (δ : ℝ)) * Fintype.card ι ≤ (T.card : ℝ) := by
    rw [NNReal.coe_mul, NNReal.coe_sub hδle] at hTcardR0
    norm_num at hTcardR0
    exact hTcardR0
  have hf_le : ⌊(δ : ℝ) * Fintype.card ι⌋₊ ≤ Fintype.card ι := by omega
  have hTcardNatR : ((Fintype.card ι -
      ⌊(δ : ℝ) * Fintype.card ι⌋₊ : ℕ) : ℝ) ≤ (T.card : ℝ) := by
    rw [Nat.cast_sub hf_le, hint]
    nlinarith only [hTcardR]
  have hTcardNat : Fintype.card ι - ⌊(δ : ℝ) * Fintype.card ι⌋₊ ≤ T.card := by
    exact_mod_cast hTcardNatR
  have hkT : k < T.card := by omega
  have hv1 : v (1 : Fin 2) ∈ ReedSolomon.code domain k := (hv (1 : Fin 2)).1
  obtain ⟨p, hpdeg, hpeval⟩ := (ReedSolomon.mem_code_iff_eval).mp hv1
  have hden (i : ι) : domain i - a ≠ 0 := by
    intro hzero
    have heq : domain i = a := sub_eq_zero.mp hzero
    apply ha
    rw [← heq]
    exact hdom i
  have hpagree (i : ι) (hi : i ∈ T) : p.eval (domain i) = u 1 i := by
    have hvi : v (1 : Fin 2) i = u 1 i :=
      (Finset.mem_filter.mp ((hv (1 : Fin 2)).2 hi)).2
    exact (hpeval i).trans hvi
  let Q : Polynomial F := (Polynomial.X - Polynomial.C a) * p + 1
  have hQroot (i : ι) (hi : i ∈ T) : Q.eval (domain i) = 0 := by
    dsimp only [Q]
    rw [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, hpagree i hi, Polynomial.eval_one]
    dsimp only [u, subfield_ca_reciprocal_stack]
    rw [if_neg (by decide : (1 : Fin 2) ≠ 0)]
    field_simp [hden i]
    ring
  have hXne : (Polynomial.X - Polynomial.C a : Polynomial F) ≠ 0 := by
    intro hzero
    have hc := congrArg (fun z : Polynomial F => z.coeff 1) hzero
    simp at hc
  have hQNat : Q.natDegree ≤ k := by
    by_cases hp0 : p = 0
    · subst p
      simp only [Q, mul_zero, zero_add, Polynomial.natDegree_one]
      omega
    · have hpNat : p.natDegree < k :=
        (Polynomial.natDegree_lt_iff_degree_lt hp0).mpr hpdeg
      apply le_trans (Polynomial.natDegree_add_le
        ((Polynomial.X - Polynomial.C a) * p) 1)
      rw [Polynomial.natDegree_mul hXne hp0, Polynomial.natDegree_X_sub_C,
        Polynomial.natDegree_one]
      omega
  have hQzero : Q = 0 := by
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero'
      Q (T.map domain)
    · intro x hx
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
      exact hQroot i hi
    · rw [Finset.card_map]
      exact lt_of_le_of_lt hQNat hkT
  have hcontra := congrArg (fun z : Polynomial F => z.eval a) hQzero
  have hone : (1 : F) = 0 := by
    simpa only [Q, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_X, Polynomial.eval_C, sub_self, zero_mul, zero_add,
      Polynomial.eval_one, Polynomial.eval_zero] using hcontra
  exact one_ne_zero hone

open scoped BigOperators in
private noncomputable def subfield_ca_second_moment
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (δ : NNReal)
    (a : F) : ℝ := by
  classical
  letI := Fintype.ofFinite B
  exact ∑ y : ι → B, ∑ α : F,
    (subfield_ca_multiplicity B domainB k δ a y α : ℝ) ^ 2

private noncomputable def subfield_ca_support
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (δ : NNReal)
    (a : F) : Finset ((ι → B) × F) := by
  classical
  letI := Fintype.ofFinite B
  exact Finset.univ.filter (fun z =>
    0 < subfield_ca_multiplicity B domainB k δ a z.1 z.2)

omit [Nonempty ι] [DecidableEq ι] in
private theorem subfield_ca_witness_data_eps_ca
    (domain : ι ↪ F) (k : ℕ) (δ : NNReal) (B : Subfield F)
    (u : Fin 2 → ι → F) (G : Finset F)
    (h : SubfieldCaWitnessData domain k δ B u G) :
    ENNReal.ofReal
      (1 - (Fintype.card F * (Nat.card B : ℝ) ^
          ((Fintype.card ι : ℝ) *
            (1 - (k : ℝ) / Fintype.card ι - (δ : ℝ)))
          * subfieldCaFactor
            ((δ : ℝ) * (1 - δ) * (Fintype.card ι) ^ 2 / Nat.card B)) /
        Nat.choose (Fintype.card ι)
          ⌊(δ : ℝ) * Fintype.card ι⌋₊) ≤
      epsCa (F := F) (A := F)
        ((ReedSolomon.code domain k : Set (ι → F))) δ δ := by
  calc
    ENNReal.ofReal
        (1 - (Fintype.card F * (Nat.card B : ℝ) ^
            ((Fintype.card ι : ℝ) *
              (1 - (k : ℝ) / Fintype.card ι - (δ : ℝ)))
            * subfieldCaFactor
              ((δ : ℝ) * (1 - δ) * (Fintype.card ι) ^ 2 / Nat.card B)) /
          Nat.choose (Fintype.card ι)
            ⌊(δ : ℝ) * Fintype.card ι⌋₊) ≤
        ((((G.card : NNReal) / (Fintype.card F : NNReal)) : NNReal) : ENNReal) :=
      h.card_lower
    _ ≤ ((((Finset.univ.filter (fun γ : F =>
          Code.relDistFromCode (u 0 + γ • u 1)
            (ReedSolomon.code domain k : Set (ι → F)) ≤ δ)).card : NNReal) /
          (Fintype.card F : NNReal) : NNReal) : ENNReal) := by
      apply ENNReal.coe_le_coe.mpr
      apply div_le_div_of_nonneg_right
      · exact_mod_cast Finset.card_le_card h.good_subset
      · exact zero_le
    _ ≤ epsCa (F := F) (A := F)
        ((ReedSolomon.code domain k : Set (ι → F))) δ δ :=
      fold_density_le_eps_ca_of_not_joint_proximity
        (ReedSolomon.code domain k : Set (ι → F)) δ δ u h.not_joint

open scoped BigOperators in
private theorem subfield_ca_bessel_partial_le_exp
    (x : ℝ) (m : ℕ) (hx : 0 ≤ x) :
    subfield_ca_bessel_partial x m ≤ Real.exp x := by
  unfold subfield_ca_bessel_partial
  calc
    (∑ s ∈ Finset.range (m + 1), x ^ s / ((s.factorial : ℝ) ^ 2)) ≤
        ∑ s ∈ Finset.range (m + 1), x ^ s / (s.factorial : ℝ) := by
      apply Finset.sum_le_sum
      intro s hs
      have hpow : 0 ≤ x ^ s := pow_nonneg hx s
      have hfac : (1 : ℝ) ≤ s.factorial := by exact_mod_cast s.factorial_pos
      have hfacpos : (0 : ℝ) < s.factorial := lt_of_lt_of_le zero_lt_one hfac
      rw [pow_two]
      exact div_le_div_of_nonneg_left hpow hfacpos (by
        nlinarith [hfac])
    _ ≤ Real.exp x := Real.sum_le_exp_of_nonneg hx (m + 1)

private theorem subfield_ca_bessel_partial_le_factor_small
    (x : ℝ) (m : ℕ) (hx : 0 ≤ x) (hxle : x ≤ 3 / 2) :
    subfield_ca_bessel_partial x m ≤ subfieldCaFactor x := by
  rw [subfieldCaFactor, if_pos hxle]
  exact subfield_ca_bessel_partial_le_exp x m hx

omit [DecidableEq F] in
private theorem subfield_ca_card_eq_pow_finrank (B : Subfield F) :
    Fintype.card F = Nat.card B ^ Module.finrank B F := by
  rw [Fintype.card_eq_nat_card]
  exact Module.natCard_eq_pow_finrank

open scoped BigOperators in
omit [Nonempty ι] [Fintype F] [DecidableEq F] in
private theorem subfield_ca_collision_divisor_dvd_aeval_zero
    (B : Subfield F) (domainB : ι ↪ B) (a : F)
    (S T : Finset ι) (r : Polynomial B)
    (hr : subfield_ca_collision_divisor B domainB a S T ∣ r) :
    Polynomial.aeval a r = 0 := by
  apply (minpoly.dvd_iff).mp
  apply dvd_trans (dvd_mul_right (minpoly B a)
    (∏ i ∈ (Finset.univ \ (S ∪ T)),
      (Polynomial.X - Polynomial.C (domainB i))))
  exact hr

open scoped BigOperators in
omit [Nonempty ι] [Fintype F] [DecidableEq F] in
private theorem subfield_ca_collision_divisor_dvd_eval_zero
    (B : Subfield F) (domainB : ι ↪ B) (a : F)
    (S T : Finset ι) (r : Polynomial B)
    (hr : subfield_ca_collision_divisor B domainB a S T ∣ r)
    (i : ι) (hi : i ∉ S ∪ T) :
    r.eval (domainB i) = 0 := by
  have hiU : i ∈ Finset.univ \ (S ∪ T) :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hi⟩
  have hfacprod :
      (Polynomial.X - Polynomial.C (domainB i)) ∣
        ∏ j ∈ (Finset.univ \ (S ∪ T)),
          (Polynomial.X - Polynomial.C (domainB j)) :=
    Finset.dvd_prod_of_mem
      (fun j => Polynomial.X - Polynomial.C (domainB j)) hiU
  have hfacH :
      (Polynomial.X - Polynomial.C (domainB i)) ∣
        subfield_ca_collision_divisor B domainB a S T := by
    unfold subfield_ca_collision_divisor
    exact dvd_mul_of_dvd_right hfacprod (minpoly B a)
  have hfacr :
      (Polynomial.X - Polynomial.C (domainB i)) ∣ r :=
    dvd_trans hfacH hr
  rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def] at hfacr
  exact hfacr

open scoped BigOperators in
omit [Nonempty ι] [Fintype F] [DecidableEq F] in
private theorem subfield_ca_collision_divisor_monic [Finite F]
    (B : Subfield F) (domainB : ι ↪ B) (a : F)
    (S T : Finset ι) :
    (subfield_ca_collision_divisor B domainB a S T).Monic := by
  unfold subfield_ca_collision_divisor
  apply Polynomial.Monic.mul
  · exact minpoly.monic (Algebra.IsIntegral.isIntegral a)
  · exact Polynomial.monic_prod_X_sub_C domainB
      (Finset.univ \ (S ∪ T))

open scoped BigOperators in
omit [Nonempty ι] [Fintype F] [DecidableEq F] in
private theorem subfield_ca_collision_divisor_nat_degree_card [Finite F]
    (B : Subfield F) (domainB : ι ↪ B) (a : F)
    (S T : Finset ι)
    (hmin : (minpoly B a).natDegree = Module.finrank B F) :
    (subfield_ca_collision_divisor B domainB a S T).natDegree =
      Module.finrank B F + (Finset.univ \ (S ∪ T)).card := by
  unfold subfield_ca_collision_divisor
  have hmp : (minpoly B a).Monic :=
    minpoly.monic (Algebra.IsIntegral.isIntegral a)
  have hlin :
      (∏ i ∈ (Finset.univ \ (S ∪ T)),
        (Polynomial.X - Polynomial.C (domainB i))).Monic :=
    Polynomial.monic_prod_X_sub_C domainB (Finset.univ \ (S ∪ T))
  rw [hmp.natDegree_mul hlin, hmin,
    Polynomial.natDegree_finsetProd_X_sub_C_eq_card]

omit [Fintype F] [DecidableEq F] in
private theorem subfield_ca_degree_lt_card [Finite F] (B : Subfield F) (k : ℕ) :
    Nat.card (Polynomial.degreeLT B k) = Nat.card B ^ k := by
  classical
  calc
    Nat.card (Polynomial.degreeLT B k) = Nat.card (Fin k → B) :=
      Nat.card_congr (Polynomial.degreeLTEquiv B k).toEquiv
    _ = Nat.card B ^ k := by rw [Nat.card_fun, Nat.card_fin]

private theorem subfield_ca_density_error_term_eq
    (n k f b q C : ℕ) (G : ℝ)
    (hkf : k + f ≤ n) (hb : 0 < b) (hC : 0 < C) :
    let A : ℝ := (C : ℝ) * (b : ℝ) ^ (k + f)
    let N : ℝ := (q : ℝ) * (b : ℝ) ^ n
    N * G / A =
      (q : ℝ) * (b : ℝ) ^ (n - k - f) * G / (C : ℝ) := by
  dsimp only
  have hbne : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hCne : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
  have hexp : n - k - f = n - (k + f) := by omega
  rw [hexp, pow_sub₀ _ hbne hkf]
  field_simp [hbne, hCne]

omit [Fintype F] [DecidableEq F] in
private theorem subfield_ca_divisible_degree_lt_mul_mem
    (B : Subfield F) (H : Polynomial B) (hH : H.Monic) (k : ℕ)
    (q : Polynomial.degreeLT B (k - H.natDegree)) :
    H * q.1 ∈ Polynomial.degreeLT B k := by
  rw [Polynomial.mem_degreeLT]
  by_cases hq0 : (q.1 : Polynomial B) = 0
  · simp only [hq0, mul_zero, Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  · have hqnat : (q.1 : Polynomial B).natDegree < k - H.natDegree :=
      (Polynomial.natDegree_lt_iff_degree_lt hq0).2
        (Polynomial.mem_degreeLT.mp q.2)
    have hprod0 : H * q.1 ≠ 0 := mul_ne_zero hH.ne_zero hq0
    apply (Polynomial.natDegree_lt_iff_degree_lt hprod0).1
    rw [hH.natDegree_mul' hq0]
    omega

omit [Fintype F] [DecidableEq F] in
private theorem subfield_ca_divisible_degree_lt_quotient_mem
    (B : Subfield F) (H : Polynomial B) (hH : H.Monic) (k : ℕ)
    (r : Polynomial.degreeLT B k) (hr : H ∣ (r.1 : Polynomial B)) :
    Polynomial.divByMonic r.1 H ∈
      Polynomial.degreeLT B (k - H.natDegree) := by
  rw [Polynomial.mem_degreeLT]
  by_cases hr0 : (r.1 : Polynomial B) = 0
  · simp only [hr0, Polynomial.zero_divByMonic, Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  · obtain ⟨q, hq⟩ := hr
    have hq0 : q ≠ 0 := by
      intro hzero
      apply hr0
      rw [hq, hzero, mul_zero]
    have hrnat : (r.1 : Polynomial B).natDegree < k :=
      (Polynomial.natDegree_lt_iff_degree_lt hr0).2
        (Polynomial.mem_degreeLT.mp r.2)
    have hqnat : q.natDegree < k - H.natDegree := by
      have hprod := hH.natDegree_mul' hq0
      rw [← hq] at hprod
      omega
    have hdiv : Polynomial.divByMonic r.1 H = q := by
      rw [hq]
      exact Polynomial.mul_divByMonic_cancel_left q hH
    rw [hdiv]
    exact (Polynomial.natDegree_lt_iff_degree_lt hq0).1 hqnat

private noncomputable def subfield_ca_divisible_degree_lt_quotient
    (B : Subfield F) (H : Polynomial B) (hH : H.Monic) (k : ℕ) :
    subfield_ca_divisible_degree_lt B k H →
      Polynomial.degreeLT B (k - H.natDegree) :=
  fun r => ⟨Polynomial.divByMonic r.1.1 H,
    subfield_ca_divisible_degree_lt_quotient_mem B H hH k r.1 r.2⟩

omit [Fintype F] [DecidableEq F] in
private theorem subfield_ca_divisible_degree_lt_quotient_injective
    (B : Subfield F) (H : Polynomial B) (hH : H.Monic) (k : ℕ) :
    Function.Injective
      (subfield_ca_divisible_degree_lt_quotient B H hH k) := by
  intro r s hrs
  have hdiv : Polynomial.divByMonic r.1.1 H =
      Polynomial.divByMonic s.1.1 H :=
    congrArg (fun z => (z.1 : Polynomial B)) hrs
  obtain ⟨qr, hqr⟩ := r.2
  obtain ⟨qs, hqs⟩ := s.2
  rw [hqr, hqs, Polynomial.mul_divByMonic_cancel_left qr hH,
    Polynomial.mul_divByMonic_cancel_left qs hH] at hdiv
  apply Subtype.ext
  apply Subtype.ext
  rw [hqr, hqs, hdiv]

omit [Fintype F] [DecidableEq F] in
private theorem subfield_ca_divisible_degree_lt_card_le [Finite F]
    (B : Subfield F) (H : Polynomial B) (hH : H.Monic) (k : ℕ) :
    Nat.card (subfield_ca_divisible_degree_lt B k H) ≤
      Nat.card B ^ (k - H.natDegree) := by
  classical
  let := Fintype.ofFinite B
  let : Fintype (Polynomial.degreeLT B (k - H.natDegree)) :=
    Fintype.ofEquiv (Fin (k - H.natDegree) → B)
      (Polynomial.degreeLTEquiv B (k - H.natDegree)).toEquiv.symm
  calc
    Nat.card (subfield_ca_divisible_degree_lt B k H) ≤
        Nat.card (Polynomial.degreeLT B (k - H.natDegree)) :=
      Nat.card_le_card_of_injective
        (subfield_ca_divisible_degree_lt_quotient B H hH k)
        (subfield_ca_divisible_degree_lt_quotient_injective B H hH k)
    _ = Nat.card B ^ (k - H.natDegree) :=
      subfield_ca_degree_lt_card B (k - H.natDegree)

private theorem subfield_ca_exp_term_succ (t : ℝ) (s : ℕ) :
    t ^ (s + 1) / ((s + 1).factorial : ℝ) =
      (t ^ s / (s.factorial : ℝ)) * t / (s + 1 : ℕ) := by
  rw [pow_succ, Nat.factorial_succ]
  push_cast
  field_simp

private theorem subfield_ca_exp_term_step_down
    (t : ℝ) (s : ℕ) (ht0 : 0 ≤ t) (hs : t ≤ (s + 1 : ℕ)) :
    t ^ (s + 1) / ((s + 1).factorial : ℝ) ≤
      t ^ s / (s.factorial : ℝ) := by
  rw [subfield_ca_exp_term_succ]
  have hterm : 0 ≤ t ^ s / (s.factorial : ℝ) := by positivity
  have hspos : (0 : ℝ) < (s + 1 : ℕ) := by positivity
  rw [div_le_iff₀ hspos]
  exact mul_le_mul_of_nonneg_left hs hterm

private theorem subfield_ca_exp_term_step_up
    (t : ℝ) (s : ℕ) (ht0 : 0 ≤ t) (hs : (s + 1 : ℕ) ≤ t) :
    t ^ s / (s.factorial : ℝ) ≤
      t ^ (s + 1) / ((s + 1).factorial : ℝ) := by
  rw [subfield_ca_exp_term_succ]
  have hterm : 0 ≤ t ^ s / (s.factorial : ℝ) := by positivity
  have hspos : (0 : ℝ) < (s + 1 : ℕ) := by positivity
  rw [le_div_iff₀ hspos]
  exact mul_le_mul_of_nonneg_left hs hterm

private theorem subfield_ca_exp_term_le_floor_mode
    (t : ℝ) (r s : ℕ) (ht0 : 0 ≤ t)
    (hrle : (r : ℝ) ≤ t) (htlt : t < (r : ℝ) + 1) :
    t ^ s / (s.factorial : ℝ) ≤
      t ^ r / (r.factorial : ℝ) := by
  by_cases hsr : s ≤ r
  · refine Nat.decreasingInduction
      (n := r)
      (motive := fun j _ =>
        t ^ j / (j.factorial : ℝ) ≤
          t ^ r / (r.factorial : ℝ)) ?_ (le_refl _) hsr
    intro j hj ih
    have hjr : j + 1 ≤ r := Nat.succ_le_of_lt hj
    have hjt : (j + 1 : ℕ) ≤ t := by
      have hjrR : ((j + 1 : ℕ) : ℝ) ≤ r := by exact_mod_cast hjr
      exact hjrR.trans hrle
    exact (subfield_ca_exp_term_step_up t j ht0 hjt).trans ih
  · have hrs : r ≤ s := Nat.le_of_lt (Nat.lt_of_not_ge hsr)
    refine Nat.le_induction
      (m := r)
      (P := fun j _ =>
        t ^ j / (j.factorial : ℝ) ≤
          t ^ r / (r.factorial : ℝ)) (le_refl _) ?_ s hrs
    intro j hrj ih
    have hrj' : r + 1 ≤ j + 1 := Nat.add_le_add_right hrj 1
    have hrjR : (r : ℝ) + 1 ≤ (j + 1 : ℕ) := by exact_mod_cast hrj'
    have htj : t ≤ (j + 1 : ℕ) := le_of_lt (htlt.trans_le hrjR)
    exact (subfield_ca_exp_term_step_down t j ht0 htj).trans ih

private theorem subfield_ca_exponent_cast_eq
    (n k f : ℕ) (δ : NNReal)
    (hn : 0 < n) (hkf : k + f ≤ n)
    (hint : (f : ℝ) = (δ : ℝ) * n) :
    ((n - k - f : ℕ) : ℝ) =
      (n : ℝ) * (1 - (k : ℝ) / n - (δ : ℝ)) := by
  have hk : k ≤ n := by omega
  have hf : f ≤ n - k := by omega
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [Nat.cast_sub hf, Nat.cast_sub hk, hint]
  field_simp [hnR]

open scoped BigOperators in
omit [Nonempty ι] [DecidableEq F] in
private theorem subfield_ca_first_moment_expand
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (δ : NNReal)
    (a : F) :
    subfield_ca_first_moment B domainB k δ a =
      ∑ S ∈ subfield_ca_error_sets (ι := ι) δ,
        (subfield_ca_event_fiber B domainB k a S).card := by
  classical
  let := Fintype.ofFinite B
  unfold subfield_ca_first_moment
  have hprod := Fintype.sum_prod_type
    (fun z : (ι → B) × F =>
      subfield_ca_multiplicity B domainB k δ a z.1 z.2)
  rw [← hprod]
  simp_rw [subfield_ca_multiplicity, Finset.card_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  rw [subfield_ca_event_fiber, Finset.card_filter]

omit [Fintype F] [DecidableEq F] in
private theorem subfield_ca_generator_adjoin_eq_top
    (B : Subfield F) (g : Fˣ) (hg : ∀ y : Fˣ, y ∈ Submonoid.powers g) :
    IntermediateField.adjoin B ({(g : F)} : Set F) = ⊤ := by
  apply top_unique
  intro x _hx
  by_cases hx0 : x = 0
  · subst x
    exact (IntermediateField.adjoin B ({(g : F)} : Set F)).zero_mem
  · let u : Fˣ := Units.mk0 x hx0
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff u g).mp (hg u)
    have hgmem : (g : F) ∈ IntermediateField.adjoin B ({(g : F)} : Set F) :=
      IntermediateField.subset_adjoin B ({(g : F)} : Set F) (Set.mem_singleton (g : F))
    have hpow : (g : F) ^ n ∈ IntermediateField.adjoin B ({(g : F)} : Set F) :=
      (IntermediateField.adjoin B ({(g : F)} : Set F)).toSubfield.pow_mem hgmem n
    have hval : (g : F) ^ n = x := by
      have h := congrArg (fun z : Fˣ => (z : F)) hn
      simpa only [Units.val_pow_eq_pow_val, u, Units.val_mk0] using h
    rw [hval] at hpow
    exact hpow

omit [Fintype F] [DecidableEq F] in
private theorem subfield_ca_generator_minpoly_nat_degree [Finite F]
    (B : Subfield F) (g : Fˣ) (hg : ∀ y : Fˣ, y ∈ Submonoid.powers g) :
    (minpoly B (g : F)).natDegree = Module.finrank B F := by
  exact (Field.primitive_element_iff_minpoly_natDegree_eq B (g : F)).mp
    (subfield_ca_generator_adjoin_eq_top B g hg)

omit [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
private theorem subfield_ca_interpolant_unique
    (B : Subfield F) (domainB : ι ↪ B)
    (k f : ℕ) (hkf : k + f < Fintype.card ι)
    (S : Finset ι) (hS : S.card = f) (y : ι → B)
    (p q : Polynomial B)
    (hpdeg : p.degree < k) (hqdeg : q.degree < k)
    (hp : ∀ i, i ∉ S → p.eval (domainB i) = y i)
    (hq : ∀ i, i ∉ S → q.eval (domainB i) = y i) : p = q := by
  classical
  by_contra hpq
  have hr : p - q ≠ 0 := sub_ne_zero.mpr hpq
  have hrdeg : (p - q).degree < (k : WithBot ℕ) :=
    lt_of_le_of_lt (Polynomial.degree_sub_le p q) (max_lt hpdeg hqdeg)
  have hrnat : (p - q).natDegree < k :=
    (Polynomial.natDegree_lt_iff_degree_lt hr).2 hrdeg
  let T : Finset B := (Finset.univ \ S).map domainB
  have hTcard : T.card = Fintype.card ι - f := by
    dsimp only [T]
    rw [Finset.card_map, Finset.card_sdiff_of_subset (Finset.subset_univ S),
      Finset.card_univ, hS]
  have hroots : T.val ⊆ (p - q).roots := by
    intro x hx
    rw [← Finset.mem_def] at hx
    simp only [T, Finset.mem_map] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    have hiS : i ∉ S := (Finset.mem_sdiff.mp hi).2
    rw [Polynomial.mem_roots hr, Polynomial.IsRoot.def]
    simp only [Polynomial.eval_sub, hp i hiS, hq i hiS, sub_self]
  have hle : T.card ≤ (p - q).natDegree :=
    Polynomial.card_le_degree_of_subset_roots hroots
  omega

omit [Nonempty ι] [DecidableEq F] in
private theorem subfield_ca_event_fiber_card
    (B : Subfield F) (domainB : ι ↪ B) (k f : ℕ)
    (a : F) (S : Finset ι) (hS : S.card = f)
    (hkf : k + f < Fintype.card ι) :
    (subfield_ca_event_fiber B domainB k a S).card =
      Nat.card B ^ (k + f) := by
  classical
  let := Fintype.ofFinite B
  let : Fintype (Polynomial.degreeLT B k) :=
    Fintype.ofEquiv (Fin k → B) (Polynomial.degreeLTEquiv B k).toEquiv.symm
  let φ : Polynomial.degreeLT B k × (S → B) → (ι → B) × F :=
    fun z =>
      (fun i => if hi : i ∈ S then z.2 ⟨i, hi⟩
        else z.1.1.eval (domainB i),
       Polynomial.aeval a z.1.1)
  have hcard :
      (Finset.univ : Finset (Polynomial.degreeLT B k × (S → B))).card =
        (subfield_ca_event_fiber B domainB k a S).card := by
    apply Finset.card_bij (fun z _ => φ z)
    · intro z _hz
      rw [subfield_ca_event_fiber, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      refine ⟨z.1.1, Polynomial.mem_degreeLT.mp z.1.2, ?_, rfl⟩
      intro i hi
      simp only [φ, hi, ↓reduceDIte]
    · intro z₁ _hz₁ z₂ _hz₂ heq
      have hy : (φ z₁).1 = (φ z₂).1 := congrArg Prod.fst heq
      have hp : z₁.1.1 = z₂.1.1 := by
        apply subfield_ca_interpolant_unique B domainB k f hkf S hS (φ z₁).1
          z₁.1.1 z₂.1.1
          (Polynomial.mem_degreeLT.mp z₁.1.2)
          (Polynomial.mem_degreeLT.mp z₂.1.2)
        · intro i hi
          simp only [φ, hi, ↓reduceDIte]
        · intro i hi
          rw [hy]
          simp only [φ, hi, ↓reduceDIte]
      apply Prod.ext
      · exact Subtype.ext hp
      · funext j
        have hj := congrFun hy j
        simpa only [φ, j.property, ↓reduceDIte] using hj
    · intro w hw
      rw [subfield_ca_event_fiber, Finset.mem_filter] at hw
      obtain ⟨_hwuniv, p, hpdeg, hpagree, hpa⟩ := hw
      let z : Polynomial.degreeLT B k × (S → B) :=
        (⟨p, Polynomial.mem_degreeLT.mpr hpdeg⟩, fun j => w.1 j)
      refine ⟨z, Finset.mem_univ _, ?_⟩
      apply Prod.ext
      · funext i
        by_cases hi : i ∈ S
        · simp only [φ, z, hi, ↓reduceDIte]
        · simp only [φ, z, hi, ↓reduceDIte, hpagree i hi]
      · simpa only [φ, z] using hpa
  rw [← hcard, Finset.card_univ, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_coe, hS, pow_add]
  rw [← Nat.card_eq_fintype_card, subfield_ca_degree_lt_card]
  rw [Nat.card_eq_fintype_card]

open scoped BigOperators in
omit [Nonempty ι] [DecidableEq F] in
private theorem subfield_ca_first_moment_eq
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (δ : NNReal)
    (a : F)
    (hkf : k + ⌊(δ : ℝ) * Fintype.card ι⌋₊ < Fintype.card ι) :
    subfield_ca_first_moment B domainB k δ a =
      Nat.choose (Fintype.card ι) ⌊(δ : ℝ) * Fintype.card ι⌋₊ *
        Nat.card B ^ (k + ⌊(δ : ℝ) * Fintype.card ι⌋₊) := by
  classical
  rw [subfield_ca_first_moment_expand]
  calc
    (∑ S ∈ subfield_ca_error_sets (ι := ι) δ,
        (subfield_ca_event_fiber B domainB k a S).card) =
        ∑ _S ∈ subfield_ca_error_sets (ι := ι) δ,
          Nat.card B ^ (k + ⌊(δ : ℝ) * Fintype.card ι⌋₊) := by
      apply Finset.sum_congr rfl
      intro S hS
      apply subfield_ca_event_fiber_card B domainB k
        ⌊(δ : ℝ) * Fintype.card ι⌋₊ a S
      · exact subfield_ca_error_sets_mem_iff_card δ S |>.mp hS
      · exact hkf
    _ = (subfield_ca_error_sets (ι := ι) δ).card *
          Nat.card B ^ (k + ⌊(δ : ℝ) * Fintype.card ι⌋₊) := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id]
    _ = Nat.choose (Fintype.card ι) ⌊(δ : ℝ) * Fintype.card ι⌋₊ *
          Nat.card B ^ (k + ⌊(δ : ℝ) * Fintype.card ι⌋₊) := by
      rw [subfield_ca_error_sets_card]

open scoped BigOperators in
omit [Nonempty ι] [DecidableEq F] in
private theorem subfield_ca_first_moment_real_eq
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (δ : NNReal)
    (a : F)
    (hkf : k + ⌊(δ : ℝ) * Fintype.card ι⌋₊ < Fintype.card ι) :
    letI := Fintype.ofFinite B
    ∑ z : (ι → B) × F,
        (subfield_ca_multiplicity B domainB k δ a z.1 z.2 : ℝ) =
      (Nat.choose (Fintype.card ι)
        ⌊(δ : ℝ) * Fintype.card ι⌋₊ : ℝ) *
      (Nat.card B : ℝ) ^
        (k + ⌊(δ : ℝ) * Fintype.card ι⌋₊) := by
  classical
  let := Fintype.ofFinite B
  rw [Fintype.sum_prod_type]
  exact_mod_cast subfield_ca_first_moment_eq B domainB k δ a hkf

omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
private theorem subfield_ca_minpoly_coprime_linear [Finite F]
    (B : Subfield F) (domainB : ι ↪ B) (a : F)
    (ha : a ∉ B) (i : ι) :
    IsCoprime (minpoly B a)
      (Polynomial.X - Polynomial.C (domainB i)) := by
  have hirr : Irreducible (minpoly B a) :=
    minpoly.irreducible (Algebra.IsIntegral.isIntegral a)
  rw [hirr.coprime_iff_not_dvd]
  intro hdvd
  have hz :
      Polynomial.aeval a
        (Polynomial.X - Polynomial.C (domainB i)) = 0 :=
    (minpoly.dvd_iff).mp hdvd
  have heq : a = algebraMap B F (domainB i) := by
    simpa only [Polynomial.aeval_sub, Polynomial.aeval_X,
      Polynomial.aeval_C, sub_eq_zero] using hz
  apply ha
  rw [heq, Subfield.algebraMap_ofSubfield]
  exact (domainB i).property

open scoped BigOperators in
omit [Fintype ι] [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
private theorem subfield_ca_minpoly_coprime_linear_prod
    [Finite F]
    (B : Subfield F) (domainB : ι ↪ B) (a : F)
    (ha : a ∉ B) (U : Finset ι) :
    IsCoprime (minpoly B a)
      (∏ i ∈ U, (Polynomial.X - Polynomial.C (domainB i))) := by
  apply IsCoprime.prod_right
  intro i hi
  exact subfield_ca_minpoly_coprime_linear B domainB a ha i

open scoped BigOperators in
omit [Nonempty ι] [Fintype F] [DecidableEq F] in
private theorem subfield_ca_collision_divisor_dvd_sub [Finite F]
    (B : Subfield F) (domainB : ι ↪ B) (a : F)
    (ha : a ∉ B) (S T : Finset ι) (y : ι → B) (α : F)
    (p q : Polynomial B)
    (hp : ∀ i, i ∉ S → p.eval (domainB i) = y i)
    (hq : ∀ i, i ∉ T → q.eval (domainB i) = y i)
    (hpa : Polynomial.aeval a p = α)
    (hqa : Polynomial.aeval a q = α) :
    subfield_ca_collision_divisor B domainB a S T ∣ p - q := by
  unfold subfield_ca_collision_divisor
  apply (subfield_ca_minpoly_coprime_linear_prod B domainB a ha
    (Finset.univ \ (S ∪ T))).mul_dvd
  · rw [minpoly.dvd_iff, Polynomial.aeval_sub, hpa, hqa, sub_self]
  · apply Finset.prod_dvd_of_coprime
    · intro i hi j hj hij
      exact Polynomial.pairwise_coprime_X_sub_C domainB.injective hij
    · intro i hi
      have hiST : i ∉ S ∪ T := (Finset.mem_sdiff.mp hi).2
      have hiS : i ∉ S := by
        intro hiS
        exact hiST (Finset.mem_union.mpr (Or.inl hiS))
      have hiT : i ∉ T := by
        intro hiT
        exact hiST (Finset.mem_union.mpr (Or.inr hiT))
      rw [Polynomial.dvd_iff_isRoot, Polynomial.IsRoot.def,
        Polynomial.eval_sub, hp i hiS, hq i hiT, sub_self]

omit [Fintype F] [DecidableEq F] in
private noncomputable def subfield_ca_pair_witness_to_parameters [Finite F]
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (a : F)
    (ha : a ∉ B) (S T : Finset ι) :
    SubfieldCaPairWitness B domainB k a S T →
      subfield_ca_pair_parameters B domainB k a S T := by
  classical
  intro w
  let r : Polynomial.degreeLT B k :=
    ⟨w.p.1 - w.q.1, by
      rw [Polynomial.mem_degreeLT]
      exact lt_of_le_of_lt (Polynomial.degree_sub_le w.p.1 w.q.1)
        (max_lt (Polynomial.mem_degreeLT.mp w.p.2)
          (Polynomial.mem_degreeLT.mp w.q.2))⟩
  refine ⟨w.q, ⟨r, ?_⟩, fun i => w.y i⟩
  exact subfield_ca_collision_divisor_dvd_sub B domainB a ha S T
    w.y w.α w.p.1 w.q.1 w.p_agree w.q_agree w.p_value w.q_value

omit [Fintype F] [DecidableEq F] in
private noncomputable def subfield_ca_pair_fiber_to_parameters [Finite F]
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (a : F)
    (ha : a ∉ B) (S T : Finset ι) :
    ↥(subfield_ca_pair_event_fiber B domainB k a S T) →
      subfield_ca_pair_parameters B domainB k a S T :=
  fun z => subfield_ca_pair_witness_to_parameters B domainB k a ha S T
    (subfield_ca_pair_fiber_to_witness B domainB k a S T z)

omit [Nonempty ι] [Fintype F] [DecidableEq F] in
private theorem subfield_ca_pair_witness_to_parameters_injective [Finite F]
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (a : F)
    (ha : a ∉ B) (S T : Finset ι) :
    Function.Injective
      (subfield_ca_pair_witness_to_parameters B domainB k a ha S T) := by
  classical
  intro w₁ w₂ h
  have hq : w₁.q.1 = w₂.q.1 :=
    congrArg (fun z => z.1.1) h
  have hr : w₁.p.1 - w₁.q.1 = w₂.p.1 - w₂.q.1 :=
    congrArg (fun z => z.2.1.1.1) h
  have hp : w₁.p.1 = w₂.p.1 := by
    rw [← sub_add_cancel w₁.p.1 w₁.q.1,
      ← sub_add_cancel w₂.p.1 w₂.q.1, hr, hq]
  have hα : w₁.α = w₂.α := by
    calc
      w₁.α = Polynomial.aeval a w₁.q.1 := w₁.q_value.symm
      _ = Polynomial.aeval a w₂.q.1 := congrArg (Polynomial.aeval a) hq
      _ = w₂.α := w₂.q_value
  have hy : w₁.y = w₂.y := by
    funext i
    by_cases hiS : i ∈ S
    · by_cases hiT : i ∈ T
      · have hc := congrArg (fun z => z.2.2) h
        exact congrFun hc ⟨i, Finset.mem_inter.mpr ⟨hiS, hiT⟩⟩
      · calc
          w₁.y i = w₁.q.1.eval (domainB i) :=
            (w₁.q_agree i hiT).symm
          _ = w₂.q.1.eval (domainB i) := congrArg (fun q => q.eval (domainB i)) hq
          _ = w₂.y i := w₂.q_agree i hiT
    · calc
        w₁.y i = w₁.p.1.eval (domainB i) :=
          (w₁.p_agree i hiS).symm
        _ = w₂.p.1.eval (domainB i) := congrArg (fun p => p.eval (domainB i)) hp
        _ = w₂.y i := w₂.p_agree i hiS
  have hp' : w₁.p = w₂.p := Subtype.ext hp
  have hq' : w₁.q = w₂.q := Subtype.ext hq
  rcases w₁ with ⟨y₁, α₁, p₁, q₁, hp₁, hq₁, hpa₁, hqa₁⟩
  rcases w₂ with ⟨y₂, α₂, p₂, q₂, hp₂, hq₂, hpa₂, hqa₂⟩
  dsimp only at hy hα hp' hq'
  cases hy
  cases hα
  cases hp'
  cases hq'
  rfl

omit [Nonempty ι] [DecidableEq F] in
private theorem subfield_ca_pair_fiber_to_parameters_injective
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (a : F)
    (ha : a ∉ B) (S T : Finset ι) :
    Function.Injective
      (subfield_ca_pair_fiber_to_parameters B domainB k a ha S T) :=
  (subfield_ca_pair_witness_to_parameters_injective B domainB k a ha S T).comp
    (subfield_ca_pair_fiber_to_witness_injective B domainB k a S T)

open scoped BigOperators in
omit [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
private theorem subfield_ca_multiplicity_real_eq_indicator_sum
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (δ : NNReal)
    (a : F) (y : ι → B) (α : F) :
    (subfield_ca_multiplicity B domainB k δ a y α : ℝ) =
      ∑ S ∈ subfield_ca_error_sets (ι := ι) δ,
        subfield_ca_event_indicator B domainB k a S y α := by
  classical
  unfold subfield_ca_multiplicity subfield_ca_event_indicator
  exact Finset.natCast_card_filter
    (fun S => subfield_ca_event B domainB k a S y α)
    (subfield_ca_error_sets (ι := ι) δ)

private theorem subfield_ca_natural_power_eq_rpow
    (n k f b : ℕ) (δ : NNReal)
    (hn : 0 < n) (hkf : k + f ≤ n)
    (hint : (f : ℝ) = (δ : ℝ) * n) :
    (b : ℝ) ^ (n - k - f) =
      (b : ℝ) ^ ((n : ℝ) * (1 - (k : ℝ) / n - (δ : ℝ)) : ℝ) := by
  rw [← Real.rpow_natCast]
  rw [subfield_ca_exponent_cast_eq n k f δ hn hkf hint]

private theorem subfield_ca_overlap_argument_eq
    (n f b : ℕ) (δ : NNReal)
    (hf : f ≤ n)
    (hint : (f : ℝ) = (δ : ℝ) * n) :
    ((f : ℝ) * (n - f : ℕ)) / b =
      (δ : ℝ) * (1 - δ) * (n : ℝ) ^ 2 / b := by
  rw [Nat.cast_sub hf, hint]
  ring

omit [Nonempty ι] in
private theorem subfield_ca_overlap_count
    (S : Finset ι) (f s : ℕ) (hS : S.card = f) :
    ((Finset.univ.powersetCard f).filter
      (fun T : Finset ι => (S \ T).card = s)).card =
      Nat.choose f s * Nat.choose (Fintype.card ι - f) s := by
  classical
  let A : Finset (Finset ι) :=
    (Finset.univ.powersetCard f).filter (fun T : Finset ι => (S \ T).card = s)
  let P : Finset (Finset ι × Finset ι) :=
    S.powersetCard s ×ˢ (Finset.univ \ S).powersetCard s
  have hcard : A.card = P.card := by
    apply Finset.card_bij (fun T _ => (S \ T, T \ S))
    · intro T hT
      simp only [A, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
        true_and] at hT
      rw [show P = S.powersetCard s ×ˢ (Finset.univ \ S).powersetCard s by rfl,
        Finset.mem_product]
      constructor
      · exact Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset, hT.2⟩
      · apply Finset.mem_powersetCard.mpr
        constructor
        · intro x hx
          exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ x, (Finset.mem_sdiff.mp hx).2⟩
        · change (T \ S).card = s
          have hST := Finset.card_sdiff_add_card_inter S T
          have hTS := Finset.card_sdiff_add_card_inter T S
          have hinter : (T ∩ S).card = (S ∩ T).card := by rw [Finset.inter_comm]
          omega
    · intro T₁ hT₁ T₂ hT₂ heq
      have hl : S \ T₁ = S \ T₂ := congrArg Prod.fst heq
      have hr : T₁ \ S = T₂ \ S := congrArg Prod.snd heq
      ext x
      have hlx := Finset.ext_iff.mp hl x
      have hrx := Finset.ext_iff.mp hr x
      simp only [Finset.mem_sdiff] at hlx hrx
      by_cases hx : x ∈ S <;> grind
    · intro RA hRA
      rcases RA with ⟨R, D⟩
      have hRA' : R ∈ S.powersetCard s ∧ D ∈ (Finset.univ \ S).powersetCard s := by
        rw [show P = S.powersetCard s ×ˢ (Finset.univ \ S).powersetCard s by rfl,
          Finset.mem_product] at hRA
        exact hRA
      have hR := Finset.mem_powersetCard.mp hRA'.1
      have hD := Finset.mem_powersetCard.mp hRA'.2
      let T : Finset ι := (S \ R) ∪ D
      have hSD : Disjoint (S \ R) D := by
        rw [Finset.disjoint_left]
        intro x hxS hxD
        have hxD' := hD.1 hxD
        exact (Finset.mem_sdiff.mp hxD').2 ((Finset.mem_sdiff.mp hxS).1)
      have hTcard : T.card = f := by
        dsimp only [T]
        rw [Finset.card_union_of_disjoint hSD,
          Finset.card_sdiff_of_subset hR.1, hS, hR.2, hD.2]
        have hsle : s ≤ f := by simpa [hS, hR.2] using Finset.card_le_card hR.1
        omega
      have hleft : S \ T = R := by
        ext x
        simp only [T, Finset.mem_sdiff, Finset.mem_union]
        have hRsub := hR.1
        have hDsub := hD.1
        constructor
        · intro hx
          by_contra hxR
          exact hx.2 (Or.inl ⟨hx.1, hxR⟩)
        · intro hxR
          have hxS := hRsub hxR
          refine ⟨hxS, ?_⟩
          intro hxT
          rcases hxT with hxSR | hxD
          · exact hxSR.2 hxR
          · exact (Finset.mem_sdiff.mp (hDsub hxD)).2 hxS
      have hright : T \ S = D := by
        ext x
        simp only [T, Finset.mem_sdiff, Finset.mem_union]
        have hDsub := hD.1
        constructor
        · intro hx
          rcases hx.1 with hxSR | hxD
          · exact (hx.2 hxSR.1).elim
          · exact hxD
        · intro hxD
          have hxDS := Finset.mem_sdiff.mp (hDsub hxD)
          exact ⟨Or.inr hxD, hxDS.2⟩
      refine ⟨T, ?_, ?_⟩
      · simp only [A, Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ,
          hTcard, hleft, hR.2, and_self]
      · exact Prod.ext hleft hright
  change A.card = _
  rw [hcard]
  change (S.powersetCard s ×ˢ (Finset.univ \ S).powersetCard s).card = _
  rw [Finset.card_product, Finset.card_powersetCard, Finset.card_powersetCard,
    Finset.card_sdiff_of_subset (Finset.subset_univ S), Finset.card_univ, hS]

open scoped BigOperators in
private theorem subfield_ca_overlap_sum_le_bessel
    (n f b : ℕ) (_hf : f ≤ n) (hb : 0 < b) :
    subfield_ca_overlap_sum n f b ≤
      subfield_ca_bessel_partial (((f : ℝ) * (n - f : ℕ)) / b) f := by
  unfold subfield_ca_overlap_sum subfield_ca_bessel_partial
  apply Finset.sum_le_sum
  intro s hs
  have h₁ : (Nat.choose f s : ℝ) ≤ (f : ℝ) ^ s / (s.factorial : ℝ) :=
    Nat.choose_le_pow_div s f
  have h₂ : (Nat.choose (n - f) s : ℝ) ≤
      (n - f : ℕ) ^ s / (s.factorial : ℝ) :=
    Nat.choose_le_pow_div s (n - f)
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hfac : (0 : ℝ) < s.factorial := by exact_mod_cast s.factorial_pos
  calc
    (Nat.choose f s : ℝ) * (Nat.choose (n - f) s : ℝ) / (b : ℝ) ^ s ≤
        (((f : ℝ) ^ s / (s.factorial : ℝ)) *
          ((n - f : ℕ) ^ s / (s.factorial : ℝ))) / (b : ℝ) ^ s := by
      gcongr
    _ = (((f : ℝ) * (n - f : ℕ)) / b) ^ s / ((s.factorial : ℝ) ^ 2) := by
      rw [div_pow, mul_pow]
      field_simp

private theorem subfield_ca_overlap_sum_le_factor_small
    (n f b : ℕ) (hf : f ≤ n) (hb : 0 < b)
    (hxle : ((f : ℝ) * (n - f : ℕ)) / b ≤ 3 / 2) :
    subfield_ca_overlap_sum n f b ≤
      subfieldCaFactor (((f : ℝ) * (n - f : ℕ)) / b) := by
  apply le_trans (subfield_ca_overlap_sum_le_bessel n f b hf hb)
  apply subfield_ca_bessel_partial_le_factor_small
  · positivity
  · exact hxle

open scoped BigOperators in
omit [Nonempty ι] in
private theorem subfield_ca_overlap_weight_sum
    (S : Finset ι) (f b : ℕ) (hS : S.card = f) :
    (∑ T ∈ Finset.univ.powersetCard f,
        (1 : ℝ) / (b : ℝ) ^ (S \ T).card) =
      subfield_ca_overlap_sum (Fintype.card ι) f b := by
  classical
  have hmap : ∀ T ∈ Finset.univ.powersetCard f,
      (S \ T).card ∈ Finset.range (f + 1) := by
    intro T hT
    rw [Finset.mem_range]
    have hle : (S \ T).card ≤ S.card := Finset.card_le_card Finset.sdiff_subset
    omega
  rw [← Finset.sum_fiberwise_of_maps_to'
    (s := Finset.univ.powersetCard f) (t := Finset.range (f + 1))
    (g := fun T : Finset ι => (S \ T).card) hmap
    (fun s : ℕ => (1 : ℝ) / (b : ℝ) ^ s)]
  unfold subfield_ca_overlap_sum
  apply Finset.sum_congr rfl
  intro s hs
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [subfield_ca_overlap_count S f s hS]
  push_cast
  ring

open scoped BigOperators in
omit [Nonempty ι] [Fintype F] [DecidableEq F] in
private theorem subfield_ca_overlap_contribution_eq
    (B : Subfield F) (k : ℕ) (δ : NNReal) :
    let f := ⌊(δ : ℝ) * Fintype.card ι⌋₊
    (∑ S ∈ subfield_ca_error_sets (ι := ι) δ,
      ∑ T ∈ subfield_ca_error_sets (ι := ι) δ,
        (Nat.card B : ℝ) ^ (k + f) /
          (Nat.card B : ℝ) ^ (S \ T).card) =
      (Nat.choose (Fintype.card ι) f : ℝ) *
        (Nat.card B : ℝ) ^ (k + f) *
          subfield_ca_overlap_sum (Fintype.card ι) f (Nat.card B) := by
  classical
  dsimp only
  let f := ⌊(δ : ℝ) * Fintype.card ι⌋₊
  change (∑ S ∈ subfield_ca_error_sets (ι := ι) δ,
      ∑ T ∈ subfield_ca_error_sets (ι := ι) δ,
        (Nat.card B : ℝ) ^ (k + f) /
          (Nat.card B : ℝ) ^ (S \ T).card) =
    (Nat.choose (Fintype.card ι) f : ℝ) *
      (Nat.card B : ℝ) ^ (k + f) *
        subfield_ca_overlap_sum (Fintype.card ι) f (Nat.card B)
  have hinner (S : Finset ι)
      (hS : S ∈ subfield_ca_error_sets (ι := ι) δ) :
      (∑ T ∈ subfield_ca_error_sets (ι := ι) δ,
        (Nat.card B : ℝ) ^ (k + f) /
          (Nat.card B : ℝ) ^ (S \ T).card) =
        (Nat.card B : ℝ) ^ (k + f) *
          subfield_ca_overlap_sum (Fintype.card ι) f (Nat.card B) := by
    have hScard : S.card = f := by
      exact subfield_ca_error_sets_mem_iff_card δ S |>.mp hS
    change (∑ T ∈ (Finset.univ : Finset ι).powersetCard f,
        (Nat.card B : ℝ) ^ (k + f) /
          (Nat.card B : ℝ) ^ (S \ T).card) = _
    calc
      (∑ T ∈ (Finset.univ : Finset ι).powersetCard f,
          (Nat.card B : ℝ) ^ (k + f) /
            (Nat.card B : ℝ) ^ (S \ T).card) =
          (Nat.card B : ℝ) ^ (k + f) *
            ∑ T ∈ (Finset.univ : Finset ι).powersetCard f,
              (1 : ℝ) / (Nat.card B : ℝ) ^ (S \ T).card := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro T hT
        ring
      _ = (Nat.card B : ℝ) ^ (k + f) *
          subfield_ca_overlap_sum (Fintype.card ι) f (Nat.card B) := by
        rw [subfield_ca_overlap_weight_sum S f (Nat.card B) hScard]
  calc
    (∑ S ∈ subfield_ca_error_sets (ι := ι) δ,
        ∑ T ∈ subfield_ca_error_sets (ι := ι) δ,
          (Nat.card B : ℝ) ^ (k + f) /
            (Nat.card B : ℝ) ^ (S \ T).card) =
        ∑ _S ∈ subfield_ca_error_sets (ι := ι) δ,
          (Nat.card B : ℝ) ^ (k + f) *
            subfield_ca_overlap_sum (Fintype.card ι) f (Nat.card B) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact hinner S hS
    _ = ((subfield_ca_error_sets (ι := ι) δ).card : ℝ) *
        ((Nat.card B : ℝ) ^ (k + f) *
          subfield_ca_overlap_sum (Fintype.card ι) f (Nat.card B)) := by
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = (Nat.choose (Fintype.card ι) f : ℝ) *
        (Nat.card B : ℝ) ^ (k + f) *
          subfield_ca_overlap_sum (Fintype.card ι) f (Nat.card B) := by
      rw [subfield_ca_error_sets_card]
      ring

omit [Nonempty ι] [DecidableEq F] in
private theorem subfield_ca_pair_event_fiber_nat_card_le_parameters
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (a : F)
    (ha : a ∉ B) (S T : Finset ι) :
    Nat.card ↥(subfield_ca_pair_event_fiber B domainB k a S T) ≤
      Nat.card (subfield_ca_pair_parameters B domainB k a S T) := by
  classical
  let := Fintype.ofFinite B
  let : Fintype (Polynomial.degreeLT B k) :=
    Fintype.ofEquiv (Fin k → B)
      (Polynomial.degreeLTEquiv B k).toEquiv.symm
  let : Finite
      (subfield_ca_divisible_degree_lt B k
        (subfield_ca_collision_divisor B domainB a S T)) :=
    Subtype.finite
  let : Finite (subfield_ca_pair_parameters B domainB k a S T) := by
    unfold subfield_ca_pair_parameters
    infer_instance
  apply Nat.card_le_card_of_injective
    (subfield_ca_pair_fiber_to_parameters B domainB k a ha S T)
    (subfield_ca_pair_fiber_to_parameters_injective B domainB k a ha S T)

omit [Nonempty ι] [DecidableEq F] in
private theorem subfield_ca_pair_fiber_card_le_parameters
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (a : F)
    (ha : a ∉ B) (S T : Finset ι) :
    (subfield_ca_pair_event_fiber B domainB k a S T).card ≤
      Nat.card (subfield_ca_pair_parameters B domainB k a S T) := by
  rw [← Nat.card_eq_finsetCard]
  exact subfield_ca_pair_event_fiber_nat_card_le_parameters
    B domainB k a ha S T

open scoped BigOperators in
omit [Nonempty ι] [DecidableEq F] in
private theorem subfield_ca_pair_indicator_sum_eq_fiber_card
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (a : F)
    (S T : Finset ι) :
    letI := Fintype.ofFinite B
    (∑ z : (ι → B) × F,
        subfield_ca_event_indicator B domainB k a S z.1 z.2 *
        subfield_ca_event_indicator B domainB k a T z.1 z.2) =
      ((subfield_ca_pair_event_fiber B domainB k a S T).card : ℝ) := by
  classical
  let := Fintype.ofFinite B
  rw [subfield_ca_pair_event_fiber, Finset.natCast_card_filter]
  apply Finset.sum_congr rfl
  intro z hz
  unfold subfield_ca_event_indicator
  by_cases hS : subfield_ca_event B domainB k a S z.1 z.2
  · by_cases hT : subfield_ca_event B domainB k a T z.1 z.2
    · simp only [hS, hT, if_true, mul_one, and_self]
    · simp only [hS, hT, if_true, if_false, mul_zero, and_false]
  · simp only [hS, if_false, zero_mul, false_and]

omit [Nonempty ι] [Fintype F] [DecidableEq F] in
private theorem subfield_ca_pair_parameters_card_le [Finite F]
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (a : F)
    (S T : Finset ι) :
    Nat.card (subfield_ca_pair_parameters B domainB k a S T) ≤
      Nat.card B ^ k *
        (Nat.card B ^
            (k - (subfield_ca_collision_divisor B domainB a S T).natDegree) *
          Nat.card B ^ (S ∩ T).card) := by
  unfold subfield_ca_pair_parameters
  rw [Nat.card_prod, Nat.card_prod,
    subfield_ca_degree_lt_card B k, Nat.card_fun,
    Nat.card_eq_finsetCard]
  gcongr
  exact subfield_ca_divisible_degree_lt_card_le B
    (subfield_ca_collision_divisor B domainB a S T)
    (subfield_ca_collision_divisor_monic B domainB a S T) k

omit [Nonempty ι] in
private theorem subfield_ca_pair_set_card_facts
    (S T : Finset ι) (f : ℕ) (hS : S.card = f) (hT : T.card = f) :
    let s := (S \ T).card
    (S ∩ T).card = f - s ∧
      (Finset.univ \ (S ∪ T)).card = Fintype.card ι - f - s := by
  dsimp only
  have hdiff := Finset.card_sdiff_add_card_inter S T
  have hunion := Finset.card_union_add_card_inter S T
  have hinter : (S ∩ T).card = f - (S \ T).card := by
    omega
  have hunioncard : (S ∪ T).card = f + (S \ T).card := by
    omega
  constructor
  · exact hinter
  · rw [Finset.card_univ_sdiff, hunioncard]
    omega

omit [Nonempty ι] [Fintype F] [DecidableEq F] in
private theorem subfield_ca_collision_divisor_nat_degree [Finite F]
    (B : Subfield F) (domainB : ι ↪ B) (a : F)
    (S T : Finset ι) (f : ℕ)
    (hS : S.card = f) (hT : T.card = f)
    (hmin : (minpoly B a).natDegree = Module.finrank B F) :
    (subfield_ca_collision_divisor B domainB a S T).natDegree =
      Module.finrank B F +
        (Fintype.card ι - f - (S \ T).card) := by
  rw [subfield_ca_collision_divisor_nat_degree_card B domainB a S T hmin]
  rw [(subfield_ca_pair_set_card_facts S T f hS hT).2]

omit [Nonempty ι] [DecidableEq F] in
private theorem subfield_ca_pair_fiber_card_le_overlap_branch
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (a : F)
    (ha : a ∉ B) (S T : Finset ι) (f : ℕ)
    (hS : S.card = f) (hT : T.card = f)
    (hmin : (minpoly B a).natDegree = Module.finrank B F)
    (hlarge : k < Module.finrank B F +
      (Fintype.card ι - f - (S \ T).card)) :
    (subfield_ca_pair_event_fiber B domainB k a S T).card ≤
      Nat.card B ^ (k + f - (S \ T).card) := by
  have hsle : (S \ T).card ≤ f := by
    rw [← hS]
    exact Finset.card_le_card Finset.sdiff_subset
  have hdeg := subfield_ca_collision_divisor_nat_degree
    B domainB a S T f hS hT hmin
  have hinter := (subfield_ca_pair_set_card_facts S T f hS hT).1
  have hsub : k - (subfield_ca_collision_divisor B domainB a S T).natDegree = 0 := by
    rw [hdeg]
    exact Nat.sub_eq_zero_of_le (Nat.le_of_lt hlarge)
  calc
    (subfield_ca_pair_event_fiber B domainB k a S T).card ≤
        Nat.card (subfield_ca_pair_parameters B domainB k a S T) :=
      subfield_ca_pair_fiber_card_le_parameters B domainB k a ha S T
    _ ≤ Nat.card B ^ k *
        (Nat.card B ^
            (k - (subfield_ca_collision_divisor B domainB a S T).natDegree) *
          Nat.card B ^ (S ∩ T).card) :=
      subfield_ca_pair_parameters_card_le B domainB k a S T
    _ = Nat.card B ^ (k + (f - (S \ T).card)) := by
      rw [hsub, hinter, pow_zero, one_mul, ← pow_add]
    _ = Nat.card B ^ (k + f - (S \ T).card) := by
      congr 1
      omega

omit [Nonempty ι] [DecidableEq F] in
private theorem subfield_ca_pair_fiber_card_le_overlap_real
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (a : F)
    (ha : a ∉ B) (S T : Finset ι) (f : ℕ)
    (hS : S.card = f) (hT : T.card = f)
    (hmin : (minpoly B a).natDegree = Module.finrank B F)
    (hlarge : k < Module.finrank B F +
      (Fintype.card ι - f - (S \ T).card)) :
    ((subfield_ca_pair_event_fiber B domainB k a S T).card : ℝ) ≤
      (Nat.card B : ℝ) ^ (k + f) /
        (Nat.card B : ℝ) ^ (S \ T).card := by
  have hsle : (S \ T).card ≤ f := by
    rw [← hS]
    exact Finset.card_le_card Finset.sdiff_subset
  have hsle' : (S \ T).card ≤ k + f := by omega
  have hnat := subfield_ca_pair_fiber_card_le_overlap_branch
    B domainB k a ha S T f hS hT hmin hlarge
  have hcast :
      ((subfield_ca_pair_event_fiber B domainB k a S T).card : ℝ) ≤
        (Nat.card B : ℝ) ^ (k + f - (S \ T).card) := by
    exact_mod_cast hnat
  have hbpos : 0 < Nat.card B := Nat.card_pos
  have hbne : (Nat.card B : ℝ) ≠ 0 := by
    exact_mod_cast hbpos.ne'
  calc
    ((subfield_ca_pair_event_fiber B domainB k a S T).card : ℝ) ≤
        (Nat.card B : ℝ) ^ (k + f - (S \ T).card) := hcast
    _ = (Nat.card B : ℝ) ^ (k + f) /
        (Nat.card B : ℝ) ^ (S \ T).card := by
      rw [pow_sub₀ _ hbne hsle', div_eq_mul_inv]

omit [Nonempty ι] [DecidableEq F] in
private theorem subfield_ca_pair_fiber_card_le_uniform_nat_branch
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (a : F)
    (ha : a ∉ B) (S T : Finset ι) (f : ℕ)
    (hS : S.card = f) (hT : T.card = f)
    (hmin : (minpoly B a).natDegree = Module.finrank B F)
    (hsmall : Module.finrank B F +
      (Fintype.card ι - f - (S \ T).card) ≤ k) :
    (subfield_ca_pair_event_fiber B domainB k a S T).card ≤
      Nat.card B ^
        (2 * (k + f) - Module.finrank B F - Fintype.card ι) := by
  have hsle : (S \ T).card ≤ f := by
    rw [← hS]
    exact Finset.card_le_card Finset.sdiff_subset
  have hdiff := Finset.card_sdiff_add_card_inter S T
  have hunion := Finset.card_union_add_card_inter S T
  have hUle : (S ∪ T).card ≤ Fintype.card ι := by
    simpa only [Finset.card_univ] using
      Finset.card_le_card (Finset.subset_univ (S ∪ T))
  have hdeg := subfield_ca_collision_divisor_nat_degree
    B domainB a S T f hS hT hmin
  have hinter := (subfield_ca_pair_set_card_facts S T f hS hT).1
  calc
    (subfield_ca_pair_event_fiber B domainB k a S T).card ≤
        Nat.card (subfield_ca_pair_parameters B domainB k a S T) :=
      subfield_ca_pair_fiber_card_le_parameters B domainB k a ha S T
    _ ≤ Nat.card B ^ k *
        (Nat.card B ^
            (k - (subfield_ca_collision_divisor B domainB a S T).natDegree) *
          Nat.card B ^ (S ∩ T).card) :=
      subfield_ca_pair_parameters_card_le B domainB k a S T
    _ = Nat.card B ^
        (k + ((k - (Module.finrank B F +
          (Fintype.card ι - f - (S \ T).card))) +
          (f - (S \ T).card))) := by
      rw [hdeg, hinter, ← pow_add, ← pow_add]
    _ = Nat.card B ^
        (2 * (k + f) - Module.finrank B F - Fintype.card ι) := by
      congr 1
      omega

omit [Nonempty ι] [DecidableEq F] in
private theorem subfield_ca_pair_fiber_card_le_uniform_real
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (a : F)
    (ha : a ∉ B) (S T : Finset ι) (f : ℕ)
    (hS : S.card = f) (hT : T.card = f)
    (hmin : (minpoly B a).natDegree = Module.finrank B F)
    (hsmall : Module.finrank B F +
      (Fintype.card ι - f - (S \ T).card) ≤ k) :
    ((subfield_ca_pair_event_fiber B domainB k a S T).card : ℝ) ≤
      (Nat.card B : ℝ) ^ (2 * (k + f)) /
        ((Fintype.card F : ℝ) *
          (Nat.card B : ℝ) ^ Fintype.card ι) := by
  have hsle : (S \ T).card ≤ f := by
    rw [← hS]
    exact Finset.card_le_card Finset.sdiff_subset
  have hdiff := Finset.card_sdiff_add_card_inter S T
  have hunion := Finset.card_union_add_card_inter S T
  have hUle : (S ∪ T).card ≤ Fintype.card ι := by
    simpa only [Finset.card_univ] using
      Finset.card_le_card (Finset.subset_univ (S ∪ T))
  have hfsle : f + (S \ T).card ≤ Fintype.card ι := by omega
  have hexple : Module.finrank B F + Fintype.card ι ≤ 2 * (k + f) := by
    omega
  have hexp :
      2 * (k + f) - Module.finrank B F - Fintype.card ι =
        2 * (k + f) - (Module.finrank B F + Fintype.card ι) := by
    omega
  have hnat := subfield_ca_pair_fiber_card_le_uniform_nat_branch
    B domainB k a ha S T f hS hT hmin hsmall
  have hcast :
      ((subfield_ca_pair_event_fiber B domainB k a S T).card : ℝ) ≤
        (Nat.card B : ℝ) ^
          (2 * (k + f) - Module.finrank B F - Fintype.card ι) := by
    exact_mod_cast hnat
  have hbpos : 0 < Nat.card B := Nat.card_pos
  have hbne : (Nat.card B : ℝ) ≠ 0 := by
    exact_mod_cast hbpos.ne'
  have hcard :
      (Fintype.card F : ℝ) =
        (Nat.card B : ℝ) ^ Module.finrank B F := by
    exact_mod_cast subfield_ca_card_eq_pow_finrank B
  have hden :
      (Fintype.card F : ℝ) *
          (Nat.card B : ℝ) ^ Fintype.card ι =
        (Nat.card B : ℝ) ^
          (Module.finrank B F + Fintype.card ι) := by
    rw [hcard, pow_add]
  calc
    ((subfield_ca_pair_event_fiber B domainB k a S T).card : ℝ) ≤
        (Nat.card B : ℝ) ^
          (2 * (k + f) - Module.finrank B F - Fintype.card ι) := hcast
    _ = (Nat.card B : ℝ) ^
          (2 * (k + f) - (Module.finrank B F + Fintype.card ι)) := by
      rw [hexp]
    _ = (Nat.card B : ℝ) ^ (2 * (k + f)) /
        (Nat.card B : ℝ) ^
          (Module.finrank B F + Fintype.card ι) := by
      rw [pow_sub₀ _ hbne hexple, div_eq_mul_inv]
    _ = (Nat.card B : ℝ) ^ (2 * (k + f)) /
        ((Fintype.card F : ℝ) *
          (Nat.card B : ℝ) ^ Fintype.card ι) := by
      rw [hden]

omit [Nonempty ι] [DecidableEq F] in
private theorem subfield_ca_pair_fiber_card_le_real
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (a : F)
    (ha : a ∉ B) (S T : Finset ι) (f : ℕ)
    (hS : S.card = f) (hT : T.card = f)
    (hmin : (minpoly B a).natDegree = Module.finrank B F) :
    ((subfield_ca_pair_event_fiber B domainB k a S T).card : ℝ) ≤
      (Nat.card B : ℝ) ^ (k + f) /
          (Nat.card B : ℝ) ^ (S \ T).card +
        (Nat.card B : ℝ) ^ (2 * (k + f)) /
          ((Fintype.card F : ℝ) *
            (Nat.card B : ℝ) ^ Fintype.card ι) := by
  by_cases hsmall : Module.finrank B F +
      (Fintype.card ι - f - (S \ T).card) ≤ k
  · have h := subfield_ca_pair_fiber_card_le_uniform_real
      B domainB k a ha S T f hS hT hmin hsmall
    have hnon : 0 ≤ (Nat.card B : ℝ) ^ (k + f) /
        (Nat.card B : ℝ) ^ (S \ T).card := by positivity
    exact h.trans (le_add_of_nonneg_left hnon)
  · have hlarge : k < Module.finrank B F +
        (Fintype.card ι - f - (S \ T).card) :=
      Nat.lt_of_not_ge hsmall
    have h := subfield_ca_pair_fiber_card_le_overlap_real
      B domainB k a ha S T f hS hT hmin hlarge
    have hnon : 0 ≤ (Nat.card B : ℝ) ^ (2 * (k + f)) /
        ((Fintype.card F : ℝ) *
          (Nat.card B : ℝ) ^ Fintype.card ι) := by positivity
    exact h.trans (le_add_of_nonneg_right hnon)

private theorem subfield_ca_pow_ratio_le_exp_sub
    (t : ℝ) (r : ℕ) (hrpos : 0 < r) (hrle : (r : ℝ) ≤ t) :
    (t / (r : ℝ)) ^ r ≤ Real.exp (t - r) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hrpos
  have ht : 0 < t := lt_of_lt_of_le hrR hrle
  have hu : 0 < t / (r : ℝ) := div_pos ht hrR
  have hlog := Real.log_le_sub_one_of_pos hu
  have hmul :
      (r : ℝ) * Real.log (t / (r : ℝ)) ≤ t - r := by
    calc
      (r : ℝ) * Real.log (t / (r : ℝ)) ≤
          (r : ℝ) * (t / (r : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left hlog hrR.le
      _ = t - r := by field_simp
  have hexp :
      Real.exp ((r : ℝ) * Real.log (t / (r : ℝ))) ≤
        Real.exp (t - r) := Real.exp_le_exp.mpr hmul
  calc
    (t / (r : ℝ)) ^ r =
        (Real.exp (Real.log (t / (r : ℝ)))) ^ r := by
      rw [Real.exp_log hu]
    _ = Real.exp ((r : ℝ) * Real.log (t / (r : ℝ))) := by
      rw [Real.exp_nat_mul]
    _ ≤ Real.exp (t - r) := hexp

private theorem subfield_ca_floor_mode_le_stirling
    (t : ℝ) (r : ℕ) (hrpos : 0 < r) (hrle : (r : ℝ) ≤ t) :
    t ^ r / (r.factorial : ℝ) ≤
      Real.exp t / Real.sqrt (2 * Real.pi * (r : ℝ)) := by
  have hrR : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hrpos
  have hrne : (r : ℝ) ≠ 0 := hrR.ne'
  have ht : 0 < t := lt_of_lt_of_le hrR hrle
  have hdarg : (0 : ℝ) < 2 * Real.pi * (r : ℝ) := by positivity
  have hd : 0 < Real.sqrt (2 * Real.pi * (r : ℝ)) :=
    Real.sqrt_pos.2 hdarg
  have hfac : (0 : ℝ) < (r.factorial : ℝ) := by positivity
  have hratio := subfield_ca_pow_ratio_le_exp_sub t r hrpos hrle
  have hst := Stirling.le_factorial_stirling r
  have ht_pow :
      t ^ r = (t / (r : ℝ)) ^ r * (r : ℝ) ^ r := by
    rw [div_pow]
    field_simp [hrne]
  have hr_pow :
      (r : ℝ) ^ r =
        ((r : ℝ) / Real.exp 1) ^ r * (Real.exp 1) ^ r := by
    rw [div_pow]
    field_simp [Real.exp_ne_zero]
  have hratio' :
      (t / (r : ℝ)) ^ r * (Real.exp 1) ^ r ≤
        Real.exp (t - r) * (Real.exp 1) ^ r :=
    mul_le_mul_of_nonneg_right hratio (by positivity)
  have hprod :
      Real.sqrt (2 * Real.pi * (r : ℝ)) * t ^ r ≤
        (r.factorial : ℝ) *
          (Real.exp (t - r) * (Real.exp 1) ^ r) := by
    rw [ht_pow, hr_pow]
    calc
      Real.sqrt (2 * Real.pi * (r : ℝ)) *
          ((t / (r : ℝ)) ^ r *
            (((r : ℝ) / Real.exp 1) ^ r * (Real.exp 1) ^ r)) =
          (Real.sqrt (2 * Real.pi * (r : ℝ)) *
            ((r : ℝ) / Real.exp 1) ^ r) *
            ((t / (r : ℝ)) ^ r * (Real.exp 1) ^ r) := by ring
      _ ≤ (r.factorial : ℝ) *
          (Real.exp (t - r) * (Real.exp 1) ^ r) := by
        exact mul_le_mul hst hratio' (by positivity) hfac.le
  have hexp :
      Real.exp (t - r) * (Real.exp 1) ^ r = Real.exp t := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    ring
  have hcross :
      Real.sqrt (2 * Real.pi * (r : ℝ)) * t ^ r ≤
        Real.exp t * (r.factorial : ℝ) := by
    calc
      Real.sqrt (2 * Real.pi * (r : ℝ)) * t ^ r ≤
          (r.factorial : ℝ) *
            (Real.exp (t - r) * (Real.exp 1) ^ r) := hprod
      _ = Real.exp t * (r.factorial : ℝ) := by rw [hexp]; ring
  apply (div_le_div_iff₀ hfac hd).2
  simpa only [mul_comm] using hcross

open scoped BigOperators in
omit [Nonempty ι] [DecidableEq F] in
private theorem subfield_ca_second_moment_expand
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (δ : NNReal)
    (a : F) :
    subfield_ca_second_moment B domainB k δ a =
      ∑ S ∈ subfield_ca_error_sets (ι := ι) δ,
        ∑ T ∈ subfield_ca_error_sets (ι := ι) δ,
          ((subfield_ca_pair_event_fiber B domainB k a S T).card : ℝ) := by
  classical
  let := Fintype.ofFinite B
  unfold subfield_ca_second_moment
  have hprod := Fintype.sum_prod_type
    (fun z : (ι → B) × F =>
      (subfield_ca_multiplicity B domainB k δ a z.1 z.2 : ℝ) ^ 2)
  rw [← hprod]
  simp_rw [subfield_ca_multiplicity_real_eq_indicator_sum, pow_two,
    Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  exact subfield_ca_pair_indicator_sum_eq_fiber_card B domainB k a S T

private theorem subfield_ca_sqrt_floor_facts (x : ℝ) (hx : 3 / 2 < x) :
    0 ≤ x ∧
      1 < Real.sqrt x ∧
      0 < ⌊Real.sqrt x⌋₊ ∧
      (⌊Real.sqrt x⌋₊ : ℝ) ≤ Real.sqrt x ∧
      Real.sqrt x < (⌊Real.sqrt x⌋₊ : ℝ) + 1 ∧
      x = (Real.sqrt x) ^ 2 := by
  have hx0 : 0 ≤ x := by linarith
  have ht : 1 < Real.sqrt x := by
    rw [Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num
    linarith
  have hrpos : 0 < ⌊Real.sqrt x⌋₊ :=
    Nat.floor_pos.mpr (le_of_lt ht)
  have hrle : (⌊Real.sqrt x⌋₊ : ℝ) ≤ Real.sqrt x :=
    Nat.floor_le (Real.sqrt_nonneg x)
  have htlt : Real.sqrt x < (⌊Real.sqrt x⌋₊ : ℝ) + 1 := by
    exact Nat.lt_floor_add_one (Real.sqrt x)
  exact ⟨hx0, ht, hrpos, hrle, htlt, (Real.sq_sqrt hx0).symm⟩

private theorem subfield_ca_bessel_term_le_mode
    (x : ℝ) (hx : 3 / 2 < x) (s : ℕ) :
    (Real.sqrt x) ^ s / (s.factorial : ℝ) ≤
      (Real.sqrt x) ^ ⌊Real.sqrt x⌋₊ /
        (⌊Real.sqrt x⌋₊.factorial : ℝ) := by
  obtain ⟨hx0, _ht, _hrpos, hrle, htlt, _hsq⟩ :=
    subfield_ca_sqrt_floor_facts x hx
  exact subfield_ca_exp_term_le_floor_mode
    (Real.sqrt x) ⌊Real.sqrt x⌋₊ s (Real.sqrt_nonneg x) hrle htlt

open scoped BigOperators in
private theorem subfield_ca_bessel_partial_le_factor_large
    (x : ℝ) (m : ℕ) (hx : 3 / 2 < x) :
    subfield_ca_bessel_partial x m ≤ subfieldCaFactor x := by
  obtain ⟨hx0, _ht, hrpos, hrle, htlt, hsq⟩ :=
    subfield_ca_sqrt_floor_facts x hx
  rw [subfieldCaFactor, if_neg (not_le.mpr hx)]
  unfold subfield_ca_bessel_partial
  let t : ℝ := Real.sqrt x
  let r : ℕ := ⌊Real.sqrt x⌋₊
  have ht0 : 0 ≤ t := by dsimp only [t]; exact Real.sqrt_nonneg x
  have hsq_t : x = t ^ 2 := by simpa only [t] using hsq
  have hterm_eq (s : ℕ) :
      x ^ s / ((s.factorial : ℝ) ^ 2) =
        (t ^ s / (s.factorial : ℝ)) ^ 2 := by
    rw [hsq_t, div_pow]
    congr 1
    calc
      (t ^ 2) ^ s = t ^ (2 * s) := (pow_mul t 2 s).symm
      _ = t ^ (s * 2) := by rw [Nat.mul_comm]
      _ = (t ^ s) ^ 2 := pow_mul t s 2
  have hpoint (s : ℕ) :
      (t ^ s / (s.factorial : ℝ)) ^ 2 ≤
        (t ^ r / (r.factorial : ℝ)) *
          (t ^ s / (s.factorial : ℝ)) := by
    have hmode :
        t ^ s / (s.factorial : ℝ) ≤
          t ^ r / (r.factorial : ℝ) := by
      dsimp only [t, r]
      exact subfield_ca_exp_term_le_floor_mode
        (Real.sqrt x) ⌊Real.sqrt x⌋₊ s (Real.sqrt_nonneg x) hrle htlt
    have hnon : 0 ≤ t ^ s / (s.factorial : ℝ) := by positivity
    rw [pow_two]
    exact mul_le_mul_of_nonneg_right hmode hnon
  have hsum :
      (∑ s ∈ Finset.range (m + 1),
          x ^ s / ((s.factorial : ℝ) ^ 2)) ≤
        (t ^ r / (r.factorial : ℝ)) *
          ∑ s ∈ Finset.range (m + 1),
            t ^ s / (s.factorial : ℝ) := by
    calc
      (∑ s ∈ Finset.range (m + 1),
          x ^ s / ((s.factorial : ℝ) ^ 2)) =
          ∑ s ∈ Finset.range (m + 1),
            (t ^ s / (s.factorial : ℝ)) ^ 2 := by
        apply Finset.sum_congr rfl
        intro s hs
        exact hterm_eq s
      _ ≤ ∑ s ∈ Finset.range (m + 1),
          (t ^ r / (r.factorial : ℝ)) *
            (t ^ s / (s.factorial : ℝ)) := by
        apply Finset.sum_le_sum
        intro s hs
        exact hpoint s
      _ = (t ^ r / (r.factorial : ℝ)) *
          ∑ s ∈ Finset.range (m + 1),
            t ^ s / (s.factorial : ℝ) := by
        rw [Finset.mul_sum]
  have hmode_bound :
      t ^ r / (r.factorial : ℝ) ≤
        Real.exp t / Real.sqrt (2 * Real.pi * (r : ℝ)) := by
    apply subfield_ca_floor_mode_le_stirling
    · exact hrpos
    · exact hrle
  have hpartial :
      (∑ s ∈ Finset.range (m + 1),
          t ^ s / (s.factorial : ℝ)) ≤ Real.exp t := by
    exact Real.sum_le_exp_of_nonneg ht0 (m + 1)
  have hpartial_nonneg :
      0 ≤ ∑ s ∈ Finset.range (m + 1),
          t ^ s / (s.factorial : ℝ) := by
    apply Finset.sum_nonneg
    intro s hs
    exact div_nonneg (pow_nonneg ht0 s) (by positivity)
  have hmode_rhs_nonneg :
      0 ≤ Real.exp t / Real.sqrt (2 * Real.pi * (r : ℝ)) :=
    div_nonneg (Real.exp_nonneg t) (Real.sqrt_nonneg _)
  calc
    (∑ s ∈ Finset.range (m + 1),
        x ^ s / ((s.factorial : ℝ) ^ 2)) ≤
        (t ^ r / (r.factorial : ℝ)) *
          ∑ s ∈ Finset.range (m + 1),
            t ^ s / (s.factorial : ℝ) := hsum
    _ ≤ (Real.exp t / Real.sqrt (2 * Real.pi * (r : ℝ))) *
        Real.exp t := by
      exact mul_le_mul hmode_bound hpartial hpartial_nonneg hmode_rhs_nonneg
    _ = Real.exp (2 * Real.sqrt x) /
        Real.sqrt (2 * Real.pi * (⌊Real.sqrt x⌋₊ : ℝ)) := by
      dsimp only [t, r]
      rw [div_mul_eq_mul_div, ← Real.exp_add]
      congr 2
      ring

private theorem subfield_ca_bessel_partial_le_factor
    (x : ℝ) (m : ℕ) (hx : 0 ≤ x) :
    subfield_ca_bessel_partial x m ≤ subfieldCaFactor x := by
  by_cases hxle : x ≤ 3 / 2
  · exact subfield_ca_bessel_partial_le_factor_small x m hx hxle
  · exact subfield_ca_bessel_partial_le_factor_large x m (lt_of_not_ge hxle)

private theorem subfield_ca_overlap_sum_le_factor
    (n f b : ℕ) (hf : f ≤ n) (hb : 0 < b) :
    subfield_ca_overlap_sum n f b ≤
      subfieldCaFactor (((f : ℝ) * (n - f : ℕ)) / b) := by
  apply le_trans (subfield_ca_overlap_sum_le_bessel n f b hf hb)
  apply subfield_ca_bessel_partial_le_factor
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg f) (Nat.cast_nonneg (n - f)))
    (Nat.cast_nonneg b)

private theorem subfield_ca_support_algebra
    (A N H M G : ℝ)
    (hA : 0 < A) (hN : 0 < N) (hH : 0 ≤ H) (hHN : H ≤ N)
    (hG : 0 ≤ G)
    (hfirst : A ^ 2 ≤ H * M)
    (hsecond : M ≤ A ^ 2 / N + A * G) :
    1 - N * G / A ≤ H / N := by
  have hchain : A ^ 2 ≤ H * (A ^ 2 / N + A * G) :=
    hfirst.trans (mul_le_mul_of_nonneg_left hsecond hH)
  have hchainN := mul_le_mul_of_nonneg_right hchain hN.le
  field_simp [hN.ne'] at hchainN
  have herror : H * (N * G) ≤ N * (N * G) :=
    mul_le_mul_of_nonneg_right hHN (mul_nonneg hN.le hG)
  have hcross : A * N ≤ H * A + N ^ 2 * G := by
    nlinarith only [hchainN, herror]
  apply (le_div_iff₀ hN).2
  apply le_of_mul_le_mul_right (a := A) ?_ hA
  field_simp [hA.ne']
  nlinarith only [hcross]

open scoped BigOperators in
omit [Nonempty ι] [DecidableEq F] in
private theorem subfield_ca_support_card_eq_sum_good_scalars
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (δ : NNReal)
    (a : F) :
    letI := Fintype.ofFinite B
    (subfield_ca_support B domainB k δ a).card =
      ∑ y : ι → B, (subfield_ca_good_scalars B domainB k δ a y).card := by
  classical
  let := Fintype.ofFinite B
  unfold subfield_ca_support subfield_ca_good_scalars
  simp_rw [Finset.card_filter]
  exact Fintype.sum_prod_type
    (fun z : (ι → B) × F =>
      if 0 < subfield_ca_multiplicity B domainB k δ a z.1 z.2 then 1 else 0)

open scoped BigOperators in
omit [Nonempty ι] [DecidableEq F] in
private theorem subfield_ca_exists_center_from_support
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (δ : NNReal)
    (a : F) :
    ∃ y : ι → B,
      ((subfield_ca_support B domainB k δ a).card : ℝ) /
          ((Fintype.card F : ℝ) *
            (Nat.card B : ℝ) ^ Fintype.card ι) ≤
        ((subfield_ca_good_scalars B domainB k δ a y).card : ℝ) /
          (Fintype.card F : ℝ) := by
  classical
  let := Fintype.ofFinite B
  let H : ℝ := (subfield_ca_support B domainB k δ a).card
  let N : ℝ := (Fintype.card F : ℝ) *
    (Nat.card B : ℝ) ^ Fintype.card ι
  let Q : ℝ := Fintype.card F
  have hbne : (Nat.card B : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := B)).ne'
  have hQne : Q ≠ 0 := by
    dsimp only [Q]
    exact_mod_cast Fintype.card_ne_zero
  have hsupportR : H =
      ∑ y : ι → B,
        ((subfield_ca_good_scalars B domainB k δ a y).card : ℝ) := by
    dsimp only [H]
    exact_mod_cast subfield_ca_support_card_eq_sum_good_scalars
      B domainB k δ a
  have hsum_eq :
      (∑ _y : ι → B, H / N) =
        ∑ y : ι → B,
          ((subfield_ca_good_scalars B domainB k δ a y).card : ℝ) / Q := by
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [← Finset.sum_div]
    rw [← hsupportR]
    rw [Finset.card_univ, Fintype.card_fun,
      ← Nat.card_eq_fintype_card]
    push_cast
    dsimp only [N]
    field_simp [hbne, hQne]
    dsimp only [Q]
  have hsum_le :
      (∑ y ∈ (Finset.univ : Finset (ι → B)), H / N) ≤
        ∑ y ∈ (Finset.univ : Finset (ι → B)),
          ((subfield_ca_good_scalars B domainB k δ a y).card : ℝ) / Q := by
    simpa only using hsum_eq.le
  obtain ⟨y, _hyuniv, hy⟩ := Finset.exists_le_of_sum_le
    (s := (Finset.univ : Finset (ι → B)))
    (f := fun _y => H / N)
    (g := fun y =>
      ((subfield_ca_good_scalars B domainB k δ a y).card : ℝ) / Q)
    Finset.univ_nonempty hsum_le
  refine ⟨y, ?_⟩
  simpa only [H, N, Q] using hy

omit [Nonempty ι] [DecidableEq F] in
private theorem subfield_ca_support_card_le_ambient
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (δ : NNReal)
    (a : F) :
    ((subfield_ca_support B domainB k δ a).card : ℝ) ≤
      (Fintype.card F : ℝ) *
        (Nat.card B : ℝ) ^ Fintype.card ι := by
  classical
  let := Fintype.ofFinite B
  have hnat :
      (subfield_ca_support B domainB k δ a).card ≤
        Fintype.card ((ι → B) × F) := by
    calc
      (subfield_ca_support B domainB k δ a).card ≤
          (Finset.univ : Finset ((ι → B) × F)).card := by
        unfold subfield_ca_support
        exact Finset.card_le_card (Finset.filter_subset _ _)
      _ = Fintype.card ((ι → B) × F) := Finset.card_univ
  have hreal :
      ((subfield_ca_support B domainB k δ a).card : ℝ) ≤
        (Fintype.card ((ι → B) × F) : ℝ) := by
    exact_mod_cast hnat
  calc
    ((subfield_ca_support B domainB k δ a).card : ℝ) ≤
        (Fintype.card ((ι → B) × F) : ℝ) := hreal
    _ = (Fintype.card F : ℝ) *
        (Nat.card B : ℝ) ^ Fintype.card ι := by
      rw [Fintype.card_prod, Fintype.card_fun,
        ← Nat.card_eq_fintype_card]
      push_cast
      ring

open scoped BigOperators in
omit [Nonempty ι] [DecidableEq F] in
private theorem subfield_ca_support_first_second
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (δ : NNReal)
    (a : F)
    (hkf : k + ⌊(δ : ℝ) * Fintype.card ι⌋₊ < Fintype.card ι) :
    let f := ⌊(δ : ℝ) * Fintype.card ι⌋₊
    let A : ℝ := (Nat.choose (Fintype.card ι) f : ℝ) *
      (Nat.card B : ℝ) ^ (k + f)
    A ^ 2 ≤
      ((subfield_ca_support B domainB k δ a).card : ℝ) *
        subfield_ca_second_moment B domainB k δ a := by
  classical
  let := Fintype.ofFinite B
  dsimp only
  let f := ⌊(δ : ℝ) * Fintype.card ι⌋₊
  let A : ℝ := (Nat.choose (Fintype.card ι) f : ℝ) *
    (Nat.card B : ℝ) ^ (k + f)
  let X : ((ι → B) × F) → ℕ := fun z =>
    subfield_ca_multiplicity B domainB k δ a z.1 z.2
  have h := finite_support_second_moment X
  rw [subfield_ca_first_moment_real_eq B domainB k δ a hkf] at h
  rw [Fintype.sum_prod_type] at h
  change A ^ 2 ≤
    ((subfield_ca_support B domainB k δ a).card : ℝ) *
      subfield_ca_second_moment B domainB k δ a at h
  exact h

open scoped BigOperators in
omit [Nonempty ι] [DecidableEq ι] [DecidableEq F] in
private theorem subfield_ca_uniform_contribution_eq
    (B : Subfield F) (k : ℕ) (δ : NNReal) :
    let f := ⌊(δ : ℝ) * Fintype.card ι⌋₊
    (∑ _S ∈ subfield_ca_error_sets (ι := ι) δ,
      ∑ _T ∈ subfield_ca_error_sets (ι := ι) δ,
        (Nat.card B : ℝ) ^ (2 * (k + f)) /
          ((Fintype.card F : ℝ) *
            (Nat.card B : ℝ) ^ Fintype.card ι)) =
      (((Nat.choose (Fintype.card ι) f : ℝ) *
          (Nat.card B : ℝ) ^ (k + f)) ^ 2) /
        ((Fintype.card F : ℝ) *
          (Nat.card B : ℝ) ^ Fintype.card ι) := by
  classical
  dsimp only
  let f := ⌊(δ : ℝ) * Fintype.card ι⌋₊
  change (∑ _S ∈ subfield_ca_error_sets (ι := ι) δ,
      ∑ _T ∈ subfield_ca_error_sets (ι := ι) δ,
        (Nat.card B : ℝ) ^ (2 * (k + f)) /
          ((Fintype.card F : ℝ) *
            (Nat.card B : ℝ) ^ Fintype.card ι)) =
    (((Nat.choose (Fintype.card ι) f : ℝ) *
        (Nat.card B : ℝ) ^ (k + f)) ^ 2) /
      ((Fintype.card F : ℝ) *
        (Nat.card B : ℝ) ^ Fintype.card ι)
  rw [Finset.sum_const, nsmul_eq_mul, Finset.sum_const, nsmul_eq_mul]
  rw [subfield_ca_error_sets_card]
  rw [show 2 * (k + f) = (k + f) * 2 by omega, pow_mul]
  dsimp only [f]
  ring

open scoped BigOperators in
omit [Nonempty ι] [DecidableEq F] in
private theorem subfield_ca_second_moment_le_overlap
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (δ : NNReal)
    (a : F) (ha : a ∉ B)
    (hmin : (minpoly B a).natDegree = Module.finrank B F) :
    let f := ⌊(δ : ℝ) * Fintype.card ι⌋₊
    let A := (Nat.choose (Fintype.card ι) f : ℝ) *
      (Nat.card B : ℝ) ^ (k + f)
    let N := (Fintype.card F : ℝ) *
      (Nat.card B : ℝ) ^ Fintype.card ι
    subfield_ca_second_moment B domainB k δ a ≤
      A ^ 2 / N +
        A * subfield_ca_overlap_sum (Fintype.card ι) f (Nat.card B) := by
  classical
  dsimp only
  let f := ⌊(δ : ℝ) * Fintype.card ι⌋₊
  let A : ℝ := (Nat.choose (Fintype.card ι) f : ℝ) *
    (Nat.card B : ℝ) ^ (k + f)
  let N : ℝ := (Fintype.card F : ℝ) *
    (Nat.card B : ℝ) ^ Fintype.card ι
  change subfield_ca_second_moment B domainB k δ a ≤
    A ^ 2 / N +
      A * subfield_ca_overlap_sum (Fintype.card ι) f (Nat.card B)
  rw [subfield_ca_second_moment_expand]
  calc
    (∑ S ∈ subfield_ca_error_sets (ι := ι) δ,
        ∑ T ∈ subfield_ca_error_sets (ι := ι) δ,
          ((subfield_ca_pair_event_fiber B domainB k a S T).card : ℝ)) ≤
        ∑ S ∈ subfield_ca_error_sets (ι := ι) δ,
          ∑ T ∈ subfield_ca_error_sets (ι := ι) δ,
            ((Nat.card B : ℝ) ^ (k + f) /
                (Nat.card B : ℝ) ^ (S \ T).card +
              (Nat.card B : ℝ) ^ (2 * (k + f)) /
                ((Fintype.card F : ℝ) *
                  (Nat.card B : ℝ) ^ Fintype.card ι)) := by
      apply Finset.sum_le_sum
      intro S hS
      apply Finset.sum_le_sum
      intro T hT
      exact subfield_ca_pair_fiber_card_le_real B domainB k a ha S T f
        ((subfield_ca_error_sets_mem_iff_card δ S).mp hS)
        ((subfield_ca_error_sets_mem_iff_card δ T).mp hT) hmin
    _ = (∑ S ∈ subfield_ca_error_sets (ι := ι) δ,
          ∑ T ∈ subfield_ca_error_sets (ι := ι) δ,
            (Nat.card B : ℝ) ^ (k + f) /
              (Nat.card B : ℝ) ^ (S \ T).card) +
        (∑ _S ∈ subfield_ca_error_sets (ι := ι) δ,
          ∑ _T ∈ subfield_ca_error_sets (ι := ι) δ,
            (Nat.card B : ℝ) ^ (2 * (k + f)) /
              ((Fintype.card F : ℝ) *
                (Nat.card B : ℝ) ^ Fintype.card ι)) := by
      simp_rw [Finset.sum_add_distrib]
    _ = A ^ 2 / N +
        A * subfield_ca_overlap_sum (Fintype.card ι) f (Nat.card B) := by
      rw [subfield_ca_overlap_contribution_eq,
        subfield_ca_uniform_contribution_eq]
      dsimp only [A, N, f]
      ring

omit [Nonempty ι] [DecidableEq F] in
private theorem subfield_ca_second_moment_le_factor
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (δ : NNReal)
    (a : F) (ha : a ∉ B)
    (hmin : (minpoly B a).natDegree = Module.finrank B F)
    (hf : ⌊(δ : ℝ) * Fintype.card ι⌋₊ ≤ Fintype.card ι) :
    let f := ⌊(δ : ℝ) * Fintype.card ι⌋₊
    let A := (Nat.choose (Fintype.card ι) f : ℝ) *
      (Nat.card B : ℝ) ^ (k + f)
    let N := (Fintype.card F : ℝ) *
      (Nat.card B : ℝ) ^ Fintype.card ι
    subfield_ca_second_moment B domainB k δ a ≤
      A ^ 2 / N +
        A * subfieldCaFactor
          (((f : ℝ) * (Fintype.card ι - f : ℕ)) / Nat.card B) := by
  dsimp only
  let f := ⌊(δ : ℝ) * Fintype.card ι⌋₊
  let A : ℝ := (Nat.choose (Fintype.card ι) f : ℝ) *
    (Nat.card B : ℝ) ^ (k + f)
  let N : ℝ := (Fintype.card F : ℝ) *
    (Nat.card B : ℝ) ^ Fintype.card ι
  change subfield_ca_second_moment B domainB k δ a ≤
    A ^ 2 / N +
      A * subfieldCaFactor
        (((f : ℝ) * (Fintype.card ι - f : ℕ)) / Nat.card B)
  have hover := subfield_ca_overlap_sum_le_factor
    (Fintype.card ι) f (Nat.card B) hf Nat.card_pos
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  calc
    subfield_ca_second_moment B domainB k δ a ≤
        A ^ 2 / N +
          A * subfield_ca_overlap_sum (Fintype.card ι) f (Nat.card B) := by
      exact subfield_ca_second_moment_le_overlap B domainB k δ a ha hmin
    _ ≤ A ^ 2 / N +
        A * subfieldCaFactor
          (((f : ℝ) * (Fintype.card ι - f : ℕ)) / Nat.card B) := by
      exact add_le_add_right (mul_le_mul_of_nonneg_left hover hA) _

open scoped BigOperators in
omit [Nonempty ι] [DecidableEq F] in
private theorem subfield_ca_support_density_lower_nat
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (δ : NNReal)
    (a : F) (ha : a ∉ B)
    (hmin : (minpoly B a).natDegree = Module.finrank B F)
    (hkf : k + ⌊(δ : ℝ) * Fintype.card ι⌋₊ < Fintype.card ι)
    (hchoose : Nat.choose (Fintype.card ι)
      ⌊(δ : ℝ) * Fintype.card ι⌋₊ ≠ 0) :
    let f := ⌊(δ : ℝ) * Fintype.card ι⌋₊
    let N : ℝ := (Fintype.card F : ℝ) *
      (Nat.card B : ℝ) ^ Fintype.card ι
    1 - (Fintype.card F : ℝ) *
          (Nat.card B : ℝ) ^ (Fintype.card ι - k - f) *
          subfieldCaFactor
            (((f : ℝ) * (Fintype.card ι - f : ℕ)) / Nat.card B) /
          (Nat.choose (Fintype.card ι) f : ℝ) ≤
      ((subfield_ca_support B domainB k δ a).card : ℝ) / N := by
  classical
  let := Fintype.ofFinite B
  dsimp only
  let f := ⌊(δ : ℝ) * Fintype.card ι⌋₊
  let C := Nat.choose (Fintype.card ι) f
  let A : ℝ := (C : ℝ) * (Nat.card B : ℝ) ^ (k + f)
  let N : ℝ := (Fintype.card F : ℝ) *
    (Nat.card B : ℝ) ^ Fintype.card ι
  let H : ℝ := (subfield_ca_support B domainB k δ a).card
  let M : ℝ := subfield_ca_second_moment B domainB k δ a
  let G : ℝ := subfieldCaFactor
    (((f : ℝ) * (Fintype.card ι - f : ℕ)) / Nat.card B)
  change 1 - (Fintype.card F : ℝ) *
        (Nat.card B : ℝ) ^ (Fintype.card ι - k - f) * G / (C : ℝ) ≤
    H / N
  have hf_le : f ≤ Fintype.card ι := by omega
  have hkf_le : k + f ≤ Fintype.card ι := Nat.le_of_lt hkf
  have hb : 0 < Nat.card B := Nat.card_pos
  have hC : 0 < C := Nat.pos_of_ne_zero hchoose
  have hA : 0 < A := by
    dsimp only [A]
    positivity
  have hN : 0 < N := by
    dsimp only [N]
    positivity
  have hH : 0 ≤ H := by
    dsimp only [H]
    positivity
  have hHN : H ≤ N := by
    dsimp only [H, N]
    exact subfield_ca_support_card_le_ambient B domainB k δ a
  have hG : 0 ≤ G := by
    dsimp only [G]
    exact subfield_ca_factor_nonneg _
  have hfirst : A ^ 2 ≤ H * M := by
    dsimp only [A, C, H, M, f]
    exact subfield_ca_support_first_second B domainB k δ a hkf
  have hsecond : M ≤ A ^ 2 / N + A * G := by
    dsimp only [M, A, C, N, G, f]
    exact subfield_ca_second_moment_le_factor B domainB k δ a ha hmin hf_le
  have halg : 1 - N * G / A ≤ H / N :=
    subfield_ca_support_algebra A N H M G hA hN hH hHN hG hfirst hsecond
  have hcancel : N * G / A =
      (Fintype.card F : ℝ) *
        (Nat.card B : ℝ) ^ (Fintype.card ι - k - f) * G / (C : ℝ) := by
    dsimp only [A, N, C]
    exact subfield_ca_density_error_term_eq
      (Fintype.card ι) k f (Nat.card B) (Fintype.card F) C G
      hkf_le hb hC
  calc
    1 - (Fintype.card F : ℝ) *
          (Nat.card B : ℝ) ^ (Fintype.card ι - k - f) * G / (C : ℝ) =
        1 - N * G / A := by rw [hcancel]
    _ ≤ H / N := halg

open scoped BigOperators in
omit [Nonempty ι] [DecidableEq ι] [DecidableEq F] in
private theorem subfield_ca_exists_good_center_nat
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (δ : NNReal)
    (a : F) (ha : a ∉ B)
    (hmin : (minpoly B a).natDegree = Module.finrank B F)
    (hkf : k + ⌊(δ : ℝ) * Fintype.card ι⌋₊ < Fintype.card ι)
    (hchoose : Nat.choose (Fintype.card ι)
      ⌊(δ : ℝ) * Fintype.card ι⌋₊ ≠ 0) :
    let f := ⌊(δ : ℝ) * Fintype.card ι⌋₊
    ∃ y : ι → B,
      1 - (Fintype.card F : ℝ) *
            (Nat.card B : ℝ) ^ (Fintype.card ι - k - f) *
            subfieldCaFactor
              (((f : ℝ) * (Fintype.card ι - f : ℕ)) / Nat.card B) /
            (Nat.choose (Fintype.card ι) f : ℝ) ≤
        ((subfield_ca_good_scalars B domainB k δ a y).card : ℝ) /
          (Fintype.card F : ℝ) := by
  classical
  dsimp only
  obtain ⟨y, hy⟩ := subfield_ca_exists_center_from_support
    B domainB k δ a
  refine ⟨y, ?_⟩
  exact (subfield_ca_support_density_lower_nat
    B domainB k δ a ha hmin hkf hchoose).trans hy

private def subfield_domain (domain : ι ↪ F) (B : Subfield F)
    (hdom : ∀ i, domain i ∈ B) : ι ↪ B :=
  { toFun := fun i => ⟨domain i, hdom i⟩
    inj' := by
      intro i j hij
      apply domain.injective
      exact congrArg Subtype.val hij }

omit [Nonempty ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
private theorem subfield_domain_card_le [Finite F] (domain : ι ↪ F) (B : Subfield F)
    (hdom : ∀ i, domain i ∈ B) : Fintype.card ι ≤ Nat.card B := by
  let e : ι ↪ B :=
    { toFun := fun i => ⟨domain i, hdom i⟩
      inj' := by
        intro i j hij
        apply domain.injective
        exact congrArg Subtype.val hij }
  rw [← Nat.card_eq_fintype_card]
  exact Finite.card_le_of_embedding e

omit [Fintype F] [DecidableEq F] in
private theorem subfield_primitive_not_mem
    (B : Subfield F) (hB : B < ⊤) (a : F)
    (ha : IntermediateField.adjoin B ({a} : Set F) = ⊤) : a ∉ B := by
  intro haB
  have ha_bot : a ∈ (⊥ : IntermediateField B F) := by
    rw [IntermediateField.mem_bot, Subfield.algebraMap_ofSubfield B]
    exact ⟨⟨a, haB⟩, rfl⟩
  have hadj_bot : IntermediateField.adjoin B ({a} : Set F) = ⊥ :=
    IntermediateField.adjoin_simple_eq_bot_iff.mpr ha_bot
  have htop_bot : (⊤ : IntermediateField B F) = ⊥ := ha.symm.trans hadj_bot
  have hB_top : B = ⊤ := by
    apply top_unique
    intro x _
    have hxbot : x ∈ (⊥ : IntermediateField B F) := by
      rw [← htop_bot]
      trivial
    rw [IntermediateField.mem_bot, Subfield.algebraMap_ofSubfield B] at hxbot
    obtain ⟨b, hb⟩ := hxbot
    rw [← hb]
    exact b.property
  exact (ne_of_lt hB) hB_top

omit [Fintype F] [DecidableEq F] in
private theorem subfield_ca_generator_not_mem
    (B : Subfield F) (hB : B < ⊤) (g : Fˣ)
    (hg : ∀ y : Fˣ, y ∈ Submonoid.powers g) : (g : F) ∉ B := by
  exact subfield_primitive_not_mem B hB (g : F)
    (subfield_ca_generator_adjoin_eq_top B g hg)

omit [DecidableEq F] in
private theorem subfield_ca_generator_degree_card
    (B : Subfield F) (hB : B < ⊤) (g : Fˣ)
    (hg : ∀ y : Fˣ, y ∈ Submonoid.powers g) :
    (minpoly B (g : F)).natDegree = Module.finrank B F ∧
      Fintype.card F = Nat.card B ^ Module.finrank B F ∧
      (g : F) ∉ B := by
  exact ⟨subfield_ca_generator_minpoly_nat_degree B g hg,
    subfield_ca_card_eq_pow_finrank B,
    subfield_ca_generator_not_mem B hB g hg⟩

omit [Fintype F] [DecidableEq F] in
private theorem subfield_ca_exists_primitive_center [Finite F]
    (B : Subfield F) (hB : B < ⊤) :
    ∃ a : F, a ∉ B ∧
      (minpoly B a).natDegree = Module.finrank B F := by
  obtain ⟨g, hg⟩ := exists_subfield_multiplicative_generator (F := F)
  have hdeg := subfield_ca_generator_minpoly_nat_degree B g hg
  have hnot := subfield_ca_generator_not_mem B hB g hg
  exact ⟨(g : F), hnot, hdeg⟩

omit [DecidableEq ι] in
private theorem subfield_radius_parameter_facts
    (k : ℕ) (δ : NNReal)
    (h_int : ((⌊(δ : ℝ) * Fintype.card ι⌋₊ : ℝ)) =
      (δ : ℝ) * Fintype.card ι)
    (hδ_pos : 0 < δ)
    (hδ_lt : (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ι) :
    let f := ⌊(δ : ℝ) * Fintype.card ι⌋₊
    (δ : ℝ) < 1 ∧ k < Fintype.card ι ∧ 0 < f ∧
      k + f < Fintype.card ι ∧ Nat.choose (Fintype.card ι) f ≠ 0 := by
  dsimp only
  have hnN : 0 < Fintype.card ι := Fintype.card_pos
  have hnR : (0 : ℝ) < Fintype.card ι := by exact_mod_cast hnN
  have hn_ne : (Fintype.card ι : ℝ) ≠ 0 := hnR.ne'
  have hkdiv_nonneg : (0 : ℝ) ≤ (k : ℝ) / Fintype.card ι :=
    div_nonneg (Nat.cast_nonneg k) hnR.le
  have hδ_one : (δ : ℝ) < 1 :=
    lt_of_lt_of_le hδ_lt (sub_le_self 1 hkdiv_nonneg)
  have hδR_pos : (0 : ℝ) < δ := by exact_mod_cast hδ_pos
  have hkdiv_lt : (k : ℝ) / Fintype.card ι < 1 := by
    linarith only [hδ_lt, hδR_pos]
  have hkR : (k : ℝ) < Fintype.card ι :=
    (div_lt_one hnR).mp hkdiv_lt
  have hk : k < Fintype.card ι := by exact_mod_cast hkR
  have hfR : (0 : ℝ) < (⌊(δ : ℝ) * Fintype.card ι⌋₊ : ℝ) := by
    rw [h_int]
    exact mul_pos hδR_pos hnR
  have hf : 0 < ⌊(δ : ℝ) * Fintype.card ι⌋₊ := by exact_mod_cast hfR
  have hadddiv : (δ : ℝ) + (k : ℝ) / Fintype.card ι < 1 := by
    linarith only [hδ_lt]
  have hquot :
      ((k : ℝ) + (δ : ℝ) * Fintype.card ι) / Fintype.card ι < 1 := by
    calc
      ((k : ℝ) + (δ : ℝ) * Fintype.card ι) / Fintype.card ι =
          (δ : ℝ) + (k : ℝ) / Fintype.card ι := by
        field_simp [hn_ne]
        ring
      _ < 1 := hadddiv
  have hsumR : (k : ℝ) + (δ : ℝ) * Fintype.card ι < Fintype.card ι := by
    have h := (div_lt_iff₀ hnR).mp hquot
    simpa using h
  have hkfR : (k : ℝ) + (⌊(δ : ℝ) * Fintype.card ι⌋₊ : ℝ) <
      Fintype.card ι := by
    rw [h_int]
    exact hsumR
  have hkf : k + ⌊(δ : ℝ) * Fintype.card ι⌋₊ < Fintype.card ι := by
    exact_mod_cast hkfR
  have hf_le : ⌊(δ : ℝ) * Fintype.card ι⌋₊ ≤ Fintype.card ι := by omega
  exact ⟨hδ_one, hk, hf, hkf, Nat.choose_ne_zero hf_le⟩

open scoped NNReal in
omit [DecidableEq ι] in
private theorem subfield_ca_exists_witness_data
    (domain : ι ↪ F) (k : ℕ) (δ : NNReal) (B : Subfield F)
    (hB : B < ⊤)
    (hdom : ∀ i, domain i ∈ B)
    (hint : ((⌊(δ : ℝ) * Fintype.card ι⌋₊ : ℝ)) =
      (δ : ℝ) * Fintype.card ι)
    (hδpos : 0 < δ)
    (hδlt : (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ι) :
    ∃ (u : Fin 2 → ι → F) (G : Finset F),
      SubfieldCaWitnessData domain k δ B u G := by
  classical
  let := Fintype.ofFinite B
  let domainB : ι ↪ B := subfield_domain domain B hdom
  obtain ⟨hδone, _hk, _hfpos, hkf, hchoose⟩ :=
    subfield_radius_parameter_facts (ι := ι) k δ hint hδpos hδlt
  obtain ⟨a, ha, hmin⟩ := subfield_ca_exists_primitive_center B hB
  obtain ⟨y, hy⟩ := subfield_ca_exists_good_center_nat
    B domainB k δ a ha hmin hkf hchoose
  let u : Fin 2 → ι → F := subfield_ca_reciprocal_stack domain B a y
  let G : Finset F := subfield_ca_good_scalars B domainB k δ a y
  have hdomB (i : ι) : (domainB i : F) = domain i := rfl
  have hgood : G ⊆ Finset.univ.filter (fun α : F =>
      Code.relDistFromCode (u 0 + α • u 1)
        (ReedSolomon.code domain k : Set (ι → F)) ≤ δ) := by
    simpa only [u, G] using
      subfield_ca_good_scalars_subset_fold_close B domain domainB
        k δ a y hint ha hdomB
  have hnot : ¬ Code.jointProximity
      (C := (ReedSolomon.code domain k : Set (ι → F)))
      (u := u) δ := by
    simpa only [u] using
      subfield_ca_reciprocal_stack_not_joint domain B k δ a y ha hdom
        hint hδone hkf
  have hn : 0 < Fintype.card ι := Fintype.card_pos
  have hkf_le : k + ⌊(δ : ℝ) * Fintype.card ι⌋₊ ≤ Fintype.card ι :=
    Nat.le_of_lt hkf
  have hf_le : ⌊(δ : ℝ) * Fintype.card ι⌋₊ ≤ Fintype.card ι := by
    omega
  have hpow := subfield_ca_natural_power_eq_rpow
    (Fintype.card ι) k ⌊(δ : ℝ) * Fintype.card ι⌋₊
      (Nat.card B) δ hn hkf_le hint
  have harg := subfield_ca_overlap_argument_eq
    (Fintype.card ι) ⌊(δ : ℝ) * Fintype.card ι⌋₊
      (Nat.card B) δ hf_le hint
  have hy' :
      1 - (Fintype.card F * (Nat.card B : ℝ) ^
          ((Fintype.card ι : ℝ) *
            (1 - (k : ℝ) / Fintype.card ι - (δ : ℝ)))
          * subfieldCaFactor
            ((δ : ℝ) * (1 - δ) * (Fintype.card ι) ^ 2 / Nat.card B)) /
        Nat.choose (Fintype.card ι)
          ⌊(δ : ℝ) * Fintype.card ι⌋₊ ≤
        (G.card : ℝ) / (Fintype.card F : ℝ) := by
    change 1 - (Fintype.card F : ℝ) *
          (Nat.card B : ℝ) ^
            (Fintype.card ι - k - ⌊(δ : ℝ) * Fintype.card ι⌋₊) *
          subfieldCaFactor
            (((⌊(δ : ℝ) * Fintype.card ι⌋₊ : ℝ) *
              (Fintype.card ι - ⌊(δ : ℝ) * Fintype.card ι⌋₊ : ℕ)) /
              Nat.card B) /
          (Nat.choose (Fintype.card ι)
            ⌊(δ : ℝ) * Fintype.card ι⌋₊ : ℝ) ≤
        (G.card : ℝ) / (Fintype.card F : ℝ) at hy
    rw [hpow, harg] at hy
    exact hy
  have hratio :
      (G.card : ℝ) / (Fintype.card F : ℝ) =
        ((((G.card : NNReal) / (Fintype.card F : NNReal)) : NNReal) : ℝ) := by
    rw [NNReal.coe_div]
    norm_num
  have hcard :
      ENNReal.ofReal
        (1 - (Fintype.card F * (Nat.card B : ℝ) ^
            ((Fintype.card ι : ℝ) *
              (1 - (k : ℝ) / Fintype.card ι - (δ : ℝ)))
            * subfieldCaFactor
              ((δ : ℝ) * (1 - δ) * (Fintype.card ι) ^ 2 / Nat.card B)) /
          Nat.choose (Fintype.card ι)
            ⌊(δ : ℝ) * Fintype.card ι⌋₊) ≤
        ((((G.card : NNReal) / (Fintype.card F : NNReal)) : NNReal) : ENNReal) := by
    calc
      ENNReal.ofReal
          (1 - (Fintype.card F * (Nat.card B : ℝ) ^
              ((Fintype.card ι : ℝ) *
                (1 - (k : ℝ) / Fintype.card ι - (δ : ℝ)))
              * subfieldCaFactor
                ((δ : ℝ) * (1 - δ) * (Fintype.card ι) ^ 2 / Nat.card B)) /
            Nat.choose (Fintype.card ι)
              ⌊(δ : ℝ) * Fintype.card ι⌋₊) ≤
          ENNReal.ofReal ((G.card : ℝ) / (Fintype.card F : ℝ)) :=
        ENNReal.ofReal_mono hy'
      _ = ((((G.card : NNReal) / (Fintype.card F : NNReal)) : NNReal) : ENNReal) := by
        rw [hratio, ENNReal.ofReal_coe_nnreal]
  exact ⟨u, G,
    { not_joint := hnot
      good_subset := hgood
      card_lower := hcard }⟩

omit [DecidableEq ι] in
/-- Lower-bounds Reed--Solomon CA error when the evaluation domain lies in a proper
subfield. The analytic correction term is `subfieldCaFactor`. -/
theorem subfield_epsCa_lower_bound
    (domain : ι ↪ F) (k : ℕ) (δ : ℝ≥0) (B : Subfield F)
    (_hB_proper : B < ⊤)
    (_h_dom : ∀ i, domain i ∈ B)
    (_h_int : ((⌊(δ : ℝ) * Fintype.card ι⌋₊ : ℝ)) = (δ : ℝ) * Fintype.card ι)
    (_hδ_pos : 0 < δ)
    (_hδ_lt : (δ : ℝ) < 1 - (k : ℝ) / Fintype.card ι) :
    let n : ℝ := Fintype.card ι
    let ρ : ℝ := k / n
    ENNReal.ofReal
        (1 - (Fintype.card F * (Nat.card B : ℝ) ^ (n * (1 - ρ - δ) : ℝ)
              * subfieldCaFactor ((δ : ℝ) * (1 - δ) * (Fintype.card ι) ^ 2
                  / Nat.card B))
            / (Nat.choose (Fintype.card ι) ⌊(δ : ℝ) * Fintype.card ι⌋₊)) ≤
      epsCa (F := F) (A := F) ((ReedSolomon.code domain k : Set (ι → F))) δ δ := by
  classical
  dsimp only
  obtain ⟨u, G, h⟩ := subfield_ca_exists_witness_data
    domain k δ B _hB_proper _h_dom _h_int _hδ_pos _hδ_lt
  exact subfield_ca_witness_data_eps_ca domain k δ B u G h

end ReedSolomon

end CodingTheory

set_option linter.style.longFile 2700
