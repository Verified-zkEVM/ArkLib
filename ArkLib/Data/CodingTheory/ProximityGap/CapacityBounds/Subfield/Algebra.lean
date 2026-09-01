/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.FieldTheory.PrimitiveElement

/-!
# Algebraic setup for the Reed--Solomon subfield lower bound

This internal stage defines the reciprocal-stack witnesses and events, develops interpolation
and collision-divisor algebra, and establishes the first-moment identities used by
`Subfield.Moments`.

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

namespace SubfieldInternal

def subfield_ca_divisible_degree_lt
    (B : Subfield F) (k : ℕ) (H : Polynomial B) :=
  {r : Polynomial.degreeLT B k // H ∣ (r.1 : Polynomial B)}

structure SubfieldCaPairWitness
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

structure SubfieldCaWitnessData
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
theorem exists_subfield_multiplicative_generator [Finite F] :
    ∃ g : Fˣ, ∀ y : Fˣ, y ∈ Submonoid.powers g := by
  exact IsCyclic.exists_monoid_generator

omit [Fintype F] [DecidableEq F] in
private theorem exists_subfield_primitive_element [Finite F] (B : Subfield F) :
    ∃ a : F, IntermediateField.adjoin B ({a} : Set F) = ⊤ := by
  exact Field.exists_primitive_element_of_finite_top B F

open scoped BigOperators in
theorem finite_support_second_moment
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
noncomputable def subfield_ca_bessel_partial (x : ℝ) (m : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (m + 1), x ^ s / ((s.factorial : ℝ) ^ 2)

open scoped BigOperators in
noncomputable def subfield_ca_collision_divisor
    (B : Subfield F) (domainB : ι ↪ B) (a : F)
    (S T : Finset ι) : Polynomial B :=
  minpoly B a *
    ∏ i ∈ (Finset.univ \ (S ∪ T)),
      (Polynomial.X - Polynomial.C (domainB i))

def subfield_ca_pair_parameters
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (a : F)
    (S T : Finset ι) :=
  Polynomial.degreeLT B k ×
    subfield_ca_divisible_degree_lt B k
      (subfield_ca_collision_divisor B domainB a S T) ×
    (↥(S ∩ T) → B)

noncomputable def subfield_ca_error_sets (δ : NNReal) : Finset (Finset ι) :=
  (Finset.univ : Finset ι).powersetCard ⌊(δ : ℝ) * Fintype.card ι⌋₊

omit [Nonempty ι] [DecidableEq ι] in
theorem subfield_ca_error_sets_card (δ : NNReal) :
    (subfield_ca_error_sets (ι := ι) δ).card =
      Nat.choose (Fintype.card ι) ⌊(δ : ℝ) * Fintype.card ι⌋₊ := by
  classical
  simp only [subfield_ca_error_sets, Finset.card_powersetCard, Finset.card_univ]

omit [Nonempty ι] [DecidableEq ι] in
theorem subfield_ca_error_sets_mem_iff_card (δ : NNReal) (S : Finset ι) :
    S ∈ subfield_ca_error_sets (ι := ι) δ ↔
      S.card = ⌊(δ : ℝ) * Fintype.card ι⌋₊ := by
  classical
  simp only [subfield_ca_error_sets, Finset.mem_powersetCard, Finset.subset_univ, true_and]

def subfield_ca_event (B : Subfield F) (domainB : ι ↪ B)
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

noncomputable def subfield_ca_event_indicator
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (a : F)
    (S : Finset ι) (y : ι → B) (α : F) : ℝ := by
  classical
  exact if subfield_ca_event B domainB k a S y α then 1 else 0

theorem subfield_ca_factor_nonneg (x : ℝ) : 0 ≤ subfieldCaFactor x := by
  rw [subfieldCaFactor]
  split_ifs
  · exact Real.exp_nonneg x
  · exact div_nonneg (Real.exp_nonneg _) (Real.sqrt_nonneg _)

noncomputable def subfield_ca_multiplicity
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

noncomputable def subfield_ca_good_scalars
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (δ : NNReal)
    (a : F) (y : ι → B) : Finset F := by
  classical
  exact Finset.univ.filter
    (fun α : F => 0 < subfield_ca_multiplicity B domainB k δ a y α)

open scoped BigOperators in
noncomputable def subfield_ca_overlap_sum (n f b : ℕ) : ℝ :=
  ∑ s ∈ Finset.range (f + 1),
    ((Nat.choose f s : ℝ) * (Nat.choose (n - f) s : ℝ)) / (b : ℝ) ^ s

noncomputable def subfield_ca_pair_event_fiber
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
theorem subfield_ca_pair_fiber_to_witness_injective
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

def subfield_ca_reciprocal_stack (domain : ι ↪ F) (B : Subfield F)
    (a : F) (y : ι → B) : Fin 2 → ι → F :=
  fun j i =>
    if j = 0 then (y i : F) / (domain i - a)
    else -(1 : F) / (domain i - a)

omit [DecidableEq ι] in
theorem subfield_ca_good_scalars_subset_fold_close
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
theorem subfield_ca_reciprocal_stack_not_joint
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
noncomputable def subfield_ca_second_moment
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (δ : NNReal)
    (a : F) : ℝ := by
  classical
  letI := Fintype.ofFinite B
  exact ∑ y : ι → B, ∑ α : F,
    (subfield_ca_multiplicity B domainB k δ a y α : ℝ) ^ 2

noncomputable def subfield_ca_support
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (δ : NNReal)
    (a : F) : Finset ((ι → B) × F) := by
  classical
  letI := Fintype.ofFinite B
  exact Finset.univ.filter (fun z =>
    0 < subfield_ca_multiplicity B domainB k δ a z.1 z.2)

omit [Nonempty ι] [DecidableEq ι] in
theorem subfield_ca_witness_data_eps_ca
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

theorem subfield_ca_bessel_partial_le_factor_small
    (x : ℝ) (m : ℕ) (hx : 0 ≤ x) (hxle : x ≤ 3 / 2) :
    subfield_ca_bessel_partial x m ≤ subfieldCaFactor x := by
  rw [subfieldCaFactor, if_pos hxle]
  exact subfield_ca_bessel_partial_le_exp x m hx

omit [DecidableEq F] in
theorem subfield_ca_card_eq_pow_finrank (B : Subfield F) :
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
theorem subfield_ca_collision_divisor_monic [Finite F]
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
theorem subfield_ca_collision_divisor_nat_degree_card [Finite F]
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
theorem subfield_ca_degree_lt_card [Finite F] (B : Subfield F) (k : ℕ) :
    Nat.card (Polynomial.degreeLT B k) = Nat.card B ^ k := by
  classical
  calc
    Nat.card (Polynomial.degreeLT B k) = Nat.card (Fin k → B) :=
      Nat.card_congr (Polynomial.degreeLTEquiv B k).toEquiv
    _ = Nat.card B ^ k := by rw [Nat.card_fun, Nat.card_fin]

theorem subfield_ca_density_error_term_eq
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
theorem subfield_ca_divisible_degree_lt_card_le [Finite F]
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

theorem subfield_ca_exp_term_le_floor_mode
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

theorem subfield_ca_exponent_cast_eq
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
theorem subfield_ca_generator_adjoin_eq_top
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
theorem subfield_ca_generator_minpoly_nat_degree [Finite F]
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
theorem subfield_ca_first_moment_real_eq
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
noncomputable def subfield_ca_pair_witness_to_parameters [Finite F]
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
noncomputable def subfield_ca_pair_fiber_to_parameters [Finite F]
    (B : Subfield F) (domainB : ι ↪ B) (k : ℕ) (a : F)
    (ha : a ∉ B) (S T : Finset ι) :
    ↥(subfield_ca_pair_event_fiber B domainB k a S T) →
      subfield_ca_pair_parameters B domainB k a S T :=
  fun z => subfield_ca_pair_witness_to_parameters B domainB k a ha S T
    (subfield_ca_pair_fiber_to_witness B domainB k a S T z)


end SubfieldInternal

end ReedSolomon

end CodingTheory
