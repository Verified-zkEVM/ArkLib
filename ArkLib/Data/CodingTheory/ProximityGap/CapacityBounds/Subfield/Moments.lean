/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.Subfield.Algebra

/-!
# Moment bounds for the Reed--Solomon subfield construction

This internal stage bounds pair fibers and overlap contributions, then develops the
Bessel/floor-mode estimates that control the second moment consumed by `CapacityBounds.Subfield`.

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

namespace SubfieldInternal

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

theorem subfield_ca_natural_power_eq_rpow
    (n k f b : ℕ) (δ : NNReal)
    (hn : 0 < n) (hkf : k + f ≤ n)
    (hint : (f : ℝ) = (δ : ℝ) * n) :
    (b : ℝ) ^ (n - k - f) =
      (b : ℝ) ^ ((n : ℝ) * (1 - (k : ℝ) / n - (δ : ℝ)) : ℝ) := by
  rw [← Real.rpow_natCast]
  rw [subfield_ca_exponent_cast_eq n k f δ hn hkf hint]

theorem subfield_ca_overlap_argument_eq
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
theorem subfield_ca_overlap_contribution_eq
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
theorem subfield_ca_pair_fiber_card_le_real
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
theorem subfield_ca_second_moment_expand
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

theorem subfield_ca_overlap_sum_le_factor
    (n f b : ℕ) (hf : f ≤ n) (hb : 0 < b) :
    subfield_ca_overlap_sum n f b ≤
      subfieldCaFactor (((f : ℝ) * (n - f : ℕ)) / b) := by
  apply le_trans (subfield_ca_overlap_sum_le_bessel n f b hf hb)
  apply subfield_ca_bessel_partial_le_factor
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg f) (Nat.cast_nonneg (n - f)))
    (Nat.cast_nonneg b)


end SubfieldInternal

end ReedSolomon

end CodingTheory
