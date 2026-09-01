/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.Subfield.Moments

/-!
# Subfield lower bound for Reed--Solomon correlated agreement

This final stage assembles the support/density argument and primitive-center construction from
the algebraic and moment bounds in `Subfield.Algebra` and `Subfield.Moments`.

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

open SubfieldInternal

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
