/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks, Aleph
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.LinearAlgebra.Matrix.Module

/-!
# Incidence estimates for the univariate-powers MCA bound

This internal module constructs witnesses for bad power challenges and proves the collision,
interpolation, and initial incidence estimates consumed by `CapacityBounds.Powers`.

## References

- [BCGM25] Bafna, Choudhary, Guruswami, and Mardia. Theorem 8.2 and Definition 8.1.
-/

namespace CodingTheory

open scoped NNReal
open CoreDefinitions ProximityGap

/- Internal implementation lemmas for the public univariate-powers MCA bound. -/
namespace PowersInternal

structure PowersBadWitness
    {ι : Type} [Fintype ι]
    {F : Type} [Field F]
    {A : Type} [AddCommMonoid A] [Module F A]
    (C : ModuleCode ι F A) (k : ℕ)
    (U : Fin (k + 1) → ι → A) (x : F) (δ : ℝ) where
  T : Finset ι
  card_ge : (T.card : ℝ) ≥ (Fintype.card ι : ℝ) * (1 - δ)
  w : ι → A
  w_mem : w ∈ C
  combination_eq_on :
    ∀ i ∈ T, ∑ j : Fin (k + 1), (x ^ (j : ℕ)) • U j i = w i
  bad_row :
    ∃ j : Fin (k + 1),
      LinearCode.projectedWord (U j) T ∉ LinearCode.projectedCodeSubmod C T

theorem module_code_eq_of_agree_gt_card_sub_min_dist
    {ι : Type} [Fintype ι]
    {F : Type} [Semiring F]
    {A : Type} [DecidableEq A] [AddCommMonoid A] [Module F A]
    (C : ModuleCode ι F A) {c₁ c₂ : ι → A}
    (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C)
    (hagree : Code.agree c₁ c₂ >
      Fintype.card ι - Code.minDist (C : Set (ι → A))) :
    c₁ = c₂ := by
  apply Code.eq_of_lt_dist hc₁ hc₂
  rw [Code.dist_eq_minDist]
  have hsum := Code.agree_add_hammingDist (u := c₁) (v := c₂)
  omega

theorem module_code_eq_of_eq_on_large_finset
    {ι : Type} [Fintype ι]
    {F : Type} [Semiring F]
    {A : Type} [DecidableEq A] [AddCommMonoid A] [Module F A]
    (C : ModuleCode ι F A) {c₁ c₂ : ι → A}
    (hc₁ : c₁ ∈ C) (hc₂ : c₂ ∈ C) (T : Finset ι)
    (hT : T.card > Fintype.card ι - Code.minDist (C : Set (ι → A)))
    (heq : ∀ i ∈ T, c₁ i = c₂ i) :
    c₁ = c₂ := by
  apply module_code_eq_of_agree_gt_card_sub_min_dist C hc₁ hc₂
  apply lt_of_lt_of_le hT
  unfold Code.agree
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact heq i hi

theorem normalized_module_code_min_dist_le_one
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Semiring F]
    {A : Type} [AddCommMonoid A] [Module F A] [DecidableEq A]
    (C : ModuleCode ι F A) (δmin : NNReal)
    (hδmin : (δmin : ℝ) =
      (Code.minDist (C : Set (ι → A)) : ℝ) / Fintype.card ι) :
    (δmin : ℝ) ≤ 1 := by
  rw [hδmin]
  apply (div_le_one (by exact_mod_cast Fintype.card_pos)).2
  exact_mod_cast (show Code.minDist (C : Set (ι → A)) ≤ Fintype.card ι by
    rw [← Code.dist_eq_minDist]
    exact Code.dist_le_card _)

def powers_bad_seed_embedding
    {F : Type} (B : Finset F) : {x : F // x ∈ B} ↪ F :=
  ⟨Subtype.val, Subtype.val_injective⟩

open scoped BigOperators in
noncomputable def powers_bad_witness_of_is_mca
    {ι : Type} [Fintype ι]
    {F : Type} [Field F] [Fintype F]
    {A : Type} [AddCommMonoid A] [Module F A]
    (C : ModuleCode ι F A) (k : ℕ)
    (U : Fin (k + 1) → ι → A) (x : F) (δ : ℝ)
    (h : CoreDefinitions.IsMCA
      (CoreDefinitions.univariatePowersGenerator F k) C x U δ) :
    PowersBadWitness C k U x δ := by
  classical
  unfold CoreDefinitions.IsMCA at h
  let T : Finset ι := Classical.choose h
  have hT := Classical.choose_spec h
  have hcomb := hT.2.1
  rw [LinearCode.mem_projectedCodeSubmod_iff] at hcomb
  let w : ι → A := Classical.choose hcomb
  have hw := Classical.choose_spec hcomb
  refine ⟨T, hT.1, w, hw.1, ?_, hT.2.2⟩
  intro i hi
  have hpoint := congrFun hw.2 ⟨i, hi⟩
  simpa [w, LinearCode.projectedWord,
    CoreDefinitions.univariatePowersGenerator] using hpoint

open scoped BigOperators in
noncomputable def powers_bad_witness_of_bad_seed_subtype
    {ι : Type} [Fintype ι]
    {F : Type} [Field F] [Fintype F]
    {A : Type} [AddCommMonoid A] [Module F A]
    (C : ModuleCode ι F A) (k : ℕ) (U : Fin (k + 1) → ι → A)
    (δ : ℝ) (B : Finset F)
    (hB : ∀ x : F, x ∈ B ↔
      CoreDefinitions.IsMCA (CoreDefinitions.univariatePowersGenerator F k) C x U δ)
    (x : {x : F // x ∈ B}) :
    PowersBadWitness C k U (powers_bad_seed_embedding B x) δ := by
  apply powers_bad_witness_of_is_mca
  exact (hB x.1).mp x.2

open scoped BigOperators in
theorem powers_bad_witness_w_eq_interpolated_of_eq_on_large_finset
    {ι : Type} [Fintype ι]
    {F : Type} [Field F]
    {A : Type} [DecidableEq A] [AddCommGroup A] [Module F A]
    (C : ModuleCode ι F A) (k : ℕ)
    (U : Fin (k + 1) → ι → A) (x : F) (δ : ℝ)
    (bw : PowersBadWitness C k U x δ)
    (cstar : Fin (k + 1) → ι → A) (hcstar : ∀ j, cstar j ∈ C)
    (T : Finset ι)
    (hTlarge : T.card > Fintype.card ι - Code.minDist (C : Set (ι → A)))
    (hTsub : T ⊆ bw.T)
    (heq : ∀ i ∈ T,
      (∑ j : Fin (k + 1), (x ^ (j : ℕ)) • U j i) =
        ∑ j : Fin (k + 1), (x ^ (j : ℕ)) • cstar j i) :
    bw.w = fun i => ∑ j : Fin (k + 1), (x ^ (j : ℕ)) • cstar j i := by
  let cinterp : ι → A :=
    fun i => ∑ j : Fin (k + 1), (x ^ (j : ℕ)) • cstar j i
  have hcinterp_eq : cinterp =
      ∑ j : Fin (k + 1), (x ^ (j : ℕ)) • cstar j := by
    funext i
    simp [cinterp]
  have hcinterp : cinterp ∈ C := by
    rw [hcinterp_eq]
    exact C.sum_mem fun j _ => C.smul_mem _ (hcstar j)
  apply module_code_eq_of_eq_on_large_finset C bw.w_mem hcinterp T hTlarge
  intro i hi
  calc
    bw.w i = ∑ j : Fin (k + 1), (x ^ (j : ℕ)) • U j i :=
      (bw.combination_eq_on i (hTsub hi)).symm
    _ = ∑ j : Fin (k + 1), (x ^ (j : ℕ)) • cstar j i := heq i hi
    _ = cinterp i := rfl

def powers_common_domain
    {ι : Type} [Fintype ι]
    {A : Type} [DecidableEq A]
    (k : ℕ) (U cstar : Fin (k + 1) → ι → A) : Finset ι :=
  Finset.univ.filter fun i => ∀ j, U j i = cstar j i

theorem powers_bad_witness_exists_mem_not_common_domain
    {ι : Type} [Fintype ι]
    {F : Type} [Field F]
    {A : Type} [DecidableEq A] [AddCommGroup A] [Module F A]
    (C : ModuleCode ι F A) (k : ℕ)
    (U : Fin (k + 1) → ι → A) (x : F) (δ : ℝ)
    (bw : PowersBadWitness C k U x δ)
    (cstar : Fin (k + 1) → ι → A) (hcstar : ∀ j, cstar j ∈ C) :
    ∃ i, i ∈ bw.T ∧ i ∉ powers_common_domain k U cstar := by
  by_contra hnone
  have hsub : bw.T ⊆ powers_common_domain k U cstar := by
    intro i hi
    by_contra hout
    exact hnone ⟨i, hi, hout⟩
  obtain ⟨j, hj⟩ := bw.bad_row
  apply hj
  rw [LinearCode.mem_projectedCodeSubmod_iff]
  refine ⟨cstar j, hcstar j, ?_⟩
  funext i
  have hicommon : (i : ι) ∈ powers_common_domain k U cstar := hsub i.property
  have hrow := (Finset.mem_filter.mp hicommon).2 j
  simpa only [LinearCode.projectedWord, Set.domRestrict_apply] using hrow

def powers_point_degree
    {ι S : Type} [DecidableEq ι]
    (B : Finset S) (T : S → Finset ι) (i : ι) : ℕ :=
  (B.filter fun x => i ∈ T x).card

def powers_radius_base (δmin η : ℝ) : ℝ := 1 - δmin + η

noncomputable def powers_middle_bound (n q : ℕ) (k : ℕ) (δmin η : ℝ) : ℝ :=
  ((n : ℝ) * (1 - powers_radius_base δmin η ^ ((1 : ℝ) / (k + 1))) / η)
      * ((k : ℝ) / q)
    + max
        (2 * (k : ℝ) /
          (η * (powers_radius_base δmin η ^ ((1 : ℝ) / (k + 2))
            - powers_radius_base δmin η ^ ((1 : ℝ) / (k + 1))) * q))
        (((k : ℝ) + 1) * ((k : ℝ) + 2) / (η * q))

theorem powers_radius_base_mem_ioo (δmin η : NNReal)
    (hδmin_le : (δmin : ℝ) ≤ 1) (hη : 0 < η) (hηlt : η < δmin) :
    powers_radius_base (δmin : ℝ) (η : ℝ) ∈ Set.Ioo (0 : ℝ) 1 := by
  constructor
  · unfold powers_radius_base
    have hηR : (0 : ℝ) < η := by exact_mod_cast hη
    linarith
  · unfold powers_radius_base
    have hηltR : (η : ℝ) < δmin := by exact_mod_cast hηlt
    linarith

theorem powers_radius_base_mem_ioo_of_module_code
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Semiring F]
    {A : Type} [AddCommMonoid A] [Module F A] [DecidableEq A]
    (C : ModuleCode ι F A) (δmin η : NNReal)
    (hδmin : (δmin : ℝ) =
      (Code.minDist (C : Set (ι → A)) : ℝ) / Fintype.card ι)
    (hη : 0 < η) (hηlt : η < δmin) :
    powers_radius_base (δmin : ℝ) (η : ℝ) ∈ Set.Ioo (0 : ℝ) 1 :=
  powers_radius_base_mem_ioo δmin η
    (normalized_module_code_min_dist_le_one C δmin hδmin) hη hηlt

open scoped BigOperators in
noncomputable def powers_scalar_polynomial
    {F : Type} [Field F]
    {A : Type} [AddCommGroup A] [Module F A]
    (k : ℕ) (φ : A →ₗ[F] F) (v : Fin (k + 1) → A) : Polynomial F :=
  ∑ j : Fin (k + 1),
    Polynomial.C (φ (v j)) * Polynomial.X ^ (j : ℕ)

def powers_tuple_intersection
    {ι S : Type} [Fintype ι] [DecidableEq ι]
    (t : ℕ) (T : S → Finset ι) (xs : Fin t → S) : Finset ι :=
  Finset.univ.filter fun i => ∀ s, i ∈ T (xs s)

theorem powers_alpha_pow_relation
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Semiring F]
    {A : Type} [AddCommMonoid A] [Module F A] [DecidableEq A]
    (C : ModuleCode ι F A) (k : ℕ) (δmin η : NNReal)
    (hδmin : (δmin : ℝ) =
      (Code.minDist (C : Set (ι → A)) : ℝ) / Fintype.card ι)
    (hη : 0 < η) (hηlt : η < δmin) :
    (Fintype.card ι : ℝ) *
        (powers_radius_base (δmin : ℝ) (η : ℝ) ^
          ((1 : ℝ) / (k + 2))) ^ (k + 2) =
      ((Fintype.card ι - Code.minDist (C : Set (ι → A)) : ℕ) : ℝ) +
        (Fintype.card ι : ℝ) * (η : ℝ) := by
  have hr := powers_radius_base_mem_ioo_of_module_code C δmin η hδmin hη hηlt
  have hD : Code.minDist (C : Set (ι → A)) ≤ Fintype.card ι := by
    rw [← Code.dist_eq_minDist]
    exact Code.dist_le_card _
  have hnpos : (0 : ℝ) < Fintype.card ι := by
    exact_mod_cast Fintype.card_pos
  have hnne : (Fintype.card ι : ℝ) ≠ 0 := hnpos.ne'
  have hpow :
      (powers_radius_base (δmin : ℝ) (η : ℝ) ^
        ((1 : ℝ) / (k + 2))) ^ (k + 2) =
        powers_radius_base (δmin : ℝ) (η : ℝ) := by
    rw [one_div]
    convert Real.rpow_inv_natCast_pow (n := k + 2) hr.1.le (by omega) using 1
    all_goals norm_num
  have hδmul : (δmin : ℝ) * (Fintype.card ι : ℝ) =
      (Code.minDist (C : Set (ι → A)) : ℝ) := by
    calc
      (δmin : ℝ) * (Fintype.card ι : ℝ) =
          ((Code.minDist (C : Set (ι → A)) : ℝ) /
            Fintype.card ι) * (Fintype.card ι : ℝ) := by rw [hδmin]
      _ = (Code.minDist (C : Set (ι → A)) : ℝ) :=
        div_mul_cancel₀ _ hnne
  rw [hpow, Nat.cast_sub hD]
  unfold powers_radius_base
  nlinarith

theorem powers_bad_seed_final_arithmetic
    (η B c G N M : ℝ) (hη : 0 < η)
    (hlower : η * B - c ≤ G) (hupper : G ≤ N)
    (hcM : c / η ≤ M) :
    B ≤ N / η + M := by
  have hmul : B * η ≤ N + c := by
    nlinarith
  have hdiv : B ≤ (N + c) / η :=
    (le_div_iff₀ hη).2 hmul
  have hsplit : (N + c) / η = N / η + c / η := by
    field_simp [hη.ne']
  rw [hsplit] at hdiv
  linarith

open scoped ProbabilityTheory in
theorem powers_bad_seed_probability_le_card
    {S : Type} [Fintype S] [Nonempty S]
    (P : S → Prop) (B : ℝ)
    (hB : (Set.ncard {x : S | P x} : ℝ) ≤ B) :
    (PMF.uniformOfFintype S).map P True ≤ ENNReal.ofReal (B / Fintype.card S) := by
  classical
  change Pr_{let x ← $ᵖ S}[P x] ≤ ENNReal.ofReal (B / Fintype.card S)
  rw [Probability.prob_uniform_eq_ofReal]
  apply ENNReal.ofReal_le_ofReal
  have hset : {x : S | P x} = (Finset.filter P Finset.univ : Set S) := by
    ext x
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
  have hcard : ((Finset.filter P Finset.univ).card : ℝ) =
      (Set.ncard {x : S | P x} : ℝ) := by
    rw [hset, Set.ncard_coe_finset]
  rw [hcard]
  exact div_le_div_of_nonneg_right hB (by positivity)

theorem powers_choose_two_cast (k : ℕ) :
    2 * (Nat.choose (k + 2) 2 : ℝ) =
      ((k : ℝ) + 1) * ((k : ℝ) + 2) := by
  rw [Nat.cast_choose_two]
  push_cast
  ring

theorem powers_collision_tuple_card_le
    {S : Type} [Fintype S] [DecidableEq S]
    (t : ℕ) (i j : Fin (t + 1)) (hij : i ≠ j) :
    (Finset.univ.filter fun xs : Fin (t + 1) → S => xs i = xs j).card ≤
      (Fintype.card S) ^ t := by
  classical
  let C := {xs : Fin (t + 1) → S // xs i = xs j}
  let f : C → (Fin t → S) := fun xs => Fin.removeNth j xs.1
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    funext p
    by_cases hp : p = j
    · subst p
      obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hij
      have hi : x.1 i = y.1 i := by
        have hzxy := congrFun hxy z
        simpa [f, Fin.removeNth, hz] using hzxy
      calc
        x.1 j = x.1 i := x.2.symm
        _ = y.1 i := hi
        _ = y.1 j := y.2
    · obtain ⟨z, hz⟩ := Fin.exists_succAbove_eq hp
      have hzxy := congrFun hxy z
      simpa [f, Fin.removeNth, hz] using hzxy
  rw [← Fintype.card_subtype]
  calc
    Fintype.card C ≤ Fintype.card (Fin t → S) :=
      Fintype.card_le_of_injective f hf
    _ = (Fintype.card S) ^ t := by simp

theorem powers_common_domain_difference_ne
    {ι : Type} [Fintype ι]
    {A : Type} [DecidableEq A] [AddCommGroup A]
    (k : ℕ) (U cstar : Fin (k + 1) → ι → A) (i : ι)
    (hi : i ∉ powers_common_domain k U cstar) :
    (fun j : Fin (k + 1) => U j i - cstar j i) ≠ 0 := by
  intro hzero
  apply hi
  simp only [powers_common_domain, Finset.mem_filter, Finset.mem_univ, true_and]
  intro j
  have hj := congrFun hzero j
  simp only [Pi.zero_apply] at hj
  exact sub_eq_zero.mp hj

theorem powers_complement_card_real_le
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (T : Finset ι) (γ : ℝ)
    (hT : (T.card : ℝ) ≥ (Fintype.card ι : ℝ) * (1 - γ)) :
    ((Finset.univ \ T).card : ℝ) ≤ (Fintype.card ι : ℝ) * γ := by
  have hle : T.card ≤ Fintype.card ι := by
    simpa only [← Finset.card_univ] using Finset.card_le_univ T
  rw [Finset.card_univ_sdiff, Nat.cast_sub hle]
  linarith

theorem powers_exponent_strict (k : ℕ) :
    (1 : ℝ) / (k + 2) < (1 : ℝ) / (k + 1) := by
  apply one_div_lt_one_div_of_lt
  · positivity
  · norm_num

open scoped BigOperators in
theorem powers_good_witness_eq_interpolated_of_large_intersection
    {ι : Type} [Fintype ι]
    {F : Type} [Field F]
    {A : Type} [DecidableEq A] [AddCommGroup A] [Module F A]
    (C : ModuleCode ι F A) (k : ℕ)
    (U : Fin (k + 1) → ι → A) (x : F) (δ : ℝ)
    (bw : PowersBadWitness C k U x δ)
    (cstar : Fin (k + 1) → ι → A) (hcstar : ∀ j, cstar j ∈ C)
    (T : Finset ι)
    (hTlarge : T.card > Fintype.card ι - Code.minDist (C : Set (ι → A)))
    (hTbw : T ⊆ bw.T)
    (hTcommon : T ⊆ powers_common_domain k U cstar) :
    bw.w = fun i => ∑ j : Fin (k + 1), (x ^ (j : ℕ)) • cstar j i := by
  apply powers_bad_witness_w_eq_interpolated_of_eq_on_large_finset
    C k U x δ bw cstar hcstar T hTlarge hTbw
  intro i hi
  have hicommon := hTcommon hi
  have hrows := (Finset.mem_filter.mp hicommon).2
  apply Finset.sum_congr rfl
  intro j _
  rw [hrows j]

theorem powers_injective_prefix_of_snoc
    {S : Type} {t : ℕ} (xs : Fin t → S) (x : S)
    (h : Function.Injective (Fin.snoc xs x : Fin (t + 1) → S)) :
    Function.Injective xs := by
  intro a b hab
  have hs :
      (Fin.snoc xs x : Fin (t + 1) → S) a.castSucc =
        (Fin.snoc xs x : Fin (t + 1) → S) b.castSucc := by
    simpa only [Fin.snoc_castSucc] using hab
  exact (Fin.castSucc_injective t) (h hs)

open scoped BigOperators in
open scoped Matrix.Module in
theorem powers_interpolate_module_codewords
    {ι : Type}
    {F : Type} [Field F]
    {A : Type} [AddCommGroup A] [Module F A]
    (C : ModuleCode ι F A) (k : ℕ)
    (xs : Fin (k + 1) → F) (hxs : Function.Injective xs)
    (w : Fin (k + 1) → ι → A) (hw : ∀ s, w s ∈ C) :
    ∃ cstar : Fin (k + 1) → ι → A,
      (∀ j, cstar j ∈ C) ∧
      ∀ s, ∑ j : Fin (k + 1), (xs s ^ (j : ℕ)) • cstar j = w s := by
  classical
  let V : Matrix (Fin (k + 1)) (Fin (k + 1)) F := Matrix.vandermonde xs
  have hdet : V.det ≠ 0 := by
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hxs
  have hunit : IsUnit V.det := isUnit_iff_ne_zero.mpr hdet
  let cstar : Fin (k + 1) → ι → A := V⁻¹ • w
  refine ⟨cstar, ?_, ?_⟩
  · intro j
    change (V⁻¹ • w) j ∈ C
    rw [Matrix.Module.smul_apply]
    exact C.sum_mem fun s _ => C.smul_mem _ (hw s)
  · have hV : V • cstar = w := by
      calc
        V • cstar = V • (V⁻¹ • w) := by rfl
        _ = (V * V⁻¹) • w := (mul_smul V V⁻¹ w).symm
        _ = (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) • w := by
          rw [Matrix.mul_nonsing_inv V hunit]
        _ = w := one_smul _ _
    intro s
    have hs := congrFun hV s
    simpa [V, Matrix.Module.smul_apply, Matrix.vandermonde_apply] using hs

theorem powers_large_branch_arithmetic
    (κ c η Δ B G : ℝ)
    (hη : 0 < η) (hΔ : 0 < Δ) (hc0 : 0 ≤ c)
    (hfirst : 2 * κ / (η * Δ) < B)
    (hsecond : 2 * c / η < B)
    (hG : η * B - c ≤ G) :
    c < η * B ∧ κ < G * Δ := by
  have hden : 0 < η * Δ := mul_pos hη hΔ
  have hfirst' : 2 * κ < B * (η * Δ) :=
    (div_lt_iff₀ hden).mp hfirst
  have hsecond' : 2 * c < B * η :=
    (div_lt_iff₀ hη).mp hsecond
  rw [mul_comm B η] at hsecond'
  have hc : c < η * B := by
    linarith
  have hhalf : η * B / 2 < G := by
    linarith
  have hκhalf : κ < (η * B / 2) * Δ := by
    have heq : B * (η * Δ) = 2 * ((η * B / 2) * Δ) := by ring
    rw [heq] at hfirst'
    linarith
  have hmul : (η * B / 2) * Δ < G * Δ :=
    mul_lt_mul_of_pos_right hhalf hΔ
  exact ⟨hc, lt_trans hκhalf hmul⟩

open scoped BigOperators in
theorem powers_module_zero_set_card_le
    {F : Type} [Field F] [Fintype F]
    {A : Type} [DecidableEq A] [AddCommGroup A] [Module F A]
    (k : ℕ) (v : Fin (k + 1) → A) (hv : v ≠ 0) :
    (Finset.univ.filter fun x : F =>
      ∑ j : Fin (k + 1), (x ^ (j : ℕ)) • v j = 0).card ≤ k := by
  classical
  obtain ⟨j0, hj0⟩ : ∃ j, v j ≠ 0 := by
    by_contra h
    push Not at h
    apply hv
    funext j
    exact h j
  obtain ⟨φ, hφ, _⟩ :=
    Submodule.exists_le_ker_of_notMem
      (p := (⊥ : Submodule F A)) (v := v j0) (by simpa using hj0)
  let p : Polynomial F := powers_scalar_polynomial k φ v
  have hpcoeff : p.coeff (j0 : ℕ) = φ (v j0) := by
    change (∑ b ∈ (Finset.univ : Finset (Fin (k + 1))),
      Polynomial.C (φ (v b)) * Polynomial.X ^ (b : ℕ)).coeff (j0 : ℕ) = _
    rw [Polynomial.finsetSum_coeff]
    rw [Finset.sum_eq_single j0]
    · rw [Polynomial.coeff_C_mul_X_pow, if_pos rfl]
    · intro b _ hb
      have hne : (j0 : ℕ) ≠ (b : ℕ) := by
        intro h
        exact hb (Fin.ext h.symm)
      rw [Polynomial.coeff_C_mul_X_pow, if_neg hne]
    · simp
  have hp : p ≠ 0 := by
    intro hp0
    have hz : p.coeff (j0 : ℕ) = 0 := by rw [hp0]; simp
    exact hφ (hpcoeff ▸ hz)
  have hdeg : p.degree < (k + 1 : ℕ) := by
    simpa [p, powers_scalar_polynomial] using
      (Polynomial.degree_sum_fin_lt (fun j : Fin (k + 1) => φ (v j)))
  have hnat : p.natDegree ≤ k := by
    have hlt : p.natDegree < k + 1 :=
      (Polynomial.natDegree_lt_iff_degree_lt hp).2 hdeg
    omega
  apply le_trans (Polynomial.card_le_degree_of_subset_roots (p := p) (Z :=
    Finset.univ.filter fun x : F =>
      ∑ j : Fin (k + 1), (x ^ (j : ℕ)) • v j = 0) ?_) hnat
  intro x hx
  have hx' : x ∈ Finset.univ.filter (fun x : F =>
      ∑ j : Fin (k + 1), (x ^ (j : ℕ)) • v j = 0) := by simpa using hx
  have hsum := (Finset.mem_filter.mp hx').2
  have hmap : φ (∑ j : Fin (k + 1), (x ^ (j : ℕ)) • v j) = 0 := by
    rw [hsum, map_zero]
  have hmap' : (∑ j : Fin (k + 1), (x ^ (j : ℕ)) * φ (v j)) = 0 := by
    simpa only [map_sum, map_smul, smul_eq_mul] using hmap
  have heval_formula : Polynomial.eval x p =
      ∑ j : Fin (k + 1), φ (v j) * x ^ (j : ℕ) := by
    change Polynomial.eval x
      (∑ j ∈ (Finset.univ : Finset (Fin (k + 1))),
        Polynomial.C (φ (v j)) * Polynomial.X ^ (j : ℕ)) = _
    rw [Polynomial.eval_finsetSum]
    apply Finset.sum_congr rfl
    intro j _
    simp
  have heval : Polynomial.eval x p = 0 := by
    rw [heval_formula]
    calc
      (∑ j : Fin (k + 1), φ (v j) * x ^ (j : ℕ)) =
          ∑ j : Fin (k + 1), x ^ (j : ℕ) * φ (v j) := by
            apply Finset.sum_congr rfl
            intro j _
            exact mul_comm _ _
      _ = 0 := hmap'
  exact (Polynomial.mem_roots hp).2 heval

open scoped BigOperators in
theorem powers_coefficients_eq_of_agree_on_distinct_seeds
    {ι : Type}
    {F : Type} [Field F] [Finite F]
    {A : Type} [AddCommGroup A] [Module F A]
    (k : ℕ) (xs : Fin (k + 1) → F) (hxs : Function.Injective xs)
    (U cstar : Fin (k + 1) → ι → A) (i : ι)
    (hagree : ∀ s : Fin (k + 1),
      (∑ j : Fin (k + 1), (xs s ^ (j : ℕ)) • U j i) =
        ∑ j : Fin (k + 1), (xs s ^ (j : ℕ)) • cstar j i) :
    ∀ j : Fin (k + 1), U j i = cstar j i := by
  classical
  let := Fintype.ofFinite F
  let v : Fin (k + 1) → A := fun j => U j i - cstar j i
  have hvzero : v = 0 := by
    by_contra hv
    have hroot := powers_module_zero_set_card_le (F := F) (A := A) k v hv
    let X : Finset F := Finset.univ.image xs
    have hsubset : X ⊆ Finset.univ.filter (fun x : F =>
        ∑ j : Fin (k + 1), (x ^ (j : ℕ)) • v j = 0) := by
      intro x hx
      obtain ⟨s, -, rfl⟩ := Finset.mem_image.mp hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      dsimp [v]
      simp_rw [smul_sub]
      rw [Finset.sum_sub_distrib, hagree s, sub_self]
    have hcardX : X.card = k + 1 := by
      dsimp [X]
      rw [Finset.card_image_of_injective Finset.univ hxs]
      simp
    have hbad : k + 1 ≤ k := calc
      k + 1 = X.card := hcardX.symm
      _ ≤ (Finset.univ.filter (fun x : F =>
          ∑ j : Fin (k + 1), (x ^ (j : ℕ)) • v j = 0)).card :=
        Finset.card_le_card hsubset
      _ ≤ k := hroot
    omega
  intro j
  have hj := congrFun hvzero j
  dsimp [v] at hj
  exact sub_eq_zero.mp hj

open scoped BigOperators in
theorem powers_coefficients_eq_on_anchor_intersection
    {ι : Type} [Fintype ι]
    {F : Type} [Field F] [Finite F]
    {A : Type} [AddCommGroup A] [Module F A]
    (C : ModuleCode ι F A) (k : ℕ)
    (U : Fin (k + 1) → ι → A) (δ : ℝ)
    (xs : Fin (k + 1) → F) (hxs : Function.Injective xs)
    (bw : (s : Fin (k + 1)) → PowersBadWitness C k U (xs s) δ)
    (cstar : Fin (k + 1) → ι → A)
    (hinterp : ∀ (s : Fin (k + 1)) (i : ι),
      (∑ j : Fin (k + 1), (xs s ^ (j : ℕ)) • cstar j i) = (bw s).w i)
    (i : ι) (hi : ∀ s : Fin (k + 1), i ∈ (bw s).T) :
    ∀ j : Fin (k + 1), U j i = cstar j i := by
  classical
  let := Fintype.ofFinite F
  apply powers_coefficients_eq_of_agree_on_distinct_seeds (F := F) k xs hxs U cstar i
  intro s
  calc
    (∑ j : Fin (k + 1), (xs s ^ (j : ℕ)) • U j i) = (bw s).w i :=
      (bw s).combination_eq_on i (hi s)
    _ = ∑ j : Fin (k + 1), (xs s ^ (j : ℕ)) • cstar j i :=
      (hinterp s i).symm

open scoped BigOperators in
theorem powers_coordinate_agreement_seeds_card_le
    {ι : Type} [Fintype ι]
    {F : Type} [Field F] [Fintype F]
    {A : Type} [DecidableEq A] [AddCommGroup A] [Module F A]
    (k : ℕ) (U cstar : Fin (k + 1) → ι → A) (i : ι)
    (hi : i ∉ powers_common_domain k U cstar) :
    (Finset.univ.filter fun x : F =>
      (∑ j : Fin (k + 1), (x ^ (j : ℕ)) • U j i) =
        ∑ j : Fin (k + 1), (x ^ (j : ℕ)) • cstar j i).card ≤ k := by
  classical
  let v : Fin (k + 1) → A := fun j => U j i - cstar j i
  have hv : v ≠ 0 := powers_common_domain_difference_ne k U cstar i hi
  have hroot := powers_module_zero_set_card_le (F := F) (A := A) k v hv
  have hfilter :
      (Finset.univ.filter fun x : F =>
        (∑ j : Fin (k + 1), (x ^ (j : ℕ)) • U j i) =
          ∑ j : Fin (k + 1), (x ^ (j : ℕ)) • cstar j i) =
      Finset.univ.filter fun x : F =>
        ∑ j : Fin (k + 1), (x ^ (j : ℕ)) • v j = 0 := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro h
      dsimp [v]
      simp_rw [smul_sub]
      rw [Finset.sum_sub_distrib, h, sub_self]
    · intro h
      dsimp [v] at h
      simp_rw [smul_sub] at h
      rw [Finset.sum_sub_distrib] at h
      exact sub_eq_zero.mp h
  rw [hfilter]
  exact hroot

open scoped BigOperators in
theorem powers_middle_good_seeds_card_le
    {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] [Finite F]
    {A : Type} [DecidableEq A] [AddCommGroup A] [Module F A]
    (k : ℕ) (U cstar : Fin (k + 1) → ι → A)
    (Bgood : Finset F) (Bx : F → Finset ι)
    (hext : ∀ x ∈ Bgood,
      ∃ i, i ∈ Bx x ∧ i ∉ powers_common_domain k U cstar)
    (heq : ∀ x ∈ Bgood, ∀ i ∈ Bx x,
      (∑ j : Fin (k + 1), (x ^ (j : ℕ)) • U j i) =
        ∑ j : Fin (k + 1), (x ^ (j : ℕ)) • cstar j i) :
    Bgood.card ≤ (Finset.univ \ powers_common_domain k U cstar).card * k := by
  classical
  let := Fintype.ofFinite F
  let T : Finset ι := Finset.univ \ powers_common_domain k U cstar
  let R : F → ι → Prop := fun x i => i ∈ Bx x
  have hleft : ∀ x ∈ Bgood, 1 ≤ (T.bipartiteAbove R x).card := by
    intro x hx
    obtain ⟨i, hiBx, hiout⟩ := hext x hx
    apply Finset.one_le_card.mpr
    refine ⟨i, ?_⟩
    simp only [Finset.mem_bipartiteAbove, T, R, Finset.mem_sdiff,
      Finset.mem_univ, true_and]
    exact ⟨hiout, hiBx⟩
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
  have hcount := Finset.card_mul_le_card_mul R hleft hright
  simpa [T] using hcount

open scoped BigOperators in
theorem powers_middle_good_seeds_real_card_le
    {ι : Type} [Fintype ι]
    {F : Type} [Field F] [Finite F]
    {A : Type} [DecidableEq A] [AddCommGroup A] [Module F A]
    (k : ℕ) (U cstar : Fin (k + 1) → ι → A)
    (γ : ℝ) (Bgood : Finset F) (Bx : F → Finset ι)
    (hcommon : ((powers_common_domain k U cstar).card : ℝ) ≥
      (Fintype.card ι : ℝ) * (1 - γ))
    (hext : ∀ x ∈ Bgood,
      ∃ i, i ∈ Bx x ∧ i ∉ powers_common_domain k U cstar)
    (heq : ∀ x ∈ Bgood, ∀ i ∈ Bx x,
      (∑ j : Fin (k + 1), (x ^ (j : ℕ)) • U j i) =
        ∑ j : Fin (k + 1), (x ^ (j : ℕ)) • cstar j i) :
    (Bgood.card : ℝ) ≤
      (Fintype.card ι : ℝ) * γ * (k : ℝ) := by
  classical
  let := Fintype.ofFinite F
  have hnat := powers_middle_good_seeds_card_le (F := F) k U cstar Bgood Bx hext heq
  have hreal : (Bgood.card : ℝ) ≤
      ((Finset.univ \ powers_common_domain k U cstar).card : ℝ) * (k : ℝ) := by
    exact_mod_cast hnat
  have hcomp := powers_complement_card_real_le
    (powers_common_domain k U cstar) γ hcommon
  calc
    (Bgood.card : ℝ) ≤
        ((Finset.univ \ powers_common_domain k U cstar).card : ℝ) * (k : ℝ) := hreal
    _ ≤ ((Fintype.card ι : ℝ) * γ) * (k : ℝ) :=
      mul_le_mul_of_nonneg_right hcomp (Nat.cast_nonneg k)
    _ = (Fintype.card ι : ℝ) * γ * (k : ℝ) := rfl

open scoped BigOperators in
theorem powers_middle_good_seeds_real_card_le_embedding
    {ι S : Type} [Fintype ι]
    {F : Type} [Field F] [Finite F]
    {A : Type} [DecidableEq A] [AddCommGroup A] [Module F A]
    (e : S ↪ F) (k : ℕ) (U cstar : Fin (k + 1) → ι → A)
    (γ : ℝ) (Bgood : Finset S) (Bx : S → Finset ι)
    (hcommon : ((powers_common_domain k U cstar).card : ℝ) ≥
      (Fintype.card ι : ℝ) * (1 - γ))
    (hext : ∀ x ∈ Bgood,
      ∃ i, i ∈ Bx x ∧ i ∉ powers_common_domain k U cstar)
    (heq : ∀ x ∈ Bgood, ∀ i ∈ Bx x,
      (∑ j : Fin (k + 1), ((e x) ^ (j : ℕ)) • U j i) =
        ∑ j : Fin (k + 1), ((e x) ^ (j : ℕ)) • cstar j i) :
    (Bgood.card : ℝ) ≤
      (Fintype.card ι : ℝ) * γ * (k : ℝ) := by
  classical
  let := Fintype.ofFinite F
  let T : Finset ι := Finset.univ \ powers_common_domain k U cstar
  let R : S → ι → Prop := fun x i => i ∈ Bx x
  have hleft : ∀ x ∈ Bgood, 1 ≤ (T.bipartiteAbove R x).card := by
    intro x hx
    obtain ⟨i, hiBx, hiout⟩ := hext x hx
    apply Finset.one_le_card.mpr
    refine ⟨i, ?_⟩
    simp only [Finset.mem_bipartiteAbove, T, R, Finset.mem_sdiff,
      Finset.mem_univ, true_and]
    exact ⟨hiout, hiBx⟩
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
  have hnat : Bgood.card ≤
      (Finset.univ \ powers_common_domain k U cstar).card * k := by
    have hcount := Finset.card_mul_le_card_mul R hleft hright
    simpa [T] using hcount
  have hreal : (Bgood.card : ℝ) ≤
      ((Finset.univ \ powers_common_domain k U cstar).card : ℝ) * (k : ℝ) := by
    exact_mod_cast hnat
  have hcomp := powers_complement_card_real_le
    (powers_common_domain k U cstar) γ hcommon
  calc
    (Bgood.card : ℝ) ≤
        ((Finset.univ \ powers_common_domain k U cstar).card : ℝ) * (k : ℝ) := hreal
    _ ≤ ((Fintype.card ι : ℝ) * γ) * (k : ℝ) :=
      mul_le_mul_of_nonneg_right hcomp (Nat.cast_nonneg k)
    _ = (Fintype.card ι : ℝ) * γ * (k : ℝ) := rfl


end PowersInternal

end CodingTheory
