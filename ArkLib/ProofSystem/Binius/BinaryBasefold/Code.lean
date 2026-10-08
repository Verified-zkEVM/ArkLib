/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude

/-!
# Binary Basefold codes
-/

@[expose] public section

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open Code BerlekampWelch
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

noncomputable section -- expands with 𝔽q in front
variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] -- Should we allow ℓ = 0?
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}


section SoundnessTools
-- In this section, we use the generic notation `steps` instead of `ϑ` to avoid conflicts

/-!
### Binary Basefold Specific Code Definitions

Definitions specific to the Binary Basefold protocol based on the fundamentals document.
-/

/-- The Reed-Solomon code C^(i) for round i in Binary Basefold.
For each i ∈ {0, steps, ..., ℓ}, C(i) is the Reed-Solomon code
RS_{L, S⁽ⁱ⁾}[2^{ℓ+R-i}, 2^{ℓ-i}]. -/
def BBF_Code (i : Fin (ℓ + 1)) : Submodule L ((sDomain 𝔽q β h_ℓ_add_R_rate)
    ⟨i, by
      exact Nat.lt_of_le_of_lt (n := i) (k := r) (m := ℓ) (h₁ := by exact Fin.is_le i)
        (by exact lt_of_add_right_lt h_ℓ_add_R_rate)⟩ → L) :=
  let domain : (sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i, by omega⟩ ↪ L :=
    ⟨fun x => x.val, fun x y h => by exact Subtype.ext h⟩
  ReedSolomon.code (domain := domain) (deg := 2^(ℓ - i.val))

/-- The (minimum) distance d_i of the code C^(i) : `dᵢ := 2^(ℓ + R - i) - 2^(ℓ - i) + 1` -/
def BBF_CodeDistance (ℓ 𝓡 : ℕ) (i : Fin (ℓ + 1)) : ℕ :=
  2^(ℓ + 𝓡 - i.val) - 2^(ℓ - i.val) + 1

/-- Disagreement set Δ : The set of points where two functions disagree.
For functions f^(i+ϑ) and g^(i+ϑ), this is {y ∈ S^(i+ϑ) | f^(i+ϑ)(y) ≠ g^(i+ϑ)(y)}. -/
def disagreementSet (i : Fin ℓ) (steps : ℕ) [NeZero steps] (h_i_add_steps : i.val + steps ≤ ℓ)
    (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i.val + steps, by
    exact Nat.lt_add_of_pos_right_of_le (↑i + steps) ℓ 1 h_i_add_steps⟩) :
  Set ((sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i.val + steps, by omega⟩) :=
  {y | f y ≠ g y}

/-- Fiber-wise disagreement set Δ^(i) : The set of points y ∈ S^(i+ϑ) for which
functions f^(i) and g^(i) are not identical when restricted to the entire fiber
of points in S⁽ⁱ⁾ that maps to y. -/
def fiberwiseDisagreementSet (i : Fin ℓ) (steps : ℕ) [NeZero steps]
    (h_i_add_steps : i.val + steps ≤ ℓ) (f g : OracleFunction 𝔽q β (h_ℓ_add_R_rate :=
      h_ℓ_add_R_rate) ⟨i, by omega⟩) :
  Set ((sDomain 𝔽q β h_ℓ_add_R_rate) ⟨i.val + steps, by omega⟩) :=
  -- The set of points `y ∈ S^{i+steps}` that there exists a
    -- point `x` in its fiber where `f x ≠ g x`
  {y | ∃ x, iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
    (i := ⟨i, by omega⟩) (destIdx := ⟨i.val + steps, by omega⟩) (k := steps)
    (h_destIdx := by simp) (h_destIdx_le := h_i_add_steps) x = y ∧
      f x ≠ g x}

/-- Fiber-wise distance d^(i) : The minimum size of the fiber-wise disagreement set
between f^(i) and any codeword in C^(i). -/
def fiberwiseDistance (i : Fin ℓ) (steps : ℕ) [NeZero steps] (h_i_add_steps : i.val + steps ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i.val, by omega⟩) : ℕ :=
  -- The minimum size of the fiber-wise disagreement set between f^(i) and any codeword in C^(i)
  -- d^(i)(f^(i), C^(i)) := min_{g^(i) ∈ C^(i)} |Δ^(i)(f^(i), g^(i))|
  let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i.val, by omega⟩
  let disagreement_sizes := (fun (g : C_i) =>
    (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g).ncard) '' Set.univ
  sInf disagreement_sizes

/-- Fiberwise closeness : f^(i) is fiberwise close to C^(i) if
2 * d^(i)(f^(i), C^(i)) < d_{i+steps} -/
def fiberwiseClose (i : Fin ℓ) (steps : ℕ) [NeZero steps] (h_i_add_steps : i.val + steps ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
      ⟨i, by omega⟩) : Prop :=
  2 * fiberwiseDistance 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) steps
    (h_i_add_steps := h_i_add_steps) (f := f) < (BBF_CodeDistance ℓ 𝓡 ⟨i + steps, by omega⟩ : ℕ∞)

/-- Hamming closeness : f is close to C in Hamming distance if
2 * d(f, C) < d_i -/
def hammingClose (i : Fin (ℓ + 1)) (f : OracleFunction 𝔽q β
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) : Prop :=
  2 * Code.distFromCode (u := f)
    (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i) <
    (BBF_CodeDistance ℓ 𝓡 i : ℕ∞)

#check hammingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
-- i (f := fun x => 0)
/-- Unique closest codeword : If a function f^(i) is within the unique decoding radius
of the code C^(i), then this gives the unique closest codeword using Berlekamp-Welch decoder. -/
def uniqueClosestCodeword
    (i : Fin (ℓ + 1)) (h_i : i < ℓ + 𝓡)
  (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, i.isLt⟩)
  (h_within_radius : hammingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i f) :
  OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, i.isLt⟩ := by
  -- Set up Berlekamp-Welch parameters
  set domain_size := Fintype.card (sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩)
  set d := Code.distFromCode (u := f)
    (C := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  let e : ℕ := d.toNat
  have h_dist_ne_top : d ≠ ⊤ := by
    intro h_dist_eq_top
    unfold hammingClose at h_within_radius
    unfold d at h_dist_eq_top
    simp only [h_dist_eq_top, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, ENat.mul_top]
      at h_within_radius
    exact not_top_lt h_within_radius
  let k : ℕ := 2^(ℓ - i.val) -- degree bound from BBF_Code definition
  -- Convert domain to Fin format for Berlekamp-Welch
  let domain_to_fin : (sDomain 𝔽q β h_ℓ_add_R_rate)
    ⟨i, by omega⟩ ≃ Fin domain_size := by
    simp only [domain_size]
    rw [sDomain_card 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (h_i := h_i)]
    have h_equiv := sDomainFinEquiv 𝔽q β
      h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (h_i := h_i)
    convert h_equiv
    exact hF₂.out
  -- ωs is the mapping from the point index to the actually point in the domain S^{i}
  let ωs : Fin domain_size → L := fun j => (domain_to_fin.symm j).val
  let f_vals : Fin domain_size → L := fun j => f (domain_to_fin.symm j)
  -- Run Berlekamp-Welch decoder to get P(X) in monomial basis
  have domain_neZero : NeZero domain_size := by
    simp only [domain_size];
    rw [sDomain_card 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (h_i := h_i)]
    exact {
      out := by
        rw [hF₂.out]
        simp only [ne_eq, Nat.pow_eq_zero, OfNat.ofNat_ne_zero, false_and, not_false_eq_true]
    }
  let berlekamp_welch_result : Option L[X] := BerlekampWelch.decoder (F := L) e k ωs f_vals
  have h_ne_none : berlekamp_welch_result ≠ none := by
    -- 1) Choose a codeword achieving minimal Hamming distance (closest codeword).
    let C_i := BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩
    let S := (fun (g : C_i) => Δ₀(f, g)) '' Set.univ
    let SENat := (fun (g : C_i) => (Δ₀(f, g) : ENat)) '' Set.univ
      -- let S_nat := (fun (g : C_i) => hammingDist f g) '' Set.univ
    have hS_nonempty : S.Nonempty := Set.image_nonempty.mpr Set.univ_nonempty
    have h_coe_sinfS_eq_sinfSENat : ↑(sInf S) = sInf SENat := by
      rw [ENat.natCast_sInf (hs := hS_nonempty)]
      simp only [SENat, Set.image_univ, sInf_range]
      simp only [S, Set.image_univ, iInf_range]
    rcases Nat.sInf_mem hS_nonempty with ⟨g_subtype, hg_subtype, hg_min⟩
    rcases g_subtype with ⟨g_closest, hg_mem⟩
    have h_dist_f : hammingDist f g_closest ≤ e := by
      rw [show e = d.toNat from rfl]
      -- The distance `d` is exactly the Hamming distance of `f` to `g_closest` (lifted to `ℕ∞`).
      have h_dist_eq_hamming : d = (hammingDist f g_closest) := by
        -- We found `g_closest` by taking the `sInf` of all distances, and `hg_min`
        -- shows that the distance to `g_closest` achieves this `sInf`.
        have h_distFromCode_eq_sInf : d = sInf SENat := by
          apply le_antisymm
          · -- Part 1 : `d ≤ sInf ...`
            simp only [d, distFromCode]
            apply sInf_le_sInf
            intro a ha
            -- `a` is in `SENat`, so `a = ↑Δ₀(f, g)` for some codeword `g`.
            rcases (Set.mem_image _ _ _).mp ha with ⟨g, _, rfl⟩
            -- We must show `a` is in the set for `d`, which is `{d' | ∃ v, ↑Δ₀(f, v) ≤ d'}`.
            -- We can use `g` itself as the witness `v`, since `↑Δ₀(f, g) ≤ ↑Δ₀(f, g)`.
            use g; simp only [Fin.eta, Subtype.coe_prop, le_refl, and_self]
          · -- Part 2 : `sInf ... ≤ d`
            simp only [d, distFromCode]
            apply le_sInf
            -- Let `d'` be any element in the set that `d` is the infimum of.
            intro d' h_d'
            -- Unpack `h_d'` : there exists some `v` in the code such that
            -- `↑(hammingDist f v) ≤ d'`.
            rcases h_d' with ⟨v, hv_mem, h_dist_v_le_d'⟩
            -- By definition, `sInf SENat` is a lower bound for all elements in `SENat`.
            -- The element `↑(hammingDist f v)` is in `SENat`.
            have h_sInf_le_dist_v : sInf SENat ≤ ↑(hammingDist f v) := by
              apply sInf_le -- ⊢ ↑Δ₀(f, v) ∈ SENat
              rw [Set.mem_image]
              -- ⊢ ∃ x ∈ Set.univ, ↑Δ₀(f, ↑x) = ↑Δ₀(f, v)
              simp only [Fin.eta, Set.mem_univ, Nat.cast_inj, true_and, Subtype.exists, exists_prop]
              -- ⊢ ∃ a ∈ C_i, Δ₀(f, a) = Δ₀(f, v)
              use v
              exact And.symm ⟨rfl, hv_mem⟩
            -- Now, chain the inequalities : `sInf SENat ≤ ↑(dist_to_any_v) ≤ d'`.
            exact h_sInf_le_dist_v.trans h_dist_v_le_d'
        rw [h_distFromCode_eq_sInf, ←h_coe_sinfS_eq_sinfSENat, ←hg_min]
      rw [h_dist_eq_hamming]
      rw [ENat.toNat_natCast]
    -- Get the closest polynomial
    obtain ⟨p, hp_deg_lt, hp_eval⟩ : ∃ p, p ∈ Polynomial.degreeLT L k ∧
      (fun (x : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩)) ↦ p.eval (↑x)) = g_closest := by
      simp only [Fin.eta, BBF_Code, ReedSolomon.code, ReedSolomon.evalOnPoints,
        Submodule.mem_map, LinearMap.coe_mk, AddHom.coe_mk, C_i] at hg_mem
      rcases hg_mem with ⟨p_witness, hp_prop, hp_eq⟩
      exact ⟨p_witness, by simpa [k] using hp_prop, hp_eq⟩
    have natDeg_p_lt_k : p.natDegree < k := by
      simp only [mem_degreeLT] at hp_deg_lt
      by_cases hi : i = ℓ
      · simp only [hi, tsub_self, pow_zero, cast_one, lt_one_iff, k] at ⊢ hp_deg_lt
        by_cases hp_p_eq_0 : p = 0
        · rw [hp_p_eq_0, Polynomial.natDegree_zero];
        · rw [Polynomial.natDegree_eq_of_degree_eq_some]
          have h_deg_p : p.degree = 0 := by
            have h_le_zero : p.degree ≤ 0 := by
              exact WithBot.lt_one_iff_le_zero.mp hp_deg_lt
            have h_deg_ne_bot : p.degree ≠ ⊥ := by
              rw [Polynomial.degree_ne_bot]; omega
            apply le_antisymm h_le_zero (zero_le_degree_iff.mpr hp_p_eq_0)
          simp only [h_deg_p, CharP.cast_eq_zero]
      · by_cases hp_p_eq_0 : p = 0
        · rw [hp_p_eq_0, Polynomial.natDegree_zero];
          have h_i_lt_ℓ : i < ℓ := by omega
          simp only [ofNat_pos, pow_pos, k]
        · rw [Polynomial.natDegree_lt_iff_degree_lt (by omega)]
          exact hp_deg_lt
    have h_decoder_succeeds : BerlekampWelch.decoder e k ωs f_vals = some p := by
      apply BerlekampWelch.decoder_eq_some
      · -- ⊢ `2 * e < d_i = n - k + 1`
        simp only [domain_size, k]; rw [sDomain_card 𝔽q β (h_i := by omega),]
        · -- ⊢ 2 * e < 2 ^ (ℓ + 𝓡 - ↑i) - 2 ^ (ℓ - ↑i) + 1
          simp only [hammingClose, BBF_CodeDistance, cast_add, ENat.natCast_sub, cast_pow,
            cast_ofNat, cast_one] at h_within_radius;
          have h_lt_eq : ↑(2 * Δ₀(f, ↑(BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)).toNat) =
  2 * Δ₀(f, ↑(BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i)) := by
            simp only [cast_mul, cast_ofNat]
            rw [ENat.natCast_toNat]
            exact h_dist_ne_top
          apply ENat.natCast_lt_natCast.mp
          rw [h_lt_eq, hF₂.out]
          exact h_within_radius
      · -- ⊢ `k ≤ domain_size`. This holds by the problem setup.
        simp only [k, domain_size]
        rw [sDomain_card 𝔽q β (h_i := by omega), hF₂.out]
        apply Nat.pow_le_pow_right (by omega) -- ⊢ ℓ - ↑i ≤ ℓ + 𝓡 - ↑⟨↑i, ⋯⟩
        simp only [tsub_le_iff_right]
        omega
      · -- ⊢ Function.Injective ωs
        simp only [ωs]
        -- The composition of two injective functions (`Equiv.symm` and `Subtype.val`) is injective.
        exact Function.Injective.comp Subtype.val_injective (Equiv.injective _)
      · -- ⊢ `p.natDegree < k`. This is true from `hp_deg`.
        exact natDeg_p_lt_k
      · -- ⊢ `Δ₀(f_vals, (fun a ↦ Polynomial.eval a p) ∘ ωs) ≤ e`
        change hammingDist f_vals ((fun a ↦ Polynomial.eval a p) ∘ ωs) ≤ e
        simp only [ωs]
        have h_functions_eq : (fun a ↦ Polynomial.eval a p) ∘ ωs
          = g_closest ∘ domain_to_fin.symm := by
          ext j; simp only [Function.comp_apply, Fin.eta, ωs]
          rw [←hp_eval]
        rw [h_functions_eq]
        -- ⊢ Δ₀(f_vals, g_closest ∘ ⇑domain_to_fin.symm) ≤ e
        simp only [Fin.eta, ge_iff_le, f_vals]
        -- ⊢ Δ₀(fun j ↦ f (domain_to_fin.symm j), g_closest ∘ ⇑domain_to_fin.symm) ≤ e
        calc
          _ ≤ hammingDist f g_closest := by
            apply hammingDist_le_of_outer_comp_injective f g_closest domain_to_fin.symm
              (hg := by exact Equiv.injective domain_to_fin.symm)
          _ ≤ e := by exact h_dist_f
    simp only [ne_eq, berlekamp_welch_result]
    simp only [h_decoder_succeeds, reduceCtorEq, not_false_eq_true]
  let p : L[X] := berlekamp_welch_result.get (Option.ne_none_iff_isSome.mp h_ne_none)
  exact fun x => p.eval x.val

omit [CharP L 2] [DecidableEq 𝔽q] [NeZero ℓ] in
/-- if `d⁽ⁱ⁾(f⁽ⁱ⁾, C⁽ⁱ⁾) < d_{ᵢ₊steps} / 2` (fiberwise distance),
then `d(f⁽ⁱ⁾, C⁽ⁱ⁾) < dᵢ/2` (regular code distance) -/
theorem fiberwise_dist_lt_imp_dist_lt_unique_decoding_radius (i : Fin ℓ) (steps : ℕ)
    [NeZero steps] (h_i_add_steps : i.val + steps ≤ ℓ)
    (f : OracleFunction 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  (h_fw_dist_lt : fiberwiseClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate)
    (i := i) (steps := steps) (h_i_add_steps := h_i_add_steps) (f := f)) :
  hammingClose 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩ f := by
  classical
  unfold fiberwiseClose at h_fw_dist_lt
  unfold hammingClose
  -- 2 * Δ₀(f, ↑(BBF_Code 𝔽q β ⟨↑i, ⋯⟩)) < ↑(BBF_CodeDistance ℓ 𝓡 ⟨↑i, ⋯⟩)
  let d_fw := fiberwiseDistance 𝔽q β (i := i) steps h_i_add_steps f
  let C_i := (BBF_Code 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) ⟨i, by omega⟩)
  let d_H := Code.distFromCode f C_i
  let d_i := BBF_CodeDistance ℓ 𝓡 (⟨i, by omega⟩)
  let d_i_plus_steps := BBF_CodeDistance ℓ 𝓡 ⟨i.val + steps, by omega⟩
  -- `BBF_CodeDistance` is a successor.
  have h_d_i_gt_0 : d_i > 0 := Nat.succ_pos _
  have h_C_i_nonempty : Nonempty C_i := ⟨0⟩
  -- 1. Relate Hamming distance `d_H` to fiber-wise distance `d_fw`.
  obtain ⟨g', h_g'_mem, h_g'_min_card⟩ : ∃ g' ∈ C_i, d_fw
    = (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g').ncard := by
    -- Let `S` be the set of all possible fiber-wise disagreement sizes.
    let S := (fun (g : C_i) => (fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps
      f g).ncard) '' Set.univ
    -- The code `C_i` (a submodule) is non-empty, so `S` is also non-empty.
    have hS_nonempty : S.Nonempty := by
      refine Set.image_nonempty.mpr ?_
      exact Set.univ_nonempty
    -- For a non-empty set of natural numbers, `sInf` is an element of the set.
    have h_sInf_mem : sInf S ∈ S := Nat.sInf_mem hS_nonempty
    -- Since `sInf S` is in the image set `S`, there must be an element `g_subtype` in the domain
    -- (`C_i`) that maps to it. This `g_subtype` is the codeword we're looking for.
    rw [Set.mem_image] at h_sInf_mem
    rcases h_sInf_mem with ⟨g_subtype, _, h_eq⟩
    -- Extract the codeword and its membership proof.
    exact ⟨g_subtype.val, g_subtype.property, by exact id (Eq.symm h_eq)⟩
  -- The Hamming distance to any codeword `g'` is bounded by `d_fw * 2 ^ steps`.
  have h_dist_le_fw_dist_times_fiber_size : (hammingDist f g' : ℕ∞) ≤ d_fw * 2 ^ steps := by
    -- This proves `dist f g' ≤ (fiberwiseDisagreementSet ... f g').ncard * 2 ^ steps`
    -- and lifts to ℕ∞. We prove the `Nat` version `hammingDist f g' ≤ ...`,
    -- which is equivalent.
    change (Δ₀(f, g') : ℕ∞) ≤ ↑d_fw * ((2 ^ steps : ℕ) : ℕ∞)
    rw [←ENat.natCast_mul, ENat.natCast_le_natCast, h_g'_min_card]
    -- Let ΔH be the finset of actually bad x points where f and g' disagree.
    let ΔH := Finset.filter (fun x => f x ≠ g' x) Finset.univ
    have h_dist_eq_card : hammingDist f g' = ΔH.card := by
      simp only [hammingDist, ne_eq, ΔH]
    rw [h_dist_eq_card]
    -- Y_bad is the set of quotient points y that THERE EXISTS a bad fiber point x
    let Y_bad := fiberwiseDisagreementSet 𝔽q β i steps h_i_add_steps f g'
    simp only at * -- simplify domain indices everywhere
    -- ⊢ #ΔH ≤ Y_bad.ncard * 2 ^ steps
    have hFinType_Y_bad : Fintype Y_bad := by exact Fintype.ofFinite ↑Y_bad
    -- Every point of disagreement `x` must belong to a fiber over some `y` in `Y_bad`,
    -- BY DEFINITION of `Y_bad`. Therefore, `ΔH` is a subset of the union of the fibers
    -- of `Y_bad`
    have h_ΔH_subset_bad_fiber_points : ΔH ⊆ Finset.biUnion Y_bad.toFinset
        (t := fun y => ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
          (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y)) ''
          (Finset.univ : Finset (Fin ((2:ℕ)^steps)))).toFinset) := by
      -- ⊢ If any x ∈ ΔH, then x ∈ Union(qMap_total_fiber(y), ∀ y ∈ Y_bad)
      intro x hx_in_ΔH; -- ⊢ x ∈ Union(qMap_total_fiber(y), ∀ y ∈ Y_bad)
      simp only [ΔH, Finset.mem_filter] at hx_in_ΔH
      -- Now we actually apply iterated qMap into x to get y_of_x,
      -- then x ∈ qMap_total_fiber(y_of_x) by definition
      let y_of_x := iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
        (i := ⟨i, by omega⟩) (destIdx := ⟨i.val + steps, by omega⟩) (k := steps)
        (h_destIdx := by simp) (h_destIdx_le := h_i_add_steps) x
      apply Finset.mem_biUnion.mpr; use y_of_x
      -- ⊢ y_of_x ∈ Y_bad.toFinset ∧ x ∈ qMap_total_fiber(y_of_x)
      -- one bad fiber point of y_of_x is x itself
      have h_elemenet_Y_bad : y_of_x ∈ Y_bad.toFinset :=
        Set.mem_toFinset.mpr ⟨x, rfl, hx_in_ΔH.2⟩
      simp only [h_elemenet_Y_bad, true_and]
      simp only [coe_univ, Set.image_univ, Set.toFinset_range, mem_image, mem_univ, true_and]
      use (pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by omega) (x := x))
      have h_res := is_fiber_iff_generates_quotient_point 𝔽q β i steps (by omega)
        (x := x) (y := y_of_x).mp (by rfl)
      exact h_res
    -- ⊢ #ΔH ≤ Y_bad.ncard * 2 ^ steps
    -- The cardinality of a subset is at most the cardinality of the superset.
    apply (Finset.card_le_card h_ΔH_subset_bad_fiber_points).trans
    -- The cardinality of a disjoint union is the sum of cardinalities.
    rw [Finset.card_biUnion]
    · -- The size of the sum is the number of bad fibers (`Y_bad.ncard`) times
      -- the size of each fiber (`2 ^ steps`).
      simp only [Set.toFinset_card]
      have h_card_fiber_per_quotient_point := card_qMap_total_fiber 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i steps h_i_add_steps
      simp only [Set.image_univ, Fintype.card_ofFinset,
        Subtype.forall] at h_card_fiber_per_quotient_point
      have h_card_fiber_of_each_y : ∀ y ∈ Y_bad.toFinset,
          Fintype.card ((qMap_total_fiber 𝔽q β (i := ⟨↑i, by omega⟩) (steps := steps)
            (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y)) ''
            ↑(Finset.univ : Finset (Fin ((2:ℕ)^steps)))) = 2 ^ steps := by
        intro y hy_in_Y_bad
        have hy_card_fiber_of_y := h_card_fiber_per_quotient_point (a := y) (b := by
          exact Submodule.coe_mem y)
        simp only [coe_univ, Set.image_univ, Fintype.card_ofFinset, hy_card_fiber_of_y]
      rw [Finset.sum_congr rfl h_card_fiber_of_each_y]
      -- ⊢ ∑ x ∈ Y_bad.toFinset, 2 ^ steps ≤ Y_bad.encard.toNat * 2 ^ steps
      simp only [sum_const, Set.toFinset_card, smul_eq_mul, ge_iff_le]
      conv_rhs => rw [←_root_.Nat.card_coe_set_eq] -- convert .ncard back to .card
      -- ⊢ Fintype.card ↑Y_bad ≤ Nat.card ↑Y_bad
      simp only [card_eq_fintype_card, Y_bad, le_refl]
    · -- Prove that the fibers for distinct quotient points y₁, y₂ are disjoint.
      intro y₁ hy₁ y₂ hy₂ hy_ne
      have h_disjoint := qMap_total_fiber_disjoint (i := ⟨↑i, by omega⟩) (steps := steps)
        (h_i_add_steps := by omega) (y₁ := y₁) (y₂ := y₂) (hy_ne := hy_ne)
      simp only [Function.onFun, coe_univ]
      exact h_disjoint
  -- The minimum distance `d_H` is bounded by the distance to this specific `g'`.
  have h_dist_bridge : d_H ≤ d_fw * 2 ^ steps := by
    -- exact h_dist_le_fw_dist_times_fiber_size
    apply le_trans (a := d_H) (c := d_fw * 2 ^ steps) (b := hammingDist f g')
    · -- ⊢ d_H ≤ ↑Δ₀(f, g')
      simp only [distFromCode, SetLike.mem_coe, hammingDist, ne_eq, d_H];
      -- ⊢ Δ₀(f, C_i) ≤ ↑Δ₀(f, g')
      -- ⊢ sInf {d | ∃ v ∈ C_i, ↑(#{i | f i ≠ v i}) ≤ d} ≤ ↑(#{i | f i ≠ g' i})
      apply sInf_le
      use g'
    · exact h_dist_le_fw_dist_times_fiber_size
  -- 2. Use the premise : `2 * d_fw < d_{i+steps}`.
  -- As a `Nat` inequality, this is equivalent to `2 * d_fw ≤ d_{i+steps} - 1`.
  have h_fw_bound : 2 * d_fw ≤ d_i_plus_steps - 1 := by
    -- Convert the ENat inequality to a Nat inequality using `a < b ↔ a + 1 ≤ b`.
    exact Nat.le_of_lt_succ (WithTop.coe_lt_coe.1 h_fw_dist_lt)
  -- 3. The Algebraic Identity.
  -- The core of the proof is the identity : `(d_{i+steps} - 1) * 2 ^ steps = d_i - 1`.
  have h_algebraic_identity : (d_i_plus_steps - 1) * 2 ^ steps = d_i - 1 := by
    dsimp [d_i, d_i_plus_steps, BBF_CodeDistance]
    rw [Nat.sub_mul, ←Nat.pow_add, ←Nat.pow_add];
    have h1 : ℓ + 𝓡 - (↑i + steps) + steps = ℓ + 𝓡 - i := by
      rw [← Nat.sub_sub, Nat.sub_add_cancel
        (Nat.le_sub_of_add_le' (h_i_add_steps.trans (Nat.le_add_right ℓ 𝓡)))]
    have h2 : (ℓ - (↑i + steps) + steps) = ℓ - i := by
      rw [← Nat.sub_sub, Nat.sub_add_cancel (Nat.le_sub_of_add_le' h_i_add_steps)]
    rw [h1, h2]
  -- 4. Conclusion : Chain the inequalities to prove `2 * d_H < d_i`.
  -- We know `d_H` is finite, since `C_i` is nonempty.
  have h_dH_ne_top : d_H ≠ ⊤ := by
    simp only [ne_eq, d_H]
    rw [Code.distFromCode_eq_top_iff_empty f C_i]
    exact Set.nonempty_iff_ne_empty'.mp h_C_i_nonempty
  -- We can now work with the `Nat` value of `d_H`.
  let d_H_nat := ENat.toNat d_H
  have h_dH_eq : d_H = d_H_nat := (ENat.natCast_toNat h_dH_ne_top).symm
  -- The calculation is now done entirely in `Nat`.
  have h_final_inequality : 2 * d_H_nat ≤ d_i - 1 := by
    have h_bridge_nat : d_H_nat ≤ d_fw * 2 ^ steps := by
        rw [←ENat.natCast_le_natCast]
        exact le_of_eq_of_le (id (Eq.symm h_dH_eq)) h_dist_bridge
    calc 2 * d_H_nat
      _ ≤ 2 * (d_fw * 2 ^ steps) := Nat.mul_le_mul_left 2 h_bridge_nat
      _ = (2 * d_fw) * 2 ^ steps := (Nat.mul_assoc _ _ _).symm
      _ ≤ (d_i_plus_steps - 1) * 2 ^ steps := Nat.mul_le_mul_right _ h_fw_bound
      _ = d_i - 1 := h_algebraic_identity
  -- This final line is equivalent to the goal statement.
  change (2 : ℕ∞) * d_H < d_i
  rw [h_dH_eq]
  exact_mod_cast Nat.lt_of_le_pred h_d_i_gt_0 h_final_inequality

end SoundnessTools
end

end Binius.BinaryBasefold
