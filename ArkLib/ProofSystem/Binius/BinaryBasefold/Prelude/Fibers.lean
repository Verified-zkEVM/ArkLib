/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.BerlekampWelch.BerlekampWelch
public import ArkLib.Data.CodingTheory.ReedSolomon
public import CompPoly.Fields.Binary.AdditiveNTT.AdditiveNTT
public import ArkLib.Data.MvPolynomial.Multilinear
public import ArkLib.Data.MvPolynomial.RestrictDegree
public import CompPoly.Data.Vector.Basic
public import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound
public import ArkLib.ProofSystem.Sumcheck.Structured.SingleRound

/-!
# Binary Basefold fibers
-/

@[expose] public section

namespace Binius.BinaryBasefold

open OracleSpec OracleComp ProtocolSpec Finset AdditiveNTT Polynomial MvPolynomial
  Binius.BinaryBasefold
open scoped NNReal
open Code BerlekampWelch
open Finset AdditiveNTT Polynomial MvPolynomial Nat Matrix

section Preliminaries

/-- Hamming distance is non-increasing under inner composition with an injective function.
NOTE : we can prove strict equality given `g` being an equivalence instead of injection.
-/
theorem hammingDist_le_of_outer_comp_injective {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    {β : ι₂ → Type*} [∀ i, DecidableEq (β i)]
    (x y : ∀ i, β i) (g : ι₁ → ι₂) (hg : Function.Injective g) :
    hammingDist (fun i => x (g i)) (fun i => y (g i)) ≤ hammingDist x y := by
  classical
  -- Let D₂ be the set of disagreeing indices for x and y.
  let D₂ := Finset.filter (fun i₂ => x i₂ ≠ y i₂) Finset.univ
  -- The Hamming distance of the composed functions is the card of the preimage of D₂.
  suffices (Finset.filter (fun i₁ => x (g i₁) ≠ y (g i₁)) Finset.univ).card ≤ D₂.card by
    unfold hammingDist; simp only [this, D₂]
  -- The cardinality of a preimage is at most the cardinalit
    -- of the original set for an injective function.
  -- ⊢ #{i₁ | x (g i₁) ≠ y (g i₁)} ≤ #D₂
   -- First, we state that the set on the left is the `preimage` of D₂ under g.
  have h_preimage : Finset.filter (fun i₁ => x (g i₁) ≠ y (g i₁)) Finset.univ
    = D₂.preimage g (by exact hg.injOn) := by
    -- Use `ext` to prove equality by showing the membership conditions are the same.
    ext i₁
    -- Now `simp` can easily unfold `mem_filter` and `mem_preimage` and see they are equivalent.
    simp only [ne_eq, mem_filter, mem_univ, true_and, mem_preimage, D₂]
  -- Now, rewrite the goal using `preimage`.
  rw [h_preimage]
  rw [Finset.card_preimage]
  exact Finset.card_filter_le _ _

variable {L : Type} [CommRing L] (ℓ : ℕ) [NeZero ℓ]

-- `fixFirstVariablesOfMQP` and `fixFirstVariablesOfMQP_degreeLE` (plus three private
-- helper lemmas) were lifted to `ArkLib.Data.MvPolynomial.RestrictDegree`, and
-- `getSumcheckRoundPoly` was lifted to `ArkLib.ProofSystem.Sumcheck.Structured.SingleRound`,
-- so the structured sumcheck (`ArkLib.ProofSystem.Sumcheck.Structured`) and any future
-- ring-switching protocol can use them without depending on `Binius.BinaryBasefold`.
-- They are accessible here unqualified via `open MvPolynomial` / `open Sumcheck.Structured`
-- above; we also export them under the `Binius.BinaryBasefold` namespace for any
-- fully-qualified callers.
export MvPolynomial (fixFirstVariablesOfMQP fixFirstVariablesOfMQP_degreeLE)
export Sumcheck.Structured (getSumcheckRoundPoly)

end Preliminaries

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


section Essentials
-- In this section, we ue notation `ϑ` for the folding steps, along with `(hdiv : ϑ ∣ ℓ)`

/-- Oracle function type for round i.
f^(i) : S⁽ⁱ⁾ → L, where |S⁽ⁱ⁾| = 2^{ℓ + R - i} -/
abbrev OracleFunction (i : Fin (ℓ + 1)) : Type _ := sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by
  exact Nat.lt_of_le_of_lt (n := i) (k := r) (m := ℓ) (h₁ := by exact Fin.is_le i)
    (by exact lt_of_add_right_lt h_ℓ_add_R_rate)⟩ → L

omit [NeZero ℓ] in
lemma fin_ℓ_lt_ℓ_add_one (i : Fin ℓ) : i < ℓ + 1 :=
  Nat.lt_of_lt_of_le i.isLt (Nat.le_succ ℓ)

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_ℓ_lt_ℓ_add_R (i : Fin ℓ) : i.val < ℓ + 𝓡 := by omega

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_ℓ_lt_r {h_ℓ_add_R_rate : ℓ + 𝓡 < r} (i : Fin ℓ) : i.val < r := by omega

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_ℓ_add_one_lt_r {h_ℓ_add_R_rate : ℓ + 𝓡 < r} (i : Fin (ℓ + 1)) : i.val < r := by omega

omit [NeZero ℓ] in
lemma fin_ℓ_steps_lt_ℓ_add_one (i : Fin ℓ) (steps : ℕ)
    (h : i.val + steps ≤ ℓ) : i.val + steps < ℓ + 1 :=
  Nat.lt_of_le_of_lt h (Nat.lt_succ_self ℓ)

omit [NeZero ℓ] in
lemma fin_ℓ_steps_lt_ℓ_add_R (i : Fin ℓ) (steps : ℕ) (h : i.val + steps ≤ ℓ) :
    i.val + steps < ℓ + 𝓡 := by
  apply Nat.lt_add_of_pos_right_of_le; omega

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_ℓ_steps_lt_r {h_ℓ_add_R_rate : ℓ + 𝓡 < r} (i : Fin ℓ) (steps : ℕ)
    (h : i.val + steps ≤ ℓ) : i.val + steps < r := by
  apply Nat.lt_of_le_of_lt (n := i + steps) (k := r) (m := ℓ) (h₁ := h)
    (by exact lt_of_add_right_lt h_ℓ_add_R_rate)

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma ℓ_lt_r {h_ℓ_add_R_rate : ℓ + 𝓡 < r} : ℓ < r := by omega

omit [NeZero ℓ] [NeZero r] [NeZero 𝓡] in
lemma fin_r_succ_bound {h_ℓ_add_R_rate : ℓ + 𝓡 < r} (i : Fin r)
    (h_i : i + 1 < ℓ + 𝓡) : i + 1 < r := by omega

/-!
### The Fiber of the Quotient Map `qMap`

Utilities for constructing fibers and defining the fold operations used by Binary Basefold.
-/

def Fin2ToF2 (𝔽q : Type*) [Ring 𝔽q] (k : Fin 2) : 𝔽q :=
  if k = 0 then 0 else 1

/-! Standalone helper for the fiber coefficients used in `qMap_total_fiber`. -/
noncomputable def fiber_coeff
    (i : Fin r) (steps : ℕ)
    (j : Fin (ℓ + 𝓡 - i)) (elementIdx : Fin (2 ^ steps))
    (y_coeffs : Fin (ℓ + 𝓡 - (i + steps)) →₀ 𝔽q) : 𝔽q :=
  if hj : j.val < steps then
    if Nat.getBit (k := j) (n := elementIdx) = 0 then 0 else 1
  else y_coeffs ⟨j.val - steps, by -- ⊢ ↑j - steps < ℓ + 𝓡 - ↑⟨↑i + steps, ⋯⟩
    rw [←Nat.sub_sub]; -- ⊢ ↑j - steps < ℓ + 𝓡 - ↑i - steps
    apply Nat.sub_lt_sub_right;
    · exact Nat.le_of_not_lt hj
    · exact j.isLt⟩

/-- Get the full fiber list `(x₀, ..., x_{2 ^ steps-1})` which represents the
joined fiber `(q⁽ⁱ⁺steps⁻¹⁾ ∘ ⋯ ∘ q⁽ⁱ⁾)⁻¹({y}) ⊂ S⁽ⁱ⁾` over `y ∈ S^(i+steps)`,
in which the LSB repsents the FIRST qMap `q⁽ⁱ⁾`, and the MSB represents the LAST `q⁽ⁱ⁺steps⁻¹⁾`
-/
noncomputable def qMap_total_fiber
    -- S^i is source domain, S^{i + steps} is the target domain
      (i : Fin r) (steps : ℕ) (h_i_add_steps : i.val + steps < ℓ + 𝓡)
        (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩)) :
    Fin (2 ^ steps) → sDomain 𝔽q β h_ℓ_add_R_rate i :=
  if h_steps : steps = 0 then by
    -- Base case : 0 steps, the fiber is just the point y itself.
    subst h_steps
    simp only [add_zero, Fin.eta] at y
    exact fun _ => y
  else by
    -- fun (k : 𝔽q) =>
    let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := ⟨i+steps,by omega⟩) (by omega)
    let y_coeffs : Fin (ℓ + 𝓡 - (↑i + steps)) →₀ 𝔽q := basis_y.repr y
    let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (by simp only; omega)
    exact fun elementIdx => by
      let x_coeffs : Fin (ℓ + 𝓡 - i) → 𝔽q := fun j =>
        if hj_lt_steps : j.val < steps then
          if Nat.getBit (k := j) (n := elementIdx) = 0 then (0 : 𝔽q)
          else (1 : 𝔽q)
        else
          y_coeffs ⟨j.val - steps, by
            rw [←Nat.sub_sub]; apply Nat.sub_lt_sub_right;
            · exact Nat.le_of_not_lt hj_lt_steps
            · exact j.isLt
          ⟩ -- Shift indices to match y's basis
      exact basis_x.repr.symm ((Finsupp.equivFunOnFinite).symm x_coeffs)

/- TODO : state that the fiber of y is the set of all 2 ^ steps points in the
larger domain S⁽ⁱ⁾ that get mapped to y by the series of quotient maps q⁽ⁱ⁾, ..., q⁽ⁱ⁺steps⁻¹⁾. -/

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **qMap_fiber coefficient extraction**.
The coefficients of `x = qMap_total_fiber(y, k)` with respect to `basis_x` are exactly
the function that puts binary coeffs corresponding to bits of `k` in
the first `steps` positions, and shifts `y`'s coefficients.
This is the multi-step counterpart of `qMap_fiber_repr_coeff`.
-/
lemma qMap_total_fiber_repr_coeff (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩))
    (k : Fin (2 ^ steps)) :
    let x := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩)
      (steps := steps)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) (y := y) k
    let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩)
      (h_i := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
    let y_coeffs := basis_y.repr y
    ∀ j, -- j refers to bit index of the fiber point x
      ((sDomain_basis 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) (by simp only; omega)).repr x) j
      = fiber_coeff (i := i) (steps := steps) (j := j) (elementIdx := k)
        (y_coeffs := y_coeffs) := by
  unfold fiber_coeff
  simp only
  intro j
  -- have h_steps_ne_0 : steps ≠ 0 := by exact?
  by_cases h_steps_eq_0 : steps = 0
  · subst h_steps_eq_0
    simp only [qMap_total_fiber, ↓reduceDIte, Nat.add_zero, eq_mp_eq_cast, cast_eq,
      _root_.not_lt_zero, tsub_zero, Fin.eta]
  · simp only [qMap_total_fiber, h_steps_eq_0, ↓reduceDIte, Module.Basis.repr_symm_apply,
    Module.Basis.repr_linearCombination, Finsupp.equivFunOnFinite_symm_apply_apply]

def pointToIterateQuotientIndex (i : Fin (ℓ + 1)) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩)) : Fin (2 ^ steps) := by
  let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩
    (by apply Nat.lt_add_of_pos_right_of_le; simp only; omega)
  let x_coeffs := basis_x.repr x
  let k_bits : Fin steps → Nat := fun j =>
    if x_coeffs ⟨j, by simp only; omega⟩ = 0 then 0 else 1
  let k := Nat.binaryFinMapToNat (n := steps) (m := k_bits) (h_binary := by
    intro j; simp only [k_bits]; split_ifs
    · norm_num
    · norm_num
  )
  exact k

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- When ϑ = 1, qMap_total_fiber maps k = 0 to an element with first coefficient 0
and k = 1 to an element with first coefficient 1. -/
lemma qMap_total_fiber_one_level_eq (i : Fin ℓ) (h_i_add_1 : i.val + 1 ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i + 1, by omega⟩)) (k : Fin 2) :
    let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (by simp only; omega)
    let x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩)
      (steps := 1) (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) k
    let y_lifted : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ := sDomain.lift 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (j := ⟨i.val + 1, by omega⟩)
      (h_j := by apply Nat.lt_add_of_pos_right_of_le; omega)
      (h_le := by apply Fin.mk_le_mk.mpr (by omega)) y
    let free_coeff_term : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ :=
      (Fin2ToF2 𝔽q k) • (basis_x ⟨0, by simp only; omega⟩)
    x = free_coeff_term + y_lifted := by
  let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (by simp only; omega)
  apply basis_x.repr.injective
  simp only [map_add, map_smul]
  simp only [Module.Basis.repr_self, Finsupp.smul_single, smul_eq_mul, mul_one, basis_x]
  ext j
  have h_repr_x := qMap_total_fiber_repr_coeff 𝔽q β i (steps := 1) (by omega)
    (y := y) (k := k) (j := j)
  simp only [h_repr_x, Finsupp.coe_add, Pi.add_apply]
  simp only [fiber_coeff, lt_one_iff, reducePow, Fin2ToF2, Fin.isValue]
  by_cases hj : j = ⟨0, by omega⟩
  · simp only [hj, ↓reduceDIte, Fin.isValue, Finsupp.single_eq_same]
    by_cases hk : k = 0
    · simp only [getBit, hk, Fin.isValue, Fin.coe_ofNat_eq_mod, zero_mod, shiftRight_zero,
      and_one_is_mod, ↓reduceIte, zero_add]
      -- => Now use basis_repr_of_sDomain_lift
      simp only [basis_repr_of_sDomain_lift, add_tsub_cancel_left, zero_lt_one, ↓reduceDIte]
    · have h_k_eq_1 : k = 1 := by omega
      simp only [getBit, h_k_eq_1, Fin.isValue, Fin.coe_ofNat_eq_mod, mod_succ, shiftRight_zero,
        Nat.and_self, one_ne_zero, ↓reduceIte, left_eq_add]
      simp only [basis_repr_of_sDomain_lift, add_tsub_cancel_left, zero_lt_one, ↓reduceDIte]
  · have hj_ne_zero : j ≠ ⟨0, by omega⟩ := by omega
    have hj_val_ne_zero : j.val ≠ 0 := by
      change j.val ≠ ((⟨0, by omega⟩ : Fin (ℓ + 𝓡 - ↑i)).val)
      apply Fin.val_ne_of_ne
      exact hj_ne_zero
    simp only [hj_val_ne_zero, ↓reduceDIte, Finsupp.single, Fin.isValue, ite_eq_left_iff,
      one_ne_zero, imp_false, Decidable.not_not, Pi.single, Finsupp.coe_mk, Function.update,
      hj_ne_zero, Pi.zero_apply, zero_add]
    simp only [basis_repr_of_sDomain_lift, add_tsub_cancel_left, lt_one_iff, right_eq_dite_iff]
    intro hj_eq_zero
    exact False.elim (hj_val_ne_zero hj_eq_zero)

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ [NeZero ℓ] in
/-- `x` is in the fiber of `y` under `qMap_total_fiber` iff `y` is the iterated
quotient of `x`. That is, for binary field, the fiber of `y` is exactly the set of
all `x` that map to `y` under the iterated quotient map. -/
theorem generates_quotient_point_if_is_fiber_of_y
    (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩))
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩))
    (hx_is_fiber : ∃ (k : Fin (2 ^ steps)), x = qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩)
      (steps := steps) (h_i_add_steps := by
        simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) (y := y) k) :
    y = iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (destIdx := ⟨i.val + steps, by omega⟩) (k := steps)
      (h_destIdx := by simp) (h_destIdx_le := h_i_add_steps) x := by
 -- Get the fiber index `k` and the equality from the hypothesis.
  rcases hx_is_fiber with ⟨k, hx_eq⟩
  let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate
    (i := ⟨i.val + steps, by omega⟩) (h_i := by apply Nat.lt_add_of_pos_right_of_le; omega)
  apply basis_y.repr.injective
  ext j
  conv_rhs =>
    rw [getSDomainBasisCoeff_of_iteratedQuotientMap]
  have h_repr_x := qMap_total_fiber_repr_coeff 𝔽q β i (steps := steps)
    (h_i_add_steps := by omega) (y := y) (k := k) (j := ⟨j + steps, by simp only; omega⟩)
  simp only at h_repr_x
  rw [←hx_eq] at h_repr_x
  simp only [fiber_coeff, add_lt_iff_neg_right, _root_.not_lt_zero, ↓reduceDIte,
    add_tsub_cancel_right, Fin.eta] at h_repr_x
  exact h_repr_x.symm

omit [CharP L 2] [NeZero ℓ] in
/-- State the corrrespondence between the forward qMap and the backward qMap_total_fiber -/
theorem is_fiber_iff_generates_quotient_point (i : Fin ℓ) (steps : ℕ)
    (h_i_add_steps : i.val + steps ≤ ℓ)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩))
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩)) :
    let qMapFiber := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) (y := y)
    let k := pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := h_i_add_steps) (x := x)
    y = iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (destIdx := ⟨i.val + steps, by omega⟩) (k := steps)
      (h_destIdx := by simp) (h_destIdx_le := h_i_add_steps) x ↔
    qMapFiber k = x := by
  let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩
    (by simp only; omega)
  let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i.val + steps, by omega⟩
    (h_i := by apply Nat.lt_add_of_pos_right_of_le; omega)
  simp only
  set k := pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps)
    (h_i_add_steps := h_i_add_steps) (x := x)
  constructor
  · intro h_x_generates_y
    -- ⊢ qMap_total_fiber ...` ⟨↑i, ⋯⟩ steps ⋯ y k = x
    -- We prove that `qMap_total_fiber` with this `k` reconstructs `x` via basis repr
    apply basis_x.repr.injective
    ext j
    let reConstructedX := basis_x.repr (qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩)
      (steps := steps) (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) k)
    have h_repr_of_reConstructedX := qMap_total_fiber_repr_coeff 𝔽q β i (steps := steps)
      (h_i_add_steps := by omega) (y := y) (k := k) (j := j)
    simp only at h_repr_of_reConstructedX
    -- ⊢ repr of reConstructedX at j = repr of x at j
    rw [h_repr_of_reConstructedX]; dsimp [k, pointToIterateQuotientIndex, fiber_coeff];
    rw [getBit_of_binaryFinMapToNat]; simp only [Fin.eta, dite_eq_right_iff, ite_eq_left_iff,
      one_ne_zero, imp_false, Decidable.not_not]
    -- Now we only need to do case analysis
    by_cases h_j : j.val < steps
    · -- Case 1 : The first `steps` coefficients, determined by `k`.
      simp only [h_j, ↓reduceDIte, forall_const]
      by_cases h_coeff_j_of_x : basis_x.repr x j = 0
      · simp only [basis_x, h_coeff_j_of_x, ↓reduceIte];
      · simp only [basis_x, h_coeff_j_of_x, ↓reduceIte];
        have h_coeff := 𝔽q_element_eq_zero_or_eq_one 𝔽q (c := basis_x.repr x j)
        simp only [h_coeff_j_of_x, false_or] at h_coeff
        exact id (Eq.symm h_coeff)
    · -- Case 2 : The remaining coefficients, determined by `y`.
      simp only [h_j, ↓reduceDIte]
      simp only [basis_x]
      -- ⊢ Here we compare coeffs, not the basis elements
      simp only [h_x_generates_y]
      have h_res := getSDomainBasisCoeff_of_iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
        (i := ⟨i, by omega⟩) (k := steps) (destIdx := ⟨i.val + steps, by omega⟩)
        (h_destIdx := by simp) (h_destIdx_le := h_i_add_steps) x
        (j := ⟨j - steps, by -- TODO : make this index bound proof cleaner
          simp only; rw [←Nat.sub_sub]; -- ⊢ ↑j - steps < ℓ + 𝓡 - ↑i - steps
          apply Nat.sub_lt_sub_right;
          · exact Nat.le_of_not_lt h_j
          · exact j.isLt
        ⟩) -- ⊢ ↑j - steps < ℓ + 𝓡 - (↑i + steps)
      have h_j_sub_add_steps : j - steps + steps = j := by omega
      simp only at h_res
      simp only [h_j_sub_add_steps, Fin.eta] at h_res
      exact h_res
  · intro h_x_is_fiber_of_y
    -- y is the quotient point of x over steps steps
    apply generates_quotient_point_if_is_fiber_of_y (h_i_add_steps := h_i_add_steps)
      (x := x) (y := y) (hx_is_fiber := by use k; exact h_x_is_fiber_of_y.symm)

omit [CharP L 2] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- the pointToIterateQuotientIndex of qMap_total_fiber -/
lemma pointToIterateQuotientIndex_qMap_total_fiber_eq_self (i : Fin ℓ) (steps : ℕ)
    (h_i_add_steps : i.val + steps ≤ ℓ)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) (i := ⟨i + steps, by omega⟩)) (k : Fin (2 ^ steps)) :
    pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps) (h_i_add_steps := by omega)
      (x := ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) k):
          sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩))) = k := by
  apply Fin.eq_mk_iff_val_eq.mpr
  apply eq_iff_eq_all_getBits.mpr
  intro j -- bit index j
  simp only [pointToIterateQuotientIndex, qMap_total_fiber]
  rw [Nat.getBit_of_binaryFinMapToNat]
  simp only [Nat.add_zero, Nat.pow_zero, eq_mp_eq_cast, cast_eq, Module.Basis.repr_symm_apply]
  by_cases h_j : j < steps
  · simp only [h_j, ↓reduceDIte];
    by_cases hsteps : steps = 0
    · simp only [hsteps, ↓reduceDIte, eqRec_eq_cast, Nat.add_zero, Nat.pow_zero]
      omega
    · simp only [hsteps, ↓reduceDIte, Module.Basis.repr_linearCombination,
      Finsupp.equivFunOnFinite_symm_apply_apply, h_j, ite_eq_left_iff, one_ne_zero,
      imp_false, Decidable.not_not]
      -- ⊢ (if j.getBit ↑k = 0 then 0 else 1) = j.getBit ↑k
      have h := Nat.getBit_eq_zero_or_one (k := j) (n := k)
      by_cases h_j_getBit_k_eq_0 : j.getBit ↑k = 0
      · simp only [h_j_getBit_k_eq_0, ↓reduceIte]
      · simp only [h_j_getBit_k_eq_0, false_or, ↓reduceIte] at h ⊢
        exact id (Eq.symm h)
  · rw [Nat.getBit_of_lt_two_pow];
    simp only [h_j, ↓reduceDIte, ↓reduceIte];

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
/-- **qMap_fiber coefficient extraction** -/
lemma qMap_total_fiber_basis_sum_repr (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
    (y : (sDomain 𝔽q β h_ℓ_add_R_rate) (i := ⟨i + steps, by omega⟩))
    (k : Fin (2 ^ steps)) :
    let x : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩) := qMap_total_fiber 𝔽q β
      (i := ⟨i, by omega⟩) (steps := steps) (h_i_add_steps := by
        apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) (k)
    let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩
      (by simp only; apply Nat.lt_add_of_pos_right_of_le; omega)
    let basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩
      (h_i := by apply Nat.lt_add_of_pos_right_of_le; omega)
    let y_coeffs := basis_y.repr y
    x = ∑ j : Fin (ℓ + 𝓡 - i), (
      fiber_coeff (i := i) (steps := steps) (j := j) (elementIdx := k) (y_coeffs := y_coeffs)
    ) • (basis_x j) := by
    set basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (by
      simp only; apply Nat.lt_add_of_pos_right_of_le; omega)
    set basis_y := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i + steps, by omega⟩
      (h_i := by apply Nat.lt_add_of_pos_right_of_le; omega)
    set y_coeffs := basis_y.repr y
    -- Let `x` be the element from the fiber for brevity.
    set x := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) (k)
    simp only;
    -- Express `(x:L)` using its basis representation, which is built from `x_coeffs_fn`.
    set x_coeffs_fn := fun j : Fin (ℓ + 𝓡 - i) =>
      fiber_coeff (i := i) (steps := steps) (j := j) (elementIdx := k) (y_coeffs := y_coeffs)
    have hx_val_sum : (x : L) = ∑ j, (x_coeffs_fn j) • (basis_x j) := by
      rw [←basis_x.sum_repr x]
      rw [Submodule.coe_sum, Submodule.coe_sum]
      congr; funext j;
      simp_rw [Submodule.coe_smul]
      congr; unfold x_coeffs_fn
      have h := qMap_total_fiber_repr_coeff 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by omega) (y := y) (k := k) (j := j)
      rw [h]
    apply Subtype.ext -- convert to equality in Subtype embedding
    rw [hx_val_sum]

omit [CharP L 2] [DecidableEq 𝔽q] hF₂ h_β₀_eq_1 [NeZero ℓ] in
theorem card_qMap_total_fiber (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i.val + steps ≤ ℓ)
    (y : sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i.val + steps, by omega⟩)) :
    Fintype.card (Set.image (qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by simp only; exact fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps)
      (y := y)) Set.univ) = 2 ^ steps := by
  -- The cardinality of the image of a function equals the cardinality of its domain
  -- if it is injective.
  rw [Set.card_image_of_injective Set.univ]
  -- The domain is `Fin (2 ^ steps)`, which has cardinality `2 ^ steps`.
  · -- ⊢ Fintype.card ↑Set.univ = 2 ^ steps
    simp only [Fintype.card_setUniv, Fintype.card_fin]
  · -- prove that `qMap_total_fiber` is an injective function.
    intro k₁ k₂ h_eq
    -- Assume two indices `k₁` and `k₂` produce the same point `x`.
    let basis_x := sDomain_basis 𝔽q β h_ℓ_add_R_rate ⟨i, by omega⟩ (by simp only; omega)
    -- If the points are equal, their basis representations must be equal.
    set fiberMap := qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y)
    have h_coeffs_eq : basis_x.repr (fiberMap k₁) = basis_x.repr (fiberMap k₂) := by
      rw [h_eq]
    -- The first `steps` coefficients are determined by the bits of `k₁` and `k₂`.
    -- If the coefficients are equal, the bits must be equal.
    have h_bits_eq : ∀ j : Fin steps,
        Nat.getBit (k := j) (n := k₁.val) = Nat.getBit (k := j) (n := k₂.val) := by
      intro j
      have h_coeff_j_eq : basis_x.repr (fiberMap k₁) ⟨j, by simp only; omega⟩
        = basis_x.repr (fiberMap k₂) ⟨j, by simp only; omega⟩ := by rw [h_coeffs_eq]
      rw [qMap_total_fiber_repr_coeff 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := h_i_add_steps) (y := y) (j := ⟨j, by simp only; omega⟩)]
        at h_coeff_j_eq
      rw [qMap_total_fiber_repr_coeff 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := h_i_add_steps) (y := y) (k := k₂) (j := ⟨j, by simp only; omega⟩)]
        at h_coeff_j_eq
      simp only [fiber_coeff, Fin.is_lt, ↓reduceDIte] at h_coeff_j_eq
      by_cases hbitj_k₁ : Nat.getBit (k := j) (n := k₁.val) = 0
      · simp only [hbitj_k₁, ↓reduceIte, left_eq_ite_iff, zero_ne_one, imp_false,
        Decidable.not_not] at ⊢ h_coeff_j_eq
        simp only [h_coeff_j_eq]
      · simp only [hbitj_k₁, ↓reduceIte, right_eq_ite_iff, one_ne_zero,
        imp_false] at ⊢ h_coeff_j_eq
        have b1 : Nat.getBit (k := j) (n := k₁.val) = 1 := by
          have h := Nat.getBit_eq_zero_or_one (k := j) (n := k₁.val)
          simp only [hbitj_k₁, false_or] at h
          exact h
        have b2 : Nat.getBit (k := j) (n := k₂.val) = 1 := by
          have h := Nat.getBit_eq_zero_or_one (k := j) (n := k₂.val)
          simp only [h_coeff_j_eq, false_or] at h
          exact h
        simp only [b1, b2]
      -- Extract the j-th coefficient from h_coeffs_eq and show it implies the bits are equal.
    -- If all the bits of two numbers are equal, the numbers themselves are equal.
    apply Fin.eq_of_val_eq
    -- ⊢ ∀ {n : ℕ} {i j : Fin n}, ↑i = ↑j → i = j
    apply eq_iff_eq_all_getBits.mpr
    intro k
    by_cases h_k : k < steps
    · simp only [h_bits_eq ⟨k, by omega⟩]
    · -- The bits at positions ≥ steps must be deterministic
      conv_lhs => rw [Nat.getBit_of_lt_two_pow]
      conv_rhs => rw [Nat.getBit_of_lt_two_pow]
      simp only [h_k, ↓reduceIte]
omit [CharP L 2] [DecidableEq 𝔽q] [NeZero ℓ] in
/-- The images of `qMap_total_fiber` over distinct quotient points `y₁ ≠ y₂` are
disjoint -/
theorem qMap_total_fiber_disjoint
    (i : Fin ℓ) (steps : ℕ) (h_i_add_steps : i + steps ≤ ℓ)
  {y₁ y₂ : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + steps, by omega⟩}
  (hy_ne : y₁ ≠ y₂) :
  Disjoint
    ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) y₁ '' Set.univ).toFinset)
    ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := fin_ℓ_steps_lt_ℓ_add_R i steps h_i_add_steps) y₂ ''
        Set.univ).toFinset) := by
  classical
 -- Proof by contradiction. Assume the intersection is non-empty.
  rw [Finset.disjoint_iff_inter_eq_empty]
  by_contra h_nonempty
  -- Let `x` be an element in the intersection of the two fiber sets.
  obtain ⟨x, h_x_mem_inter⟩ := Finset.nonempty_of_ne_empty h_nonempty
  have hx₁ := Finset.mem_of_mem_inter_left h_x_mem_inter
  have hx₂ := Finset.mem_of_mem_inter_right h_x_mem_inter
  -- A helper lemma : applying the forward map to a point in a generated fiber returns
  -- the original quotient point.
  have iteratedQuotientMap_of_qMap_total_fiber_eq_self
    (y : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + steps, by omega⟩)
    (k : Fin (2 ^ steps)) :
    iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (destIdx := ⟨i.val + steps, by omega⟩) (k := steps)
      (h_destIdx := by simp) (h_destIdx_le := h_i_add_steps)
      (qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) k) = y := by
      have h := generates_quotient_point_if_is_fiber_of_y
        (h_i_add_steps := h_i_add_steps) (x:=
        ((qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
          (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) (y := y) k) :
          sDomain 𝔽q β h_ℓ_add_R_rate (i := ⟨i, by omega⟩))
      ) (y := y) (hx_is_fiber := by use k)
      exact h.symm
  have h_exists_k₁ : ∃ k, x = qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) y₁ k := by
    -- convert (x ∈ Finset of the image of the fiber) to statement
    -- about membership in the Set.
    rw [Set.mem_toFinset] at hx₁
    rw [Set.mem_image] at hx₁ -- Set.mem_image gives us t an index that maps to x
    -- ⊢ `∃ (k : Fin (2 ^ steps)), k ∈ Set.univ ∧ qMap_total_fiber ... y₁ k = x`.
    rcases hx₁ with ⟨k, _, h_eq⟩
    use k; exact h_eq.symm
  have h_exists_k₂ : ∃ k, x = qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
      (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) y₂ k := by
    rw [Set.mem_toFinset] at hx₂
    rw [Set.mem_image] at hx₂ -- Set.mem_image gives us t an index that maps to x
    rcases hx₂ with ⟨k, _, h_eq⟩
    use k; exact h_eq.symm
  have h_y₁_eq_quotient_x : y₁ =
      iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
        (i := ⟨i, by omega⟩) (destIdx := ⟨i.val + steps, by omega⟩) (k := steps)
        (h_destIdx := by simp) (h_destIdx_le := h_i_add_steps) x := by
    apply generates_quotient_point_if_is_fiber_of_y (hx_is_fiber := by exact h_exists_k₁)
  have h_y₂_eq_quotient_x : y₂ =
      iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
        (i := ⟨i, by omega⟩) (destIdx := ⟨i.val + steps, by omega⟩) (k := steps)
        (h_destIdx := by simp) (h_destIdx_le := h_i_add_steps) x := by
    apply generates_quotient_point_if_is_fiber_of_y (hx_is_fiber := by exact h_exists_k₂)
  let kQuotientIndex := pointToIterateQuotientIndex (i := ⟨i, by omega⟩) (steps := steps)
    (h_i_add_steps := by omega) (x := x)
  -- Since `x` is in the fiber of `y₁`, applying the forward map to `x` yields `y₁`.
  have h_map_x_eq_y₁ : iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (destIdx := ⟨i.val + steps, by omega⟩) (k := steps)
      (h_destIdx := by simp) (h_destIdx_le := h_i_add_steps) x = y₁ := by
    have h := iteratedQuotientMap_of_qMap_total_fiber_eq_self (y := y₁) (k := kQuotientIndex)
    have hx₁ : x = qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) y₁ kQuotientIndex := by
      have h_res := is_fiber_iff_generates_quotient_point 𝔽q β i steps (by omega)
        (x := x) (y := y₁).mp (h_y₁_eq_quotient_x)
      exact h_res.symm
    rw [hx₁]
    exact iteratedQuotientMap_of_qMap_total_fiber_eq_self y₁ kQuotientIndex
  -- Similarly, since `x` is in the fiber of `y₂`, applying the forward map yields `y₂`.
  have h_map_x_eq_y₂ : iteratedQuotientMap 𝔽q β h_ℓ_add_R_rate
      (i := ⟨i, by omega⟩) (destIdx := ⟨i.val + steps, by omega⟩) (k := steps)
      (h_destIdx := by simp) (h_destIdx_le := h_i_add_steps) x = y₂ := by
    -- have h := iteratedQuotientMap_of_qMap_total_fiber_eq_self (y := y₂) (k := kQuotientIndex)
    have hx₂ : x = qMap_total_fiber 𝔽q β (i := ⟨i, by omega⟩) (steps := steps)
        (h_i_add_steps := by apply Nat.lt_add_of_pos_right_of_le; omega) y₂ kQuotientIndex := by
      have h_res := is_fiber_iff_generates_quotient_point 𝔽q β i steps (by omega)
        (x := x) (y := y₂).mp (h_y₂_eq_quotient_x)
      exact h_res.symm
    rw [hx₂]
    exact iteratedQuotientMap_of_qMap_total_fiber_eq_self y₂ kQuotientIndex
  exact hy_ne (h_map_x_eq_y₁.symm.trans h_map_x_eq_y₂)

end Essentials

end

end Binius.BinaryBasefold
