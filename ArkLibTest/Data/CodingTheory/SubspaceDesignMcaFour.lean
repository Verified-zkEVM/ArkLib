import ArkLib.Data.CodingTheory.ProximityGap.CapacityBounds.SubspaceDesign

namespace CodingTheory

open scoped NNReal
open CoreDefinitions ProximityGap FrsInternal

theorem finrank_submodule_ge_sub_ker
    {F V W : Type*} [Field F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (φ : V →ₗ[F] W) (S : Submodule F V) (K : Submodule F W)
    (hmap : ∀ x, x ∈ S → φ x ∈ K) :
    Module.finrank F K ≥ Module.finrank F S - Module.finrank F (LinearMap.ker φ) := by
  let g : S →ₗ[F] W := φ.comp S.subtype
  have hkerMap : (LinearMap.ker g).map S.subtype = S ⊓ LinearMap.ker φ := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      exact LinearMap.mem_ker.mp hy
    · rintro ⟨hxS, hxφ⟩
      refine ⟨⟨x, hxS⟩, LinearMap.mem_ker.mpr ?_, rfl⟩
      exact LinearMap.mem_ker.mp hxφ
  have hkerDim :
      Module.finrank F (LinearMap.ker g) =
        Module.finrank F ↥(S ⊓ LinearMap.ker φ) := by
    calc
      Module.finrank F (LinearMap.ker g) =
          Module.finrank F ((LinearMap.ker g).map S.subtype) :=
        (Submodule.finrank_map_subtype_eq S (LinearMap.ker g)).symm
      _ = Module.finrank F ↥(S ⊓ LinearMap.ker φ) := by rw [hkerMap]
  have hkerLe : Module.finrank F (LinearMap.ker g) ≤
      Module.finrank F (LinearMap.ker φ) := by
    rw [hkerDim]
    exact Submodule.finrank_mono (inf_le_right : S ⊓ LinearMap.ker φ ≤ LinearMap.ker φ)
  have hrange : LinearMap.range g ≤ K := by
    rintro y ⟨x, rfl⟩
    exact hmap x.1 x.2
  have hrangeLe : Module.finrank F (LinearMap.range g) ≤ Module.finrank F K :=
    Submodule.finrank_mono hrange
  have hnull := LinearMap.finrank_range_add_finrank_ker g
  omega

theorem subspaceDesignMcaFour_rank_sensitive_kernel_lower_bound
    {F V W : Type*} [Field F]
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    [AddCommGroup W] [Module F W] [FiniteDimensional F W]
    (φ : V →ₗ[F] W) (S : Submodule F V) (K : Submodule F W)
    (hmap : ∀ x, x ∈ S → φ x ∈ K)
    (h : ℕ) (d q : ℕ) (hq : 2 ≤ q) (hd : d + 2 ≤ h)
    (hS : q - 2 ≤ Module.finrank F S)
    (hker : Module.finrank F (LinearMap.ker φ) ≤ h - 2 - d) :
    max 0 (d + q - h) ≤ Module.finrank F K := by
  have hdim := finrank_submodule_ge_sub_ker φ S K hmap
  by_cases hpositive : h < d + q
  · have hresult : d + q - h ≤ Module.finrank F S -
        Module.finrank F (LinearMap.ker φ) := by omega
    have hbound : d + q - h ≤ Module.finrank F K := hresult.trans hdim
    simpa [Nat.max_eq_left (Nat.zero_le _)] using hbound
  · have hzero : d + q - h = 0 := by omega
    simp [hzero]

theorem subspaceDesignMcaFour_low_threshold_two (τ : ℝ)
    (hτ : τ < 89 / 242) : 96 > 7 + 242 * τ := by
  norm_num at hτ ⊢
  nlinarith

theorem subspaceDesignMcaFour_low_threshold_three (τ : ℝ)
    (hτ : τ < 89 / 491) : 96 > 7 + 491 * τ := by
  norm_num at hτ ⊢
  nlinarith

theorem subspaceDesignMcaFour_low_threshold_four (τ : ℝ)
    (hτ : τ < 89 / 740) : 96 > 7 + 740 * τ := by
  norm_num at hτ ⊢
  nlinarith

theorem subspaceDesignMcaFour_low_threshold_five (τ : ℝ)
    (hτ : τ < 89 / 989) : 96 > 7 + 989 * τ := by
  norm_num at hτ ⊢
  nlinarith

theorem subspaceDesignMcaFour_low_condition_rank_two (τ : ℝ)
    (hτ : τ < 89 / 242) :
    96 > 7 + (249 * (2 : ℝ) - 256) * τ := by
  have h := subspaceDesignMcaFour_low_threshold_two τ hτ
  norm_num at h ⊢
  exact h

theorem subspaceDesignMcaFour_low_condition_rank_three (τ : ℝ)
    (hτ : τ < 89 / 491) :
    96 > 7 + (249 * (3 : ℝ) - 256) * τ := by
  have h := subspaceDesignMcaFour_low_threshold_three τ hτ
  norm_num at h ⊢
  exact h

theorem subspaceDesignMcaFour_low_condition_rank_four (τ : ℝ)
    (hτ : τ < 89 / 740) :
    96 > 7 + (249 * (4 : ℝ) - 256) * τ := by
  have h := subspaceDesignMcaFour_low_threshold_four τ hτ
  norm_num at h ⊢
  exact h

theorem subspaceDesignMcaFour_low_condition_rank_five (τ : ℝ)
    (hτ : τ < 89 / 989) :
    96 > 7 + (249 * (5 : ℝ) - 256) * τ := by
  have h := subspaceDesignMcaFour_low_threshold_five τ hτ
  norm_num at h ⊢
  exact h

theorem subspaceDesignMcaFour_high_cutoff_lt_low_two :
    (1 : ℝ) / 4 < 89 / 242 := by norm_num

theorem subspaceDesignMcaFour_high_cutoff_lt_low_three :
    (1 : ℝ) / 16 < 89 / 491 := by norm_num

theorem subspaceDesignMcaFour_high_cutoff_lt_low_four :
    (-1 : ℝ) / 8 < 89 / 740 := by norm_num

theorem subspaceDesignMcaFour_high_cutoff_lt_low_five :
    (-5 : ℝ) / 16 < 89 / 989 := by norm_num

theorem subspaceDesignMcaFour_threshold_coverage_rank_two (τ : ℝ) :
    τ < 89 / 242 ∨ 1 / 4 < τ := by
  by_cases hlow : τ < 89 / 242
  · exact Or.inl hlow
  · exact Or.inr (lt_of_lt_of_le
      subspaceDesignMcaFour_high_cutoff_lt_low_two (le_of_not_gt hlow))

theorem subspaceDesignMcaFour_threshold_coverage_rank_three (τ : ℝ) :
    τ < 89 / 491 ∨ 1 / 16 < τ := by
  by_cases hlow : τ < 89 / 491
  · exact Or.inl hlow
  · exact Or.inr (lt_of_lt_of_le
      subspaceDesignMcaFour_high_cutoff_lt_low_three (le_of_not_gt hlow))

theorem subspaceDesignMcaFour_threshold_coverage_rank_four (τ : ℝ) :
    τ < 89 / 740 ∨ (-1 : ℝ) / 8 < τ := by
  by_cases hlow : τ < 89 / 740
  · exact Or.inl hlow
  · exact Or.inr (lt_of_lt_of_le
      subspaceDesignMcaFour_high_cutoff_lt_low_four (le_of_not_gt hlow))

theorem subspaceDesignMcaFour_threshold_coverage_rank_five (τ : ℝ) :
    τ < 89 / 989 ∨ (-5 : ℝ) / 16 < τ := by
  by_cases hlow : τ < 89 / 989
  · exact Or.inl hlow
  · exact Or.inr (lt_of_lt_of_le
      subspaceDesignMcaFour_high_cutoff_lt_low_five (le_of_not_gt hlow))

theorem subspaceDesignMcaFour_threshold_coverage_all (τ : ℝ) :
    (τ < 89 / 242 ∨ 1 / 4 < τ) ∧
      (τ < 89 / 491 ∨ 1 / 16 < τ) ∧
      (τ < 89 / 740 ∨ (-1 : ℝ) / 8 < τ) ∧
      (τ < 89 / 989 ∨ (-5 : ℝ) / 16 < τ) :=
  ⟨subspaceDesignMcaFour_threshold_coverage_rank_two τ,
    subspaceDesignMcaFour_threshold_coverage_rank_three τ,
    subspaceDesignMcaFour_threshold_coverage_rank_four τ,
    subspaceDesignMcaFour_threshold_coverage_rank_five τ⟩

theorem subspaceDesignMcaFour_low_cutoff_equality_goes_high_two
    (τ : ℝ) (hτ : τ = 89 / 242) : 1 / 4 < τ := by
  rw [hτ]
  norm_num

theorem subspaceDesignMcaFour_low_cutoff_equality_goes_high_three
    (τ : ℝ) (hτ : τ = 89 / 491) : 1 / 16 < τ := by
  rw [hτ]
  norm_num

theorem subspaceDesignMcaFour_low_cutoff_equality_goes_high_four
    (τ : ℝ) (hτ : τ = 89 / 740) : (-1 : ℝ) / 8 < τ := by
  rw [hτ]
  norm_num

theorem subspaceDesignMcaFour_low_cutoff_equality_goes_high_five
    (τ : ℝ) (hτ : τ = 89 / 989) : (-5 : ℝ) / 16 < τ := by
  rw [hτ]
  norm_num

theorem subspaceDesignMcaFour_threshold_coverage_two (τ : ℝ) :
    τ < 89 / 242 ∨ 1 / 4 < τ := by
  by_cases h : τ < 89 / 242
  · exact Or.inl h
  · right
    norm_num at h ⊢
    nlinarith

theorem subspaceDesignMcaFour_threshold_coverage_three (τ : ℝ) :
    τ < 89 / 491 ∨ 1 / 16 < τ := by
  by_cases h : τ < 89 / 491
  · exact Or.inl h
  · right
    norm_num at h ⊢
    nlinarith

theorem subspaceDesignMcaFour_high_threshold_two (τ : ℝ)
    (hτ : 1 / 4 < τ) : 4 * (τ + 3 / 8) - 2 > 2 * τ := by
  norm_num at hτ ⊢
  nlinarith

theorem subspaceDesignMcaFour_high_threshold_three (τ : ℝ)
    (hτ : 1 / 16 < τ) : 5 * (τ + 3 / 8) - 2 > 3 * τ := by
  norm_num at hτ ⊢
  nlinarith

theorem subspaceDesignMcaFour_high_threshold_four (τ : ℝ)
    (hτ : 0 ≤ τ) : 6 * (τ + 3 / 8) - 2 > 4 * τ := by
  norm_num at hτ ⊢
  nlinarith

theorem subspaceDesignMcaFour_high_threshold_five (τ : ℝ)
    (hτ : 0 ≤ τ) : 7 * (τ + 3 / 8) - 2 > 5 * τ := by
  norm_num at hτ ⊢
  nlinarith

theorem subspaceDesignMcaFour_high_threshold_rank_five (τ : ℝ)
    (hτ : 0 ≤ τ) : 7 * (τ + 3 / 8) - 2 > 5 * τ := by
  exact subspaceDesignMcaFour_high_threshold_five τ hτ

theorem subspaceDesignMcaFour_high_threshold_four_five (τ : ℝ)
    (hτ : 0 ≤ τ) :
    6 * (τ + 3 / 8) - 2 > 4 * τ ∧
      7 * (τ + 3 / 8) - 2 > 5 * τ := by
  exact ⟨subspaceDesignMcaFour_high_threshold_four τ hτ,
    subspaceDesignMcaFour_high_threshold_five τ hτ⟩

theorem subspaceDesignMcaFour_list_radius_identity (τ : ℝ) :
    4 / 5 * (1 - τ) - 8 / 7 * (5 / 8 - τ) =
      (3 + 12 * τ) / 35 := by
  ring

theorem subspaceDesignMcaFour_list_radius_strict (τ : ℝ) (hτ : 0 ≤ τ) :
    (5 / 8 - τ) * 8 / 7 < (4 : ℝ) / (4 + 1) * (1 - τ) := by
  have hpos : 0 < (3 + 12 * τ) / 35 := by positivity
  rw [show (4 : ℝ) / (4 + 1) = 4 / 5 by norm_num]
  nlinarith [subspaceDesignMcaFour_list_radius_identity τ]

theorem subspaceDesignMcaFour_budget (n : ℕ) :
    (4 + 1) ^ 2 ≤ n * 4 + 256 := by
  omega

theorem subspaceDesignMcaFour_radius_bounds (τ : ℝ)
    (hτ₀ : 0 ≤ τ) (hτ₁ : τ ≤ 5 / 8) :
    0 ≤ 5 / 8 - τ ∧ 5 / 8 - τ < 1 := by
  constructor <;> norm_num at * <;> linarith

theorem subspaceDesignMcaFour_list_bound
    {ι : Type} [Fintype ι] {F : Type} [Field F] {s : ℕ}
    (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C) (δ : ℝ)
    (hδ : δ = 5 / 8 - τ 5) (hτ : 0 ≤ τ 5) :
    Code.Lambda (C : Set (ι → Fin s → F)) (δ * 8 / 7) ≤ (4 : ℕ∞) := by
  apply subspaceDesign_lambda_le_of_radius_lt hdesign (r := 5) (L := 4)
    (by omega)
  rw [hδ]
  exact subspaceDesignMcaFour_list_radius_strict (τ 5) hτ

theorem subspaceDesignMcaFour_convert_strongLineDecodable
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Fintype F] [SampleableType F] [DecidableEq F]
    {s : ℕ} (C : Submodule F (ι → Fin s → F)) (δ : NNReal)
    (hδlt : δ < 1)
    (hweak : StrongLineDecodable (C : Set (ι → Fin s → F)) δ 256 8)
    (hlist : Code.Lambda (C : Set (ι → Fin s → F)) ((δ : ℝ) * 8 / 7) ≤ 4) :
    mcaError (AffineLineGenerator F) C (δ : ℝ) ≤
      ENNReal.ofReal (((4 : ℝ) * Fintype.card ι + 256) / Fintype.card F) := by
  have hlist' : Code.Lambda (C : Set (ι → Fin s → F))
      ((δ : ℝ) * (2 * (4 : ℝ)) / (2 * (4 : ℝ) - 1)) ≤ (4 : ℕ∞) := by
    convert hlist using 1
    norm_num
  have hmca := mcaError_le_of_strongLineDecodable (t := 4) C δ (by norm_num)
    hδlt hweak hlist' (by omega)
  convert hmca using 1
  push_cast
  ring_nf

def subspaceDesignMcaFour_interpolationSlope
    {ι : Type} {F : Type} [Field F] {s : ℕ}
    (U : F → ι → Fin s → F) (α β : F) : ι → Fin s → F :=
  (β - α)⁻¹ • (U β - U α)

def subspaceDesignMcaFour_interpolationIntercept
    {ι : Type} {F : Type} [Field F] {s : ℕ}
    (U : F → ι → Fin s → F) (α β : F) : ι → Fin s → F :=
  U α - α • subspaceDesignMcaFour_interpolationSlope U α β

theorem subspaceDesignMcaFour_interpolation_slope_mem
    {ι : Type} {F : Type} [Field F] {s : ℕ}
    (C : Submodule F (ι → Fin s → F)) (U : F → ι → Fin s → F)
    (α β : F) (hα : U α ∈ C) (hβ : U β ∈ C) :
    subspaceDesignMcaFour_interpolationSlope U α β ∈ C := by
  exact C.smul_mem _ (C.sub_mem hβ hα)

theorem subspaceDesignMcaFour_interpolation_intercept_mem
    {ι : Type} {F : Type} [Field F] {s : ℕ}
    (C : Submodule F (ι → Fin s → F)) (U : F → ι → Fin s → F)
    (α β : F) (hα : U α ∈ C) (hβ : U β ∈ C) :
    subspaceDesignMcaFour_interpolationIntercept U α β ∈ C := by
  exact C.sub_mem hα
    (C.smul_mem _ (subspaceDesignMcaFour_interpolation_slope_mem C U α β hα hβ))

theorem subspaceDesignMcaFour_interpolation_at_left
    {ι : Type} {F : Type} [Field F] {s : ℕ}
    (U : F → ι → Fin s → F) (α β : F) :
    subspaceDesignMcaFour_interpolationIntercept U α β +
      α • subspaceDesignMcaFour_interpolationSlope U α β = U α := by
  simp [subspaceDesignMcaFour_interpolationIntercept]

theorem subspaceDesignMcaFour_interpolation_at_right
    {ι : Type} {F : Type} [Field F] {s : ℕ}
    (U : F → ι → Fin s → F) (α β : F) (hαβ : α ≠ β) :
    subspaceDesignMcaFour_interpolationIntercept U α β +
      β • subspaceDesignMcaFour_interpolationSlope U α β = U β := by
  have hba : β - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hαβ)
  have hmul : (β - α) * (β - α)⁻¹ = 1 := mul_inv_cancel₀ hba
  calc
    subspaceDesignMcaFour_interpolationIntercept U α β +
        β • subspaceDesignMcaFour_interpolationSlope U α β =
      U α + (β - α) • subspaceDesignMcaFour_interpolationSlope U α β := by
        simp only [subspaceDesignMcaFour_interpolationIntercept]
        module
    _ = U α + (U β - U α) := by
      congr 1
      simp only [subspaceDesignMcaFour_interpolationSlope]
      rw [← smul_assoc]
      change ((β - α) * (β - α)⁻¹) • (U β - U α) = _
      rw [hmul, one_smul]
    _ = U β := by abel

def subspaceDesignMcaFour_residual
    {ι : Type} {F : Type} [Field F] {s : ℕ}
    (U : F → ι → Fin s → F) (c₀ c₁ : ι → Fin s → F) (γ : F) :
    ι → Fin s → F :=
  U γ - (c₀ + γ • c₁)

def subspaceDesignMcaFour_residualSpan
    {ι : Type} {F : Type} [Field F] {s : ℕ} [DecidableEq F]
    (T : Finset F) (U : F → ι → Fin s → F) (c₀ c₁ : ι → Fin s → F) :
    Submodule F (ι → Fin s → F) :=
  Submodule.span F
    (subspaceDesignMcaFour_residual U c₀ c₁ '' (T : Set F))

theorem subspaceDesignMcaFour_exists_pair_independent_residuals
    {ι : Type} {F : Type} [Field F] [DecidableEq F] {s : ℕ}
    [FiniteDimensional F (ι → Fin s → F)]
    (T : Finset F) (U : F → ι → Fin s → F) (c₀ c₁ : ι → Fin s → F)
    (hD : Module.finrank F
      (subspaceDesignMcaFour_residualSpan T U c₀ c₁) = 2) :
    ∃ α ∈ T, ∃ β ∈ T, α ≠ β ∧
      LinearIndependent F ![
        subspaceDesignMcaFour_residual U c₀ c₁ α,
        subspaceDesignMcaFour_residual U c₀ c₁ β] := by
  classical
  let G : Set (ι → Fin s → F) :=
    subspaceDesignMcaFour_residual U c₀ c₁ '' (T : Set F)
  have hspan : Submodule.span F G =
      subspaceDesignMcaFour_residualSpan T U c₀ c₁ := rfl
  have hdim : Module.finrank F (Submodule.span F G) = 2 := by
    rw [hspan]
    exact hD
  obtain ⟨f₀, hf₀, _hfspan, hli₀⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq F G
  let e : Fin 2 → Fin (Module.finrank F (Submodule.span F G)) :=
    Fin.cast hdim.symm
  let f : Fin 2 → ι → Fin s → F := f₀ ∘ e
  have hf : ∀ i, f i ∈ G := fun i => hf₀ (e i)
  have hli : LinearIndependent F f :=
    hli₀.comp _ (Fin.cast_injective hdim.symm)
  have hmem₀ : f 0 ∈ G := hf 0
  have hmem₁ : f 1 ∈ G := hf 1
  change ∃ α ∈ (T : Set F),
    subspaceDesignMcaFour_residual U c₀ c₁ α = f 0 at hmem₀
  change ∃ β ∈ (T : Set F),
    subspaceDesignMcaFour_residual U c₀ c₁ β = f 1 at hmem₁
  obtain ⟨α, hα, hαeq⟩ := hmem₀
  obtain ⟨β, hβ, hβeq⟩ := hmem₁
  have hpair : LinearIndependent F ![f 0, f 1] := by
    have hfun : (fun i : Fin 2 => f i) = ![f 0, f 1] := by
      funext i
      fin_cases i <;> simp
    rw [← hfun]
    exact hli
  have hpair_residual : LinearIndependent F ![
      subspaceDesignMcaFour_residual U c₀ c₁ α,
      subspaceDesignMcaFour_residual U c₀ c₁ β] := by
    simpa [hαeq, hβeq] using hpair
  have hαβ : α ≠ β := by
    intro h
    have hfeq : f 0 = f 1 := by
      calc
        f 0 = subspaceDesignMcaFour_residual U c₀ c₁ α := hαeq.symm
        _ = subspaceDesignMcaFour_residual U c₀ c₁ β := by rw [h]
        _ = f 1 := hβeq
    have h01 : (0 : Fin 2) = 1 := hpair.injective hfeq
    exact Fin.zero_ne_one h01
  exact ⟨α, hα, β, hβ, hαβ, hpair_residual⟩

theorem subspaceDesignMcaFour_exists_four_seed_configuration
    {ι : Type} {F : Type} [Field F] [DecidableEq F] {s : ℕ}
    [FiniteDimensional F (ι → Fin s → F)]
    (T : Finset F) (U : F → ι → Fin s → F) (c₀ c₁ : ι → Fin s → F)
    (α₀ α₁ : F) (hα₀ : α₀ ∈ T) (hα₁ : α₁ ∈ T) (hα₀α₁ : α₀ ≠ α₁)
    (hres₀ : subspaceDesignMcaFour_residual U c₀ c₁ α₀ = 0)
    (hres₁ : subspaceDesignMcaFour_residual U c₀ c₁ α₁ = 0)
    (hD : Module.finrank F
      (subspaceDesignMcaFour_residualSpan T U c₀ c₁) = 2) :
    ∃ α₂ ∈ T, ∃ α₃ ∈ T,
      α₀ ∈ T ∧ α₁ ∈ T ∧ α₀ ≠ α₁ ∧
      α₀ ≠ α₂ ∧ α₀ ≠ α₃ ∧ α₁ ≠ α₂ ∧ α₁ ≠ α₃ ∧ α₂ ≠ α₃ ∧
      LinearIndependent F ![
        subspaceDesignMcaFour_residual U c₀ c₁ α₂,
        subspaceDesignMcaFour_residual U c₀ c₁ α₃] := by
  obtain ⟨α₂, hα₂, α₃, hα₃, hα₂α₃, hli⟩ :=
    subspaceDesignMcaFour_exists_pair_independent_residuals T U c₀ c₁ hD
  have hres₂ : subspaceDesignMcaFour_residual U c₀ c₁ α₂ ≠ 0 :=
    LinearIndependent.ne_zero 0 hli
  have hres₃ : subspaceDesignMcaFour_residual U c₀ c₁ α₃ ≠ 0 :=
    LinearIndependent.ne_zero 1 hli
  have hα₀α₂ : α₀ ≠ α₂ := by
    intro h
    apply hres₂
    rw [← h, hres₀]
  have hα₀α₃ : α₀ ≠ α₃ := by
    intro h
    apply hres₃
    rw [← h, hres₀]
  have hα₁α₂ : α₁ ≠ α₂ := by
    intro h
    apply hres₂
    rw [← h, hres₁]
  have hα₁α₃ : α₁ ≠ α₃ := by
    intro h
    apply hres₃
    rw [← h, hres₁]
  exact ⟨α₂, hα₂, α₃, hα₃, hα₀, hα₁, hα₀α₁,
    hα₀α₂, hα₀α₃, hα₁α₂, hα₁α₃, hα₂α₃, hli⟩

def subspaceDesignMcaFour_evalMap
    {ι : Type} {F : Type} [Semiring F] {s : ℕ} (i : ι) :
    (ι → Fin s → F) →ₗ[F] (Fin s → F) :=
  LinearMap.proj (R := F) (φ := fun _ : ι ↦ Fin s → F) i

def subspaceDesignMcaFour_coordinateKernel
    {ι : Type} {F : Type} [Field F] {s : ℕ}
    (V : Submodule F (ι → Fin s → F)) (i : ι) :
    Submodule F (ι → Fin s → F) :=
  V ⊓ LinearMap.ker (subspaceDesignMcaFour_evalMap i)

theorem subspaceDesignMcaFour_rank_sensitive_design_sum
    {ι : Type} {F : Type} [Field F] [Fintype ι] [Nonempty ι]
    [DecidableEq F] {s d h : ℕ} [FiniteDimensional F (ι → Fin s → F)]
    (τ : ℕ → ℝ) (C V : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C) (hVC : V ≤ C)
    (hdim : Module.finrank F V = d) (hd : d ≤ 5)
    (q : ι → ℕ)
    (hq : ∀ i, max 0 (d + q i - h) ≤
      Module.finrank F (subspaceDesignMcaFour_coordinateKernel V i)) :
    (∑ i : ι, ((max 0 (d + q i - h) : ℕ) : ℝ)) ≤
      Fintype.card ι * (d : ℝ) * τ 5 := by
  have hdes := hdesign 5 V hVC (by rw [hdim]; exact hd)
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hn] at hdes
  change (∑ i : ι, (Module.finrank F
      ↥(V ⊓ LinearMap.ker (subspaceDesignMcaFour_evalMap i)) : ℝ)) ≤ _ at hdes
  have hsum : (∑ i : ι,
      (Module.finrank F (subspaceDesignMcaFour_coordinateKernel V i) : ℝ)) ≤
      (Module.finrank F V : ℝ) * τ 5 * Fintype.card ι := by
    change (∑ i : ι, (Module.finrank F
      ↥(V ⊓ LinearMap.ker (subspaceDesignMcaFour_evalMap i)) : ℝ)) ≤ _
    exact hdes
  calc
    (∑ i : ι, ((max 0 (d + q i - h) : ℕ) : ℝ)) ≤
      ∑ i : ι, (Module.finrank F
        (subspaceDesignMcaFour_coordinateKernel V i) : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact_mod_cast hq i
    _ ≤ (Module.finrank F V : ℝ) * τ 5 * Fintype.card ι := hsum
    _ = Fintype.card ι * (d : ℝ) * τ 5 := by rw [hdim]; ring

theorem subspaceDesignMcaFour_rank_two_four_seed_design_sum
    {ι : Type} {F : Type} [Field F] [Fintype ι] [Nonempty ι]
    [DecidableEq F] {s : ℕ} [FiniteDimensional F (ι → Fin s → F)]
    (τ : ℕ → ℝ) (C V : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C) (hVC : V ≤ C)
    (hD : Module.finrank F V = 2) (q : ι → ℕ)
    (hq : ∀ i, max 0 (q i - 2) ≤
      Module.finrank F (subspaceDesignMcaFour_coordinateKernel V i)) :
    (∑ i : ι, ((max 0 (q i - 2) : ℕ) : ℝ)) ≤
      Fintype.card ι * (2 : ℝ) * τ 5 := by
  have h := subspaceDesignMcaFour_rank_sensitive_design_sum
    τ C V hdesign hVC (h := 4) (d := 2) hD (by omega) q (by
      intro i
      have hi := hq i
      omega)
  have hsub : ∀ i, 2 + q i - 4 = q i - 2 := by
    intro i
    omega
  simpa [hsub] using h

theorem subspaceDesignMcaFour_four_seed_positive_agreement_lower
    {ι : Type} {F : Type} [Field F] [Fintype ι] [Nonempty ι]
    [DecidableEq F] {s : ℕ}
    (T : Finset F) (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (δ τ₅ : ℝ) (hTcard : T.card = 4)
    (hδ : δ = 5 / 8 - τ₅)
    (hclose : ∀ γ ∈ T,
      (Code.relHammingDist (f₀ + γ • f₁) (U γ) : ℝ) ≤ δ) :
    (4 * τ₅ - 1 / 2) * Fintype.card ι ≤
      ∑ i : ι,
        ((max 0 ((lineAgreementSeeds f₀ f₁ U T i).card - 2) : ℕ) : ℝ) := by
  let q : ι → ℕ := fun i =>
    (lineAgreementSeeds f₀ f₁ U T i).card
  have hlower := lineClose_sum_agreement_lower f₀ f₁ U δ T hclose
  rw [hTcard] at hlower
  have hqsum :
      (∑ i : ι, (q i : ℝ)) ≤
        2 * Fintype.card ι +
          ∑ i : ι, ((max 0 (q i - 2) : ℕ) : ℝ) := by
    calc
      (∑ i : ι, (q i : ℝ)) ≤
        ∑ i : ι, (2 + (max 0 (q i - 2) : ℕ) : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          exact_mod_cast (show q i ≤ 2 + max 0 (q i - 2) by omega)
      _ = 2 * Fintype.card ι +
          ∑ i : ι, ((max 0 (q i - 2) : ℕ) : ℝ) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
          ring_nf
  have hlower' :
      4 * (1 - δ) * Fintype.card ι ≤ ∑ i : ι, (q i : ℝ) := by
    simpa [q, mul_comm, mul_left_comm, mul_assoc] using hlower
  have hpos :
      (4 * (1 - δ) - 2) * Fintype.card ι ≤
        ∑ i : ι, ((max 0 (q i - 2) : ℕ) : ℝ) := by
    nlinarith
  rw [hδ] at hpos
  convert hpos using 1
  ring

noncomputable def subspaceDesignMcaFour_agreementCount
    {ι : Type} {F : Type} [Field F] [DecidableEq F] {s : ℕ}
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (T : Finset F) (i : ι) : ℕ :=
  (lineAgreementSeeds f₀ f₁ U T i).card

def subspaceDesignMcaFour_fourSeedDisagreementCount
    {ι : Type} {F : Type} [Field F] [DecidableEq F] {s : ℕ}
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (α₀ α₁ α₂ α₃ : F) (i : ι) : ℕ :=
  (if U α₀ i = f₀ i + α₀ • f₁ i then 0 else 1) +
  (if U α₁ i = f₀ i + α₁ • f₁ i then 0 else 1) +
  (if U α₂ i = f₀ i + α₂ • f₁ i then 0 else 1) +
  (if U α₃ i = f₀ i + α₃ • f₁ i then 0 else 1)

theorem subspaceDesignMcaFour_residual_eval_eq_zero_iff
    {ι : Type} {F : Type} [Field F] {s : ℕ}
    (U : F → ι → Fin s → F) (c₀ c₁ : ι → Fin s → F)
    (γ : F) (i : ι) :
    subspaceDesignMcaFour_evalMap i
        (subspaceDesignMcaFour_residual U c₀ c₁ γ) = 0 ↔
      U γ i = c₀ i + γ • c₁ i := by
  constructor
  · intro h
    change U γ i - (c₀ i + γ • c₁ i) = 0 at h
    exact sub_eq_zero.mp h
  · intro h
    ext j
    simp [subspaceDesignMcaFour_evalMap, subspaceDesignMcaFour_residual,
      LinearMap.proj_apply, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, h]

theorem subspaceDesignMcaFour_four_seed_coordinate_kernel_bound
    {ι : Type} {F : Type} [Field F] [DecidableEq F] {s : ℕ}
    [FiniteDimensional F (ι → Fin s → F)]
    (U : F → ι → Fin s → F)
    (c₀ c₁ : ι → Fin s → F) (V : Submodule F (ι → Fin s → F))
    (α₀ α₁ α₂ α₃ : F)
    (h01 : α₀ ≠ α₁) (h02 : α₀ ≠ α₂) (h03 : α₀ ≠ α₃)
    (h12 : α₁ ≠ α₂) (h13 : α₁ ≠ α₃) (h23 : α₂ ≠ α₃)
    (hres₀ : subspaceDesignMcaFour_residual U c₀ c₁ α₀ = 0)
    (hres₁ : subspaceDesignMcaFour_residual U c₀ c₁ α₁ = 0)
    (hV₂ : subspaceDesignMcaFour_residual U c₀ c₁ α₂ ∈ V)
    (hV₃ : subspaceDesignMcaFour_residual U c₀ c₁ α₃ ∈ V)
    (hli : LinearIndependent F ![
      subspaceDesignMcaFour_residual U c₀ c₁ α₂,
      subspaceDesignMcaFour_residual U c₀ c₁ α₃])
    (i : ι) :
    max 0
        (subspaceDesignMcaFour_agreementCount c₀ c₁ U
          (insert α₀ (insert α₁ (insert α₂ {α₃}))) i - 2)
      ≤ Module.finrank F (subspaceDesignMcaFour_coordinateKernel V i) := by
  classical
  let S : Finset F := insert α₀ (insert α₁ (insert α₂ ({α₃} : Finset F)))
  let v : Fin 2 → ι → Fin s → F := ![
    subspaceDesignMcaFour_residual U c₀ c₁ α₂,
    subspaceDesignMcaFour_residual U c₀ c₁ α₃]
  have heval₀ :
      subspaceDesignMcaFour_evalMap i
        (subspaceDesignMcaFour_residual U c₀ c₁ α₀) = 0 := by
    rw [hres₀]
    simp [subspaceDesignMcaFour_evalMap]
  have heval₁ :
      subspaceDesignMcaFour_evalMap i
        (subspaceDesignMcaFour_residual U c₀ c₁ α₁) = 0 := by
    rw [hres₁]
    simp [subspaceDesignMcaFour_evalMap]
  have hcard₀₁ : (insert α₀ (insert α₁ (∅ : Finset F))).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [h01])]
    rw [Finset.card_insert_of_notMem (by simp)]
    simp
  have hcard₀₁₂ : (insert α₀ (insert α₁ (insert α₂ ({α₃} : Finset F)))).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h01, h02, h03])]
    rw [Finset.card_insert_of_notMem (by simp [h12, h13])]
    rw [Finset.card_insert_of_notMem (by simp [h23])]
    simp
  have hcard₀₁₂' : (insert α₀ (insert α₁ (insert α₂ (∅ : Finset F)))).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h01, h02])]
    rw [Finset.card_insert_of_notMem (by simp [h12])]
    simp
  have hcard₀₁₃ : (insert α₀ (insert α₁ (insert α₃ (∅ : Finset F)))).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [h01, h03])]
    rw [Finset.card_insert_of_notMem (by simp [h13])]
    simp
  have hq :
      subspaceDesignMcaFour_agreementCount c₀ c₁ U S i =
        2 +
          (if subspaceDesignMcaFour_evalMap i (v 0) = 0 then 1 else 0) +
          (if subspaceDesignMcaFour_evalMap i (v 1) = 0 then 1 else 0) := by
    simp only [subspaceDesignMcaFour_agreementCount, lineAgreementSeeds]
    have hfilter : S.filter (fun γ => U γ i = c₀ i + γ • c₁ i) =
        S.filter (fun γ => subspaceDesignMcaFour_evalMap i
          (subspaceDesignMcaFour_residual U c₀ c₁ γ) = 0) := by
      apply Finset.filter_congr
      intro γ hγ
      exact (subspaceDesignMcaFour_residual_eval_eq_zero_iff U c₀ c₁ γ i).symm
    rw [hfilter]
    by_cases h₂ : subspaceDesignMcaFour_evalMap i
        (subspaceDesignMcaFour_residual U c₀ c₁ α₂) = 0
    · by_cases h₃ : subspaceDesignMcaFour_evalMap i
          (subspaceDesignMcaFour_residual U c₀ c₁ α₃) = 0
      · simpa [S, Finset.filter_insert, Finset.filter_singleton,
          heval₀, heval₁, h₂, h₃, v, Matrix.cons_val_zero, Matrix.cons_val_one]
          using hcard₀₁₂
      · simpa [S, Finset.filter_insert, Finset.filter_singleton,
          heval₀, heval₁, h₂, h₃, v, Matrix.cons_val_zero, Matrix.cons_val_one]
          using hcard₀₁₂'
    · by_cases h₃ : subspaceDesignMcaFour_evalMap i
          (subspaceDesignMcaFour_residual U c₀ c₁ α₃) = 0
      · simpa [S, Finset.filter_insert, Finset.filter_singleton,
          heval₀, heval₁, h₂, h₃, v, Matrix.cons_val_zero, Matrix.cons_val_one]
          using hcard₀₁₃
      · simpa [S, Finset.filter_insert, Finset.filter_singleton,
          heval₀, heval₁, h₂, h₃, v, Matrix.cons_val_zero, Matrix.cons_val_one]
          using hcard₀₁
  let J : Finset (Fin 2) :=
    Finset.univ.filter (fun j => subspaceDesignMcaFour_evalMap i (v j) = 0)
  have hJcard :
      J.card =
        (if subspaceDesignMcaFour_evalMap i (v 0) = 0 then 1 else 0) +
          (if subspaceDesignMcaFour_evalMap i (v 1) = 0 then 1 else 0) := by
    simp only [J, Finset.univ_fin2, Finset.filter_insert, Finset.filter_singleton,
      v, Matrix.cons_val_zero, Matrix.cons_val_one]
    split_ifs <;> simp_all
  have hqbound : subspaceDesignMcaFour_agreementCount c₀ c₁ U S i - 2 ≤ J.card := by
    rw [hq, hJcard]
    omega
  have hvli : LinearIndependent F v := by
    simpa [v] using hli
  let w : J → ↥(subspaceDesignMcaFour_coordinateKernel V i) := fun j =>
    ⟨v j.1, by
      refine ⟨?_, LinearMap.mem_ker.mpr (Finset.mem_filter.mp j.2).2⟩
      have hzero_or_one : j.1.val = 0 ∨ j.1.val = 1 := by omega
      rcases hzero_or_one with hz | ho
      · have hj : j.1 = 0 := Fin.ext hz
        simpa [hj, v] using hV₂
      · have hj : j.1 = 1 := Fin.ext ho
        simpa [hj, v] using hV₃⟩
  have hwli : LinearIndependent F w := by
    apply LinearIndependent.of_comp
      (subspaceDesignMcaFour_coordinateKernel V i).subtype
    change LinearIndependent F
      (fun j : J => (subspaceDesignMcaFour_coordinateKernel V i).subtype (w j))
    have hcomp : (fun j : J =>
        (subspaceDesignMcaFour_coordinateKernel V i).subtype (w j)) =
          fun j : J => v j.1 := by
      funext j
      rfl
    rw [hcomp]
    exact hvli.comp (fun j : J => j.1) (by
      intro x y hxy
      exact Subtype.ext hxy)
  have hcard : J.card ≤
      Module.finrank F (subspaceDesignMcaFour_coordinateKernel V i) :=
    by simpa using hwli.fintype_card_le_finrank
  have hnonneg : 0 ≤
      subspaceDesignMcaFour_agreementCount c₀ c₁ U S i - 2 := Nat.zero_le _
  have hqbound' :
      max 0 (subspaceDesignMcaFour_agreementCount c₀ c₁ U S i - 2) ≤ J.card := by
    rw [Nat.max_eq_right hnonneg]
    exact hqbound
  exact hqbound'.trans hcard

theorem subspaceDesignMcaFour_rank_two_four_seed_design_sum_from_anchors
    {ι : Type} {F : Type} [Field F] [DecidableEq F]
    [Fintype ι] [Nonempty ι] {s : ℕ}
    [FiniteDimensional F (ι → Fin s → F)]
    (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C) (T : Finset F)
    (U : F → ι → Fin s → F) (c₀ c₁ : ι → Fin s → F)
    (α₀ α₁ : F) (hα₀ : α₀ ∈ T) (hα₁ : α₁ ∈ T) (h01 : α₀ ≠ α₁)
    (hU : ∀ γ ∈ T, U γ ∈ C) (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C)
    (hres₀ : subspaceDesignMcaFour_residual U c₀ c₁ α₀ = 0)
    (hres₁ : subspaceDesignMcaFour_residual U c₀ c₁ α₁ = 0)
    (hD : Module.finrank F
      (subspaceDesignMcaFour_residualSpan T U c₀ c₁) = 2) :
    ∃ α₂ ∈ T, ∃ α₃ ∈ T,
      α₀ ≠ α₂ ∧ α₀ ≠ α₃ ∧ α₁ ≠ α₂ ∧ α₁ ≠ α₃ ∧ α₂ ≠ α₃ ∧
      ∑ i : ι,
        (((max 0
          (subspaceDesignMcaFour_agreementCount c₀ c₁ U
            (insert α₀ (insert α₁ (insert α₂ {α₃}))) i - 2) : ℕ) : ℝ))
        ≤ Fintype.card ι * (2 : ℝ) * τ 5 := by
  classical
  let V := subspaceDesignMcaFour_residualSpan T U c₀ c₁
  have hVC : V ≤ C := by
    change Submodule.span F
      (subspaceDesignMcaFour_residual U c₀ c₁ '' (T : Set F)) ≤ C
    apply Submodule.span_le.mpr
    rintro x ⟨γ, hγ, rfl⟩
    exact C.sub_mem (hU γ hγ) (C.add_mem hc₀ (C.smul_mem γ hc₁))
  obtain ⟨α₂, hα₂, α₃, hα₃, _, _, h01', h02, h03, h12, h13, h23, hli⟩ :=
    subspaceDesignMcaFour_exists_four_seed_configuration
      T U c₀ c₁ α₀ α₁ hα₀ hα₁ h01 hres₀ hres₁ hD
  have hV₂ : subspaceDesignMcaFour_residual U c₀ c₁ α₂ ∈ V := by
    apply Submodule.subset_span
    exact ⟨α₂, hα₂, rfl⟩
  have hV₃ : subspaceDesignMcaFour_residual U c₀ c₁ α₃ ∈ V := by
    apply Submodule.subset_span
    exact ⟨α₃, hα₃, rfl⟩
  let S : Finset F := insert α₀ (insert α₁ (insert α₂ ({α₃} : Finset F)))
  have hsum := subspaceDesignMcaFour_rank_two_four_seed_design_sum
    τ C V hdesign hVC hD
    (fun i => subspaceDesignMcaFour_agreementCount c₀ c₁ U S i)
    (fun i => subspaceDesignMcaFour_four_seed_coordinate_kernel_bound
      U c₀ c₁ V α₀ α₁ α₂ α₃ h01' h02 h03 h12 h13 h23
      hres₀ hres₁ hV₂ hV₃ hli i)
  exact ⟨α₂, hα₂, α₃, hα₃, h02, h03, h12, h13, h23, by
    simpa [S] using hsum⟩

noncomputable def subspaceDesignMcaFour_noEightAligned
    {ι : Type} {F : Type} [Field F] [DecidableEq F] {s : ℕ}
    (C : Submodule F (ι → Fin s → F)) (T : Finset F)
    (U : F → ι → Fin s → F) : Prop := by
  classical
  exact ∀ c₀ ∈ C, ∀ c₁ ∈ C,
    (T.filter (fun γ => U γ = c₀ + γ • c₁)).card < 8

theorem subspaceDesignMcaFour_eval_eq_zero_of_kernel_finrank_eq_zero
    {ι : Type} {F : Type} [Field F] {s : ℕ}
    [FiniteDimensional F (ι → Fin s → F)]
    (V : Submodule F (ι → Fin s → F)) (i : ι)
    (v : ι → Fin s → F) (hv : v ∈ V)
    (h_eval : subspaceDesignMcaFour_evalMap i v = 0)
    (hk : Module.finrank F (subspaceDesignMcaFour_coordinateKernel V i) = 0) :
    v = 0 := by
  have hbot : subspaceDesignMcaFour_coordinateKernel V i = ⊥ :=
    Submodule.finrank_eq_zero.mp hk
  have hvker : v ∈ subspaceDesignMcaFour_coordinateKernel V i := by
    exact ⟨hv, LinearMap.mem_ker.mpr h_eval⟩
  have : v ∈ (⊥ : Submodule F (ι → Fin s → F)) := by
    simpa [hbot] using hvker
  simpa using this

theorem subspaceDesignMcaFour_coordinateKernel_finrank_ge_one_of_nonzero
    {ι : Type} {F : Type} [Field F] {s : ℕ}
    [FiniteDimensional F (ι → Fin s → F)]
    (V : Submodule F (ι → Fin s → F)) (i : ι)
    (v : ι → Fin s → F) (hv : v ∈ V)
    (heval : subspaceDesignMcaFour_evalMap i v = 0) (hv0 : v ≠ 0) :
    1 ≤ Module.finrank F (subspaceDesignMcaFour_coordinateKernel V i) := by
  by_contra h
  have hk : Module.finrank F (subspaceDesignMcaFour_coordinateKernel V i) = 0 := by
    omega
  have hz := subspaceDesignMcaFour_eval_eq_zero_of_kernel_finrank_eq_zero
    V i v hv heval hk
  exact hv0 hz

theorem subspaceDesignMcaFour_coordinateKernel_finrank_ge_two_of_independent
    {ι : Type} {F : Type} [Field F] {s : ℕ}
    [FiniteDimensional F (ι → Fin s → F)]
    (V : Submodule F (ι → Fin s → F)) (i : ι)
    (v : Fin 2 → ι → Fin s → F) (hv : ∀ j, v j ∈ V)
    (heval : ∀ j, subspaceDesignMcaFour_evalMap i (v j) = 0)
    (hli : LinearIndependent F v) :
    2 ≤ Module.finrank F (subspaceDesignMcaFour_coordinateKernel V i) := by
  let w : Fin 2 → subspaceDesignMcaFour_coordinateKernel V i := fun j =>
    ⟨v j, hv j, LinearMap.mem_ker.mpr (heval j)⟩
  have hw : LinearIndependent F w := by
    apply LinearIndependent.of_comp
      (subspaceDesignMcaFour_coordinateKernel V i).subtype
    change LinearIndependent F (fun j => (v j : ι → Fin s → F))
    exact hli
  simpa using hw.fintype_card_le_finrank

theorem subspaceDesignMcaFour_affine_values_eq_of_two_roots
    {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    (α β : F) (hαβ : α ≠ β) (a₀ a₁ b₀ b₁ : W)
    (hα : a₀ + α • a₁ = b₀ + α • b₁)
    (hβ : a₀ + β • a₁ = b₀ + β • b₁) :
    ∀ γ : F, a₀ + γ • a₁ = b₀ + γ • b₁ := by
  have hdiff : (β - α) • (a₁ - b₁) = 0 := by
    calc
      (β - α) • (a₁ - b₁) =
          (a₀ + (β : F) • a₁ - (b₀ + (β : F) • b₁)) -
            (a₀ + (α : F) • a₁ - (b₀ + (α : F) • b₁)) := by module
      _ = 0 := by rw [hα, hβ]; simp
  have hcoef : a₁ = b₁ := by
    rcases smul_eq_zero.mp hdiff with h | h
    · exact (sub_ne_zero.mpr (Ne.symm hαβ) h).elim
    · exact sub_eq_zero.mp h
  have hintercept : a₀ = b₀ := by
    have hα' : a₀ + α • b₁ = b₀ + α • b₁ := by
      simpa [hcoef] using hα
    have hzero : a₀ - b₀ = 0 := by
      calc
        a₀ - b₀ = (a₀ + α • b₁) - (b₀ + α • b₁) := by module
        _ = 0 := by rw [hα']; simp
    exact sub_eq_zero.mp hzero
  intro γ
  simp [hcoef, hintercept]

theorem subspaceDesignMcaFour_affine_values_relation_of_root
    {F W : Type} [Field F] [AddCommGroup W] [Module F W]
    (α β γ : F) (a₀ a₁ : W) (hα : a₀ + α • a₁ = 0) :
    (β - α) • (a₀ + γ • a₁) =
      (γ - α) • (a₀ + β • a₁) := by
  have hbase : a₀ = -(α • a₁) := by
    calc
      a₀ = (a₀ + α • a₁) - α • a₁ := by module
      _ = -(α • a₁) := by rw [hα]; simp
  calc
    (β - α) • (a₀ + γ • a₁) =
        ((β - α) * (γ - α)) • a₁ := by
          rw [hbase]
          module
    _ = ((γ - α) * (β - α)) • a₁ := by rw [mul_comm]
    _ = (γ - α) • (a₀ + β • a₁) := by
          rw [hbase]
          module

theorem subspaceDesignMcaFour_four_seed_disagreement_kernel_lower
    {ι : Type} {F : Type} [Field F] [DecidableEq F] {s : ℕ}
    [FiniteDimensional F (ι → Fin s → F)]
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (c₀ c₁ : ι → Fin s → F)
    (V : Submodule F (ι → Fin s → F))
    (α₀ α₁ α₂ α₃ : F)
    (hα₀α₁ : α₀ ≠ α₁) (hα₀α₂ : α₀ ≠ α₂)
    (hα₁α₂ : α₁ ≠ α₂)
    (hres₀ : subspaceDesignMcaFour_residual U c₀ c₁ α₀ = 0)
    (hres₁ : subspaceDesignMcaFour_residual U c₀ c₁ α₁ = 0)
    (hv₂ : subspaceDesignMcaFour_residual U c₀ c₁ α₂ ∈ V)
    (hv₃ : subspaceDesignMcaFour_residual U c₀ c₁ α₃ ∈ V)
    (hli : LinearIndependent F ![
      subspaceDesignMcaFour_residual U c₀ c₁ α₂,
      subspaceDesignMcaFour_residual U c₀ c₁ α₃])
    (i : ι) :
    2 ≤ subspaceDesignMcaFour_fourSeedDisagreementCount
      f₀ f₁ U α₀ α₁ α₂ α₃ i +
      Module.finrank F (subspaceDesignMcaFour_coordinateKernel V i) := by
  let m := subspaceDesignMcaFour_fourSeedDisagreementCount
    f₀ f₁ U α₀ α₁ α₂ α₃ i
  let d₀ := c₀ i - f₀ i
  let d₁ := c₁ i - f₁ i
  let r₂ := subspaceDesignMcaFour_residual U c₀ c₁ α₂
  let r₃ := subspaceDesignMcaFour_residual U c₀ c₁ α₃
  have hU₀ : U α₀ = c₀ + α₀ • c₁ := sub_eq_zero.mp hres₀
  have hU₁ : U α₁ = c₀ + α₁ • c₁ := sub_eq_zero.mp hres₁
  have hU₀i : U α₀ i = c₀ i + α₀ • c₁ i :=
    congrArg (fun v => v i) hU₀
  have hU₁i : U α₁ i = c₀ i + α₁ • c₁ i :=
    congrArg (fun v => v i) hU₁
  have hres_eval (γ : F) (hgood : U γ i = f₀ i + γ • f₁ i) :
      subspaceDesignMcaFour_evalMap i
          (subspaceDesignMcaFour_residual U c₀ c₁ γ) =
        -(d₀ + γ • d₁) := by
    ext j
    simp [subspaceDesignMcaFour_evalMap, subspaceDesignMcaFour_residual,
      LinearMap.proj_apply, d₀, d₁, Pi.sub_apply, Pi.smul_apply, hgood]
    ring
  have hline_roots (hgood₀ : U α₀ i = f₀ i + α₀ • f₁ i)
      (hgood₁ : U α₁ i = f₀ i + α₁ • f₁ i) :
      ∀ γ : F, c₀ i + γ • c₁ i = f₀ i + γ • f₁ i := by
    apply subspaceDesignMcaFour_affine_values_eq_of_two_roots
      α₀ α₁ hα₀α₁ (c₀ i) (c₁ i) (f₀ i) (f₁ i)
    · calc
        c₀ i + α₀ • c₁ i = U α₀ i := hU₀i.symm
        _ = f₀ i + α₀ • f₁ i := hgood₀
    · calc
        c₀ i + α₁ • c₁ i = U α₁ i := hU₁i.symm
        _ = f₀ i + α₁ • f₁ i := hgood₁
  have heval_zero_of_line (γ : F)
      (hgood : U γ i = f₀ i + γ • f₁ i)
      (hline : c₀ i + γ • c₁ i = f₀ i + γ • f₁ i) :
      subspaceDesignMcaFour_evalMap i
        (subspaceDesignMcaFour_residual U c₀ c₁ γ) = 0 := by
    rw [hres_eval γ hgood]
    have hd : d₀ + γ • d₁ = 0 := by
      change (c₀ i - f₀ i) + γ • (c₁ i - f₁ i) = 0
      calc
        _ = (c₀ i + γ • c₁ i) - (f₀ i + γ • f₁ i) := by module
        _ = 0 := by rw [hline]; simp
    rw [hd]
    simp
  by_cases hm₂ : 2 ≤ m
  · change 2 ≤ m + Module.finrank F
      (subspaceDesignMcaFour_coordinateKernel V i)
    omega
  · have hm₁ : m ≤ 1 := by omega
    by_cases hgood₀ : U α₀ i = f₀ i + α₀ • f₁ i
    · by_cases hgood₁ : U α₁ i = f₀ i + α₁ • f₁ i
      · by_cases hgood₂ : U α₂ i = f₀ i + α₂ • f₁ i
        · by_cases hgood₃ : U α₃ i = f₀ i + α₃ • f₁ i
          · have hline := hline_roots hgood₀ hgood₁
            have heval₂ : subspaceDesignMcaFour_evalMap i r₂ = 0 := by
              simpa [r₂] using heval_zero_of_line α₂ hgood₂ (hline α₂)
            have heval₃ : subspaceDesignMcaFour_evalMap i r₃ = 0 := by
              simpa [r₃] using heval_zero_of_line α₃ hgood₃ (hline α₃)
            have hdim := subspaceDesignMcaFour_coordinateKernel_finrank_ge_two_of_independent
              V i ![r₂, r₃] (by
                intro j
                fin_cases j
                · exact hv₂
                · exact hv₃) (by
                intro j
                fin_cases j
                · exact heval₂
                · exact heval₃) (by simpa [r₂, r₃] using hli)
            have hmval : m = 0 := by
              simp [m, subspaceDesignMcaFour_fourSeedDisagreementCount,
                hgood₀, hgood₁, hgood₂, hgood₃]
            change 2 ≤ m + Module.finrank F
              (subspaceDesignMcaFour_coordinateKernel V i)
            rw [hmval]
            omega
          · have hline := hline_roots hgood₀ hgood₁
            have heval₂ : subspaceDesignMcaFour_evalMap i r₂ = 0 := by
              simpa [r₂] using heval_zero_of_line α₂ hgood₂ (hline α₂)
            have hdim : 1 ≤ Module.finrank F
                (subspaceDesignMcaFour_coordinateKernel V i) :=
              subspaceDesignMcaFour_coordinateKernel_finrank_ge_one_of_nonzero
                V i r₂ hv₂ heval₂ (by
                  intro h
                  exact (LinearIndependent.ne_zero 0 hli) (by simpa [r₂] using h))
            have hmval : m = 1 := by
              simp [m, subspaceDesignMcaFour_fourSeedDisagreementCount,
                hgood₀, hgood₁, hgood₂, hgood₃]
            change 2 ≤ m + Module.finrank F
              (subspaceDesignMcaFour_coordinateKernel V i)
            rw [hmval]
            omega
        · by_cases hgood₃ : U α₃ i = f₀ i + α₃ • f₁ i
          · have hline := hline_roots hgood₀ hgood₁
            have heval₃ : subspaceDesignMcaFour_evalMap i r₃ = 0 := by
              simpa [r₃] using heval_zero_of_line α₃ hgood₃ (hline α₃)
            have hdim : 1 ≤ Module.finrank F
                (subspaceDesignMcaFour_coordinateKernel V i) :=
              subspaceDesignMcaFour_coordinateKernel_finrank_ge_one_of_nonzero
                V i r₃ hv₃ heval₃ (by
                  intro h
                  exact (LinearIndependent.ne_zero 1 hli) (by simpa [r₃] using h))
            have hmval : m = 1 := by
              simp [m, subspaceDesignMcaFour_fourSeedDisagreementCount,
                hgood₀, hgood₁, hgood₂, hgood₃]
            change 2 ≤ m + Module.finrank F
              (subspaceDesignMcaFour_coordinateKernel V i)
            rw [hmval]
            omega
          · simp [m, subspaceDesignMcaFour_fourSeedDisagreementCount,
              hgood₀, hgood₁, ite_eq_right hgood₂, ite_eq_right hgood₃] at hm₁
      · by_cases hgood₂ : U α₂ i = f₀ i + α₂ • f₁ i
        · by_cases hgood₃ : U α₃ i = f₀ i + α₃ • f₁ i
          · have hroot : d₀ + α₀ • d₁ = 0 := by
              have hline : c₀ i + α₀ • c₁ i =
                  f₀ i + α₀ • f₁ i := by
                calc
                  c₀ i + α₀ • c₁ i = U α₀ i := hU₀i.symm
                  _ = f₀ i + α₀ • f₁ i := hgood₀
              change (c₀ i - f₀ i) + α₀ • (c₁ i - f₁ i) = 0
              calc
                _ = (c₀ i + α₀ • c₁ i) -
                    (f₀ i + α₀ • f₁ i) := by module
                _ = 0 := by rw [hline]; simp
            have hrel := subspaceDesignMcaFour_affine_values_relation_of_root
              α₀ α₂ α₃ d₀ d₁ hroot
            have heval₂ := hres_eval α₂ hgood₂
            have heval₃ := hres_eval α₃ hgood₃
            let w := (α₂ - α₀) • r₃ - (α₃ - α₀) • r₂
            have hevalw : subspaceDesignMcaFour_evalMap i w = 0 := by
              dsimp [w]
              rw [map_sub, map_smul, map_smul, heval₃, heval₂]
              have hrel' :
                  (α₂ - α₀) • (-(d₀ + α₃ • d₁)) =
                    (α₃ - α₀) • (-(d₀ + α₂ • d₁)) := by
                simpa [smul_neg] using congrArg (fun z => -z) hrel
              exact sub_eq_zero.mpr hrel'
            have hwmem : w ∈ V := by
              dsimp [w]
              exact V.sub_mem (V.smul_mem _ hv₃) (V.smul_mem _ hv₂)
            have hwne : w ≠ 0 := by
              intro hw
              have hcomb :
                  (-(α₃ - α₀)) • r₂ + (α₂ - α₀) • r₃ = 0 := by
                calc
                  (-(α₃ - α₀)) • r₂ + (α₂ - α₀) • r₃ =
                      (α₂ - α₀) • r₃ - (α₃ - α₀) • r₂ := by module
                  _ = 0 := by simpa [w] using hw
              have hcoef := (LinearIndependent.pair_iff.mp hli)
                (-(α₃ - α₀)) (α₂ - α₀) hcomb
              exact (sub_ne_zero.mpr (Ne.symm hα₀α₂)) hcoef.2
            have hdim : 1 ≤ Module.finrank F
                (subspaceDesignMcaFour_coordinateKernel V i) :=
              subspaceDesignMcaFour_coordinateKernel_finrank_ge_one_of_nonzero
                V i w hwmem hevalw hwne
            have hmval : m = 1 := by
              simp [m, subspaceDesignMcaFour_fourSeedDisagreementCount,
                hgood₀, hgood₁, hgood₂, hgood₃]
            change 2 ≤ m + Module.finrank F
              (subspaceDesignMcaFour_coordinateKernel V i)
            rw [hmval]
            omega
          · by_cases hgood₃ : U α₃ i = f₀ i + α₃ • f₁ i
            · simp [m, subspaceDesignMcaFour_fourSeedDisagreementCount,
                hgood₀, hgood₂, hgood₃, ite_eq_right hgood₁] at hm₁; simp_all
            · simp [m, subspaceDesignMcaFour_fourSeedDisagreementCount,
                hgood₀, hgood₂, ite_eq_right hgood₁, ite_eq_right hgood₃] at hm₁
        · by_cases hgood₂ : U α₂ i = f₀ i + α₂ • f₁ i
          · by_cases hgood₃ : U α₃ i = f₀ i + α₃ • f₁ i
            · simp [m, subspaceDesignMcaFour_fourSeedDisagreementCount,
                hgood₀, hgood₂, hgood₃, ite_eq_right hgood₁] at hm₁; simp_all
            · simp [m, subspaceDesignMcaFour_fourSeedDisagreementCount,
                hgood₀, hgood₂, ite_eq_right hgood₁, ite_eq_right hgood₃] at hm₁
          · by_cases hgood₃ : U α₃ i = f₀ i + α₃ • f₁ i
            · simp [m, subspaceDesignMcaFour_fourSeedDisagreementCount,
                hgood₀, hgood₃, ite_eq_right hgood₁, ite_eq_right hgood₂] at hm₁
            · simp [m, subspaceDesignMcaFour_fourSeedDisagreementCount,
                hgood₀, ite_eq_right hgood₁, ite_eq_right hgood₂,
                ite_eq_right hgood₃] at hm₁
    · by_cases hgood₁ : U α₁ i = f₀ i + α₁ • f₁ i
      · by_cases hgood₂ : U α₂ i = f₀ i + α₂ • f₁ i
        · by_cases hgood₃ : U α₃ i = f₀ i + α₃ • f₁ i
          · have hroot : d₀ + α₁ • d₁ = 0 := by
              have hline : c₀ i + α₁ • c₁ i =
                  f₀ i + α₁ • f₁ i := by
                calc
                  c₀ i + α₁ • c₁ i = U α₁ i := hU₁i.symm
                  _ = f₀ i + α₁ • f₁ i := hgood₁
              change (c₀ i - f₀ i) + α₁ • (c₁ i - f₁ i) = 0
              calc
                _ = (c₀ i + α₁ • c₁ i) -
                    (f₀ i + α₁ • f₁ i) := by module
                _ = 0 := by rw [hline]; simp
            have hrel := subspaceDesignMcaFour_affine_values_relation_of_root
              α₁ α₂ α₃ d₀ d₁ hroot
            have heval₂ := hres_eval α₂ hgood₂
            have heval₃ := hres_eval α₃ hgood₃
            let w := (α₂ - α₁) • r₃ - (α₃ - α₁) • r₂
            have hevalw : subspaceDesignMcaFour_evalMap i w = 0 := by
              dsimp [w]
              rw [map_sub, map_smul, map_smul, heval₃, heval₂]
              have hrel' :
                  (α₂ - α₁) • (-(d₀ + α₃ • d₁)) =
                    (α₃ - α₁) • (-(d₀ + α₂ • d₁)) := by
                simpa [smul_neg] using congrArg (fun z => -z) hrel
              exact sub_eq_zero.mpr hrel'
            have hwmem : w ∈ V := by
              dsimp [w]
              exact V.sub_mem (V.smul_mem _ hv₃) (V.smul_mem _ hv₂)
            have hwne : w ≠ 0 := by
              intro hw
              have hcomb :
                  (-(α₃ - α₁)) • r₂ + (α₂ - α₁) • r₃ = 0 := by
                calc
                  (-(α₃ - α₁)) • r₂ + (α₂ - α₁) • r₃ =
                      (α₂ - α₁) • r₃ - (α₃ - α₁) • r₂ := by module
                  _ = 0 := by simpa [w] using hw
              have hcoef := (LinearIndependent.pair_iff.mp hli)
                (-(α₃ - α₁)) (α₂ - α₁) hcomb
              exact (sub_ne_zero.mpr (Ne.symm hα₁α₂)) hcoef.2
            have hdim : 1 ≤ Module.finrank F
                (subspaceDesignMcaFour_coordinateKernel V i) :=
              subspaceDesignMcaFour_coordinateKernel_finrank_ge_one_of_nonzero
                V i w hwmem hevalw hwne
            have hmval : m = 1 := by
              simp [m, subspaceDesignMcaFour_fourSeedDisagreementCount,
                hgood₀, hgood₁, hgood₂, hgood₃]
            change 2 ≤ m + Module.finrank F
              (subspaceDesignMcaFour_coordinateKernel V i)
            rw [hmval]
            omega
          · simp [m, subspaceDesignMcaFour_fourSeedDisagreementCount,
              hgood₁, hgood₂, ite_eq_right hgood₀, ite_eq_right hgood₃] at hm₁
        · simp [m, subspaceDesignMcaFour_fourSeedDisagreementCount,
            hgood₁, ite_eq_right hgood₀, ite_eq_right hgood₂] at hm₁
          split_ifs at hm₁ <;> omega
      · simp [m, subspaceDesignMcaFour_fourSeedDisagreementCount,
          ite_eq_right hgood₀, ite_eq_right hgood₁] at hm₁
        split_ifs at hm₁ <;> omega

theorem subspaceDesignMcaFour_sum_pointwise_disagreement_kernel_lower
    {ι : Type} [Fintype ι]
    (m k : ι → ℕ) (hpoint : ∀ i, 2 ≤ m i + k i) :
    (2 : ℝ) * Fintype.card ι ≤
      (∑ i, (m i : ℝ)) + (∑ i, (k i : ℝ)) := by
  calc
    (2 : ℝ) * Fintype.card ι = ∑ _i : ι, (2 : ℝ) := by simp; ring
    _ ≤ ∑ i : ι, ((m i : ℝ) + (k i : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      exact_mod_cast hpoint i
    _ = (∑ i, (m i : ℝ)) + (∑ i, (k i : ℝ)) := by
      rw [Finset.sum_add_distrib]

theorem subspaceDesignMcaFour_residual_affine_relation
    {ι : Type} {F : Type} [Field F] {s : ℕ}
    (U : F → ι → Fin s → F) (c₀ c₁ : ι → Fin s → F)
    (α β γ : F) :
    (β - γ) • subspaceDesignMcaFour_residual U c₀ c₁ α +
      (γ - α) • subspaceDesignMcaFour_residual U c₀ c₁ β +
      (α - β) • subspaceDesignMcaFour_residual U c₀ c₁ γ =
    (β - γ) • U α + (γ - α) • U β + (α - β) • U γ := by
  ext i j
  simp [subspaceDesignMcaFour_residual, Pi.sub_apply, Pi.add_apply,
    Pi.smul_apply]
  ring

theorem subspaceDesignMcaFour_affine_relation_vanishes_at_agreement_coordinate
    {ι : Type} {F : Type} [Field F] {s : ℕ}
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (c₀ c₁ : ι → Fin s → F) (i : ι) (α β γ : F)
    (hα : U α i = f₀ i + α • f₁ i)
    (hβ : U β i = f₀ i + β • f₁ i)
    (hγ : U γ i = f₀ i + γ • f₁ i) :
    subspaceDesignMcaFour_evalMap i
        ((β - γ) • subspaceDesignMcaFour_residual U c₀ c₁ α +
          (γ - α) • subspaceDesignMcaFour_residual U c₀ c₁ β +
          (α - β) • subspaceDesignMcaFour_residual U c₀ c₁ γ) = 0 := by
  rw [subspaceDesignMcaFour_residual_affine_relation]
  ext j
  simp [subspaceDesignMcaFour_evalMap, LinearMap.proj_apply,
    Pi.add_apply, Pi.smul_apply, hα, hβ, hγ]
  ring

theorem subspaceDesignMcaFour_interpolation_of_affine_relation
    {ι : Type} {F : Type} [Field F] {s : ℕ}
    (U : F → ι → Fin s → F) (α β γ : F) (hαβ : α ≠ β)
    (hrel : (β - γ) • U α + (γ - α) • U β + (α - β) • U γ = 0) :
    U γ = subspaceDesignMcaFour_interpolationIntercept U α β +
      γ • subspaceDesignMcaFour_interpolationSlope U α β := by
  have hba : β - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hαβ)
  have hscale :
      (β - α) •
        (U γ - (subspaceDesignMcaFour_interpolationIntercept U α β +
          γ • subspaceDesignMcaFour_interpolationSlope U α β)) = 0 := by
    calc
      (β - α) •
          (U γ - (subspaceDesignMcaFour_interpolationIntercept U α β +
            γ • subspaceDesignMcaFour_interpolationSlope U α β)) =
        -((β - γ) • U α + (γ - α) • U β + (α - β) • U γ) := by
          ext i j
          simp [subspaceDesignMcaFour_interpolationIntercept,
            subspaceDesignMcaFour_interpolationSlope, Pi.sub_apply,
            Pi.add_apply, Pi.smul_apply]
          field_simp [hba]
          ring
      _ = 0 := by rw [hrel]; simp
  rcases smul_eq_zero.mp hscale with h | h
  · exact (hba h).elim
  · exact sub_eq_zero.mp h

theorem subspaceDesignMcaFour_agreement_count_le_seven_of_kernel_zero
    {ι : Type} {F : Type} [Field F] [DecidableEq F] {s : ℕ}
    [FiniteDimensional F (ι → Fin s → F)]
    (C : Submodule F (ι → Fin s → F)) (T : Finset F)
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (c₀ c₁ : ι → Fin s → F) (i : ι)
    (hU : ∀ γ ∈ T, U γ ∈ C)
    (hno8 : subspaceDesignMcaFour_noEightAligned C T U)
    (hk : Module.finrank F
      (subspaceDesignMcaFour_coordinateKernel
        (subspaceDesignMcaFour_residualSpan T U c₀ c₁) i) = 0) :
    subspaceDesignMcaFour_agreementCount f₀ f₁ U T i ≤ 7 := by
  classical
  by_contra htarget
  let A := lineAgreementSeeds f₀ f₁ U T i
  have hAcard : 8 ≤ A.card := by
    change 8 ≤ subspaceDesignMcaFour_agreementCount f₀ f₁ U T i
    omega
  obtain ⟨α, hα, β, hβ, hαβ⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < A.card)
  have hαT : α ∈ T := (Finset.mem_filter.mp hα).1
  have hβT : β ∈ T := (Finset.mem_filter.mp hβ).1
  have hαagree : U α i = f₀ i + α • f₁ i :=
    (Finset.mem_filter.mp hα).2
  have hβagree : U β i = f₀ i + β • f₁ i :=
    (Finset.mem_filter.mp hβ).2
  have hc₀ : subspaceDesignMcaFour_interpolationIntercept U α β ∈ C :=
    subspaceDesignMcaFour_interpolation_intercept_mem C U α β
      (hU α hαT) (hU β hβT)
  have hc₁ : subspaceDesignMcaFour_interpolationSlope U α β ∈ C :=
    subspaceDesignMcaFour_interpolation_slope_mem C U α β
      (hU α hαT) (hU β hβT)
  have halign : ∀ γ ∈ A,
      U γ = subspaceDesignMcaFour_interpolationIntercept U α β +
        γ • subspaceDesignMcaFour_interpolationSlope U α β := by
    intro γ hγ
    have hγT : γ ∈ T := (Finset.mem_filter.mp hγ).1
    have hγagree : U γ i = f₀ i + γ • f₁ i :=
      (Finset.mem_filter.mp hγ).2
    let R :=
      (β - γ) • subspaceDesignMcaFour_residual U c₀ c₁ α +
        (γ - α) • subspaceDesignMcaFour_residual U c₀ c₁ β +
        (α - β) • subspaceDesignMcaFour_residual U c₀ c₁ γ
    have hresα :
        subspaceDesignMcaFour_residual U c₀ c₁ α ∈
          subspaceDesignMcaFour_residualSpan T U c₀ c₁ := by
      apply Submodule.subset_span
      exact ⟨α, hαT, rfl⟩
    have hresβ :
        subspaceDesignMcaFour_residual U c₀ c₁ β ∈
          subspaceDesignMcaFour_residualSpan T U c₀ c₁ := by
      apply Submodule.subset_span
      exact ⟨β, hβT, rfl⟩
    have hresγ :
        subspaceDesignMcaFour_residual U c₀ c₁ γ ∈
          subspaceDesignMcaFour_residualSpan T U c₀ c₁ := by
      apply Submodule.subset_span
      exact ⟨γ, hγT, rfl⟩
    have hRmem :
        R ∈ subspaceDesignMcaFour_residualSpan T U c₀ c₁ := by
      dsimp [R]
      exact (Submodule.add_mem _ (Submodule.add_mem _
        (Submodule.smul_mem _ _ hresα)
        (Submodule.smul_mem _ _ hresβ))
        (Submodule.smul_mem _ _ hresγ))
    have hReval : subspaceDesignMcaFour_evalMap i R = 0 := by
      dsimp [R]
      exact subspaceDesignMcaFour_affine_relation_vanishes_at_agreement_coordinate
        f₀ f₁ U c₀ c₁ i α β γ hαagree hβagree hγagree
    have hRzero := subspaceDesignMcaFour_eval_eq_zero_of_kernel_finrank_eq_zero
      (subspaceDesignMcaFour_residualSpan T U c₀ c₁) i R hRmem hReval hk
    have hrel :
        (β - γ) • U α + (γ - α) • U β + (α - β) • U γ = 0 := by
      rw [← subspaceDesignMcaFour_residual_affine_relation U c₀ c₁ α β γ]
      exact hRzero
    exact subspaceDesignMcaFour_interpolation_of_affine_relation
      U α β γ hαβ hrel
  have hsubset : A ⊆ T.filter (fun γ =>
      U γ = subspaceDesignMcaFour_interpolationIntercept U α β +
        γ • subspaceDesignMcaFour_interpolationSlope U α β) := by
    intro γ hγ
    exact Finset.mem_filter.mpr
      ⟨(Finset.mem_filter.mp hγ).1, halign γ hγ⟩
  have hoccupancy := hno8
    (subspaceDesignMcaFour_interpolationIntercept U α β) hc₀
    (subspaceDesignMcaFour_interpolationSlope U α β) hc₁
  have hcard : A.card ≤
      (T.filter (fun γ =>
        U γ = subspaceDesignMcaFour_interpolationIntercept U α β +
          γ • subspaceDesignMcaFour_interpolationSlope U α β)).card :=
    Finset.card_le_card hsubset
  omega

theorem subspaceDesignMcaFour_agreement_count_le_seven_add_kernel
    {ι : Type} {F : Type} [Field F] [DecidableEq F] {s : ℕ}
    [FiniteDimensional F (ι → Fin s → F)]
    (C : Submodule F (ι → Fin s → F)) (T : Finset F)
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (c₀ c₁ : ι → Fin s → F) (i : ι)
    (hTcard : T.card = 256)
    (hU : ∀ γ ∈ T, U γ ∈ C)
    (hno8 : subspaceDesignMcaFour_noEightAligned C T U) :
    subspaceDesignMcaFour_agreementCount f₀ f₁ U T i ≤
      7 + 249 * Module.finrank F
        (subspaceDesignMcaFour_coordinateKernel
          (subspaceDesignMcaFour_residualSpan T U c₀ c₁) i) := by
  by_cases hk :
      Module.finrank F (subspaceDesignMcaFour_coordinateKernel
        (subspaceDesignMcaFour_residualSpan T U c₀ c₁) i) = 0
  · have hm := subspaceDesignMcaFour_agreement_count_le_seven_of_kernel_zero
      C T f₀ f₁ U c₀ c₁ i hU hno8 hk
    omega
  · have hkpos : 1 ≤ Module.finrank F
        (subspaceDesignMcaFour_coordinateKernel
          (subspaceDesignMcaFour_residualSpan T U c₀ c₁) i) := by omega
    have hcount :
        subspaceDesignMcaFour_agreementCount f₀ f₁ U T i ≤ 256 := by
      unfold subspaceDesignMcaFour_agreementCount
      exact (Finset.card_filter_le _ _).trans (by omega)
    omega

theorem subspaceDesignMcaFour_sum_agreement_le
    {ι : Type} {F : Type} [Field F] [DecidableEq F] {s : ℕ}
    [Fintype ι] [FiniteDimensional F (ι → Fin s → F)]
    (C : Submodule F (ι → Fin s → F)) (T : Finset F)
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (c₀ c₁ : ι → Fin s → F)
    (hTcard : T.card = 256)
    (hU : ∀ γ ∈ T, U γ ∈ C)
    (hno8 : subspaceDesignMcaFour_noEightAligned C T U) :
    (∑ i : ι,
      (subspaceDesignMcaFour_agreementCount f₀ f₁ U T i : ℝ)) ≤
      7 * Fintype.card ι +
        249 * ∑ i : ι, (Module.finrank F
          (subspaceDesignMcaFour_coordinateKernel
            (subspaceDesignMcaFour_residualSpan T U c₀ c₁) i) : ℝ) := by
  calc
    (∑ i : ι,
      (subspaceDesignMcaFour_agreementCount f₀ f₁ U T i : ℝ)) ≤
      ∑ i : ι, (7 + 249 * Module.finrank F
        (subspaceDesignMcaFour_coordinateKernel
          (subspaceDesignMcaFour_residualSpan T U c₀ c₁) i) : ℝ) := by
        apply Finset.sum_le_sum
        intro i hi
        exact_mod_cast subspaceDesignMcaFour_agreement_count_le_seven_add_kernel
          C T f₀ f₁ U c₀ c₁ i hTcard hU hno8
    _ = 7 * Fintype.card ι + 249 * ∑ i : ι,
        (Module.finrank F
          (subspaceDesignMcaFour_coordinateKernel
            (subspaceDesignMcaFour_residualSpan T U c₀ c₁) i) : ℝ) := by
          simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
            nsmul_eq_mul]
          rw [← Finset.mul_sum]
          ring_nf

theorem subspaceDesignMcaFour_residualSpan_le_code
    {ι : Type} {F : Type} [Field F] [DecidableEq F] {s : ℕ}
    (C : Submodule F (ι → Fin s → F)) (T : Finset F)
    (U : F → ι → Fin s → F) (c₀ c₁ : ι → Fin s → F)
    (hU : ∀ γ ∈ T, U γ ∈ C) (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C) :
    subspaceDesignMcaFour_residualSpan T U c₀ c₁ ≤ C := by
  rw [subspaceDesignMcaFour_residualSpan, Submodule.span_le]
  rintro v ⟨γ, hγ, rfl⟩
  exact C.sub_mem (hU γ hγ) (C.add_mem hc₀ (C.smul_mem γ hc₁))

theorem subspaceDesignMcaFour_coordinate_kernel_sum_le_design
    {ι : Type} {F : Type} [Field F] [Fintype ι] [Nonempty ι]
    [DecidableEq F] {s D : ℕ}
    (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C) (T : Finset F)
    (U : F → ι → Fin s → F) (c₀ c₁ : ι → Fin s → F)
    (hU : ∀ γ ∈ T, U γ ∈ C) (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C)
    (hτ : 0 ≤ τ 5)
    (hD : Module.finrank F
      (subspaceDesignMcaFour_residualSpan T U c₀ c₁) = D)
    (hDle : D ≤ 5) :
    (∑ i : ι, (Module.finrank F
      (subspaceDesignMcaFour_coordinateKernel
        (subspaceDesignMcaFour_residualSpan T U c₀ c₁) i) : ℝ)) ≤
      Fintype.card ι * (D : ℝ) * τ 5 := by
  let V := subspaceDesignMcaFour_residualSpan T U c₀ c₁
  have hVC : V ≤ C := by
    dsimp [V]
    exact subspaceDesignMcaFour_residualSpan_le_code C T U c₀ c₁ hU hc₀ hc₁
  have hdes := hdesign 5 V hVC (by rw [hD]; exact hDle)
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  rw [div_le_iff₀ hn] at hdes
  have hdim : (Module.finrank F V : ℝ) ≤ (D : ℝ) := by
    rw [hD]
  have hscaled := mul_le_mul_of_nonneg_right hdim hτ
  change (∑ i : ι, (Module.finrank F
      (subspaceDesignMcaFour_coordinateKernel V i) : ℝ)) ≤ _ at hdes
  have hsum : (∑ i : ι, (Module.finrank F
      (subspaceDesignMcaFour_coordinateKernel V i) : ℝ)) ≤
      (Module.finrank F V : ℝ) * τ 5 * Fintype.card ι := by
    simpa [subspaceDesignMcaFour_coordinateKernel,
      subspaceDesignMcaFour_evalMap] using hdes
  calc
    (∑ i : ι, (Module.finrank F
      (subspaceDesignMcaFour_coordinateKernel V i) : ℝ)) ≤
      (Module.finrank F V : ℝ) * τ 5 * Fintype.card ι := hsum
    _ ≤ (D : ℝ) * τ 5 * Fintype.card ι :=
      mul_le_mul_of_nonneg_right hscaled (Nat.cast_nonneg _)
    _ = Fintype.card ι * (D : ℝ) * τ 5 := by ring

theorem subspaceDesignMcaFour_low_rank_sum_agreement_upper
    {ι : Type} {F : Type} [Field F] [Fintype ι] [Nonempty ι]
    [DecidableEq F] {s D : ℕ} [FiniteDimensional F (ι → Fin s → F)]
    (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C) (T : Finset F)
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (c₀ c₁ : ι → Fin s → F)
    (hTcard : T.card = 256)
    (hU : ∀ γ ∈ T, U γ ∈ C)
    (hno8 : subspaceDesignMcaFour_noEightAligned C T U)
    (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C)
    (hτ : 0 ≤ τ 5)
    (hD : Module.finrank F
      (subspaceDesignMcaFour_residualSpan T U c₀ c₁) = D)
    (hDle : D ≤ 5) :
    (∑ i : ι,
      (subspaceDesignMcaFour_agreementCount f₀ f₁ U T i : ℝ)) ≤
      ((7 : ℝ) + 249 * (D : ℝ) * τ 5) * Fintype.card ι := by
  have hcount := subspaceDesignMcaFour_sum_agreement_le
    C T f₀ f₁ U c₀ c₁ hTcard hU hno8
  have hkernel := subspaceDesignMcaFour_coordinate_kernel_sum_le_design
    τ C hdesign T U c₀ c₁ hU hc₀ hc₁ hτ hD hDle
  calc
    (∑ i : ι,
      (subspaceDesignMcaFour_agreementCount f₀ f₁ U T i : ℝ)) ≤
      7 * Fintype.card ι +
        249 * ∑ i : ι, (Module.finrank F
          (subspaceDesignMcaFour_coordinateKernel
            (subspaceDesignMcaFour_residualSpan T U c₀ c₁) i) : ℝ) := hcount
    _ ≤ 7 * Fintype.card ι +
        249 * (Fintype.card ι * (D : ℝ) * τ 5) := by
      gcongr
    _ = ((7 : ℝ) + 249 * (D : ℝ) * τ 5) * Fintype.card ι := by ring

theorem subspaceDesignMcaFour_sum_agreement_lower_of_close
    {ι : Type} {F : Type} [Field F] [Fintype ι] [Nonempty ι]
    [DecidableEq F] {s : ℕ}
    (T : Finset F) (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (δ τ₅ : ℝ) (hTcard : T.card = 256)
    (hδ : δ = 5 / 8 - τ₅)
    (hclose : ∀ γ ∈ T,
      (Code.relHammingDist (f₀ + γ • f₁) (U γ) : ℝ) ≤ δ) :
    256 * (τ₅ + 3 / 8) * Fintype.card ι ≤
      ∑ i : ι,
        (subspaceDesignMcaFour_agreementCount f₀ f₁ U T i : ℝ) := by
  have hlower := lineClose_sum_agreement_lower f₀ f₁ U δ T hclose
  rw [hTcard] at hlower
  have hidentity : 1 - δ = τ₅ + 3 / 8 := by rw [hδ]; ring
  rw [hidentity] at hlower
  norm_num at hlower
  simpa [subspaceDesignMcaFour_agreementCount, mul_comm, mul_left_comm,
    mul_assoc] using hlower

theorem subspaceDesignMcaFour_seed_disagreement_sum_le
    {ι : Type} {F : Type} [Field F] [Fintype ι] [Nonempty ι]
    [DecidableEq F] {s : ℕ}
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (δ : ℝ) (γ : F)
    (hclose : (Code.relHammingDist (f₀ + γ • f₁) (U γ) : ℝ) ≤ δ) :
    (∑ i : ι,
      (if U γ i = f₀ i + γ • f₁ i then (0 : ℝ) else 1)) ≤
      δ * Fintype.card ι := by
  have hlower := lineClose_sum_agreement_lower f₀ f₁ U δ ({γ} : Finset F)
    (by
      intro β hβ
      have : β = γ := by simpa using hβ
      subst β
      exact hclose)
  have hagree :
      Fintype.card ι * (1 - δ) ≤
        ∑ i : ι, (if U γ i = f₀ i + γ • f₁ i then (1 : ℝ) else 0) := by
    have hsum :
        (∑ i : ι,
          ((lineAgreementSeeds f₀ f₁ U ({γ} : Finset F) i).card : ℝ)) =
          ∑ i : ι, (if U γ i = f₀ i + γ • f₁ i then (1 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [lineAgreementSeeds, Finset.filter_singleton]
      split_ifs <;> simp
    rw [hsum] at hlower
    simpa [mul_comm, mul_left_comm, mul_assoc] using hlower
  have hpartition :
      (∑ i : ι,
        (if U γ i = f₀ i + γ • f₁ i then (0 : ℝ) else 1)) +
      (∑ i : ι,
        (if U γ i = f₀ i + γ • f₁ i then (1 : ℝ) else 0)) =
      Fintype.card ι := by
    calc
      _ = ∑ i : ι,
          ((if U γ i = f₀ i + γ • f₁ i then (0 : ℝ) else 1) +
            (if U γ i = f₀ i + γ • f₁ i then (1 : ℝ) else 0)) := by
              rw [Finset.sum_add_distrib]
      _ = ∑ _i : ι, (1 : ℝ) := by
            apply Finset.sum_congr rfl
            intro i _
            split_ifs <;> norm_num
      _ = Fintype.card ι := by simp
  linarith

theorem subspaceDesignMcaFour_four_seed_disagreement_sum_le
    {ι : Type} {F : Type} [Field F] [Fintype ι] [Nonempty ι]
    [DecidableEq F] {s : ℕ}
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (δ : ℝ) (α₀ α₁ α₂ α₃ : F)
    (hclose₀ : (Code.relHammingDist (f₀ + α₀ • f₁) (U α₀) : ℝ) ≤ δ)
    (hclose₁ : (Code.relHammingDist (f₀ + α₁ • f₁) (U α₁) : ℝ) ≤ δ)
    (hclose₂ : (Code.relHammingDist (f₀ + α₂ • f₁) (U α₂) : ℝ) ≤ δ)
    (hclose₃ : (Code.relHammingDist (f₀ + α₃ • f₁) (U α₃) : ℝ) ≤ δ) :
    (∑ i : ι,
      (subspaceDesignMcaFour_fourSeedDisagreementCount
        f₀ f₁ U α₀ α₁ α₂ α₃ i : ℝ)) ≤
      4 * δ * Fintype.card ι := by
  have hb₀ := subspaceDesignMcaFour_seed_disagreement_sum_le
    f₀ f₁ U δ α₀ hclose₀
  have hb₁ := subspaceDesignMcaFour_seed_disagreement_sum_le
    f₀ f₁ U δ α₁ hclose₁
  have hb₂ := subspaceDesignMcaFour_seed_disagreement_sum_le
    f₀ f₁ U δ α₂ hclose₂
  have hb₃ := subspaceDesignMcaFour_seed_disagreement_sum_le
    f₀ f₁ U δ α₃ hclose₃
  have hsum :
      (∑ i : ι,
        (subspaceDesignMcaFour_fourSeedDisagreementCount
          f₀ f₁ U α₀ α₁ α₂ α₃ i : ℝ)) =
      (∑ i : ι, (if U α₀ i = f₀ i + α₀ • f₁ i then (0 : ℝ) else 1)) +
      (∑ i : ι, (if U α₁ i = f₀ i + α₁ • f₁ i then (0 : ℝ) else 1)) +
      (∑ i : ι, (if U α₂ i = f₀ i + α₂ • f₁ i then (0 : ℝ) else 1)) +
      (∑ i : ι, (if U α₃ i = f₀ i + α₃ • f₁ i then (0 : ℝ) else 1)) := by
    simp [subspaceDesignMcaFour_fourSeedDisagreementCount,
      Finset.sum_add_distrib]
  rw [hsum]
  have h01 := add_le_add hb₀ hb₁
  have h23 := add_le_add hb₂ hb₃
  nlinarith

theorem subspaceDesignMcaFour_rank_two_high_profile_contradiction
    {ι : Type} {F : Type} [Field F] [Fintype ι] [Nonempty ι]
    [DecidableEq F] {s : ℕ} [FiniteDimensional F (ι → Fin s → F)]
    (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C) (T : Finset F)
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (c₀ c₁ : ι → Fin s → F) (δ : ℝ)
    (hU : ∀ γ ∈ T, U γ ∈ C)
    (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C)
    (hτ : 0 ≤ τ 5)
    (hD : Module.finrank F
      (subspaceDesignMcaFour_residualSpan T U c₀ c₁) = 2)
    (hδ : δ = 5 / 8 - τ 5)
    (hclose : ∀ γ ∈ T,
      (Code.relHammingDist (f₀ + γ • f₁) (U γ) : ℝ) ≤ δ)
    (α₀ α₁ : F) (hα₀ : α₀ ∈ T) (hα₁ : α₁ ∈ T)
    (hα₀α₁ : α₀ ≠ α₁)
    (hres₀ : subspaceDesignMcaFour_residual U c₀ c₁ α₀ = 0)
    (hres₁ : subspaceDesignMcaFour_residual U c₀ c₁ α₁ = 0)
    (hprofile : 1 / 4 < τ 5) : False := by
  obtain ⟨α₂, hα₂, α₃, hα₃, _, _, hdistinct₀₁, hdistinct₀₂, _,
      hdistinct₁₂, _, _, hli⟩ :=
    subspaceDesignMcaFour_exists_four_seed_configuration
      T U c₀ c₁ α₀ α₁ hα₀ hα₁ hα₀α₁ hres₀ hres₁ hD
  let V := subspaceDesignMcaFour_residualSpan T U c₀ c₁
  have hv₂ : subspaceDesignMcaFour_residual U c₀ c₁ α₂ ∈ V := by
    change subspaceDesignMcaFour_residual U c₀ c₁ α₂ ∈
      Submodule.span F
        (subspaceDesignMcaFour_residual U c₀ c₁ '' (T : Set F))
    exact Submodule.subset_span ⟨α₂, hα₂, rfl⟩
  have hv₃ : subspaceDesignMcaFour_residual U c₀ c₁ α₃ ∈ V := by
    change subspaceDesignMcaFour_residual U c₀ c₁ α₃ ∈
      Submodule.span F
        (subspaceDesignMcaFour_residual U c₀ c₁ '' (T : Set F))
    exact Submodule.subset_span ⟨α₃, hα₃, rfl⟩
  have hpoint (i : ι) :
      2 ≤ subspaceDesignMcaFour_fourSeedDisagreementCount
          f₀ f₁ U α₀ α₁ α₂ α₃ i +
        Module.finrank F (subspaceDesignMcaFour_coordinateKernel V i) :=
    subspaceDesignMcaFour_four_seed_disagreement_kernel_lower
      f₀ f₁ U c₀ c₁ V α₀ α₁ α₂ α₃
      hdistinct₀₁ hdistinct₀₂ hdistinct₁₂ hres₀ hres₁ hv₂ hv₃ hli i
  have hsumlower := subspaceDesignMcaFour_sum_pointwise_disagreement_kernel_lower
    (fun i => subspaceDesignMcaFour_fourSeedDisagreementCount
      f₀ f₁ U α₀ α₁ α₂ α₃ i)
    (fun i => Module.finrank F
      (subspaceDesignMcaFour_coordinateKernel V i)) hpoint
  have hmismatch := subspaceDesignMcaFour_four_seed_disagreement_sum_le
    f₀ f₁ U δ α₀ α₁ α₂ α₃
    (hclose α₀ hα₀) (hclose α₁ hα₁) (hclose α₂ hα₂) (hclose α₃ hα₃)
  have hkernel := subspaceDesignMcaFour_coordinate_kernel_sum_le_design
    τ C hdesign T U c₀ c₁ hU hc₀ hc₁ hτ hD (by omega)
  have hcombined :
      (2 : ℝ) * Fintype.card ι ≤
        (4 * δ * Fintype.card ι) +
          (Fintype.card ι * 2 * τ 5) := by
    calc
      (2 : ℝ) * Fintype.card ι ≤
          (∑ i : ι,
            (subspaceDesignMcaFour_fourSeedDisagreementCount
              f₀ f₁ U α₀ α₁ α₂ α₃ i : ℝ)) +
          (∑ i : ι, (Module.finrank F
            (subspaceDesignMcaFour_coordinateKernel V i) : ℝ)) := hsumlower
      _ ≤ (4 * δ * Fintype.card ι) +
          (Fintype.card ι * 2 * τ 5) :=
        add_le_add hmismatch (by simpa [V] using hkernel)
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hstrict : 4 * δ + 2 * τ 5 < 2 := by
    rw [hδ]
    nlinarith
  nlinarith [hcombined, hn, hstrict]

theorem subspaceDesignMcaFour_low_rank_contradiction
    {ι : Type} {F : Type} [Field F] [Fintype ι] [Nonempty ι]
    [DecidableEq F] {s D : ℕ} [FiniteDimensional F (ι → Fin s → F)]
    (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C) (T : Finset F)
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (c₀ c₁ : ι → Fin s → F) (δ : ℝ)
    (hTcard : T.card = 256)
    (hU : ∀ γ ∈ T, U γ ∈ C)
    (hno8 : subspaceDesignMcaFour_noEightAligned C T U)
    (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C)
    (hτ : 0 ≤ τ 5)
    (hD : Module.finrank F
      (subspaceDesignMcaFour_residualSpan T U c₀ c₁) = D)
    (hDle : D ≤ 5)
    (hδ : δ = 5 / 8 - τ 5)
    (hclose : ∀ γ ∈ T,
      (Code.relHammingDist (f₀ + γ • f₁) (U γ) : ℝ) ≤ δ)
    (hthreshold : 96 > 7 + (249 * (D : ℝ) - 256) * τ 5) :
    False := by
  have hupper := subspaceDesignMcaFour_low_rank_sum_agreement_upper
    τ C hdesign T f₀ f₁ U c₀ c₁ hTcard hU hno8 hc₀ hc₁ hτ hD hDle
  have hlower := subspaceDesignMcaFour_sum_agreement_lower_of_close
    T f₀ f₁ U δ (τ 5) hTcard hδ hclose
  have hcombined :
      256 * (τ 5 + 3 / 8) * Fintype.card ι ≤
        ((7 : ℝ) + 249 * (D : ℝ) * τ 5) * Fintype.card ι :=
    hlower.trans hupper
  have hfactor :
      0 < 256 * (τ 5 + 3 / 8) -
        ((7 : ℝ) + 249 * (D : ℝ) * τ 5) := by
    have hid :
        256 * (τ 5 + 3 / 8) -
          ((7 : ℝ) + 249 * (D : ℝ) * τ 5) =
        96 - (7 + (249 * (D : ℝ) - 256) * τ 5) := by ring
    rw [hid]
    linarith
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hpositive := mul_pos hfactor hn
  linarith

theorem subspaceDesignMcaFour_rank_two_no_eight_contradiction
    {s : ℕ} {ι : Type} {F : Type} [Field F] [Fintype ι] [Nonempty ι]
    [DecidableEq F] [FiniteDimensional F (ι → Fin s → F)]
    (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C) (T : Finset F)
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (c₀ c₁ : ι → Fin s → F) (δ : ℝ)
    (hTcard : T.card = 256)
    (hU : ∀ γ ∈ T, U γ ∈ C)
    (hno8 : subspaceDesignMcaFour_noEightAligned C T U)
    (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C)
    (hτ : 0 ≤ τ 5)
    (hD : Module.finrank F
      (subspaceDesignMcaFour_residualSpan T U c₀ c₁) = 2)
    (hδ : δ = 5 / 8 - τ 5)
    (hclose : ∀ γ ∈ T,
      (Code.relHammingDist (f₀ + γ • f₁) (U γ) : ℝ) ≤ δ)
    (α₀ α₁ : F) (hα₀ : α₀ ∈ T) (hα₁ : α₁ ∈ T)
    (hα₀α₁ : α₀ ≠ α₁)
    (hres₀ : subspaceDesignMcaFour_residual U c₀ c₁ α₀ = 0)
    (hres₁ : subspaceDesignMcaFour_residual U c₀ c₁ α₁ = 0) :
    False := by
  by_cases hlow : τ 5 < 89 / 242
  · apply subspaceDesignMcaFour_low_rank_contradiction τ C hdesign T
      f₀ f₁ U c₀ c₁ δ hTcard hU hno8 hc₀ hc₁ hτ hD (by omega)
      hδ hclose
    norm_num
    nlinarith [hlow]
  · have hhigh : 1 / 4 < τ 5 := by
      have hcut : (1 / 4 : ℝ) < 89 / 242 := by norm_num
      exact lt_of_lt_of_le hcut (le_of_not_gt hlow)
    exact subspaceDesignMcaFour_rank_two_high_profile_contradiction
      τ C hdesign T f₀ f₁ U c₀ c₁ δ hU hc₀ hc₁ hτ hD hδ hclose
      α₀ α₁ hα₀ hα₁ hα₀α₁ hres₀ hres₁ hhigh

theorem subspaceDesignMcaFour_low_rank_forces_high_threshold
    {ι : Type} {F : Type} [Field F] [Fintype ι] [Nonempty ι]
    [DecidableEq F] {s D : ℕ} [FiniteDimensional F (ι → Fin s → F)]
    (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C) (T : Finset F)
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (c₀ c₁ : ι → Fin s → F) (δ L H : ℝ)
    (hTcard : T.card = 256)
    (hU : ∀ γ ∈ T, U γ ∈ C)
    (hno8 : subspaceDesignMcaFour_noEightAligned C T U)
    (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C)
    (hτ : 0 ≤ τ 5)
    (hD : Module.finrank F
      (subspaceDesignMcaFour_residualSpan T U c₀ c₁) = D)
    (hDle : D ≤ 5)
    (hδ : δ = 5 / 8 - τ 5)
    (hclose : ∀ γ ∈ T,
      (Code.relHammingDist (f₀ + γ • f₁) (U γ) : ℝ) ≤ δ)
    (hthreshold : ∀ x, x < L →
      96 > 7 + (249 * (D : ℝ) - 256) * x)
    (hhigh_lt_low : H < L) :
    H < τ 5 := by
  by_cases hlow : τ 5 < L
  · exfalso
    exact subspaceDesignMcaFour_low_rank_contradiction τ C hdesign T
      f₀ f₁ U c₀ c₁ δ hTcard hU hno8 hc₀ hc₁ hτ hD hDle hδ hclose
      (hthreshold (τ 5) hlow)
  · exact lt_of_lt_of_le hhigh_lt_low (le_of_not_gt hlow)

theorem subspaceDesignMcaFour_low_rank_one_contradiction
    {ι : Type} {F : Type} [Field F] [Fintype ι] [Nonempty ι]
    [DecidableEq F] {s : ℕ} [FiniteDimensional F (ι → Fin s → F)]
    (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C) (hCne : C ≠ ⊥)
    (T : Finset F) (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (c₀ c₁ : ι → Fin s → F) (δ : ℝ)
    (hTcard : T.card = 256)
    (hU : ∀ γ ∈ T, U γ ∈ C)
    (hno8 : subspaceDesignMcaFour_noEightAligned C T U)
    (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C)
    (hD : Module.finrank F
      (subspaceDesignMcaFour_residualSpan T U c₀ c₁) = 1)
    (hδ : δ = 5 / 8 - τ 5)
    (hτupper : τ 5 ≤ 5 / 8)
    (hclose : ∀ γ ∈ T,
      (Code.relHammingDist (f₀ + γ • f₁) (U γ) : ℝ) ≤ δ) :
    False := by
  have hτnonneg : 0 ≤ τ 5 := hdesign.profile_nonneg hCne (by norm_num)
  have hradius := subspaceDesignMcaFour_radius_bounds (τ 5) hτnonneg hτupper
  have hδnonneg : 0 ≤ δ := by rw [hδ]; exact hradius.1
  have hδlt : δ < 1 := by rw [hδ]; exact hradius.2
  have hthreshold : 96 > 7 + (249 * (1 : ℝ) - 256) * τ 5 := by
    norm_num
    nlinarith
  exact subspaceDesignMcaFour_low_rank_contradiction
    τ C hdesign T f₀ f₁ U c₀ c₁ δ hTcard hU hno8 hc₀ hc₁
    hτnonneg hD (by omega) hδ hclose hthreshold

theorem subspaceDesignMcaFour_residualSpan_bot_of_finrank_eq_zero
    {ι : Type} {F : Type} [Field F] [Fintype F] {s : ℕ}
    [FiniteDimensional F (ι → Fin s → F)] [DecidableEq F]
    (T : Finset F) (U : F → ι → Fin s → F) (c₀ c₁ : ι → Fin s → F)
    (hD : Module.finrank F
      (subspaceDesignMcaFour_residualSpan T U c₀ c₁) = 0) :
    subspaceDesignMcaFour_residualSpan T U c₀ c₁ = ⊥ := by
  exact Submodule.finrank_eq_zero.mp hD

theorem subspaceDesignMcaFour_rank_zero_alignment
    {ι : Type} {F : Type} [Field F] [Fintype F] {s : ℕ}
    [FiniteDimensional F (ι → Fin s → F)] [DecidableEq F]
    (T : Finset F) (U : F → ι → Fin s → F) (c₀ c₁ : ι → Fin s → F)
    (hD : Module.finrank F
      (subspaceDesignMcaFour_residualSpan T U c₀ c₁) = 0) :
    ∀ γ ∈ T, U γ = c₀ + γ • c₁ := by
  have hV := subspaceDesignMcaFour_residualSpan_bot_of_finrank_eq_zero
    T U c₀ c₁ hD
  intro γ hγ
  have hv : subspaceDesignMcaFour_residual U c₀ c₁ γ ∈
      subspaceDesignMcaFour_residualSpan T U c₀ c₁ := by
    apply Submodule.subset_span
    exact ⟨γ, hγ, rfl⟩
  have hz : subspaceDesignMcaFour_residual U c₀ c₁ γ = 0 := by
    simpa [hV] using hv
  exact sub_eq_zero.mp hz

theorem subspaceDesignMcaFour_interpolated_rank_zero_alignment
    {ι : Type} {F : Type} [Field F] [Fintype F] [DecidableEq F] {s : ℕ}
    [FiniteDimensional F (ι → Fin s → F)]
    (C : Submodule F (ι → Fin s → F)) (T : Finset F)
    (U : F → ι → Fin s → F) (α β : F) (hαβ : α ≠ β)
    (hαT : α ∈ T) (hβT : β ∈ T)
    (hU : ∀ γ ∈ T, U γ ∈ C)
    (hD : Module.finrank F
      (subspaceDesignMcaFour_residualSpan T U
        (subspaceDesignMcaFour_interpolationIntercept U α β)
        (subspaceDesignMcaFour_interpolationSlope U α β)) = 0) :
    subspaceDesignMcaFour_interpolationIntercept U α β ∈ C ∧
      subspaceDesignMcaFour_interpolationSlope U α β ∈ C ∧
      subspaceDesignMcaFour_interpolationIntercept U α β +
        α • subspaceDesignMcaFour_interpolationSlope U α β = U α ∧
      subspaceDesignMcaFour_interpolationIntercept U α β +
        β • subspaceDesignMcaFour_interpolationSlope U α β = U β ∧
      (∀ γ ∈ T, U γ =
        subspaceDesignMcaFour_interpolationIntercept U α β +
          γ • subspaceDesignMcaFour_interpolationSlope U α β) := by
  have hc₀ := subspaceDesignMcaFour_interpolation_intercept_mem C U α β
    (hU α hαT) (hU β hβT)
  have hc₁ := subspaceDesignMcaFour_interpolation_slope_mem C U α β
    (hU α hαT) (hU β hβT)
  have halign := subspaceDesignMcaFour_rank_zero_alignment T U
    (subspaceDesignMcaFour_interpolationIntercept U α β)
    (subspaceDesignMcaFour_interpolationSlope U α β) hD
  exact ⟨hc₀, hc₁,
    subspaceDesignMcaFour_interpolation_at_left U α β,
    subspaceDesignMcaFour_interpolation_at_right U α β hαβ,
    halign⟩

theorem subspaceDesignMcaFour_rank_zero_contradicts_noEight
    {ι : Type} {F : Type} [Field F] [Fintype F] [DecidableEq F] {s : ℕ}
    [FiniteDimensional F (ι → Fin s → F)]
    (C : Submodule F (ι → Fin s → F)) (T : Finset F)
    (U : F → ι → Fin s → F) (c₀ c₁ : ι → Fin s → F)
    (hTcard : T.card = 256)
    (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C)
    (hno8 : subspaceDesignMcaFour_noEightAligned C T U)
    (hD : Module.finrank F
      (subspaceDesignMcaFour_residualSpan T U c₀ c₁) = 0) :
    False := by
  classical
  have halign := subspaceDesignMcaFour_rank_zero_alignment T U c₀ c₁ hD
  have hsubset : T ⊆ T.filter (fun γ => U γ = c₀ + γ • c₁) := by
    intro γ hγ
    exact Finset.mem_filter.mpr ⟨hγ, halign γ hγ⟩
  have hcard := Finset.card_le_card hsubset
  have hbound := hno8 c₀ hc₀ c₁ hc₁
  omega

theorem subspaceDesignMcaFour_exists_three_independent_residuals
    {ι : Type} {F : Type} [Field F] [DecidableEq F] {s : ℕ}
    [FiniteDimensional F (ι → Fin s → F)]
    (T : Finset F) (U : F → ι → Fin s → F) (c₀ c₁ : ι → Fin s → F)
    (hD : Module.finrank F
      (subspaceDesignMcaFour_residualSpan T U c₀ c₁) = 3) :
    ∃ α₂ ∈ T, ∃ α₃ ∈ T, ∃ α₄ ∈ T,
      LinearIndependent F ![
        subspaceDesignMcaFour_residual U c₀ c₁ α₂,
        subspaceDesignMcaFour_residual U c₀ c₁ α₃,
        subspaceDesignMcaFour_residual U c₀ c₁ α₄] := by
  classical
  let G : Set (ι → Fin s → F) :=
    subspaceDesignMcaFour_residual U c₀ c₁ '' (T : Set F)
  have hspan : Submodule.span F G =
      subspaceDesignMcaFour_residualSpan T U c₀ c₁ := rfl
  have hdim : Module.finrank F (Submodule.span F G) = 3 := by
    rw [hspan]
    exact hD
  obtain ⟨b, hb, _hbspan, hli₀⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq F G
  let e : Fin 3 → Fin (Module.finrank F (Submodule.span F G)) :=
    Fin.cast hdim.symm
  let v : Fin 3 → ι → Fin s → F := b ∘ e
  have hli : LinearIndependent F v :=
    hli₀.comp _ (Fin.cast_injective hdim.symm)
  have hv (j : Fin 3) : v j ∈ G := hb (e j)
  have hmem₂ : v 0 ∈ G := hv 0
  have hmem₃ : v 1 ∈ G := hv 1
  have hmem₄ : v 2 ∈ G := hv 2
  change ∃ α ∈ (T : Set F),
    subspaceDesignMcaFour_residual U c₀ c₁ α = v 0 at hmem₂
  change ∃ α ∈ (T : Set F),
    subspaceDesignMcaFour_residual U c₀ c₁ α = v 1 at hmem₃
  change ∃ α ∈ (T : Set F),
    subspaceDesignMcaFour_residual U c₀ c₁ α = v 2 at hmem₄
  obtain ⟨α₂, hα₂, hα₂eq⟩ := hmem₂
  obtain ⟨α₃, hα₃, hα₃eq⟩ := hmem₃
  obtain ⟨α₄, hα₄, hα₄eq⟩ := hmem₄
  have hfun : v = ![v 0, v 1, v 2] := by
    funext j
    fin_cases j <;> simp
  have hli' : LinearIndependent F ![v 0, v 1, v 2] := by
    rw [← hfun]
    exact hli
  refine ⟨α₂, hα₂, α₃, hα₃, α₄, hα₄, ?_⟩
  simpa [hα₂eq, hα₃eq, hα₄eq] using hli'

def subspaceDesignMcaFour_fiveSeedDisagreementCount
    {ι : Type} {F : Type} [Field F] [DecidableEq F] {s : ℕ}
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (α₀ α₁ α₂ α₃ α₄ : F) (i : ι) : ℕ :=
  (if U α₀ i = f₀ i + α₀ • f₁ i then 0 else 1) +
  (if U α₁ i = f₀ i + α₁ • f₁ i then 0 else 1) +
  (if U α₂ i = f₀ i + α₂ • f₁ i then 0 else 1) +
  (if U α₃ i = f₀ i + α₃ • f₁ i then 0 else 1) +
  (if U α₄ i = f₀ i + α₄ • f₁ i then 0 else 1)

theorem subspaceDesignMcaFour_coordinateKernel_finrank_ge_good_subset
    {ι : Type} {F : Type} [Field F] {s : ℕ}
    [FiniteDimensional F (ι → Fin s → F)]
    (V : Submodule F (ι → Fin s → F)) (i : ι)
    (v : Fin 3 → ι → Fin s → F) (J : Finset (Fin 3))
    (hv : ∀ j ∈ J, v j ∈ V)
    (hli : LinearIndependent F v)
    (S : Submodule F (Fin s → F)) (r : ℕ)
    (hS : Module.finrank F S ≤ r)
    (heval : ∀ j ∈ J, subspaceDesignMcaFour_evalMap i (v j) ∈ S) :
    J.card - r ≤ Module.finrank F
      (subspaceDesignMcaFour_coordinateKernel V i) := by
  classical
  let W := Submodule.span F (v '' (J : Set (Fin 3)))
  have hWleV : W ≤ V := by
    apply Submodule.span_le.mpr
    rintro x ⟨j, hj, rfl⟩
    exact hv j hj
  have hliJ : LinearIndependent F (fun j : J => v j.1) :=
    hli.comp _ (by
      intro a b hab
      exact Subtype.ext hab)
  let w : J → ↥W := fun j =>
    ⟨v j.1, Submodule.subset_span ⟨j.1, j.2, rfl⟩⟩
  have hwli : LinearIndependent F w := by
    apply LinearIndependent.of_comp W.subtype
    change LinearIndependent F (fun j : J => v j.1)
    exact hliJ
  have hJle : J.card ≤ Module.finrank F W := by
    simpa using hwli.fintype_card_le_finrank
  let ψ : ↥W →ₗ[F] (Fin s → F) :=
    (subspaceDesignMcaFour_evalMap i).comp W.subtype
  have hevalW : ∀ x, x ∈ W →
      subspaceDesignMcaFour_evalMap i x ∈ S := by
    intro x hx
    change x ∈ Submodule.span F (v '' (J : Set (Fin 3))) at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨j, hj, rfl⟩ := hx
        exact heval j hj
    | zero => exact S.zero_mem
    | add _ _ _ _ hx hy => exact S.add_mem hx hy
    | smul a _ _ hx => exact S.smul_mem a hx
  have hrange : LinearMap.range ψ ≤ S := by
    rintro y ⟨x, rfl⟩
    exact hevalW x.1 x.2
  have hrangeDim : Module.finrank F (LinearMap.range ψ) ≤ r :=
    (Submodule.finrank_mono hrange).trans hS
  have hnull := LinearMap.finrank_range_add_finrank_ker ψ
  have hkerLower : J.card - r ≤
      Module.finrank F (LinearMap.ker ψ) := by
    omega
  have hkerMap : (LinearMap.ker ψ).map W.subtype =
      W ⊓ LinearMap.ker (subspaceDesignMcaFour_evalMap i) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, ?_⟩
      exact LinearMap.mem_ker.mp (by simpa [ψ] using hy)
    · rintro ⟨hxW, hxEval⟩
      refine ⟨⟨x, hxW⟩, LinearMap.mem_ker.mpr ?_, rfl⟩
      exact LinearMap.mem_ker.mp hxEval
  have hkerDim :
      Module.finrank F (LinearMap.ker ψ) =
        Module.finrank F ↥(W ⊓
          LinearMap.ker (subspaceDesignMcaFour_evalMap i)) := by
    calc
      Module.finrank F (LinearMap.ker ψ) =
          Module.finrank F ((LinearMap.ker ψ).map W.subtype) :=
        (Submodule.finrank_map_subtype_eq W (LinearMap.ker ψ)).symm
      _ = Module.finrank F ↥(W ⊓
          LinearMap.ker (subspaceDesignMcaFour_evalMap i)) := by rw [hkerMap]
  have hkerLe : Module.finrank F ↥(W ⊓
        LinearMap.ker (subspaceDesignMcaFour_evalMap i)) ≤
      Module.finrank F (subspaceDesignMcaFour_coordinateKernel V i) :=
    Submodule.finrank_mono (inf_le_inf hWleV le_rfl)
  rw [hkerDim] at hkerLower
  exact hkerLower.trans hkerLe

theorem subspaceDesignMcaFour_five_seed_disagreement_kernel_lower
    {ι : Type} {F : Type} [Field F] [DecidableEq F] {s : ℕ}
    [FiniteDimensional F (ι → Fin s → F)]
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (c₀ c₁ : ι → Fin s → F)
    (V : Submodule F (ι → Fin s → F))
    (α₀ α₁ α₂ α₃ α₄ : F)
    (hα₀α₁ : α₀ ≠ α₁)
    (hres₀ : subspaceDesignMcaFour_residual U c₀ c₁ α₀ = 0)
    (hres₁ : subspaceDesignMcaFour_residual U c₀ c₁ α₁ = 0)
    (hv₂ : subspaceDesignMcaFour_residual U c₀ c₁ α₂ ∈ V)
    (hv₃ : subspaceDesignMcaFour_residual U c₀ c₁ α₃ ∈ V)
    (hv₄ : subspaceDesignMcaFour_residual U c₀ c₁ α₄ ∈ V)
    (hli : LinearIndependent F ![
      subspaceDesignMcaFour_residual U c₀ c₁ α₂,
      subspaceDesignMcaFour_residual U c₀ c₁ α₃,
      subspaceDesignMcaFour_residual U c₀ c₁ α₄])
    (i : ι) :
    3 ≤ subspaceDesignMcaFour_fiveSeedDisagreementCount
      f₀ f₁ U α₀ α₁ α₂ α₃ α₄ i +
      Module.finrank F (subspaceDesignMcaFour_coordinateKernel V i) := by
  classical
  let m := subspaceDesignMcaFour_fiveSeedDisagreementCount
    f₀ f₁ U α₀ α₁ α₂ α₃ α₄ i
  let d₀ := c₀ i - f₀ i
  let d₁ := c₁ i - f₁ i
  let r₂ := subspaceDesignMcaFour_residual U c₀ c₁ α₂
  let r₃ := subspaceDesignMcaFour_residual U c₀ c₁ α₃
  let r₄ := subspaceDesignMcaFour_residual U c₀ c₁ α₄
  let a : Fin 3 → F := ![α₂, α₃, α₄]
  let v : Fin 3 → ι → Fin s → F := ![r₂, r₃, r₄]
  let J : Finset (Fin 3) := Finset.univ.filter
    (fun j => U (a j) i = f₀ i + a j • f₁ i)
  have hU₀ : U α₀ = c₀ + α₀ • c₁ := sub_eq_zero.mp hres₀
  have hU₁ : U α₁ = c₀ + α₁ • c₁ := sub_eq_zero.mp hres₁
  have hU₀i : U α₀ i = c₀ i + α₀ • c₁ i := congrArg (fun x => x i) hU₀
  have hU₁i : U α₁ i = c₀ i + α₁ • c₁ i := congrArg (fun x => x i) hU₁
  have hres_eval (γ : F) (hgood : U γ i = f₀ i + γ • f₁ i) :
      subspaceDesignMcaFour_evalMap i
          (subspaceDesignMcaFour_residual U c₀ c₁ γ) =
        -(d₀ + γ • d₁) := by
    ext j
    simp [subspaceDesignMcaFour_evalMap, subspaceDesignMcaFour_residual,
      LinearMap.proj_apply, d₀, d₁, Pi.sub_apply, Pi.smul_apply, hgood]
    ring
  have hroot_of_good (γ : F) (hres :
      subspaceDesignMcaFour_residual U c₀ c₁ γ = 0)
      (hgood : U γ i = f₀ i + γ • f₁ i) :
      d₀ + γ • d₁ = 0 := by
    have heval := hres_eval γ hgood
    rw [hres] at heval
    have hneg : -(d₀ + γ • d₁) = 0 := by
      simpa [subspaceDesignMcaFour_evalMap] using heval.symm
    exact neg_eq_zero.mp hneg
  have hline_roots (hgood₀ : U α₀ i = f₀ i + α₀ • f₁ i)
      (hgood₁ : U α₁ i = f₀ i + α₁ • f₁ i) :
      ∀ γ : F, c₀ i + γ • c₁ i = f₀ i + γ • f₁ i := by
    apply subspaceDesignMcaFour_affine_values_eq_of_two_roots
      α₀ α₁ hα₀α₁ (c₀ i) (c₁ i) (f₀ i) (f₁ i)
    · calc
        c₀ i + α₀ • c₁ i = U α₀ i := hU₀i.symm
        _ = f₀ i + α₀ • f₁ i := hgood₀
    · calc
        c₀ i + α₁ • c₁ i = U α₁ i := hU₁i.symm
        _ = f₀ i + α₁ • f₁ i := hgood₁
  have heval_zero (γ : F) (hgood :
      U γ i = f₀ i + γ • f₁ i)
      (hline : c₀ i + γ • c₁ i = f₀ i + γ • f₁ i) :
      subspaceDesignMcaFour_evalMap i
        (subspaceDesignMcaFour_residual U c₀ c₁ γ) = 0 := by
    rw [hres_eval γ hgood]
    have hd : d₀ + γ • d₁ = 0 := by
      change (c₀ i - f₀ i) + γ • (c₁ i - f₁ i) = 0
      calc
        _ = (c₀ i + γ • c₁ i) - (f₀ i + γ • f₁ i) := by module
        _ = 0 := by rw [hline]; simp
    rw [hd]
    simp
  have hJcard :
      J.card +
        (if U α₂ i = f₀ i + α₂ • f₁ i then 0 else 1) +
        (if U α₃ i = f₀ i + α₃ • f₁ i then 0 else 1) +
        (if U α₄ i = f₀ i + α₄ • f₁ i then 0 else 1) = 3 := by
    have hUniv : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by
      ext j
      simp
      omega
    dsimp [J]
    rw [hUniv]
    simp [a, Finset.filter_insert, Finset.filter_singleton]
    split_ifs <;> simp_all
  have hv : ∀ j, v j ∈ V := by
    intro j
    fin_cases j
    · simpa [v, r₂] using hv₂
    · simpa [v, r₃] using hv₃
    · simpa [v, r₄] using hv₄
  have hli_v : LinearIndependent F v := by
    simpa [v, r₂, r₃, r₄] using hli
  have hJmem (j : Fin 3) (hj : j ∈ J) :
      U (a j) i = f₀ i + a j • f₁ i :=
    (Finset.mem_filter.mp hj).2
  let g₁ : Fin 1 → Fin s → F := fun _ => d₁
  let S₁ : Submodule F (Fin s → F) := Submodule.span F (Set.range g₁)
  have hS₁ : Module.finrank F S₁ ≤ 1 := by
    calc
      Module.finrank F S₁ ≤ (Set.range g₁).toFinset.card :=
        finrank_span_le_card _
      _ ≤ Fintype.card (Fin 1) := by
        rw [Set.toFinset_range]
        exact Finset.card_image_le
      _ = 1 := by simp
  have hd₁S : d₁ ∈ S₁ := Submodule.subset_span ⟨0, rfl⟩
  let g₂ : Fin 2 → Fin s → F := ![d₀, d₁]
  let S₂ : Submodule F (Fin s → F) := Submodule.span F (Set.range g₂)
  have hS₂ : Module.finrank F S₂ ≤ 2 := by
    calc
      Module.finrank F S₂ ≤ (Set.range g₂).toFinset.card :=
        finrank_span_le_card _
      _ ≤ Fintype.card (Fin 2) := by
        rw [Set.toFinset_range]
        exact Finset.card_image_le
      _ = 2 := by simp
  have hd₀S : d₀ ∈ S₂ := Submodule.subset_span ⟨0, by simp [g₂]⟩
  have hd₁S₂ : d₁ ∈ S₂ := Submodule.subset_span ⟨1, by simp [g₂]⟩
  have hJzero (hgood₀ : U α₀ i = f₀ i + α₀ • f₁ i)
      (hgood₁ : U α₁ i = f₀ i + α₁ • f₁ i) :
      ∀ j ∈ J, subspaceDesignMcaFour_evalMap i (v j) = 0 := by
    intro j hj
    have hgood := hJmem j hj
    fin_cases j
    · have hgood₂ : U α₂ i = f₀ i + α₂ • f₁ i := by
        simpa [a] using hgood
      have hz := heval_zero α₂ hgood₂ (hline_roots hgood₀ hgood₁ α₂)
      simpa [v, r₂] using hz
    · have hgood₃ : U α₃ i = f₀ i + α₃ • f₁ i := by
        simpa [a] using hgood
      have hz := heval_zero α₃ hgood₃ (hline_roots hgood₀ hgood₁ α₃)
      simpa [v, r₃] using hz
    · have hgood₄ : U α₄ i = f₀ i + α₄ • f₁ i := by
        simpa [a] using hgood
      have hz := heval_zero α₄ hgood₄ (hline_roots hgood₀ hgood₁ α₄)
      simpa [v, r₄] using hz
  have hlineform (α γ : F) (hroot : d₀ + α • d₁ = 0) :
      d₀ + γ • d₁ = (γ - α) • d₁ := by
    calc
      d₀ + γ • d₁ =
          (d₀ + α • d₁) + (γ - α) • d₁ := by module
      _ = (γ - α) • d₁ := by rw [hroot]; simp
  have hJspan_one_anchor (α : F) (hroot : d₀ + α • d₁ = 0) :
      ∀ j ∈ J, subspaceDesignMcaFour_evalMap i (v j) ∈ S₁ := by
    intro j hj
    have hgood := hJmem j hj
    fin_cases j
    · have hgood₂ : U α₂ i = f₀ i + α₂ • f₁ i := by
        simpa [a] using hgood
      have hform := hlineform α α₂ hroot
      have heval := hres_eval α₂ hgood₂
      change subspaceDesignMcaFour_evalMap i r₂ ∈ S₁
      rw [heval, hform]
      exact S₁.neg_mem (S₁.smul_mem (α₂ - α) hd₁S)
    · have hgood₃ : U α₃ i = f₀ i + α₃ • f₁ i := by
        simpa [a] using hgood
      have hform := hlineform α α₃ hroot
      have heval := hres_eval α₃ hgood₃
      change subspaceDesignMcaFour_evalMap i r₃ ∈ S₁
      rw [heval, hform]
      exact S₁.neg_mem (S₁.smul_mem (α₃ - α) hd₁S)
    · have hgood₄ : U α₄ i = f₀ i + α₄ • f₁ i := by
        simpa [a] using hgood
      have hform := hlineform α α₄ hroot
      have heval := hres_eval α₄ hgood₄
      change subspaceDesignMcaFour_evalMap i r₄ ∈ S₁
      rw [heval, hform]
      exact S₁.neg_mem (S₁.smul_mem (α₄ - α) hd₁S)
  have hJspan_no_anchor :
      ∀ j ∈ J, subspaceDesignMcaFour_evalMap i (v j) ∈ S₂ := by
    intro j hj
    have hgood := hJmem j hj
    fin_cases j
    · have hgood₂ : U α₂ i = f₀ i + α₂ • f₁ i := by
        simpa [a] using hgood
      have heval := hres_eval α₂ hgood₂
      change subspaceDesignMcaFour_evalMap i r₂ ∈ S₂
      rw [heval]
      exact S₂.neg_mem (S₂.add_mem hd₀S (S₂.smul_mem α₂ hd₁S₂))
    · have hgood₃ : U α₃ i = f₀ i + α₃ • f₁ i := by
        simpa [a] using hgood
      have heval := hres_eval α₃ hgood₃
      change subspaceDesignMcaFour_evalMap i r₃ ∈ S₂
      rw [heval]
      exact S₂.neg_mem (S₂.add_mem hd₀S (S₂.smul_mem α₃ hd₁S₂))
    · have hgood₄ : U α₄ i = f₀ i + α₄ • f₁ i := by
        simpa [a] using hgood
      have heval := hres_eval α₄ hgood₄
      change subspaceDesignMcaFour_evalMap i r₄ ∈ S₂
      rw [heval]
      exact S₂.neg_mem (S₂.add_mem hd₀S (S₂.smul_mem α₄ hd₁S₂))
  by_cases hgood₀ : U α₀ i = f₀ i + α₀ • f₁ i
  · by_cases hgood₁ : U α₁ i = f₀ i + α₁ • f₁ i
    · have hkernel :=
        subspaceDesignMcaFour_coordinateKernel_finrank_ge_good_subset
          V i v J (fun j _ => hv j) hli_v ⊥ 0 (by simp)
          (hJzero hgood₀ hgood₁)
      have hm : m =
          (if U α₂ i = f₀ i + α₂ • f₁ i then 0 else 1) +
          (if U α₃ i = f₀ i + α₃ • f₁ i then 0 else 1) +
          (if U α₄ i = f₀ i + α₄ • f₁ i then 0 else 1) := by
        simp [m, subspaceDesignMcaFour_fiveSeedDisagreementCount, hgood₀, hgood₁]
      change 3 ≤ m + Module.finrank F
        (subspaceDesignMcaFour_coordinateKernel V i)
      omega
    · have hroot := hroot_of_good α₀ hres₀ hgood₀
      have hkernel :=
        subspaceDesignMcaFour_coordinateKernel_finrank_ge_good_subset
          V i v J (fun j _ => hv j) hli_v S₁ 1 hS₁
          (hJspan_one_anchor α₀ hroot)
      have hm : m = 1 +
          (if U α₂ i = f₀ i + α₂ • f₁ i then 0 else 1) +
          (if U α₃ i = f₀ i + α₃ • f₁ i then 0 else 1) +
          (if U α₄ i = f₀ i + α₄ • f₁ i then 0 else 1) := by
        simp [m, subspaceDesignMcaFour_fiveSeedDisagreementCount, hgood₀, hgood₁]
      change 3 ≤ m + Module.finrank F
        (subspaceDesignMcaFour_coordinateKernel V i)
      omega
  · by_cases hgood₁ : U α₁ i = f₀ i + α₁ • f₁ i
    · have hroot := hroot_of_good α₁ hres₁ hgood₁
      have hkernel :=
        subspaceDesignMcaFour_coordinateKernel_finrank_ge_good_subset
          V i v J (fun j _ => hv j) hli_v S₁ 1 hS₁
          (hJspan_one_anchor α₁ hroot)
      have hm : m = 1 +
          (if U α₂ i = f₀ i + α₂ • f₁ i then 0 else 1) +
          (if U α₃ i = f₀ i + α₃ • f₁ i then 0 else 1) +
          (if U α₄ i = f₀ i + α₄ • f₁ i then 0 else 1) := by
        simp [m, subspaceDesignMcaFour_fiveSeedDisagreementCount, hgood₀, hgood₁]
      change 3 ≤ m + Module.finrank F
        (subspaceDesignMcaFour_coordinateKernel V i)
      omega
    · have hkernel :=
        subspaceDesignMcaFour_coordinateKernel_finrank_ge_good_subset
          V i v J (fun j _ => hv j) hli_v S₂ 2 hS₂
          hJspan_no_anchor
      have hm : m = 2 +
          (if U α₂ i = f₀ i + α₂ • f₁ i then 0 else 1) +
          (if U α₃ i = f₀ i + α₃ • f₁ i then 0 else 1) +
          (if U α₄ i = f₀ i + α₄ • f₁ i then 0 else 1) := by
        simp [m, subspaceDesignMcaFour_fiveSeedDisagreementCount, hgood₀, hgood₁]
      change 3 ≤ m + Module.finrank F
        (subspaceDesignMcaFour_coordinateKernel V i)
      omega

theorem subspaceDesignMcaFour_five_seed_disagreement_sum_le
    {ι : Type} {F : Type} [Field F] [Fintype ι] [Nonempty ι]
    [DecidableEq F] {s : ℕ}
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (δ : ℝ) (α₀ α₁ α₂ α₃ α₄ : F)
    (hclose₀ : (Code.relHammingDist (f₀ + α₀ • f₁) (U α₀) : ℝ) ≤ δ)
    (hclose₁ : (Code.relHammingDist (f₀ + α₁ • f₁) (U α₁) : ℝ) ≤ δ)
    (hclose₂ : (Code.relHammingDist (f₀ + α₂ • f₁) (U α₂) : ℝ) ≤ δ)
    (hclose₃ : (Code.relHammingDist (f₀ + α₃ • f₁) (U α₃) : ℝ) ≤ δ)
    (hclose₄ : (Code.relHammingDist (f₀ + α₄ • f₁) (U α₄) : ℝ) ≤ δ) :
    (∑ i : ι,
      (subspaceDesignMcaFour_fiveSeedDisagreementCount
        f₀ f₁ U α₀ α₁ α₂ α₃ α₄ i : ℝ)) ≤
      5 * δ * Fintype.card ι := by
  have hb₀ := subspaceDesignMcaFour_seed_disagreement_sum_le
    f₀ f₁ U δ α₀ hclose₀
  have hb₁ := subspaceDesignMcaFour_seed_disagreement_sum_le
    f₀ f₁ U δ α₁ hclose₁
  have hb₂ := subspaceDesignMcaFour_seed_disagreement_sum_le
    f₀ f₁ U δ α₂ hclose₂
  have hb₃ := subspaceDesignMcaFour_seed_disagreement_sum_le
    f₀ f₁ U δ α₃ hclose₃
  have hb₄ := subspaceDesignMcaFour_seed_disagreement_sum_le
    f₀ f₁ U δ α₄ hclose₄
  have hsum :
      (∑ i : ι,
        (subspaceDesignMcaFour_fiveSeedDisagreementCount
          f₀ f₁ U α₀ α₁ α₂ α₃ α₄ i : ℝ)) =
      (∑ i : ι, (if U α₀ i = f₀ i + α₀ • f₁ i then (0 : ℝ) else 1)) +
      (∑ i : ι, (if U α₁ i = f₀ i + α₁ • f₁ i then (0 : ℝ) else 1)) +
      (∑ i : ι, (if U α₂ i = f₀ i + α₂ • f₁ i then (0 : ℝ) else 1)) +
      (∑ i : ι, (if U α₃ i = f₀ i + α₃ • f₁ i then (0 : ℝ) else 1)) +
      (∑ i : ι, (if U α₄ i = f₀ i + α₄ • f₁ i then (0 : ℝ) else 1)) := by
    simp [subspaceDesignMcaFour_fiveSeedDisagreementCount,
      Finset.sum_add_distrib]
  rw [hsum]
  nlinarith

theorem subspaceDesignMcaFour_sum_pointwise_disagreement_kernel_lower_three
    {ι : Type} [Fintype ι]
    (m k : ι → ℕ) (hpoint : ∀ i, 3 ≤ m i + k i) :
    (3 : ℝ) * Fintype.card ι ≤
      (∑ i, (m i : ℝ)) + (∑ i, (k i : ℝ)) := by
  calc
    (3 : ℝ) * Fintype.card ι = ∑ _i : ι, (3 : ℝ) := by simp; ring
    _ ≤ ∑ i : ι, ((m i : ℝ) + (k i : ℝ)) := by
      apply Finset.sum_le_sum
      intro i _
      exact_mod_cast hpoint i
    _ = (∑ i, (m i : ℝ)) + (∑ i, (k i : ℝ)) := by
      rw [Finset.sum_add_distrib]

theorem subspaceDesignMcaFour_rank_three_high_profile_contradiction
    {ι : Type} {F : Type} [Field F] [Fintype ι] [Nonempty ι]
    [DecidableEq F] {s : ℕ} [FiniteDimensional F (ι → Fin s → F)]
    (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C) (T : Finset F)
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (c₀ c₁ : ι → Fin s → F) (δ : ℝ)
    (hU : ∀ γ ∈ T, U γ ∈ C)
    (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C)
    (hτ : 0 ≤ τ 5)
    (hD : Module.finrank F
      (subspaceDesignMcaFour_residualSpan T U c₀ c₁) = 3)
    (hδ : δ = 5 / 8 - τ 5)
    (hclose : ∀ γ ∈ T,
      (Code.relHammingDist (f₀ + γ • f₁) (U γ) : ℝ) ≤ δ)
    (α₀ α₁ : F) (hα₀ : α₀ ∈ T) (hα₁ : α₁ ∈ T)
    (hα₀α₁ : α₀ ≠ α₁)
    (hres₀ : subspaceDesignMcaFour_residual U c₀ c₁ α₀ = 0)
    (hres₁ : subspaceDesignMcaFour_residual U c₀ c₁ α₁ = 0)
    (hprofile : 1 / 16 < τ 5) : False := by
  obtain ⟨α₂, hα₂, α₃, hα₃, α₄, hα₄, hli⟩ :=
    subspaceDesignMcaFour_exists_three_independent_residuals
      T U c₀ c₁ hD
  let V := subspaceDesignMcaFour_residualSpan T U c₀ c₁
  have hv₂ : subspaceDesignMcaFour_residual U c₀ c₁ α₂ ∈ V := by
    change subspaceDesignMcaFour_residual U c₀ c₁ α₂ ∈
      Submodule.span F
        (subspaceDesignMcaFour_residual U c₀ c₁ '' (T : Set F))
    exact Submodule.subset_span ⟨α₂, hα₂, rfl⟩
  have hv₃ : subspaceDesignMcaFour_residual U c₀ c₁ α₃ ∈ V := by
    change subspaceDesignMcaFour_residual U c₀ c₁ α₃ ∈
      Submodule.span F
        (subspaceDesignMcaFour_residual U c₀ c₁ '' (T : Set F))
    exact Submodule.subset_span ⟨α₃, hα₃, rfl⟩
  have hv₄ : subspaceDesignMcaFour_residual U c₀ c₁ α₄ ∈ V := by
    change subspaceDesignMcaFour_residual U c₀ c₁ α₄ ∈
      Submodule.span F
        (subspaceDesignMcaFour_residual U c₀ c₁ '' (T : Set F))
    exact Submodule.subset_span ⟨α₄, hα₄, rfl⟩
  have hpoint (i : ι) :
      3 ≤ subspaceDesignMcaFour_fiveSeedDisagreementCount
          f₀ f₁ U α₀ α₁ α₂ α₃ α₄ i +
        Module.finrank F (subspaceDesignMcaFour_coordinateKernel V i) :=
    subspaceDesignMcaFour_five_seed_disagreement_kernel_lower
      f₀ f₁ U c₀ c₁ V α₀ α₁ α₂ α₃ α₄ hα₀α₁ hres₀ hres₁
      hv₂ hv₃ hv₄ hli i
  have hsumlower := subspaceDesignMcaFour_sum_pointwise_disagreement_kernel_lower_three
    (fun i => subspaceDesignMcaFour_fiveSeedDisagreementCount
      f₀ f₁ U α₀ α₁ α₂ α₃ α₄ i)
    (fun i => Module.finrank F
      (subspaceDesignMcaFour_coordinateKernel V i)) hpoint
  have hmismatch := subspaceDesignMcaFour_five_seed_disagreement_sum_le
    f₀ f₁ U δ α₀ α₁ α₂ α₃ α₄
    (hclose α₀ hα₀) (hclose α₁ hα₁) (hclose α₂ hα₂)
    (hclose α₃ hα₃) (hclose α₄ hα₄)
  have hkernel := subspaceDesignMcaFour_coordinate_kernel_sum_le_design
    τ C hdesign T U c₀ c₁ hU hc₀ hc₁ hτ hD (by omega)
  have hcombined :
      (3 : ℝ) * Fintype.card ι ≤
        (5 * δ * Fintype.card ι) +
          (Fintype.card ι * 3 * τ 5) := by
    calc
      (3 : ℝ) * Fintype.card ι ≤
          (∑ i : ι,
            (subspaceDesignMcaFour_fiveSeedDisagreementCount
              f₀ f₁ U α₀ α₁ α₂ α₃ α₄ i : ℝ)) +
          (∑ i : ι, (Module.finrank F
            (subspaceDesignMcaFour_coordinateKernel V i) : ℝ)) := hsumlower
      _ ≤ (5 * δ * Fintype.card ι) +
          (Fintype.card ι * 3 * τ 5) :=
        add_le_add hmismatch (by simpa [V] using hkernel)
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hstrict : 5 * δ + 3 * τ 5 < 3 := by
    rw [hδ]
    nlinarith
  nlinarith [hcombined, hn, hstrict, hprofile]

theorem subspaceDesignMcaFour_rank_three_no_eight_contradiction
    {ι : Type} {F : Type} [Field F] [Fintype ι] [Nonempty ι]
    [DecidableEq F] {s : ℕ} [FiniteDimensional F (ι → Fin s → F)]
    (τ : ℕ → ℝ) (C : Submodule F (ι → Fin s → F))
    (hdesign : IsSubspaceDesign s τ C) (T : Finset F)
    (f₀ f₁ : ι → Fin s → F) (U : F → ι → Fin s → F)
    (c₀ c₁ : ι → Fin s → F) (δ : ℝ)
    (hTcard : T.card = 256)
    (hU : ∀ γ ∈ T, U γ ∈ C)
    (hno8 : subspaceDesignMcaFour_noEightAligned C T U)
    (hc₀ : c₀ ∈ C) (hc₁ : c₁ ∈ C)
    (hτ : 0 ≤ τ 5)
    (hD : Module.finrank F
      (subspaceDesignMcaFour_residualSpan T U c₀ c₁) = 3)
    (hδ : δ = 5 / 8 - τ 5)
    (hclose : ∀ γ ∈ T,
      (Code.relHammingDist (f₀ + γ • f₁) (U γ) : ℝ) ≤ δ)
    (α₀ α₁ : F) (hα₀ : α₀ ∈ T) (hα₁ : α₁ ∈ T)
    (hα₀α₁ : α₀ ≠ α₁)
    (hres₀ : subspaceDesignMcaFour_residual U c₀ c₁ α₀ = 0)
    (hres₁ : subspaceDesignMcaFour_residual U c₀ c₁ α₁ = 0) :
    False := by
  by_cases hlow : τ 5 < 89 / 491
  · exact subspaceDesignMcaFour_low_rank_contradiction
      τ C hdesign T f₀ f₁ U c₀ c₁ δ hTcard hU hno8 hc₀ hc₁ hτ hD
      (by omega) hδ hclose
      (subspaceDesignMcaFour_low_condition_rank_three (τ 5) hlow)
  · have hhigh : 1 / 16 < τ 5 := by
      have hcut : (1 / 16 : ℝ) < 89 / 491 := by norm_num
      exact lt_of_lt_of_le hcut (le_of_not_gt hlow)
    exact subspaceDesignMcaFour_rank_three_high_profile_contradiction
      τ C hdesign T f₀ f₁ U c₀ c₁ δ hU hc₀ hc₁ hτ hD hδ hclose
      α₀ α₁ hα₀ hα₁ hα₀α₁ hres₀ hres₁ hhigh

end CodingTheory
