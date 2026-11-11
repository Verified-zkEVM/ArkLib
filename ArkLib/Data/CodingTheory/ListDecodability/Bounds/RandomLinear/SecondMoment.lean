/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability.Bounds.RandomLinear.RowOrbit
public import ArkLib.Data.CodingTheory.ListDecodability.Bounds.RandomLinear.Types
public import ArkLib.Data.Probability.FiniteChernoff

/-!
# Second moment for one row orbit

Let `M₀` have independent columns, and suppose that every full-rank image `A M₀` with `s` rows has
a row orbit of size at least `R · q^{m s}`. Then at most a fraction `L q^{2 L²} / R` of all
`m`-row parity-check matrices `H` have no matrix of the row orbit of `M₀` inside `C(H)`.

The proof is the second-moment method for the number of matrices of the orbit inside `C(H)`.
If `[M | M']` has rank `2L - s`, then `M'` lies in a fiber of the map `M' ↦ A₂ M'` for some
full-rank `A₂` with `s` rows. Such a fiber is small.

## Main statements

* `CodingTheory.RandomLinearInternal.exists_relation`: the relation `A₂ M' = -A₁ M` of a rank
  deficiency.
* `CodingTheory.RandomLinearInternal.ncard_fiber_rowOrbit_mul_le`: the fibers of a row-equivariant
  map.
* `CodingTheory.RandomLinearInternal.card_pc_avoid_le`: the second-moment bound.
-/

@[expose] public section

namespace CodingTheory.RandomLinearInternal

open Probability

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Fintype F] [DecidableEq F]

open Classical in
/-- The number of matrices of the row orbit of `M₀` whose columns lie in `C(H)`. -/
noncomputable def pcCount {L : ℕ} (M₀ : ι → Fin L → F) (m : ℕ)
    (H : Fin m → Module.Dual F (ι → F)) : ℕ :=
  ((Set.toFinite (rowOrbit M₀)).toFinset.filter (fun M => ∀ i, Function.swap M i ∈ pcCode m H)).card

open Classical in
omit [DecidableEq ι] [DecidableEq F] in
private theorem card_filter_le_pcCode [Fintype (Module.Dual F (ι → F))] (m : ℕ)
    (V : Submodule F (ι → F)) :
    (Finset.univ.filter (fun H : Fin m → Module.Dual F (ι → F) => V ≤ pcCode m H)).card =
      Fintype.card F ^ (m * (Fintype.card ι - Module.finrank F V)) := by
  classical
  rw [← card_pc_contains m V, Nat.card_eq_fintype_card, Fintype.card_subtype]

omit [DecidableEq ι] [Fintype ι] [DecidableEq F] [Fintype F] in
private theorem cols_mem_and_iff_span_le {L : ℕ} (M M' : ι → Fin L → F) (P : Submodule F (ι → F)) :
    ((∀ i, Function.swap M i ∈ P) ∧ ∀ i, Function.swap M' i ∈ P) ↔
      Submodule.span F (Set.range (Function.swap M) ∪ Set.range (Function.swap M')) ≤ P := by
  rw [Submodule.span_le, Set.union_subset_iff, Set.range_subset_iff, Set.range_subset_iff]
  rfl

omit [DecidableEq ι] [DecidableEq F] in
/-- First moment of `pcCount`. -/
theorem sum_pcCount [Fintype (Module.Dual F (ι → F))] {L : ℕ} (M₀ : ι → Fin L → F)
    (hM₀ : LinearIndependent F (Function.swap M₀)) (m : ℕ) :
    ∑ H : Fin m → Module.Dual F (ι → F), pcCount M₀ m H =
      (rowOrbit M₀).ncard * Fintype.card F ^ (m * (Fintype.card ι - L)) := by
  classical
  unfold pcCount
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm, Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
  rw [Finset.card_eq_sum_ones, Finset.sum_mul, one_mul]
  refine Finset.sum_congr rfl fun M hM => ?_
  have hMo : M ∈ rowOrbit M₀ := (Set.toFinite _).mem_toFinset.1 hM
  have hli := linearIndependent_cols_of_mem_rowOrbit hMo hM₀
  have hc := card_filter_le_pcCode m (Submodule.span F (Set.range (Function.swap M)))
  rw [finrank_span_eq_card hli, Fintype.card_fin] at hc
  rw [← hc, Finset.card_filter]
  refine Finset.sum_congr rfl fun H _ => ?_
  simp only [Submodule.span_le, Set.range_subset_iff, SetLike.mem_coe]

omit [DecidableEq ι] [DecidableEq F] in
/-- Second moment of `pcCount`. -/
theorem sum_pcCount_sq [Fintype (Module.Dual F (ι → F))] {L : ℕ} (M₀ : ι → Fin L → F)
    (m : ℕ) :
    ∑ H : Fin m → Module.Dual F (ι → F), pcCount M₀ m H ^ 2 =
      ∑ M ∈ (Set.toFinite (rowOrbit M₀)).toFinset, ∑ M' ∈ (Set.toFinite (rowOrbit M₀)).toFinset,
        Fintype.card F ^ (m * (Fintype.card ι - Module.finrank F
          (Submodule.span F (Set.range (Function.swap M) ∪ Set.range (Function.swap M'))))) := by
  classical
  unfold pcCount
  simp_rw [Finset.card_filter, sq, Finset.sum_mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun M _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun M' _ => ?_
  rw [← card_filter_le_pcCode, Finset.card_filter]
  refine Finset.sum_congr rfl fun H _ => ?_
  simp only [← cols_mem_and_iff_span_le, ite_mul, one_mul, zero_mul, ite_and]

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
/-- Rank deficiency `s` of `[M | M']` gives an `s`-dimensional relation with full-rank `A₂`. -/
theorem exists_relation {L : ℕ} (M M' : ι → Fin L → F) (hM : LinearIndependent F (Function.swap M))
    (s : ℕ) (hr : Module.finrank F
      (Submodule.span F (Set.range (Function.swap M) ∪ Set.range (Function.swap M')))
      + s ≤ 2 * L) :
    ∃ A₁ A₂ : Matrix (Fin s) (Fin L) F, LinearIndependent F A₂ ∧
      ∀ j, A₂.mulVec (M' j) = -A₁.mulVec (M j) := by
  classical
  set V := Submodule.span F (Set.range (Function.swap M) ∪ Set.range (Function.swap M')) with hV
  have : Module.Finite F V := FiniteDimensional.span_of_finite F
    ((Set.finite_range _).union (Set.finite_range _))
  let φ : ((Fin L → F) × (Fin L → F)) →ₗ[F] (ι → F) :=
    (Fintype.linearCombination F (Function.swap M)).coprod
      (Fintype.linearCombination F (Function.swap M'))
  have hφ : ∀ x, φ x = ∑ i, x.1 i • Function.swap M i + ∑ i, x.2 i • Function.swap M' i :=
    fun x => rfl
  have hrange : LinearMap.range φ ≤ V := by
    rintro _ ⟨x, rfl⟩
    rw [hφ]
    exact add_mem
      (sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨i, rfl⟩)))
      (sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨i, rfl⟩)))
  have h1 := LinearMap.finrank_range_add_finrank_ker φ
  have h2 : Module.finrank F (LinearMap.range φ) ≤ Module.finrank F V :=
    Submodule.finrank_mono hrange
  have h3 : Module.finrank F ((Fin L → F) × (Fin L → F)) = 2 * L := by
    simp [Module.finrank_prod]; ring
  have hs : s ≤ Module.finrank F (LinearMap.ker φ) := by omega
  let b := Module.finBasis F (LinearMap.ker φ)
  let g : LinearMap.ker φ →ₗ[F] (Fin L → F) :=
    (LinearMap.snd F _ _).comp (LinearMap.ker φ).subtype
  have hg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨a, b'⟩, hx⟩ h
    have hb' : b' = 0 := h
    subst hb'
    have hx' : ∑ i, a i • Function.swap M i = 0 := by simpa [hφ] using hx
    have := Fintype.linearIndependent_iff.1 hM a hx'
    exact Subtype.ext (Prod.ext (funext this) rfl)
  have hli : LinearIndependent F (fun k : Fin s => g (b (Fin.castLE hs k))) :=
    (b.linearIndependent.comp _ (Fin.castLE_injective hs)).map' g (LinearMap.ker_eq_bot.2 hg)
  refine ⟨Matrix.of fun k i => ((b (Fin.castLE hs k) : LinearMap.ker φ) :
      (Fin L → F) × (Fin L → F)).1 i,
    Matrix.of fun k i => g (b (Fin.castLE hs k)) i, hli, fun j => ?_⟩
  funext k
  have hx := (b (Fin.castLE hs k)).2
  rw [LinearMap.mem_ker, hφ] at hx
  have := congrFun hx j
  simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
  simp only [Matrix.mulVec, dotProduct, Matrix.of_apply, Pi.neg_apply, g, LinearMap.comp_apply,
    Submodule.subtype_apply, LinearMap.snd_apply]
  simp only [Function.swap] at this
  linear_combination this

omit [Fintype ι] [DecidableEq ι] in
/-- Fibres of a row-equivariant map on a row orbit: `|fibre| · |image orbit| ≤ |orbit|`. -/
theorem ncard_fiber_rowOrbit_mul_le [Finite ι] {β γ : Type} (M₀ : ι → β) (f : β → γ)
    (N : ι → γ) :
    {M ∈ rowOrbit M₀ | f ∘ M = N}.ncard * (rowOrbit (f ∘ M₀)).ncard ≤ (rowOrbit M₀).ncard := by
  classical
  have hfin : (rowOrbit M₀).Finite :=
    (Set.finite_range fun σ : Equiv.Perm ι => M₀ ∘ σ).subset fun _ hM => mem_rowOrbit.1 hM
  rcases Set.eq_empty_or_nonempty {M ∈ rowOrbit M₀ | f ∘ M = N} with h | ⟨M₁, hM₁o, hM₁⟩
  · simp [h]
  obtain ⟨σ₁, rfl⟩ := mem_rowOrbit.1 hM₁o
  have hN : ∀ N' ∈ rowOrbit (f ∘ M₀), ∃ ρ : Equiv.Perm ι, N ∘ ρ = N' := by
    intro N' hN'
    obtain ⟨τ, rfl⟩ := mem_rowOrbit.1 hN'
    refine ⟨σ₁⁻¹ * τ, ?_⟩
    rw [← hM₁]
    funext x
    simp [Function.comp_def]
  let r : (ι → γ) → Equiv.Perm ι := fun N' => if h : ∃ ρ : Equiv.Perm ι, N ∘ ρ = N' then
    h.choose else 1
  have hr : ∀ N' ∈ rowOrbit (f ∘ M₀), N ∘ r N' = N' := fun N' hN' => by
    have h := hN N' hN'
    simp only [r, h, ↓reduceDIte]
    exact h.choose_spec
  rw [← Set.ncard_prod]
  refine Set.ncard_le_ncard_of_injOn (fun p => p.1 ∘ r p.2) ?_ ?_ hfin
  · rintro ⟨M, N'⟩ ⟨⟨hMo, -⟩, -⟩
    obtain ⟨σ, rfl⟩ := mem_rowOrbit.1 hMo
    exact mem_rowOrbit.2 ⟨σ * r N', by funext x; simp [Function.comp_def]⟩
  · rintro ⟨M, N'⟩ ⟨⟨hMo, hM⟩, hN'⟩ ⟨M'', N''⟩ ⟨⟨hMo', hM'⟩, hN''⟩ h
    simp only at h hM hM' hN' hN''
    have e1 : N' = N'' := by
      calc N' = N ∘ r N' := (hr N' hN').symm
        _ = f ∘ (M ∘ r N') := by rw [← hM]; rfl
        _ = f ∘ (M'' ∘ r N'') := by rw [h]
        _ = N ∘ r N'' := by rw [← hM']; rfl
        _ = N'' := hr N'' hN''
    subst e1
    refine Prod.ext ?_ rfl
    simp only
    funext x
    have := congrFun h ((r N').symm x)
    simpa using this

/-- Rank of the joint column span of two matrices. -/
private noncomputable def jointRank {L : ℕ} (M M' : ι → Fin L → F) : ℕ :=
  Module.finrank F (Submodule.span F (Set.range (Function.swap M) ∪ Set.range (Function.swap M')))

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
private theorem jointRank_le {L : ℕ} (M M' : ι → Fin L → F) : jointRank M M' ≤ 2 * L := by
  unfold jointRank
  rw [← Set.Sum.elim_range]
  exact (finrank_range_le_card _).trans (by simp [two_mul])

omit [DecidableEq ι] [Fintype F] [DecidableEq F] in
private theorem jointRank_le_card {L : ℕ} (M M' : ι → Fin L → F) :
    jointRank M M' ≤ Fintype.card ι := by
  unfold jointRank
  simpa using Submodule.finrank_le
    (Submodule.span F (Set.range (Function.swap M) ∪ Set.range (Function.swap M')))

omit [Fintype ι] [DecidableEq ι] [Fintype F] [DecidableEq F] in
private theorem le_jointRank {L : ℕ} (M M' : ι → Fin L → F)
    (hM : LinearIndependent F (Function.swap M)) :
    L ≤ jointRank M M' := by
  unfold jointRank
  have : Module.Finite F
      (Submodule.span F (Set.range (Function.swap M) ∪ Set.range (Function.swap M'))) :=
    FiniteDimensional.span_of_finite F ((Set.finite_range _).union (Set.finite_range _))
  have h := Submodule.finrank_mono (R := F)
    (Submodule.span_mono (Set.subset_union_left : Set.range (Function.swap M) ⊆
      Set.range (Function.swap M) ∪ Set.range (Function.swap M')))
  rwa [finrank_span_eq_card hM, Fintype.card_fin] at h

/-- Every full-rank image `A M₀` with `s ≥ 1` rows has a row orbit of size at least `R q^{m s}`. -/
def LargeImageOrbits {L : ℕ} (M₀ : ι → Fin L → F) (m : ℕ) (R : ℝ) : Prop :=
  ∀ s : ℕ, 1 ≤ s → ∀ A : Matrix (Fin s) (Fin L) F, LinearIndependent F A →
    R * (Fintype.card F : ℝ) ^ (m * s) ≤ (rowOrbit (fun j => A.mulVec (M₀ j))).ncard

omit [DecidableEq ι] in
private theorem card_fiber_mul_le {L : ℕ} (M₀ : ι → Fin L → F) (R : ℝ) (m s : ℕ)
    (A : Matrix (Fin s) (Fin L) F)
    (hA : R * (Fintype.card F : ℝ) ^ (m * s) ≤ (rowOrbit (fun j => A.mulVec (M₀ j))).ncard)
    (N : ι → Fin s → F) :
    (((Set.toFinite (rowOrbit M₀)).toFinset.filter
        (fun M' => (fun j => A.mulVec (M' j)) = N)).card : ℝ) * (R * (Fintype.card F : ℝ) ^ (m * s))
      ≤ (Set.toFinite (rowOrbit M₀)).toFinset.card := by
  classical
  have h := ncard_fiber_rowOrbit_mul_le M₀ (fun v => A.mulVec v) N
  have e1 : {M ∈ rowOrbit M₀ | (fun v => A.mulVec v) ∘ M = N} =
      ↑((Set.toFinite (rowOrbit M₀)).toFinset.filter
        (fun M' => (fun j => A.mulVec (M' j)) = N)) := by
    ext M
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Set.Finite.mem_toFinset]
    rfl
  rw [e1, Set.ncard_coe_finset] at h
  rw [← Set.ncard_eq_toFinset_card _ (Set.toFinite (rowOrbit M₀))]
  calc _ ≤ ((_ : ℕ) : ℝ) * ((rowOrbit (fun j => A.mulVec (M₀ j))).ncard : ℝ) :=
        mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg _)
    _ ≤ _ := by exact_mod_cast h

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
private theorem card_jointRank_eq_mul_le [Finite ι] {L : ℕ} (M₀ : ι → Fin L → F)
    (hM₀ : LinearIndependent F (Function.swap M₀)) (m : ℕ) (R : ℝ) (hR : 0 < R)
    (hrare : LargeImageOrbits M₀ m R)
    (s : ℕ) (hs : 1 ≤ s) (M : ι → Fin L → F) (hM : M ∈ rowOrbit M₀) :
    (((Set.toFinite (rowOrbit M₀)).toFinset.filter
        (fun M' => jointRank M M' + s = 2 * L)).card : ℝ) * (R * (Fintype.card F : ℝ) ^ (m * s))
      ≤ (Fintype.card F : ℝ) ^ (s * L) * (Fintype.card F : ℝ) ^ (s * L) *
        (Set.toFinite (rowOrbit M₀)).toFinset.card := by
  classical
  have := Fintype.ofFinite ι
  have hli := linearIndependent_cols_of_mem_rowOrbit hM hM₀
  have hq : (0 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  set T := (Set.toFinite (rowOrbit M₀)).toFinset with hT
  set idx : Finset (Matrix (Fin s) (Fin L) F × Matrix (Fin s) (Fin L) F) :=
    Finset.univ.filter (fun p => LinearIndependent F p.2) with hidx
  have hsub : T.filter (fun M' => jointRank M M' + s = 2 * L) ⊆
      idx.biUnion (fun p => T.filter
        (fun M' => (fun j => p.2.mulVec (M' j)) = fun j => -p.1.mulVec (M j))) := by
    intro M' hM'
    rw [Finset.mem_filter] at hM'
    obtain ⟨A₁, A₂, hA₂, hrel⟩ := exists_relation M M' hli s hM'.2.le
    rw [Finset.mem_biUnion]
    exact ⟨(A₁, A₂), by simpa [hidx] using hA₂, Finset.mem_filter.2 ⟨hM'.1, funext hrel⟩⟩
  have hRq : 0 < R * (Fintype.card F : ℝ) ^ (m * s) := by positivity
  have hcard : idx.card ≤ Fintype.card F ^ (s * L) * Fintype.card F ^ (s * L) := by
    refine (Finset.card_filter_le _ _).trans ?_
    have hmat : Fintype.card (Matrix (Fin s) (Fin L) F) = Fintype.card F ^ (s * L) := by
      change Fintype.card (Fin s → Fin L → F) = _
      rw [Fintype.card_fun, Fintype.card_fun]
      simp [← pow_mul, mul_comm]
    rw [Finset.card_univ, Fintype.card_prod, hmat]
  calc _ ≤ ((∑ p ∈ idx, (T.filter
          (fun M' => (fun j => p.2.mulVec (M' j)) = fun j => -p.1.mulVec (M j))).card : ℕ) : ℝ) *
        (R * (Fintype.card F : ℝ) ^ (m * s)) := by
        refine mul_le_mul_of_nonneg_right ?_ hRq.le
        exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    _ = ∑ p ∈ idx, ((T.filter
          (fun M' => (fun j => p.2.mulVec (M' j)) = fun j => -p.1.mulVec (M j))).card : ℝ) *
        (R * (Fintype.card F : ℝ) ^ (m * s)) := by
        rw [Nat.cast_sum, Finset.sum_mul]
    _ ≤ ∑ p ∈ idx, (T.card : ℝ) := by
        refine Finset.sum_le_sum fun p hp => card_fiber_mul_le M₀ R m s p.2 ?_ _
        exact hrare s hs p.2 (by simpa [hidx] using hp)
    _ = idx.card * (T.card : ℝ) := by simp
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
        exact_mod_cast hcard

omit [Fintype ι] [DecidableEq ι] [DecidableEq F] in
private theorem sum_sum_jointRank_le [Finite ι] {L : ℕ} (M₀ : ι → Fin L → F)
    (hM₀ : LinearIndependent F (Function.swap M₀)) (m : ℕ) (R : ℝ) (hR : 0 < R)
    (hrare : LargeImageOrbits M₀ m R)
    (c : ℝ) (hc : 0 ≤ c) :
    ∑ M ∈ (Set.toFinite (rowOrbit M₀)).toFinset, ∑ M' ∈ (Set.toFinite (rowOrbit M₀)).toFinset,
        c * ((Fintype.card F : ℝ) ^ (m * (2 * L - jointRank M M')) - 1) ≤
      ((Set.toFinite (rowOrbit M₀)).toFinset.card : ℝ) *
        ((Set.toFinite (rowOrbit M₀)).toFinset.card : ℝ) *
        (L * (c * (Fintype.card F : ℝ) ^ (2 * L ^ 2) / R)) := by
  classical
  have := Fintype.ofFinite ι
  have hq1 : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
  set q : ℝ := (Fintype.card F : ℝ) with hq
  set T := (Set.toFinite (rowOrbit M₀)).toFinset with hT
  have hMo : ∀ M ∈ T, M ∈ rowOrbit M₀ := fun M hM => (Set.toFinite _).mem_toFinset.1 hM
  have step : ∀ M ∈ T, ∑ M' ∈ T, c * (q ^ (m * (2 * L - jointRank M M')) - 1) ≤
      T.card * (L * (c * q ^ (2 * L ^ 2) / R)) := by
    intro M hM
    have hli := linearIndependent_cols_of_mem_rowOrbit (hMo M hM) hM₀
    have h1 : ∀ M' ∈ T, c * (q ^ (m * (2 * L - jointRank M M')) - 1) ≤
        ∑ s ∈ Finset.Icc 1 L, if jointRank M M' + s = 2 * L then c * q ^ (m * s) else 0 := by
      intro M' _
      have hge := le_jointRank M M' hli
      have hle := jointRank_le M M'
      by_cases hd : 2 * L - jointRank M M' = 0
      · rw [hd]
        simp only [mul_zero, pow_zero, sub_self, mul_zero]
        exact Finset.sum_nonneg fun s _ => by split_ifs <;> positivity
      · refine le_trans ?_ (Finset.single_le_sum (f := fun s => if jointRank M M' + s = 2 * L
          then c * q ^ (m * s) else 0) (fun s _ => by split_ifs <;> positivity)
          (Finset.mem_Icc.2 ⟨Nat.pos_of_ne_zero hd, by omega⟩))
        rw [ite_eq_left (by omega : jointRank M M' + (2 * L - jointRank M M') = 2 * L)]
        nlinarith [mul_nonneg hc (zero_le_one' ℝ)]
    have h2 : ∀ s ∈ Finset.Icc 1 L, c * q ^ (m * s) * ((T.filter
        (fun M' => jointRank M M' + s = 2 * L)).card : ℝ) ≤ T.card * (c * q ^ (2 * L ^ 2) / R) := by
      intro s hs
      rw [Finset.mem_Icc] at hs
      have h := card_jointRank_eq_mul_le M₀ hM₀ m R hR hrare s hs.1 M (hMo M hM)
      have hqs : q ^ (s * L) * q ^ (s * L) ≤ q ^ (2 * L ^ 2) := by
        rw [← pow_add]
        exact pow_le_pow_right₀ hq1.le (by nlinarith [hs.2])
      have hq0 : 0 < q ^ (m * s) := by positivity
      have h3 : ((T.filter (fun M' => jointRank M M' + s = 2 * L)).card : ℝ) * q ^ (m * s) ≤
          T.card * q ^ (2 * L ^ 2) / R := by
        rw [le_div_iff₀ hR]
        nlinarith [Nat.cast_nonneg (α := ℝ) T.card]
      calc _ = c * (((T.filter (fun M' => jointRank M M' + s = 2 * L)).card : ℝ) *
            q ^ (m * s)) := by
            ring
        _ ≤ c * (T.card * q ^ (2 * L ^ 2) / R) := mul_le_mul_of_nonneg_left h3 hc
        _ = _ := by ring
    calc _ ≤ ∑ M' ∈ T, ∑ s ∈ Finset.Icc 1 L,
          if jointRank M M' + s = 2 * L then c * q ^ (m * s) else 0 := Finset.sum_le_sum h1
      _ = ∑ s ∈ Finset.Icc 1 L, c * q ^ (m * s) *
          ((T.filter (fun M' => jointRank M M' + s = 2 * L)).card : ℝ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]
      _ ≤ ∑ s ∈ Finset.Icc 1 L, (T.card : ℝ) * (c * q ^ (2 * L ^ 2) / R) :=
        Finset.sum_le_sum h2
      _ = _ := by simp; ring
  calc _ ≤ ∑ M ∈ T, (T.card : ℝ) * (L * (c * q ^ (2 * L ^ 2) / R)) := Finset.sum_le_sum step
    _ = _ := by simp; ring

omit [DecidableEq ι] [DecidableEq F] in
/-- Combinatorial second-moment bound: few parity-check matrices avoid the orbit of `M₀`. -/
theorem card_pc_avoid_le {L : ℕ} (M₀ : ι → Fin L → F) (hM₀ : LinearIndependent F (Function.swap M₀))
    (m : ℕ) (R : ℝ) (hR : 0 < R)
    (hrare : LargeImageOrbits M₀ m R) :
    (Nat.card {H : Fin m → Module.Dual F (ι → F) //
        ∀ M ∈ rowOrbit M₀, ¬ ∀ i, Function.swap M i ∈ pcCode m H} : ℝ)
      ≤ ((L : ℝ) * (Fintype.card F : ℝ) ^ (2 * L ^ 2) / R) *
          (Fintype.card F : ℝ) ^ (Fintype.card ι * m) := by
  classical
  have : Finite (Module.Dual F (ι → F)) := Module.finite_of_finite F
  let _ : Fintype (Module.Dual F (ι → F)) := Fintype.ofFinite _
  have hq1 : (1 : ℝ) < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.one_lt_card
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq0 : 0 < q := by linarith
  set n := Fintype.card ι with hn
  set T := (Set.toFinite (rowOrbit M₀)).toFinset with hT
  have hMo : ∀ M ∈ T, M ∈ rowOrbit M₀ := fun M hM => (Set.toFinite _).mem_toFinset.1 hM
  have hM₀T : M₀ ∈ T := (Set.toFinite _).mem_toFinset.2 ⟨1, by simp⟩
  have ht : 0 < (T.card : ℝ) := by exact_mod_cast Finset.card_pos.2 ⟨M₀, hM₀T⟩
  set t : ℝ := (T.card : ℝ) with ht_def
  have hLn : L ≤ n := (le_jointRank M₀ M₀ hM₀).trans (jointRank_le_card M₀ M₀)
  have hncard : ((rowOrbit M₀).ncard : ℝ) = t := by
    rw [Set.ncard_eq_toFinset_card _ (Set.toFinite _)]
  -- the bad set
  have hbad : (Nat.card {H : Fin m → Module.Dual F (ι → F) //
        ∀ M ∈ rowOrbit M₀, ¬ ∀ i, Function.swap M i ∈ pcCode m H} : ℝ) =
      ((Finset.univ.filter (fun H : Fin m → Module.Dual F (ι → F) =>
        (pcCount M₀ m H : ℝ) = 0)).card : ℝ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    congr 2
    refine Finset.filter_congr fun H _ => ?_
    unfold pcCount
    rw [Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    simp only [Set.Finite.mem_toFinset]
  set c : ℝ := q ^ (n * m) / q ^ (m * (2 * L)) with hc
  have hc0 : 0 ≤ c := by positivity
  set μ : ℝ := t / q ^ (m * L) with hμ
  have hE : q ^ (m * (2 * L)) = (q ^ (m * L)) ^ 2 := by rw [← pow_mul]; congr 1; ring
  have hN : (Fintype.card (Fin m → Module.Dual F (ι → F)) : ℝ) = q ^ (n * m) := by
    rw [Fintype.card_fun, Fintype.card_fin, Module.card_eq_pow_finrank (K := F)
      (V := Module.Dual F (ι → F)), Subspace.dual_finrank_eq, Module.finrank_fintype_fun_eq_card]
    push_cast
    rw [← pow_mul]
  have hS1 : ∑ H : Fin m → Module.Dual F (ι → F), (pcCount M₀ m H : ℝ) =
      t * q ^ (m * (n - L)) := by
    have h := congrArg (Nat.cast : ℕ → ℝ) (sum_pcCount M₀ hM₀ m)
    push_cast at h
    rw [← hncard]
    exact h
  have hμN : μ * q ^ (n * m) = t * q ^ (m * (n - L)) := by
    have : q ^ (n * m) = q ^ (m * (n - L)) * q ^ (m * L) := by
      rw [← pow_add, ← Nat.mul_add, Nat.sub_add_cancel hLn, mul_comm]
    rw [this, hμ]
    field_simp
  have hS2 : ∑ H : Fin m → Module.Dual F (ι → F), (pcCount M₀ m H : ℝ) ^ 2 =
      ∑ M ∈ T, ∑ M' ∈ T, c * q ^ (m * (2 * L - jointRank M M')) := by
    have := sum_pcCount_sq M₀ m
    have h2 : ((∑ H : Fin m → Module.Dual F (ι → F), pcCount M₀ m H ^ 2 : ℕ) : ℝ) = _ :=
      congrArg (Nat.cast : ℕ → ℝ) this
    push_cast at h2
    rw [h2]
    refine Finset.sum_congr rfl fun M hM => Finset.sum_congr rfl fun M' hM' => ?_
    have hli := linearIndependent_cols_of_mem_rowOrbit (hMo M hM) hM₀
    have hge := le_jointRank M M' hli
    have hle := jointRank_le M M'
    have hlen := jointRank_le_card M M'
    change q ^ (m * (n - jointRank M M')) = _
    have e1 : q ^ (n * m) = q ^ (m * (n - jointRank M M')) * q ^ (m * jointRank M M') := by
      rw [← pow_add, ← Nat.mul_add, Nat.sub_add_cancel hlen, mul_comm]
    have e2 : q ^ (m * (2 * L)) =
        q ^ (m * (2 * L - jointRank M M')) * q ^ (m * jointRank M M') := by
      rw [← pow_add, ← Nat.mul_add, Nat.sub_add_cancel hle]
    have hp : 0 < q ^ (m * jointRank M M') := by positivity
    rw [hc, e2, e1]
    field_simp
  have hsq : ∑ H : Fin m → Module.Dual F (ι → F), ((pcCount M₀ m H : ℝ) - μ) ^ 2 =
      ∑ M ∈ T, ∑ M' ∈ T, c * (q ^ (m * (2 * L - jointRank M M')) - 1) := by
    have e : ∀ H : Fin m → Module.Dual F (ι → F), ((pcCount M₀ m H : ℝ) - μ) ^ 2 =
        (pcCount M₀ m H : ℝ) ^ 2 - 2 * μ * pcCount M₀ m H + μ ^ 2 := fun H => by ring
    have hR' : ∑ M ∈ T, ∑ M' ∈ T, c * (q ^ (m * (2 * L - jointRank M M')) - 1) =
        ∑ M ∈ T, ∑ M' ∈ T, c * q ^ (m * (2 * L - jointRank M M')) - t * t * c := by
      simp only [mul_sub, Finset.sum_sub_distrib, mul_one, Finset.sum_const, nsmul_eq_mul]
      rw [← ht_def]; ring
    have hh : 2 * μ * (t * q ^ (m * (n - L))) = 2 * μ ^ 2 * q ^ (n * m) := by
      rw [← hμN]; ring
    have h3 : μ ^ 2 * q ^ (n * m) = t * t * c := by
      rw [hc, hμ, div_pow, ← hE]; field_simp
    rw [hR']
    simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hS1, hS2,
      Finset.sum_const, Finset.card_univ, hN, nsmul_eq_mul]
    linear_combination (-1 : ℝ) * hh - h3
  have hcheb := card_zero_mul_sq_le (fun H : Fin m → Module.Dual F (ι → F) =>
    (pcCount M₀ m H : ℝ)) μ
  have hpair : ∑ M ∈ T, ∑ M' ∈ T, c * (q ^ (m * (2 * L - jointRank M M')) - 1) ≤
      t * t * (L * (c * q ^ (2 * L ^ 2) / R)) := sum_sum_jointRank_le M₀ hM₀ m R hR hrare c hc0
  rw [hsq] at hcheb
  rw [hbad]
  have hE0 : 0 < q ^ (m * (2 * L)) := by positivity
  have hμ2 : μ ^ 2 = t * t / q ^ (m * (2 * L)) := by rw [hμ, hE, div_pow]; ring
  have key : ((Finset.univ.filter (fun H : Fin m → Module.Dual F (ι → F) =>
        (pcCount M₀ m H : ℝ) = 0)).card : ℝ) * (t * t / q ^ (m * (2 * L))) ≤
      ((L : ℝ) * q ^ (2 * L ^ 2) / R * q ^ (n * m)) * (t * t / q ^ (m * (2 * L))) := by
    rw [← hμ2]
    refine hcheb.trans (hpair.trans (le_of_eq ?_))
    rw [hμ2, hc]
    field_simp
  exact le_of_mul_le_mul_right key (by positivity)

end CodingTheory.RandomLinearInternal
