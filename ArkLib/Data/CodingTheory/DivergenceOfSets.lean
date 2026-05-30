/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland
-/

import ArkLib.Data.CodingTheory.Basic.DecodingRadius
import ArkLib.Data.CodingTheory.Basic.Distance
import ArkLib.Data.CodingTheory.Basic.LinearCode
import ArkLib.Data.CodingTheory.Basic.RelativeDistance
import ArkLib.Data.CodingTheory.ProximityGap.Basic
import ArkLib.Data.CodingTheory.ProximityGap.BCIKS20.ErrorBound
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Probability.Notation
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs

open NNReal ProximityGap

/-!
  # Definitions and Theorems about Divergence of Sets

  ## Main Definitions and Statements

  - divergence of sets
  - statement of Corollary 1.3 (Concentration bounds) from [BCIKS20].
-/

namespace DivergenceOfSets

open Code ReedSolomon ProbabilityTheory

section Defs

variable {ι : Type*} [Fintype ι] [Nonempty ι]
         {F : Type*} [DecidableEq F]
         {U V : Set (ι → F)} [Nonempty V] [Fintype V]

/-- The set of possible relative Hamming distances between two sets. -/
def possibleDeltas (U V : Set (ι → F)) [Nonempty V] [Fintype V] : Set ℚ≥0 :=
  {d : ℚ≥0 | ∃ u ∈ U, δᵣ'(u,V) = d}

/-- The set of possible relative Hamming distances between two sets is well-defined. -/
@[simp]
lemma possibleDeltas_subset_relHammingDistRange :
    possibleDeltas U V ⊆ relHammingDistRange ι :=
  fun x hx_mem_deltas ↦ by
    simp only [possibleDeltas, Set.mem_setOf_eq] at hx_mem_deltas
    rcases hx_mem_deltas with ⟨u, hu_mem, h_dist_eq⟩
    rw [←h_dist_eq]
    unfold relDistFromCode'
    have h_mem : (Finset.univ.image (fun (c : V) => relHammingDist u c)).min'
      (Finset.univ_nonempty.image _) ∈ Finset.univ.image (fun (c : V) => relHammingDist u c) :=
      Finset.min'_mem _ (Finset.univ_nonempty.image _)
    obtain ⟨c, _, h_eq⟩ := Finset.mem_image.mp h_mem
    rw [←h_eq]
    exact relHammingDist_mem_relHammingDistRange

/-- The set of possible relative Hamming distances between two sets is finite. -/
@[simp]
lemma finite_possibleDeltas : (possibleDeltas U V).Finite :=
  Set.Finite.subset finite_relHammingDistRange possibleDeltas_subset_relHammingDistRange

open Classical in
/-- Definition of divergence of two sets from Section 1.2 in [BCIKS20].

For two sets `U` and `V`, the divergence of `U` from `V` is the maximum of the possible
relative Hamming distances between elements of `U` and the set `V`. -/
noncomputable def divergence (U V : Set (ι → F)) [Nonempty V] [Fintype V] : ℚ≥0 :=
  haveI : Fintype (possibleDeltas U V) := @Fintype.ofFinite _ finite_possibleDeltas
  if h : (possibleDeltas U V).Nonempty
  then (possibleDeltas U V).toFinset.max' (Set.toFinset_nonempty.2 h)
  else 0

end Defs

section Theorems

variable {ι : Type} [Fintype ι] [Nonempty ι]
         {F : Type} [Fintype F] [Field F]
         {U V : Set (ι → F)}

open scoped ProbabilityTheory in
theorem Pr_uniform_eq_one_imp_forall {α : Type} [Fintype α] [Nonempty α] (P : α → Prop) :
    Pr_{let a ← $ᵖ α}[P a] = 1 → ∀ a, P a := by
  classical
  intro hPr a
  by_contra hPa
  let q : PMF Prop := ($ᵖ α : PMF α).map P
  have hqTrue : q True = 1 := by
    simpa only [q, PMF.monad_map_eq_map] using hPr
  have hsupport : q.support = {True} := (PMF.apply_eq_one_iff q True).1 hqTrue
  have hPfalse : P a = False := by
    exact propext (iff_false_intro hPa)
  have hFalse : False ∈ q.support := by
    refine (PMF.mem_support_map_iff (p := ($ᵖ α : PMF α)) (f := P) (b := False)).2 ?_
    refine ⟨a, ?_, hPfalse⟩
    simp
  have : False ∈ ({True} : Set Prop) := by
    simp [hsupport] at hFalse
  have hEq : False = True := by
    simp [Set.mem_singleton_iff] at this
  exact false_ne_true hEq

open scoped ProbabilityTheory in
theorem Pr_uniform_equiv {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (e : α ≃ β) (P : β → Prop) :
  Pr_{let a ← $ᵖ α}[P (e a)] = Pr_{let b ← $ᵖ β}[P b] := by
  classical
  have hmap : (PMF.uniformOfFintype α).map e = PMF.uniformOfFintype β := by
    ext b
    -- Reduce to a finite sum over a singleton fiber.
    simp only [PMF.map_apply, PMF.uniformOfFintype_apply,
      Fintype.card_congr e, tsum_fintype]
    -- Transport the sum along the equivalence `e`.
    have hs :
        Finset.univ.sum (fun a : α =>
            if b = e a then (Fintype.card β : ENNReal)⁻¹ else 0)
          =
          Finset.univ.sum (fun b' : β =>
            if b = b' then (Fintype.card β : ENNReal)⁻¹ else 0) := by
      -- `Fintype.sum_equiv` is the change-of-variables lemma for sums over `univ`.
      simpa using
        (Fintype.sum_equiv e
          (fun a : α => if b = e a then (Fintype.card β : ENNReal)⁻¹ else 0)
          (fun b' : β => if b = b' then (Fintype.card β : ENNReal)⁻¹ else 0)
          (by intro a; rfl))
    -- Evaluate the Kronecker delta sum.
    have hdelta :
        Finset.univ.sum (fun b' : β =>
            if b = b' then (Fintype.card β : ENNReal)⁻¹ else 0) =
          (Fintype.card β : ENNReal)⁻¹ := by
      simp
    exact hs.trans hdelta
  -- Now use functoriality of `PMF.map` to move `P` across the equivalence.
  -- (Unfolding `Pr_{...}[_]` gives a `PMF Prop` evaluated at `True`.)
  change
    (do
        let a ← (PMF.uniformOfFintype α)
        pure (P (e a))) True =
      (do
        let b ← (PMF.uniformOfFintype β)
        pure (P b)) True
  -- Rewrite the left-hand `do` block as successive `PMF.map`s.
  -- First push forward along `e`, then along `P`.
  --
  -- `do let a ← p; pure (P (e a))` is `p.map (P ∘ e)`.
  -- `PMF.map_comp` converts it to `((p.map e).map P)`.
  have hcomp :
      (PMF.uniformOfFintype α).map (P ∘ e) = ((PMF.uniformOfFintype α).map e).map P := by
    simpa [Function.comp] using
      (PMF.map_comp (p := PMF.uniformOfFintype α) (f := e) (g := P)).symm
  -- Apply both sides to `True`, then use `hmap`.
  -- Finally, recognize the right-hand side as the original `do` block.
  simpa using congrArg (fun q : PMF Prop => q True) (by
    calc
      (PMF.uniformOfFintype α).map (P ∘ e)
          = ((PMF.uniformOfFintype α).map e).map P := hcomp
      _ = (PMF.uniformOfFintype β).map P := by simp [hmap]
    )

theorem divergence_attains {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [DecidableEq F]
  {U V : Set (ι → F)} [Nonempty U] [Nonempty V] [Fintype V] :
  ∃ u ∈ U, δᵣ'(u, V) = divergence U V := by
  classical
  have hDeltas : (possibleDeltas U V).Nonempty := by
    rcases (show Nonempty U from inferInstance) with ⟨u⟩
    refine ⟨δᵣ'(u.1, V), ?_⟩
    exact ⟨u.1, u.2, rfl⟩
  have hmem : divergence U V ∈ possibleDeltas U V := by
    -- rewrite `divergence` using nonemptiness of `possibleDeltas`
    simp only [divergence, hDeltas, ↓reduceDIte]
    -- provide the `Fintype` instance needed for `toFinset` lemmas
    letI : Fintype (possibleDeltas U V) := @Fintype.ofFinite _ finite_possibleDeltas
    exact (Set.mem_toFinset (s := possibleDeltas U V)
      (a := (possibleDeltas U V).toFinset.max' (Set.toFinset_nonempty.2 hDeltas))).1
        (Finset.max'_mem (s := (possibleDeltas U V).toFinset)
          (H := Set.toFinset_nonempty.2 hDeltas))
  simpa [possibleDeltas] using hmem

open scoped ProbabilityTheory in
theorem proximity_gap_affineSubspace {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Fintype F] [Field F] [DecidableEq F]
  {deg : ℕ} {domain : ι ↪ F}
  (U : AffineSubspace F (ι → F)) [Nonempty U] {δ : ℝ≥0}
  (_hδ : δ < 1 - ReedSolomon.sqrtRate deg domain)
  (hPG : ∀ {k t : ℕ} [NeZero k] [NeZero t] (C : Fin t → (Fin k → (ι → F))),
    ProximityGap.δ_ε_proximityGap
      (ReedSolomon.toFinset domain deg)
      (Affine.AffSpanFinsetCollection C) δ (errorBound δ deg domain)) :
  Xor'
    (Pr_{let u ← $ᵖ U}[Code.relDistFromCode u (RScodeSet domain deg) ≤ δ] = 1)
    (Pr_{let u ← $ᵖ U}[Code.relDistFromCode u (RScodeSet domain deg) ≤ δ] ≤
      errorBound δ deg domain) := by
  classical
  -- Let k be the cardinality of the affine subspace U
  let k : ℕ := Fintype.card U
  haveI hk : NeZero k := ⟨Fintype.card_ne_zero⟩
  -- Enumerate U by Fin k
  let e : Fin k ≃ U := (Fintype.equivFin U).symm
  let u : Fin k → (ι → F) := fun i => (e i : U)
  -- Turn this into a (trivial) collection of one affine span
  let C : Fin 1 → (Fin k → (ι → F)) := fun _ => u
  -- Apply ProximityGap Theorem 1.2 via hypothesis
  have hpg : ProximityGap.δ_ε_proximityGap
      (ReedSolomon.toFinset domain deg)
      (Affine.AffSpanFinsetCollection C)
      δ
      (errorBound δ deg domain) :=
    hPG C
  -- Specialize to the unique element of the collection
  let S : Finset (ι → F) := Affine.AffSpanFinset (C 0)
  have hS_mem : S ∈ Affine.AffSpanFinsetCollection C := by
    refine ⟨0, rfl⟩
  -- Provide a nonempty instance for S
  haveI hS_nonempty : Nonempty S := by
    rcases (show Nonempty U from inferInstance) with ⟨x⟩
    -- show that x lies in the affine span of the enumerated set
    have hx_mem_image : (x : ι → F) ∈ (Finset.univ.image u : Finset (ι → F)) := by
      refine Finset.mem_image.mpr ?_
      refine ⟨e.symm x, by simp, ?_⟩
      simp [u]
    have hx_mem_affineSpan :
        (x : ι → F) ∈ affineSpan F (Finset.univ.image u : Set (ι → F)) :=
      (subset_affineSpan (k := F)
        (s := (Finset.univ.image u : Set (ι → F)))) hx_mem_image
    -- convert membership in the carrier set to membership in the finset S
    have hx_mem_S : (x : ι → F) ∈ S := by
      dsimp [S, Affine.AffSpanFinset]
      exact (Affine.AffSpanSet.instFinite (u := C 0)).mem_toFinset.2 (by
        dsimp [Affine.AffSpanSet]
        simpa using hx_mem_affineSpan)
    exact ⟨⟨(x : ι → F), hx_mem_S⟩⟩
  have hxorS :
      Xor'
        (Pr_{let x ← $ᵖ S}[δᵣ(x.val, (ReedSolomon.toFinset domain deg)) ≤ δ] = 1)
        (Pr_{let x ← $ᵖ S}[δᵣ(x.val, (ReedSolomon.toFinset domain deg)) ≤ δ] ≤
          errorBound δ deg domain) := by
    simpa using hpg S hS_mem
  -- The enumeration hits exactly the carrier of U
  have hu_image : (Finset.univ.image u : Set (ι → F)) = (U : Set (ι → F)) := by
    ext x
    constructor
    · intro hx
      have hx' : x ∈ (Finset.univ.image u : Finset (ι → F)) := by
        simpa using hx
      rcases Finset.mem_image.mp hx' with ⟨i, -, rfl⟩
      simp [u]
    · intro hx
      have hx' : x ∈ (Finset.univ.image u : Finset (ι → F)) := by
        refine Finset.mem_image.mpr ?_
        refine ⟨e.symm ⟨x, hx⟩, by simp, ?_⟩
        simp [u]
      simpa using hx'
  have h_affineSpan : affineSpan F (Finset.univ.image u : Set (ι → F)) = U := by
    calc
      affineSpan F (Finset.univ.image u : Set (ι → F)) = affineSpan F (U : Set (ι → F)) := by
        simp [hu_image]
      _ = U := by
        simp
  have h_AffSpanSet : Affine.AffSpanSet (U := C 0) = (U : Set (ι → F)) := by
    unfold Affine.AffSpanSet
    dsimp [C]
    rw [h_affineSpan]
    rfl
  have hUS : (U : Set (ι → F)) = (S : Set (ι → F)) := by
    have hScoe : (S : Set (ι → F)) = Affine.AffSpanSet (U := C 0) := by
      dsimp [S, Affine.AffSpanFinset]
      -- coercion of `toFinset` gives back the set
      simp
    simpa [h_AffSpanSet] using hScoe.symm
  -- Build an equivalence between U and S (identity on the underlying word)
  let eUS : U ≃ S :=
    { toFun := fun x =>
        ⟨(x : ι → F), by
          have hxU : (x : ι → F) ∈ (U : Set (ι → F)) := x.property
          have hxS : (x : ι → F) ∈ (S : Set (ι → F)) := by
            rw [hUS.symm]
            exact hxU
          simpa using hxS⟩
      invFun := fun x =>
        ⟨(x : ι → F), by
          have hxS : (x : ι → F) ∈ (S : Set (ι → F)) := by
            simp
          have hxU : (x : ι → F) ∈ (U : Set (ι → F)) := by
            rw [hUS]
            exact hxS
          simpa using hxU⟩
      left_inv := by
        intro x
        ext
        rfl
      right_inv := by
        intro x
        ext
        rfl }
  -- Transfer the probability statement from S to U
  have hPr :
      Pr_{let u ← $ᵖ U}[Code.relDistFromCode u (RScodeSet domain deg) ≤ δ] =
        Pr_{let x ← $ᵖ S}[Code.relDistFromCode x (RScodeSet domain deg) ≤ δ] := by
    simpa [eUS] using
      (Pr_uniform_equiv (α := U) (β := S) eUS
        (fun x : S => Code.relDistFromCode x (RScodeSet domain deg) ≤ δ))
  -- Rewrite the XOR statement for S into the desired one for U
  have hxorS' :
      Xor'
        (Pr_{let x ← $ᵖ S}[Code.relDistFromCode x (RScodeSet domain deg) ≤ δ] = 1)
        (Pr_{let x ← $ᵖ S}[Code.relDistFromCode x (RScodeSet domain deg) ≤ δ] ≤
          errorBound δ deg domain) := by
    simpa [ReedSolomon.toFinset, ReedSolomon.RScodeSet] using hxorS
  -- Finish by rewriting the goal using hPr
  rw [hPr]
  exact hxorS'

theorem real_sqrt_div_10_pow_two {r : ℝ≥0} :
    (Real.sqrt (r : ℝ) / 10) ^ 2 = (r : ℝ) / 100 := by
  have hr : (0 : ℝ) ≤ (r : ℝ) := r.2
  calc
    (Real.sqrt (r : ℝ) / 10) ^ 2 = (Real.sqrt (r : ℝ)) ^ 2 / (10 : ℝ) ^ 2 := by
      simp [div_pow]
    _ = (r : ℝ) / 100 := by
      have h10 : (10 : ℝ) ^ 2 = (100 : ℝ) := by
        norm_num
      -- rewrite sqrt and 10^2
      simp [Real.sq_sqrt hr, h10]

theorem real_sqrt_rate_eq_coe_nnreal_sqrt {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F]
  {deg : ℕ} {domain : ι ↪ F} :
  Real.sqrt ((LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) : ℝ)
    = (((LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0).sqrt : ℝ≥0) : ℝ) := by
  simp

theorem reedSolomon_dim_le_deg {ι : Type} [Nonempty ι]
    {F : Type} [Field F]
  {deg : ℕ} {domain : ι ↪ F} :
  LinearCode.dim (ReedSolomon.code domain deg) ≤ deg := by
  classical
  rw [LinearCode.dim]
  -- unfold the definition of the RS code
  simp only [ReedSolomon.code]
  have hle : Module.finrank F
        ((Polynomial.degreeLT F deg).map (ReedSolomon.evalOnPoints (F := F) domain)) ≤
      Module.finrank F (Polynomial.degreeLT F deg) := by
    simpa using
      (Submodule.finrank_map_le (f := ReedSolomon.evalOnPoints (F := F) domain)
        (p := Polynomial.degreeLT F deg))
  simpa [Polynomial.finrank_degreeLT_n] using hle

theorem reedSolomon_rate_le_one {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F]
  {deg : ℕ} {domain : ι ↪ F} :
  LinearCode.rate (ReedSolomon.code domain deg) ≤ 1 := by
  classical
  unfold LinearCode.rate
  refine div_le_one_of_le₀ ?_ (by
    simp)
  have hdim_le_len_nat :
      LinearCode.dim (ReedSolomon.code domain deg) ≤
        LinearCode.length (ReedSolomon.code domain deg) := by
    unfold LinearCode.dim LinearCode.length
    have h_le :
        Module.finrank F (ReedSolomon.code domain deg) ≤ Module.finrank F (ι → F) := by
      simpa using
        (Submodule.finrank_le (R := F) (M := (ι → F)) (ReedSolomon.code domain deg))
    simpa using h_le
  exact_mod_cast hdim_le_len_nat

theorem reedSolomon_rate_mul_card_eq_dim {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F]
  {deg : ℕ} {domain : ι ↪ F} :
  (Fintype.card ι : ℝ≥0) * (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)
    = (LinearCode.dim (ReedSolomon.code domain deg) : ℝ≥0) := by
  classical
  have hn : (Fintype.card ι : ℝ≥0) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := ι))
  -- unfold the definitions
  simp only [ne_eq, Nat.cast_eq_zero, Fintype.card_ne_zero, not_false_eq_true,
    LinearCode.rate, LinearCode.dim, ModuleCode, LinearCode.length,
    NNRat.cast_div, NNRat.cast_natCast] at *
  -- goal should now be `n * (d / n) = d`
  -- rewrite into `(n * d) / n` and cancel
  -- (the simp above turned the main goal into the following one)
  --
  -- Note: `mul_div_assoc` is used in the reverse direction.
  rw [← mul_div_assoc]
  simp

theorem reedSolomon_rate_mul_card_le_deg {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F]
  {deg : ℕ} {domain : ι ↪ F} :
  (Fintype.card ι : ℝ≥0) * (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)
    ≤ (deg : ℝ≥0) := by
  -- Rewrite the rate expression in terms of the dimension
  rw [reedSolomon_rate_mul_card_eq_dim (deg := deg) (domain := domain)]
  -- Cast the dimension bound to `ℝ≥0`
  exact_mod_cast (reedSolomon_dim_le_deg (deg := deg) (domain := domain))


theorem reedSolomon_rate_pos {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F]
  {deg : ℕ} {domain : ι ↪ F}
  (hdeg : 0 < deg) :
  0 < LinearCode.rate (ReedSolomon.code domain deg) := by
  classical
  haveI : NeZero deg := ⟨Nat.ne_of_gt hdeg⟩
  have hmem : ReedSolomon.constantCode (1 : F) ι ∈ ReedSolomon.code domain deg := by
    simp
  let c : ReedSolomon.code domain deg := ⟨ReedSolomon.constantCode (1 : F) ι, hmem⟩
  have hc_ne_zero : c ≠ 0 := by
    intro hc
    have hval : ReedSolomon.constantCode (1 : F) ι = 0 := by
      simpa [c] using congrArg (fun x : ReedSolomon.code domain deg => (x : ι → F)) hc
    have : (1 : F) = 0 :=
      (ReedSolomon.constantCode_eq_ofNat_zero_iff (ι := ι) (x := (1 : F))).1 hval
    exact one_ne_zero this
  haveI : Nontrivial (ReedSolomon.code domain deg) := by
    refine ⟨c, 0, hc_ne_zero⟩
  have hdim_pos : 0 < LinearCode.dim (ReedSolomon.code domain deg) := by
    -- check lemma exists
    simpa [LinearCode.dim] using (Module.finrank_pos (R := F) (M := ReedSolomon.code domain deg))
  have hlen_pos : 0 < LinearCode.length (ReedSolomon.code domain deg) := by
    simp [LinearCode.length]
  have hdim_pos' : (0 : ℚ≥0) < (LinearCode.dim (ReedSolomon.code domain deg) : ℚ≥0) := by
    exact_mod_cast hdim_pos
  have hlen_pos' : (0 : ℚ≥0) < (LinearCode.length (ReedSolomon.code domain deg) : ℚ≥0) := by
    exact_mod_cast hlen_pos
  have : (0 : ℚ≥0) <
      (LinearCode.dim (ReedSolomon.code domain deg) : ℚ≥0) /
        (LinearCode.length (ReedSolomon.code domain deg) : ℚ≥0) :=
    div_pos hdim_pos' hlen_pos'
  simpa [LinearCode.rate] using this

theorem errorBound_ge_const {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Fintype F] [Field F]
  {deg : ℕ} {domain : ι ↪ F}
  (hdeg : 0 < deg)
  {δ : ℝ≥0}
  (hδ : δ < 1 - ReedSolomon.sqrtRate deg domain) :
  (Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0) ≤ errorBound δ deg domain := by
  classical
  set r : ℝ≥0 := (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) with hr
  by_cases hUD : δ ≤ (1 - r) / 2
  · simp [ProximityGap.errorBound, ←hr, hUD]
  · have hlt : (1 - r) / 2 < δ := lt_of_not_ge hUD
    have hδ' : δ < 1 - r.sqrt := by
      simpa [ReedSolomon.sqrtRate, ←hr] using hδ
    have hmem2 : (1 - r) / 2 < δ ∧ δ < 1 - r.sqrt := ⟨hlt, hδ'⟩
    simp only [errorBound, ← hr, Set.mem_Icc, zero_le, hUD, and_false,
      ↓reduceIte, Set.mem_Ioo, hmem2, and_self, coe_pow, NNReal.coe_natCast,
      coe_min, NNReal.coe_div, Real.coe_sqrt, NNReal.coe_ofNat, ge_iff_le]
    change (↑(Fintype.card ι) / ↑(Fintype.card F) : ℝ) ≤
      (↑deg ^ 2 : ℝ) /
        ((2 * min (↑(1 - sqrt r - δ) : ℝ) (Real.sqrt (r : ℝ) / 20)) ^ 7 *
          (Fintype.card F : ℝ))
    have hqpos : (0 : ℝ) < (Fintype.card F : ℝ) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
    have hqne : (Fintype.card F : ℝ) ≠ 0 := ne_of_gt hqpos
    field_simp [hqne]
    set m : ℝ := min (↑(1 - sqrt r - δ) : ℝ) (Real.sqrt (r : ℝ) / 20) with hm
    simp only [ge_iff_le]
    have hm_le : m ≤ Real.sqrt (r : ℝ) / 20 := by
      simp [hm]
    have hm_nonneg : 0 ≤ m := by
      have h1 : (0 : ℝ) ≤ (↑(1 - sqrt r - δ) : ℝ) := by
        exact_mod_cast (show (0 : ℝ≥0) ≤ (1 - sqrt r - δ) from zero_le _)
      have h2 : (0 : ℝ) ≤ Real.sqrt (r : ℝ) / 20 := by
        have : (0 : ℝ) ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
        nlinarith
      have : (0 : ℝ) ≤ min (↑(1 - sqrt r - δ) : ℝ) (Real.sqrt (r : ℝ) / 20) :=
        le_min h1 h2
      simpa [hm] using this
    have hr_le_one : r ≤ 1 := by
      have h := reedSolomon_rate_le_one (deg := deg) (domain := domain)
      have : (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) ≤ 1 := by
        exact_mod_cast h
      simpa [hr] using this
    have h_sqrt_le_one : Real.sqrt (r : ℝ) ≤ 1 := by
      have : (r : ℝ) ≤ (1 : ℝ) := by
        exact_mod_cast hr_le_one
      have := Real.sqrt_le_sqrt this
      simpa using this
    have h2m_le_one : 2 * m ≤ 1 := by
      have h2m_le_sqrt10 : 2 * m ≤ Real.sqrt (r : ℝ) / 10 := by
        have : 2 * m ≤ 2 * (Real.sqrt (r : ℝ) / 20) := by
          gcongr
        nlinarith
      have hsqrt10_le_one : Real.sqrt (r : ℝ) / 10 ≤ 1 := by
        have : Real.sqrt (r : ℝ) / 10 ≤ 1 / 10 := by
          nlinarith [h_sqrt_le_one]
        linarith
      exact h2m_le_sqrt10.trans hsqrt10_le_one
    have h2m_nonneg : 0 ≤ 2 * m := by nlinarith [hm_nonneg]
    have hpow7_le_pow2 : (2 * m) ^ 7 ≤ (2 * m) ^ 2 := by
      exact pow_le_pow_of_le_one h2m_nonneg h2m_le_one (by decide : (2 : ℕ) ≤ 7)
    have hpow2_le : (2 * m) ^ 2 ≤ (Real.sqrt (r : ℝ) / 10) ^ 2 := by
      have hle : 2 * m ≤ Real.sqrt (r : ℝ) / 10 := by
        have : 2 * m ≤ 2 * (Real.sqrt (r : ℝ) / 20) := by
          gcongr
        nlinarith
      have hsqrt10_nonneg : 0 ≤ Real.sqrt (r : ℝ) / 10 := by
        have : 0 ≤ Real.sqrt (r : ℝ) := Real.sqrt_nonneg _
        nlinarith
      have habs : |2 * m| ≤ |Real.sqrt (r : ℝ) / 10| := by
        have ha : 0 ≤ 2 * m := h2m_nonneg
        have hb : 0 ≤ Real.sqrt (r : ℝ) / 10 := hsqrt10_nonneg
        simpa [abs_of_nonneg ha, abs_of_nonneg hb] using hle
      have := (sq_le_sq).2 habs
      simpa using this
    have hsqrt_sq : (Real.sqrt (r : ℝ) / 10) ^ 2 = (r : ℝ) / 100 := by
      simpa using (real_sqrt_div_10_pow_two (r := r))
    have h2m_pow7_le : (2 * m) ^ 7 ≤ (r : ℝ) / 100 := by
      calc
        (2 * m) ^ 7 ≤ (2 * m) ^ 2 := hpow7_le_pow2
        _ ≤ (Real.sqrt (r : ℝ) / 10) ^ 2 := hpow2_le
        _ = (r : ℝ) / 100 := hsqrt_sq
    -- show m>0
    have hr_pos : (0 : ℝ) < (r : ℝ) := by
      have hrate_posQ : (0 : ℚ≥0) < LinearCode.rate (ReedSolomon.code domain deg) :=
        reedSolomon_rate_pos (deg := deg) (domain := domain) hdeg
      have hrate_pos :
          (0 : ℝ≥0) < (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) := by
        exact_mod_cast hrate_posQ
      have : (0 : ℝ≥0) < r := by
        simpa [hr] using hrate_pos
      exact_mod_cast this
    have hm_pos : 0 < m := by
      have hA_nnreal : (0 : ℝ≥0) < (1 - sqrt r - δ) := tsub_pos_of_lt hδ'
      have hA : (0 : ℝ) < (↑(1 - sqrt r - δ) : ℝ) := by exact_mod_cast hA_nnreal
      have hB : (0 : ℝ) < Real.sqrt (r : ℝ) / 20 := by
        have hsqrt_pos : (0 : ℝ) < Real.sqrt (r : ℝ) := (Real.sqrt_pos).2 hr_pos
        nlinarith
      have : 0 < min (↑(1 - sqrt r - δ) : ℝ) (Real.sqrt (r : ℝ) / 20) := lt_min hA hB
      simpa [hm] using this
    have hm7_pos : 0 < m ^ 7 := by
      simpa using (pow_pos hm_pos 7)
    -- main inequality after clearing denominators
    have hmul_goal : (↑(Fintype.card ι) * 2 ^ 7) * m ^ 7 ≤ (↑deg ^ 2 : ℝ) := by
      have h2pow_mul : (2 : ℝ) ^ 7 * m ^ 7 ≤ (r : ℝ) / 100 := by
        simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm] using h2m_pow7_le
      have hcard_nonneg : 0 ≤ (↑(Fintype.card ι) : ℝ) := by
        exact_mod_cast (Nat.zero_le (Fintype.card ι))
      have hstep1 : (↑(Fintype.card ι) : ℝ) * ((2 : ℝ) ^ 7 * m ^ 7) ≤
          (↑(Fintype.card ι) : ℝ) * ((r : ℝ) / 100) := by
        exact mul_le_mul_of_nonneg_left h2pow_mul hcard_nonneg
      have hrmul_nnreal : (Fintype.card ι : ℝ≥0) * r ≤ (deg : ℝ≥0) := by
        simpa [hr] using
          (reedSolomon_rate_mul_card_le_deg (deg := deg) (domain := domain))
      have hrmul : (↑(Fintype.card ι) : ℝ) * (r : ℝ) ≤ (deg : ℝ) := by
        exact_mod_cast hrmul_nnreal
      have hrmul_div : (↑(Fintype.card ι) : ℝ) * ((r : ℝ) / 100) ≤ (deg : ℝ) / 100 := by
        nlinarith [hrmul]
      have hdeg_sq : (deg : ℝ) / 100 ≤ (↑deg ^ 2 : ℝ) := by
        have hdeg1_nat : 1 ≤ deg := Nat.one_le_of_lt hdeg
        have hdeg1 : (1 : ℝ) ≤ (deg : ℝ) := by
          exact_mod_cast hdeg1_nat
        have hdeg_nonneg : 0 ≤ (deg : ℝ) := by
          exact_mod_cast (Nat.zero_le deg)
        have hdeg_le_sq : (deg : ℝ) ≤ (deg : ℝ) ^ 2 := by
          nlinarith [hdeg1]
        have hdiv_le : (deg : ℝ) / 100 ≤ (deg : ℝ) := by
          nlinarith [hdeg_nonneg]
        -- rewrite `(deg : ℝ) ^ 2` as `↑deg ^ 2` at the end
        have : (deg : ℝ) / 100 ≤ (deg : ℝ) ^ 2 := hdiv_le.trans hdeg_le_sq
        simpa using this
      -- combine
      have hfinal : (↑(Fintype.card ι) : ℝ) * ((2 : ℝ) ^ 7 * m ^ 7) ≤ (↑deg ^ 2 : ℝ) :=
        hstep1.trans (hrmul_div.trans hdeg_sq)
      -- rearrange into the exact goal form
      -- goal: (↑cardI * 2^7) * m^7 ≤ deg^2
      -- current: ↑cardI * (2^7 * m^7) ≤ deg^2
      simpa [mul_assoc, mul_left_comm, mul_comm] using hfinal
    have : (↑(Fintype.card ι) * 2 ^ 7 : ℝ) ≤ (↑deg ^ 2 : ℝ) / m ^ 7 := by
      exact (le_div_iff₀ hm7_pos).2 (by
        simpa [mul_assoc] using hmul_goal)
    simpa [mul_assoc] using this


theorem errorBound_johnson_mono {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Fintype F] [Field F]
  {deg : ℕ} {domain : ι ↪ F}
  (hdeg : 0 < deg)
  {δ₁ δ₂ : ℝ≥0}
  (hδ : δ₁ ≤ δ₂)
  (hδ₁ : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ₁)
  (hδ₂ : δ₂ < 1 - ReedSolomon.sqrtRate deg domain) :
  errorBound δ₁ deg domain ≤ errorBound δ₂ deg domain := by
  classical
  -- threshold t = (1 - rate)/2
  set t : ℝ≥0 := (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2
  have ht1 : t < δ₁ := by simpa [t] using hδ₁
  have ht2 : t < δ₂ := lt_of_lt_of_le ht1 hδ
  -- rewrite the Johnson upper bound using `sqrtRate`
  have hδ₂' : δ₂ < 1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0).sqrt := by
    simpa [ReedSolomon.sqrtRate] using hδ₂
  have hδ₁' : δ₁ < 1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0).sqrt :=
    lt_of_le_of_lt hδ hδ₂'
  -- unfold `errorBound` into the Johnson branch for both δ₁ and δ₂
  simp only [errorBound, Set.mem_Icc, zero_le, (not_le_of_gt ht1), and_false,
    ↓reduceIte, Set.mem_Ioo, ht1, hδ₁', and_self, coe_pow, NNReal.coe_natCast,
    coe_min, NNReal.coe_div, Real.coe_sqrt, NNReal.coe_ofNat,
    (not_le_of_gt ht2), ht2, hδ₂', ge_iff_le, t]
  -- Turn the subtype inequality into a plain real inequality.
  change (↑deg ^ 2 /
        ((2 * min
          (↑(1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0).sqrt - δ₁) : ℝ)
          (Real.sqrt ((LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) : ℝ) / 20)) ^ 7
          * (Fintype.card F : ℝ)))
      ≤
      (↑deg ^ 2 /
        ((2 * min
          (↑(1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0).sqrt - δ₂) : ℝ)
          (Real.sqrt ((LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) : ℝ) / 20)) ^ 7
          * (Fintype.card F : ℝ)))
  -- Abbreviate the min-arguments exactly as they appear.
  set A₁ : ℝ :=
    (↑(1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0).sqrt - δ₁) : ℝ)
  set A₂ : ℝ :=
    (↑(1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0).sqrt - δ₂) : ℝ)
  set B : ℝ :=
    (Real.sqrt ((LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) : ℝ) / 20)
  have htsub : (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0).sqrt - δ₂)
      ≤ (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0).sqrt - δ₁) := by
    -- antitonicity of `tsub` in the second argument
    simpa [sub_eq_add_neg, tsub_tsub] using
      (tsub_le_tsub_left hδ (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0).sqrt))
  have hA : A₂ ≤ A₁ := by
    exact_mod_cast htsub
  have hmin : min A₂ B ≤ min A₁ B := min_le_min_right _ hA
  have hden : (2 * min A₂ B) ^ 7 * (Fintype.card F : ℝ)
        ≤ (2 * min A₁ B) ^ 7 * (Fintype.card F : ℝ) := by
    have h2 : 2 * min A₂ B ≤ 2 * min A₁ B := by gcongr
    have hp : (2 * min A₂ B) ^ 7 ≤ (2 * min A₁ B) ^ 7 :=
      pow_le_pow_left₀ (by positivity) h2 7
    exact mul_le_mul_of_nonneg_right hp (by positivity)
  have hdenpos : 0 < (2 * min A₂ B) ^ 7 * (Fintype.card F : ℝ) := by
    -- show `min A₂ B > 0`, hence the whole product is positive
    have hratepos_nn : 0 < LinearCode.rate (ReedSolomon.code domain deg) :=
      reedSolomon_rate_pos (ι := ι) (F := F) (deg := deg) (domain := domain) hdeg
    have hratepos : 0 < (LinearCode.rate (ReedSolomon.code domain deg) : ℝ) := by
      exact_mod_cast hratepos_nn
    have hBpos : 0 < B := by
      -- `B = sqrt(rate)/20`
      have : 0 < Real.sqrt
          ((LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) : ℝ) := by
        -- rate is positive
        have hratepos' :
            0 < ((LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) : ℝ) := by
          exact_mod_cast hratepos_nn
        exact Real.sqrt_pos.2 hratepos'
      have : 0 < Real.sqrt
          ((LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0) : ℝ) / 20 := by
        exact div_pos this (by norm_num)
      simpa [B] using this
    have hA2pos : 0 < A₂ := by
      -- from `δ₂ < 1 - sqrtRate`, the NNReal subtraction is positive, then cast
      have hA2pos_nn :
          0 < (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0).sqrt - δ₂) := by
        simpa [sub_eq_add_neg, tsub_tsub] using (tsub_pos_of_lt hδ₂')
      -- cast to ℝ
      have : (0 : ℝ) <
          (↑(1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0).sqrt - δ₂) : ℝ) := by
        exact_mod_cast hA2pos_nn
      simpa [A₂] using this
    have hminpos : 0 < min A₂ B := lt_min hA2pos hBpos
    have hbase : 0 < 2 * min A₂ B := by
      have : (0 : ℝ) < (2 : ℝ) := by norm_num
      exact mul_pos this hminpos
    have hpowpos : 0 < (2 * min A₂ B) ^ 7 := pow_pos hbase 7
    have hcardpos : 0 < (Fintype.card F : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.2 (inferInstance : Nonempty F))
    exact mul_pos hpowpos hcardpos
  -- Numerator is nonnegative.
  have hnum_nonneg : 0 ≤ (↑deg ^ 2 : ℝ) := by positivity
  -- Denominator antitonicity.
  exact div_le_div_of_nonneg_left hnum_nonneg hdenpos hden


theorem errorBound_mono {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Fintype F] [Field F]
  {deg : ℕ} {domain : ι ↪ F}
  (hdeg : 0 < deg)
  {δ₁ δ₂ : ℝ≥0}
  (hδ : δ₁ ≤ δ₂)
  (hδ₂ : δ₂ < 1 - ReedSolomon.sqrtRate deg domain) :
  errorBound δ₁ deg domain ≤ errorBound δ₂ deg domain := by
  classical
  let ρ : ℝ≥0 := (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)
  let t : ℝ≥0 := (1 - ρ) / 2
  have ht_def : t = (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 := by
    simp [t, ρ]
  by_cases h2 : δ₂ ≤ t
  · have h1 : δ₁ ≤ t := le_trans hδ h2
    -- both in the constant branch
    simp [ProximityGap.errorBound, t, ρ, Set.mem_Icc, h1, h2]
  · have ht2 : t < δ₂ := lt_of_not_ge h2
    by_cases h1 : δ₁ ≤ t
    · -- δ₁ constant, δ₂ Johnson
      have hconst :
          (Fintype.card ι : ℝ≥0) / (Fintype.card F : ℝ≥0) ≤ errorBound δ₂ deg domain :=
        errorBound_ge_const (deg := deg) (domain := domain) hdeg (δ := δ₂) (hδ := hδ₂)
      -- reduce goal to constant ≤ errorBound δ₂
      simpa [ProximityGap.errorBound, t, ρ, Set.mem_Icc, Set.mem_Ioo, h1, h2, ht2] using hconst
    · have ht1 : t < δ₁ := lt_of_not_ge h1
      -- both in Johnson regime
      have hmono : errorBound δ₁ deg domain ≤ errorBound δ₂ deg domain := by
        -- use the provided monotonicity lemma in the Johnson branch
        have ht1' :
            (1 - (LinearCode.rate (ReedSolomon.code domain deg) : ℝ≥0)) / 2 < δ₁ := by
          simpa [t, ρ] using ht1
        exact errorBound_johnson_mono (deg := deg) (domain := domain) hdeg
          (δ₁ := δ₁) (δ₂ := δ₂) hδ ht1' hδ₂
      simpa [ProximityGap.errorBound, t, ρ, Set.mem_Icc, Set.mem_Ioo, h1, h2, ht1, ht2] using hmono

theorem relDistFromCode'_le_divergence {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [DecidableEq F]
  {U V : Set (ι → F)} [Nonempty U] [Nonempty V] [Fintype V]
  (u : ι → F) (hu : u ∈ U) :
  δᵣ'(u, V) ≤ divergence U V := by
  classical
  have hδ : δᵣ'(u, V) ∈ possibleDeltas U V := by
    simp only [possibleDeltas, Set.mem_setOf_eq]
    exact ⟨u, hu, rfl⟩
  have hnonempty : (possibleDeltas U V).Nonempty := ⟨δᵣ'(u, V), hδ⟩
  -- Unfold `divergence` using the fact that `possibleDeltas U V` is nonempty.
  simp only [divergence, hnonempty, ↓reduceDIte, ge_iff_le]
  -- Now `divergence U V` is the `max'` of `(possibleDeltas U V).toFinset`.
  refine Finset.le_max' _ _ ?_
  -- Show `δᵣ'(u, V)` is one of the possible deltas.
  simpa [Set.mem_toFinset] using hδ

theorem divergence_pred_spec {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [DecidableEq F]
  {U V : Set (ι → F)} [Nonempty U] [Nonempty V] [Fintype V]
  (hdiv_pos : 0 < (divergence U V : ℝ≥0)) :
  ∃ δ : ℚ≥0, δ < divergence U V ∧
    (∀ u ∈ U, δᵣ'(u, V) ≠ divergence U V ↔ δᵣ'(u, V) ≤ δ) := by
  classical
  haveI : Fintype (possibleDeltas U V) :=
    @Fintype.ofFinite _ (finite_possibleDeltas (U := U) (V := V))
  let δ' : ℚ≥0 := divergence U V
  let S : Finset ℚ≥0 := (possibleDeltas U V).toFinset
  let Slt : Finset ℚ≥0 := S.filter (fun d => d < δ')
  let δ : ℚ≥0 := if h : Slt.Nonempty then Slt.max' h else 0
  have hδlt : δ < δ' := by
    by_cases h : Slt.Nonempty
    · have hmem : δ ∈ Slt := by
        simpa [δ, h] using (Finset.max'_mem (s := Slt) h)
      exact (Finset.mem_filter.mp hmem).2
    · have hposR : (0 : ℝ≥0) < (δ' : ℝ≥0) := by
        simpa [δ'] using hdiv_pos
      have hposQ : (0 : ℚ≥0) < δ' := by
        exact (NNRat.cast_lt (K := ℝ≥0) (p := (0 : ℚ≥0)) (q := δ')).1
          (by simpa using hposR)
      simpa [δ, h] using hposQ
  refine ⟨δ, ?_, ?_⟩
  · simpa [δ'] using hδlt
  · intro u hu
    have hu_le : δᵣ'(u, V) ≤ divergence U V :=
      relDistFromCode'_le_divergence (U := U) (V := V) u hu
    have hu_le' : δᵣ'(u, V) ≤ δ' := by simpa [δ'] using hu_le
    have hne_iff_lt : δᵣ'(u, V) ≠ divergence U V ↔ δᵣ'(u, V) < δ' := by
      constructor
      · intro hne
        have hne' : δᵣ'(u, V) ≠ δ' := by simpa [δ'] using hne
        exact lt_of_le_of_ne hu_le' hne'
      · intro hlt heq
        have : δᵣ'(u, V) = δ' := by simpa [δ'] using heq
        exact (lt_irrefl _ (this ▸ hlt))
    have hlt_iff_leδ : δᵣ'(u, V) < δ' ↔ δᵣ'(u, V) ≤ δ := by
      constructor
      · intro hlt
        have hmemS : δᵣ'(u, V) ∈ S := by
          -- membership in possibleDeltas
          have : δᵣ'(u, V) ∈ possibleDeltas U V := by
            refine ⟨u, hu, rfl⟩
          simpa [S] using (Set.mem_toFinset (s := possibleDeltas U V) (a := δᵣ'(u, V))).2 this
        have hmemSlt : δᵣ'(u, V) ∈ Slt := by
          exact Finset.mem_filter.2 ⟨hmemS, hlt⟩
        have hnonempty : Slt.Nonempty := ⟨δᵣ'(u, V), hmemSlt⟩
        have hle_max : δᵣ'(u, V) ≤ Slt.max' hnonempty :=
          Finset.le_max' (s := Slt) (x := δᵣ'(u, V)) hmemSlt
        -- unfold δ
        simpa [δ, hnonempty] using hle_max
      · intro hle
        exact lt_of_le_of_lt hle hδlt
    -- combine
    constructor
    · intro hne
      have : δᵣ'(u, V) < δ' := (hne_iff_lt).1 hne
      exact (hlt_iff_leδ).1 this
    · intro hle
      have : δᵣ'(u, V) < δ' := (hlt_iff_leδ).2 hle
      exact (hne_iff_lt).2 this


open scoped ProbabilityTheory in
theorem concentration_bounds {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Fintype F] [Field F] [DecidableEq F]
  {deg : ℕ} {domain : ι ↪ F}
  (hdeg : 0 < deg)
  {U : AffineSubspace F (ι → F)} [Nonempty U]
  (hdiv_pos : 0 < (divergence U (RScodeSet domain deg) : ℝ≥0))
  (hdiv_lt : (divergence U (RScodeSet domain deg) : ℝ≥0) <
    1 - ReedSolomon.sqrtRate deg domain)
  (hPG : ∀ {δ : ℝ≥0}, 0 < δ → δ < 1 - ReedSolomon.sqrtRate deg domain →
    ∀ {k t : ℕ} [NeZero k] [NeZero t] (C : Fin t → (Fin k → (ι → F))),
    ProximityGap.δ_ε_proximityGap
      (ReedSolomon.toFinset domain deg)
      (Affine.AffSpanFinsetCollection C) δ (errorBound δ deg domain)) :
    let δ' := divergence U (RScodeSet domain deg)
    Pr_{let u ← $ᵖ U}[Code.relDistFromCode u (RScodeSet domain deg) ≠ δ']
      ≤ errorBound δ' deg domain := by
  classical
  dsimp
  -- Abbreviate the Reed–Solomon code set
  set V : Set (ι → F) := RScodeSet domain deg
  -- Obtain the proximity threshold δ < δ' and the pointwise characterization
  obtain ⟨δ, hδlt, hpred⟩ :=
    divergence_pred_spec (U := (U : Set (ι → F))) (V := V) (hdiv_pos := hdiv_pos)
  -- Abbreviate δ' = divergence U V
  set δ' : ℚ≥0 := divergence (U : Set (ι → F)) V
  have hδlt' : δ < δ' := by
    simpa [δ'] using hδlt
  have hdiv_lt' : (δ' : ℝ≥0) < 1 - ReedSolomon.sqrtRate deg domain := by
    -- rewrite the hypothesis `hdiv_lt` using our abbreviations
    simpa [δ', V] using hdiv_lt
  -- Pointwise spec on subtype elements `u : U`
  have hpredU : ∀ u : U, δᵣ'((u : ι → F), V) ≠ δ' ↔ δᵣ'((u : ι → F), V) ≤ δ := by
    intro u
    simpa [δ'] using (hpred (u : ι → F) u.property)
  -- Cast lemmas from ℚ≥0 to ENNReal via NNReal
  have cast_ennreal_eq_iff (p q : ℚ≥0) : ((p : ENNReal) = (q : ENNReal)) ↔ p = q := by
    change (((p : ℝ≥0) : ENNReal) = ((q : ℝ≥0) : ENNReal)) ↔ p = q
    simp [ENNReal.coe_inj]
  have cast_ennreal_le_iff (p q : ℚ≥0) : ((p : ENNReal) ≤ (q : ENNReal)) ↔ p ≤ q := by
    change (((p : ℝ≥0) : ENNReal) ≤ ((q : ℝ≥0) : ENNReal)) ↔ p ≤ q
    simp [ENNReal.coe_le_coe]
  -- Bridge between ENNReal relative distance and the computable ℚ≥0 version
  have hbridge : ∀ u : ι → F, Code.relDistFromCode u V = (δᵣ'(u, V) : ENNReal) := by
    intro u
    simpa using (Code.relDistFromCode'_eq_relDistFromCode (w := u) (C := V))
  -- Pointwise equivalence on `U` between the `≠ δ'` event and the `≤ δ` event
  have hiffU : ∀ u : U,
      (Code.relDistFromCode (u : ι → F) V ≠ (δ' : ENNReal)) ↔
        (Code.relDistFromCode (u : ι → F) V ≤ (δ : ℝ≥0)) := by
    intro u
    set p : ℚ≥0 := δᵣ'((u : ι → F), V)
    have hs : p ≠ δ' ↔ p ≤ δ := by
      simpa [p] using (hpredU u)
    have hcast : ((p : ENNReal) ≠ (δ' : ENNReal)) ↔ ((p : ENNReal) ≤ (δ : ENNReal)) := by
      constructor
      · intro hne_cast
        have hne : p ≠ δ' := by
          intro hp
          apply hne_cast
          simp [hp]
        have hle : p ≤ δ := hs.mp hne
        exact (cast_ennreal_le_iff p δ).2 hle
      · intro hle_cast
        have hle : p ≤ δ := (cast_ennreal_le_iff p δ).1 hle_cast
        have hne : p ≠ δ' := hs.mpr hle
        intro hEqCast
        have hEq : p = δ' := (cast_ennreal_eq_iff p δ').1 hEqCast
        exact hne hEq
    simpa [hbridge (u := (u : ι → F)), p] using hcast
  -- Turn the pointwise iff into an equality of probabilities
  have hPr_eq :
      Pr_{let u ← $ᵖ U}[Code.relDistFromCode u V ≠ (δ' : ENNReal)] =
        Pr_{let u ← $ᵖ U}[Code.relDistFromCode u V ≤ (δ : ℝ≥0)] := by
    have hfun : (fun u : U => Code.relDistFromCode u V ≠ (δ' : ENNReal)) =
        (fun u : U => Code.relDistFromCode u V ≤ (δ : ℝ≥0)) := by
      funext u
      apply propext
      simpa using (hiffU u)
    simp [hfun]
  -- Apply proximity gap at parameter δ
  have hδ_bound : (δ : ℝ≥0) < 1 - ReedSolomon.sqrtRate deg domain := by
    have hδ_lt_div : (δ : ℝ≥0) < (δ' : ℝ≥0) := by
      exact_mod_cast hδlt'
    exact lt_trans hδ_lt_div hdiv_lt'
  -- Maximizer: some u_max achieves divergence δ', proves Pr[≤ δ] ≠ 1
  rcases divergence_attains (U := (U : Set (ι → F))) (V := V) with ⟨u_max, hu_max, hmax⟩
  have hu_max_eq : δᵣ'(u_max, V) = δ' := by simpa [δ'] using hmax
  let u_max_sub : U := ⟨u_max, hu_max⟩
  have hnotA : (Pr_{let u ← $ᵖ U}[Code.relDistFromCode u V ≤ (δ : ℝ≥0)] = 1) → False := by
    intro hA
    have hall : ∀ u : U, Code.relDistFromCode u V ≤ (δ : ℝ≥0) :=
      Pr_uniform_eq_one_imp_forall (α := U)
        (P := fun u : U => Code.relDistFromCode u V ≤ (δ : ℝ≥0)) hA
    have hle_umax : Code.relDistFromCode u_max_sub V ≤ (δ : ℝ≥0) := hall u_max_sub
    have hnot_le : ¬ Code.relDistFromCode u_max_sub V ≤ (δ : ℝ≥0) := by
      intro hle
      have hle' : (δᵣ'(u_max, V) : ENNReal) ≤ (δ : ENNReal) := by
        simpa [u_max_sub, hbridge (u := u_max)] using hle
      have hle_q : δᵣ'(u_max, V) ≤ δ := (cast_ennreal_le_iff (δᵣ'(u_max, V)) δ).1 hle'
      have hδ_lt_umax : δ < δᵣ'(u_max, V) := by simpa [hu_max_eq] using hδlt'
      exact (not_le_of_gt hδ_lt_umax) hle_q
    exact hnot_le hle_umax
  -- Case split: 0 < δ uses proximity gap via hPG; δ = 0 uses hPG at δ'/2
  have hmain :
      Pr_{let u ← $ᵖ U}[Code.relDistFromCode u V ≠ (δ' : ENNReal)] ≤
        (errorBound (δ' : ℝ≥0) deg domain : ENNReal) := by
    rcases eq_or_lt_of_le (zero_le (δ : ℝ≥0)) with hδ0 | hδ_pos
    · -- δ = 0: use hPG at δ₁ = δ'/2 > 0 instead.
      -- relDist values are {0, δ'}, so Pr[≤ 0] = Pr[≤ δ₁] for δ₁ < δ'.
      -- Then Pr[≤ δ₁] ≤ errorBound(δ₁) ≤ errorBound(δ').
      set δ₁ : ℝ≥0 := (δ' : ℝ≥0) / 2 with hδ₁_def
      have hδ₁_pos : 0 < δ₁ := by positivity
      have hδ₁_lt_δ' : δ₁ < (δ' : ℝ≥0) := NNReal.half_lt_self (ne_of_gt hdiv_pos)
      have hδ₁_bound : δ₁ < 1 - ReedSolomon.sqrtRate deg domain :=
        lt_trans hδ₁_lt_δ' hdiv_lt'
      -- Pr[≤ δ] = Pr[≤ δ₁]: both count codewords (relDist ∈ {0, δ'}, δ₁ < δ')
      have hPr_eq_δ₁ :
          Pr_{let u ← $ᵖ U}[Code.relDistFromCode u V ≤ (δ : ℝ≥0)] =
            Pr_{let u ← $ᵖ U}[Code.relDistFromCode u V ≤ δ₁] := by
        have hfun₁ : (fun u : U => Code.relDistFromCode u V ≤ (δ : ℝ≥0)) =
            (fun u : U => Code.relDistFromCode u V ≤ δ₁) := by
          funext u; apply propext
          constructor
          · intro hle; exact le_trans hle (by rw [← hδ0]; exact zero_le _)
          · intro hle
            have hne : Code.relDistFromCode (u : ι → F) V ≠ (δ' : ENNReal) := by
              intro heq; exact absurd (heq ▸ hle : (δ' : ENNReal) ≤ δ₁)
                (not_le.mpr (by exact_mod_cast hδ₁_lt_δ'))
            exact (hiffU u).mp hne
        simp [hfun₁]
      -- Proximity gap at δ₁
      have hx₁ : Xor'
          (Pr_{let u ← $ᵖ U}[Code.relDistFromCode u V ≤ δ₁] = 1)
          (Pr_{let u ← $ᵖ U}[Code.relDistFromCode u V ≤ δ₁] ≤
            errorBound δ₁ deg domain) := by
        simpa [V] using
          (proximity_gap_affineSubspace (deg := deg) (domain := domain) (U := U) (δ := δ₁)
            (_hδ := hδ₁_bound) (hPG := hPG hδ₁_pos hδ₁_bound))
      have hnotA₁ : (Pr_{let u ← $ᵖ U}[Code.relDistFromCode u V ≤ δ₁] = 1) → False := by
        rw [← hPr_eq_δ₁]; exact hnotA
      have hPr_le₁ : Pr_{let u ← $ᵖ U}[Code.relDistFromCode u V ≤ δ₁] ≤
          errorBound δ₁ deg domain := by
        cases hx₁ with
        | inl h => exact False.elim (hnotA₁ h.1)
        | inr h => exact h.1
      have herr₁ : errorBound δ₁ deg domain ≤ errorBound (δ' : ℝ≥0) deg domain :=
        errorBound_mono hdeg (le_of_lt hδ₁_lt_δ') hdiv_lt'
      calc Pr_{let u ← $ᵖ U}[Code.relDistFromCode u V ≠ (δ' : ENNReal)]
            = Pr_{let u ← $ᵖ U}[Code.relDistFromCode u V ≤ (δ : ℝ≥0)] := hPr_eq
        _ = Pr_{let u ← $ᵖ U}[Code.relDistFromCode u V ≤ δ₁] := hPr_eq_δ₁
        _ ≤ (errorBound δ₁ deg domain : ENNReal) := hPr_le₁
        _ ≤ (errorBound (δ' : ℝ≥0) deg domain : ENNReal) := by exact_mod_cast herr₁
    · -- 0 < δ: standard path via proximity gap
      have hx : Xor'
          (Pr_{let u ← $ᵖ U}[Code.relDistFromCode u V ≤ (δ : ℝ≥0)] = 1)
          (Pr_{let u ← $ᵖ U}[Code.relDistFromCode u V ≤ (δ : ℝ≥0)]
            ≤ errorBound (δ : ℝ≥0) deg domain) := by
        simpa [V] using
          (proximity_gap_affineSubspace (deg := deg) (domain := domain) (U := U) (δ := (δ : ℝ≥0))
            (_hδ := hδ_bound) (hPG := hPG hδ_pos hδ_bound))
      have hPr_le : Pr_{let u ← $ᵖ U}[Code.relDistFromCode u V ≤ (δ : ℝ≥0)] ≤
          errorBound (δ : ℝ≥0) deg domain := by
        cases hx with
        | inl h => exact False.elim (hnotA h.1)
        | inr h => exact h.1
      have hδ_le_δ' : (δ : ℝ≥0) ≤ (δ' : ℝ≥0) := by exact_mod_cast (le_of_lt hδlt')
      have herr_mono : errorBound (δ : ℝ≥0) deg domain ≤ errorBound (δ' : ℝ≥0) deg domain :=
        errorBound_mono hdeg hδ_le_δ' hdiv_lt'
      calc Pr_{let u ← $ᵖ U}[Code.relDistFromCode u V ≠ (δ' : ENNReal)]
            = Pr_{let u ← $ᵖ U}[Code.relDistFromCode u V ≤ (δ : ℝ≥0)] := hPr_eq
        _ ≤ (errorBound (δ : ℝ≥0) deg domain : ENNReal) := hPr_le
        _ ≤ (errorBound (δ' : ℝ≥0) deg domain : ENNReal) := by exact_mod_cast herr_mono
  -- rewrite back to the original goal
  simpa [δ', V] using hmain


end Theorems

end DivergenceOfSets
