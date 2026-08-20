/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.InterleavedCode
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.CodingTheory.ProximityGap.Errors
import ArkLib.Data.Probability.Combinatorial
import ArkLib.ProofSystem.ToyProblem.Definitions

/-!
# Fixed-radius soundness bounds for the toy problem

This module contains the coding-theoretic combination-round argument used by the
ABF26 toy IOP.  It is stated against the current canonical objects:

* `CoreDefinitions.mcaError` for affine-line mutual correlated agreement;
* a `ModuleCode` rather than a parallel set-valued MCA event; and
* `Code.Lambda` of the two-row interleaving for the list term.

The central result, `gamma_transition_prob_le`, bounds the probability that a
folded message satisfies the post-challenge state while the original two-row
instance has no relaxed witness.  The proof splits on `IsMCA`.  Off the MCA event,
the common projected codewords form a two-row point-list element, and each invalid
message pair accounts for at most one affine challenge.

## References

* [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26], Section 6.
-/

namespace ToyProblem

open Code InterleavedCode ProximityGap CoreDefinitions
open scoped NNReal ENNReal ProbabilityTheory
open Probability

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

variable {ι F : Type} [Fintype ι] [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

/-- Stack the two codewords obtained by encoding a pair of scalar messages. -/
def encStack {k : ℕ} (enc : (Fin k → F) →ₗ[F] (ι → A))
    (m : (Fin k → F) × (Fin k → F)) : ι → Fin 2 → A :=
  fun i row ↦ if row = 0 then enc m.1 i else enc m.2 i

omit [Fintype ι] [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A] in
@[simp]
theorem encStack_apply_zero {k : ℕ} (enc : (Fin k → F) →ₗ[F] (ι → A))
    (m : (Fin k → F) × (Fin k → F)) (i : ι) :
    encStack enc m i 0 = enc m.1 i := rfl

omit [Fintype ι] [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A] in
@[simp]
theorem encStack_apply_one {k : ℕ} (enc : (Fin k → F) →ₗ[F] (ι → A))
    (m : (Fin k → F) × (Fin k → F)) (i : ι) :
    encStack enc m i 1 = enc m.2 i := rfl

omit [Fintype ι] [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A] in
theorem encStack_injective {k : ℕ} {enc : (Fin k → F) →ₗ[F] (ι → A)}
    (hinj : Function.Injective enc) : Function.Injective (encStack enc) := by
  intro p q hpq
  apply Prod.ext
  · apply hinj
    funext i
    exact congrFun (congrFun hpq i) 0
  · apply hinj
    funext i
    exact congrFun (congrFun hpq i) 1

omit [Fintype F] [DecidableEq F] [Fintype A] in
/-- A stacked encoded pair is in the interleaved point list exactly when both
rows agree with the received pair on one sufficiently large column set. -/
theorem encStack_mem_closeCodewordsRel_iff [Nonempty ι] {k : ℕ}
    (enc : (Fin k → F) →ₗ[F] (ι → A)) (C : ModuleCode ι F A)
    (hC : Set.range enc = (C : Set (ι → A))) {δ : ℝ≥0} (hδ_lt : δ < 1)
    {fStar : ι → Fin 2 → A} (m : (Fin k → F) × (Fin k → F)) :
    encStack enc m ∈ Code.closeCodewordsRel
      ((C ^⋈ (Fin 2) : ModuleCode ι F (Fin 2 → A)) : Set (ι → Fin 2 → A))
      fStar (δ : ℝ) ↔
      ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
        ∀ i ∈ S, fStar i 0 = enc m.1 i ∧ fStar i 1 = enc m.2 i := by
  rw [Code.mem_closeCodewordsRel_iff]
  have hmem : encStack enc m ∈
      (C ^⋈ (Fin 2) : ModuleCode ι F (Fin 2 → A)) := by
    change ∀ row, (fun i ↦ encStack enc m i row) ∈ C
    intro row
    fin_cases row
    · change enc m.1 ∈ C
      have hm : enc m.1 ∈ (C : Set (ι → A)) := hC ▸ Set.mem_range_self m.1
      exact hm
    · change enc m.2 ∈ C
      have hm : enc m.2 ∈ (C : Set (ι → A)) := hC ▸ Set.mem_range_self m.2
      exact hm
  constructor
  · rintro ⟨_, hdistR⟩
    have hdist : (δᵣ(fStar, encStack enc m) : ℝ≥0) ≤ δ := by
      exact_mod_cast hdistR
    rw [Code.relCloseToWord_iff_exists_agreementCols] at hdist
    obtain ⟨S, hScard, hagree⟩ := hdist
    refine ⟨S, ?_, ?_⟩
    · have hcomp := (Code.relDist_floor_bound_iff_complement_bound _ _ _).mp hScard
      have hcoe : ((1 - δ : ℝ≥0) : ℝ) = 1 - (δ : ℝ) := by
        rw [NNReal.coe_sub hδ_lt.le]
        simp
      have hcompR := NNReal.coe_le_coe.mpr hcomp
      rw [NNReal.coe_mul, hcoe] at hcompR
      push_cast at hcompR ⊢
      linarith
    · intro i hi
      have hiEq := (hagree i).1 hi
      exact ⟨congrFun hiEq 0, congrFun hiEq 1⟩
  · rintro ⟨S, hScard, hagree⟩
    refine ⟨hmem, ?_⟩
    have hdist : (δᵣ(fStar, encStack enc m) : ℝ≥0) ≤ δ := by
      rw [Code.relCloseToWord_iff_exists_agreementCols]
      refine ⟨S, ?_, ?_⟩
      · rw [Code.relDist_floor_bound_iff_complement_bound]
        have hcoe : ((1 - δ : ℝ≥0) : ℝ) = 1 - (δ : ℝ) := by
          rw [NNReal.coe_sub hδ_lt.le]
          simp
        rw [← NNReal.coe_le_coe, NNReal.coe_mul, hcoe]
        push_cast
        linarith
      · intro i
        constructor
        · intro hi
          funext row
          fin_cases row
          · exact (hagree i hi).1
          · exact (hagree i hi).2
        · intro hne hi
          apply hne
          funext row
          fin_cases row
          · exact (hagree i hi).1
          · exact (hagree i hi).2
    exact_mod_cast hdist

omit [Field F] [Fintype F] [Fintype A] [AddCommGroup A] in
/-- Deprecated compatibility name for the general coding-theory bound. -/
@[deprecated Code.minRelHammingDistCode_le_one (since := "2026-08-16")]
theorem minRelHammingDistCode_le_one [Nonempty ι] (C : Set (ι → A)) :
    minRelHammingDistCode C ≤ 1 :=
  Code.minRelHammingDistCode_le_one (C := C)

omit [Field F] [Fintype F] [Fintype A] [AddCommGroup A] in
/-- Two codewords agreeing on more than the minimum-distance erasure threshold
are equal. -/
theorem codeword_eq_of_agree_on_large_set [Nonempty ι] {C : Set (ι → A)}
    {δ : ℝ≥0} (hδ_lt : δ < (minRelHammingDistCode C : ℝ≥0)) {w₁ w₂ : ι → A}
    (hw₁ : w₁ ∈ C) (hw₂ : w₂ ∈ C) {S : Finset ι}
    (hScard : (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card)
    (hagree : ∀ j ∈ S, w₁ j = w₂ j) : w₁ = w₂ := by
  by_contra hne
  have hδ1 : δ < 1 :=
    lt_of_lt_of_le hδ_lt (by exact_mod_cast Code.minRelHammingDistCode_le_one (C := C))
  have hclose : (δᵣ(w₁, w₂) : ℝ≥0) ≤ δ := by
    rw [Code.relCloseToWord_iff_exists_agreementCols]
    refine ⟨S, ?_, fun colIdx ↦
      ⟨fun hin ↦ hagree colIdx hin, fun hne' hin ↦ hne' (hagree colIdx hin)⟩⟩
    rw [Code.relDist_floor_bound_iff_complement_bound]
    have hcoe : ((1 - δ : ℝ≥0) : ℝ) = 1 - (δ : ℝ) := by
      rw [NNReal.coe_sub hδ1.le]
      simp
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, hcoe]
    push_cast
    linarith
  have hmem : δᵣ(w₁, w₂) ∈ possibleRelHammingDists C :=
    ⟨(w₁, w₂), Set.mem_offDiag.mpr ⟨hw₁, hw₂, hne⟩, rfl⟩
  have hmin : ((minRelHammingDistCode C : ℚ≥0) : ℝ≥0) ≤
      (δᵣ(w₁, w₂) : ℝ≥0) := by
    exact_mod_cast minRelHammingDistCode_le hmem
  exact absurd hδ_lt (not_lt.mpr (hmin.trans hclose))

omit [Fintype ι] in
/-- A nontrivial affine scalar equation has at most one solution. -/
theorem affine_solution_card_le_one {a b μ₁ μ₂ : F}
    (h : ¬ (a = μ₁ ∧ b = μ₂)) :
    (Finset.univ.filter (fun γ : F ↦ a + γ * b = μ₁ + γ * μ₂)).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro x hx y hy
  rw [Finset.mem_filter] at hx hy
  by_cases hb : b = μ₂
  · exfalso
    subst hb
    exact h ⟨add_right_cancel hx.2, rfl⟩
  · have key : (x - y) * (b - μ₂) = 0 := by
      linear_combination hx.2 - hy.2
    rcases mul_eq_zero.mp key with h1 | h2
    · exact sub_eq_zero.mp h1
    · exact absurd (sub_eq_zero.mp h2) hb

omit [Fintype ι] [Fintype F] [DecidableEq F] in
/-- Deprecated compatibility name for the general probability union bound. -/
@[deprecated Probability.Pr_or_le (since := "2026-08-16")]
theorem Pr_or_le {α : Type} [Fintype α] [Nonempty α] (P Q : α → Prop) :
    Pr_{let x ← $ᵖ α}[P x ∨ Q x] ≤
      Pr_{let x ← $ᵖ α}[P x] + Pr_{let x ← $ᵖ α}[Q x] :=
  Probability.Pr_or_le ($ᵖ α) P Q

/-- The post-combination-challenge state: a message satisfies the folded linear
constraint and its codeword agrees with the folded received word on enough columns. -/
def GammaEvent {k : ℕ} (enc : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0)
    (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → A) (γ : F) : Prop :=
  ∃ m : Fin k → F, (∑ j, m j * v j = μ₁ + γ * μ₂) ∧
    ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
      ∀ j ∈ S, f₁ j + γ • f₂ j = enc m j

omit [DecidableEq F] [Fintype A] in
/-- Off the canonical MCA event, a successful folded state determines a message
pair in the two-row point list whose affine constraints hold at `γ`. -/
theorem gamma_bad_pair {k : ℕ} [Nonempty ι] (C : ModuleCode ι F A) {δ : ℝ≥0}
    (enc : (Fin k → F) →ₗ[F] (ι → A)) (hinj : Function.Injective enc)
    (hC : Set.range enc = (C : Set (ι → A)))
    (hδ_lt : δ < (minRelHammingDistCode (C : Set (ι → A)) : ℝ≥0))
    {v : Fin k → F} {μ₁ μ₂ : F} {f₁ f₂ : ι → A} {γ : F}
    (hEvent : GammaEvent enc δ v μ₁ μ₂ f₁ f₂ γ)
    (hmca : ¬ IsMCA (AffineLineGenerator F) C γ ![f₁, f₂] (δ : ℝ)) :
    ∃ p : (Fin k → F) × (Fin k → F),
      encStack enc p ∈ Code.closeCodewordsRel
        ((C ^⋈ (Fin 2) : ModuleCode ι F (Fin 2 → A)) : Set (ι → Fin 2 → A))
        (fun i ↦ ![f₁ i, f₂ i]) (δ : ℝ) ∧
      (∑ j, p.1 j * v j) + γ * (∑ j, p.2 j * v j) = μ₁ + γ * μ₂ := by
  classical
  have hδ1 : δ < 1 :=
    lt_of_lt_of_le hδ_lt
      (by exact_mod_cast Code.minRelHammingDistCode_le_one (C := (C : Set (ι → A))))
  obtain ⟨m, hconstr, S, hScard, hagree⟩ := hEvent
  have hcard : (S.card : ℝ) ≥ (Fintype.card ι : ℝ) * (1 - (δ : ℝ)) := by
    linarith
  have hcomb : LinearCode.projectedWord
      (fun x ↦ ∑ i : Fin 2, AffineLineGenerator F γ i • ![f₁, f₂] i x) S ∈
      LinearCode.projectedCodeSubmod C S := by
    rw [LinearCode.mem_projectedCodeSubmod_iff]
    have hm : enc m ∈ (C : Set (ι → A)) := hC ▸ Set.mem_range_self m
    refine ⟨enc m, hm, ?_⟩
    funext x
    simp only [LinearCode.projectedWord, Set.restrict_apply]
    simpa [AffineLineGenerator, Fin.sum_univ_two] using hagree x x.property
  have hall : ∀ i : Fin 2,
      LinearCode.projectedWord (![f₁, f₂] i) S ∈
        LinearCode.projectedCodeSubmod C S := by
    by_contra hnot
    push Not at hnot
    exact hmca ⟨S, hcard, hcomb, hnot⟩
  choose words hwords hproj using fun i ↦
    (LinearCode.mem_projectedCodeSubmod_iff C S
      (LinearCode.projectedWord (![f₁, f₂] i) S)).mp (hall i)
  have hmsg : ∀ i : Fin 2, ∃ msg, enc msg = words i := by
    intro i
    have hw : words i ∈ (C : Set (ι → A)) := hwords i
    rw [← hC] at hw
    exact hw
  choose msgs hmsgs using hmsg
  let p : (Fin k → F) × (Fin k → F) := (msgs 0, msgs 1)
  refine ⟨p, ?_, ?_⟩
  · rw [encStack_mem_closeCodewordsRel_iff enc C hC hδ1]
    refine ⟨S, hScard, fun x hx ↦ ⟨?_, ?_⟩⟩
    · have h := congrFun (hproj 0) ⟨x, hx⟩
      change f₁ x = enc (msgs 0) x
      rw [hmsgs 0]
      simpa [LinearCode.projectedWord] using h
    · have h := congrFun (hproj 1) ⟨x, hx⟩
      change f₂ x = enc (msgs 1) x
      rw [hmsgs 1]
      simpa [LinearCode.projectedWord] using h
  · have hagreeCode : ∀ x ∈ S, enc m x = enc (msgs 0 + γ • msgs 1) x := by
      intro x hx
      rw [map_add, map_smul]
      simp only [Pi.add_apply, Pi.smul_apply]
      have h0 := congrFun (hproj 0) ⟨x, hx⟩
      have h1 := congrFun (hproj 1) ⟨x, hx⟩
      rw [hmsgs 0, hmsgs 1]
      have h0' : f₁ x = words 0 x := by
        simpa [LinearCode.projectedWord] using h0
      have h1' : f₂ x = words 1 x := by
        simpa [LinearCode.projectedWord] using h1
      exact (hagree x hx).symm.trans (by rw [h0', h1'])
    have hmC : enc m ∈ (C : Set (ι → A)) := hC ▸ Set.mem_range_self m
    have hcombC : enc (msgs 0 + γ • msgs 1) ∈ (C : Set (ι → A)) :=
      hC ▸ Set.mem_range_self (msgs 0 + γ • msgs 1)
    have heq : enc m = enc (msgs 0 + γ • msgs 1) :=
      codeword_eq_of_agree_on_large_set hδ_lt hmC hcombC hScard hagreeCode
    have hm : m = msgs 0 + γ • msgs 1 := hinj heq
    have hsum : (∑ j, (msgs 0 + γ • msgs 1) j * v j) =
        (∑ j, msgs 0 j * v j) + γ * (∑ j, msgs 1 j * v j) := by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc]
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [hm, hsum] at hconstr
    exact hconstr

omit [Fintype F] [DecidableEq F] [Fintype A] in
/-- Every point-list message pair violates at least one original constraint when
the two-row input has no relaxed witness. -/
theorem not_constraint_pair_of_mem_closeCodewordsRel {k : ℕ} [Nonempty ι] (C : ModuleCode ι F A) {δ : ℝ≥0}
    (hδ1 : δ < 1) (enc : (Fin k → F) →ₗ[F] (ι → A))
    (hC : Set.range enc = (C : Set (ι → A)))
    {v : Fin k → F} {μ₁ μ₂ : F} {f₁ f₂ : ι → A}
    (hNoWit : ¬ ∃ M : Fin 2 → (Fin k → F),
      (∀ i : Fin 2, ∑ j, M i j * v j = ![μ₁, μ₂] i) ∧
      ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
        ∀ i : Fin 2, ∀ j ∈ S, ![f₁, f₂] i j = enc (M i) j)
    {p : (Fin k → F) × (Fin k → F)}
    (hp : encStack enc p ∈ Code.closeCodewordsRel
      ((C ^⋈ (Fin 2) : ModuleCode ι F (Fin 2 → A)) : Set (ι → Fin 2 → A))
      (fun i ↦ ![f₁ i, f₂ i]) (δ : ℝ)) :
    ¬ ((∑ j, p.1 j * v j) = μ₁ ∧ (∑ j, p.2 j * v j) = μ₂) := by
  rintro ⟨h1, h2⟩
  obtain ⟨S, hScard, hagree⟩ :=
    (encStack_mem_closeCodewordsRel_iff enc C hC hδ1 p).mp hp
  apply hNoWit
  refine ⟨![p.1, p.2], fun i ↦ ?_, S, hScard, fun i j hj ↦ ?_⟩
  · fin_cases i
    · exact h1
    · exact h2
  · fin_cases i
    · exact (hagree j hj).1
    · exact (hagree j hj).2

/-- **Combination-round MCA-plus-list bound.**  For a two-row input with no
relaxed witness, the probability of reaching the post-`γ` state is at most the
canonical affine-line MCA error plus the two-row point-list size divided by the
field size. -/
theorem gamma_transition_prob_le {k : ℕ} [Nonempty ι]
    (C : ModuleCode ι F A) (δ : ℝ≥0)
    (enc : (Fin k → F) →ₗ[F] (ι → A)) (hinj : Function.Injective enc)
    (hC : Set.range enc = (C : Set (ι → A)))
    (_hδ_pos : 0 < δ)
    (hδ_lt : δ < (minRelHammingDistCode (C : Set (ι → A)) : ℝ≥0))
    (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → A)
    (hNoWit : ¬ ∃ M : Fin 2 → (Fin k → F),
      (∀ i : Fin 2, ∑ j, M i j * v j = ![μ₁, μ₂] i) ∧
      ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
        ∀ i : Fin 2, ∀ j ∈ S, ![f₁, f₂] i j = enc (M i) j) :
    Pr_{let γ ← $ᵖ F}[GammaEvent enc δ v μ₁ μ₂ f₁ f₂ γ] ≤
      mcaError (AffineLineGenerator F) C (δ : ℝ) +
        ((Code.Lambda
          ((C ^⋈ (Fin 2) : ModuleCode ι F (Fin 2 → A)) : Set (ι → Fin 2 → A))
          (δ : ℝ)).toNat : ENNReal) / (Fintype.card F : ENNReal) := by
  classical
  have hδ1 : δ < 1 :=
    lt_of_lt_of_le hδ_lt
      (by exact_mod_cast Code.minRelHammingDistCode_le_one (C := (C : Set (ι → A))))
  let Cint : Set (ι → Fin 2 → A) :=
    ((C ^⋈ (Fin 2) : ModuleCode ι F (Fin 2 → A)) : Set (ι → Fin 2 → A))
  let center : ι → Fin 2 → A := fun i ↦ ![f₁ i, f₂ i]
  let Smsg : Finset ((Fin k → F) × (Fin k → F)) := Finset.univ.filter
    (fun p ↦ encStack enc p ∈ Code.closeCodewordsRel Cint center (δ : ℝ))
  have hSmsg_le : Smsg.card ≤ (Code.Lambda Cint (δ : ℝ)).toNat := by
    have hsub : encStack enc '' (Smsg : Set ((Fin k → F) × (Fin k → F))) ⊆
        Code.closeCodewordsRel Cint center (δ : ℝ) := by
      rintro V ⟨p, hp, rfl⟩
      exact (Finset.mem_filter.mp hp).2
    have himage :
        (encStack enc '' (Smsg : Set ((Fin k → F) × (Fin k → F)))).ncard =
          Smsg.card := by
      rw [Set.ncard_image_of_injective _ (encStack_injective hinj), Set.ncard_coe_finset]
    have hencard :
        ((Code.closeCodewordsRel Cint center (δ : ℝ)).ncard : ENat) ≤
          Code.Lambda Cint (δ : ℝ) := by
      rw [(Set.toFinite (Code.closeCodewordsRel Cint center (δ : ℝ))).cast_ncard_eq]
      exact Code.encard_closeCodewordsRel_le_Lambda Cint (δ : ℝ) center
    have hfinite : Code.Lambda Cint (δ : ℝ) ≠ ⊤ := Code.Lambda_ne_top _
    have hncard : Smsg.card ≤ (Code.closeCodewordsRel Cint center (δ : ℝ)).ncard := by
      rw [← himage]
      exact Set.ncard_le_ncard hsub (Set.toFinite _)
    have hcast : (Smsg.card : ENat) ≤ Code.Lambda Cint (δ : ℝ) :=
      le_trans (by exact_mod_cast hncard) hencard
    rwa [← ENat.coe_toNat hfinite, Nat.cast_le] at hcast
  have hcards : (Finset.univ.filter (fun γ : F ↦
      GammaEvent enc δ v μ₁ μ₂ f₁ f₂ γ ∧
        ¬ IsMCA (AffineLineGenerator F) C γ ![f₁, f₂] (δ : ℝ))).card ≤
      (Code.Lambda Cint (δ : ℝ)).toNat := by
    have hsub : Finset.univ.filter (fun γ : F ↦
        GammaEvent enc δ v μ₁ μ₂ f₁ f₂ γ ∧
          ¬ IsMCA (AffineLineGenerator F) C γ ![f₁, f₂] (δ : ℝ)) ⊆
        Smsg.biUnion (fun p ↦ Finset.univ.filter (fun γ : F ↦
          (∑ j, p.1 j * v j) + γ * (∑ j, p.2 j * v j) = μ₁ + γ * μ₂)) := by
      intro γ hγ
      rw [Finset.mem_filter] at hγ
      obtain ⟨p, hplist, heq⟩ :=
        gamma_bad_pair C enc hinj hC hδ_lt hγ.2.1 hγ.2.2
      rw [Finset.mem_biUnion]
      refine ⟨p, ?_, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hplist⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩
    refine le_trans (Finset.card_le_card hsub) (le_trans Finset.card_biUnion_le ?_)
    calc
      ∑ p ∈ Smsg, (Finset.univ.filter (fun γ : F ↦
          (∑ j, p.1 j * v j) + γ * (∑ j, p.2 j * v j) = μ₁ + γ * μ₂)).card
          ≤ ∑ _p ∈ Smsg, 1 := Finset.sum_le_sum fun p hp ↦
            affine_solution_card_le_one
              (not_constraint_pair_of_mem_closeCodewordsRel C hδ1 enc hC hNoWit (Finset.mem_filter.mp hp).2)
      _ = Smsg.card := by rw [Finset.sum_const, smul_eq_mul, mul_one]
      _ ≤ (Code.Lambda Cint (δ : ℝ)).toNat := hSmsg_le
  refine le_trans (Pr_le_Pr_of_implies ($ᵖ F) _
      (fun γ ↦ IsMCA (AffineLineGenerator F) C γ ![f₁, f₂] (δ : ℝ) ∨
        (GammaEvent enc δ v μ₁ μ₂ f₁ f₂ γ ∧
          ¬ IsMCA (AffineLineGenerator F) C γ ![f₁, f₂] (δ : ℝ)))
      (fun γ h ↦ by
        by_cases hm : IsMCA (AffineLineGenerator F) C γ ![f₁, f₂] (δ : ℝ)
        · exact Or.inl hm
        · exact Or.inr ⟨h, hm⟩))
    (le_trans (Probability.Pr_or_le ($ᵖ F) _ _) (add_le_add ?_ ?_))
  · exact le_iSup
      (fun U : Fin 2 → (ι → A) ↦
        Pr_{let γ ← $ᵖ F}[IsMCA (AffineLineGenerator F) C γ U (δ : ℝ)])
      ![f₁, f₂]
  · rw [prob_uniform_eq_card_filter_div_card]
    exact ENNReal.div_le_div_right (by exact_mod_cast hcards) _

omit [Fintype ι] [Fintype F] [DecidableEq F] in
/-- **ENNReal → ℝ bridge for the Claim-B.1 output.** Rewrites Claim B.1's image
bound `M / (1 + (M−1)·|F|⁻¹) ≤ s` into the real-arithmetic form
`M·c/(c+M−1) ≤ s` consumed by `listDecoding_div_le_div` (here `c = |F|`). -/
private lemma image_bound_toReal {M s c : ℕ} (hc : 1 ≤ c) (hM : 1 ≤ M)
    (h : (M : ENNReal) / (1 + ((M : ENNReal) - 1) * (c : ENNReal)⁻¹) ≤ (s : ENNReal)) :
    (M : ℝ) * c / (c + M - 1) ≤ s := by
  have hc0 : (c : ENNReal) ≠ 0 := by exact_mod_cast Nat.one_le_iff_ne_zero.mp hc
  have hct : (c : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcc : (c : ENNReal)⁻¹ * c = 1 := ENNReal.inv_mul_cancel hc0 hct
  have hMc : (M : ENNReal) - 1 = ((M - 1 : ℕ) : ENNReal) := by
    have hMe : (M : ENNReal) = ((M - 1 : ℕ) : ENNReal) + 1 := by
      rw [← Nat.cast_add_one, Nat.sub_add_cancel hM]
    rw [hMe, ENNReal.add_sub_cancel_right ENNReal.one_ne_top]
  set D : ENNReal := 1 + ((M : ENNReal) - 1) * (c : ENNReal)⁻¹ with hD
  have hD0 : D ≠ 0 := by
    rw [hD]; exact (add_pos_of_pos_of_nonneg one_pos zero_le).ne'
  have hDt : D ≠ ⊤ := by
    rw [hD, hMc]
    exact ENNReal.add_ne_top.mpr ⟨ENNReal.one_ne_top,
      ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) (ENNReal.inv_ne_top.mpr hc0)⟩
  -- `M ≤ s · D`, then multiply through by `c`.
  have hle : (M : ENNReal) ≤ (s : ENNReal) * D := by
    have hmul : (M : ENNReal) / D * D ≤ (s : ENNReal) * D := by gcongr
    rwa [ENNReal.div_mul_cancel hD0 hDt] at hmul
  have hDc : D * (c : ENNReal) = (c : ENNReal) + ((M - 1 : ℕ) : ENNReal) := by
    rw [hD, hMc, add_mul, one_mul, mul_assoc, hcc, mul_one]
  have hsum : (c : ENNReal) + ((M - 1 : ℕ) : ENNReal) = ((c + M - 1 : ℕ) : ENNReal) := by
    rw [← Nat.cast_add]; congr 1; omega
  have hkey : ((M * c : ℕ) : ENNReal) ≤ ((s * (c + M - 1) : ℕ) : ENNReal) := by
    calc ((M * c : ℕ) : ENNReal) = (M : ENNReal) * c := by push_cast; ring
      _ ≤ (s : ENNReal) * D * c := by gcongr
      _ = (s : ENNReal) * (D * c) := by ring
      _ = (s : ENNReal) * ((c + M - 1 : ℕ) : ENNReal) := by rw [hDc, hsum]
      _ = ((s * (c + M - 1) : ℕ) : ENNReal) := by push_cast; ring
  have hnat : M * c ≤ s * (c + M - 1) := by exact_mod_cast hkey
  have hcM : ((c + M - 1 : ℕ) : ℝ) = (c : ℝ) + M - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ c + M)]; push_cast; ring
  have hpos : (0 : ℝ) < (c : ℝ) + M - 1 := by
    have h1 : (1 : ℝ) ≤ ((c + M - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ c + M - 1)
    rw [hcM] at h1; linarith
  rw [div_le_iff₀ hpos]
  have hnat' : (M : ℝ) * c ≤ s * ((c : ℝ) + M - 1) := by
    rw [← hcM]; exact_mod_cast hnat
  linarith [hnat']

omit [Fintype ι] [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A] in
lemma encStack_transpose_zero {k : ℕ} (enc : (Fin k → F) →ₗ[F] (ι → A))
    (m : (Fin k → F) × (Fin k → F)) :
    (fun i ↦ encStack enc m i 0) = enc m.1 := by
  funext i; rfl

omit [Fintype ι] [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A] in
lemma encStack_transpose_one {k : ℕ} (enc : (Fin k → F) →ₗ[F] (ι → A))
    (m : (Fin k → F) × (Fin k → F)) :
    (fun i ↦ encStack enc m i 1) = enc m.2 := by
  funext i; rfl

open Probability in
/-- **First Claim-B.1 application (abstract inner-product form).** For an
injective family `a : σ → (F^k)²` of message pairs, there is a constraint vector
`v` under which the collision map `s ↦ (⟨a(s)₁, v⟩, ⟨a(s)₂, v⟩)` has image of
size at least `|σ| / (1 + (|σ|−1)/|F|)` (= `|σ|·|F|/(|F|+|σ|−1)`).

This is the first of the two `exists_large_image_of_pairwise_collision_bound`
(Claim B.1) applications in ABF26 §6.4.1, stripped of all coding theory: the
pairwise-collision bound is exactly `prob_dotProduct_eq_zero_le` (a nonzero
linear form vanishes with probability `≤ 1/|F|`), pulled back through the
pushforward identity `Pr_map_eq`. -/
private lemma exists_dotProduct_image_card_le {k : ℕ} {σ : Type} [Fintype σ]
    (a : σ → (Fin k → F) × (Fin k → F)) (ha : Function.Injective a) :
    ∃ v : Fin k → F,
      (Fintype.card σ : ENNReal) / (1 + (Fintype.card σ - 1) * (Fintype.card F : ENNReal)⁻¹)
        ≤ ((Set.range (fun s : σ ↦
            ((∑ j, (a s).1 j * v j), (∑ j, (a s).2 j * v j)))).ncard : ENNReal) := by
  classical
  set g : (Fin k → F) → (σ → F × F) :=
    fun v s ↦ ((∑ j, (a s).1 j * v j), (∑ j, (a s).2 j * v j)) with hg
  set Φ : PMF (σ → F × F) := (PMF.uniformOfFintype (Fin k → F)).map g with hΦ
  have hcoll : ∀ x y : σ, x ≠ y →
      Pr_{ let φ ← Φ }[φ x = φ y] ≤ (Fintype.card F : ENNReal)⁻¹ := by
    intro x y hxy
    rw [hΦ, Pr_map_eq]
    have hne : a x ≠ a y := fun h ↦ hxy (ha h)
    by_cases h1 : (a x).1 = (a y).1
    · have h2 : (a x).2 ≠ (a y).2 := fun h ↦ hne (Prod.ext h1 h)
      refine le_trans (Pr_le_Pr_of_implies _ _
        (fun v ↦ (∑ j, ((a x).2 - (a y).2) j * v j = 0)) ?_)
        (prob_dotProduct_eq_zero_le ((a x).2 - (a y).2) (sub_ne_zero.mpr h2))
      intro v hv
      have hv' : g v x = g v y := by simpa using hv
      have : (∑ j, (a x).2 j * v j) = (∑ j, (a y).2 j * v j) := (Prod.ext_iff.mp hv').2
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, this, sub_self]
    · refine le_trans (Pr_le_Pr_of_implies _ _
        (fun v ↦ (∑ j, ((a x).1 - (a y).1) j * v j = 0)) ?_)
        (prob_dotProduct_eq_zero_le ((a x).1 - (a y).1) (sub_ne_zero.mpr h1))
      intro v hv
      have hv' : g v x = g v y := by simpa using hv
      have : (∑ j, (a x).1 j * v j) = (∑ j, (a y).1 j * v j) := (Prod.ext_iff.mp hv').1
      simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib, this, sub_self]
  obtain ⟨φ, hφ_supp, hφ_card⟩ :=
    exists_large_image_of_pairwise_collision_bound_of_Pr
      Φ (Fintype.card F : ENNReal)⁻¹ hcoll
  rw [hΦ, PMF.mem_support_map_iff] at hφ_supp
  obtain ⟨v, _, hv⟩ := hφ_supp
  refine ⟨v, ?_⟩
  have hgv : (fun s : σ ↦
      ((∑ j, (a s).1 j * v j), (∑ j, (a s).2 j * v j))) = φ := by
    exact rfl.trans hv
  rw [hgv]
  refine hφ_card.trans_eq ?_
  norm_cast
  rw [← Set.ncard_coe_finset]
  congr 1
  ext z
  simp

omit [Fintype ι] in
/-- **Affine collision has at most one solution (ABF26 §6.4.1, second B.1).**
For distinct points `(a₁,a₂) ≠ (b₁,b₂)` with `a₂, b₂ ≠ μ₂`, the equation
`(μ₁−a₁)/(a₂−μ₂) = (μ₁−b₁)/(b₂−μ₂)` has at most one solution `μ₁`: if `a₂ ≠ b₂`
it is affine in `μ₁`; if `a₂ = b₂` it is unsatisfiable. -/
private lemma affine_collision_card_le_one {a₁ a₂ b₁ b₂ μ₂ : F}
    (ha : a₂ ≠ μ₂) (hb : b₂ ≠ μ₂) (hpq : (a₁, a₂) ≠ (b₁, b₂)) :
    (Finset.univ.filter
      (fun μ₁ : F ↦ (μ₁ - a₁) / (a₂ - μ₂) = (μ₁ - b₁) / (b₂ - μ₂))).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro x hx y hy
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx hy
  rw [div_eq_div_iff (sub_ne_zero.mpr ha) (sub_ne_zero.mpr hb)] at hx hy
  have key : (x - y) * (b₂ - a₂) = 0 := by linear_combination hx - hy
  rcases mul_eq_zero.mp key with hxy | hba
  · exact sub_eq_zero.mp hxy
  · exfalso
    have hab : a₂ = b₂ := (sub_eq_zero.mp hba).symm
    apply hpq
    subst hab
    have hx' : (x - a₁) = (x - b₁) := mul_right_cancel₀ (sub_ne_zero.mpr ha) hx
    have : a₁ = b₁ := sub_right_injective hx'
    rw [this]

open Probability in
/-- **Second Claim-B.1 application (abstract affine form).** For a set `T ⊆ F×F`
with `|T| < |F|`, there is a value `μ₂` avoiding every second coordinate of `T`
and a `μ₁` under which the affine map `(a,b) ↦ (μ₁−a)/(b−μ₂)` has image of size
at least `|T| / (1 + (|T|−1)/|F|)` (= `|F|·|T|/(|F|+|T|−1)`).

This is the second `exists_large_image_of_pairwise_collision_bound` (Claim B.1)
application in ABF26 §6.4.1: the per-point collision bound is `≤ 1/|F|` because
the affine equation has `≤ 1` solution (`affine_collision_card_le_one`). The
`∀ p ∈ T, p.2 ≠ μ₂` clause also forces `(μ₁,μ₂) ∉ T` (the violation step). -/
private lemma exists_affine_image_card_le (T : Finset (F × F))
    (hTcard : T.card < Fintype.card F) :
    ∃ (μ₁ μ₂ : F), (∀ p ∈ T, p.2 ≠ μ₂) ∧
      (T.card : ENNReal) / (1 + (T.card - 1) * (Fintype.card F : ENNReal)⁻¹)
        ≤ ((Set.range (fun p : ↥T ↦
          (μ₁ - (p : F × F).1) / ((p : F × F).2 - μ₂))).ncard : ENNReal) := by
  classical
  obtain ⟨μ₂, hμ₂⟩ : ∃ μ₂ : F, μ₂ ∉ T.image Prod.snd := by
    by_contra h
    simp only [not_exists, not_not] at h
    have heq : T.image Prod.snd = Finset.univ := Finset.eq_univ_iff_forall.mpr h
    have h2 : Fintype.card F ≤ T.card := by
      rw [← Finset.card_univ (α := F), ← heq]; exact Finset.card_image_le
    exact absurd h2 (not_le.mpr hTcard)
  have hμ₂' : ∀ p ∈ T, p.2 ≠ μ₂ := fun p hp h ↦ hμ₂ (h ▸ Finset.mem_image_of_mem Prod.snd hp)
  set g' : F → (↥T → F) := fun μ₁ p ↦ (μ₁ - (p : F × F).1) / ((p : F × F).2 - μ₂) with hg'
  set Φ' : PMF (↥T → F) := (PMF.uniformOfFintype F).map g' with hΦ'
  have hcoll : ∀ x y : ↥T, x ≠ y →
      Pr_{ let φ ← Φ' }[φ x = φ y] ≤ (Fintype.card F : ENNReal)⁻¹ := by
    intro x y hxy
    rw [hΦ', Pr_map_eq]
    have hxy' : (x : F × F) ≠ (y : F × F) := fun h ↦ hxy (Subtype.ext h)
    have hpq : ((x : F × F).1, (x : F × F).2) ≠ ((y : F × F).1, (y : F × F).2) := by
      simpa using hxy'
    simp only [hg']
    exact prob_uniform_le_inv_of_card_le_one _
      (affine_collision_card_le_one (hμ₂' x x.2) (hμ₂' y y.2) hpq)
  obtain ⟨φ, hφ_supp, hφ_card⟩ :=
    exists_large_image_of_pairwise_collision_bound_of_Pr
      Φ' (Fintype.card F : ENNReal)⁻¹ hcoll
  rw [hΦ', PMF.mem_support_map_iff] at hφ_supp
  obtain ⟨μ₁, _, hμ₁⟩ := hφ_supp
  refine ⟨μ₁, μ₂, hμ₂', ?_⟩
  have hcardT : (Fintype.card ↥T) = T.card := Fintype.card_coe T
  have hfun : (fun p : ↥T ↦
      (μ₁ - (p : F × F).1) / ((p : F × F).2 - μ₂)) = φ := by
    exact rfl.trans hμ₁
  rw [hfun, ← hcardT]
  refine hφ_card.trans_eq ?_
  norm_cast
  rw [← Set.ncard_coe_finset]
  congr 1
  ext z
  simp

omit [Fintype F] [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- **Fixed-encoding winning-set membership (agreement form).** Generalises
`mem_winningSetFor_zero_of_relClose` to arbitrary instance data `(v, μ₁, μ₂)`, against
the *fixed-encoding* winning set `winningSetFor enc` (Definition 6.11 of [ABF26]
with the code's encoding pinned — the faithful object for the §6.4.1 attack).

If `f₁ + γ·f₂` agrees with the codeword `enc m` on a column set `S` covering at
least a `(1 - δ)`-fraction of `ι`, and the message `m` satisfies the linear
constraint `⟨m, v⟩ = μ₁ + γ·μ₂`, then `γ` is a winning challenge (paper: "every
`γ = (μ₁−a₁)/(a₂−μ₂)` belongs to `Ω`"). -/
theorem mem_winningSetFor_of_agree {k : ℕ} {δ : ℝ≥0}
    (enc : (Fin k → F) →ₗ[F] (ι → A))
    {v : Fin k → F} {μ₁ μ₂ : F} {f₁ f₂ : ι → A} {γ : F} {m : Fin k → F}
    (hconstr : ∑ j, m j * v j = μ₁ + γ * μ₂)
    (S : Finset ι) (hScard : (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card)
    (hagree : ∀ j ∈ S, f₁ j + γ • f₂ j = enc m j) :
    γ ∈ winningSetFor enc δ v μ₁ μ₂ f₁ f₂ := by
  rw [winningSetFor, Set.mem_setOf_eq]
  exact ⟨fun _ ↦ enc m,
    ⟨fun _ ↦ m, fun _ ↦ rfl, fun _ ↦ hconstr⟩,
    S, hScard, fun _ j hj ↦ hagree j hj⟩

/-- **Real-arithmetic chain closing ABF26 §6.4.1.** From the first Claim-B.1
lower bound `N·|F|/(|F|+N−1) ≤ s` (here `s = |S_v|`), the second Claim-B.1
application's winning fraction `|F|·s/(|F|+s−1)` is at least the final bound
`N·|F|/(|F|+2N)`.

The paper argues via the increasing map `z ↦ z/(|F|+z−1)` and the inequality
`(|F|−1)²+(2|F|−1)N ≤ |F|²+2|F|N`; after clearing denominators the whole chain
collapses to `N·(|F|−1) ≤ s·(|F|+N)`, which follows from `N·|F| ≤ s·(|F|+N−1)`
and `s ≥ 0`. -/
lemma listDecoding_div_le_div {Fc N s : ℝ} (hF : (1 : ℝ) ≤ Fc) (hN : (1 : ℝ) ≤ N)
    (hslb : N * Fc / (Fc + N - 1) ≤ s) :
    N * Fc / (Fc + 2 * N) ≤ Fc * s / (Fc + s - 1) := by
  have hFN1 : (0 : ℝ) < Fc + N - 1 := by linarith
  have hslb' : N * Fc ≤ s * (Fc + N - 1) := by rwa [div_le_iff₀ hFN1] at hslb
  have hs1 : (1 : ℝ) ≤ s := by
    refine le_trans ?_ hslb
    rw [le_div_iff₀ hFN1]
    nlinarith [mul_nonneg (by linarith : (0 : ℝ) ≤ N - 1) (by linarith : (0 : ℝ) ≤ Fc - 1)]
  have hFs1 : (0 : ℝ) < Fc + s - 1 := by linarith
  have hF2N : (0 : ℝ) < Fc + 2 * N := by linarith
  rw [div_le_div_iff₀ hF2N hFs1]
  nlinarith [mul_le_mul_of_nonneg_left hslb' (by linarith : (0 : ℝ) ≤ Fc), hs1, hN, hF,
    mul_nonneg (by linarith : (0:ℝ) ≤ s) (by linarith : (0:ℝ) ≤ N)]

omit [DecidableEq F] in
/-- **Lemma 6.12 of [ABF26]** (list-decoding lower bound on the simplified IOR).

Coding-theory form: if `C` is a linear code (the image of an `F`-linear
encoding of message dimension `k`) and `|Λ(C^{≡2}, δ)| < |F|`,
then there exist witnesses `(v, μ_1, μ_2, f_1, f_2)` with `(f_1, f_2)` lying
**outside** the relaxed relation `R̃_{C,δ}^2` (the `violates` conjunct), for
which the winning challenge set `Ω^{f_1,f_2}_{v,μ_1,μ_2}` (Definition 6.11)
has at least `|Λ(C^{≡2}, δ)| · |F| / (|F| + 2·|Λ(C^{≡2}, δ)|)` elements.

The protocol-level reading: the soundness error of the simplified IOR
`T'[C, t]` (Construction 6.9, `ToyProblem.SimplifiedIOR.oracleReduction`) is
at least `|Λ(C^{≡2}, δ)| / (|F| + 2·|Λ(C^{≡2}, δ)|)`.

## Statement provenance (corrected 2026-06-04, finding S5)

Writing `N := |Λ(C^{≡2}, δ)|`, `F := |F|`, the **final** soundness bound in
ABF26 §6.4.1 (canonical `.tex` `lemma:list-decoding-attack`)
is `N / (F + 2N)`, hence the winning-set cardinality bound `N · F / (F + 2N)`.
The earlier in-tree denominator `F + N − 1` was the *intermediate* `|S_v|`
bound from the **first** Claim-B.1 application (paper step 3); the winning set
is bounded only after a **second** B.1 application (step 4) by
`F · |S_v| / (F + |S_v| − 1)`, which the paper then chains down (via the
increasing map `z ↦ z/(F + z − 1)` and `(F−1)² + (2F−1)N ≤ F² + 2FN`) to the
final `N/(F + 2N)`. The old `N · F / (F + N − 1)` therefore *overshot* the
provable bound. The corrected `N · F / (F + 2N)` matches the `.tex`.

## Proof recipe (ABF26 §6.4.1, with B.1 now machine-checked)

The intermediate `|S_v| ≥ N · F / (F + N − 1)` is exactly the conclusion of
Claim B.1 specialised to `|S| = N`, `|T| = F`, `ε = 1/F`:
`N / (1 + (N − 1) · (1/F)) = N · F / (F + N − 1)`, so the proof skeleton is:

1. **Build the list.** Enumerate `Λ(C^{≡2}, δ)` as pairs `(W₀(λ), W₁(λ))` of
   `δ`-close codewords in `C` (paper `(v_0(λ), v_1(λ))`). Pick `v ∈ F^k` and
   define `φ_v : λ ↦ (⟨W₀(λ), v⟩, ⟨W₁(λ), v⟩)`.

2. **Pairwise collision bound.** For distinct list entries the linear
   functional `⟨·, v⟩` collides with probability `≤ 1/F` over `v ←$ F^k`.

3. **Apply B.1 (first time).** Obtain `v*` with `|S_{v*}| ≥ N·F/(F+N−1)`.

4. **Apply B.1 (second time) + violation.** Pick `μ₂` not a second coordinate
   in `S_{v*}` and (by a second B.1 on the affine map `(a₁,a₂) ↦
   (μ₁−a₁)/(a₂−μ₂)`) a `μ₁` giving a winning set of size
   `≥ F·|S_{v*}|/(F+|S_{v*}|−1)`. Since `(μ₁,μ₂) ∉ S_{v*}`, the instance
   violates `R̃_{C,δ}^2` (the `violates` conjunct). Chasing the algebra gives
   the final `N·F/(F+2N)`.

The encoding hypothesis is `∃ enc, Function.Injective enc ∧ range enc = C` — the
faithful "linear code of dimension `k`" assumption (an injective `F`-linear
encoding onto `C`), which is what makes `Λ(C^{≡2}, δ)` enumerable by *message*
pairs `F^k × F^k` (the inner products `⟨·, v⟩` of paper step 1 live on messages).
This matches L6.13's hypothesis shape and the pinned `encode` of
`ToyProblem.RelationFor` (Definition 6.1's "code as the injective map").

The statement is against the **fixed-encoding** relation and winning set
(`RelaxedRelationFor enc`, `winningSetFor enc`), with `enc` the code's injective
`F`-linear encoding (`Set.range enc = C`). This is the paper's `R_C`. (Against
an existential-encoding relaxed relation the violation conjunct is false — an
adversary reparameterises the constraint through another encoding; that
defective family has been deleted from `Definitions.lean`.)

The proof decomposes into reusable, separately-verified pieces:
`exists_dotProduct_image_card_le` (first B.1, inner-product collision via
`prob_dotProduct_eq_zero_le`), `exists_affine_image_card_le` (second B.1, affine
collision via `affine_collision_card_le_one`), `image_bound_toReal` (the
ENNReal→ℝ bridge), `listDecoding_div_le_div` (the `z ↦ z/(F+z−1)` denominator
chain), and `mem_winningSetFor_of_agree` (the membership step). -/
theorem exists_winningSetFor_ncard_ge_of_lambda_lt_card {k : ℕ}
    [Nonempty ι]
    (C : ModuleCode ι F A) (δ : ℝ≥0) (_hδ_pos : (0 : ℝ≥0) < δ) (_hδ_lt : δ < 1)
    (enc : (Fin k → F) →ₗ[F] (ι → A)) (hinj : Function.Injective enc)
    (hC : Set.range enc = (C : Set (ι → A)))
    (hF : ((Lambda
      (((C^⋈(Fin 2) : ModuleCode ι F (Fin 2 → A)) : Set (ι → Fin 2 → A)))
      (δ : ℝ)).toNat : ℝ) < Fintype.card F) :
    ∃ (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → A),
      ¬ RelaxedRelationFor (ℓ := 2) enc δ v ![μ₁, μ₂] ![f₁, f₂] ∧
      ((winningSetFor enc δ v μ₁ μ₂ f₁ f₂).ncard : ℝ) ≥
        (((Lambda
          (((C^⋈(Fin 2) : ModuleCode ι F (Fin 2 → A)) : Set (ι → Fin 2 → A)))
          (δ : ℝ)).toNat : ℝ) * Fintype.card F)
          / (Fintype.card F
              + 2 * ((Lambda
                (((C^⋈(Fin 2) : ModuleCode ι F (Fin 2 → A)) : Set (ι → Fin 2 → A)))
                (δ : ℝ)).toNat : ℝ)) := by
  classical
  set Cint : Set (ι → Fin 2 → A) :=
    ((C ^⋈ (Fin 2) : ModuleCode ι F (Fin 2 → A)) : Set (ι → Fin 2 → A))
    with hCint
  obtain ⟨fStar, hfStar⟩ :=
    Code.exists_encard_eq_Lambda_of_finite (C := Cint) (δ : ℝ)
  set N : ℕ := (Lambda Cint (δ : ℝ)).toNat with hNdef
  have hNeq : N = (closeCodewordsRel Cint fStar (δ : ℝ)).ncard := by
    rw [hNdef, ← hfStar]
    exact (Set.ncard_def _).symm
  set f₁ : ι → A := fun i ↦ fStar i 0 with hf1
  set f₂ : ι → A := fun i ↦ fStar i 1 with hf2
  have hcardF1 : 1 ≤ Fintype.card F := Fintype.card_pos
  have hNltF : N < Fintype.card F := by exact_mod_cast hF
  -- Message-pair enumeration of `Λ(C^{≡2}, δ, (f₁,f₂))`.
  set Smsg : Finset ((Fin k → F) × (Fin k → F)) :=
    Finset.univ.filter (fun p ↦ encStack enc p ∈ closeCodewordsRel Cint fStar (δ : ℝ)) with hSmsg
  -- ENUMERATION (bijection codewords ↔ message pairs via the injective `enc`).
  -- `encStack enc` is injective: its two columns determine `enc m.1, enc m.2`, hence (by
  -- `hinj`) `m.1, m.2`.
  have hencStack_inj : Function.Injective (encStack enc) := by
    intro p q hpq
    have h1 : enc p.1 = enc q.1 := by
      rw [← encStack_transpose_zero enc p, ← encStack_transpose_zero enc q, hpq]
    have h2 : enc p.2 = enc q.2 := by
      rw [← encStack_transpose_one enc p, ← encStack_transpose_one enc q, hpq]
    exact Prod.ext (hinj h1) (hinj h2)
  have hSmsgN : Smsg.card = N := by
    -- ABF26-L6.12 enumeration: `encStack enc` is a bijection from the message pairs `Smsg`
    -- onto `closeCodewordsRel C^{≡2} fStar δ`. Injective by `hencStack_inj`; surjective
    -- since every close codeword stack `V` has both columns in `C = range enc`.
    rw [hNeq]
    -- The image of `Smsg` under `encStack enc` is exactly the close-codewords set.
    have himg : (encStack enc) '' (Smsg : Set ((Fin k → F) × (Fin k → F)))
        = (closeCodewordsRel Cint fStar (δ : ℝ) : Set (Matrix ι (Fin 2) A)) := by
      ext V
      simp only [Set.mem_image, Finset.mem_coe, hSmsg, Finset.mem_filter,
        Finset.mem_univ, true_and]
      constructor
      · rintro ⟨p, hp, rfl⟩; exact hp
      · intro hV
        -- `V`'s columns are codewords: `V.transpose 0 = enc m₀`, `V.transpose 1 = enc m₁`.
        have hcol0 : (fun i ↦ V i 0) ∈ Set.range enc := by
          rw [hC]
          exact hV.1 0
        have hcol1 : (fun i ↦ V i 1) ∈ Set.range enc := by
          rw [hC]
          exact hV.1 1
        obtain ⟨m₀, hm₀⟩ := hcol0
        obtain ⟨m₁, hm₁⟩ := hcol1
        refine ⟨(m₀, m₁), ?_, ?_⟩
        · -- `encStack enc (m₀, m₁) ∈ closeCodewordsRel`, since it equals `V`.
          have hVeq : encStack enc (m₀, m₁) = V := by
            funext i j; fin_cases j
            · change encStack enc (m₀, m₁) i 0 = V i 0
              rw [encStack_apply_zero]; exact congrFun hm₀ i
            · change encStack enc (m₀, m₁) i 1 = V i 1
              rw [encStack_apply_one]; exact congrFun hm₁ i
          rw [hVeq]; exact hV
        · funext i j; fin_cases j
          · change encStack enc (m₀, m₁) i 0 = V i 0
            rw [encStack_apply_zero]; exact congrFun hm₀ i
          · change encStack enc (m₀, m₁) i 1 = V i 1
            rw [encStack_apply_one]; exact congrFun hm₁ i
    calc Smsg.card
        = (Smsg : Set ((Fin k → F) × (Fin k → F))).ncard := (Set.ncard_coe_finset _).symm
      _ = (encStack enc '' (Smsg : Set ((Fin k → F) × (Fin k → F)))).ncard :=
          (Set.ncard_image_of_injective _ hencStack_inj).symm
      _ = (closeCodewordsRel Cint fStar (δ : ℝ)).ncard := by rw [himg]
  have hcardSmsg : Fintype.card ↥Smsg = N := by rw [Fintype.card_coe, hSmsgN]
  -- FIRST B.1: a constraint vector `v` with a large inner-product image `S_v`.
  obtain ⟨v, hv⟩ :=
    exists_dotProduct_image_card_le (Subtype.val : ↥Smsg → (Fin k → F) × (Fin k → F))
      Subtype.coe_injective
  rw [hcardSmsg] at hv
  set Sv : Finset (F × F) := Finset.univ.image
    (fun s : ↥Smsg ↦ ((∑ j, (s : (Fin k → F) × (Fin k → F)).1 j * v j),
                       (∑ j, (s : (Fin k → F) × (Fin k → F)).2 j * v j))) with hSvdef
  have hSvcard : (Set.range (fun s : ↥Smsg ↦
      ((∑ j, (s : (Fin k → F) × (Fin k → F)).1 j * v j),
       (∑ j, (s : (Fin k → F) × (Fin k → F)).2 j * v j)))).ncard = Sv.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext z
    simp [hSvdef]
  rw [hSvcard] at hv
  -- `|S_v| ≤ N < |F|`.
  have hSvle : Sv.card ≤ N := by
    rw [← hcardSmsg, hSvdef]; exact le_trans Finset.card_image_le (le_of_eq (Finset.card_univ))
  have hSvltF : Sv.card < Fintype.card F := lt_of_le_of_lt hSvle hNltF
  -- SECOND B.1: pick `μ₂` off the second coordinates and a winning `μ₁`.
  obtain ⟨μ₁, μ₂, hμ₂off, hwin⟩ := exists_affine_image_card_le Sv hSvltF
  set winImg : Finset F := Sv.image (fun p ↦ (μ₁ - p.1) / (p.2 - μ₂)) with hwinImg
  have hwinCard : (Set.range (fun p : ↥Sv ↦
      (μ₁ - (p : F × F).1) / ((p : F × F).2 - μ₂))).ncard = winImg.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext z
    simp [hwinImg]
  rw [hwinCard] at hwin
  refine ⟨v, μ₁, μ₂, f₁, f₂, ?_, ?_⟩
  · -- VIOLATION CONJUNCT (against the fixed-encoding `RelaxedRelationFor enc`).
    --
    -- The paper's violation `Δ((f₁,f₂), R²[x]) > δ` is, under the code's fixed
    -- encoding, exactly `(μ₁,μ₂) ∉ S_v`. PROOF: suppose `RelaxedRelationFor enc`
    -- holds — extract `Wstar` with `Wstar i = enc (M i)` and `∑ⱼ M i j vⱼ = μ i`
    -- (so `⟨M 0, v⟩ = μ₁`, `⟨M 1, v⟩ = μ₂`), δ-close to `![f₁,f₂]` on a set `S'`.
    -- Then `encStack enc (M 0, M 1) = Wstar` is δ-close to `fStar`, so it lies in
    -- `closeCodewordsRel Cint fStar δ` (columns `enc (M i) ∈ C` via `hC`; distance
    -- from the `S'` agreement, reverse of the reconciliation used for `hmem`).
    -- Hence `(M 0, M 1) ∈ Smsg`, so `φ_v(M 0, M 1) = (μ₁, μ₂) ∈ S_v` — contradicting
    -- `hμ₂off` (`(μ₁,μ₂).2 = μ₂` is a second coordinate of `S_v`). ABF26-L6.12.
    rintro ⟨Wstar, ⟨M, hWeq, hconstr⟩, S', hS'card, hS'ag⟩
    -- `(M 0, M 1) ∈ Smsg`: build the agreement set `S'` for `encStack enc (M 0, M 1)`.
    have hmemSmsg : (M 0, M 1) ∈ Smsg := by
      rw [hSmsg, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [encStack_mem_closeCodewordsRel_iff enc C hC _hδ_lt]
      refine ⟨S', hS'card, fun i hi ↦ ⟨?_, ?_⟩⟩
      · -- `fStar i 0 = f₁ i = ![f₁,f₂] 0 i = Wstar 0 i = enc (M 0) i = enc (M 0,M 1).1 i`
        have hag : f₁ i = Wstar 0 i := hS'ag 0 i hi
        -- `f₁ i = fStar i 0` definitionally.
        change fStar i 0 = enc (M 0) i
        rw [show fStar i 0 = f₁ i from rfl, hag, hWeq 0]
      · have hag : f₂ i = Wstar 1 i := hS'ag 1 i hi
        change fStar i 1 = enc (M 1) i
        rw [show fStar i 1 = f₂ i from rfl, hag, hWeq 1]
    -- `(μ₁, μ₂) ∈ S_v`, contradicting `hμ₂off`.
    have hpair : ((∑ j, (M 0) j * v j), (∑ j, (M 1) j * v j)) = (μ₁, μ₂) := by
      have h0 : ∑ j, (M 0) j * v j = μ₁ := hconstr 0
      have h1 : ∑ j, (M 1) j * v j = μ₂ := hconstr 1
      rw [h0, h1]
    have hμ₂mem : (μ₁, μ₂) ∈ Sv := by
      rw [hSvdef, Finset.mem_image]
      exact ⟨⟨(M 0, M 1), hmemSmsg⟩, Finset.mem_univ _, hpair⟩
    exact hμ₂off (μ₁, μ₂) hμ₂mem rfl
  · -- CARDINALITY CHAIN.
    rcases Nat.eq_zero_or_pos N with hN0 | hN1
    · -- N = 0: the bound is `0 ≤ ncard`, trivially true.
      rw [hN0, ge_iff_le]; simp
    -- Main case N ≥ 1.
    -- MEMBERSHIP: every winning challenge in `winImg` lies in the winning set.
    have hmem : (winImg : Set F) ⊆ winningSetFor enc δ v μ₁ μ₂ f₁ f₂ := by
      -- ABF26-L6.12 membership: each `γ = (μ₁−a)/(b−μ₂)` with `(a,b) = φ_v(m)`,
      -- `m ∈ Smsg`, is winning via `mem_winningSetFor_of_agree` (message `m.1+γ•m.2`,
      -- constraint `⟨m.1+γ·m.2, v⟩ = a+γb = μ₁+γμ₂`, agreement from `encStack`
      -- closeness + `enc`-linearity). Uses the same agreement-cols reconciliation
      -- as `mem_winningSetFor_zero_of_relClose`.
      intro γ hγ
      rw [Finset.coe_image, Set.mem_image] at hγ
      obtain ⟨⟨a, b⟩, hab, hγeq⟩ := hγ
      -- `hγeq : (μ₁ - a)/(b - μ₂) = γ`
      rw [hSvdef, Finset.mem_coe, Finset.mem_image] at hab
      obtain ⟨s, _, hsab⟩ := hab
      -- `m = ↑s` is a message pair in `Smsg`; extract its agreement set `S'`.
      set m : (Fin k → F) × (Fin k → F) := (s : (Fin k → F) × (Fin k → F)) with hm
      have hmSmsg : m ∈ Smsg := s.2
      rw [hSmsg, Finset.mem_filter] at hmSmsg
      obtain ⟨S', hS'card, hS'ag⟩ :=
        (encStack_mem_closeCodewordsRel_iff enc C hC _hδ_lt m).mp hmSmsg.2
      -- The image point: `a = ∑ⱼ m.1 ⱼ vⱼ`, `b = ∑ⱼ m.2 ⱼ vⱼ`.
      have hab_eq : (∑ j, m.1 j * v j) = a ∧ (∑ j, m.2 j * v j) = b := by
        have := Prod.ext_iff.mp hsab; exact ⟨this.1, this.2⟩
      obtain ⟨ha, hb⟩ := hab_eq
      -- `b ≠ μ₂` (so the affine challenge is well-defined).
      have hbμ₂ : b ≠ μ₂ := hμ₂off (a, b) (by
        rw [hSvdef, Finset.mem_image]; exact ⟨s, Finset.mem_univ _, hsab⟩)
      -- Apply the membership helper with message `m.1 + γ • m.2`.
      refine mem_winningSetFor_of_agree enc (m := m.1 + γ • m.2) ?_ S' hS'card ?_
      · -- constraint `⟨m.1 + γ•m.2, v⟩ = a + γ b = μ₁ + γ μ₂`.
        have hsum : (∑ j, (m.1 + γ • m.2) j * v j) = a + γ * b := by
          simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul, mul_assoc]
          rw [Finset.sum_add_distrib, ← Finset.mul_sum, ha, hb]
        rw [hsum]
        -- `γ = (μ₁ - a)/(b - μ₂)`, `b ≠ μ₂` ⇒ `γ*(b - μ₂) = μ₁ - a` ⇒ `a + γ b = μ₁ + γ μ₂`.
        have hbsub : b - μ₂ ≠ 0 := sub_ne_zero.mpr hbμ₂
        rw [← hγeq]
        field_simp
        ring
      · -- agreement: on `S'`, `f₁ i + γ•f₂ i = enc m.1 i + γ•enc m.2 i = enc (m.1+γ•m.2) i`.
        intro i hi
        obtain ⟨h0, h1⟩ := hS'ag i hi
        have henc : enc (m.1 + γ • m.2) i = enc m.1 i + γ • enc m.2 i := by
          rw [map_add, map_smul]; simp [Pi.add_apply, Pi.smul_apply]
        rw [henc]
        -- `f₁ i = fStar i 0 = enc m.1 i`, `f₂ i = fStar i 1 = enc m.2 i`.
        rw [show f₁ i = fStar i 0 from rfl, show f₂ i = fStar i 1 from rfl, h0, h1]
    -- A + bridge: `N·F/(F+N−1) ≤ |S_v|`.
    have hAreal : (N : ℝ) * Fintype.card F / (Fintype.card F + N - 1) ≤ (Sv.card : ℝ) :=
      image_bound_toReal hcardF1 hN1 hv
    -- B + bridge: `|S_v|·F/(F+|S_v|−1) ≤ |winImg|`.
    have hSv1 : 1 ≤ Sv.card := by
      rcases Nat.eq_zero_or_pos Sv.card with h0 | h; swap; · exact h
      -- |S_v| = 0 would force the A-bound `N·F/(F+N−1) ≤ 0`, impossible for N ≥ 1.
      exfalso
      have hpos : (0 : ℝ) < (N : ℝ) * Fintype.card F / (Fintype.card F + N - 1) := by
        have : (0 : ℝ) < Fintype.card F + N - 1 := by
          have : (1 : ℝ) ≤ N := by exact_mod_cast hN1
          have : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast hcardF1
          linarith
        positivity
      rw [h0] at hAreal; norm_num at hAreal; linarith
    have hBreal : (Sv.card : ℝ) * Fintype.card F / (Fintype.card F + Sv.card - 1)
        ≤ (winImg.card : ℝ) := image_bound_toReal hcardF1 hSv1 hwin
    -- Denominator chain.
    have hchain : (N : ℝ) * Fintype.card F / (Fintype.card F + 2 * N)
        ≤ Fintype.card F * (Sv.card : ℝ) / (Fintype.card F + Sv.card - 1) :=
      listDecoding_div_le_div (by exact_mod_cast hcardF1) (by exact_mod_cast hN1) hAreal
    have hwinge : (N : ℝ) * Fintype.card F / (Fintype.card F + 2 * N) ≤ (winImg.card : ℝ) := by
      refine le_trans hchain (le_trans (le_of_eq ?_) hBreal)
      ring
    -- winImg ⊆ winningSet ⇒ |winImg| ≤ ncard(winningSet).
    have hncard : (winImg.card : ℝ) ≤ ((winningSetFor enc δ v μ₁ μ₂ f₁ f₂).ncard : ℝ) := by
      have : winImg.card ≤ (winningSetFor enc δ v μ₁ μ₂ f₁ f₂).ncard := by
        rw [← Set.ncard_coe_finset winImg]
        exact Set.ncard_le_ncard hmem (Set.toFinite _)
      exact_mod_cast this
    rw [ge_iff_le]
    exact le_trans hwinge hncard

/-! ## Correlated-agreement lower bridge -/

omit [Fintype F] [DecidableEq F] [Fintype A] in
/-- If an affine fold is close to a linear code, then the same challenge wins
the all-zero constrained toy instance. -/
theorem mem_winningSetFor_zero_of_relClose {k : ℕ} [Nonempty ι]
    {C : Set (ι → A)} {δ : ℝ≥0} (hδ_lt : δ < 1)
    (enc : (Fin k → F) →ₗ[F] (ι → A)) (hC : Set.range enc = C)
    (f₁ f₂ : ι → A) {γ : F} (hγ : δᵣ(f₁ + γ • f₂, C) ≤ δ) :
    γ ∈ winningSetFor enc δ (0 : Fin k → F) 0 0 f₁ f₂ := by
  classical
  rw [winningSetFor, Set.mem_setOf_eq]
  rw [relCloseToCode_iff_relCloseToCodeword_of_minDist] at hγ
  obtain ⟨w, hwC, hwd⟩ := hγ
  obtain ⟨m, hm⟩ : ∃ m, enc m = w := by
    rw [← hC] at hwC
    exact hwC
  refine ⟨fun _ ↦ w,
    ⟨fun _ ↦ m, fun i ↦ by simp [hm], fun i ↦ by simp⟩, ?_⟩
  rw [relCloseToWord_iff_exists_agreementCols] at hwd
  obtain ⟨S, hScard, hSagree⟩ := hwd
  refine ⟨S, ?_, ?_⟩
  · have hcomp :=
      (relDist_floor_bound_iff_complement_bound (Fintype.card ι) S.card δ).mp hScard
    have hcoe : ((1 - δ : ℝ≥0) : ℝ) = 1 - (δ : ℝ) := by
      rw [NNReal.coe_sub hδ_lt.le]
      simp
    have hcompR := NNReal.coe_le_coe.mpr hcomp
    rw [NNReal.coe_mul, hcoe] at hcompR
    push_cast at hcompR ⊢
    linarith
  · intro i j hj
    have hagree := (hSagree j).1 hj
    simpa only [Pi.add_apply, Pi.smul_apply] using hagree

omit [DecidableEq F] in
/-- ABF26 Lemma 6.13 in fixed-encoding form: positive correlated-agreement
error yields an explicit violating instance whose winning-set ratio
lower-bounds that error. -/
theorem exists_winningSetFor_ncard_ge_of_epsCa_pos {k : ℕ} [Nonempty ι]
    (C : Set (ι → A)) (δ : ℝ≥0) (_hδ_pos : (0 : ℝ≥0) < δ)
    (hδ_lt : δ < 1)
    (enc : (Fin k → F) →ₗ[F] (ι → A))
    (_henc_inj : Function.Injective enc) (hC : Set.range enc = C)
    (hca : 0 < epsCa (F := F) (A := A) C δ δ) :
    ∃ (v : Fin k → F) (μ₁ μ₂ : F) (f₁ f₂ : ι → A),
      ¬ RelaxedRelationFor (ℓ := 2) enc δ v ![μ₁, μ₂] ![f₁, f₂] ∧
      ((winningSetFor enc δ v μ₁ μ₂ f₁ f₂).ncard : ENNReal) ≥
        epsCa (F := F) (A := A) C δ δ *
          (Fintype.card F : ENNReal) := by
  classical
  obtain ⟨u, hu_max⟩ := Finite.exists_max
    (fun u : WordStack A (Fin 2) ι ↦
      if jointProximity C u δ then (0 : ENNReal)
      else Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ])
  have h_eps : epsCa (F := F) (A := A) C δ δ =
      (if jointProximity C u δ then (0 : ENNReal)
       else Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ]) := by
    refine le_antisymm ?_ ?_
    · rw [epsCa]
      exact iSup_le hu_max
    · rw [epsCa]
      exact le_iSup (fun w : WordStack A (Fin 2) ι ↦
        if jointProximity C w δ then (0 : ENNReal)
        else Pr_{let γ ← $ᵖ F}[δᵣ(w 0 + γ • w 1, C) ≤ δ]) u
  have hjp : ¬ jointProximity C u δ := by
    intro h
    rw [h_eps, if_pos h] at hca
    exact lt_irrefl _ hca
  rw [if_neg hjp] at h_eps
  refine ⟨0, 0, 0, u 0, u 1, ?_, ?_⟩
  · intro hrel
    apply hjp
    have hu_eq : u = ![u 0, u 1] := by
      funext i
      fin_cases i <;> rfl
    rw [hu_eq, ← jointAgreement_iff_jointProximity]
    obtain ⟨Wstar, ⟨M, hWstar, _hconstr⟩, S, hScard, hSag⟩ := hrel
    refine ⟨S, ?_, Wstar, fun i ↦
      ⟨hWstar i ▸ (hC ▸ Set.mem_range_self (M i)), ?_⟩⟩
    · have hcoe : ((1 - δ : ℝ≥0) : ℝ) = 1 - (δ : ℝ) := by
        rw [NNReal.coe_sub hδ_lt.le]
        simp
      rw [ge_iff_le, ← NNReal.coe_le_coe, NNReal.coe_mul, hcoe]
      push_cast
      linarith [hScard]
    · intro j hj
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ j, (hSag i j hj).symm⟩
  · rw [h_eps]
    have hsub : {γ : F | δᵣ(u 0 + γ • u 1, C) ≤ δ} ⊆
        winningSetFor enc δ 0 0 0 (u 0) (u 1) :=
      fun γ hγ ↦ mem_winningSetFor_zero_of_relClose
        hδ_lt enc hC (u 0) (u 1) hγ
    have hF0 : (Fintype.card F : ℝ≥0) ≠ 0 := by
      simp [Fintype.card_ne_zero]
    have hprob :
        Pr_{let γ ← $ᵖ F}[δᵣ(u 0 + γ • u 1, C) ≤ δ] *
            (Fintype.card F : ENNReal) =
          ({γ : F | δᵣ(u 0 + γ • u 1, C) ≤ δ}.ncard : ENNReal) := by
      rw [prob_uniform_eq_card_filter_div_card,
        Set.ncard_eq_toFinset_card', Set.toFinset_setOf]
      push_cast
      rw [ENNReal.div_mul_cancel (by exact_mod_cast hF0)
        (ENNReal.natCast_ne_top _)]
    rw [hprob]
    have hmono := Set.ncard_le_ncard hsub (Set.toFinite _)
    exact_mod_cast hmono

/-! ## Winning-set and extractor-certified error interfaces

The winning-set quantity below is the exact combinatorial supremum from ABF26
Definition 6.11.  It is deliberately distinct from
`certifiedGammaError`, the MCA-plus-list expression proved for the executable
extractor.  The bridge theorem makes their relationship explicit; the matching
optimal-adversary theorem needed to call the supremum an exact protocol-game
error is outside the proved interface. -/

/-- A two-row instance which violates the relaxed toy relation for the pinned
encoder.  These are precisely the instances indexed by Definition 6.11's
winning-set supremum. -/
structure ViolatingInstance {k : ℕ}
    (enc : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0) where
  v : Fin k → F
  μ₁ : F
  μ₂ : F
  f₁ : ι → A
  f₂ : ι → A
  violates : ¬ RelaxedRelationFor (ℓ := 2) enc δ v ![μ₁, μ₂] ![f₁, f₂]

/-- The Definition 6.11 supremum is never indexed by an empty type: the zero
constraint vector with first claimed value `1` cannot be satisfied by any
message, independently of the encoder or radius. -/
instance violatingInstanceNonempty {k : ℕ}
    (enc : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0) :
    Nonempty (ViolatingInstance enc δ) := by
  refine ⟨{
    v := 0
    μ₁ := 1
    μ₂ := 0
    f₁ := 0
    f₂ := 0
    violates := ?_ }⟩
  rintro ⟨Wstar, ⟨M, -, hlin⟩, -⟩
  have h := hlin 0
  simp at h

/-- The fraction of challenges won by one violating instance. -/
noncomputable def winningSetRatio {k : ℕ}
    {enc : (Fin k → F) →ₗ[F] (ι → A)} {δ : ℝ≥0}
    (x : ViolatingInstance enc δ) : ℝ≥0 :=
  ((winningSetFor enc δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard : ℝ≥0) /
    (Fintype.card F : ℝ≥0)

/-- Definition 6.11's worst-case winning-challenge density at radius `δ`.

This is an exact combinatorial quantity. The protocol-level upper coupling is proved below; the
matching optimal-adversary/lower-coupling theorem needed to identify it with a minimal game error
is not asserted here. -/
noncomputable def winningSetDensity {k : ℕ}
    (enc : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0) : ℝ≥0 :=
  ⨆ x : ViolatingInstance enc δ, winningSetRatio x

omit [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- A winning-challenge fraction is at most one. -/
theorem winningSetRatio_le_one {k : ℕ}
    {enc : (Fin k → F) →ₗ[F] (ι → A)} {δ : ℝ≥0}
    (x : ViolatingInstance enc δ) : winningSetRatio x ≤ 1 := by
  haveI : Nonempty F := ⟨0⟩
  have hpos : (0 : ℝ≥0) < (Fintype.card F : ℝ≥0) := by
    exact_mod_cast Fintype.card_pos
  rw [winningSetRatio, div_le_one hpos]
  have hle : (winningSetFor enc δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂).ncard ≤
      Fintype.card F := by
    have h := Set.ncard_le_ncard
      (Set.subset_univ (winningSetFor enc δ x.v x.μ₁ x.μ₂ x.f₁ x.f₂))
      Set.finite_univ
    rwa [Set.ncard_univ, Nat.card_eq_fintype_card] at h
  exact_mod_cast hle

omit [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- The family of winning-challenge fractions is bounded above. -/
theorem bddAbove_winningSetRatio {k : ℕ}
    (enc : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0) :
    BddAbove (Set.range (fun x : ViolatingInstance enc δ ↦ winningSetRatio x)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact winningSetRatio_le_one x

omit [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- Every explicit violating instance lower-bounds the worst-case winning-set density. -/
theorem winningSetRatio_le_winningSetDensity {k : ℕ}
    {enc : (Fin k → F) →ₗ[F] (ι → A)} {δ : ℝ≥0}
    (x : ViolatingInstance enc δ) :
    winningSetRatio x ≤ winningSetDensity enc δ :=
  le_ciSup (bddAbove_winningSetRatio enc δ) x

omit [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- The worst-case winning-set density never exceeds one. -/
theorem winningSetDensity_le_one {k : ℕ}
    (enc : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0) :
    winningSetDensity enc δ ≤ 1 :=
  ciSup_le' (fun x ↦ winningSetRatio_le_one x)

omit [DecidableEq F] in
/-- Correlated-agreement error lower-bounds the Definition 6.11 winning-set
quantity (ABF26 Lemma 6.13). -/
theorem epsCa_le_winningSetDensity {k : ℕ} [Nonempty ι]
    {C : Set (ι → A)} (δ : ℝ≥0) (hδpos : (0 : ℝ≥0) < δ)
    (hδlt : δ < 1) (enc : (Fin k → F) →ₗ[F] (ι → A))
    (henc_inj : Function.Injective enc) (henc_range : Set.range enc = C) :
    epsCa (F := F) (A := A) C δ δ ≤
      (winningSetDensity enc δ : ENNReal) := by
  rcases eq_or_lt_of_le
      (zero_le (a := epsCa (F := F) (A := A) C δ δ)) with hzero | hca
  · rw [← hzero]
    exact zero_le
  obtain ⟨v, μ₁, μ₂, f₁, f₂, hviol, hbound⟩ :=
    exists_winningSetFor_ncard_ge_of_epsCa_pos
      C δ hδpos hδlt enc henc_inj henc_range hca
  let x : ViolatingInstance enc δ := ⟨v, μ₁, μ₂, f₁, f₂, hviol⟩
  have hratio : (winningSetRatio x : ENNReal) =
      ((winningSetFor enc δ v μ₁ μ₂ f₁ f₂).ncard : ENNReal) /
        (Fintype.card F : ENNReal) := by
    rw [winningSetRatio,
      ENNReal.coe_div (by simp [Fintype.card_ne_zero])]
    push_cast
    rfl
  have hactual : (winningSetRatio x : ENNReal) ≤
      (winningSetDensity enc δ : ENNReal) := by
    exact_mod_cast winningSetRatio_le_winningSetDensity x
  refine le_trans ?_ hactual
  rw [hratio, ENNReal.le_div_iff_mul_le (Or.inl (by simp))
    (Or.inl (ENNReal.natCast_ne_top _))]
  exact hbound

omit [DecidableEq F] in
/-- The two-row point-list attack lower-bounds the Definition 6.11 winning-set
quantity (ABF26 Lemma 6.12). -/
theorem listDecoding_le_winningSetDensity {k : ℕ} [Nonempty ι]
    (C : ModuleCode ι F A) (δ : ℝ≥0) (hδpos : (0 : ℝ≥0) < δ)
    (hδlt : δ < 1) (enc : (Fin k → F) →ₗ[F] (ι → A))
    (henc_inj : Function.Injective enc)
    (henc_range : Set.range enc = (C : Set (ι → A)))
    (hF : ((Code.Lambda
      ((C^⋈(Fin 2) : ModuleCode ι F (Fin 2 → A)) : Set (ι → Fin 2 → A))
      (δ : ℝ)).toNat : ℝ) < Fintype.card F) :
    ((Code.Lambda
      ((C ^⋈ (Fin 2) : ModuleCode ι F (Fin 2 → A)) : Set (ι → Fin 2 → A))
      (δ : ℝ)).toNat : ℝ≥0) /
        ((Fintype.card F : ℝ≥0) +
          2 * ((Code.Lambda
            ((C ^⋈ (Fin 2) : ModuleCode ι F (Fin 2 → A)) :
              Set (ι → Fin 2 → A))
            (δ : ℝ)).toNat : ℝ≥0)) ≤ winningSetDensity enc δ := by
  obtain ⟨v, μ₁, μ₂, f₁, f₂, hviol, hbound⟩ :=
    exists_winningSetFor_ncard_ge_of_lambda_lt_card
      C δ hδpos hδlt enc henc_inj henc_range hF
  rw [ge_iff_le] at hbound
  let N : ℕ := (Code.Lambda
    ((C ^⋈ (Fin 2) : ModuleCode ι F (Fin 2 → A)) : Set (ι → Fin 2 → A))
    (δ : ℝ)).toNat
  let x : ViolatingInstance enc δ := ⟨v, μ₁, μ₂, f₁, f₂, hviol⟩
  refine le_trans ?_ (winningSetRatio_le_winningSetDensity x)
  have hcardF : (0 : ℝ) < (Fintype.card F : ℝ) := by
    exact_mod_cast Fintype.card_pos
  have hden : (0 : ℝ) < (Fintype.card F : ℝ) + 2 * N := by
    positivity
  have hkey : (N : ℝ) * Fintype.card F ≤
      ((winningSetFor enc δ v μ₁ μ₂ f₁ f₂).ncard : ℝ) *
        ((Fintype.card F : ℝ) + 2 * N) :=
    (div_le_iff₀ hden).mp hbound
  have hreal : (N : ℝ) / ((Fintype.card F : ℝ) + 2 * N) ≤
      ((winningSetFor enc δ v μ₁ μ₂ f₁ f₂).ncard : ℝ) /
        (Fintype.card F : ℝ) := by
    rw [div_le_div_iff₀ hden hcardF]
    linarith
  change (N : ℝ≥0) / ((Fintype.card F : ℝ≥0) + 2 * N) ≤
    winningSetRatio x
  rw [winningSetRatio, ← NNReal.coe_le_coe, NNReal.coe_div, NNReal.coe_div,
    NNReal.coe_add, NNReal.coe_mul]
  push_cast
  exact hreal

/-- The finite nonnegative-real reflection of the executable extractor's
canonical affine-line MCA-plus-two-row-list certificate. -/
noncomputable def certifiedGammaError
    (C : ModuleCode ι F A) (δ : ℝ≥0) : ℝ≥0 :=
  ENNReal.toNNReal <|
    mcaError (AffineLineGenerator F) C (δ : ℝ) +
      ((Code.Lambda
        ((C ^⋈ (Fin 2) : ModuleCode ι F (Fin 2 → A)) : Set (ι → Fin 2 → A))
        (δ : ℝ)).toNat : ENNReal) / (Fintype.card F : ENNReal)

omit [DecidableEq F] [Fintype A] [DecidableEq A] in
/-- `certifiedGammaError` coerces to the exact MCA-plus-list certificate. -/
theorem coe_certifiedGammaError (C : ModuleCode ι F A) (δ : ℝ≥0) :
    (certifiedGammaError C δ : ENNReal) =
      mcaError (AffineLineGenerator F) C (δ : ℝ) +
        ((Code.Lambda
          ((C ^⋈ (Fin 2) : ModuleCode ι F (Fin 2 → A)) : Set (ι → Fin 2 → A))
          (δ : ℝ)).toNat : ENNReal) / (Fintype.card F : ENNReal) := by
  rw [certifiedGammaError, ENNReal.coe_toNNReal]
  rw [ENNReal.add_ne_top]
  exact ⟨mcaError_ne_top _ _ _, ENNReal.div_ne_top (by simp) (by simp)⟩

/-- The Definition 6.11 winning-set quantity is bounded by the extractor-certified
MCA-plus-list error.  This is the quantitative content of ABF26 Lemma 6.10. -/
theorem winningSetDensity_le_certifiedGammaError {k : ℕ} [Nonempty ι]
    (C : ModuleCode ι F A) (δ : ℝ≥0)
    (hδ : δ ∈ Set.Ioo (0 : ℝ≥0)
      ((minRelHammingDistCode (C : Set (ι → A)) : ℝ≥0)))
    (enc : (Fin k → F) →ₗ[F] (ι → A))
    (henc_inj : Function.Injective enc)
    (henc_range : Set.range enc = (C : Set (ι → A))) :
    winningSetDensity enc δ ≤ certifiedGammaError C δ := by
  classical
  obtain ⟨hδpos, hδlt⟩ := hδ
  refine ciSup_le' (fun x ↦ ?_)
  obtain ⟨v, μ₁, μ₂, f₁, f₂, hviol⟩ := x
  have hNoWit : ¬ ∃ M : Fin 2 → (Fin k → F),
      (∀ i : Fin 2, ∑ j, M i j * v j = ![μ₁, μ₂] i) ∧
      ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
        ∀ i : Fin 2, ∀ j ∈ S, ![f₁, f₂] i j = enc (M i) j := by
    rintro ⟨M, hlin, S, hScard, hagree⟩
    exact hviol
      ⟨fun i ↦ enc (M i), ⟨M, fun _ ↦ rfl, hlin⟩, S, hScard, hagree⟩
  have hWSeq : winningSetFor enc δ v μ₁ μ₂ f₁ f₂ =
      {γ : F | ∃ m : Fin k → F,
        (∑ j, m j * v j = μ₁ + γ * μ₂) ∧
        ∃ S : Finset ι, (1 - (δ : ℝ)) * Fintype.card ι ≤ S.card ∧
          ∀ j ∈ S, f₁ j + γ • f₂ j = enc m j} := by
    ext γ
    constructor
    · rintro ⟨Wstar, ⟨M, hWeq, hlin⟩, S, hScard, hagree⟩
      refine ⟨M 0, by simpa using hlin 0, S, hScard, fun j hj ↦ ?_⟩
      have h := hagree 0 j hj
      rw [hWeq 0] at h
      simpa using h
    · rintro ⟨m, hlin, S, hScard, hagree⟩
      exact ⟨fun _ ↦ enc m,
        ⟨fun _ ↦ m, fun _ ↦ rfl, fun _ ↦ by simpa using hlin⟩,
        S, hScard, fun i j hj ↦ by simpa using hagree j hj⟩
  have hWEvent : winningSetFor enc δ v μ₁ μ₂ f₁ f₂ =
      {γ : F | GammaEvent enc δ v μ₁ μ₂ f₁ f₂ γ} := by
    simpa [GammaEvent] using hWSeq
  rw [← ENNReal.coe_le_coe, coe_certifiedGammaError]
  refine le_trans (le_of_eq ?_)
    (gamma_transition_prob_le C δ enc henc_inj henc_range hδpos hδlt
      v μ₁ μ₂ f₁ f₂ hNoWit)
  rw [winningSetRatio, prob_uniform_eq_card_filter_div_card, hWEvent,
    Set.ncard_eq_toFinset_card', Set.toFinset_setOf,
    ENNReal.coe_div (Nat.cast_ne_zero.mpr Fintype.card_ne_zero),
    ENNReal.coe_natCast, ENNReal.coe_natCast]

/-- A certified full-protocol fixed-radius upper bound: the exact worst-case
winning-set ratio for the combination round, mixed with the uniform
`(1 - δ)^t` upper bound for the spot-check round.

This is not claimed to equal the optimal full-protocol adversarial acceptance
probability: the actual spot-check acceptance outside the winning set can be
strictly smaller than `(1 - δ)^t`. -/
noncomputable def winningSetUpperBound {k : ℕ}
    (enc : (Fin k → F) →ₗ[F] (ι → A)) (δ : ℝ≥0) (t : ℕ) : ℝ≥0 :=
  (1 - δ) ^ t + winningSetDensity enc δ * (1 - (1 - δ) ^ t)

/-- The executable extractor's full fixed-radius certificate.  Unlike
`winningSetUpperBound`, its combination term is the proved MCA-plus-list
upper bound. -/
noncomputable def certifiedExtractorError
    (C : ModuleCode ι F A) (δ : ℝ≥0) (t : ℕ) : ℝ≥0 :=
  (1 - δ) ^ t + certifiedGammaError C δ * (1 - (1 - δ) ^ t)

/-- The winning-set/spot-check upper bound is no larger than the executable
extractor's certificate. -/
theorem winningSetUpperBound_le_certifiedExtractorError {k : ℕ}
    [Nonempty ι] (C : ModuleCode ι F A) (δ : ℝ≥0) (t : ℕ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ≥0)
      ((minRelHammingDistCode (C : Set (ι → A)) : ℝ≥0)))
    (enc : (Fin k → F) →ₗ[F] (ι → A))
    (henc_inj : Function.Injective enc)
    (henc_range : Set.range enc = (C : Set (ι → A))) :
    winningSetUpperBound enc δ t ≤ certifiedExtractorError C δ t := by
  rw [winningSetUpperBound, certifiedExtractorError]
  gcongr
  exact winningSetDensity_le_certifiedGammaError
    C δ hδ enc henc_inj henc_range

end ToyProblem
