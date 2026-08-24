/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ProximityGap.Errors

/-!
# Line decoding

Line decoding strengthens list decoding by requiring nearby words on a sampled affine line to
align with one affine pair of codewords. ArkLib follows [GG25] Definition 3.1, whose concluding
event requires both proximity and alignment. The proximity conjunct is absent from [ABF26]
Definition 4.20; without it, the stated MCA consequence is false. The discrepancy and a finite
counterexample are recorded in the
[ABF26 knowledge-base page](../../../../docs/kb/papers/ABF26.md).

## Main definitions

- `CodingTheory.IsLineDecodable` — `(δ, a, b)`-line-decodability of an `F`-additive code.

## Main statements

- `CodingTheory.IsLineDecodable.mcaError_le` — `(δ, a, n+1)`-line-decodability gives
  `ε_mca(C, δ) ≤ a / |F|`.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
  2026. §4.4.
- [GG25] Goyal-Guruswami. Definition 3.1 / Theorem 3.5 (original source).
-/

-- The proof-term statements below carry unused `Fintype`/`DecidableEq`/section hypotheses
-- (surfaced by the 4.32 linters when these proposition-valued `def`s became `theorem`s);
-- silenced file-wide to match the `CapacityBounds.lean` umbrella, scoped narrowly on revisit.
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false

namespace CodingTheory

open scoped NNReal ProbabilityTheory
open CoreDefinitions ProximityGap

section

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {A : Type} [Fintype A] [DecidableEq A] [AddCommGroup A] [Module F A]

open Classical in
/-- A code is `(δ, a, b)`-line-decodable when every family of nearby codewords along an affine
line that occurs with probability at least `a / |F|` agrees with one affine pair of codewords on
the same nearby challenges with probability at least `b / |F|`.

In formula:

  `∀ f₁ f₂ : ι → A, ∀ U : F → ι → A, (∀ γ, U γ ∈ C) →`
  `  Pr_γ [δᵣ(f₁ + γ • f₂, U γ) ≤ δ] ≥ a / |F| →`
  `  ∃ u₁ u₂ ∈ C, Pr_γ [δᵣ(f₁ + γ • f₂, U γ) ≤ δ ∧`
  `                            U γ = u₁ + γ • u₂] ≥ b / |F|`

The function `U` takes values in the ambient word space, with membership in `C` imposed
separately. Probabilities are `ENNReal`-valued. -/
def IsLineDecodable (C : Set (ι → A)) (δ : ℝ≥0) (a b : ℕ) : Prop :=
  ∀ f₁ f₂ : ι → A, ∀ U : F → ι → A, (∀ γ : F, U γ ∈ C) →
    (a : ENNReal) / (Fintype.card F : ENNReal)
        ≤ Pr_{let γ ← $ᵖ F}[δᵣ(f₁ + γ • f₂, U γ) ≤ δ] →
    ∃ u₁ ∈ C, ∃ u₂ ∈ C,
      (b : ENNReal) / (Fintype.card F : ENNReal)
          ≤ Pr_{let γ ← $ᵖ F}[
              δᵣ(f₁ + γ • f₂, U γ) ≤ δ ∧ U γ = u₁ + γ • u₂]

open scoped NNReal in
private structure AffineMCABadWitness (C : ModuleCode ι F A) (δ : ℝ≥0)
    (γ : F) (u : Fin 2 → ι → A) where
  cols : Finset ι
  card_bound : Fintype.card ι - Nat.floor (δ * Fintype.card ι) ≤ cols.card
  codeword : C
  fold_agree : ∀ i ∈ cols, u 0 i + γ • u 1 i = codeword.1 i
  row_not_projected : ∃ j : Fin 2,
    LinearCode.projectedWord (u j) cols ∉ LinearCode.projectedCodeSubmod C cols

open scoped NNReal in
private theorem affine_bad_witness_exists_collision_mismatch
    (C : ModuleCode ι F A) (δ : ℝ≥0) (γ : F) (u : Fin 2 → ι → A)
    (w : AffineMCABadWitness C δ γ u) (c₀ c₁ : C)
    (halign : w.codeword = c₀ + γ • c₁) :
    ∃ i ∈ w.cols,
      u 0 i + γ • u 1 i = c₀.1 i + γ • c₁.1 i ∧
      (u 0 i ≠ c₀.1 i ∨ u 1 i ≠ c₁.1 i) := by
  classical
  have hmismatch : ∃ i ∈ w.cols,
      u 0 i ≠ c₀.1 i ∨ u 1 i ≠ c₁.1 i := by
    by_contra hnone
    have hall : ∀ i ∈ w.cols,
        u 0 i = c₀.1 i ∧ u 1 i = c₁.1 i := by
      intro i hi
      have hn : ¬ (u 0 i ≠ c₀.1 i ∨ u 1 i ≠ c₁.1 i) := by
        intro hm
        exact hnone ⟨i, hi, hm⟩
      exact ⟨not_ne_iff.mp (not_or.mp hn).1, not_ne_iff.mp (not_or.mp hn).2⟩
    obtain ⟨j, hj⟩ := w.row_not_projected
    fin_cases j
    · apply hj
      rw [LinearCode.mem_projectedCodeSubmod_iff]
      refine ⟨c₀.1, c₀.2, ?_⟩
      funext i
      simp only [LinearCode.projectedWord, Set.restrict_apply]
      exact (hall i i.property).1
    · apply hj
      rw [LinearCode.mem_projectedCodeSubmod_iff]
      refine ⟨c₁.1, c₁.2, ?_⟩
      funext i
      simp only [LinearCode.projectedWord, Set.restrict_apply]
      exact (hall i i.property).2
  obtain ⟨i, hi, hm⟩ := hmismatch
  refine ⟨i, hi, ?_, hm⟩
  calc
    u 0 i + γ • u 1 i = w.codeword.1 i := w.fold_agree i hi
    _ = (c₀ + γ • c₁).1 i := congrArg (fun c : C => c.1 i) halign
    _ = c₀.1 i + γ • c₁.1 i := rfl

private theorem affine_collision_injective
    (E : Finset F) (u₀ u₁ c₀ c₁ : ι → A)
    (pick : {γ : F // γ ∈ E} → ι)
    (hroot : ∀ γ, u₀ (pick γ) + γ.1 • u₁ (pick γ) =
      c₀ (pick γ) + γ.1 • c₁ (pick γ))
    (hmismatch : ∀ γ, u₀ (pick γ) ≠ c₀ (pick γ) ∨
      u₁ (pick γ) ≠ c₁ (pick γ)) :
    Function.Injective pick := by
  intro γ β hpick
  apply Subtype.ext
  by_cases hval : γ.1 = β.1
  · exact hval
  · exfalso
    have hrγ := hroot γ
    have hrβ := hroot β
    rw [← hpick] at hrβ
    let x₀ : A := u₀ (pick γ) - c₀ (pick γ)
    let x₁ : A := u₁ (pick γ) - c₁ (pick γ)
    have hrγ' : x₀ + γ.1 • x₁ = 0 := by
      calc
        x₀ + γ.1 • x₁ =
            (u₀ (pick γ) + γ.1 • u₁ (pick γ)) -
              (c₀ (pick γ) + γ.1 • c₁ (pick γ)) := by
                dsimp only [x₀, x₁]
                module
        _ = 0 := sub_eq_zero.mpr hrγ
    have hrβ' : x₀ + β.1 • x₁ = 0 := by
      calc
        x₀ + β.1 • x₁ =
            (u₀ (pick γ) + β.1 • u₁ (pick γ)) -
              (c₀ (pick γ) + β.1 • c₁ (pick γ)) := by
                dsimp only [x₀, x₁]
                module
        _ = 0 := sub_eq_zero.mpr hrβ
    have hs : (γ.1 - β.1) • x₁ = 0 := by
      calc
        (γ.1 - β.1) • x₁ =
            (x₀ + γ.1 • x₁) - (x₀ + β.1 • x₁) := by module
        _ = 0 := by rw [hrγ', hrβ']; simp only [sub_self]
    have hx₁ : x₁ = 0 := (smul_eq_zero.mp hs).resolve_left (sub_ne_zero.mpr hval)
    have hx₀ : x₀ = 0 := by
      rw [hx₁, smul_zero, add_zero] at hrγ'
      exact hrγ'
    have hu₀ : u₀ (pick γ) = c₀ (pick γ) :=
      sub_eq_zero.mp (by simpa only [x₀] using hx₀)
    have hu₁ : u₁ (pick γ) = c₁ (pick γ) :=
      sub_eq_zero.mp (by simpa only [x₁] using hx₁)
    exact (hmismatch γ).elim (fun h => h hu₀) (fun h => h hu₁)

private theorem affine_collision_card_le
    (E : Finset F) (u₀ u₁ c₀ c₁ : ι → A)
    (pick : {γ : F // γ ∈ E} → ι)
    (hroot : ∀ γ, u₀ (pick γ) + γ.1 • u₁ (pick γ) =
      c₀ (pick γ) + γ.1 • c₁ (pick γ))
    (hmismatch : ∀ γ, u₀ (pick γ) ≠ c₀ (pick γ) ∨
      u₁ (pick γ) ≠ c₁ (pick γ)) :
    E.card ≤ Fintype.card ι := by
  have hcard := Fintype.card_le_of_injective pick
    (affine_collision_injective E u₀ u₁ c₀ c₁ pick hroot hmismatch)
  simpa using hcard

open scoped NNReal in
private theorem curated_outside_exists_collision_mismatch
    (C : ModuleCode ι F A) (δ : ℝ≥0) (γ : F) (u : Fin 2 → ι → A)
    (J : Finset ι)
    (hvanish : ∀ i, i ∉ J → ∀ c : C, c.1 i = 0)
    (hZcard : (Finset.univ.filter fun i : ι =>
      i ∉ J ∧ u 0 i = 0 ∧ u 1 i = 0).card <
        Fintype.card ι - Nat.floor (δ * Fintype.card ι))
    (selected c₀ c₁ : C)
    (hclose : δᵣ(u 0 + γ • u 1, selected.1) ≤ δ)
    (halign : selected = c₀ + γ • c₁)
    (havoid : ∀ i ∈ J, u 0 i + γ • u 1 i ≠ selected.1 i) :
    ∃ i,
      u 0 i + γ • u 1 i = c₀.1 i + γ • c₁.1 i ∧
      (u 0 i ≠ c₀.1 i ∨ u 1 i ≠ c₁.1 i) := by
  classical
  rw [Code.relCloseToWord_iff_exists_agreementCols] at hclose
  obtain ⟨S, hScard, hSagree⟩ := hclose
  let Z := Finset.univ.filter fun i : ι =>
    i ∉ J ∧ u 0 i = 0 ∧ u 1 i = 0
  have hZS : Z.card < S.card := lt_of_lt_of_le hZcard hScard
  obtain ⟨i, hiS, hiZ⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := Z) (t := S) hZS
  have hagree : u 0 i + γ • u 1 i = selected.1 i := (hSagree i).1 hiS
  have hcollision : u 0 i + γ • u 1 i = c₀.1 i + γ • c₁.1 i := by
    calc
      u 0 i + γ • u 1 i = selected.1 i := hagree
      _ = (c₀ + γ • c₁).1 i := congrArg (fun c : C => c.1 i) halign
      _ = c₀.1 i + γ • c₁.1 i := rfl
  refine ⟨i, hcollision, ?_⟩
  by_contra hmismatch
  have heq : u 0 i = c₀.1 i ∧ u 1 i = c₁.1 i := by
    exact ⟨not_ne_iff.mp (not_or.mp hmismatch).1,
      not_ne_iff.mp (not_or.mp hmismatch).2⟩
  have hiJ : i ∉ J := by
    intro hi
    exact (havoid i hi) hagree
  have hc₀ : c₀.1 i = 0 := hvanish i hiJ c₀
  have hc₁ : c₁.1 i = 0 := hvanish i hiJ c₁
  apply hiZ
  simp only [Z, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨hiJ, heq.1.trans hc₀, heq.2.trans hc₁⟩

open scoped NNReal in
private theorem decoded_challenge_exists_collision_mismatch
    (C : ModuleCode ι F A) (δ : ℝ≥0) (u : Fin 2 → ι → A)
    (B : Finset F)
    (w : ∀ γ : {γ : F // γ ∈ B}, AffineMCABadWitness C δ γ.1 u)
    (J : Finset ι)
    (hvanish : ∀ i, i ∉ J → ∀ c : C, c.1 i = 0)
    (hZcard : (Finset.univ.filter fun i : ι =>
      i ∉ J ∧ u 0 i = 0 ∧ u 1 i = 0).card <
        Fintype.card ι - Nat.floor (δ * Fintype.card ι))
    (U : F → C)
    (hUbad : ∀ γ (hγ : γ ∈ B), U γ = (w ⟨γ, hγ⟩).codeword)
    (hUavoid : ∀ γ, γ ∉ B → δᵣ(u 0 + γ • u 1, (U γ).1) ≤ δ →
      ∀ i ∈ J, u 0 i + γ • u 1 i ≠ (U γ).1 i)
    (c₀ c₁ : C) (γ : F)
    (hclose : δᵣ(u 0 + γ • u 1, (U γ).1) ≤ δ)
    (halign : U γ = c₀ + γ • c₁) :
    ∃ i,
      u 0 i + γ • u 1 i = c₀.1 i + γ • c₁.1 i ∧
      (u 0 i ≠ c₀.1 i ∨ u 1 i ≠ c₁.1 i) := by
  classical
  by_cases hγ : γ ∈ B
  · have hwAlign : (w ⟨γ, hγ⟩).codeword = c₀ + γ • c₁ :=
      (hUbad γ hγ).symm.trans halign
    obtain ⟨i, _hi, hcollision, hmismatch⟩ :=
      affine_bad_witness_exists_collision_mismatch C δ γ u (w ⟨γ, hγ⟩) c₀ c₁ hwAlign
    exact ⟨i, hcollision, hmismatch⟩
  · exact curated_outside_exists_collision_mismatch C δ γ u J hvanish hZcard
      (U γ) c₀ c₁ hclose halign (hUavoid γ hγ hclose)

private theorem exists_outside_finite_union_submodules
    {α K M : Type} [Field K] [Fintype K] [AddCommGroup M] [Module K M]
    [Finite M] [Nontrivial M]
    (s : Finset α) (p : α → Submodule K M)
    (hp : ∀ i ∈ s, p i ≠ ⊤) (hs : s.card ≤ Fintype.card K) :
    ∃ x : M, ∀ i ∈ s, x ∉ p i := by
  classical
  letI := Fintype.ofFinite M
  let q := Fintype.card K
  let d := Module.finrank K M
  let nz (i : α) := Finset.univ.filter fun x : M => x ∈ p i ∧ x ≠ 0
  let covered := insert (0 : M) (s.biUnion nz)
  have hq : 1 < q := Fintype.one_lt_card
  have hd : 0 < d := Module.finrank_pos
  have hnz (i : α) (hi : i ∈ s) : (nz i).card ≤ q ^ (d - 1) - 1 := by
    let allp := Finset.univ.filter fun x : M => x ∈ p i
    have hzero : (0 : M) ∈ allp := by simp [allp]
    have hnz_eq : nz i = allp.erase 0 := by
      ext x
      simp [nz, allp, and_comm]
    rw [hnz_eq, Finset.card_erase_of_mem hzero]
    have hcard : allp.card = Fintype.card (p i) := by
      symm
      exact Fintype.card_ofFinset allp (by simp [allp])
    have hcardpow : Fintype.card (p i) = q ^ Module.finrank K (p i) := by
      simpa [q] using (Module.card_eq_pow_finrank (K := K) (V := p i))
    rw [hcard, hcardpow]
    exact Nat.sub_le_sub_right
      (Nat.pow_le_pow_right (Nat.zero_lt_of_lt hq)
        (Nat.le_sub_one_of_lt (Submodule.finrank_lt (hp i hi)))) 1
  have hcovered : covered.card < Fintype.card M := by
    have hbi : (s.biUnion nz).card ≤ s.card * (q ^ (d - 1) - 1) := by
      calc
        (s.biUnion nz).card ≤ ∑ i ∈ s, (nz i).card := Finset.card_biUnion_le
        _ ≤ ∑ _i ∈ s, (q ^ (d - 1) - 1) :=
          Finset.sum_le_sum fun i hi => hnz i hi
        _ = s.card * (q ^ (d - 1) - 1) := by simp
    have hmul : s.card * (q ^ (d - 1) - 1) ≤ q * (q ^ (d - 1) - 1) :=
      Nat.mul_le_mul_right _ hs
    have hpow : q ^ d = q * q ^ (d - 1) := by
      conv_lhs => rw [← Nat.succ_pred_eq_of_pos hd]
      simp [pow_succ, Nat.mul_comm]
    have hcardM : Fintype.card M = q ^ d := by
      simpa [q, d] using (Module.card_eq_pow_finrank (K := K) (V := M))
    rw [hcardM, hpow]
    calc
      covered.card ≤ (s.biUnion nz).card + 1 := Finset.card_insert_le _ _
      _ ≤ s.card * (q ^ (d - 1) - 1) + 1 := Nat.add_le_add_right hbi 1
      _ ≤ q * (q ^ (d - 1) - 1) + 1 := Nat.add_le_add_right hmul 1
      _ < q * q ^ (d - 1) := by
        have hpos : 0 < q ^ (d - 1) := pow_pos (Nat.zero_lt_of_lt hq) _
        have hqmul : q ≤ q * q ^ (d - 1) := by
          simpa using Nat.mul_le_mul_left q hpos
        rw [Nat.mul_sub_left_distrib]
        simp only [mul_one]
        omega
  obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := covered) (t := Finset.univ) (by simpa using hcovered)
  refine ⟨x, fun i hi hxi => hx ?_⟩
  by_cases hx0 : x = 0
  · simp [covered, hx0]
  · simp only [covered, Finset.mem_insert]
    exact Or.inr (Finset.mem_biUnion.mpr ⟨i, hi, by simp [nz, hxi, hx0]⟩)

private theorem exists_codeword_nonzero_on_active
    (C : ModuleCode ι F A) [Nontrivial C] (J : Finset ι)
    (hactive : ∀ i ∈ J, ∃ c : C, c.1 i ≠ 0)
    (hJcard : J.card < Fintype.card F) :
    ∃ d : C, ∀ i ∈ J, d.1 i ≠ 0 := by
  classical
  let p (j : {i : ι // i ∈ J}) : Submodule F C :=
    { carrier := {c | c.1 j.1 = 0}
      zero_mem' := by simp
      add_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        simp [hx, hy]
      smul_mem' := by
        intro a x hx
        simp only [Set.mem_setOf_eq] at hx ⊢
        simp [hx] }
  have hp (j : {i : ι // i ∈ J}) (hj : j ∈ (Finset.univ : Finset {i : ι // i ∈ J})) :
      p j ≠ ⊤ := by
    obtain ⟨c, hc⟩ := hactive j.1 j.2
    intro htop
    have hcTop : c ∈ p j := by
      rw [htop]
      exact Submodule.mem_top
    exact hc (by simpa [p] using hcTop)
  have hcard : (Finset.univ : Finset {i : ι // i ∈ J}).card ≤ Fintype.card F := by
    rw [Finset.card_univ, Fintype.card_coe]
    exact hJcard.le
  obtain ⟨d, hd⟩ := exists_outside_finite_union_submodules
    (s := (Finset.univ : Finset {i : ι // i ∈ J})) p hp hcard
  refine ⟨d, ?_⟩
  intro i hi hdi
  let j : {i : ι // i ∈ J} := ⟨i, hi⟩
  apply hd j (Finset.mem_univ j)
  change d.1 j.1 = 0
  exact hdi

private theorem exists_scalar_avoiding_active_coordinates
    (J : Finset ι) (d y : ι → A)
    (hd : ∀ i ∈ J, d i ≠ 0)
    (hJcard : J.card < Fintype.card F) :
    ∃ t : F, ∀ i ∈ J, y i ≠ t • d i := by
  classical
  by_contra h
  push Not at h
  choose pick hpickJ hpickEq using h
  let f : F → {i : ι // i ∈ J} := fun t => ⟨pick t, hpickJ t⟩
  have hf : Function.Injective f := by
    intro t s hts
    have his : pick t = pick s := congrArg Subtype.val hts
    have ht := hpickEq t
    have hs := hpickEq s
    rw [his] at ht
    exact smul_left_injective F (hd (pick s) (hpickJ s)) (ht.symm.trans hs)
  have hcard : Fintype.card F ≤ Fintype.card {i : ι // i ∈ J} :=
    Fintype.card_le_of_injective f hf
  rw [Fintype.card_coe] at hcard
  omega

open scoped NNReal in
private theorem exists_curated_affine_codeword_family
    (C : ModuleCode ι F A) (δ : ℝ≥0) (u : Fin 2 → ι → A)
    (B : Finset F)
    (w : ∀ γ : {γ : F // γ ∈ B}, AffineMCABadWitness C δ γ.1 u)
    (J : Finset ι) (d : C)
    (hd : ∀ i ∈ J, d.1 i ≠ 0)
    (hJcard : J.card < Fintype.card F) :
    ∃ U : F → C,
      (∀ γ (hγ : γ ∈ B), U γ = (w ⟨γ, hγ⟩).codeword) ∧
      (∀ γ (_hγ : γ ∈ B), δᵣ(u 0 + γ • u 1, (U γ).1) ≤ δ) ∧
      (∀ γ, γ ∉ B → δᵣ(u 0 + γ • u 1, (U γ).1) ≤ δ →
        ∀ i ∈ J, u 0 i + γ • u 1 i ≠ (U γ).1 i) := by
  classical
  let y : F → ι → A := fun γ => u 0 + γ • u 1
  let AllClose : F → Prop := fun γ => ∀ c : C, δᵣ(y γ, c.1) ≤ δ
  let U : F → C := fun γ =>
    if hγ : γ ∈ B then (w ⟨γ, hγ⟩).codeword
    else if hAll : AllClose γ then
      (Classical.choose
        (exists_scalar_avoiding_active_coordinates J d.1 (y γ) hd hJcard)) • d
    else Classical.choose (not_forall.mp hAll)
  refine ⟨U, ?_, ?_, ?_⟩
  · intro γ hγ
    simp only [U, hγ, ↓reduceDIte]
  · intro γ hγ
    have hU : U γ = (w ⟨γ, hγ⟩).codeword := by
      simp only [U, hγ, ↓reduceDIte]
    rw [hU, Code.relCloseToWord_iff_exists_agreementCols]
    refine ⟨(w ⟨γ, hγ⟩).cols, (w ⟨γ, hγ⟩).card_bound, ?_⟩
    intro i
    constructor
    · intro hi
      exact (w ⟨γ, hγ⟩).fold_agree i hi
    · intro hne hi
      exact hne ((w ⟨γ, hγ⟩).fold_agree i hi)
  · intro γ hγnot hclose i hi
    by_cases hAll : AllClose γ
    · have hU : U γ =
          (Classical.choose
            (exists_scalar_avoiding_active_coordinates J d.1 (y γ) hd hJcard)) • d := by
        simp only [U, hγnot, ↓reduceDIte, hAll]
      rw [hU]
      have hav := Classical.choose_spec
        (exists_scalar_avoiding_active_coordinates J d.1 (y γ) hd hJcard)
      simpa only [y, Pi.add_apply, Pi.smul_apply, Submodule.coe_smul] using hav i hi
    · have hU : U γ = Classical.choose (not_forall.mp hAll) := by
        simp only [U, hγnot, ↓reduceDIte, hAll]
      have hnclose := Classical.choose_spec (not_forall.mp hAll)
      exact (hnclose (hU ▸ hclose)).elim

private theorem exists_synthetic_affine_zero_set
    (B : Finset F) (pick : {γ : F // γ ∈ B} → ι)
    (hinj : Function.Injective pick) (Z : Finset ι)
    (hpickNotZ : ∀ γ, pick γ ∉ Z)
    (k : ℕ) (hkpos : 0 < k) (hkZ : k ≤ Z.card)
    (x : A) (hx : x ≠ 0) :
    ∃ v₀ v₁ : ι → A, ∀ β : F,
      k ≤ (Finset.univ.filter fun i : ι =>
        v₀ i + β • v₁ i = 0).card ↔ β ∈ B := by
  classical
  obtain ⟨P, hPZ, hPcard⟩ := Finset.exists_subset_card_eq
    (show k - 1 ≤ Z.card by omega)
  let assigned : ι → Prop := fun i => ∃ γ : {γ : F // γ ∈ B}, pick γ = i
  let root : ι → F := fun i => if h : assigned i then (Classical.choose h).1 else 0
  have hrootPick (γ : {γ : F // γ ∈ B}) : root (pick γ) = γ.1 := by
    dsimp only [root]
    split
    next h =>
      apply congrArg Subtype.val
      apply hinj
      exact Classical.choose_spec h
    next h => exact (h ⟨γ, rfl⟩).elim
  have hpickNotP (γ : {γ : F // γ ∈ B}) : pick γ ∉ P := by
    intro hiP
    exact hpickNotZ γ (hPZ hiP)
  let v₀ : ι → A := fun i =>
    if i ∈ P then 0 else if assigned i then -(root i) • x else x
  let v₁ : ι → A := fun i =>
    if i ∈ P then 0 else if assigned i then x else 0
  let Zero : F → Finset ι := fun β =>
    Finset.univ.filter fun i : ι => v₀ i + β • v₁ i = 0
  have hPzero (β : F) : P ⊆ Zero β := by
    intro i hiP
    simp [Zero, v₀, v₁, hiP]
  have hzeroOutside (β : F) (i : ι) (hiZero : i ∈ Zero β) (hiP : i ∉ P) :
      β ∈ B := by
    have hiEq : v₀ i + β • v₁ i = 0 := (Finset.mem_filter.mp hiZero).2
    by_cases hiAssigned : assigned i
    · let g : {γ : F // γ ∈ B} := Classical.choose hiAssigned
      have hpickg : pick g = i := Classical.choose_spec hiAssigned
      have hrootg : root i = g.1 := by
        dsimp only [root]
        split
        next h =>
          apply congrArg Subtype.val
          apply hinj
          exact (Classical.choose_spec h).trans hpickg.symm
        next h => exact (h ⟨g, hpickg⟩).elim
      have hiEq' : -(root i) • x + β • x = 0 := by
        simpa only [v₀, v₁, hiP, ↓reduceIte, hiAssigned] using hiEq
      have hs : (β - root i) • x = 0 := by
        calc
          (β - root i) • x = -(root i) • x + β • x := by module
          _ = 0 := hiEq'
      have hcoef : β - root i = 0 := (smul_eq_zero.mp hs).resolve_right hx
      have hβroot : β = root i := sub_eq_zero.mp hcoef
      have hβg : β = g.1 := hβroot.trans hrootg
      rw [hβg]
      exact g.2
    · have hx0 : x = 0 := by
        simpa only [v₀, v₁, hiP, ↓reduceIte, hiAssigned, smul_zero, add_zero] using hiEq
      exact (hx hx0).elim
  refine ⟨v₀, v₁, ?_⟩
  intro β
  change k ≤ (Zero β).card ↔ β ∈ B
  constructor
  · intro hkZero
    by_contra hβ
    have hsub : Zero β ⊆ P := by
      intro i hiZero
      by_contra hiP
      exact hβ (hzeroOutside β i hiZero hiP)
    have hcard := Finset.card_le_card hsub
    rw [hPcard] at hcard
    omega
  · intro hβ
    let gβ : {γ : F // γ ∈ B} := ⟨β, hβ⟩
    let pβ : ι := pick gβ
    have hpβP : pβ ∉ P := hpickNotP gβ
    have hpβZero : pβ ∈ Zero β := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      have hpβAssigned : assigned pβ := ⟨gβ, rfl⟩
      simp only [v₀, v₁, hpβP, ↓reduceIte, hpβAssigned]
      rw [hrootPick gβ]
      dsimp only [gβ]
      module
    have hins : insert pβ P ⊆ Zero β := by
      intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hiP
      · exact hpβZero
      · exact hPzero β hiP
    calc
      k = (insert pβ P).card := by
        rw [Finset.card_insert_of_notMem hpβP, hPcard]
        omega
      _ ≤ (Zero β).card := Finset.card_le_card hins

open scoped NNReal in
private theorem is_mca_affine_line_bad_witness_nonempty
    (C : ModuleCode ι F A) (δ : ℝ≥0) (hδ : δ ≤ 1)
    (γ : F) (u : Fin 2 → ι → A)
    (hmca : IsMCA (AffineLineGenerator F) C γ u (δ : ℝ)) :
    Nonempty (AffineMCABadWitness C δ γ u) := by
  classical
  obtain ⟨T, hT, hcomb, hfail⟩ := hmca
  rw [LinearCode.mem_projectedCodeSubmod_iff] at hcomb
  obtain ⟨c, hc, hproj⟩ := hcomb
  have hTnat : Fintype.card ι - Nat.floor (δ * Fintype.card ι) ≤ T.card := by
    apply (Code.relDist_floor_bound_iff_complement_bound _ _ _).mpr
    rw [← NNReal.coe_le_coe, NNReal.coe_mul, NNReal.coe_sub hδ]
    push_cast
    nlinarith
  refine ⟨{
    cols := T
    card_bound := hTnat
    codeword := ⟨c, hc⟩
    fold_agree := ?_
    row_not_projected := hfail }⟩
  intro i hi
  have hiProj := congrFun hproj ⟨i, hi⟩
  simpa [AffineLineGenerator, Fin.sum_univ_two, LinearCode.projectedWord] using hiProj

open scoped NNReal ProbabilityTheory in
private theorem line_decodable_cardinality_form
    (C : ModuleCode ι F A) (δ : ℝ≥0) (a b : ℕ)
    (hld : IsLineDecodable (F := F) ((C : Set (ι → A))) δ a b)
    (f₀ f₁ : ι → A) (U : F → C)
    (B : Finset F)
    (hBclose : ∀ γ ∈ B, δᵣ(f₀ + γ • f₁, (U γ).1) ≤ δ)
    (haB : a ≤ B.card) :
    ∃ c₀ c₁ : C, ∃ E : Finset F,
      b ≤ E.card ∧
      ∀ γ ∈ E,
        δᵣ(f₀ + γ • f₁, (U γ).1) ≤ δ ∧
          (U γ).1 = c₀.1 + γ • c₁.1 := by
  classical
  have hprem : (a : ENNReal) / (Fintype.card F : ENNReal) ≤
      Pr_{let γ ← $ᵖ F}[δᵣ(f₀ + γ • f₁, (U γ).1) ≤ δ] := by
    rw [Probability.prob_uniform_eq_card_filter_div_card]
    apply ENNReal.div_le_div_right
    exact_mod_cast (haB.trans (Finset.card_le_card (fun γ hγ =>
      Finset.mem_filter.mpr ⟨Finset.mem_univ _, hBclose γ hγ⟩)))
  obtain ⟨c₀, hc₀, c₁, hc₁, hout⟩ :=
    hld f₀ f₁ (fun γ => (U γ).1) (fun γ => (U γ).2) hprem
  let E := Finset.univ.filter fun γ : F =>
    δᵣ(f₀ + γ • f₁, (U γ).1) ≤ δ ∧
      (U γ).1 = c₀ + γ • c₁
  have hout' : (b : ENNReal) / (Fintype.card F : ENNReal) ≤
      (E.card : ENNReal) / (Fintype.card F : ENNReal) := by
    rw [Probability.prob_uniform_eq_card_filter_div_card] at hout
    exact hout
  have hq0 : (Fintype.card F : ENNReal) ≠ 0 := by simp
  have hqtop : (Fintype.card F : ENNReal) ≠ ⊤ := by simp
  have hEcard : b ≤ E.card := by
    by_contra hnot
    have hltNat : E.card < b := Nat.lt_of_not_ge hnot
    have hltCast : (E.card : ENNReal) < (b : ENNReal) := by exact_mod_cast hltNat
    have hlt := ENNReal.div_lt_div_right hq0 hqtop hltCast
    exact (not_lt_of_ge hout') hlt
  refine ⟨⟨c₀, hc₀⟩, ⟨c₁, hc₁⟩, E, hEcard, ?_⟩
  intro γ hγ
  exact (Finset.mem_filter.mp hγ).2

open scoped NNReal ProbabilityTheory in
private theorem line_decodable_output_card_le_field_card
    (C : ModuleCode ι F A) (δ : ℝ≥0) (a b : ℕ)
    (hld : IsLineDecodable (F := F) ((C : Set (ι → A))) δ a b)
    (haq : a ≤ Fintype.card F) :
    b ≤ Fintype.card F := by
  classical
  let z : C := 0
  obtain ⟨c₀, c₁, E, hE, _⟩ := line_decodable_cardinality_form C δ a b hld
    (0 : ι → A) (0 : ι → A) (fun _ => z) Finset.univ
    (by
      intro γ _hγ
      simp only [zero_add, smul_zero]
      rw [Code.relCloseToWord_iff_exists_agreementCols]
      refine ⟨Finset.univ, Nat.sub_le _ _, ?_⟩
      intro i
      constructor
      · intro _hi
        rfl
      · intro hne
        exact (hne rfl).elim)
    (by simpa using haq)
  exact hE.trans (by simpa using Finset.card_le_univ E)

private theorem quadratic_alignment_card_le_two
    (E : Finset F) (d c₀ c₁ : A) (hd : d ≠ 0)
    (hroot : ∀ γ ∈ E, γ ^ 2 • d = c₀ + γ • c₁) :
    E.card ≤ 2 := by
  by_contra hle
  have hgt : 2 < E.card := Nat.lt_of_not_ge hle
  obtain ⟨α, β, γ, hα, hβ, hγ, hαβ, hαγ, hβγ⟩ :=
    (Finset.two_lt_card_iff.mp hgt)
  have hrα := hroot α hα
  have hrβ := hroot β hβ
  have hrγ := hroot γ hγ
  have hcβ : c₁ = (α + β) • d := by
    have hs : (α - β) • c₁ = (α - β) • ((α + β) • d) := by
      calc
        (α - β) • c₁ = α • c₁ - β • c₁ := by module
        _ = (c₀ + α • c₁) - (c₀ + β • c₁) := by module
        _ = α ^ 2 • d - β ^ 2 • d := by rw [← hrα, ← hrβ]
        _ = (α - β) • ((α + β) • d) := by module
    exact smul_right_injective A (sub_ne_zero.mpr hαβ) hs
  have hcγ : c₁ = (α + γ) • d := by
    have hs : (α - γ) • c₁ = (α - γ) • ((α + γ) • d) := by
      calc
        (α - γ) • c₁ = α • c₁ - γ • c₁ := by module
        _ = (c₀ + α • c₁) - (c₀ + γ • c₁) := by module
        _ = α ^ 2 • d - γ ^ 2 • d := by rw [← hrα, ← hrγ]
        _ = (α - γ) • ((α + γ) • d) := by module
    exact smul_right_injective A (sub_ne_zero.mpr hαγ) hs
  have hsum : α + β = α + γ :=
    smul_left_injective F hd (hcβ.symm.trans hcγ)
  exact hβγ (add_left_cancel hsum)

private theorem card_sub_floor_pos_of_lt_one
    {n : ℕ} (hnpos : 0 < n) (δ : ℝ≥0) (hδlt : δ < 1) :
    0 < n - Nat.floor (δ * (n : ℝ≥0)) := by
  have hmul : δ * (n : ℝ≥0) < (n : ℝ≥0) := by
    calc
      δ * (n : ℝ≥0) < 1 * (n : ℝ≥0) :=
        mul_lt_mul_of_pos_right hδlt (by exact_mod_cast hnpos)
      _ = (n : ℝ≥0) := one_mul _
  have he : Nat.floor (δ * (n : ℝ≥0)) < n :=
    (Nat.floor_lt (show (0 : ℝ≥0) ≤ δ * (n : ℝ≥0) by positivity)).2 hmul
  exact Nat.sub_pos_of_lt he

open scoped NNReal ProbabilityTheory in
open Classical in
private theorem active_outside_common_zero_card_lt
    (C : ModuleCode ι F A) [Nontrivial C] (δ : ℝ≥0) (a : ℕ)
    (hδlt : δ < 1)
    (hld : IsLineDecodable (F := F) ((C : Set (ι → A))) δ a
      (Fintype.card ι + 1))
    (u : Fin 2 → ι → A) (B : Finset F) (haB : a < B.card) :
    let J := Finset.univ.filter fun i : ι => ∃ c : C, c.1 i ≠ 0
    let Z := Finset.univ.filter fun i : ι =>
      i ∉ J ∧ u 0 i = 0 ∧ u 1 i = 0
    Z.card < Fintype.card ι - Nat.floor (δ * Fintype.card ι) := by
  let n := Fintype.card ι
  let q := Fintype.card F
  let k := n - Nat.floor (δ * n)
  let J := Finset.univ.filter fun i : ι => ∃ c : C, c.1 i ≠ 0
  let Z := Finset.univ.filter fun i : ι =>
    i ∉ J ∧ u 0 i = 0 ∧ u 1 i = 0
  change Z.card < k
  have hBq : B.card ≤ q := by
    simpa only [q] using Finset.card_le_univ B
  have haq : a ≤ q := haB.le.trans hBq
  have hnq : n + 1 ≤ q := by
    exact line_decodable_output_card_le_field_card C δ a (n + 1) hld haq
  have hnpos : 0 < n := by
    simpa only [n] using (Fintype.card_pos : 0 < Fintype.card ι)
  have hkpos : 0 < k := by
    simpa only [k, n] using card_sub_floor_pos_of_lt_one hnpos δ hδlt
  by_contra hZlt
  have hkZ : k ≤ Z.card := Nat.le_of_not_gt hZlt
  obtain ⟨d₀, hd₀⟩ := exists_ne (0 : C)
  obtain ⟨c₀, c₁, E, hEcard, hE⟩ :=
    line_decodable_cardinality_form C δ a (n + 1) hld
      (u 0) (u 1) (fun γ : F => γ ^ 2 • d₀) Finset.univ
      (by
        intro γ _hγ
        rw [Code.relCloseToWord_iff_exists_agreementCols]
        refine ⟨Z, hkZ, ?_⟩
        intro i
        constructor
        · intro hiZ
          have hi := (Finset.mem_filter.mp hiZ).2
          have hd₀i : d₀.1 i = 0 := by
            by_contra hne
            exact hi.1 (Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, ⟨d₀, hne⟩⟩)
          simp only [Pi.add_apply, Pi.smul_apply, hi.2.1, hi.2.2,
            hd₀i, smul_zero, add_zero, Submodule.coe_smul]
        · intro hne hiZ
          have hi := (Finset.mem_filter.mp hiZ).2
          have hd₀i : d₀.1 i = 0 := by
            by_contra hdi
            exact hi.1 (Finset.mem_filter.mpr
              ⟨Finset.mem_univ _, ⟨d₀, hdi⟩⟩)
          apply hne
          simp only [Pi.add_apply, Pi.smul_apply, hi.2.1, hi.2.2,
            hd₀i, smul_zero, add_zero, Submodule.coe_smul])
      (by simpa only [Finset.card_univ, q] using haq)
  have hquad : E.card ≤ 2 := by
    apply quadratic_alignment_card_le_two E d₀ c₀ c₁ hd₀
    intro γ hγ
    apply Subtype.ext
    exact (hE γ hγ).2
  have hd₀coe : d₀.1 ≠ (0 : ι → A) := by
    intro hz
    apply hd₀
    apply Subtype.ext
    exact hz
  obtain ⟨iJ, hiJnz⟩ := Function.ne_iff.mp hd₀coe
  have hiJ : iJ ∈ J := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, d₀, ?_⟩
    simpa only [Pi.zero_apply] using hiJnz
  have hZpos : 0 < Z.card := hkpos.trans_le hkZ
  obtain ⟨iZ, hiZ⟩ := Finset.card_pos.mp hZpos
  have hiJZ : iJ ≠ iZ := by
    intro hij
    subst iZ
    exact (Finset.mem_filter.mp hiZ).2.1 hiJ
  have hone : 1 < n := by
    apply Fintype.one_lt_card_iff.mpr
    exact ⟨iJ, iZ, hiJZ⟩
  have htwo : 2 ≤ n := by omega
  omega

open scoped NNReal ProbabilityTheory in
private theorem nontrivial_bad_set_card_le_a
    (C : ModuleCode ι F A) [Nontrivial C] (δ : ℝ≥0) (hδlt : δ < 1)
    (a : ℕ)
    (hld : IsLineDecodable (F := F) ((C : Set (ι → A))) δ a
      (Fintype.card ι + 1))
    (u : Fin 2 → ι → A) (B : Finset F)
    (w : ∀ γ : {γ : F // γ ∈ B}, AffineMCABadWitness C δ γ.1 u) :
    B.card ≤ a := by
  classical
  by_contra hle
  have haB : a < B.card := Nat.lt_of_not_ge hle
  let n := Fintype.card ι
  let q := Fintype.card F
  let J := Finset.univ.filter fun i : ι => ∃ c : C, c.1 i ≠ 0
  have hBq : B.card ≤ q := by
    simpa only [q] using Finset.card_le_univ B
  have haq : a ≤ q := haB.le.trans hBq
  have hnq : n + 1 ≤ q :=
    line_decodable_output_card_le_field_card C δ a (n + 1) hld haq
  have hJle : J.card ≤ n := by
    simpa only [J, n] using Finset.card_le_univ J
  have hJcard : J.card < q := by omega
  have hactive : ∀ i ∈ J, ∃ c : C, c.1 i ≠ 0 := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hvanish : ∀ i, i ∉ J → ∀ c : C, c.1 i = 0 := by
    intro i hi c
    by_contra hci
    apply hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨c, hci⟩⟩
  obtain ⟨d, hd⟩ := exists_codeword_nonzero_on_active C J hactive hJcard
  have hZcard : (Finset.univ.filter fun i : ι =>
      i ∉ J ∧ u 0 i = 0 ∧ u 1 i = 0).card <
        Fintype.card ι - Nat.floor (δ * Fintype.card ι) := by
    simpa only [J] using
      (active_outside_common_zero_card_lt C δ a hδlt hld u B haB)
  obtain ⟨U, hUbad, hUclose, hUavoid⟩ :=
    exists_curated_affine_codeword_family C δ u B w J d hd hJcard
  obtain ⟨c₀, c₁, E, hEcard, hE⟩ :=
    line_decodable_cardinality_form C δ a (Fintype.card ι + 1) hld
      (u 0) (u 1) U B hUclose haB.le
  have hex : ∀ γ : {γ : F // γ ∈ E}, ∃ i : ι,
      u 0 i + γ.1 • u 1 i = c₀.1 i + γ.1 • c₁.1 i ∧
      (u 0 i ≠ c₀.1 i ∨ u 1 i ≠ c₁.1 i) := by
    intro γ
    have hdata := hE γ.1 γ.2
    have halign : U γ.1 = c₀ + γ.1 • c₁ := by
      apply Subtype.ext
      exact hdata.2
    exact decoded_challenge_exists_collision_mismatch C δ u B w J hvanish hZcard
      U hUbad hUavoid c₀ c₁ γ.1 hdata.1 halign
  choose pick hroot hmismatch using hex
  have hcard : E.card ≤ Fintype.card ι :=
    affine_collision_card_le E (u 0) (u 1) c₀.1 c₁.1 pick hroot hmismatch
  omega

open scoped NNReal in
private theorem subsingleton_bad_set_pick
    (C : ModuleCode ι F A) [Subsingleton C] (δ : ℝ≥0)
    (u : Fin 2 → ι → A) (B : Finset F)
    (w : ∀ γ : {γ : F // γ ∈ B}, AffineMCABadWitness C δ γ.1 u) :
    ∃ pick : {γ : F // γ ∈ B} → ι,
      Function.Injective pick ∧
      (∀ γ, u 0 (pick γ) + γ.1 • u 1 (pick γ) = 0) ∧
      (∀ γ, u 0 (pick γ) ≠ 0 ∨ u 1 (pick γ) ≠ 0) := by
  classical
  have hex : ∀ γ : {γ : F // γ ∈ B}, ∃ i : ι,
      u 0 i + γ.1 • u 1 i = 0 ∧ (u 0 i ≠ 0 ∨ u 1 i ≠ 0) := by
    intro γ
    have halign : (w γ).codeword = (0 : C) + γ.1 • (0 : C) :=
      Subsingleton.elim _ _
    obtain ⟨i, _hi, hroot, hmismatch⟩ :=
      affine_bad_witness_exists_collision_mismatch C δ γ.1 u (w γ)
        (0 : C) (0 : C) halign
    refine ⟨i, ?_, ?_⟩
    · simpa using hroot
    · simpa using hmismatch
  choose pick hroot hmismatch using hex
  refine ⟨pick, ?_, hroot, hmismatch⟩
  apply affine_collision_injective B (u 0) (u 1) (0 : ι → A) (0 : ι → A)
    pick
  · intro γ
    simpa using hroot γ
  · intro γ
    simpa using hmismatch γ

open scoped NNReal in
private theorem subsingleton_bad_set_card_le
    (C : ModuleCode ι F A) [Subsingleton C] (δ : ℝ≥0)
    (u : Fin 2 → ι → A) (B : Finset F)
    (w : ∀ γ : {γ : F // γ ∈ B}, AffineMCABadWitness C δ γ.1 u) :
    B.card ≤ Fintype.card ι := by
  obtain ⟨pick, hinj, _hroot, _hmismatch⟩ :=
    subsingleton_bad_set_pick C δ u B w
  calc
    B.card = Fintype.card {γ : F // γ ∈ B} := (Fintype.card_coe B).symm
    _ ≤ Fintype.card ι := Fintype.card_le_of_injective pick hinj

open scoped NNReal in
private theorem subsingleton_original_line_exact
    (C : ModuleCode ι F A) [Subsingleton C] (δ : ℝ≥0) (hδlt : δ < 1)
    (u : Fin 2 → ι → A) (B : Finset F)
    (hBmem : ∀ β : F, β ∈ B ↔
      IsMCA (AffineLineGenerator F) C β u (δ : ℝ))
    (w : ∀ γ : {γ : F // γ ∈ B}, AffineMCABadWitness C δ γ.1 u)
    (hZcard : (Finset.univ.filter fun i : ι =>
      u 0 i = 0 ∧ u 1 i = 0).card <
        Fintype.card ι - Nat.floor (δ * Fintype.card ι)) :
    ∀ β : F, δᵣ(u 0 + β • u 1, (0 : ι → A)) ≤ δ ↔ β ∈ B := by
  classical
  intro β
  constructor
  · intro hclose
    rw [Code.relCloseToWord_iff_exists_agreementCols] at hclose
    obtain ⟨S, hScard, hSagree⟩ := hclose
    let Z := Finset.univ.filter fun i : ι => u 0 i = 0 ∧ u 1 i = 0
    have hZS : Z.card < S.card := hZcard.trans_le hScard
    obtain ⟨i, hiS, hiZ⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := Z) (t := S) hZS
    have hnonzero : u 0 i ≠ 0 ∨ u 1 i ≠ 0 := by
      have hnand : ¬ (u 0 i = 0 ∧ u 1 i = 0) := by
        intro hz
        apply hiZ
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hz⟩
      exact not_and_or.mp hnand
    have hScardNN : (1 - δ) * (Fintype.card ι : ℝ≥0) ≤ (S.card : ℝ≥0) :=
      (Code.relDist_floor_bound_iff_complement_bound _ _ _).mp hScard
    have hScardR' :
        ((((1 - δ) * (Fintype.card ι : ℝ≥0)) : ℝ≥0) : ℝ) ≤
          (((S.card : ℝ≥0) : ℝ)) := NNReal.coe_le_coe.mpr hScardNN
    rw [NNReal.coe_mul, NNReal.coe_sub hδlt.le] at hScardR'
    push_cast at hScardR'
    have hScardR : (S.card : ℝ) ≥
        (Fintype.card ι : ℝ) * (1 - (δ : ℝ)) := by
      nlinarith
    have hmca : IsMCA (AffineLineGenerator F) C β u (δ : ℝ) := by
      refine ⟨S, hScardR, ?_, ?_⟩
      · rw [LinearCode.mem_projectedCodeSubmod_iff]
        refine ⟨(0 : ι → A), (0 : C).2, ?_⟩
        funext j
        have hj := (hSagree j.1).1 j.2
        simpa [LinearCode.projectedWord, AffineLineGenerator, Fin.sum_univ_two] using hj
      · rcases hnonzero with h0 | h1
        · refine ⟨0, ?_⟩
          intro hmem
          rw [LinearCode.mem_projectedCodeSubmod_iff] at hmem
          obtain ⟨c, hc, hproj⟩ := hmem
          have hc0 : c = (0 : ι → A) :=
            congrArg Subtype.val (Subsingleton.elim (⟨c, hc⟩ : C) (0 : C))
          have hi := congrFun hproj ⟨i, hiS⟩
          rw [hc0] at hi
          apply h0
          simpa [LinearCode.projectedWord] using hi
        · refine ⟨1, ?_⟩
          intro hmem
          rw [LinearCode.mem_projectedCodeSubmod_iff] at hmem
          obtain ⟨c, hc, hproj⟩ := hmem
          have hc0 : c = (0 : ι → A) :=
            congrArg Subtype.val (Subsingleton.elim (⟨c, hc⟩ : C) (0 : C))
          have hi := congrFun hproj ⟨i, hiS⟩
          rw [hc0] at hi
          apply h1
          simpa [LinearCode.projectedWord] using hi
    exact (hBmem β).2 hmca
  · intro hβ
    let wb := w ⟨β, hβ⟩
    rw [Code.relCloseToWord_iff_exists_agreementCols]
    refine ⟨wb.cols, wb.card_bound, ?_⟩
    intro i
    have hcodezero : wb.codeword = (0 : C) := Subsingleton.elim _ _
    constructor
    · intro hi
      have hiagree := wb.fold_agree i hi
      rw [hcodezero] at hiagree
      simpa using hiagree
    · intro hne hi
      have hiagree := wb.fold_agree i hi
      rw [hcodezero] at hiagree
      exact hne (by simpa using hiagree)

open scoped NNReal in
private theorem subsingleton_synthetic_line_exact
    (C : ModuleCode ι F A) [Subsingleton C] (δ : ℝ≥0) (hδlt : δ < 1)
    (u : Fin 2 → ι → A) (B : Finset F) (hBne : B.Nonempty)
    (w : ∀ γ : {γ : F // γ ∈ B}, AffineMCABadWitness C δ γ.1 u)
    (hZcard : Fintype.card ι - Nat.floor (δ * Fintype.card ι) ≤
      (Finset.univ.filter fun i : ι => u 0 i = 0 ∧ u 1 i = 0).card) :
    ∃ v₀ v₁ : ι → A, ∀ β : F,
      δᵣ(v₀ + β • v₁, (0 : ι → A)) ≤ δ ↔ β ∈ B := by
  classical
  let n := Fintype.card ι
  let k := n - Nat.floor (δ * n)
  let Z := Finset.univ.filter fun i : ι => u 0 i = 0 ∧ u 1 i = 0
  have hnpos : 0 < n := by
    simpa only [n] using (Fintype.card_pos : 0 < Fintype.card ι)
  have hkpos : 0 < k := by
    simpa only [k, n] using card_sub_floor_pos_of_lt_one hnpos δ hδlt
  have hkZ : k ≤ Z.card := by
    simpa only [k, n, Z] using hZcard
  obtain ⟨pick, hinj, _hroot, hmismatch⟩ :=
    subsingleton_bad_set_pick C δ u B w
  have hpickNotZ : ∀ γ, pick γ ∉ Z := by
    intro γ hiZ
    have hz := (Finset.mem_filter.mp hiZ).2
    exact (hmismatch γ).elim (fun h => h hz.1) (fun h => h hz.2)
  obtain ⟨β, hβ⟩ := hBne
  let gβ : {γ : F // γ ∈ B} := ⟨β, hβ⟩
  obtain ⟨x, hx⟩ : ∃ x : A, x ≠ 0 := by
    rcases hmismatch gβ with h0 | h1
    · exact ⟨u 0 (pick gβ), h0⟩
    · exact ⟨u 1 (pick gβ), h1⟩
  obtain ⟨v₀, v₁, hzero⟩ :=
    exists_synthetic_affine_zero_set B pick hinj Z hpickNotZ k hkpos hkZ x hx
  refine ⟨v₀, v₁, ?_⟩
  intro γ
  let Zero := Finset.univ.filter fun i : ι => v₀ i + γ • v₁ i = 0
  have hthreshold : k ≤ Zero.card ↔ γ ∈ B := by
    simpa only [Zero] using hzero γ
  constructor
  · intro hclose
    rw [Code.relCloseToWord_iff_exists_agreementCols] at hclose
    obtain ⟨S, hScard, hSagree⟩ := hclose
    have hsub : S ⊆ Zero := by
      intro i hiS
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply] using
        (hSagree i).1 hiS
    apply hthreshold.mp
    exact hScard.trans (Finset.card_le_card hsub)
  · intro hγ
    rw [Code.relCloseToWord_iff_exists_agreementCols]
    refine ⟨Zero, hthreshold.mpr hγ, ?_⟩
    intro i
    constructor
    · intro hiZero
      have hi := (Finset.mem_filter.mp hiZero).2
      simpa only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply] using hi
    · intro hne hiZero
      have hi := (Finset.mem_filter.mp hiZero).2
      exact hne (by simpa only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply] using hi)

open scoped NNReal in
private theorem subsingleton_bad_set_exact_close
    (C : ModuleCode ι F A) [Subsingleton C] (δ : ℝ≥0) (hδlt : δ < 1)
    (u : Fin 2 → ι → A) (B : Finset F) (hBne : B.Nonempty)
    (hBmem : ∀ β : F, β ∈ B ↔
      IsMCA (AffineLineGenerator F) C β u (δ : ℝ))
    (w : ∀ γ : {γ : F // γ ∈ B}, AffineMCABadWitness C δ γ.1 u) :
    ∃ v₀ v₁ : ι → A, ∀ β : F,
      δᵣ(v₀ + β • v₁, (0 : ι → A)) ≤ δ ↔ β ∈ B := by
  classical
  let Z := Finset.univ.filter fun i : ι => u 0 i = 0 ∧ u 1 i = 0
  let k := Fintype.card ι - Nat.floor (δ * Fintype.card ι)
  by_cases hZ : Z.card < k
  · refine ⟨u 0, u 1, ?_⟩
    exact subsingleton_original_line_exact C δ hδlt u B hBmem w (by
      simpa only [Z, k] using hZ)
  · have hkZ : k ≤ Z.card := Nat.le_of_not_gt hZ
    exact subsingleton_synthetic_line_exact C δ hδlt u B hBne w (by
      simpa only [Z, k] using hkZ)

open scoped NNReal ProbabilityTheory in
private theorem subsingleton_bad_set_card_le_a
    (C : ModuleCode ι F A) [Subsingleton C] (δ : ℝ≥0) (hδlt : δ < 1)
    (a : ℕ)
    (hld : IsLineDecodable (F := F) ((C : Set (ι → A))) δ a
      (Fintype.card ι + 1))
    (u : Fin 2 → ι → A) (B : Finset F)
    (hBmem : ∀ β : F, β ∈ B ↔
      IsMCA (AffineLineGenerator F) C β u (δ : ℝ))
    (w : ∀ γ : {γ : F // γ ∈ B}, AffineMCABadWitness C δ γ.1 u) :
    B.card ≤ a := by
  classical
  by_contra hle
  have haB : a < B.card := Nat.lt_of_not_ge hle
  have hBne : B.Nonempty := Finset.card_pos.mp (lt_of_le_of_lt (Nat.zero_le a) haB)
  obtain ⟨v₀, v₁, hexact⟩ :=
    subsingleton_bad_set_exact_close C δ hδlt u B hBne hBmem w
  have hBcard : B.card ≤ Fintype.card ι :=
    subsingleton_bad_set_card_le C δ u B w
  let z : C := 0
  obtain ⟨c₀, c₁, E, hEcard, hE⟩ :=
    line_decodable_cardinality_form C δ a (Fintype.card ι + 1) hld
      v₀ v₁ (fun _ : F => z) B
      (by
        intro γ hγ
        have hc := (hexact γ).2 hγ
        simpa only [z, Submodule.coe_zero] using hc)
      haB.le
  have hEB : E ⊆ B := by
    intro γ hγ
    have hc := (hE γ hγ).1
    apply (hexact γ).1
    simpa only [z, Submodule.coe_zero] using hc
  have hcardEB : E.card ≤ B.card := Finset.card_le_card hEB
  omega

open scoped NNReal ProbabilityTheory in
open Classical in
private theorem fixed_stack_bad_set_card_le_a
    (C : ModuleCode ι F A) (δ : ℝ≥0) (hδlt : δ < 1) (a : ℕ)
    (hld : IsLineDecodable (F := F) ((C : Set (ι → A))) δ a
      (Fintype.card ι + 1))
    (u : Fin 2 → ι → A) :
    (Finset.univ.filter fun γ : F =>
      IsMCA (AffineLineGenerator F) C γ u (δ : ℝ)).card ≤ a := by
  let B := Finset.univ.filter fun γ : F =>
    IsMCA (AffineLineGenerator F) C γ u (δ : ℝ)
  have hBmem : ∀ γ : F, γ ∈ B ↔
      IsMCA (AffineLineGenerator F) C γ u (δ : ℝ) := by
    intro γ
    simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
  let w : ∀ γ : {γ : F // γ ∈ B}, AffineMCABadWitness C δ γ.1 u :=
    fun γ => Classical.choice
      (is_mca_affine_line_bad_witness_nonempty C δ hδlt.le γ.1 u
        ((hBmem γ.1).1 γ.2))
  change B.card ≤ a
  cases subsingleton_or_nontrivial C with
  | inl hsub =>
      letI : Subsingleton C := hsub
      exact subsingleton_bad_set_card_le_a C δ hδlt a hld u B hBmem w
  | inr hnon =>
      letI : Nontrivial C := hnon
      exact nontrivial_bad_set_card_le_a C δ hδlt a hld u B w

open scoped NNReal ProbabilityTheory in
open Classical in
private theorem mcaError_le_proof
    (C : ModuleCode ι F A) (δ : ℝ≥0) (a : ℕ)
    (_hδ_lt : δ < 1)
    (_h : IsLineDecodable (F := F) ((C : Set (ι → A))) δ a
      (Fintype.card ι + 1)) :
    mcaError (AffineLineGenerator F) C (δ : ℝ) ≤
      (a : ENNReal) / (Fintype.card F : ENNReal) := by
  unfold mcaError
  refine iSup_le fun u => ?_
  rw [Probability.prob_uniform_eq_card_filter_div_card]
  apply ENNReal.div_le_div_right
  exact_mod_cast (fixed_stack_bad_set_card_le_a C δ _hδ_lt a _h u)

-- The pre-existing public signature below is locked to `origin/main`'s (fills a prior `sorry`),
-- and genuinely does not need `[DecidableEq ι]`, `[DecidableEq F]`, or `[Fintype A]`; `omit`
-- would alter the signature, so the two linters are suppressed narrowly here instead.
set_option linter.unusedDecidableInType false in
set_option linter.unusedFintypeInType false in
open scoped NNReal ProbabilityTheory in
/-- If `C` is `(δ, a, n+1)`-line-decodable, then its affine-line MCA error is at most
`a / |F|`:

  `IsLineDecodable (F := F) C δ a (n+1) → mcaError(AffineLineGenerator F, C, δ) ≤ a / |F|`

where `n = |ι|`. The hypotheses retain the source radius conditions `0 < δ < 1`. -/
theorem IsLineDecodable.mcaError_le
    (C : ModuleCode ι F A) (δ : ℝ≥0) (a : ℕ)
    (_hδ_pos : 0 < δ) (_hδ_lt : δ < 1)
    (_h : IsLineDecodable (F := F) ((C : Set (ι → A))) δ a
            (Fintype.card ι + 1)) :
    mcaError (AffineLineGenerator F) C (δ : ℝ)
        ≤ (a : ENNReal) / (Fintype.card F : ENNReal) :=
  mcaError_le_proof C δ a _hδ_lt _h -- ABF26-T4.21; external admit [GG25 Thm 3.5].

/-- Threshold form of `IsLineDecodable.mcaError_le`: any target `ε_star` that the `a/|F|`
budget clears at the instantiated parameters is a genuine affine-line MCA bound. The numeric
budget check is a hypothesis, so the contentful-range condition is discharged at the use site
rather than assumed by the reader. -/
theorem IsLineDecodable.mcaError_le_of_budget
    {ι : Type} [Fintype ι] [Nonempty ι]
    {F : Type} [Field F] [Fintype F]
    {A : Type} [Finite A] [DecidableEq A] [AddCommGroup A] [Module F A]
    (C : ModuleCode ι F A) (δ : ℝ≥0) (a : ℕ)
    (hδ_pos : 0 < δ) (hδ_lt : δ < 1)
    (h : IsLineDecodable (F := F) ((C : Set (ι → A))) δ a
           (Fintype.card ι + 1))
    (ε_star : ℝ≥0)
    (hbudget : (a : ENNReal) / (Fintype.card F : ENNReal) ≤ (ε_star : ENNReal)) :
    mcaError (AffineLineGenerator F) C (δ : ℝ) ≤ (ε_star : ENNReal) := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  exact le_trans (IsLineDecodable.mcaError_le C δ a hδ_pos hδ_lt h) hbudget

end

end CodingTheory
