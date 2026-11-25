/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.AffineCombiner.Persistent
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Persistence at poles and rational-pair counting -/

open Polynomial ReedSolomon Finset

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private def fullDomain : ZMod 5 ↪ ZMod 5 := Function.Embedding.refl _

private def spike (i : ZMod 5) : ZMod 5 := if i = 0 then 1 else 0

-- `H = 0`, `L = X` explains four coordinates, while the value at the pole is excluded.
example : IsAffinePersistent fullDomain 0 spike 0 4 0 1 0 := by
  refine ⟨0, X, X_ne_zero, by simp, by simp, ?_⟩
  have hset : affinePersistenceSet fullDomain 0 spike 0 1 0 0 X = univ.erase 0 := by
    ext i
    by_cases hi : i = 0 <;> simp [fullDomain, spike, hi]
  rw [hset]
  norm_num [ZMod.card]

private theorem mem_of_card_ge {s : Finset (ZMod 5)} (h : 5 ≤ #s) (i : ZMod 5) : i ∈ s := by
  have hcard : #s = Fintype.card (ZMod 5) :=
    Nat.le_antisymm s.card_le_univ (by simpa using h)
  rw [s.eq_univ_of_card hcard]
  exact mem_univ i

-- Counting the pole as agreement would incorrectly make this example persistent at all five
-- coordinates. A constant numerator vanishing at `1` must also vanish at `0`.
example : ¬ IsAffinePersistent fullDomain 0 spike 0 5 0 1 0 := by
  rintro ⟨H, L, _, _, hH, hB⟩
  have h0 := mem_of_card_ge hB 0
  have h1 := mem_of_card_ge hB 1
  have hconstant : H = C (H.coeff 0) := degree_le_zero_iff.mp hH
  rw [mem_affinePersistenceSet] at h0 h1
  have h0 := h0.2
  have h1 := h1.2
  have heval (x : ZMod 5) : H.eval x = H.coeff 0 := by
    simpa only [eval_C] using congrArg (fun Q : (ZMod 5)[X] ↦ Q.eval x) hconstant
  have hL : L.eval 0 ≠ 0 := by simpa [fullDomain] using h0.1
  have hH0 : H.coeff 0 = L.eval 0 := by
    simpa [fullDomain, spike, heval] using h0.2
  have hH1 : H.coeff 0 = 0 := by
    simpa [fullDomain, spike, heval] using h1.2
  exact hL (hH0.symm.trans hH1)

-- A nonpolynomial explanation: `G = 1 / X` gives `X * G = 1` away from the pole.
example : IsAffinePersistent fullDomain 0 (fun i ↦ i⁻¹) 1 4 0 1 1 := by
  refine ⟨1, X, X_ne_zero, by simp, by simp, ?_⟩
  have hset : affinePersistenceSet fullDomain 0 (fun i ↦ i⁻¹) 0 1 1 1 X =
      univ.erase 0 := by
    ext i
    by_cases hi : i = 0 <;> simp [fullDomain, hi]
  rw [hset]
  norm_num [ZMod.card]

-- The compatibility bound for a nonpolynomial pair applies to `G = 1 / X` at every degree bound.
open Classical in
example (d : ℕ) :
    #{c : ZMod 5 × ZMod 5 | ∃ P : (ZMod 5)[X], P.degree ≤ d ∧
      algebraMap (ZMod 5)[X] (RatFunc (ZMod 5)) P =
        algebraMap (ZMod 5)[X] (RatFunc (ZMod 5)) (affineMultiplier c.1 c.2) *
          (algebraMap (ZMod 5)[X] (RatFunc (ZMod 5)) X)⁻¹} ≤ 5 := by
  classical
  have hx : algebraMap (ZMod 5)[X] (RatFunc (ZMod 5)) X ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective (ZMod 5))).mpr X_ne_zero
  have hnot : ¬ ∃ F₁ G₁ : (ZMod 5)[X],
      algebraMap (ZMod 5)[X] (RatFunc (ZMod 5)) F₁ = 0 ∧
      algebraMap (ZMod 5)[X] (RatFunc (ZMod 5)) G₁ =
        (algebraMap (ZMod 5)[X] (RatFunc (ZMod 5)) X)⁻¹ ∧
      F₁.degree ≤ d ∧ G₁.degree < d := by
    rintro ⟨_, G₁, _, hG, _, _⟩
    have hmul : algebraMap (ZMod 5)[X] (RatFunc (ZMod 5)) (G₁ * X) =
        algebraMap (ZMod 5)[X] (RatFunc (ZMod 5)) 1 := by
      rw [map_mul, hG, inv_mul_cancel₀ hx, map_one]
    have hpoly := RatFunc.algebraMap_injective (ZMod 5) hmul
    have := congrArg (Polynomial.eval (0 : ZMod 5)) hpoly
    norm_num at this
  simpa [ZMod.card] using card_ratFunc_combination_map_le (.refl _) 0
    (algebraMap (ZMod 5)[X] (RatFunc (ZMod 5)) X)⁻¹ hnot

-- The Johnson hypotheses hold at `d = 0`, `B = 4`, and the bound is below `|F|² = 25`.
open Classical in
example (f g : ZMod 5 → ZMod 5) :
    (#{c : ZMod 5 × ZMod 5 | ∃ P,
      IsAffineExceptional fullDomain f g 0 3 1 c.1 c.2 P ∧
        IsAffinePersistent fullDomain f g 0 4 c.1 c.2 P} : ℝ) ≤ 150 / 11 := by
  have h := card_isAffineExceptional_persistent_map_le fullDomain f g (.refl _) (d := 0) (A := 3)
    (B := 4) (by decide) (by norm_num [ZMod.card])
  norm_num [ZMod.card, Nat.choose] at h ⊢
  exact h

-- Over `𝔽₄ ⊇ 𝔽₂`, the pair `(0, 1 / X)` is compatible exactly with the base-field
-- challenges `(0, β)`, so the subfield bound `|𝔽₂| = 2` is attained.
open Classical in
example (d : ℕ) :
    #{c : ZMod 2 × ZMod 2 | ∃ P : (GaloisField 2 2)[X], P.degree ≤ d ∧
      algebraMap (GaloisField 2 2)[X] (RatFunc (GaloisField 2 2)) P =
        algebraMap (GaloisField 2 2)[X] (RatFunc (GaloisField 2 2))
            (affineMultiplier (algebraMap (ZMod 2) (GaloisField 2 2) c.1)
              (algebraMap (ZMod 2) (GaloisField 2 2) c.2)) *
          (algebraMap (GaloisField 2 2)[X] (RatFunc (GaloisField 2 2)) X)⁻¹} = 2 := by
  set E := GaloisField 2 2
  set ι := algebraMap E[X] (RatFunc E)
  have hx : ι X ≠ 0 := (map_ne_zero_iff _ (RatFunc.algebraMap_injective E)).mpr X_ne_zero
  have hnot : ¬ ∃ F₁ G₁ : E[X], ι F₁ = 0 ∧ ι G₁ = (ι X)⁻¹ ∧ F₁.degree ≤ d ∧ G₁.degree < d := by
    rintro ⟨_, G₁, _, hG, _, _⟩
    have hmul : ι (G₁ * X) = ι 1 := by rw [map_mul, hG, inv_mul_cancel₀ hx, map_one]
    have := congrArg (Polynomial.eval (0 : E)) (RatFunc.algebraMap_injective E hmul)
    norm_num at this
  refine le_antisymm ?_ ?_
  · simpa [ZMod.card] using
      card_ratFunc_combination_map_le ⟨algebraMap (ZMod 2) E, (algebraMap (ZMod 2) E).injective⟩ 0
        (ι X)⁻¹ hnot
  · refine (card_le_card (s := {(0, 0), (0, 1)}) fun c hc ↦ ?_).trans' (by decide)
    refine mem_filter.mpr ⟨mem_univ _, C (algebraMap (ZMod 2) E c.2),
      degree_C_le.trans (by exact_mod_cast Nat.zero_le d), ?_⟩
    have hc1 : c.1 = 0 := by
      simp only [mem_insert, mem_singleton] at hc
      rcases hc with h | h <;> simp [h]
    rw [hc1, affineMultiplier, map_zero, map_zero, zero_add, map_mul, mul_assoc,
      mul_inv_cancel₀ hx, mul_one]

private noncomputable instance : Fintype (GaloisField 2 2) := Fintype.ofFinite _

private theorem card_galoisField_2_2 : Fintype.card (GaloisField 2 2) = 4 := by
  rw [← Nat.card_eq_fintype_card, GaloisField.card 2 2 (by norm_num)]
  norm_num

/-- An embedding of `𝔽₄` into `𝔽₁₆`, which exists since `2 ∣ 4`. -/
private noncomputable def embed₄ : GaloisField 2 2 →+* GaloisField 2 4 :=
  (Classical.choice (FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod 2)
    (by rw [GaloisField.finrank 2 (by norm_num), GaloisField.finrank 2 (by norm_num)]
        norm_num))).toRingHom

/-- The subfield `𝔽₄` as a 4-point domain in `𝔽₁₆`. -/
private noncomputable def domain₄ : GaloisField 2 2 ↪ GaloisField 2 4 :=
  ⟨embed₄, embed₄.injective⟩

/-- The challenge embedding `𝔽₄ ↪ 𝔽₁₆`, kept apart from the evaluation domain `domain₄`. -/
private noncomputable def challenge₄ : GaloisField 2 2 ↪ GaloisField 2 4 :=
  ⟨embed₄, embed₄.injective⟩

-- Challenges from `𝔽₄ ⊂ 𝔽₁₆` with polynomial witnesses: at most `4 choose 2 = 6` of the
-- `|𝔽₄|² = 16` challenges are exceptional.
open Classical in
example (f g : GaloisField 2 2 → GaloisField 2 4) (F₀ G₀ : (GaloisField 2 4)[X])
    (hF : F₀.degree ≤ 1) (hG : G₀.degree < 1) :
    #{c : GaloisField 2 2 × GaloisField 2 2 | IsAffineExceptional domain₄ f g 1 3 1
      (challenge₄ c.1) (challenge₄ c.2)
      (F₀ + affineMultiplier (challenge₄ c.1) (challenge₄ c.2) * G₀)} ≤ 6 := by
  refine (card_isAffineExceptional_add_mul_map_le domain₄ f g challenge₄ (d := 1) (A := 3) F₀ G₀
    hF hG).trans ?_
  rw [card_galoisField_2_2]
  decide

-- Any rational pair over `𝔽₁₆` accounts for at most `max |𝔽₄| (4 choose 2) = 6` challenges
-- from `𝔽₄`, below `|𝔽₄|² = 16`.
open Classical in
example (f g : GaloisField 2 2 → GaloisField 2 4) (F₀ G₀ : RatFunc (GaloisField 2 4)) :
    #{c : GaloisField 2 2 × GaloisField 2 2 | ∃ P : (GaloisField 2 4)[X],
      algebraMap (GaloisField 2 4)[X] (RatFunc (GaloisField 2 4)) P =
          F₀ + algebraMap (GaloisField 2 4)[X] (RatFunc (GaloisField 2 4))
            (affineMultiplier (challenge₄ c.1) (challenge₄ c.2)) * G₀ ∧
        IsAffineExceptional domain₄ f g 1 3 1 (challenge₄ c.1) (challenge₄ c.2) P} ≤ 6 := by
  refine (card_isAffineExceptional_ratFunc_map_le domain₄ f g challenge₄ (d := 1) (A := 3) F₀
    G₀).trans ?_
  rw [card_galoisField_2_2]
  decide

-- At `d = 0`, `B = 3`, `n = 4`, the persistent challenges from `𝔽₄` number at most
-- `4 · 2 / 5 · max 4 6 = 48 / 5`, below `|𝔽₄|² = 16`.
open Classical in
example (f g : GaloisField 2 2 → GaloisField 2 4) :
    (#{c : GaloisField 2 2 × GaloisField 2 2 | ∃ P,
      IsAffineExceptional domain₄ f g 0 3 1 (challenge₄ c.1) (challenge₄ c.2) P ∧
        IsAffinePersistent domain₄ f g 0 3 (challenge₄ c.1) (challenge₄ c.2) P} : ℝ) ≤ 48 / 5 := by
  have h := card_isAffineExceptional_persistent_map_le domain₄ f g challenge₄ (d := 0) (A := 3)
    (B := 3) (by decide) (by rw [card_galoisField_2_2]; decide)
  norm_num [card_galoisField_2_2, Nat.choose] at h
  exact h

/-- Two challenges in `𝔽₅`, indexed by a type that is not a field. -/
private def challenge₂ : Fin 2 ↪ ZMod 5 := ⟨fun i ↦ (i : ℕ), by decide⟩

-- The challenge type only needs to be finite. A rational pair that is not a low-degree
-- polynomial pair is polynomial for at most `|Fin 2| = 2` of the `4` challenges in `Fin 2 × Fin 2`.
open Classical in
example (F₀ G₀ : RatFunc (ZMod 5))
    (h : ¬ ∃ F₁ G₁ : (ZMod 5)[X], algebraMap (ZMod 5)[X] (RatFunc (ZMod 5)) F₁ = F₀ ∧
      algebraMap (ZMod 5)[X] (RatFunc (ZMod 5)) G₁ = G₀ ∧ F₁.degree ≤ 1 ∧ G₁.degree < 1) :
    #{c : Fin 2 × Fin 2 | ∃ P : (ZMod 5)[X], P.degree ≤ 1 ∧
      algebraMap (ZMod 5)[X] (RatFunc (ZMod 5)) P =
        F₀ + algebraMap (ZMod 5)[X] (RatFunc (ZMod 5))
          (affineMultiplier (challenge₂ c.1) (challenge₂ c.2)) * G₀} ≤ 2 :=
  card_ratFunc_combination_map_le challenge₂ F₀ G₀ h

/-- info: 'ReedSolomon.card_ratFunc_combination_map_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.card_ratFunc_combination_map_le

/-- info: 'ReedSolomon.card_isAffineExceptional_persistent_map_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.card_isAffineExceptional_persistent_map_le

/-- info: 'ReedSolomon.card_isAffineExceptional_add_mul_map_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.card_isAffineExceptional_add_mul_map_le

/-- info: 'ReedSolomon.card_isAffineExceptional_ratFunc_map_le' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedSolomon.card_isAffineExceptional_ratFunc_map_le
