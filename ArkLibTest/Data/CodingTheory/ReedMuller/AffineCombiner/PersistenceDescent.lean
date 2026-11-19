/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/

import ArkLib.Data.CodingTheory.ReedMuller.AffineCombiner.PersistenceDescent
import Mathlib.FieldTheory.Finite.GaloisField

/-! # Acceptance cases for Reed–Muller persistence witnesses over the base field -/

open ReedMuller MvPolynomial Finset

private instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The multiplier `L = X₁` in two variables over `F₉`. -/
private noncomputable def σE : Fin 3 → GaloisField 3 2 := ![0, 1, 0]

-- Over `F₉`, `H = X₁` and `L = X₁` satisfy `H = L · 1` at every point of `F₃²`.
-- The identities descend to a nonzero `σ₀` and `H₀` of total degree at most one over `F₃`.
example : ∃ H₀ : MvPolynomial (Fin 2) (ZMod 3), ∃ σ₀ : Fin 3 → ZMod 3, σ₀ ≠ 0 ∧
    H₀.totalDegree ≤ 1 ∧ ∀ z : Fin 2 → ZMod 3, eval z H₀ = eval z (affineMultiplier σ₀) * 1 := by
  refine exists_affineRatioWitness_of_map (algebraMap (ZMod 3) (GaloisField 3 2)) id
    (fun _ ↦ 1) 1 (H := X 0) (σ := σE) (fun h ↦ ?_) (by simp) fun z ↦ ?_
  · simpa [σE] using congrFun h 1
  · simp [σE, Fin.sum_univ_two]

/-- The multiplier `L = X₁` in two variables over `F₃`. -/
private def σX : Fin 3 → ZMod 3 := ![0, 1, 0]

-- On the grid `F₃²` (`q₀ᵏ⁻¹ = 3`), `H = 0` and `L = X₁` explain the zero words on all `9` points.
-- `X₁` vanishes at exactly `3` of them, so `9 = B + 3` common agreements give persistence at `6`.
example : IsAffinePersistent (K₀ := ZMod 3) (F := ZMod 3) (k := 2) (fun _ ↦ 0) (fun _ ↦ 0)
    0 6 0 0 := by
  refine isAffinePersistent_of_commonAgreement _ _ (σ := σX) (H := 0) univ ?_ ?_ (by decide)
    (by simp) fun z _ ↦ by simp
  · simp [ZMod.card]
  · intro z _
    simp

-- A nonzero constant multiplier has no zeros, and `B + q₀ᵏ⁻¹` agreements still suffice.
example (f g : (Fin 2 → ZMod 3) → ZMod 3) (α : Fin 3 → ZMod 3) (P : MvPolynomial (Fin 2) (ZMod 3))
    (T : Finset (Fin 2 → ZMod 3)) (hT : 5 ≤ #T)
    (hagree : T ⊆ agreementSet (combinedWord f g (affineMultiplier α)) P)
    (hg : ∀ z ∈ T, g z = 0) :
    IsAffinePersistent f g 0 2 α P :=
  isAffinePersistent_of_commonAgreement f g (σ := ![1, 0, 0]) (H := 0) T
    (by simpa [ZMod.card] using hT) hagree (by decide) (by simp) fun z hz ↦ by simp [hg z hz]

/-- info: 'ReedMuller.exists_affineRatioWitness_of_map' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.exists_affineRatioWitness_of_map

/-- info: 'ReedMuller.isAffinePersistent_of_commonAgreement' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms ReedMuller.isAffinePersistent_of_commonAgreement
