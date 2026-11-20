/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nam Ngo
-/

import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges.Goldilocks512.Lower
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallenges.Goldilocks512.Upper
import CompPoly.Fields.Goldilocks.Basic
import Mathlib.FieldTheory.Finite.GaloisField

/-!
# Goldilocks `RS[512, 128]`: the witnesses at `GaloisField p 3`

The field facts the `Goldilocks512` witnesses need hold for `K = GaloisField p 3`,
`p = Goldilocks.fieldSize = 2 ^ 64 - 2 ^ 32 + 1`: they are proved here, not assumed, so the four
witnesses are not vacuous. On the domain of powers of a primitive `512`-th root of unity in `K`,
every boundary index `kStar` of a `GrandMcaResolution` or of a `GrandListResolution` satisfies
`273 ≤ kStar < 377`.
-/

namespace Goldilocks512Test

open ProximityGap ProximityGap.GrandChallenges ProximityGap.GrandChallenges.Goldilocks512
open ReedSolomon
open scoped NNReal

/-- The cubic extension of the Goldilocks field. -/
abbrev K := GaloisField Goldilocks.fieldSize 3

noncomputable instance : Fintype K := Fintype.ofFinite _
noncomputable instance : DecidableEq K := Classical.decEq _
noncomputable instance : SampleableType K := SampleableType.ofFintype _

theorem card_K : Fintype.card K = Goldilocks.fieldSize ^ 3 := by
  rw [Fintype.card_eq_nat_card, GaloisField.card _ _ (by norm_num)]

theorem ringChar_K : ringChar K = Goldilocks.fieldSize := ringChar.eq K _

/-- `512` divides `p ^ 3 - 1 = |Kˣ|`, and `Kˣ` is cyclic. -/
theorem exists_primitiveRoot_K : ∃ ω : K, IsPrimitiveRoot ω 512 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hdvd : 512 ∣ Nat.card Kˣ := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, card_K]; decide +kernel
  obtain ⟨c, hc⟩ := hdvd
  have hpr : IsPrimitiveRoot g (Nat.card Kˣ) := hg ▸ IsPrimitiveRoot.orderOf g
  have h512 : IsPrimitiveRoot (g ^ c) 512 := hpr.pow Nat.card_pos (by rw [hc, mul_comm])
  exact ⟨((g ^ c : Kˣ) : K), IsPrimitiveRoot.coe_units_iff.mpr h512⟩

theorem hcharMca : ringChar K = 0 ∨ 280 < ringChar K :=
  Or.inr (by rw [ringChar_K]; decide +kernel)

theorem hcharList : ringChar K = 0 ∨ 260 < ringChar K :=
  Or.inr (by rw [ringChar_K]; decide +kernel)

theorem mcaLower_card : 968363869378722615 * 2 ^ 128 ≤ Fintype.card K := by
  rw [card_K]; decide +kernel

theorem listLower_card : 399224017 * 2 ^ 128 ≤ Fintype.card K := by
  rw [card_K]; decide +kernel

theorem card_ge : 1024 ≤ Fintype.card K := by
  rw [card_K]; decide +kernel

theorem listUpper_card : Fintype.card K < cosetListSize * 2 ^ 128 := by
  rw [card_K]; unfold cosetListSize; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel

theorem mcaUpper_card : 2 * Fintype.card K < (cosetListSize - 1) * 2 ^ 128 := by
  rw [card_K]; unfold cosetListSize; rw [Nat.choose_eq_descFactorial_div_factorial]; decide +kernel

noncomputable example (domain : Fin 512 ↪ K) :
    McaLowerWitness (ReedSolomon.code domain 128) (1 / 2 ^ 128) :=
  mcaLowerWitness hcharMca mcaLower_card domain

noncomputable example (domain : Fin 512 ↪ K) :
    ListLowerWitness (ReedSolomon.code domain 128 : Set (Fin 512 → K)) 3 (1 / 2 ^ 128) :=
  listLowerWitness hcharList listLower_card domain 3

noncomputable example {ω : K} (hω : IsPrimitiveRoot ω 512) :
    McaUpperWitness (ReedSolomon.code (primitiveRootDomain hω) 128) (1 / 2 ^ 128) :=
  mcaUpperWitness hω card_ge mcaUpper_card

noncomputable example {ω : K} (hω : IsPrimitiveRoot ω 512) :
    ListUpperWitness (ReedSolomon.code (primitiveRootDomain hω) 128 : Set (Fin 512 → K)) 3
      (1 / 2 ^ 128) :=
  listUpperWitness hω listUpper_card 3 (by norm_num)

/-- On the domain of powers of `ω`, every MCA boundary lies in `[273, 377)`. -/
theorem mca_bracket {ω : K} (hω : IsPrimitiveRoot ω 512)
    (R : GrandMcaResolution (ReedSolomon.code (primitiveRootDomain hω) 128) (1 / 2 ^ 128)) :
    273 ≤ R.kStar ∧ R.kStar < 377 := by
  have h1 := (mcaLowerWitness hcharMca mcaLower_card (primitiveRootDomain hω)).lt_boundary R
  have h2 := (mcaUpperWitness hω card_ge mcaUpper_card).boundary_lt R
  change (273 / 512 : ℝ≥0) < gridPt (ι := Fin 512) (R.kStar + 1) at h1
  change gridPt (ι := Fin 512) R.kStar < (377 / 512 : ℝ).toNNReal at h2
  rw [gridPt, Fintype.card_fin, ← NNReal.coe_lt_coe] at h1 h2
  rw [Real.coe_toNNReal _ (by norm_num)] at h2
  push_cast at h1 h2
  rw [div_lt_div_iff_of_pos_right (by norm_num)] at h1 h2
  constructor
  · have : (273 : ℝ) < ((R.kStar + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact Nat.lt_succ_iff.mp (by exact_mod_cast this)
  · exact_mod_cast h2

/-- On the domain of powers of `ω`, every list-decoding boundary lies in `[273, 377)`, for every
interleaving `m ≥ 1`. -/
theorem list_bracket {ω : K} (hω : IsPrimitiveRoot ω 512) (m : ℕ) (hm : 1 ≤ m)
    (R : GrandListResolution (ReedSolomon.code (primitiveRootDomain hω) 128 :
      Set (Fin 512 → K)) m (1 / 2 ^ 128)) :
    273 ≤ R.kStar ∧ R.kStar < 377 := by
  have h1 := (listLowerWitness hcharList listLower_card (primitiveRootDomain hω) m).lt_boundary R
  have h2 := (listUpperWitness hω listUpper_card m hm).boundary_lt R
  change (273 / 512 : ℝ≥0) < gridPt (ι := Fin 512) (R.kStar + 1) at h1
  change gridPt (ι := Fin 512) R.kStar < (377 / 512 : ℝ≥0) at h2
  rw [gridPt, Fintype.card_fin, ← NNReal.coe_lt_coe] at h1 h2
  push_cast at h1 h2
  rw [div_lt_div_iff_of_pos_right (by norm_num)] at h1 h2
  constructor
  · have : (273 : ℝ) < ((R.kStar + 1 : ℕ) : ℝ) := by push_cast; linarith
    exact Nat.lt_succ_iff.mp (by exact_mod_cast this)
  · exact_mod_cast h2

end Goldilocks512Test
