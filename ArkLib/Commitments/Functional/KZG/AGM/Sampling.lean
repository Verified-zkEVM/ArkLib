/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import VCVio.CryptoFoundations.HardnessAssumptions.SDH

/-!
# Changing the KZG trapdoor distribution

An event under uniform nonzero sampling is bounded by its probability under uniform sampling
plus the probability of zero. This accounts for the distribution change in the KZG AGM reduction.

References: [KZG10TR]; Fuchsbauer, Kiltz, and Loss, *The Algebraic Group Model and its
Applications*, CRYPTO 2018.
-/

@[expose] public section

open OracleComp OracleSpec
open scoped ENNReal

namespace KZG.AGM

/-- Any probabilistic event loses at most `1 / |F|` when replacing nonzero sampling by uniform
sampling. The continuation may itself use randomness or fail. -/
theorem sampleTrapdoor_event_le {F α : Type} [Field F] [Fintype F] [DecidableEq F]
    [SampleableType F] (A : F → ProbComp α) (event : α → Prop) :
    Pr{let a ← SDH.sampleTrapdoor F >>= A}[event a] ≤
      Pr{let a ← ($ᵗ F : ProbComp F) >>= A}[event a] + 1 / (Fintype.card F : ℝ≥0∞) := by
  classical
  let : Nonempty {x : F // x ≠ 0} := ⟨⟨1, one_ne_zero⟩⟩
  let := SampleableType.subtype F (· ≠ 0)
  let p := Pr{let a ← SDH.sampleTrapdoor F >>= A}[event a]
  let q := Pr{let a ← ($ᵗ F : ProbComp F) >>= A}[event a]
  have hp : (Fintype.card {x : F // x ≠ 0} : ℝ≥0∞) * p =
      ∑ x : {x : F // x ≠ 0}, Pr{let a ← A x.val}[event a] := by
    simpa only [p, SDH.sampleTrapdoor, bind_map_left] using
      SampleableType.natCast_card_mul_prEvent_uniformSample_bind
        (fun x : {x : F // x ≠ 0} => A x.val) event
  have hq := SampleableType.natCast_card_mul_prEvent_uniformSample_bind A event
  have hc : Fintype.card {x : F // x ≠ 0} + 1 = Fintype.card F := by
    simp only [Fintype.card_subtype, Finset.filter_ne',
      Finset.card_erase_of_mem (Finset.mem_univ (0 : F)), Finset.card_univ]
    exact Nat.sub_add_cancel Fintype.card_pos
  have hs : (∑ x : {x : F // x ≠ 0}, Pr{let a ← A x.val}[event a]) ≤
      ∑ x : F, Pr{let a ← A x}[event a] := by
    rw [← Finset.sum_subtype (p := fun x : F => x ≠ 0)
      (Finset.univ.filter (fun x : F => x ≠ 0)) (by simp) (fun x => Pr{let a ← A x}[event a])]
    exact Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  have hmul : (Fintype.card F : ℝ≥0∞) * p ≤ (Fintype.card F : ℝ≥0∞) * q + 1 := by
    calc
      (Fintype.card F : ℝ≥0∞) * p =
          (Fintype.card {x : F // x ≠ 0} : ℝ≥0∞) * p + p := by
            rw [← hc, Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      _ ≤ (Fintype.card F : ℝ≥0∞) * q + 1 :=
        add_le_add (hp.le.trans (hs.trans hq.symm.le)) (prEvent_le_one _)
  have hne : (Fintype.card F : ℝ≥0∞) ≠ 0 := by simp
  have hfin : (Fintype.card F : ℝ≥0∞) ≠ ⊤ := by simp
  have hd : (Fintype.card F : ℝ≥0∞)⁻¹ * ((Fintype.card F : ℝ≥0∞) * p) ≤
      (Fintype.card F : ℝ≥0∞)⁻¹ * ((Fintype.card F : ℝ≥0∞) * q + 1) := by
    gcongr
  simpa only [mul_add, ← mul_assoc, ENNReal.inv_mul_cancel hne hfin, one_mul,
    mul_one, one_div] using hd

end KZG.AGM
