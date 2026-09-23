/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Probability.Uniform
import Mathlib.MeasureTheory.Measure.Basic

open scoped ENNReal ProbabilityTheory

example {α : Type} [Fintype α] [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : ProbComp α) (p : α → Prop) :
    Pr{let x ← mx}[p x] =
      ∑' x, {x | p x}.indicator (fun y => 𝒟[mx] {y}) x := by
  classical
  rw [prEvent_eq_evalDist_of_discrete, tsum_fintype]
  calc
    𝒟[mx] {x | p x} = 𝒟[mx] ↑(Finset.univ.filter p) := by
      congr 1
      ext n
      simp
    _ = ∑ x ∈ Finset.univ.filter p, 𝒟[mx] {x} :=
      (MeasureTheory.sum_measure_singleton
        (μ := 𝒟[mx]) (s := Finset.univ.filter p)).symm
    _ = ∑ x, {x | p x}.indicator (fun y => 𝒟[mx] {y}) x := by
      simp [Set.indicator, Finset.sum_filter]

example : Pr{let n ← $ᵗ (Fin 2)}[n = 0] = (1 / 2 : ENNReal) := by
  rw [SampleableType.prEvent_uniformSample]
  have hcard : (Finset.univ.filter (fun n : Fin 2 => n = 0)).card = 1 := by
    decide
  rw [hcard]
  norm_num

example :
    Pr{let n ← $ᵗ (Fin 2)}[Equiv.swap (0 : Fin 2) 1 n = 0] =
      Pr{let n ← $ᵗ (Fin 2)}[n = 0] := by
  exact SampleableType.prEvent_uniformSample_equiv
    (Equiv.swap 0 1) (fun n : Fin 2 => n = 0)
