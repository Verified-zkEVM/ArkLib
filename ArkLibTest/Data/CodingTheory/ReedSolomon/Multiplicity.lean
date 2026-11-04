/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frederik
-/

import ArkLib.Data.CodingTheory.ReedSolomon.Multiplicity
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum

/-!
# Univariate multiplicity code distance tests

The distance theorems apply over `ZMod 3` on its full domain, with `k = 3` and `s = 2`, so their
hypotheses are satisfiable at the characteristic boundary `k = ringChar F`. At `s = 1` the formula
is the Reed-Solomon value `n - k + 1`. At `k = 0` the code has no two distinct words, so the
distance is `0` rather than `n`, and `0 < k` cannot be dropped.
-/

open ReedSolomon ReedSolomon.Multiplicity

namespace ArkLibTest.ReedSolomonMultiplicity

/-- The three points of `ZMod 3`. -/
def domain : ZMod 3 ↪ ZMod 3 := Function.Embedding.refl _

private lemma char_ge : ringChar (ZMod 3) = 0 ∨ 3 ≤ ringChar (ZMod 3) :=
  Or.inr (by rw [ZMod.ringChar_zmod_n])

/-- Below saturation and at the characteristic boundary, the distance is `3 - 2 / 2 = 2`. -/
example : Code.dist (umCode domain 3 2 : Set (ZMod 3 → Fin 2 → ZMod 3)) = 2 := by
  have h := dist_umCode_eq domain (k := 3) (s := 2) char_ge (by norm_num) (by norm_num)
    (by simp [ZMod.card])
  simpa [ZMod.card] using h

/-- The bound applies to the distinct codewords of the message `X` and the zero message. -/
example : 2 ≤ hammingDist (umEvalOnPoints domain 2 Polynomial.X)
    (umEvalOnPoints domain 2 (0 : Polynomial (ZMod 3))) := by
  have hX : umEvalOnPoints domain 2 Polynomial.X ∈ umCode domain 3 2 :=
    Submodule.mem_map_of_mem
      (Polynomial.mem_degreeLT.mpr (by rw [Polynomial.degree_X]; norm_num))
  have h0 : umEvalOnPoints domain 2 (0 : Polynomial (ZMod 3)) ∈ umCode domain 3 2 :=
    Submodule.mem_map_of_mem (zero_mem _)
  have hne : umEvalOnPoints domain 2 Polynomial.X ≠
      umEvalOnPoints domain 2 (0 : Polynomial (ZMod 3)) := by
    intro h
    have := congrFun (congrFun h 1) 0
    simp [umEvalOnPoints, domain] at this
  have hb := hammingDist_umCode_ge domain char_ge (by norm_num) hX h0 hne
  simpa [ZMod.card] using hb

/-- At `s = 1` the formula is the Reed-Solomon distance. -/
example {ι F : Type*} [Fintype ι] [Field F] [DecidableEq F] (dom : ι ↪ F) {k : ℕ}
    (hchar : ringChar F = 0 ∨ k ≤ ringChar F) (hk : 0 < k) (hkn : k ≤ Fintype.card ι) :
    Code.dist (umCode dom k 1 : Set (ι → Fin 1 → F)) = Fintype.card ι - (k - 1) := by
  simpa using dist_umCode_eq dom hchar one_pos hk (by simpa using hkn)

/-- At `k = 0` the only codeword is zero, so the distance is `0`, not `3`. -/
example : Code.dist (umCode domain 0 2 : Set (ZMod 3 → Fin 2 → ZMod 3)) = 0 := by
  have hzero : ∀ c ∈ (umCode domain 0 2 : Set (ZMod 3 → Fin 2 → ZMod 3)), c = 0 := by
    intro c hc
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hc
    have hp0 : p = 0 := by
      have hdeg := Polynomial.mem_degreeLT.mp hp
      rwa [Nat.cast_zero, Nat.WithBot.lt_zero_iff, Polynomial.degree_eq_bot] at hdeg
    simp [hp0]
  have hempty : {d | ∃ u ∈ (umCode domain 0 2 : Set (ZMod 3 → Fin 2 → ZMod 3)),
      ∃ v ∈ (umCode domain 0 2 : Set (ZMod 3 → Fin 2 → ZMod 3)),
        u ≠ v ∧ hammingDist u v ≤ d} = ∅ := by
    ext d
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨u, hu, v, hv, hne, -⟩
    exact hne ((hzero u hu).trans (hzero v hv).symm)
  rw [Code.dist, hempty, Nat.sInf_empty]

end ArkLibTest.ReedSolomonMultiplicity
