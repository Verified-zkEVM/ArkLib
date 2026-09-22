/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.FullCode
import Mathlib.Data.Fin.VecNotation
import Mathlib.FieldTheory.Finite.Basic

/-!
# Acceptance tests for Reed–Solomon codes at full rate

On the domain `0, 1` in `ℚ`, the word `(5, 7)` is a codeword of every code with degree bound at
least `2`. The bound `Fintype.card ι ≤ k` is needed: `(0, 1)` is not a codeword of degree bound
`1`. The MCA error of the full-rate code over `ZMod 3` is `0` for the affine-line generator and
for the affine-space generator. The forms with `[Nonempty ι]` are derived from the general
ones.
-/

open Polynomial CoreDefinitions

namespace ReedSolomon.FullCodeTest

/-- The domain `0, 1` in `ℚ`. -/
def dom : Fin 2 ↪ ℚ := ⟨![0, 1], by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all⟩

/-- Every word is a codeword at degree bound `3 ≥ 2`. -/
example : (![5, 7] : Fin 2 → ℚ) ∈ code dom 3 := by
  rw [code_eq_top_of_card_le dom (by simp)]
  exact Submodule.mem_top

/-- The bound is needed: `(0, 1)` is not the evaluation of a constant, so it is not a codeword of
degree bound `1 < 2`. -/
example : code dom 1 ≠ ⊤ := by
  intro htop
  have hmem : (![0, 1] : Fin 2 → ℚ) ∈ code dom 1 := htop ▸ Submodule.mem_top
  obtain ⟨p, hp, heval⟩ := mem_code_iff_eval.mp hmem
  rw [eq_C_of_degree_le_zero (p := p) (Nat.WithBot.lt_one_iff_le_zero.mp (by exact_mod_cast hp))]
    at heval
  have h0 := heval 0
  have h1 := heval 1
  simp only [eval_C] at h0 h1
  simp [h0] at h1

section Concrete

private instance : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩

/-- The domain `0, 1, 2` in `ZMod 3`. -/
def dom3 : ZMod 3 ↪ ZMod 3 := Function.Embedding.refl _

/-- The full-rate affine-line error over `ZMod 3` is `0` at radius `1 / 2`. -/
example [SampleableType (ZMod 3)] :
    mcaError (AffineLineGenerator (ZMod 3)) (code dom3 3) (1 / 2) = 0 := by
  simpa using mcaError_affineLine_fullRate_eq_zero dom3 (1 / 2)

/-- Any generator, here the affine-space generator in dimension `2`, at the degree bound `4`
above the block length and at the negative radius `-1`. -/
example [SampleableType (Fin 2 → ZMod 3)] :
    mcaError (AffineSpaceGenerator (ZMod 3) 2) (code dom3 4) (-1) = 0 :=
  mcaError_eq_zero_of_card_le _ dom3 (by simp) (-1)

end Concrete

section Specializations

open Classical in
/-- The code of degree bound `Fintype.card ι` is the whole space. -/
example {ι F : Type} [Fintype ι] [Field F] (domain : ι ↪ F) :
    code domain (Fintype.card ι) = ⊤ :=
  fullRate_code_eq_top domain

/-- The affine-line MCA error of the full-rate code is `0`, with the extra hypothesis
`[Nonempty ι]`. -/
example {ι F : Type} [Fintype ι] [Nonempty ι] [Field F] [Fintype F] [SampleableType F]
    (domain : ι ↪ F) (δ : ℝ) :
    mcaError (AffineLineGenerator F) (code domain (Fintype.card ι)) δ = 0 :=
  mcaError_affineLine_fullRate_eq_zero domain δ

/-- The generic step: the full module code has zero MCA error for every generator. -/
example {ι F ℓ S A : Type} [Fintype ι] [Field F] [Fintype ℓ] [Nonempty S] [Fintype S]
    [SampleableType S] [AddCommMonoid A] [Module F A] (G : Generator S ℓ F) (δ : ℝ) :
    mcaError G (⊤ : ModuleCode ι F A) δ = 0 :=
  mcaError_top_eq_zero G δ

end Specializations

end ReedSolomon.FullCodeTest
