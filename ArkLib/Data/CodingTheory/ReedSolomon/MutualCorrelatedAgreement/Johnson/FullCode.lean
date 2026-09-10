/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ProximityGenerator.Basic
public import ArkLib.Data.CodingTheory.ReedSolomon

/-!
# The full-rate Reed--Solomon boundary

A Reed--Solomon code whose message dimension equals its block length is the whole ambient
space: Lagrange interpolation represents every received word by a polynomial of degree strictly
less than the block length. Consequently no constituent of an affine-line family can fail to
extend from an agreement subset, so the mutual correlated agreement error is exactly zero at
every real radius.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial CoreDefinitions LinearCode
open scoped ProbabilityTheory

open Classical in
/-- A Reed--Solomon code of dimension equal to its block length is the full ambient code. -/
theorem fullRate_code_eq_top
    {ι F : Type} [Fintype ι] [Field F]
    (domain : ι ↪ F) :
    code domain (Fintype.card ι) = ⊤ := by
  apply top_unique
  intro w _
  apply mem_code_iff_eval.mpr
  refine ⟨Lagrange.interpolate Finset.univ domain w, ?_, ?_⟩
  · simpa using Lagrange.degree_interpolate_lt
      (s := Finset.univ) (v := domain) (r := w) domain.injective.injOn
  · intro i
    exact Lagrange.eval_interpolate_at_node w domain.injective.injOn (Finset.mem_univ i)

open Classical in
/-- At full rate, affine-line MCA has zero error at every real radius.

This includes the endpoint and out-of-range radii: the conclusion follows from every word being
a codeword, independently of the agreement-size clause in the MCA event. -/
theorem mcaError_affineLine_fullRate_eq_zero
    {ι F : Type} [Fintype ι] [Nonempty ι]
    [Field F] [Fintype F]
    (domain : ι ↪ F) (δ : ℝ) :
    mcaError (AffineLineGenerator F) (code domain (Fintype.card ι)) δ = 0 := by
  classical
  have hcode : code domain (Fintype.card ι) = ⊤ := fullRate_code_eq_top domain
  unfold mcaError
  apply le_antisymm
  · refine iSup_le fun U => ?_
    rw [Probability.prob_uniform_eq_ofReal]
    have hfalse : ∀ x : F,
        ¬ IsMCA (AffineLineGenerator F) (code domain (Fintype.card ι)) x U δ := by
      rintro x ⟨T, _hT, _hcombination, j, hj⟩
      apply hj
      rw [LinearCode.mem_projectedCodeSubmod_iff]
      refine ⟨U j, ?_, rfl⟩
      rw [hcode]
      exact Submodule.mem_top
    rw [Finset.filter_false_of_mem fun x _ => hfalse x]
    simp
  · exact bot_le

end ReedSolomon
