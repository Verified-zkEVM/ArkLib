/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.RingSwitching.Packing.Relations
public import ArkLib.ProofSystem.RingSwitching.Packing.Batching
public import VCVio.EvalDist.ProbabilityBounds

/-!
# Batching publicly derived packing slices

A preceding scalar head can send component values `α : ιP → E` and retain the committed packed
source. The verifier derives `transpose α : ιE → P` publicly and batches it with one fresh
challenge. No additional slice message is sent. The pure reconstruction and target laws are in
`Relations.lean`; this module supplies separation for incorrect packed candidates.

The packing data, retained point `r`, message `α`, candidate set `S` and its cardinality bound
are fixed before this batching challenge. The weights, derived target and public multiplier
depend on the challenge. A consumer must separately anchor each candidate to its original commitment
and supply the fixed candidate-list premise. Correct candidates are excluded from the bad event.
An injective coefficient map `P → C` transports distinct slice families to the challenge algebra;
no embedding between the packing and opening algebras is required.

The concrete intended consumer is reference Flock's early residual scalar claim, using
`quirkyLayout` and `quirkyComponent` with the same packed source. Its native head, fixed residual
relation and eventual same-source `pc.evalRel` endpoint still require their conformance proofs.
These conditional algebraic probability laws do not establish commitment binding or extraction.

## References

* [Bünz, B., Rothblum, R., and Wang, W., *Flock: Fast Proving for Batch Boolean
  Computations*][BRW26]
* [*Ring switching, generalized*][RSG]
-/

@[expose] public section

noncomputable section

namespace RingSwitching.Packing.PackingData

open MvPolynomial Probability ProbabilityTheory
open scoped NNReal ENNReal

variable {B : Type} [CommRing B] (data : PackingData B)
  {C : Type} [CommRing C] [Algebra B C] [Algebra data.P C]
  [IsScalarTower B data.P C]

/-- An incorrect fixed packed candidate survives one fresh batching challenge only on a collision.
Injectivity is required only for this separation step. -/
theorem pr_derivedTarget_of_not_openingClaimRel_le {m : ℕ}
    (bat : BatchingStrategy C data.ιE)
    (hinj : Function.Injective (algebraMap data.P C)) (r : Fin m → data.E)
    (α : data.ιP → data.E) (p : data.P⦃≤ 1⦄[X Fin m])
    (h : ((α, r), data.unpack p) ∉ data.openingClaimRel m) :
    Pr{let c ← $ᵗ bat.Challenge}[
      (data.derivedTarget α (bat.weight c), p) ∈ data.sumcheckClaimRel m r (bat.weight c)] ≤
      (bat.error : ℝ≥0∞) := by
  have hne : data.transpose α ≠ data.actualSlices r p :=
    fun he => h ((data.openingClaimRel_iff_transpose_actualSlices r α p).mpr he)
  simp_rw [data.sumcheckClaimRel_iff_actualSlices, derivedTarget]
  exact bat.separates_map (algebraMap data.P C) hinj _ _ hne

open Classical in
/-- Only incorrect packed candidates contribute to the collision bound. The retained point,
component claims and candidate list are fixed before the fresh batching challenge. -/
theorem pr_exists_derivedTarget_not_openingClaimRel_le_card_filter_mul {m : ℕ}
    (bat : BatchingStrategy C data.ιE)
    (hinj : Function.Injective (algebraMap data.P C)) (r : Fin m → data.E)
    (α : data.ιP → data.E) (S : Finset data.P⦃≤ 1⦄[X Fin m]) :
    Pr{let c ← $ᵗ bat.Challenge}[∃ p ∈ S,
      ((α, r), data.unpack p) ∉ data.openingClaimRel m ∧
      (data.derivedTarget α (bat.weight c), p) ∈ data.sumcheckClaimRel m r (bat.weight c)] ≤
      (S.filter fun p => ((α, r), data.unpack p) ∉ data.openingClaimRel m).card *
        (bat.error : ℝ≥0∞) := by
  calc
    _ = Pr{let c ← $ᵗ bat.Challenge}[∃ p ∈
        S.filter (fun p => ((α, r), data.unpack p) ∉ data.openingClaimRel m),
        (data.derivedTarget α (bat.weight c), p) ∈ data.sumcheckClaimRel m r (bat.weight c)] := by
      apply prEvent_congr
      intro c
      simp only [Finset.mem_filter, and_assoc]
    _ ≤ _ := prEvent_exists_finset_le_card_mul _ _ _ (ε := bat.error) fun p hp =>
      data.pr_derivedTarget_of_not_openingClaimRel_le bat hinj r α p (Finset.mem_filter.mp hp).2

/-- For a fixed point, component family and at most `L` fixed candidates, the probability
that an incorrect candidate satisfies the derived target is at most `L * bat.error`. -/
theorem pr_exists_derivedTarget_not_openingClaimRel_le {m : ℕ}
    (bat : BatchingStrategy C data.ιE)
    (hinj : Function.Injective (algebraMap data.P C)) (r : Fin m → data.E)
    (α : data.ιP → data.E) (S : Finset data.P⦃≤ 1⦄[X Fin m])
    {L : ℕ} (hS : S.card ≤ L) :
    Pr{let c ← $ᵗ bat.Challenge}[∃ p ∈ S,
      ((α, r), data.unpack p) ∉ data.openingClaimRel m ∧
      (data.derivedTarget α (bat.weight c), p) ∈ data.sumcheckClaimRel m r (bat.weight c)] ≤
      L * (bat.error : ℝ≥0∞) := by
  classical
  refine (data.pr_exists_derivedTarget_not_openingClaimRel_le_card_filter_mul
    bat hinj r α S).trans ?_
  have hcard : (S.filter fun p => ((α, r), data.unpack p) ∉ data.openingClaimRel m).card ≤ L :=
    (Finset.card_filter_le _ _).trans hS
  gcongr

end RingSwitching.Packing.PackingData

end
