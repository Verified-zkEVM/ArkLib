/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.Polynomial
import Mathlib.Algebra.Algebra.Tower

/-!
# Evaluation families, packed slices, and batched claims

These are the algebraic relations used by a coordinate-packing reduction. The input contains
the full family of opening values. A scalar evaluation protocol must separately prove its
head's reconstruction check. No commitment or security assumptions are hidden in these
relations; commitment anchoring is an additional boundary of a protocol integration.
-/

noncomputable section

namespace RingSwitching.Packing.PackingData

open Module MvPolynomial

variable {B : Type} [CommRing B] (data : PackingData B)

/-- Every component of a base-valued polynomial family has the claimed opening value. -/
def openingClaimRel (m : ℕ) :
    Set (((data.ιP → data.E) × (Fin m → data.E)) × (data.ιP → B⦃≤ 1⦄[X Fin m])) :=
  {x | ∀ i, x.1.1 i = MvPolynomial.aeval x.1.2 (x.2 i).val}

/-- Each slice is the coordinate-weighted Boolean sum of the packed polynomial. -/
def sliceRel (m : ℕ) (r : Fin m → data.E) :
    Set ((data.ιE → data.P) × data.P⦃≤ 1⦄[X Fin m]) :=
  {x | ∀ u, x.1 u =
    ∑ y : Fin m → Fin 2, data.eqCoord r y u • x.2.val.eval (y : Fin m → data.P)}

/-- The consistency check reads packed slice coordinates back in the opening basis. -/
def claimConsistent (α : data.ιP → data.E) (s : data.ιE → data.P) : Prop :=
  ∀ i, α i = ∑ u, data.packBasis.repr (s u) i • data.openBasis u

/-- The coordinate check is precisely equality with the faithful transpose. -/
theorem claimConsistent_iff_transpose (α : data.ιP → data.E) (s : data.ιE → data.P) :
    data.claimConsistent α s ↔ data.transpose α = s := by
  simp only [claimConsistent, ← data.transpose_symm_apply, ← funext_iff]
  exact data.transpose.eq_symm_apply

/-- Honest slices read back to the component evaluations, without a domain assumption. -/
theorem aeval_unpack_of_slices {m : ℕ} {r : Fin m → data.E}
    {s : data.ιE → data.P} {p : data.P⦃≤ 1⦄[X Fin m]}
    (hs : (s, p) ∈ data.sliceRel m r) (i : data.ιP) :
    MvPolynomial.aeval r (data.unpack p i).val =
      ∑ u, data.packBasis.repr (s u) i • data.openBasis u := by
  calc
    MvPolynomial.aeval r (data.unpack p i).val
        = ∑ y : Fin m → Fin 2, eqTilde (y : Fin m → data.E) r *
          algebraMap B data.E ((data.unpack p i).val.eval (y : Fin m → B)) :=
      aeval_multilinear_eq_sum_eqTilde (data.unpack p i).property r
    _ = ∑ y : Fin m → Fin 2, ∑ u, (data.eqCoord r y u *
          data.packBasis.repr (p.val.eval (y : Fin m → data.P)) i) • data.openBasis u := by
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [data.unpack_eval_zeroOne]
      have heq : eqTilde (y : Fin m → data.E) r = eqTilde r (y : Fin m → data.E) :=
        eqPolynomial_symm _ _
      rw [heq, ← data.openBasis.sum_repr (eqTilde r (y : Fin m → data.E)), Finset.sum_mul]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [smul_mul_assoc, ← Algebra.commutes, ← Algebra.smul_def, smul_smul]
      rfl
    _ = ∑ u, data.packBasis.repr (∑ y : Fin m → Fin 2,
          data.eqCoord r y u • p.val.eval (y : Fin m → data.P)) i • data.openBasis u := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← Finset.sum_smul]
      congr 1
      rw [map_sum, Finsupp.finsetSum_apply]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [map_smul, Finsupp.smul_apply, smul_eq_mul]
    _ = ∑ u, data.packBasis.repr (s u) i • data.openBasis u := by
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← hs u]

/-- Honest slices of a packed family satisfy the consistency check. -/
theorem claimConsistent_of_slices {m : ℕ} {r : Fin m → data.E}
    {α : data.ιP → data.E} {ps : data.ιP → B⦃≤ 1⦄[X Fin m]} {s : data.ιE → data.P}
    (hα : ((α, r), ps) ∈ data.openingClaimRel m)
    (hs : (s, data.packedMLE ps) ∈ data.sliceRel m r) :
    data.claimConsistent α s := fun i => by
  have h := data.aeval_unpack_of_slices hs i
  rw [data.unpack_packedMLE] at h
  exact (hα i).trans h

/-- Correct slices and the coordinate check imply every original opening claim. -/
theorem openingClaimRel_of_claimConsistent {m : ℕ} {r : Fin m → data.E}
    {α : data.ιP → data.E} {s : data.ιE → data.P} {p : data.P⦃≤ 1⦄[X Fin m]}
    (hc : data.claimConsistent α s) (hs : (s, p) ∈ data.sliceRel m r) :
    ((α, r), data.unpack p) ∈ data.openingClaimRel m :=
  fun i => (hc i).trans (data.aeval_unpack_of_slices hs i).symm

/-- Transposing all honest opening values yields exactly the packed slice sums. -/
theorem transpose_evaluations {m : ℕ} (r : Fin m → data.E)
    (ps : data.ιP → B⦃≤ 1⦄[X Fin m]) :
    data.transpose (fun i => MvPolynomial.aeval r (ps i).val) =
      fun u => ∑ y : Fin m → Fin 2,
        data.eqCoord r y u • (data.packedMLE ps).val.eval (y : Fin m → data.P) := by
  apply (data.claimConsistent_iff_transpose _ _).mp
  exact data.claimConsistent_of_slices (fun _ => rfl) (fun _ => rfl)

/-- The public transpose preserves and reflects the full family of evaluation claims. -/
theorem openingClaimRel_iff_sliceRel {m : ℕ} (r : Fin m → data.E)
    (α : data.ιP → data.E) (ps : data.ιP → B⦃≤ 1⦄[X Fin m]) :
    ((α, r), ps) ∈ data.openingClaimRel m ↔
      (data.transpose α, data.packedMLE ps) ∈ data.sliceRel m r := by
  change (∀ i, α i = _) ↔ (∀ u, data.transpose α u = _)
  rw [← funext_iff, ← funext_iff, ← data.transpose_evaluations]
  exact data.transpose.injective.eq_iff.symm

section ChallengeAlgebra

variable {C : Type*} [CommRing C] [Algebra B C] [Algebra data.P C]
  [IsScalarTower B data.P C]

/-- The weighted sumcheck claim after transporting packed values into a challenge algebra.
This algebraic definition does not require the coefficient transport to be injective. -/
def sumcheckClaimRel (m : ℕ) (r : Fin m → data.E) (weight : data.ιE → C) :
    Set (C × data.P⦃≤ 1⦄[X Fin m]) :=
  {x | x.1 = ∑ y : Fin m → Fin 2,
    (data.multiplier r weight).val.eval (y : Fin m → C) *
      algebraMap data.P C (x.2.val.eval (y : Fin m → data.P))}

/-- Batching honest slices gives the sumcheck target in any compatible challenge algebra. -/
theorem sumcheckClaim_of_slices {m : ℕ} {r : Fin m → data.E}
    {s : data.ιE → data.P} {p : data.P⦃≤ 1⦄[X Fin m]}
    (hs : (s, p) ∈ data.sliceRel m r) (weight : data.ιE → C) :
    (∑ u, weight u * algebraMap data.P C (s u), p) ∈
      data.sumcheckClaimRel m r weight := by
  change _ = _
  change ∀ u, s u = ∑ y : Fin m → Fin 2,
    data.eqCoord r y u • p.val.eval (y : Fin m → data.P) at hs
  simp only [hs, map_sum, Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply B data.P C, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [data.multiplier_eval_zeroOne, Finset.sum_mul]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Algebra.smul_def]
  ring

end ChallengeAlgebra

end RingSwitching.Packing.PackingData

end
