/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Opening
public import ArkLib.ProofSystem.RingSwitching.Packing.ProductSumcheck.Basic

/-!
# Initial state of the fused sumcheck and folding loop

The batching head supplies a packed polynomial and a claim about its product with a public
multilinear multiplier. The folding loop starts with that product as its residual polynomial
and the honest encoding as its internal word. The internal word is not the committed oracle:
relaxed input compatibility continues to permit a nearby, inexact committed oracle.

The canonical witness is a mathematical object using the existing noncomputable encoding API.
No extra prover message or verifier challenge is introduced by this state representation.
-/

@[expose] public section

namespace Binius.FRIBinius.Unrolled

open Binius.BinaryBasefold Sumcheck.Structured MvPolynomial AdditiveNTT

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (K : Type) [Field K] [Fintype K] [Fact (Fintype.card K = 2)] [Algebra K L]
local instance [Finite K] : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩
variable (β : Fin r → L) [Fact (LinearIndependent K β)]
variable {ℓ R : ℕ} [NeZero R] {h_rate : ℓ + R < r}
variable {Context : Type} (multpoly : Context → MultilinearPoly L ℓ)

/-- The public batching target and context, with no folding challenges yet. -/
def initialStatement (ctx : Context) (target : L) :
    Statement (L := L) (ℓ := ℓ) Context 0 :=
  ⟨target, Fin.elim0, ctx⟩

/-- The packed polynomial, its multiplier product, and its internally reconstructed encoding. -/
noncomputable def initialWitness (ctx : Context) (p : MultilinearPoly L ℓ) :
    Witness K β (h_ℓ_add_R_rate := h_rate) (ℓ := ℓ) 0 where
  t := p
  H := projectToMidSumcheckPoly ℓ p (multpoly ctx) 0 Fin.elim0
  f := getMidCodewords K β (h_ℓ_add_R_rate := h_rate) p Fin.elim0

/-- The initial residual polynomial is the public multiplier times the packed polynomial. -/
theorem initialWitness_H_val (ctx : Context) (p : MultilinearPoly L ℓ) :
    (initialWitness K β multpoly (h_rate := h_rate) ctx p).H.val =
      (multpoly ctx).val * p.val := by
  simp [initialWitness, projectToMidSumcheckPoly, computeInitialSumcheckPoly,
    MvPolynomial.fixFirstVariablesOfMQP_zero]

/-- Canonical initialization satisfies the folding loop's structural invariant, independently
of the committed oracle and of whether that oracle is an exact encoding. -/
theorem initialWitness_structural (ctx : Context) (target : L) (p : MultilinearPoly L ℓ) :
    WitnessStructuralInvariant K β (multpoly := multpoly) (h_ℓ_add_R_rate := h_rate)
      (initialStatement ctx target) (initialWitness K β multpoly ctx p) := by
  exact ⟨rfl, rfl⟩

/-- Initial sum-check consistency is the Boolean sum of the multiplier-product polynomial. -/
theorem initial_sumcheck_iff (ctx : Context) (target : L) (p : MultilinearPoly L ℓ) :
    sumcheckConsistencyProp (boolDomain L ℓ) target
      (initialWitness K β multpoly (h_rate := h_rate) ctx p).H ↔
      target = ∑ y : Fin ℓ → Fin 2,
        (multpoly ctx).val.eval (y : Fin ℓ → L) * p.val.eval (y : Fin ℓ → L) := by
  unfold sumcheckConsistencyProp
  rw [sum_cube_boolDomain]
  simp only [initialWitness_H_val, eval_mul]

variable [Fact (β 0 = 1)] [NeZero ℓ]
variable {ϑ : ℕ} [NeZero ϑ] [Fact (ϑ ∣ ℓ)]

/-- Backward extraction at the initial frontier recovers the product-sum claim and proximity
of the same packed polynomial, without upgrading proximity to exact equality. -/
theorem product_sum_and_compatibility_of_mem_roundRelation_zero
    (ctx : Context) (target : L)
    (ost : ∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j)
    (w : Witness K β (h_ℓ_add_R_rate := h_rate) (ℓ := ℓ) 0)
    (h : ((initialStatement ctx target, ost), w) ∈
      roundRelation (multpoly := multpoly) K β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L) 0) :
    (target = ∑ y : Fin ℓ → Fin 2,
      (multpoly ctx).val.eval (y : Fin ℓ → L) * w.t.val.eval (y : Fin ℓ → L)) ∧
      FirstOracleWitnessConsistent K β w.t (getFirstOracle K β ost) := by
  rw [mem_roundRelation_zero_iff] at h
  obtain ⟨hsum, hstruct, hfirst, _⟩ := h
  have hH : w.H = (initialWitness K β multpoly (h_rate := h_rate) ctx w.t).H := hstruct.1
  rw [hH] at hsum
  exact ⟨(initial_sumcheck_iff K β multpoly ctx target w.t).mp hsum, hfirst⟩

omit [Fact (β 0 = 1)] in
/-- Exact encoding and the product-sum claim initialize the strict folding relation. -/
theorem mem_strictRoundRelation_initialWitness
    (ctx : Context) (target : L) (p : MultilinearPoly L ℓ)
    (ost : ∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j)
    (hs : target = ∑ y : Fin ℓ → Fin 2,
      (multpoly ctx).val.eval (y : Fin ℓ → L) * p.val.eval (y : Fin ℓ → L))
    (ho : getFirstOracle K β ost = firstOracleEncoding K β p) :
    ((initialStatement ctx target, ost), initialWitness K β multpoly ctx p) ∈
      strictRoundRelation (multpoly := multpoly) K β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L) 0 := by
  have hencoding := Opening.mem_strictRoundRelation_zero_witness K β
    (h_rate := h_rate) (ϑ := ϑ) ⟨0, p.val.eval 0⟩ ost p rfl ho
  change _ ∧ WitnessStructuralInvariant K β (multpoly := multpoly) _ _ ∧ _
  refine ⟨(initial_sumcheck_iff K β multpoly ctx target p).mpr hs,
    initialWitness_structural K β multpoly ctx target p, ?_⟩
  exact hencoding.2.2

end Binius.FRIBinius.Unrolled
