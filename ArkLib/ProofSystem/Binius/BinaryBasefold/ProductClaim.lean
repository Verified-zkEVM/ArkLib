/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao, Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Commitment
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Relations.Initial
-- The strict initial relation exposes dependent fold-index proof terms.
import all ArkLib.ProofSystem.Binius.BinaryBasefold.Relations
-- The initial-fold identity unfolds the dependent fold implementation.
import all ArkLib.ProofSystem.Binius.BinaryBasefold.Prelude.Folding

/-!
# Product claims entering the Binary Basefold loop

The sum-check-and-fold loop starts from a product claim `s = ∑_{y ∈ {0,1}^ℓ} A(y) · t(y)`, for a
public multilinear multiplier `A` determined by the context and a committed multilinear `t`.
This file gives the canonical round-`0` statement and witness of such a claim and the two facts
that every front end needs:

* `sum_eq_and_firstOracleWitnessConsistent_of_mem_roundRelation_zero`: a relaxed round-`0` witness
  certifies the product claim for its own polynomial, together with unique-radius compatibility
  of that polynomial with the committed first oracle. Proximity is not upgraded to equality.
* `mem_strictRoundRelation_zero_initialWitness`: the product claim and an exact first encoding
  give the strict round-`0` relation used for perfect completeness.

An evaluation claim `s = t(r)` is the product claim at `A = eq̃(r, ·)` (`Opening`); the unrolled
FRI-Binius protocol uses the ring-switching multiplier.
-/

@[expose] public section

open OracleSpec OracleComp ProtocolSpec AdditiveNTT MvPolynomial Sumcheck.Structured

namespace Binius.BinaryBasefold

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (K : Type) [Field K] [Fintype K] [Fact (Fintype.card K = 2)] [Algebra K L]
local instance [Finite K] : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩
variable (β : Fin r → L) [Fact (LinearIndependent K β)]
variable {ℓ R : ℕ} [NeZero R] {h_rate : ℓ + R < r}
variable {Context : Type} (multpoly : Context → MultilinearPoly L ℓ)

/-- The round-`0` statement of a product claim: its target and context, with no challenges. -/
def initialStatement (ctx : Context) (target : L) : Statement (L := L) (ℓ := ℓ) Context 0 :=
  ⟨target, Fin.elim0, ctx⟩

/-- The canonical round-`0` witness of `t`: the residual polynomial is `A(ctx) · t` and the
folded word is the encoding of `t`. -/
noncomputable def initialWitness (ctx : Context) (t : MultilinearPoly L ℓ) :
    Witness K β (h_ℓ_add_R_rate := h_rate) (ℓ := ℓ) 0 where
  t := t
  H := fixPrefix ℓ 0 (computeInitialSumcheckPoly ℓ t (multpoly ctx)) Fin.elim0
  f := getMidCodewords K β (h_ℓ_add_R_rate := h_rate) t Fin.elim0

/-- The initial residual polynomial is the multiplier times the committed polynomial. -/
theorem initialWitness_H_val (ctx : Context) (t : MultilinearPoly L ℓ) :
    (initialWitness K β multpoly (h_rate := h_rate) ctx t).H.val = (multpoly ctx).val * t.val := by
  simp [initialWitness, fixPrefix, MvPolynomial.fixFirstVariablesOfMQP_zero]

/-- The canonical witness satisfies the structural invariant of the loop, independently of the
committed oracle. -/
theorem initialWitness_structural (ctx : Context) (target : L) (t : MultilinearPoly L ℓ) :
    WitnessStructuralInvariant K β (multpoly := multpoly) (h_ℓ_add_R_rate := h_rate)
      (initialStatement ctx target) (initialWitness K β multpoly ctx t) :=
  ⟨rfl, rfl⟩

/-- Boolean sum-check consistency of the canonical witness is the product claim. -/
theorem sumcheckConsistencyProp_initialWitness_iff (ctx : Context) (target : L)
    (t : MultilinearPoly L ℓ) :
    sumcheckConsistencyProp (boolDomain L ℓ) target
      (initialWitness K β multpoly (h_rate := h_rate) ctx t).H ↔
      target = ∑ y : Fin ℓ → Fin 2,
        (multpoly ctx).val.eval (y : Fin ℓ → L) * t.val.eval (y : Fin ℓ → L) := by
  unfold sumcheckConsistencyProp
  rw [sum_cube_boolDomain]
  simp only [initialWitness_H_val, eval_mul]

variable [Fact (β 0 = 1)] [NeZero ℓ] {ϑ : ℕ} [NeZero ϑ] [Fact (ϑ ∣ ℓ)]

/-- A relaxed round-`0` witness certifies the product claim for its own polynomial and the
unique-radius compatibility of that polynomial with the committed first oracle. -/
theorem sum_eq_and_firstOracleWitnessConsistent_of_mem_roundRelation_zero
    (ctx : Context) (target : L)
    (ost : ∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j)
    (w : Witness K β (h_ℓ_add_R_rate := h_rate) (ℓ := ℓ) 0)
    (h : ((initialStatement ctx target, ost), w) ∈
      roundRelation (multpoly := multpoly) K β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L) 0) :
    target = ∑ y : Fin ℓ → Fin 2,
        (multpoly ctx).val.eval (y : Fin ℓ → L) * w.t.val.eval (y : Fin ℓ → L) ∧
      FirstOracleWitnessConsistent K β w.t (getFirstOracle K β ost) := by
  rw [mem_roundRelation_zero_iff] at h
  obtain ⟨hsum, hstruct, hfirst, _⟩ := h
  have hH : w.H = (initialWitness K β multpoly (h_rate := h_rate) ctx w.t).H := hstruct.1
  rw [hH] at hsum
  exact ⟨(sumcheckConsistencyProp_initialWitness_iff K β multpoly ctx target w.t).mp hsum, hfirst⟩

omit [Fact (β 0 = 1)] in
-- The strict initial fold identity compares definitionally equal dependent domains.
set_option backward.isDefEq.respectTransparency false in
/-- The product claim and an exact first encoding give the strict round-`0` relation. -/
theorem mem_strictRoundRelation_zero_initialWitness
    (ctx : Context) (target : L) (t : MultilinearPoly L ℓ)
    (ost : ∀ j, OracleStatement K β (ϑ := ϑ) (h_ℓ_add_R_rate := h_rate) 0 j)
    (hs : target = ∑ y : Fin ℓ → Fin 2,
      (multpoly ctx).val.eval (y : Fin ℓ → L) * t.val.eval (y : Fin ℓ → L))
    (ho : getFirstOracle K β ost = firstOracleEncoding K β t) :
    ((initialStatement ctx target, ost), initialWitness K β multpoly ctx t) ∈
      strictRoundRelation (multpoly := multpoly) K β (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_rate) (𝓑 := boolEmbedding L) 0 := by
  classical
  dsimp only [strictRoundRelation, StrictRoundRelated, StrictOracleWitnessConsistent]
  refine ⟨(sumcheckConsistencyProp_initialWitness_iff K β multpoly ctx target t).mpr hs,
    initialWitness_structural K β multpoly ctx target t, ?_⟩
  change StrictOracleFoldingConsistent K β t (0 : Fin (ℓ + 1)) Fin.elim0 ost
  dsimp only [StrictOracleFoldingConsistent]
  rintro ⟨j, hj⟩
  have hj0 : j = 0 := Nat.lt_one_iff.mp
    (lt_of_lt_of_eq hj (toOutCodewordsCount_zero ℓ ϑ))
  subst j
  funext y
  rw [iteratedFold_congr_steps_index K β (h_ℓ_add_R_rate := h_rate) (steps' := 0)
    (h_destIdx := by simp only [Nat.zero_mod, Nat.zero_mul, Fin.coe_ofNat_eq_mod,
      Nat.zero_add])
    (h_destIdx_le := by simp only [Nat.zero_mul, Nat.zero_le])
    (h_steps_eq_steps' := by simp only [Nat.zero_mul])]
  rw [iteratedFold_zero_steps K β (h_ℓ_add_R_rate := h_rate) (i := 0)
    (h_destIdx := by simp only [Nat.zero_mod, Nat.zero_mul, Fin.coe_ofNat_eq_mod])]
  have hy := congrFun ho (cast (by simp only [Fin.mk_zero', Nat.zero_mul]) y)
  simpa [getFirstOracle, firstOracleEncoding] using hy

end Binius.BinaryBasefold
