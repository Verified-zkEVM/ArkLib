/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.Fri.Spec.Completeness
import Mathlib.Algebra.Field.ZMod

/-!
# FRI completeness acceptance tests

These clients check the complete reduction contract, including radius-zero output,
arbitrary initial oracle state, and the single-fold and empty-query boundaries. Numeric
examples check clipping before repetition, and kernel guards inspect the main proof bodies.
-/

open Domain OracleSpec OracleComp
open scoped NNReal

/--
info: 'Fri.Spec.reduction_completeness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.reduction_completeness

/--
info: 'Fri.Spec.perfect_completeness' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.perfect_completeness

/--
info: 'Fri.Spec.card_cleanFirstQueries_add' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.card_cleanFirstQueries_add

/--
info: 'Fri.Spec.reduction_completeness_blocks' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.reduction_completeness_blocks

/--
info: 'Fri.Spec.QueryRound.mem_queryBlock_iff_pow_eq' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Fri.Spec.QueryRound.mem_queryBlock_iff_pow_eq

section FullContract

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (d : ℕ+)
variable (hdom : 2 ^ (∑ i, (s i).val) * d.val ≤ 2 ^ n)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

example (l : ℕ) (δ : ℝ≥0) :
    (Fri.Spec.reduction (ω := ω) k s d hdom l).completeness init impl
      (Fri.Spec.inputRelation k s d hdom δ) (Fri.Spec.outputRelation k s d hdom 0)
      (Fri.Spec.completenessError s δ l) :=
  Fri.Spec.reduction_completeness s d hdom l δ init impl

example (l : ℕ) :
    (Fri.Spec.reduction (ω := ω) k s d hdom l).perfectCompleteness init impl
      (Fri.Spec.inputRelation k s d hdom 0) (Fri.Spec.outputRelation k s d hdom 0) :=
  Fri.Spec.perfect_completeness s d hdom l init impl

-- The sharper contract keeps the supplied word and witness fixed without a proximity premise.
example (l : ℕ) (f : Fri.Spec.OracleStatement s ω (0 : Fin (k + 1)) 0)
    (p₀ : Fri.Spec.Witness F s d 0) :
    (Fri.Spec.reduction (ω := ω) k s d hdom l).completeness init impl
      (Fri.Spec.honestFoldRelation s d f p₀ 0) (Fri.Spec.outputRelation k s d hdom 0)
      (1 - (((Fri.Spec.cleanFirstQueries ω (s 0).val
        (fun z ↦ f (Fri.Spec.initialQuery z))
        (fun z ↦ p₀.val.eval (ω z))).card : ℝ≥0) / 2 ^ n) ^ l) :=
  Fri.Spec.reduction_completeness_blocks s d hdom l f p₀ init impl

-- With no queries, even a noisy input has completeness error zero.
example (δ : ℝ≥0) :
    (Fri.Spec.reduction (ω := ω) k s d hdom 0).perfectCompleteness init impl
      (Fri.Spec.inputRelation k s d hdom δ) (Fri.Spec.outputRelation k s d hdom 0) :=
  Fri.Spec.perfect_completeness_zero_queries s d hdom δ init impl

end FullContract

section SingleFold

variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin 1 → ℕ+) (d : ℕ+)
variable (hdom : 2 ^ (∑ i, (s i).val) * d.val ≤ 2 ^ n)
variable {σ : Type} (init : ProbComp σ) (impl : QueryImpl []ₒ (StateT σ ProbComp))

-- Zero non-final folds still includes the final fold and its first-block error amplification.
example (l : ℕ) (δ : ℝ≥0) :
    (Fri.Spec.reduction (ω := ω) 0 s d hdom l).completeness init impl
      (Fri.Spec.inputRelation 0 s d hdom δ) (Fri.Spec.outputRelation 0 s d hdom 0)
      (Fri.Spec.completenessError s δ l) :=
  Fri.Spec.reduction_completeness s d hdom l δ init impl

-- Full-rate folding with d = 1 and a singleton final domain is allowed.
example (hs : ∑ i, (s i).val = n) (l : ℕ) :
    (Fri.Spec.reduction (ω := ω) 0 s 1
      (((Nat.mul_one _).trans (congrArg (fun m : ℕ ↦ 2 ^ m) hs)).le) l).perfectCompleteness
      init impl
      (Fri.Spec.inputRelation 0 s 1 (by
        exact ((Nat.mul_one _).trans (congrArg (fun m : ℕ ↦ 2 ^ m) hs)).le) 0)
      (Fri.Spec.outputRelation 0 s 1 (by
        exact ((Nat.mul_one _).trans (congrArg (fun m : ℕ ↦ 2 ^ m) hs)).le) 0) :=
  Fri.Spec.perfect_completeness s 1 (by
    exact ((Nat.mul_one _).trans (congrArg (fun m : ℕ ↦ 2 ^ m) hs)).le) l init impl

-- The zero polynomial passes the natural-degree guard, including at d = 1.
example :
    (0 : CompPoly.CPolynomial F).natDegree <
      Fri.Spec.foldingDegree s 1 (Fin.last 1) := by
  exact Fri.Spec.witness_natDegree_lt s 1 _ ⟨0, CompPoly.CPolynomial.zero_mem_degreeLT _⟩

end SingleFold

section Clipping

-- A binary first fold amplifies radius 1/8 to 1/4 before the two-query repetition.
example : Fri.Spec.completenessError (fun _ : Fin 1 ↦ 1) (1 / 8) 2 = 7 / 16 := by
  apply NNReal.coe_injective
  simp only [Fri.Spec.completenessError, NNReal.coe_sub_def, NNReal.coe_pow, NNReal.coe_min,
    NNReal.coe_one, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_ofNat]
  norm_num [min_def, max_def]

example : Fri.Spec.completenessError (fun _ : Fin 1 ↦ 1) (1 / 2) 3 = 1 := by
  apply NNReal.coe_injective
  simp only [Fri.Spec.completenessError, NNReal.coe_sub_def, NNReal.coe_pow, NNReal.coe_min,
    NNReal.coe_one, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_ofNat]
  norm_num [min_def, max_def]

example : Fri.Spec.completenessError (fun _ : Fin 1 ↦ 1) (3 / 4) 3 = 1 := by
  apply NNReal.coe_injective
  simp only [Fri.Spec.completenessError, NNReal.coe_sub_def, NNReal.coe_pow, NNReal.coe_min,
    NNReal.coe_one, NNReal.coe_mul, NNReal.coe_div, NNReal.coe_ofNat]
  norm_num [min_def, max_def]

-- Empty repetition has zero error even when clipping makes the success base zero.
example : Fri.Spec.completenessError (fun _ : Fin 1 ↦ 1) 2 0 = 0 := by
  simp

example {k : ℕ} (s : Fin (k + 1) → ℕ+) (l : ℕ) :
    Fri.Spec.completenessError s 0 l = 0 := by
  simp

end Clipping

-- A singleton folding block may be centered at zero; no nonzero-center premise is needed.
example {F : Type} [Field F] [DecidableEq F] (q : CompPoly.CPolynomial F) (γ : F) :
    RoundConsistency.roundConsistencyCheck γ (fun _ : Fin 1 ↦ (0, q.eval 0))
      ((CompPoly.CPolynomial.FoldingPolynomial.cpolyFold q 1 γ).eval 0) = true := by
  let points : Fin 1 ↪ F := ⟨fun _ ↦ 0, fun _ _ _ ↦ Subsingleton.elim _ _⟩
  have hp (j : Fin 1) : points j = (0 : F) := rfl
  simpa only [hp, pow_one] using
    RoundConsistency.roundConsistencyCheck_eq_true_of_pow_eq points q 0 γ
      (by intro j; rfl)

namespace Fri.Spec.CompletenessTest

/-- Primality of the fixture's field modulus. -/
private instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- The fixture field has characteristic different from two. -/
private instance : NonBinaryField (ZMod 17) where
  toField := inferInstance
  char_neq_2 := by decide

/-- A generator of the four-element subgroup of the fixture field. -/
private def root : (ZMod 17)ˣ := ⟨4, 13, by decide, by decide⟩

/-- The four-point coset `3 * {1, 4, 16, 13}`, distinct from its underlying subgroup. -/
private def domain : SmoothCosetFftDomain 2 (ZMod 17) where
  subgroupDomain :=
    { toFun := fun i ↦ root ^ i.toAdd.val
      map_one' := by decide
      map_mul' := by decide }
  subgroupDomain_inj := by decide
  cosetGenerator := ⟨3, 6, by decide, by decide⟩

/-- One binary folding stage. -/
private def schedule : Fin 1 → ℕ+ := fun _ ↦ 1

-- The actual query enumeration uses the complete two-point fiber in the shifted coset.
example :
    ((QueryRound.queryBlock (ω := domain) schedule (by decide) 0
      (initialQuery 0)).map Subtype.val).toFinset = {3, 14} := by
  decide +kernel

example :
    ((QueryRound.queryBlock (ω := domain) (fun _ : Fin 1 ↦ 2) (by decide) 0
      (initialQuery 0)).map Subtype.val).toFinset = {3, 12, 14, 5} := by
  decide +kernel

-- Two errors in one folding block leave one of the two blocks clean.
example :
    (firstErrorBlocks domain 1
      (fun z ↦ if z = 0 ∨ z = 2 then 1 else 0) (fun _ ↦ 0)).card = 1 := by
  decide

-- The same number of errors, in distinct folding blocks, touches every block.
example :
    (firstErrorBlocks domain 1
      (fun z ↦ if z = 0 ∨ z = 1 then 1 else 0) (fun _ ↦ 0)).card = 2 := by
  decide

/-- The zero polynomial with the fixture's initial degree bound. -/
private def zeroWitness : Witness (ZMod 17) schedule 1 0 :=
  ⟨0, CompPoly.CPolynomial.zero_mem_degreeLT _⟩

/-- The honest history of the zero polynomial with folding challenge zero. -/
private def zeroHistory : ∀ j, FinalOracleStatement schedule domain j :=
  honestHistory schedule 1
    (fun y : (domain.subdomain 0).toFinset ↦ zeroWitness.val.eval y.val)
    zeroWitness (fun _ ↦ 0)

example :
    simulateQ (OracleInterface.simOracle0 (FinalOracleStatement schedule domain) zeroHistory)
      (QueryRound.checkRound schedule (by decide) (finalPolynomial schedule zeroHistory)
        0 0 (initialQuery 0)) = true :=
  QueryRound.eval_checkRound_honestHistory schedule 1 (by decide) zeroWitness (fun _ ↦ 0)
    0 (initialQuery 0)

-- Repeated query positions remain valid, including with zero folding challenge.
example :
    (simulateQ (OracleInterface.simOracle0 (FinalOracleStatement schedule domain) zeroHistory)
      (QueryRound.verifyQueries schedule (by decide) 2 (fun _ ↦ 0)
        (fun _ ↦ initialQuery 0)).run).run = some (fun _ ↦ 0) :=
  QueryRound.eval_verifyQueries_honestHistory schedule 1 (by decide) zeroWitness
    (fun _ ↦ 0) (fun _ ↦ initialQuery 0)

end Fri.Spec.CompletenessTest
