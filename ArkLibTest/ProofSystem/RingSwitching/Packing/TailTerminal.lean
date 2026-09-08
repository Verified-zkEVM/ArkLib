/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.Tail.Terminal
import ArkLibTest.ProofSystem.RingSwitching.Packing.PackedCommitment

/-!
# The actual zero-variable terminal over a non-domain and nonfunctional commitment

The packed ring is a product of two ZMod5 fields. The oracle contains both the zero and one
polynomials, so its relation is not functional. The actual terminal still opens the original
polynomial, forwards its value through zero and nonzero multipliers, and rejects a false target.
-/

noncomputable section

namespace RingSwitching.Packing.Tests.TailTerminal

open MvPolynomial OracleSpec OracleComp ProtocolSpec
open NonfunctionalCommitment

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

abbrev R := Fin 2 → ZMod 5
abbrev pc := finiteList R 0

def p : R⦃≤ 1⦄[X Fin 0] := constant 0 1
open scoped Classical in
def ost : ∀ j, pc.OStmt j := fun _ => ({0, p} : Finset R⦃≤ 1⦄[X Fin 0])
def multiplier (a : R) : Unit → R⦃≤ 1⦄[X Fin 0] := fun _ => constant 0 a
def stmt (a : R) : Tail.Statement Unit R (Fin.last 0) := ⟨(), Fin.elim0, a⟩

/-- The same finite-list oracle contains two different packed polynomials. -/
theorem nonfunctional : ¬ pc.Functional := finiteList_not_functional R 0

/-- The retained opening is the nonzero polynomial in this very oracle. -/
theorem committed : pc.commitsTo ost p := by simp [pc, finiteList, ost]

/-- A non-domain product algebra is a live parameter instance. -/
theorem zero_divisors : (fun i : Fin 2 => if i = 0 then (1 : ZMod 5) else 0) *
    (fun i : Fin 2 => if i = 0 then (0 : ZMod 5) else 1) = 0 := by
  ext i
  fin_cases i <;> decide

/-- Every multiplier gives the actual terminal source relation for the same constant one. -/
theorem source_related (a : R) :
    ((stmt a, ost), p) ∈ Tail.rel (multiplier a) pc (Fin.last 0) := by
  rw [Tail.rel_last]
  exact ⟨by simp [stmt, multiplier, p, constant], committed⟩

/-- The actual prover sends one, independently of the public multiplier. -/
theorem prover_sends_one (a : R) :
    (Tail.Terminal.prover pc).run (stmt a, ost) p =
      pure (Tail.Terminal.transcript (1 : R), ((Fin.elim0, 1), ost), p) := by
  rw [Tail.Terminal.prover_run]
  simp [p, constant, Tail.Terminal.nextStatement, stmt]

/-- The actual verifier forwards one with the identical list oracle at every multiplier. -/
theorem verifier_forwards_one (a : R) :
    (Tail.Terminal.verifier (multiplier a) pc).toVerifier.verify
      (stmt a, ost) (Tail.Terminal.transcript (1 : R)) =
      pure ((Fin.elim0, 1), ost) := by
  rw [Tail.Terminal.verifier_verify]
  have hc : Tail.Terminal.check (multiplier a) (stmt a) 1 := by
    simp [Tail.Terminal.check, multiplier, constant, stmt]
  exact if_pos hc

/-- Zero multiplication cannot replace the forwarded opening value by the product. -/
theorem zero_multiplier_forwards_one :
    (Tail.Terminal.verifier (multiplier 0) pc).toVerifier.verify
      (stmt 0, ost) (Tail.Terminal.transcript (1 : R)) =
      pure ((Fin.elim0, 1), ost) := verifier_forwards_one 0

/-- The nonzero multiplier is a zero divisor, so correctness cannot depend on cancellation. -/
def zeroDivisor : R := fun i => if i = 0 then 0 else 1

/-- The chosen multiplier really is nonzero. -/
theorem zeroDivisor_nonzero : zeroDivisor ≠ 0 := by
  intro h
  exact (by decide : (1 : ZMod 5) ≠ 0) (congrFun h 1)

/-- The same production leaf forwards one with a nonzero nonunit multiplier. -/
theorem nonzero_multiplier_forwards_one :
    (Tail.Terminal.verifier (multiplier zeroDivisor) pc).toVerifier.verify
      (stmt zeroDivisor, ost) (Tail.Terminal.transcript (1 : R)) =
      pure ((Fin.elim0, 1), ost) := verifier_forwards_one zeroDivisor

/-- The claimed output is the actual opening relation of the same original packed polynomial. -/
theorem output_related : (((Fin.elim0, (1 : R)), ost), p) ∈ pc.evalRel :=
  ⟨by simp [p, constant], committed⟩

/-- Zero-challenge knowledge applies to this nonfunctional commitment and product ring. -/
theorem actual_worstCase (a : R) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    Verifier.rbrKnowledgeSoundnessWorstCaseWith init impl
      (Tail.rel (multiplier a) pc (Fin.last 0)) pc.evalRel
      (Tail.Terminal.verifier (multiplier a) pc).toVerifier
      Tail.Terminal.WitMid (Tail.Terminal.extractor (Context := Unit) pc)
      (Tail.Terminal.knowledgeStateFunction (multiplier a) pc init impl) (fun _ => 0) :=
  Tail.Terminal.rbrKnowledgeSoundnessWorstCaseWith (multiplier a) pc init impl

/-- Actual perfect completeness covers arbitrary shared initial oracle-state distributions. -/
theorem actual_complete (a : R) {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (Tail.Terminal.reduction (multiplier a) pc).perfectCompleteness init impl
      (Tail.rel (multiplier a) pc (Fin.last 0)) pc.evalRel :=
  Tail.Terminal.perfectCompleteness (multiplier a) pc init impl

/-- Changing the zero-product target to one is rejected through the actual reduction run. -/
theorem false_target_rejected :
    ((Tail.Terminal.reduction (multiplier 0) pc).toReduction.run (stmt 1, ost) p).run =
      pure none := by
  rw [Tail.Terminal.reduction_run]
  have hc : ¬ Tail.Terminal.check (multiplier 0) (stmt 1)
      (aeval (stmt 1).challenges p.val) := by
    simp [Tail.Terminal.check, multiplier, constant, stmt]
  exact congrArg pure (if_neg hc)

end RingSwitching.Packing.Tests.TailTerminal

end
