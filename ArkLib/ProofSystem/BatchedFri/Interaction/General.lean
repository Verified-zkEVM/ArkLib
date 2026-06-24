/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Data.Fin.Basic
import ArkLib.ProofSystem.Fri.Interaction.General
import CompPoly.Univariate.ToPoly.Degree

open Interaction.TwoParty

/-!
# Batched FRI Interaction

This module packages the random linear-combination batching round as an
`Interaction.Oracle.Reduction`, then composes it with the FRI reduction.

The batching round is a genuine verifier-challenge round: after receiving
coefficients `cs : Fin m → F`, the prover exposes a single FRI input codeword

`w₀ + ∑ j, cs j • wⱼ₊₁`

and the verifier simulates queries to that codeword by routing them back to the
original batched input oracle family.
-/

open scoped BigOperators
open Interaction CompPoly CPoly OracleComp OracleSpec

namespace BatchedFri

namespace OracleLayer

section

variable {F : Type} [BEq F] [LawfulBEq F] [DecidableEq F] [NonBinaryField F] [Finite F]
variable (D : Subgroup Fˣ) {n : ℕ}
variable [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D]
variable (x : Fˣ)
variable {k : ℕ} (s : Fin (k + 1) → ℕ+) (d : ℕ)
variable (m l : ℕ)

/-- The batching round samples one coefficient for every non-base codeword. -/
abbrev Coefficients : Type :=
  Fin m → F

/-- Batched FRI starts with `m + 1` codewords on the initial FRI domain. -/
abbrev InputOracleFamily :
    Fin (m + 1) → Type :=
  fun _ => Fri.OracleLayer.Codeword (F := F) s n 0

instance instOracleInterfaceInputOracleFamily :
    ∀ i, OracleInterface (InputOracleFamily (F := F) (n := n) (s := s) m i) :=
  fun _ => inferInstance

/-- Batched FRI starts with one honest polynomial witness for each input codeword. -/
abbrev Witness :
    Type :=
  Fin (m + 1) → Fri.OracleLayer.HonestPoly (F := F) s d 0

/-- The one-round public-coin batching context. -/
def batchingSpec : Interaction.Oracle.Spec :=
  .public (Coefficients (F := F) m) fun _ => .done

/-- The verifier sends the batching coefficients. -/
def batchingRoles :
    Interaction.Oracle.Spec.RoleDeco (batchingSpec (F := F) m) :=
  ⟨.receiver, fun _ => ⟨⟩⟩

/-- The batching round sends no oracle message of its own. -/
def batchingOD :
    Interaction.Oracle.Spec.OracleDeco (batchingSpec (F := F) m) :=
  fun _ => ⟨⟩

/-- Linear-combine the input codewords into the single FRI input codeword. -/
def batchCodeword
    (cs : Coefficients (F := F) m)
    (codewords : OracleStatement (InputOracleFamily (F := F) (n := n) (s := s) m)) :
    Fri.OracleLayer.Codeword (F := F) s n 0 :=
  fun idx => codewords 0 idx + ∑ j : Fin m, cs j * codewords j.succ idx

omit [DecidableEq F] [Finite F] in
private theorem natDegree_batchWitness_le
    (cs : Coefficients (F := F) m)
    (witness : Witness (F := F) (s := s) (d := d) m) :
    ((witness 0).1 + ∑ j : Fin m, cs j • (witness j.succ).1).natDegree ≤
      Fri.OracleLayer.residualDegreeBound s d 0 := by
  rw [CPolynomial.natDegree_toPoly]
  have h_toPoly :
      ((witness 0).1 + ∑ j : Fin m, cs j • (witness j.succ).1).toPoly =
        (witness 0).1.toPoly +
          ∑ j : Fin m, cs j • (witness j.succ).1.toPoly := by
    rw [CPolynomial.toPoly_add]
    rw [show (∑ j : Fin m, cs j • (witness j.succ).1).toPoly =
        ∑ j : Fin m, (cs j • (witness j.succ).1).toPoly from by
          classical
          refine Finset.induction_on (s := (Finset.univ : Finset (Fin m))) ?_ ?_
          · simp [CPolynomial.toPoly_zero]
          · intro j js hjs ih
            rw [Finset.sum_insert hjs, Finset.sum_insert hjs, CPolynomial.toPoly_add, ih]]
    simp [CPolynomial.toPoly_smul]
  rw [h_toPoly]
  refine (Polynomial.natDegree_add_le _ _).trans ?_
  refine max_le ?_ ?_
  · simpa [← CPolynomial.natDegree_toPoly (p := (witness 0).1)] using
      (witness 0).2
  · exact Polynomial.natDegree_sum_le_of_forall_le
      (s := Finset.univ)
      (f := fun j : Fin m => cs j • (witness j.succ).1.toPoly)
      (n := Fri.OracleLayer.residualDegreeBound s d 0)
      (fun j _ =>
        (Polynomial.natDegree_smul_le (cs j) (witness j.succ).1.toPoly).trans <|
          by
            simpa [← CPolynomial.natDegree_toPoly (p := (witness j.succ).1)] using
              (witness j.succ).2)

/-- Linear-combine the input polynomial witnesses into the single FRI witness. -/
noncomputable def batchWitness
    (cs : Coefficients (F := F) m)
    (witness : Witness (F := F) (s := s) (d := d) m) :
    Fri.OracleLayer.HonestPoly (F := F) s d 0 :=
  ⟨(witness 0).1 + ∑ j : Fin m, cs j • (witness j.succ).1,
    natDegree_batchWitness_le (F := F) (s := s) (d := d) (m := m) cs witness⟩

/-- Simulate queries to the batched FRI input codeword by querying the original
batched input family at the same domain index. -/
def simulateBatchCodeword
    (cs : Coefficients (F := F) m) :
    QueryImpl [Fri.OracleLayer.InputOracleFamily (F := F) (n := n) D x s]ₒ
      (OracleComp
        ([InputOracleFamily (F := F) (n := n) (s := s) m]ₒ +
          Interaction.Oracle.Spec.toOracleSpec
            (batchingSpec (F := F) m)
            (batchingOD (F := F) m)
            ⟨cs, ⟨⟩⟩))
  | ⟨(), idx⟩ => do
      let base : F ← liftM <|
        ([InputOracleFamily (F := F) (n := n) (s := s) m]ₒ).query ⟨0, idx⟩
      let rest ← Fin.traverseM fun j : Fin m => do
        let value : F ← liftM <|
          ([InputOracleFamily (F := F) (n := n) (s := s) m]ₒ).query ⟨j.succ, idx⟩
        pure (cs j * value)
      pure (base + ∑ j : Fin m, rest j)

/-- Random linear-combination batching round. Its output oracle family is
exactly the single input oracle family consumed by FRI. -/
noncomputable def batchingReduction {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    (sampleCoefficients : OracleComp oSpec (Coefficients (F := F) m)) :
    Interaction.Oracle.Reduction (ι := ι) oSpec PUnit
      (fun _ => batchingSpec (F := F) m)
      (fun _ => batchingRoles (F := F) m)
      (fun _ => batchingOD (F := F) m)
      (fun _ => PUnit)
      (ιₛᵢ := fun _ => Fin (m + 1))
      (fun _ => InputOracleFamily (F := F) (n := n) (s := s) m)
      (fun _ => Witness (F := F) (s := s) (d := d) m)
      (fun _ _ => PUnit)
      (ιₛₒ := fun _ _ => Unit)
      (fun _ _ => Fri.OracleLayer.InputOracleFamily (F := F) (n := n) D x s)
      (fun _ _ => Fri.OracleLayer.HonestPoly (F := F) s d 0) where
  prover shared sWithOracles witness := do
    let proverStep :
        Interaction.Spec.StrategyOver (pairedSyntax (OracleComp oSpec)) Interaction.TwoParty.Participant.focal
          (batchingSpec (F := F) m).toInteractionSpec
          ((batchingSpec (F := F) m).toSpecRoles (batchingRoles (F := F) m))
          (fun _ =>
            HonestProverOutput
              (StatementWithOracles
                (fun _ => PUnit)
                (fun _ => Fri.OracleLayer.InputOracleFamily (F := F) (n := n) D x s)
                shared)
              (Fri.OracleLayer.HonestPoly (F := F) s d 0)) :=
      fun cs => do
        let codeword :=
          batchCodeword (F := F) (n := n) (s := s) (m := m) cs sWithOracles.oracleStmt
        let witnessOut :=
          batchWitness (F := F) (s := s) (d := d) (m := m) cs witness
        pure
          (⟨⟨PUnit.unit, fun _ => codeword⟩, witnessOut⟩ :
            HonestProverOutput
              (StatementWithOracles
                (fun _ => PUnit)
                (fun _ => Fri.OracleLayer.InputOracleFamily (F := F) (n := n) D x s)
                shared)
              (Fri.OracleLayer.HonestPoly (F := F) s d 0))
    pure <|
      Interaction.TwoParty.Focal.toConstantMonads
        (batchingSpec (F := F) m).toInteractionSpec
        ((batchingSpec (F := F) m).toSpecRoles (batchingRoles (F := F) m))
        proverStep
  verifier := {
    toFun := fun _ _ => do
      let cs ← sampleCoefficients
      pure ⟨cs, ⟨⟩⟩
    simulate := fun _ pt =>
      match pt with
      | ⟨cs, ⟨⟩⟩ =>
          simulateBatchCodeword (F := F) (D := D) (n := n) (x := x) (s := s) (m := m) cs
  }

/-- Public interaction context for Batched FRI: batching followed by FRI. -/
abbrev context : Interaction.Oracle.Spec :=
  (batchingSpec (F := F) m).append
    (fun _ => Fri.OracleLayer.context (F := F) (D := D) (n := n) (x := x) (s := s)
      (d := d) l)

/-- Role decoration for Batched FRI. -/
abbrev roles :
    Interaction.Oracle.Spec.RoleDeco
      (context (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) m l) :=
  Interaction.Oracle.Spec.RoleDeco.append
    (batchingSpec (F := F) m)
    (fun _ => Fri.OracleLayer.context (F := F) (D := D) (n := n) (x := x) (s := s)
      (d := d) l)
    (batchingRoles (F := F) m)
    (fun _ => Fri.OracleLayer.roles (F := F) (D := D) (n := n) (x := x) (s := s)
      (d := d) l)

/-- Oracle-message decoration for Batched FRI. -/
abbrev oracleDeco :
    Interaction.Oracle.Spec.OracleDeco
      (context (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) m l) :=
  Interaction.Oracle.Spec.OracleDeco.append
    (batchingSpec (F := F) m)
    (fun _ => Fri.OracleLayer.context (F := F) (D := D) (n := n) (x := x) (s := s)
      (d := d) l)
    (batchingOD (F := F) m)
    (fun _ => Fri.OracleLayer.oracleDeco (F := F) (D := D) (n := n) (x := x) (s := s)
      (d := d) l)

/-- Full Batched FRI reduction, built by composing the random
linear-combination round with FRI. -/
noncomputable def reduction {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    (h_domain : Fri.OracleLayer.totalShift s ≤ n)
    (sampleCoefficients : OracleComp oSpec (Coefficients (F := F) m))
    (sampleFoldChallenge : (i : Fin k) → OracleComp oSpec F)
    (sampleFinalChallenge : OracleComp oSpec F)
    (sampleQueries : OracleComp oSpec (Fri.OracleLayer.QueryBatch (n := n) s l)) :
    Interaction.Oracle.Reduction (ι := ι) oSpec PUnit
      (fun _ => context (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) m l)
      (fun _ => roles (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) m l)
      (fun _ => oracleDeco (F := F) (D := D) (n := n) (x := x) (s := s) (d := d) m l)
      (fun _ => PUnit)
      (ιₛᵢ := fun _ => Fin (m + 1))
      (fun _ => InputOracleFamily (F := F) (n := n) (s := s) m)
      (fun _ => Witness (F := F) (s := s) (d := d) m)
      (fun _ _ => Fri.OracleLayer.QueryResult)
      (ιₛₒ := fun _ _ => PEmpty)
      (fun _ _ => Fri.OracleLayer.EmptyOracleFamily)
      (fun _ _ => PUnit) := by
  exact Interaction.Oracle.Reduction.comp
    (batchingReduction (F := F) (D := D) (n := n) (x := x) (s := s) (d := d)
      (m := m) sampleCoefficients)
    (fun _ _ =>
      Fri.OracleLayer.reduction (F := F) (D := D) (n := n) (x := x) (s := s)
        (d := d) (l := l)
        h_domain sampleFoldChallenge sampleFinalChallenge sampleQueries)

end

end OracleLayer

end BatchedFri

