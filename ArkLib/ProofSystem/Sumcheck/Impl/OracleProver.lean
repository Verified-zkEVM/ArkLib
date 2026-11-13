/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Impl.Projection
public import ArkLib.ProofSystem.Sumcheck.Spec.General

/-!
# Executable honest sum-check oracle prover

Finite coefficient and domain enumeration realize the honest prover on the specification's
message types. The refinement equations identify this implementation with the specified prover.
-/

@[expose] public section

namespace Sumcheck.Impl.Computable

open Polynomial MvPolynomial OracleSpec OracleComp ProtocolSpec Finset

variable (R : Type) [CommSemiring R] (deg : ℕ) {ι : Type} (oSpec : OracleSpec ι)

variable [BEq R] [LawfulBEq R] [Nontrivial R] (n : ℕ) {m : ℕ} (D : Fin m ↪ R)

/-- Construct a mathematical round message by computational finite-domain projection. -/
def projectedStatementMessage (i : Fin n) (challenges : Fin i.castSucc → R)
    (poly : Spec.OracleStatement R n deg ()) : R⦃≤ deg⦄[X] :=
  Representation.toMessage R deg
    (projectedMessage D i challenges (fromOracleStatement poly)
      (fromOracleStatement_degreeOf_le poly))

/-- Computational projection produces the specification's honest round message. -/
theorem projectedStatementMessage_eq (i : Fin n) (challenges : Fin i.castSucc → R)
    (poly : Spec.OracleStatement R n deg ()) :
    projectedStatementMessage R deg n D i challenges poly =
      Spec.SingleRound.projectedRoundPolynomial R n deg D i challenges poly := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
    exact projectedRoundMessage_toMessage D i challenges (fromOracleStatement poly)
      (fromOracleStatement_degreeOf_le poly) poly (fromOracleStatement_interpretation poly)

/-- Context projection uses the finite-support implementation of the honest message. -/
def proverContextLens (i : Fin n) : Context.Lens
    (Spec.StatementRound R n i.castSucc × (∀ j, Spec.OracleStatement R n deg j))
    (Spec.StatementRound R n i.succ × (∀ j, Spec.OracleStatement R n deg j))
    (Spec.SingleRound.Simple.StmtIn R × (∀ j, Spec.SingleRound.Simple.OStmtIn R deg j))
    (Spec.SingleRound.Simple.StmtOut R × (∀ j, Spec.SingleRound.Simple.OStmtOut R deg j))
    Unit Unit Unit Unit where
  wit := Witness.Lens.trivial
  stmt := {
    toFunA := fun ⟨⟨target, challenges⟩, oStmt⟩ =>
      ⟨target, fun _ => projectedStatementMessage R deg n D i challenges (oStmt ())⟩
    toFunB := fun ⟨⟨_, challenges⟩, oStmt⟩ ⟨⟨target, chal⟩, _⟩ =>
      ⟨⟨target, Fin.snoc challenges chal⟩, oStmt⟩ }

/-- The computational context projection agrees with the specified projection. -/
theorem proverContextLens_eq (i : Fin n) :
    proverContextLens R deg n D i = (Spec.SingleRound.oCtxLens R n deg D i).toContext := by
  simp only [proverContextLens, Spec.SingleRound.oCtxLens, Spec.SingleRound.oStmtLens,
    OracleContext.Lens.toContext]
  congr 2
  funext input
  simp only [projectedStatementMessage_eq]

/-- Honest round prover with executable message projection and output evaluation. -/
def oracleProver (i : Fin n) : OracleProver oSpec
    (Spec.StatementRound R n i.castSucc) (Spec.OracleStatement R n deg) Unit
    (Spec.StatementRound R n i.succ) (Spec.OracleStatement R n deg) Unit
    (Spec.SingleRound.pSpec R deg) :=
  Prover.liftContext (proverContextLens R deg n D i) (Spec.SingleRound.Simple.prover R deg oSpec)

/-- Context lifting preserves the honest round prover's pure output. -/
instance (i : Fin n) : (oracleProver R deg oSpec n D i).OutputIsPure := by
  unfold oracleProver
  infer_instance

variable [DecidableEq R] [SampleableType R]

/-- The executable honest round prover refines the existing oracle reduction exactly. -/
theorem oracleProver_eq (i : Fin n) :
    oracleProver R deg oSpec n D i =
      (Spec.SingleRound.oracleReduction R n deg D oSpec i).prover := by
  rw [oracleProver, proverContextLens_eq]
  rfl

/-- Execute every honest sumcheck round using finite coefficient and domain enumeration. -/
def generalOracleProver : OracleProver oSpec
    (Spec.StatementRound R n 0) (Spec.OracleStatement R n deg) Unit
    (Spec.StatementRound R n (.last n)) (Spec.OracleStatement R n deg) Unit
    (Spec.pSpec R deg n) :=
  Prover.seqCompose
    (fun i => Spec.StatementRound R n i × (∀ j, Spec.OracleStatement R n deg j))
    (fun _ => Unit) (oracleProver R deg oSpec n D)

/-- The executable full prover is exactly the prover in the specified sumcheck reduction. -/
theorem generalOracleProver_eq :
    generalOracleProver R deg oSpec n D = (Spec.oracleReduction R deg D n oSpec).prover := by
  unfold generalOracleProver
  have h : oracleProver R deg oSpec n D =
      fun i => (Spec.SingleRound.oracleReduction R n deg D oSpec i).prover :=
    funext (oracleProver_eq R deg oSpec n D)
  rw [h]

omit [DecidableEq R] [SampleableType R] in
/-- Every supported honest full-prover output retains exactly the input polynomial oracle. -/
theorem generalOracleProver_run_retains
    (stmt : Spec.StatementRound R n 0 × (∀ i, Spec.OracleStatement R n deg i))
    (wit : Unit)
    (out : (Spec.pSpec R deg n).FullTranscript ×
      (Spec.StatementRound R n (.last n) × (∀ i, Spec.OracleStatement R n deg i)) × Unit)
    (h : out ∈ support ((generalOracleProver R deg oSpec n D).run stmt wit)) :
    out.2.1.2 = stmt.2 := by
  apply Prover.seqCompose_run_retains (Spec.StatementRound R n) (fun _ => Unit)
    (oracleProver R deg oSpec n D) (fun _ => inferInstance) ?_ stmt wit out h
  intro i s w z hz
  rw [oracleProver, Prover.liftContext_run] at hz
  simp only [bind_pure_comp, support_map, Set.mem_image] at hz
  obtain ⟨inner, _, rfl⟩ := hz
  rfl

end Sumcheck.Impl.Computable
