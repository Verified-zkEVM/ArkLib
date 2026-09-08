/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.RingSwitching.Packing.Opening
import ArkLib.ProofSystem.RingSwitching.Packing.ExactCommitment

/-!
# Effectful downstream data at an explicit ambient oracle

This relation-preserving fixture queries and changes a Boolean oracle state. Its generic prefix
uses that same nonempty ambient oracle. It is not an instance of the concrete packing prefixes,
which currently use the empty ambient oracle, and it does not close the opening relation.
-/

noncomputable section

namespace RingSwitching.Packing.Tests.OpeningEffects

open OracleSpec OracleComp ProtocolSpec MvPolynomial

abbrev oracle : OracleSpec Unit := fun _ => Bool
abbrev pc := ExactPackedCommitment.polynomialOracle (ZMod 5) 0
abbrev Stmt := (Fin 0 → ZMod 5) × ZMod 5
abbrev F := ZMod 5
abbrev Poly := F⦃≤ 1⦄[X Fin 0]
local instance : ∀ i, OracleInterface (pc.OStmt i) := pc.Oᵢ

/-- The downstream verifier actually performs an ambient query before preserving the claim. -/
def verifier : OracleVerifier oracle Stmt pc.OStmt Stmt pc.OStmt !p[] where
  verify stmt _ := do
    let _ : Bool ← query (spec := oracle) ()
    return stmt
  outputOracle := .inl {
    embed := ⟨fun j => Sum.inl j, fun _ _ h => by cases h; rfl⟩
    hEq := fun _ => rfl
    outputInterface_heq := by intro i; rfl }

/-- This downstream datum retains pc.evalRel and deliberately has an effectful verifier. -/
def opening : PackedOpening pc.toPackedCommitment (ZMod 5) oracle !p[] where
  StmtOut := Stmt
  ιOut := pc.ιC
  OStmtOut := pc.OStmt
  Oᵢ := pc.Oᵢ
  WitOut := Poly
  relOut := pc.evalRel
  reduction := by
    letI : ∀ i, OracleInterface (pc.OStmt i) := pc.Oᵢ
    exact ⟨OracleProver.id, verifier⟩

set_option backward.isDefEq.respectTransparency false in
/-- Materializing input oracles retains the actual ambient query. -/
theorem verifier_run (stmt : Stmt) (ost : ∀ i, pc.OStmt i) (tr : FullTranscript !p[]) :
    verifier.toVerifier.run (stmt, ost) tr = (do
      let _ : Bool ← query (spec := oracle) ()
      pure (stmt, ost)) := by
  apply OptionT.ext
  have hout : verifier.materializeOutput tr.challenges ost tr.messages = ost := by
    funext i
    rfl
  simp only [Verifier.run, OracleVerifier.toVerifier, OptionT.run_mk]
  rw [hout]
  change (Option.map fun out => (out, ost)) <$>
    simulateQ (OracleInterface.simOracle2 oracle ost tr.messages)
      ((fun _ : Bool => some stmt) <$>
        (liftM (oracle.query ()) :
          OracleComp (oracle + ([pc.OStmt]ₒ + [(!p[]).Message]ₒ)) Bool)) = _
  rw [simulateQ_map]
  have hquery : simulateQ (OracleInterface.simOracle2 oracle ost tr.messages)
      (liftM (oracle.query ()) :
        OracleComp (oracle + ([pc.OStmt]ₒ + [(!p[]).Message]ₒ)) Bool) =
      (oracle.query () : OracleComp oracle Bool) := by
    rfl
  rw [hquery]
  rfl

/-- A generic zero-round prefix can reject before this effectful suffix is entered. -/
def front (accept : Bool) : OracleReduction oracle Stmt pc.OStmt Poly Stmt pc.OStmt Poly !p[] :=
  ⟨OracleProver.id, {
    verify stmt _ := if accept then pure stmt else failure
    outputOracle := .inl {
      embed := ⟨fun j => Sum.inl j, fun _ _ h => by cases h; rfl⟩
      hEq := fun _ => rfl
      outputInterface_heq := by intro i; rfl } }⟩

def frontGuard (accept : Bool) : (front accept).verifier.toVerifier.GuardedForm where
  check _ _ := accept
  out stmt _ := stmt
  verify_eq stmt tr := by
    apply OptionT.ext
    cases accept <;> simp [OracleVerifier.toVerifier, front, OptionT.run_failure]
    rfl

/-- One call changes the actual shared Boolean state. -/
def toggle : QueryImpl oracle (StateT Bool ProbComp) := fun _ => do
  let b ← get
  set (!b)
  pure b

local instance : ∀ i, OracleInterface ((!p[] ++ₚ !p[]).Message i) :=
  ProtocolSpec.instOracleInterfaceMessageAppend (pSpec₁ := !p[]) (pSpec₂ := !p[])

/-- An accepted generic prefix executes the downstream query and retains its changed state. -/
theorem accepted_effect (stmt : Stmt) (ost : ∀ i, pc.OStmt i) :
    (simulateQ toggle ((opening.assemble (front true)).verifier.toVerifier.run
      (stmt, ost) (fun i => Fin.elim0 i))).run false = pure (some (stmt, ost), true) := by
  rw [PackedOpening.verifier_run opening (front true) (frontGuard true)]
  simp only [frontGuard, ↓reduceIte]
  change (simulateQ toggle (verifier.toVerifier.run (stmt, ost) _)).run false = _
  rw [verifier_run]
  change (simulateQ toggle ((fun _ : Bool => some (stmt, ost)) <$>
    (query (spec := oracle) () : OracleComp oracle Bool))).run false = _
  simp [simulateQ_map, toggle]

/-- Rejection prevents the downstream query, so the shared state is unchanged. -/
theorem rejected_no_effect (stmt : Stmt) (ost : ∀ i, pc.OStmt i) :
    (simulateQ toggle ((opening.assemble (front false)).verifier.toVerifier.run
      (stmt, ost) (fun i => Fin.elim0 i))).run false = pure (none, false) := by
  rw [PackedOpening.verifier_run opening (front false) (frontGuard false)]
  simp only [frontGuard, Bool.false_eq_true, ↓reduceIte]
  rfl

end RingSwitching.Packing.Tests.OpeningEffects

end
