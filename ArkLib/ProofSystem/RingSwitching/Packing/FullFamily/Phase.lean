/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.Relations
import ArkLib.ProofSystem.RingSwitching.Packing.Batching
import ArkLib.ProofSystem.RingSwitching.Packing.PackedCommitment
import ArkLib.ProofSystem.RingSwitching.RoundVerifiers
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Guarded

/-!
# Full-family packing with a checked slice message

The public input contains every opening claim. The prover sends the packed slices, the verifier
checks their coordinate read-back against that public family, and a fresh challenge batches the
slices into a sumcheck claim. Failed read-back aborts the verifier.

The target may lie in a separate challenge algebra `C`, with compatible coefficient transport
`B → P → C`. Injectivity is a security premise rather than a requirement on the phase itself.
The original commitment relation is retained on the same oracle statements throughout.
Functionality is required only by the randomized security bound, not by this protocol.

This checked-message protocol is a sound variant of the public-derived slice presentation:
full-family claims already determine the slices by the coordinate transpose [RSG]. The
coordinate read-back is the uniqueness argument of [BRW26], Appendix B, Remark 5.

## References

* [*Ring switching, generalized*][RSG]
* [Bünz, B., Rothblum, R., and Wang, W., *Flock: Fast Proving for Batch Boolean
  Computations*][BRW26]
-/

noncomputable section

namespace RingSwitching.Packing.FullFamily

open OracleSpec OracleComp ProtocolSpec MvPolynomial CoordinateWise.ScalarRound

variable {B : Type} [CommRing B] (data : PackingData B) (m : ℕ)
  {C : Type} [CommRing C] [Algebra B C] [Algebra data.P C] [IsScalarTower B data.P C]
  (bat : BatchingStrategy C data.ιE) (pc : PackedCommitment data.P m)

/-- The opening family and its common evaluation point. -/
abbrev Input := (data.ιP → data.E) × (Fin m → data.E)

/-- The public point, batching challenge, and claimed sumcheck target. -/
abbrev Output := ((Fin m → data.E) × bat.Challenge) × C

/-- Send the packed slices, then sample a batching challenge. -/
def pSpec : ProtocolSpec 2 := pSpecScalar (data.ιE → data.P) bat.Challenge

instance : ∀ i, OracleInterface ((pSpec data bat).Message i) :=
  letI : OracleInterface (data.ιE → data.P) := OracleInterface.instDefault
  inferInstanceAs (∀ i, OracleInterface
    ((pSpecScalar (data.ιE → data.P) bat.Challenge).Message i))

instance : ∀ i, SampleableType ((pSpec data bat).Challenge i)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => SampleableType.ofFintype bat.Challenge

/-- The canonical slice family of a packed polynomial at the opening point. -/
def honestSlices (r : Fin m → data.E) (p : data.P⦃≤ 1⦄[X Fin m]) : data.ιE → data.P :=
  fun u => ∑ y : Fin m → Fin 2, data.eqCoord r y u • p.val.eval (y : Fin m → data.P)

/-- Honest slices satisfy the algebraic slice relation. -/
theorem honestSlices_mem_sliceRel (r : Fin m → data.E) (p : data.P⦃≤ 1⦄[X Fin m]) :
    (honestSlices data m r p, p) ∈ data.sliceRel m r :=
  fun _ => rfl

/-- The C-valued linear combination of a slice message. -/
def target (s : data.ιE → data.P) (c : bat.Challenge) : C :=
  ∑ u, bat.weight c u * algebraMap data.P C (s u)

/-- Public output when the checked message is accepted. -/
def nextStatement (stmt : Input data m) (s : data.ιE → data.P) (c : bat.Challenge) :
    Output data m bat :=
  ((stmt.2, c), target data bat s c)

/-- Honest prover state before packing, after packing, and after the challenge. -/
def ProverState : Fin 3 → Type
  | ⟨0, _⟩ => (Input data m × (∀ j, pc.OStmt j)) × (data.ιP → B⦃≤ 1⦄[X Fin m])
  | ⟨1, _⟩ => (Input data m × (∀ j, pc.OStmt j)) × data.P⦃≤ 1⦄[X Fin m]
  | _ => ((Input data m × (∀ j, pc.OStmt j)) × data.P⦃≤ 1⦄[X Fin m]) × bat.Challenge

/-- Pack the family, send its honest slices, and retain the committed packed polynomial. -/
def prover :
    OracleProver (oSpec := []ₒ) (StmtIn := Input data m) (OStmtIn := pc.OStmt)
      (WitIn := data.ιP → B⦃≤ 1⦄[X Fin m])
      (StmtOut := Output data m bat) (OStmtOut := pc.OStmt)
      (WitOut := data.P⦃≤ 1⦄[X Fin m]) (pSpec := pSpec data bat) where
  PrvState := ProverState data m bat pc
  input := fun ⟨⟨stmt, oStmt⟩, ps⟩ => ((stmt, oStmt), ps)
  sendMessage
    | ⟨0, _⟩ => fun ((stmt, oStmt), ps) => do
      let p := data.packedMLE ps
      return ⟨honestSlices data m stmt.2 p, ((stmt, oStmt), p)⟩
    | ⟨1, h⟩ => fun _ => nomatch h
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun st => pure fun c => (st, c)
  output := fun (((stmt, oStmt), p), c) =>
    pure ((nextStatement data m bat stmt (honestSlices data m stmt.2 p) c, oStmt), p)

open scoped Classical in
/-- Check slice read-back and abort on failure; otherwise retain the challenge and batched claim. -/
def verifier :
    OracleVerifier (oSpec := []ₒ) (StmtIn := Input data m) (OStmtIn := pc.OStmt)
      (StmtOut := Output data m bat) (OStmtOut := pc.OStmt) (pSpec := pSpec data bat) :=
  guardedScalarRoundOracleVerifier
    (oSpec := []ₒ) (OStmt := pc.OStmt)
    (check := fun stmt s => data.claimConsistent stmt.1 s)
    (accept := nextStatement data m bat)

/-- The checked-slice oracle reduction. -/
def reduction :
    OracleReduction (oSpec := []ₒ) (StmtIn := Input data m) (OStmtIn := pc.OStmt)
      (WitIn := data.ιP → B⦃≤ 1⦄[X Fin m])
      (StmtOut := Output data m bat) (OStmtOut := pc.OStmt)
      (WitOut := data.P⦃≤ 1⦄[X Fin m]) (pSpec := pSpec data bat) where
  prover := prover data m bat pc
  verifier := verifier data m bat pc

/-- Every public opening is true, and the input oracles commit to the packed family. -/
def relIn :
    Set (((Input data m) × (∀ j, pc.OStmt j)) × (data.ιP → B⦃≤ 1⦄[X Fin m])) :=
  { x | (x.1.1, x.2) ∈ data.openingClaimRel m ∧ pc.commitsTo x.1.2 (data.packedMLE x.2) }

/-- The batched sumcheck claim with the same commitment relation on the same oracles. -/
def relOut :
    Set (((Output data m bat) × (∀ j, pc.OStmt j)) × data.P⦃≤ 1⦄[X Fin m]) :=
  { x | (x.1.1.2, x.2) ∈ data.sumcheckClaimRel m x.1.1.1.1 (bat.weight x.1.1.1.2)
      ∧ pc.commitsTo x.1.2 x.2 }

open scoped Classical in
omit [Algebra B C] [IsScalarTower B data.P C] in
/-- Exact execution after materializing the input and message oracles. -/
theorem verifier_verify (stmt : Input data m) (oStmt : ∀ j, pc.OStmt j)
    (tr : FullTranscript (pSpec data bat)) :
    (verifier data m bat pc).toVerifier.verify (stmt, oStmt) tr =
      (if data.claimConsistent stmt.1 (tr.messages ⟨0, rfl⟩) then
        pure (nextStatement data m bat stmt (tr.messages ⟨0, rfl⟩)
          (tr.challenges ⟨1, rfl⟩), oStmt) else failure) := by
  classical
  apply guardedScalarRoundOracleVerifier_verify

open scoped Classical in
/-- Deterministic guarded execution, suitable for state-aware composition contracts. -/
def guardedForm : (verifier data m bat pc).toVerifier.GuardedForm where
  check stmt tr := decide (data.claimConsistent stmt.1.1 (tr.messages ⟨0, rfl⟩))
  out stmt tr := (nextStatement data m bat stmt.1 (tr.messages ⟨0, rfl⟩)
    (tr.challenges ⟨1, rfl⟩), stmt.2)
  verify_eq stmt tr := by
    rw [verifier_verify]
    simp

/-- The prover's output contains no oracle queries, so it can be sequenced statefully. -/
instance : (prover data m bat pc).OutputIsPure where
  output_is_pure := ⟨fun (((stmt, oStmt), p), c) =>
    ((nextStatement data m bat stmt (honestSlices data m stmt.2 p) c, oStmt), p), fun _ => rfl⟩

end RingSwitching.Packing.FullFamily

end
