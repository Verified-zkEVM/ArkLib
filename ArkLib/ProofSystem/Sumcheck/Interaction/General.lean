/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.SingleRound
import ArkLib.Interaction.Oracle.Chain
import ArkLib.Interaction.Oracle.Protocol
import ArkLib.Interaction.Choreo

/-!
# Sum-Check Multi-Round Oracle Surface

This module builds the `n`-round sum-check oracle reduction as a state-machine
fold over the oracle chain. The input oracle statement is the bounded-degree
polynomial being checked. The prover has no separate polynomial witness; it
keeps a private residual state whose type shrinks from `PolyStmt ... (n + 1)`
to `PolyStmt ... n` at each round.
-/

namespace Sumcheck

open Interaction.TwoParty
open Interaction CompPoly OracleComp OracleSpec

section

variable (R : Type) [BEq R] [CommSemiring R] [LawfulBEq R] [Nontrivial R] (deg : ℕ)

/-- The `n`-round sum-check oracle chain.

Each level is the existing one-round oracle spec. The continuation is
constant because the next round shape does not depend on the public challenge;
participant state is handled by the parties, not by the protocol shape. -/
def fullChain : (n : Nat) → Interaction.Oracle.Spec.Chain n :=
  Interaction.Oracle.Spec.Chain.replicate
    (roundSpec R deg) (roundRoles R deg) (roundOracleDeco R deg)

/-- Decorated `n`-round sum-check oracle protocol, flattened from
`fullChain`. -/
abbrev protocol (n : Nat) : Interaction.Oracle.Spec.Protocol where
  spec := Interaction.Oracle.Spec.Chain.toSpec n (fullChain R deg n)
  roles := Interaction.Oracle.Spec.Chain.toRoles n (fullChain R deg n)
  oracleDeco := Interaction.Oracle.Spec.Chain.toOracleDeco n (fullChain R deg n)

/-- The `n`-round sum-check oracle spec, flattened from `fullChain`. -/
abbrev context (n : Nat) : Interaction.Oracle.Spec :=
  (protocol R deg n).spec

/-- Role decoration for `context`. -/
abbrev roles (n : Nat) : Interaction.Oracle.Spec.RoleDeco (context R deg n) :=
  (protocol R deg n).roles

/-- Oracle decoration for `context`. -/
abbrev oracleDeco (n : Nat) :
    Interaction.Oracle.Spec.OracleDeco (context R deg n) :=
  (protocol R deg n).oracleDeco

/-- Extract the public transcript of the `i`-th oracle sum-check round. Since
round polynomials are oracle messages, this transcript contains the oracle-round
marker and the verifier challenge, but not the polynomial message itself. -/
def roundPublicTranscript (n : Nat)
    (pt : Interaction.Oracle.Spec.PublicTranscript (context R deg n)) (i : Fin n) :
    RoundPublicTranscript R deg :=
  match n with
  | 0 => i.elim0
  | n + 1 =>
      let split := Interaction.Oracle.Spec.Chain.splitPublicTranscript n
        (fullChain R deg (n + 1)) pt
      Fin.cases split.1
        (fun i => roundPublicTranscript n split.2 i)
        i

/-- Extract the vector of verifier challenges from an `n`-round oracle
sum-check public transcript. -/
def challengePoint (n : Nat)
    (pt : Interaction.Oracle.Spec.PublicTranscript (context R deg n)) :
    Fin n → R :=
  fun i => roundChallenge R deg (roundPublicTranscript R deg n pt i)

/-- Package an optional terminal round claim with the public transcript's
challenge point. -/
def finalClaimFromOption (n : Nat)
    (pt : Interaction.Oracle.Spec.PublicTranscript (context R deg n)) :
    Option (RoundClaim R) → Option (FinalClaim R n)
  | none => none
  | some value => some { point := challengePoint R deg n pt, value }

end

section

variable {R : Type} [BEq R] [CommSemiring R] [LawfulBEq R] [Nontrivial R] {deg : ℕ}

/-- Honest prover state for the chain fold. The current claim mirrors the
verifier state so the honest prover can emit the terminal statement, while the
residual polynomial is private execution state derived from the original
degree-bounded oracle statement. -/
private structure ProverState (numVars : Nat) (k : Nat) where
  claim : Option (RoundClaim R)
  oracleStmt : OracleStatement (Sumcheck.PolyFamily R deg numVars)
  residual : Sumcheck.PolyStmt R deg k

/-- Honest prover strategy for one step of the concrete sum-check chain.

This is deliberately kept as a lower-level chain handler. The reduction-level
choreography surface is currently represented by `SingleRound.roundProgram`;
multi-round should move back to choreography only once the DSL can compile an
entire chain/telescope together with its single `simulate` field. -/
private def proverRoundStep (m : Type → Type) [Monad m]
    {NextState : Type}
    {m_dom : ℕ} (D : Fin m_dom → R)
    {numVars : ℕ}
    (poly : Sumcheck.PolyStmt R deg (numVars + 1))
    (computeNext : CDegreeLE R deg → R → NextState) :
    Interaction.Spec.StrategyOver (pairedSyntax m)
      Interaction.TwoParty.Participant.focal
      (roundSpec R deg).toInteractionSpec
      ((roundSpec R deg).toSpecRoles (roundRoles R deg))
      (fun _ => NextState) :=
  let sentPoly := honestRoundPoly (R := R) (deg := deg) D poly
  pure ⟨sentPoly, fun chal => pure (computeNext sentPoly chal)⟩

/-- Verifier strategy for one step of the concrete sum-check chain.

This is not the final choreography surface; it is the low-level handler used by
`Oracle.Spec.Chain` until a reduction-level chain choreography compiler exists. -/
private noncomputable def verifierRoundStepOption
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {m_dom : ℕ} (D : Fin m_dom → R) (numVars : Nat)
    (target : Option (RoundClaim R))
    (sampleChallenge : OracleComp oSpec R) :
    Interaction.Spec.StrategyOver counterpartMonadicSyntax PUnit.unit
      (roundSpec R deg).toInteractionSpec
      (RoleDecoration.withMonads ((roundSpec R deg).toSpecRoles (roundRoles R deg))
        ((roundSpec R deg).toMonadDecoration oSpec (Sumcheck.PolyFamily R deg numVars)
          (roundRoles R deg) (roundOracleDeco R deg) []ₒ))
      (fun _ => Option (RoundClaim R)) :=
  let oiSpec := @OracleInterface.spec (CDegreeLE R deg) inferInstance
  match target with
  | none =>
      fun _ =>
        let receiverStep :
            OracleComp
              (oSpec + [Sumcheck.PolyFamily R deg numVars]ₒ + ([]ₒ + oiSpec))
              ((_ : R) × Option (RoundClaim R)) := do
            let chal : R ← liftM sampleChallenge
            pure ⟨chal, none⟩
        receiverStep
  | some target =>
      fun _ =>
        let receiverStep :
            OracleComp
              (oSpec + [Sumcheck.PolyFamily R deg numVars]ₒ + ([]ₒ + oiSpec))
              ((_ : R) × Option (RoundClaim R)) := do
            let total ← (Finset.univ : Finset (Fin m_dom)).toList.foldlM
              (fun (acc : R) (j : Fin m_dom) => do
                let val : R ← liftM <| oiSpec.query (D j)
                pure (acc + val))
              (0 : R)
            let chal : R ← liftM sampleChallenge
            if total == target then do
              let polyAtChal : R ← liftM <| oiSpec.query chal
              pure ⟨chal, some polyAtChal⟩
            else
              pure ⟨chal, none⟩
        receiverStep

/-- Prover round handlers for the concrete sum-check chain. -/
private noncomputable def proverRoundSteps
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {m_dom : ℕ} (D : Fin m_dom → R) (numVars : Nat) :
    (n : Nat) →
      Interaction.Oracle.Spec.Chain.Prover.RoundSteps (m := OracleComp oSpec)
        (fun {k} _ => ProverState (R := R) (deg := deg) numVars k)
        n (fullChain R deg n)
  | 0 => PUnit.unit
  | n + 1 =>
      ⟨fun state =>
        pure <|
          proverRoundStep (m := OracleComp oSpec) (R := R) (deg := deg)
            D state.residual
            (fun sentPoly chal =>
              { claim := state.claim.bind fun _ => some (CPolynomial.eval chal sentPoly.1)
                oracleStmt := state.oracleStmt
                residual := stepResidual (R := R) (deg := deg) chal state.residual }),
        fun _ => proverRoundSteps (oSpec := oSpec) D numVars n⟩

/-- Verifier round handlers for the concrete sum-check chain. -/
private noncomputable def verifierRoundSteps
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {m_dom : ℕ} (D : Fin m_dom → R) (numVars : Nat)
    (sampleChallenge : OracleComp oSpec R) :
    (n : Nat) →
      Interaction.Oracle.Spec.Chain.Verifier.RoundSteps
        (oSpec := oSpec) (OStmtIn := Sumcheck.PolyFamily R deg numVars)
        (fun {_k} _ => Option (RoundClaim R))
        n (fullChain R deg n)
  | 0 => PUnit.unit
  | n + 1 =>
      ⟨fun claim =>
        verifierRoundStepOption (R := R) (deg := deg) (oSpec := oSpec)
          D numVars claim sampleChallenge,
        fun _ => verifierRoundSteps (oSpec := oSpec) D numVars sampleChallenge n⟩

/-- Stateful oracle choreography program for the `n`-round sum-check reduction. -/
private noncomputable def reductionProgram
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    (sampleChallenge : OracleComp oSpec R) (n : Nat) :
    Interaction.Choreo.OracleProtocol.ChainProgram
      (oSpec := oSpec)
      (SharedIn := RoundClaim R)
      (StatementIn := fun _ => PUnit)
      (OStatementIn := fun _ => Sumcheck.PolyFamily R deg n)
      (WitnessIn := fun _ => PUnit)
      (n := n)
      (chain := fun _ => fullChain R deg n)
      (StatementOut := fun _ _ => Option (FinalClaim R n))
      (OStatementOut := fun _ _ => Sumcheck.PolyFamily R deg n)
      (WitnessOut := fun _ _ => PUnit) where
  ProverState := fun _ {k} _ => ProverState (R := R) (deg := deg) n k
  VerifierState := fun _ {_k} _ => Option (RoundClaim R)
  proverInit := fun shared sWithOracles _ =>
    { claim := some shared
      oracleStmt := sWithOracles.oracleStmt
      residual := sWithOracles.oracleStmt () }
  verifierInit := fun shared _ => some shared
  proverSteps := fun _ =>
    proverRoundSteps (R := R) (deg := deg) (oSpec := oSpec)
      D n n
  verifierSteps := fun _ =>
    verifierRoundSteps (R := R) (deg := deg) (oSpec := oSpec)
      D n sampleChallenge n
  proverStmtResult := fun _ pt state =>
    finalClaimFromOption R deg n pt
      (Interaction.Oracle.Spec.Chain.terminalOutput
        (fun {k} _ => ProverState (R := R) (deg := deg) n k)
        n (fullChain R deg n) pt state).claim
  verifierStmtResult := fun _ pt state =>
    finalClaimFromOption R deg n pt
      (Interaction.Oracle.Spec.Chain.terminalOutput
        (fun {_k} _ => Option (RoundClaim R))
        n (fullChain R deg n) pt state)
  oracleStmtResult := fun _ pt state =>
    (Interaction.Oracle.Spec.Chain.terminalOutput
      (fun {k} _ => ProverState (R := R) (deg := deg) n k)
      n (fullChain R deg n) pt state).oracleStmt
  witnessResult := fun _ _ _ => PUnit.unit
  simulate := fun _ _ q => liftM <| ([Sumcheck.PolyFamily R deg n]ₒ).query q

/-- The `n`-round sum-check reduction, built by composing one-round oracle
choreographies.

The input statement is the initial claim. The singleton input oracle statement
is the bounded-degree polynomial itself and is carried unchanged through all
rounds. The prover's shrinking residual polynomial is internal execution state,
not a witness supplied to the reduction. The output statement is the final
challenge point and claimed value, with `none` representing verifier rejection. -/
noncomputable def reduction
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    {m_dom : ℕ} (D : Fin m_dom → R)
    (sampleChallenge : OracleComp oSpec R) (n : Nat) :
    Interaction.Oracle.Reduction oSpec
      (RoundClaim R)
      (fun _ => context R deg n)
      (fun _ => roles R deg n)
      (fun _ => oracleDeco R deg n)
      (fun _ => PUnit)
      (fun _ => Sumcheck.PolyFamily R deg n)
      (fun _ => PUnit)
      (fun _ _ => Option (FinalClaim R n))
      (fun _ _ => Sumcheck.PolyFamily R deg n)
      (fun _ _ => PUnit) := by
  exact (reductionProgram (R := R) (deg := deg) (oSpec := oSpec)
    D sampleChallenge n).toReduction

end

end Sumcheck
