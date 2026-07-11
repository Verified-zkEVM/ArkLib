/- 
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Interaction.SingleRound
import PolyFun.Interaction.TwoParty.Refine
import VCVio

/-!
# Interaction-Native Sum-Check: General Oracle Protocol

The canonical interaction-native `n`-round sum-check protocol is an
oracle-native continuation composition over a **fixed original polynomial
oracle**.

The public protocol state is just the current live claim:
- the first round starts from `target : RoundClaim R`;
- later rounds carry `Option (RoundClaim R)`, preserving failure after the first
  rejected check.

The honest prover is stateless at the protocol boundary. At every round it
recomputes the current residual polynomial from the original oracle statement
and the prefix transcript of prior challenges.
-/

namespace Sumcheck

open Interaction Interaction.TwoParty Interaction.OracleDecoration
open CompPoly CPoly OracleComp OracleSpec
open scoped NNReal ENNReal

section

variable (R : Type) [BEq R] [CommSemiring R] [LawfulBEq R] [Nontrivial R] (deg : ℕ)

section

variable {R} {deg}

/-- The replicated sender-message oracle decoration for the full `n`-round
sum-check surface. -/
abbrev fullOD (n : Nat) :
    OracleDecoration (Sumcheck.fullSpec R deg n) (Sumcheck.fullRoles R deg n) :=
  (roundOracleDecoration R deg).replicate n

/-- Append one more round transcript to the right end of an existing replicated
prefix transcript. -/
private def snocRoundTranscript (prefixLen : Nat)
    (prefixTr : Spec.Transcript (Sumcheck.fullSpec R deg prefixLen))
    (tr : Spec.Transcript (roundSpec R deg)) :
    Spec.Transcript (Sumcheck.fullSpec R deg (prefixLen + 1)) :=
  Spec.Transcript.replicateJoin (roundSpec R deg) (prefixLen + 1) fun j =>
    Fin.lastCases tr (fun i => Sumcheck.roundTranscript R deg prefixLen prefixTr i) j

/-- Consume a replicated tail transcript against a current residual polynomial,
threading the residual forward round by round until only the final `0`-variate
residual remains. This is the private witness produced by the stateful prover
after replaying the tail. -/
private def consumeResidual :
    (remaining : Nat) →
    Sumcheck.PolyStmt R deg remaining →
    Spec.Transcript (Sumcheck.fullSpec R deg remaining) →
    Sumcheck.PolyStmt R deg 0
  | 0, residual, _ => by
      simpa [Sumcheck.fullSpec] using residual
  | remaining + 1, residual, tr => by
      let split := Spec.Transcript.replicateUncons (roundSpec R deg) remaining tr
      exact
        consumeResidual remaining
          (stepResidual (R := R) (deg := deg)
            (Sumcheck.roundChallenge R deg split.1) residual)
          split.2
termination_by remaining _ _ => remaining
decreasing_by simp_wf

@[simp]
private theorem consumeResidual_replicateCons
    (remaining : Nat)
    (residual : Sumcheck.PolyStmt R deg (remaining + 1))
    (tr₁ : Spec.Transcript (roundSpec R deg))
    (tr₂ : Spec.Transcript (Sumcheck.fullSpec R deg remaining)) :
    consumeResidual (R := R) (deg := deg) (remaining + 1) residual
      (Spec.Transcript.replicateCons (roundSpec R deg) remaining tr₁ tr₂) =
      consumeResidual (R := R) (deg := deg) remaining
        (stepResidual (R := R) (deg := deg)
          (Sumcheck.roundChallenge R deg tr₁) residual)
        tr₂ := by
  simp [consumeResidual, Spec.Transcript.replicateCons, Spec.Transcript.split_append]

/-- The active residual polynomial after fixing the `prefixLen` verifier
challenges already present in `prefixTr`. The equality `prefixLen + remaining = n`
lets us view this as a polynomial in exactly `remaining` variables. -/
private def residualAtPrefix
    (n remaining prefixLen : Nat)
    (h : prefixLen + remaining = n)
    (prefixTr : Spec.Transcript (Sumcheck.fullSpec R deg prefixLen))
    (poly : Sumcheck.PolyStmt R deg n) :
    Sumcheck.PolyStmt R deg remaining := by
  have hle : prefixLen ≤ n := by omega
  have hk : n - prefixLen = remaining := by omega
  simpa [hk] using
    currentResidual (R := R) (deg := deg) (n := n) (prefixLen := prefixLen)
      hle
      (Sumcheck.challengePrefix R deg prefixLen prefixTr)
      poly

/-- Tail continuation for the remaining `remaining` rounds after a fixed prefix
transcript of length `prefixLen`. The original polynomial oracle remains
unchanged throughout. -/
private noncomputable def tailContinuation
    {ι : Type} {oSpec : OracleSpec ι}
    {m_dom : Nat} (D : Fin m_dom → R)
    (n : Nat)
    (sampleChallenge : OracleComp oSpec R) :
    (remaining prefixLen : Nat) →
    (h : prefixLen + remaining = n) →
    Spec.Transcript (Sumcheck.fullSpec R deg prefixLen) →
    OracleReduction oSpec PUnit
      (fun _ => Sumcheck.fullSpec R deg remaining)
      (fun _ => Sumcheck.fullRoles R deg remaining)
      (fun _ => fullOD remaining)
      (fun _ => Option (RoundClaim R))
      (fun _ => Sumcheck.PolyFamily R deg n)
      (fun _ => PUnit)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg n)
      (fun _ _ => PUnit)
  | 0, _, _, _ => by
      simpa [Sumcheck.fullSpec, Sumcheck.fullRoles, fullOD] using
        (OracleReduction.id
          (SharedIn := PUnit)
          (StatementIn := fun _ => Option (RoundClaim R))
          (OStmtIn := fun _ => Sumcheck.PolyFamily R deg n)
          (WitnessIn := fun _ => PUnit))
  | remaining + 1, prefixLen, hEq, prefixTr => by
      have hRound : prefixLen < n := by omega
      have hTail : prefixLen + 1 + remaining = n := by omega
      have cont :
          OracleReduction oSpec PUnit
            (fun _ => (roundSpec R deg).append (fun _ => Sumcheck.fullSpec R deg remaining))
            (fun _ =>
              Spec.Decoration.append
                (roundRoles R deg)
                (fun _ => Sumcheck.fullRoles R deg remaining))
            (fun _ =>
              Role.Refine.append
                (roundOracleDecoration R deg)
                (fun _ => fullOD remaining))
            (fun _ => Option (RoundClaim R))
            (fun _ => Sumcheck.PolyFamily R deg n)
            (fun _ => PUnit)
            (fun _ _ => Option (RoundClaim R))
            (fun _ _ => Sumcheck.PolyFamily R deg n)
            (fun _ _ => PUnit) :=
        OracleReduction.comp
          (StmtMid := fun _ _ => Option (RoundClaim R))
          (ιₛₘ := fun _ _ => Unit)
          (OStatementMid := fun _ _ => Sumcheck.PolyFamily R deg n)
          (WitMid := fun _ _ => PUnit)
          (ctx₂ := fun _ _ => Sumcheck.fullSpec R deg remaining)
          (roles₂ := fun _ _ => Sumcheck.fullRoles R deg remaining)
          (oracleDeco₂ := fun _ _ => fullOD remaining)
          (StmtOut := fun _ _ _ => Option (RoundClaim R))
          (ιₛₒ := fun _ _ _ => Unit)
          (OStatementOut := fun _ _ _ => Sumcheck.PolyFamily R deg n)
          (WitOut := fun _ _ _ => PUnit)
          (roundContinuationOption
            (R := R) (deg := deg) D
            (n := n) (prefixLen := prefixLen) hRound prefixTr sampleChallenge)
          { prover := fun st sWithOracles w => do
              let tail :=
                tailContinuation D n sampleChallenge
                  remaining (prefixLen + 1) hTail
                  (snocRoundTranscript (R := R) (deg := deg) prefixLen prefixTr st.2)
              let input' :
                  StatementWithOracles
                    (fun _ => Option (RoundClaim R))
                    (fun _ => Sumcheck.PolyFamily R deg n) PUnit.unit :=
                ⟨sWithOracles.stmt, sWithOracles.oracleStmt⟩
              let remapOutput :
                  (tr : Spec.Transcript (Sumcheck.fullSpec R deg remaining)) →
                  HonestProverOutput
                    (StatementWithOracles
                      (fun _ => Option (RoundClaim R))
                      (fun _ => Sumcheck.PolyFamily R deg n) PUnit.unit)
                    PUnit →
                  HonestProverOutput
                    (StatementWithOracles
                      (fun _ => Option (RoundClaim R))
                      (fun _ => Sumcheck.PolyFamily R deg n) st)
                    PUnit
                | _, ⟨stmtOut, witOut⟩ => ⟨⟨stmtOut.stmt, stmtOut.oracleStmt⟩, witOut⟩
              let strat ← tail.prover PUnit.unit input' w
              pure <| Spec.Strategy.mapOutputWithRoles remapOutput strat
            verifier := fun st {_} accSpec stmt =>
              let tail :=
                tailContinuation D n sampleChallenge
                  remaining (prefixLen + 1) hTail
                  (snocRoundTranscript (R := R) (deg := deg) prefixLen prefixTr st.2)
              tail.verifier PUnit.unit accSpec stmt
            simulate := fun st tr =>
              let tail :=
                tailContinuation D n sampleChallenge
                  remaining (prefixLen + 1) hTail
                  (snocRoundTranscript (R := R) (deg := deg) prefixLen prefixTr st.2)
              tail.simulate PUnit.unit tr }
      simpa [Sumcheck.fullSpec, Sumcheck.fullRoles, fullOD, Spec.replicate_succ] using cont

/-- Tail continuation for the remaining `remaining` rounds when the honest prover
threads the current residual polynomial privately instead of recomputing it from
the prefix transcript. The public oracle statement still stays fixed as the
original polynomial. -/
private noncomputable def tailContinuationStateful
    {ι : Type} {oSpec : OracleSpec ι}
    {m_dom : Nat} (D : Fin m_dom → R)
    (n : Nat)
    (sampleChallenge : OracleComp oSpec R) :
    (remaining : Nat) →
    OracleReduction oSpec PUnit
      (fun _ => Sumcheck.fullSpec R deg remaining)
      (fun _ => Sumcheck.fullRoles R deg remaining)
      (fun _ => fullOD remaining)
      (fun _ => Option (RoundClaim R))
      (fun _ => Sumcheck.PolyFamily R deg n)
      (fun _ => Sumcheck.PolyStmt R deg remaining)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg n)
      (fun _ _ => Sumcheck.PolyStmt R deg 0)
  | 0 => by
      simpa [Sumcheck.fullSpec, Sumcheck.fullRoles, fullOD] using
        (OracleReduction.id
          (SharedIn := PUnit)
          (StatementIn := fun _ => Option (RoundClaim R))
          (OStmtIn := fun _ => Sumcheck.PolyFamily R deg n)
          (WitnessIn := fun _ => Sumcheck.PolyStmt R deg 0))
  | remaining + 1 => by
      have cont :
          OracleReduction oSpec PUnit
            (fun _ => (roundSpec R deg).append (fun _ => Sumcheck.fullSpec R deg remaining))
            (fun _ =>
              Spec.Decoration.append
                (roundRoles R deg)
                (fun _ => Sumcheck.fullRoles R deg remaining))
            (fun _ =>
              Role.Refine.append
                (roundOracleDecoration R deg)
                (fun _ => fullOD remaining))
            (fun _ => Option (RoundClaim R))
            (fun _ => Sumcheck.PolyFamily R deg n)
            (fun _ => Sumcheck.PolyStmt R deg (remaining + 1))
            (fun _ _ => Option (RoundClaim R))
            (fun _ _ => Sumcheck.PolyFamily R deg n)
            (fun _ _ => Sumcheck.PolyStmt R deg 0) :=
        OracleReduction.comp
          (StmtMid := fun _ _ => Option (RoundClaim R))
          (ιₛₘ := fun _ _ => Unit)
          (OStatementMid := fun _ _ => Sumcheck.PolyFamily R deg n)
          (WitMid := fun _ _ => Sumcheck.PolyStmt R deg remaining)
          (ctx₂ := fun _ _ => Sumcheck.fullSpec R deg remaining)
          (roles₂ := fun _ _ => Sumcheck.fullRoles R deg remaining)
          (oracleDeco₂ := fun _ _ => fullOD remaining)
          (StmtOut := fun _ _ _ => Option (RoundClaim R))
          (ιₛₒ := fun _ _ _ => Unit)
          (OStatementOut := fun _ _ _ => Sumcheck.PolyFamily R deg n)
          (WitOut := fun _ _ _ => Sumcheck.PolyStmt R deg 0)
          (roundContinuationOptionStateful
            (R := R) (deg := deg) D
            (totalVars := n) remaining sampleChallenge)
          { prover := fun st sWithOracles w => do
              let tail := tailContinuationStateful D n sampleChallenge remaining
              let input' :
                  StatementWithOracles
                    (fun _ => Option (RoundClaim R))
                    (fun _ => Sumcheck.PolyFamily R deg n) PUnit.unit :=
                ⟨sWithOracles.stmt, sWithOracles.oracleStmt⟩
              let remapOutput :
                  (tr : Spec.Transcript (Sumcheck.fullSpec R deg remaining)) →
                  HonestProverOutput
                    (StatementWithOracles
                      (fun _ => Option (RoundClaim R))
                      (fun _ => Sumcheck.PolyFamily R deg n) PUnit.unit)
                    (Sumcheck.PolyStmt R deg 0) →
                  HonestProverOutput
                    (StatementWithOracles
                      (fun _ => Option (RoundClaim R))
                      (fun _ => Sumcheck.PolyFamily R deg n) st)
                    (Sumcheck.PolyStmt R deg 0)
                | _, ⟨stmtOut, witOut⟩ => ⟨⟨stmtOut.stmt, stmtOut.oracleStmt⟩, witOut⟩
              let strat ← tail.prover PUnit.unit input' w
              pure <| Spec.Strategy.mapOutputWithRoles remapOutput strat
            verifier := fun _ {_} accSpec stmt =>
              (tailContinuationStateful D n sampleChallenge remaining).verifier
                PUnit.unit accSpec stmt
            simulate := fun _ tr =>
              (tailContinuationStateful D n sampleChallenge remaining).simulate
                PUnit.unit tr }
      simpa [Sumcheck.fullSpec, Sumcheck.fullRoles, fullOD, Spec.replicate_succ] using cont

/-- The full continuation-native sum-check protocol over the fixed original
polynomial oracle. -/
private noncomputable def sumcheckContinuation
    {ι : Type} {oSpec : OracleSpec ι}
    (n : Nat)
    {m_dom : Nat} (D : Fin m_dom → R)
    (sampleChallenge : OracleComp oSpec R) :
    OracleReduction oSpec PUnit
      (fun _ => Sumcheck.fullSpec R deg n)
      (fun _ => Sumcheck.fullRoles R deg n)
      (fun _ => fullOD n)
      (fun _ => RoundClaim R)
      (fun _ => Sumcheck.PolyFamily R deg n)
      (fun _ => PUnit)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg n)
      (fun _ _ => PUnit) := by
  cases n with
  | zero =>
      refine
        { prover := ?_
          verifier := ?_
          simulate := ?_ }
      · intro _ sWithOracles _
        exact pure ⟨⟨some sWithOracles.stmt, sWithOracles.oracleStmt⟩, PUnit.unit⟩
      · intro _ _ _ target
        exact some target
      · intro _ _ q
        exact liftM <| ([Sumcheck.PolyFamily R deg 0]ₒ).query q
  | succ n =>
      let prefix0 : Spec.Transcript (Sumcheck.fullSpec R deg 0) := by
        simpa [Sumcheck.fullSpec] using
          (show Spec.Transcript ((roundSpec R deg).replicate 0) from ⟨⟩)
      have cont :
          OracleReduction oSpec PUnit
            (fun _ => (roundSpec R deg).append (fun _ => Sumcheck.fullSpec R deg n))
            (fun _ =>
              Spec.Decoration.append
                (roundRoles R deg)
                (fun _ => Sumcheck.fullRoles R deg n))
            (fun _ =>
              Role.Refine.append
                (roundOracleDecoration R deg)
                (fun _ => fullOD n))
            (fun _ => RoundClaim R)
            (fun _ => Sumcheck.PolyFamily R deg (n + 1))
            (fun _ => PUnit)
            (fun _ _ => Option (RoundClaim R))
            (fun _ _ => Sumcheck.PolyFamily R deg (n + 1))
            (fun _ _ => PUnit) :=
        OracleReduction.comp
          (StmtMid := fun _ _ => Option (RoundClaim R))
          (ιₛₘ := fun _ _ => Unit)
          (OStatementMid := fun _ _ => Sumcheck.PolyFamily R deg (n + 1))
          (WitMid := fun _ _ => PUnit)
          (ctx₂ := fun _ _ => Sumcheck.fullSpec R deg n)
          (roles₂ := fun _ _ => Sumcheck.fullRoles R deg n)
          (oracleDeco₂ := fun _ _ => fullOD n)
          (StmtOut := fun _ _ _ => Option (RoundClaim R))
          (ιₛₒ := fun _ _ _ => Unit)
          (OStatementOut := fun _ _ _ => Sumcheck.PolyFamily R deg (n + 1))
          (WitOut := fun _ _ _ => PUnit)
          (roundContinuation
            (R := R) (deg := deg) D
            (n := n + 1) (prefixLen := 0)
            (Nat.succ_pos n)
            prefix0
            sampleChallenge)
          { prover := fun st sWithOracles w => do
              let tail :=
                tailContinuation D (n + 1) sampleChallenge
                  n 1 (by omega)
                  (snocRoundTranscript (R := R) (deg := deg) 0 prefix0 st.2)
              let input' :
                  StatementWithOracles
                    (fun _ => Option (RoundClaim R))
                    (fun _ => Sumcheck.PolyFamily R deg (n + 1)) PUnit.unit :=
                ⟨sWithOracles.stmt, sWithOracles.oracleStmt⟩
              let remapOutput :
                  (tr : Spec.Transcript (Sumcheck.fullSpec R deg n)) →
                  HonestProverOutput
                    (StatementWithOracles
                      (fun _ => Option (RoundClaim R))
                      (fun _ => Sumcheck.PolyFamily R deg (n + 1)) PUnit.unit)
                    PUnit →
                  HonestProverOutput
                    (StatementWithOracles
                      (fun _ => Option (RoundClaim R))
                      (fun _ => Sumcheck.PolyFamily R deg (n + 1)) st)
                    PUnit
                | _, ⟨stmtOut, witOut⟩ => ⟨⟨stmtOut.stmt, stmtOut.oracleStmt⟩, witOut⟩
              let strat ← tail.prover PUnit.unit input' w
              pure <| Spec.Strategy.mapOutputWithRoles remapOutput strat
            verifier := fun st {_} accSpec stmt =>
              let tail :=
                tailContinuation D (n + 1) sampleChallenge
                  n 1 (by omega)
                  (snocRoundTranscript (R := R) (deg := deg) 0 prefix0 st.2)
              tail.verifier PUnit.unit accSpec stmt
            simulate := fun st tr =>
              let tail :=
                tailContinuation D (n + 1) sampleChallenge
                  n 1 (by omega)
                  (snocRoundTranscript (R := R) (deg := deg) 0 prefix0 st.2)
              tail.simulate PUnit.unit tr }
      simpa [Sumcheck.fullSpec, Sumcheck.fullRoles, fullOD, Spec.replicate_succ] using cont

/-- The full continuation-native sum-check protocol with a private residual
polynomial witness threaded across rounds. The public oracle statement remains
the original polynomial oracle throughout. -/
private noncomputable def sumcheckContinuationStateful
    {ι : Type} {oSpec : OracleSpec ι}
    (n : Nat)
    {m_dom : Nat} (D : Fin m_dom → R)
    (sampleChallenge : OracleComp oSpec R) :
    OracleReduction oSpec PUnit
      (fun _ => Sumcheck.fullSpec R deg n)
      (fun _ => Sumcheck.fullRoles R deg n)
      (fun _ => fullOD n)
      (fun _ => RoundClaim R)
      (fun _ => Sumcheck.PolyFamily R deg n)
      (fun _ => Sumcheck.PolyStmt R deg n)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg n)
      (fun _ _ => Sumcheck.PolyStmt R deg 0) := by
  cases n with
  | zero =>
      refine
        { prover := ?_
          verifier := ?_
          simulate := ?_ }
      · intro _ sWithOracles witness
        exact pure ⟨⟨some sWithOracles.stmt, sWithOracles.oracleStmt⟩, witness⟩
      · intro _ _ _ target
        exact some target
      · intro _ _ q
        exact liftM <| ([Sumcheck.PolyFamily R deg 0]ₒ).query q
  | succ n =>
      have cont :
          OracleReduction oSpec PUnit
            (fun _ => (roundSpec R deg).append (fun _ => Sumcheck.fullSpec R deg n))
            (fun _ =>
              Spec.Decoration.append
                (roundRoles R deg)
                (fun _ => Sumcheck.fullRoles R deg n))
            (fun _ =>
              Role.Refine.append
                (roundOracleDecoration R deg)
                (fun _ => fullOD n))
            (fun _ => RoundClaim R)
            (fun _ => Sumcheck.PolyFamily R deg (n + 1))
            (fun _ => Sumcheck.PolyStmt R deg (n + 1))
            (fun _ _ => Option (RoundClaim R))
            (fun _ _ => Sumcheck.PolyFamily R deg (n + 1))
            (fun _ _ => Sumcheck.PolyStmt R deg 0) :=
        OracleReduction.comp
          (StmtMid := fun _ _ => Option (RoundClaim R))
          (ιₛₘ := fun _ _ => Unit)
          (OStatementMid := fun _ _ => Sumcheck.PolyFamily R deg (n + 1))
          (WitMid := fun _ _ => Sumcheck.PolyStmt R deg n)
          (ctx₂ := fun _ _ => Sumcheck.fullSpec R deg n)
          (roles₂ := fun _ _ => Sumcheck.fullRoles R deg n)
          (oracleDeco₂ := fun _ _ => fullOD n)
          (StmtOut := fun _ _ _ => Option (RoundClaim R))
          (ιₛₒ := fun _ _ _ => Unit)
          (OStatementOut := fun _ _ _ => Sumcheck.PolyFamily R deg (n + 1))
          (WitOut := fun _ _ _ => Sumcheck.PolyStmt R deg 0)
          (roundContinuationStateful
            (R := R) (deg := deg) D
            (totalVars := n + 1) n sampleChallenge)
          { prover := fun st sWithOracles w => do
              let tail := tailContinuationStateful D (n + 1) sampleChallenge n
              let input' :
                  StatementWithOracles
                    (fun _ => Option (RoundClaim R))
                    (fun _ => Sumcheck.PolyFamily R deg (n + 1)) PUnit.unit :=
                ⟨sWithOracles.stmt, sWithOracles.oracleStmt⟩
              let remapOutput :
                  (tr : Spec.Transcript (Sumcheck.fullSpec R deg n)) →
                  HonestProverOutput
                    (StatementWithOracles
                      (fun _ => Option (RoundClaim R))
                      (fun _ => Sumcheck.PolyFamily R deg (n + 1)) PUnit.unit)
                    (Sumcheck.PolyStmt R deg 0) →
                  HonestProverOutput
                    (StatementWithOracles
                      (fun _ => Option (RoundClaim R))
                      (fun _ => Sumcheck.PolyFamily R deg (n + 1)) st)
                    (Sumcheck.PolyStmt R deg 0)
                | _, ⟨stmtOut, witOut⟩ => ⟨⟨stmtOut.stmt, stmtOut.oracleStmt⟩, witOut⟩
              let strat ← tail.prover PUnit.unit input' w
              pure <| Spec.Strategy.mapOutputWithRoles remapOutput strat
            verifier := fun _ {_} accSpec stmt =>
              (tailContinuationStateful D (n + 1) sampleChallenge n).verifier
                PUnit.unit accSpec stmt
            simulate := fun _ tr =>
              (tailContinuationStateful D (n + 1) sampleChallenge n).simulate
                PUnit.unit tr }
      simpa [Sumcheck.fullSpec, Sumcheck.fullRoles, fullOD, Spec.replicate_succ] using cont

/-- The canonical `n`-round oracle-native sum-check protocol.

The prover and verifier interact across `n` replicated rounds, but the oracle
statement stays fixed as the original polynomial in `n` variables. The output
statement is the terminal live claim, or `none` after the first rejecting
round. -/
noncomputable def sumcheckReduction
    {ι : Type} {oSpec : OracleSpec ι}
    (n : Nat)
    {m_dom : Nat} (D : Fin m_dom → R)
    (sampleChallenge : OracleComp oSpec R) :
    OracleReduction oSpec
      (RoundClaim R)
      (fun _ => Sumcheck.fullSpec R deg n)
      (fun _ => Sumcheck.fullRoles R deg n)
      (fun _ => fullOD n)
      (fun _ => PUnit)
      (fun _ => Sumcheck.PolyFamily R deg n)
      (fun _ => PUnit)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg n)
      (fun _ _ => PUnit) :=
  (sumcheckContinuation (R := R) (deg := deg) n D sampleChallenge).promoteStatementToShared
    PUnit.unit

/-- The canonical `n`-round oracle-native sum-check protocol with a private
residual polynomial witness threaded across rounds. The public oracle statement
still stays fixed as the original polynomial in `n` variables. -/
noncomputable def sumcheckReductionStateful
    {ι : Type} {oSpec : OracleSpec ι}
    (n : Nat)
    {m_dom : Nat} (D : Fin m_dom → R)
    (sampleChallenge : OracleComp oSpec R) :
    OracleReduction oSpec
      (RoundClaim R)
      (fun _ => Sumcheck.fullSpec R deg n)
      (fun _ => Sumcheck.fullRoles R deg n)
      (fun _ => fullOD n)
      (fun _ => PUnit)
      (fun _ => Sumcheck.PolyFamily R deg n)
      (fun _ => Sumcheck.PolyStmt R deg n)
      (fun _ _ => Option (RoundClaim R))
      (fun _ _ => Sumcheck.PolyFamily R deg n)
      (fun _ _ => Sumcheck.PolyStmt R deg 0) :=
  (sumcheckContinuationStateful (R := R) (deg := deg) n D sampleChallenge).promoteStatementToShared
    PUnit.unit

/-! ## Security placeholders

The canonical object is now an oracle-native continuation composition over a
fixed original polynomial oracle. Completeness and soundness should be restated
against the oracle-side security APIs once that layer is upgraded for the new
sum-check surface.
-/

omit [Nontrivial R] in
theorem sumcheckReduction_completeness
    {ι : Type} {oSpec : OracleSpec ι}
    (n : Nat)
    {m_dom : Nat} (D : Fin m_dom → R)
    (poly : Sumcheck.PolyStmt R deg n)
    (_sampleChallenge : OracleComp oSpec R)
    (target : RoundClaim R) (_hValid : fullSum R deg D poly = target) :
    True := by
  trivial

omit [Nontrivial R] in
theorem sumcheckReduction_soundness
    {ι : Type} {oSpec : OracleSpec ι}
    {m : Type → Type} [Monad m] [MonadLiftT m SPMF] [LawfulMonadLiftT m SPMF]
    (n : Nat)
    {m_dom : Nat} (D : Fin m_dom → R)
    (poly : Sumcheck.PolyStmt R deg n)
    (_sampleChallenge : OracleComp oSpec R)
    (target : RoundClaim R) (_hInvalid : fullSum R deg D poly ≠ target) :
    True := by
  trivial

end

end

end Sumcheck
