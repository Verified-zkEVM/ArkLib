/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Program
import ArkLib.Interaction.Oracle.Security.Completeness
import ArkLib.Interaction.Oracle.Security.KnowledgeSoundness

open Interaction.TwoParty

/-!
# Security notions for programmatic oracle verifiers

Additive security definitions for the experimental verifier-program layer. The
existing split-verifier security files stay unchanged.
-/

noncomputable section

open OracleComp
open scoped ENNReal

namespace Interaction
namespace Oracle

/-- Query-level agreement stated directly for a packaged terminal verifier
output. -/
def TerminalOutputRealizes
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (shared : SharedIn)
    (inputImpl : InputImpl OStatementIn shared)
    (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec)
    (terminal :
      Verifier.TerminalOutput SharedIn Context OracleDeco OStatementIn
        StatementOut OStatementOut shared ((Context shared).projectPublic tr))
    (oStatementOut :
      OracleStatement (OStatementOut shared ((Context shared).projectPublic tr))) :
    Prop :=
  OutputRealizes shared inputImpl tr terminal.simulate oStatementOut

namespace Reduction

/-- Output relation stated on the packaged terminal verifier output. -/
abbrev TerminalOutputRelation
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _)
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _) :=
  (shared : SharedIn) →
  (inputImpl : InputImpl OStatementIn shared) →
  (pt : Spec.PublicTranscript (Context shared)) →
  Verifier.TerminalOutput SharedIn Context OracleDeco OStatementIn
    StatementOut OStatementOut shared pt →
  WitnessOut shared pt →
  Prop

namespace OutputRelation

/-- View a legacy split output relation as a relation on terminal outputs. -/
def toTerminal
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    (relOut :
      OutputRelation (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
        WitnessOut) :
    TerminalOutputRelation (Context := Context) (OracleDeco := OracleDeco)
      (StatementOut := StatementOut)
      (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
      WitnessOut :=
  fun shared inputImpl pt terminal witOut =>
    relOut shared inputImpl pt terminal.stmt terminal.simulate witOut

end OutputRelation

namespace Extractor

/-- A straightline extractor whose verifier-side input is the packaged terminal
output, rather than the legacy split `(statement, simulate)` pair. -/
structure StraightlineTerminal
    (SharedIn : Type _)
    (Context : SharedIn → Spec)
    (OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared))
    (StatementIn : SharedIn → Type _)
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (WitnessIn : SharedIn → Type _)
    (StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _)
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _)
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _) where
  toFun : ∀ (shared : SharedIn)
      (_stmt : StatementIn shared)
      (_inputImpl : InputImpl OStatementIn shared)
      (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec),
      Verifier.TerminalOutput SharedIn Context OracleDeco OStatementIn
          StatementOut OStatementOut shared ((Context shared).projectPublic tr) →
        WitnessOut shared ((Context shared).projectPublic tr) → WitnessIn shared

instance
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _} :
    CoeFun
      (StraightlineTerminal
        (SharedIn := SharedIn) (Context := Context) (OracleDeco := OracleDeco)
        (StatementIn := StatementIn) (OStatementIn := OStatementIn)
        (WitnessIn := WitnessIn) (StatementOut := StatementOut)
        (OStatementOut := OStatementOut) (WitnessOut := WitnessOut))
      (fun _ => ∀ (shared : SharedIn)
        (_stmt : StatementIn shared)
        (_inputImpl : InputImpl OStatementIn shared)
        (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec),
        Verifier.TerminalOutput SharedIn Context OracleDeco OStatementIn
            StatementOut OStatementOut shared ((Context shared).projectPublic tr) →
          WitnessOut shared ((Context shared).projectPublic tr) →
            WitnessIn shared) where
  coe E := E.toFun

namespace Straightline

/-- View a legacy split extractor as a terminal-output extractor. -/
def toTerminal
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    (extractor : Straightline SharedIn Context OracleDeco StatementIn
      OStatementIn WitnessIn StatementOut OStatementOut WitnessOut) :
    StraightlineTerminal SharedIn Context OracleDeco StatementIn
      OStatementIn WitnessIn StatementOut OStatementOut WitnessOut where
  toFun := fun shared stmt inputImpl tr terminal witOut =>
    extractor shared stmt inputImpl tr terminal.stmt terminal.simulate witOut

end Straightline
end Extractor
end Reduction

namespace Verifier

/-- Output language stated directly on the packaged terminal verifier output. -/
abbrev TerminalOutputLanguage
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _)
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)] :=
  (shared : SharedIn) →
  (inputImpl : InputImpl OStatementIn shared) →
  (pt : Spec.PublicTranscript (Context shared)) →
  Oracle.Verifier.TerminalOutput SharedIn Context OracleDeco OStatementIn
    StatementOut OStatementOut shared pt →
  Prop

namespace OutputLanguage

/-- View a legacy split output language as a terminal-output language. -/
def toTerminal
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (langOut :
      OutputLanguage (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)) :
    TerminalOutputLanguage (Context := Context) (OracleDeco := OracleDeco)
      (StatementOut := StatementOut)
      (OStatementIn := OStatementIn) (OStatementOut := OStatementOut) :=
  fun shared inputImpl pt terminal =>
    langOut shared inputImpl pt terminal.stmt terminal.simulate

end OutputLanguage

/-- Completeness stated against the packaged terminal verifier output. -/
def terminalCompleteness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    (reduction : Oracle.Reduction.Programmatic oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (relIn :
      Reduction.InputRelation (StatementIn := StatementIn) (OStatementIn := OStatementIn)
        WitnessIn)
    (relOut :
      Reduction.TerminalOutputRelation (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
        WitnessOut)
    (ε : ℝ≥0∞) : Prop :=
  ∀ (shared : SharedIn)
    (s : StatementWithOracles StatementIn OStatementIn shared)
    (w : WitnessIn shared),
      relIn shared s.stmt
        (OracleInterface.simOracle0 (OStatementIn shared) s.oracleStmt) w →
        let inputImpl := OracleInterface.simOracle0 (OStatementIn shared) s.oracleStmt
        1 - ε ≤ Pr[fun z =>
          let pt := (Context shared).projectPublic z.1
          z.2.1.stmt.stmt = z.2.2.stmt ∧
            TerminalOutputRealizes shared inputImpl z.1 z.2.2
              z.2.1.stmt.oracleStmt ∧
            relOut shared inputImpl pt z.2.2 z.2.1.wit
          | reduction.executeConcrete shared s w]

/-- Perfect terminal completeness: terminal completeness with error `0`. -/
def perfectTerminalCompleteness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    (reduction : Oracle.Reduction.Programmatic oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (relIn :
      Reduction.InputRelation (StatementIn := StatementIn) (OStatementIn := OStatementIn)
        WitnessIn)
    (relOut :
      Reduction.TerminalOutputRelation (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
        WitnessOut) : Prop :=
  terminalCompleteness reduction relIn relOut 0

/-- Terminal soundness for a verifier whose leaf returns a packaged terminal
output. -/
def terminalSoundness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    (verifier : Oracle.Verifier.Programmatic oSpec SharedIn Context Roles
      OracleDeco StatementIn OStatementIn StatementOut OStatementOut)
    (langIn : InputLanguage (StatementIn := StatementIn) (OStatementIn := OStatementIn))
    (langOut :
      TerminalOutputLanguage (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut))
    (ε : ℝ≥0∞) : Prop :=
  ∀ (shared : SharedIn) (stmt : StatementIn shared)
      (inputImpl : InputImpl OStatementIn shared)
      {OutputP : Interaction.Spec.Transcript
        (Context shared).toInteractionSpec → Type _}
      (prover : Interaction.Spec.StrategyOver (pairedSyntax (OracleComp oSpec))
        Interaction.TwoParty.Participant.focal
        (Context shared).toInteractionSpec
        ((Context shared).toSpecRoles (Roles shared)) OutputP),
      ¬ langIn shared stmt inputImpl →
        Pr[fun z =>
          let pt := (Context shared).projectPublic z.1
          langOut shared inputImpl pt z.2.2
          | verifier.run shared stmt inputImpl prover] ≤ ε

/-- Knowledge soundness for a verifier whose leaf returns a packaged terminal
output. The extractor receives that terminal output as a single semantic
object. -/
def terminalKnowledgeSoundness
    {ι : Type _} {oSpec : OracleSpec ι} [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    (verifier : Oracle.Verifier.Programmatic oSpec SharedIn Context Roles
      OracleDeco StatementIn OStatementIn StatementOut OStatementOut)
    (relIn :
      Reduction.InputRelation (StatementIn := StatementIn)
        (OStatementIn := OStatementIn) WitnessIn)
    (relOut :
      Reduction.TerminalOutputRelation (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
        WitnessOut)
    (ε : ℝ≥0∞) : Prop :=
  ∃ extractor : Reduction.Extractor.StraightlineTerminal
      SharedIn Context OracleDeco StatementIn OStatementIn WitnessIn
      StatementOut OStatementOut WitnessOut,
  ∀ (shared : SharedIn) (stmt : StatementIn shared)
      (inputImpl : InputImpl OStatementIn shared)
      (prover : Interaction.Spec.StrategyOver (pairedSyntax (OracleComp oSpec))
        Interaction.TwoParty.Participant.focal
        (Context shared).toInteractionSpec
        ((Context shared).toSpecRoles (Roles shared))
        (fun tr => WitnessOut shared ((Context shared).projectPublic tr))),
      Pr[fun z =>
        let pt := (Context shared).projectPublic z.1
        let witOut := z.2.1
        relOut shared inputImpl pt z.2.2 witOut ∧
          ¬ relIn shared stmt inputImpl
            (extractor shared stmt inputImpl z.1 z.2.2 witOut)
        | verifier.run shared stmt inputImpl prover] ≤ ε

end Verifier
end Oracle
end Interaction
