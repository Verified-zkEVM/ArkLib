/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Security.Completeness
import ArkLib.Interaction.Oracle.Security.KnowledgeSoundness

open Interaction.TwoParty

/-!
# Concrete Reification for Oracle.Spec Protocols

This module adds optional concrete-oracle packaging on top of the behavior-first
`Interaction.Oracle.Security.Basic` behavior layer.

The relative layer treats input and output oracles as query implementations.
Reification packages concrete oracle statements when a protocol consumer wants
plain statement languages and relations over `StatementWithOracles`.
-/

noncomputable section

open OracleComp
open scoped ENNReal

namespace Interaction
namespace Oracle

/-! ## Reduction-side concrete packaging -/

namespace Reduction

/-- Query-level agreement between a reduction's output-oracle simulation and a
concrete output oracle family, relative to a concrete input oracle statement. -/
def SimulatesConcrete
    {ι : Type _} {oSpec : OracleSpec ι}
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
    (reduction : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (shared : SharedIn)
    (oStatementIn : OracleStatement (OStatementIn shared))
    (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec)
    (oStatementOut :
      OracleStatement (OStatementOut shared ((Context shared).projectPublic tr))) :
    Prop :=
  OutputRealizes shared
    (OracleInterface.simOracle0 (OStatementIn shared) oStatementIn)
    tr
    (reduction.verifier.simulate shared ((Context shared).projectPublic tr))
    oStatementOut

@[simp]
theorem simulatesConcrete_iff_outputRealizes
    {ι : Type _} {oSpec : OracleSpec ι}
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
    (reduction : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (shared : SharedIn)
    (oStatementIn : OracleStatement (OStatementIn shared))
    (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec)
    (oStatementOut :
      OracleStatement (OStatementOut shared ((Context shared).projectPublic tr))) :
    SimulatesConcrete reduction shared oStatementIn tr oStatementOut ↔
      OutputRealizes shared
        (OracleInterface.simOracle0 (OStatementIn shared) oStatementIn)
        tr
        (reduction.verifier.simulate shared ((Context shared).projectPublic tr))
        oStatementOut :=
  Iff.rfl

/-- Optional materialization of a reduction's output oracle family. -/
structure Reification
    {ι : Type _} {oSpec : OracleSpec ι}
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
    (reduction : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut) where
  reify : (shared : SharedIn) →
    OracleStatement (OStatementIn shared) →
    (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec) →
      Option (OracleStatement
        (OStatementOut shared ((Context shared).projectPublic tr)))
  correct : ∀ (shared : SharedIn)
      (oStatementIn : OracleStatement (OStatementIn shared))
      (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec)
      (oStatementOut :
        OracleStatement (OStatementOut shared ((Context shared).projectPublic tr))),
      reify shared oStatementIn tr = some oStatementOut →
        SimulatesConcrete reduction shared oStatementIn tr oStatementOut

/-- Concrete reduction output with materialized output oracle statements. -/
abbrev Output
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _)
    (shared : SharedIn)
    (pt : Spec.PublicTranscript (Context shared)) :=
  StatementWithOracles
    (fun _ => StatementOut shared pt)
    (fun _ => OStatementOut shared pt)
    shared

/-- Package a plain output statement together with reified output-oracle data. -/
def output
    {ι : Type _} {oSpec : OracleSpec ι}
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
    {reduction : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut}
    (reification : Reification reduction)
    (shared : SharedIn)
    (oStatementIn : OracleStatement (OStatementIn shared))
    (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec)
    (stmtOut : StatementOut shared ((Context shared).projectPublic tr)) :
    Option
      (Output (Context := Context) (StatementOut := StatementOut)
        OStatementOut shared ((Context shared).projectPublic tr)) := do
  let oStatementOut ← reification.reify shared oStatementIn tr
  pure ⟨stmtOut, oStatementOut⟩

/-- Turn a concrete input relation into the behavior-first input relation by
existentially choosing concrete input oracle statements realizing the input
implementation. -/
def inputRelationOfRelation
    {SharedIn : Type _}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    (relIn : ∀ (shared : SharedIn),
      StatementWithOracles StatementIn OStatementIn shared →
        WitnessIn shared → Prop) :
    InputRelation (StatementIn := StatementIn) (OStatementIn := OStatementIn)
      WitnessIn :=
  fun shared stmt inputImpl wit =>
    ∃ oStatementIn : OracleStatement (OStatementIn shared),
      OracleStatement.Realizes inputImpl oStatementIn ∧
        relIn shared ⟨stmt, oStatementIn⟩ wit

/-- Turn a concrete output relation into the behavior-first output relation.
Concrete realization of the output oracle is checked separately by
`Reduction.completeness`, where the full transcript is available. -/
def outputRelationOfRelation
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
    (relOut : ∀ (shared : SharedIn) (pt : Spec.PublicTranscript (Context shared)),
      StatementWithOracles
          (fun _ => StatementOut shared pt) (fun _ => OStatementOut shared pt) shared →
        WitnessOut shared pt → Prop) :
    OutputRelation (Context := Context) (OracleDeco := OracleDeco)
      (StatementOut := StatementOut)
      (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
      WitnessOut :=
  fun shared _inputImpl pt stmtOut _outputImpl witOut =>
    ∃ oStatementOut : OracleStatement (OStatementOut shared pt),
      relOut shared pt ⟨stmtOut, oStatementOut⟩ witOut

/-- Concrete-view completeness, derived from the behavior-first completeness
definition plus its built-in output-realization check. -/
def reifiedCompleteness
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
    (reduction : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (relIn : ∀ (shared : SharedIn),
      StatementWithOracles StatementIn OStatementIn shared →
        WitnessIn shared → Prop)
    (relOut : ∀ (shared : SharedIn) (pt : Spec.PublicTranscript (Context shared)),
      StatementWithOracles
          (fun _ => StatementOut shared pt) (fun _ => OStatementOut shared pt) shared →
        WitnessOut shared pt → Prop)
    (ε : ℝ≥0∞) : Prop :=
  completeness reduction
    (inputRelationOfRelation relIn)
    (outputRelationOfRelation
      (Context := Context) (OracleDeco := OracleDeco)
      (StatementOut := StatementOut)
      (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
      relOut)
    ε

/-- Concrete-view perfect completeness. -/
def reifiedPerfectCompleteness
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
    (reduction : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut)
    (relIn : ∀ (shared : SharedIn),
      StatementWithOracles StatementIn OStatementIn shared →
        WitnessIn shared → Prop)
    (relOut : ∀ (shared : SharedIn) (pt : Spec.PublicTranscript (Context shared)),
      StatementWithOracles
          (fun _ => StatementOut shared pt) (fun _ => OStatementOut shared pt) shared →
        WitnessOut shared pt → Prop) : Prop :=
  reifiedCompleteness reduction relIn relOut 0

end Reduction

/-! ## Verifier-side concrete packaging -/

namespace Verifier

/-- Concrete input language for verifier-side oracle semantics. -/
abbrev ReifiedInputLanguage
    {SharedIn : Type _}
    (StatementIn : SharedIn → Type _)
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _) :=
  ∀ shared, Set (StatementWithOracles StatementIn OStatementIn shared)

/-- Concrete output language for verifier-side oracle semantics. -/
abbrev ReifiedOutputLanguage
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    (StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _)
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _) :=
  ∀ (shared : SharedIn) (pt : Spec.PublicTranscript (Context shared)),
    Set (StatementWithOracles
      (fun _ => StatementOut shared pt) (fun _ => OStatementOut shared pt) shared)

/-- Concrete witness-bearing input relation for verifier knowledge soundness. -/
abbrev ReifiedInputRelation
    {SharedIn : Type _}
    (StatementIn : SharedIn → Type _)
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    (WitnessIn : SharedIn → Type _) :=
  ∀ shared, Set (StatementWithOracles StatementIn OStatementIn shared × WitnessIn shared)

/-- Concrete witness-bearing output relation for verifier knowledge soundness. -/
abbrev ReifiedOutputRelation
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    (StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _)
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _)
    (WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _) :=
  ∀ (shared : SharedIn) (pt : Spec.PublicTranscript (Context shared)),
    Set (StatementWithOracles
      (fun _ => StatementOut shared pt) (fun _ => OStatementOut shared pt) shared ×
        WitnessOut shared pt)

/-- Query-level agreement between a verifier's output-oracle simulation and a
concrete output oracle family, relative to a concrete input oracle statement. -/
def SimulatesConcrete
    {ι : Type _} {oSpec : OracleSpec ι}
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
    (verifier : Oracle.Verifier oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn StatementOut OStatementOut)
    (shared : SharedIn)
    (oStatementIn : OracleStatement (OStatementIn shared))
    (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec)
    (oStatementOut :
      OracleStatement (OStatementOut shared ((Context shared).projectPublic tr))) :
    Prop :=
  OutputRealizes shared
    (OracleInterface.simOracle0 (OStatementIn shared) oStatementIn)
    tr
    (verifier.simulate shared ((Context shared).projectPublic tr))
    oStatementOut

@[simp]
theorem simulatesConcrete_iff_outputRealizes
    {ι : Type _} {oSpec : OracleSpec ι}
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
    (verifier : Oracle.Verifier oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn StatementOut OStatementOut)
    (shared : SharedIn)
    (oStatementIn : OracleStatement (OStatementIn shared))
    (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec)
    (oStatementOut :
      OracleStatement (OStatementOut shared ((Context shared).projectPublic tr))) :
    SimulatesConcrete verifier shared oStatementIn tr oStatementOut ↔
      OutputRealizes shared
        (OracleInterface.simOracle0 (OStatementIn shared) oStatementIn)
        tr
        (verifier.simulate shared ((Context shared).projectPublic tr))
        oStatementOut :=
  Iff.rfl

/-- Optional materialization of a verifier's output oracle family. -/
structure Reification
    {ι : Type _} {oSpec : OracleSpec ι}
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
    (verifier : Oracle.Verifier oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn StatementOut OStatementOut) where
  reify : (shared : SharedIn) →
    OracleStatement (OStatementIn shared) →
    (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec) →
      Option (OracleStatement
        (OStatementOut shared ((Context shared).projectPublic tr)))
  correct : ∀ (shared : SharedIn)
      (oStatementIn : OracleStatement (OStatementIn shared))
      (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec)
      (oStatementOut :
        OracleStatement (OStatementOut shared ((Context shared).projectPublic tr))),
      reify shared oStatementIn tr = some oStatementOut →
        SimulatesConcrete verifier shared oStatementIn tr oStatementOut

/-- Concrete verifier output with materialized output oracle statements. -/
abbrev Output
    {SharedIn : Type _}
    {Context : SharedIn → Spec}
    (StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _)
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type _}
    (OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type _)
    (shared : SharedIn)
    (pt : Spec.PublicTranscript (Context shared)) :=
  StatementWithOracles
    (fun _ => StatementOut shared pt)
    (fun _ => OStatementOut shared pt)
    shared

/-- Package a plain output statement together with reified oracle data. -/
def output
    {ι : Type _} {oSpec : OracleSpec ι}
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
    {verifier : Oracle.Verifier oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn StatementOut OStatementOut}
    (reification : Reification verifier)
    (shared : SharedIn)
    (oStatementIn : OracleStatement (OStatementIn shared))
    (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec)
    (stmtOut : StatementOut shared ((Context shared).projectPublic tr)) :
    Option (Output (Context := Context) StatementOut OStatementOut shared
      ((Context shared).projectPublic tr)) := do
  let oStatementOut ← reification.reify shared oStatementIn tr
  pure ⟨stmtOut, oStatementOut⟩

/-- A concrete input language as a behavior-first input language. -/
def inputLanguageOfReifiedLanguage
    {SharedIn : Type _}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    (langIn : ReifiedInputLanguage StatementIn OStatementIn) :
    InputLanguage (StatementIn := StatementIn) (OStatementIn := OStatementIn) :=
  fun shared stmt inputImpl =>
    ∃ oStatementIn : OracleStatement (OStatementIn shared),
      OracleStatement.Realizes inputImpl oStatementIn ∧
        ⟨stmt, oStatementIn⟩ ∈ langIn shared

/-- A concrete output language as a behavior-first output language.

This adapter only forgets concrete output oracle data into an existential
plain predicate at a public transcript. Query-level realization of the verifier
simulation depends on the full transcript and is therefore handled by the
direct `reifiedSoundness` event rather than by this public-transcript-only
adapter. -/
def outputLanguageOfReifiedLanguage
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
      ReifiedOutputLanguage (Context := Context)
        (StatementOut := StatementOut) OStatementOut) :
    OutputLanguage (Context := Context) (OracleDeco := OracleDeco)
      (StatementOut := StatementOut)
      (OStatementIn := OStatementIn) (OStatementOut := OStatementOut) :=
  fun shared _inputImpl pt stmtOut _outputImpl =>
    ∃ oStatementOut : OracleStatement (OStatementOut shared pt),
      ⟨stmtOut, oStatementOut⟩ ∈ langOut shared pt

/-- A concrete witness-bearing input relation as a behavior-first relation. -/
def inputRelationOfReifiedRelation
    {SharedIn : Type _}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type _}
    (relIn : ReifiedInputRelation StatementIn OStatementIn WitnessIn) :
    Reduction.InputRelation (StatementIn := StatementIn)
      (OStatementIn := OStatementIn) WitnessIn :=
  fun shared stmt inputImpl wit =>
    ∃ oStatementIn : OracleStatement (OStatementIn shared),
      OracleStatement.Realizes inputImpl oStatementIn ∧
        (⟨stmt, oStatementIn⟩, wit) ∈ relIn shared

/-- A concrete witness-bearing output relation as a behavior-first relation.

As with `outputLanguageOfReifiedLanguage`, this adapter cannot mention the full
transcript, so it records only the existential concrete output relation at the
public transcript. Direct reified games carry the stronger full-transcript
realization check explicitly. -/
def outputRelationOfReifiedRelation
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
      ReifiedOutputRelation (Context := Context)
        (StatementOut := StatementOut) OStatementOut WitnessOut) :
    Reduction.OutputRelation (Context := Context) (OracleDeco := OracleDeco)
      (StatementOut := StatementOut)
      (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
      WitnessOut :=
  fun shared _inputImpl pt stmtOut _outputImpl witOut =>
    ∃ oStatementOut : OracleStatement (OStatementOut shared pt),
      (⟨stmtOut, oStatementOut⟩, witOut) ∈ relOut shared pt

/-- Concrete-language soundness. The event is direct over verifier execution so
the concrete output oracle must realize the verifier's simulation at the full
transcript that was actually sampled. -/
def reifiedSoundness
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
    (verifier : Oracle.Verifier oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn StatementOut OStatementOut)
    (langIn : ReifiedInputLanguage StatementIn OStatementIn)
    (langOut :
      ReifiedOutputLanguage (Context := Context)
        (StatementOut := StatementOut) OStatementOut)
    (ε : ℝ≥0∞) : Prop :=
  ∀ (shared : SharedIn) (stmt : StatementIn shared)
      (inputImpl : InputImpl OStatementIn shared)
      {OutputP : Interaction.Spec.Transcript
        (Context shared).toInteractionSpec → Type _}
      (prover : Interaction.Spec.StrategyOver (pairedSyntax (OracleComp oSpec))
        Interaction.TwoParty.Participant.focal
        (Context shared).toInteractionSpec
        ((Context shared).toSpecRoles (Roles shared)) OutputP),
      ¬ inputLanguageOfReifiedLanguage langIn shared stmt inputImpl →
        Pr[fun z =>
          let pt := (Context shared).projectPublic z.1
          ∃ oStatementOut : OracleStatement (OStatementOut shared pt),
            OutputRealizes shared inputImpl z.1
              (verifier.simulate shared pt)
              oStatementOut ∧
            ⟨z.2.2.1, oStatementOut⟩ ∈ langOut shared pt
          | verifier.run shared stmt inputImpl prover] ≤ ε

/-- Concrete-language knowledge soundness. The output oracle realization check
is direct over the sampled full transcript, while the extractor target is the
behavior-first input relation induced by the concrete input relation. -/
def reifiedKnowledgeSoundness
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
    (verifier : Oracle.Verifier oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn StatementOut OStatementOut)
    (relIn : ReifiedInputRelation StatementIn OStatementIn WitnessIn)
    (relOut :
      ReifiedOutputRelation (Context := Context)
        (StatementOut := StatementOut) OStatementOut WitnessOut)
    (ε : ℝ≥0∞) : Prop :=
  ∃ extractor : Reduction.Extractor.Straightline
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
        ∃ oStatementOut : OracleStatement (OStatementOut shared pt),
          OutputRealizes shared inputImpl z.1
            (verifier.simulate shared pt)
            oStatementOut ∧
          (⟨z.2.2.1, oStatementOut⟩, witOut) ∈ relOut shared pt ∧
          ¬ inputRelationOfReifiedRelation relIn shared stmt inputImpl
            (extractor shared stmt inputImpl z.1 z.2.2.1
              (verifier.simulate shared pt) witOut)
        | verifier.run shared stmt inputImpl prover] ≤ ε

/-- Concrete reified knowledge soundness implies concrete reified soundness
when invalid concrete inputs admit no witness and accepted concrete outputs
admit a transcript-indexed witness selector. -/
theorem reifiedKnowledgeSoundness_implies_reifiedSoundness
    {ι : Type _} {oSpec : OracleSpec.{0, 0} ι}
    [LawfulMonad (OracleComp oSpec)] [HasEvalSPMF (OracleComp oSpec)]
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
    {verifier : Oracle.Verifier oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn StatementOut OStatementOut}
    {relIn : ReifiedInputRelation StatementIn OStatementIn WitnessIn}
    {relOut :
      ReifiedOutputRelation (Context := Context)
        (StatementOut := StatementOut) OStatementOut WitnessOut}
    {ε : ℝ≥0∞}
    (hKS : reifiedKnowledgeSoundness verifier relIn relOut ε)
    (langIn : ReifiedInputLanguage StatementIn OStatementIn)
    (hLang :
      ∀ shared (s : StatementWithOracles StatementIn OStatementIn shared),
        s ∉ langIn shared → ∀ w, (s, w) ∉ relIn shared)
    (langOut :
      ReifiedOutputLanguage (Context := Context)
        (StatementOut := StatementOut) OStatementOut)
    (acceptWitness :
      ∀ (shared : SharedIn)
        (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec),
        WitnessOut shared ((Context shared).projectPublic tr))
    (hLangOut :
      ∀ shared
        (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec)
        (sOut :
          StatementWithOracles
            (fun _ => StatementOut shared ((Context shared).projectPublic tr))
            (fun _ => OStatementOut shared ((Context shared).projectPublic tr))
            shared),
        sOut ∈ langOut shared ((Context shared).projectPublic tr) →
          (sOut, acceptWitness shared tr) ∈
            relOut shared ((Context shared).projectPublic tr)) :
    reifiedSoundness verifier langIn langOut ε := by
  rcases hKS with ⟨extractor, hKS⟩
  intro shared stmt inputImpl OutputP prover hs
  let proverKS :
      Interaction.Spec.StrategyOver (pairedSyntax (OracleComp oSpec))
        Interaction.TwoParty.Participant.focal
        (Context shared).toInteractionSpec
        ((Context shared).toSpecRoles (Roles shared))
        (fun tr => WitnessOut shared ((Context shared).projectPublic tr)) :=
    Interaction.TwoParty.Focal.mapOutput
      (fun tr _ => acceptWitness shared tr) prover
  have hrun :
      verifier.run shared stmt inputImpl proverKS =
        (fun z => ⟨z.1, acceptWitness shared z.1, z.2.2⟩) <$>
          verifier.run shared stmt inputImpl prover := by
    simp only [proverKS]
    rw [Verifier.run_mapOutput]
  have hKS' := hKS shared stmt inputImpl proverKS
  rw [hrun, probEvent_map] at hKS'
  refine le_trans ?_ hKS'
  refine probEvent_mono ?_
  intro z _ hz
  rcases hz with ⟨oStatementOut, hRealizes, hOut⟩
  refine ⟨oStatementOut, hRealizes, hLangOut shared z.1 ⟨z.2.2.1, oStatementOut⟩ hOut, ?_⟩
  intro hInputRel
  rcases hInputRel with ⟨oStatementIn, hInputRealizes, hRelIn⟩
  exact
    hLang shared ⟨stmt, oStatementIn⟩
      (by
        intro hIn
        exact hs ⟨oStatementIn, hInputRealizes, hIn⟩)
      (extractor shared stmt inputImpl z.1 z.2.2.1
        (verifier.simulate shared ((Context shared).projectPublic z.1))
        (acceptWitness shared z.1))
      hRelIn

end Verifier

end Oracle
end Interaction

