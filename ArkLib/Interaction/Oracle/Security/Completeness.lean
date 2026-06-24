/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Security.Basic

/-!
# Oracle Completeness

Honest completeness for `Interaction.Oracle.Reduction`.
-/

noncomputable section

open OracleComp
open scoped ENNReal

namespace Interaction
namespace Oracle
namespace Reduction

/-- Honest completeness for an `Oracle.Reduction`. The honest prover produces
concrete output oracle data `oStmtOut`, and we check three conditions:
1. The prover's output statement agrees with the verifier's.
2. `OutputRealizes`: the verifier's simulate agrees with the prover's concrete
   `oStmtOut`.
3. The output relation `relOut` holds. -/
def completeness
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
    (relIn :
      InputRelation (StatementIn := StatementIn) (OStatementIn := OStatementIn)
        WitnessIn)
    (relOut :
      OutputRelation (Context := Context) (OracleDeco := OracleDeco)
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
          z.2.1.stmt.stmt = z.2.2.1 ∧
            OutputRealizes shared inputImpl z.1
              (reduction.verifier.simulate shared pt)
              z.2.1.stmt.oracleStmt ∧
            relOut shared inputImpl pt z.2.2.1
              (reduction.verifier.simulate shared pt)
              z.2.1.wit
          | reduction.executeConcrete shared s w]

/-- Perfect completeness: completeness with error `0`. -/
def perfectCompleteness
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
    (relIn :
      InputRelation (StatementIn := StatementIn) (OStatementIn := OStatementIn)
        WitnessIn)
    (relOut :
      OutputRelation (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
        WitnessOut) : Prop :=
  completeness reduction relIn relOut 0

/-- Completeness is monotone in the error bound. -/
theorem completeness_error_mono
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
    {reduction : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut}
    {relIn :
      InputRelation (StatementIn := StatementIn) (OStatementIn := OStatementIn)
        WitnessIn}
    {relOut :
      OutputRelation (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
        WitnessOut}
    {ε₁ ε₂ : ℝ≥0∞}
    (hε : ε₁ ≤ ε₂) :
    completeness reduction relIn relOut ε₁ →
      completeness reduction relIn relOut ε₂ := by
  intro h shared s w hIn
  exact le_trans (tsub_le_tsub_left hε 1) (h shared s w hIn)

/-- Completeness is contravariant in the input relation. -/
theorem completeness_relIn_mono
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
    {reduction : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut}
    {relIn₁ relIn₂ :
      InputRelation (StatementIn := StatementIn) (OStatementIn := OStatementIn)
        WitnessIn}
    {relOut :
      OutputRelation (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
        WitnessOut}
    {ε : ℝ≥0∞}
    (hRelIn : ∀ shared stmt inputImpl wit,
      relIn₂ shared stmt inputImpl wit → relIn₁ shared stmt inputImpl wit) :
    completeness reduction relIn₁ relOut ε →
      completeness reduction relIn₂ relOut ε := by
  intro h shared s w hIn
  exact h shared s w
    (hRelIn shared s.stmt
      (OracleInterface.simOracle0 (OStatementIn shared) s.oracleStmt) w hIn)

/-- Completeness is covariant in the output relation. -/
theorem completeness_relOut_mono
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
    {reduction : Oracle.Reduction oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn WitnessIn StatementOut OStatementOut WitnessOut}
    {relIn :
      InputRelation (StatementIn := StatementIn) (OStatementIn := OStatementIn)
        WitnessIn}
    {relOut₁ relOut₂ :
      OutputRelation (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
        WitnessOut}
    {ε : ℝ≥0∞}
    (hRelOut : ∀ shared inputImpl pt stmtOut outputImpl witOut,
      relOut₁ shared inputImpl pt stmtOut outputImpl witOut →
        relOut₂ shared inputImpl pt stmtOut outputImpl witOut) :
    completeness reduction relIn relOut₁ ε →
      completeness reduction relIn relOut₂ ε := by
  intro h shared s w hIn
  refine le_trans (h shared s w hIn) ?_
  apply probEvent_mono
  intro z _ hz
  refine ⟨hz.1, hz.2.1, ?_⟩
  exact hRelOut shared
    (OracleInterface.simOracle0 (OStatementIn shared) s.oracleStmt)
    ((Context shared).projectPublic z.1) z.2.2.1
    (reduction.verifier.simulate shared ((Context shared).projectPublic z.1))
    z.2.1.wit hz.2.2

end Reduction
end Oracle
end Interaction
