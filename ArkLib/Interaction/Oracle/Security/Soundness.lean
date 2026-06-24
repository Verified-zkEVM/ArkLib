/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Security.Basic

open Interaction.TwoParty

/-!
# Oracle Soundness

Verifier-side soundness definitions for `Interaction.Oracle`.
-/

noncomputable section

open OracleComp
open scoped ENNReal

namespace Interaction
namespace Oracle
namespace Verifier

abbrev InputLanguage
    {SharedIn : Type _}
    {StatementIn : SharedIn → Type _}
    {ιₛᵢ : SharedIn → Type _}
    (OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type _)
    [∀ shared i, OracleInterface (OStatementIn shared i)] :=
  (shared : SharedIn) →
  StatementIn shared →
  InputImpl OStatementIn shared →
  Prop

abbrev OutputLanguage
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
  StatementOut shared pt →
  OutputImpl (Context := Context) (OracleDeco := OracleDeco)
    OStatementIn OStatementOut shared pt →
  Prop

/-- Soundness for an oracle verifier. The verifier is run against an arbitrary
prover strategy and invalid input behavior, and the probability of producing an
output in the target language is bounded by `ε`. -/
def soundness
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
    (verifier : Oracle.Verifier oSpec SharedIn Context Roles OracleDeco StatementIn
      OStatementIn StatementOut OStatementOut)
    (langIn : InputLanguage (StatementIn := StatementIn) (OStatementIn := OStatementIn))
    (langOut :
      OutputLanguage (Context := Context) (OracleDeco := OracleDeco)
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
          langOut shared inputImpl pt z.2.2.1
            (verifier.simulate shared pt)
          | verifier.run shared stmt inputImpl prover] ≤ ε

/-- Soundness is monotone in the error bound. -/
theorem soundness_error_mono
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
    {verifier : Oracle.Verifier oSpec SharedIn Context Roles OracleDeco StatementIn
      OStatementIn StatementOut OStatementOut}
    {langIn :
      InputLanguage (StatementIn := StatementIn) (OStatementIn := OStatementIn)}
    {langOut :
      OutputLanguage (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)}
    {ε₁ ε₂ : ℝ≥0∞}
    (hε : ε₁ ≤ ε₂) :
    soundness verifier langIn langOut ε₁ →
      soundness verifier langIn langOut ε₂ := by
  intro h shared stmt inputImpl _ prover hInvalid
  exact le_trans (h shared stmt inputImpl prover hInvalid) hε

/-- Soundness is contravariant in the input language: enlarging the accepted
input language shrinks the invalid-input set that soundness must handle. -/
theorem soundness_langIn_mono
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
    {verifier : Oracle.Verifier oSpec SharedIn Context Roles OracleDeco StatementIn
      OStatementIn StatementOut OStatementOut}
    {langIn₁ langIn₂ :
      InputLanguage (StatementIn := StatementIn) (OStatementIn := OStatementIn)}
    {langOut :
      OutputLanguage (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)}
    {ε : ℝ≥0∞}
    (hLangIn : ∀ shared stmt inputImpl,
      langIn₁ shared stmt inputImpl → langIn₂ shared stmt inputImpl) :
    soundness verifier langIn₁ langOut ε →
      soundness verifier langIn₂ langOut ε := by
  intro h shared stmt inputImpl _ prover hInvalid
  exact h shared stmt inputImpl prover
    (fun hValid => hInvalid (hLangIn shared stmt inputImpl hValid))

/-- Soundness is monotone under strengthening the output language event. -/
theorem soundness_langOut_mono
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
    {verifier : Oracle.Verifier oSpec SharedIn Context Roles OracleDeco StatementIn
      OStatementIn StatementOut OStatementOut}
    {langIn :
      InputLanguage (StatementIn := StatementIn) (OStatementIn := OStatementIn)}
    {langOut₁ langOut₂ :
      OutputLanguage (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)}
    {ε : ℝ≥0∞}
    (hLangOut : ∀ shared inputImpl pt stmtOut outputImpl,
      langOut₂ shared inputImpl pt stmtOut outputImpl →
        langOut₁ shared inputImpl pt stmtOut outputImpl) :
    soundness verifier langIn langOut₁ ε →
      soundness verifier langIn langOut₂ ε := by
  intro h shared stmt inputImpl _ prover hInvalid
  refine le_trans ?_ (h shared stmt inputImpl prover hInvalid)
  apply probEvent_mono
  intro z _ hz
  exact hLangOut shared inputImpl ((Context shared).projectPublic z.1) z.2.2.1
    (verifier.simulate shared ((Context shared).projectPublic z.1)) hz

end Verifier
end Oracle
end Interaction

