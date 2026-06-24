/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Security.Soundness

open Interaction.TwoParty

/-!
# Oracle Knowledge Soundness

Straightline knowledge soundness and its implication to soundness.
-/

noncomputable section

open OracleComp
open scoped ENNReal

namespace Interaction
namespace Oracle
namespace Verifier

/-- Knowledge soundness for an `Oracle.Verifier`. The adversarial prover outputs
only a witness `witOut`; the extractor receives the input statement, input
oracle implementation, the **full transcript** `tr` (public transcript plus
concrete prover oracle messages), the verifier's output statement, the
verifier's output-oracle simulator, and `witOut`, and must produce a valid
input witness.

The bound is: `Pr[relOut(simulate, witOut) ∧ ¬ relIn(extractor …)] ≤ ε`.

The prover does **not** output concrete output oracle data: the output oracle's
semantics are defined by the verifier via `simulate`, not asserted by the
prover. -/
def knowledgeSoundness
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
    (verifier : Oracle.Verifier oSpec SharedIn Context Roles OracleDeco StatementIn
      OStatementIn StatementOut OStatementOut)
    (relIn :
      Reduction.InputRelation (StatementIn := StatementIn)
        (OStatementIn := OStatementIn) WitnessIn)
    (relOut :
      Reduction.OutputRelation (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
        WitnessOut)
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
        relOut shared inputImpl pt z.2.2.1
          (verifier.simulate shared pt) witOut ∧
          ¬ relIn shared stmt inputImpl
            (extractor shared stmt inputImpl z.1 z.2.2.1
              (verifier.simulate shared pt) witOut)
        | verifier.run shared stmt inputImpl prover] ≤ ε

/-- Knowledge soundness is monotone in the error bound. -/
theorem knowledgeSoundness_error_mono
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
    {verifier : Oracle.Verifier oSpec SharedIn Context Roles OracleDeco StatementIn
      OStatementIn StatementOut OStatementOut}
    {relIn :
      Reduction.InputRelation (StatementIn := StatementIn)
        (OStatementIn := OStatementIn) WitnessIn}
    {relOut :
      Reduction.OutputRelation (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
        WitnessOut}
    {ε₁ ε₂ : ℝ≥0∞}
    (hε : ε₁ ≤ ε₂) :
    knowledgeSoundness verifier relIn relOut ε₁ →
      knowledgeSoundness verifier relIn relOut ε₂ := by
  rintro ⟨extractor, hKS⟩
  refine ⟨extractor, ?_⟩
  intro shared stmt inputImpl prover
  exact le_trans (hKS shared stmt inputImpl prover) hε

/-- Knowledge soundness is monotone under enlarging the input relation:
the bad event `¬ relIn` becomes smaller. -/
theorem knowledgeSoundness_relIn_mono
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
    {verifier : Oracle.Verifier oSpec SharedIn Context Roles OracleDeco StatementIn
      OStatementIn StatementOut OStatementOut}
    {relIn₁ relIn₂ :
      Reduction.InputRelation (StatementIn := StatementIn)
        (OStatementIn := OStatementIn) WitnessIn}
    {relOut :
      Reduction.OutputRelation (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
        WitnessOut}
    {ε : ℝ≥0∞}
    (hRelIn : ∀ shared stmt inputImpl wit,
      relIn₁ shared stmt inputImpl wit →
        relIn₂ shared stmt inputImpl wit) :
    knowledgeSoundness verifier relIn₁ relOut ε →
      knowledgeSoundness verifier relIn₂ relOut ε := by
  rintro ⟨extractor, hKS⟩
  refine ⟨extractor, ?_⟩
  intro shared stmt inputImpl prover
  refine le_trans ?_ (hKS shared stmt inputImpl prover)
  apply probEvent_mono
  intro z _ hz
  refine ⟨hz.1, ?_⟩
  exact fun hIn =>
    hz.2 (hRelIn shared stmt inputImpl
      (extractor shared stmt inputImpl z.1 z.2.2.1
        (verifier.simulate shared ((Context shared).projectPublic z.1)) z.2.1)
      hIn)

/-- Knowledge soundness is monotone under strengthening the output relation
event. -/
theorem knowledgeSoundness_relOut_mono
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
    {verifier : Oracle.Verifier oSpec SharedIn Context Roles OracleDeco StatementIn
      OStatementIn StatementOut OStatementOut}
    {relIn :
      Reduction.InputRelation (StatementIn := StatementIn)
        (OStatementIn := OStatementIn) WitnessIn}
    {relOut₁ relOut₂ :
      Reduction.OutputRelation (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
        WitnessOut}
    {ε : ℝ≥0∞}
    (hRelOut : ∀ shared inputImpl pt stmtOut outputImpl witOut,
      relOut₂ shared inputImpl pt stmtOut outputImpl witOut →
        relOut₁ shared inputImpl pt stmtOut outputImpl witOut) :
    knowledgeSoundness verifier relIn relOut₁ ε →
      knowledgeSoundness verifier relIn relOut₂ ε := by
  rintro ⟨extractor, hKS⟩
  refine ⟨extractor, ?_⟩
  intro shared stmt inputImpl prover
  refine le_trans ?_ (hKS shared stmt inputImpl prover)
  apply probEvent_mono
  intro z _ hz
  refine ⟨?_, hz.2⟩
  exact hRelOut shared inputImpl ((Context shared).projectPublic z.1)
    z.2.2.1 (verifier.simulate shared ((Context shared).projectPublic z.1))
    z.2.1 hz.1

/-- Knowledge soundness implies soundness, under a transcript-indexed choice
of accepting witness.

The caller supplies:
- `acceptWitness`: for every transcript `tr`, a candidate output witness at
  `projectPublic tr`.
- `hLang`: outside the input language, no witness satisfies the input relation
  (this makes `hLang` applicable to the extractor's output).
- `hLangOut`: whenever the verifier's output is in `langOut`, the output
  relation holds for `acceptWitness` at that transcript.

The proof constructs a KS adversary from the soundness adversary by mapping
its output through `acceptWitness`. Since `acceptWitness` depends only on the
full transcript, this is a valid `TwoParty.Focal.mapOutput` map. The
`Verifier.run_mapOutput` lemma guarantees this does
not change the transcript or verifier-side output distribution. -/
theorem knowledgeSoundness_implies_soundness
    {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
    [LawfulMonad (OracleComp oSpec)] [HasEvalSPMF (OracleComp oSpec)]
    {SharedIn : Type}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → Spec.RoleDeco (Context shared)}
    {OracleDeco : (shared : SharedIn) → Spec.OracleDeco (Context shared)}
    {StatementIn : SharedIn → Type}
    {ιₛᵢ : SharedIn → Type}
    {OStatementIn : (shared : SharedIn) → ιₛᵢ shared → Type}
    [∀ shared i, OracleInterface (OStatementIn shared i)]
    {WitnessIn : SharedIn → Type}
    {StatementOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {ιₛₒ : (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {OStatementOut :
      (shared : SharedIn) → (pt : Spec.PublicTranscript (Context shared)) →
        ιₛₒ shared pt → Type}
    [∀ shared pt i, OracleInterface (OStatementOut shared pt i)]
    {WitnessOut :
      (shared : SharedIn) → Spec.PublicTranscript (Context shared) → Type}
    {verifier : Oracle.Verifier oSpec SharedIn Context Roles OracleDeco
      StatementIn OStatementIn StatementOut OStatementOut}
    {relIn :
      Reduction.InputRelation (StatementIn := StatementIn)
        (OStatementIn := OStatementIn) WitnessIn}
    {relOut :
      Reduction.OutputRelation (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut)
        WitnessOut}
    {ε : ℝ≥0∞}
    (hKS : knowledgeSoundness verifier relIn relOut ε)
    (langIn : InputLanguage (StatementIn := StatementIn)
      (OStatementIn := OStatementIn))
    (hLang :
      ∀ shared stmt inputImpl,
        ¬ langIn shared stmt inputImpl →
          ∀ w, ¬ relIn shared stmt inputImpl w)
    (langOut :
      OutputLanguage (Context := Context) (OracleDeco := OracleDeco)
        (StatementOut := StatementOut)
        (OStatementIn := OStatementIn) (OStatementOut := OStatementOut))
    (acceptWitness :
      ∀ (shared : SharedIn)
        (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec),
        WitnessOut shared ((Context shared).projectPublic tr))
    (hLangOut :
      ∀ shared inputImpl
        (tr : Interaction.Spec.Transcript (Context shared).toInteractionSpec)
        (stmtOut : StatementOut shared ((Context shared).projectPublic tr)),
        langOut shared inputImpl ((Context shared).projectPublic tr) stmtOut
          (verifier.simulate shared ((Context shared).projectPublic tr)) →
        relOut shared inputImpl ((Context shared).projectPublic tr) stmtOut
          (verifier.simulate shared ((Context shared).projectPublic tr))
          (acceptWitness shared tr)) :
    soundness verifier langIn langOut ε := by
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
  refine ⟨hLangOut shared inputImpl z.1 z.2.2.1 hz, ?_⟩
  exact hLang shared stmt inputImpl hs
    (extractor shared stmt inputImpl z.1 z.2.2.1
      (verifier.simulate shared ((Context shared).projectPublic z.1))
      (acceptWitness shared z.1))

end Verifier
end Oracle
end Interaction

