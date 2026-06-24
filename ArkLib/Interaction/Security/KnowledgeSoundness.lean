/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Security.Soundness

open Interaction.TwoParty

/-!
# Knowledge Soundness for Interactive Verifiers
-/

noncomputable section

open OracleComp
open scoped NNReal ENNReal

universe u v w

namespace Interaction

/-! ## Knowledge soundness -/

namespace Extractor

/-- A straightline extractor for a transcript-indexed interaction. It observes the
shared input, local statement, public transcript, and both terminal outputs,
and reconstructs an input witness. -/
structure Straightline
    (SharedIn : Type v)
    (StatementIn WitnessIn : SharedIn → Type w)
    (Context : SharedIn → Spec)
    (StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (Context shared) → Type u) where
  toFun : ∀ (shared : SharedIn) (_stmt : StatementIn shared)
      (tr : Spec.Transcript (Context shared)),
      StatementOut shared tr → WitnessOut shared tr → WitnessIn shared

instance
    {SharedIn : Type v}
    {StatementIn WitnessIn : SharedIn → Type w}
    {Context : SharedIn → Spec}
    {StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (Context shared) → Type u} :
    CoeFun
      (Straightline SharedIn StatementIn WitnessIn Context StatementOut WitnessOut)
      (fun _ => ∀ (shared : SharedIn) (_stmt : StatementIn shared)
        (tr : Spec.Transcript (Context shared)),
        StatementOut shared tr → WitnessOut shared tr → WitnessIn shared) where
  coe E := E.toFun

end Extractor

namespace Verifier

/-- A verifier satisfies **knowledge soundness** with error `ε` if there exists
an extractor that, given the shared input, local statement, transcript, and
both outputs, recovers a valid input witness whenever the output is in `relOut`.
The bound says: the probability that the output is in `relOut` but the
extracted input witness is not in `relIn` is at most `ε`. -/
def knowledgeSoundness
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {StatementIn WitnessIn : SharedIn → Type w}
    {StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (Context shared) → Type u}
    (verifier : Verifier m SharedIn Context Roles StatementIn StatementOut)
    (relIn : ∀ shared, Set (StatementIn shared × WitnessIn shared))
    (relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementOut shared tr × WitnessOut shared tr))
    (ε : ℝ≥0∞) : Prop :=
  ∃ extractor :
      Extractor.Straightline SharedIn StatementIn WitnessIn Context StatementOut WitnessOut,
  ∀ (shared : SharedIn)
      (stmt : StatementIn shared)
      (prover : Spec.StrategyOver (pairedSyntax m)
        Interaction.TwoParty.Participant.focal (Context shared) (Roles shared)
        (WitnessOut shared)),
      Pr[fun z =>
        (z.2.2, z.2.1) ∈ relOut shared z.1 ∧
          (stmt, extractor shared stmt z.1 z.2.2 z.2.1) ∉ relIn shared
        | Verifier.run verifier shared stmt prover] ≤ ε

/-- Knowledge soundness is monotone in the error bound. -/
theorem knowledgeSoundness_error_mono
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {StatementIn WitnessIn : SharedIn → Type w}
    {StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (Context shared) → Type u}
    {verifier : Verifier m SharedIn Context Roles StatementIn StatementOut}
    {relIn : ∀ shared, Set (StatementIn shared × WitnessIn shared)}
    {relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementOut shared tr × WitnessOut shared tr)}
    {ε₁ ε₂ : ℝ≥0∞}
    (hε : ε₁ ≤ ε₂) :
    knowledgeSoundness verifier relIn relOut ε₁ →
      knowledgeSoundness verifier relIn relOut ε₂ := by
  rintro ⟨extractor, hKS⟩
  refine ⟨extractor, ?_⟩
  intro shared stmt prover
  exact le_trans (hKS shared stmt prover) hε

/-- Knowledge soundness is monotone under enlarging the input relation:
the bad event `¬ relIn` becomes smaller. -/
theorem knowledgeSoundness_relIn_mono
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {StatementIn WitnessIn : SharedIn → Type w}
    {StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (Context shared) → Type u}
    {verifier : Verifier m SharedIn Context Roles StatementIn StatementOut}
    {relIn₁ relIn₂ : ∀ shared, Set (StatementIn shared × WitnessIn shared)}
    {relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementOut shared tr × WitnessOut shared tr)}
    {ε : ℝ≥0∞}
    (hRelIn : ∀ shared, relIn₁ shared ⊆ relIn₂ shared) :
    knowledgeSoundness verifier relIn₁ relOut ε →
      knowledgeSoundness verifier relIn₂ relOut ε := by
  rintro ⟨extractor, hKS⟩
  refine ⟨extractor, ?_⟩
  intro shared stmt prover
  refine le_trans ?_ (hKS shared stmt prover)
  apply probEvent_mono
  intro z _ hz
  refine ⟨hz.1, ?_⟩
  exact fun hIn => hz.2 (hRelIn shared hIn)

/-- Knowledge soundness is monotone under strengthening the output relation
event. -/
theorem knowledgeSoundness_relOut_mono
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {StatementIn WitnessIn : SharedIn → Type w}
    {StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (Context shared) → Type u}
    {verifier : Verifier m SharedIn Context Roles StatementIn StatementOut}
    {relIn : ∀ shared, Set (StatementIn shared × WitnessIn shared)}
    {relOut₁ relOut₂ : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementOut shared tr × WitnessOut shared tr)}
    {ε : ℝ≥0∞}
    (hRelOut : ∀ shared tr, relOut₂ shared tr ⊆ relOut₁ shared tr) :
    knowledgeSoundness verifier relIn relOut₁ ε →
      knowledgeSoundness verifier relIn relOut₂ ε := by
  rintro ⟨extractor, hKS⟩
  refine ⟨extractor, ?_⟩
  intro shared stmt prover
  refine le_trans ?_ (hKS shared stmt prover)
  apply probEvent_mono
  intro z _ hz
  exact ⟨hRelOut shared z.1 hz.1, hz.2⟩

/-- Knowledge soundness implies soundness under a transcript-indexed choice of
accepting witness. -/
theorem knowledgeSoundness_implies_soundness
    {m : Type u → Type u} [Monad m] [LawfulMonad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {StatementIn WitnessIn : SharedIn → Type w}
    {StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (Context shared) → Type u}
    {verifier : Verifier m SharedIn Context Roles StatementIn StatementOut}
    {relIn : ∀ shared, Set (StatementIn shared × WitnessIn shared)}
    {relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementOut shared tr × WitnessOut shared tr)}
    {ε : ℝ≥0∞}
    (hKS : knowledgeSoundness verifier relIn relOut ε)
    (langIn : ∀ shared, Set (StatementIn shared))
    (hLang : ∀ shared stmt, stmt ∉ langIn shared → ∀ w, (stmt, w) ∉ relIn shared)
    (langOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementOut shared tr))
    (acceptWitness : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      WitnessOut shared tr)
    (hLangOut : ∀ shared tr sOut,
      sOut ∈ langOut shared tr → (sOut, acceptWitness shared tr) ∈ relOut shared tr) :
    soundness verifier langIn langOut ε := by
  rcases hKS with ⟨extractor, hKS⟩
  intro shared OutputP prover stmt hs
  let proverKS :
      Spec.StrategyOver (pairedSyntax m) Interaction.TwoParty.Participant.focal
        (Context shared) (Roles shared) (WitnessOut shared) :=
    TwoParty.Focal.mapOutput
      (fun tr _ => acceptWitness shared tr) prover
  have hrun :
      Verifier.run verifier shared stmt proverKS =
        (fun z => ⟨z.1, acceptWitness shared z.1, z.2.2⟩) <$>
          Verifier.run verifier shared stmt prover := by
    simpa [Verifier.run, proverKS, TwoParty.Counterpart.mapOutput_id] using
      (TwoParty.run_mapOutput_mapOutput
        (fP := fun tr (_ : OutputP tr) => acceptWitness shared tr)
        (fC := fun _ sOut => sOut)
        prover (verifier shared stmt))
  let badFromAccept :
      ((tr : Spec.Transcript (Context shared)) × OutputP tr × StatementOut shared tr) → Prop :=
    fun z =>
      (z.2.2, acceptWitness shared z.1) ∈ relOut shared z.1 ∧
        (stmt, extractor shared stmt z.1 z.2.2 (acceptWitness shared z.1)) ∉ relIn shared
  have hKS' :
      Pr[badFromAccept | Verifier.run verifier shared stmt prover] ≤ ε := by
    simpa [badFromAccept, hrun, proverKS, probEvent_map] using
      hKS shared stmt proverKS
  have hmono :
      Pr[fun z => z.2.2 ∈ langOut shared z.1
          | Verifier.run verifier shared stmt prover] ≤
        Pr[badFromAccept | Verifier.run verifier shared stmt prover] := by
    apply probEvent_mono
    intro z _ hz
    exact ⟨hLangOut shared z.1 z.2.2 hz,
      hLang shared stmt hs (extractor shared stmt z.1 z.2.2 (acceptWitness shared z.1))⟩
  exact le_trans hmono hKS'

end Verifier

end Interaction

end

