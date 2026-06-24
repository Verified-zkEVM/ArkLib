/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Security.Basic

open Interaction.TwoParty

/-!
# Soundness for Interactive Verifiers
-/

noncomputable section

open OracleComp
open scoped NNReal ENNReal

universe u v w

namespace Interaction

/-! ## Soundness -/

namespace Verifier

/-- A verifier satisfies **soundness** with error `ε` if for all malicious
provers and invalid shared inputs/local statements, the probability that the
verifier produces an output in `langOut` is at most `ε`. The output language
`langOut` specifies which verifier outputs are considered acceptance.

Soundness is a property of the verifier alone — no honest prover appears.
The prover can use any output type and any strategy. -/
def soundness
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {StatementIn : SharedIn → Type w}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type u}
    (verifier : Verifier m SharedIn Context Roles StatementIn StatementOut)
    (langIn : ∀ shared, Set (StatementIn shared))
    (langOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementOut shared tr))
    (ε : ℝ≥0∞) : Prop :=
  ∀ (shared : SharedIn),
  ∀ {OutputP : Spec.Transcript (Context shared) → Type u},
  ∀ (prover : Spec.StrategyOver (pairedSyntax m)
    Interaction.TwoParty.Participant.focal (Context shared) (Roles shared) OutputP),
  ∀ (stmt : StatementIn shared), stmt ∉ langIn shared →
    Pr[fun z => z.2.2 ∈ langOut shared z.1
      | Verifier.run verifier shared stmt prover] ≤ ε

/-- Soundness is monotone in the error bound. -/
theorem soundness_error_mono
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {StatementIn : SharedIn → Type w}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type u}
    {verifier : Verifier m SharedIn Context Roles StatementIn StatementOut}
    {langIn : ∀ shared, Set (StatementIn shared)}
    {langOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementOut shared tr)}
    {ε₁ ε₂ : ℝ≥0∞}
    (hε : ε₁ ≤ ε₂) :
    soundness verifier langIn langOut ε₁ →
      soundness verifier langIn langOut ε₂ := by
  intro h shared _ prover stmt hInvalid
  exact le_trans (h shared prover stmt hInvalid) hε

/-- Soundness is contravariant in the input language: enlarging the accepted
input language shrinks the invalid-input set that soundness must handle. -/
theorem soundness_langIn_mono
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {StatementIn : SharedIn → Type w}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type u}
    {verifier : Verifier m SharedIn Context Roles StatementIn StatementOut}
    {langIn₁ langIn₂ : ∀ shared, Set (StatementIn shared)}
    {langOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementOut shared tr)}
    {ε : ℝ≥0∞}
    (hLangIn : ∀ shared, langIn₁ shared ⊆ langIn₂ shared) :
    soundness verifier langIn₁ langOut ε →
      soundness verifier langIn₂ langOut ε := by
  intro h shared _ prover stmt hInvalid
  exact h shared prover stmt (fun hValid => hInvalid (hLangIn shared hValid))

/-- Soundness is monotone under strengthening the output language event. -/
theorem soundness_langOut_mono
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {StatementIn : SharedIn → Type w}
    {StatementOut : (shared : SharedIn) → Spec.Transcript (Context shared) → Type u}
    {verifier : Verifier m SharedIn Context Roles StatementIn StatementOut}
    {langIn : ∀ shared, Set (StatementIn shared)}
    {langOut₁ langOut₂ : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      Set (StatementOut shared tr)}
    {ε : ℝ≥0∞}
    (hLangOut : ∀ shared tr, langOut₂ shared tr ⊆ langOut₁ shared tr) :
    soundness verifier langIn langOut₁ ε →
      soundness verifier langIn langOut₂ ε := by
  intro h shared _ prover stmt hInvalid
  refine le_trans ?_ (h shared prover stmt hInvalid)
  apply probEvent_mono
  intro z _ hz
  exact hLangOut shared z.1 hz

/-- Soundness composes at the verifier level. -/
theorem soundness_comp
    {m : Type u → Type u} [Monad m] [LawfulMonad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {StatementIn : SharedIn → Type w}
    {ctx₁ : SharedIn → Spec}
    {roles₁ : (shared : SharedIn) → RoleDecoration (ctx₁ shared)}
    {StmtMid : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Type u}
    {ctx₂ : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Spec}
    {roles₂ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      RoleDecoration (ctx₂ shared tr₁)}
    {StmtOut : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      Spec.Transcript (ctx₂ shared tr₁) → Type u}
    {langIn : ∀ shared, Set (StatementIn shared)}
    {langMid : ∀ (shared : SharedIn) (tr₁ : Spec.Transcript (ctx₁ shared)),
      Set (StmtMid shared tr₁)}
    {langOut : ∀ (shared : SharedIn) (tr₁ : Spec.Transcript (ctx₁ shared))
      (tr₂ : Spec.Transcript (ctx₂ shared tr₁)), Set (StmtOut shared tr₁ tr₂)}
    (verifier1 : Verifier m SharedIn ctx₁ roles₁ StatementIn StmtMid)
    (verifier2 : Verifier m
      ((shared : SharedIn) × StatementIn shared × Spec.Transcript (ctx₁ shared))
      (fun shared => ctx₂ shared.1 shared.2.2)
      (fun shared => roles₂ shared.1 shared.2.2)
      (fun shared => StmtMid shared.1 shared.2.2)
      (fun shared tr₂ => StmtOut shared.1 shared.2.2 tr₂))
    {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : Verifier.soundness verifier1 langIn langMid ε₁)
    (h₂ : Verifier.soundness verifier2
      (fun shared => langMid shared.1 shared.2.2)
      (fun shared tr₂ => langOut shared.1 shared.2.2 tr₂)
      ε₂) :
    Verifier.soundness
      (StatementOut := fun shared =>
        Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared))
      (fun shared stmt =>
        TwoParty.Counterpart.append
          (verifier1 shared stmt)
          (fun tr₁ sMid => verifier2 ⟨shared, stmt, tr₁⟩ sMid))
      langIn
      (fun shared tr =>
        {sOut | Spec.Transcript.liftAppendPred (ctx₁ shared) (ctx₂ shared) (StmtOut shared)
          (fun tr₁ tr₂ sOut => sOut ∈ langOut shared tr₁ tr₂) tr sOut})
      (ε₁ + ε₂) := by
  intro shared OutputP prover stmt hs
  change Spec.Transcript ((ctx₁ shared).append (ctx₂ shared)) → Type u at OutputP
  change Spec.StrategyOver (pairedSyntax m) Interaction.TwoParty.Participant.focal
    ((ctx₁ shared).append (ctx₂ shared))
    ((roles₁ shared).append (roles₂ shared)) OutputP at prover
  let prefixProver :
      Spec.StrategyOver (pairedSyntax m) Interaction.TwoParty.Participant.focal
        (ctx₁ shared) (roles₁ shared) (fun tr₁ =>
        Spec.StrategyOver (pairedSyntax m) Interaction.TwoParty.Participant.focal
          (ctx₂ shared tr₁) (roles₂ shared tr₁)
          (fun tr₂ => OutputP (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂))) :=
    TwoParty.Focal.splitPrefix
      (s₂ := ctx₂ shared) (r₁ := roles₁ shared) (r₂ := roles₂ shared) prover
  let mx :
      m ((tr₁ : Spec.Transcript (ctx₁ shared)) ×
        Spec.StrategyOver (pairedSyntax m) Interaction.TwoParty.Participant.focal
          (ctx₂ shared tr₁) (roles₂ shared tr₁)
          (fun tr₂ => OutputP (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)) ×
        StmtMid shared tr₁) :=
    TwoParty.run (ctx₁ shared) (roles₁ shared) prefixProver
      (verifier1 shared stmt)
  let my :
      ((tr₁ : Spec.Transcript (ctx₁ shared)) ×
        Spec.StrategyOver (pairedSyntax m) Interaction.TwoParty.Participant.focal
          (ctx₂ shared tr₁) (roles₂ shared tr₁)
          (fun tr₂ =>
            OutputP (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)) ×
        StmtMid shared tr₁) →
      m ((tr : Spec.Transcript ((ctx₁ shared).append (ctx₂ shared))) ×
        OutputP tr × Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr) :=
    fun z₁ => do
      let packOut :
          ((tr₂ : Spec.Transcript (ctx₂ shared z₁.1)) ×
            OutputP (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) z₁.1 tr₂) ×
            StmtOut shared z₁.1 tr₂) →
          ((tr : Spec.Transcript ((ctx₁ shared).append (ctx₂ shared))) ×
            OutputP tr ×
            Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr) :=
        fun z₂ => ⟨Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) z₁.1 z₂.1,
          z₂.2.1,
          Spec.Transcript.packAppend
            (ctx₁ shared) (ctx₂ shared) (StmtOut shared) z₁.1 z₂.1 z₂.2.2⟩
      packOut <$> TwoParty.run (ctx₂ shared z₁.1) (roles₂ shared z₁.1) z₁.2.1
        (verifier2 ⟨shared, stmt, z₁.1⟩ z₁.2.2)
  let bad₁ :
      ((tr₁ : Spec.Transcript (ctx₁ shared)) ×
        Spec.StrategyOver (pairedSyntax m) Interaction.TwoParty.Participant.focal
          (ctx₂ shared tr₁) (roles₂ shared tr₁)
          (fun tr₂ =>
            OutputP (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)) ×
        StmtMid shared tr₁) → Prop :=
    fun z₁ => z₁.2.2 ∉ langMid shared z₁.1
  let inLangOut :
      ((tr : Spec.Transcript ((ctx₁ shared).append (ctx₂ shared))) ×
        OutputP tr ×
        Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr) → Prop :=
    fun z =>
      let splitTr := Spec.Transcript.split (ctx₁ shared) (ctx₂ shared) z.1
      let sOut :=
        Spec.Transcript.unliftAppend
          (ctx₁ shared) (ctx₂ shared) (StmtOut shared) z.1 z.2.2
      sOut ∈ langOut shared splitTr.1 splitTr.2
  have h₁_bad : Pr[fun z₁ => ¬ bad₁ z₁ | mx] ≤ ε₁ := by
    simpa [mx, bad₁, prefixProver, Verifier.soundness] using
      h₁ shared (prover := prefixProver) stmt hs
  have h₂_bad :
      ∀ z₁ ∈ support mx, bad₁ z₁ → Pr[fun z => ¬¬ inLangOut z | my z₁] ≤ ε₂ := by
    intro z₁ _ hz₁
    rcases z₁ with ⟨tr₁, strat₂, sMid⟩
    let prover₂ : (sMid' : StmtMid shared tr₁) →
        Spec.StrategyOver (pairedSyntax m) Interaction.TwoParty.Participant.focal
          (ctx₂ shared tr₁) (roles₂ shared tr₁)
          (fun tr₂ =>
            OutputP (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)) :=
      fun _ => strat₂
    let packOut :
        ((tr₂ : Spec.Transcript (ctx₂ shared tr₁)) ×
          OutputP (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂) ×
          StmtOut shared tr₁ tr₂) →
        ((tr : Spec.Transcript ((ctx₁ shared).append (ctx₂ shared))) ×
          OutputP tr ×
          Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr) :=
      fun z₂ => ⟨Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ z₂.1,
        z₂.2.1,
        Spec.Transcript.packAppend
          (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr₁ z₂.1 z₂.2.2⟩
    have hpack :
        inLangOut ∘ packOut = fun z => z.2.2 ∈ langOut shared tr₁ z.1 := by
      funext z
      rcases z with ⟨tr₂, outP, sOut⟩
      let tr := Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂
      simpa [inLangOut, packOut, tr] using
        (Spec.Transcript.rel_unliftAppend_append
          (ctx₁ shared) (ctx₂ shared) (StmtOut shared) (fun _ _ => PUnit)
          (fun tr₁ tr₂ sOut _ => sOut ∈ langOut shared tr₁ tr₂)
          tr₁ tr₂ sOut PUnit.unit)
    have hmy :
        my ⟨tr₁, strat₂, sMid⟩ =
          packOut <$> TwoParty.run (ctx₂ shared tr₁) (roles₂ shared tr₁) strat₂
            (verifier2 ⟨shared, stmt, tr₁⟩ sMid) := by
      simp [my, packOut]
    simpa [Verifier.soundness, bad₁, hmy, hpack, prover₂, probEvent_map] using
      h₂ ⟨shared, stmt, tr₁⟩ strat₂ sMid hz₁
  have hbind : Pr[inLangOut | mx >>= my] ≤ ε₁ + ε₂ := by
    simpa using
      (probEvent_bind_le_add (mx := mx) (my := my)
        (p := bad₁) (q := fun z => ¬ inLangOut z) h₁_bad h₂_bad)
  let verifierAppend :
      Verifier m SharedIn
        (fun shared => (ctx₁ shared).append (ctx₂ shared))
        (fun shared => (roles₁ shared).append (roles₂ shared))
        StatementIn
        (fun shared => Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared)) :=
    fun shared stmt =>
      TwoParty.Counterpart.append
        (verifier1 shared stmt)
        (fun tr₁ sMid => verifier2 ⟨shared, stmt, tr₁⟩ sMid)
  have hrun :
      Verifier.run verifierAppend shared stmt prover =
        mx >>= my := by
    let mappedStep :
        (tr₁ : Spec.Transcript (ctx₁ shared)) → StmtMid shared tr₁ →
        Spec.StrategyOver (pairedSyntax m) Interaction.TwoParty.Participant.counterpart
          (ctx₂ shared tr₁) (roles₂ shared tr₁)
          (fun tr₂ =>
            Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared)
              (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)) :=
      fun tr₁ sMid =>
        TwoParty.Counterpart.mapOutput
          (fun tr₂ sOut =>
            Spec.Transcript.packAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr₁ tr₂ sOut)
          (verifier2 ⟨shared, stmt, tr₁⟩ sMid)
    have hverifier :
        verifierAppend shared stmt =
        TwoParty.Counterpart.appendFlat (verifier1 shared stmt) mappedStep := by
      simp only [verifierAppend, mappedStep]
      exact TwoParty.Counterpart.append_eq_appendFlat_mapOutput
        (verifier1 shared stmt) (fun tr₁ sMid => verifier2 ⟨shared, stmt, tr₁⟩ sMid)
    let myMapped :
        ((tr₁ : Spec.Transcript (ctx₁ shared)) ×
          Spec.StrategyOver (pairedSyntax m) Interaction.TwoParty.Participant.focal
            (ctx₂ shared tr₁) (roles₂ shared tr₁)
            (fun tr₂ =>
              OutputP (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)) ×
          StmtMid shared tr₁) →
        m ((tr : Spec.Transcript ((ctx₁ shared).append (ctx₂ shared))) ×
          OutputP tr ×
          Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr) :=
      fun z₁ =>
        (fun z₂ =>
          ⟨Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) z₁.1 z₂.1, z₂.2.1, z₂.2.2⟩) <$>
          TwoParty.run (ctx₂ shared z₁.1) (roles₂ shared z₁.1) z₁.2.1
            (mappedStep z₁.1 z₁.2.2)
    have hrun' := TwoParty.run_compFlat_appendFlat_pure
      (strat₁ := prefixProver)
      (f := fun _ strat₂ => strat₂)
      (cpt₁ := verifier1 shared stmt)
      (cpt₂ := mappedStep)
    have hmap :
        myMapped = my := by
      funext z₁
      rcases z₁ with ⟨tr₁, strat₂, sMid⟩
      let packStmt :
          (tr₂ : Spec.Transcript (ctx₂ shared tr₁)) → StmtOut shared tr₁ tr₂ →
            Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared)
              (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂) :=
        fun tr₂ sOut =>
          Spec.Transcript.packAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr₁ tr₂ sOut
      have hrunMap :
          TwoParty.run
              (ctx₂ shared tr₁) (roles₂ shared tr₁) strat₂ (mappedStep tr₁ sMid) =
            (fun z => ⟨z.1, z.2.1, packStmt z.1 z.2.2⟩) <$>
              TwoParty.run (ctx₂ shared tr₁) (roles₂ shared tr₁) strat₂
                (verifier2 ⟨shared, stmt, tr₁⟩ sMid) := by
        simpa [mappedStep, packStmt, TwoParty.Focal.mapOutput_id] using
          (TwoParty.run_mapOutput_mapOutput
            (fP := fun _ outP => outP) (fC := packStmt) strat₂
            (verifier2 ⟨shared, stmt, tr₁⟩ sMid))
      simp [myMapped, my, hrunMap, packStmt]
    calc
      Verifier.run verifierAppend shared stmt prover = mx >>= myMapped := by
        simpa [verifierAppend, Verifier.run, hverifier, prefixProver, mx, myMapped,
          TwoParty.Focal.compFlat_splitPrefix] using hrun'
      _ = mx >>= my := by
        refine congrArg (fun k => mx >>= k) hmap
  have hconv : inLangOut = fun z =>
      Spec.Transcript.liftAppendPred (ctx₁ shared) (ctx₂ shared) (StmtOut shared)
        (fun tr₁ tr₂ sOut => sOut ∈ langOut shared tr₁ tr₂) z.1 z.2.2 :=
    funext fun z => propext
      (Spec.Transcript.liftAppendPred_iff (ctx₁ shared) (ctx₂ shared) (StmtOut shared)
        (fun tr₁ tr₂ sOut => sOut ∈ langOut shared tr₁ tr₂) z.1 z.2.2).symm
  have haccept :
      Pr[fun z =>
          Spec.Transcript.liftAppendPred (ctx₁ shared) (ctx₂ shared) (StmtOut shared)
            (fun tr₁ tr₂ sOut => sOut ∈ langOut shared tr₁ tr₂) z.1 z.2.2
        | Verifier.run verifierAppend shared stmt prover] ≤ ε₁ + ε₂ := by
    simpa [hconv, hrun] using hbind
  simpa [Verifier.soundness, verifierAppend] using haccept

end Verifier

end Interaction

end

