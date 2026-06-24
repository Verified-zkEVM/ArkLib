/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Security.Basic

open Interaction.TwoParty

/-!
# Completeness for Interactive Reductions
-/

noncomputable section

open OracleComp
open scoped NNReal ENNReal

universe u v w

namespace Interaction

/-! ## Completeness -/

/-- A reduction satisfies **completeness** with error `ε` if for all valid
shared inputs, local statements, and witnesses, honest execution produces a
valid output with probability at least `1 - ε`. The honest prover and verifier
must agree on the output statement, and the verifier statement together with
the honest prover's witness output must satisfy `relOut`. -/
def Reduction.completeness
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {StatementIn WitnessIn : SharedIn → Type w}
    {StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (Context shared) → Type u}
    (reduction : Reduction m SharedIn Context Roles
      StatementIn WitnessIn StatementOut WitnessOut)
    (relIn : ∀ shared, StatementIn shared → WitnessIn shared → Prop)
    (relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      StatementOut shared tr → WitnessOut shared tr → Prop)
    (ε : ℝ≥0∞) : Prop :=
  ∀ (shared : SharedIn) (stmt : StatementIn shared) (wit : WitnessIn shared),
    relIn shared stmt wit →
      1 - ε ≤ Pr[fun z => z.2.1.stmt = z.2.2 ∧ relOut shared z.1 z.2.2 z.2.1.wit |
        reduction.execute shared stmt wit]

/-- Perfect completeness: completeness with error `0`. -/
def Reduction.perfectCompleteness
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {StatementIn WitnessIn : SharedIn → Type w}
    {StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (Context shared) → Type u}
    (reduction : Reduction m SharedIn Context Roles
      StatementIn WitnessIn StatementOut WitnessOut)
    (relIn : ∀ shared, StatementIn shared → WitnessIn shared → Prop)
    (relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      StatementOut shared tr → WitnessOut shared tr → Prop) : Prop :=
  reduction.completeness relIn relOut 0

/-- Completeness is monotone in the error bound. -/
theorem Reduction.completeness_error_mono
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {StatementIn WitnessIn : SharedIn → Type w}
    {StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (Context shared) → Type u}
    {reduction : Reduction m SharedIn Context Roles
      StatementIn WitnessIn StatementOut WitnessOut}
    {relIn : ∀ shared, StatementIn shared → WitnessIn shared → Prop}
    {relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      StatementOut shared tr → WitnessOut shared tr → Prop}
    {ε₁ ε₂ : ℝ≥0∞}
    (hε : ε₁ ≤ ε₂) :
    reduction.completeness relIn relOut ε₁ →
      reduction.completeness relIn relOut ε₂ := by
  intro h shared stmt wit hIn
  exact le_trans (tsub_le_tsub_left hε 1) (h shared stmt wit hIn)

/-- Completeness is contravariant in the input relation. -/
theorem Reduction.completeness_relIn_mono
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {StatementIn WitnessIn : SharedIn → Type w}
    {StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (Context shared) → Type u}
    {reduction : Reduction m SharedIn Context Roles
      StatementIn WitnessIn StatementOut WitnessOut}
    {relIn₁ relIn₂ : ∀ shared, StatementIn shared → WitnessIn shared → Prop}
    {relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      StatementOut shared tr → WitnessOut shared tr → Prop}
    {ε : ℝ≥0∞}
    (hRelIn : ∀ shared stmt wit,
      relIn₂ shared stmt wit → relIn₁ shared stmt wit) :
    reduction.completeness relIn₁ relOut ε →
      reduction.completeness relIn₂ relOut ε := by
  intro h shared stmt wit hIn
  exact h shared stmt wit (hRelIn shared stmt wit hIn)

/-- Completeness is covariant in the output relation. -/
theorem Reduction.completeness_relOut_mono
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {Context : SharedIn → Spec}
    {Roles : (shared : SharedIn) → RoleDecoration (Context shared)}
    {StatementIn WitnessIn : SharedIn → Type w}
    {StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (Context shared) → Type u}
    {reduction : Reduction m SharedIn Context Roles
      StatementIn WitnessIn StatementOut WitnessOut}
    {relIn : ∀ shared, StatementIn shared → WitnessIn shared → Prop}
    {relOut₁ relOut₂ : ∀ (shared : SharedIn) (tr : Spec.Transcript (Context shared)),
      StatementOut shared tr → WitnessOut shared tr → Prop}
    {ε : ℝ≥0∞}
    (hRelOut : ∀ shared tr stmtOut witOut,
      relOut₁ shared tr stmtOut witOut → relOut₂ shared tr stmtOut witOut) :
    reduction.completeness relIn relOut₁ ε →
      reduction.completeness relIn relOut₂ ε := by
  intro h shared stmt wit hIn
  refine le_trans (h shared stmt wit hIn) ?_
  apply probEvent_mono
  intro z _ hz
  exact ⟨hz.1, hRelOut shared z.1 z.2.2 z.2.1.wit hz.2⟩

/-- Completeness composes: if the first reduction is complete up to `ε₁`, and
the second stage is complete up to `ε₂` whenever the first stage succeeds, then
the composed reduction is complete up to `ε₁ + ε₂`. -/
theorem Reduction.completeness_comp
    {m : Type u → Type u} [Monad m] [TwoParty.LawfulCommMonad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {StatementIn : SharedIn → Type w}
    {WitnessIn : SharedIn → Type w}
    {ctx₁ : SharedIn → Spec}
    {roles₁ : (shared : SharedIn) → RoleDecoration (ctx₁ shared)}
    {StmtMid WitMid : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Type u}
    {ctx₂ : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Spec}
    {roles₂ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      RoleDecoration (ctx₂ shared tr₁)}
    {StmtOut WitOut : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      Spec.Transcript (ctx₂ shared tr₁) → Type u}
    {relIn : ∀ shared, StatementIn shared → WitnessIn shared → Prop}
    {relMid : ∀ (shared : SharedIn) (tr₁ : Spec.Transcript (ctx₁ shared)),
      StmtMid shared tr₁ → WitMid shared tr₁ → Prop}
    {relOut : ∀ (shared : SharedIn) (tr₁ : Spec.Transcript (ctx₁ shared))
      (tr₂ : Spec.Transcript (ctx₂ shared tr₁)),
      StmtOut shared tr₁ tr₂ → WitOut shared tr₁ tr₂ → Prop}
    (reduction1 : Reduction m SharedIn ctx₁ roles₁ StatementIn
      WitnessIn StmtMid WitMid)
    (reduction2 : Reduction m
      ((shared : SharedIn) × StatementIn shared × Spec.Transcript (ctx₁ shared))
      (fun shared => ctx₂ shared.1 shared.2.2)
      (fun shared => roles₂ shared.1 shared.2.2)
      (fun shared => StmtMid shared.1 shared.2.2)
      (fun shared => WitMid shared.1 shared.2.2)
      (fun shared tr₂ => StmtOut shared.1 shared.2.2 tr₂)
      (fun shared tr₂ => WitOut shared.1 shared.2.2 tr₂))
    {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : reduction1.completeness relIn relMid ε₁)
    (h₂ : reduction2.completeness
      (fun shared sMid wMid => relMid shared.1 shared.2.2 sMid wMid)
      (fun shared tr₂ sOut wOut => relOut shared.1 shared.2.2 tr₂ sOut wOut)
      ε₂) :
    (Reduction.comp reduction1 reduction2).completeness
      relIn
      (fun shared tr sOut wOut =>
        Spec.Transcript.liftAppendRel (ctx₁ shared) (ctx₂ shared) (StmtOut shared)
          (WitOut shared) (relOut shared) tr sOut wOut)
      (ε₁ + ε₂) := by
  intro shared stmt w hIn
  let mx : m ((tr₁ : Spec.Transcript (ctx₁ shared)) ×
      HonestProverOutput (StmtMid shared tr₁) (WitMid shared tr₁) × StmtMid shared tr₁) :=
    reduction1.execute shared stmt w
  let my :
      ((tr₁ : Spec.Transcript (ctx₁ shared)) ×
        HonestProverOutput (StmtMid shared tr₁) (WitMid shared tr₁) × StmtMid shared tr₁) →
      m ((tr : Spec.Transcript ((ctx₁ shared).append (ctx₂ shared))) ×
          HonestProverOutput
            (Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr)
            (Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (WitOut shared) tr) ×
          Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr) :=
    fun z₁ => do
      let strat₂ ← reduction2.prover ⟨shared, stmt, z₁.1⟩ z₁.2.1.stmt z₁.2.1.wit
      let ⟨tr₂, out, sOut⟩ ←
        TwoParty.run (ctx₂ shared z₁.1) (roles₂ shared z₁.1) strat₂
          (reduction2.verifier ⟨shared, stmt, z₁.1⟩ z₁.2.2)
      pure ⟨Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) z₁.1 tr₂,
        ⟨Spec.Transcript.packAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) z₁.1 tr₂ out.stmt,
          Spec.Transcript.packAppend (ctx₁ shared) (ctx₂ shared) (WitOut shared) z₁.1 tr₂ out.wit⟩,
        Spec.Transcript.packAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) z₁.1 tr₂ sOut⟩
  let good₁ :
      ((tr₁ : Spec.Transcript (ctx₁ shared)) ×
        HonestProverOutput (StmtMid shared tr₁) (WitMid shared tr₁) × StmtMid shared tr₁) → Prop :=
    fun z₁ => z₁.2.1.stmt = z₁.2.2 ∧ relMid shared z₁.1 z₁.2.2 z₁.2.1.wit
  let goodOut :
      ((tr : Spec.Transcript ((ctx₁ shared).append (ctx₂ shared))) ×
          HonestProverOutput
            (Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr)
            (Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (WitOut shared) tr) ×
          Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr) → Prop :=
    fun z =>
      z.2.1.stmt = z.2.2 ∧
        Spec.Transcript.liftAppendRel (ctx₁ shared) (ctx₂ shared) (StmtOut shared) (WitOut shared)
          (relOut shared) z.1 z.2.2 z.2.1.wit
  have h₁_success : 1 - ε₁ ≤ Pr[good₁ | mx] := by
    simpa [mx, good₁, Reduction.completeness] using h₁ shared stmt w hIn
  have h₂_success :
      ∀ z₁ ∈ support mx, good₁ z₁ → 1 - ε₂ ≤ Pr[goodOut | my z₁] := by
    intro z₁ _ hz₁
    rcases z₁ with ⟨tr₁, ⟨sMidP, wMid⟩, sMidV⟩
    rcases hz₁ with ⟨hEqMid, hRelMid⟩
    change sMidP = sMidV at hEqMid
    change relMid shared tr₁ sMidV wMid at hRelMid
    subst sMidV
    let packOut :
        ((tr₂ : Spec.Transcript (ctx₂ shared tr₁)) ×
          HonestProverOutput (StmtOut shared tr₁ tr₂) (WitOut shared tr₁ tr₂) ×
            StmtOut shared tr₁ tr₂) →
          ((tr : Spec.Transcript ((ctx₁ shared).append (ctx₂ shared))) ×
            HonestProverOutput
              (Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr)
              (Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (WitOut shared) tr) ×
            Spec.Transcript.liftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr) :=
      fun z => ⟨Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ z.1,
        ⟨Spec.Transcript.packAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr₁ z.1 z.2.1.stmt,
          Spec.Transcript.packAppend (ctx₁ shared) (ctx₂ shared) (WitOut shared) tr₁ z.1 z.2.1.wit⟩,
        Spec.Transcript.packAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr₁ z.1 z.2.2⟩
    have hpack :
        goodOut ∘ packOut =
          fun z => z.2.1.stmt = z.2.2 ∧ relOut shared tr₁ z.1 z.2.2 z.2.1.wit := by
      funext z
      rcases z with ⟨tr₂, ⟨sOutP, wOut⟩, sOutV⟩
      refine propext ?_
      constructor
      · intro hz
        refine ⟨?_, ?_⟩
        · have hEq := congrArg
            (Spec.Transcript.unpackAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr₁ tr₂)
            hz.1
          simpa [packOut, HonestProverOutput.stmt] using hEq
        · have hRel := (Spec.Transcript.liftAppendRel_iff
            (ctx₁ shared) (ctx₂ shared) (StmtOut shared) (WitOut shared) (relOut shared)
            (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)
            (Spec.Transcript.packAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr₁ tr₂ sOutV)
            (Spec.Transcript.packAppend (ctx₁ shared) (ctx₂ shared) (WitOut shared) tr₁ tr₂ wOut)).1
            hz.2
          have hRelEq :
              relOut shared
                (Spec.Transcript.split (ctx₁ shared) (ctx₂ shared)
                  (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)).1
                (Spec.Transcript.split (ctx₁ shared) (ctx₂ shared)
                  (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)).2
                (Spec.Transcript.unliftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared)
                  (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)
                  (Spec.Transcript.packAppend
                    (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr₁ tr₂ sOutV))
                (Spec.Transcript.unliftAppend (ctx₁ shared) (ctx₂ shared) (WitOut shared)
                  (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)
                  (Spec.Transcript.packAppend
                    (ctx₁ shared) (ctx₂ shared) (WitOut shared) tr₁ tr₂ wOut)) =
              relOut shared tr₁ tr₂ sOutV wOut := by
            simpa using
              (Spec.Transcript.rel_unliftAppend_append
                (ctx₁ shared) (ctx₂ shared) (StmtOut shared) (WitOut shared)
                (relOut shared) tr₁ tr₂ sOutV wOut)
          rw [hRelEq] at hRel
          exact hRel
      · rintro ⟨hEq, hRel⟩
        change sOutP = sOutV at hEq
        change relOut shared tr₁ tr₂ sOutV wOut at hRel
        refine ⟨by simp [packOut, hEq], ?_⟩
        exact (Spec.Transcript.liftAppendRel_iff
          (ctx₁ shared) (ctx₂ shared) (StmtOut shared) (WitOut shared) (relOut shared)
          (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)
          (Spec.Transcript.packAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr₁ tr₂ sOutV)
          (Spec.Transcript.packAppend (ctx₁ shared) (ctx₂ shared) (WitOut shared) tr₁ tr₂ wOut)).2
          (by
            have hRelEq :
                relOut shared
                  (Spec.Transcript.split (ctx₁ shared) (ctx₂ shared)
                    (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)).1
                  (Spec.Transcript.split (ctx₁ shared) (ctx₂ shared)
                    (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)).2
                  (Spec.Transcript.unliftAppend (ctx₁ shared) (ctx₂ shared) (StmtOut shared)
                    (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)
                    (Spec.Transcript.packAppend
                      (ctx₁ shared) (ctx₂ shared) (StmtOut shared) tr₁ tr₂ sOutV))
                  (Spec.Transcript.unliftAppend (ctx₁ shared) (ctx₂ shared) (WitOut shared)
                    (Spec.Transcript.append (ctx₁ shared) (ctx₂ shared) tr₁ tr₂)
                    (Spec.Transcript.packAppend
                      (ctx₁ shared) (ctx₂ shared) (WitOut shared) tr₁ tr₂ wOut)) =
                relOut shared tr₁ tr₂ sOutV wOut := by
              simpa using
                (Spec.Transcript.rel_unliftAppend_append
                  (ctx₁ shared) (ctx₂ shared) (StmtOut shared) (WitOut shared)
                  (relOut shared) tr₁ tr₂ sOutV wOut)
            rw [hRelEq]
            exact hRel)
    have hmy :
        my ⟨tr₁, ⟨sMidP, wMid⟩, sMidP⟩ =
          packOut <$> reduction2.execute ⟨shared, stmt, tr₁⟩ sMidP wMid := by
      simp [my, packOut, Reduction.execute,
        HonestProverOutput.stmt, HonestProverOutput.wit]
    simpa [hmy, hpack, probEvent_map] using h₂ ⟨shared, stmt, tr₁⟩ sMidP wMid hRelMid
  have hmul :
      (1 - ε₁) * (1 - ε₂) ≤ Pr[goodOut | mx >>= my] := by
    exact mul_le_probEvent_bind (mx := mx) (my := my) (p := good₁) (q := goodOut)
      h₁_success h₂_success
  have hsub :
      1 - (ε₁ + ε₂) ≤ (1 - ε₁) * (1 - ε₂) := by
    by_cases hε₁ : ε₁ ≤ 1
    · by_cases hε₂ : ε₂ ≤ 1
      · have hsum :
            1 = (ε₁ + ε₂ - ε₁ * ε₂) + (1 - ε₁) * (1 - ε₂) := by
          have := congrArg (fun z => z + (1 - ε₁) * (1 - ε₂))
            (ENNReal.one_sub_one_sub_mul_one_sub hε₁ hε₂)
          have hmul_le_one : (1 - ε₁) * (1 - ε₂) ≤ 1 := by
            calc
              (1 - ε₁) * (1 - ε₂) ≤ 1 * 1 := by
                exact mul_le_mul' (tsub_le_self) (tsub_le_self)
              _ = 1 := one_mul 1
          simpa [tsub_add_cancel_of_le hmul_le_one, add_comm, add_left_comm, add_assoc] using this
        have hne :
            (ε₁ + ε₂ - ε₁ * ε₂) ≠ ⊤ := by
          have hle_two : ε₁ + ε₂ - ε₁ * ε₂ ≤ (2 : ℝ≥0∞) := by
            calc
              ε₁ + ε₂ - ε₁ * ε₂ ≤ ε₁ + ε₂ := tsub_le_self
              _ ≤ 1 + 1 := add_le_add hε₁ hε₂
              _ = 2 := by norm_num
          exact ne_of_lt (lt_of_le_of_lt hle_two (by simp))
        calc
          1 - (ε₁ + ε₂) ≤ 1 - (ε₁ + ε₂ - ε₁ * ε₂) := by
            exact tsub_le_tsub_left (tsub_le_self) 1
          _ = (1 - ε₁) * (1 - ε₂) := by
            exact ENNReal.sub_eq_of_eq_add hne (by simpa [add_comm] using hsum)
      · have hε₂' : (1 : ℝ≥0∞) ≤ ε₂ := le_of_not_ge hε₂
        have : (1 : ℝ≥0∞) ≤ ε₁ + ε₂ := le_trans hε₂' (le_add_of_nonneg_left (by positivity))
        simp [tsub_eq_zero_of_le this]
    · have hε₁' : (1 : ℝ≥0∞) ≤ ε₁ := le_of_not_ge hε₁
      have : (1 : ℝ≥0∞) ≤ ε₁ + ε₂ := le_trans hε₁' (le_add_of_nonneg_right (by positivity))
      simp [tsub_eq_zero_of_le this]
  have hbind :
      1 - (ε₁ + ε₂) ≤ Pr[goodOut | mx >>= my] :=
    le_trans hsub hmul
  have hexec :
      (Reduction.comp reduction1 reduction2).execute shared stmt w = mx >>= my := by
    simpa [mx, my] using Reduction.execute_comp reduction1 reduction2 shared stmt w
  simpa [Reduction.completeness, hexec] using hbind

/-- Perfect completeness composes. -/
theorem Reduction.perfectCompleteness_comp
    {m : Type u → Type u} [Monad m] [TwoParty.LawfulCommMonad m] [HasEvalSPMF m]
    {SharedIn : Type v}
    {StatementIn : SharedIn → Type w}
    {WitnessIn : SharedIn → Type w}
    {ctx₁ : SharedIn → Spec}
    {roles₁ : (shared : SharedIn) → RoleDecoration (ctx₁ shared)}
    {StmtMid WitMid : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Type u}
    {ctx₂ : (shared : SharedIn) → Spec.Transcript (ctx₁ shared) → Spec}
    {roles₂ : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      RoleDecoration (ctx₂ shared tr₁)}
    {StmtOut WitOut : (shared : SharedIn) → (tr₁ : Spec.Transcript (ctx₁ shared)) →
      Spec.Transcript (ctx₂ shared tr₁) → Type u}
    {relIn : ∀ shared, StatementIn shared → WitnessIn shared → Prop}
    {relMid : ∀ (shared : SharedIn) (tr₁ : Spec.Transcript (ctx₁ shared)),
      StmtMid shared tr₁ → WitMid shared tr₁ → Prop}
    {relOut : ∀ (shared : SharedIn) (tr₁ : Spec.Transcript (ctx₁ shared))
      (tr₂ : Spec.Transcript (ctx₂ shared tr₁)),
      StmtOut shared tr₁ tr₂ → WitOut shared tr₁ tr₂ → Prop}
    (reduction1 : Reduction m SharedIn ctx₁ roles₁ StatementIn
      WitnessIn StmtMid WitMid)
    (reduction2 : Reduction m
      ((shared : SharedIn) × StatementIn shared × Spec.Transcript (ctx₁ shared))
      (fun shared => ctx₂ shared.1 shared.2.2)
      (fun shared => roles₂ shared.1 shared.2.2)
      (fun shared => StmtMid shared.1 shared.2.2)
      (fun shared => WitMid shared.1 shared.2.2)
      (fun shared tr₂ => StmtOut shared.1 shared.2.2 tr₂)
      (fun shared tr₂ => WitOut shared.1 shared.2.2 tr₂))
    (h₁ : reduction1.perfectCompleteness relIn relMid)
    (h₂ : reduction2.perfectCompleteness
      (fun shared sMid wMid => relMid shared.1 shared.2.2 sMid wMid)
      (fun shared tr₂ sOut wOut => relOut shared.1 shared.2.2 tr₂ sOut wOut)) :
    (Reduction.comp reduction1 reduction2).perfectCompleteness
      relIn
      (fun shared tr sOut wOut =>
        Spec.Transcript.liftAppendRel (ctx₁ shared) (ctx₂ shared) (StmtOut shared)
          (WitOut shared) (relOut shared) tr sOut wOut) := by
  simpa [Reduction.perfectCompleteness] using
    Reduction.completeness_comp reduction1 reduction2 h₁ h₂

end Interaction

end

