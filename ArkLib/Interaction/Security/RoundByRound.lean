/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Security.ClaimTree

open Interaction.TwoParty

/-!
# Round-by-Round Soundness
-/

noncomputable section

open OracleComp
open scoped NNReal ENNReal

universe u v w

namespace Interaction

/-! ## Round-by-round soundness via claim trees

Round-by-round soundness existentially quantifies over a `ClaimTree` (the state
function) with per-round error bounds. This matches core ArkLib's
`Verifier.StateFunction`-based definition, where the `ClaimTree` serves as the
structural equivalent:
- `ClaimTree.good` = state function predicate at each round
- `.sender` nodes: bad claims stay bad (= `toFun_next`)
- `.receiver` nodes: per-round error bound (= per-challenge error)
- `ClaimTree.maxPathError` = worst-case total error -/

namespace Verifier

/-- **Round-by-round soundness**: there exists a claim tree (state function)
such that:
1. The tree is sound per-round (`IsSound`): bad claims stay bad at sender nodes,
   and flip to good with probability at most `error` at receiver nodes.
2. The root claim is bad for all invalid statements.
3. The worst-case cumulative error is at most `ε`.
4. Membership in the output language implies terminal goodness (bridges the tree
   to the verifier). -/
def rbrSoundness
    {SharedIn : Type v}
    {pSpec : SharedIn → Spec} {roles : (shared : SharedIn) → RoleDecoration (pSpec shared)}
    {StatementIn : SharedIn → Type w}
    (sample : (T : Type) → ProbComp T)
    (langIn : ∀ shared, Set (StatementIn shared))
    (langOut : ∀ shared, Spec.Transcript (pSpec shared) → Prop)
    (ε : ∀ shared, StatementIn shared → ℝ≥0∞) : Prop :=
  ∃ (Claim : ∀ shared, StatementIn shared → Type)
    (tree : ∀ (shared : SharedIn) (stmt : StatementIn shared),
      ClaimTree (pSpec shared) (roles shared) (Claim shared stmt))
    (root : ∀ (shared : SharedIn) (stmt : StatementIn shared), Claim shared stmt),
  (∀ shared stmt, (tree shared stmt).IsSound sample) ∧
  (∀ shared stmt, stmt ∉ langIn shared → ¬ (tree shared stmt).good (root shared stmt)) ∧
  (∀ shared stmt, (tree shared stmt).maxPathError ≤ ε shared stmt) ∧
  (∀ shared stmt tr, langOut shared tr →
    (tree shared stmt).terminalGood tr ((tree shared stmt).follow tr (root shared stmt)))

/-- Round-by-round soundness is monotone in the accumulated error bound. -/
theorem rbrSoundness_error_mono
    {SharedIn : Type v}
    {pSpec : SharedIn → Spec} {roles : (shared : SharedIn) → RoleDecoration (pSpec shared)}
    {StatementIn : SharedIn → Type w}
    {sample : (T : Type) → ProbComp T}
    {langIn : ∀ shared, Set (StatementIn shared)}
    {langOut : ∀ shared, Spec.Transcript (pSpec shared) → Prop}
    {ε₁ ε₂ : ∀ shared, StatementIn shared → ℝ≥0∞}
    (hε : ∀ shared stmt, ε₁ shared stmt ≤ ε₂ shared stmt) :
    Verifier.rbrSoundness (roles := roles) sample langIn langOut ε₁ →
      Verifier.rbrSoundness (roles := roles) sample langIn langOut ε₂ := by
  rintro ⟨Claim, tree, root, hSound, hRootBad, hErr, hTerm⟩
  refine ⟨Claim, tree, root, hSound, hRootBad, ?_, hTerm⟩
  intro shared stmt
  exact le_trans (hErr shared stmt) (hε shared stmt)

/-- Round-by-round soundness is contravariant in the input language. -/
theorem rbrSoundness_langIn_mono
    {SharedIn : Type v}
    {pSpec : SharedIn → Spec} {roles : (shared : SharedIn) → RoleDecoration (pSpec shared)}
    {StatementIn : SharedIn → Type w}
    {sample : (T : Type) → ProbComp T}
    {langIn₁ langIn₂ : ∀ shared, Set (StatementIn shared)}
    {langOut : ∀ shared, Spec.Transcript (pSpec shared) → Prop}
    {ε : ∀ shared, StatementIn shared → ℝ≥0∞}
    (hLangIn : ∀ shared, langIn₁ shared ⊆ langIn₂ shared) :
    Verifier.rbrSoundness (roles := roles) sample langIn₁ langOut ε →
      Verifier.rbrSoundness (roles := roles) sample langIn₂ langOut ε := by
  rintro ⟨Claim, tree, root, hSound, hRootBad, hErr, hTerm⟩
  refine ⟨Claim, tree, root, hSound, ?_, hErr, hTerm⟩
  intro shared stmt hInvalid
  exact hRootBad shared stmt (fun hValid => hInvalid (hLangIn shared hValid))

/-- Round-by-round soundness is monotone under strengthening the output
language event. -/
theorem rbrSoundness_langOut_mono
    {SharedIn : Type v}
    {pSpec : SharedIn → Spec} {roles : (shared : SharedIn) → RoleDecoration (pSpec shared)}
    {StatementIn : SharedIn → Type w}
    {sample : (T : Type) → ProbComp T}
    {langIn : ∀ shared, Set (StatementIn shared)}
    {langOut₁ langOut₂ : ∀ shared, Spec.Transcript (pSpec shared) → Prop}
    {ε : ∀ shared, StatementIn shared → ℝ≥0∞}
    (hLangOut : ∀ shared tr, langOut₂ shared tr → langOut₁ shared tr) :
    Verifier.rbrSoundness (roles := roles) sample langIn langOut₁ ε →
      Verifier.rbrSoundness (roles := roles) sample langIn langOut₂ ε := by
  rintro ⟨Claim, tree, root, hSound, hRootBad, hErr, hTerm⟩
  refine ⟨Claim, tree, root, hSound, hRootBad, hErr, ?_⟩
  intro shared stmt tr hOut
  exact hTerm shared stmt tr (hLangOut shared tr hOut)

/-- Round-by-round soundness implies overall soundness: if `rbrSoundness` holds
with error `ε`, then for any prover and any invalid statement, the probability
of acceptance is at most `ε`. Uses `bound_terminalProb` internally. -/
theorem soundness_of_rbrSoundness
    {SharedIn : Type v}
    {pSpec : SharedIn → Spec} {roles : (shared : SharedIn) → RoleDecoration (pSpec shared)}
    {StatementIn : SharedIn → Type w}
    {sample : (T : Type) → ProbComp T}
    {langIn : ∀ shared, Set (StatementIn shared)}
    {langOut : ∀ shared, Spec.Transcript (pSpec shared) → Prop}
    {ε : ∀ shared, StatementIn shared → ℝ≥0∞}
    (h : Verifier.rbrSoundness (roles := roles) sample langIn langOut ε) :
    ∀ (shared : SharedIn)
      {OutputP : Spec.Transcript (pSpec shared) → Type}
      (prover : Spec.StrategyOver (pairedSyntax ProbComp)
        Interaction.TwoParty.Participant.focal (pSpec shared) (roles shared) OutputP)
      (stmt : StatementIn shared), stmt ∉ langIn shared →
      Pr[fun z => langOut shared z.1
        | TwoParty.run (pSpec shared) (roles shared) prover
            (randomChallenger sample (pSpec shared) (roles shared))] ≤ ε shared stmt := by
  rcases h with ⟨Claim, tree, root, hSound, hRootBad, hErr, hTerm⟩
  intro shared OutputP prover stmt hs
  have hmono :
      Pr[fun z => langOut shared z.1
        | TwoParty.run (pSpec shared) (roles shared) prover
            (randomChallenger sample (pSpec shared) (roles shared))] ≤
        Pr[fun z =>
            (tree shared stmt).terminalGood z.1
              ((tree shared stmt).follow z.1 (root shared stmt))
          | TwoParty.run (pSpec shared) (roles shared) prover
              (randomChallenger sample (pSpec shared) (roles shared))] := by
    refine probEvent_mono ?_
    intro z _ hz
    exact hTerm shared stmt z.1 hz
  exact le_trans hmono <|
    le_trans
      (ClaimTree.IsSound.bound_terminalProb sample (tree shared stmt) (hSound shared stmt) prover
        (claim := root shared stmt) (hRootBad shared stmt hs))
      (hErr shared stmt)

end Verifier

end Interaction

end

