/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Security.Basic

open Interaction.TwoParty

/-!
# Claim Trees for Round-by-Round Soundness
-/

noncomputable section

open OracleComp
open scoped NNReal ENNReal

universe u v w

namespace Interaction

/-! ## Claim tree

A `ClaimTree` is a recursive soundness witness defined by structural recursion
on `Spec` + `RoleDecoration`. Each node carries:
- `good : Claim → Prop`, the "good claim" predicate at this point
- At sender nodes: `advance` maps a claim through the prover's message
- At receiver nodes: `error` bounds the probability of a bad claim becoming good

The key invariant (`IsSound`):
- Sender nodes: bad claims MUST stay bad regardless of the prover's message
- Receiver nodes: bad claims may become good with probability at most `error`

This gives a round-by-round soundness analysis. -/

/-- A recursive claim tree annotating each node of a `Spec` with a soundness
witness. The `Claim` type may change at each node via `NextClaim`. -/
inductive ClaimTree : (spec : Spec) → (roles : RoleDecoration spec) →
    (Claim : Type u) → Type (u + 1) where
  /-- Base case: leaf with a good predicate. -/
  | done {Claim : Type u} (good : Claim → Prop) :
      ClaimTree .done ⟨⟩ Claim
  /-- Sender (prover message) node: the prover's choice cannot improve a bad
  claim. `advance` maps the current claim through the message. -/
  | sender
      {Claim : Type u} {X : Type u} {rest : X → Spec} {rRest : ∀ x, RoleDecoration (rest x)}
      (good : Claim → Prop)
      (NextClaim : X → Type u)
      (next : (x : X) → ClaimTree (rest x) (rRest x) (NextClaim x))
      (advance : Claim → (x : X) → NextClaim x) :
      ClaimTree (.node X rest) ⟨.sender, rRest⟩ Claim
  /-- Receiver (verifier challenge) node: a bad claim may flip to good
  with probability at most `error`. -/
  | receiver
      {Claim : Type u} {X : Type u} {rest : X → Spec} {rRest : ∀ x, RoleDecoration (rest x)}
      (good : Claim → Prop)
      (error : ℝ≥0)
      (NextClaim : X → Type u)
      (next : (x : X) → ClaimTree (rest x) (rRest x) (NextClaim x))
      (advance : Claim → (x : X) → NextClaim x) :
      ClaimTree (.node X rest) ⟨.receiver, rRest⟩ Claim

namespace ClaimTree

/-- The root "good" predicate. -/
def good {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : ClaimTree spec roles Claim) : Claim → Prop :=
  match tree with
  | .done g => g
  | .sender g _ _ _ => g
  | .receiver g _ _ _ _ => g

/-- The claim type at the terminal (leaf) of a transcript path. -/
def Terminal {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : ClaimTree spec roles Claim) (tr : Spec.Transcript spec) : Type u :=
  match spec, roles, tree, tr with
  | .done, _, .done _, _ => Claim
  | .node _ _, ⟨.sender, _⟩, .sender _ _ next _, ⟨x, trRest⟩ =>
      (next x).Terminal trRest
  | .node _ _, ⟨.receiver, _⟩, .receiver _ _ _ next _, ⟨x, trRest⟩ =>
      (next x).Terminal trRest

/-- Transport a root claim along a transcript to the terminal claim. -/
def follow {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : ClaimTree spec roles Claim)
    (tr : Spec.Transcript spec) (claim : Claim) : tree.Terminal tr :=
  match spec, roles, tree, tr with
  | .done, _, .done _, _ => claim
  | .node _ _, ⟨.sender, _⟩, .sender _ _ next advance, ⟨x, trRest⟩ =>
      (next x).follow trRest (advance claim x)
  | .node _ _, ⟨.receiver, _⟩, .receiver _ _ _ next advance, ⟨x, trRest⟩ =>
      (next x).follow trRest (advance claim x)

/-- The "good" predicate at the terminal claim reached by a transcript. -/
def terminalGood {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : ClaimTree spec roles Claim)
    (tr : Spec.Transcript spec) (terminal : tree.Terminal tr) : Prop :=
  match spec, roles, tree, tr with
  | .done, _, .done g, _ => g terminal
  | .node _ _, ⟨.sender, _⟩, .sender _ _ next _, ⟨x, trRest⟩ =>
      (next x).terminalGood trRest terminal
  | .node _ _, ⟨.receiver, _⟩, .receiver _ _ _ next _, ⟨x, trRest⟩ =>
      (next x).terminalGood trRest terminal

/-- Worst-case cumulative error along any root-to-leaf path. Sender nodes
contribute `0` error; receiver nodes contribute their `error` bound plus the
sup over children. -/
def maxPathError {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : ClaimTree spec roles Claim) : ℝ≥0∞ :=
  match tree with
  | .done _ => 0
  | .sender _ _ next _ => ⨆ x, (next x).maxPathError
  | .receiver _ error _ next _ =>
      error + ⨆ x, (next x).maxPathError

/-- Structural soundness of a claim tree. At sender nodes, bad claims must
stay bad for all messages. At receiver nodes, bad claims flip to good with
probability at most `error`. All children must be sound recursively. -/
def IsSound {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    (sample : (T : Type u) → m T) {spec : Spec}
    {roles : RoleDecoration spec} {Claim : Type u}
    (tree : ClaimTree spec roles Claim) : Prop :=
  match tree with
  | .done _ => True
  | .sender good _ next advance =>
      (∀ claim, ¬ good claim → ∀ x, ¬ (next x).good (advance claim x)) ∧
      (∀ x, (next x).IsSound sample)
  | .receiver good error _ next advance =>
      (∀ claim, ¬ good claim →
        Pr[fun x => (next x).good (advance claim x) | sample _] ≤ error) ∧
      (∀ x, (next x).IsSound sample)

/-- The main round-by-round soundness theorem. If a claim tree is sound and
the root claim is bad, then the probability of reaching a good terminal claim
under any adversarial prover (playing against a random challenger built from
the same sampler) is at most `maxPathError`. -/
theorem IsSound.bound_terminalProb
    (sample : (T : Type) → ProbComp T)
    {spec : Spec} {roles : RoleDecoration spec} {Claim : Type}
    (tree : ClaimTree spec roles Claim)
    (hSound : tree.IsSound sample)
    {OutputP : Spec.Transcript spec → Type}
    (prover : Spec.StrategyOver (pairedSyntax ProbComp)
      Interaction.TwoParty.Participant.focal spec roles OutputP)
    {claim : Claim} (hBad : ¬ tree.good claim) :
    Pr[fun z => tree.terminalGood z.1 (tree.follow z.1 claim)
      | TwoParty.run spec roles prover
          (randomChallenger sample spec roles)] ≤ tree.maxPathError := by
  sorry
/-
  classical
  induction tree with
  | done good =>
      simpa [ClaimTree.follow, ClaimTree.terminalGood, ClaimTree.maxPathError,
        TwoParty.run_done] using hBad
  | @sender _ X rest rRest good NextClaim next advance ih =>
      rcases hSound with ⟨hStayBad, hChildrenSound⟩
      let mx :
          ProbComp ((x : X) × Spec.StrategyOver (pairedSyntax ProbComp)
            Interaction.TwoParty.Participant.focal (rest x) (rRest x)
            (fun tr => OutputP ⟨x, tr⟩)) := prover
      let event :
          ((tr : Spec.Transcript (Spec.node X rest)) × OutputP tr × PUnit) → Prop :=
        fun z => ClaimTree.terminalGood (.sender good NextClaim next advance) z.1
          (ClaimTree.follow (.sender good NextClaim next advance) z.1 claim)
      let my :
          ((x : X) × Spec.StrategyOver (pairedSyntax ProbComp)
            Interaction.TwoParty.Participant.focal (rest x) (rRest x)
            (fun tr => OutputP ⟨x, tr⟩)) →
            ProbComp ((tr : Spec.Transcript (Spec.node X rest)) × OutputP tr × PUnit) :=
        fun xc =>
          let addPrefix :
              ((tr : Spec.Transcript (rest xc.1)) × (fun tr => OutputP ⟨xc.1, tr⟩) tr × PUnit) →
                ((tr : Spec.Transcript (Spec.node X rest)) × OutputP tr × PUnit) :=
            fun z => ⟨⟨xc.1, z.1⟩, z.2.1, z.2.2⟩
          addPrefix <$>
            TwoParty.run (rest xc.1) (rRest xc.1) xc.2
              (randomChallenger sample (rest xc.1) (rRest xc.1))
      have hChild :
          ∀ xc, Pr[event | my xc] ≤ ⨆ x, (next x).maxPathError := by
        intro xc
        let addPrefix :
            ((tr : Spec.Transcript (rest xc.1)) × (fun tr => OutputP ⟨xc.1, tr⟩) tr × PUnit) →
              ((tr : Spec.Transcript (Spec.node X rest)) × OutputP tr × PUnit) :=
          fun z => ⟨⟨xc.1, z.1⟩, z.2.1, z.2.2⟩
        have hEvent :
            event ∘ addPrefix =
              fun z =>
                (next xc.1).terminalGood z.1
                  ((next xc.1).follow z.1 (advance claim xc.1)) := by
          funext z
          cases z
          rfl
        have hChild' :
            Pr[event | my xc] ≤ (next xc.1).maxPathError := by
          simpa [my, addPrefix, hEvent, probEvent_map] using
            (ih xc.1 (hChildrenSound xc.1) xc.2
              (hStayBad claim hBad xc.1))
        exact le_trans hChild' (le_iSup (fun x => (next x).maxPathError) xc.1)
      have hbind :
          Pr[event | mx >>= my] ≤ ⨆ x, (next x).maxPathError := by
        rw [probEvent_bind_eq_tsum]
        calc
          ∑' xc, Pr[= xc | mx] * Pr[event | my xc]
              ≤ ∑' xc, Pr[= xc | mx] * (⨆ x, (next x).maxPathError) := by
                refine ENNReal.tsum_le_tsum fun xc => ?_
                exact mul_le_mul' le_rfl (hChild xc)
          _ = (∑' xc, Pr[= xc | mx]) * (⨆ x, (next x).maxPathError) := by
                rw [ENNReal.tsum_mul_right]
          _ ≤ 1 * (⨆ x, (next x).maxPathError) := by
                exact mul_le_mul' tsum_probOutput_le_one le_rfl
          _ = ⨆ x, (next x).maxPathError := by simp
      have hrun :
          TwoParty.run _ _ prover (randomChallenger sample _ _) = mx >>= my := by
        simp [mx, my, randomChallenger, TwoParty.run_sender]
      simpa [ClaimTree.maxPathError, hrun]
        using hbind
  | @receiver _ X rest rRest good error NextClaim next advance ih =>
      rcases hSound with ⟨hStep, hChildrenSound⟩
      let event :
          ((tr : Spec.Transcript (Spec.node X rest)) × OutputP tr × PUnit) → Prop :=
        fun z => ClaimTree.terminalGood (.receiver good error NextClaim next advance) z.1
          (ClaimTree.follow (.receiver good error NextClaim next advance) z.1 claim)
      let p : _ → Prop :=
        fun x => ¬ (next x).good (advance claim x)
      let my :
          (x : X) → ProbComp ((tr : Spec.Transcript (Spec.node X rest)) × OutputP tr × PUnit) :=
        fun x =>
          let childRun :
              Spec.StrategyOver (pairedSyntax ProbComp)
                Interaction.TwoParty.Participant.focal (rest x) (rRest x)
                (fun tr => OutputP ⟨x, tr⟩) →
                ProbComp ((tr : Spec.Transcript (Spec.node X rest)) × OutputP tr × PUnit) :=
            fun nextProver =>
              let addPrefix :
                  ((tr : Spec.Transcript (rest x)) × (fun tr => OutputP ⟨x, tr⟩) tr × PUnit) →
                    ((tr : Spec.Transcript (Spec.node X rest)) × OutputP tr × PUnit) :=
                fun z => ⟨⟨x, z.1⟩, z.2.1, z.2.2⟩
              addPrefix <$>
                TwoParty.run (rest x) (rRest x) nextProver
                  (randomChallenger sample (rest x) (rRest x))
          prover x >>= childRun
      have h₁ : Pr[fun x => ¬ p x | sample _] ≤ error := by
        simpa [p] using hStep claim hBad
      have h₂ :
          ∀ x ∈ support (sample _), p x → Pr[event | my x] ≤ ⨆ x, (next x).maxPathError := by
        intro x _ hp
        let childRun :
            Spec.StrategyOver (pairedSyntax ProbComp)
              Interaction.TwoParty.Participant.focal (rest x) (rRest x)
              (fun tr => OutputP ⟨x, tr⟩) →
              ProbComp ((tr : Spec.Transcript (Spec.node X rest)) × OutputP tr × PUnit) :=
          fun nextProver =>
            let addPrefix :
                ((tr : Spec.Transcript (rest x)) × (fun tr => OutputP ⟨x, tr⟩) tr × PUnit) →
                  ((tr : Spec.Transcript (Spec.node X rest)) × OutputP tr × PUnit) :=
              fun z => ⟨⟨x, z.1⟩, z.2.1, z.2.2⟩
            addPrefix <$>
              TwoParty.run (rest x) (rRest x) nextProver
                (randomChallenger sample (rest x) (rRest x))
        have hChildRun :
            ∀ nextProver ∈ support (prover x), Pr[event | childRun nextProver] ≤
              (next x).maxPathError := by
          intro nextProver hxProver
          let addPrefix :
              ((tr : Spec.Transcript (rest x)) × (fun tr => OutputP ⟨x, tr⟩) tr × PUnit) →
                ((tr : Spec.Transcript (Spec.node X rest)) × OutputP tr × PUnit) :=
            fun z => ⟨⟨x, z.1⟩, z.2.1, z.2.2⟩
          have hEvent :
              event ∘ addPrefix =
                fun z =>
                  (next x).terminalGood z.1
                    ((next x).follow z.1 (advance claim x)) := by
            funext z
            cases z
            rfl
          simpa [childRun, addPrefix, hEvent, probEvent_map] using
            (ih x (hChildrenSound x) nextProver hp)
        have hChild :
            Pr[event | my x] ≤ (next x).maxPathError := by
          rw [show my x = prover x >>= childRun by rfl, probEvent_bind_eq_tsum]
          calc
            ∑' nextProver, Pr[= nextProver | prover x] * Pr[event | childRun nextProver]
                ≤ ∑' nextProver, Pr[= nextProver | prover x] * (next x).maxPathError := by
                  refine ENNReal.tsum_le_tsum fun nextProver => ?_
                  by_cases hxProver : nextProver ∈ support (prover x)
                  · exact mul_le_mul' le_rfl (hChildRun nextProver hxProver)
                  · simp [probOutput_eq_zero_of_not_mem_support hxProver]
            _ = (∑' nextProver, Pr[= nextProver | prover x]) * (next x).maxPathError := by
                  rw [ENNReal.tsum_mul_right]
            _ ≤ 1 * (next x).maxPathError := by
                  exact mul_le_mul' tsum_probOutput_le_one le_rfl
            _ = (next x).maxPathError := by simp
        exact le_trans hChild (le_iSup (fun x => (next x).maxPathError) x)
      have hbind :
          Pr[event | sample _ >>= my] ≤ error + ⨆ x, (next x).maxPathError := by
        simpa using
          (probEvent_bind_le_add (mx := sample _) (my := my)
            (p := p) (q := fun z => ¬ event z) h₁
            (fun x hx hp => by simpa using h₂ x hx hp))
      have hrun :
          TwoParty.run _ _ prover (randomChallenger sample _ _) =
            sample _ >>= my := by
        simp [my, randomChallenger, TwoParty.run_receiver]
      simpa [ClaimTree.maxPathError, hrun] using hbind
-/

end ClaimTree

end Interaction

end

