/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Security.KnowledgeSoundness
import ArkLib.Interaction.Security.RoundByRound

open Interaction.TwoParty

/-!
# Knowledge Claim Trees
-/

noncomputable section

open OracleComp
open scoped NNReal ENNReal

universe u v w

namespace Interaction

/-! ## Knowledge claim tree

A `KnowledgeClaimTree` augments `ClaimTree` with a backward `extractMid`
function at each node. This enables round-by-round *knowledge* soundness:
- At sender nodes, if the child claim is good, extracting back yields a good
  parent claim (backward condition).
- At receiver nodes, a bad parent claim leads to a good child claim with
  probability at most `error` (forward probabilistic bound).
-/

/-- A recursive claim tree with backward extraction, annotating each node of
a `Spec` with a knowledge-soundness witness. -/
inductive KnowledgeClaimTree : (spec : Spec) → (roles : RoleDecoration spec) →
    (Claim : Type u) → Type (u + 1) where
  | done {Claim : Type u} (good : Claim → Prop) :
      KnowledgeClaimTree .done ⟨⟩ Claim
  | sender
      {Claim : Type u} {X : Type u} {rest : X → Spec} {rRest : ∀ x, RoleDecoration (rest x)}
      (good : Claim → Prop)
      (NextClaim : X → Type u)
      (next : (x : X) → KnowledgeClaimTree (rest x) (rRest x) (NextClaim x))
      (advance : Claim → (x : X) → NextClaim x)
      (extractMid : (x : X) → NextClaim x → Claim)
      (extractAdvance : ∀ claim x, extractMid x (advance claim x) = claim) :
      KnowledgeClaimTree (.node X rest) ⟨.sender, rRest⟩ Claim
  | receiver
      {Claim : Type u} {X : Type u} {rest : X → Spec} {rRest : ∀ x, RoleDecoration (rest x)}
      (good : Claim → Prop)
      (error : ℝ≥0)
      (NextClaim : X → Type u)
      (next : (x : X) → KnowledgeClaimTree (rest x) (rRest x) (NextClaim x))
      (advance : Claim → (x : X) → NextClaim x)
      (extractMid : (x : X) → NextClaim x → Claim)
      (extractAdvance : ∀ claim x, extractMid x (advance claim x) = claim) :
      KnowledgeClaimTree (.node X rest) ⟨.receiver, rRest⟩ Claim

namespace KnowledgeClaimTree

/-- The root "good" predicate. -/
def good {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : KnowledgeClaimTree spec roles Claim) : Claim → Prop :=
  match tree with
  | .done g => g
  | .sender g _ _ _ _ _ => g
  | .receiver g _ _ _ _ _ _ => g

/-- Forget the extraction data to get a plain `ClaimTree`. -/
def toClaimTree {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : KnowledgeClaimTree spec roles Claim) : ClaimTree spec roles Claim :=
  match tree with
  | .done g => .done g
  | .sender g nc next adv _ _ =>
      .sender g nc (fun x => (next x).toClaimTree) adv
  | .receiver g err nc next adv _ _ =>
      .receiver g err nc (fun x => (next x).toClaimTree) adv

@[simp] theorem toClaimTree_good {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : KnowledgeClaimTree spec roles Claim) :
    tree.toClaimTree.good = tree.good := by
  cases tree <;> rfl

/-- The claim type at the terminal of a transcript path (via `toClaimTree`). -/
def Terminal {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : KnowledgeClaimTree spec roles Claim) (tr : Spec.Transcript spec) : Type u :=
  tree.toClaimTree.Terminal tr

/-- Transport a root claim along a transcript (via `toClaimTree`). -/
def follow {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : KnowledgeClaimTree spec roles Claim)
    (tr : Spec.Transcript spec) (claim : Claim) : tree.Terminal tr :=
  tree.toClaimTree.follow tr claim

/-- The "good" predicate at the terminal claim (via `toClaimTree`). -/
def terminalGood {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : KnowledgeClaimTree spec roles Claim)
    (tr : Spec.Transcript spec) (terminal : tree.Terminal tr) : Prop :=
  tree.toClaimTree.terminalGood tr terminal

/-- Worst-case cumulative error (via `toClaimTree`). -/
def maxPathError {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : KnowledgeClaimTree spec roles Claim) : ℝ≥0∞ :=
  tree.toClaimTree.maxPathError

/-- Extract backward from a terminal claim to a root claim, composing the
per-node `extractMid` functions along the transcript path. -/
def extractBack {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    (tree : KnowledgeClaimTree spec roles Claim)
    (tr : Spec.Transcript spec) : tree.Terminal tr → Claim :=
  match spec, roles, tree, tr with
  | .done, _, .done _, _ => id
  | .node _ _, ⟨.sender, _⟩, .sender _ _ next _ extractMid _, ⟨x, trRest⟩ =>
      fun terminal => extractMid x ((next x).extractBack trRest terminal)
  | .node _ _, ⟨.receiver, _⟩, .receiver _ _ _ next _ extractMid _, ⟨x, trRest⟩ =>
      fun terminal => extractMid x ((next x).extractBack trRest terminal)

/-- Backward extraction is a left-inverse of forward advancement: extracting
back from `follow tr claim` always recovers the original `claim`. -/
theorem extractBack_follow : {spec : Spec} → {roles : RoleDecoration spec} → {Claim : Type u} →
    (tree : KnowledgeClaimTree spec roles Claim) →
    (tr : Spec.Transcript spec) → (claim : Claim) →
    tree.extractBack tr (tree.follow tr claim) = claim
  | .done, _, _, .done _, _, _ => rfl
  | .node _ _, ⟨.sender, _⟩, _, .sender _ _ next advance extractMid extractAdvance,
      ⟨x, trRest⟩, claim => by
      change extractMid x ((next x).extractBack trRest
        ((next x).follow trRest (advance claim x))) = claim
      rw [extractBack_follow (next x) trRest, extractAdvance]
  | .node _ _, ⟨.receiver, _⟩, _, .receiver _ _ _ next advance extractMid extractAdvance,
      ⟨x, trRest⟩, claim => by
      change extractMid x ((next x).extractBack trRest
        ((next x).follow trRest (advance claim x))) = claim
      rw [extractBack_follow (next x) trRest, extractAdvance]

/-- Knowledge-soundness condition. At both sender and receiver nodes, the
backward condition holds: if the child claim is good, extracting back gives
a good parent claim. At receiver nodes, the forward probabilistic condition
also holds: a bad parent claim leads to a good child with probability at
most `error`. -/
def IsKnowledgeSound {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    (sample : (T : Type u) → m T) {spec : Spec}
    {roles : RoleDecoration spec} {Claim : Type u}
    (tree : KnowledgeClaimTree spec roles Claim) : Prop :=
  match tree with
  | .done _ => True
  | .sender good _ next _advance extractMid _extractAdvance =>
      (∀ x (nc : _), (next x).good nc → good (extractMid x nc)) ∧
      (∀ x, (next x).IsKnowledgeSound sample)
  | .receiver good error _ next advance extractMid _extractAdvance =>
      (∀ x (nc : _), (next x).good nc → good (extractMid x nc)) ∧
      (∀ claim, ¬ good claim →
        Pr[fun x => (next x).good (advance claim x) | sample _] ≤ error) ∧
      (∀ x, (next x).IsKnowledgeSound sample)

/-- A knowledge-sound tree yields a sound `ClaimTree`. The backward sender
condition implies the forward "bad stays bad" condition by contrapositive. -/
theorem isKnowledgeSound_implies_isSound
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {sample : (T : Type u) → m T}
    {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    {tree : KnowledgeClaimTree spec roles Claim}
    (h : tree.IsKnowledgeSound sample) :
    tree.toClaimTree.IsSound sample := by
  induction tree with
  | done good =>
      trivial
  | @sender _ X rest rRest good NextClaim next advance extractMid extractAdvance ih =>
      rcases h with ⟨hBack, hChildren⟩
      refine ⟨?_, ?_⟩
      · intro claim hBad x hGoodChild
        have hGoodChild' : (next x).good (advance claim x) := by
          simpa using hGoodChild
        have hParent : good (extractMid x (advance claim x)) :=
          hBack x (advance claim x) hGoodChild'
        have : good claim := by
          simpa [extractAdvance claim x] using hParent
        exact hBad this
      · intro x
        exact ih x (hChildren x)
  | @receiver _ X rest rRest good error NextClaim next advance extractMid extractAdvance ih =>
      rcases h with ⟨_, hStep, hChildren⟩
      refine ⟨?_, fun x => ih x (hChildren x)⟩
      intro claim hBad
      simpa using hStep claim hBad

/-- If a knowledge claim tree is knowledge-sound and a terminal claim is good,
then backward extraction yields a good root claim. This is the key property
that enables transcript-dependent witness extraction. -/
theorem IsKnowledgeSound.good_extractBack
    {m : Type u → Type u} [Monad m] [HasEvalSPMF m]
    {sample : (T : Type u) → m T}
    {spec : Spec} {roles : RoleDecoration spec} {Claim : Type u}
    {tree : KnowledgeClaimTree spec roles Claim}
    (hSound : tree.IsKnowledgeSound sample)
    (tr : Spec.Transcript spec) (terminal : tree.Terminal tr)
    (hGood : tree.terminalGood tr terminal) :
    tree.good (tree.extractBack tr terminal) := by
  cases tree with
  | done _ => exact hGood
  | sender good NextClaim next advance extractMid extractAdvance =>
      obtain ⟨x, trRest⟩ := tr
      exact hSound.1 _ _ (good_extractBack (hSound.2 x) trRest terminal hGood)
  | receiver good error NextClaim next advance extractMid extractAdvance =>
      obtain ⟨x, trRest⟩ := tr
      exact hSound.1 _ _ (good_extractBack (hSound.2.2 x) trRest terminal hGood)

/-- Bound on the terminal probability for knowledge claim trees, via the
underlying `ClaimTree.IsSound.bound_terminalProb`. -/
theorem IsKnowledgeSound.bound_terminalProb
    (sample : (T : Type) → ProbComp T)
    {spec : Spec} {roles : RoleDecoration spec} {Claim : Type}
    (tree : KnowledgeClaimTree spec roles Claim)
    (hSound : tree.IsKnowledgeSound sample)
    {OutputP : Spec.Transcript spec → Type}
    (prover : Spec.StrategyOver (pairedSyntax ProbComp)
      Interaction.TwoParty.Participant.focal spec roles OutputP)
    {claim : Claim} (hBad : ¬ tree.good claim) :
    Pr[fun z => tree.terminalGood z.1 (tree.follow z.1 claim)
      | TwoParty.run spec roles prover
          (randomChallenger sample spec roles)] ≤ tree.maxPathError := by
  have hBad' : ¬ tree.toClaimTree.good claim := by
    simpa using hBad
  simpa [KnowledgeClaimTree.terminalGood, KnowledgeClaimTree.follow,
    KnowledgeClaimTree.maxPathError] using
    ClaimTree.IsSound.bound_terminalProb sample tree.toClaimTree
      (isKnowledgeSound_implies_isSound hSound) prover (claim := claim) hBad'

end KnowledgeClaimTree

/-! ## Round-by-round knowledge soundness

Round-by-round knowledge soundness existentially quantifies over a
`KnowledgeClaimTree` with per-round error bounds and boundary conditions
connecting the claim tree to `relIn` and `relOut`. -/

namespace Verifier

/-- **Round-by-round knowledge soundness**: there exists a knowledge claim tree
such that:
1. The tree satisfies `IsKnowledgeSound` per-round.
2. The worst-case cumulative error is at most `ε shared stmt`.
3. Root boundary: good root claim is equivalent to the extracted witness being
   in `relIn`.
4. Forward terminal boundary: valid output in `relOut` implies the root claim's
   forward path reaches a good terminal (for soundness via `maxPathError`).
5. Backward terminal boundary: valid output maps to a good terminal claim
   via `terminalOf` (for transcript-dependent knowledge extraction via
   `extractBack`). -/
def rbrKnowledgeSoundness
    {SharedIn : Type v}
    {pSpec : SharedIn → Spec} {roles : (shared : SharedIn) → RoleDecoration (pSpec shared)}
    {StatementIn WitnessIn : SharedIn → Type w}
    {StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (pSpec shared) → Type u}
    (sample : (T : Type) → ProbComp T)
    (relIn : ∀ shared, Set (StatementIn shared × WitnessIn shared))
    (relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (pSpec shared)),
      Set (StatementOut shared tr × WitnessOut shared tr))
    (ε : ∀ shared, StatementIn shared → ℝ≥0∞) : Prop :=
  ∃ (Claim : ∀ shared, StatementIn shared → Type)
    (tree : ∀ (shared : SharedIn) (stmt : StatementIn shared),
      KnowledgeClaimTree (pSpec shared) (roles shared) (Claim shared stmt))
    (root : ∀ (shared : SharedIn) (stmt : StatementIn shared), Claim shared stmt)
    (extract : ∀ (shared : SharedIn) (stmt : StatementIn shared),
      Claim shared stmt → WitnessIn shared)
    (terminalOf : ∀ (shared : SharedIn) (stmt : StatementIn shared)
      (tr : Spec.Transcript (pSpec shared)),
      WitnessOut shared tr → (tree shared stmt).Terminal tr),
  (∀ shared stmt, (tree shared stmt).IsKnowledgeSound sample) ∧
  (∀ shared stmt, (tree shared stmt).maxPathError ≤ ε shared stmt) ∧
  (∀ shared stmt c, (tree shared stmt).good c ↔ (stmt, extract shared stmt c) ∈ relIn shared) ∧
  (∀ shared stmt tr sOut wOut, (sOut, wOut) ∈ relOut shared tr →
    (tree shared stmt).terminalGood tr ((tree shared stmt).follow tr (root shared stmt))) ∧
  (∀ shared stmt tr sOut wOut, (sOut, wOut) ∈ relOut shared tr →
    (tree shared stmt).terminalGood tr (terminalOf shared stmt tr wOut))

/-- Round-by-round knowledge soundness is monotone in the accumulated error
bound. -/
theorem rbrKnowledgeSoundness_error_mono
    {SharedIn : Type v}
    {pSpec : SharedIn → Spec} {roles : (shared : SharedIn) → RoleDecoration (pSpec shared)}
    {StatementIn WitnessIn : SharedIn → Type w}
    {StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (pSpec shared) → Type u}
    {sample : (T : Type) → ProbComp T}
    {relIn : ∀ shared, Set (StatementIn shared × WitnessIn shared)}
    {relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (pSpec shared)),
      Set (StatementOut shared tr × WitnessOut shared tr)}
    {ε₁ ε₂ : ∀ shared, StatementIn shared → ℝ≥0∞}
    (hε : ∀ shared stmt, ε₁ shared stmt ≤ ε₂ shared stmt) :
    Verifier.rbrKnowledgeSoundness (roles := roles) sample relIn relOut ε₁ →
      Verifier.rbrKnowledgeSoundness (roles := roles) sample relIn relOut ε₂ := by
  rintro ⟨Claim, tree, root, extract, terminalOf,
    hSound, hErr, hRoot, hTermFwd, hTermBwd⟩
  refine ⟨Claim, tree, root, extract, terminalOf, hSound, ?_, hRoot, hTermFwd, hTermBwd⟩
  intro shared stmt
  exact le_trans (hErr shared stmt) (hε shared stmt)

/-- Round-by-round knowledge soundness is monotone under strengthening the
output relation event. -/
theorem rbrKnowledgeSoundness_relOut_mono
    {SharedIn : Type v}
    {pSpec : SharedIn → Spec} {roles : (shared : SharedIn) → RoleDecoration (pSpec shared)}
    {StatementIn WitnessIn : SharedIn → Type w}
    {StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (pSpec shared) → Type u}
    {sample : (T : Type) → ProbComp T}
    {relIn : ∀ shared, Set (StatementIn shared × WitnessIn shared)}
    {relOut₁ relOut₂ : ∀ (shared : SharedIn) (tr : Spec.Transcript (pSpec shared)),
      Set (StatementOut shared tr × WitnessOut shared tr)}
    {ε : ∀ shared, StatementIn shared → ℝ≥0∞}
    (hRelOut : ∀ shared tr, relOut₂ shared tr ⊆ relOut₁ shared tr) :
    Verifier.rbrKnowledgeSoundness (roles := roles) sample relIn relOut₁ ε →
      Verifier.rbrKnowledgeSoundness (roles := roles) sample relIn relOut₂ ε := by
  rintro ⟨Claim, tree, root, extract, terminalOf,
    hSound, hErr, hRoot, hTermFwd, hTermBwd⟩
  refine ⟨Claim, tree, root, extract, terminalOf, hSound, hErr, hRoot, ?_, ?_⟩
  · intro shared stmt tr sOut wOut hOut
    exact hTermFwd shared stmt tr sOut wOut (hRelOut shared tr hOut)
  · intro shared stmt tr sOut wOut hOut
    exact hTermBwd shared stmt tr sOut wOut (hRelOut shared tr hOut)

/-- Round-by-round knowledge soundness implies round-by-round soundness. -/
theorem rbrKnowledgeSoundness_implies_rbrSoundness
    {SharedIn : Type v}
    {pSpec : SharedIn → Spec} {roles : (shared : SharedIn) → RoleDecoration (pSpec shared)}
    {StatementIn WitnessIn : SharedIn → Type w}
    {StatementOut WitnessOut :
      (shared : SharedIn) → Spec.Transcript (pSpec shared) → Type u}
    {sample : (T : Type) → ProbComp T}
    {relIn : ∀ shared, Set (StatementIn shared × WitnessIn shared)}
    {relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (pSpec shared)),
      Set (StatementOut shared tr × WitnessOut shared tr)}
    {ε : ∀ shared, StatementIn shared → ℝ≥0∞}
    (h : Verifier.rbrKnowledgeSoundness (roles := roles) sample relIn relOut ε)
    (langIn : ∀ shared, Set (StatementIn shared))
    (hLang : ∀ shared stmt, stmt ∉ langIn shared → ∀ w, (stmt, w) ∉ relIn shared)
    (langOut : ∀ shared, Spec.Transcript (pSpec shared) → Prop)
    (hLangOut : ∀ shared tr, langOut shared tr → ∃ pOut, pOut ∈ relOut shared tr) :
    Verifier.rbrSoundness (roles := roles) sample langIn langOut ε := by
  rcases h with ⟨Claim, tree, root, extract, _, hSound, hErr, hRoot, hTermFwd, _⟩
  refine ⟨Claim, fun shared stmt => (tree shared stmt).toClaimTree, root, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro shared stmt
    exact KnowledgeClaimTree.isKnowledgeSound_implies_isSound (hSound shared stmt)
  · intro shared stmt hs hGood
    have hGood' : (tree shared stmt).good (root shared stmt) := by
      simpa using hGood
    exact hLang shared stmt hs (extract shared stmt (root shared stmt))
      ((hRoot shared stmt (root shared stmt)).mp hGood')
  · intro shared stmt
    exact hErr shared stmt
  · intro shared stmt tr hLangOut'
    rcases hLangOut shared tr hLangOut' with ⟨⟨sOut, wOut⟩, hpOut⟩
    exact hTermFwd shared stmt tr sOut wOut hpOut

/-- Round-by-round knowledge soundness implies plain knowledge soundness.
The extractor uses backward extraction through the claim tree: given a valid
output `(sOut, wOut) ∈ relOut`, `terminalOf` identifies a good terminal claim,
`extractBack` propagates it backward to a good root claim, and `extract`
converts it to a valid input witness. -/
theorem rbrKnowledgeSoundness_implies_knowledgeSoundness
    {SharedIn : Type v}
    {pSpec : SharedIn → Spec} {roles : (shared : SharedIn) → RoleDecoration (pSpec shared)}
    {StatementIn : SharedIn → Type w} {WitnessIn : SharedIn → Type w}
    {WitnessOut : (shared : SharedIn) → Spec.Transcript (pSpec shared) → Type}
    {sample : (T : Type) → ProbComp T}
    {relIn : ∀ shared, Set (StatementIn shared × WitnessIn shared)}
    {relOut : ∀ (shared : SharedIn) (tr : Spec.Transcript (pSpec shared)),
      Set (PUnit.{1} × WitnessOut shared tr)}
    {ε : ∀ shared, StatementIn shared → ℝ≥0∞}
    (h : Verifier.rbrKnowledgeSoundness (pSpec := pSpec) (roles := roles)
      sample relIn relOut ε) :
    Verifier.knowledgeSoundness
      (SharedIn := SharedIn)
      (Context := pSpec)
      (Roles := roles)
      (StatementIn := StatementIn)
      (WitnessIn := WitnessIn)
      (StatementOut := fun _ _ => PUnit.{1})
      (WitnessOut := WitnessOut)
      (fun shared _ => randomChallenger sample (pSpec shared) (roles shared))
      relIn
      relOut
      0 := by
  rcases h with ⟨Claim, tree, root, extract, terminalOf,
    hSound, _hErr, hRoot, _hTermFwd, hTermBwd⟩
  let extractor : Extractor.Straightline SharedIn StatementIn WitnessIn pSpec
      (fun _ _ => PUnit.{1}) WitnessOut :=
    ⟨fun shared stmt tr _sOut wOut =>
      extract shared stmt
        ((tree shared stmt).extractBack tr (terminalOf shared stmt tr wOut))⟩
  refine ⟨extractor, ?_⟩
  intro shared stmt prover
  suffices h : Pr[fun z =>
      (z.2.2, z.2.1) ∈ relOut shared z.1 ∧
        (stmt, extractor shared stmt z.1 z.2.2 z.2.1) ∉ relIn shared
      | Verifier.run (fun shared _ => randomChallenger sample (pSpec shared) (roles shared))
          shared stmt prover] = 0 from h ▸ le_refl _
  rw [probEvent_eq_zero_iff]
  intro z _ ⟨hRelOut, hNotRelIn⟩
  have hTermGood := hTermBwd shared stmt z.1 z.2.2 z.2.1 hRelOut
  have hGoodRoot := KnowledgeClaimTree.IsKnowledgeSound.good_extractBack
    (hSound shared stmt) z.1 (terminalOf shared stmt z.1 z.2.1) hTermGood
  exact hNotRelIn ((hRoot shared stmt _).mp hGoodRoot)

end Verifier

end Interaction

end

