/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Core.Security.KnowledgeComposition
import ArkLibTest.Interaction.Core.Support

/-!
# Knowledge certificates with history-dependent challenges

Two Boolean challenges have fixed shape. The second challenge is the complement of the first.
The certificate has unit witnesses, identity backward maps and zero local errors, although its
terminal predicate compares both bits and its earlier predicates are false.
-/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.TwoParty.Lens OracleComp MeasureTheory
open scoped ENNReal

namespace Interaction.Core.PrefixKnowledgeTests

/-- Two Boolean challenges, with no public prover messages. -/
abbrev twoBits : Protocol :=
  .liftBind (.challenge Bool) fun _ => .liftBind (.challenge Bool) fun _ => .pure ⟨⟩

/-- The first bit is uniform; the second is the complement of the actual first bit. -/
def draw : PrefixDraw plainSig ProbComp twoBits
  | _, _, .root _, _, _ => $ᵗ Bool
  | _, _, .down _ (.root _), _, history => pure (!history.1.1)

/-- Knowledge holds only at the terminal prefix, when the two bits coincide. -/
def predicate : {t : FreeM PlainPoly PUnit} →
    (sp : Cursor.Spine twoBits t) → PrefixMoves plainSig sp → Prop
  | _, .root _, _ => False
  | _, .down _ (.root _), _ => False
  | _, .down _ (.down _ (.root _)), history => history.2.1.1 = history.1.1

/-- Every backward map is the identity on unit witnesses. -/
def certificate : KnowledgeStateFunction plainSig twoBits Unit (fun _ _ => Unit) (fun _ => Unit)
    (fun _ => True) (fun _ _ => False) (fun _ tr _ => tr.2.1 = tr.1) where
  Witness _ {_} _ _ := Unit
  toFun _ {_} sp history _ := predicate sp history
  extractRoot _ := id
  extractStep _ {_ _} _ _ _ := id
  extractLeaf _ _ _ := id
  root _ _ _ := False.elim
  send sp _ _ ho := by
    cases sp with
    | root => cases ho
    | down _ tail =>
      cases tail with
      | root => cases ho
      | down _ tail => cases tail
  leaf sp history _ _ h := by
    cases sp with
    | down _ tail =>
      cases tail with
      | down _ tail =>
        cases tail
        exact h

/-- The full-prefix knowledge predicate certifies zero error at both receiver nodes. -/
theorem zero_error : rbrKnowledgeSoundness.{0, 0, 0} plainSig twoBits (fun (_ : Unit) => True)
    (fun _ (_ : Unit) => False) (fun _ tr (_ : Unit) => tr.2.1 = tr.1)
    draw (fun _ _ _ => 0) := by
  refine ⟨certificate, ?_⟩
  intro stmt _ a next sp ho history
  cases sp with
  | root =>
    cases history
    change 𝒟[($ᵗ Bool : ProbComp Bool)] {x | ∃ _ : Unit, ¬ False ∧ False} ≤ 0
    simp
  | down _ tail =>
    cases tail with
    | root =>
      rcases history with ⟨⟨first, rfl⟩, history⟩
      cases history
      change 𝒟[(pure (!first) : ProbComp Bool)] {x | ∃ _ : Unit, ¬ False ∧ x = first} ≤ 0
      cases first <;> simp [evalDist_pure]
    | down _ tail => cases tail

/-- A one-challenge protocol used on either side of the seam. -/
abbrev oneBit : Protocol := .liftBind (.challenge Bool) fun _ => .pure ⟨⟩

/-- The suffix error may depend on the erased challenge in the first transcript. -/
def suffixError (tr : PathAlong plainSig oneBit) : PrefixError plainSig oneBit :=
  fun _ _ _ => cond (show Bool from tr.1) 2 3

-- Both prefixes project to the same shape, but the composed local errors differ.
example : projectPathAlong plainSig oneBit ⟨true, ⟨⟩⟩ =
    projectPathAlong plainSig oneBit ⟨false, ⟨⟩⟩ := rfl

example (first : Bool) :
    combinePrefixDraw plainSig oneBit (fun _ => oneBit) (fun _ _ _ => (1 : ℝ≥0∞)) suffixError
      (.down ⟨⟩ (.root _)) rfl ⟨⟨first, rfl⟩, ⟨⟩⟩ = cond first 2 3 := rfl

end Interaction.Core.PrefixKnowledgeTests

run_cmd do
  for decl in [``Interaction.Core.PrefixKnowledgeTests.zero_error,
      ``Interaction.Core.appendPrefixSampler_eq_combinePrefixDraw,
      ``Interaction.Core.combinePrefixDraw_ofNodes,
      ``Interaction.Core.combinePrefixError_ofNodes,
      ``Interaction.Core.rbrKnowledgeSoundness_append_prefix,
      ``Interaction.Core.rbrKnowledgeSoundness_append_of_mid_prefix,
      ``Interaction.Core.Verifier.rbrKnowledgeSoundness_append_prefix,
      ``Interaction.Core.Verifier.rbrKnowledgeSoundness_append_of_pure_prefix] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
