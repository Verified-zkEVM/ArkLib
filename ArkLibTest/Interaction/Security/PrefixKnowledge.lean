/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Security.KnowledgeComposition
import ArkLibTest.Interaction.Support

/-!
# Knowledge certificates with history-dependent challenges

Two Boolean challenges have fixed shape. The second challenge is the complement of the first.
The certificate has unit witnesses, identity backward maps and zero local errors, although its
leaf predicate compares both bits and its earlier predicates are false.
-/

open PFunctor PFunctor.FreeM Interaction Interaction.TwoParty.Lens OracleComp MeasureTheory
open scoped ENNReal

namespace Interaction.PrefixKnowledgeTests

/-- Two Boolean challenges, with no public prover messages. -/
abbrev twoBits : Protocol :=
  .liftBind (.challenge Bool) fun _ => .liftBind (.challenge Bool) fun _ => .pure ⟨⟩

/-- The first bit is uniform; the second is the complement of the actual first bit. -/
def draw : PrefixDraw plainSig ProbComp twoBits
  | _, _, .root _, _, _ => $ᵗ Bool
  | _, _, .down _ (.root _), _, history => pure (!history.1.1)

/-- Knowledge holds only at the full prefix at the leaf, when the two bits coincide. -/
def predicate : {t : FreeM PlainPoly PUnit} →
    (sp : Cursor.Spine twoBits t) → PartialTranscriptAt plainSig sp → Prop
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
theorem zero_error : rbrKnowledgeSoundness plainSig twoBits (fun (_ : Unit) => True)
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
def suffixError (tr : Transcript plainSig oneBit) : PrefixError plainSig oneBit :=
  fun _ _ _ => cond (show Bool from tr.1) 2 3

-- Both prefixes project to the same shape, but the composed local errors differ.
example : Transcript.path (l := plainSig) (s := oneBit) ⟨true, ⟨⟩⟩ =
    Transcript.path (l := plainSig) (s := oneBit) ⟨false, ⟨⟩⟩ := rfl

example (first : Bool) :
    combinePrefixDraw plainSig oneBit (fun _ => oneBit) (fun _ _ _ => (1 : ℝ≥0∞)) suffixError
      (.down ⟨⟩ (.root _)) rfl ⟨⟨first, rfl⟩, ⟨⟩⟩ = cond first 2 3 := rfl

/-! ### Oracle verifier views

An oracle verifier's draw reads the verifier view of the history. The two executions below send
different oracle bits and have equal verifier views. A full-prefix draw can still return the bit.
-/

/-- An oracle bit followed by a challenge. -/
abbrev oracleThenBit : OracleProtocol.{0, 0} :=
  .liftBind (.oracle Bool OracleInterface.instDefault) fun _ =>
    .liftBind (.challenge Bool) fun _ => .pure ⟨⟩

-- Equal views: erasing the oracle bit `true` or `false` gives the same view history.
example : PartialTranscriptAt.mapMoves oracleSig eraseOracle (s := oracleThenBit)
      (.down ⟨⟩ (.root _)) ⟨⟨true, rfl⟩, ⟨⟩⟩ =
    PartialTranscriptAt.mapMoves oracleSig eraseOracle (s := oracleThenBit)
      (.down ⟨⟩ (.root _)) ⟨⟨false, rfl⟩, ⟨⟩⟩ := rfl

/-- A view-restricted draw draws the challenge the same way after either oracle bit. -/
theorem ofView_oracleBit_eq (d : PrefixDraw viewSig ProbComp oracleThenBit) :
    PrefixDraw.ofView d (.down ⟨⟩ (.root _)) rfl ⟨⟨true, rfl⟩, ⟨⟩⟩ =
      PrefixDraw.ofView d (.down ⟨⟩ (.root _)) rfl ⟨⟨false, rfl⟩, ⟨⟩⟩ := rfl

/-- A full-prefix draw that returns the oracle bit as the challenge. -/
def leakyDraw : PrefixDraw oracleSig ProbComp oracleThenBit := fun sp h history => by
  cases sp with
  | root => exact nomatch h
  | down _ tail =>
    cases tail with
    | root => exact (pure history.1.1 : ProbComp Bool)
    | down _ tail => cases tail

-- The full-prefix draw separates the two executions.
example (b : Bool) : leakyDraw (.down ⟨⟩ (.root _)) rfl ⟨⟨b, rfl⟩, ⟨⟩⟩ = pure b := rfl

/-- A first stage that sends one oracle bit. -/
abbrev oracleBit : OracleProtocol.{0, 0} :=
  .liftBind (.oracle Bool OracleInterface.instDefault) fun _ => .pure ⟨⟩

/-- A second stage with one challenge. -/
abbrev challengeBit : OracleProtocol.{0, 0} := .liftBind (.challenge Bool) fun _ => .pure ⟨⟩

/-- The view combinator chooses the suffix draw from the first-stage view, so the suffix
challenge is drawn the same way after either first-stage oracle bit. -/
theorem combineView_oracleBit_eq (d₁ : PrefixDraw viewSig ProbComp oracleBit)
    (d₂ : (p : Path oracleBit) → View oracleBit p → PrefixDraw viewSig ProbComp challengeBit) :
    PrefixDraw.ofView (combineViewPrefixDraw oracleBit (fun _ => challengeBit) d₁ d₂)
        (.down ⟨⟩ (.root _)) rfl ⟨⟨true, rfl⟩, ⟨⟩⟩ =
      PrefixDraw.ofView (combineViewPrefixDraw oracleBit (fun _ => challengeBit) d₁ d₂)
        (.down ⟨⟩ (.root _)) rfl ⟨⟨false, rfl⟩, ⟨⟩⟩ := rfl

/-- A suffix draw chosen from the full first transcript, which returns its oracle bit. -/
def leakySuffixDraw (tr₁ : Transcript oracleSig oracleBit) :
    PrefixDraw oracleSig ProbComp challengeBit := fun sp _ _ => by
  cases sp with
  | root => exact (pure tr₁.1 : ProbComp Bool)
  | down _ tail => cases tail

-- The full-prefix combinator lets the first-stage oracle bit choose the suffix challenge.
example (d₁ : PrefixDraw viewSig ProbComp oracleBit) (b : Bool) :
    combinePrefixDraw oracleSig oracleBit (fun _ => challengeBit) (PrefixDraw.ofView d₁)
      leakySuffixDraw (.down ⟨⟩ (.root _)) rfl ⟨⟨b, rfl⟩, ⟨⟩⟩ = pure b := rfl

end Interaction.PrefixKnowledgeTests

run_cmd do
  for decl in [``Interaction.PrefixKnowledgeTests.zero_error,
      ``Interaction.appendPrefixSampler_eq_combinePrefixDraw,
      ``Interaction.combinePrefixDraw_ofNodes,
      ``Interaction.combinePrefixError_ofNodes,
      ``Interaction.rbrKnowledgeSoundness_append_prefix,
      ``Interaction.rbrKnowledgeSoundness_append_of_mid_prefix,
      ``Interaction.Verifier.rbrKnowledgeSoundness_append_prefix,
      ``Interaction.Verifier.rbrKnowledgeSoundness_append_of_pure_prefix,
      ``Interaction.PrefixDraw.ofView_ofNodesView,
      ``Interaction.ofView_combineViewPrefixDraw,
      ``Interaction.appendViewPrefixSampler_eq_combineViewPrefixDraw,
      ``Interaction.PrefixKnowledgeTests.ofView_oracleBit_eq,
      ``Interaction.PrefixKnowledgeTests.combineView_oracleBit_eq] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
