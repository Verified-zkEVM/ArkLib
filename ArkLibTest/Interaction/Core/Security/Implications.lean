/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Security.Implications
import ArkLibTest.Interaction.Core.Security

/-!
Round-by-round soundness implies soundness: the general statements, the one-challenge coin
protocol, and a two-challenge protocol bounded through the uniform corollary.
-/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.TwoParty.Lens OracleComp MeasureTheory
open scoped ENNReal

namespace Interaction.Core.ImplicationsTests

open Interaction.Core.SecurityTests

/-! ### The general statements -/

-- Row #3: frozen `Interaction.Oracle.Security.executeStrategies_soundness`.
example {ι σ S T : Type} {ambient : OracleSpec ι} {s : Protocol}
    (V : Verifier ambient s S T) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem S) (output : StatementProblem T)
    (draw : QueryImpl (challengeSpec plainSig s) ProbComp)
    (ε : ChallengeNode plainSig s → ℝ≥0∞)
    (h : V.rbrSoundness impl input output draw ε) :
    V.soundness init impl draw input output
      (⨆ path : Path s, ∑ c ∈ challengeNodesOn plainSig s path, ε c) ∧
    V.soundness init impl draw input output (∑' c, ε c) :=
  ⟨Verifier.soundness_of_rbrSoundness h, Verifier.soundness_of_rbrSoundness_tsum h⟩

-- Row #4: frozen `Interaction.Oracle.Security.executeStrategies_soundness_uniform`.
example {ι σ S T : Type} {ambient : OracleSpec ι} {s : Protocol}
    (V : Verifier ambient s S T) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem S) (output : StatementProblem T)
    (draw : QueryImpl (challengeSpec plainSig s) ProbComp) (e : ℝ≥0∞) (k : ℕ)
    (hcount : ∀ path, (challengeNodesOn plainSig s path).card ≤ k)
    (h : V.rbrSoundness impl input output draw fun _ => e) :
    V.soundness init impl draw input output (k • e) :=
  Verifier.soundness_of_rbrSoundness_uniform h (fun _ => le_rfl) hcount

-- Row #5: frozen `Interaction.Oracle.Security.OrdinaryState.exists_verifier_escape`.
example {P : PFunctor.{1, 0}} (l : PFunctor.Lens P rolePoly) {s : FreeM P PUnit} {S : Type}
    {admissible language : S → Prop} {accepts : S → PathAlong l s → Prop}
    (F : StateFunction l s S admissible language accepts) (stmt : S)
    (hadm : admissible stmt) (hlang : ¬ language stmt) (tr : PathAlong l s)
    (hacc : accepts stmt tr) :
    EscapeAlong l s (fun sp history => F.toFun sp history stmt) tr :=
  F.escapeAlong l hadm hlang hacc

-- Row #6: frozen `Interaction.Oracle.Security.LocalSoundness.random_prefix`.
example {P : PFunctor.{1, 0}} (l : PFunctor.Lens P rolePoly) {s : FreeM P PUnit} {S : Type}
    {admissible language : S → Prop} {accepts : S → PathAlong l s → Prop}
    (draw : QueryImpl (challengeSpec l s) ProbComp) (ε : ChallengeNode l s → ℝ≥0∞)
    (F : StateFunction l s S admissible language accepts) (stmt : S)
    (hF : ∀ (a : P.A) (next : P.B a → FreeM P PUnit)
      (sp : Cursor.Spine s (.liftBind a next)) (h : owner l a = .receiver)
      (history : PrefixMoves l sp),
      letI : MeasurableSpace (Move l a) := ⊤
      𝒟[sampleAt l draw sp h] {x | ¬ F.toFun sp history stmt ∧
        F.toFun (sp.comp (.down (l.toFunB a x) (.root _)))
          (PrefixMoves.snoc l sp history x) stmt} ≤ ε (spineChallenge l sp h))
    {a : P.A} {next : P.B a → FreeM P PUnit} (sp : Cursor.Spine s (.liftBind a next))
    (h : owner l a = .receiver) {α : Type} (author : ProbComp α)
    (prefixOf : α → PrefixMoves l sp) :
    Pr{let y ← author; let x ← sampleAt l draw sp h}[¬ F.toFun sp (prefixOf y) stmt ∧
      F.toFun (sp.comp (.down (l.toFunB a x) (.root _)))
        (PrefixMoves.snoc l sp (prefixOf y) x) stmt] ≤ ε (spineChallenge l sp h) :=
  flip_random_prefix_le l (fun sp history => F.toFun sp history stmt) draw sp h
    (hF a next sp h) author prefixOf

/-! ### The coin protocol

Its single challenge node has error one half, so a false statement is accepted with probability
at most one half from every initial counter distribution.
-/

theorem coin_card (path : Path SecurityTests.coin) :
    (challengeNodesOn plainSig SecurityTests.coin path).card ≤ 1 := by
  rcases path with ⟨⟨⟩, ⟨⟩⟩
  rfl

example (init : ProbComp Nat) :
    coinVerifier.soundness init tick draw boolProblem anyOutput (1 / 2) := by
  simpa only [one_nsmul] using
    Verifier.soundness_of_rbrSoundness_uniform (init := init) coin_rbrSoundness
      (fun _ => le_rfl) coin_card

/-! ### A two-challenge protocol

The verifier accepts a true statement, or a zero among two uniform challenges in `Fin 4`. Each
challenge node has error one quarter, and every path meets two of them.
-/

abbrev twoChallenges : Protocol :=
  .liftBind (.challenge (Fin 4)) fun _ => .liftBind (.challenge (Fin 4)) fun _ => .pure ⟨⟩

/-- Whether a challenge is zero. -/
def isZero (x : Fin 4) : Bool := x == 0

def drawTwo : QueryImpl (challengeSpec plainSig twoChallenges) ProbComp
  | ⟨.inl _, _⟩ => (show ProbComp (Fin 4) from $ᵗ Fin 4)
  | ⟨.inr ⟨_, .inl _⟩, _⟩ => (show ProbComp (Fin 4) from $ᵗ Fin 4)
  | ⟨.inr ⟨_, .inr ⟨_, i⟩⟩, _⟩ => i.elim

/-- Accepts a true statement or a zero challenge, with the counter reading. -/
def twoVerifier : Verifier counter twoChallenges Bool Nat where
  decide stmt _ v := OptionT.mk do
    let n ← liftM (counter.query ())
    pure (if (stmt || isZero v.val.1 || isZero v.val.2.1) = true then some n else none)

theorem twoVerifier_validAcceptance_iff (stmt : Bool) (tr : PathAlong plainSig twoChallenges) :
    twoVerifier.validAcceptance tick (anyOutput.language ()) stmt tr ↔
      (stmt || isZero tr.1 || isZero tr.2.1) = true := by
  rcases tr with ⟨x, y, ⟨⟩⟩
  have key : ∀ st, (simulateQ tick (twoVerifier.decide stmt _
      (toPlainView twoChallenges ⟨x, y, ⟨⟩⟩)).run).run' st =
        pure (if (stmt || isZero x || isZero y) = true then some st else none) :=
    fun _ => rfl
  simp only [Verifier.validAcceptance, key, evalDist_pure]
  by_cases hb : (stmt || isZero x || isZero y) = true
  · simp [hb, Oracle.Problem.language, anyOutput]
  · simp [hb]

/-- The state records whether the statement or a challenge drawn so far makes acceptance
certain. -/
def twoState : StateFunction plainSig twoChallenges Bool (boolProblem.admissible ())
    (boolProblem.language ()) (twoVerifier.validAcceptance tick (anyOutput.language ())) where
  toFun {_} sp history stmt := match sp, history with
    | .root _, _ => stmt = true
    | .down _ (.root _), history => (stmt || isZero history.1.1) = true
    | .down _ (.down _ _), history => (stmt || isZero history.1.1 ||
      isZero history.2.1.1) = true
  root _ _ h := ⟨(), h⟩
  send sp _ _ h := by
    cases sp with
    | root => exact nomatch h
    | down _ tail =>
      cases tail with
      | root => exact nomatch h
      | down _ tail => cases tail
  leaf sp history stmt h := by
    cases sp with
    | down _ tail =>
      cases tail with
      | down _ tail =>
        cases tail
        rcases history with ⟨⟨x, _⟩, ⟨y, _⟩, ⟨⟩⟩
        rw [twoVerifier_validAcceptance_iff]
        exact h

theorem uniform_zero : 𝒟[($ᵗ Fin 4 : ProbComp (Fin 4))] {0} = 1 / 4 := by
  rw [SampleableType.evalDist_uniformSample_singleton, Fintype.card_fin, one_div]
  rfl

theorem two_rbrSoundness :
    twoVerifier.rbrSoundness tick boolProblem anyOutput drawTwo (fun _ => 1 / 4) := by
  refine ⟨twoState, ?_⟩
  intro stmt _ _ a next sp h history
  cases sp with
  | root =>
    change 𝒟[id <$> ($ᵗ Fin 4 : ProbComp (Fin 4))] _ ≤ _
    rw [LawfulFunctor.id_map, ← uniform_zero]
    refine measure_mono fun x hx => ?_
    obtain ⟨hstmt, hx⟩ := hx
    change ¬ stmt = true at hstmt
    change (stmt || isZero x) = true at hx
    cases stmt
    · simpa [isZero] using hx
    · exact absurd rfl hstmt
  | down b tail =>
    cases tail with
    | root =>
      change 𝒟[id <$> ($ᵗ Fin 4 : ProbComp (Fin 4))] _ ≤ _
      rw [LawfulFunctor.id_map, ← uniform_zero]
      refine measure_mono fun y hy => ?_
      obtain ⟨hprev, hy⟩ := hy
      rcases history with ⟨⟨x, _⟩, ⟨⟩⟩
      change ¬ (stmt || isZero x) = true at hprev
      change (stmt || isZero x || isZero y) = true at hy
      simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hprev
      simp only [hprev.1, hprev.2, Bool.or_false, Bool.false_or] at hy
      simpa [isZero] using hy
    | down _ tail => cases tail

theorem two_card (path : Path twoChallenges) :
    (challengeNodesOn plainSig twoChallenges path).card ≤ 2 := by
  rcases path with ⟨⟨⟩, ⟨⟩, ⟨⟩⟩
  rfl

example (init : ProbComp Nat) :
    twoVerifier.soundness init tick drawTwo boolProblem anyOutput (2 • (1 / 4)) :=
  Verifier.soundness_of_rbrSoundness_uniform two_rbrSoundness (fun _ => le_rfl) two_card

end Interaction.Core.ImplicationsTests

run_cmd do
  for name in [``Interaction.Core.Verifier.soundness_of_rbrSoundness,
      ``Interaction.Core.Verifier.soundness_of_rbrSoundness_tsum,
      ``Interaction.Core.Verifier.soundness_of_rbrSoundness_uniform,
      ``Interaction.Core.StateFunction.escapeAlong,
      ``Interaction.Core.flip_random_prefix_le,
      ``Interaction.Core.ImplicationsTests.two_rbrSoundness] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} depends on {ax}"
