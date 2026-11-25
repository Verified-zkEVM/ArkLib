/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Security.Implications
import ArkLibTest.Interaction.Security

/-!
Round-by-round soundness implies soundness: the general statements for plain and oracle
verifiers, the averaged-prefix bound with a node chosen by a possibly failing author, the
one-challenge coin protocol, and a two-challenge protocol bounded through the uniform corollary.
-/

open PFunctor PFunctor.FreeM Interaction Interaction.TwoParty.Lens OracleComp MeasureTheory
open Interaction.Oracle
open scoped ENNReal


-- These ordinary imports expose both classical specialization laws for each verifier form.
#check Verifier.soundness_iff_soundnessUsing
#check OracleVerifier.soundness_iff_soundnessUsing
#check Verifier.validAcceptance_iff_validAcceptanceUsing
#check OracleVerifier.validAcceptance_iff_validAcceptanceUsing

#check runPrefixChallenges_eq_run
#check prEvent_runPrefixChallenges_le
#check prEvent_runPrefixChallenges_soundness

namespace Interaction.ImplicationsTests

open Interaction.SecurityTests

/-! ### The general statements -/

-- Disposition S2: soundness-implication-disposition.md#soundnesslean.
example {ι σ : Type} {S : Type} {ambient : OracleSpec ι} {s : Protocol}
    {T : Path s → Type}
    (V : Verifier ambient s S T) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem S) (output : PathProblem s T)
    (draw : QueryImpl (challengeSpec plainSig s) ProbComp)
    (ε : ChallengeNode plainSig s → ℝ≥0∞)
    (h : V.rbrSoundness impl input output draw ε) :
    V.soundness init impl draw input output
      (⨆ path : Path s, ∑ c ∈ challengeNodesOn plainSig s path, ε c) ∧
    V.soundness init impl draw input output (∑' c, ε c) :=
  ⟨Verifier.soundness_of_rbrSoundness h, Verifier.soundness_of_rbrSoundness_tsum h⟩

-- Disposition S3: soundness-implication-disposition.md#soundnesslean.
example {ι σ : Type} {S : Type} {ambient : OracleSpec ι} {s : Protocol}
    {T : Path s → Type}
    (V : Verifier ambient s S T) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem S) (output : PathProblem s T)
    (draw : QueryImpl (challengeSpec plainSig s) ProbComp) (e : ℝ≥0∞) (k : ℕ)
    (hcount : ∀ path, (challengeNodesOn plainSig s path).card ≤ k)
    (h : V.rbrSoundness impl input output draw fun _ => e) :
    V.soundness init impl draw input output (k • e) :=
  Verifier.soundness_of_rbrSoundness_uniform h (fun _ => le_rfl) hcount

-- Disposition S2, oracle form: soundness-implication-disposition.md#soundnesslean.
example {ι σ : Type} {I : Type} {S : Type}
    {ambient : OracleSpec ι} {s : OracleProtocol} {T : Path s → Type} {A : I → Type}
    {J : Path s → Type} {B : (p : Path s) → J p → Type}
    {inputs : OracleFamily.{0, 0, 0} I A}
    {outputs : (p : Path s) → OracleFamily.{0, 0, 0} (J p) (B p)}
    (V : OracleVerifier ambient s S T inputs outputs) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (S × (∀ i, A i))) (output : PathProblem s (OracleVerifier.Output T B))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (ε : ChallengeNode oracleSig s → ℝ≥0∞)
    (h : V.rbrSoundness impl input output draw ε) :
    V.soundness init impl draw input output
      (⨆ path : Path s, ∑ c ∈ challengeNodesOn oracleSig s path, ε c) ∧
    V.soundness init impl draw input output (∑' c, ε c) :=
  ⟨OracleVerifier.soundness_of_rbrSoundness h, OracleVerifier.soundness_of_rbrSoundness_tsum h⟩

-- Disposition S3, oracle form: soundness-implication-disposition.md#soundnesslean.
example {ι σ : Type} {I : Type} {S : Type}
    {ambient : OracleSpec ι} {s : OracleProtocol} {T : Path s → Type} {A : I → Type}
    {J : Path s → Type} {B : (p : Path s) → J p → Type}
    {inputs : OracleFamily.{0, 0, 0} I A}
    {outputs : (p : Path s) → OracleFamily.{0, 0, 0} (J p) (B p)}
    (V : OracleVerifier ambient s S T inputs outputs) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (S × (∀ i, A i))) (output : PathProblem s (OracleVerifier.Output T B))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp) (e : ℝ≥0∞) (k : ℕ)
    (hcount : ∀ path, (challengeNodesOn oracleSig s path).card ≤ k)
    (h : V.rbrSoundness impl input output draw fun _ => e) :
    V.soundness init impl draw input output (k • e) :=
  OracleVerifier.soundness_of_rbrSoundness_uniform h (fun _ => le_rfl) hcount

-- The oracle implication takes any input bundle, as `OracleVerifier.run` does; the oracle-family
-- examples above use the coercion from a family to its bundle.
example {ι σ : Type} {S : Type}
    {ambient : OracleSpec ι} {s : OracleProtocol} {T : Path s → Type}
    {J : Path s → Type} {B : (p : Path s) → J p → Type}
    {inputs : OracleBundle.{0, 0, 0}}
    {outputs : (p : Path s) → OracleFamily.{0, 0, 0} (J p) (B p)}
    (V : OracleVerifier ambient s S T inputs outputs) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (S × inputs.Data))
    (output : PathProblem s (OracleVerifier.Output T B))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (ε : ChallengeNode oracleSig s → ℝ≥0∞)
    (h : V.rbrSoundness impl input output draw ε) :
    V.soundness init impl draw input output (∑' c, ε c) :=
  OracleVerifier.soundness_of_rbrSoundness_tsum h

-- The oracle conclusion is the model soundness of the classical oracle model, with acceptance read
-- from the verdict and the output oracle data of the outcome.
example {ι σ : Type} {I : Type} {S : Type}
    {ambient : OracleSpec ι} {s : OracleProtocol} {T : Path s → Type} {A : I → Type}
    {J : Path s → Type} {B : (p : Path s) → J p → Type}
    {inputs : OracleFamily.{0, 0, 0} I A}
    {outputs : (p : Path s) → OracleFamily.{0, 0, 0} (J p) (B p)}
    (V : OracleVerifier ambient s S T inputs outputs) (init : ProbComp σ)
    (impl : QueryImpl ambient (StateT σ ProbComp))
    (input : StatementProblem (S × (∀ i, A i))) (output : PathProblem s (OracleVerifier.Output T B))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp) (ε : ℝ≥0∞) :
    V.soundness init impl draw input output ε ↔
      ∀ Out : Transcript oracleSig s → Type,
        letI : MeasurableSpace (Outcome oracleSig s Out (OracleVerifier.Output T B)) := ⊤
        soundness (V.classicalModel (Out := Out) init impl draw) input output
          (fun obs => Transcript.path obs.1) (fun obs => obs.2.2) ε :=
  Iff.rfl

-- Disposition R1: soundness-implication-disposition.md#roundbyroundlean.
example {P : PFunctor.{1, 0}} (l : PFunctor.Lens P rolePoly) {s : FreeM P PUnit} {S : Type}
    {admissible language : S → Prop} {accepts : S → Transcript l s → Prop}
    (F : StateFunction l s S admissible language accepts) (stmt : S)
    (hadm : admissible stmt) (hlang : ¬ language stmt) (tr : Transcript l s)
    (hacc : accepts stmt tr) :
    EscapeAlong l s (fun sp history => F.toFun sp history stmt) tr :=
  F.escapeAlong l hadm hlang hacc

-- Disposition S4: soundness-implication-disposition.md#soundnesslean.
example {P : PFunctor.{1, 0}} (l : PFunctor.Lens P rolePoly) {s : FreeM P PUnit} {S : Type}
    {admissible language : S → Prop} {accepts : S → Transcript l s → Prop}
    (draw : QueryImpl (challengeSpec l s) ProbComp) (ε : ChallengeNode l s → ℝ≥0∞)
    (F : StateFunction l s S admissible language accepts) (stmt : S)
    (hF : ∀ (a : P.A) (next : P.B a → FreeM P PUnit)
      (sp : Cursor.Spine s (.liftBind a next)) (h : owner l a = .receiver)
      (history : PartialTranscriptAt l sp),
      letI : MeasurableSpace (Move l a) := ⊤
      𝒟[sampleAt l draw sp h] {x | ¬ F.toFun sp history stmt ∧
        F.toFun (sp.comp (.down (l.toFunB a x) (.root _)))
          (PartialTranscriptAt.snoc l sp history x) stmt} ≤ ε (spineChallenge l sp h))
    {α : Type} (author : OptionT ProbComp α) (select : α → ReceiverPrefix l s) (e : ℝ≥0∞)
    (hselect : ∀ y, ε (select y).node ≤ e) :
    Pr{let flip ← (author >>= fun y =>
      (select y).Flips l (fun sp history => F.toFun sp history stmt) <$>
        OptionT.lift (sampleAt l draw (select y).spine (select y).receiver))}[flip] ≤ e :=
  flip_random_prefix_le l (fun sp history => F.toFun sp history stmt) draw ε hF author select
    hselect

-- Disposition S4 also covers a fixed receiver node and a nonfailing prefix author.
example {P : PFunctor.{1, 0}} (l : PFunctor.Lens P rolePoly) {s : FreeM P PUnit} {S : Type}
    {admissible language : S → Prop} {accepts : S → Transcript l s → Prop}
    (draw : QueryImpl (challengeSpec l s) ProbComp) (ε : ChallengeNode l s → ℝ≥0∞)
    (F : StateFunction l s S admissible language accepts) (stmt : S)
    (hF : ∀ (a : P.A) (next : P.B a → FreeM P PUnit)
      (sp : Cursor.Spine s (.liftBind a next)) (h : owner l a = .receiver)
      (history : PartialTranscriptAt l sp),
      letI : MeasurableSpace (Move l a) := ⊤
      𝒟[sampleAt l draw sp h] {x | ¬ F.toFun sp history stmt ∧
        F.toFun (sp.comp (.down (l.toFunB a x) (.root _)))
          (PartialTranscriptAt.snoc l sp history x) stmt} ≤ ε (spineChallenge l sp h))
    {a : P.A} {next : P.B a → FreeM P PUnit} (sp : Cursor.Spine s (.liftBind a next))
    (h : owner l a = .receiver) {α : Type} (author : ProbComp α)
    (prefixOf : α → PartialTranscriptAt l sp) :
    Pr{let y ← author; let x ← sampleAt l draw sp h}[¬ F.toFun sp (prefixOf y) stmt ∧
      F.toFun (sp.comp (.down (l.toFunB a x) (.root _)))
        (PartialTranscriptAt.snoc l sp (prefixOf y) x) stmt] ≤ ε (spineChallenge l sp h) :=
  flip_random_history_le l (fun sp history => F.toFun sp history stmt) draw sp h
    (hF a next sp h) author prefixOf

/-! ### An author choosing between two challenge nodes

A public bit selects one of two challenge nodes. A possibly failing author of the bit selects the
node, so the selected node varies with the author's output.
-/

/-- A public bit, then a challenge in `Fin 4` below either value of the bit. -/
abbrev branchy : Protocol :=
  .liftBind (.message Bool) fun _ => .liftBind (.challenge (Fin 4)) fun _ => .pure ⟨⟩

/-- The challenge node below the public bit `b`, with the bit as its full prefix. -/
def afterBit (b : Bool) : ReceiverPrefix plainSig branchy where
  pos := .challenge (Fin 4)
  next _ := .pure ⟨⟩
  spine := .down b (.root _)
  receiver := rfl
  history := ⟨⟨b, rfl⟩, ⟨⟩⟩

/-- The two values of the bit select different challenge nodes. -/
theorem afterBit_node_ne : (afterBit true).node ≠ (afterBit false).node := by
  intro h
  have h' := congrArg Subtype.val h
  injection h' with h'
  injection h' with h'
  cases h'

-- Disposition S4 also permits the selected node to depend on the author's output.
example
    (G : ∀ {t : Protocol}, (sp : Cursor.Spine branchy t) → PartialTranscriptAt plainSig sp → Prop)
    (draw : QueryImpl (challengeSpec plainSig branchy) ProbComp)
    (ε : ChallengeNode plainSig branchy → ℝ≥0∞)
    (hlocal : ∀ (a : PlainPos) (next : PlainPoly.B a → Protocol)
      (sp : Cursor.Spine branchy (.liftBind a next)) (h : owner plainSig a = .receiver)
      (history : PartialTranscriptAt plainSig sp),
      letI : MeasurableSpace (Move plainSig a) := ⊤
      𝒟[sampleAt plainSig draw sp h] {x | ¬ G sp history ∧
        G (sp.comp (.down (plainSig.toFunB a x) (.root _)))
          (PartialTranscriptAt.snoc plainSig sp history x)} ≤ ε (spineChallenge plainSig sp h))
    (author : OptionT ProbComp Bool) (e : ℝ≥0∞) (htrue : ε (afterBit true).node ≤ e)
    (hfalse : ε (afterBit false).node ≤ e) :
    Pr{let flip ← (author >>= fun b => (afterBit b).Flips plainSig G <$>
      OptionT.lift (sampleAt plainSig draw (afterBit b).spine (afterBit b).receiver))}[flip] ≤
        e :=
  flip_random_prefix_le plainSig G draw ε hlocal author afterBit fun b => by
    cases b
    · exact hfalse
    · exact htrue

/-! ### The coin protocol

Its single challenge node has error one half, so a false statement is accepted with probability
at most one half from every initial counter distribution.
-/

/-- Every path of the coin protocol meets at most one challenge node. -/
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

/-- Two challenges in `Fin 4`, one after the other. -/
abbrev twoChallenges : Protocol :=
  .liftBind (.challenge (Fin 4)) fun _ => .liftBind (.challenge (Fin 4)) fun _ => .pure ⟨⟩

/-- Whether a challenge is zero. -/
def isZero (x : Fin 4) : Bool := x == 0

/-- Each of the two challenges is drawn uniformly from `Fin 4`. -/
def drawTwo : QueryImpl (challengeSpec plainSig twoChallenges) ProbComp
  | ⟨.inl _, _⟩ => (show ProbComp (Fin 4) from $ᵗ Fin 4)
  | ⟨.inr ⟨_, .inl _⟩, _⟩ => (show ProbComp (Fin 4) from $ᵗ Fin 4)
  | ⟨.inr ⟨_, .inr ⟨_, i⟩⟩, _⟩ => i.elim

/-- Accepts a true statement or a zero challenge, with the counter reading. -/
def twoVerifier : Verifier counter twoChallenges Bool (fun _ => Nat) where
  decide stmt _ v := OptionT.mk do
    let n ← liftM (counter.query ())
    pure (if (stmt || isZero v.val.1 || isZero v.val.2.1) = true then some n else none)

/-- Every natural-number claim at a two-challenge path is valid, with a unit witness. -/
@[instance_reducible] def twoOutput : PathProblem twoChallenges (fun _ => Nat) where
  Witness _ _ := Unit
  admissible _ _ := True
  rel _ _ _ := True
  rel_admissible _ _ _ _ := trivial

/-- The two-challenge verifier accepts exactly a true statement or a zero challenge. -/
theorem twoVerifier_validAcceptance_iff (stmt : Bool) (tr : Transcript plainSig twoChallenges) :
    twoVerifier.validAcceptance tick stmt tr
      (twoOutput.language tr.path) ↔
      (stmt || isZero tr.1 || isZero tr.2.1) = true := by
  rcases tr with ⟨x, y, ⟨⟩⟩
  have key : ∀ st, (simulateQ tick (twoVerifier.decide stmt _
      (toPlainView twoChallenges ⟨x, y, ⟨⟩⟩)).run).run' st =
        pure (if (stmt || isZero x || isZero y) = true then some st else none) :=
    fun _ => rfl
  simp only [Verifier.validAcceptance, key, evalDist_pure]
  by_cases hb : (stmt || isZero x || isZero y) = true
  · simp [hb, Oracle.Problem.language, twoOutput]
  · simp [hb]

/-- The state records whether the statement or a challenge drawn so far makes acceptance
certain. -/
def twoState : StateFunction plainSig twoChallenges Bool (boolProblem.admissible ())
    (boolProblem.language ()) (fun stmt tr => twoVerifier.validAcceptance tick stmt tr
      (twoOutput.language tr.path)) where
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

/-- A uniform draw from `Fin 4` is zero with probability one quarter. -/
theorem uniform_zero : 𝒟[($ᵗ Fin 4 : ProbComp (Fin 4))] {0} = 1 / 4 := by
  rw [SampleableType.evalDist_uniformSample_singleton, Fintype.card_fin, one_div]
  rfl

/-- The two-challenge verifier is round-by-round sound with error one quarter at each node. -/
theorem two_rbrSoundness :
    twoVerifier.rbrSoundness tick boolProblem twoOutput drawTwo (fun _ => 1 / 4) := by
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

/-- Every path of the two-challenge protocol meets at most two challenge nodes. -/
theorem two_card (path : Path twoChallenges) :
    (challengeNodesOn plainSig twoChallenges path).card ≤ 2 := by
  rcases path with ⟨⟨⟩, ⟨⟩, ⟨⟩⟩
  rfl

example (init : ProbComp Nat) :
    twoVerifier.soundness init tick drawTwo boolProblem twoOutput (2 • (1 / 4)) :=
  Verifier.soundness_of_rbrSoundness_uniform two_rbrSoundness (fun _ => le_rfl) two_card

-- Disposition S1/S2: the path bound recovers arbitrary finite rank-indexed sums.
example {P : PFunctor.{1, 0}} {l : PFunctor.Lens P rolePoly} {s : FreeM P PUnit}
    (rank : ChallengeNode l s → ℕ) (error : ℕ → ℝ≥0∞) (count : ℕ)
    (hinj : ∀ path, Set.InjOn rank (challengeNodesOn l s path))
    (hrange : ∀ path c, c ∈ challengeNodesOn l s path → rank c < count) :
    ⨆ path : Path s, ∑ c ∈ challengeNodesOn l s path, error (rank c) ≤
      ∑ j ∈ Finset.range count, error j := by
  simpa only [Nat.Ico_zero_eq_range] using
    iSup_sum_challengeNodesOn_le_rank_sum (fun c => error (rank c)) rank error 0 count
      hinj (fun path c hc => Finset.mem_Ico.mpr ⟨Nat.zero_le _, hrange path c hc⟩)
      (fun _ => le_rfl)

/-! ### Prefix-dependent challenge samplers -/

namespace AdaptiveChallenges

/-- Two erased Boolean challenges have one fixed shape path. -/
abbrev protocol : Protocol := .liftBind (.challenge Bool) (fun _ =>
  .liftBind (.challenge Bool) (fun _ => .pure ⟨⟩))

/-- The first challenge comes from the ambient service. -/
abbrev ambient : OracleSpec Unit := Unit →ₒ Bool

/-- The second challenge is the negation of the first, without changing shape. -/
def draws : PrefixChallengePrograms plainSig ambient protocol
  | _, _, .root _, _, _ => ambient.query ()
  | _, _, .down _ (.root _), _, history => pure (!history.1.1)
  | _, _, .down _ (.down _ tail), _, _ => nomatch tail

/-- A focal strategy that observes both challenges and returns a unit output. -/
def prover : Prover plainSig ambient protocol (fun _ => Unit) :=
  pure (fun _ => pure (fun _ => pure ()))

/-- The actual executor retains the first challenge when choosing the second sampler. -/
theorem execution : runPrefixChallenges plainSig protocol prover draws =
    (do let x ← ambient.query ()
        pure ⟨⟨x, !x, ⟨⟩⟩, (), ⟨⟩⟩) := by
  rfl

/-- The ambient service answers with a uniform bit. -/
def uniformBit : QueryImpl ambient ProbComp := fun _ => $ᵗ Bool

/-- Whether two challenges are equal. -/
def same (x y : Bool) : Bool := x == y

/-- Accept a true statement or two equal challenges. -/
def agree (stmt : Bool) (tr : Transcript plainSig protocol) : Bool :=
  stmt || same tr.1 tr.2.1

/-- The state is true at a true statement, and at a leaf whose two challenges are equal. -/
def state : StateFunction plainSig protocol Bool (fun _ => True) (· = true)
    (fun stmt tr => agree stmt tr = true) where
  toFun {_} sp history stmt := match sp, history with
    | .root _, _ => stmt = true
    | .down _ (.root _), _ => stmt = true
    | .down _ (.down _ _), history => (stmt || same history.1.1 history.2.1.1) = true
  root _ _ h := h
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
        exact h

/-- On the adaptive experiment, `prEvent_runPrefixChallenges_soundness` with zero node errors
shows that a false statement is never accepted: the second draw always differs from the first. -/
theorem soundness :
    Pr{let y ← simulateQ uniformBit (runPrefixChallenges plainSig protocol prover draws >>=
      fun r => pure (agree false r.1))}[y = true] = 0 := by
  refine le_antisymm ((prEvent_runPrefixChallenges_soundness plainSig state uniformBit
    (· = true) (fun _ => 0) draws (fun tr _ => pure (agree false tr)) false trivial
    Bool.false_ne_true ?_ ?_ prover).trans (by simp)) zero_le
  · intro a next sp h history
    refine le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun x hx hflip => ?_)
    cases sp with
    | root => exact hflip.1 hflip.2
    | down b tail =>
      cases tail with
      | root =>
        rcases history with ⟨⟨y, _⟩, ⟨⟩⟩
        have hx' : x ∈ support (simulateQ uniformBit (pure (!y) : OracleComp ambient Bool)) := hx
        simp only [simulateQ_pure, support_pure, Set.mem_singleton_iff] at hx'
        subst hx'
        cases y <;> exact Bool.false_ne_true hflip.2
      | down _ tail => cases tail
  · intro tr _ hpos
    by_contra hne
    simp [hne] at hpos

end AdaptiveChallenges

/-! ### A full-prefix draw reads oracle messages

The generic prefix runner passes each sender move, an oracle message included, to later draws.
Two executions whose prefixes have the same `viewSig` projection can therefore receive different
challenges. An oracle-verifier API that exposes a prefix draw restricts it to the view.
-/

namespace OracleMessageDraw

/-- A Boolean oracle message, then a Boolean challenge. -/
abbrev protocol : OracleProtocol.{0, 0} :=
  .liftBind (.oracle Bool OracleInterface.instDefault) fun _ =>
    .liftBind (.challenge Bool) fun _ => .pure ⟨⟩

/-- The draw makes no queries; the specification is only the draw's query interface. -/
abbrev spec : OracleSpec Unit := Unit →ₒ Bool

/-- The full-prefix draw sends the oracle bit as the challenge. -/
def copyOracle : PrefixChallengePrograms oracleSig spec protocol
  | _, _, .root _, h, _ => nomatch h
  | _, _, .down _ (.root _), _, history => pure history.1.1
  | _, _, .down _ (.down _ tail), _, _ => nomatch tail

/-- The prover sends the oracle bit `b`, then observes the challenge. -/
def prover (b : Bool) : Prover oracleSig spec protocol (fun _ => Unit) :=
  pure ⟨b, pure fun _ => pure ()⟩

/-- The generic run returns the oracle bit as the challenge. -/
theorem execution (b : Bool) :
    runPrefixChallenges oracleSig protocol (prover b) copyOracle = pure ⟨⟨b, b, ⟨⟩⟩, (), ⟨⟩⟩ :=
  rfl

/-- The verifier's view erases the oracle bit, so runs with the same challenge have equal views.
-/
theorem view_eq (x : Bool) :
    (toView protocol ⟨true, x, ⟨⟩⟩).val = (toView protocol ⟨false, x, ⟨⟩⟩).val :=
  rfl

end OracleMessageDraw

-- Disposition S4: models and their result types may vary with the authored prefix.
example {α : Type} (author : OptionT ProbComp α) {Result : α → Type}
    (sample : (a : α) → ProbComp (Result a)) (flip : (a : α) → Result a → Prop)
    (rank : α → ℕ) (error : ℕ → ℝ≥0∞) (round : ℕ)
    (hlocal : ∀ a, Pr{let r ← sample a}[flip a r] ≤ error (rank a))
    (hrank : ∀ a, rank a = round) :
    Pr{let escape ← (author >>= fun a => flip a <$> OptionT.lift (sample a))}[escape] ≤
      error round :=
  flip_random_model_le author sample flip (fun a => error (rank a)) hlocal
    (fun a => le_of_eq (congrArg error (hrank a)))

/-! ### A handler with missing probability mass -/

/-- Each ambient call succeeds with probability one half, independently of the challenge. -/
def optionalAmbient : QueryImpl counter (OptionT ProbComp) := fun _ =>
  OptionT.mk do
    let b ← ($ᵗ Bool : ProbComp Bool)
    pure (if b then some 0 else none)

/-- Generic implication allows a target monad whose result universe is above its data. -/
example {m : Type → Type 1} [Monad m] [LawfulMonad m] [EvalDistSemantics m]
    [LawfulEvalDistSemantics m]
    {ι : Type} {S : Type} {ambient : OracleSpec ι} {s : Protocol}
    {T : Path s → Type}
    (V : Verifier ambient s S T) (H : QueryImpl (ambient + challengeSpec plainSig s) m)
    (draw : QueryImpl (challengeSpec plainSig s) ProbComp)
    (input : StatementProblem S) (output : PathProblem s T)
    (ε : ChallengeNode plainSig s → ℝ≥0∞) (fresh : FreshChallenges H draw)
    (h : rbrSoundness plainSig s (input.admissible ()) (input.language ())
      (V.validAcceptanceWith (fun q => H (.inl q)) (output.language)) draw ε) :
    V.soundnessWith H input output (∑' c, ε c) :=
  Verifier.soundnessWith_of_rbrSoundness_tsum fresh h

/-- The optional handler keeps the challenge draw separate from ambient failure. -/
def optionalHandler : QueryImpl (counter + challengeSpec plainSig coin) (OptionT ProbComp) :=
  QueryImpl.addLift optionalAmbient draw

/-- The optional challenge action has exactly the specified event marginals. -/
theorem optionalHandler_fresh : FreshChallenges optionalHandler draw := by
  intro c event
  simp only [optionalHandler, QueryImpl.addLift_def, QueryImpl.add_apply_inr,
    QueryImpl.liftTarget_apply, OptionT.prEvent_liftM]

/-- This verifier accepts a true input or a true challenge. Its prover may use the failing
ambient service even though its decision needs no ambient calls. -/
def optionalVerifier : Verifier counter coin Bool (fun _ => Nat) where
  decide stmt _ view := OptionT.mk
    (pure (if (stmt || view.val.1) = true then some 0 else none))

/-- The optional verifier has the same acceptance condition as the counter verifier. -/
theorem optionalAcceptance (stmt : Bool) (tr : Transcript plainSig coin) :
    optionalVerifier.validAcceptanceWith optionalAmbient anyOutput.language stmt tr ↔
      coinVerifier.validAcceptance tick stmt tr
        (anyOutput.language tr.path) := by
  classical
  rw [validAcceptance_iff (fun _ => ⟨(), trivial⟩)]
  rcases tr with ⟨x, ⟨⟩⟩
  have key : simulateQ optionalAmbient (optionalVerifier.decide stmt _
      (toPlainView coin ⟨x, ⟨⟩⟩)).run =
        (pure (if (stmt || x) = true then some 0 else none) : OptionT ProbComp (Option Nat)) := rfl
  rw [Verifier.validAcceptanceWith, Verifier.validAcceptanceUsing, key, prEvent_pure]
  cases stmt <;> cases x <;> simp [Oracle.Problem.language, anyOutput]

/-- The one-challenge certificate applies to the optional handler without a state encoding. -/
theorem optional_rbrSoundness :
    rbrSoundness plainSig coin (boolProblem.admissible ()) (boolProblem.language ())
      (optionalVerifier.validAcceptanceWith optionalAmbient anyOutput.language) draw
      (fun _ => 1 / 2) := by
  obtain ⟨F, hF⟩ := coin_rbrSoundness
  refine ⟨{ toFun := F.toFun, root := F.root, send := F.send, leaf := ?_ }, hF⟩
  intro sp history stmt hfalse hacc
  exact F.leaf sp history stmt hfalse ((optionalAcceptance _ _).mp hacc)

/-- Generic soundness applies in `OptionT ProbComp`, where ambient queries lose mass. -/
theorem optional_soundness :
    optionalVerifier.soundnessWith optionalHandler boolProblem anyOutput (1 / 2) := by
  simpa only [one_nsmul] using
    Verifier.soundnessWith_of_rbrSoundness_uniform optionalHandler_fresh optional_rbrSoundness
      (fun _ => le_rfl) coin_card

/-- The actual optional run with a prover that reads the counter before and after the challenge:
the counter reads may fail, and the challenge is the uniform draw. -/
theorem optional_counting_run (stmt : Bool) :
    simulateQ optionalHandler (optionalVerifier.run stmt countingProver) = (do
      let _ ← optionalAmbient ()
      let b ← (OptionT.lift ($ᵗ Bool : ProbComp Bool) : OptionT ProbComp Bool)
      let n ← optionalAmbient ()
      pure ⟨⟨b, ⟨⟩⟩, n, if (stmt || b) = true then some 0 else none⟩ :
        OptionT ProbComp (Outcome plainSig coin (fun _ => Nat) (fun _ => Nat))) := by
  rfl

/-- `optional_soundness` bounds the acceptance probability of that run on a false statement. -/
theorem optional_counting_bound :
    Pr{let obs ← simulateQ optionalHandler (optionalVerifier.run false countingProver)}[
      ∃ t, obs.2.2 = some t ∧ anyOutput.language (Transcript.path obs.1) t] ≤ 1 / 2 :=
  optional_soundness (fun _ => Nat) false trivial (fun ⟨_, h⟩ => Bool.false_ne_true h)
    countingProver

/-- The oracle implication also accepts a handler in the optional distribution monad.
Its challenge premise is discharged by the separate lifted draw. -/
example {ι : Type} {I : Type} {S : Type}
    {ambient : OracleSpec ι} {s : OracleProtocol} {T : Path s → Type}
    {A : I → Type} {J : Path s → Type} {B : (p : Path s) → J p → Type}
    {inputs : OracleFamily.{0, 0, 0} I A}
    {outputs : (p : Path s) → OracleFamily.{0, 0, 0} (J p) (B p)}
    (V : OracleVerifier ambient s S T inputs outputs)
    (impl : QueryImpl ambient (OptionT ProbComp))
    (draw : QueryImpl (challengeSpec oracleSig s) ProbComp)
    (input : StatementProblem (S × (∀ i, A i))) (output : PathProblem s (OracleVerifier.Output T B))
    (ε : ChallengeNode oracleSig s → ℝ≥0∞)
    (h : rbrSoundness oracleSig s (input.admissible ()) (input.language ())
      (V.validAcceptanceWith impl (output.language)) draw ε) :
    V.soundnessWith
      (impl.addLift draw : QueryImpl (ambient + challengeSpec oracleSig s) (OptionT ProbComp))
      input output (∑' c, ε c) := by
  apply OracleVerifier.soundnessWith_of_rbrSoundness_tsum (h := h)
  intro c event
  simp only [QueryImpl.addLift_def, QueryImpl.add_apply_inr, QueryImpl.liftTarget_apply,
    OptionT.prEvent_liftM]

/-- The ambient handler really loses half its mass; this is not a lossless transformer test. -/
theorem optionalAmbient_mass : Pr{let _ ← optionalAmbient ()}[True] = 1 / 2 := by
  rw [OptionT.prEvent_eq_run]
  change Pr{let v ← (fun b => if b then some (0 : Nat) else none) <$>
    ($ᵗ Bool : ProbComp Bool)}[v.elim False (fun _ => True)] = 1 / 2
  rw [prEvent_map, prEvent_eq_evalDist_of_discrete]
  convert uniform_true using 1
  congr 1
  ext b
  cases b <;> simp

/-! ### Failure of the actual execution -/

namespace EmptyResponse

/-- An ambient service without any possible answer. -/
abbrev ambient : OracleSpec Unit := Unit →ₒ Empty

/-- Interpret every service request by failure. -/
def handler : QueryImpl ambient (OptionT ProbComp) := fun _ => failure

/-- One public sender move. -/
def protocol : Protocol := .liftBind (.message Unit) (fun _ => .pure ⟨⟩)

/-- The prover must obtain an impossible answer before sending. -/
def prover : Prover plainSig ambient protocol (fun _ => Unit) := do
  let impossible ← liftM (ambient.query ())
  nomatch impossible

/-- A final decision that accepts every completed interaction. -/
def verifier : Verifier ambient protocol Unit (fun _ => Unit) where
  decide _ _ _ := pure ()

/-- The empty-response query fails before the prover can produce a move. -/
theorem interpreted_action : simulateQ handler prover =
    (failure : OptionT ProbComp ((_move : Unit) ×
      Prover plainSig ambient (.pure ⟨⟩) (fun _ => Unit))) := by
  simp [prover, handler, simulateQ_bind]

/-- There are no challenge nodes in the one-message protocol. -/
def noChallenges : QueryImpl (challengeSpec plainSig protocol) ProbComp := fun c => by
  rcases c with ⟨node, h⟩
  rcases node with root | ⟨_, node⟩
  · cases h
  · nomatch node

/-- The actual verifier run has no returned outcome, including returned rejection. -/
theorem run_mass :
    Pr{let _ ← (simulateQ
      (handler.addLift noChallenges :
        QueryImpl (ambient + challengeSpec plainSig protocol) (OptionT ProbComp))
      (verifier.run () prover))}[True] = 0 := by
  have hfail : simulateQ
      (handler.addLift noChallenges :
        QueryImpl (ambient + challengeSpec plainSig protocol) (OptionT ProbComp))
      (verifier.run () prover) =
        (failure : OptionT ProbComp (Outcome plainSig protocol (fun _ => Unit)
          (fun _ => Unit))) := by
    rfl
  rw [hfail]
  simp

end EmptyResponse

end Interaction.ImplicationsTests

run_cmd do
  for name in [``Interaction.Verifier.soundness_of_rbrSoundness,
      ``Interaction.Verifier.soundness_of_rbrSoundness_tsum,
      ``Interaction.Verifier.soundness_of_rbrSoundness_uniform,
      ``Interaction.OracleVerifier.soundness_of_rbrSoundness,
      ``Interaction.OracleVerifier.soundness_of_rbrSoundness_tsum,
      ``Interaction.OracleVerifier.soundness_of_rbrSoundness_uniform,
      ``Interaction.runPrefixChallenges_eq_run,
      ``Interaction.prEvent_runPrefixChallenges_le,
      ``Interaction.prEvent_runPrefixChallenges_soundness,
      ``Interaction.flip_random_model_le,
      ``Interaction.ImplicationsTests.AdaptiveChallenges.execution,
      ``Interaction.ImplicationsTests.AdaptiveChallenges.soundness,
      ``Interaction.ImplicationsTests.OracleMessageDraw.execution,
      ``Interaction.ImplicationsTests.OracleMessageDraw.view_eq,
      ``Interaction.ImplicationsTests.optional_counting_run,
      ``Interaction.ImplicationsTests.optional_counting_bound,
      ``Interaction.prEvent_run_le,
      ``Interaction.prEvent_run_state_le,
      ``Interaction.prEvent_run_state_le_of_local,
      ``Interaction.ReceiverPrefix.flip_le_of_encoded_marginals,
      ``Interaction.iSup_sum_challengeNodesOn_le_rank_sum,
      ``Interaction.Verifier.soundnessUsing_of_localSoundness,
      ``Interaction.OracleVerifier.soundnessUsing_of_localSoundness,
      ``Interaction.Verifier.soundness_iff_soundnessUsing,
      ``Interaction.OracleVerifier.soundness_iff_soundnessUsing,
      ``Interaction.Verifier.validAcceptance_iff_validAcceptanceUsing,
      ``Interaction.OracleVerifier.validAcceptance_iff_validAcceptanceUsing,
      ``Interaction.Verifier.soundnessWith_of_rbrSoundness,
      ``Interaction.OracleVerifier.soundnessWith_of_rbrSoundness,
      ``Interaction.ImplicationsTests.optional_soundness,
      ``Interaction.ImplicationsTests.optionalAmbient_mass,
      ``Interaction.ImplicationsTests.EmptyResponse.interpreted_action,
      ``Interaction.ImplicationsTests.EmptyResponse.run_mass,
      ``Interaction.simulateQ_addLift_bundleAnswer,
      ``Interaction.StateFunction.escapeAlong,
      ``Interaction.flip_random_prefix_le,
      ``Interaction.flip_random_history_le,
      ``Interaction.ImplicationsTests.afterBit_node_ne,
      ``Interaction.ImplicationsTests.two_rbrSoundness] do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "{name} depends on {ax}"
