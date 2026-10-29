/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.Security.Basic
public import ArkLib.OracleReduction.Security.RbrGame

/-!
  # Round-by-Round Security Definitions

  This file defines round-by-round security notions for (oracle) reductions.
-/

@[expose] public section

noncomputable section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

namespace Extractor

/-- A **one-shot** round-by-round extractor is a function that:
- Takes in index `m : Fin (n + 1)`
- Takes in the input statement `stmtIn : StmtIn`
- Takes in a partial transcript up to round `m`
- Takes in the prover's query log (TODO: refine this, verifier's query log as well?)

and returns an input witness `witIn : WitIn`.

This is the old definition of round-by-round extractor, which is less general than the new
definition (i.e. the input witness is extracted immediately, "in one shot", unlike the general
definition where the input witness is derived via intermediate witnesses). -/
def RoundByRoundOneShot
    (oSpec : OracleSpec ι) (StmtIn WitIn : Type) {n : ℕ} (pSpec : ProtocolSpec n) :=
  (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → QueryLog oSpec → WitIn

/-- A one-shot round-by-round extractor is **monotone** if its success probability on a given query
  log is the same as the success probability on any extension of that query log.

  TODO: refine this -/
class RoundByRoundOneShot.IsMonotone (E : RoundByRoundOneShot oSpec StmtIn WitIn pSpec)
    (relIn : Set (StmtIn × WitIn)) where
  is_monotone : ∀ roundIdx stmtIn transcript,
    ∀ proveQueryLog₁ proveQueryLog₂ : oSpec.QueryLog,
    -- ∀ verifyQueryLog₁ verifyQueryLog₂ : oSpec.QueryLog,
    proveQueryLog₁.Sublist proveQueryLog₂ →
    -- verifyQueryLog₁.Sublist verifyQueryLog₂ →
    -- Placeholder condition for now, will need to consider the whole game w/ probabilities
    (stmtIn, E roundIdx stmtIn transcript proveQueryLog₁) ∈ relIn →
      (stmtIn, E roundIdx stmtIn transcript proveQueryLog₂) ∈ relIn

/-- A **round-by-round extractor** is a tuple of algorithms that iteratively extracts the input
  witness from the output witness, through a series of intermediate witnesses
  (indexed by `m : Fin (n + 1)`). Formally, it contains the following components:

  - A function `extractIn : StmtIn → WitMid 0 → WitIn` from the initial intermediate witness
    to the input witness
  - A function `extractMid : (m : Fin n) → StmtIn → Transcript m.succ pSpec`
    `→ WitMid m.succ → WitMid m.castSucc` that extracts the intermediate witness for round `m`
    from the intermediate witness for round `m+1`, using the transcript up to round `m+1` and
    the intermediate witness for round `m+1`
  - A function `extractOut : StmtIn → FullTranscript pSpec → WitOut → WitMid (.last n)` that
    constructs the intermediate witness for the final round from the output witness

  The extractor processes rounds in decreasing order: `n → n-1 → ... → 1 → 0`, using
  intermediate witness types `WitMid m` for each round `m`.
-/
structure RoundByRound
    (oSpec : OracleSpec ι) (StmtIn WitIn WitOut : Type) {n : ℕ} (pSpec : ProtocolSpec n)
    (WitMid : Fin (n + 1) → Type) where
  /-- Extract an input witness from the initial intermediate witness. -/
  extractIn : StmtIn → WitMid 0 → WitIn
  /-- Extract intermediate witness for round `m` from intermediate witness for round `m+1`,
    using the transcript up to round `m+1` -/
  extractMid : (m : Fin n) → StmtIn → Transcript m.succ pSpec → WitMid m.succ → WitMid m.castSucc
  /-- Construct the intermediate witness for the final round from the output witness -/
  extractOut : StmtIn → FullTranscript pSpec → WitOut → WitMid (.last n)

/-- The extractor with no witnesses. -/
def RoundByRound.unit : RoundByRound oSpec StmtIn Unit Unit pSpec (fun _ => Unit) where
  extractIn := fun _ _ => ()
  extractMid := fun _ _ _ _ => ()
  extractOut := fun _ _ _ => ()

namespace RoundByRoundOneShot

/-- A one-shot round-by-round extractor can be converted to the general round-by-round extractor
  format, where all intermediate witness types are equal to the input witness type.

  Note that the converse is _not_ true: it's not possible in general to convert a general
  round-by-round extractor to a one-shot one. -/
def toRoundByRound (E : RoundByRoundOneShot oSpec StmtIn WitIn pSpec) :
    RoundByRound oSpec StmtIn WitIn WitOut pSpec (fun _ => WitIn) where
  extractIn := fun _ => _root_.id
  extractMid := fun m stmtIn tr witIn =>
    if m.castSucc = 0 then witIn else E m.castSucc stmtIn (Fin.init tr) default
  extractOut := fun stmtIn tr _ => E (.last n) stmtIn tr default

open Classical in
/-- The relation-aware conversion of a one-shot extractor into a general round-by-round one.

This differs from `toRoundByRound` in the intermediate step: it returns a witness that is *valid for
the input relation* whenever one exists at all, rather than the extractor's output or the witness it
was handed. The choice is classical. Within ArkLib's current extensional security interface,
`extractMid` is a mathematical function rather than an algorithm with a tracked running time, so
selecting a valid witness non-constructively preserves the property formalized here. It does not
establish the extraction-time bounds present in algorithmic formulations of round-by-round
knowledge soundness.

This relation-aware variant retains the extraction-failure condition needed by the
one-shot-to-general security implication. -/
noncomputable def toRoundByRoundOfRel (E : RoundByRoundOneShot oSpec StmtIn WitIn pSpec)
    (relIn : Set (StmtIn × WitIn)) :
    RoundByRound oSpec StmtIn WitIn WitOut pSpec (fun _ => WitIn) where
  extractIn := fun _ => _root_.id
  extractMid := fun _ stmtIn _ witIn => if h : ∃ v, (stmtIn, v) ∈ relIn then h.choose else witIn
  extractOut := fun stmtIn tr _ => E (.last n) stmtIn tr default

open Classical in
/-- An unbounded one-shot extractor, selecting an input witness whenever one exists.
This is noncomputable because it chooses a witness from an arbitrary relation. -/
noncomputable def ofRelation [Nonempty WitIn] (relIn : Set (StmtIn × WitIn)) :
    RoundByRoundOneShot oSpec StmtIn WitIn pSpec :=
  fun _ stmt _ _ => if h : ∃ w, (stmt, w) ∈ relIn then h.choose else Classical.ofNonempty

end RoundByRoundOneShot

end Extractor

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- The round-by-round extraction-failure event at challenge `i`: some intermediate witness
satisfies the knowledge state after the challenge, while its extraction fails it before. This is
the event `Verifier.rbrKnowledgeSoundnessWorstCase` bounds, named so that per-protocol bounds can
state it. -/
@[reducible]
def rbrExtractionFailureEvent {WitMid : Fin (n + 1) → Type}
    (kSF : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → WitMid m → Prop)
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (i : pSpec.ChallengeIdx) (stmtIn : StmtIn)
    (transcript : Transcript i.1.castSucc pSpec) (challenge : pSpec.Challenge i) : Prop :=
  ∃ witMid : WitMid i.1.succ,
    ¬ kSF i.1.castSucc stmtIn transcript
      (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
    kSF i.1.succ stmtIn (transcript.concat challenge) witMid

namespace Verifier

section RoundByRound

/-- A (deterministic) state function for a verifier, with respect to input language `langIn` and
  output language `langOut`. This is used to define round-by-round soundness. -/
structure StateFunction
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    where
  toFun : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop
  /-- For all input statement not in the language, the state function is false for that statement
    and the empty transcript -/
  toFun_empty : ∀ stmt, toFun 0 stmt default → stmt ∈ langIn
  /-- If the state function is false for a partial transcript, and the next message is from the
    prover to the verifier, then the state function is also false for the new partial transcript
    regardless of the message -/
  toFun_next : ∀ m, pSpec.dir m = .P_to_V →
    ∀ stmt tr, ¬ toFun m.castSucc stmt tr →
    ∀ msg, ¬ toFun m.succ stmt (tr.concat msg)
  /-- If the state function is false for a full transcript, the verifier will not output a statement
    in the output language in a fresh-`init` experiment. For guarded verifiers, the guarded
    terminal lemmas make this faithful to execution from the current shared oracle state. -/
  toFun_full : ∀ stmt tr, ¬ toFun (.last n) stmt tr →
    Pr{let stmtOut ← (OptionT.mk do
      (simulateQ impl (verifier.run stmt tr)).run' (← init))}[stmtOut ∈ langOut] = 0

/-- A generalized extractor-aware knowledge state function for a verifier, with respect to input
relation `relIn`, output relation `relOut`, and stage-dependent witness types `WitMid`. This is used
to define round-by-round knowledge soundness.

Across prover moves, `extractMid` may transform the witness before testing the earlier state.
The terminal law requires positive-probability related output to imply the extracted final state.
A true initial state yields a related witness via `extractIn`; relation membership need not make
that state true. These contracts suffice for `toStateFunction` and the bad-transition proof. -/
structure KnowledgeStateFunction
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    {WitMid : Fin (n + 1) → Type}
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    where
  /-- The knowledge state function: takes in round index, input statement, transcript up to that
      round, and intermediate witness of that round, and returns True/False. -/
  toFun : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → WitMid m → Prop
  /-- A true initial state yields a related extracted input witness. -/
  toFun_empty : ∀ stmtIn witMid,
    toFun 0 stmtIn default witMid → ⟨stmtIn, extractor.extractIn stmtIn witMid⟩ ∈ relIn
  /-- If the state function is true for a partial transcript extended with a prover message, then
    the state function is also true for the original partial transcript with the extracted
    intermediate witness -/
  toFun_next : ∀ m, pSpec.dir m = .P_to_V →
    ∀ stmtIn tr msg witMid, toFun m.succ stmtIn (tr.concat msg) witMid →
      toFun m.castSucc stmtIn tr (extractor.extractMid m stmtIn (tr.concat msg) witMid)
  /-- If the verifier can output a statement `stmtOut` that is in the output relation with some
    output witness `witOut`, then the state function is true for the full transcript and the
    extracted last middle witness. This describes a fresh-`init` experiment; the guarded
    terminal lemmas make it faithful to the current shared oracle state for guarded verifiers. -/
  toFun_full : ∀ stmtIn tr witOut,
    Pr{let stmtOut ← (OptionT.mk do
      (simulateQ impl (verifier.run stmtIn tr)).run' (← init))}[
        (stmtOut, witOut) ∈ relOut] > 0 →
    toFun (.last n) stmtIn tr (extractor.extractOut stmtIn tr witOut)

omit [∀ i, SampleableType (pSpec.Challenge i)] in
variable {init impl} in
/-- A knowledge state function's value depends on its round, transcript and witness only up to
(heterogeneous) equality. -/
theorem KnowledgeStateFunction.toFun_congr {V : Verifier oSpec StmtIn StmtOut pSpec}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {WitMid : Fin (n + 1) → Type}
    {E : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
    (K : V.KnowledgeStateFunction init impl relIn relOut E) {k k' : Fin (n + 1)} (hk : k = k')
    (stmt : StmtIn) {T : pSpec.Transcript k} {T' : pSpec.Transcript k'} (hT : HEq T T')
    {w : WitMid k} {w' : WitMid k'} (hw : HEq w w') :
    K.toFun k stmt T w ↔ K.toFun k' stmt T' w' := by
  subst hk
  cases hT
  cases hw
  rfl

/-- A knowledge state function gives rise to a state function via quantifying over the witness -/
def KnowledgeStateFunction.toStateFunction
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} {WitMid : Fin (n + 1) → Type}
    {extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
    (kSF : KnowledgeStateFunction init impl relIn relOut verifier extractor) :
      verifier.StateFunction init impl relIn.language relOut.language where
  toFun := fun m stmtIn tr => ∃ witMid, kSF.toFun m stmtIn tr witMid
  toFun_empty := by
    rintro stmtIn ⟨witMid, h⟩
    exact (Set.mem_language_iff relIn stmtIn).2 ⟨_, kSF.toFun_empty stmtIn witMid h⟩
  toFun_next := fun m hDir stmtIn tr hToFunNext msg => by
    simp only [not_exists]
    intro witMid hToFunNext
    have := kSF.toFun_next m hDir stmtIn tr msg witMid hToFunNext
    simp_all
  toFun_full := fun stmtIn tr hToFunFull => by
    simp only [Fin.val_last, Set.mem_image, Prod.exists, exists_and_right, exists_eq_right,
      OptionT.prEvent_mk_eq_zero_iff, not_exists]
    intro stmtOut hStmtOut witOut hRelOut
    have hProb :
        Pr{let stmtOut ← (OptionT.mk do
          (simulateQ impl (verifier.run stmtIn tr)).run' (← init))}[
            (stmtOut, witOut) ∈ relOut] > 0 := by
      simp only [Fin.val_last, gt_iff_lt, OptionT.prEvent_mk_pos_iff]
      exact ⟨stmtOut, hStmtOut, hRelOut⟩
    have := kSF.toFun_full stmtIn tr witOut hProb
    simp_all

/-- A (deterministic) knowledge state function for a verifier, with respect to input language
  `langIn` and output language `langOut`. This is used to define one-shot round-by-round knowledge
  soundness. Note the different condition for the empty transcript: `toFun 0` is supposed to be
  always zero. -/
structure KnowledgeStateFunctionOneShot
    (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    where
  toFun : (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop
  /-- For all input statement not in the language, the state function is false for the empty
    transcript -/
  toFun_empty : ∀ stmtIn, ¬ toFun 0 stmtIn default
  /-- If the state function is false for a partial transcript, and the next message is from the
    prover to the verifier, then the state function is also false for the new partial transcript
    regardless of the message -/
  toFun_next : ∀ m, pSpec.dir m = .P_to_V →
    ∀ stmt tr msg, ¬ toFun m.castSucc stmt tr → ¬ toFun m.succ stmt (tr.concat msg)
  /-- If the state function is false for a full transcript, the verifier will not output a statement
    in the output language -/
  toFun_full : ∀ stmt tr, ¬ toFun (.last n) stmt tr →
    Pr{let stmtOut ← (OptionT.mk do
      (simulateQ impl (verifier.run stmt tr)).run' (← init))}[stmtOut ∈ langOut] = 0

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- The one-shot state function is false at any round index that is `0`, for any transcript.

`toFun_empty` states this for the literal index `0` and the canonical empty transcript; this is the
transported form, which is what round-by-round arguments actually need (the index at hand is
typically `m.castSucc` together with a proof that it equals `0`). -/
theorem KnowledgeStateFunctionOneShot.toFun_empty_of_eq_zero
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    (stF : KnowledgeStateFunctionOneShot init impl langIn langOut verifier)
    (stmtIn : StmtIn) (m : Fin (n + 1)) (hm : m = 0) (tr : Transcript m pSpec) :
    ¬ stF.toFun m stmtIn tr := by
  subst hm
  have : tr = default := by ext i; exact Fin.elim0 i
  subst this
  exact stF.toFun_empty stmtIn

/-- A state function and a one-shot extractor induce a knowledge state function when the
extractor recovers a valid witness at a true initial state. Intermediate extraction uses
noncomputable choice of a related witness. -/
noncomputable def StateFunction.toKnowledgeStateFunctionOfOneShot
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    (stF : StateFunction init impl relIn.language relOut.language verifier)
    (oneShotE : Extractor.RoundByRoundOneShot oSpec StmtIn WitIn pSpec)
    (hE : ∀ stmt, stF.toFun 0 stmt default → (stmt, oneShotE 0 stmt default default) ∈ relIn) :
    verifier.KnowledgeStateFunction init impl relIn relOut
      (oneShotE.toRoundByRoundOfRel (WitOut := WitOut) relIn) where
  toFun := fun m stmtIn tr witIn => if m = 0 then (stmtIn, witIn) ∈ relIn else
    stF.toFun m stmtIn tr ∨ ∃ v, (stmtIn, v) ∈ relIn
  toFun_empty := fun stmtIn witIn h => by
    simpa [Extractor.RoundByRoundOneShot.toRoundByRoundOfRel] using h
  toFun_next := fun m hDir stmtIn tr msg witIn h => by
    rw [ite_eq_right (Fin.succ_ne_zero m)] at h
    have hprev : stF.toFun m.castSucc stmtIn tr ∨ ∃ v, (stmtIn, v) ∈ relIn :=
      h.imp_left fun hsucc => not_not.mp fun hcast =>
        stF.toFun_next m hDir stmtIn tr hcast msg hsucc
    by_cases hm : m.castSucc = 0
    · rw [ite_eq_left hm]
      have hex : ∃ v, (stmtIn, v) ∈ relIn := by
        rcases hprev with hprev | hex
        · have hzero : stF.toFun 0 stmtIn default := by
            have htransport : ∀ (k : Fin (n + 1)) (tr : Transcript k pSpec),
                k = 0 → stF.toFun k stmtIn tr → stF.toFun 0 stmtIn default := by
              intro k tr hk
              subst hk
              simp [Subsingleton.elim tr default]
            exact htransport _ tr hm hprev
          exact (Set.mem_language_iff relIn stmtIn).1 (stF.toFun_empty stmtIn hzero)
        · exact hex
      simpa [Extractor.RoundByRoundOneShot.toRoundByRoundOfRel, hex] using hex.choose_spec
    · exact (ite_eq_right hm).symm ▸ hprev
  toFun_full := fun stmtIn tr witOut h => by
    have hLang :
        0 < Pr{let stmtOut ← (OptionT.mk do
          (simulateQ impl (verifier.run stmtIn tr)).run' (← init))}[
            stmtOut ∈ relOut.language] :=
      h.trans_le (prEvent_mono _ _ _ fun stmtOut hrel ↦
        (Set.mem_language_iff relOut stmtOut).2 ⟨witOut, hrel⟩)
    have hstF : stF.toFun (.last n) stmtIn tr := by
      by_contra hfalse
      rw [stF.toFun_full stmtIn tr hfalse] at hLang
      exact (lt_irrefl 0 hLang).elim
    by_cases hn : (Fin.last n : Fin (n + 1)) = 0
    · simp only [hn, ↓reduceIte]
      simp only [Extractor.RoundByRoundOneShot.toRoundByRoundOfRel]
      clear h hLang
      generalize hk : (Fin.last n : Fin (n + 1)) = k at tr hstF ⊢
      have hk0 : k = 0 := hk.symm.trans hn
      subst hk0
      have htr : tr = default := Subsingleton.elim _ _
      subst htr
      exact hE stmtIn hstF
    · rw [ite_eq_right hn]
      exact Or.inl hstF

/-- An ordinary state function induces a knowledge state function by unbounded extraction.
The extractor is noncomputable because it chooses related input witnesses. -/
noncomputable def StateFunction.toKnowledgeStateFunctionOfRel [Nonempty WitIn]
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    (S : verifier.StateFunction init impl relIn.language relOut.language) :
    verifier.KnowledgeStateFunction init impl relIn relOut
      ((Extractor.RoundByRoundOneShot.ofRelation relIn).toRoundByRoundOfRel relIn) :=
  S.toKnowledgeStateFunctionOfOneShot init impl
    (Extractor.RoundByRoundOneShot.ofRelation relIn) (fun stmt h => by
      have hex := (Set.mem_language_iff relIn stmt).1 (S.toFun_empty stmt h)
      simpa [Extractor.RoundByRoundOneShot.ofRelation, hex] using hex.choose_spec)

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- Unbounded extraction can fail only outside the input language, at a bad state transition. -/
theorem StateFunction.toKnowledgeStateFunctionOfRel_failure [Nonempty WitIn]
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    (S : verifier.StateFunction init impl relIn.language relOut.language)
    (i : pSpec.ChallengeIdx) (stmt : StmtIn) (tr : Transcript i.1.castSucc pSpec)
    (challenge : pSpec.Challenge i)
    (h : rbrExtractionFailureEvent (oSpec := oSpec) (WitOut := WitOut)
      (S.toKnowledgeStateFunctionOfRel init impl).toFun
      ((Extractor.RoundByRoundOneShot.ofRelation relIn).toRoundByRoundOfRel relIn)
      i stmt tr challenge) :
    stmt ∉ relIn.language ∧ ¬ S.toFun i.1.castSucc stmt tr ∧
      S.toFun i.1.succ stmt (tr.concat challenge) := by
  classical
  obtain ⟨w, hprev, hnext⟩ := h
  simp only [toKnowledgeStateFunctionOfRel, toKnowledgeStateFunctionOfOneShot,
    Extractor.RoundByRoundOneShot.toRoundByRoundOfRel,
    ite_eq_right (Fin.succ_ne_zero _)] at hprev hnext
  have hnex : ¬ ∃ v, (stmt, v) ∈ relIn := by
    intro hex
    apply hprev
    split
    · simpa [hex] using hex.choose_spec
    · exact Or.inr hex
  have hlang : stmt ∉ relIn.language := fun h => hnex ((Set.mem_language_iff _ _).1 h)
  refine ⟨hlang, ?_, hnext.resolve_right hnex⟩
  intro hstate
  by_cases hz : i.1.castSucc = 0
  · have hzero : ∀ (k : Fin (n + 1)) (tr : Transcript k pSpec),
        k = 0 → S.toFun k stmt tr → stmt ∈ relIn.language := by
      intro k tr hk
      subst hk
      simpa [Subsingleton.elim tr default] using S.toFun_empty stmt
    exact hlang (hzero _ tr hz hstate)
  · exact hprev (by simpa [hz] using Or.inl hstate)

/-- A one-shot state function and extractor induce a knowledge state function with input
witnesses at every round. Intermediate extraction uses noncomputable choice. -/
noncomputable def KnowledgeStateFunctionOneShot.toKnowledgeStateFunction
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    (stF : KnowledgeStateFunctionOneShot init impl relIn.language relOut.language verifier)
    (oneShotE : Extractor.RoundByRoundOneShot oSpec StmtIn WitIn pSpec) :
    verifier.KnowledgeStateFunction init impl relIn relOut
      (oneShotE.toRoundByRoundOfRel (WitOut := WitOut) relIn) :=
  StateFunction.toKnowledgeStateFunctionOfOneShot init impl
    { toFun := stF.toFun
      toFun_empty := fun stmt h => (stF.toFun_empty stmt h).elim
      toFun_next := fun m hdir stmt tr h msg => stF.toFun_next m hdir stmt tr msg h
      toFun_full := stF.toFun_full }
    oneShotE (fun stmt h => (stF.toFun_empty stmt h).elim)

/-- Coercion to the underlying function of a state function -/
instance {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} :
    CoeFun (verifier.StateFunction init impl langIn langOut)
    (fun _ => (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop) := ⟨fun f => f.toFun⟩

instance {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} :
    CoeFun (KnowledgeStateFunctionOneShot init impl langIn langOut verifier)
    (fun _ => (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → Prop) := ⟨fun f => f.toFun⟩

instance {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} {WitMid : Fin (n + 1) → Type}
    {extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid} :
    CoeFun (verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (fun _ => (m : Fin (n + 1)) → StmtIn → Transcript m pSpec → WitMid m → Prop) :=
      ⟨fun f => f.toFun⟩

/-- An ordinary state function, read as a knowledge state function with `Unit` witnesses. -/
def StateFunction.toKnowledgeStateFunction
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    (S : verifier.StateFunction init impl langIn langOut) :
    verifier.KnowledgeStateFunction init impl (langIn ×ˢ (Set.univ : Set Unit))
      (langOut ×ˢ (Set.univ : Set Unit)) Extractor.RoundByRound.unit where
  toFun := fun m x tr _ => S m x tr
  toFun_empty := fun x _ h => ⟨S.toFun_empty x h, Set.mem_univ _⟩
  toFun_next := fun m hdir x tr msg _ h => by
    by_contra hprev
    exact S.toFun_next m hdir x tr hprev msg h
  toFun_full := fun x tr _ h => by
    by_contra hfalse
    have hzero := S.toFun_full x tr hfalse
    simp only [Set.mem_prod, Set.mem_univ, and_true] at h
    exact (ne_of_gt h) hzero

omit [∀ i, SampleableType (pSpec.Challenge i)] in
@[simp]
theorem StateFunction.toKnowledgeStateFunction_apply
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    (S : verifier.StateFunction init impl langIn langOut)
    (m : Fin (n + 1)) (x : StmtIn) (tr : Transcript m pSpec) :
    S.toKnowledgeStateFunction init impl m x tr () ↔ S m x tr := Iff.rfl

omit [∀ i, SampleableType (pSpec.Challenge i)] in
@[simp]
theorem StateFunction.toKnowledgeStateFunction_toStateFunction_apply
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    (S : verifier.StateFunction init impl langIn langOut)
    (m : Fin (n + 1)) (x : StmtIn) (tr : Transcript m pSpec) :
    (S.toKnowledgeStateFunction init impl).toStateFunction init impl m x tr ↔ S m x tr := by
  change (∃ _ : Unit, S m x tr) ↔ S m x tr
  simp

/-- A protocol with `verifier` satisfies round-by-round soundness with respect to input language
  `langIn`, output language `langOut`, and error `rbrSoundnessError` if:

  - there exists a state function `stateFunction` for the verifier and the input/output languages,
    such that
  - for all initial statement `stmtIn` not in `langIn`,
  - for all initial witness `witIn`,
  - for all provers `prover`,
  - for all `i : Fin n` that is a round corresponding to a challenge,

  the probability that:
  - the state function is false for the partial transcript output by the prover
  - the state function is true for the partial transcript appended by next challenge (chosen
    randomly)

  is at most `rbrSoundnessError i`.
-/
def rbrSoundness (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∃ stateFunction : verifier.StateFunction init impl langIn langOut,
  ∀ stmtIn ∉ langIn,
  ∀ WitIn WitOut : Type,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
  ∀ i : pSpec.ChallengeIdx,
    Pr{let ⟨transcript, challenge⟩ ← do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨transcript, _⟩ ← prover.runToRound i.1.castSucc stmtIn witIn
          let challenge ← liftComp (pSpec.getChallenge i) _
          return (transcript, challenge))).run' (← init)}[
      ¬ stateFunction i.1.castSucc stmtIn transcript ∧
        stateFunction i.1.succ stmtIn (transcript.concat challenge)] ≤
      rbrSoundnessError i

/-- Type class for round-by-round soundness for a verifier

Note that we put the error as a field in the type class to make it easier for synthesization
(often the rbr error will need additional simplification / proof) -/
class IsRBRSound (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) where
  rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0
  is_rbr_sound : rbrSoundness init impl langIn langOut verifier rbrSoundnessError

/-- A protocol with `verifier` satisfies round-by-round knowledge soundness with respect to input
  relation `relIn`, output relation `relOut`, and error `rbrKnowledgeError` if:

  - there exists a state function `stateFunction` for the verifier and the languages of the
    input/output relations, such that
  - for all initial statement `stmtIn` not in the language of `relIn`,
  - for all initial witness `witIn`,
  - for all provers `prover`,
  - for all `i : Fin n` that is a round corresponding to a challenge,

  the probability that:
  - the state function is false for the partial transcript output by the prover
  - the state function is true for the partial transcript appended by next challenge (chosen
    randomly)

  is at most `rbrKnowledgeError i`.
-/
def rbrKnowledgeSoundnessOneShot (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∃ stateFunction : verifier.KnowledgeStateFunctionOneShot init impl relIn.language relOut.language,
  ∃ extractor : Extractor.RoundByRoundOneShot oSpec StmtIn WitIn pSpec,
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
  ∀ i : pSpec.ChallengeIdx,
    Pr{let ⟨transcript, challenge, proveQueryLog⟩ ← do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨⟨transcript, _⟩, proveQueryLog⟩ ← prover.runWithLogToRound i.1.castSucc stmtIn witIn
          let challenge ← liftComp (pSpec.getChallenge i) _
          return (transcript, challenge, proveQueryLog))).run' (← init)}[
      letI extractedWitIn := extractor i.1.castSucc stmtIn transcript proveQueryLog.fst
      (stmtIn, extractedWitIn) ∉ relIn ∧
        ¬ stateFunction i.1.castSucc stmtIn transcript ∧
          stateFunction i.1.succ stmtIn (transcript.concat challenge)] ≤
      rbrKnowledgeError i

-- New definition of rbr knowledge soundness, using the knowledge state function
def rbrKnowledgeSoundness (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∃ WitMid : Fin (n + 1) → Type,
  ∃ extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid,
  ∃ kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor,
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
  ∀ i : pSpec.ChallengeIdx,
    Pr{let ⟨transcript, challenge, _proveQueryLog⟩ ← do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨⟨transcript, _⟩, proveQueryLog⟩ ← prover.runWithLogToRound i.1.castSucc stmtIn witIn
          let challenge ← liftComp (pSpec.getChallenge i) _
          return (transcript, challenge, proveQueryLog))).run' (← init)}[
      ∃ witMid,
        ¬ kSF i.1.castSucc stmtIn transcript
          (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
          kSF i.1.succ stmtIn (transcript.concat challenge) witMid] ≤
      rbrKnowledgeError i

/-- Round-by-round knowledge soundness for one exact intermediate-witness
family, extractor, and knowledge-state function.  Unlike
`rbrKnowledgeSoundness`, these proof objects remain visible in the proposition
type and can therefore be inspected by downstream clients. -/
def rbrKnowledgeSoundnessWith
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (WitMid : Fin (n + 1) → Type)
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∀ stmtIn : StmtIn,
  ∀ witIn : WitIn,
  ∀ prover : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec,
  ∀ i : pSpec.ChallengeIdx,
    Pr{let ⟨transcript, challenge, _proveQueryLog⟩ ← do
      (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
        (do
          let ⟨⟨transcript, _⟩, proveQueryLog⟩ ←
            prover.runWithLogToRound i.1.castSucc stmtIn witIn
          let challenge ← liftComp (pSpec.getChallenge i) _
          return (transcript, challenge, proveQueryLog))).run' (← init)}[
      ∃ witMid,
        ¬ kSF i.1.castSucc stmtIn transcript
          (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
          kSF i.1.succ stmtIn (transcript.concat challenge) witMid] ≤
      rbrKnowledgeError i

/-- The existential RBR contract is exactly existence of the corresponding
extractor-specific contract. -/
theorem rbrKnowledgeSoundness_iff_exists_with
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) :
    rbrKnowledgeSoundness init impl relIn relOut verifier rbrKnowledgeError ↔
      ∃ WitMid : Fin (n + 1) → Type,
      ∃ extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid,
      ∃ kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor,
        rbrKnowledgeSoundnessWith init impl relIn relOut verifier
          WitMid extractor kSF rbrKnowledgeError := by
  rfl

/-- Type class for round-by-round knowledge soundness for a verifier

Note that we put the error as a field in the type class to make it easier for synthesization
(often the rbr error will need additional simplification / proof)
-/
class IsRBRKnowledgeSound (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) where
  rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0
  is_rbr_knowledge_sound : rbrKnowledgeSoundness init impl relIn relOut verifier rbrKnowledgeError

/-! ### Worst-case-per-prefix variants

The standard literature definition of round-by-round (knowledge) soundness bounds the bad
transition probability for **every fixed transcript prefix**, quantified *before* the
challenge draw. ArkLib's `rbrSoundness` / `rbrKnowledgeSoundness` above instead sample the
prefix inside the game (via the prover run under the simulated oracles) and bound the
resulting **mixture** over prefixes — a formally weaker property with the same error
constants (safe direction: averaged ≤ worst-case). The definitions below are the faithful
worst-case forms, and the two implication theorems discharge the averaged forms from them
via the master mixture bound
`ProtocolSpec.prEvent_simulateQ_addLift_getChallenge_bind_le`
(`ArkLib/OracleReduction/Security/RbrGame.lean`).

Practical consequence: a protocol proven in the worst-case form gets the averaged form for
free, so prefer proving the worst-case variant. It is also the easier obligation to discharge
— it carries no prover quantifier at all, so one reasons about a fixed prefix and the fresh
challenge only. Conversely, a result established solely in the averaged form does **not**
yield the worst-case one; the implication runs in one direction. -/

/-- **Worst-case-per-prefix round-by-round soundness**, the standard literature shape: for
*every fixed* transcript prefix — not a prover-sampled one — the probability over only the
fresh challenge of a bad transition (state function false at the prefix, true after appending
the challenge) is at most the round error.
Implies `rbrSoundness` with the same error
(`rbrSoundnessWorstCase_implies_rbrSoundness`). -/
def rbrSoundnessWorstCase (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∃ stateFunction : verifier.StateFunction init impl langIn langOut,
  ∀ stmtIn ∉ langIn,
  ∀ i : pSpec.ChallengeIdx,
  ∀ transcript : Transcript i.1.castSucc pSpec,
    Pr{let challenge ← $ᵗ (pSpec.Challenge i)}[
      ¬ stateFunction i.1.castSucc stmtIn transcript ∧
        stateFunction i.1.succ stmtIn (transcript.concat challenge)] ≤ rbrSoundnessError i

/-- **Worst-case-per-prefix round-by-round knowledge soundness**, the standard literature shape:
the knowledge analogue of `rbrSoundnessWorstCase`, with the bad-transition event of
`rbrKnowledgeSoundness` evaluated at every fixed transcript prefix over only the fresh
challenge. Implies `rbrKnowledgeSoundness` with the same error
(`rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness`). -/
def rbrKnowledgeSoundnessWorstCase (relIn : Set (StmtIn × WitIn))
    (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∃ WitMid : Fin (n + 1) → Type,
  ∃ extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid,
  ∃ kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor,
  ∀ stmtIn : StmtIn,
  ∀ i : pSpec.ChallengeIdx,
  ∀ transcript : Transcript i.1.castSucc pSpec,
    Pr{let challenge ← $ᵗ (pSpec.Challenge i)}[
      ∃ witMid,
        ¬ kSF i.1.castSucc stmtIn transcript
          (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
          kSF i.1.succ stmtIn (transcript.concat challenge) witMid] ≤ rbrKnowledgeError i

/-- Worst-case-per-prefix RBR knowledge soundness for one exact
intermediate-witness family, extractor, and knowledge-state function. -/
def rbrKnowledgeSoundnessWorstCaseWith
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (WitMid : Fin (n + 1) → Type)
    (extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∀ stmtIn : StmtIn,
  ∀ i : pSpec.ChallengeIdx,
  ∀ transcript : Transcript i.1.castSucc pSpec,
    Pr{let challenge ← $ᵗ (pSpec.Challenge i)}[
      ∃ witMid,
        ¬ kSF i.1.castSucc stmtIn transcript
          (extractor.extractMid i.1 stmtIn (transcript.concat challenge) witMid) ∧
          kSF i.1.succ stmtIn (transcript.concat challenge) witMid] ≤ rbrKnowledgeError i

/-- The existential worst-case RBR contract is exactly existence of the
corresponding extractor-specific contract. -/
theorem rbrKnowledgeSoundnessWorstCase_iff_exists_with
    (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) :
    rbrKnowledgeSoundnessWorstCase init impl relIn relOut verifier rbrKnowledgeError ↔
      ∃ WitMid : Fin (n + 1) → Type,
      ∃ extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid,
      ∃ kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor,
        rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut verifier
          WitMid extractor kSF rbrKnowledgeError := by
  rfl

/-- Worst-case-per-prefix rbr soundness implies the (averaged) `rbrSoundness`, with the
same error: the averaged game's prefix distribution is a mixture, and the challenge is
drawn independently of the prefix, so the mixture probability is dominated by the
per-prefix supremum (master bound
`ProtocolSpec.prEvent_simulateQ_addLift_getChallenge_bind_le`). -/
theorem rbrSoundnessWorstCase_implies_rbrSoundness
    {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0}
    (h : rbrSoundnessWorstCase init impl langIn langOut verifier rbrSoundnessError) :
    rbrSoundness init impl langIn langOut verifier rbrSoundnessError := by
  obtain ⟨sF, hsF⟩ := h
  refine ⟨sF, fun stmtIn hstmt WitIn WitOut witIn prover i => ?_⟩
  exact ProtocolSpec.prEvent_simulateQ_addLift_getChallenge_bind_le
    init impl (prover.runToRound i.1.castSucc stmtIn witIn) i
    (fun tr c => (tr.1, c))
    (fun x => ¬ sF i.1.castSucc stmtIn x.1 ∧ sF i.1.succ stmtIn (x.1.concat x.2))
    (fun tr => hsF stmtIn hstmt i tr.1)

/-- Worst-case-per-prefix rbr knowledge soundness implies the (averaged)
`rbrKnowledgeSoundness`, with the same error (same mixture argument as
`rbrSoundnessWorstCase_implies_rbrSoundness`). -/
theorem rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    (h : rbrKnowledgeSoundnessWorstCase init impl relIn relOut verifier rbrKnowledgeError) :
    rbrKnowledgeSoundness init impl relIn relOut verifier rbrKnowledgeError := by
  obtain ⟨WitMid, extractor, kSF, hkSF⟩ := h
  refine ⟨WitMid, extractor, kSF, fun stmtIn witIn prover i => ?_⟩
  exact ProtocolSpec.prEvent_simulateQ_addLift_getChallenge_bind_le
    init impl (prover.runWithLogToRound i.1.castSucc stmtIn witIn) i
    (fun tr c => (tr.1.1, c, tr.2))
    (fun x => ∃ witMid,
      ¬ kSF i.1.castSucc stmtIn x.1
        (extractor.extractMid i.1 stmtIn (x.1.concat x.2.1) witMid) ∧
        kSF i.1.succ stmtIn (x.1.concat x.2.1) witMid)
    (fun tr => hkSF stmtIn i tr.1.1)

/-- The exact-object worst-case RBR contract implies the exact-object averaged
contract without hiding the extractor or knowledge-state function. -/
theorem rbrKnowledgeSoundnessWorstCaseWith_implies_rbrKnowledgeSoundnessWith
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {WitMid : Fin (n + 1) → Type}
    {extractor : Extractor.RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid}
    {kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    (h : rbrKnowledgeSoundnessWorstCaseWith init impl relIn relOut verifier
      WitMid extractor kSF rbrKnowledgeError) :
    rbrKnowledgeSoundnessWith init impl relIn relOut verifier
      WitMid extractor kSF rbrKnowledgeError := by
  intro stmtIn witIn prover i
  exact ProtocolSpec.prEvent_simulateQ_addLift_getChallenge_bind_le
    init impl (prover.runWithLogToRound i.1.castSucc stmtIn witIn) i
    (fun tr c => (tr.1.1, c, tr.2))
    (fun x => ∃ witMid,
      ¬ kSF i.1.castSucc stmtIn x.1
        (extractor.extractMid i.1 stmtIn (x.1.concat x.2.1) witMid) ∧
        kSF i.1.succ stmtIn (x.1.concat x.2.1) witMid)
    (fun tr => h stmtIn i tr.1.1)

/-- Implication: one-shot rbr knowledge soundness implies general rbr knowledge soundness (with the
  same error).

  The two notions score the *same* game, so the proof is a pointwise comparison of their bad
  events. The one-shot event carries an extra conjunct — that the extractor *fails* on the prover's
  query log — which the general event cannot mention, because `Extractor.RoundByRound.extractMid`
  never sees a query log. The bridge is that the general event forces `relIn` to contain **no**
  witness at all for `stmtIn`: at round `0` because
  `Extractor.RoundByRoundOneShot.toRoundByRoundOfRel` would otherwise have selected a valid witness,
  and at later rounds because the induced state function carries `∃ v, (stmtIn, v) ∈ relIn` as a
  disjunct. With no witness in existence the extra conjunct holds for free, whatever the log. -/
theorem rbrKnowledgeSoundnessOneShot_implies_rbrKnowledgeSoundness
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    (h : verifier.rbrKnowledgeSoundnessOneShot init impl relIn relOut rbrKnowledgeError) :
    verifier.rbrKnowledgeSoundness init impl relIn relOut rbrKnowledgeError := by
  unfold rbrKnowledgeSoundness
  obtain ⟨stF, oneShotE, h⟩ := h
  refine ⟨_, oneShotE.toRoundByRoundOfRel relIn,
    stF.toKnowledgeStateFunction init impl oneShotE, ?_⟩
  -- Both notions score the *same* game, so it suffices to compare the two bad events pointwise.
  refine fun stmtIn witIn prover i ↦ le_trans ?_ (h stmtIn witIn prover i)
  refine prEvent_mono _ _ _ ?_
  rintro ⟨transcript, challenge, proveQueryLog⟩ ⟨witMid, hcast, hsucc⟩
  simp only [Extractor.RoundByRoundOneShot.toRoundByRoundOfRel, ite_eq_right (Fin.succ_ne_zero _),
    KnowledgeStateFunctionOneShot.toKnowledgeStateFunction,
    StateFunction.toKnowledgeStateFunctionOfOneShot] at hcast hsucc
  -- The crux: the general bad event forces `relIn` to have *no* witness for `stmtIn` at all.
  -- That is what bridges the gap to the one-shot event, whose extractor sees the prover's query
  -- log while `extractMid` cannot.
  have hnex : ¬ ∃ v, (stmtIn, v) ∈ relIn := by
    intro hex
    by_cases hz : i.1.castSucc = 0
    · -- Round-0 branch: `extractMid` would have selected a valid witness.
      rw [ite_eq_left hz] at hcast
      exact hcast (by simpa [hex] using hex.choose_spec)
    · rw [ite_eq_right hz] at hcast
      exact hcast (Or.inr hex)
  refine ⟨fun hmem => hnex ⟨_, hmem⟩, ?_, hsucc.resolve_right hnex⟩
  -- `¬ stF.toFun i.castSucc`: at a nonzero index it is the left half of `hcast`; at index `0`
  -- it is the one-shot state function's empty-transcript axiom, transported along `hz`.
  by_cases hz : i.1.castSucc = 0
  · exact stF.toFun_empty_of_eq_zero (stmtIn := stmtIn) (m := i.1.castSucc)
      (hm := hz) (tr := transcript)
  · rw [ite_eq_right hz] at hcast
    exact fun hstF => hcast (Or.inl hstF)

end RoundByRound

end Verifier

open Verifier

section OracleProtocol

variable
  {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
  {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}
  [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  [∀ i, OracleInterface (pSpec.Message i)]

namespace OracleVerifier

@[reducible, simp]
def StateFunction
    (langIn : Set (StmtIn × ∀ i, OStmtIn i))
    (langOut : Set (StmtOut × ∀ i, OStmtOut i))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) :=
  verifier.toVerifier.StateFunction init impl langIn langOut

@[reducible, simp]
def KnowledgeStateFunction
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    {WitMid : Fin (n + 1) → Type}
    (extractor : Extractor.RoundByRound oSpec
      (StmtIn × (∀ i, OStmtIn i)) WitIn WitOut pSpec WitMid) :=
  verifier.toVerifier.KnowledgeStateFunction init impl relIn relOut extractor

/-- Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions. -/
def rbrSoundness
    (langIn : Set (StmtIn × ∀ i, OStmtIn i))
    (langOut : Set (StmtOut × ∀ i, OStmtOut i))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.toVerifier.rbrSoundness init impl langIn langOut rbrSoundnessError

/-- Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle
reductions. -/
def rbrKnowledgeSoundness
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.toVerifier.rbrKnowledgeSoundness init impl relIn relOut rbrKnowledgeError

/-- Extractor-specific round-by-round knowledge soundness of an oracle
reduction, retaining the exact intermediate-witness family, extractor, and
knowledge-state function in the proposition type. -/
def rbrKnowledgeSoundnessWith
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (WitMid : Fin (n + 1) → Type)
    (extractor : Extractor.RoundByRound oSpec
      (StmtIn × (∀ i, OStmtIn i)) WitIn WitOut pSpec WitMid)
    (kSF : verifier.KnowledgeStateFunction init impl relIn relOut extractor)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.toVerifier.rbrKnowledgeSoundnessWith init impl relIn relOut
    WitMid extractor kSF rbrKnowledgeError

end OracleVerifier

end OracleProtocol

variable {Statement : Type} {ιₛ : Type} {OStatement : ιₛ → Type} {Witness : Type}
  [∀ i, OracleInterface (OStatement i)]
  [∀ i, OracleInterface (pSpec.Message i)]

namespace Proof

@[reducible, simp]
def rbrSoundness (langIn : Set Statement)
    (verifier : Verifier oSpec Statement Bool pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.rbrSoundness init impl langIn acceptRejectRel.language rbrSoundnessError

@[reducible, simp]
def rbrKnowledgeSoundness (relation : Set (Statement × Witness))
    (verifier : Verifier oSpec Statement Bool pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.rbrKnowledgeSoundness init impl relation acceptRejectRel rbrKnowledgeError

end Proof

namespace OracleProof

/-- A knowledge state function for an IOP verifier, with its empty output-oracle
family discharged explicitly. -/
@[reducible, simp]
def KnowledgeStateFunction
    (relIn : Set ((Statement × ∀ i, OStatement i) × Witness))
    (verifier : OracleProofVerifier oSpec Statement OStatement pSpec)
    {WitMid : Fin (n + 1) → Type}
    (extractor : Extractor.RoundByRound oSpec
      (Statement × (∀ i, OStatement i)) Witness Unit pSpec WitMid) :=
  OracleVerifier.KnowledgeStateFunction (Oₛₒ := fun i => nomatch i)
    init impl relIn acceptRejectOracleRel verifier extractor

/-- Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions. -/
@[reducible, simp]
def rbrSoundness
    (langIn : Set (Statement × ∀ i, OStatement i))
    (verifier : OracleProofVerifier oSpec Statement OStatement pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) : Prop := by
  exact OracleVerifier.rbrSoundness (Oₛₒ := fun i => nomatch i) init impl
    langIn acceptRejectOracleRel.language verifier rbrSoundnessError

/-- Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle
reductions. -/
def rbrKnowledgeSoundness
    (relIn : Set ((Statement × ∀ i, OStatement i) × Witness))
    (verifier : OracleProofVerifier oSpec Statement OStatement pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop := by
  exact OracleVerifier.rbrKnowledgeSoundness (Oₛₒ := fun i => nomatch i) init impl
    relIn acceptRejectOracleRel verifier rbrKnowledgeError

/-- Worst-case-per-prefix round-by-round knowledge soundness of an oracle proof: that of its
verifier (`Verifier.rbrKnowledgeSoundnessWorstCase`), with the empty output-oracle family
discharged explicitly. It implies `OracleProof.rbrKnowledgeSoundness` with the same error
(`OracleProof.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness`). The implication runs
in one direction only; see the note on the worst-case-per-prefix variants above. -/
def rbrKnowledgeSoundnessWorstCase
    (relIn : Set ((Statement × ∀ i, OStatement i) × Witness))
    (verifier : OracleProofVerifier oSpec Statement OStatement pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  (OracleVerifier.toVerifier (Oₛₒ := fun i => nomatch i) verifier).rbrKnowledgeSoundnessWorstCase
    init impl relIn acceptRejectOracleRel rbrKnowledgeError

variable {init impl} in
/-- Worst-case-per-prefix round-by-round knowledge soundness of an oracle proof implies the
prover-averaged `OracleProof.rbrKnowledgeSoundness`, with the same error. -/
theorem rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness
    {relIn : Set ((Statement × ∀ i, OStatement i) × Witness)}
    {verifier : OracleProofVerifier oSpec Statement OStatement pSpec}
    {rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0}
    (h : rbrKnowledgeSoundnessWorstCase init impl relIn verifier rbrKnowledgeError) :
    rbrKnowledgeSoundness init impl relIn verifier rbrKnowledgeError :=
  Verifier.rbrKnowledgeSoundnessWorstCase_implies_rbrKnowledgeSoundness init impl h

end OracleProof

section Trivial

/-- The state function for the identity / trivial verifier, which just returns whether the
  statement is in the language. -/
def Verifier.StateFunction.id {lang : Set Statement} :
    (Verifier.id : Verifier oSpec Statement _ _).StateFunction init impl lang lang where
  toFun | ⟨0, _⟩ => fun stmtIn _ => stmtIn ∈ lang
  toFun_empty := fun _ h => h
  toFun_next := fun i => Fin.elim0 i
  toFun_full := fun stmt tr h => by
    simp only [Verifier.id, Verifier.run]
    rw [OptionT.prEvent_mk_eq_zero_iff]
    intro x hx
    simp only [support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    have key : (simulateQ impl (pure stmt : OptionT (OracleComp oSpec) Statement)).run' s =
        pure (some stmt) := by
      change (simulateQ impl (pure (some stmt) : OracleComp oSpec (Option Statement))).run' s = _
      rw [simulateQ_pure]
      change Prod.fst <$> (pure (some stmt) : StateT σ ProbComp _).run s = _
      rw [StateT.run_pure]; simp [map_pure]
    rw [key] at hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    cases hx; exact h

/-- The identity / trivial verifier is perfectly round-by-round sound. -/
@[simp]
lemma Verifier.id_rbrSoundness {lang : Set Statement} :
    (Verifier.id : Verifier oSpec Statement _ _).rbrSoundness init impl lang lang 0 := by
  refine ⟨Verifier.StateFunction.id init impl, ?_⟩
  intro _ _ _ _ _ _ i
  exact Fin.elim0 i.1

/-- The round-by-round extractor for the identity / trivial verifier, which just returns the
  input witness. -/
def Extractor.RoundByRound.id :
    Extractor.RoundByRound oSpec Statement Witness Witness !p[] (fun _ => Witness) where
  extractIn := fun _ => _root_.id
  extractMid := fun i => Fin.elim0 i
  extractOut := fun _ _ => _root_.id

/-- The knowledge state function for the identity / trivial verifier, which just returns whether
  the statement is in the relation. -/
def Verifier.KnowledgeStateFunction.id {rel : Set (Statement × Witness)} :
    (Verifier.id : Verifier oSpec Statement _ _).KnowledgeStateFunction init impl rel rel
      (Extractor.RoundByRound.id) where
  toFun | ⟨0, _⟩ => fun stmtIn _ witIn => (stmtIn, witIn) ∈ rel
  toFun_empty := fun _ _ h => h
  toFun_next := fun i => Fin.elim0 i
  toFun_full := fun stmtIn tr witOut h => by
    simp only [Verifier.id, Verifier.run] at h
    rw [gt_iff_lt, OptionT.prEvent_mk_pos_iff] at h
    obtain ⟨x, hx, hrel⟩ := h
    simp only [support_bind, Set.mem_iUnion] at hx
    obtain ⟨s, _, hx⟩ := hx
    have key : (simulateQ impl (pure stmtIn : OptionT (OracleComp oSpec) Statement)).run' s =
        pure (some stmtIn) := by
      change (simulateQ impl (pure (some stmtIn) : OracleComp oSpec (Option Statement))).run' s = _
      rw [simulateQ_pure]
      change Prod.fst <$> (pure (some stmtIn) : StateT σ ProbComp _).run s = _
      rw [StateT.run_pure]; simp [map_pure]
    rw [key] at hx
    simp only [support_pure, Set.mem_singleton_iff] at hx
    cases (Option.some.inj hx)
    exact hrel

/-- The identity / trivial verifier is perfectly round-by-round knowledge sound. -/
@[simp]
lemma Verifier.id_rbrKnowledgeSoundness {rel : Set (Statement × Witness)} :
    (Verifier.id : Verifier oSpec Statement _ _).rbrKnowledgeSoundness
      init impl rel rel 0 := by
  refine ⟨_, _, Verifier.KnowledgeStateFunction.id init impl, ?_⟩
  intro stmtIn witIn prover i
  exact Fin.elim0 i.1

/-- The identity / trivial oracle verifier is perfectly round-by-round knowledge sound. -/
@[simp]
lemma OracleVerifier.id_rbrKnowledgeSoundness
    {rel : Set ((Statement × ∀ i, OStatement i) × Witness)} :
    (OracleVerifier.id : OracleVerifier oSpec Statement OStatement _ _ _).rbrKnowledgeSoundness
      init impl rel rel 0 := by
  exact Verifier.id_rbrKnowledgeSoundness init impl (rel := rel)

end Trivial
