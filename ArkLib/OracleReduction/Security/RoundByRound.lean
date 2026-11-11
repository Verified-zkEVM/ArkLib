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

  This file defines round-by-round soundness and knowledge soundness for (oracle) reductions,
  following [CCHLRRW19] and [ABF26]. The notions bound bad transitions at every transcript prefix;
  the section below explains their quantifier structure.

  Bounds averaged over prefixes reached with honestly sampled earlier challenges follow from
  these bounds with the same error. They gain only when bad prefixes require unlikely earlier
  challenges; that gain does not survive Fiat-Shamir or state restoration, where the adversary
  chooses the prefix to extend. Averaging changes how prefixes are sampled; it does not give the
  round-by-round extractor access to the prover's query log.

  ## Extraction cost

  A round-by-round extractor is a family of Lean functions, and nothing here bounds their cost or
  requires them to be computable. The existential knowledge notion therefore carries no efficiency
  content. Round-by-round knowledge soundness in the cryptographic sense needs, in addition, a cost
  bound for each stage of a named extractor, such as the one named in
  `Verifier.rbrKnowledgeSoundnessWith`. No predicate here states such a bound.

  For inhabited input-witness types, `Security.Implications` identifies the existential knowledge
  form with round-by-round soundness of the induced languages. This language-soundness equivalence
  is distinct from the terminal relation-soundness equivalence and does not characterize native
  certificates.

  ## References

  * [Canetti, R., Chen, Y., Holmgren, J., Lombardi, A., Rothblum, G. N., Rothblum, R. D., and
      Wichs, D., *Fiat-Shamir: from practice to theory*][CCHLRRW19]
  * [Arnon, G., Boneh, D., and Fenzi, G., *Open Problems in List Decoding and Correlated
      Agreement*][ABF26]
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

  The maps are Lean functions with no cost bound, and need not be computable.
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

namespace RoundByRound

variable {WitMid : Fin (n + 1) → Type}

/-- Fold intermediate extraction backward along a transcript prefix. -/
def foldPrefix (E : RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (stmt : StmtIn) : (m : Fin (n + 1)) → pSpec.Transcript m → WitMid m → WitIn :=
  Fin.induction (fun _ w ↦ E.extractIn stmt w)
    (fun j ih tr w ↦ ih (Fin.init tr) (E.extractMid j stmt tr w))

omit [∀ i, SampleableType (pSpec.Challenge i)] in
@[simp]
theorem foldPrefix_zero (E : RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (stmt : StmtIn) (tr : pSpec.Transcript 0) (w : WitMid 0) :
    E.foldPrefix stmt 0 tr w = E.extractIn stmt w := rfl

omit [∀ i, SampleableType (pSpec.Challenge i)] in
@[simp]
theorem foldPrefix_succ (E : RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)
    (stmt : StmtIn) (j : Fin n) (tr : pSpec.Transcript j.succ) (w : WitMid j.succ) :
    E.foldPrefix stmt j.succ tr w =
      E.foldPrefix stmt j.castSucc (Fin.init tr) (E.extractMid j stmt tr w) := by
  simp [foldPrefix, Fin.induction_succ]

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- With no input witnesses, a round-by-round extractor exists only if no input statement, full
transcript and output witness exist together: folding extraction from them would produce an
input witness. Extraction is total, so this holds whatever the relations, including for
transcripts the verifier rejects. -/
theorem isEmpty_of_isEmpty_witIn [IsEmpty WitIn] (stmtIn : StmtIn) (tr : FullTranscript pSpec)
    (witOut : WitOut) : IsEmpty (RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid) :=
  ⟨fun E => isEmptyElim (E.foldPrefix stmtIn (.last n) tr (E.extractOut stmtIn tr witOut))⟩

/-- The extractor with empty intermediate witnesses, available when no input statement, full
transcript and output witness exist together. -/
def ofIsEmpty [IsEmpty (StmtIn × FullTranscript pSpec × WitOut)] :
    RoundByRound oSpec StmtIn WitIn WitOut pSpec (fun _ => Empty) where
  extractIn := fun _ w => w.elim
  extractMid := fun _ _ _ w => w
  extractOut := fun stmtIn tr witOut => isEmptyElim (stmtIn, tr, witOut)

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- A round-by-round extractor exists for some intermediate witness types exactly when input
witnesses exist, or no input statement, full transcript and output witness exist together. -/
theorem exists_nonempty_iff :
    (∃ WitMid : Fin (n + 1) → Type,
        Nonempty (RoundByRound oSpec StmtIn WitIn WitOut pSpec WitMid)) ↔
      Nonempty WitIn ∨ IsEmpty (StmtIn × FullTranscript pSpec × WitOut) := by
  refine ⟨fun ⟨_, ⟨E⟩⟩ => ?_, ?_⟩
  · by_contra h
    rw [not_or, not_nonempty_iff, not_isEmpty_iff] at h
    obtain ⟨_, ⟨stmtIn, tr, witOut⟩⟩ := h
    exact (isEmpty_of_isEmpty_witIn stmtIn tr witOut).false E
  · rintro (h | h)
    · exact ⟨fun _ => WitIn,
        ⟨⟨fun _ w => w, fun _ _ _ w => w, fun _ _ _ => Classical.choice h⟩⟩⟩
    · exact ⟨_, ⟨ofIsEmpty⟩⟩

end RoundByRound

open Classical in
/-- An unbounded round-by-round extractor that selects a related input witness whenever one
exists. It is noncomputable because the input relation is arbitrary. -/
noncomputable def RoundByRound.ofRelation [Nonempty WitIn] (relIn : Set (StmtIn × WitIn)) :
    RoundByRound oSpec StmtIn WitIn WitOut pSpec (fun _ => WitIn) where
  extractIn := fun _ => _root_.id
  extractMid := fun _ stmtIn _ witIn => if h : ∃ v, (stmtIn, v) ∈ relIn then h.choose else witIn
  extractOut := fun stmtIn _ _ =>
    if h : ∃ v, (stmtIn, v) ∈ relIn then h.choose else Classical.ofNonempty

end Extractor

omit [∀ i, SampleableType (pSpec.Challenge i)] in
/-- The round-by-round extraction-failure event at challenge `i`: some intermediate witness
satisfies the knowledge state after the challenge, while its extraction fails it before. This is
the event `Verifier.rbrKnowledgeSoundness` bounds, named so that per-protocol bounds can
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

/-- The everywhere false knowledge state function of `Extractor.RoundByRound.ofIsEmpty`. Its
terminal law is vacuous because no input statement, full transcript and output witness exist
together. -/
def KnowledgeStateFunction.ofIsEmpty [IsEmpty (StmtIn × FullTranscript pSpec × WitOut)]
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} :
    verifier.KnowledgeStateFunction init impl relIn relOut
      (Extractor.RoundByRound.ofIsEmpty (oSpec := oSpec)) where
  toFun := fun _ _ _ _ => False
  toFun_empty := fun _ _ h => h.elim
  toFun_next := fun _ _ _ _ _ _ h => h
  toFun_full := fun stmtIn tr witOut _ =>
    isEmptyElim (α := StmtIn × FullTranscript pSpec × WitOut) (stmtIn, tr, witOut)

/-- An ordinary state function induces a knowledge state function by unbounded extraction.
The extractor is noncomputable because it chooses related input witnesses. -/
noncomputable def StateFunction.toKnowledgeStateFunctionOfRel [Nonempty WitIn]
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec}
    (stF : StateFunction init impl relIn.language relOut.language verifier) :
    verifier.KnowledgeStateFunction init impl relIn relOut
      (Extractor.RoundByRound.ofRelation relIn) where
  toFun := fun m stmtIn tr witIn => if m = 0 then (stmtIn, witIn) ∈ relIn else
    stF.toFun m stmtIn tr ∨ ∃ v, (stmtIn, v) ∈ relIn
  toFun_empty := fun stmtIn witIn h => by
    simpa [Extractor.RoundByRound.ofRelation] using h
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
      simpa [Extractor.RoundByRound.ofRelation, hex] using hex.choose_spec
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
      simp only [Extractor.RoundByRound.ofRelation]
      clear h hLang
      generalize hk : (Fin.last n : Fin (n + 1)) = k at tr hstF ⊢
      have hk0 : k = 0 := hk.symm.trans hn
      subst hk0
      have htr : tr = default := Subsingleton.elim _ _
      subst htr
      have hex := (Set.mem_language_iff relIn stmtIn).1 (stF.toFun_empty stmtIn hstF)
      simpa [Extractor.RoundByRound.ofRelation, hex] using hex.choose_spec
    · rw [ite_eq_right hn]
      exact Or.inl hstF

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
      (Extractor.RoundByRound.ofRelation relIn)
      i stmt tr challenge) :
    stmt ∉ relIn.language ∧ ¬ S.toFun i.1.castSucc stmt tr ∧
      S.toFun i.1.succ stmt (tr.concat challenge) := by
  classical
  obtain ⟨w, hprev, hnext⟩ := h
  simp only [toKnowledgeStateFunctionOfRel,
    Extractor.RoundByRound.ofRelation,
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

/-- Coercion to the underlying function of a state function -/
instance {langIn : Set StmtIn} {langOut : Set StmtOut}
    {verifier : Verifier oSpec StmtIn StmtOut pSpec} :
    CoeFun (verifier.StateFunction init impl langIn langOut)
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

/-! ### Round-by-round soundness

Round-by-round (knowledge) soundness bounds, for every challenge round, the probability that the
fresh challenge moves a state function from "doomed" to "not doomed". The notions quantify the
transcript prefix **before** the challenge is drawn: for every fixed prefix, the probability over
the fresh challenge alone is bounded. A protocol proof therefore reasons about one prefix and one
fresh challenge, without a prover quantifier. -/

/-- **Round-by-round soundness** with respect to input language `langIn`, output language
`langOut`, and error `rbrSoundnessError`: there is a state function for the verifier and the two
languages such that, for every statement `stmtIn ∉ langIn`, every challenge round `i`, and every
fixed transcript prefix up to that round, the probability over the fresh challenge alone that the
state function is false at the prefix and true after appending the challenge is at most
`rbrSoundnessError i`. -/
def rbrSoundness (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  ∃ stateFunction : verifier.StateFunction init impl langIn langOut,
  ∀ stmtIn ∉ langIn,
  ∀ i : pSpec.ChallengeIdx,
  ∀ transcript : Transcript i.1.castSucc pSpec,
    Pr{let challenge ← $ᵗ (pSpec.Challenge i)}[
      ¬ stateFunction i.1.castSucc stmtIn transcript ∧
        stateFunction i.1.succ stmtIn (transcript.concat challenge)] ≤ rbrSoundnessError i

/-- **Round-by-round knowledge soundness** with respect to input relation `relIn`, output relation
`relOut`, and error `rbrKnowledgeError`: there are an intermediate-witness family, a round-by-round
extractor, and a knowledge state function such that, for every statement, every challenge round
`i`, and every fixed transcript prefix up to that round, the probability over the fresh challenge
alone of a bad transition (some intermediate witness makes the knowledge state function true
after the challenge, while the witness extracted back from it makes it false at the prefix) is at
most `rbrKnowledgeError i`.

The extractor is unconstrained, so this contract carries no efficiency content; see the module
documentation. For inhabited input-witness types, `Security.Implications` identifies it with
round-by-round soundness of the induced languages. This is distinct from the terminal equivalence
with `Verifier.relationSoundness`; native notions are not characterized here. -/
def rbrKnowledgeSoundness (relIn : Set (StmtIn × WitIn))
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

/-- `rbrKnowledgeSoundness` for one exact intermediate-witness family, extractor, and
knowledge state function. Unlike `rbrKnowledgeSoundness`, these objects remain visible in the
proposition type and can therefore be inspected by downstream clients.

The predicate bounds only the error. Round-by-round knowledge soundness in the cryptographic sense
also needs a cost bound for each stage of this extractor, which is not part of this predicate. -/
def rbrKnowledgeSoundnessWith
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

/-- The existential round-by-round knowledge contract is exactly existence of the corresponding
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

/-- Type class for round-by-round soundness (`rbrSoundness`) of a verifier.

Note that we put the error as a field in the type class to make it easier for synthesization
(often the rbr error will need additional simplification / proof) -/
class IsRBRSound (langIn : Set StmtIn) (langOut : Set StmtOut)
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) where
  rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0
  is_rbr_sound : rbrSoundness init impl langIn langOut verifier rbrSoundnessError

/-- Type class for round-by-round knowledge soundness (`rbrKnowledgeSoundness`) of a verifier.

Note that we put the error as a field in the type class to make it easier for synthesization
(often the rbr error will need additional simplification / proof)

Like `rbrKnowledgeSoundness`, the instance carries no efficiency content.
-/
class IsRBRKnowledgeSound (relIn : Set (StmtIn × WitIn)) (relOut : Set (StmtOut × WitOut))
    (verifier : Verifier oSpec StmtIn StmtOut pSpec) where
  rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0
  is_rbr_knowledge_sound : rbrKnowledgeSoundness init impl relIn relOut verifier rbrKnowledgeError

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

/-- Round-by-round soundness (`Verifier.rbrSoundness`) of an oracle verifier: that of the
verifier it induces. -/
def rbrSoundness
    (langIn : Set (StmtIn × ∀ i, OStmtIn i))
    (langOut : Set (StmtOut × ∀ i, OStmtOut i))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.toVerifier.rbrSoundness init impl langIn langOut rbrSoundnessError

/-- Round-by-round knowledge soundness (`Verifier.rbrKnowledgeSoundness`) of an oracle verifier:
that of the verifier it induces. -/
def rbrKnowledgeSoundness
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (verifier : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.toVerifier.rbrKnowledgeSoundness init impl relIn relOut rbrKnowledgeError

/-- Extractor-specific round-by-round knowledge soundness (`Verifier.rbrKnowledgeSoundnessWith`)
of an oracle verifier, retaining the exact intermediate-witness family, extractor, and knowledge
state function in the proposition type. -/
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

/-- Round-by-round soundness (`Verifier.rbrSoundness`) of a proof: the output language is the
accepting verdict. -/
@[reducible, simp]
def rbrSoundness (langIn : Set Statement)
    (verifier : Verifier oSpec Statement Bool pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  verifier.rbrSoundness init impl langIn acceptRejectRel.language rbrSoundnessError

/-- Round-by-round knowledge soundness (`Verifier.rbrKnowledgeSoundness`) of a proof: the output
relation is the accepting verdict. Like `Verifier.rbrKnowledgeSoundness`, it carries no efficiency
content. -/
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

/-- Round-by-round soundness (`Verifier.rbrSoundness`) of an oracle proof, with the empty
output-oracle family discharged explicitly. -/
@[reducible, simp]
def rbrSoundness
    (langIn : Set (Statement × ∀ i, OStatement i))
    (verifier : OracleProofVerifier oSpec Statement OStatement pSpec)
    (rbrSoundnessError : pSpec.ChallengeIdx → ℝ≥0) : Prop := by
  exact OracleVerifier.rbrSoundness (Oₛₒ := fun i => nomatch i) init impl
    langIn acceptRejectOracleRel.language verifier rbrSoundnessError

/-- Round-by-round knowledge soundness (`Verifier.rbrKnowledgeSoundness`) of an oracle proof:
that of its verifier, with the empty output-oracle family discharged explicitly. -/
def rbrKnowledgeSoundness
    (relIn : Set ((Statement × ∀ i, OStatement i) × Witness))
    (verifier : OracleProofVerifier oSpec Statement OStatement pSpec)
    (rbrKnowledgeError : pSpec.ChallengeIdx → ℝ≥0) : Prop :=
  (OracleVerifier.toVerifier (Oₛₒ := fun i => nomatch i) verifier).rbrKnowledgeSoundness
    init impl relIn acceptRejectOracleRel rbrKnowledgeError

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
  intro _ _ i
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
  intro stmtIn i
  exact Fin.elim0 i.1

/-- The identity / trivial oracle verifier is perfectly round-by-round knowledge sound. -/
@[simp]
lemma OracleVerifier.id_rbrKnowledgeSoundness
    {rel : Set ((Statement × ∀ i, OStatement i) × Witness)} :
    (OracleVerifier.id :
      OracleVerifier oSpec Statement OStatement _ _ _).rbrKnowledgeSoundness
        init impl rel rel 0 := by
  exact Verifier.id_rbrKnowledgeSoundness init impl (rel := rel)

end Trivial
