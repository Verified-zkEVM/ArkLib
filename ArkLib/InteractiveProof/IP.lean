/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuxi Zheng, Chung Thai Nguyen, Michele Orrù
-/
module

public import ArkLib.InteractiveProof.StateRestorationSoundness

/-!
# Public-coin interactive-proof security

The verifier has no ambient oracle and decides from the statement and transcript. These
state-restoration games specialize the legacy protocol representation to Boolean acceptance;
provers and extractors retain private randomness. The named extractor receives the statement,
salt, transcript, and move-response trace, with no prover handle.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec
open scoped NNReal ProbabilityTheory

namespace IP

/-- An ordinary public-coin verifier's statement and full transcript determine its final
decision. Both `none` and `some false` mean rejection. -/
abbrev Verifier (Statement : Type) {n : ℕ} (pSpec : ProtocolSpec n) :=
  _root_.Verifier []ₒ Statement Bool pSpec

/-- The empty interface has a unique handler, with no state effects. -/
def emptyImpl {σ : Type} : QueryImpl []ₒ (StateT σ ProbComp) := fun q => nomatch q

/-- An SR adversary returns `((𝕩, τ), α)`: the statement, chosen salt, and prover messages.
It queries the single-salt challenge oracles and uses private coins. The empty summand is
only the generic backend's interface adapter. -/
abbrev SRProver (Statement : Type) {Salt : Type} {n : ℕ} (pSpec : ProtocolSpec n) :=
  Prover.StateRestoration.Soundness []ₒ unifSpec Statement pSpec (Salt := Salt)

/-- An ordinary non-rewinding SR extractor computes `E(𝕩, τ, T, tr_sr)` from the original
statement, chosen salt, final transcript, and SR move-response trace. It may use private coins
and may fail; it receives no prover handle or private sampling log. -/
abbrev SRExtractor (Statement Witness : Type) {Salt : Type} {n : ℕ} (pSpec : ProtocolSpec n) :=
  Statement → Salt → pSpec.FullTranscript → QueryLog (srChallengeOracle (Statement × Salt) pSpec) →
    OptionT ProbComp Witness

/-- Run an ordinary SR adversary and reconstruct its final transcript using the same
verifier-message functions queried during its moves. -/
def srGame {Statement Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    (P : SRProver Statement pSpec (Salt := Salt)) :
    OracleComp (([]ₒ + srChallengeOracle (Statement × Salt) pSpec) + unifSpec)
      (pSpec.FullTranscript × (Statement × Salt)) :=
  srSoundnessGame (Salt := Salt) P

/-- The internal reduction output relation for Boolean acceptance has a dummy witness. -/
def acceptRelation : Set (Bool × Unit) := {result | result.1 ∈ ({true} : Set Bool)}

/-- Add the unique dummy witness required by the generic reduction game. -/
def SRProver.toReduction {Statement Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    (P : SRProver Statement pSpec (Salt := Salt)) :
    Prover.StateRestoration.KnowledgeSoundness []ₒ unifSpec Statement Unit pSpec (Salt := Salt) :=
  (fun result => (result.1, result.2, ())) <$> P

/-- Erase the generic game's dummy witness. This does not change any query. -/
def SRProver.ofReduction {Statement Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    (P : Prover.StateRestoration.KnowledgeSoundness
      []ₒ unifSpec Statement Unit pSpec (Salt := Salt)) :
    SRProver Statement pSpec (Salt := Salt) :=
  (fun result => (result.1, result.2.1)) <$> P

/-- The dummy output witness carries no information. -/
theorem SRProver.toReduction_ofReduction {Statement Salt : Type} {n : ℕ}
    {pSpec : ProtocolSpec n}
    (P : Prover.StateRestoration.KnowledgeSoundness
      []ₒ unifSpec Statement Unit pSpec (Salt := Salt)) :
    (SRProver.ofReduction P).toReduction = P := by
  unfold Prover.StateRestoration.KnowledgeSoundness at P
  simp only [SRProver.toReduction, SRProver.ofReduction, Functor.map_map]
  have h : (fun result : (Statement × Salt) × pSpec.Messages × Unit =>
      (result.1, result.2.1, ())) = id := by
    funext ⟨x, messages, u⟩
    cases u
    rfl
  rw [h, id_map]

/-- Adapt the ordinary extractor to the general reduction interface. Pass it the statement,
salt, transcript, and SR move-response log, discarding the empty ambient logs and dummy witness. -/
def SRExtractor.toReduction {Statement Witness Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}
    (E : SRExtractor Statement Witness pSpec (Salt := Salt)) :
    Extractor.StateRestoration []ₒ Statement Witness Unit pSpec (Salt := Salt) :=
  fun x salt _ transcript log _ => OptionT.mk
    (liftComp (E x salt transcript log.snd).run ([]ₒ + unifSpec))

section

variable {Statement Witness Salt : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  [∀ i, SampleableType (pSpec.Challenge i)]
  [DecidableEq Statement] [∀ i, DecidableEq (pSpec.Message i)]
  [∀ i, DecidableEq (pSpec.Challenge i)]
  (init : ProbComp (QueryImpl (srChallengeOracle (Statement × Salt) pSpec) Id))

/-- Extraction failure for an ordinary SR adversary. The dummy witness is introduced only
inside the general backend; the adversary and extractor interfaces do not expose it. -/
noncomputable def srKnowledgeSoundnessFailureProb (relation : Set (Statement × Witness))
    (V : Verifier Statement pSpec) (E : SRExtractor Statement Witness pSpec (Salt := Salt))
    (P : SRProver Statement pSpec (Salt := Salt)) : ENNReal :=
  _root_.Verifier.StateRestoration.knowledgeSoundnessFailureProb (Salt := Salt) init emptyImpl
    (QueryImpl.id' unifSpec) E.toReduction relation acceptRelation V P.toReduction

omit [DecidableEq Statement] [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Challenge i)] in
/-- The same named ordinary extractor works in the general dummy-witness game. -/
theorem srKnowledgeSoundnessQueryBoundedWithExtractor_to_generic
    (relation : Set (Statement × Witness)) (V : Verifier Statement pSpec)
    (E : SRExtractor Statement Witness pSpec (Salt := Salt)) (t : ℕ) (error : ENNReal)
    (h : ∀ P : SRProver Statement pSpec (Salt := Salt),
      P.IsQueryBoundP (publicQuerySelector
        (_root_.Verifier.StateRestoration.isSrChallengeMove (Salt := Salt) (oSpec := []ₒ))) t →
      srKnowledgeSoundnessFailureProb (Salt := Salt) init relation V E P ≤ error) :
    _root_.Verifier.StateRestoration.knowledgeSoundnessQueryBoundedWithExtractor (Salt := Salt)
      init emptyImpl relation acceptRelation V E.toReduction
      (_root_.Verifier.StateRestoration.isSrChallengeMove (Salt := Salt)) t error := by
  intro P hP
  unfold Prover.StateRestoration.KnowledgeSoundness at P
  have hBound : (SRProver.ofReduction P).IsQueryBoundP
      (publicQuerySelector (_root_.Verifier.StateRestoration.isSrChallengeMove (Salt := Salt)
        (oSpec := []ₒ))) t := by
    simpa only [SRProver.ofReduction, isQueryBoundP_map_iff] using hP
  have hResult := h (SRProver.ofReduction P) hBound
  unfold srKnowledgeSoundnessFailureProb at hResult
  simp only [SRProver.toReduction_ofReduction] at hResult
  exact hResult

end

section Families

variable {Statement Witness : Type} {Salt : ℕ → ℕ → Type}
  {rounds : ℕ → ℕ → ℕ} {pSpec : ∀ s n, ProtocolSpec (rounds s n)}
  [∀ s n i, SampleableType ((pSpec s n).Challenge i)]
  [DecidableEq Statement] [∀ s n i, DecidableEq ((pSpec s n).Message i)]
  [∀ s n i, DecidableEq ((pSpec s n).Challenge i)]
  (init : ∀ s n, ProbComp
    (QueryImpl (srChallengeOracle (Statement × Salt s n) (pSpec s n)) Id))
  (V : ∀ s n, Verifier Statement (pSpec s n))

/-- **[snarg-book, state-restoration soundness]** SR soundness for every public salt-size
parameter `s`, instance-size bound `n`, and move budget `t`. The salt carrier and challenge
sampler may depend on `s,n`. Guarding the final decision implements the joint event
`size x ≤ n ∧ x ∉ language ∧ accepted`; it does not condition or truncate the game. -/
def srSoundness (language : Set Statement) (size : Statement → ℕ)
    (error : ℕ → ℕ → ℕ → ENNReal) : Prop :=
  ∀ s n t, _root_.Verifier.StateRestoration.soundnessQueryBounded (Salt := Salt s n)
    (init s n) emptyImpl language {true} ((V s n).restrictSize size n)
    (_root_.Verifier.StateRestoration.isSrChallengeMove (Salt := Salt s n)) t (error s n t)

/-- The state-restoration bound for a supplied non-rewinding extractor family, for every
salt-size parameter `s`, instance-size bound `n`, move budget, and adversary. The family may
depend on `s` and `n`; no efficiency guarantee is imposed. -/
def srKnowledgeSoundnessWithExtractor (relation : Set (Statement × Witness)) (size : Statement → ℕ)
    (E : ∀ s n, SRExtractor Statement Witness (pSpec s n) (Salt := Salt s n))
    (error : ℕ → ℕ → ℕ → ENNReal) : Prop :=
  ∀ s n t (P : SRProver Statement (pSpec s n) (Salt := Salt s n)),
    P.IsQueryBoundP (publicQuerySelector
      (_root_.Verifier.StateRestoration.isSrChallengeMove (Salt := Salt s n) (oSpec := []ₒ))) t →
    srKnowledgeSoundnessFailureProb (init s n) relation ((V s n).restrictSize size n)
      (E s n) P ≤ error s n t

/-- **[snarg-book, state-restoration knowledge soundness]** One non-rewinding extractor
family satisfies `srKnowledgeSoundnessWithExtractor`. With no resource bound on the
extractor, classical witness selection gives an extractor from soundness for the relation's
language. See `Verifier.knowledgeSoundness_iff_relationSoundness` for this argument in the
ordinary interactive game. -/
def srKnowledgeSoundness (relation : Set (Statement × Witness)) (size : Statement → ℕ)
    (error : ℕ → ℕ → ℕ → ENNReal) : Prop :=
  ∃ E, srKnowledgeSoundnessWithExtractor init V relation size E error

end Families

end IP
