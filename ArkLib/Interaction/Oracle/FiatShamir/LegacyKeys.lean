/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.LegacyCorrespondence

/-!
# Native restoration keys and legacy Fiat–Shamir queries

An alternating legacy transcript hashes precisely the public-message prefix before each
challenge. This module identifies those dependent query keys with the native fixed-round
restoration keys, then transports complete challenge tables across that identification.
-/

@[expose] public section

namespace Interaction.Oracle.FiatShamir

open Security.StateRestoration ProtocolSpec OracleSpec

/-- The legacy index of the first challenge in a nonempty alternating schedule. -/
def legacyChallengeHere (round : Round) (rounds : List Round) :
    (legacySpec (round :: rounds)).ChallengeIdx :=
  ⟨Fin.succ (0 : Fin (legacySteps rounds + 1)), by simp [legacySpec, ProtocolSpec.cons]⟩

/-- Embed a challenge index of the remaining schedule after the first message and challenge. -/
def legacyChallengeLater (round : Round) (rounds : List Round)
    (i : (legacySpec rounds).ChallengeIdx) :
    (legacySpec (round :: rounds)).ChallengeIdx :=
  ⟨Fin.succ (Fin.succ i.1), by simpa [legacySpec, ProtocolSpec.cons] using i.2⟩

@[simp]
theorem legacyChallengeHere_response (round : Round) (rounds : List Round) :
    (legacySpec (round :: rounds)).Challenge (legacyChallengeHere round rounds) =
      round.Challenge := by
  simp [legacySpec, legacyChallengeHere, ProtocolSpec.Challenge, ProtocolSpec.cons]

@[simp]
theorem legacyChallengeLater_response (round : Round) (rounds : List Round)
    (i : (legacySpec rounds).ChallengeIdx) :
    (legacySpec (round :: rounds)).Challenge (legacyChallengeLater round rounds i) =
      (legacySpec rounds).Challenge i := by
  simp [legacySpec, legacyChallengeLater, ProtocolSpec.Challenge, ProtocolSpec.cons]

/-- Every challenge in a nonempty alternating schedule is its first one or comes from the tail. -/
theorem legacyChallenge_here_or_later (round : Round) (rounds : List Round)
    (i : (legacySpec (round :: rounds)).ChallengeIdx) :
    i = legacyChallengeHere round rounds ∨
      ∃ j : (legacySpec rounds).ChallengeIdx, i = legacyChallengeLater round rounds j := by
  rcases i with ⟨idx, hdir⟩
  cases idx using Fin.cases with
  | zero => simp [legacySpec, ProtocolSpec.cons] at hdir
  | succ idx =>
      cases idx using Fin.cases with
      | zero =>
          left
          apply Subtype.ext
          rfl
      | succ idx =>
          right
          have htail : (legacySpec rounds).dir idx = .V_to_P := by
            simpa [legacySpec, ProtocolSpec.cons] using hdir
          exact ⟨⟨idx, htail⟩, by apply Subtype.ext; rfl⟩

theorem legacyChallengeHere_ne_later (round : Round) (rounds : List Round)
    (i : (legacySpec rounds).ChallengeIdx) :
    legacyChallengeHere round rounds ≠ legacyChallengeLater round rounds i := by
  intro h
  have hidx := congrArg Subtype.val h
  have hv := congrArg Fin.val hidx
  simp [legacyChallengeHere, legacyChallengeLater] at hv

theorem legacyChallengeLater_injective (round : Round) (rounds : List Round) :
    Function.Injective (legacyChallengeLater round rounds) := by
  intro i j h
  apply Subtype.ext
  exact Fin.succ_injective _ (Fin.succ_injective _ (congrArg Subtype.val h))

/-- The legacy challenge round selected by a native restoration key. -/
def keyChallengeIndex {Input : Type} : {rounds : List Round} →
    Key Input PUnit rounds → (legacySpec rounds).ChallengeIdx
  | [], key => nomatch key
  | round :: rounds, .inl _ => legacyChallengeHere round rounds
  | round :: rounds, .inr (_, _, key) =>
      legacyChallengeLater round rounds (keyChallengeIndex key)

/-- The selected legacy and native oracle queries have the same answer type. -/
theorem keyChallengeIndex_response {Input : Type} : {rounds : List Round} →
    (key : Key Input PUnit rounds) →
    (legacySpec rounds).Challenge (keyChallengeIndex key) = key.Challenge
  | [], key => key.elim
  | round :: rounds, .inl _ => legacyChallengeHere_response round rounds
  | round :: rounds, .inr (_, _, key) => by
      simpa only [keyChallengeIndex, legacyChallengeLater_response, Key.Challenge] using
        keyChallengeIndex_response key

/-- Every legacy FS challenge retains a native sampler at the same round. -/
theorem legacyChallengeSampleable_nonempty : (rounds : List Round) →
    ∀ i : (legacySpec rounds).ChallengeIdx,
      Nonempty (SampleableType ((legacySpec rounds).Challenge i))
  | [], i => i.1.elim0
  | round :: rounds, i => by
      rcases legacyChallenge_here_or_later round rounds i with h | ⟨j, h⟩
      · subst i
        rw [legacyChallengeHere_response]
        exact ⟨round.sampleChallenge⟩
      · subst i
        rw [legacyChallengeLater_response]
        exact legacyChallengeSampleable_nonempty rounds j

/-- A uniform sampler for each legacy challenge carrier, inherited from the corresponding native
round. This supplies the sampling law, not an equality of sampling programs. -/
@[instance_reducible]
noncomputable def legacyChallengeSampleable (rounds : List Round) :
    ∀ i : (legacySpec rounds).ChallengeIdx,
      SampleableType ((legacySpec rounds).Challenge i) :=
  fun i => Classical.choice (legacyChallengeSampleable_nonempty rounds i)

/-- A deterministic assignment to every query of the concrete legacy FS challenge oracle. -/
abbrev LegacyTable (Input : Type) (rounds : List Round) :=
  (q : (fsChallengeOracle Input (legacySpec rounds)).Domain) →
    (fsChallengeOracle Input (legacySpec rounds)).Range q

/-- The legacy FS query corresponding to a first-round native restoration key. -/
def firstLegacyQuery {Input : Type} (round : Round) (rounds : List Round)
    (input : Input) (message : round.Message) :
    (fsChallengeOracle Input (legacySpec (round :: rounds))).Domain :=
  ⟨legacyChallengeHere round rounds,
    ⟨input, firstLegacyPrefixEquiv round rounds message⟩⟩

theorem firstLegacyQuery_injective {Input : Type} (round : Round) (rounds : List Round) :
    Function.Injective (fun p : Input × round.Message =>
      firstLegacyQuery round rounds p.1 p.2) := by
  intro ⟨z₁, m₁⟩ ⟨z₂, m₂⟩ h
  have hdata : (z₁, firstLegacyPrefixEquiv round rounds m₁) =
      (z₂, firstLegacyPrefixEquiv round rounds m₂) := by
    exact eq_of_heq (Sigma.mk.inj h).2
  have hz : z₁ = z₂ := congrArg Prod.fst hdata
  have hm : m₁ = m₂ := (firstLegacyPrefixEquiv round rounds).injective
    (congrArg Prod.snd hdata)
  cases hz
  cases hm
  rfl

theorem firstLegacyQuery_surjective_on_here {Input : Type} (round : Round)
    (rounds : List Round)
    (q : (fsChallengeOracle Input (legacySpec (round :: rounds))).Domain)
    (h : q.1 = legacyChallengeHere round rounds) :
    ∃ input message, q = firstLegacyQuery round rounds input message := by
  rcases q with ⟨i, input, messages⟩
  change i = legacyChallengeHere round rounds at h
  subst i
  obtain ⟨message, hm⟩ := (firstLegacyPrefixEquiv round rounds).surjective messages
  exact ⟨input, message, by simp [firstLegacyQuery, hm]⟩

/-- Prepend a public message to a legacy challenge query in the remaining rounds. -/
def laterLegacyQuery {Input : Type} (round : Round) (rounds : List Round)
    (message : round.Message)
    (q : (fsChallengeOracle Input (legacySpec rounds)).Domain) :
    (fsChallengeOracle Input (legacySpec (round :: rounds))).Domain :=
  ⟨legacyChallengeLater round rounds q.1,
    ⟨q.2.1, laterLegacyPrefixEquiv round rounds q.1 (message, q.2.2)⟩⟩

theorem laterLegacyQuery_injective {Input : Type} (round : Round) (rounds : List Round) :
    Function.Injective (fun p : round.Message ×
      (fsChallengeOracle Input (legacySpec rounds)).Domain =>
        laterLegacyQuery round rounds p.1 p.2) := by
  intro ⟨message₁, q₁⟩ ⟨message₂, q₂⟩ h
  rcases q₁ with ⟨i₁, input₁, messages₁⟩
  rcases q₂ with ⟨i₂, input₂, messages₂⟩
  have hi : i₁ = i₂ :=
    legacyChallengeLater_injective round rounds (congrArg Sigma.fst h)
  subst i₂
  have hdata : (input₁, laterLegacyPrefixEquiv round rounds i₁
      (message₁, messages₁)) =
      (input₂, laterLegacyPrefixEquiv round rounds i₁
        (message₂, messages₂)) := by
    exact eq_of_heq (Sigma.mk.inj h).2
  have hinput : input₁ = input₂ := congrArg Prod.fst hdata
  have hmessages : (message₁, messages₁) = (message₂, messages₂) :=
    (laterLegacyPrefixEquiv round rounds i₁).injective (congrArg Prod.snd hdata)
  cases hinput
  cases hmessages
  rfl

theorem laterLegacyQuery_surjective_on_later {Input : Type} (round : Round)
    (rounds : List Round)
    (q : (fsChallengeOracle Input (legacySpec (round :: rounds))).Domain)
    (i : (legacySpec rounds).ChallengeIdx)
    (h : q.1 = legacyChallengeLater round rounds i) :
    ∃ message qTail, q = laterLegacyQuery round rounds message qTail := by
  rcases q with ⟨j, input, messages⟩
  change j = legacyChallengeLater round rounds i at h
  subst j
  obtain ⟨⟨message, suffix⟩, hm⟩ :=
    (laterLegacyPrefixEquiv round rounds i).surjective messages
  exact ⟨message, ⟨i, (input, suffix)⟩, by simp [laterLegacyQuery, hm]⟩

/-- Send each native restoration key to its exact legacy Fiat–Shamir oracle query. -/
def keyToLegacy {Input : Type} : (rounds : List Round) →
    Key Input PUnit rounds → (fsChallengeOracle Input (legacySpec rounds)).Domain
  | [], key => nomatch key
  | round :: rounds, .inl (input, message, _) =>
      firstLegacyQuery round rounds input message
  | round :: rounds, .inr (message, _, key) =>
      laterLegacyQuery round rounds message (keyToLegacy rounds key)

/-- Query transport preserves the challenge round selected by the native key. -/
theorem keyToLegacy_index {Input : Type} : (rounds : List Round) →
    (key : Key Input PUnit rounds) →
      (keyToLegacy rounds key).1 = keyChallengeIndex key
  | [], key => key.elim
  | _ :: _, .inl _ => rfl
  | round :: rounds, .inr (_, _, key) =>
      congrArg (legacyChallengeLater round rounds) (keyToLegacy_index rounds key)

theorem keyToLegacy_injective {Input : Type} : (rounds : List Round) →
    Function.Injective (keyToLegacy (Input := Input) rounds)
  | [] => by
      intro key₁
      exact key₁.elim
  | round :: rounds => by
      intro key₁ key₂ h
      cases key₁ with
      | inl data₁ =>
          rcases data₁ with ⟨input₁, message₁, salt₁⟩
          cases salt₁
          cases key₂ with
          | inl data₂ =>
              rcases data₂ with ⟨input₂, message₂, salt₂⟩
              cases salt₂
              have hp : (input₁, message₁) = (input₂, message₂) :=
                firstLegacyQuery_injective round rounds (by
                  simpa only [keyToLegacy] using h)
              cases hp
              rfl
          | inr data₂ =>
              rcases data₂ with ⟨message₂, salt₂, tail₂⟩
              have hi : legacyChallengeHere round rounds =
                  legacyChallengeLater round rounds (keyToLegacy rounds tail₂).1 := by
                exact congrArg Sigma.fst h
              exact (legacyChallengeHere_ne_later round rounds _ hi).elim
      | inr data₁ =>
          rcases data₁ with ⟨message₁, salt₁, tail₁⟩
          cases salt₁
          cases key₂ with
          | inl data₂ =>
              rcases data₂ with ⟨input₂, message₂, salt₂⟩
              have hi : legacyChallengeLater round rounds (keyToLegacy rounds tail₁).1 =
                  legacyChallengeHere round rounds := by
                exact congrArg Sigma.fst h
              exact (legacyChallengeHere_ne_later round rounds _ hi.symm).elim
          | inr data₂ =>
              rcases data₂ with ⟨message₂, salt₂, tail₂⟩
              cases salt₂
              have hp : (message₁, keyToLegacy rounds tail₁) =
                  (message₂, keyToLegacy rounds tail₂) :=
                laterLegacyQuery_injective round rounds (by
                  simpa only [keyToLegacy] using h)
              have hm : message₁ = message₂ := congrArg Prod.fst hp
              have ht : tail₁ = tail₂ :=
                keyToLegacy_injective rounds (congrArg Prod.snd hp)
              cases hm
              cases ht
              rfl

theorem keyToLegacy_surjective {Input : Type} : (rounds : List Round) →
    Function.Surjective (keyToLegacy (Input := Input) rounds)
  | [] => by
      intro ⟨i, _⟩
      exact i.1.elim0
  | round :: rounds => by
      intro q
      rcases legacyChallenge_here_or_later round rounds q.1 with hi | ⟨i, hi⟩
      · obtain ⟨input, message, hq⟩ :=
          firstLegacyQuery_surjective_on_here round rounds q hi
        refine ⟨Key.here input message PUnit.unit, ?_⟩
        simpa only [keyToLegacy, Key.here] using hq.symm
      · obtain ⟨message, qTail, hq⟩ :=
          laterLegacyQuery_surjective_on_later round rounds q i hi
        obtain ⟨tail, ht⟩ := keyToLegacy_surjective rounds qTail
        refine ⟨Key.later message PUnit.unit tail, ?_⟩
        simpa only [keyToLegacy, Key.later, ht] using hq.symm

/-- Native restoration keys are exactly the old Fiat–Shamir challenge-oracle queries. -/
noncomputable def keyEquiv (Input : Type) (rounds : List Round) :
    Key Input PUnit rounds ≃
      (fsChallengeOracle Input (legacySpec rounds)).Domain :=
  Equiv.ofBijective (keyToLegacy rounds)
    ⟨keyToLegacy_injective rounds, keyToLegacy_surjective rounds⟩

/-- The key equivalence preserves each query's dependent challenge response type. -/
theorem keyEquiv_response {Input : Type} (rounds : List Round)
    (key : Key Input PUnit rounds) :
    (fsChallengeOracle Input (legacySpec rounds)).Range (keyEquiv Input rounds key) =
      key.Challenge := by
  change (legacySpec rounds).Challenge (keyToLegacy rounds key).1 = key.Challenge
  rw [keyToLegacy_index rounds key]
  exact keyChallengeIndex_response key

/-- Bijection of complete cached challenge tables, with each answer carried to its exact fibre. -/
noncomputable def nativeLegacyTableEquiv (Input : Type) (rounds : List Round) :
    Table Input PUnit rounds ≃ LegacyTable Input rounds :=
  (keyEquiv Input rounds).piCongr
    (fun key => Equiv.cast (keyEquiv_response rounds key).symm)

/-- Present a full native challenge table to the legacy Fiat–Shamir oracle. -/
noncomputable def nativeTableToLegacy {Input : Type} (rounds : List Round)
    (table : Table Input PUnit rounds) : LegacyTable Input rounds :=
  nativeLegacyTableEquiv Input rounds table

/-- Recover a full native restoration table from a legacy Fiat–Shamir table. -/
noncomputable def legacyTableToNative {Input : Type} (rounds : List Round)
    (table : LegacyTable Input rounds) : Table Input PUnit rounds :=
  (nativeLegacyTableEquiv Input rounds).symm table

@[simp]
theorem legacyTableToNative_nativeTableToLegacy {Input : Type} (rounds : List Round)
    (table : Table Input PUnit rounds) :
    legacyTableToNative rounds (nativeTableToLegacy rounds table) = table :=
  (nativeLegacyTableEquiv Input rounds).symm_apply_apply table

@[simp]
theorem nativeTableToLegacy_legacyTableToNative {Input : Type} (rounds : List Round)
    (table : LegacyTable Input rounds) :
    nativeTableToLegacy rounds (legacyTableToNative rounds table) = table :=
  (nativeLegacyTableEquiv Input rounds).apply_symm_apply table

@[simp]
theorem nativeTableToLegacy_apply {Input : Type} (rounds : List Round)
    (table : Table Input PUnit rounds) (key : Key Input PUnit rounds) :
    nativeTableToLegacy rounds table (keyEquiv Input rounds key) =
      cast (keyEquiv_response rounds key).symm (table key) := by
  exact (keyEquiv Input rounds).piCongr_apply_apply
    (fun key => Equiv.cast (keyEquiv_response rounds key).symm) table key

private theorem cast_oracleComp_eq_map_cast {ι : Type} {spec : OracleSpec ι}
    {α β : Type} (h : α = β) (oa : OracleComp spec α) :
    (Equiv.cast (congrArg (OracleComp spec) h)) oa = (cast h) <$> oa := by
  cases h
  have hcast : (cast (rfl : α = α)) = (id : α → α) := by
    funext x
    exact cast_eq _ x
  rw [hcast, id_map]
  rw [Equiv.cast_apply]
  exact cast_eq (congrArg (OracleComp spec) (rfl : α = α)) oa

/-- Answer actual legacy Fiat–Shamir challenge queries through the native restoration oracle. -/
noncomputable def legacyQueryInNative {Input : Type} (rounds : List Round) :
    QueryImpl (fsChallengeOracle Input (legacySpec rounds))
      (OracleComp (oracleSpec Input PUnit rounds)) :=
  (keyEquiv Input rounds).piCongr
    (fun key => Equiv.cast (congrArg (OracleComp (oracleSpec Input PUnit rounds))
      (keyEquiv_response rounds key).symm))
    (fun key => liftM ((oracleSpec Input PUnit rounds).query key))

@[simp]
theorem legacyQueryInNative_apply_keyEquiv {Input : Type} (rounds : List Round)
    (key : Key Input PUnit rounds) :
    legacyQueryInNative rounds (keyEquiv Input rounds key) =
      (fun answer => cast (keyEquiv_response rounds key).symm answer) <$>
        liftM ((oracleSpec Input PUnit rounds).query key) := by
  rw [legacyQueryInNative, (keyEquiv Input rounds).piCongr_apply_apply]
  exact cast_oracleComp_eq_map_cast (keyEquiv_response rounds key).symm _

/-- Concrete legacy queries read exactly the corresponding transported native table entry. -/
theorem legacyQueryInNative_eval {Input : Type} (rounds : List Round)
    (table : Table Input PUnit rounds)
    (q : (fsChallengeOracle Input (legacySpec rounds)).Domain) :
    evalWithAnswerFn (QueryImpl.ofFn table) (legacyQueryInNative rounds q) =
      nativeTableToLegacy rounds table q := by
  obtain ⟨key, rfl⟩ := (keyEquiv Input rounds).surjective q
  simp only [legacyQueryInNative_apply_keyEquiv, evalWithAnswerFn_map,
    evalWithAnswerFn_liftM_query, QueryImpl.ofFn_apply, nativeTableToLegacy_apply]

/-- Answer native restoration queries through the actual legacy Fiat–Shamir oracle. -/
noncomputable def nativeQueryInLegacy {Input : Type} (rounds : List Round) :
    QueryImpl (oracleSpec Input PUnit rounds)
      (OracleComp (fsChallengeOracle Input (legacySpec rounds))) :=
  fun key =>
    (fun answer => cast (keyEquiv_response rounds key) answer) <$>
      liftM ((fsChallengeOracle Input (legacySpec rounds)).query (keyEquiv Input rounds key))

end Interaction.Oracle.FiatShamir
