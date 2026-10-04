/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.LegacyKeys

/-!
# Canonical legacy completion queries

The alternating legacy transcript hashes the same message prefixes, in the same order, as
native fixed-round restoration completion. These data laws support an operational comparison
of the legacy knowledge game with the native cached execution.
-/

@[expose] public section

namespace Interaction.Oracle.FiatShamir

open Security.StateRestoration ProtocolSpec OracleSpec

private theorem nativeTableToLegacy_congr {Input : Type} (rounds : List Round)
    (table : Table Input PUnit rounds)
    {q₁ q₂ : (fsChallengeOracle Input (legacySpec rounds)).Domain}
    (h : q₁ = q₂) :
    nativeTableToLegacy rounds table q₁ ≍ nativeTableToLegacy rounds table q₂ := by
  cases h
  rfl

private theorem toLegacyTranscript_challenge_later (round : Round) (rounds : List Round)
    (path : (publicProtocol (round :: rounds)).tree.ExecutionPath)
    (i : (legacySpec rounds).ChallengeIdx) :
    (toLegacyTranscript (round :: rounds) path).toMessagesChallenges.2
      (legacyChallengeLater round rounds i) ≍
      (toLegacyTranscript rounds path.2.2).toMessagesChallenges.2 i := by
  rcases path with ⟨message, challenge, suffix⟩
  change (Fin.hcons message (Fin.hcons challenge (toLegacyTranscript rounds suffix)))
    (Fin.succ (Fin.succ i.1)) ≍ (toLegacyTranscript rounds suffix) i.1
  have houter := Fin.hcons_succ message
    (Fin.hcons challenge (toLegacyTranscript rounds suffix)) (Fin.succ i.1)
  have hinner := Fin.hcons_succ challenge (toLegacyTranscript rounds suffix) i.1
  exact (heq_of_eq houter).trans ((cast_heq _ _).trans
    ((heq_of_eq hinner).trans (cast_heq _ _)))

/-- The first canonical legacy query is the image of the first native completion key. -/
theorem canonicalLegacyQuery_here {Input : Type} (round : Round) (rounds : List Round)
    (z : Input) (message : round.Message) (suffix : PublicMessages rounds) :
    (⟨legacyChallengeHere round rounds,
      (z, (fullLegacyMessagesEquiv (round :: rounds) (message, suffix)).take
        (legacyChallengeHere round rounds).1.castSucc)⟩ :
      (fsChallengeOracle Input (legacySpec (round :: rounds))).Domain) =
      keyEquiv Input (round :: rounds) (Key.here z message PUnit.unit) := by
  change _ = firstLegacyQuery round rounds z message
  simp only [firstLegacyQuery]
  congr 1
  change (z, (fullLegacyMessagesEquiv (round :: rounds) (message, suffix)).take
      (legacyChallengeHere round rounds).1.castSucc) =
    (z, firstLegacyPrefixEquiv round rounds message)
  have hcut : (legacyChallengeHere round rounds).1.castSucc =
      (⟨1, by simp [legacySteps]⟩ : Fin (legacySteps (round :: rounds) + 1)) := by
    apply Fin.ext
    rfl
  cases hcut
  exact congrArg (fun pfx => (z, pfx))
    (fullLegacyMessagesEquiv_take_first round rounds message suffix)

/-- Every later canonical legacy query is the image of the corresponding embedded native key. -/
theorem canonicalLegacyQuery_later {Input : Type} (round : Round) (rounds : List Round)
    (z : Input) (message : round.Message) (suffix : PublicMessages rounds)
    (i : (legacySpec rounds).ChallengeIdx) :
    (⟨legacyChallengeLater round rounds i,
      (z, (fullLegacyMessagesEquiv (round :: rounds) (message, suffix)).take
        (legacyChallengeLater round rounds i).1.castSucc)⟩ :
      (fsChallengeOracle Input (legacySpec (round :: rounds))).Domain) =
      keyEquiv Input (round :: rounds) (Key.later message PUnit.unit
        ((keyEquiv Input rounds).symm
          ⟨i, (z, (fullLegacyMessagesEquiv rounds suffix).take i.1.castSucc)⟩)) := by
  change _ = laterLegacyQuery round rounds message
    ((keyEquiv Input rounds) ((keyEquiv Input rounds).symm
      ⟨i, (z, (fullLegacyMessagesEquiv rounds suffix).take i.1.castSucc)⟩))
  rw [Equiv.apply_symm_apply]
  simp only [laterLegacyQuery]
  congr 1
  change (z, (fullLegacyMessagesEquiv (round :: rounds) (message, suffix)).take
      (legacyChallengeLater round rounds i).1.castSucc) =
    (z, laterLegacyPrefixEquiv round rounds i
      (message, (fullLegacyMessagesEquiv rounds suffix).take i.1.castSucc))
  have hcut : (legacyChallengeLater round rounds i).1.castSucc =
      (Fin.succ (Fin.succ i.1)).castSucc := rfl
  cases hcut
  exact congrArg (fun pfx => (z, pfx))
    (fullLegacyMessagesEquiv_take_later round rounds i message suffix)

/-- Under a fixed native table, each challenge in the encoded completed path is exactly the
legacy Fiat–Shamir query at the full public-message prefix. -/
theorem completedPath_legacyChallenges {Input : Type} (rounds : List Round)
    (z : Input) (messages : PublicMessages rounds)
    (table : Table Input PUnit rounds) :
    (toLegacyTranscript rounds (toPublicPath rounds
      (completedPath rounds z (withUnitSalts rounds messages) table)))
        |>.toMessagesChallenges.2 =
      fun i => nativeTableToLegacy rounds table
        ⟨i, (z, (fullLegacyMessagesEquiv rounds messages).take i.1.castSucc)⟩ := by
  induction rounds with
  | nil => funext i; exact i.1.elim0
  | cons round rounds ih =>
      rcases messages with ⟨message, suffix⟩
      funext i
      rcases legacyChallenge_here_or_later round rounds i with hhere | ⟨j, hlater⟩
      · subst i
        have hq := canonicalLegacyQuery_here round rounds z message suffix
        have hdata : (z, (fullLegacyMessagesEquiv (round :: rounds)
            (message, suffix)).take (legacyChallengeHere round rounds).1.castSucc) =
            (z, firstLegacyPrefixEquiv round rounds message) := by
          exact eq_of_heq (Sigma.mk.inj hq).2
        have hv := congrArg (fun data => nativeTableToLegacy (round :: rounds) table
          ⟨legacyChallengeHere round rounds, data⟩) hdata
        rw [hv]
        change _ = nativeTableToLegacy (round :: rounds) table
          (keyEquiv Input (round :: rounds) (Key.here z message PUnit.unit))
        rw [nativeTableToLegacy_apply]
        simp only [toLegacyTranscript, toPublicPath, completedPath, withUnitSalts,
          legacyChallengeHere, ProtocolSpec.FullTranscript.toMessagesChallenges,
          ProtocolSpec.Transcript.toMessagesChallenges,
          ProtocolSpec.Transcript.toChallengesUpTo, Fin.hcons_succ, Fin.hcons_zero]
        apply eq_of_heq
        exact (cast_heq _ _).trans ((cast_heq _ _).trans (cast_heq _ _).symm)
      · subst i
        have hq := canonicalLegacyQuery_later round rounds z message suffix j
        let tailQuery : (fsChallengeOracle Input (legacySpec rounds)).Domain :=
          ⟨j, (z, (fullLegacyMessagesEquiv rounds suffix).take j.1.castSucc)⟩
        let tailKey := (keyEquiv Input rounds).symm tailQuery
        have htailEq : keyToLegacy rounds tailKey = tailQuery := by
          change (keyEquiv Input rounds) tailKey = tailQuery
          exact (keyEquiv Input rounds).apply_symm_apply tailQuery
        have htail := congrFun (ih suffix (fun q => table (Key.later message
          PUnit.unit q))) j
        apply eq_of_heq
        have htailQuery : tailQuery = (keyEquiv Input rounds) tailKey := by
          change tailQuery = keyToLegacy rounds tailKey
          exact htailEq.symm
        have htableTail : nativeTableToLegacy rounds
            (fun q => table (Key.later message PUnit.unit q)) tailQuery ≍
            table (Key.later message PUnit.unit tailKey) := by
          exact (nativeTableToLegacy_congr rounds _ htailQuery).trans
            ((heq_of_eq (nativeTableToLegacy_apply rounds
              (fun q => table (Key.later message PUnit.unit q)) tailKey)).trans
                (cast_heq _ _))
        have hpath := toLegacyTranscript_challenge_later round rounds
          (toPublicPath (round :: rounds)
            (completedPath (round :: rounds) z
              (withUnitSalts (round :: rounds) (message, suffix)) table)) j
        have hleft :
            (toLegacyTranscript (round :: rounds)
              (toPublicPath (round :: rounds)
                (completedPath (round :: rounds) z
                  (withUnitSalts (round :: rounds) (message, suffix)) table)))
                |>.toMessagesChallenges.2 (legacyChallengeLater round rounds j) ≍
              table (Key.later message PUnit.unit tailKey) := by
          exact hpath.trans ((heq_of_eq htail).trans htableTail)
        have hright : nativeTableToLegacy (round :: rounds) table
            ⟨legacyChallengeLater round rounds j,
              (z, (fullLegacyMessagesEquiv (round :: rounds)
                (message, suffix)).take (legacyChallengeLater round rounds j).1.castSucc)⟩ ≍
            table (Key.later message PUnit.unit tailKey) := by
          exact (nativeTableToLegacy_congr (round :: rounds) table hq).trans
            ((heq_of_eq (nativeTableToLegacy_apply (round :: rounds) table
              (Key.later message PUnit.unit tailKey))).trans (cast_heq _ _))
        exact hleft.trans hright.symm

end Interaction.Oracle.FiatShamir
