/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.OracleComp.RandomOracleQueryBounds
public import ArkLib.Interaction.Oracle.Security.StateRestorationRandomized

/-!
# Structural adversary query bounds for native restoration

Only the hash summand consumes the budget. The resulting support and expectation bounds refer to
the actual lazy cached run, with all earlier queries retained when the adversary returns `none`.
-/

@[expose] public section

open OracleComp OracleSpec

namespace Interaction.Oracle.Security.StateRestoration

/-- A structural hash-query bound implies the support cap used by native security theorems. -/
theorem adversaryFreshKeys_le_of_queryBound
    {Input Salt W : Type} [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (Q : ℕ) (hbound : adversary.IsQueryBoundP (fun q => q.isRight) Q)
    (phase : _) (hphase : phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅)) :
    (freshKeysOfLog phase.1.2).card ≤ Q :=
  randomOracleLoggedRun_distinctKeys_le_queryBound adversary.withQueryLog Q
    (hashQueryBound_withQueryLog adversary Q hbound) ∅ phase hphase

/-- The expected number of distinct adversary keys is at most its structural hash-query cap. -/
theorem expectedAdversaryFreshKeys_le_of_queryBound
    {Input Salt W : Type} [DecidableEq Input] [DecidableEq Salt]
    (rounds : List Round) (adversary : RandomizedRestorationAdversary Input Salt W rounds)
    (Q : ℕ) (hbound : adversary.IsQueryBoundP (fun q => q.isRight) Q) :
    expectedAdversaryFreshKeys rounds adversary ≤ Q :=
  expectedAdversaryFreshKeys_le_queryBound rounds adversary Q
    (adversaryFreshKeys_le_of_queryBound rounds adversary Q hbound)

end Interaction.Oracle.Security.StateRestoration
