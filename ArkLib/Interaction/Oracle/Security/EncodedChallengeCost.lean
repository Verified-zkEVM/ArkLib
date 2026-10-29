/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.EncodedChallengeCoupling
public import ArkLib.Interaction.Oracle.Security.EncodedWeighted

/-!
# Query costs under a change of challenge representation

Transporting uniformly sampled challenge answers through the common-carrier equivalences
preserves the expected weighted charge of distinct queried keys, including failed executions.
-/

@[expose] public section

open OracleComp OracleSpec MeasureTheory

namespace Interaction.Oracle.Security.StateRestoration

variable {Input Salt C A : Type} {rounds : List Round}

/-- Changing challenge representations preserves every distinct key in the hash log. -/
theorem CommonChallenge.freshKeys_toCommonLog
    [DecidableEq Input] [DecidableEq Salt]
    (common : CommonChallenge Input Salt C rounds)
    (log : QueryLog (oracleSpec Input Salt rounds)) :
    freshKeysOfLog (common.toCommonLog log) = freshKeysOfLog log := by
  induction log with
  | nil => rfl
  | cons entry tail ih =>
      simp only [CommonChallenge.toCommonLog, List.map_cons, freshKeysOfLog_cons]
      change insert entry.1 (freshKeysOfLog (common.toCommonLog tail)) =
        insert entry.1 (freshKeysOfLog tail)
      rw [ih]

/-- The full adaptive coupling preserves any nonnegative weight attached to each distinct key.
No termination or successful-return condition is imposed on the observed log. -/
theorem CommonChallenge.expectedFreshQueryCharge_simulateNative
    [DecidableEq Input] [DecidableEq Salt] [SampleableType C]
    (common : CommonChallenge Input Salt C rounds)
    (program : OracleComp (unifSpec + (Key Input Salt rounds →ₒ C)) A)
    (weight : Key Input Salt rounds → ENNReal) :
    expectedFreshQueryCharge (common.simulateNative program) weight =
      expectedFreshQueryCharge program weight := by
  let : MeasurableSpace
      ((A × QueryLog (oracleSpec Input Salt rounds)) ×
        (oracleSpec Input Salt rounds).QueryCache) := ⊤
  let : MeasurableSpace
      ((A × QueryLog (Key Input Salt rounds →ₒ C)) ×
        (Key Input Salt rounds →ₒ C).QueryCache) := ⊤
  have h := common.evalDist_randomOracleLoggedRun_simulateNative program ∅
  rw [common.toCommonCache_empty] at h
  unfold expectedFreshQueryCharge
  rw [← h, lintegral_evalDist_map_of_discrete]
  simp only [CommonChallenge.encodeJoint, freshQueryCharge, common.freshKeys_toCommonLog]

end Interaction.Oracle.Security.StateRestoration
