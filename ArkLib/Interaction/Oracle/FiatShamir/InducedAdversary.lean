/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.FiatShamir.PublicMessage
public import ArkLib.Interaction.Oracle.Security.StateRestorationRandomized

/-!
# Single-salt proof and induced restoration adversary

The public proof carries one global salt. Repackaging the selected statement and proof gives the
native restoration experiment input `(statement, salt)` and a complete sequence with trivial
per-round salts. This transformation runs no oracle query, so the adversary's ordered challenge
log and final lazy cache are identical, including when it returns failure.
-/

@[expose] public section

open Interaction.Oracle OracleComp OracleSpec

namespace Interaction.Oracle.FiatShamir

open Security.StateRestoration

/-- A single global salt followed by every public prover message. -/
abbrev SaltedProof (GlobalSalt : Type) (rounds : List Round) :=
  GlobalSalt × PublicMessages rounds

/-- The output rearrangement of a malicious single-salt proof producer. -/
def toRestorationSelection {Statement GlobalSalt Witness : Type} {rounds : List Round} :
    Option (Statement × SaltedProof GlobalSalt rounds × Witness) →
      Option ((Statement × GlobalSalt) × Messages PUnit rounds × Witness)
  | none => none
  | some (statement, (salt, messages), witness) =>
      some ((statement, salt), withUnitSalts rounds messages, witness)

/-- The induced native restoration adversary shares the typed challenge oracle verbatim. -/
def inducedAdversary {Statement GlobalSalt Witness : Type} {rounds : List Round}
    (adversary : OracleComp
      (unifSpec + oracleSpec (Statement × GlobalSalt) PUnit rounds)
      (Option (Statement × SaltedProof GlobalSalt rounds × Witness))) :
    RandomizedRestorationAdversary (Statement × GlobalSalt) PUnit Witness rounds :=
  toRestorationSelection <$> adversary

/-- Output mapping does not change the ordered oracle log or the final lazy cache. -/
theorem inducedAdversary_loggedRun {Statement GlobalSalt Witness : Type}
    {rounds : List Round} [DecidableEq Statement] [DecidableEq GlobalSalt]
    (adversary : OracleComp
      (unifSpec + oracleSpec (Statement × GlobalSalt) PUnit rounds)
      (Option (Statement × SaltedProof GlobalSalt rounds × Witness)))
    (cache : (oracleSpec (Statement × GlobalSalt) PUnit rounds).QueryCache) :
    randomOracleLoggedRun (inducedAdversary adversary) cache =
      (fun result => ((toRestorationSelection result.1.1, result.1.2), result.2)) <$>
        randomOracleLoggedRun adversary cache := by
  exact randomOracleLoggedRun_map _ adversary cache

end Interaction.Oracle.FiatShamir
