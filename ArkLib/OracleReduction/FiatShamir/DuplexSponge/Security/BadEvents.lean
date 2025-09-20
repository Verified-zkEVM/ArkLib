/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ProverTransform
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.TraceTransform

/-!
# Definition and analysis of bad events

This file contains the definition and analysis of bad events for the analysis of duplex sponge
Fiat-Shamir, following Section 5.6 in the paper.

(TODO: may have to split this into multiple files given the number of lemmas)
-/

open OracleComp OracleSpec ProtocolSpec

#check QueryLog

namespace OracleSpec

namespace QueryLog

section
-- WIP defining more general properties for query log

variable {ι : Type*} [DecidableEq ι] {spec : OracleSpec ι} [spec.DecidableEq]

/-- A query tuple `(i, q, r)` is redundant in a query log if it appears more than once -/
def redundantQuery (log : QueryLog spec) (i : ι) (q : spec.domain i) (r : spec.range i) : Prop :=
  (log.getQ i).count (q, r) > 1

def existPriorSameQuery (log : QueryLog spec) (idx : Fin log.length) : Prop :=
  ∃ j' < idx, log[j'] = log[idx]

end

section DuplexSpongeFS

variable {StmtIn : Type} {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

/-- The definition of a redundant entry in a duplex sponge challenge oracle trace (Definition 5.5),
  used in the analysis of bad events

TODO: refactor this into a combination of simpler properties? -/
def redundantEntryDS (log : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (idx : Fin log.length) : Prop :=
  match log[idx] with
  /- If it's a hash query, it's redundant if there is a prior hash query with the same query-answer
     pair -/
  | ⟨.inl _, ⟨stmt, state⟩⟩ => ∃ j' < idx, log[j'] = ⟨.inl _, ⟨stmt, state⟩⟩
  /- If it's a permutation query (`dir ∈ {Fwd, Bwd}`), it's redundant if there is a prior
    permutation query with either:
    - the same direction and input-output pair, or
    - the opposite direction and output-input pair -/
  | ⟨.inr .Fwd, stateIn, stateOut⟩ =>
    ∃ j' < idx, log[j'] = ⟨.inr .Fwd, stateIn, stateOut⟩ ∨ log[j'] = ⟨.inr .Bwd, stateOut, stateIn⟩
  | ⟨.inr .Bwd, stateOut, stateIn⟩ =>
    ∃ j' < idx, log[j'] = ⟨.inr .Bwd, stateOut, stateIn⟩ ∨ log[j'] = ⟨.inr .Fwd, stateIn, stateOut⟩

/-- A duplex sponge challenge oracle trace has no redundant entries if no entry is redundant -/
def NoRedundantEntryDS (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) : Prop :=
  ∀ idx : Fin log.length, ¬ log.redundantEntryDS idx

/-- Procedure to remove all redundant queries from the duplex sponge query-answer trace -/
def removeRedundantEntryDS (log : QueryLog (duplexSpongeChallengeOracle StmtIn U)) :
    {log : QueryLog (duplexSpongeChallengeOracle StmtIn U) | log.NoRedundantEntryDS} :=
  sorry

namespace BadEventDS

/-! Fist, we define the main bad event, which consists of four sub-cases -/

-- def hash

-- def perm

-- def permInv

-- def func

-- def combined = hash + perm + permInv + func

/-! Then we define other bad events that would be false (`= 0`) if the main event is false (`= 0`)
-/

-- def collisionFwdFwd

-- def collisionFwdBwd

-- def collisionBwdFwd

-- def collisionBwdBwd

-- def collisionPerm

-- alias prp := collisionPerm

-- lemma not_collisionPerm_of_not_combined

-- def inv

-- lemma not_inv_of_not_combined

-- def fork

-- lemma not_fork_of_not_combined

-- def outOfOrderHash

-- def outOfOrderPerm

-- def outOfOrder

-- alias time := outOfOrder

-- lemma not_outOfOrder_of_not_combined

end BadEventDS

end DuplexSpongeFS

end QueryLog

end OracleSpec
