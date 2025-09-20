/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs

/-!
# Backtracking sequence family and procedure

This file contains the backtracking sequence family and procedure for the analysis of duplex sponge
Fiat-Shamir, following Section 5.2 in the paper.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS

variable {StmtIn : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]

/-- A backtracking sequence (Definition 5.3) for a given hash-duplex-sponge oracle trace `tr` and
  final duplex-sponge state `s` consists of the following data:
- An input statement `𝕩`
- A list `inputState = [sᵢₙ, ...]` of input states
- A list `outputState = [sₒᵤₜ, ...]` of output states

subject to the following conditions:
- The last of the input states is the given final state
- There is one more input state than output state
- The statement is queried with the hash, and returns the capacity of the first input state
  `(hash, 𝕩, inputState[0].capacitySegment) ∈ tr` -/
structure BacktrackSequence (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) where
  /-- The input statement in a backtracking sequence -/
  stmt : StmtIn
  /-- The list of input states in a backtracking sequence -/
  inputState : List (CanonicalSpongeState U)
  /-- The list of output states in a backtracking sequence -/
  outputState : List (CanonicalSpongeState U)

  /-- The input state list is one longer than the output state list -/
  inputState_length_eq_outputState_length_succ : inputState.length = outputState.length + 1

  /-- The last input state is the given final state -/
  last_inputState_eq_state : inputState[inputState.length - 1] = state

  /-- The query-answer pair `("hash", stmt, inputState[0].capacitySegment)` is in the trace -/
  hash_in_trace : (stmt, (Vector.drop inputState[0] SpongeSize.R)) ∈ trace.getQ (.inl ())

  /-- For all `i < outputState.length`, either
    - `inputState[i]` is permuted to `outputState[i]` in the trace, or
    - `outputState[i]` is inverted to `inputState[i]` in the trace -/
  permute_or_inv_in_trace : ∀ i : Fin outputState.length,
    (inputState[i], outputState[i]) ∈ trace.getQ (.inr .Fwd)
    ∨ (outputState[i], inputState[i]) ∈ trace.getQ (.inr .Bwd)

  /-- For all `i < outputState.length`, the capacity segment of `inputState[i]` is the same as
    the capacity segment of `outputState[i]` -/
  capacitySegment_output_eq_input : ∀ i : Fin outputState.length,
    outputState[i].capacitySegment = inputState[i.val + 1].capacitySegment

  /-- For all `i < outputState.length`, the capacity segment of `inputState[i]` is not the same as
    the capacity segment of `outputState[i]` -/
  capacitySegment_input_ne_output : ∀ i : Fin outputState.length,
    inputState[i].capacitySegment ≠ outputState[i].capacitySegment

/-- The associated indices (first occurrences in the trace) for a backtracking sequence -/
def BacktrackSequence.Index (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) (seq : BacktrackSequence trace state) :
    Fin trace.length × (Fin seq.inputState.length → Fin trace.length) :=
  -- TODO: define `List.findFinIdx` that returns `Fin (l.length + 1)` and `List.findFinIdxIfTrue`
  -- that returns `Fin l.length` given the fact that the predicate is true for at least one element
  -- of the list
  (⟨trace.findIdx sorry, sorry⟩, sorry)

/-- A family of backtrack sequences, defined as a finite set of backtrack sequences such that
no two sequences are strict subsets of each other -/
structure BacktrackSequenceFamily (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) where
  /-- The family of backtrack sequences, defined as a finite set -/
  seqFamily : Finset (BacktrackSequence trace state)
  /-- Maximality condition: no strict containment between two sequences, defined in terms of
    - the statements are different, or
    - the input states are not a strict subset of each other, or
    - the output states are not a strict subset of each other -/
  maximality : ∀ s ∈ seqFamily, ∀ s' ∈ seqFamily,
    (s.stmt ≠ s'.stmt) ∨ ¬ (s.inputState ⊆ s'.inputState) ∨ ¬ (s'.outputState ⊆ s.outputState)

/-- The backtracking procedure in Section 5.2, which takes in:
- the query-answer trace for the oracle `(h, p, p⁻¹)`
- a state (vector of `N` units)

And returns one of the following:
- `none`
- `err`
- A result consisting of: an input statement, a round index `i ≤ n`, and the protocol messages up to
  round `i`

NOTE: we do _not_ define the extra data structure `tr▵` as in the paper, as that is entirely derived
from the actual trace and is only present for efficiency (which we do not plan to reason about)

TODO: figure out the best way to encode the two errors (currently we encode `err` as the failure of
OracleComp, and `none` as `Option.none` inside) -/
def backTrack (trace : QueryLog (duplexSpongeChallengeOracle StmtIn U))
    (state : CanonicalSpongeState U) :
    OptionT Option ((StmtIn × (i : Fin (n + 1)) × (pSpec.MessagesUpTo i))) :=
  sorry

end DuplexSpongeFS
