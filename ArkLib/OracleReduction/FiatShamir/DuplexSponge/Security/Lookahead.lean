/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs

/-!
# Lookahead sequence family and procedure

This file contains the lookahead sequence family and procedure for the analysis of duplex sponge
Fiat-Shamir, following Section 5.3 in the paper.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS

variable {StmtIn : Type}
  {n : ℕ} {pSpec : ProtocolSpec n}
  {U : Type} [SpongeUnit U] [SpongeSize]
  [HasChallengeSize pSpec]

/-- A look-ahead sequence (Equation 14) of a given trace of forward permutation queries, and an
  initial state, consists of:
- A list of input states
- A list of output states

subject to the following conditions:
- The two list of states have the same length
- The first input state is the given initial state
  ...

TODO: refactor this to cut down on data (can just omit output states?) -/
structure LookaheadSequence (trace : QueryLog (forwardPermutationOracle (CanonicalSpongeState U)))
    (state : CanonicalSpongeState U) where
  /-- The list of input states in a look-ahead sequence -/
  inputState : List (CanonicalSpongeState U)
  /-- The list of output states in a look-ahead sequence -/
  outputState : List (CanonicalSpongeState U)

  /-- The two list of states have the same length -/
  inputState_length_eq_outputState_length : inputState.length = outputState.length

  /-- The first input state is the given initial state -/
  first_inputState_eq_state : inputState[0]? = state

  /-- For all `i < inputState.length`, the query-answer pair `(inputState[i], outputState[i])` is in
    the trace -/
  inputOutput_in_trace : ∀ i : Fin inputState.length,
    (inputState[i], outputState[i]) ∈ trace.getQ ()

  /-- For all `i < outputState.length`, the output state is the next input state -/
  outputState_eq_next_inputState : ∀ i : Fin (outputState.length - 1),
    outputState[i] = inputState[i.val + 1]

  /-- For all `i < inputState.length`, the capacity segment of `inputState[i]` is not the same as
    the capacity segment of `outputState[i]` -/
  capacitySegment_inputState_ne_outputState : ∀ i : Fin inputState.length,
    inputState[i].capacitySegment ≠ outputState[i].capacitySegment

/-- A family of look-ahead sequences (Equation 14), parametrized by a trace of forward permutation
  queries, an initial state, and a challenge round index `i`, is defined as a finite set of
  look-ahead sequences such that:
- no two sequences are strict subsets of each other
- the length of any sequence is at most the challenge size of the given challenge round `i` -/
structure LookaheadSequenceFamily
    (trace : QueryLog (forwardPermutationOracle (CanonicalSpongeState U)))
    (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) where
  /-- The family of look-ahead sequences, defined as a finite set -/
  seqFamily : Finset (LookaheadSequence trace state)
  /-- Maximality condition: no strict containment between two sequences, defined in terms of
    - the input states are not a strict subset of each other, or
    - the output states are not a strict subset of each other -/
  maximality : ∀ s ∈ seqFamily, ∀ s' ∈ seqFamily,
    ¬ (s.inputState ⊆ s'.inputState) ∨ ¬ (s'.outputState ⊆ s.outputState)
  /-- The length of any sequence is at most the challenge size of the given challenge round `i` -/
  length_le_challengeSize : ∀ s ∈ seqFamily, s.inputState.length ≤ challengeSize i

/-- The lookahead procedure in Section 5.2, which takes in:
- A query-answer trace for the oracle `h`
- A permutation state (vector of `N` units)
- A round index `i` for a challenge round

And returns (with potential failure):
- An encoded verifier's challenge (vector of `chalSize i` units)
-/
def lookAhead (hashTrace : QueryLog (StmtIn →ₒ Vector U SpongeSize.C))
    (state : CanonicalSpongeState U) (i : pSpec.ChallengeIdx) :
    Option (Vector U (challengeSize i)) :=
  sorry

end DuplexSpongeFS
