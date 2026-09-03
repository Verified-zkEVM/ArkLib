/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michele Orrù, Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs

/-!
# Nondegenerate rounds for duplex-sponge Fiat–Shamir

CO25 models each round as a nonempty prover-message absorb followed by a nonempty
verifier-challenge squeeze. Its Section-5 proof therefore uses the paired schedule
`A(ℓ_P(1)), S(ℓ_V(1)), …, A(ℓ_P(k)), S(ℓ_V(k))` without restating these conditions
at every claim. ArkLib's generic `ProtocolSpec` permits arbitrary directions and zero-length
actions, so the assumptions implicit in the paper's model must be explicit in Lean.

Without them, zero-length actions disappear from the sponge execution, consecutive challenges
share one squeeze stream, and consecutive messages are not all reconstructed by BackTrack.
The salt length remains unrestricted, including `δ = 0`.
-/

namespace DuplexSpongeFS

open ProtocolSpec

variable {n : ℕ}

/-- The nonempty, strictly alternating message/challenge schedule implicitly used by CO25
Section 5, with every action having positive encoded length. -/
structure NondegenerateRounds (pSpec : ProtocolSpec n) [HasMessageSize pSpec]
    [HasChallengeSize pSpec] : Prop where
  /-- The schedule begins with a prover message. -/
  startsWithMessage : ∃ i : pSpec.MessageIdx, (i.1 : ℕ) = 0
  /-- The schedule ends with a verifier challenge. -/
  endsWithChallenge : ∃ i : pSpec.ChallengeIdx, (i.1 : ℕ) + 1 = n
  /-- Every encoded prover message is nonempty. -/
  messagePos : ∀ i : pSpec.MessageIdx, 0 < messageSize i
  /-- Every encoded verifier challenge is nonempty. -/
  challengePos : ∀ i : pSpec.ChallengeIdx, 0 < challengeSize i
  /-- No two verifier challenges are adjacent. -/
  noAdjacentChallenges : ∀ i j : Fin n, pSpec.dir i = .V_to_P → pSpec.dir j = .V_to_P →
    (j : ℕ) + 1 = (i : ℕ) → False
  /-- No two prover messages are adjacent. -/
  noAdjacentMessages : ∀ i j : Fin n, pSpec.dir i = .P_to_V → pSpec.dir j = .P_to_V →
    (j : ℕ) + 1 = (i : ℕ) → False

namespace NondegenerateRounds

variable {pSpec : ProtocolSpec n} [HasMessageSize pSpec] [HasChallengeSize pSpec]

/-- A nondegenerate schedule contains a verifier challenge. -/
lemma exists_challenge (h : NondegenerateRounds pSpec) : Nonempty pSpec.ChallengeIdx :=
  ⟨h.endsWithChallenge.choose⟩

/-- A nondegenerate schedule contains a prover message. -/
lemma exists_message (h : NondegenerateRounds pSpec) : Nonempty pSpec.MessageIdx :=
  ⟨h.startsWithMessage.choose⟩

/-- Every challenge is immediately preceded by a prover message. -/
lemma dir_pred_eq_P_to_V (h : NondegenerateRounds pSpec) {i : Fin n}
    (hi : pSpec.dir i = .V_to_P) {k : ℕ} (hk : (i : ℕ) = k + 1) (hkn : k < n) :
    pSpec.dir ⟨k, hkn⟩ = .P_to_V := by
  cases hdir : pSpec.dir ⟨k, hkn⟩ with
  | P_to_V => rfl
  | V_to_P => exact (h.noAdjacentChallenges i ⟨k, hkn⟩ hi hdir hk.symm).elim

/-- A prover-message length is nonzero. -/
lemma messageSize_ne_zero (h : NondegenerateRounds pSpec) (i : pSpec.MessageIdx) :
    messageSize i ≠ 0 := (h.messagePos i).ne'

/-- A verifier-challenge length is nonzero. -/
lemma challengeSize_ne_zero (h : NondegenerateRounds pSpec) (i : pSpec.ChallengeIdx) :
    challengeSize i ≠ 0 := (h.challengePos i).ne'

/-- A nondegenerate schedule performs at least one protocol permutation query. -/
lemma totalNumPermQueries_pos {U : Type} [SpongeUnit U] [SpongeSize]
    [∀ i, Serialize (pSpec.Message i) (Vector U (messageSize i))]
    [∀ i, Deserialize (pSpec.Challenge i) (Vector U (challengeSize i))]
    (h : NondegenerateRounds pSpec) :
    0 < pSpec.totalNumPermQueries := by
  have hchallenge : ∀ i : pSpec.ChallengeIdx, 0 < pSpec.numPermQueriesChallenge i := by
    intro i
    unfold ProtocolSpec.numPermQueriesChallenge
    apply Nat.ceil_pos.mpr
    apply div_pos
    · exact_mod_cast h.challengePos i
    · exact_mod_cast SpongeSize.R_pos
  have hsum : 0 < pSpec.totalNumPermQueriesChallenge := by
    let _ : Nonempty pSpec.ChallengeIdx := h.exists_challenge
    unfold ProtocolSpec.totalNumPermQueriesChallenge
    exact Finset.sum_pos (fun i _ => hchallenge i) Finset.univ_nonempty
  unfold ProtocolSpec.totalNumPermQueries
  exact Nat.lt_of_lt_of_le hsum (Nat.le_add_left _ _)

end NondegenerateRounds

end DuplexSpongeFS
