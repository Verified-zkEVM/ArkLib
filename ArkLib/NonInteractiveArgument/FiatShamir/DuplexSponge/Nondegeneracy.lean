/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.NonInteractiveArgument.FiatShamir.DuplexSponge.Defs

/-!
# Nondegenerate rounds for duplex-sponge Fiat–Shamir

CO25 models each round as a nonempty prover-message absorb followed by a nonempty
verifier message squeeze. Its Section-5 proof therefore uses the paired schedule
`A(ℓ_P(1)), S(ℓ_V(1)), …, A(ℓ_P(k)), S(ℓ_V(k))` without restating these conditions
at every claim. ArkLib's generic `ProtocolSpec` permits arbitrary directions and zero-length
actions. The security proofs admit either party at either endpoint; they require at least one
prover message and at least one verifier message.

Without them, zero-length actions disappear from the sponge execution, consecutive verifier messages
share one squeeze stream, and consecutive prover messages are not all reconstructed by BackTrack.
The salt length remains unrestricted, including `δ = 0`.
-/

@[expose] public section

namespace DuplexSpongeFS

open ProtocolSpec

variable {n : ℕ}

/-- A strictly alternating schedule containing both parties and having positive encoded lengths.
Either party may send the first or last message: `P…V`, `P…P`, `V…V`, and `V…P` are allowed,
where `P` denotes a prover message and `V` a verifier message. The ellipsis denotes an
alternating interior; both parties must occur even when the endpoints coincide. -/
structure NondegenerateRounds (pSpec : ProtocolSpec n) [HasProverMessageSize pSpec]
    [HasVerifierMessageSize pSpec] : Prop where
  /-- The schedule contains at least one prover message. -/
  hasProverMessage : Nonempty pSpec.MessageIdx
  /-- The schedule contains at least one verifier message. -/
  hasVerifierMessage : Nonempty pSpec.ChallengeIdx
  /-- Every encoded prover message is nonempty. -/
  proverMessagePos : ∀ i : pSpec.MessageIdx, 0 < proverMessageSize i
  /-- Every encoded verifier message is nonempty. -/
  verifierMessagePos : ∀ i : pSpec.ChallengeIdx, 0 < verifierMessageSize i
  /-- No two verifier messages are adjacent. -/
  noAdjacentVerifierMessages : ∀ i j : Fin n, pSpec.dir i = .V_to_P → pSpec.dir j = .V_to_P →
    (j : ℕ) + 1 = (i : ℕ) → False
  /-- No two prover messages are adjacent. -/
  noAdjacentProverMessages : ∀ i j : Fin n, pSpec.dir i = .P_to_V → pSpec.dir j = .P_to_V →
    (j : ℕ) + 1 = (i : ℕ) → False

namespace NondegenerateRounds

variable {pSpec : ProtocolSpec n} [HasProverMessageSize pSpec] [HasVerifierMessageSize pSpec]

/-- A nondegenerate schedule contains a verifier message. -/
lemma exists_verifierMessage (h : NondegenerateRounds pSpec) : Nonempty pSpec.ChallengeIdx :=
  h.hasVerifierMessage

/-- A nondegenerate schedule contains a prover message. -/
lemma exists_proverMessage (h : NondegenerateRounds pSpec) : Nonempty pSpec.MessageIdx :=
  h.hasProverMessage

/-- Every noninitial verifier message is immediately preceded by a prover message. -/
lemma dir_pred_eq_P_to_V (h : NondegenerateRounds pSpec) {i : Fin n}
    (hi : pSpec.dir i = .V_to_P) {k : ℕ} (hk : (i : ℕ) = k + 1) (hkn : k < n) :
    pSpec.dir ⟨k, hkn⟩ = .P_to_V := by
  cases hdir : pSpec.dir ⟨k, hkn⟩ with
  | P_to_V => rfl
  | V_to_P => exact (h.noAdjacentVerifierMessages i ⟨k, hkn⟩ hi hdir hk.symm).elim

/-- A prover-message length is nonzero. -/
lemma proverMessageSize_ne_zero (h : NondegenerateRounds pSpec) (i : pSpec.MessageIdx) :
    proverMessageSize i ≠ 0 := (h.proverMessagePos i).ne'

/-- A verifier message length is nonzero. -/
lemma verifierMessageSize_ne_zero (h : NondegenerateRounds pSpec) (i : pSpec.ChallengeIdx) :
    verifierMessageSize i ≠ 0 := (h.verifierMessagePos i).ne'

end NondegenerateRounds

end DuplexSpongeFS
