/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.BacktrackSchedule

/-!
# Scope convention for the revised Section 5 reduction

The revised paper restricts only its Section 5 reduction to protocols in which every encoded
prover message and verifier challenge has positive length.  The underlying FS and DSFS
constructions remain general.  This file records that paper-level scope once, as a protocol
property, so schedule-sensitive theorems do not reintroduce empty-action cases locally.
-/

namespace DuplexSpongeFS

open ProtocolSpec

/-- The nonempty-round convention of the revised Section 5 paper.

`ProtocolSpec` represents a transcript as direction-labelled actions rather than bundled
prover/verifier pairs.  Thus the faithful internal formulation requires every present message
and every present challenge action to have positive encoded length, and requires that both kinds
of action occur.  It is deliberately a `Prop` class: it scopes the Section 5 reduction but does
not alter either Fiat--Shamir construction. -/
class Section5Nonempty {n : ℕ} (pSpec : ProtocolSpec n)
    [HasMessageSize pSpec] [HasChallengeSize pSpec] : Prop where
  message_actions : Nonempty pSpec.MessageIdx
  challenge_actions : Nonempty pSpec.ChallengeIdx
  message_size_pos : ∀ i : pSpec.MessageIdx, 0 < messageSize i
  challenge_size_pos : ∀ i : pSpec.ChallengeIdx, 0 < challengeSize i

/-- The round discipline implicit in CO25's notation
`A(ℓ_P(1)); S(ℓ_V(1)); …; A(ℓ_P(k)); S(ℓ_V(k))`.

`ProtocolSpec` intentionally permits arbitrary direction-labelled action streams, whereas the
paper's Section 5 parser and marker arguments are for a public-coin protocol with one prover
action followed by one verifier action in every round.  This class records exactly that embedding
at the formalization boundary.  It is not an additional cryptographic hypothesis and does not
modify the general FS or DSFS constructions: it only identifies their general action stream with
the paper's already-assumed round schedule. -/
class Section5RoundStructure {n : ℕ} (roundCount : ℕ) (pSpec : ProtocolSpec n) : Prop where
  actionCount : n = 2 * roundCount
  prover_action : ∀ i : Fin roundCount,
    pSpec.dir ⟨2 * i.1, by
      rw [actionCount]
      omega⟩ = .P_to_V
  verifier_action : ∀ i : Fin roundCount,
    pSpec.dir ⟨2 * i.1 + 1, by
      rw [actionCount]
      omega⟩ = .V_to_P

namespace Section5Nonempty

variable {n : ℕ} {pSpec : ProtocolSpec n} {U : Type}
  [HasMessageSize pSpec] [HasChallengeSize pSpec] [Section5Nonempty pSpec]

/-- The Section 5 convention supplies the positive encoded length of each verifier action. -/
lemma challenge_pos (i : pSpec.ChallengeIdx) : 0 < challengeSize i :=
  Section5Nonempty.challenge_size_pos i

/-- Every verifier action in the Section 5 scope occupies at least one padded rate block.
This is the small bridge from the paper's no-empty-challenge convention to the executable
`d2sRateBlocksFromChallenge` parser: the parser's `[]` branch is unreachable for a certified
verifier challenge. -/
lemma challenge_block_count_pos [SpongeSize] (i : pSpec.ChallengeIdx) :
    0 < pSpec.Lᵥᵢ i := by
  unfold ProtocolSpec.Lᵥᵢ ProtocolSpec.numPermQueriesChallenge
  apply Nat.ceil_pos.mpr
  exact div_pos
    (by exact_mod_cast challenge_pos i)
    (by exact_mod_cast SpongeSize.R_pos)

/-- A vector of the rate blocks output by the verifier-challenge parser cannot be empty in the
Section 5 scope.  Keeping this as a vector fact makes it directly usable after an adaptive
`d2sRateBlocksFromChallenge` call has produced its concrete blocks. -/
lemma challenge_rateBlocks_toList_ne_nil [SpongeSize] (i : pSpec.ChallengeIdx)
    (blocks : Vector (Vector U SpongeSize.R) (pSpec.Lᵥᵢ i)) : blocks.toList ≠ [] := by
  apply List.ne_nil_of_length_pos
  simpa only [Vector.length_toList] using challenge_block_count_pos (pSpec := pSpec) i

/-- The revised Section 5 scope gives a genuinely positive exact verifier permutation count.
This derives `N_𝒱 ≥ 1` from an actual positive-length challenge phase by the stateful schedule;
it is not an inference from a rounded per-round block budget. -/
lemma verifierPermCallCount_pos [SpongeSize] (δ : ℕ) :
    0 < verifierPermCallCount (pSpec := pSpec) (δ := δ) := by
  obtain ⟨i⟩ := Section5Nonempty.challenge_actions (pSpec := pSpec)
  change 0 <
    (Backtrack.ScheduleCursor.schedulePhases SpongeSize.R
      (Backtrack.ScheduleCursor.absorbWithLocations SpongeSize.R ⟨0, 0, SpongeSize.R⟩ δ).2
      (protocolPhases pSpec)).2.queryIndex
  rw [Backtrack.ScheduleCursor.absorbWithLocations_cursor]
  apply Backtrack.ScheduleCursor.schedulePhases_queryIndex_pos_of_mem_nonempty_squeeze
    SpongeSize.R
    (Backtrack.ScheduleCursor.absorb SpongeSize.R ⟨0, 0, SpongeSize.R⟩ δ)
  · right
    exact Backtrack.ScheduleCursor.absorb_squeezeOffset SpongeSize.R ⟨0, 0, SpongeSize.R⟩ δ
  · refine ⟨challengeSize i, ?_, challenge_pos i⟩
    apply List.mem_ofFn.mpr
    refine ⟨i.1, ?_⟩
    unfold phaseOf
    split
    · rename_i hdir
      have : False := by simpa [hdir] using i.2
      exact False.elim this
    · rfl

end Section5Nonempty

namespace Section5RoundStructure

variable {n roundCount : ℕ} {pSpec : ProtocolSpec n}
  [Section5RoundStructure roundCount pSpec]

/-- The paper's action index of the prover message in round `i`. -/
def proverAction (i : Fin roundCount) : Fin n :=
  ⟨2 * i.1, by
    calc
      2 * i.1 < 2 * roundCount := by omega
      _ = n := (Section5RoundStructure.actionCount (roundCount := roundCount)
        (pSpec := pSpec)).symm⟩

/-- The paper's action index of the verifier challenge in round `i`. -/
def verifierAction (i : Fin roundCount) : Fin n :=
  ⟨2 * i.1 + 1, by
    calc
      2 * i.1 + 1 < 2 * roundCount := by omega
      _ = n := (Section5RoundStructure.actionCount (roundCount := roundCount)
        (pSpec := pSpec)).symm⟩

/-- Round `i` starts with its prover action. -/
@[simp]
lemma proverAction_dir (i : Fin roundCount) :
    pSpec.dir (proverAction (pSpec := pSpec) i) = .P_to_V :=
  Section5RoundStructure.prover_action i

/-- Round `i` ends with its verifier action. -/
@[simp]
lemma verifierAction_dir (i : Fin roundCount) :
    pSpec.dir (verifierAction (pSpec := pSpec) i) = .V_to_P :=
  Section5RoundStructure.verifier_action i

end Section5RoundStructure

end DuplexSpongeFS
