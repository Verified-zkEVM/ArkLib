/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Core.Protocol
public import ArkLib.OracleReduction.ProtocolSpec.Basic

/-!
# Legacy protocol specifications as protocol trees

A legacy `ProtocolSpec n` lists `n` rounds, each with a direction and a payload type. This file
turns it into a tree of the interaction layer with one node per round, in order. A prover message
becomes a plain message node and a verifier challenge becomes a challenge node. In the oracle
tree, a prover message becomes an oracle payload node that carries the legacy query interface.

The continuation at every node ignores the branch, so the tree does not branch on message
values. A runtime path through the tree therefore records exactly one payload per round, and
`transcriptEquiv` identifies it with the legacy full transcript. The equivalence covers the
empty protocol and any sequence of directions, including consecutive rounds of the same owner.

Every construction is by recursion on the number of remaining rounds, starting at an offset
`k`, so that each tree, path and transcript computes definitionally.
-/

@[expose] public section

namespace Interaction.Core.Legacy
open PFunctor FreeM TwoParty.Lens ProtocolSpec

variable {n : ℕ}

/-! ### Generic round chains -/

/-- The chain of rounds `k, k + 1, …, n - 1`, where `h` records that `m` rounds remain. The node
for round `j` sits at position `pos j`, and its continuation ignores the branch. -/
def chain {P : PFunctor.{1, 0}} (pos : Fin n → P.A) :
    (k m : ℕ) → k + m = n → FreeM P PUnit.{1}
  | _, 0, _ => .pure ⟨⟩
  | k, m + 1, h => .liftBind (pos ⟨k, by omega⟩) (fun _ => chain pos (k + 1) m (by omega))

@[simp] theorem chain_zero {P : PFunctor.{1, 0}} (pos : Fin n → P.A) (k : ℕ) (h : k + 0 = n) :
    chain pos k 0 h = .pure ⟨⟩ := rfl

theorem chain_succ {P : PFunctor.{1, 0}} (pos : Fin n → P.A) (k m : ℕ) (h : k + (m + 1) = n) :
    chain pos k (m + 1) h =
      .liftBind (pos ⟨k, by omega⟩) (fun _ => chain pos (k + 1) m (by omega)) := rfl

section Decode

variable {pSpec : ProtocolSpec n} {P : PFunctor.{1, 0}} (l : PFunctor.Lens P rolePoly.{0})
  (pos : Fin n → P.A) (e : (j : Fin n) → Move l (pos j) ≃ pSpec.«Type» j)

/-- Read a legacy transcript off a runtime path, extending the transcript `pre` of the rounds
before `k`. -/
def decodeFrom : (k m : ℕ) → (h : k + m = n) → Transcript ⟨k, by omega⟩ pSpec →
    PathAlong l (chain pos k m h) → FullTranscript pSpec
  | k, 0, h, pre, _ => fun i => pre ⟨i.val, show i.val < k by omega⟩
  | k, m + 1, h, pre, ⟨d, rest⟩ =>
    decodeFrom (k + 1) m (by omega)
      (Transcript.concat (m := ⟨k, by omega⟩) (e ⟨k, by omega⟩ d) pre) rest

/-- Write the rounds `k, …, n - 1` of a legacy transcript as a runtime path. -/
def encodeFrom (tr : FullTranscript pSpec) :
    (k m : ℕ) → (h : k + m = n) → PathAlong l (chain pos k m h)
  | _, 0, _ => ⟨⟩
  | k, m + 1, h => ⟨(e ⟨k, by omega⟩).symm (tr ⟨k, by omega⟩), encodeFrom tr (k + 1) m (by omega)⟩

/-- Decoding keeps the rounds that were already in the prefix. -/
theorem decodeFrom_lt : (k m : ℕ) → (h : k + m = n) → (pre : Transcript ⟨k, by omega⟩ pSpec) →
    (p : PathAlong l (chain pos k m h)) → (i : Fin n) → (hi : i.val < k) →
    decodeFrom l pos e k m h pre p i = pre ⟨i.val, hi⟩
  | _, 0, _, _, _, _, _ => rfl
  | k, m + 1, h, pre, ⟨d, rest⟩, i, hi => by
    refine (decodeFrom_lt (k + 1) m (by omega) _ rest i (by omega)).trans ?_
    exact eq_of_heq (Transcript.concat_apply_lt (m := ⟨k, by omega⟩) pre _ i.val hi _)

/-- Decoding an encoded transcript recovers it, given a prefix that agrees with it. -/
theorem decodeFrom_encodeFrom (tr : FullTranscript pSpec) : (k m : ℕ) → (h : k + m = n) →
    (pre : Transcript ⟨k, by omega⟩ pSpec) →
    (∀ (i : Fin n) (hi : i.val < k), pre ⟨i.val, hi⟩ = tr i) →
    decodeFrom l pos e k m h pre (encodeFrom l pos e tr k m h) = tr
  | _, 0, _, _, hpre => funext fun i => hpre i (by omega)
  | k, m + 1, h, pre, hpre => by
    refine decodeFrom_encodeFrom tr (k + 1) m (by omega) _ fun i hi => ?_
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
    · exact (eq_of_heq (Transcript.concat_apply_lt (m := ⟨k, by omega⟩) pre _ i.val hlt _)).trans
        (hpre i hlt)
    · obtain ⟨i, hi'⟩ := i
      simp only at heq
      subst heq
      exact eq_of_heq ((Transcript.concat_apply_last (m := ⟨i, by omega⟩) pre _ i rfl _).trans
        (heq_of_eq ((e _).apply_symm_apply _)))

/-- Encoding a decoded path recovers it. -/
theorem encodeFrom_decodeFrom : (k m : ℕ) → (h : k + m = n) →
    (pre : Transcript ⟨k, by omega⟩ pSpec) → (p : PathAlong l (chain pos k m h)) →
    encodeFrom l pos e (decodeFrom l pos e k m h pre p) k m h = p
  | _, 0, _, _, _ => rfl
  | k, m + 1, h, pre, ⟨d, rest⟩ => by
    have hrest := encodeFrom_decodeFrom (k + 1) m (by omega)
      (Transcript.concat (m := ⟨k, by omega⟩) (e ⟨k, by omega⟩ d) pre) rest
    have hhead : decodeFrom l pos e (k + 1) m (by omega)
        (Transcript.concat (m := ⟨k, by omega⟩) (e ⟨k, by omega⟩ d) pre) rest ⟨k, by omega⟩ =
          e ⟨k, by omega⟩ d := by
      rw [decodeFrom_lt l pos e (k + 1) m (by omega) _ rest ⟨k, by omega⟩ (by simp)]
      exact eq_of_heq (Transcript.concat_apply_last (m := ⟨k, by omega⟩) pre _ k rfl _)
    simp only [encodeFrom, decodeFrom] at hrest ⊢
    rw [hrest, hhead, Equiv.symm_apply_apply]

/-- Runtime paths through the whole chain are legacy full transcripts. -/
def chainEquiv : PathAlong l (chain pos 0 n (Nat.zero_add n)) ≃ FullTranscript pSpec where
  toFun := decodeFrom l pos e 0 n _ default
  invFun tr := encodeFrom l pos e tr 0 n _
  left_inv p := encodeFrom_decodeFrom l pos e 0 n _ default p
  right_inv tr := decodeFrom_encodeFrom l pos e tr 0 n _ default fun _ hi => absurd hi (by omega)

end Decode

/-! ### Plain trees -/

/-- The plain position of a round with direction `d` and payload type `T`. -/
def plainPos : Direction → Type → PlainPos.{0}
  | .P_to_V, T => .message T
  | .V_to_P, T => .challenge T

/-- A plain round's runtime move is its legacy payload. -/
def plainMoveEquiv : (d : Direction) → (T : Type) → Move plainSig (plainPos d T) ≃ T
  | .P_to_V, T => Equiv.refl T
  | .V_to_P, T => Equiv.refl T

@[simp] theorem owner_plainPos_P_to_V (T : Type) :
    owner plainSig (plainPos .P_to_V T) = .sender := rfl

@[simp] theorem owner_plainPos_V_to_P (T : Type) :
    owner plainSig (plainPos .V_to_P T) = .receiver := rfl

/-- The plain position of round `j`. -/
abbrev plainRound (pSpec : ProtocolSpec n) (j : Fin n) : PlainPos.{0} :=
  plainPos (pSpec.dir j) (pSpec.«Type» j)

/-- The legacy protocol from round `k` onwards, as a plain tree. -/
abbrev suffix (pSpec : ProtocolSpec n) (k m : ℕ) (h : k + m = n) : Protocol.{0} :=
  chain (plainRound pSpec) k m h

/-- The legacy protocol as a plain tree. -/
abbrev protocol (pSpec : ProtocolSpec n) : Protocol.{0} := suffix pSpec 0 n (Nat.zero_add n)

/-- Read the legacy transcript off a plain runtime path, after the prefix `pre`. -/
abbrev decodePlainFrom (pSpec : ProtocolSpec n) (k m : ℕ) (h : k + m = n)
    (pre : Transcript ⟨k, by omega⟩ pSpec) (p : PathAlong plainSig (suffix pSpec k m h)) :
    FullTranscript pSpec :=
  decodeFrom plainSig (plainRound pSpec) (fun _ => plainMoveEquiv _ _) k m h pre p

/-- Legacy full transcripts are the runtime paths of the plain tree. -/
def transcriptEquiv (pSpec : ProtocolSpec n) :
    PathAlong plainSig (protocol pSpec) ≃ FullTranscript pSpec :=
  chainEquiv plainSig (plainRound pSpec) (fun _ => plainMoveEquiv _ _)

/-- Read the legacy full transcript off a completed plain run. -/
abbrev decode (pSpec : ProtocolSpec n) (tr : PathAlong plainSig (protocol pSpec)) :
    FullTranscript pSpec :=
  transcriptEquiv pSpec tr

theorem decode_eq (pSpec : ProtocolSpec n) (tr : PathAlong plainSig (protocol pSpec)) :
    decode pSpec tr = decodePlainFrom pSpec 0 n _ default tr := rfl

/-! ### Oracle trees -/

/-- The oracle position of round `j`, given its direction `d`. Prover messages become oracle
payloads with their legacy query interface. -/
def oraclePos (pSpec : ProtocolSpec n) [Oₘ : ∀ i, OracleInterface.{0, 0} (pSpec.Message i)]
    (j : Fin n) : (d : Direction) → pSpec.dir j = d → OraclePos.{0}
  | .P_to_V, h => .oracle (pSpec.«Type» j) (Oₘ ⟨j, h⟩)
  | .V_to_P, _ => .challenge (pSpec.«Type» j)

/-- An oracle round's runtime move is its legacy payload. -/
def oracleMoveEquiv (pSpec : ProtocolSpec n) [∀ i, OracleInterface.{0, 0} (pSpec.Message i)]
    (j : Fin n) : (d : Direction) → (h : pSpec.dir j = d) →
    Move oracleSig (oraclePos pSpec j d h) ≃ pSpec.«Type» j
  | .P_to_V, _ => Equiv.refl _
  | .V_to_P, _ => Equiv.refl _

/-- The oracle position of round `j`. -/
abbrev oracleRound (pSpec : ProtocolSpec n) [∀ i, OracleInterface.{0, 0} (pSpec.Message i)]
    (j : Fin n) : OraclePos.{0} :=
  oraclePos pSpec j (pSpec.dir j) rfl

/-- The legacy protocol from round `k` onwards, as an oracle tree. -/
abbrev oracleSuffix (pSpec : ProtocolSpec n) [∀ i, OracleInterface.{0, 0} (pSpec.Message i)]
    (k m : ℕ) (h : k + m = n) : OracleProtocol.{0} :=
  chain (oracleRound pSpec) k m h

/-- The legacy protocol as an oracle tree. -/
abbrev oracleProtocol (pSpec : ProtocolSpec n) [∀ i, OracleInterface.{0, 0} (pSpec.Message i)] :
    OracleProtocol.{0} :=
  oracleSuffix pSpec 0 n (Nat.zero_add n)

/-- Legacy full transcripts are the runtime paths of the oracle tree. -/
def oracleTranscriptEquiv (pSpec : ProtocolSpec n)
    [∀ i, OracleInterface.{0, 0} (pSpec.Message i)] :
    PathAlong oracleSig (oracleProtocol pSpec) ≃ FullTranscript pSpec :=
  chainEquiv oracleSig (oracleRound pSpec) (fun j => oracleMoveEquiv pSpec j _ rfl)

/-- Read the legacy full transcript off a completed oracle run. -/
abbrev oracleDecode (pSpec : ProtocolSpec n) [∀ i, OracleInterface.{0, 0} (pSpec.Message i)]
    (tr : PathAlong oracleSig (oracleProtocol pSpec)) : FullTranscript pSpec :=
  oracleTranscriptEquiv pSpec tr

end Interaction.Core.Legacy
