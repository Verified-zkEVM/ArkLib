/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Fin.TakeDrop
import ArkLib.OracleReduction.Prelude
import ArkLib.OracleReduction.OracleInterface
import ArkLib.ToVCVio.Oracle

/-!
# Protocol Specifications for (Oracle) Reductions

This file defines the `ProtocolSpec` type, which is used to specify the protocol between the prover
and the verifier.
-/

universe u v

open OracleComp OracleSpec

/-- Type signature for an interactive protocol, with `n` messages exchanged. -/
@[reducible]
def ProtocolSpec (n : ℕ) := Fin n → Direction × Type

variable {n : ℕ}

namespace ProtocolSpec

@[simp]
abbrev getDir (pSpec : ProtocolSpec n) (i : Fin n) := pSpec i |>.1

@[simp]
abbrev getType (pSpec : ProtocolSpec n) (i : Fin n) := pSpec i |>.2

/-- Subtype of `Fin n` for the indices corresponding to messages in a protocol specification -/
@[reducible, simp]
def MessageIdx (pSpec : ProtocolSpec n) :=
  {i : Fin n // (pSpec i).1 = Direction.P_to_V}

/-- Subtype of `Fin n` for the indices corresponding to challenges in a protocol specification -/
@[reducible, simp]
def ChallengeIdx (pSpec : ProtocolSpec n) :=
  {i : Fin n // (pSpec i).1 = Direction.V_to_P}

/-- Subtype of `Fin k` for the indices corresponding to messages in a protocol specification up to
  round `k` -/
@[reducible, simp]
def MessageIdxUpTo (k : Fin (n + 1)) (pSpec : ProtocolSpec n) :=
  {i : Fin k // (pSpec <| i.castLE (by omega)).1 = Direction.P_to_V}

/-- Subtype of `Fin k` for the indices corresponding to challenges in a protocol specification up to
  round `k` -/
@[reducible, simp]
def ChallengeIdxUpTo (k : Fin (n + 1)) (pSpec : ProtocolSpec n) :=
  {i : Fin k // (pSpec <| i.castLE (by omega)).1 = Direction.V_to_P}

instance {pSpec : ProtocolSpec n} : CoeHead (MessageIdx pSpec) (Fin n) where
  coe := fun i => i.1
instance {pSpec : ProtocolSpec n} : CoeHead (ChallengeIdx pSpec) (Fin n) where
  coe := fun i => i.1

/-- The type of the `i`-th message in a protocol specification.

This does not distinguish between messages received in full or as an oracle. -/
@[reducible, inline, specialize, simp]
def Message (pSpec : ProtocolSpec n) (i : MessageIdx pSpec) := (pSpec i.val).2

/-- The type of the `i`-th challenge in a protocol specification -/
@[reducible, inline, specialize, simp]
def Challenge (pSpec : ProtocolSpec n) (i : ChallengeIdx pSpec) := (pSpec i.val).2

/-- The type of all messages in a protocol specification. Uncurried version of `Message`. -/
@[reducible, inline, specialize]
def Messages (pSpec : ProtocolSpec n) : Type := ∀ i, pSpec.Message i

/-- The type of all challenges in a protocol specification -/
@[reducible, inline, specialize]
def Challenges (pSpec : ProtocolSpec n) : Type := ∀ i, pSpec.Challenge i

/-- The indexed family of messages from the prover up to round `k`.

Note that by definition, `MessagesUpTo (Fin.last n)` is definitionally equal to `Messages`. -/
@[reducible, inline, specialize]
def MessagesUpTo (k : Fin (n + 1)) (pSpec : ProtocolSpec n) :=
  (i : pSpec.MessageIdxUpTo k) → pSpec.Message ⟨i.val.castLE (by omega), i.property⟩

/-- The indexed family of challenges from the verifier up to round `k`.

Note that by definition, `ChallengesUpTo (Fin.last n)` is definitionally equal to `Challenges`. -/
@[reducible, inline, specialize]
def ChallengesUpTo (k : Fin (n + 1)) (pSpec : ProtocolSpec n) :=
  (i : pSpec.ChallengeIdxUpTo k) → pSpec.Challenge ⟨i.val.castLE (by omega), i.property⟩

section Instances

/-- There is only one protocol specification with 0 messages (the empty one) -/
instance : Unique (ProtocolSpec 0) := inferInstance

-- Two different ways to write the empty protocol specification: `![]` and `default`

instance : ∀ i, VCVCompatible (Challenge ![] i) := fun ⟨i, _⟩ => Fin.elim0 i
instance : ∀ i, SelectableType (Challenge ![] i) := fun ⟨i, _⟩ => Fin.elim0 i
instance : ∀ i, OracleInterface (Message ![] i) := fun ⟨i, _⟩ => Fin.elim0 i

instance : ∀ i, VCVCompatible ((default : ProtocolSpec 0).Challenge i) := fun ⟨i, _⟩ => Fin.elim0 i
instance : ∀ i, SelectableType ((default : ProtocolSpec 0).Challenge i) := fun ⟨i, _⟩ => Fin.elim0 i
instance : ∀ i, OracleInterface ((default : ProtocolSpec 0).Message i) := fun ⟨i, _⟩ => Fin.elim0 i

variable {Msg Chal : Type}

instance : IsEmpty (ChallengeIdx ![(.P_to_V, Msg)]) := by
  simp [ChallengeIdx]
  infer_instance
instance : Unique (MessageIdx ![(.P_to_V, Msg)]) where
  default := ⟨0, by simp⟩
  uniq := fun i => by ext; simp
instance [inst : OracleInterface Msg] : ∀ i, OracleInterface (Message ![(.P_to_V, Msg)] i)
  | ⟨0, _⟩ => inst
instance : ∀ i, VCVCompatible (Challenge ![(.P_to_V, Msg)] i)
  | ⟨0, h⟩ => nomatch h
instance : ∀ i, SelectableType (Challenge ![(.P_to_V, Msg)] i)
  | ⟨0, h⟩ => nomatch h

instance : IsEmpty (MessageIdx ![(.V_to_P, Chal)]) := by
  simp [MessageIdx]
  infer_instance
instance : Unique (ChallengeIdx ![(.V_to_P, Chal)]) where
  default := ⟨0, by simp⟩
  uniq := fun i => by ext; simp
instance : ∀ i, OracleInterface (Message ![(.V_to_P, Chal)] i)
  | ⟨0, h⟩ => nomatch h
instance [inst : VCVCompatible Chal] : ∀ i, VCVCompatible (Challenge ![(.V_to_P, Chal)] i)
  | ⟨0, _⟩ => inst
instance [inst : SelectableType Chal] : ∀ i, SelectableType (Challenge ![(.V_to_P, Chal)] i)
  | ⟨0, _⟩ => inst

variable {pSpec : ProtocolSpec n}

instance : Fintype (pSpec.MessageIdx) := Subtype.fintype (fun i => pSpec.getDir i = .P_to_V)
instance : Fintype (pSpec.ChallengeIdx) := Subtype.fintype (fun i => pSpec.getDir i = .V_to_P)
instance {k : Fin (n + 1)} : Fintype (pSpec.MessageIdxUpTo k) :=
  inferInstanceAs (Fintype <| MessageIdx (fun i => pSpec (i.castLE (by omega)) : ProtocolSpec k))
instance {k : Fin (n + 1)} : Fintype (pSpec.ChallengeIdxUpTo k) :=
  inferInstanceAs (Fintype <| ChallengeIdx (fun i => pSpec (i.castLE (by omega)) : ProtocolSpec k))

end Instances

variable {pSpec : ProtocolSpec n}

namespace MessagesUpTo

variable {k : Fin (n + 1)}

/-- For a tuple of messages up to round `k`, take the messages up to round `j : Fin (k + 1)` -/
def take (j : Fin (k + 1)) (messages : MessagesUpTo k pSpec) :
    MessagesUpTo (j.castLE (by omega)) pSpec :=
  fun i => messages ⟨i.val.castLE (by simp; omega), i.property⟩

end MessagesUpTo

namespace Messages

/-- Take the messages up to round `j : Fin (n + 1)` -/
def take (j : Fin (n + 1)) (messages : Messages pSpec) : MessagesUpTo j pSpec :=
  by exact (by exact messages : MessagesUpTo (Fin.last n) pSpec).take j

end Messages

namespace ChallengesUpTo

variable {k : Fin (n + 1)}

/-- For a tuple of challenges up to round `k`, take the challenges up to round `j : Fin (k + 1)` -/
def take (j : Fin (k + 1)) (challenges : ChallengesUpTo k pSpec) :
    ChallengesUpTo (j.castLE (by omega)) pSpec :=
  fun i => challenges ⟨i.val.castLE (by simp; omega), i.property⟩

end ChallengesUpTo

namespace Challenges

/-- Take the challenges up to round `j : Fin (n + 1)` -/
def take (j : Fin (n + 1)) (challenges : Challenges pSpec) : ChallengesUpTo j pSpec :=
  by exact (by exact challenges : ChallengesUpTo (Fin.last n) pSpec).take j

end Challenges

namespace MessagesUpTo

/-- There is only one transcript for the empty protocol,
  represented as `default : ProtocolSpec 0` -/
instance {k : Fin 1} : Unique (MessagesUpTo k (default : ProtocolSpec 0)) where
  default := fun i => ()
  uniq := by solve_by_elim

/-- There is only one transcript for the empty protocol, represented as `![]` -/
instance {k : Fin 1} : Unique (MessagesUpTo k ![]) where
  default := fun ⟨⟨i, h⟩, _⟩ => by
    have : k = 0 := Fin.fin_one_eq_zero k
    subst this; simp at h
  uniq := fun _ => by
    ext ⟨⟨i, h⟩, _⟩
    have : k = 0 := Fin.fin_one_eq_zero k
    subst this; simp at h

/-- There is only one transcript for any protocol specification with cutoff index 0 -/
instance : Unique (MessagesUpTo 0 pSpec) where
  default := fun ⟨i, _⟩ => Fin.elim0 i
  uniq := fun T => by ext ⟨i, _⟩; exact Fin.elim0 i

/-- Concatenate the `k`-th message to the end of the tuple of messages up to round `k`, assuming
  round `k` is a message round. -/
def concat {k : Fin n} (messages : MessagesUpTo k.castSucc pSpec)
    (h : (pSpec k).1 = .P_to_V) (msg : pSpec.Message ⟨k, h⟩) : MessagesUpTo k.succ pSpec :=
  fun i => if hi : i.1.1 < k then messages ⟨⟨i.1.1, hi⟩, i.property⟩ else
    (by simp [Fin.eq_last_of_not_lt hi]; exact msg)

/-- Extend the tuple of messages up to round `k` to up to round `k + 1`, assuming round `k` is a
  challenge round (so no message from the prover is sent). -/
def extend {k : Fin n} (messages : MessagesUpTo k.castSucc pSpec)
    (h : (pSpec k).1 = .V_to_P) : MessagesUpTo k.succ pSpec :=
  fun i => if hi : i.1.1 < k then messages ⟨⟨i.1.1, hi⟩, i.property⟩ else
    -- contradiction proof
    (by
      haveI := Fin.eq_last_of_not_lt hi
      haveI := i.property
      simp_all [Fin.castLE])

instance [∀ i, DecidableEq (pSpec.Message i)] {k : Fin (n + 1)} :
    DecidableEq (MessagesUpTo k pSpec) := by
  unfold MessagesUpTo
  infer_instance

end MessagesUpTo

namespace ChallengesUpTo

/-- There is only one transcript for the empty protocol,
  represented as `default : ProtocolSpec 0` -/
instance {k : Fin 1} : Unique (ChallengesUpTo k (default : ProtocolSpec 0)) where
  default := fun i => ()
  uniq := by solve_by_elim

/-- There is only one transcript for the empty protocol, represented as `![]` -/
instance {k : Fin 1} : Unique (ChallengesUpTo k ![]) where
  default := fun ⟨⟨i, h⟩, _⟩ => by
    have : k = 0 := Fin.fin_one_eq_zero k
    subst this; simp at h
  uniq := fun _ => by
    ext ⟨⟨i, h⟩, _⟩
    have : k = 0 := Fin.fin_one_eq_zero k
    subst this; simp at h

/-- There is only one transcript for any protocol specification with cutoff index 0 -/
instance : Unique (ChallengesUpTo 0 pSpec) where
  default := fun ⟨i, _⟩ => Fin.elim0 i
  uniq := fun T => by ext ⟨i, _⟩; exact Fin.elim0 i

/-- Concatenate the `k`-th challenge to the end of the tuple of challenges up to round `k`, assuming
  round `k` is a challenge round. -/
def concat {k : Fin n} (challenges : ChallengesUpTo k.castSucc pSpec)
    (h : (pSpec k).1 = .V_to_P) (chal : pSpec.Challenge ⟨k, h⟩) : ChallengesUpTo k.succ pSpec :=
  fun i => if hi : i.1.1 < k then challenges ⟨⟨i.1.1, hi⟩, i.property⟩ else
    (by simp [Fin.eq_last_of_not_lt hi]; exact chal)

/-- Extend the tuple of challenges up to round `k` to up to round `k + 1`, assuming round `k` is a
  message round (so no challenge from the verifier is sent). -/
def extend {k : Fin n} (challenges : ChallengesUpTo k.castSucc pSpec)
    (h : (pSpec k).1 = .P_to_V) : ChallengesUpTo k.succ pSpec :=
  fun i => if hi : i.1.1 < k then challenges ⟨⟨i.1.1, hi⟩, i.property⟩ else
    -- contradiction proof
    (by
      haveI := Fin.eq_last_of_not_lt hi
      haveI := i.property
      simp_all [Fin.castLE])

end ChallengesUpTo

/-- A (partial) transcript of a protocol specification, indexed by some `k : Fin (n + 1)`, is a
list of messages from the protocol for all indices `i` less than `k`.

Note that by definition, `Transcript (Fin.last n) pSpec` is definitionally equal to
`FullTranscript pSpec`. -/
@[reducible, inline, specialize]
def Transcript (k : Fin (n + 1)) (pSpec : ProtocolSpec n) :=
  (i : Fin k) → (pSpec (Fin.castLE (by omega) i)).2

/-- The full transcript of an interactive protocol, which is a list of messages and challenges.

Note that this is definitionally equal to `Transcript (Fin.last n) pSpec`. -/
@[reducible, inline, specialize]
def FullTranscript (pSpec : ProtocolSpec n) := (i : Fin n) → (pSpec i).2

namespace FullTranscript

@[reducible, inline, specialize]
def messages (transcript : FullTranscript pSpec) (i : MessageIdx pSpec) :=
  transcript i.val

@[reducible, inline, specialize]
def challenges (transcript : FullTranscript pSpec) (i : ChallengeIdx pSpec) :=
  transcript i.val

/-- There is only one full transcript (the empty one) for an empty protocol -/
instance : Unique (FullTranscript (default : ProtocolSpec 0)) := inferInstance

end FullTranscript

/-! ### Restriction of Protocol Specifications & Transcripts -/

section Restrict

variable {n : ℕ}

/-
TODOs:
1. Change function signature to `m : Fin (n + 1)`
2. Show that `(pSpec.take m).MessageIdx` is definitionally equal to `pSpec.MessageIdxUpTo m`
-/

/-- Take the first `m ≤ n` rounds of a `ProtocolSpec n` -/
abbrev take (m : ℕ) (h : m ≤ n) (pSpec : ProtocolSpec n) : ProtocolSpec m := Fin.take m h pSpec

def take' (m : Fin (n + 1)) (pSpec : ProtocolSpec n) : ProtocolSpec m.val :=
  Fin.take m.val m.is_le pSpec

@[simp]
lemma take'_MessageIdx (m : Fin (n + 1)) (pSpec : ProtocolSpec n) :
    (pSpec.take' m).MessageIdx = pSpec.MessageIdxUpTo m := by
  rfl

lemma take'_Transcript (m : Fin (n + 1)) (pSpec : ProtocolSpec n) :
    (pSpec.take' m).FullTranscript = pSpec.Transcript m := rfl

/-- Take the last `m ≤ n` rounds of a `ProtocolSpec n` -/
abbrev rtake (m : ℕ) (h : m ≤ n) (pSpec : ProtocolSpec n) := Fin.rtake m h pSpec

/-- Take the first `m ≤ n` rounds of a (full) transcript for a protocol specification `pSpec` -/
abbrev FullTranscript.take {pSpec : ProtocolSpec n} (m : ℕ) (h : m ≤ n)
    (transcript : FullTranscript pSpec) : FullTranscript (pSpec.take m h) :=
  Fin.take m h transcript

/-- Take the last `m ≤ n` rounds of a (full) transcript for a protocol specification `pSpec` -/
abbrev FullTranscript.rtake {pSpec : ProtocolSpec n} (m : ℕ) (h : m ≤ n)
    (transcript : FullTranscript pSpec) : FullTranscript (pSpec.rtake m h) :=
  Fin.rtake m h transcript

end Restrict

namespace Transcript

/-- There is only one transcript for the empty protocol -/
instance {k : Fin 1} : Unique (Transcript k (default : ProtocolSpec 0)) where
  default := fun i => ()
  uniq := by solve_by_elim

/-- There is only one transcript for the empty protocol, represented as `![]` -/
instance {k : Fin 1} : Unique (Transcript k ![]) where
  default := fun ⟨i, h⟩ => by
    have : k = 0 := Fin.fin_one_eq_zero k
    subst this; simp at h
  uniq := fun _ => by
    ext ⟨i, h⟩
    have : k = 0 := Fin.fin_one_eq_zero k
    subst this; simp at h

/-- There is only one transcript for any protocol with cutoff index 0 -/
instance : Unique (Transcript 0 pSpec) where
  default := fun i => Fin.elim0 i
  uniq := fun T => by ext i; exact Fin.elim0 i

-- Potential natural re-indexing of messages and challenges.
-- Not needed for now, but could be useful.

-- instance instFinEnumMessageIdx : FinEnum pSpec.MessageIdx :=
--   FinEnum.Subtype.finEnum fun x ↦ pSpec.getDir x = Direction.P_to_V
-- instance instFinEnumChallengeIdx : FinEnum pSpec.ChallengeIdx :=
--   FinEnum.Subtype.finEnum fun x ↦ pSpec.getDir x = Direction.V_to_P

/-- Concatenate a message to the end of a partial transcript. This is definitionally equivalent to
    `Fin.snoc`. -/
@[inline]
abbrev concat {m : Fin n} (msg : (pSpec m).2) (T : Transcript m.castSucc pSpec) :
    Transcript m.succ pSpec :=
  Fin.snoc T msg

-- Define conversions to and from `Transcript` with `MessagesUpTo` and `ChallengesUpTo`

variable {k : Fin (n + 1)}

/-- Extract messages from a transcript up to round `k` -/
def toMessagesUpTo (transcript : Transcript k pSpec) : MessagesUpTo k pSpec :=
  fun ⟨i, _⟩ => transcript i

/-- Extract challenges from a transcript up to round `k` -/
def toChallengesUpTo (transcript : Transcript k pSpec) : ChallengesUpTo k pSpec :=
  fun ⟨i, _⟩ => transcript i

def toMessagesChallenges (transcript : Transcript k pSpec) :
    MessagesUpTo k pSpec × ChallengesUpTo k pSpec :=
  (transcript.toMessagesUpTo, transcript.toChallengesUpTo)

def ofMessagesChallenges (messages : MessagesUpTo k pSpec)
    (challenges : ChallengesUpTo k pSpec) : Transcript k pSpec :=
  fun i => match h : pSpec.getDir (i.castLE (by omega)) with
  | Direction.P_to_V => messages ⟨i.castLE (by omega), h⟩
  | Direction.V_to_P => challenges ⟨i.castLE (by omega), h⟩

/-- An equivalence between transcripts up to round `k` and the tuple of messages and challenges up
  to round `k`. -/
@[simps!]
def equivMessagesChallenges :
    Transcript k pSpec ≃ (MessagesUpTo k pSpec × ChallengesUpTo k pSpec) where
  toFun := toMessagesChallenges
  invFun := ofMessagesChallenges.uncurry
  left_inv := fun T => by
    ext i
    simp [ofMessagesChallenges, toMessagesChallenges, toMessagesUpTo, toChallengesUpTo]
    split <;> simp
  right_inv := fun ⟨messages, challenges⟩ => by
    ext i
    · have : (pSpec <| i.val.castLE (by omega)).1 = Direction.P_to_V := i.property
      simp [ofMessagesChallenges, toMessagesChallenges, toMessagesUpTo]
      split <;> aesop
    · have : (pSpec <| i.val.castLE (by omega)).1 = Direction.V_to_P := i.property
      simp [ofMessagesChallenges, toMessagesChallenges, toChallengesUpTo]
      split <;> aesop

-- TODO: state theorem that `Transcript.concat` is equivalent to `MessagesUpTo.{concat/extend}` with
-- `ChallengesUpTo.{extend/concat}`, depending on the direction of the round

end Transcript

namespace FullTranscript

/-- Convert a full transcript to the tuple of messages and challenges -/
def toMessagesChallenges (transcript : FullTranscript pSpec) : Messages pSpec × Challenges pSpec :=
  by exact Transcript.toMessagesChallenges (by exact transcript : Transcript (Fin.last n) pSpec)

/-- Convert the tuple of messages and challenges to a full transcript -/
def ofMessagesChallenges (messages : Messages pSpec) (challenges : Challenges pSpec) :
    FullTranscript pSpec :=
  by exact
    (Transcript.ofMessagesChallenges
      (by exact messages : MessagesUpTo (Fin.last n) pSpec)
      (by exact challenges : ChallengesUpTo (Fin.last n) pSpec))

/-- An equivalence between full transcripts and the tuple of messages and challenges. -/
@[simps!]
def equivMessagesChallenges : FullTranscript pSpec ≃ (Messages pSpec × Challenges pSpec) := by
  change Transcript (Fin.last n) pSpec ≃
    (MessagesUpTo (Fin.last n) pSpec × ChallengesUpTo (Fin.last n) pSpec)
  exact Transcript.equivMessagesChallenges

end FullTranscript

/-- The specification of whether each message in a protocol specification is available in full
    (`None`) or received as an oracle (`Some (instOracleInterface (pSpec.Message i))`).

    This is defined as a type class for notational convenience. -/
class OracleInterfaces (pSpec : ProtocolSpec n) where
  oracleInterfaces : ∀ i, Option (OracleInterface (pSpec.Message i))

section OracleInterfaces

variable (pSpec : ProtocolSpec n) [inst : OracleInterfaces pSpec]

/-- Subtype of `pSpec.MessageIdx` for messages that are received as oracles -/
@[reducible, inline, specialize]
def OracleMessageIdx := {i : pSpec.MessageIdx // (inst.oracleInterfaces i).isSome }

/-- The oracle interface instances for messages that are received as oracles -/
instance {i : OracleMessageIdx pSpec} : OracleInterface (pSpec.Message i) :=
  (inst.oracleInterfaces i).get i.2

/-- Subtype of `pSpec.MessageIdx` for messages that are received in full -/
@[reducible, inline, specialize]
def PlainMessageIdx := {i : pSpec.MessageIdx // (inst.oracleInterfaces i).isNone }

/-- The type of messages that are received in full -/
@[reducible, inline, specialize]
def PlainMessage (i : pSpec.PlainMessageIdx) := pSpec.Message i.1

/-- The type of messages that are received as oracles -/
@[reducible, inline, specialize]
def OracleMessage (i : pSpec.OracleMessageIdx) := pSpec.Message i.1

def PlainMessages (pSpec : ProtocolSpec n) [OracleInterfaces pSpec] : Type :=
  ∀ i, pSpec.PlainMessage i

def OracleMessages (pSpec : ProtocolSpec n) [OracleInterfaces pSpec] : Type :=
  ∀ i, pSpec.OracleMessage i

-- TODO: re-define `OracleReduction` to depend on these oracle interfaces, since currently we
-- assume that _all_ messages are available as oracles in an oracle reduction

-- Alternatively, we can define a `HybridReduction` structure, where the oracle interface for each
-- message is optional, that can be specialized to `OracleReduction` and `Reduction`

end OracleInterfaces

/-- Turn each verifier's challenge into an oracle, where querying a unit type gives back the
  challenge -/
@[reducible, inline, specialize]
instance instChallengeOracleInterface {pSpec : ProtocolSpec n} {i : pSpec.ChallengeIdx} :
    OracleInterface (pSpec.Challenge i) where
  Query := Unit
  Response := pSpec.Challenge i
  oracle := fun c _ => c

/-- Query a verifier's challenge for a given challenge round `i`, given the "trivial" challenge
oracle interface -/
@[reducible, inline, specialize]
def getChallenge (pSpec : ProtocolSpec n) (i : pSpec.ChallengeIdx) :
    OracleComp [pSpec.Challenge]ₒ (pSpec.Challenge i) :=
  (query i () : OracleQuery [pSpec.Challenge]ₒ (pSpec.Challenge i))

/-- Define the query implementation for the verifier's challenge in terms of `ProbComp`.

This is a randomness oracle: it simply calls the `selectElem` method inherited from the
  `SelectableType` instance on the challenge types.
-/
def challengeQueryImpl {pSpec : ProtocolSpec n} [∀ i, SelectableType (pSpec.Challenge i)] :
    QueryImpl [pSpec.Challenge]ₒ ProbComp where
  impl | query i () => uniformOfFintype (pSpec.Challenge i)

/-- Turn each verifier's challenge into an oracle, where one needs to query
  with an input statement and prior messages up to that round to get a challenge -/
@[reducible, inline, specialize]
def instChallengeOracleInterfaceFiatShamir {pSpec : ProtocolSpec n} {i : pSpec.ChallengeIdx}
    {StmtIn : Type} : OracleInterface (pSpec.Challenge i) where
  Query := StmtIn × pSpec.MessagesUpTo i.1.castSucc
  Response := pSpec.Challenge i
  oracle := fun c _ => c

/-- The oracle interface for Fiat-Shamir.

This is the (inefficient) version where we hash the input statement and the entire transcript up to
the point of deriving a new challenge. To be precise:
- The domain of the oracle is `Statement × pSpec.MessagesUpTo i.1.castSucc`
- The range of the oracle is `pSpec.Challenge i`

Some variants of Fiat-Shamir takes in a salt each round. We assume that such salts are included in
the input statement (i.e. we can always transform a given reduction into one where every round has a
random salt). -/
@[inline, reducible]
def srChallengeOracle (Statement : Type) {n : ℕ} (pSpec : ProtocolSpec n) :
    OracleSpec pSpec.ChallengeIdx :=
  fun i => (Statement × pSpec.MessagesUpTo i.1.castSucc, pSpec.Challenge i)

alias fsChallengeOracle := srChallengeOracle

/-- Decidable equality for the state-restoration / (slow) Fiat-Shamir oracle -/
instance {pSpec : ProtocolSpec n} {Statement : Type}
    [DecidableEq Statement]
    [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Challenge i)] :
    OracleSpec.DecidableEq (srChallengeOracle Statement pSpec) where
  domain_decidableEq' := fun i => by
    unfold OracleSpec.domain srChallengeOracle MessagesUpTo
    infer_instance
  range_decidableEq' := fun i => by
    unfold OracleSpec.range
    infer_instance

instance {pSpec : ProtocolSpec n} {Statement : Type} [∀ i, VCVCompatible (pSpec.Challenge i)] :
    OracleSpec.FiniteRange (srChallengeOracle Statement pSpec) where
  range_inhabited' := fun i => by simp [OracleSpec.range]; infer_instance
  range_fintype' := fun i => by simp [OracleSpec.range]; infer_instance

instance {pSpec : ProtocolSpec n} {Statement : Type} [∀ i, VCVCompatible (pSpec.Challenge i)] :
    OracleSpec.FiniteRange (fsChallengeOracle Statement pSpec) :=
  inferInstanceAs (OracleSpec.FiniteRange (srChallengeOracle Statement pSpec))

/-- Define the query implementation for the state-restoration / (slow) Fiat-Shamir oracle (returns a
    challenge given messages up to that point) in terms of `ProbComp`.

  This is a randomness oracle: it simply calls the `selectElem` method inherited from the
  `SelectableType` instance on the challenge types. We may then augment this with `withCaching` to
  obtain a function-like implementation (caches and replays previous queries).

  For implementation with caching, we add `withCaching`.

  For implementation where the whole function is sampled ahead of time, and we answer with that
  function, see `srChallengeQueryImpl'`.
-/
@[reducible, inline, specialize, simp]
def srChallengeQueryImpl {Statement : Type} {pSpec : ProtocolSpec n}
    [∀ i, SelectableType (pSpec.Challenge i)] :
    QueryImpl (srChallengeOracle Statement pSpec) ProbComp where
  impl | query i _ => uniformOfFintype (pSpec.Challenge i)

/-- Alternate version of query implementation that takes in a cached function `f` and returns
  the result and the updated function.

  TODO: upstream this as a more general construction in VCVio -/
@[reducible, inline, specialize, simp]
def srChallengeQueryImpl' {Statement : Type} {pSpec : ProtocolSpec n}
    [∀ i, SelectableType (pSpec.Challenge i)] :
    QueryImpl (srChallengeOracle Statement pSpec)
      (StateT (srChallengeOracle Statement pSpec).FunctionType ProbComp)
    where
  impl | query i t => fun f => pure (f i t, f)

alias fsChallengeQueryImpl' := srChallengeQueryImpl'

namespace MessagesUpTo

/-- Auxiliary function for deriving the transcript up to round `k` from the (full) messages, via
  querying the state-restoration / Fiat-Shamir oracle for the challenges.

  This is used to define `deriveTranscriptFS`. -/
def deriveTranscriptSRAux {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (stmt : StmtIn) (k : Fin (n + 1)) (messages : pSpec.MessagesUpTo k)
    (j : Fin (k + 1)) :
    OracleComp (oSpec ++ₒ fsChallengeOracle StmtIn pSpec)
      (pSpec.Transcript (j.castLE (by omega))) := do
  Fin.induction (n := k)
    (pure (fun i => i.elim0))
    (fun i ih => do
      let prevTranscript ← ih
      match hDir : pSpec.getDir (i.castLE (by omega)) with
      | .V_to_P =>
        let challenge : pSpec.Challenge ⟨i.castLE (by omega), hDir⟩ ←
          query (spec := fsChallengeOracle _ _) ⟨i.castLE (by omega), hDir⟩
            (stmt, messages.take i.castSucc)
        return prevTranscript.concat challenge
      | .P_to_V => return prevTranscript.concat (messages ⟨i, hDir⟩))
    j

/-- Derive the transcript up to round `k` from the (full) messages, via querying the
    state-restoration / Fiat-Shamir oracle for the challenges. -/
def deriveTranscriptSR {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (stmt : StmtIn) (k : Fin (n + 1)) (messages : pSpec.MessagesUpTo k) :
    OracleComp (oSpec ++ₒ fsChallengeOracle StmtIn pSpec) (pSpec.Transcript k) := do
  deriveTranscriptSRAux stmt k messages (Fin.last k)

alias deriveTranscriptFS := deriveTranscriptSR

end MessagesUpTo

namespace Messages

/-- Derive the transcript up to round `k` from the (full) messages, via querying the
    state-restoration / Fiat-Shamir oracle for the challenges. -/
def deriveTranscriptSR {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (stmt : StmtIn) (messages : pSpec.Messages) :
    OracleComp (oSpec ++ₒ fsChallengeOracle StmtIn pSpec) pSpec.FullTranscript := do
  MessagesUpTo.deriveTranscriptSR stmt (Fin.last n) messages

alias deriveTranscriptFS := deriveTranscriptSR

end Messages

end ProtocolSpec

-- Notation for the type signature of an interactive protocol
notation "𝒫——⟦" term "⟧⟶𝒱" => (Direction.P_to_V, term)
notation "𝒫⟵⟦" term "⟧——𝒱" => (Direction.V_to_P, term)

-- Test notation
def pSpecNotationTest : ProtocolSpec 2 :=
  ![ 𝒫——⟦ Polynomial (ZMod 101) ⟧⟶𝒱,
     𝒫⟵⟦ ZMod 101 ⟧——𝒱]
