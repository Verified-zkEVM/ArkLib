/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.Fin.Tuple.Lemmas
import ArkLib.OracleReduction.Prelude
import ArkLib.OracleReduction.OracleInterface

/-!
# Protocol Specifications for (Oracle) Reductions

This file defines the `ProtocolSpec` type, which is used to specify the protocol between the prover
and the verifier.
-/

universe u v

open OracleComp OracleSpec

/-- A protocol specification for an interactive protocol with `n` steps consists of:
- A vector of directions `dir` for each step, which is either `.P_to_V` (the prover sends a message
  to the verifier) or `.V_to_P` (the verifier sends a challenge to the prover).
- A vector of types `«Type»` for each step, which is the type of the message or challenge sent in
  that step. -/
@[ext]
structure ProtocolSpec (n : ℕ) where
  /-- The direction of each message in the protocol. -/
  dir : Fin n → Direction
  /-- The type of each message in the protocol. -/
  «Type» : Fin n → Type
deriving Inhabited

variable {n : ℕ}

namespace ProtocolSpec

section Defs

/-- The empty protocol specification, with no messages or challenges, written as `!p[]`. -/
@[reducible]
def empty : ProtocolSpec 0 := ⟨!v[], !v[]⟩

@[inherit_doc] notation "!p[]" => empty

/-- Subtype of `Fin n` for the indices corresponding to messages in a protocol specification -/
@[reducible, simp]
def MessageIdx (pSpec : ProtocolSpec n) :=
  {i : Fin n // pSpec.dir i = Direction.P_to_V}

/-- Subtype of `Fin n` for the indices corresponding to challenges in a protocol specification -/
@[reducible, simp]
def ChallengeIdx (pSpec : ProtocolSpec n) :=
  {i : Fin n // pSpec.dir i = Direction.V_to_P}

instance {pSpec : ProtocolSpec n} : CoeHead (MessageIdx pSpec) (Fin n) where
  coe := fun i => i.1
instance {pSpec : ProtocolSpec n} : CoeHead (ChallengeIdx pSpec) (Fin n) where
  coe := fun i => i.1

/-- The type of the `i`-th message in a protocol specification.

This does not distinguish between messages received in full or as an oracle. -/
@[reducible, inline, specialize, simp]
def Message (pSpec : ProtocolSpec n) (i : MessageIdx pSpec) := pSpec.«Type» i.val

/-- Unbundled version of `Message`, which supplies the proof separately from the index. -/
@[reducible, inline, specialize, simp]
def Message' (pSpec : ProtocolSpec n) (i : Fin n) (_ : pSpec.dir i = .P_to_V) := pSpec.«Type» i

/-- The type of the `i`-th challenge in a protocol specification -/
@[reducible, inline, specialize, simp]
def Challenge (pSpec : ProtocolSpec n) (i : ChallengeIdx pSpec) := pSpec.«Type» i.val

/-- Unbundled version of `Challenge`, which supplies the proof separately from the index. -/
@[reducible, inline, specialize, simp]
def Challenge' (pSpec : ProtocolSpec n) (i : Fin n) (_ : pSpec.dir i = .V_to_P) := pSpec.«Type» i

/-- The type of all messages in a protocol specification. Uncurried version of `Message`. -/
@[reducible, inline, specialize]
def Messages (pSpec : ProtocolSpec n) : Type := ∀ i, pSpec.Message i

/-- Unbundled version of `Messages`, which supplies the proof separately from the index. -/
@[reducible, inline, specialize]
def Messages' (pSpec : ProtocolSpec n) : Type :=
  ∀ i, (hi : pSpec.dir i = .P_to_V) → pSpec.«Type» i

/-- The type of all challenges in a protocol specification -/
@[reducible, inline, specialize]
def Challenges (pSpec : ProtocolSpec n) : Type := ∀ i, pSpec.Challenge i

/-- Unbundled version of `Challenges`, which supplies the proof separately from the index. -/
@[reducible, inline, specialize]
def Challenges' (pSpec : ProtocolSpec n) : Type :=
  ∀ i, (hi : pSpec.dir i = .V_to_P) → pSpec.«Type» i

/-- The (full)) transcript of an interactive protocol, which is a list of messages and challenges.

Note that this is definitionally equal to `Transcript (Fin.last n) pSpec`. -/
@[reducible, inline, specialize]
def FullTranscript (pSpec : ProtocolSpec n) := (i : Fin n) → pSpec.«Type» i

section Restrict

variable {n : ℕ}

/-- Take the first `m ≤ n` rounds of a `ProtocolSpec n` -/
def take (m : ℕ) (h : m ≤ n) (pSpec : ProtocolSpec n) : ProtocolSpec m :=
  {dir := Fin.take m h pSpec.dir, «Type» := Fin.take m h pSpec.«Type»}

/-- Take the last `m ≤ n` rounds of a `ProtocolSpec n` -/
def rtake (m : ℕ) (h : m ≤ n) (pSpec : ProtocolSpec n) : ProtocolSpec m :=
  {dir := Fin.rtake m h pSpec.dir, «Type» := Fin.rtake m h pSpec.«Type»}

/-- Drop the first `m ≤ n` rounds of a `ProtocolSpec n` -/
def drop (m : ℕ) (h : m ≤ n) (pSpec : ProtocolSpec n) : ProtocolSpec (n - m) :=
  {dir := Fin.drop m h pSpec.dir, «Type» := Fin.drop m h pSpec.«Type»}

/-- Drop the last `m ≤ n` rounds of a `ProtocolSpec n` -/
def rdrop (m : ℕ) (h : m ≤ n) (pSpec : ProtocolSpec n) : ProtocolSpec (n - m) :=
  {dir := Fin.rdrop m h pSpec.dir, «Type» := Fin.rdrop m h pSpec.«Type»}

/-- Extract the slice of the rounds of a `ProtocolSpec n` from `start` to `stop - 1`. -/
def extract (start stop : ℕ) (h1 : start ≤ stop) (h2 : stop ≤ n) (pSpec : ProtocolSpec n) :
    ProtocolSpec (stop - start) where
  dir := Fin.extract start stop h1 h2 pSpec.dir
  «Type» := Fin.extract start stop h1 h2 pSpec.«Type»

/- Instances for accessing slice notation -/

instance : SliceLT (ProtocolSpec n) ℕ
    (fun _ stop => stop ≤ n)
    (fun _ stop _ => ProtocolSpec stop)
    where
  sliceLT := fun v stop h => take stop h v

instance : SliceGE (ProtocolSpec n) ℕ
    (fun _ start => start ≤ n)
    (fun _ start _ => ProtocolSpec (n - start))
    where
  sliceGE := fun v start h => drop start h v

instance : Slice (ProtocolSpec n) ℕ ℕ
    (fun _ start stop => start ≤ stop ∧ stop ≤ n)
    (fun _ start stop _ => ProtocolSpec (stop - start))
    where
  slice := fun v start stop h => extract start stop h.1 h.2 v

variable {m start stop : ℕ} {h : m ≤ n} {h1 : start ≤ stop} {h2 : stop ≤ n}
  {pSpec : ProtocolSpec n}

@[simp] lemma take_dir : pSpec⟦:m⟧.dir = pSpec.dir⟦:m⟧ := rfl
@[simp] lemma take_Type : pSpec⟦:m⟧.«Type» = pSpec.«Type»⟦:m⟧ := rfl
@[simp] lemma drop_dir : pSpec⟦m:⟧.dir = pSpec.dir⟦m:⟧ := rfl
@[simp] lemma drop_Type : pSpec⟦m:⟧.«Type» = pSpec.«Type»⟦m:⟧ := rfl
@[simp] lemma extract_dir : pSpec⟦start:stop⟧.dir = pSpec.dir⟦start:stop⟧ := rfl
@[simp] lemma extract_Type : pSpec⟦start:stop⟧.«Type» = pSpec.«Type»⟦start:stop⟧ := rfl

namespace FullTranscript

variable {pSpec : ProtocolSpec n}

/-- Take the first `m ≤ n` rounds of a (full) transcript for a protocol specification `pSpec` -/
abbrev take (m : ℕ) (h : m ≤ n)
    (transcript : FullTranscript pSpec) : FullTranscript (pSpec.take m h) :=
  Fin.take m h transcript

/-- Take the last `m ≤ n` rounds of a (full) transcript for a protocol specification `pSpec` -/
abbrev rtake (m : ℕ) (h : m ≤ n)
    (transcript : FullTranscript pSpec) : FullTranscript (pSpec.rtake m h) :=
  Fin.rtake m h transcript

abbrev drop (m : ℕ) (h : m ≤ n)
    (transcript : FullTranscript pSpec) : FullTranscript (pSpec.drop m h) :=
  Fin.drop m h transcript

abbrev rdrop (m : ℕ) (h : m ≤ n)
    (transcript : FullTranscript pSpec) : FullTranscript (pSpec.rdrop m h) :=
  Fin.rdrop m h transcript

abbrev extract (start stop : ℕ) (h1 : start ≤ stop) (h2 : stop ≤ n)
    (transcript : FullTranscript pSpec) : FullTranscript (pSpec.extract start stop h1 h2) :=
  Fin.extract start stop h1 h2 transcript

/- Instances for accessing slice notation -/

instance : SliceLT (FullTranscript pSpec) ℕ
    (fun _ stop => stop ≤ n)
    (fun _ stop _ => FullTranscript (pSpec⟦:stop⟧))
    where
  sliceLT := fun v stop h => take stop h v

instance : SliceGE (FullTranscript pSpec) ℕ
    (fun _ start => start ≤ n)
    (fun _ start _ => FullTranscript (pSpec⟦start:⟧))
    where
  sliceGE := fun v start h => drop start h v

instance : Slice (FullTranscript pSpec) ℕ ℕ
    (fun _ start stop => start ≤ stop ∧ stop ≤ n)
    (fun _ start stop _ => FullTranscript (pSpec⟦start:stop⟧))
    where
  slice := fun v start stop h => extract start stop h.1 h.2 v

variable {m start stop : ℕ} {h : m ≤ n} {h1 : start ≤ stop} {h2 : stop ≤ n}
  {pSpec : ProtocolSpec n} {transcript : FullTranscript pSpec}

lemma take_eq_take : transcript⟦:m⟧ = transcript.take m h := rfl
lemma rtake_eq_rtake : transcript⟦m:⟧ = transcript.drop m h := rfl
lemma extract_eq_extract : transcript⟦start:stop⟧ = transcript.extract start stop h1 h2 :=
  rfl

end FullTranscript

end Restrict

/-- Subtype of `Fin k` for the indices corresponding to messages in a protocol specification up to
  round `k` -/
@[reducible, simp]
def MessageIdxUpTo (k : Fin (n + 1)) (pSpec : ProtocolSpec n) : Type :=
  (pSpec⟦:k.val⟧).MessageIdx

lemma MessageIdxUpTo.eq_MessageIdx {k : Fin (n + 1)} {pSpec : ProtocolSpec n} :
    pSpec.MessageIdxUpTo k = {i : Fin k // pSpec.dir (i.castLE (by omega)) = .P_to_V} := rfl

/-- Subtype of `Fin k` for the indices corresponding to challenges in a protocol specification up to
  round `k` -/
@[reducible, simp]
def ChallengeIdxUpTo (k : Fin (n + 1)) (pSpec : ProtocolSpec n) : Type :=
  (pSpec⟦:k.val⟧).ChallengeIdx

/-- The indexed family of messages from the prover up to round `k`. -/
@[reducible, inline, specialize]
def MessageUpTo (k : Fin (n + 1)) (pSpec : ProtocolSpec n) (i : pSpec.MessageIdxUpTo k) :=
  (pSpec⟦:k.val⟧).Message i

/-- The indexed family of challenges from the verifier up to round `k`. -/
@[reducible, inline, specialize]
def ChallengeUpTo (k : Fin (n + 1)) (pSpec : ProtocolSpec n) (i : pSpec.ChallengeIdxUpTo k) :=
  (pSpec⟦:k.val⟧).Challenge i

/-- The type of all messages from the prover up to round `k`. -/
@[reducible, inline, specialize]
def MessagesUpTo (k : Fin (n + 1)) (pSpec : ProtocolSpec n) : Type :=
  ∀ i, pSpec.MessageUpTo k i

/-- The type of all challenges from the verifier up to round `k`. -/
@[reducible, inline, specialize]
def ChallengesUpTo (k : Fin (n + 1)) (pSpec : ProtocolSpec n) : Type :=
  ∀ i, (pSpec.take k k.is_le).Challenge i

/-- A (partial) transcript of a protocol specification, indexed by some `k : Fin (n + 1)`, is a
list of messages from the protocol for all indices `i` less than `k`.

This is defined as the full transcript of the protocol specification up to round `k`. -/
@[reducible, inline, specialize]
def Transcript (k : Fin (n + 1)) (pSpec : ProtocolSpec n) : Type :=
  (pSpec⟦:k.val⟧).FullTranscript

@[simp]
lemma Transcript.def_eq {k : Fin (n + 1)} {pSpec : ProtocolSpec n} :
    (pSpec.take k k.is_le).FullTranscript =
      ((i : Fin k) → pSpec.«Type» (Fin.castLE (by omega) i)) :=
  rfl

end Defs

section Instances

/-- There is only one protocol specification with 0 messages (the empty one) -/
instance : Unique (ProtocolSpec 0) where
  default := empty
  uniq := fun ⟨_, _⟩ => by simp; constructor <;> (funext i; exact Fin.elim0 i)

-- Note these strange instance syntheses. This is necessary to avoid diamonds later on when
-- going to sequential composition.

instance : ∀ i, VCVCompatible (Challenge !p[] i) :=
  fun ⟨i, h⟩ =>
    (Fin.elim0 i : (h' : !p[].dir i = .V_to_P) → VCVCompatible (!p[].Challenge ⟨i, h'⟩)) h
instance : ∀ i, SampleableType (Challenge !p[] i) :=
  fun ⟨i, h⟩ =>
    (Fin.elim0 i : (h' : !p[].dir i = .V_to_P) → SampleableType (!p[].Challenge ⟨i, h'⟩)) h
instance : ∀ i, OracleInterface (Message !p[] i) :=
  fun ⟨i, h⟩ =>
    (Fin.elim0 i : (h' : !p[].dir i = .P_to_V) → OracleInterface (!p[].Message ⟨i, h'⟩)) h

instance : ∀ i, VCVCompatible ((default : ProtocolSpec 0).Challenge i) := fun ⟨i, _⟩ => Fin.elim0 i
instance : ∀ i, SampleableType ((default : ProtocolSpec 0).Challenge i) := fun ⟨i, _⟩ => Fin.elim0 i
instance : ∀ i, OracleInterface ((default : ProtocolSpec 0).Message i) := fun ⟨i, _⟩ => Fin.elim0 i

variable {Msg Chal : Type}

instance : IsEmpty (ChallengeIdx ⟨!v[.P_to_V], !v[Msg]⟩) :=
  ⟨fun ⟨i, h⟩ => by aesop⟩
instance : Unique (MessageIdx ⟨!v[.P_to_V], !v[Msg]⟩) where
  default := ⟨0, by simp⟩
  uniq := fun i => by ext; simp
instance [inst : OracleInterface Msg] : ∀ i, OracleInterface (Message ⟨!v[.P_to_V], !v[Msg]⟩ i)
  | ⟨0, _⟩ => inst
instance : ∀ i, VCVCompatible (Challenge ⟨!v[.P_to_V], !v[Msg]⟩ i)
  | ⟨0, h⟩ => nomatch h
instance : ∀ i, SampleableType (Challenge ⟨!v[.P_to_V], !v[Msg]⟩ i)
  | ⟨0, h⟩ => nomatch h

instance : IsEmpty (MessageIdx ⟨!v[.V_to_P], !v[Chal]⟩) :=
  ⟨fun ⟨i, h⟩ => by aesop⟩
instance : Unique (ChallengeIdx ⟨!v[.V_to_P], !v[Chal]⟩) where
  default := ⟨0, by simp⟩
  uniq := fun i => by ext; simp
instance : ∀ i, OracleInterface (Message ⟨!v[.V_to_P], !v[Chal]⟩ i)
  | ⟨0, h⟩ => nomatch h
instance [inst : VCVCompatible Chal] : ∀ i, VCVCompatible (Challenge ⟨!v[.V_to_P], !v[Chal]⟩ i)
  | ⟨0, _⟩ => inst
instance [inst : SampleableType Chal] : ∀ i, SampleableType (Challenge ⟨!v[.V_to_P], !v[Chal]⟩ i)
  | ⟨0, _⟩ => inst

variable {pSpec : ProtocolSpec n}

instance : Fintype (pSpec.MessageIdx) := Subtype.fintype (fun i => pSpec.dir i = .P_to_V)
instance : Fintype (pSpec.ChallengeIdx) := Subtype.fintype (fun i => pSpec.dir i = .V_to_P)
instance {k : Fin (n + 1)} : Fintype (pSpec.MessageIdxUpTo k) :=
  inferInstanceAs (Fintype <| MessageIdx (pSpec.take k k.is_le))
instance {k : Fin (n + 1)} : Fintype (pSpec.ChallengeIdxUpTo k) :=
  inferInstanceAs (Fintype <| ChallengeIdx (pSpec.take k k.is_le))

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
instance {k : Fin 1} : Unique (MessagesUpTo k !p[]) where
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

def concat' {k : Fin n}
    (messages : (i : Fin k) → (pSpec.dir (i.castLE (by omega)) = .P_to_V
      → pSpec.«Type» (i.castLE (by omega))))
    (msg : (h : pSpec.dir k = .P_to_V) → pSpec.Message ⟨k, h⟩) :
    (i : Fin (k + 1)) → (pSpec.dir (i.castLE (by omega)) = .P_to_V) →
      pSpec.«Type» (i.castLE (by omega)) :=
  Fin.dconcat messages msg

/-- Concatenate the `k`-th message to the end of the tuple of messages up to round `k`, assuming
  round `k` is a message round. -/
def concat {k : Fin n} (messages : MessagesUpTo k.castSucc pSpec)
    (h : pSpec.dir k = .P_to_V) (msg : pSpec.Message ⟨k, h⟩) : MessagesUpTo k.succ pSpec :=
  fun ⟨i, h⟩ => (concat' (pSpec := pSpec) (fun i hi => messages ⟨i, hi⟩) (fun _ => msg)) i h
  -- fun i => if hi : i.1.1 < k then messages ⟨⟨i.1.1, hi⟩, i.property⟩ else
  --   (by simp [MessageUpTo, Fin.eq_last_of_not_lt hi]; exact msg)

/-- Extend the tuple of messages up to round `k` to up to round `k + 1`, assuming round `k` is a
  challenge round (so no message from the prover is sent). -/
def extend {k : Fin n} (messages : MessagesUpTo k.castSucc pSpec)
    (h : pSpec.dir k = .V_to_P) : MessagesUpTo k.succ pSpec :=
  fun ⟨i, h⟩ => (concat' (pSpec := pSpec) (fun i hi => messages ⟨i, hi⟩) (fun h' => by aesop)) i h
  -- fun i => if hi : i.1.1 < k then messages ⟨⟨i.1.1, hi⟩, i.property⟩ else
  --   -- contradiction proof
  --   (by
  --     haveI hik : i.1 = Fin.last k := Fin.eq_last_of_not_lt hi
  --     haveI := i.property
  --     simp [hik] at this
  --     have : pSpec.dir k = .P_to_V := this
  --     aesop)

instance [inst : ∀ i, DecidableEq (pSpec.Message i)] {k : Fin (n + 1)} :
    DecidableEq (MessagesUpTo k pSpec) :=
  @Fintype.decidablePiFintype _ _ (fun i => inst ⟨i.1.castLE (by omega), i.property⟩) _

end MessagesUpTo

namespace ChallengesUpTo

/-- There is only one transcript for the empty protocol,
  represented as `default : ProtocolSpec 0` -/
instance {k : Fin 1} : Unique (ChallengesUpTo k (default : ProtocolSpec 0)) where
  default := fun i => ()
  uniq := by solve_by_elim

/-- There is only one transcript for the empty protocol, represented as `![]` -/
instance {k : Fin 1} : Unique (ChallengesUpTo k !p[]) where
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

def concat' {k : Fin n}
    (challenges : (i : Fin k) → (pSpec.dir (i.castLE (by omega)) = .V_to_P
      → pSpec.«Type» (i.castLE (by omega))))
    (chal : (h : pSpec.dir k = .V_to_P) → pSpec.Challenge ⟨k, h⟩) :
    (i : Fin (k + 1)) → (pSpec.dir (i.castLE (by omega)) = .V_to_P) →
      pSpec.«Type» (i.castLE (by omega)) :=
  Fin.dconcat challenges chal

/-- Concatenate the `k`-th challenge to the end of the tuple of challenges up to round `k`, assuming
  round `k` is a challenge round. -/
def concat {k : Fin n} (challenges : ChallengesUpTo k.castSucc pSpec)
    (h : pSpec.dir k = .V_to_P) (chal : pSpec.Challenge ⟨k, h⟩) : ChallengesUpTo k.succ pSpec :=
  fun ⟨i, h⟩ => (concat' (pSpec := pSpec) (fun i hi => challenges ⟨i, hi⟩) (fun _ => chal)) i h
  -- fun i => if hi : i.1.1 < k then challenges ⟨⟨i.1.1, hi⟩, i.property⟩ else
  --   (by simp [Fin.eq_last_of_not_lt hi]; exact chal)

/-- Extend the tuple of challenges up to round `k` to up to round `k + 1`, assuming round `k` is a
  message round (so no challenge from the verifier is sent). -/
def extend {k : Fin n} (challenges : ChallengesUpTo k.castSucc pSpec)
    (h : pSpec.dir k = .P_to_V) : ChallengesUpTo k.succ pSpec :=
  fun ⟨i, h⟩ => (concat' (pSpec := pSpec) (fun i hi => challenges ⟨i, hi⟩) (fun h' => by aesop)) i h
  -- fun i => if hi : i.1.1 < k then challenges ⟨⟨i.1.1, hi⟩, i.property⟩ else
  --   -- contradiction proof
  --   (by
  --     haveI := Fin.eq_last_of_not_lt hi
  --     haveI := i.property
  --     simp_all [Fin.castLE])

end ChallengesUpTo

namespace Transcript

/-- There is only one transcript for the empty protocol -/
instance {k : Fin 1} : Unique (Transcript k (default : ProtocolSpec 0)) where
  default := fun i => ()
  uniq := by solve_by_elim

/-- There is only one transcript for the empty protocol, represented as `![]` -/
instance {k : Fin 1} : Unique (Transcript k !p[]) where
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
--   FinEnum.Subtype.finEnum fun x ↦ pSpec.dir x = Direction.P_to_V
-- instance instFinEnumChallengeIdx : FinEnum pSpec.ChallengeIdx :=
--   FinEnum.Subtype.finEnum fun x ↦ pSpec.dir x = Direction.V_to_P

/-- Concatenate a message to the end of a partial transcript. This is definitionally equivalent to
    `Fin.snoc`. -/
@[inline]
abbrev concat {m : Fin n} (msg : pSpec.«Type» m) (T : Transcript m.castSucc pSpec) :
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
  fun i => match h : pSpec.dir (i.castLE (by omega)) with
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
    · have : pSpec.dir (i.val.castLE (by omega)) = Direction.P_to_V := i.property
      simp [ofMessagesChallenges, toMessagesChallenges, toMessagesUpTo]
      split <;> aesop
    · have : pSpec.dir (i.val.castLE (by omega)) = Direction.V_to_P := i.property
      simp [ofMessagesChallenges, toMessagesChallenges, toChallengesUpTo]
      split <;> aesop

-- TODO: state theorem that `Transcript.concat` is equivalent to `MessagesUpTo.{concat/extend}` with
-- `ChallengesUpTo.{extend/concat}`, depending on the direction of the round

end Transcript

namespace FullTranscript

@[reducible, inline, specialize]
def messages (transcript : FullTranscript pSpec) (i : MessageIdx pSpec) :=
  transcript i.val

@[reducible, inline, specialize]
def challenges (transcript : FullTranscript pSpec) (i : ChallengeIdx pSpec) :=
  transcript i.val

/-- There is only one full transcript (the empty one) for an empty protocol -/
instance : Unique (FullTranscript (default : ProtocolSpec 0)) := inferInstance

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
    challenge.

  This is the default instance for the challenge oracle interface. It may be overridden by
  `challengeOracleInterface{SR/FS}` for state-restoration and/or Fiat-Shamir. -/
@[reducible, inline, specialize]
instance challengeOracleInterface {pSpec : ProtocolSpec n} :
    ∀ i, OracleInterface (pSpec.Challenge i) := fun i =>
  { Query := Unit
    toOC.spec := fun _ => pSpec.Challenge i
    toOC.impl := fun _ => do read }

-- dtumad: Longer term I think you want this, but need to change `[_]ₒ` stuff for that
def challengeOracleInterface' {pSpec : ProtocolSpec n} :
    OracleInterface (∀ i, pSpec.Challenge i) where
  Query := pSpec.ChallengeIdx
  toOC.spec := pSpec.Challenge
  toOC.impl i := do return (← read) i

/-- Query a verifier's challenge for a given challenge round `i`, given the default challenge
  oracle interface `challengeOracleInterface`.

  This is the default version for getting challenges, where we query the default
  `challengeOracleInterface`, which accepts trivial input. In contrast, `getChallenge{SR/FS}`
  requires an input statement and prior messages up to that round. -/
@[reducible, inline, specialize]
def getChallenge (pSpec : ProtocolSpec n) (i : pSpec.ChallengeIdx) :
    OracleComp ([pSpec.Challenge]ₒ'challengeOracleInterface) (pSpec.Challenge i) :=
  query (spec := [pSpec.Challenge]ₒ'challengeOracleInterface) ⟨i, ()⟩

/-- Define the query implementation for the verifier's challenge in terms of `ProbComp`.

This is a randomness oracle: it simply calls the `selectElem` method inherited from the
  `SampleableType` instance on the challenge types.
-/
def challengeQueryImpl {pSpec : ProtocolSpec n} [∀ i, SampleableType (pSpec.Challenge i)] :
    QueryImpl ([pSpec.Challenge]ₒ'challengeOracleInterface) ProbComp :=
  fun q => $ᵗ (pSpec.Challenge q.1)

/-- The oracle interface for state-restoration and (basic) Fiat-Shamir.

This is the version where we hash the input statement and the entire transcript up to
the point of deriving a new challenge. To be precise:
- The domain of the oracle is `Statement × pSpec.MessagesUpTo i.1.castSucc`
- The range of the oracle is `pSpec.Challenge i`
- The oracle just returns the challenge -/
@[reducible, inline, specialize]
def challengeOracleInterfaceSR (StmtIn : Type) (pSpec : ProtocolSpec n) :
    ∀ i, OracleInterface (pSpec.Challenge i) := fun i =>
  { Query := StmtIn × pSpec.MessagesUpTo i.1.castSucc
    toOC.spec := fun _ => pSpec.Challenge i
    toOC.impl := fun _ => read }

alias challengeOracleInterfaceFS := challengeOracleInterfaceSR

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
    OracleSpec (((i : pSpec.ChallengeIdx) × (challengeOracleInterfaceSR Statement pSpec i).Query)) :=
  [pSpec.Challenge]ₒ'(challengeOracleInterfaceSR Statement pSpec)

alias fsChallengeOracle := srChallengeOracle

-- dtumad: If we keep these they should just move to VCV about `OracleContext`.
/-- Decidable equality for the state-restoration / (slow) Fiat-Shamir oracle -/
instance {pSpec : ProtocolSpec n} {Statement : Type}
    [DecidableEq Statement]
    [∀ i, DecidableEq (pSpec.Message i)]
    [∀ i, DecidableEq (pSpec.Challenge i)] :
    OracleSpec.DecidableEq (srChallengeOracle Statement pSpec) := by
  refine { decidableEq_A := ?_, decidableEq_B := fun q => ?_ }
  · dsimp only [srChallengeOracle, OracleInterface.toOracleSpec,
      challengeOracleInterfaceSR, OracleSpec.toPFunctor,
      OracleInterface.Query]
    infer_instance
  · dsimp only [srChallengeOracle, OracleInterface.toOracleSpec,
      challengeOracleInterfaceSR, OracleSpec.toPFunctor,
      OracleInterface.Response]
    infer_instance

instance {pSpec : ProtocolSpec n} {Statement : Type} [∀ i, VCVCompatible (pSpec.Challenge i)] :
    OracleSpec.Fintype (srChallengeOracle Statement pSpec) := by
  refine { fintype_B := fun q => ?_ }
  dsimp only [srChallengeOracle, OracleInterface.toOracleSpec,
    challengeOracleInterfaceSR, OracleSpec.toPFunctor, OracleInterface.Response]
  infer_instance

instance {pSpec : ProtocolSpec n} {Statement : Type} [∀ i, VCVCompatible (pSpec.Challenge i)] :
    OracleSpec.Fintype (fsChallengeOracle Statement pSpec) := by
  refine { fintype_B := fun q => ?_ }
  dsimp only [fsChallengeOracle, srChallengeOracle, OracleInterface.toOracleSpec,
    challengeOracleInterfaceSR, OracleSpec.toPFunctor, OracleInterface.Response]
  infer_instance

/-- Define the query implementation for the state-restoration / (slow) Fiat-Shamir oracle (returns a
    challenge given messages up to that point) in terms of `ProbComp`.

  This is a randomness oracle: it simply calls the `selectElem` method inherited from the
  `SampleableType` instance on the challenge types. We may then augment this with `withCaching` to
  obtain a function-like implementation (caches and replays previous queries).

  For implementation with caching, we add `withCaching`.

  For implementation where the whole function is sampled ahead of time, and we answer with that
  function, see `srChallengeQueryImpl'`.
-/
@[reducible, inline, specialize, simp]
def srChallengeQueryImpl {Statement : Type} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)] :
    QueryImpl (srChallengeOracle Statement pSpec) ProbComp :=
  fun q => $ᵗ (pSpec.Challenge q.1)

/-- Alternate version of query implementation that takes in a cached function `f` and returns
  the result and the updated function.

  TODO: upstream this as a more general construction in VCVio -/
@[reducible, inline, specialize, simp]
def srChallengeQueryImpl' {Statement : Type} {pSpec : ProtocolSpec n}
    [∀ i, SampleableType (pSpec.Challenge i)] :
    QueryImpl (srChallengeOracle Statement pSpec)
      (StateT (QueryImpl (srChallengeOracle Statement pSpec) Id) ProbComp)
    :=
  fun | ⟨i, t⟩ => fun f => pure (f ⟨i, t⟩, f)

alias fsChallengeQueryImpl' := srChallengeQueryImpl'

namespace MessagesUpTo

/-- Auxiliary function for deriving the transcript up to round `k` from the (full) messages, via
  querying the state-restoration / Fiat-Shamir oracle for the challenges.

  This is used to define `deriveTranscriptFS`. -/
def deriveTranscriptSRAux {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (stmt : StmtIn) (k : Fin (n + 1)) (messages : pSpec.MessagesUpTo k)
    (j : Fin (k + 1)) :
    OracleComp (oSpec + fsChallengeOracle StmtIn pSpec)
      (pSpec.Transcript (j.castLE (by omega))) := do
  Fin.induction (n := k)
    (pure (fun i => i.elim0))
    (fun i ih => do
      let prevTranscript ← ih
      match hDir : pSpec.dir (i.castLE (by omega)) with
      | .V_to_P =>
        let challenge : pSpec.Challenge ⟨i.castLE (by omega), hDir⟩ ←
          query (spec := fsChallengeOracle _ _) ⟨⟨i.castLE (by omega), hDir⟩,
            (stmt, messages.take i.castSucc)⟩
        return prevTranscript.concat challenge
      | .P_to_V => return prevTranscript.concat (messages ⟨i, hDir⟩))
    j

/-- Derive the transcript up to round `k` from the (full) messages, via querying the
    state-restoration / Fiat-Shamir oracle for the challenges. -/
def deriveTranscriptSR {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (stmt : StmtIn) (k : Fin (n + 1)) (messages : pSpec.MessagesUpTo k) :
    OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) (pSpec.Transcript k) := do
  deriveTranscriptSRAux stmt k messages (Fin.last k)

alias deriveTranscriptFS := deriveTranscriptSR

end MessagesUpTo

namespace Messages

/-- Derive the transcript up to round `k` from the (full) messages, via querying the
    state-restoration / Fiat-Shamir oracle for the challenges. -/
def deriveTranscriptSR {ι : Type} {oSpec : OracleSpec ι} {StmtIn : Type}
    (stmt : StmtIn) (messages : pSpec.Messages) :
    OracleComp (oSpec + fsChallengeOracle StmtIn pSpec) pSpec.FullTranscript := do
  MessagesUpTo.deriveTranscriptSR stmt (Fin.last n) messages

alias deriveTranscriptFS := deriveTranscriptSR

end Messages

end ProtocolSpec

-- -- Notation for the type signature of an interactive protocol
-- notation "𝒫——⟦" term "⟧⟶𝒱" => (Direction.P_to_V, term)
-- notation "𝒫⟵⟦" term "⟧——𝒱" => (Direction.V_to_P, term)

-- -- Test notation
-- def pSpecNotationTest : ProtocolSpec 2 :=
--   ![ 𝒫——⟦ Polynomial (ZMod 101) ⟧⟶𝒱,
--      𝒫⟵⟦ ZMod 101 ⟧——𝒱]
