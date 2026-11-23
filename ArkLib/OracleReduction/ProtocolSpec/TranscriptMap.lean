/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.OracleReduction.ProtocolSpec.ScalarRound
public import ArkLib.OracleReduction.ProtocolSpec.SeqCompose

/-!
# Slotwise transcript decoding

A transcript decoder converts the slots of one protocol wire to another without changing their
directions. It acts on prefixes as well as complete transcripts and preserves the challenge types
up to bijection.
-/

@[expose] public section

namespace ProtocolSpec

/-- A slotwise transcript decoder between wires with the same round directions and
bijectively related challenge types. Prover messages need not decode bijectively. -/
structure TranscriptMap {n : ℕ} (wireSpec decodedSpec : ProtocolSpec n) where
  /-- Decoding does not change which party sends a slot. -/
  dir_eq : ∀ i, wireSpec.dir i = decodedSpec.dir i
  /-- Decode one prover message or challenge. -/
  decodeSlot : ∀ i, wireSpec.«Type» i → decodedSpec.«Type» i
  /-- The decoder is bijective at each verifier challenge, preserving uniform sampling. -/
  challenge_bijective : ∀ i : wireSpec.ChallengeIdx, Function.Bijective (decodeSlot i.1)

namespace TranscriptMap

variable {n : ℕ} {wireSpec decodedSpec : ProtocolSpec n}
  (decoder : TranscriptMap wireSpec decodedSpec)

/-- Regard the same challenge slot as an index in the decoded protocol. -/
def challengeIdx (i : wireSpec.ChallengeIdx) : decodedSpec.ChallengeIdx :=
  ⟨i.1, (decoder.dir_eq i.1).symm.trans i.2⟩

/-- Both wires have exactly the same challenge slots. -/
def challengeIdxEquiv : wireSpec.ChallengeIdx ≃ decodedSpec.ChallengeIdx where
  toFun := decoder.challengeIdx
  invFun i := ⟨i.1, (decoder.dir_eq i.1).trans i.2⟩
  left_inv i := Subtype.ext (rfl : i.1 = i.1)
  right_inv i := Subtype.ext (rfl : i.1 = i.1)

/-- Decode a prefix, using only its existing slots. -/
def decodePrefix {k : Fin (n + 1)} (wirePrefix : wireSpec.Transcript k) :
    decodedSpec.Transcript k :=
  fun j => decoder.decodeSlot (j.castLE k.is_le) (wirePrefix j)

/-- Decode a completed transcript. -/
def decodeFull (transcript : wireSpec.FullTranscript) : decodedSpec.FullTranscript :=
  decoder.decodePrefix (k := Fin.last n) transcript

@[simp] theorem decodeFull_apply (transcript : wireSpec.FullTranscript) (i : Fin n) :
    decoder.decodeFull transcript i = decoder.decodeSlot i (transcript i) := rfl

@[simp] theorem decodePrefix_default :
    decoder.decodePrefix (default : wireSpec.Transcript 0) = default := Subsingleton.elim _ _

/-- Decoding an extended prefix appends the decoded slot to the decoded prefix. -/
@[simp] theorem decodePrefix_concat {i : Fin n} (wirePrefix : wireSpec.Transcript i.castSucc)
    (value : wireSpec.«Type» i) :
    decoder.decodePrefix (wirePrefix.concat value) =
      (decoder.decodePrefix wirePrefix).concat (decoder.decodeSlot i value) := by
  funext j
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [decodePrefix, Transcript.concat_last]
    rfl
  · simp only [decodePrefix, Transcript.concat_castSucc]
    rfl

/-! ## Composition -/

/-- Keep all slots and challenges unchanged. -/
def refl (pSpec : ProtocolSpec n) : TranscriptMap pSpec pSpec where
  dir_eq _ := rfl
  decodeSlot _ := id
  challenge_bijective _ := Function.bijective_id

@[simp] theorem decodeFull_refl (pSpec : ProtocolSpec n) (tr : pSpec.FullTranscript) :
    (refl pSpec).decodeFull tr = tr := rfl

/-- Decode a prover message followed by a verifier challenge, leaving the challenge unchanged. -/
def proverThenChallenge {WireMessage DecodedMessage Challenge : Type}
    (decodeMessage : WireMessage → DecodedMessage) :
    TranscriptMap
      (CoordinateWise.ScalarRound.pSpecScalar WireMessage Challenge)
      (CoordinateWise.ScalarRound.pSpecScalar DecodedMessage Challenge) where
  dir_eq _ := rfl
  decodeSlot
    | ⟨0, _⟩ => decodeMessage
    | ⟨1, _⟩ => id
  challenge_bijective := by
    rintro ⟨i, hi⟩
    fin_cases i
    · cases hi
    · exact Function.bijective_id

private def castSlot {A B A' B' : Type} (hWire : A' = A) (hDecoded : B' = B)
    (decode : A → B) : A' → B' :=
  fun value => cast hDecoded.symm (decode (cast hWire value))

private theorem castSlot_bijective {A B A' B' : Type} (hWire : A' = A) (hDecoded : B' = B)
    {decode : A → B} (hDecode : Function.Bijective decode) :
    Function.Bijective (castSlot hWire hDecoded decode) :=
  (cast_bijective hDecoded.symm).comp (hDecode.comp (cast_bijective hWire))

section Append

variable {k : ℕ} {wireSpec₂ decodedSpec₂ : ProtocolSpec k}

private def appendSlot (left : TranscriptMap wireSpec decodedSpec)
    (right : TranscriptMap wireSpec₂ decodedSpec₂) :
    ∀ j, (wireSpec ++ₚ wireSpec₂).«Type» j →
      (decodedSpec ++ₚ decodedSpec₂).«Type» j :=
  Fin.addCases
    (fun j => castSlot (append_Type_castAdd j) (append_Type_castAdd j) (left.decodeSlot j))
    (fun j => castSlot (append_Type_natAdd j) (append_Type_natAdd j) (right.decodeSlot j))

/-- Append two maps without changing which component decodes each slot. -/
@[no_expose]
def append (left : TranscriptMap wireSpec decodedSpec)
    (right : TranscriptMap wireSpec₂ decodedSpec₂) :
    TranscriptMap (wireSpec ++ₚ wireSpec₂) (decodedSpec ++ₚ decodedSpec₂) where
  dir_eq j := by
    induction j using Fin.addCases with
    | left j => simpa only [Fin.vappend_eq_append, Fin.append_left] using left.dir_eq j
    | right j => simpa only [Fin.vappend_eq_append, Fin.append_right] using right.dir_eq j
  decodeSlot := appendSlot left right
  challenge_bijective := by
    rintro ⟨j, hj⟩
    induction j using Fin.addCases with
    | left j =>
      simp only [appendSlot, Fin.addCases_left]
      have hChallenge : wireSpec.dir j = .V_to_P := by
        simpa only [Fin.vappend_eq_append, Fin.append_left] using hj
      exact castSlot_bijective _ _ (left.challenge_bijective ⟨j, hChallenge⟩)
    | right j =>
      simp only [appendSlot, Fin.addCases_right]
      have hChallenge : wireSpec₂.dir j = .V_to_P := by
        simpa only [Fin.vappend_eq_append, Fin.append_right] using hj
      exact castSlot_bijective _ _ (right.challenge_bijective ⟨j, hChallenge⟩)

/-- Decoding an appended transcript decodes its two parts independently. -/
theorem decodeFull_append (left : TranscriptMap wireSpec decodedSpec)
    (right : TranscriptMap wireSpec₂ decodedSpec₂)
    (transcript : (wireSpec ++ₚ wireSpec₂).FullTranscript) :
    (left.append right).decodeFull transcript =
      left.decodeFull transcript.fst ++ₜ right.decodeFull transcript.snd := by
  funext j
  induction j using Fin.addCases with
  | left j =>
    simp only [decodeFull_apply, append, appendSlot, Fin.addCases_left, FullTranscript.append,
      Fin.happend_left, FullTranscript.fst, castSlot]
    rfl
  | right j =>
    simp only [decodeFull_apply, append, appendSlot, Fin.addCases_right, FullTranscript.append,
      Fin.happend_right, FullTranscript.snd, castSlot]
    rfl

end Append

section Sequential

variable {k : ℕ} {len : Fin k → ℕ} {wireSpecs decodedSpecs : ∀ i, ProtocolSpec (len i)}
  (componentMap : ∀ i, TranscriptMap (wireSpecs i) (decodedSpecs i))

private def seqSlot (slot : Fin (Fin.vsum len)) :
    (ProtocolSpec.seqCompose wireSpecs).«Type» slot →
      (ProtocolSpec.seqCompose decodedSpecs).«Type» slot :=
  let componentSlot := Fin.finSum'FinEquiv'.symm slot
  have hSlot : Fin.embedSum componentSlot.1 componentSlot.2 = slot :=
    Fin.finSum'FinEquiv'.apply_symm_apply slot
  castSlot
    (by rw [← hSlot]; simp [ProtocolSpec.seqCompose])
    (by rw [← hSlot]; simp [ProtocolSpec.seqCompose])
    ((componentMap componentSlot.1).decodeSlot componentSlot.2)

private theorem seqSlot_embed (component : Fin k) (localSlot : Fin (len component)) :
    seqSlot componentMap (Fin.embedSum component localSlot) =
      castSlot (by simp [ProtocolSpec.seqCompose]) (by simp [ProtocolSpec.seqCompose])
        ((componentMap component).decodeSlot localSlot) := by
  unfold seqSlot
  have hSlot :
      Fin.finSum'FinEquiv'.symm (Fin.embedSum component localSlot) = ⟨component, localSlot⟩ :=
    Fin.finSum'FinEquiv'.symm_apply_apply ⟨component, localSlot⟩
  rw! (castMode := .all) [hSlot]
  rfl

/-- Decode each component of a sequential composition in place. -/
@[no_expose]
def seqCompose :
    TranscriptMap (ProtocolSpec.seqCompose wireSpecs) (ProtocolSpec.seqCompose decodedSpecs) where
  dir_eq j := by
    obtain ⟨⟨i, j⟩, rfl⟩ := Fin.finSum'FinEquiv'.surjective j
    simpa only [Fin.finSum'FinEquiv', Equiv.coe_fn_mk, ProtocolSpec.seqCompose_dir,
      Fin.vflatten_embedSum] using (componentMap i).dir_eq j
  decodeSlot := seqSlot componentMap
  challenge_bijective := by
    rintro ⟨j, hj⟩
    obtain ⟨⟨i, j⟩, rfl⟩ := Fin.finSum'FinEquiv'.surjective j
    change Function.Bijective (seqSlot componentMap (Fin.embedSum i j))
    rw [seqSlot_embed]
    have hChallenge : (wireSpecs i).dir j = .V_to_P := by
      simpa only [Fin.finSum'FinEquiv', Equiv.coe_fn_mk, ProtocolSpec.seqCompose_dir,
        Fin.vflatten_embedSum] using hj
    exact castSlot_bijective _ _ ((componentMap i).challenge_bijective ⟨j, hChallenge⟩)

/-- Decoding a complete sequence is equivalent to decoding each component transcript. -/
theorem decodeFull_seqCompose (transcript : (ProtocolSpec.seqCompose wireSpecs).FullTranscript) :
    (seqCompose componentMap).decodeFull transcript =
      FullTranscript.seqCompose
        (fun i => (componentMap i).decodeFull (transcript.component i)) := by
  funext j
  obtain ⟨⟨i, j⟩, rfl⟩ := Fin.finSum'FinEquiv'.surjective j
  simp only [Fin.finSum'FinEquiv', Equiv.coe_fn_mk, decodeFull_apply, seqCompose, seqSlot_embed,
    FullTranscript.seqCompose_embedSum, FullTranscript.component, castSlot]

end Sequential

end TranscriptMap

end ProtocolSpec
