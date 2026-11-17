/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/

import ArkLib.NonInteractiveArgument.FiatShamir.Protocol.DuplexSponge
import ArkLib.NonInteractiveArgument.FiatShamir.Protocol.Canonical
import VCVio.OracleComp.EvalDist.DiscreteTVDistBind
import ArkLib.OracleReduction.Execution.Transcript

/-!
# Protocol-facing duplex-sponge execution regressions

A salt of seven and a permutation that increments each byte give verifier message eight.
The inverse decrements bytes, so the expected NARG string also checks forward-query routing.
-/

open OracleComp OracleSpec ProtocolSpec

namespace ProtocolDuplexSpongeRegression

instance : SpongeSize where
  N := 4
  R := 2

instance : VCVCompatible UInt8 where
  default := 0

abbrev spec : ProtocolSpec 2 :=
  ⟨fun i => if i.val = 0 then .V_to_P else .P_to_V, fun _ => Vector UInt8 1⟩

instance : Codec spec UInt8 where
  proverMessageSize := fun _ => 1
  verifierMessageSize := fun _ => 1
  encode := fun _ x => x
  encode_injective := fun _ => Function.injective_id
  decode := fun _ x => x
  decodingBias := fun _ => 0
  decode_isBiased := by
    intro i hEncoded hVerifierMessage
    classical
    refine le_of_eq (discreteTVDist.eq_zero_of_evalDistEq (.of_forall_prEvent_eq fun p => ?_))
    erw [id_map', @SampleableType.prEvent_uniformSample _ hVerifierMessage
      (inferInstanceAs (Fintype (Vector UInt8 1))) p _,
      @SampleableType.prEvent_uniformSample (Vector UInt8 1) hEncoded _ p
        (Classical.decPred _)]
  decode_surjective := fun _ => Function.surjective_id

abbrev ambient : OracleSpec Unit := Unit →ₒ Vector UInt8 1

/-- A valid witness echoes the verifier message; an invalid witness sends zero. -/
def protocol : InteractiveProtocol ambient Unit Bool spec where
  prover :=
    { PrvState := fun _ => Bool × Vector UInt8 1
      input := fun (_, invalid) => (invalid, #v[0])
      sendMessage := fun _ state => pure (state.2, state)
      receiveChallenge := fun _ state =>
        pure (fun message => (state.1, if state.1 then #v[0] else message)) }
  verifier := ⟨fun _ transcript => pure (transcript 0 == transcript 1)⟩

/-- The wire format is exactly two bytes: salt followed by the only prover message. -/
def payloadEquiv : DSFSTypedNARGString spec UInt8 1 ≃ Vector UInt8 2 where
  toFun p := #v[p.1[0], (p.2 ⟨1, rfl⟩)[0]]
  invFun v := (#v[v[0]], fun _ => #v[v[1]])
  left_inv p := by
    apply Prod.ext
    · ext i h
      have : i = 0 := by omega
      subst i
      rfl
    · funext i
      have hi : i = ⟨1, rfl⟩ := by
        apply Subtype.ext
        rcases i with ⟨i, hi⟩
        fin_cases i
        · cases hi
        · rfl
      subst i
      ext j h
      have : j = 0 := by omega
      subst j
      rfl
  right_inv v := by
    ext i h
    have : i = 0 ∨ i = 1 := by omega
    rcases this with rfl | rfl <;> rfl

def serializer := (Serializer.vector 2).ofEquiv payloadEquiv

/-- Basic FS uses exactly the same canonical byte format as DSFS. -/
def basicArgument := protocol.fiatShamir (U := UInt8) 1 serializer
  (query (spec := ambient) ())

def basicImpl : QueryImpl (ambient + canonicalFSOracle Unit spec UInt8 1) Id :=
  fun q => match q with
  | .inl _ => pure #v[7]
  | .inr _ => pure #v[8]

-- The public basic-FS generator returns bytes; verification parses before any oracle query.
run_cmd do
  let bytes := Id.run (simulateQ basicImpl (basicArgument.prover () false))
  unless bytes == ByteArray.mk #[7, 8] do
    throwError "Basic FS returned the wrong byte encoding"
  unless Id.run (simulateQ basicImpl (basicArgument.verifier () bytes)) do
    throwError "Basic FS rejected its honest serialized NARG string"
  if Id.run (simulateQ basicImpl (basicArgument.verifier () (ByteArray.mk #[7, 0]))) then
    throwError "Basic FS accepted a forged response"
  for malformed in [ByteArray.empty, ByteArray.mk #[7], ByteArray.mk #[7, 8, 0]] do
    let counter : QueryImpl (ambient + canonicalFSOracle Unit spec UInt8 1)
        (StateT Nat Id) := fun q count => pure (Id.run (basicImpl q), count + 1)
    let result := Id.run ((simulateQ counter (basicArgument.verifier () malformed)).run 0)
    unless result == (false, 0) do
      throwError "Malformed basic-FS bytes must reject before querying any oracle"

def argument := protocol.duplexSpongeFiatShamir 1 serializer (ambient.query ())

/-- The two permutation directions deliberately differ and are mutual inverses. -/
def oracleImpl : QueryImpl (ambient + duplexSpongeOracle Unit UInt8) Id :=
  fun key => match key with
    | .inl _ => pure #v[7]
    | .inr (.inl _) => pure (Vector.replicate SpongeSize.C 0)
    | .inr (.inr (.inl state)) => pure (state.map (· + 1))
    | .inr (.inr (.inr state)) => pure (state.map (· - 1))

def run {α : Type} (comp : OracleComp
    (ambient + duplexSpongeOracle Unit UInt8) α) : α :=
  Id.run (simulateQ oracleImpl comp)

-- The NARG string contains the public salt and verifier-message-dependent prover message only.
run_cmd do
  let actual := run (argument.prover () false)
  unless actual == ByteArray.mk #[7, 8] do
    throwError "DSFS must retain the salt and use the forward permutation for its response"
  unless run (argument.run () false) do
    throwError "DSFS rejected the honest response"
  if run (argument.run () true) then
    throwError "DSFS accepted the invalid witness"
  if run (argument.verifier () (ByteArray.mk #[7, 0])) then
    throwError "DSFS accepted the forged NARG string"

/-- The forward interface has no inverse-permutation slot. -/
def forwardImpl : QueryImpl (ambient + duplexSpongeForwardOracle Unit UInt8) Id :=
  fun key => match key with
    | .inl _ => pure #v[7]
    | .inr (.inl _) => pure (Vector.replicate SpongeSize.C 0)
    | .inr (.inr state) => pure (state.map (· + 1))

-- Narrow verification agrees with the wide verifier on accepting and rejecting NARG strings.
run_cmd do
  let narrowAccept := Id.run (simulateQ forwardImpl
    (protocol.verifier.duplexSpongeFiatShamirForward 1 serializer () (ByteArray.mk #[7, 8])))
  unless narrowAccept == run (argument.verifier () (ByteArray.mk #[7, 8])) do
    throwError "Forward-only and wide DSFS verification disagree on the honest NARG string"
  let narrowReject := Id.run (simulateQ forwardImpl
    (protocol.verifier.duplexSpongeFiatShamirForward 1 serializer () (ByteArray.mk #[7, 0])))
  unless narrowReject == run (argument.verifier () (ByteArray.mk #[7, 0])) do
    throwError "Forward-only and wide DSFS verification disagree on the forged NARG string"

-- Reject empty, truncated, and extended inputs, including an honest encoding plus garbage.
run_cmd do
  for bytes in [ByteArray.empty, ByteArray.mk #[7], ByteArray.mk #[7, 8, 0]] do
    let counter : QueryImpl (ambient + duplexSpongeOracle Unit UInt8) (StateT Nat Id) :=
      fun q n => pure (Id.run (oracleImpl q), n + 1)
    let rejectedBeforeQuery := Id.run ((simulateQ counter
      (argument.verifier () bytes)).run 0)
    unless rejectedBeforeQuery == (false, 0) do
      throwError "Malformed DSFS inputs must reject before querying any oracle"

-- Transcript instrumentation executes both directions and retains the same private state.
run_cmd do
  let result : spec.Transcript (Fin.last 2) ×
      (spec.Transcript (Fin.last 2) × (Bool × Vector UInt8 1)) :=
    Id.run (simulateQ (fun q => match q with
      | .inl _ => pure #v[7]
      | .inr _ => pure #v[8])
    (protocol.prover.toReductionProver.withTranscript.runToRound (Fin.last 2) () false))
  let sent : Vector UInt8 1 := result.1 ⟨1, by decide⟩
  let received : Vector UInt8 1 := result.1 ⟨0, by decide⟩
  let recordedSent : Vector UInt8 1 := result.2.1 ⟨1, by decide⟩
  let recordedReceived : Vector UInt8 1 := result.2.1 ⟨0, by decide⟩
  unless sent == #v[8] && received == #v[8] && recordedSent == #v[8] &&
      recordedReceived == #v[8] && result.2.2 == (false, #v[8]) do
    throwError "Transcript instrumentation changed the messages or final private state"

end ProtocolDuplexSpongeRegression
