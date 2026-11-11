/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.ProverTransform

/-!
# Duplex-sponge Fiat–Shamir: honest end-to-end run under `D2SQuery`

The honest salted DSFS prover (`Prover.runToRoundDSFSSalted`) runs first, then the honest salted
DSFS verifier (`Verifier.duplexSpongeFiatShamirSalted`). Both run against one shared `D2SQuery`
simulator state, as in the CO25 §5.8 hybrids. The simulator programs every recognised challenge
boundary from a frozen function `g`.

For every configuration in the grid, the checks assert the following:
- **Agreement:** the verifier accepts and derives exactly the challenges the prover received.
- **Boundary recovery:** `g` is queried once per round by each party (`2k` calls in all), and both
  parties use the same keys. The key of challenge round `c` is the honest
  `(c, 𝕩, τ, α̂_1, …, α̂_c)`; `BackTrack` recovered every boundary with the right labels.
- **Programming:** the challenges are the programmed `g` answers.
- **Simulator consistency:** the simulated `p` is a function, and the online index `tr_∇.p` holds
  the same pairs as the index rebuilt from the whole trace (StdTrace's view).
- **Capacity freshness:** on the trace with exact repeats removed, no answer capacity repeats an
  earlier query or answer capacity, nor its own query capacity. This is the `E_dup` condition of
  Definition 5.7 for a trace without `p⁻¹` entries.

The grid has sponge shapes `(N, R) ∈ {(3, 1), (5, 2), (6, 4)}`, `k ∈ {1, 2, 3}` rounds, four
message/challenge length profiles (up to 5 units, so several rate blocks per action), and salt
lengths `δ ∈ {0, …, 4}` (covering `δ = 0` and `R ∤ δ`).

Messages are bits encoded as `n` copies of `0` or `1`, so only two of the `256ⁿ` encoded vectors
are in the image of the codec. `D2SQuery` decides `α̂ ∈ Im(φ)` by enumerating the message type, so
a small message type keeps the run executable.
-/

open OracleComp OracleSpec ProtocolSpec DuplexSpongeFS DuplexSpongeFS.ProverTransform
open DuplexSpongeFS.DSTraceStorage

namespace ArkLibTest.HonestEndToEnd

/-- Encoded length of transcript position `i`: entry `i / 2` of `msz` (messages, even `i`) or of
`csz` (challenges, odd `i`), at least `1`. -/
def roundSize (msz csz : List Nat) (i : Nat) : Nat :=
  max 1 (if i % 2 = 0 then msz.getD (i / 2) 1 else csz.getD (i / 2) 1)

/-- `k` rounds of a one-bit prover message followed by a byte-vector challenge. -/
def spec (k : Nat) (msz csz : List Nat) : ProtocolSpec (2 * k) where
  dir i := if i.val % 2 = 0 then .P_to_V else .V_to_P
  «Type» i := if i.val % 2 = 0 then Bool else Vector UInt8 (roundSize msz csz i.val)

/-- Bytes are a finite, inhabited type with decidable equality. -/
instance : VCVCompatible UInt8 where

variable {k : Nat} {msz csz : List Nat}

lemma even_of_msg (i : (spec k msz csz).MessageIdx) : i.1.val % 2 = 0 := by
  by_contra h; have := i.2; simp [spec, h] at this

lemma odd_of_chal (i : (spec k msz csz).ChallengeIdx) : i.1.val % 2 ≠ 0 := by
  intro h; have := i.2; simp [spec, h] at this

lemma msgType (i : (spec k msz csz).MessageIdx) : (spec k msz csz).Message i = Bool := by
  simp [ProtocolSpec.Message, spec, even_of_msg i]

lemma chalType (i : (spec k msz csz).ChallengeIdx) :
    (spec k msz csz).Challenge i = Vector UInt8 (roundSize msz csz i.1.val) := by
  simp [ProtocolSpec.Challenge, spec, odd_of_chal i]

instance instMsgFintype : ∀ i, Fintype ((spec k msz csz).Message i) := fun i =>
  (msgType i) ▸ inferInstanceAs (Fintype Bool)

instance instMsgDecEq : ∀ i, DecidableEq ((spec k msz csz).Message i) := fun i =>
  (msgType i) ▸ inferInstanceAs (DecidableEq Bool)

instance instChallenge (i : (spec k msz csz).ChallengeIdx) :
    VCVCompatible ((spec k msz csz).Challenge i) :=
  (chalType i) ▸ inferInstanceAs (VCVCompatible (Vector UInt8 (roundSize msz csz i.1.val)))

/-- Encoding of a bit as `n` copies of `0` or `1`. -/
def encodeBit (n : Nat) (b : Bool) : Vector UInt8 n := Vector.replicate n (if b then 1 else 0)

instance instCodec : Codec (spec k msz csz) UInt8 where
  messageSize i := roundSize msz csz i.1.val
  challengeSize i := roundSize msz csz i.1.val
  encode i m := encodeBit _ (cast (msgType i) m)
  encode_injective i a b h := by
    have hpos : 0 < roundSize msz csz i.1.val := by simp [roundSize]
    have h0 := congrArg (fun v : Vector UInt8 (roundSize msz csz i.1.val) => v[0]'hpos) h
    simp only [encodeBit, Vector.getElem_replicate] at h0
    have : cast (msgType i) a = cast (msgType i) b := by
      cases ha : cast (msgType i) a <;> cases hb : cast (msgType i) b <;>
        simp_all (config := {decide := true})
    exact (cast_inj (msgType i)).mp this
  decode i v := cast (chalType i).symm v
  decodingBias _ := 1
  decode_isBiased _ := PMF.tvDist_le_one _ _
  decode_surjective i c := ⟨cast (chalType i) c, by simp⟩

/-- The bit of a message. -/
def bitOf {i : (spec k msz csz).MessageIdx} (m : (spec k msz csz).Message i) : Bool :=
  cast (msgType i) m

/-- The bytes of a challenge. -/
def bytesOf {i : (spec k msz csz).ChallengeIdx} (c : (spec k msz csz).Challenge i) : List UInt8 :=
  (cast (chalType i) c).toList

/-- The honest bit after the challenge bytes `chals`. -/
def honestBit (chals : List UInt8) : Bool := (chals.foldl (· + ·) chals.length.toUInt8) % 2 == 1

/-- Honest prover. Its state is the list of challenge bytes it has received. -/
def prover : Prover []ₒ UInt8 Unit Unit Unit (spec k msz csz) where
  PrvState _ := List UInt8
  input _ := []
  sendMessage i st := pure (cast (msgType i).symm (honestBit st), st)
  receiveChallenge _ st := pure fun c => st ++ bytesOf c
  output _ := pure ((), ())

/-- The entry of a full transcript at a message position, as a bit. -/
def trBit (tr : (spec k msz csz).FullTranscript) (j : Fin (2 * k)) (h : j.val % 2 = 0) : Bool :=
  cast (by simp [spec, h]) (tr j)

/-- The entry of a full transcript at a challenge position, as bytes. -/
def trBytes (tr : (spec k msz csz).FullTranscript) (j : Fin (2 * k)) : List UInt8 :=
  if h : j.val % 2 = 0 then []
  else (cast (show (spec k msz csz).«Type» j = Vector UInt8 (roundSize msz csz j.val) by
    simp [spec, h]) (tr j)).toList

/-- Honest verifier: accepts iff every message is the honest bit for the challenges before it,
and outputs all challenge bytes. -/
def verifier : Verifier []ₒ UInt8 (List UInt8) (spec k msz csz) where
  verify _ tr := do
    let idxs := List.finRange (2 * k)
    let chalsBefore : Nat → List UInt8 := fun m =>
      (idxs.filter fun i => i.val < m).flatMap (trBytes tr)
    for i in idxs do
      if h : i.val % 2 = 0 then
        guard (trBit tr i h = honestBit (chalsBefore i.val))
    return chalsBefore (2 * k)


/-! ### Harness -/

/-- The encoded messages of a `g`-query key, flattened in round order. -/
def flatMsgs (i : Fin (2 * k + 1))
    (f : (spec k msz csz).EncodedMessagesBefore UInt8 i) : List UInt8 :=
  (List.finRange (2 * k)).flatMap fun j =>
    if hj : j.val % 2 = 0 ∧ j.val < i.val then
      (f ⟨⟨j, by simp [spec, hj.1]⟩, hj.2⟩).toList
    else []

/-- The encoded prover messages of transcript positions before `i`, flattened in round order. -/
def flatProof (msgs : (spec k msz csz).Messages) (i : Nat) : List UInt8 :=
  (List.finRange (2 * k)).flatMap fun j =>
    if hj : j.val % 2 = 0 ∧ j.val < i then
      (encodeBit (roundSize msz csz j.val) (bitOf (msgs ⟨j, by simp [spec, hj.1]⟩))).toList
    else []

/-- A logged `g` query: transcript position of the challenge, statement, salt, messages. -/
abbrev GKey := Nat × UInt8 × List UInt8 × List UInt8

/-- Frozen `g`: a deterministic function of the key. -/
def gAnswer (key : GKey) (len : Nat) : Vector UInt8 len :=
  let seed := (key.2.2.1 ++ key.2.2.2).foldl (fun a b => a * 31 + b) (key.1.toUInt8 * 7 + key.2.1)
  Vector.ofFn fun j => seed + 3 * j.val.toUInt8 + 1

/-- Sampler state: a counter for `𝒰(Σ)` draws, and the `g` log. -/
abbrev M := OptionT (StateM (Nat × List GKey))

/-- Observable outcome of one prover-then-verifier run. -/
structure Outcome where
  proverChallenges : List UInt8
  verifierOutput : Option (List UInt8)
  encodedPrefixes : List (List UInt8)
  gLog : List GKey
  pFunctional : Bool
  onlineIndexIsOffline : Bool
  capacitiesFresh : Bool

section Run

variable [SpongeSize]

/-- Full DSFS oracle spec with no ambient oracle. -/
abbrev Wide := []ₒ + duplexSpongeChallengeOracle UInt8 UInt8

/-- Capacity freshness of a deduplicated trace without `p⁻¹` entries. An entry is a query
capacity (`none` for `h`) and an answer capacity. -/
def capsFresh (es : List (Option (List UInt8) × List UInt8)) : Bool :=
  (List.range es.length).all fun j =>
    let (qj, aj) := es.getD j (none, [])
    let prior := (es.take j).flatMap fun (q, a) => q.toList ++ [a]
    !(prior.contains aj) && qj != some aj

/-- Run the honest salted DSFS prover and then the verifier under one `D2SQuery` state. -/
def run (k : Nat) (msz csz : List Nat) (δ : Nat) : Option Outcome :=
  let St := CanonicalSpongeState UInt8
  let TH := ListBacked.ListTraceTable UInt8 (Vector UInt8 SpongeSize.C)
  let TP := ListBacked.ListTraceTable St St
  let salt : Vector UInt8 δ := Vector.ofFn fun j => j.val.toUInt8 * 13 + 1
  let stmt : UInt8 := 42
  let gImpl : QueryImpl (gSpec (U := UInt8) UInt8 (spec k msz csz) δ) M := fun q => do
    let ⟨i, (x, τ, f)⟩ := q
    let key : GKey := (i.1.val, x, τ.toList, flatMsgs i.1.castSucc f)
    modify fun (c, log) => (c, log ++ [key])
    pure (gAnswer key _)
  let auxImpl : QueryImpl ((Unit →ₒ UInt8) + unifSpec) M := fun
    | .inl () => do
        let (c, log) ← get
        set (c + 1, log)
        pure (100 + c).toUInt8
    | .inr n => pure (0 : Fin (n + 1))
  let simImpl : QueryImpl Wide (StateT (D2SQueryState (δ := δ) (T_H := TH) (T_P := TP)
      (StmtIn := UInt8) (pSpec := spec k msz csz) (U := UInt8)) M) := fun
    | .inl q => PEmpty.elim q
    | .inr q => d2sQueryImpl (δ := δ) (T_H := TH) (T_P := TP) (StmtIn := UInt8)
        (pSpec := spec k msz csz) (U := UInt8) gImpl auxImpl q
  let comp := do
    let (msgs, _, chals) ← simulateQ simImpl
      (Prover.runToRoundDSFSSalted (U := UInt8) (pSpec := spec k msz csz) salt
        (Fin.last (2 * k)) stmt prover [])
    let proof : DSSaltedProof (spec k msz csz) UInt8 δ := (salt, msgs)
    let out ← simulateQ simImpl
      ((Verifier.duplexSpongeFiatShamirSalted (U := UInt8) δ verifier).verify stmt
        (fun i => match i with | ⟨0, _⟩ => proof)).run
    pure (msgs, chals, out)
  match (comp.run default).run.run (0, []) with
  | (some ((msgs, chals, out), st), (_, gLog)) =>
      let fwd : List (St × St) := st.trace.filterMap fun
        | ⟨.inr (.inl a), b⟩ => some (a, b)
        | _ => none
      let online := TraceTableOps.entries (V := St) st.trΔ.p
      let offline := TraceTableOps.entries (V := St)
        (TraceNabla.ofQueryLogForwardOnly (T_H := TH) (T_P := TP) st.trace).p
      let ents : List (Option (List UInt8) × List UInt8) := (st.trace.map fun
        | ⟨.inl _, c⟩ => (none, c.toList)
        | ⟨.inr (.inl a), b⟩ =>
            (some (CanonicalSpongeState.capacitySegment a).toList,
              (CanonicalSpongeState.capacitySegment b).toList)
        | ⟨.inr (.inr b), a⟩ =>
            (some (CanonicalSpongeState.capacitySegment b).toList,
              (CanonicalSpongeState.capacitySegment a).toList)).dedup
      let noInverse := st.trace.all fun
        | ⟨.inr (.inr _), _⟩ => false
        | _ => true
      some
        { proverChallenges := chals
          verifierOutput := out
          encodedPrefixes := (List.range k).map fun c => flatProof msgs (2 * c + 1)
          gLog := gLog
          pFunctional := fwd.all fun (a, b) => fwd.all fun (a', b') => a ≠ a' || b == b'
          onlineIndexIsOffline := online.all (· ∈ offline) && offline.all (· ∈ online)
          capacitiesFresh := noInverse && capsFresh ents }
  | (none, _) => none

/-- All end-to-end checks for one configuration. -/
def honest (k : Nat) (msz csz : List Nat) (δ : Nat) : Bool :=
  match run k msz csz δ with
  | none => false
  | some o =>
      let salt : List UInt8 := (List.range δ).map fun j => j.toUInt8 * 13 + 1
      let keys : List GKey := (List.range k).map fun c =>
        (2 * c + 1, 42, salt, o.encodedPrefixes.getD c [])
      let programmed := keys.flatMap fun key =>
        (gAnswer key (roundSize msz csz key.1)).toList
      o.verifierOutput == some o.proverChallenges &&
        o.gLog == keys ++ keys &&
        o.proverChallenges == programmed &&
        o.pFunctional && o.onlineIndexIsOffline && o.capacitiesFresh

end Run

/-! ### Grid -/

/-- Width 3, rate 1. -/
@[instance_reducible] def sz31 : SpongeSize := { N := 3, R := 1 }
/-- Width 5, rate 2. -/
@[instance_reducible] def sz52 : SpongeSize := { N := 5, R := 2 }
/-- Width 6, rate 4. -/
@[instance_reducible] def sz64 : SpongeSize := { N := 6, R := 4 }

/-- Message and challenge length profiles (one entry per round), up to `5` units per action. -/
def lengthProfiles : List (List Nat × List Nat) :=
  [([1, 1, 1], [1, 1, 1]), ([2, 5, 3], [5, 1, 4]), ([4, 2, 1], [3, 5, 2]),
    ([5, 4, 5], [2, 3, 5])]

/-- The configurations `(k, msz, csz, δ)` of the grid that fail for the sponge shape `sz`. -/
def gridFailures (sz : SpongeSize) : List (Nat × List Nat × List Nat × Nat) :=
  letI := sz
  [1, 2, 3].flatMap fun k => lengthProfiles.flatMap fun (msz, csz) =>
    (List.range 5).filterMap fun δ =>
      if honest k msz csz δ then none else some (k, msz, csz, δ)

/-- info: [] -/
#guard_msgs in
#eval gridFailures sz31

/-- info: [] -/
#guard_msgs in
#eval gridFailures sz52

/-- info: [] -/
#guard_msgs in
#eval gridFailures sz64

/-! ### Worked instance: width 6, rate 4, `k = 2`, `δ = 1`, `ℓ_P = (2, 5)`, `ℓ_V = (5, 1)`

The salt and `α̂_1` share the first rate block, `α̂_2` spans two blocks, and the first challenge
spans two blocks, so its second block is answered from `Cache_p`. -/

/-- The transcript positions of the `g` keys of the worked instance: challenge rounds 1 and 2,
once for the prover and once for the verifier. -/
def workedKeyPositions : Option (List Nat) :=
  letI := sz64
  (run 2 [2, 5] [5, 1] 1).map (·.gLog.map (·.1))

/-- info: some [1, 3, 1, 3] -/
#guard_msgs in
#eval workedKeyPositions

end ArkLibTest.HonestEndToEnd
