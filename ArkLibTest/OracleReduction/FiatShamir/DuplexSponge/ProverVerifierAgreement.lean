/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs

/-!
# Duplex-sponge Fiat–Shamir: honest prover and verifier agree

These checks run the honest DSFS prover (`Prover.runToRoundDSFS{,Salted}`) and the honest DSFS
verifiers (`Verifier.duplexSpongeFiatShamir{,Salted}` and `runForwardVerifierWide`) against one
concrete oracle `(h, p, p⁻¹)`. The permutation `p` is not an involution, so a query sent to the
`p⁻¹` slot gives a different answer.

For every configuration in the grid, the checks assert the following:
- the prover and the verifier make the same `(h, p, p⁻¹)` queries, in the same order;
- neither of them queries `p⁻¹`;
- the challenges that the prover receives equal the challenges that the verifier derives;
- the verifier accepts the honest proof.

The grid covers the unsalted and salted variants, salt lengths `δ ∈ {0, …, 4}`, `k ∈ {1, 2, 3}`
rounds, and message and challenge lengths that span several rate blocks.
-/

open OracleComp OracleSpec ProtocolSpec

namespace DSFSAgreementTest

/-! ### A `k`-round alternating protocol over `UInt8` vectors -/

/-- Encoded length of round `i`: entry `i / 2` of `msz` for messages (even `i`) and of `csz` for
challenges (odd `i`). -/
def roundSize (msz csz : List Nat) (i : Nat) : Nat :=
  if i % 2 = 0 then msz.getD (i / 2) 1 else csz.getD (i / 2) 1

/-- `k` rounds of a prover message followed by a verifier challenge. -/
def spec (k : Nat) (msz csz : List Nat) : ProtocolSpec (2 * k) where
  dir i := if i.val % 2 = 0 then .P_to_V else .V_to_P
  «Type» i := Vector UInt8 (roundSize msz csz i.val)

/-- Bytes are a finite, inhabited type with decidable equality. -/
instance : VCVCompatible UInt8 where

variable {k : Nat} {msz csz : List Nat}

instance instCodec : Codec (spec k msz csz) UInt8 where
  messageSize i := roundSize msz csz i.1.val
  challengeSize i := roundSize msz csz i.1.val
  encode _ m := m
  encode_injective _ _ _ h := h
  decode _ v := v
  decodingBias _ := 1
  decode_isBiased _ := Codec.tvDist_uniformOn_map_le_one _
  decode_surjective _ c := ⟨c, rfl⟩

instance instChallenge (i : (spec k msz csz).ChallengeIdx) :
    VCVCompatible ((spec k msz csz).Challenge i) :=
  inferInstanceAs (VCVCompatible (Vector UInt8 (roundSize msz csz i.1.val)))

/-- Bytes of a transcript entry. -/
def entryBytes (tr : (spec k msz csz).FullTranscript) (i : Fin (2 * k)) : List UInt8 :=
  (show Vector UInt8 (roundSize msz csz i.val) from tr i).toList

/-- The honest message after the challenge bytes `chals`. It depends on every earlier challenge,
so a wrong challenge changes every later message. -/
def honestMessage (chals : List UInt8) (len : Nat) : Vector UInt8 len :=
  Vector.ofFn fun j => (chals.length.toUInt8 + 7 * j.val.toUInt8 + chals.foldl (· + ·) 3)

/-! ### Honest IP prover and verifier -/

/-- Honest prover. Its state is the list of challenge bytes it has received. -/
def prover : Prover []ₒ UInt8 Unit Unit Unit (spec k msz csz) where
  PrvState _ := List UInt8
  input _ := []
  sendMessage i st :=
    pure (show Vector UInt8 (roundSize msz csz i.1.val) from
      honestMessage st (roundSize msz csz i.1.val), st)
  receiveChallenge i st :=
    pure fun c => st ++ (show Vector UInt8 (roundSize msz csz i.1.val) from c).toList
  output _ := pure ((), ())

/-- Honest verifier. It accepts iff every message is the honest message for the challenges
before it, and then outputs all challenge bytes. -/
def verifier : Verifier []ₒ UInt8 (List UInt8) (spec k msz csz) where
  verify _ tr := do
    let idxs := List.finRange (2 * k)
    let chalsBefore : Nat → List UInt8 := fun m =>
      (idxs.filter fun i => i.val % 2 = 1 ∧ i.val < m).flatMap (entryBytes tr)
    for i in idxs do
      if i.val % 2 = 0 then
        guard (entryBytes tr i =
          (honestMessage (chalsBefore i.val) (roundSize msz csz i.val)).toList)
    return chalsBefore (2 * k)

/-! ### A concrete oracle `(h, p, p⁻¹)` with query logging -/

/-- Logged query: slot name and input bytes. -/
abbrev LogEntry := String × List UInt8

section Oracle

variable [SpongeSize]

/-- Full DSFS oracle spec with no ambient oracle. -/
abbrev Wide := []ₒ + duplexSpongeChallengeOracle UInt8 UInt8

/-- Round constant of the test permutation. -/
def roundConst (i : Nat) : UInt8 := (i + 1).toUInt8 * 17

/-- Test permutation: rotate left by one, then add a round constant. Not an involution. -/
def perm (s : CanonicalSpongeState UInt8) : CanonicalSpongeState UInt8 :=
  Vector.ofFn fun i => s[(i.val + 1) % SpongeSize.N]'(Nat.mod_lt _ i.pos) + roundConst i.val

/-- Inverse of `perm`. -/
def permInv (t : CanonicalSpongeState UInt8) : CanonicalSpongeState UInt8 :=
  Vector.ofFn fun i =>
    let j := (i.val + SpongeSize.N - 1) % SpongeSize.N
    t[j]'(Nat.mod_lt _ i.pos) - roundConst j

/-- Logging implementation of `(h, p, p⁻¹)`. -/
def impl : QueryImpl Wide (StateM (List LogEntry))
  | .inl q => nomatch q
  | .inr (.inl x) => do
      modify (· ++ [("h", [x])])
      pure (Vector.ofFn fun j => x + 31 * j.val.toUInt8 + 5)
  | .inr (.inr (.inl s)) => do modify (· ++ [("p", s.toList)]); pure (perm s)
  | .inr (.inr (.inr s)) => do modify (· ++ [("pinv", s.toList)]); pure (permInv s)

/-- Run a computation against the logging oracle. -/
def runLogged {α : Type} (oa : OracleComp Wide α) : α × List LogEntry :=
  (simulateQ impl oa).run []

end Oracle

/-! ### Agreement checks -/

/-- Common verdict: same query log, no `p⁻¹` query, same challenges, and acceptance. -/
def verdict (proverChals : List UInt8) (proverLog : List LogEntry)
    (verifierOut : Option (List UInt8)) (verifierLog : List LogEntry) : Bool :=
  proverLog == verifierLog &&
    proverLog.all (·.1 != "pinv") &&
    verifierOut == some proverChals

section Checks

variable [SpongeSize]

/-- Salted DSFS: the prover's run against the wide verifier and against
`runForwardVerifierWide`. -/
def saltedAgrees (k : Nat) (msz csz : List Nat) (δ : Nat) : Bool :=
  let salt : Vector UInt8 δ := Vector.ofFn fun j => j.val.toUInt8 * 13 + 1
  let stmt : UInt8 := 42
  let ((msgs, _, chals), pLog) := runLogged
    (Prover.runToRoundDSFSSalted (U := UInt8) (pSpec := spec k msz csz) salt
      (Fin.last (2 * k)) stmt prover [])
  let proof : DSSaltedProof (spec k msz csz) UInt8 δ := (salt, msgs)
  let (out, vLog) := runLogged
    ((Verifier.duplexSpongeFiatShamirSalted (U := UInt8) δ verifier).verify stmt
      (fun i => match i with | ⟨0, _⟩ => proof)).run
  let (outFwd, vLogFwd) := runLogged (runForwardVerifierWide δ verifier stmt proof)
  verdict chals pLog out vLog && verdict chals pLog outFwd vLogFwd

/-- Unsalted DSFS: the prover's run against the wide verifier. -/
def unsaltedAgrees (k : Nat) (msz csz : List Nat) : Bool :=
  let stmt : UInt8 := 42
  let ((msgs, _, chals), pLog) := runLogged
    (Prover.runToRoundDSFS (U := UInt8) (pSpec := spec k msz csz)
      (Fin.last (2 * k)) stmt prover [])
  let (out, vLog) := runLogged
    ((Verifier.duplexSpongeFiatShamir (U := UInt8) verifier).verify stmt
      (fun i => match i with | ⟨0, _⟩ => msgs)).run
  verdict chals pLog out vLog

end Checks

/-! ### Grid -/

/-- Sponge shapes `(N, R)`: rate 1, rate 2, and rate 4. -/
@[instance_reducible] def sz31 : SpongeSize := { N := 3, R := 1 }
/-- Width 5, rate 2. -/
@[instance_reducible] def sz52 : SpongeSize := { N := 5, R := 2 }
/-- Width 6, rate 4. -/
@[instance_reducible] def sz64 : SpongeSize := { N := 6, R := 4 }

/-- Message and challenge length profiles (one entry per round), up to `5` bytes per action. -/
def lengthProfiles : List (List Nat × List Nat) :=
  [([1, 1, 1], [1, 1, 1]), ([2, 5, 3], [5, 1, 4]), ([4, 2, 1], [3, 5, 2]),
    ([5, 4, 5], [2, 3, 5])]

/-- Every configuration of the grid passes for the sponge shape `sz`. -/
def gridAgrees (sz : SpongeSize) : Bool :=
  letI := sz
  [1, 2, 3].all fun k => lengthProfiles.all fun (msz, csz) =>
    unsaltedAgrees k msz csz && (List.range 5).all fun δ => saltedAgrees k msz csz δ

/-- The test permutation is a permutation: `permInv` inverts `perm` on sample states. -/
def permRoundTrips (sz : SpongeSize) : Bool :=
  letI := sz
  (List.range 20).all fun a =>
    let s : CanonicalSpongeState UInt8 := Vector.ofFn fun j => a.toUInt8 * 11 + j.val.toUInt8
    permInv (perm s) == s && perm s != permInv s

/-- info: true -/
#guard_msgs in
#eval permRoundTrips sz31 && permRoundTrips sz52 && permRoundTrips sz64

/-- info: true -/
#guard_msgs in
#eval gridAgrees sz31

/-- info: true -/
#guard_msgs in
#eval gridAgrees sz52

/-- info: true -/
#guard_msgs in
#eval gridAgrees sz64

/-! ### Worked instance (width 6, rate 4, `k = 2`, `δ = 1`)

The prover and the verifier make the same queries: one `h` query, then one `p` query per
squeezed block. -/

/-- Query log of the honest salted prover on the worked instance. -/
def workedProverLog : List LogEntry :=
  letI := sz64
  (runLogged (Prover.runToRoundDSFSSalted (U := UInt8) (pSpec := spec 2 [2, 5] [5, 1])
    (#v[9] : Vector UInt8 1) (Fin.last 4) (42 : UInt8) prover [])).2

/-- info: ["h", "p", "p", "p", "p"] -/
#guard_msgs in
#eval workedProverLog.map (·.1)

end DSFSAgreementTest
