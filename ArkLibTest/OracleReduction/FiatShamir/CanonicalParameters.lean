/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/

import ArkLib.OracleReduction.FiatShamir.Canonical
import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Defs

/-!
# Single-salt parameter regressions

Both transformations expose one fixed-length salt as metadata. Successive NARG strings request
successive samples. The length-zero case uses those same interfaces and security theorems.
-/

open OracleComp OracleSpec ProtocolSpec

namespace CanonicalParameters

instance : SpongeSize where
  N := 4
  R := 2

instance : VCVCompatible UInt8 where
  default := 0

abbrev spec : OracleSpec Unit := Unit →ₒ Vector UInt8 2
abbrev reduction : Reduction spec Unit Unit Unit Unit !p[] := Reduction.id
abbrev proof : Proof spec Unit Unit !p[] :=
  { prover :=
      { PrvState := fun _ => Unit
        input := fun _ => ()
        sendMessage := fun i => i.1.elim0
        receiveChallenge := fun i => i.1.elim0
        output := fun _ => pure (true, ()) }
    verifier := { verify := fun _ _ => pure true } }

instance : Codec !p[] UInt8 where
  proverMessageSize i := i.1.elim0
  verifierMessageSize i := i.1.elim0
  encode i := i.1.elim0
  decode i := i.1.elim0
  decodingBias i := i.1.elim0
  encode_injective i := i.1.elim0
  decode_isBiased i := i.1.elim0
  decode_surjective i := i.1.elim0

instance : ∀ i, VCVCompatible ((!p[]).Challenge i) := fun i => i.1.elim0

/-- Count draws, using their index to distinguish successive sampled salts. -/
def saltImpl : QueryImpl spec (StateT Nat Id) := fun _ count =>
  (Vector.replicate 2 (UInt8.ofNat count), count + 1)

def verifierMessageImpl : QueryImpl (canonicalFSOracle Unit !p[] UInt8 2) (StateT Nat Id) :=
  fun key => key.1.1.elim0

def canonicalImpl : QueryImpl (spec + canonicalFSOracle Unit !p[] UInt8 2) (StateT Nat Id) :=
  QueryImpl.addLift saltImpl verifierMessageImpl

def spongeImpl : QueryImpl (duplexSpongeOracle Unit UInt8) (StateT Nat Id) :=
  fun key => match key with
    | .inl _ => pure (Vector.replicate SpongeSize.C 0)
    | .inr (.inl state) => pure state
    | .inr (.inr state) => pure state

def duplexImpl : QueryImpl (spec + duplexSpongeOracle Unit UInt8) (StateT Nat Id) :=
  QueryImpl.addLift saltImpl spongeImpl

example : Id.run ((simulateQ canonicalImpl (do
    let P := reduction.prover.fiatShamirSalted 2 (spec.query ())
    let (first, _) ← P.sendMessage ⟨0, rfl⟩ (P.input ((), ()))
    let (second, _) ← P.sendMessage ⟨0, rfl⟩ (P.input ((), ()))
    return (first.1.toList, second.1.toList))).run 0) = (([0, 0], [1, 1]), 2) := by
  rfl

example : Id.run ((simulateQ duplexImpl (do
    let P := proof.prover.duplexSpongeFiatShamir 2 (spec.query ())
    let (first, _) ← P.sendMessage ⟨0, rfl⟩ (P.input ((), ()))
    let (second, _) ← P.sendMessage ⟨0, rfl⟩ (P.input ((), ()))
    return (first.1.toList, second.1.toList))).run 0) = (([0, 0], [1, 1]), 2) := by
  rfl

/-- Zero length changes neither the application types nor the original message family. -/
example : NonInteractiveReduction (FiatShamirNARGString !p[] UInt8 0)
    (spec + canonicalFSOracle Unit !p[] UInt8 0) Unit Unit Unit Unit :=
  reduction.fiatShamirSalted 0 (pure #v[])

example : NonInteractiveReduction (FiatShamirNARGString !p[] UInt8 0)
    (spec + duplexSpongeOracle Unit UInt8) Unit Unit Bool Unit :=
  proof.duplexSpongeFiatShamir 0 (pure #v[])

/-- The upstream unsalted compiler and salt-bearing compiler coexist in one import closure. -/
example : NonInteractiveReduction ((!p[] : ProtocolSpec 0).Messages)
    (spec + fsChallengeOracle Unit !p[]) Unit Unit Unit Unit :=
  reduction.fiatShamir

end CanonicalParameters


namespace SRSaltContext

open OracleComp OracleSpec ProtocolSpec

abbrev protocol : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[Bool]⟩

/-- Distinct salts address distinct challenge entries for the same original statement. -/
def table : QueryImpl (srChallengeOracle (Bool × Bool) protocol) Id :=
  fun | ⟨⟨⟨0, _⟩, _⟩, ((_, salt), _)⟩ => salt

def impl : QueryImpl []ₒ
    (StateT (QueryImpl (srChallengeOracle (Bool × Bool) protocol) Id) ProbComp) :=
  fun q => nomatch q

def challengeVerifier : Verifier []ₒ Bool Bool protocol where
  verify _ tr := pure (tr 0)

def statementVerifier : Verifier []ₒ Bool Bool protocol where
  verify x _ := pure x

/-- Salt is a separate extractor input, not part of the statement or input relation. -/
def extractor : Extractor.StateRestoration []ₒ Bool Bool Unit protocol (Salt := Bool) :=
  fun _ salt _ _ _ _ => pure salt

-- Changing only the salt changes the verifier message. Input validity still tests `false`.
example (salt : Bool) :
    Verifier.StateRestoration.soundnessFailureProb (Salt := Bool) (pure table) impl
      (QueryImpl.id' unifSpec) {true} {true} challengeVerifier
      (pure ((false, salt), default)) = if salt then 1 else 0 := by
  change Pr{let result ← pure (false, some salt)}[
    match result with
    | (x, some b) => b ∈ ({true} : Set Bool) ∧ x ∉ ({true} : Set Bool)
    | _ => False] = _
  cases salt <;> simp


-- The verifier receives `true` even when the salt is `false`; extraction receives the salt.
example (salt : Bool) :
    Verifier.StateRestoration.knowledgeSoundnessFailureProb (Salt := Bool) (pure table) impl
      (QueryImpl.id' unifSpec) extractor {(_x, w) | w = true} {(b, _) | b = true}
      statementVerifier (pure ((true, salt), default, ())) = if salt then 0 else 1 := by
  change Pr{let result ← pure (true, some salt, some true, ())}[
    relationKSFailEvent {p : Bool × Bool | p.2 = true}
      {p : Bool × Unit | p.1 = true} result] = _
  cases salt <;> simp [relationKSFailEvent]


end SRSaltContext
