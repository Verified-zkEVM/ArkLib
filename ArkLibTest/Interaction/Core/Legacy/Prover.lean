/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Core.Legacy.Verifier

/-! Acceptance examples for the embedded legacy prover and verifier: each legacy prover
function fills the matching slot of the interaction-layer prover, and the embedded verifier
decides with legacy `verify` on the decoded transcript. -/

open PFunctor PFunctor.FreeM OracleComp OracleSpec Interaction.Core Interaction.TwoParty.Lens
  ProtocolSpec

namespace Interaction.Core.Legacy.Tests

/-- A message, a challenge, then a second message. -/
def twoWay : ProtocolSpec 3 := ⟨!v[.P_to_V, .V_to_P, .P_to_V], !v[Nat, Bool, Nat]⟩

/-- A legacy prover with a counter state: it sends its state, keeps or resets it on the
challenge, sends it again, and outputs it as statement and witness. -/
def counterProver : _root_.Prover []ₒ Nat Nat Nat Nat twoWay where
  PrvState _ := Nat
  input sw := sw.1 + sw.2
  sendMessage
    | ⟨0, _⟩ => fun st => pure (st, st + 1)
    | ⟨1, h⟩ => nomatch h
    | ⟨2, _⟩ => fun st => pure (st * 10, st)
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun st => pure (fun b => bif (show Bool from b) then st else 0)
    | ⟨2, h⟩ => nomatch h
  output st := pure (st, st + 100)

/-- The empty ambient spec has no queries, so it is interpreted in `Id`. -/
def noQueries : QueryImpl []ₒ Id := fun q => q.elim

/-- The embedded prover, with its slots interpreted in `Id`. -/
def counterEmbedded : Focal plainSig Id (protocol twoWay) (fun _ => Nat × Nat) :=
  Prover.simulate noQueries (embedProver counterProver 2 3)

/-- The first slot is the legacy first message. -/
example : (counterEmbedded : Id _).1 = (5 : Nat) := rfl

/-- The challenge slot is the legacy `receiveChallenge` continuation; the last slot and the leaf
action are the legacy last message and output. -/
example : (show Nat from (((counterEmbedded : Id _).2 : Id _) true : Id _).1) = 60 := rfl
example : (show Nat from (((counterEmbedded : Id _).2 : Id _) false : Id _).1) = 0 := rfl
example : (show Nat × Nat from (((counterEmbedded : Id _).2 : Id _) true : Id _).2) =
    (6, 106) := rfl

/-- A legacy verifier that accepts when the challenge is `true` and returns the last message. -/
def lastIfTrue : _root_.Verifier []ₒ Nat Nat twoWay where
  verify stmt tr := bif (show Bool from tr 1) then pure (stmt + show Nat from tr 2) else failure

/-- The embedded verifier's decision is legacy `verify` on the decoded transcript. -/
example (stmt : Nat) (p : Path (protocol twoWay)) (v : PlainView (protocol twoWay) p) :
    (embedVerifier lastIfTrue).decide stmt p v = lastIfTrue.verify stmt (decode twoWay v.val) :=
  rfl

/-- The embedded reduction pairs the two embeddings. -/
example : (embedReduction ⟨counterProver, lastIfTrue⟩).verifier = embedVerifier lastIfTrue := rfl

end Interaction.Core.Legacy.Tests
