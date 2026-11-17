/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Yuxi Zheng, Michele Orrù
-/
module

public import ArkLib.Data.Hash.DuplexSponge.Initialization
public import ArkLib.NonInteractiveArgument.FiatShamir.DuplexSponge.Defs
public import ArkLib.ToCompPoly.HasSize

/-!
# Initial objects for the Fiat--Shamir transform

An initial object is a separate transform input, typically `(session identifier, statement)`.
It is encoded injectively and absorbed from the fixed public zero state, before the proof salt
and protocol rounds. The original protocol, its prover and verifier messages, and its codec are
unchanged.

`rounds` is the permutation-only interpreter corresponding to the existing DSFS round
interpreter. The operational bridge below establishes equality with that interpreter.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.InitialObject

variable {U : Type} [SpongeUnit U] [SpongeSize]
  {Object : Type} [HasSize Object U]

/-- The initial object and NARG salt have distinct typed fields. Their encodings are absorbed
consecutively, in that order, without a squeeze or cursor reset between them. -/
def initializeSponge {δ : Nat} (obj : Object) (salt : Vector U δ) :
    OracleComp (forwardPermutationOracle (CanonicalSpongeState U)) (CanonicalDuplexSponge U) := do
  let initialized ← DuplexSponge.absorbInitialObject obj
  initialized.absorb salt.toList

variable {n : Nat} {pSpec : ProtocolSpec n} [c : Codec pSpec U]

/-- The original protocol's round interpreter, using only the permutation.
It takes an already initialized sponge; the initial object is not a protocol message. -/
def rounds (s : CanonicalDuplexSponge U) (messages : pSpec.Messages) (i : Fin (n + 1)) :
    OracleComp (forwardPermutationOracle (CanonicalSpongeState U))
      (CanonicalDuplexSponge U × pSpec.Transcript i) :=
  Fin.induction
    (pure (s, fun j => j.elim0))
    (fun j ih => do
      let ⟨sponge, transcript⟩ ← ih
      match hd : pSpec.dir j with
      | .V_to_P =>
        let idx : pSpec.ChallengeIdx := ⟨j, hd⟩
        let ⟨raw, next⟩ ← sponge.squeeze (verifierMessageSize idx)
        return (next, transcript.concat (c.decode idx raw))
      | .P_to_V =>
        let idx : pSpec.MessageIdx := ⟨j, hd⟩
        let next ← sponge.absorb (c.encode idx (messages idx)).toList
        return (next, transcript.concat (messages idx))) i

omit [HasSize Object U] in
/-- The separate-initialization runner reuses exactly the existing DSFS round computation,
including its final state, cursors, outputs and all permutation queries. -/
theorem rounds_eq_existing {ι : Type} {oSpec : OracleSpec ι} {Stmt : Type}
    (s : CanonicalDuplexSponge U) (messages : pSpec.Messages) (i : Fin (n + 1)) :
    (liftM (rounds s messages i) :
      OracleComp (oSpec + duplexSpongeForwardOracle Stmt U) _) =
    messages.deriveTranscriptDSFSAux (StmtIn := Stmt) s i := by
  induction i using Fin.induction with
  | zero => rfl
  | succ j ih =>
    dsimp only [rounds] at ih
    simp only [rounds, ProtocolSpec.Messages.deriveTranscriptDSFSAux, Fin.induction_succ]
    rw [liftM_bind, ih]
    apply bind_congr
    rintro ⟨sponge, transcript⟩
    split
    · rename_i hd
      split
      · simp only [liftM_bind, liftM_pure]
        rfl
      · rename_i hd'
        cases hd.symm.trans hd'
    · rename_i hd
      split
      · rename_i hd'
        cases hd.symm.trans hd'
      · simp only [liftM_bind, liftM_pure]
        rfl

/-- Run Fiat--Shamir from a separately encoded initial object and proof salt.
The message tuple is the original protocol's unmodified message tuple. -/
def deriveTranscript {δ : Nat} (obj : Object) (salt : Vector U δ)
    (messages : pSpec.Messages) :
    OracleComp (forwardPermutationOracle (CanonicalSpongeState U))
      (CanonicalDuplexSponge U × pSpec.FullTranscript) := do
  let initialized ← initializeSponge obj salt
  rounds initialized messages (Fin.last n)

end DuplexSpongeFS.InitialObject
