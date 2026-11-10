/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.OracleReduction.FiatShamir.DuplexSponge.InitialObject
public import
  ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.Proofs.ZeroKnowledge.SaltAbsorption

/-!
# Consecutive absorption of the initial object and proof salt

The public transform interface keeps initial object, salt and prover messages separate. The
setup-absorption lemmas identify the sequence with one absorption of its concatenated encoding,
which permits reuse of the existing prefix-work and query-counting arguments.
-/

@[expose] public section

open OracleComp OracleSpec ProtocolSpec

namespace DuplexSpongeFS.InitialObject

variable {U : Type} [SpongeUnit U] [SpongeSize]
  {Object : Type} [HasSize Object U] {δ : Nat}

/-- Byte-level encoding of the separate setup fields, used only by the proof adapter. -/
def setupEncoding (obj : Object) (salt : Vector U δ) :
    Vector U (HasSize.size Object U + δ) :=
  (HasSize.toFun (α := Object) (β := U)) obj ++ salt

/-- Consecutive setup absorbs preserve their actual state and cursors. They do not become
prover messages or protocol rounds. -/
theorem initialize_eq_setup_absorb (obj : Object) (salt : Vector U δ) :
    initializeSponge obj salt =
      (DuplexSponge.zeroStart (U := U)).absorb (setupEncoding obj salt).toList := by
  unfold initializeSponge DuplexSponge.absorbInitialObject setupEncoding
  rw [Vector.toList_append, DuplexSponge.absorb_append]

omit [HasSize Object U] in
/-- Product encoding is precisely separate absorption of both initial-object fields,
followed by the salt. This composition law is independent of the sponge dimensions. -/
theorem initialize_pair {A B : Type} [HasSize A U] [HasSize B U]
    (a : A) (b : B) (salt : Vector U δ) :
    letI := HasSize.prod (α := A) (β := B) (U := U)
    initializeSponge (a, b) salt =
      (do
        let first ← DuplexSponge.absorbInitialObject a
        let second ← first.absorb ((HasSize.toFun (α := B) (β := U)) b).toList
        second.absorb salt.toList) := by
  let := HasSize.prod (α := A) (β := B) (U := U)
  unfold initializeSponge DuplexSponge.absorbInitialObject
  change ((DuplexSponge.zeroStart (U := U)).absorb
    ((HasSize.toFun (α := A) (β := U)) a ++
      (HasSize.toFun (α := B) (β := U)) b).toList >>= fun initialized =>
      initialized.absorb salt.toList) = _
  rw [Vector.toList_append, DuplexSponge.absorb_append, bind_assoc]

end DuplexSpongeFS.InitialObject
