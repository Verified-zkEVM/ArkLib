/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import PolyFun.Interaction.Basic.BundledMonad
import VCVio.OracleComp.SimSemantics.Append
import ArkLib.OracleReduction.OracleInterface

/-!
# Oracle verifier read access

Verifier computations in oracle reductions have two different kinds of effects:

* canonical reads of the input oracle statement and already-sent prover oracle
  messages;
* ambient verifier effects such as sampling from the surrounding oracle
  computation.

This file packages the canonical read part as an `accSpec`-indexed family. The
index is essential: every prover-oracle node extends the accumulated transcript
oracle interface for the continuation.
-/

open OracleComp OracleSpec

namespace Interaction
namespace Oracle
namespace Verifier

/-- The canonical pure verifier read interface: input oracle statement access
plus accumulated prover-oracle-message access. -/
abbrev ReadSpec {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type)
    [∀ i, OracleInterface (OStmtIn i)]
    {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ) :=
  [OStmtIn]ₒ + accSpec

/-- Standard left-associated ambient verifier access spec used by the current
executable oracle semantics. The canonical read spec embeds into this by
skipping the left ambient `oSpec` summand. -/
abbrev AmbientAccessSpec {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [∀ i, OracleInterface (OStmtIn i)]
    {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ) :=
  (oSpec + [OStmtIn]ₒ) + accSpec

namespace ReadSpec

variable {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
variable [∀ i, OracleInterface (OStmtIn i)]
variable {ιₐ : Type} {accSpec : OracleSpec.{0, 0} ιₐ}

/-- Canonical input-statement query in the verifier read spec. -/
def queryInput (q : [OStmtIn]ₒ.Domain) :
    OracleComp (ReadSpec OStmtIn accSpec) ([OStmtIn]ₒ.Range q) :=
  liftM ((ReadSpec OStmtIn accSpec).query (.inl q))

/-- Canonical accumulated transcript/prover-oracle-message query in the verifier
read spec. -/
def queryAcc (q : accSpec.Domain) :
    OracleComp (ReadSpec OStmtIn accSpec) (accSpec.Range q) :=
  liftM ((ReadSpec OStmtIn accSpec).query (.inr q))

end ReadSpec

/-- An `accSpec`-indexed verifier effect family with canonical read access.

The runner is specialized to the current executable setting: verifier effects
ultimately run in the surrounding `OracleComp oSpec`. This keeps the main
reduction execution API non-failing for the cutover while making the canonical
read interface independent of `oSpec`. -/
structure AccessFamily {ι : Type} (oSpec : OracleSpec.{0, 0} ι)
    {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) [∀ i, OracleInterface (OStmtIn i)] where
  /-- Verifier monad at a node with accumulated oracle-message access
  `accSpec`. -/
  M : {ιₐ : Type} → OracleSpec.{0, 0} ιₐ → Type → Type
  /-- Monad instance for the verifier monad at each accumulator. -/
  instMonad : {ιₐ : Type} → (accSpec : OracleSpec.{0, 0} ιₐ) → Monad (M accSpec)
  /-- Lift canonical reads into the verifier monad. -/
  readLift : {ιₐ : Type} → {accSpec : OracleSpec.{0, 0} ιₐ} → {α : Type} →
    OracleComp (ReadSpec OStmtIn accSpec) α → M accSpec α
  /-- Execute verifier effects by supplying concrete implementations of the
  canonical read interface. -/
  runM : {ιₐ : Type} → {accSpec : OracleSpec.{0, 0} ιₐ} → {α : Type} →
    QueryImpl (ReadSpec OStmtIn accSpec) (OracleComp oSpec) →
      M accSpec α → OracleComp oSpec α
  /-- `readLift` preserves pure computations. -/
  readLift_pure : {ιₐ : Type} → {accSpec : OracleSpec.{0, 0} ιₐ} →
    {α : Type} → (a : α) →
      readLift (accSpec := accSpec)
        (pure a : OracleComp (ReadSpec OStmtIn accSpec) α) =
          pure a
  /-- `readLift` preserves binds. -/
  readLift_bind : {ιₐ : Type} → {accSpec : OracleSpec.{0, 0} ιₐ} →
    {α β : Type} → (oa : OracleComp (ReadSpec OStmtIn accSpec) α) →
      (k : α → OracleComp (ReadSpec OStmtIn accSpec) β) →
        readLift (accSpec := accSpec) (oa >>= k) =
          (readLift (accSpec := accSpec) oa >>=
            fun a => readLift (accSpec := accSpec) (k a))
  /-- Executing a lifted canonical read is exactly `simulateQ` with the supplied
  read implementation. -/
  run_readLift : {ιₐ : Type} → {accSpec : OracleSpec.{0, 0} ιₐ} →
    {α : Type} → (readImpl : QueryImpl (ReadSpec OStmtIn accSpec) (OracleComp oSpec)) →
      (oa : OracleComp (ReadSpec OStmtIn accSpec) α) →
        runM readImpl (readLift (accSpec := accSpec) oa) =
          simulateQ readImpl oa

namespace AccessFamily

variable {ι : Type} {oSpec : OracleSpec.{0, 0} ι}
variable {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
variable [∀ i, OracleInterface (OStmtIn i)]

/-- Bundle the verifier monad at an accumulated oracle-message spec. -/
def nodeMonad (access : AccessFamily oSpec OStmtIn)
    {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ) :
    BundledMonad.{0, 0} :=
  ⟨access.M accSpec, access.instMonad accSpec⟩

/-- Canonical read implementation from concrete input and accumulator
implementations. -/
def readImpl {ιₐ : Type} {accSpec : OracleSpec.{0, 0} ιₐ}
    (inputImpl : QueryImpl [OStmtIn]ₒ (OracleComp oSpec))
    (accImpl : QueryImpl accSpec (OracleComp oSpec)) :
    QueryImpl (ReadSpec OStmtIn accSpec) (OracleComp oSpec) :=
  inputImpl + accImpl

namespace Ambient

variable (oSpec : OracleSpec.{0, 0} ι)
variable (OStmtIn : ιₛᵢ → Type)
variable [∀ i, OracleInterface (OStmtIn i)]

/-- Embed canonical verifier reads into the current left-associated ambient
access spec. -/
def readLift {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ) {α : Type}
    (oa : OracleComp (ReadSpec OStmtIn accSpec) α) :
    OracleComp (AmbientAccessSpec oSpec OStmtIn accSpec) α :=
  simulateQ
    (fun
      | .inl q => liftM ((AmbientAccessSpec oSpec OStmtIn accSpec).query (.inl (.inr q)))
      | .inr q => liftM ((AmbientAccessSpec oSpec OStmtIn accSpec).query (.inr q)))
    oa

/-- Run the current left-associated ambient verifier monad using concrete
canonical read implementations and the surrounding ambient oracle access. -/
def runM {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ) {α : Type}
    (readImpl : QueryImpl (ReadSpec OStmtIn accSpec) (OracleComp oSpec))
    (oa : OracleComp (AmbientAccessSpec oSpec OStmtIn accSpec) α) :
    OracleComp oSpec α :=
  simulateQ
    (fun
      | .inl (.inl q) => liftM (oSpec.query q)
      | .inl (.inr q) => readImpl (.inl q)
      | .inr q => readImpl (.inr q))
    oa

@[simp]
theorem readLift_pure {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ)
    {α : Type} (a : α) :
    Ambient.readLift oSpec OStmtIn accSpec
      (pure a : OracleComp (ReadSpec OStmtIn accSpec) α) =
        pure a :=
  rfl

theorem readLift_bind {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ)
    {α β : Type}
    (oa : OracleComp (ReadSpec OStmtIn accSpec) α)
    (k : α → OracleComp (ReadSpec OStmtIn accSpec) β) :
    Ambient.readLift oSpec OStmtIn accSpec (oa >>= k) =
      (Ambient.readLift oSpec OStmtIn accSpec oa >>=
        fun a => Ambient.readLift oSpec OStmtIn accSpec (k a)) := by
  simp [Ambient.readLift]

theorem run_readLift {ιₐ : Type} (accSpec : OracleSpec.{0, 0} ιₐ)
    {α : Type}
    (readImpl : QueryImpl (ReadSpec OStmtIn accSpec) (OracleComp oSpec))
    (oa : OracleComp (ReadSpec OStmtIn accSpec) α) :
    Ambient.runM oSpec OStmtIn accSpec readImpl
      (Ambient.readLift oSpec OStmtIn accSpec oa) =
        simulateQ readImpl oa := by
  induction oa using OracleComp.inductionOn with
  | pure x => rfl
  | query_bind q k ih =>
      cases q
      · simp only [Ambient.readLift, Ambient.runM, add_apply_inl, simulateQ_bind,
          simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query]
        rw [id_map]
        congr
        funext x
        exact ih x
      · simp only [Ambient.readLift, Ambient.runM, add_apply_inr, simulateQ_bind,
          simulateQ_query, OracleQuery.input_query, OracleQuery.cont_query]
        rw [id_map]
        congr
        funext x
        exact ih x

/-- The standard executable verifier access family used by the current oracle
reduction runner. -/
def accessFamily : AccessFamily oSpec OStmtIn where
  M := fun accSpec α => OracleComp (AmbientAccessSpec oSpec OStmtIn accSpec) α
  instMonad := fun _ => inferInstance
  readLift := fun {_} {accSpec} {_} oa => Ambient.readLift oSpec OStmtIn accSpec oa
  runM := fun {_} {accSpec} {_} readImpl oa => Ambient.runM oSpec OStmtIn accSpec readImpl oa
  readLift_pure := fun {_} {accSpec} {_} a => readLift_pure oSpec OStmtIn accSpec a
  readLift_bind := fun {_} {accSpec} {_} {_} oa k => readLift_bind oSpec OStmtIn accSpec oa k
  run_readLift := fun {_} {accSpec} {_} readImpl oa =>
    run_readLift oSpec OStmtIn accSpec readImpl oa

end Ambient

/-- Standard current-code verifier access family. -/
def ambient : AccessFamily oSpec OStmtIn :=
  Ambient.accessFamily oSpec OStmtIn

end AccessFamily

end Verifier
end Oracle
end Interaction
