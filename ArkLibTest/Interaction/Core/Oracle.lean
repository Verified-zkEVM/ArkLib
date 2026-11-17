/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.OracleVerifier

/-! Query-only decisions and agreement of embedded and virtual output oracles. -/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.Oracle
open OracleComp

namespace Interaction.Core.OracleTests

@[instance_reducible] def functions : OracleFamily PUnit (fun _ => Nat → Nat) :=
  singletonFamily OracleInterface.instFunction

def doubled : OracleMap functions functions where
  f x _ n := 2 * x ⟨⟩ n
  impl q := do
    let n : Nat ← liftM (functions.spec.query q)
    pure (2 * n)
  law x q := by
    simp only [simulateQ_bind, simulateQ_pure]
    rfl

def embedded := OracleMap.embedding functions (fun _ : PUnit => PUnit.unit)

example : simulateQ (functions.behaviorOfRealizations (fun _ n => n + 5))
    (embedded.impl ⟨⟨⟩, (3 : Nat)⟩) = (8 : Nat) := rfl

example : simulateQ (functions.behaviorOfRealizations (fun _ n => n + 5))
    ((doubled.comp embedded).impl ⟨⟨⟩, (3 : Nat)⟩) = (16 : Nat) := rfl

/-- No ambient oracles, with the index in `Type 0`. -/
abbrev noAmbient : OracleSpec.{0, 0} PEmpty := OracleSpec.emptySpec

/-- The empty input family, with its index in `Type 0`. -/
def emptyFamily : OracleFamily.{0, 0, 0} PEmpty.{1} (fun i => PEmpty.elim i) :=
  ⟨fun i => i.elim⟩

@[instance_reducible] def tree : OracleProtocol :=
  .liftBind (.oracle (Nat → Nat) OracleInterface.instFunction) (fun _ => .pure ⟨⟩)

def first : PathAlong oracleSig tree := ⟨fun n => n + 5, ⟨⟩⟩
def second : PathAlong oracleSig tree := ⟨fun n => 2 * n, ⟨⟩⟩

example : projectPathAlong oracleSig tree first = projectPathAlong oracleSig tree second := rfl
example : (toView tree first).val = (toView tree second).val := rfl

/-- The decision can name an evaluation query but receives no function payload. -/
def queryDecision : OracleVerifier noAmbient tree Unit (fun _ => Nat) emptyFamily
    (fun _ => functions) where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact do
      let n : Nat ← pathLift noAmbient emptyFamily (s := tree) ⟨⟨⟩, ⟨⟩⟩ ⟨.inl ⟨⟩, (3 : Nat)⟩
      pure n
  outputMap _ p _ :=
    (OracleMap.embedding (pathFamily tree p) (fun _ => .inl ⟨⟩)).comp (OracleMap.snd _ _)

example : payloadImpl tree first ⟨.inl ⟨⟩, (3 : Nat)⟩ = (8 : Nat) := rfl
example : payloadImpl tree second ⟨.inl ⟨⟩, (3 : Nat)⟩ = (6 : Nat) := rfl

run_cmd do
  let answer : Nat := simulateQ (functions.behaviorOfRealizations (fun _ n => n + 5))
    ((doubled.comp embedded).impl ⟨⟨⟩, (3 : Nat)⟩)
  unless answer == 16 do throwError "virtual routing disagrees with materialized output"

end Interaction.Core.OracleTests

namespace Interaction.Core.OracleTests

/-- The small oracle protocol with no rounds. -/
abbrev emptyTree : OracleProtocol.{0, 0} := .pure ⟨⟩
/-- The resources of the protocol with no rounds and no input oracles: both parts are empty. -/
abbrev emptyResources := pathResources emptyFamily emptyTree ⟨⟩

/-- The empty pair of input data and path payloads. -/
def emptyData : emptyResources.Data := (fun i => i.elim, fun i => i.elim)

/-- The prefix can return a statement obtained from an ambient query. -/
def ambientPrefix : OracleVerifier (Unit →ₒ Bool) emptyTree Unit (fun _ => Bool)
    emptyFamily (fun _ => emptyFamily) where
  decide _ p _ := by
    cases p
    exact do
      let bit : Bool ← liftM (((Unit →ₒ Bool) + emptyResources.spec).query (.inl ()))
      pure bit
  outputMap _ _ _ :=
    { f := fun _ i => i.elim
      impl := fun q => q.1.elim
      law := fun _ q => q.1.elim }

/-- The suffix can lawfully expose its input statement as a constant oracle. -/
def constantSuffix : OracleVerifier (Unit →ₒ Bool) emptyTree Bool (fun _ => Unit)
    emptyFamily (fun _ => functions) where
  decide _ _ _ := pure ()
  outputMap bit _ _ :=
    { f := fun _ _ _ => if bit then 1 else 0
      impl := fun _ => pure (if bit then (1 : Nat) else (0 : Nat))
      law := fun _ _ => rfl }

/-- With no resource data or public moves, one output map cannot expose both ambient answers. -/
example (output : OracleMap emptyResources functions) :
    ¬ ∀ bit, output.f emptyData ⟨⟩ 0 =
      ((constantSuffix.outputMap bit ⟨⟩ ⟨⟨⟩, rfl⟩).f emptyData) ⟨⟩ 0 := by
  intro h
  have h₀ := h false
  have h₁ := h true
  change output.f emptyData ⟨⟩ 0 = 0 at h₀
  change output.f emptyData ⟨⟩ 0 = 1 at h₁
  exact Nat.zero_ne_one (h₀.symm.trans h₁)

end Interaction.Core.OracleTests

run_cmd do
  for decl in [``Interaction.Core.plain_challenge_shape,
      ``Interaction.Core.oracle_payload_shape, ``Interaction.Core.Reduction.run,
      ``Interaction.Core.OracleMap.comp, ``Interaction.Core.OracleMap.simulate_eq,
      ``Interaction.Core.oracles_split_append, ``Interaction.Core.oracles_append_split,
      ``Interaction.Core.payloads_append, ``Interaction.Core.payloadImpl_append,
      ``Interaction.Core.OracleVerifier.run] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
