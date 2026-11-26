/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Oracle.LiftContext

/-!
# Oracle context lifting on a concrete verifier

The protocol draws a challenge `r : Bool`, then the prover sends an oracle `g : Bool → Bool`.
The inner verifier has one input oracle `f : Bool → Bool`. It queries `f true`, accepts with the
output statement `r` when the answer is `true`, and exports `g`.

The outer verifier has a tag `b : Bool` and two input oracles `F : Bool → Bool → Bool`. The lens
answers the inner input oracle by `x ↦ F b (!x)`, lifts the output statement to `xor b r`, and
exports `x ↦ F (!b) x && g x`. The tests check the lifted decision, the lifted output data and
one routed output query on a concrete path, and obtain soundness of the lifted verifier with
error `0` from `OracleVerifier.liftContext_soundness`.
-/

open PFunctor PFunctor.FreeM Interaction Interaction.Oracle OracleComp OracleSpec
open scoped ENNReal

namespace Interaction.OracleLiftContextTests

/-- A challenge `r : Bool`, then an oracle message `g : Bool → Bool`. -/
@[instance_reducible] def protocol : OracleProtocol :=
  .liftBind (.challenge Bool) (fun _ =>
    .liftBind (.oracle (Bool → Bool) OracleInterface.instFunction) (fun _ => .pure ⟨⟩))

/-- The only shape path. -/
abbrev path : Path protocol := ⟨⟨⟩, ⟨⟩, ⟨⟩⟩

/-- The verifier's view of a run with challenge `r`. -/
def view (r : Bool) : View protocol path := ⟨⟨r, ⟨⟩, ⟨⟩⟩, rfl⟩

/-- One function `Bool → Bool`, queried pointwise. -/
@[instance_reducible] def fn : OracleFamily.{0, 0, 0} PUnit (fun _ => Bool → Bool) :=
  ⟨fun _ => OracleInterface.instFunction⟩

/-- Two functions `Bool → Bool`, indexed by `Bool` and queried pointwise. -/
@[instance_reducible] def fnPair : OracleFamily.{0, 0, 0} Bool (fun _ => Bool → Bool) :=
  ⟨fun _ => OracleInterface.instFunction⟩

/-- No ambient oracles. -/
abbrev noAmbient : OracleSpec.{0, 0} PEmpty := OracleSpec.emptySpec

/-! ### The inner verifier -/

/-- Export the path's oracle message. -/
def messageOut (p : Path protocol) : OracleMap (pathBundle fn protocol p) fn := by
  rcases p with ⟨⟨⟩, ⟨⟩, ⟨⟩⟩
  exact
    { f x _ := x.2.1
      impl q := liftM ((pathBundle fn protocol path).spec.query (.inr (.inl q.2)))
      law _ _ := rfl }

/-- Query the input oracle at `true`, accept with the challenge on `true`, and export the
oracle message. -/
def innerVerifier : OracleVerifier noAmbient protocol Unit (fun _ => Bool) fn (fun _ => fn) where
  decide _ p v := by
    rcases p with ⟨⟨⟩, ⟨⟩, ⟨⟩⟩
    exact OptionT.mk do
      let a : Bool ← liftM ((noAmbient + (pathBundle fn protocol path).spec).query
        (.inr (.inl ⟨⟨⟩, true⟩)))
      pure (if a then some v.val.1 else none)
  outputMap _ p _ := messageOut p

/-! ### The lens -/

/-- Answer the inner input oracle by `x ↦ F b (!x)`. -/
def projOracle (b : Bool) : OracleMap fnPair fn where
  f F _ x := F b (!x)
  impl q := liftM (fnPair.spec.query ⟨b, !q.2⟩)
  law _ _ := rfl

/-- Export `x ↦ F (!b) x && g x` from the outer inputs `F` and the inner output `g`. -/
def liftOracle (b : Bool) :
    OracleMap ((fnPair : OracleBundle).sum (fn : OracleBundle)) fn where
  f x _ y := x.1 (!b) y && x.2 ⟨⟩ y
  impl q := do
    let a : Bool ← liftM (((fnPair : OracleBundle).sum (fn : OracleBundle)).spec.query
      (.inl ⟨!b, q.2⟩))
    let c : Bool ← liftM (((fnPair : OracleBundle).sum (fn : OracleBundle)).spec.query
      (.inr ⟨⟨⟩, q.2⟩))
    pure (a && c)
  law _ _ := by
    simp only [simulateQ_bind]
    rfl

/-- Tag `b`: project the inner input oracle from `F b`, lift the output statement `r` to
`xor b r`, and build the output oracle from `F (!b)` and the inner output oracle. -/
def lens : OracleStatementLens protocol Bool Unit (fun _ => Bool) (fun _ => Bool) fnPair fn
    (fun _ => fn) (fun _ => fn) where
  stmt := { proj _ := (), lift b _ r := xor b r }
  projOracle := projOracle
  liftOracle b _ := liftOracle b

/-- The lifted verifier. -/
def outerVerifier : OracleVerifier noAmbient protocol Bool (fun _ => Bool) fnPair (fun _ => fn) :=
  innerVerifier.liftContext lens

/-! ### A concrete run of the lifted verifier -/

/-- The outer input oracles: `F true = not` and `F false = id`. -/
def outerData : ∀ _ : Bool, Bool → Bool
  | true => not
  | false => id

/-- The oracle message `g = id`. -/
def message : (oracleMessageBundle protocol path).Data := (id, ())

/-- With tag `true`, the inner input oracle is `x ↦ not (!x) = x`, so `f true = true` and the
lifted verifier accepts `xor true r`. -/
example (r : Bool) :
    outerVerifier.decideWith true path (view r) (outerData, message) = pure (some (!r)) := by
  cases r <;> rfl

/-- With tag `false`, the inner input oracle is `x ↦ id (!x)`, so `f true = false` and the lifted
verifier rejects. -/
example (r : Bool) :
    outerVerifier.decideWith false path (view r) (outerData, message) = pure none := by
  cases r <;> rfl

/-- With tag `true`, the output oracle is `x ↦ F false x && g x = x`. -/
example (r : Bool) :
    (outerVerifier.outputMap true path (view r)).f (outerData, message) ⟨⟩ = id := by
  funext x
  cases x <;> rfl

/-- With tag `false`, the output oracle is `x ↦ F true x && g x = false`. -/
example (r : Bool) :
    (outerVerifier.outputMap false path (view r)).f (outerData, message) ⟨⟩ = fun _ => false := by
  funext x
  cases x <;> rfl

/-- A routed query of the lifted output oracle at `true`, answered from the outer input data and
the oracle message, agrees with the materialized output oracle at `true` (the `OracleMap` law). -/
example (r : Bool) :
    simulateQ ((pathBundle fnPair protocol path).answer (outerData, message))
        ((outerVerifier.outputMap true path (view r)).impl ⟨⟨⟩, true⟩) =
      ((outerVerifier.outputMap true path (view r)).f (outerData, message) ⟨⟩ true : Bool) := rfl

/-- The same routed query with tag `false` returns `F true true && g true = false`. -/
example (r : Bool) :
    simulateQ ((pathBundle fnPair protocol path).answer (outerData, message))
        ((outerVerifier.outputMap false path (view r)).impl ⟨⟨⟩, true⟩) = (false : Bool) := rfl

/-! ### Soundness through the transfer -/

/-- Inner inputs whose oracle answers `true` at `true`. -/
@[instance_reducible] def innerInput : StatementProblem (Unit × (fn : OracleBundle).Data) where
  Witness _ _ := Unit
  admissible _ _ := True
  rel _ x _ := x.2 ⟨⟩ true = true
  rel_admissible _ _ _ _ := trivial

/-- Outer inputs whose oracle `F b` answers `true` at `false`. -/
@[instance_reducible] def outerInput : StatementProblem (Bool × (fnPair : OracleBundle).Data) where
  Witness _ _ := Unit
  admissible _ _ := True
  rel _ x _ := x.2 x.1 false = true
  rel_admissible _ _ _ _ := trivial

/-- An output statement `Bool` with one output oracle `Bool → Bool`, at every path. -/
abbrev Output : Path protocol → Type :=
  OracleVerifier.Output (s := protocol) (fun _ => Bool) (fun _ => (fn : OracleBundle))

/-- Outputs whose output oracle answers `true` at `true`. -/
@[instance_reducible] def outputProblem : PathProblem protocol Output where
  Witness _ _ := Unit
  admissible _ _ := True
  rel _ t _ := t.2 ⟨⟩ true = true
  rel_admissible _ _ _ _ := trivial

/-- The inner verifier never accepts an input whose oracle answers `false` at `true`. -/
theorem innerVerifier_soundness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl noAmbient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec oracleSig protocol) ProbComp) :
    innerVerifier.soundness init impl challenges innerInput outputProblem 0 := by
  rw [OracleVerifier.soundness_iff_soundnessUsing]
  intro Out stmt _ hlang prover
  refine le_of_eq (prEvent_eq_zero_of_forall_mem_support _ _ fun obs hobs => ?_)
  rintro ⟨t, ht, -⟩
  obtain ⟨v, msgs, hv, -⟩ := innerVerifier.compatible_of_mem_support_run _ _ prover
    (support_experiment_subset _ _ _ _ hobs) ht
  have hfalse : stmt.2 ⟨⟩ true = false := by
    simpa [innerInput, Problem.language] using hlang
  revert v msgs
  generalize obs.1.path = p
  rcases p with ⟨⟨⟩, ⟨⟩, ⟨⟩⟩
  intro v msgs hv
  have hd : innerVerifier.decideWith stmt.1 path v (stmt.2, msgs) =
      pure (if stmt.2 ⟨⟩ true then some v.val.1 else none) := rfl
  rw [hd, hfalse] at hv
  simp at hv

/-- The lens projects a false outer input to a false inner input, and a lifted output oracle
that answers `true` at `true` comes from an inner output oracle that does. -/
theorem lens_isSound :
    lens.toStatementLens.IsSound outerInput innerInput outputProblem outputProblem
      innerVerifier.Compatible where
  proj_sound _ _ hlang := ⟨trivial, fun ⟨w, hw⟩ => hlang ⟨w, hw⟩⟩
  lift_sound _ _ _ _ _ _ := fun ⟨w, hw⟩ => ⟨w, (Bool.and_eq_true _ _).mp hw |>.2⟩

/-- Soundness with error `0` of the lifted verifier, from the inner one. -/
theorem outerVerifier_soundness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl noAmbient (StateT σ ProbComp))
    (challenges : QueryImpl (challengeSpec oracleSig protocol) ProbComp) :
    outerVerifier.soundness init impl challenges outerInput outputProblem 0 :=
  OracleVerifier.liftContext_soundness lens innerVerifier init impl challenges lens_isSound
    (innerVerifier_soundness init impl challenges)

end Interaction.OracleLiftContextTests
