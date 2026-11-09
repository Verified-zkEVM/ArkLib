import ArkLib.Interaction.Core.Composition
import ArkLibTest.Interaction.Core.Oracle

/-! Terminal rejection never prevents the suffix interaction or its leaf effects. -/

open PFunctor PFunctor.FreeM Interaction.Core Interaction.TwoParty.Lens OracleComp

namespace Interaction.Core.CompositionTests

abbrev done : Protocol := .pure ⟨⟩
abbrev ambient : OracleSpec Nat := Nat →ₒ PUnit

def firstProver : Prover plainSig ambient done (fun _ => PUnit) := do
  liftM (ambient.query 0)
  pure ⟨⟩

def suffix : Prover plainSig ambient done (fun _ => PUnit) := do
  liftM (ambient.query 2)
  pure ⟨⟩

def composed : Prover plainSig ambient (done.append (fun _ => done)) (fun _ => PUnit) :=
  Prover.append firstProver (fun _ _ => do
    liftM (ambient.query 1)
    pure suffix)

def reject : Verifier ambient done Unit Unit where
  decide _ _ _ := OptionT.mk do
    liftM (ambient.query 3)
    pure none

def accept : Verifier ambient done Unit Unit where
  decide _ _ _ := do
    liftM (ambient.query 4)
    pure ()

def traceHandler : QueryImpl (ambient + challengeSpec plainSig (done.append (fun _ => done)))
    (StateM (List Nat))
  | .inl n => do
    modify (· ++ [n])
    pure ⟨⟩
  | .inr c => c.val.elim

run_cmd do
  let (obs, trace) := (simulateQ traceHandler
    ((reject.append (fun _ => accept)).run () composed)).run []
  unless trace == [0, 1, 2, 3] do
    throwError "suffix or terminal effects were skipped or reordered: {trace}"
  unless obs.2.2 == none do throwError "prefix rejection was lost"

open Interaction.Core.OracleTests

/-- A suffix computes a virtual output from an embedded prefix oracle. -/
def virtualSuffix : OracleVerifier OracleSpec.emptySpec emptyTree Nat Unit functions functions where
  decide _ _ _ := pure ()
  outputMap _ p _ := doubled.comp
    (OracleMap.embedding (sumFamily functions (pathFamily emptyTree p))
      (fun _ => Sum.inl PUnit.unit))

def compatible : OracleVerifier.OutputCompatibility queryDecision (fun _ => virtualSuffix) where
  outputMap stmt p v :=
    (virtualSuffix.outputMap 0 (Path.split tree (fun _ => emptyTree) p).2
      (View.split tree (fun _ => emptyTree) p v).2).comp
      (OracleVerifier.suffixRoute queryDecision stmt p v)
  agrees _ _ _ _ _ _ := rfl

def combined := queryDecision.append (fun _ => virtualSuffix) compatible

def oracleProver : Prover oracleSig OracleSpec.emptySpec
    (tree.append (fun _ => emptyTree)) (fun _ => PUnit) :=
  pure ⟨fun n => n + 5, pure ⟨⟩⟩

def oracleHandler : QueryImpl
    (OracleSpec.emptySpec + challengeSpec oracleSig (tree.append (fun _ => emptyTree))) Id
  | .inl i => i.elim
  | .inr ⟨.inl _, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, i⟩, _⟩ => i.elim

run_cmd do
  let obs := simulateQ oracleHandler (combined.run () (fun i => i.elim) oracleProver)
  match obs.2.2 with
  | none => throwError "composed oracle decision rejected"
  | some (_, data) =>
    unless data ⟨⟩ 3 == 16 do throwError "composed virtual output disagrees with routing"

/-- The prefix accepts only `false` and never consults the ambient oracle. -/
def deterministicPrefix : OracleVerifier (Unit →ₒ Bool) emptyTree Unit Bool
    emptyFamily emptyFamily where
  decide _ _ _ := pure false
  outputMap := ambientPrefix.outputMap

/-- Only the statement the prefix can accept constrains the composite output map. -/
def deterministicCompatible :
    OracleVerifier.OutputCompatibility deterministicPrefix (fun _ => constantSuffix) :=
  .ofStatement _ _ (fun _ _ _ => false) fun _ _ _ _ t h => by
    simpa [OracleVerifier.decideWith, deterministicPrefix] using h

def deterministicAppend :=
  deterministicPrefix.append (fun _ => constantSuffix) deterministicCompatible

def unitProver : Prover oracleSig (Unit →ₒ Bool) (emptyTree.append (fun _ => emptyTree))
    (fun _ => PUnit) := pure ⟨⟩

def bitHandler : QueryImpl
    ((Unit →ₒ Bool) + challengeSpec oracleSig (emptyTree.append (fun _ => emptyTree))) Id
  | .inl _ => true
  | .inr ⟨n, _⟩ => n.elim

run_cmd do
  let obs := simulateQ bitHandler
    (deterministicAppend.run () (fun i => i.elim) unitProver)
  match obs.2.2 with
  | none => throwError "the deterministic composition rejected"
  | some (_, data) =>
    unless data ⟨⟩ 0 == 0 do throwError "the composite output ignores the accepted prefix"

/-- A prefix bit read from the ambient oracle can be either value, so no certificate exists. -/
example : ¬ Nonempty
    (OracleVerifier.OutputCompatibility ambientPrefix (fun _ => constantSuffix)) := by
  rintro ⟨c⟩
  let p : Path (emptyTree.append (fun _ => emptyTree)) := ⟨⟩
  let v : View (emptyTree.append (fun _ => emptyTree)) p := ⟨⟨⟩, rfl⟩
  have reach : ∀ bit, some bit ∈ support (ambientPrefix.decideWith ()
      (Path.split emptyTree (fun _ => emptyTree) p).1
      (View.split emptyTree (fun _ => emptyTree) p v).1
      ((OracleVerifier.prefixRoute (inputs := emptyFamily) p).f emptyData)) := by
    intro bit
    change some bit ∈ support (simulateQ _
      ((liftM (((Unit →ₒ Bool) + emptyResources.spec).query (.inl ())) :
        OptionT (OracleComp ((Unit →ₒ Bool) + emptyResources.spec)) Bool).run))
    simp
  have h₀ := congrFun (congrFun (c.agrees () p v emptyData false (reach false)) PUnit.unit) 0
  have h₁ := congrFun (congrFun (c.agrees () p v emptyData true (reach true)) PUnit.unit) 0
  change (c.outputMap () p v).f emptyData PUnit.unit 0 = 0 at h₀
  change (c.outputMap () p v).f emptyData PUnit.unit 0 = 1 at h₁
  exact Nat.zero_ne_one (h₀.symm.trans h₁)

end Interaction.Core.CompositionTests

run_cmd do
  for decl in [``Interaction.Core.appendSampler_eq, ``Interaction.Core.appendOracleSampler_eq,
      ``Interaction.Core.run_appendSampler, ``Interaction.Core.run_splitSampler,
      ``Interaction.Core.OracleVerifier.append,
      ``Interaction.Core.OracleVerifier.append_decideWith,
      ``Interaction.Core.OracleMap.simulate_withAmbient] do
    for ax in ← Lean.collectAxioms decl do
      unless [``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "unexpected axiom {ax} in {decl}"
