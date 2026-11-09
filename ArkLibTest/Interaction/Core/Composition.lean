import ArkLib.Interaction.Core.Composition
import ArkLibTest.Interaction.Core.Oracle

/-! Terminal rejection never prevents the suffix interaction or its leaf effects. Composed oracle
decisions route suffix queries as materialized execution answers them. -/

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

/-! Routing a suffix decision through both its input oracle and its own message oracle. -/

/-- Ambient queries carry a label, which the trace handler records. -/
abbrev labels : OracleSpec Nat := Nat →ₒ Nat

abbrev twoStages : OracleProtocol := tree.append (fun _ => tree)

/-- The prefix output is either its own message or a virtual oracle computed from it. -/
abbrev PrefixOutput :=
  (p : Path tree) → OracleMap (sumFamily emptyFamily (pathFamily tree p)) functions

def embeddedOutput : PrefixOutput := fun p =>
  OracleMap.embedding (sumFamily emptyFamily (pathFamily tree p)) (fun _ => .inr (.inl ⟨⟩))

def virtualOutput : PrefixOutput := fun p => doubled.comp (embeddedOutput p)

/-- The prefix records label 10, then evaluates its message at 3. -/
def routedPrefix (out : PrefixOutput) :
    OracleVerifier labels tree Unit Nat emptyFamily functions where
  decide _ p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact do
      let _ ← liftM ((labels + (sumFamily emptyFamily (pathFamily tree ⟨⟨⟩, ⟨⟩⟩)).spec).query
        (.inl 10))
      let n : Nat ← liftM ((labels + (sumFamily emptyFamily (pathFamily tree ⟨⟨⟩, ⟨⟩⟩)).spec).query
        (.inr ⟨.inr (.inl ⟨⟩), (3 : Nat)⟩))
      pure n
  outputMap _ p _ := out p

/-- The suffix records 20, evaluates its input oracle and its own message at 1, then records 30. -/
def routedSuffix : OracleVerifier labels tree Nat (Nat × Nat × Nat) functions functions where
  decide mid p _ := by
    rcases p with ⟨⟨⟩, ⟨⟩⟩
    exact do
      let _ ← liftM ((labels + (sumFamily functions (pathFamily tree ⟨⟨⟩, ⟨⟩⟩)).spec).query
        (.inl 20))
      let input : Nat ← liftM
        ((labels + (sumFamily functions (pathFamily tree ⟨⟨⟩, ⟨⟩⟩)).spec).query
          (.inr ⟨.inl ⟨⟩, (1 : Nat)⟩))
      let message : Nat ← liftM
        ((labels + (sumFamily functions (pathFamily tree ⟨⟨⟩, ⟨⟩⟩)).spec).query
          (.inr ⟨.inr (.inl ⟨⟩), (1 : Nat)⟩))
      let _ ← liftM ((labels + (sumFamily functions (pathFamily tree ⟨⟨⟩, ⟨⟩⟩)).spec).query
        (.inl 30))
      pure (mid, input, message)
  outputMap _ p _ := OracleMap.embedding (sumFamily functions (pathFamily tree p))
    (fun _ => .inr (.inl ⟨⟩))

/-- The suffix output map ignores the intermediate statement. -/
def routedCompatible (out : PrefixOutput) :
    OracleVerifier.OutputCompatibility (routedPrefix out) (fun _ => routedSuffix) where
  outputMap stmt p v :=
    (routedSuffix.outputMap 0 (Path.split tree (fun _ => tree) p).2
      (View.split tree (fun _ => tree) p v).2).comp
      (OracleVerifier.suffixRoute (routedPrefix out) stmt p v)
  agrees _ _ _ _ _ _ := rfl

def routed (out : PrefixOutput) :=
  (routedPrefix out).append (fun _ => routedSuffix) (routedCompatible out)

def firstMessage : PathAlong oracleSig tree := ⟨fun n => n + 5, ⟨⟩⟩
def secondMessage : PathAlong oracleSig tree := ⟨fun n => 7 * n, ⟨⟩⟩

def twoStageProver : Prover oracleSig labels twoStages (fun _ => PUnit) :=
  pure ⟨firstMessage.1, pure ⟨secondMessage.1, pure ⟨⟩⟩⟩

def labelHandler : QueryImpl labels (StateM (List Nat)) := fun n => do
  modify (· ++ [n])
  pure n

def twoStageHandler : QueryImpl (labels + challengeSpec oracleSig twoStages)
    (StateM (List Nat))
  | .inl n => labelHandler n
  | .inr ⟨.inl _, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inl _⟩, h⟩ => nomatch h
  | .inr ⟨.inr ⟨_, .inr ⟨_, n⟩⟩, _⟩ => n.elim

/-- Decide each stage separately on materialized data: the prefix on its own payload, the suffix
on the prefix's materialized output and its own payload. -/
def materialized (out : PrefixOutput) : OracleComp labels (Option (Nat × Nat × Nat)) := do
  let prefixData := sumData (fun i => i.elim) (payloads tree firstMessage)
  let mid ← (routedPrefix out).decideWith () _ (toView tree firstMessage) prefixData
  match mid with
  | none => pure none
  | some mid =>
    let middleData := ((routedPrefix out).outputMap () _ (toView tree firstMessage)).f prefixData
    routedSuffix.decideWith mid _ (toView tree secondMessage)
      (sumData middleData (payloads tree secondMessage))

def checkRouting (out : PrefixOutput) (input : Nat) : Lean.Elab.Command.CommandElabM Unit := do
  let (obs, trace) := (simulateQ twoStageHandler
    ((routed out).run () (fun i => i.elim) twoStageProver)).run []
  let (expected, expectedTrace) := (simulateQ labelHandler (materialized out)).run []
  unless trace == [10, 20, 30] && expectedTrace == trace do
    throwError "routed ambient queries were reordered: {trace} versus {expectedTrace}"
  match obs.2.2, expected with
  | some (verdict, data), some materializedVerdict =>
    unless verdict == (8, input, 7) && materializedVerdict == verdict do
      throwError "routing disagrees with materialized execution: {verdict}"
    unless data ⟨⟩ 3 == 21 do throwError "the composite output is not the suffix message"
  | _, _ => throwError "a routed or materialized decision rejected"

run_cmd checkRouting embeddedOutput 6
run_cmd checkRouting virtualOutput 12

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
