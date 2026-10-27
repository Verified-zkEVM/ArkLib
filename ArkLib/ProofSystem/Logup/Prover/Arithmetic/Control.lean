/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Prover.Arithmetic.State
public import ArkLib.ProofSystem.Logup.Prover.Arithmetic.Round
public import ArkLib.ProofSystem.Logup.Prover.Reference

import all PolyFun.Interaction.Basic.StrategyOver
import all PolyFun.Interaction.TwoParty.Strategy

/-!
# Shared arithmetic control for the honest prover

One ordinary control core selects the named preparation, equality-cache, message and private-fold
programs. Its terminal output can retain Unit, the existing primitive-request profile, or complete
call descriptions. The Unit interpretation retains no profile or call trace. The description at
an individual call carries its actual arguments and selects the same arithmetic program in every
interpretation; it does not introduce another arithmetic language or protocol.

Public abort ends the continuation. A successful final round needs no subsequent private fold,
and zero native rounds need no private cache initialization. All interpretations preserve the
reference honest strategy after their terminal annotations are erased. Exact observed-call
accounting and whole-prover resource envelopes are separate statements.
-/

@[expose] public section

open Interaction.Oracle OracleComp OracleSpec CompPoly Logup.Interaction
namespace Logup.Prover.Honest.Accounting
/-- A complete description of one explicitly selected private arithmetic program. -/
inductive Call (B E : Type) [CommRing B] [CommRing E] (T K : Nat) where
  | prepare (n : Nat) (f : B →+* E) (alpha : E) (groups : Vector (List (Fin T)) K)
      (data : Fin 2 × Fin T → CMlPolynomialEval B n)
  | start (n : Nat) (prepared : Logup.Prover.Prepared E T K n)
      (z : Fin n → E) (lambda : Fin K → E)
  | message (r : Nat) (groups : Vector (List (Fin T)) K)
      (state : Logup.Prover.State E T K (r + 1))
  | fold (r : Nat) (state : Logup.Prover.State E T K (r + 1)) (challenge : E)

variable {B E C : Type} [CommRing B] [CommRing E] [Inv E] [DecidableEq E] {T K : Nat}

/-- The ordinary result type of a selected arithmetic call. -/
def Call.Result : Call B E T K → Type
  | .prepare n _ _ _ _ => Logup.Prover.Prepared E T K n
  | .start n _ _ _ => Logup.Prover.State E T K n
  | .message _ _ _ => CPolynomial E
  | .fold r _ _ => Logup.Prover.State E T K r

/-- Select the existing arithmetic program on the retained call arguments. -/
def Call.program (call : Call B E T K) : OracleComp (ArithmeticSpec E) call.Result :=
  match call with
  | .prepare _ f alpha groups data => State.prepareProgram f alpha groups data
  | .start _ prepared z lambda => State.startProgram prepared z lambda
  | .message _ groups state => RoundCoefficients.messageProgram groups state.lambda
      state.denominator state.weight state.helper state.kernel
  | .fold _ state r => State.foldProgram state r

/-- An interpretation of the existing arithmetic programs with one terminal annotation. -/
abbrev Interpreter (B E C : Type) [CommRing B] [CommRing E] [Inv E] [DecidableEq E] (T K : Nat) :=
  {A : Type} → Call B E T K → OracleComp (ArithmeticSpec E) A → A × C

/-- Execute arithmetic without retaining a profile or call trace. -/
def unitInterpreter : Interpreter B E Unit T K :=
  fun _ program => (simulateQ arithmeticAnswer program, ())
/-- Execute the same program and retain its existing primitive-request profile. -/
def costInterpreter : Interpreter B E ArithmeticCost T K :=
  fun _ program => profileArithmetic program
/-- Execute the same program and retain its complete call description. -/
def callInterpreter : Interpreter B E (List (Call B E T K)) T K :=
  fun call program => (simulateQ arithmeticAnswer program, [call])

/-- The ordinary result agrees with deterministic execution of the same arithmetic program. -/
def Erases (run : Interpreter B E C T K) : Prop :=
  ∀ {A : Type} (call : Call B E T K) (program : OracleComp (ArithmeticSpec E) A),
    (run call program).1 = simulateQ arithmeticAnswer program

/-- Unit instrumentation preserves the exact arithmetic result. -/
theorem unit_erases : Erases (unitInterpreter (B := B) (E := E) (T := T) (K := K)) :=
  fun _ _ => rfl

/-- Erasing the primitive-request profile preserves the exact arithmetic result. -/
theorem cost_erases : Erases (costInterpreter (B := B) (E := E) (T := T) (K := K)) :=
  fun _ _ => profileArithmetic_fst _

/-- Erasing a call description preserves the exact arithmetic result. -/
theorem call_erases : Erases (callInterpreter (B := B) (E := E) (T := T) (K := K)) :=
  fun _ _ => rfl

/-- Execute the selected coefficient-message program and retain its annotation. -/
def messageWith (run : Interpreter B E C T K) (law : Erases run)
    {ell r : Nat} (groups : Vector (List (Fin T)) K)
    (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (state : Logup.Prover.State E T K (r + 1)) :
    Sumcheck.Impl.Representation.Message E (ell + 2) × C :=
  let call := Call.message (B := B) r groups state
  let result := run call call.program
  (⟨result.1, by
    rw [law]
    exact (RoundCoefficients.messageByProgram groups hgroups state.lambda state.denominator
      state.weight state.helper state.kernel).property⟩, result.2)

/-- Every interpretation returns the same formally certified coefficient message. -/
theorem messageWith_fst (run : Interpreter B E C T K) (law : Erases run)
    {ell r : Nat} (groups : Vector (List (Fin T)) K)
    (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (state : Logup.Prover.State E T K (r + 1)) :
    (messageWith run law groups hgroups state).1 = pureBuilder groups hgroups r state := by
  apply Subtype.ext
  exact (law _ _).trans (RoundCoefficients.simulateQ_messageProgram _ _ _ _ _ _)

/-- Execute native messages and only the private folds consumed by later rounds. -/
def nativeWith (run : Interpreter B E C T K) (law : Erases run) (combine : C → C → C)
    {ell : Nat} {ι : Type} (ambient : OracleSpec ι)
    (groups : Vector (List (Fin T)) K) (hgroups : ∀ k, (groups.get k).length ≤ ell) :
    (count : Nat) → Logup.Prover.State E T K count → C →
      Prover.Strategy ambient (Sumcheck.Interaction.Computable.protocol E (ell + 2) count).tree
        (Sumcheck.Interaction.Computable.protocol E (ell + 2) count).roles (fun _ => C)
  | 0, _, acc => acc
  | 1, state, acc =>
    let message := messageWith run law groups hgroups state
    pure ⟨message.1, fun choice => match choice with
      | none => pure (combine acc message.2)
      | some _ => pure (combine acc message.2)⟩
  | count + 2, state, acc =>
    let message := messageWith run law groups hgroups state
    pure ⟨message.1, fun choice => match choice with
      | none => pure (combine acc message.2)
      | some r =>
        let call := Call.fold (B := B) (count + 1) state r
        let next := run call call.program
        pure (nativeWith run law combine ambient groups hgroups (count + 1) next.1
          (combine (combine acc message.2) next.2))⟩

/-- An ordinary native continuation with a constant terminal output type. -/
abbrev NativeStrategy {ι : Type} (ambient : OracleSpec ι) (ell count : Nat) (C : Type) :=
  Prover.Strategy ambient (Sumcheck.Interaction.Computable.protocol E (ell + 2) count).tree
    (Sumcheck.Interaction.Computable.protocol E (ell + 2) count).roles (fun _ => C)

/-- Erasing terminal annotations gives the reference native honest continuation. -/
theorem nativeWith_erases (run : Interpreter B E C T K) (law : Erases run)
    (combine : C → C → C) {ell : Nat} {ι : Type} (ambient : OracleSpec ι)
    (groups : Vector (List (Fin T)) K) (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (count : Nat) (state : Logup.Prover.State E T K count) (acc : C) :
    Interaction.StrategyOver.TwoParty.Focal.mapOutput (fun _ _ => ())
      (nativeWith run law combine ambient groups hgroups count state acc) =
      Logup.Prover.Honest.nativeWith ambient (pureBuilder groups hgroups) count state := by
  induction count generalizing acc with
  | zero => rfl
  | succ count ih =>
    cases count with
    | zero =>
      simp only [nativeWith, Logup.Prover.Honest.nativeWith,
        Interaction.StrategyOver.TwoParty.Focal.mapOutput, Interaction.ShapeOver.mapOutput,
        Interaction.ShapeOver.TwoParty.pairedTypeTree, Interaction.ShapeOver.TwoParty.paired,
        PFunctor.Lens.id, Sumcheck.Interaction.Computable.protocol,
        Sumcheck.Interaction.Native.Core.protocol,
        Protocol.oracleWith, Protocol.public, Protocol.done, TypeTree.toTypeTree,
        PFunctor.FreeM.mapLens, TypeTree.runtimeLens,
        TypeTree.RoleDecoration.toTypeTreeRoles, map_pure, messageWith_fst]
      congr 1
      congr 1
      funext choice
      cases choice <;> rfl
    | succ count =>
      simp only [nativeWith, Logup.Prover.Honest.nativeWith,
        Interaction.StrategyOver.TwoParty.Focal.mapOutput, Interaction.ShapeOver.mapOutput,
        Interaction.ShapeOver.TwoParty.pairedTypeTree, Interaction.ShapeOver.TwoParty.paired,
        PFunctor.Lens.id, Sumcheck.Interaction.Computable.protocol,
        Sumcheck.Interaction.Native.Core.protocol,
        Protocol.oracleWith, Protocol.public, Protocol.done, TypeTree.toTypeTree,
        PFunctor.FreeM.mapLens, TypeTree.runtimeLens,
        TypeTree.RoleDecoration.toTypeTreeRoles, map_pure, messageWith_fst]
      congr 1
      congr 1
      funext choice
      cases choice with
      | none => rfl
      | some r =>
        change (fun continuation => Interaction.StrategyOver.TwoParty.Focal.mapOutput
          (fun _ _ => ()) continuation) <$>
            pure (nativeWith run law combine ambient groups hgroups (count + 1)
              (run (Call.fold (B := B) (count + 1) state r)
                (Call.fold (B := B) (count + 1) state r).program).1
              (combine (combine acc (messageWith run law groups hgroups state).2)
                (run (Call.fold (B := B) (count + 1) state r)
                  (Call.fold (B := B) (count + 1) state r).program).2)) =
            pure (Logup.Prover.Honest.nativeWith ambient (pureBuilder groups hgroups) (count + 1)
              (State.fold state r))
        rw [map_pure]
        have h := ih
          (run (Call.fold (B := B) (count + 1) state r)
                (Call.fold (B := B) (count + 1) state r).program).1
          (combine (combine acc (messageWith run law groups hgroups state).2)
            (run (Call.fold (B := B) (count + 1) state r)
              (Call.fold (B := B) (count + 1) state r).program).2)
        have hfst :
            (run (Call.fold (B := B) (count + 1) state r)
              (Call.fold (B := B) (count + 1) state r).program).1 = State.fold state r :=
          (law _ _).trans (State.simulateQ_foldProgram state r)
        exact (congrArg (fun continuation => pure continuation) h).trans
          (congrArg (fun next => pure
            (Logup.Prover.Honest.nativeWith ambient (pureBuilder groups hgroups)
              (count + 1) next)) hfst)

/-- Initialize a private equality cache only when a native message follows. -/
def startWith (run : Interpreter B E C T K) (law : Erases run) (combine : C → C → C)
    {ell : Nat} {ι : Type} (ambient : OracleSpec ι)
    (groups : Vector (List (Fin T)) K) (hgroups : ∀ k, (groups.get k).length ≤ ell) :
    (count : Nat) → Logup.Prover.Prepared E T K count → (Fin count → E) → (Fin K → E) → C →
      NativeStrategy (E := E) ambient ell count C
  | 0, _, _, _, acc => acc
  | count + 1, prepared, z, lambda, acc =>
    let call := Call.start (count + 1) prepared z lambda
    let started := run call call.program
    nativeWith run law combine ambient groups hgroups (count + 1) started.1
      (combine acc started.2)

/-- Execute preparation, send its actual helpers, and continue through the shared control. -/
def proverWith {B E C : Type} [CommRing B] [Field E] [DecidableEq E] {n T ell : Nat}
    (run : Interpreter B E C T (T ⌈/⌉ ell)) (law : Erases run) (combine : C → C → C)
    (initial : C) (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) {ι : Type} (ambient : OracleSpec ι) :
    Prover.Strategy ambient (protocol E n (T ⌈/⌉ ell) ell).tree
      (protocol E n (T ⌈/⌉ ell) ell).roles (fun _ => C) :=
  fun (alpha : E) => pure (do
    let call := Call.prepare n f alpha cfg.groups data
    let prepared := run call call.program
    return ⟨prepared.1.helper, fun joint =>
      pure (startWith run law combine ambient cfg.groups cfg.length_group_le n prepared.1
        joint.1 joint.2 (combine initial prepared.2))⟩)

/-- The Unit interpretation is the reference native honest continuation. -/
theorem native_unit_eq {ell : Nat} {ι : Type} (ambient : OracleSpec ι)
    (groups : Vector (List (Fin T)) K) (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (count : Nat) (state : Logup.Prover.State E T K count) :
    nativeWith (unitInterpreter (B := B)) unit_erases (fun _ _ => ()) ambient groups hgroups
      count state () =
      Logup.Prover.Honest.nativeWith ambient (pureBuilder groups hgroups) count state := by
  let strategy := nativeWith (unitInterpreter (B := B)) unit_erases (fun _ _ => ()) ambient
    groups hgroups count state ()
  have hid : Interaction.StrategyOver.TwoParty.Focal.mapOutput (fun _ _ => ()) strategy =
      strategy := by
    have h := Interaction.StrategyOver.TwoParty.Focal.mapOutput_id strategy
    convert h using 1
  exact hid.symm.trans (nativeWith_erases _ unit_erases _ ambient groups hgroups count state ())

/-- All native interpretations erase to the same selected Unit driver. -/
theorem nativeWith_erases_unit (run : Interpreter B E C T K) (law : Erases run)
    (combine : C → C → C) {ell : Nat} {ι : Type} (ambient : OracleSpec ι)
    (groups : Vector (List (Fin T)) K) (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (count : Nat) (state : Logup.Prover.State E T K count) (acc : C) :
    Interaction.StrategyOver.TwoParty.Focal.mapOutput (fun _ _ => ())
      (nativeWith run law combine ambient groups hgroups count state acc) =
      nativeWith (unitInterpreter (B := B)) unit_erases (fun _ _ => ()) ambient groups hgroups
        count state () :=
  (nativeWith_erases run law combine ambient groups hgroups count state acc).trans
    (native_unit_eq (B := B) ambient groups hgroups count state).symm

/-- Cache initialization and its native continuation erase to the selected Unit driver. -/
theorem startWith_erases_unit (run : Interpreter B E C T K) (law : Erases run)
    (combine : C → C → C) {ell : Nat} {ι : Type} (ambient : OracleSpec ι)
    (groups : Vector (List (Fin T)) K) (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (count : Nat) (prepared : Logup.Prover.Prepared E T K count)
    (z : Fin count → E) (lambda : Fin K → E) (acc : C) :
    Interaction.StrategyOver.TwoParty.Focal.mapOutput (fun _ _ => ())
      (startWith run law combine ambient groups hgroups count prepared z lambda acc) =
      startWith (unitInterpreter (B := B)) unit_erases (fun _ _ => ()) ambient groups hgroups
        count prepared z lambda () := by
  cases count with
  | zero => rfl
  | succ count =>
    let call : Call B E T K := Call.start (count + 1) prepared z lambda
    change Interaction.StrategyOver.TwoParty.Focal.mapOutput (fun _ _ => ())
      (nativeWith run law combine ambient groups hgroups (count + 1) (run call call.program).1
        (combine acc (run call call.program).2)) =
      nativeWith (unitInterpreter (B := B)) unit_erases (fun _ _ => ()) ambient groups hgroups
        (count + 1) (simulateQ arithmeticAnswer call.program) ()
    exact (nativeWith_erases_unit run law combine ambient groups hgroups (count + 1)
      (run call call.program).1 (combine acc (run call call.program).2)).trans
        (congrArg (fun state => nativeWith (unitInterpreter (B := B)) unit_erases
          (fun _ _ => ()) ambient groups hgroups (count + 1) state ()) (law call call.program))

/-- Skipping a zero-round cache preserves the reference ordinary continuation. -/
theorem start_unit_eq_nativeWith {ell : Nat} {ι : Type} (ambient : OracleSpec ι)
    (groups : Vector (List (Fin T)) K) (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (count : Nat) (prepared : Logup.Prover.Prepared E T K count)
    (z : Fin count → E) (lambda : Fin K → E) :
    startWith (unitInterpreter (B := B)) unit_erases (fun _ _ => ()) ambient groups hgroups
      count prepared z lambda () =
      Logup.Prover.Honest.nativeWith ambient (pureBuilder groups hgroups) count
        (State.start prepared z lambda) := by
  cases count with
  | zero => rfl
  | succ count =>
    change nativeWith (unitInterpreter (B := B)) unit_erases (fun _ _ => ()) ambient groups
      hgroups (count + 1) (simulateQ arithmeticAnswer (State.startProgram prepared z lambda)) () = _
    rw [State.simulateQ_startProgram]
    exact native_unit_eq (B := B) ambient groups hgroups (count + 1) _

/-- The complete Unit interpretation is the reference honest strategy. -/
theorem prover_unit_eq_honestWith {B E : Type} [CommRing B] [Field E] [DecidableEq E]
    {n T ell : Nat} (f : B →+* E) (cfg : Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) {ι : Type} (ambient : OracleSpec ι) :
    proverWith unitInterpreter unit_erases (fun _ _ => ()) () f cfg data ambient =
      Logup.Prover.Honest.honestWith f cfg data ambient
        (pureBuilder cfg.groups cfg.length_group_le) := by
  unfold proverWith Logup.Prover.Honest.honestWith
  funext alpha
  simp only [unitInterpreter, Call.program]
  have hprepared := State.simulateQ_prepareProgram f alpha cfg data
  congr 1
  congr 1
  congr 1
  · exact congrArg (fun prepared => prepared.helper) hprepared
  · funext joint
    congr 1
    exact (start_unit_eq_nativeWith (B := B) ambient cfg.groups cfg.length_group_le n
      (simulateQ arithmeticAnswer (State.prepareProgram f alpha cfg.groups data))
      joint.1 joint.2).trans
        (congrArg (fun prepared => Logup.Prover.Honest.nativeWith ambient
          (pureBuilder cfg.groups cfg.length_group_le) n
            (State.start prepared joint.1 joint.2)) hprepared)

set_option backward.isDefEq.respectTransparency false in
/-- Erasing terminal annotations preserves the actual Unit driver's caches and messages. -/
theorem proverWith_erases_unit {B E C : Type} [CommRing B] [Field E] [DecidableEq E]
    {n T ell : Nat}
    (run : Interpreter B E C T (T ⌈/⌉ ell))
    (law : Erases run) (combine : C → C → C) (initial : C)
    (f : B →+* E) (cfg : Logup.Interaction.Config n T ell)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n)
    {ι : Type} (ambient : OracleSpec ι) :
    Interaction.StrategyOver.TwoParty.Focal.mapOutput (fun _ _ => ())
      (proverWith run law combine initial
        f cfg data ambient) =
      proverWith
        unitInterpreter unit_erases
        (fun _ _ => ()) () f cfg data ambient := by
  simp only [proverWith,
    Interaction.StrategyOver.TwoParty.Focal.mapOutput, Interaction.ShapeOver.mapOutput,
    Interaction.ShapeOver.TwoParty.pairedTypeTree, Interaction.ShapeOver.TwoParty.paired,
    PFunctor.Lens.id, Logup.Interaction.protocol, Logup.Interaction.prefixProtocol,
    Protocol.oracleWith, Protocol.public, Protocol.done, Protocol.tree, Protocol.roles,
    Protocol.oracles, TypeTree.public, TypeTree.oracle, TypeTree.done, TypeTree.toTypeTree,
    PFunctor.FreeM.Displayed.Decoration.append,
    PFunctor.FreeM.mapLens, PFunctor.FreeM.append, TypeTree.runtimeLens,
    TypeTree.RoleDecoration.toTypeTreeRoles, map_pure]
  funext alpha
  let call := Call.prepare n f alpha cfg.groups data
  have hp := law call call.program
  congr 1
  congr 1
  congr 1
  · exact congrArg (fun prepared : Logup.Prover.Prepared E T (T ⌈/⌉ ell) n =>
      prepared.helper) hp
  · funext joint
    congr 1
    change Interaction.StrategyOver.TwoParty.Focal.mapOutput (fun _ _ => ())
      (startWith run law combine ambient cfg.groups
        cfg.length_group_le n (run call call.program).1 joint.1 joint.2
        (combine initial (run call call.program).2)) = _
    rw [hp]
    exact startWith_erases_unit run law combine ambient cfg.groups
      cfg.length_group_le n (simulateQ arithmeticAnswer call.program) joint.1 joint.2
      (combine initial (run call call.program).2)

end Logup.Prover.Honest.Accounting
