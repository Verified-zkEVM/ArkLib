/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import VCVio.OracleComp.QueryTracking.WriterCost

/-!
# Certified arithmetic instructions

The response types certify primitive arithmetic and coefficient reads. Proof fields disappear
from compiled programs; each primitive handler performs its requested operation once. Profiles
count source instructions; an inverse is one algebraic primitive. Metadata counts designated
control or array-operation ticks. Profiles exclude machine index, allocation, and runtime costs.

A profile is the output and the PolyFun path charge of the one completed path that the
deterministic handler selects (`profileArithmetic_eq_charge`).
-/

@[expose] public section

namespace PFunctor.FreeM.Path

/-- The path a fixed selector picks through a bind joins the paths it picks through the first
program and through the continuation at that path's output. -/
theorem ofHandler_bind {P : PFunctor} {α β : Type _} (choose : (a : P.A) → P.B a)
    (x : FreeM P α) (f : α → FreeM P β) :
    ofHandler choose (x.bind f) =
      joinBind x f (ofHandler choose x) (ofHandler choose (f (output x (ofHandler choose x)))) := by
  induction x using FreeM.rec with
  | pure a => rfl
  | liftBind a r ih =>
    exact congrArg (fun p ↦ (⟨choose a, p⟩ : Path (FreeM.liftBind a fun b ↦ (r b).bind f)))
      (ih (choose a))

end PFunctor.FreeM.Path

namespace CompPoly

open OracleComp OracleSpec

/-- Coordinates counted by arithmetic and coefficient-array programs. -/
inductive ArithmeticCostKind
  | add | sub | mul | inv | eq | coefficientRead | nodeRead | valueRead | metadata
  deriving DecidableEq, Repr

instance : Fintype ArithmeticCostKind where
  elems := {.add, .sub, .mul, .inv, .eq, .coefficientRead, .nodeRead, .valueRead, .metadata}
  complete kind := by cases kind <;> simp

/-- A vector of arithmetic instruction counts. -/
abbrev ArithmeticCost := ArithmeticCostKind → ℕ

/-- A field or coefficient-array instruction. -/
inductive ArithmeticOp (F : Type)
  | add (a b : F)
  | sub (a b : F)
  | mul (a b : F)
  | inv (a : F)
  | eq (a b : F)
  | coefficientRead (a : Array F) (i : ℕ)
  | nodeRead (a : Array F) (i : ℕ)
  | valueRead (a : Array F) (i : ℕ)
  | metadata

/-- The certified answer type of each arithmetic instruction. -/
def ArithmeticSpec (F : Type) [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F] :
    OracleSpec (ArithmeticOp F)
  | .add a b => {c : F // c = a + b}
  | .sub a b => {c : F // c = a - b}
  | .mul a b => {c : F // c = a * b}
  | .inv a => {c : F // c = a⁻¹}
  | .eq a b => {c : Bool // c = decide (a = b)}
  | .coefficientRead a i => {c : F // c = a[i]?.getD 0}
  | .nodeRead a i => {c : F // c = a[i]?.getD 0}
  | .valueRead a i => {c : F // c = a[i]?.getD 0}
  | .metadata => Unit

/-- The coordinate charged by an arithmetic instruction. -/
def ArithmeticOp.costKind {F : Type} : ArithmeticOp F → ArithmeticCostKind
  | .add _ _ => .add
  | .sub _ _ => .sub
  | .mul _ _ => .mul
  | .inv _ => .inv
  | .eq _ _ => .eq
  | .coefficientRead _ _ => .coefficientRead
  | .nodeRead _ _ => .nodeRead
  | .valueRead _ _ => .valueRead
  | .metadata => .metadata

/-- One unit in the coordinate charged by an arithmetic instruction. -/
def arithmeticCost {F : Type} (op : ArithmeticOp F) : ArithmeticCost :=
  fun kind ↦ if kind = op.costKind then 1 else 0

/-- Execute an arithmetic instruction and certify its result. -/
def arithmeticAnswer {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F] :
    QueryImpl (ArithmeticSpec F) Id
  | .add a b => ⟨a + b, rfl⟩
  | .sub a b => ⟨a - b, rfl⟩
  | .mul a b => ⟨a * b, rfl⟩
  | .inv a => ⟨a⁻¹, rfl⟩
  | .eq a b => ⟨decide (a = b), rfl⟩
  | .coefficientRead a i => ⟨a[i]?.getD 0, rfl⟩
  | .nodeRead a i => ⟨a[i]?.getD 0, rfl⟩
  | .valueRead a i => ⟨a[i]?.getD 0, rfl⟩
  | .metadata => ()

/-- Every certified arithmetic response is the handler's answer. -/
theorem eq_arithmeticAnswer {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]
    (op : ArithmeticOp F) (u : (ArithmeticSpec F).Range op) : u = arithmeticAnswer op := by
  cases op <;> first | rfl | exact Subtype.ext u.property

/-- Execute arithmetic instructions while recording every requested operation. -/
def arithmeticMeasured {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F] :
    QueryImpl (ArithmeticSpec F) (AddWriterT ArithmeticCost Id) :=
  arithmeticAnswer.withAddCost arithmeticCost

/-- Execute the measured backend and retain its result and cost vector. -/
def profileArithmetic {F A : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]
    (program : OracleComp (ArithmeticSpec F) A) : A × ArithmeticCost :=
  (simulateQ arithmeticMeasured program).runAdd

/-- A profile is the output and the charge of the completed path selected by the handler. -/
theorem profileArithmetic_eq_charge {F A : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F]
    [DecidableEq F] (program : OracleComp (ArithmeticSpec F) A) :
    profileArithmetic program =
      (PFunctor.FreeM.output program
          (PFunctor.FreeM.Path.ofHandler (fun op ↦ (arithmeticAnswer op).run) program),
        PFunctor.FreeM.Path.charge arithmeticCost program
          (PFunctor.FreeM.Path.ofHandler (fun op ↦ (arithmeticAnswer op).run) program)) := by
  change Prod.map id Multiplicative.toAdd
    (simulateQ (arithmeticAnswer.withAddCost arithmeticCost) program).run = _
  rw [QueryImpl.run_simulateQ_withAddCost_id]
  rfl

/-- Erasing the profile preserves the exact arithmetic program's result. -/
theorem profileArithmetic_fst {F A : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]
    (program : OracleComp (ArithmeticSpec F) A) :
    (profileArithmetic program).1 = simulateQ arithmeticAnswer program :=
  QueryImpl.fst_map_run_simulateQ_withAddCost arithmeticAnswer arithmeticCost program

namespace Arithmetic

variable {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]

/-- Request a certified field addition. -/
def add (a b : F) : OracleComp (ArithmeticSpec F) {c : F // c = a + b} :=
  liftM (OracleSpec.query (spec := ArithmeticSpec F) (.add a b))

/-- Request a certified field subtraction. -/
def sub (a b : F) : OracleComp (ArithmeticSpec F) {c : F // c = a - b} :=
  liftM (OracleSpec.query (spec := ArithmeticSpec F) (.sub a b))

/-- Request a certified field multiplication. -/
def mul (a b : F) : OracleComp (ArithmeticSpec F) {c : F // c = a * b} :=
  liftM (OracleSpec.query (spec := ArithmeticSpec F) (.mul a b))

/-- Request a certified field inversion. -/
def inv (a : F) : OracleComp (ArithmeticSpec F) {c : F // c = a⁻¹} :=
  liftM (OracleSpec.query (spec := ArithmeticSpec F) (.inv a))

/-- Request a certified field equality test. -/
def eq (a b : F) : OracleComp (ArithmeticSpec F) {c : Bool // c = decide (a = b)} :=
  liftM (OracleSpec.query (spec := ArithmeticSpec F) (.eq a b))

/-- Read one coefficient, returning zero outside the array bounds. -/
def coefficientRead (a : Array F) (i : ℕ) :
    OracleComp (ArithmeticSpec F) {c : F // c = a[i]?.getD 0} :=
  liftM (OracleSpec.query (spec := ArithmeticSpec F) (.coefficientRead a i))

/-- Read one cached field node, returning zero outside the array bounds. -/
def nodeRead (a : Array F) (i : ℕ) :
    OracleComp (ArithmeticSpec F) {c : F // c = a[i]?.getD 0} :=
  liftM (OracleSpec.query (spec := ArithmeticSpec F) (.nodeRead a i))

/-- Read one cached field value, returning zero outside the array bounds. -/
def valueRead (a : Array F) (i : ℕ) :
    OracleComp (ArithmeticSpec F) {c : F // c = a[i]?.getD 0} :=
  liftM (OracleSpec.query (spec := ArithmeticSpec F) (.valueRead a i))

/-- Charge one metadata or index-control instruction. -/
def tick : OracleComp (ArithmeticSpec F) Unit :=
  liftM (OracleSpec.query (spec := ArithmeticSpec F) .metadata)

end Arithmetic

end CompPoly
