/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import VCVio.OracleComp.QueryTracking.CountingOracle.Core

/-!
# Certified arithmetic instructions

The response types certify primitive arithmetic and coefficient reads. Proof fields disappear
from compiled programs; each primitive handler performs its requested operation once. Profiles
count source instructions; an inverse is one algebraic primitive. Metadata counts designated
control or array-operation ticks. Profiles exclude machine index, allocation, and runtime costs.
-/

@[expose] public section

namespace CompPoly

open OracleComp OracleSpec

/-- Coordinates counted by arithmetic and coefficient-array programs. -/
inductive ArithmeticCostKind
  | add | sub | mul | inv | eq | coefficientRead | nodeRead | valueRead | metadata
  deriving DecidableEq, Repr

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
  arithmeticAnswer.withCost (fun op ↦ Multiplicative.ofAdd (arithmeticCost op))

/-- Execute the measured backend and retain its result and cost vector. -/
def profileArithmetic {F A : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]
    (program : OracleComp (ArithmeticSpec F) A) : A × ArithmeticCost :=
  (simulateQ arithmeticMeasured program).runAdd

/-- Erasing the profile preserves the exact arithmetic program's result. -/
theorem profileArithmetic_fst {F A : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]
    (program : OracleComp (ArithmeticSpec F) A) :
    (profileArithmetic program).1 = simulateQ arithmeticAnswer program := by
  exact QueryImpl.fst_map_run_withCost arithmeticAnswer
    (fun op ↦ Multiplicative.ofAdd (arithmeticCost op)) program

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
