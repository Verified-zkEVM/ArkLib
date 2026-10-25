/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToCompPoly.Univariate.ArithmeticCost
import Lean.Compiler.IR

/-! # Index-dependent profiles of one actual vector traversal -/

open CompPoly OracleComp OracleSpec
namespace ArithmeticVectorProfileTests
variable {F : Type} [CommRing F] [Inv F] [DecidableEq F]

def entry (i : Fin 3) : OracleComp (ArithmeticSpec F) F :=
  if i.val = 0 then pure 10 else if i.val = 1 then Subtype.val <$> Arithmetic.add 2 3 else do
    let a ← Arithmetic.mul 7 11
    let b ← Arithmetic.mul a.val 2
    let c ← Arithmetic.sub b.val 5
    pure c.val

def value (i : Fin 3) : F :=
  if i.val = 0 then 10 else if i.val = 1 then 2 + 3 else (7 * 11) * 2 - 5

def cost (i : Fin 3) : ArithmeticCost :=
  if i.val = 0 then 0 else if i.val = 1 then
    fun kind => if kind = .add then 1 else 0
  else fun kind => if kind = .mul then 2 else if kind = .sub then 1 else 0

theorem profile_entry (i : Fin 3) : profileArithmetic (entry (F := F) i) = (value i, cost i) := by
  fin_cases i
  · simp [entry, value, cost]
  · apply Prod.ext
    · simp [entry, value]
    · funext kind
      cases kind <;> simp [entry, cost, arithmeticCost, ArithmeticOp.costKind]
  · apply Prod.ext
    · simp [entry, value]
    · funext kind
      cases kind <;> simp [entry, cost, arithmeticCost, ArithmeticOp.costKind]

theorem profile_vector : profileArithmetic (Vector.ofFnM (entry (F := F))) =
    (Vector.ofFn (value (F := F)), fun kind => ∑ i : Fin 3, cost i kind) :=
  profileArithmetic_ofFnM entry value cost profile_entry

-- Empty input neither invokes its callback nor introduces a control request.
example : profileArithmetic
    (Vector.ofFnM (fun i : Fin 0 => (pure i.val : OracleComp (ArithmeticSpec ℚ) Nat))) =
    (Vector.ofFn Fin.val, 0) := by
  simp

-- A separate state handler logs the actual varying branch instruction order.
def recorder : QueryImpl (ArithmeticSpec ℚ) (StateM (List Nat)) := fun op => do
  let tag := match op with
    | .add _ _ => 0 | .mul _ _ => 1 | .sub _ _ => 2 | _ => 3
  modify (· ++ [tag])
  pure (arithmeticAnswer op)

#eval (show IO _ from do
  let program := Vector.ofFnM (entry (F := ℚ))
  let (actual, counts) := profileArithmetic program
  let (recorded, trace) := (simulateQ recorder program).run []
  unless actual == #v[10, 5, 149] && recorded == actual && trace == [0, 1, 1, 2] &&
      counts .add == 1 && counts .mul == 2 && counts .sub == 1 && counts .inv == 0 &&
      counts .eq == 0 && counts .coefficientRead == 0 && counts .nodeRead == 0 &&
      counts .valueRead == 0 && counts .metadata == 0 do
    throw (IO.userError "vector traversal replaced heterogeneous profiles or changed entry order")
  pure (actual, trace))

open Lean Elab Command in
run_cmd do
  for name in #[``entry, ``recorder] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "expected executable compiler IR for `{name}`"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``profileArithmetic_ofFnM, ``profile_entry, ``profile_vector] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected axioms in `{name}`"

end ArithmeticVectorProfileTests
