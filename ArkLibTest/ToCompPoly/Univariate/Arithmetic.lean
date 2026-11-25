/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ToCompPoly.Univariate.ArithmeticInterpolationBound
import ArkLib.ToCompPoly.Univariate.ArithmeticInterpolationCost
import ArkLib.ToCompPoly.Univariate.ArithmeticEvaluation
import Mathlib.Data.ZMod.Basic

/-!
# Measured polynomial arithmetic trust checks

These classic clients guard the literal arithmetic erasure and the exact or bounded profiles
of raw convolution, trimming, power-sum evaluation, and cached interpolation. They also compare
the field operations of measured raw multiplication with the loop that compiled code runs.
-/

/--
info: 'CompPoly.profileArithmetic_fst' depends on axioms:
[propext, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CompPoly.profileArithmetic_fst

/--
info: 'CompPoly.Arithmetic.profileArithmetic_mulRaw' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CompPoly.Arithmetic.profileArithmetic_mulRaw

/-! ### Operation order of raw multiplication

Compiled calls to `CPolynomial.Raw.mulRaw` run `CPolynomial.Raw.mulRawFast`. The checks below
fail when that replacement changes, or when either `mulRawFast` or `Arithmetic.mulRaw` changes
its additions and multiplications on the listed shapes. A shape lists, for each output entry, the
index pairs `(i, j)` whose products `p[i] * q[j]` the entry adds to `0`, in order. The checks
compare definitions. They do not inspect the code that the compiler generates for the loop. -/

namespace MulRawTrace
open CompPoly OracleComp OracleSpec

/-- A field addition or multiplication with its operands. -/
inductive FieldOp (R : Type)
  | add (a b : R)
  | mul (a b : R)
  deriving DecidableEq

section Trace
variable {R : Type} [Semiring R] [Sub R] [Inv R] [DecidableEq R]

/-- Record each requested addition and multiplication. -/
def fieldOpLog : QueryImpl (ArithmeticSpec R) (StateM (List (FieldOp R))) where
  toFun
  | .add a b => do modify (· ++ [.add a b]); pure ⟨a + b, rfl⟩
  | .mul a b => do modify (· ++ [.mul a b]); pure ⟨a * b, rfl⟩
  | op => pure (arithmeticAnswer op)

/-- The additions and multiplications that a measured program requests, in order. -/
def fieldOps {A : Type} (oa : OracleComp (ArithmeticSpec R) A) : List (FieldOp R) :=
  ((simulateQ fieldOpLog oa).run []).2

/-- The entries of a shape, each adding its products to `0` in order. -/
def entrySums (p q : Array R) (shape : List (List (ℕ × ℕ))) : Array R :=
  (shape.map fun terms ↦ terms.foldl (fun s t ↦ s + p.getD t.1 0 * q.getD t.2 0) 0).toArray

/-- The multiplication and then the addition of each term of `entrySums`, in order. -/
def entryOps (p q : Array R) (shape : List (List (ℕ × ℕ))) : List (FieldOp R) :=
  shape.flatMap fun terms ↦ (terms.foldl (fun (s, ops) t ↦
    let c := p.getD t.1 0 * q.getD t.2 0
    (s + c, ops ++ [.mul (p.getD t.1 0) (q.getD t.2 0), .add s c])) ((0 : R), [])).2

/-- The entries of the product of a 3-coefficient and a 2-coefficient array. -/
def shape₃₂ : List (List (ℕ × ℕ)) := [[(0, 0)], [(0, 1), (1, 0)], [(1, 1), (2, 0)], [(2, 1)]]

/-- The entries of the product of a 2-coefficient and a 3-coefficient array. -/
def shape₂₃ : List (List (ℕ × ℕ)) := [[(0, 0)], [(0, 1), (1, 0)], [(0, 2), (1, 1)], [(1, 2)]]

end Trace

section Compiled
variable {R : Type} [Semiring R] (a₀ a₁ a₂ b₀ b₁ b₂ : R)

example : CPolynomial.Raw.mulRawFast #[] #[b₀, b₁] = entrySums #[] #[b₀, b₁] [] := rfl
example : CPolynomial.Raw.mulRawFast #[a₀, a₁] #[] = entrySums #[a₀, a₁] #[] [[]] := rfl
example : CPolynomial.Raw.mulRawFast #[a₀] #[b₀] = entrySums #[a₀] #[b₀] [[(0, 0)]] := rfl

example : CPolynomial.Raw.mulRawFast #[a₀, a₁, a₂] #[b₀, b₁] = entrySums #[a₀, a₁, a₂] #[b₀, b₁]
    shape₃₂ := rfl

example : CPolynomial.Raw.mulRawFast #[a₀, a₁] #[b₀, b₁, b₂] = entrySums #[a₀, a₁] #[b₀, b₁, b₂]
    shape₂₃ := rfl

end Compiled

section Measured

example : fieldOps (Arithmetic.mulRaw (#[] : Array (ZMod 101)) #[7, 11]) =
    entryOps #[] #[7, 11] [] := by decide +kernel

example : fieldOps (Arithmetic.mulRaw (#[2, 3] : Array (ZMod 101)) #[]) =
    entryOps #[2, 3] #[] [[]] := by decide +kernel

example : fieldOps (Arithmetic.mulRaw (#[2] : Array (ZMod 101)) #[7]) =
    entryOps #[2] #[7] [[(0, 0)]] := by decide +kernel

example : fieldOps (Arithmetic.mulRaw (#[2, 3, 5] : Array (ZMod 101)) #[7, 11]) =
    entryOps #[2, 3, 5] #[7, 11] shape₃₂ := by decide +kernel

example : fieldOps (Arithmetic.mulRaw (#[2, 3] : Array (ZMod 101)) #[7, 11, 13]) =
    entryOps #[2, 3] #[7, 11, 13] shape₂₃ := by decide +kernel

end Measured

open Lean in
run_meta do
  let env ← getEnv
  let target ← Compiler.CSimp.replaceConstant env (mkConst ``CPolynomial.Raw.mulRaw [Level.zero])
  let fast := ``CPolynomial.Raw.mulRawFast
  unless target.isConstOf fast && (Compiler.getImplementedBy? env fast).isNone &&
      !isExtern env fast do
    throwError "Compiled `CPolynomial.Raw.mulRaw` must run the definition of `mulRawFast`."

end MulRawTrace

/--
info: 'CompPoly.Arithmetic.profileArithmetic_trimRaw_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CompPoly.Arithmetic.profileArithmetic_trimRaw_le

/--
info: 'CompPoly.Arithmetic.profileArithmetic_evalRaw' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CompPoly.Arithmetic.profileArithmetic_evalRaw

/--
info: 'CompPoly.Arithmetic.profileArithmetic_interpolate_inv' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CompPoly.Arithmetic.profileArithmetic_interpolate_inv

/--
info: 'CompPoly.Arithmetic.profileArithmetic_interpolate_nodeRead' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CompPoly.Arithmetic.profileArithmetic_interpolate_nodeRead

/--
info: 'CompPoly.Arithmetic.profileArithmetic_interpolate_valueRead' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CompPoly.Arithmetic.profileArithmetic_interpolate_valueRead

/--
info: 'CompPoly.Arithmetic.profileArithmetic_interpolate_cubic_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CompPoly.Arithmetic.profileArithmetic_interpolate_cubic_le

/--
info: 'CompPoly.Arithmetic.profileArithmetic_interpolate_add_sub_le' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms CompPoly.Arithmetic.profileArithmetic_interpolate_add_sub_le
