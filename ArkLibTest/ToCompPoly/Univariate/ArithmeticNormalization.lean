/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ToCompPoly.Univariate.ArithmeticNormalization
import Mathlib.Algebra.Field.ZMod
import Lean.Compiler.IR

/-! # Reverse scans preserve canonical coefficients and original-array request provenance -/

namespace CompPoly.Arithmetic.NormalizationTest
open OracleComp OracleSpec CPolynomial

/-- This external generic caller executes the selected program's deterministic erasure. -/
def normalize {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]
    (p : Raw F) : CPolynomial F :=
  (simulateQ arithmeticAnswer (canonicalRawProgram p)).val

example {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]
    (p : Raw F) : normalize p = CPolynomial.ofArray p :=
  simulateQ_canonicalRawProgram p

-- An original-array handler records each request before returning its certified answer.
def record (expected : Raw ℚ) :
    QueryImpl (ArithmeticSpec ℚ) (StateM (List (Nat × Nat × Bool))) := fun op => do
  let event := match op with
    | .coefficientRead p i => (0, i, p == expected)
    | .eq _ _ => (1, 0, true)
    | .metadata => (2, 0, true)
    | _ => (3, 0, false)
  modify (· ++ [event])
  pure (arithmeticAnswer op)

#eval (show IO _ from do
  let p : Raw ℚ := #[2, 0, 0, 7, 0, 0]
  let (q, trace) := (simulateQ (record p) (canonicalRawProgram p)).run []
  unless q.val.val == #[2, 0, 0, 7] && trace ==
      [(2, 0, true), (0, 5, true), (1, 0, true),
       (2, 0, true), (0, 4, true), (1, 0, true),
       (2, 0, true), (0, 3, true), (1, 0, true)] do
    throw (IO.userError "normalization changed the original array, read order or stop position")
  pure q.val.val)

#eval (show IO _ from do
  let fixtures : List (Raw ℚ × Raw ℚ × Nat × Nat) :=
    [(#[], #[], 0, 1), (#[0], #[], 1, 2), (#[3], #[3], 1, 1),
     (#[0, 0, 0], #[], 3, 4), (#[0, 5, 0, 0], #[0, 5], 3, 3),
     (#[0, 0, -7], #[0, 0, -7], 1, 1)]
  for (p, expected, reads, ticks) in fixtures do
    let (q, cost) := profileArithmetic (canonicalRawProgram p)
    unless q.val.val == expected && normalize p == q.val &&
        cost .coefficientRead == reads && cost .eq == reads && cost .metadata == ticks &&
        cost .add == 0 && cost .sub == 0 && cost .mul == 0 && cost .inv == 0 &&
        cost .nodeRead == 0 && cost .valueRead == 0 do
      throw (IO.userError "incorrect canonical result or exact normalization profile")
  pure fixtures.length)

-- No domain, field or nonzero-factor premise is needed for a zero divisor coefficient.
#eval (show IO _ from do
  let p : Raw (ZMod 4) := #[0, 2, 0, 0]
  let (q, cost) := profileArithmetic (canonicalRawProgram p)
  unless q.val.val == #[0, 2] && cost .coefficientRead == 3 && cost .metadata == 3 do
    throw (IO.userError "normalization discarded a nonzero zero divisor")
  pure q.val.val)

-- Ordinary compiled execution, without constructing a kernel proof by deciding a large array.
#eval (show IO _ from do
  let empty := normalize (Array.replicate 100000 (0 : ℚ))
  let kept :=  normalize ((#[3, 4] : Raw ℚ) ++ Array.replicate 100000 0)
  let full := normalize ((Array.replicate 100000 (0 : ℚ)).push 5)
  unless empty.val.isEmpty && kept.val == #[3, 4] && full.val.size == 100001 &&
      full.val.back! == 5 do
    throw (IO.userError "large reverse scan returned incorrect canonical coefficients")
  pure (empty.val.size, kept.val, full.val.size))

open Lean Elab Command in
run_cmd do
  for name in #[``lastNonzeroFromProgram, ``lastNonzeroProgram, ``canonicalRawProgram,
      ``normalize, ``record] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "expected executable compiler IR for `{name}`"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``simulateQ_canonicalRawProgram, ``profileArithmetic_lastNonzeroFromProgram_zero,
      ``profileArithmetic_lastNonzeroFromProgram_succ,
      ``profileArithmetic_lastNonzeroFromProgram_le,
      ``profileArithmetic_canonicalRawProgram, ``profileArithmetic_canonicalRawProgram_le,
      ``profileArithmetic_lastNonzeroFromProgram, ``profileArithmetic_canonicalRawProgram_exact] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected axioms in `{name}`"

end CompPoly.Arithmetic.NormalizationTest
