/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
import ArkLib.ProofSystem.Logup.Prover.ArithmeticRoundCost
import ArkLibTest.ProofSystem.Logup.Prover.RoundCoefficients
import Lean.Compiler.IR

/-! # Executing the measured streamed coefficient constructor -/

open CompPoly CPolynomial CMlPolynomialEval OracleComp OracleSpec
open Logup.Prover.RoundCoefficients
namespace ArithmeticRoundTests

-- The instruction interface requires an inverse operation; this constructor never requests it.
local instance : Inv ℤ := ⟨fun _ => 0⟩

/-- The generic caller selects the measured program's erasure, rather than the pure constructor. -/
def caller {F : Type} [CommRing F] [Inv F] [DecidableEq F] {r T K ell : ℕ}
    (groups : Vector (List (Fin T)) K) (hg : ∀ k, (groups.get k).length ≤ ell)
    (lambda : Vector F K) (d w : Vector (CMlPolynomialEval F (r + 1)) T)
    (h : Vector (CMlPolynomialEval F (r + 1)) K) (kernel : CMlPolynomialEval F (r + 1)) :
    Sumcheck.Impl.Representation.Message F (ell + 2) :=
  messageByProgram groups hg lambda d w h kernel

example {F : Type} [CommRing F] [Inv F] [DecidableEq F] {r T K ell : ℕ}
    (groups : Vector (List (Fin T)) K) (hg : ∀ k, (groups.get k).length ≤ ell)
    (lambda : Vector F K) (d w : Vector (CMlPolynomialEval F (r + 1)) T)
    (h : Vector (CMlPolynomialEval F (r + 1)) K) (kernel : CMlPolynomialEval F (r + 1)) :
    caller groups hg lambda d w h kernel = message groups hg lambda d w h kernel :=
  messageByProgram_eq_message groups hg lambda d w h kernel

def kinds : List ArithmeticCostKind :=
  [.add, .sub, .mul, .inv, .eq, .coefficientRead, .nodeRead, .valueRead, .metadata]

-- A separate state backend records an explicit coordinate for every actual primitive request.
def auditIndex {F : Type} : ArithmeticOp F → Nat
  | .add _ _ => 0 | .sub _ _ => 1 | .mul _ _ => 2 | .inv _ => 3 | .eq _ _ => 4
  | .coefficientRead _ _ => 5 | .nodeRead _ _ => 6 | .valueRead _ _ => 7 | .metadata => 8

def audit {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F] :
    QueryImpl (ArithmeticSpec F) (StateM (Array Nat)) := fun op => do
  modify (fun counts => counts.modify (auditIndex op) (· + 1))
  pure (arithmeticAnswer op)

def check {F : Type} [CommRing F] [Inv F] [DecidableEq F] {r T K : ℕ}
    (groups : Vector (List (Fin T)) K) (lambda : Vector F K)
    (d w : Vector (CMlPolynomialEval F (r + 1)) T)
    (h : Vector (CMlPolynomialEval F (r + 1)) K) (kernel : CMlPolynomialEval F (r + 1))
    (expected : Raw F) (expectedCost : List Nat) : IO Unit := do
  let program := messageProgram groups lambda d w h kernel
  let (p, cost) := profileArithmetic program
  let (q, counts) := (simulateQ audit program).run (Array.replicate 9 0)
  unless p.val == expected && q == p && kinds.map cost == expectedCost &&
      counts.toList == expectedCost do
    throw (IO.userError "incorrect measured round coefficients or actual request profile")

open RoundCoefficientsTests in
#eval (show IO _ from do
  check (r := 0) groups #v[4, 6] denominator weight helper #v[-2, 3]
    #[0, 2, 10, 5] [59, 11, 28, 0, 1, 169, 0, 14, 180]
  check (r := 0) singleton #v[1] #v[xTable] #v[xTable] #v[xTable] kTable
    #[0, 0, 0, 1] [37, 6, 17, 0, 1, 104, 0, 8, 107]
  check (r := 0) singleton #v[(1 : ℚ)] #v[#v[1, 1]] #v[#v[0, 0]] #v[#v[0, 0]]
    #v[0, 0] #[] [37, 6, 17, 0, 4, 107, 0, 8, 111]
  check (r := 1) singleton #v[7] asymmetricDenominator asymmetricWeight
    asymmetricHelper asymmetricKernel #[75197, 105265, 20314, 1064]
    [74, 12, 34, 0, 1, 207, 0, 16, 212]
  pure "cubic, asymmetric rows and finite-field coefficient trap execute measured program")

def measuredBinary : Sumcheck.Impl.Representation.Message (ZMod 2) 3 :=
  messageByProgram (r := 0) RoundCoefficientsTests.singleton
    (by intro k; fin_cases k; decide) #v[1] #v[RoundCoefficientsTests.xTable]
    #v[RoundCoefficientsTests.xTable] #v[RoundCoefficientsTests.xTable]
    RoundCoefficientsTests.kTable

theorem measuredBinary_toPoly : measuredBinary.val.toPoly = Polynomial.X ^ 3 := by
  unfold measuredBinary
  rw [messageByProgram_eq_message]
  exact RoundCoefficientsTests.binary_toPoly

theorem measuredBinary_ne_X : measuredBinary.val.toPoly ≠ Polynomial.X := by
  unfold measuredBinary
  rw [messageByProgram_eq_message]
  exact RoundCoefficientsTests.binary_ne_X

-- Empty groups and T=0 do not make the helper contribution vanish.
#eval (show IO _ from do
  let p := caller (r := 0) (ell := 0) (#v[[]] : Vector (List (Fin 0)) 1) (by simp) #v[(3 : ℚ)]
    #v[] #v[] #v[#v[2, 5]] #v[7, 11]
  unless p.val.val == #[44, 90, 36] do
    throw (IO.userError "measured constructor skipped a nonzero helper when T=0")
  pure p.val.val)

-- Retained zero padding is normalized only after the complete row traversal.
def constantRows (r : Nat) (h : ℚ) : Array ℚ :=
  let tables (a : ℚ) : Vector (CMlPolynomialEval ℚ (r + 1)) 1 :=
    #v[Vector.replicate (2 ^ (r + 1)) a]
  (caller (r := r) (ell := 1) RoundCoefficientsTests.singleton
    (by intro k; fin_cases k; decide) #v[1]
    (tables 1) (tables 0) (tables h) (Vector.replicate (2 ^ (r + 1)) 0)).val.val

def singletonGroups (size : Nat) : Vector (List (Fin size)) size := Vector.ofFn fun i => [i]
def manyGroups (size : Nat) : Array ℚ :=
  let tables (a : ℚ) : Vector (CMlPolynomialEval ℚ 1) size := Vector.replicate size #v[a, a]
  (caller (r := 0) (ell := 1) (singletonGroups size) (by intro k; simp [singletonGroups])
    (Vector.replicate size 1) (tables 1) (tables 0) (tables 0) #v[1, 1]).val.val

#eval (show IO _ from do
  unless constantRows 8 1 == #[256] && (constantRows 8 0).isEmpty &&
      (manyGroups 512).isEmpty do
    throw (IO.userError "scaled measured erasure lost a row, group or all-zero normalization")
  pure "256 rows and 512 singleton groups passed")

open Lean Elab Command in
run_cmd do
  for name in #[``affineRowsProgram, ``rowProgram, ``coefficientsFromProgram,
      ``coefficientsProgram, ``messageProgram, ``messageByProgram, ``rowBudget, ``caller,
      ``measuredBinary, ``constantRows, ``manyGroups] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "expected executable compiler IR for `{name}`"
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``profileArithmetic_affineRowsProgram, ``profileArithmetic_rowProgram_fst,
      ``profileArithmetic_coefficientsFromProgram_fst, ``profileArithmetic_coefficientsProgram_fst,
      ``profileArithmetic_messageProgram_fst, ``simulateQ_messageProgram,
      ``messageByProgram_eq_message, ``profileArithmetic_rowProgram,
      ``profileArithmetic_coefficientsFromProgram_nil,
      ``profileArithmetic_coefficientsFromProgram_cons, ``profileArithmetic_coefficientsProgram,
      ``profileArithmetic_messageProgram, ``profileArithmetic_rowProgram_le,
      ``profileArithmetic_coefficientsFromProgram_le, ``profileArithmetic_coefficientsProgram_le,
      ``profileArithmetic_messageProgram_le, ``profileArithmetic_messageProgram_eq_le,
      ``profileArithmetic_rowProgram_valueRead,
      ``profileArithmetic_coefficientsFromProgram_valueRead,
      ``profileArithmetic_messageProgram_valueRead, ``rowBudget_le_of_length_sum,
      ``profileArithmetic_messageProgram_le_of_length_sum,
      ``measuredBinary_toPoly, ``measuredBinary_ne_X] do
    unless (← collectAxioms name).all allowed.contains do
      throwError "unexpected axioms in `{name}`"

end ArithmeticRoundTests
