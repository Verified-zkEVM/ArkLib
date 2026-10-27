/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.ProofSystem.Logup.Prover.CoefficientCircuitCost
import Mathlib.Data.ZMod.Basic
import Lean.Compiler.IR

/-! # Grouped coefficient circuit semantics, profiles, and runtime acceptance -/

open Logup CompPoly CPolynomial Logup.Prover.CoefficientCircuit

namespace CoefficientCircuitTests

def groups : Vector (List (Fin 2)) 2 := #v[[0], [1]]
def denominator : Vector (Raw (ZMod 17)) 2 := #v[#[2, -1], #[2, -1]]
def weight : Vector (Raw (ZMod 17)) 2 := #v[#[1, 0], #[-1, 0]]
def helper : Vector (Raw (ZMod 17)) 2 := #v[#[9, -8], #[8, 8]]
def coefficients : Raw (ZMod 17) :=
  circuitRaw groups #[-2, 5] #v[4, 6] denominator weight helper

def measured :=
  profileArithmetic (circuitProgram groups #[-2, 5] #v[4, 6] denominator weight helper)

example : measured.1 = coefficients := profileArithmetic_circuitProgram_fst _ _ _ _ _ _

-- The characteristic-two polynomial X + X^3 vanishes at every field point but is nonzero.
def binary : Raw (ZMod 2) :=
  circuitRaw #v[[0]] (Raw.affine 0 1) #v[1] #v[Raw.affine 0 1]
    #v[Raw.affine 0 0] #v[Raw.affine 0 1]

theorem binary_toPoly : Raw.toPoly binary = Polynomial.X + Polynomial.X ^ 3 := by
  unfold binary
  rw [toPoly_circuitRaw_denominator]
  simp [reconstructWithKernel, groupResidual, groupFraction, FractionPair.sum_cons,
    FractionPair.sum_nil, FractionPair.combine, FractionPair.unit, Raw.toPoly_affine]
  dsimp only [Vector.get]
  simp [Raw.toPoly_affine]
  ring

example : (Raw.toPoly binary).coeff 3 = 1 := by rw [binary_toPoly]; norm_num [Polynomial.coeff_X]
example : ∀ x : ZMod 2, (Raw.toPoly binary).eval x = 0 := by
  intro x
  rw [binary_toPoly]
  simp only [Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X]
  fin_cases x <;> decide
example : Raw.toPoly binary ≠ 0 := by
  intro h
  have hc := congrArg (fun p : Polynomial (ZMod 2) => p.coeff 3) h
  rw [binary_toPoly] at hc
  norm_num [Polynomial.coeff_X] at hc

def scalarCaller {R : Type*} [CommRing R]
    (alpha kernel lambda value weight helper : R) : R :=
  reconstructWithKernel (#v[[0]] : Vector (List (Fin 1)) 1) alpha kernel
    (fun _ => lambda) (fun _ => value) (fun _ => weight) (fun _ => helper)

def caller {R : Type*} [CommRing R] (d w h : R) : Raw R :=
  circuitRaw #v[[0]] #[1, 0] #v[1] #v[#[d, 0]] #v[#[w, 0]] #v[#[h, 0]]

def measuredCaller {R : Type} [CommRing R] [Inv R] [DecidableEq R] (d w h : R) :=
  profileArithmetic
    (circuitProgram #v[[0]] #[1, 0] #v[1] #v[#[d, 0]] #v[#[w, 0]] #v[#[h, 0]])

open Lean Elab Command in
run_cmd do
  for name in #[``scalarCaller, ``reconstructWithKernel, ``caller, ``measuredCaller,
      ``circuitRaw, ``circuitProgram] do
    unless (Lean.IR.findEnvDecl (← getEnv) name).isSome do
      throwError "missing executable coefficient-circuit IR: {name}"
  unless scalarCaller (2 : ℤ) 5 11 0 3 7 == 612 do
    throwError "already-bound scalar-kernel reconstruction changed"
  unless coefficients == #[0, 2, 10, 5] && measured.1 == coefficients do
    throwError "asymmetric honest cubic runtime mismatch"
  unless binary == #[0, 1, 0, 1] do
    throwError "characteristic-two formal cubic coefficients changed"
  let empty := circuitRaw (#v[[]] : Vector (List (Fin 0)) 1) (#[2] : Raw ℤ) #v[3]
    #v[] #v[] #v[#[7]]
  unless empty == #[49] do
    throwError "empty occurrence set incorrectly discarded a nonzero helper"
  let pole := circuitRaw #v[[0]] (#[1] : Raw ℤ) #v[1] #v[#[0, 0]]
    #v[#[3, 4]] #v[#[9, 1]]
  unless pole == #[6, -3, 0] do
    throwError "zero denominator lost its numerator constraint or padding"
  unless (measured.2 .add, measured.2 .mul, measured.2 .sub,
      measured.2 .coefficientRead, measured.2 .metadata) == (55, 28, 4, 160, 172) do
    throwError "asymmetric circuit's exact instruction profile changed"
  let noGroups := circuitRaw (#v[] : Vector (List (Fin 1)) 0) (#[7, 11] : Raw ℤ)
    #v[] #v[#[2, 3]] #v[#[5, 6]] #v[]
  unless noGroups == #[0] do
    throwError "empty group family changed its padded zero circuit"
  let repeated := circuitRaw #v[[0, 0]] (#[1, 0] : Raw ℤ) #v[1]
    #v[#[2, 1]] #v[#[3, 0]] #v[#[0, 0]]
  unless repeated == #[-12, -6, 0, 0, 0] do
    throwError "repeated occurrences were collapsed or their padded multiplicity changed"
  logInfo "honest cubic, characteristic-two formal coefficients, empty and pole checks passed"

#eval (show IO _ from do
  let groups₁ : Vector (List (Fin 3)) 3 := #v[[0, 1, 2], [], []]
  let groups₂ : Vector (List (Fin 3)) 3 := #v[[], [], [0, 1, 2]]
  let d : Vector (Raw ℚ) 3 := Vector.replicate 3 #[1, 0]
  let w : Vector (Raw ℚ) 3 := Vector.replicate 3 #[0, 0]
  let h : Vector (Raw ℚ) 3 := Vector.replicate 3 #[0, 0]
  let (a, ca) := profileArithmetic (circuitProgram groups₁ #[1, 0] #v[1, 1, 1] d w h)
  let (b, cb) := profileArithmetic (circuitProgram groups₂ #[1, 0] #v[1, 1, 1] d w h)
  unless a == b && ca .add == cb .add + 6 &&
      ca .coefficientRead == cb .coefficientRead + 12 && ca .metadata == cb .metadata + 6 do
    throw (IO.userError "empty-group accumulation ignored the actual retained batch width")
  pure (ca .add, cb .add, ca .coefficientRead, cb .coefficientRead))

#eval (show IO _ from do
  let groups : Vector (List (Fin 0)) 10000 := Vector.replicate 10000 []
  let h : Vector (Raw ℚ) 10000 := Vector.replicate 10000 #[1, 0]
  let lambda : Vector ℚ 10000 := Vector.replicate 10000 1
  let p := circuitRaw groups #[1, 0] lambda #v[] #v[] h
  let (q, _) := profileArithmetic (circuitProgram groups #[1, 0] lambda #v[] #v[] h)
  unless p == #[20000, 0, 0] && q == p do
    throw (IO.userError "large streamed empty-group circuit returned incorrect coefficients")
  pure q)

example (kind : ArithmeticCostKind) :
    (profileArithmetic (circuitProgram (F := ZMod 17) groups #[-2, 5] #v[4, 6]
      denominator weight helper)).2 kind ≤
      if kind = .add ∨ kind = .mul ∨ kind = .sub ∨ kind = .coefficientRead ∨
        kind = .metadata then 1200 else 0 := by
  exact profileArithmetic_circuitProgram_le_of_partition (F := ZMod 17)
    groups #[-2, 5] #v[4, 6]
    denominator weight helper 1 (by decide) (by decide)
    (by intro k; fin_cases k <;> decide) (by intro k; fin_cases k <;> decide)
    (by decide) (by intro i; fin_cases i <;> decide)
    (by intro i; fin_cases i <;> decide) (by intro k; fin_cases k <;> decide)
    (by decide) kind

example {R : Type 1} [CommRing R] {T K : ℕ}
    (groups : Vector (List (Fin T)) K) (kernel : Raw R) (lambda : Vector R K)
    (denominator weight : Vector (Raw R) T) (helper : Vector (Raw R) K) (ell : ℕ)
    (hgroups : ∀ k, (groups.get k).length ≤ ell)
    (hden : ∀ i, (denominator.get i).size ≤ 2)
    (hweight : ∀ i, (weight.get i).size ≤ 2)
    (hhelper : ∀ k, (helper.get k).size ≤ 2) (hkernel : kernel.size ≤ 2) :
    (circuitRaw groups kernel lambda denominator weight helper).size ≤ ell + 3 :=
  size_circuitRaw_le groups kernel lambda denominator weight helper ell
    hgroups hden hweight hhelper hkernel

open Lean Elab Command in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for name in #[``map_reconstructWithKernel, ``toPoly_groupFractionRaw,
      ``toPoly_residualRaw, ``toPoly_circuitRaw,
      ``toPoly_circuitRaw_denominator, ``profileArithmetic_circuitProgram_fst,
      ``size_groupFractionRaw_le, ``size_residualRaw_le, ``size_batchRaw_le,
      ``size_circuitRaw_le, ``profileArithmetic_residualProgram,
      ``profileArithmetic_residualProgram_le, ``profileArithmetic_batchFromProgram_nil,
      ``profileArithmetic_batchFromProgram_cons, ``profileArithmetic_batchFromProgram_le,
      ``profileArithmetic_circuitProgram, ``profileArithmetic_circuitProgram_le,
      ``profileArithmetic_circuitProgram_le_of_partition] do
    let axioms ← collectAxioms name
    unless axioms.all allowed.contains do
      throwError "unexpected coefficient-circuit axioms: {name}: {axioms}"

end CoefficientCircuitTests
