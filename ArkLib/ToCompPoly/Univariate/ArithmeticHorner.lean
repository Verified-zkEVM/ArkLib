/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ToCompPoly.Univariate.Raw.Horner
public import ArkLib.ToCompPoly.Univariate.ArithmeticCost

/-!
# Arithmetic interpretation of seeded Horner evaluation

The ordinary evaluator and these request programs execute the same monadic tail-loop. A nonempty
input uses its highest coefficient as a seed, so no multiplication or addition is charged for that
coefficient. The generic reader can bind stored base-field cells without allocating an intermediate
challenge-field coefficient array; its visits and embeddings must be reported separately by the
consumer. Array size, index arithmetic and loop control are not field arithmetic requests.
-/

@[expose] public section

namespace CompPoly.Arithmetic
open OracleComp OracleSpec
variable {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]

/-- Interpret the shared seeded Horner core with explicit arithmetic requests and an arbitrary
coefficient reader. Reader effects are retained and charged by its own profile. -/
def evalHornerWithReadProgram (read : Nat → OracleComp (ArithmeticSpec F) F)
    (length : Nat) (x : F) : OracleComp (ArithmeticSpec F) F :=
  CPolynomial.Raw.evalHornerM read
    (fun a b => Subtype.val <$> Arithmetic.mul a b)
    (fun a b => Subtype.val <$> Arithmetic.add a b) length x

/-- Array-backed seeded Horner: each stored coefficient is read once, highest index first. -/
def evalHornerProgram (p : Array F) (x : F) : OracleComp (ArithmeticSpec F) F :=
  evalHornerWithReadProgram (fun i => Subtype.val <$> Arithmetic.coefficientRead p i) p.size x

/-- One lower-coefficient step issues one multiplication and one addition. -/
def hornerStepCost : ArithmeticCost
  | .add | .mul => 1
  | _ => 0

/-- Sum the actual reader profiles and the lower-coefficient arithmetic steps. Natural-number
control and an outer size request, if any, remain separate from these arithmetic requests. -/
def hornerCost (length : Nat) (readerCost : Nat → ArithmeticCost) : ArithmeticCost :=
  fun kind => (∑ i : Fin length, readerCost i.val kind) + (length - 1) * hornerStepCost kind

private theorem profileArithmetic_hornerLoopM
    (read : Nat → OracleComp (ArithmeticSpec F) F) (values : Nat → F)
    (readerCost : Nat → ArithmeticCost) (n : Nat) (x acc : F)
    (hread : ∀ i, i < n → profileArithmetic (read i) = (values i, readerCost i)) :
    profileArithmetic (CPolynomial.Raw.hornerLoopM read
      (fun a b => Subtype.val <$> Arithmetic.mul a b)
      (fun a b => Subtype.val <$> Arithmetic.add a b) x n acc) =
      (CPolynomial.Raw.hornerLoopM (m := Id) values
        (fun a b => a * b) (fun a b => a + b) x n acc,
        fun kind => (∑ i : Fin n, readerCost i.val kind) + n * hornerStepCost kind) := by
  induction n generalizing acc with
  | zero =>
    simp only [CPolynomial.Raw.hornerLoopM, profileArithmetic_pure]
    apply Prod.ext
    · rfl
    · funext kind
      simp
  | succ n ih =>
    simp only [CPolynomial.Raw.hornerLoopM, profileArithmetic_bind,
      profileArithmetic_map, profileArithmetic_mul, profileArithmetic_add]
    rw [hread n (Nat.lt_succ_self n)]
    dsimp only
    rw [ih (acc * x + values n) (fun i hi => hread i (by omega))]
    apply Prod.ext
    · rfl
    · funext kind
      cases kind <;>
        simp [hornerStepCost, arithmeticCost, ArithmeticOp.costKind,
          Fin.sum_univ_castSucc] <;> omega

/-- Exact profile of the shared core, allowing index-dependent reader costs. -/
theorem profileArithmetic_evalHornerWithReadProgram
    (read : Nat → OracleComp (ArithmeticSpec F) F) (values : Nat → F)
    (readerCost : Nat → ArithmeticCost) (length : Nat) (x : F)
    (hread : ∀ i, i < length → profileArithmetic (read i) = (values i, readerCost i)) :
    profileArithmetic (evalHornerWithReadProgram read length x) =
      (CPolynomial.Raw.evalHornerM (m := Id) values
        (fun a b => a * b) (fun a b => a + b) length x,
        hornerCost length readerCost) := by
  cases length with
  | zero =>
    simp only [evalHornerWithReadProgram, CPolynomial.Raw.evalHornerM, profileArithmetic_pure]
    apply Prod.ext
    · rfl
    · funext kind
      simp [hornerCost]
  | succ n =>
    simp only [evalHornerWithReadProgram, CPolynomial.Raw.evalHornerM, profileArithmetic_bind]
    rw [hread n (Nat.lt_succ_self n)]
    dsimp only
    rw [profileArithmetic_hornerLoopM read values readerCost n x (values n)
      (fun i hi => hread i (by omega))]
    apply Prod.ext
    · rfl
    · funext kind
      simp [hornerCost, Fin.sum_univ_castSucc, Nat.add_comm, Nat.add_left_comm]

private theorem simulateQ_hornerLoopM
    (read : Nat → OracleComp (ArithmeticSpec F) F) (n : Nat) (x acc : F) :
    simulateQ arithmeticAnswer (CPolynomial.Raw.hornerLoopM read
      (fun a b => Subtype.val <$> Arithmetic.mul a b)
      (fun a b => Subtype.val <$> Arithmetic.add a b) x n acc) =
      CPolynomial.Raw.hornerLoopM (m := Id) (fun i => simulateQ arithmeticAnswer (read i))
        (fun a b => a * b) (fun a b => a + b) x n acc := by
  have hmul (a b : F) :
      simulateQ arithmeticAnswer (Subtype.val <$> Arithmetic.mul a b) = a * b := by
    rw [simulateQ_map]
    exact (simulateQ arithmeticAnswer (Arithmetic.mul a b)).property
  have hadd (a b : F) :
      simulateQ arithmeticAnswer (Subtype.val <$> Arithmetic.add a b) = a + b := by
    rw [simulateQ_map]
    exact (simulateQ arithmeticAnswer (Arithmetic.add a b)).property
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    simp only [CPolynomial.Raw.hornerLoopM, simulateQ_bind, hmul, hadd, ih]

/-- Arithmetic erasure preserves the same reader interpretations in the same shared core. -/
theorem simulateQ_evalHornerWithReadProgram
    (read : Nat → OracleComp (ArithmeticSpec F) F) (length : Nat) (x : F) :
    simulateQ arithmeticAnswer (evalHornerWithReadProgram read length x) =
      CPolynomial.Raw.evalHornerM (m := Id) (fun i => simulateQ arithmeticAnswer (read i))
        (fun a b => a * b) (fun a b => a + b) length x := by
  cases length with
  | zero => rfl
  | succ n =>
    simp [evalHornerWithReadProgram, CPolynomial.Raw.evalHornerM, simulateQ_bind,
      simulateQ_hornerLoopM]

/-- The arithmetic array interpreter erases to the explicitly selected pure evaluator. -/
theorem simulateQ_evalHornerProgram (p : Array F) (x : F) :
    simulateQ arithmeticAnswer (evalHornerProgram p x) = CPolynomial.Raw.evalHornerSeeded x p := by
  rw [evalHornerProgram, simulateQ_evalHornerWithReadProgram]
  apply CPolynomial.Raw.evalHornerM_congr_read (m := Id)
  intro i hi
  rw [simulateQ_map]
  exact (simulateQ arithmeticAnswer (Arithmetic.coefficientRead p i)).property

/-- An array of length L uses L coefficient reads and L-1 additions/multiplications, including
empty and singleton inputs. All other arithmetic coordinates are zero. -/
theorem profileArithmetic_evalHornerProgram (p : Array F) (x : F) :
    profileArithmetic (evalHornerProgram p x) =
      (CPolynomial.Raw.evalHornerSeeded x p,
        fun kind => match kind with
        | .coefficientRead => p.size
        | .mul | .add => p.size - 1
        | _ => 0) := by
  rw [evalHornerProgram, profileArithmetic_evalHornerWithReadProgram
    (values := fun i => p[i]?.getD 0)
    (readerCost := fun i => arithmeticCost (ArithmeticOp.coefficientRead p i))]
  · apply Prod.ext
    · rfl
    · funext kind
      cases kind <;> simp [hornerCost, hornerStepCost, arithmeticCost, ArithmeticOp.costKind]
  · intro i hi
    simp
end CompPoly.Arithmetic
