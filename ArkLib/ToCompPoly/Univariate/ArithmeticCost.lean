/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ToCompPoly.Univariate.Arithmetic

/-!
# Profiles of measured array operations

The equations count executed primitive requests and designated control ticks. Array sizes
bound coefficient requests independently of their values.
-/

@[expose] public section
namespace CompPoly

open OracleComp OracleSpec
variable {F A B : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]

/-- Mapping a result preserves its program profile. -/
@[simp]
theorem profileArithmetic_map
    (f : A → B) (p : OracleComp (ArithmeticSpec F) A) :
    profileArithmetic (f <$> p) =
      let a := profileArithmetic p
      (f a.1, a.2) := by
  rw [map_eq_bind_pure_comp, profileArithmetic_bind]
  simp only [Function.comp_apply, profileArithmetic_pure, add_zero]

/-- A control tick has one metadata request. -/
@[simp]
theorem profileArithmetic_tick : profileArithmetic (F := F) Arithmetic.tick =
    ((), arithmeticCost (ArithmeticOp.metadata : ArithmeticOp F)) := by
  exact profileArithmetic_query .metadata

/-- Multiplication returns its certified product and one multiplication request. -/
@[simp]
theorem profileArithmetic_mul (a b : F) : profileArithmetic (Arithmetic.mul a b) =
    (⟨a * b, rfl⟩, arithmeticCost (ArithmeticOp.mul a b)) := by
  exact profileArithmetic_query (.mul a b)

/-- Addition returns its certified sum and one addition request. -/
@[simp]
theorem profileArithmetic_add (a b : F) : profileArithmetic (Arithmetic.add a b) =
    (⟨a + b, rfl⟩, arithmeticCost (ArithmeticOp.add a b)) := by
  exact profileArithmetic_query (.add a b)

/-- Subtraction returns its certified difference and one subtraction request. -/
@[simp]
theorem profileArithmetic_sub (a b : F) : profileArithmetic (Arithmetic.sub a b) =
    (⟨a - b, rfl⟩, arithmeticCost (ArithmeticOp.sub a b)) := by
  exact profileArithmetic_query (.sub a b)

/-- Inversion returns its certified inverse and one inversion request. -/
@[simp]
theorem profileArithmetic_inv (a : F) : profileArithmetic (Arithmetic.inv a) =
    (⟨a⁻¹, rfl⟩, arithmeticCost (ArithmeticOp.inv a)) := by
  exact profileArithmetic_query (.inv a)

/-- Equality returns its certified decision and one equality request. -/
@[simp]
theorem profileArithmetic_eq (a b : F) : profileArithmetic (Arithmetic.eq a b) =
    (⟨decide (a = b), rfl⟩, arithmeticCost (ArithmeticOp.eq a b)) := by
  exact profileArithmetic_query (.eq a b)

/-- A coefficient read returns the padded entry and one coefficient request. -/
@[simp]
theorem profileArithmetic_coefficientRead (a : Array F) (i : ℕ) :
    profileArithmetic (Arithmetic.coefficientRead a i) =
    (⟨a[i]?.getD 0, rfl⟩, arithmeticCost (ArithmeticOp.coefficientRead a i)) := by
  exact profileArithmetic_query (.coefficientRead a i)

/-- A cached-node read returns the padded entry and one node request. -/
@[simp]
theorem profileArithmetic_nodeRead (a : Array F) (i : ℕ) :
    profileArithmetic (Arithmetic.nodeRead a i) =
    (⟨a[i]?.getD 0, rfl⟩, arithmeticCost (ArithmeticOp.nodeRead a i)) := by
  exact profileArithmetic_query (.nodeRead a i)

/-- A cached-value read returns the padded entry and one value request. -/
@[simp]
theorem profileArithmetic_valueRead (a : Array F) (i : ℕ) :
    profileArithmetic (Arithmetic.valueRead a i) =
    (⟨a[i]?.getD 0, rfl⟩, arithmeticCost (ArithmeticOp.valueRead a i)) := by
  exact profileArithmetic_query (.valueRead a i)

/-- Binding a certified result selects the continuation at its specified value. -/
@[simp 1100]
theorem profileArithmetic_bind_certified {a : A}
    (program : OracleComp (ArithmeticSpec F) {b : A // b = a})
    (next : {b : A // b = a} → OracleComp (ArithmeticSpec F) B) :
    profileArithmetic (program >>= next) =
      let b := profileArithmetic (next ⟨a, rfl⟩)
      (b.1, (profileArithmetic program).2 + b.2) := by
  rw [profileArithmetic_bind]
  exact congrArg (fun value : {b : A // b = a} ↦
    let b := profileArithmetic (next value)
    (b.1, (profileArithmetic program).2 + b.2))
    (profileArithmetic_certified_fst program)

/-- Projecting a certified result yields its specified value. -/
@[simp]
theorem profileArithmetic_certified_val {a : A}
    (program : OracleComp (ArithmeticSpec F) {b : A // b = a}) :
    (profileArithmetic program).1.val = a :=
  (profileArithmetic program).1.property

end CompPoly

namespace CompPoly.Arithmetic
open OracleComp
variable {F : Type} [Monoid F] [Zero F] [Add F] [Sub F] [Inv F] [DecidableEq F]

/-- Linear powering uses exactly one multiplication per exponent step. -/
theorem profileArithmetic_power (x : F) (n : ℕ) :
    (profileArithmetic (power x n)).2 =
      fun kind ↦ (if kind = .mul then n else 0) +
        (if kind = .metadata then n + 1 else 0) := by
  induction n with
  | zero =>
    funext kind
    cases kind <;> simp [power, arithmeticCost, ArithmeticOp.costKind]
  | succ n ih =>
    funext kind
    cases kind <;>
      simp [power, profileArithmetic_bind, ih, arithmeticCost, ArithmeticOp.costKind,
        Nat.add_left_comm, Nat.add_comm]

end CompPoly.Arithmetic

namespace CompPoly.Arithmetic
open OracleComp
variable {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]

/-- A list traversal adds its cell profiles and one tick per cell and terminal step. -/
theorem profileArithmetic_certifiedMap {A B : Type} (f : A → B)
    (step : (a : A) → OracleComp (ArithmeticSpec F) {b : B // b = f a})
    (xs : List A) (kind : ArithmeticCostKind) :
    (profileArithmetic (certifiedMap f step xs)).2 kind =
      (xs.map (fun x ↦ (profileArithmetic (step x)).2 kind)).sum +
        (if kind = .metadata then xs.length + 1 else 0) := by
  induction xs with
  | nil =>
    cases kind <;>
      simp [certifiedMap, arithmeticCost, ArithmeticOp.costKind]
  | cons x xs ih =>
    cases kind <;>
      simp [certifiedMap, profileArithmetic_bind, ih, arithmeticCost, ArithmeticOp.costKind,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm]
    omega

/-- An array construction sums its index profiles and traversal ticks. -/
theorem profileArithmetic_certifiedOfFn {n : ℕ} (f : Fin n → F)
    (step : (i : Fin n) → OracleComp (ArithmeticSpec F) {a : F // a = f i})
    (kind : ArithmeticCostKind) :
    (profileArithmetic (certifiedOfFn f step)).2 kind =
      ((List.finRange n).map (fun i ↦ (profileArithmetic (step i)).2 kind)).sum +
        (if kind = .metadata then n + 1 else 0) := by
  simp [certifiedOfFn, profileArithmetic_certifiedMap]

/-- Scalar multiplication reads and multiplies each coefficient once. -/
theorem profileArithmetic_smulRaw (x : F) (p : CPolynomial.Raw F) :
    (profileArithmetic (smulRaw x p)).2 = fun kind ↦
      if kind = .mul ∨ kind = .coefficientRead then p.size
      else if kind = .metadata then p.size + 1 else 0 := by
  funext kind
  cases kind <;>
    simp [smulRaw, profileArithmetic_certifiedOfFn,
      arithmeticCost, ArithmeticOp.costKind]

/-- Padded addition reads both arrays at each output position. -/
theorem profileArithmetic_addRaw (p q : CPolynomial.Raw F) :
    (profileArithmetic (addRaw p q)).2 = fun kind ↦
      if kind = .add then max p.size q.size
      else if kind = .coefficientRead then 2 * max p.size q.size
      else if kind = .metadata then max p.size q.size + 1 else 0 := by
  funext kind
  cases kind <;>
    simp [addRaw, profileArithmetic_certifiedOfFn,
      arithmeticCost, ArithmeticOp.costKind, Nat.mul_comm]

end CompPoly.Arithmetic

namespace CompPoly

open OracleComp OracleSpec

variable {F A : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]

/-- A vector traversal with a constant instruction profile per entry charges that profile
once per index and returns the vector of the specified entry values. -/
theorem profileArithmetic_ofFnM_uniform {n : ℕ}
    (f : Fin n → OracleComp (ArithmeticSpec F) A) (values : Fin n → A)
    (cost : ArithmeticCost)
    (h : ∀ i, profileArithmetic (f i) = (values i, cost)) :
    profileArithmetic (Vector.ofFnM f) =
      (Vector.ofFn values, fun kind => n * cost kind) := by
  induction n with
  | zero =>
    simp only [Vector.ofFnM_zero, profileArithmetic_pure]
    apply Prod.ext
    · ext i hi; omega
    · funext kind
      simp
  | succ n ih =>
    rw [Vector.ofFnM_succ', profileArithmetic_bind, h]
    dsimp only
    rw [profileArithmetic_bind, ih (fun i => f i.succ) (fun i => values i.succ)
      (fun i => h i.succ)]
    simp only [profileArithmetic_pure]
    apply Prod.ext
    · simp [Vector.ofFn_succ']
    · funext kind
      simp [Nat.add_mul, Nat.add_comm]

/-- A vector traversal returns its specified values and sums the actual index-dependent
instruction profiles. -/
theorem profileArithmetic_ofFnM {n : ℕ}
    (f : Fin n → OracleComp (ArithmeticSpec F) A) (values : Fin n → A)
    (cost : Fin n → ArithmeticCost)
    (h : ∀ i, profileArithmetic (f i) = (values i, cost i)) :
    profileArithmetic (Vector.ofFnM f) =
      (Vector.ofFn values, fun kind => ∑ i : Fin n, cost i kind) := by
  induction n with
  | zero =>
    simp only [Vector.ofFnM_zero, profileArithmetic_pure]
    apply Prod.ext
    · ext i hi; omega
    · funext kind
      simp
  | succ n ih =>
    rw [Vector.ofFnM_succ', profileArithmetic_bind, h]
    dsimp only
    rw [profileArithmetic_bind, ih (fun i => f i.succ) (fun i => values i.succ)
      (fun i => cost i.succ) (fun i => h i.succ)]
    simp only [profileArithmetic_pure]
    apply Prod.ext
    · simp [Vector.ofFn_succ']
    · funext kind
      simp [Fin.sum_univ_succ]

end CompPoly
