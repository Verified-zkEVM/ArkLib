/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import CompPoly.Data.MvPolynomial.Notation

/-! # The Plonk relation

We first define the initial relation of Plonk. The paper first defines a constraint system, then
define what it means for the constraint system to be satisfied. This forms the core relation of
Plonk. -/

namespace Plonk

/-- A wire assignment for a single gate of the Plonk constraint system, parametrized by
  `numWires : ℕ`, consists of three indices `a, b, c` that specifies the location of the
  left, right and output wires for that gate. -/
structure WireIndices (numWires : ℕ) where
  /-- The index of the left wire -/
  a : Fin numWires
  /-- The index of the right wire -/
  b : Fin numWires
  /-- The index of the output wire -/
  c : Fin numWires
deriving DecidableEq

/-- A selector for a Plonk constraint system is a set of coefficients that determine the gate type
-/
structure Selector (𝓡 : Type*) where
  /-- left input -/
  qL : 𝓡
  /-- right input -/
  qR : 𝓡
  /-- output -/
  qO : 𝓡
  /-- multiplication term -/
  qM : 𝓡
  /-- constant term -/
  qC : 𝓡
deriving DecidableEq

/-- A single gate of the Plonk constraint system, which consists of a selector and a wire index
  assignment. -/
structure Gate (𝓡 : Type*) (numWires : ℕ) extends Selector 𝓡, WireIndices numWires
deriving DecidableEq

namespace Gate

variable {𝓡 : Type} [CommRing 𝓡] {numWires : ℕ}

/-- Evaluate a gate on a given input vector. -/
def eval (x : Fin numWires → 𝓡) (g : Gate 𝓡 numWires) : 𝓡 :=
  g.qL * x g.a + g.qR * x g.b + g.qO * x g.c + g.qM * (x g.a * x g.b) + g.qC

/-- A gate accepts an input vector `x` if its evaluation at `x` is zero. -/
def accepts (x : Fin numWires → 𝓡) (g : Gate 𝓡 numWires) : Prop :=
  g.eval x = 0

/-! ## Some example constraints -/

/-- An addition gate constrains `x(c) = x(a) + x(b)` -/
def add (a b c : Fin numWires) : Gate 𝓡 numWires :=
  { qL := 1, qR := 1, qO := -1, qM := 0, qC := 0, a := a, b := b, c := c }

/-- A multiplication gate constrains `x(c) = x(a) * x(b)` -/
def mul (a b c : Fin numWires) : Gate 𝓡 numWires :=
  { qL := 0, qR := 0, qO := -1, qM := 1, qC := 0, a := a, b := b, c := c }

/-- A booleanity gate constrains `x(j) * (x(j) - 1) = 0`, implying `x(j) ∈ {0,1}`. -/
def bool (j : Fin numWires) : Gate 𝓡 numWires :=
  { qL := -1, qR := 0, qO := 0, qM := 1, qC := 0, a := j, b := j, c := j }

/-- An equality gate constrains `x(i) = c` for some public value `c`. -/
def eq (i : Fin numWires) (c : 𝓡) : Gate 𝓡 numWires :=
  { qL := 1, qR := 0, qO := 0, qM := 0, qC := -c, a := i, b := i, c := i }

-- We can show that these gates perform their intended operations.

variable {a b c j : Fin numWires} {x : Fin numWires → 𝓡}

@[simp]
theorem add_accepts_iff : (add a b c).accepts x ↔ x c = x a + x b := by
  simp [add, Gate.accepts, Gate.eval, add_neg_eq_zero, eq_comm]

@[simp]
theorem mul_accepts_iff : (mul a b c).accepts x ↔ x c = x a * x b := by
  simp [mul, Gate.accepts, Gate.eval, neg_add_eq_zero]

@[simp]
theorem bool_accepts_iff : (bool j).accepts x ↔ x j * (x j - 1) = 0 := by
  simp [bool, Gate.accepts, Gate.eval]
  ring_nf

-- Stronger statement that holds when `𝓡` is a domain; `simp` will hopefully apply this first
@[simp]
theorem bool_accepts_iff_of_domain [IsDomain 𝓡] :
    (bool j).accepts x ↔ x j = 0 ∨ x j = 1 :=
  Iff.trans bool_accepts_iff (by simp [sub_eq_zero])

@[simp]
theorem eq_accepts (i : Fin numWires) (c : 𝓡) (x : Fin numWires → 𝓡) :
    (eq i c).accepts x ↔ x i = c := by
  simp [eq, Gate.eval, Gate.accepts, add_neg_eq_zero]

end Gate

/-- A Plonk constraint system is a vector of `numGates` gates, each parametrized by the underlying
  ring `𝓡` and `numWires`, the number of wires.

  Marked `protected` so that bare `ConstraintSystem` inside `namespace Plonk` refers to the
  universal `ConstraintSystem` in `ArkLib.ProofSystem.ConstraintSystem.Basic`. Users access
  this definition as `Plonk.ConstraintSystem`.
-/
protected def ConstraintSystem (𝓡 : Type) (numWires numGates : ℕ) := Fin numGates → Gate 𝓡 numWires

variable {𝓡 : Type} [CommRing 𝓡] {numWires numGates : ℕ}

-- instance [Inhabited 𝓡] : Inhabited (ConstraintSystem 𝓡 numWires numGates) :=
--   inferInstance

-- instance : DecidableEq (ConstraintSystem 𝓡 numWires numGates) :=
--   inferInstance

namespace ConstraintSystem

/-- A constraint system accepts an input vector `x` if all of its gates accept `x`. -/
def accepts (x : Fin numWires → 𝓡)
    (cs : Plonk.ConstraintSystem 𝓡 numWires numGates) : Prop :=
  ∀ i : Fin numGates, (cs i).accepts x

/-- The partition induced by a constraint system as defined in the Plonk paper.

For `i ∈ [numWires]`, let `T_i ⊆ [3*numGates]` be the set of indices `j` such that `V_j = i`,
where `V` is the flattened vector of all wire indices `(a,b,c)` from all gates.
This creates a partition of `[3 * numGates]` based on which gates use each wire index. -/
def partition (cs : Plonk.ConstraintSystem 𝓡 numWires numGates) :
    Fin numWires → Finset (Fin (3 * numGates)) :=
  -- We first cast via the equivalence `Fin (3 * numGates) ≃ Fin 3 × Fin numGates`,
  -- then filter by matching on the first coordinate `j.1`, which determines which wire we are
  -- interested in (`a`, `b`, or `c`), and then check whether `(cs j.2).w = i` for the appropriate
  -- wire `w ∈ {a,b,c}`.
  fun i => Finset.map (Equiv.toEmbedding finProdFinEquiv)
    (Finset.filter (fun j => if j.1 = 0 then (cs j.2).a = i
      else if j.1 = 1 then (cs j.2).b = i else (cs j.2).c = i)
    (Finset.univ : Finset (Fin 3 × Fin numGates)))

/-- The permutation corresponding to the partition induced by a constraint system. -/
def perm (cs : Plonk.ConstraintSystem 𝓡 numWires numGates) : Equiv.Perm (Fin (3 * numGates)) :=
  sorry

/-- A constraint system is prepared for `ℓ` public inputs, for some `ℓ ≤ numGates, numWires`,
  if for all `i ∈ [ℓ]`, the `i`-th gate constrains the `i`-th wire to be some public value. -/
def isPreparedFor (ℓ : ℕ) (hℓ : ℓ ≤ numGates) (hℓ' : ℓ ≤ numWires)
    (cs : Plonk.ConstraintSystem 𝓡 numWires numGates) : Prop :=
  ∀ i : Fin ℓ, ∃ c, cs (Fin.castLE hℓ i) = Gate.eq (Fin.castLE hℓ' i) c

end ConstraintSystem

-- Finally, we define the Plonk relation.

/-- To define a relation based on the constraint system, we extend it with:
- A natural number `ℓ ≤ m` representing the number of public inputs
- A subset `ℐ ⊂ [m]` of "public inputs" (assumed to be `{1,...,ℓ}` without loss of generality)
-/
def relation (cs : Plonk.ConstraintSystem 𝓡 numWires numGates) (ℓ : ℕ) (hℓ : ℓ ≤ numWires) :
    (publicInputs : Fin ℓ → 𝓡) → (privateWitness : Fin (numWires - ℓ) → 𝓡) → Prop :=
  fun (x : Fin ℓ → 𝓡) (ω : Fin (numWires - ℓ) → 𝓡) =>
    let combined := Fin.append x ω ∘ Fin.cast (by omega)
    cs.accepts combined

end Plonk
