/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ProofSystem.ConstraintSystem.Basic
import ArkLib.ProofSystem.ConstraintSystem.R1CS
import ArkLib.ProofSystem.ConstraintSystem.Plonk

/-!
# Concrete instances of the universal `ConstraintSystem`

This file wires the existing R1CS and Plonkish relations into the universal
`ConstraintSystem` abstraction as a smoke test that the interface captures their shapes.

- `R1CS.toConstraintSystem R` packages R1CS of every size `(m, n, n_w)` over a commutative
  semiring `R` as a single constraint system. The three matrices `A, B, C` live in the
  oracle-statement slot.
- `Plonk.toConstraintSystem R` packages the gate-based Plonkish relation of every shape
  `(numWires, numGates, ℓ)` over a commutative ring `R`. The gate layout itself lives in
  the oracle-statement slot.

Each instance is accompanied by a trivial verification lemma showing the `satisfies`
predicate agrees with the original relation by definitional equality.
-/

/-- R1CS of every size over a fixed commutative semiring, packaged as a universal
`ConstraintSystem`. The in-the-clear statement holds the public inputs, the oracle
statement holds the three constraint matrices `A, B, C`, and the witness holds the
private witness variables. -/
def R1CS.toConstraintSystem (R : Type*) [CommSemiring R] : ConstraintSystem where
  Index := R1CS.Size
  Stmt := fun sz => Fin sz.n_x → R
  OStmt := fun sz => R1CS.MatrixIdx → Matrix (Fin sz.m) (Fin sz.n) R
  Wit := fun sz => Fin sz.n_w → R
  satisfies := R1CS.relation R

@[simp] theorem R1CS.toConstraintSystem_satisfies
    (R : Type*) [CommSemiring R] (sz : R1CS.Size)
    (stmt : Fin sz.n_x → R)
    (mats : R1CS.MatrixIdx → Matrix (Fin sz.m) (Fin sz.n) R)
    (wit : Fin sz.n_w → R) :
    (R1CS.toConstraintSystem R).satisfies sz stmt mats wit ↔
      R1CS.relation R sz stmt mats wit :=
  Iff.rfl

/-- The index data for the Plonkish constraint system: the number of wires, the number
of gates, and the number of public inputs `ℓ ≤ numWires`. -/
structure Plonk.Shape where
  /-- Number of wires in the circuit. -/
  numWires : ℕ
  /-- Number of gates in the circuit. -/
  numGates : ℕ
  /-- Number of public inputs, bounded by `numWires`. -/
  ℓ : ℕ
  /-- Proof that `ℓ ≤ numWires`. -/
  hℓ : ℓ ≤ numWires

instance : Inhabited Plonk.Shape where
  default := ⟨0, 0, 0, Nat.le_refl _⟩

/-- The Plonkish relation of every shape over a fixed commutative ring, packaged as a
universal `ConstraintSystem`. The in-the-clear statement holds the public inputs, the
oracle statement holds the full gate layout (a `Plonk.ConstraintSystem` value), and the
witness holds the private wire values. -/
def Plonk.toConstraintSystem (𝓡 : Type) [CommRing 𝓡] : ConstraintSystem where
  Index := Plonk.Shape
  Stmt := fun s => Fin s.ℓ → 𝓡
  OStmt := fun s => Plonk.ConstraintSystem 𝓡 s.numWires s.numGates
  Wit := fun s => Fin (s.numWires - s.ℓ) → 𝓡
  satisfies := fun s stmt cs wit => Plonk.relation cs s.ℓ s.hℓ stmt wit

@[simp] theorem Plonk.toConstraintSystem_satisfies
    (𝓡 : Type) [CommRing 𝓡] (s : Plonk.Shape)
    (stmt : Fin s.ℓ → 𝓡)
    (cs : Plonk.ConstraintSystem 𝓡 s.numWires s.numGates)
    (wit : Fin (s.numWires - s.ℓ) → 𝓡) :
    (Plonk.toConstraintSystem 𝓡).satisfies s stmt cs wit ↔
      Plonk.relation cs s.ℓ s.hℓ stmt wit :=
  Iff.rfl
