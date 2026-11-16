/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.ConstraintSystem.Basic
public import ArkLib.ProofSystem.ConstraintSystem.R1CS
public import ArkLib.ProofSystem.ConstraintSystem.Plonk
public import ArkLib.ProofSystem.ConstraintSystem.Air

/-!
# Concrete instances of the universal `ConstraintSystem`

This file packages the R1CS, Plonkish and AIR relations as indexed constraint systems.

- `R1CS.toConstraintSystem R` packages R1CS of every size `(m, n, n_w)` over a commutative
  semiring `R` as a single constraint system. The three matrices `A, B, C` live in the
  oracle-statement slot.
- `Plonk.toConstraintSystem R` packages the gate-based Plonkish relation of every shape
  `(numWires, numGates, ℓ)` over a commutative ring `R`. The gate layout itself lives in
  the oracle-statement slot. Public inputs occupy the prefix of the wire assignment,
  followed by the private witness.
- `Air.toConstraintSystem F` packages AIRs over a field `F`:
  - the index holds the height, the constraints and the periodic columns;
  - the statement holds the public values;
  - the oracle statement holds the preprocessed columns;
  - the witness is the main trace alone, so the prover cannot pick the public values.

Each instance is accompanied by a trivial verification lemma showing the `satisfies`
predicate agrees with the original relation by definitional equality.
-/

@[expose] public section

/-- R1CS of every size over a fixed commutative semiring, packaged as a universal
`ConstraintSystem`. The in-the-clear statement holds the public inputs, the oracle
statement holds the three constraint matrices `A, B, C`, and the witness holds the
private witness variables. -/
def R1CS.toConstraintSystem (R : Type*) [CommSemiring R] : ConstraintSystem where
  Index := R1CS.Size
  Stmt := fun sz => Fin sz.n_x → R
  OStmt := fun sz => R1CS.MatrixIdx → Matrix (Fin sz.m) (Fin sz.n) R
  toRelation := Interaction.Oracle.Relation.ofPredicate
    (fun sz _ => Fin sz.n_w → R) (fun sz c w => R1CS.relation R sz c.1 c.2 w)

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
def Plonk.toConstraintSystem (𝓡 : Type) [CommRing 𝓡] : _root_.ConstraintSystem where
  Index := Plonk.Shape
  Stmt := fun s => Fin s.ℓ → 𝓡
  OStmt := fun s => Plonk.ConstraintSystem 𝓡 s.numWires s.numGates
  toRelation := Interaction.Oracle.Relation.ofPredicate
    (fun s _ => Fin (s.numWires - s.ℓ) → 𝓡)
    (fun s c w => Plonk.relation c.2 s.ℓ s.hℓ c.1 w)

@[simp] theorem Plonk.toConstraintSystem_satisfies
    (𝓡 : Type) [CommRing 𝓡] (s : Plonk.Shape)
    (stmt : Fin s.ℓ → 𝓡)
    (cs : Plonk.ConstraintSystem 𝓡 s.numWires s.numGates)
    (wit : Fin (s.numWires - s.ℓ) → 𝓡) :
    (Plonk.toConstraintSystem 𝓡).satisfies s stmt cs wit ↔
      Plonk.relation cs s.ℓ s.hℓ stmt wit :=
  Iff.rfl

/-- The index data of an AIR, which the verifier knows in full.

It holds the trace height, the constraints with their domains and the periodic columns. -/
structure Air.Shape (F : Type*) [Field F] where
  /-- Number of rows of the trace. -/
  height : ℕ
  /-- The constraints, each with its domain. -/
  constraints : List (Air.Constraint F)
  /-- The periodic columns, already expanded to one value per row. -/
  periodic : ℕ → ℕ → F

/-- AIRs over a fixed field, packaged as a universal `ConstraintSystem`.

- index: the height, the constraints and the periodic columns;
- statement in the clear: the public values;
- oracle statement: the preprocessed columns;
- witness: the main trace. -/
def Air.toConstraintSystem (F : Type*) [Field F] : ConstraintSystem where
  Index := Air.Shape F
  Stmt := fun _ => ℕ → F
  OStmt := fun _ => ℕ → ℕ → F
  toRelation := Interaction.Oracle.Relation.ofPredicate
    (fun _ _ => ℕ → ℕ → F)
    (fun sh c main => Air.SatisfiesOn sh.constraints
      { height := sh.height, main := main, prep := c.2, pub := c.1, periodic := sh.periodic })

@[simp] theorem Air.toConstraintSystem_satisfies
    (F : Type*) [Field F] (sh : Air.Shape F)
    (pub : ℕ → F) (prep : ℕ → ℕ → F) (main : ℕ → ℕ → F) :
    (Air.toConstraintSystem F).satisfies sh pub prep main ↔
      Air.SatisfiesOn sh.constraints
        { height := sh.height, main := main, prep := prep, pub := pub,
          periodic := sh.periodic } :=
  Iff.rfl
