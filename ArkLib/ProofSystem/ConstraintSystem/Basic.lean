/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import Mathlib.Data.Set.Defs

/-!
# Universal constraint system abstraction

This file introduces a small theory of constraint systems that provides a uniform interface
for the various concrete systems used across ArkLib (R1CS, Plonkish, lookups, memory
checking, AIR, CCS, and DSL-level systems such as Clean's `FormalCircuit`).

The goals are:

1. **Unify**: capture the common shape `(index, statement, oracle statement, witness,
   satisfies)` so that protocols and compilers can be written once and instantiated for any
   concrete CS.
2. **Compose**: introduce morphisms `ConstraintSystem.Hom` that transport satisfiability
   along index/statement/witness maps, modelling reductions between constraint systems
   (e.g. Clean gadget → R1CS row block, Plonkish → CCS, Plain R1CS → padded R1CS).
3. **Extend with behaviour**: add a `BehavioralContract` layer that pairs a CS with
   user-facing I/O contracts (assumptions + spec), in the style of Clean's `FormalCircuit`.

## Design notes

- The structure is **indexed**: a single `ConstraintSystem` value packages an entire family
  of concrete relations (one per `Index`), so that, e.g., R1CS of every size is a single
  constraint system rather than one per `(m, n, n_w)`.
- The statement is split into an **in-the-clear** part (`Stmt`) and a **committed/oracle**
  part (`OStmt`). Use `fun _ => PUnit` for `OStmt` if the system is purely non-oracle. If
  multiple oracle slots are needed (as in R1CS with three matrices), bundle them via a
  dependent function type inside `OStmt`.
- `satisfies` is a `Prop`, not a `Set`, for ergonomic use inside proofs and reductions.
- Morphisms are one-way (completeness-preserving). Soundness-reflecting variants
  (extractors, embeddings, isos) are future work.
-/

universe u v w

/-- A **constraint system** packages a family of indexed relations into a single bundle.

For each `i : Index` there is a `Stmt i` (the in-the-clear statement), an `OStmt i` (the
committed/oracle-accessible statement data; use `PUnit` if absent), and a `Wit i` (the
private witness). The predicate `satisfies i s o w` asserts that the triple `(s, o, w)` is
a valid instance at index `i`. -/
structure ConstraintSystem : Type (max (u + 1) (v + 1) (w + 1)) where
  /-- Index type parametrising the family of relations (sizes, shape parameters, etc.). -/
  Index : Type u
  /-- In-the-clear part of the statement at each index. -/
  Stmt : Index → Type v
  /-- Committed/oracle-accessible part of the statement. Use `fun _ => PUnit` for a
    purely non-oracle constraint system. Multiple oracle slots can be bundled via a
    dependent function type (e.g. `MatrixIdx → Matrix _ _ R` for R1CS). -/
  OStmt : Index → Type v
  /-- Private witness. -/
  Wit : Index → Type w
  /-- The satisfiability predicate at each index. -/
  satisfies : (i : Index) → Stmt i → OStmt i → Wit i → Prop

namespace ConstraintSystem

variable (C : ConstraintSystem.{u, v, w})

/-- The underlying set-theoretic relation at a given index. -/
def relation (i : C.Index) : Set (C.Stmt i × C.OStmt i × C.Wit i) :=
  { t | C.satisfies i t.1 t.2.1 t.2.2 }

/-- Existence of valid oracle data and witness for a given in-the-clear statement. -/
def IsSatisfiable (i : C.Index) (s : C.Stmt i) : Prop :=
  ∃ o w, C.satisfies i s o w

/-- Build a constraint system from a plain indexed relation (no oracle statement slot). -/
def ofRelation
    {Idx : Type u} {S : Idx → Type v} {W : Idx → Type w}
    (rel : (i : Idx) → S i → W i → Prop) : ConstraintSystem.{u, v, w} where
  Index := Idx
  Stmt := S
  OStmt := fun _ => PUnit
  Wit := W
  satisfies := fun i s _ w => rel i s w

/-- Build a witness-free constraint system (assertions purely over the public and oracle
parts of the statement). -/
def ofWitnessFree
    {Idx : Type u} {S O : Idx → Type v}
    (rel : (i : Idx) → S i → O i → Prop) : ConstraintSystem.{u, v, 0} where
  Index := Idx
  Stmt := S
  OStmt := O
  Wit := fun _ => PUnit
  satisfies := fun i s o _ => rel i s o

end ConstraintSystem

/-!
## Morphisms between constraint systems

A `ConstraintSystem.Hom` transports valid instances of one constraint system to valid
instances of another. It consists of:

- `index` — a map of shape indices (e.g. scale the size of an R1CS instance);
- `stmt`, `oStmt`, `wit` — compatible maps of statement, oracle-statement, and witness
  data that in general may depend on the input in-the-clear statement;
- `preserves` — the core axiom that maps satisfying triples to satisfying triples.

Intuitively, `Hom C D` is a *completeness-preserving* reduction from `C` to `D`: if you can
satisfy `C` at some index, you can satisfy `D` at the image index, with an explicit
construction of the needed data. Soundness-reflecting morphisms (with extractors) are a
strict strengthening and are future work.

The name `Hom` follows Mathlib convention (`RelHom`, `RingHom`, `LinearMap`). A future
extension can add `ConstraintSystem.Hom.Embedding` or `ConstraintSystem.Iso` without
renaming anything.
-/

namespace ConstraintSystem

/-- A completeness-preserving morphism between constraint systems. -/
@[ext]
structure Hom (C D : ConstraintSystem.{u, v, w}) where
  /-- Map on index types. -/
  index : C.Index → D.Index
  /-- Map on in-the-clear statements. -/
  stmt : (i : C.Index) → C.Stmt i → D.Stmt (index i)
  /-- Map on oracle/committed statement data. It may depend on the in-the-clear statement
    as well, which is needed e.g. when the index encodes a global shape and the statement
    fixes public inputs before committed data is computed. -/
  oStmt : (i : C.Index) → (s : C.Stmt i) → C.OStmt i → D.OStmt (index i)
  /-- Map on witnesses, likewise allowed to depend on the input statement. -/
  wit : (i : C.Index) → (s : C.Stmt i) → C.Wit i → D.Wit (index i)
  /-- Preservation property: valid instances map to valid instances. -/
  preserves : ∀ i s o w,
    C.satisfies i s o w → D.satisfies (index i) (stmt i s) (oStmt i s o) (wit i s w)

namespace Hom

/-- The identity morphism on a constraint system. -/
def id (C : ConstraintSystem.{u, v, w}) : Hom C C where
  index := _root_.id
  stmt := fun _ => _root_.id
  oStmt := fun _ _ => _root_.id
  wit := fun _ _ => _root_.id
  preserves := fun _ _ _ _ h => h

/-- Composition of two morphisms. Reads right-to-left as usual. -/
def comp {C D E : ConstraintSystem.{u, v, w}} (g : Hom D E) (f : Hom C D) : Hom C E where
  index := g.index ∘ f.index
  stmt := fun i s => g.stmt (f.index i) (f.stmt i s)
  oStmt := fun i s o => g.oStmt (f.index i) (f.stmt i s) (f.oStmt i s o)
  wit := fun i s w => g.wit (f.index i) (f.stmt i s) (f.wit i s w)
  preserves := fun i s o w h =>
    g.preserves (f.index i) (f.stmt i s) (f.oStmt i s o) (f.wit i s w) (f.preserves i s o w h)

variable {C D E F : ConstraintSystem.{u, v, w}}

@[simp] theorem id_comp (f : Hom C D) : (id D).comp f = f := rfl

@[simp] theorem comp_id (f : Hom C D) : f.comp (id C) = f := rfl

theorem comp_assoc (h : Hom E F) (g : Hom D E) (f : Hom C D) :
    (h.comp g).comp f = h.comp (g.comp f) := rfl

end Hom

/-- Morphisms preserve satisfiability. -/
theorem Hom.isSatisfiable_map {C D : ConstraintSystem.{u, v, w}} (f : Hom C D)
    {i : C.Index} {s : C.Stmt i} (hs : C.IsSatisfiable i s) :
    D.IsSatisfiable (f.index i) (f.stmt i s) := by
  obtain ⟨o, w, h⟩ := hs
  exact ⟨f.oStmt i s o, f.wit i s w, f.preserves i s o w h⟩

end ConstraintSystem

/-!
## Behavioural contracts

In DSL-level systems like Clean, a circuit is bundled with a user-facing contract:
preconditions (`Assumptions`) on the statement and a high-level specification (`Spec`)
relating statement and witness. A `BehavioralContract` lifts this pattern onto an
arbitrary constraint system: at a fixed index, one provides such a contract together with
proofs that the underlying constraints *imply* the spec under the assumptions (soundness
of the gadget) and that a satisfying witness *exists* under the assumptions (completeness).

This gives us a clean target for migrating Clean's `FormalCircuit` into ArkLib without a
Clean-specific protocol bridge.
-/

namespace ConstraintSystem

/-- A behavioural contract for a constraint system at a fixed index, consisting of an
`Assumptions` precondition on the in-the-clear statement and a `Spec` postcondition
relating statement and witness, together with soundness and completeness proofs tying the
contract to the underlying satisfiability relation. -/
structure BehavioralContract (C : ConstraintSystem.{u, v, w}) (i : C.Index) where
  /-- Precondition on the in-the-clear statement under which the contract applies. -/
  Assumptions : C.Stmt i → Prop
  /-- High-level specification relating the in-the-clear statement and the witness. -/
  Spec : C.Stmt i → C.Wit i → Prop
  /-- Soundness: if the assumptions hold and the underlying constraints are satisfied,
    the spec holds for the recovered witness. -/
  soundness : ∀ s o w, Assumptions s → C.satisfies i s o w → Spec s w
  /-- Completeness: if the assumptions hold, there exist oracle and witness data making
    the underlying constraints satisfied *and* the spec true. -/
  completeness : ∀ s, Assumptions s → ∃ o w, C.satisfies i s o w ∧ Spec s w

namespace BehavioralContract

variable {C : ConstraintSystem.{u, v, w}} {i : C.Index} (B : BehavioralContract C i)

/-- Under the assumptions, the constraint system is satisfiable at `i` for every statement.
This is the most immediately useful corollary of `completeness`. -/
theorem isSatisfiable_of_assumptions {s : C.Stmt i} (hs : B.Assumptions s) :
    C.IsSatisfiable i s := by
  obtain ⟨o, w, hsat, _⟩ := B.completeness s hs
  exact ⟨o, w, hsat⟩

end BehavioralContract

end ConstraintSystem
