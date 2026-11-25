/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VCVio.OracleComp.OracleComp
import Mathlib.Algebra.Field.TransferInstance
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.ZMod.Basic

/-!
# Universe policy: experiments and workarounds

Companion to `docs/design/interaction-layer/universe-policy.md`. Part 1 reproduces the three
failures of undetermined universes. Part 2 is a small model of the protocol tree that shows what
the policy rules out and the workaround for each case. `#guard_msgs` records each expected error.
Check with `lake env lean` from a built ArkLib worktree.
-/

set_option linter.dupNamespace false

universe u v w

/-! ## Part 1. Failures of undetermined universes -/

open OracleSpec OracleComp

section Failures
set_option pp.universes true


section X1
def zeroComp := (pure 3 : OracleComp []ₒ Nat)
/--
info: zeroComp.{u_1, u_2} : OracleComp.{u_1, u_2, 0} emptySpec.{u_1, u_2} ℕ
-/
#guard_msgs in
#check @zeroComp
-- The lemma names the constant's universes in the other order.
theorem zeroComp_eq : zeroComp = (pure 3 : OracleComp []ₒ Nat) := rfl
/--
info: zeroComp_eq.{u_1, u_2} : Eq.{max (u_1 + 1) (u_2 + 1)} zeroComp.{u_2, u_1} (pure.{0, max u_1 u_2} 3)
-/
#guard_msgs in
#check @zeroComp_eq
end X1

section X2
def HasWitness.{k} (S : Type) (R : S → Prop) : Prop :=
  ∃ (K : S → Type k) (_ : ∀ s, K s → R s), ∀ s, R s → Nonempty (K s)
/--
info: HasWitness.{u_1} : (S : Type) → (S → Prop) → Prop
-/
#guard_msgs in
#check @HasWitness
/--
error: Type mismatch
  h
has type
  HasWitness.{u_1} S R
but is expected to have type
  HasWitness.{u_2} S R
-/
#guard_msgs in
theorem use (S : Type) (R : S → Prop) (h : HasWitness S R) : HasWitness S R := h
/--
info: use.{u_1, u_2} : ∀ (S : Type) (R : S → Prop), HasWitness.{u_1} S R → HasWitness.{u_2} S R
-/
#guard_msgs in
#check @use
-- Hypothesis at one universe, goal at another: needs a lift lemma.
/--
error: Type mismatch
  h
has type
  HasWitness.{0} S R
but is expected to have type
  HasWitness.{1} S R
-/
#guard_msgs in
example (S : Type) (R : S → Prop) (h : HasWitness.{0} S R) : HasWitness.{1} S R := h
end X2

section X3
def Runner (m : Type u → Type u) : Type u := m PUnit.{u+1}
def r1 {ι : Type v} (spec : OracleSpec.{v, u} ι) := Runner (OracleComp spec)
/--
info: @r1.{u_1, u_2, u_3} : {ι : Type u_2} → OracleSpec.{u_2, u_1} ι → Type (max (max u_3 u_1) u_2)
-/
#guard_msgs in
#check @r1
/--
error: failed to solve universe constraint
  u =?= max u v
while trying to unify
  Type u → Type u : Type (u + 1)
with
  Type u → Type (max v u) : Type (max (u + 1) (v + 1))
-/
#guard_msgs in
def r2 {ι : Type v} (spec : OracleSpec.{v, u} ι) := Runner.{u} (OracleComp spec)
end X3

end Failures

/-! ## Part 2. A model of the protocol tree -/


/-! ## Option C: a toy protocol tree with data in `Type` -/
namespace OptC

/-- A protocol: each node names the type of the next move. It contains types, so `Type 1`. -/
inductive Proto : Type 1 where
  | done
  | msg (X : Type) (next : X → Proto)      -- prover sends `x : X`; `x` picks the rest
  | chal (C : Type) (next : C → Proto)     -- verifier samples `c : C`

/-- A transcript holds data only, so it lives in `Type`. -/
def Transcript : Proto → Type
  | .done => Unit
  | .msg X next => (x : X) × Transcript (next x)
  | .chal C next => (c : C) × Transcript (next c)

/-- A two-move protocol over `ZMod 7`. -/
def example1 : Proto := .msg (ZMod 7) fun _ => .chal (ZMod 7) fun _ => .done

end OptC

/-! ## Option B: the same tree with one universe parameter `u` -/
namespace OptB

inductive Proto : Type (u + 1) where
  | done
  | msg (X : Type u) (next : X → Proto)
  | chal (C : Type u) (next : C → Proto)

def Transcript : Proto.{u} → Type u
  | .done => PUnit
  | .msg X next => (x : X) × Transcript (next x)
  | .chal C next => (c : C) × Transcript (next c)

/-- At `u = 0`, option B is option C. -/
def example1 : Proto.{0} := .msg (ZMod 7) fun _ => .chal (ZMod 7) fun _ => .done

/-- What B adds: at `u = 1` the prover can send a *type*. -/
def sendsAType : Proto.{1} := .msg Type fun α => .msg (ULift α) fun _ => .done

end OptB

/-! ## Loss 1: a move that is itself a type. In C this fails. -/
namespace OptC
/--
error: Application type mismatch: The argument
  Type
has type
  Type 1
of sort `Type 2` but is expected to have type
  Type
of sort `Type 1` in the application
  Proto.msg Type
-/
#guard_msgs in
def sendsAType : Proto := .msg Type fun α => .msg α fun _ => .done
end OptC

/-! ## Workaround 1: send a *name* for the type, and decode it. -/
namespace OptC

/-- The finitely many groups the prover may choose between. -/
inductive GroupCode
  | small | large

/-- What each name means. -/
def GroupCode.El : GroupCode → Type
  | .small => ZMod 7
  | .large => ZMod 101

/-- The prover names a group, then sends an element of that group. -/
def sendsACode : Proto := .msg GroupCode fun g => .msg g.El fun _ => .done

/-- The same idea for an unbounded family: send a size, then a vector of that size. -/
def sendsASize : Proto := .msg ℕ fun n => .msg (Fin n → ZMod 7) fun _ => .done

end OptC

/-! ## Not a loss: choosing the next sub-protocol at run time. -/
namespace OptC
def choosesSubprotocol (p q : Proto) : Proto := .msg Bool fun b => if b then p else q
end OptC

/-! ## Loss 2: a statement that contains types (a bundled relation). -/
namespace OptC

/-- A relation bundled with its statement and witness types: it contains types, so `Type 1`. -/
structure Rel : Type 1 where
  Stmt : Type
  Wit : Type
  holds : Stmt → Wit → Prop

/-- Security definitions take statements in `Type`. -/
def SoundFor (Stmt : Type) (lang : Set Stmt) : Prop := lang = lang

/-- A "universal" statement: a relation *and* an instance of it. Lives in `Type 1`. -/
abbrev UniversalStmt := (R : Rel) × R.Stmt

-- Fails: `UniversalStmt : Type 1`, but statements are in `Type`.
/--
error: Application type mismatch: The argument
  UniversalStmt
has type
  Type 1
of sort `Type 2` but is expected to have type
  Type
of sort `Type 1` in the application
  SoundFor UniversalStmt
-/
#guard_msgs in
example (lang : Set UniversalStmt) : Prop := SoundFor UniversalStmt lang

/-- Workaround 2a: make the relation a *parameter*. One protocol per relation, all in `Type`. -/
example (R : Rel) (lang : Set R.Stmt) : Prop := SoundFor R.Stmt lang

/-- Workaround 2b: if the verifier must receive the relation at run time, send it as *data*:
a circuit over a field, not a Lean type. -/
structure R1CS (F : Type) where
  rows : ℕ
  cols : ℕ
  A : Fin rows → Fin cols → F
  B : Fin rows → Fin cols → F
  C : Fin rows → Fin cols → F

abbrev UniversalR1CSStmt (F : Type) := (r : R1CS F) × (Fin r.cols → F)
example (F : Type) (lang : Set (UniversalR1CSStmt F)) : Prop := SoundFor _ lang

end OptC

/-! ## Loss 3: a carrier in a higher universe. -/
namespace OptC

/-- Protocol theorems in C take the field in `Type`. -/
def protocolOver (F : Type) [Field F] : Proto := .msg F fun _ => .done

-- Fails for a field in `Type 1`.
/--
error: Application type mismatch: The argument
  F
has type
  Type 1
of sort `Type 2` but is expected to have type
  Type
of sort `Type 1` in the application
  @protocolOver F
-/
#guard_msgs in
example (F : Type 1) [Field F] : Proto := protocolOver F

/-- Workaround 3: a finite field in any universe has an isomorphic copy in `Type`. -/
noncomputable def smallCopy (F : Type u) [Field F] [Fintype F] :
    (K : Type) × Field K × (F ≃ K) :=
  let e := Fintype.equivFin F
  ⟨Fin (Fintype.card F), e.symm.field, e⟩

noncomputable example (F : Type 1) [Field F] [Fintype F] : Proto :=
  let ⟨K, _, _⟩ := smallCopy F
  protocolOver K

end OptC

/-! ## Why B does not serve quantum provers, and C does -/
namespace OptC

/-- Adversaries for statements `S`, observed through `Obs`. Only `Adv` has a universe parameter,
and the model argument fixes it. (The real `outcome` is a measure; a function keeps this short.) -/
structure AdversaryModel (S Obs : Type) where
  Adv : S → Type w
  outcome : (s : S) → Adv s → Obs

/-- A stand-in for `QReg`: a register carries its carrier type, so it lives in `Type 1`. -/
structure QReg : Type 1 where
  carrier : Type

/-- A classical model: adversaries are functions, in `Type`. -/
def classical (S Obs : Type) : AdversaryModel.{0} S Obs where
  Adv _ := Unit → Obs
  outcome _ f := f ()

/-- A quantum-style model: an adversary holds a register, so it lives in `Type 1`.
The protocol, statements and observations stay in `Type`. -/
def quantum (S Obs : Type) : AdversaryModel.{1} S Obs where
  Adv _ := (r : QReg) × (r.carrier → Obs) × r.carrier
  outcome _ a := a.2.1 a.2.2

/-- Security definitions mention `M` and never write `w`. -/
def secure {S Obs : Type} (M : AdversaryModel.{w} S Obs) (good : Obs → Prop) : Prop :=
  ∀ s (a : M.Adv s), good (M.outcome s a)

example (S Obs : Type) (good : Obs → Prop) : Prop := secure (quantum S Obs) good

end OptC

namespace OptB
/-- In B, to put a `QReg`-holding prover *inside* the protocol's universe, the whole protocol
moves to `u = 1`, and every classical message must be lifted. -/
def liftedExample : Proto.{1} := .msg (ULift (ZMod 7)) fun _ => .chal (ULift (ZMod 7)) fun _ => .done
end OptB
