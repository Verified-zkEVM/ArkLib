/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Oracle.Source

/-!
# Source-context acceptance clients

Ordinary-import canaries cover dependent responses, noncommuting answer transformations,
query/environment routing, observationally irrelevant backing data, and independent universes.
The numeric examples distinguish swapped composition order and constant or misrouted handlers.
-/

universe u v w u' v' w'

namespace Interaction.Oracle.SourceExample

/-- The two queries have genuinely different response types. -/
def dependent : SourceCtx Bool (Bool × Fin 3) where
  spec := fun | false => Bool | true => Fin 3
  impl := fun | false, env => env.1 | true, env => env.2

/-- Both dependent response branches affect the final scalar. -/
def observe : OracleComp dependent.spec Nat := do
  let bit : Bool ← liftM (dependent.spec.query false)
  let value : Fin 3 ← liftM (dependent.spec.query true)
  return if bit then value.val + 7 else value.val + 11

example : dependent.eval (true, ⟨2, by decide⟩) observe = 9 := rfl
example : dependent.eval (false, ⟨1, by decide⟩) observe = 12 := rfl

/-- A dependent response map acts differently on the two query branches. -/
def twist : SourceHom dependent dependent where
  route :=
    { toFunA := fun q => q
      toFunB := fun q => match q with
        | false => fun value => Bool.not (show Bool from value)
        | true => fun value => (show Fin 3 from value) + 1 }
  pullEnv := fun env => (!env.1, env.2 + 1)
  commutes := fun _ q => by cases q <;> rfl

/-- Both dependent backward maps are observable, including `Fin` wraparound. -/
example : twist.pull (dependent.handler (true, ⟨2, by decide⟩)) false = false ∧
    twist.pull (dependent.handler (true, ⟨2, by decide⟩)) true = (0 : Fin 3) := by
  constructor <;> rfl

/-- A private backing tag is not part of the oracle interface. -/
def tagged : SourceCtx Bool ((Bool × Fin 3) × Nat) :=
  dependent.comapEnv Prod.fst

example (env : Bool × Fin 3) (p : OracleComp tagged.spec Nat) :
    tagged.eval (env, 4) p = tagged.eval (env, 19) p :=
  tagged.eval_eq_of_handler_eq rfl p

example (env : Bool × Fin 3) : ((env, 4) : (Bool × Fin 3) × Nat) ≠ (env, 19) := by
  intro h
  have htag := congrArg Prod.snd h
  norm_num at htag

/-- A function-backed source distinguishing route and response-map composition. -/
def numbers := SourceCtx.ofSpec (Bool →ₒ Nat)

/-- Flip the primitive query and then add three to its answer. -/
def shift : SourceHom numbers numbers where
  route := ⟨Bool.not, fun _ (answer : Nat) => (answer + 3 : Nat)⟩
  pullEnv := fun (env : Bool → Nat) q => (env (!q) + 3 : Nat)
  commutes := fun _ _ => rfl

/-- Double an answer without changing its query. -/
def double : SourceHom numbers numbers where
  route := ⟨fun q => q, fun _ (answer : Nat) => (answer * 2 : Nat)⟩
  pullEnv := fun (env : Bool → Nat) q => (env q * 2 : Nat)
  commutes := fun _ _ => rfl

/-- Distinct primitive answers reject a route that always chooses one branch. -/
def answers : Bool → Nat := fun | false => 2 | true => 5

/-- Preserve both observations, in order, rather than a commutative aggregate. -/
def twoQueries : OracleComp numbers.spec (Nat × Nat) := do
  let a ← liftM (numbers.spec.query false)
  let b ← liftM (numbers.spec.query true)
  return (a, b)

example : numbers.eval answers ((double.comp shift).mapProgram twoQueries) = (13, 7) := rfl
example : numbers.eval answers ((shift.comp double).mapProgram twoQueries) = (16, 10) := rfl

/-- Sum weakening must choose the matching environment, not a same-typed sibling. -/
example : (numbers.sum numbers).eval (answers, fun _ => 29)
    ((SourceHom.inr numbers numbers).mapProgram twoQueries) = (29, 29) := rfl

example : (numbers.sum numbers).eval (answers, fun _ => 29)
    ((SourceHom.inl numbers numbers).mapProgram twoQueries) = (2, 5) := rfl

/-- Reindexing can explicitly give two names to the same primitive query. -/
example : (numbers.reindex (fun _ : Bool => true)).handler answers false = (5 : Nat) := rfl

/-- Tensor queries return both answers, not a sum response. -/
example : (dependent.tensor numbers).handler ((true, ⟨2, by decide⟩), answers)
    (true, false) = ((⟨2, by decide⟩ : Fin 3), (2 : Nat)) := rfl

/-- Family selection retains the index in the backing environment. -/
example : (SourceCtx.sigma (fun _ : Bool => numbers)).handler
    (fun | false => answers | true => fun _ => 29) ⟨true, false⟩ = (29 : Nat) := rfl

section Universes

variable {I : Type u} {E : Type w} {J : Type u'} {F : Type w'}

-- Elaboration contracts, not substitutes for the discriminating examples above.
example (S : SourceCtx.{u, v, w} I E) (T : SourceCtx.{u', v, w'} J F) :
    SourceCtx.{max u u', v, max w w'} (I ⊕ J) (E × F) := S.sum T

example (S : SourceCtx.{u, v, w} I E) (T : SourceCtx.{u', v', w'} J F) :
    SourceCtx.{max u u', max v v', max w w'} (I × J) (E × F) := S.tensor T

example (S : SourceCtx.{u, v, w} I E) : SourceCtx.{u, max v v', w} I E :=
  S.liftResponse

/-- Raw routing and its inverse allow genuinely different response universes. -/
example (S : SourceCtx.{u, v, w} I E) : SourceEquiv S (S.liftResponse.{u, v, w, v'}) :=
  SourceEquiv.liftResponse S

/-- The backward response map unwraps a concretely raised answer. -/
example : (SourceHom.toLiftResponse.{0, 0, 0, 2} numbers).pull
    ((numbers.liftResponse.{0, 0, 0, 2}).handler answers) true = (5 : Nat) := rfl

/-- The inverse response map rewraps a concrete answer. -/
example : ((SourceEquiv.liftResponse.{0, 0, 0, 2} numbers).invHom.pull
    (numbers.handler answers) true).down = (5 : Nat) := rfl

end Universes

end Interaction.Oracle.SourceExample
