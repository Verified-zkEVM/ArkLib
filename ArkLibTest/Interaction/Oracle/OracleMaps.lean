/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.OracleVerifier
import ArkLib.Relation.OracleBundle

/-!
# Oracle families and oracle maps: dependent answers, routing and hidden data

Queries with different response types both affect a result. Answer-transforming oracle maps are
observable in both composition orders. Sum embeddings read the matching component, and a constant
renaming gives two indices to one realization. A pair interface answers both of its queries, and
an unqueried coordinate of a realization is not observable.
-/

open Interaction Interaction.Oracle OracleComp

namespace Interaction.OracleMapsTests


/-- The carrier of the `false` index is `Bool`; the carrier of the `true` index is `Fin 3`. -/
abbrev Carrier : Bool → Type
  | false => Bool
  | true => Fin 3

/-- Each index reveals its whole realization. -/
def dependent : OracleFamily Bool Carrier :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- Data for `dependent` from a bit and a `Fin 3` value. -/
def env (bit : Bool) (value : Fin 3) : ∀ b, Carrier b
  | false => bit
  | true => value

/-- Both dependent answers affect the final scalar. -/
def observe : OracleComp dependent.spec Nat := do
  let bit : Bool ← liftM (dependent.spec.query ⟨false, ()⟩)
  let value : Fin 3 ← liftM (dependent.spec.query ⟨true, ()⟩)
  return if bit then value.val + 7 else value.val + 11

-- SourceExample S1 (two examples), restated: the old-layer `SourceCtx` with response types `Bool`
-- and `Fin 3` becomes a `Bool`-indexed oracle family with those carriers, answered by
-- `behaviorOfRealizations`. Not weaker.
example : simulateQ (dependent.behaviorOfRealizations (env true 2)) observe = 9 := rfl
example : simulateQ (dependent.behaviorOfRealizations (env false 1)) observe = 12 := rfl

/-- Negate the bit and add one to the `Fin 3` value, in data and in query simulation. -/
def twist : OracleMap dependent dependent where
  f x
    | false => !(show Bool from x false)
    | true => (show Fin 3 from x true) + 1
  impl
    | ⟨false, _⟩ => do
      let bit : Bool ← liftM (dependent.spec.query ⟨false, ()⟩)
      pure (!bit)
    | ⟨true, _⟩ => do
      let value : Fin 3 ← liftM (dependent.spec.query ⟨true, ()⟩)
      pure (value + 1)
  law x q := by
    rcases q with ⟨_ | _, _⟩ <;> rfl

-- SourceExample S2, restated: the old-layer `SourceHom` backward maps become an `OracleMap` whose
-- `impl` transforms each answer and whose `f` transforms the data. Both the simulated answers and
-- the materialized data show `not` and the `Fin` wraparound `2 + 1 = 0`. Not weaker.
example : simulateQ (dependent.behaviorOfRealizations (env true 2)) (twist.impl ⟨false, ()⟩) =
      false ∧
    simulateQ (dependent.behaviorOfRealizations (env true 2)) (twist.impl ⟨true, ()⟩) =
      (0 : Fin 3) := by
  constructor <;> rfl

example : dependent.behaviorOfRealizations (twist.f (env true 2)) ⟨false, ()⟩ = false ∧
    dependent.behaviorOfRealizations (twist.f (env true 2)) ⟨true, ()⟩ = (0 : Fin 3) := by
  constructor <;> rfl

/-- Only the first coordinate of a tagged realization is queryable. -/
@[reducible] def taggedInterface (b : Bool) : OracleInterface (Carrier b × Nat) where
  Query := Unit
  spec := fun _ => Carrier b
  answer m _ := m.1

/-- Realizations carry a private tag. -/
def tagged : OracleFamily Bool (fun b => Carrier b × Nat) :=
  ⟨taggedInterface⟩

-- SourceExample S3, restated: the old-layer `comapEnv Prod.fst` becomes realizations with an
-- unqueried coordinate. For every program and every visible data, tags 4 and 19 give equal
-- answers. Not weaker.
example (x : ∀ b, Carrier b) {α : Type} (program : OracleComp tagged.spec α) :
    simulateQ (tagged.behaviorOfRealizations (fun b => (x b, 4))) program =
      simulateQ (tagged.behaviorOfRealizations (fun b => (x b, 19))) program := by
  congr 1

-- SourceExample S4: the two tagged realizations differ, so S3 is not vacuous.
example (x : ∀ b, Carrier b) :
    (fun b => (x b, 4) : ∀ b, Carrier b × Nat) ≠ (fun b => (x b, 19)) := by
  intro h
  have htag := congrArg (fun y => (y false).2) h
  norm_num at htag

/-- Two scalar oracles, each revealing its value. -/
def numbers : OracleFamily Bool (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- Read the other oracle and add three. -/
def shift : OracleMap numbers numbers where
  f x q := x (!q) + 3
  impl q := do
    let a : Nat ← liftM (numbers.spec.query ⟨!q.1, ()⟩)
    pure (a + 3)
  law _ _ := rfl

/-- Double the answer of the same oracle. -/
def double : OracleMap numbers numbers where
  f x q := x q * 2
  impl q := do
    let a : Nat ← liftM (numbers.spec.query ⟨q.1, ()⟩)
    pure (a * 2)
  law _ _ := rfl

/-- Distinct answers reject a route that always reads one oracle. -/
def answers : ∀ _ : Bool, Nat
  | false => 2
  | true => 5

/-- Both answers, in order. -/
def twoQueries : OracleComp numbers.spec (Nat × Nat) := do
  let a : Nat ← liftM (numbers.spec.query ⟨false, ()⟩)
  let b : Nat ← liftM (numbers.spec.query ⟨true, ()⟩)
  return (a, b)

-- SourceExample S5 (two examples), restated: `SourceHom.comp` becomes `OracleMap.comp`, which
-- composes in function order (`g.comp h` applies `h` first), so the old-layer
-- `double.comp shift` is `shift.comp double` here. Both orders are checked through the composed
-- `impl`, and the composed data agrees. Not weaker.
example : simulateQ (numbers.behaviorOfRealizations answers)
    (simulateQ (shift.comp double).impl twoQueries) = (13, 7) := rfl
example : simulateQ (numbers.behaviorOfRealizations answers)
    (simulateQ (double.comp shift).impl twoQueries) = (16, 10) := rfl
example : simulateQ (numbers.behaviorOfRealizations ((shift.comp double).f answers))
    twoQueries = (13, 7) :=
  (OracleMap.simulate_eq (shift.comp double) answers twoQueries).symm.trans rfl

/-- Data for two copies of `numbers`: the left copy holds `answers`, the right copy holds 29. -/
def pairData : ∀ k, (sumFamily numbers numbers).Realization k :=
  sumData answers (fun _ => 29)

-- SourceExample S6 (two examples), restated: `SourceHom.inl`/`inr` become the embeddings of
-- `sumFamily numbers numbers` along `Sum.inl`/`Sum.inr`. Each reads its own copy. Not weaker.
example : simulateQ ((sumFamily numbers numbers).behaviorOfRealizations pairData)
    (simulateQ (OracleMap.embedding (sumFamily numbers numbers) Sum.inr).impl
      (show OracleComp ((sumFamily numbers numbers).reindex Sum.inr).spec (Nat × Nat) from
        twoQueries)) = (29, 29) := rfl
example : simulateQ ((sumFamily numbers numbers).behaviorOfRealizations pairData)
    (simulateQ (OracleMap.embedding (sumFamily numbers numbers) Sum.inl).impl
      (show OracleComp ((sumFamily numbers numbers).reindex Sum.inl).spec (Nat × Nat) from
        twoQueries)) = (2, 5) := rfl

-- SourceExample S7, restated: `SourceCtx.reindex` becomes the embedding along a constant
-- renaming; output index `false` reads input index `true`. Not weaker.
example : simulateQ (numbers.behaviorOfRealizations answers)
    ((OracleMap.embedding numbers (fun _ : Bool => true)).impl ⟨false, ()⟩) = (5 : Nat) := rfl

/-- A pair interface: one query selects an oracle of each component and returns both answers. -/
@[reducible] def pairInterface : OracleInterface ((∀ b, Carrier b) × (∀ _ : Bool, Nat)) where
  Query := Bool × Bool
  spec := fun q => Carrier q.1 × Nat
  answer x q := (x.1 q.1, x.2 q.2)

/-- The bundle whose data the pair interface packages. -/
abbrev both := sumFamily dependent numbers

/-- Query both components and return both answers. -/
def tensor : OracleMap both (singletonFamily pairInterface) where
  f x _ := (fun b => x (.inl b), fun b => x (.inr b))
  impl q := do
    let u : Carrier q.2.1 ← liftM (both.spec.query ⟨.inl q.2.1, ()⟩)
    let v : Nat ← liftM (both.spec.query ⟨.inr q.2.2, ()⟩)
    pure (u, v)
  law _ _ := rfl

-- SourceExample S8, restated: `SourceCtx.tensor` becomes an oracle map into a pair interface whose
-- implementation queries both components. The answer is a pair, not a sum. Not weaker.
example : simulateQ (both.behaviorOfRealizations (sumData (env true 2) answers))
    (tensor.impl ⟨⟨⟩, (true, false)⟩) = ((2 : Fin 3), (2 : Nat)) := rfl

-- SourceExample S8, through the library tensor: `OracleBundle.tensor` answers the same paired
-- query on the same data with the same pair.
example : ((OracleBundle.ofFamily dependent).tensor (OracleBundle.ofFamily numbers)).answer
    (env true 2, answers) (⟨true, ()⟩, ⟨false, ()⟩) = ((2 : Fin 3), (2 : Nat)) := rfl

/-- A family of function oracles indexed by a bit. -/
def functions : OracleFamily Bool (fun _ => Bool → Nat) :=
  ⟨fun _ => OracleInterface.instFunction⟩

-- SourceExample S9, restated: `SourceCtx.sigma` becomes a `Bool`-indexed family of function
-- oracles; the query `⟨true, false⟩` is answered by the data at index `true`. Not weaker.
example : functions.behaviorOfRealizations
    (fun | false => fun b => answers b | true => fun _ => 29) ⟨true, false⟩ = (29 : Nat) := rfl

section Universes

-- SourceExample S10: disjoint sums retain their component carriers at `Type`.
/-- The sum of two bundles preserves both query and data carriers. -/
example (S : OracleBundle) (T : OracleBundle) :
    OracleBundle := S.sum T

/-- Disjoint queries keep their original index carriers. -/
example (S : OracleBundle) (T : OracleBundle) :
    OracleSpec.{0, 0} (S.Query ⊕ T.Query) := (S.sum T).spec

/-- Disjoint data remains a pair of the original carriers. -/
example (S : OracleBundle) (T : OracleBundle) :
    (S.sum T).Data = (S.Data × T.Data) := rfl

/-- Each query is answered from its own component of the pair. -/
example (S : OracleBundle) (T : OracleBundle)
    (x : S.Data × T.Data) : (S.sum T).answer x = S.answer x.1 + T.answer x.2 := rfl

-- SourceExample S11: paired queries and data at `Type`.
/-- A paired query and answer bundle also lies in `Type 1`. -/
example (S : OracleBundle) (T : OracleBundle) :
    OracleBundle := S.tensor T

/-- Tensor queries use the exact product of the two original query carriers. -/
example (S : OracleBundle) (T : OracleBundle) :
    OracleSpec.{0, 0} (S.Query × T.Query) := (S.tensor T).spec

/-- Tensor backing data remains the exact product of the two original data carriers. -/
example (S : OracleBundle) (T : OracleBundle) :
    (S.tensor T).Data = (S.Data × T.Data) := rfl

end Universes

end Interaction.OracleMapsTests
