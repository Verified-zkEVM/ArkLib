/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.Oracle.ResourceOps

/-!
# Oracle families and oracle maps: dependent answers, routing and hidden data

Queries with different response types both affect a result. Answer-transforming oracle maps are
observable in both composition orders. Sum embeddings read the matching component, a constant
renaming gives two indices to one realization, a pair interface answers both of its queries, and
an unqueried coordinate of a realization is not observable.
-/

open Interaction.Core Interaction.Oracle OracleComp

namespace Interaction.Core.SourceExampleTests

universe u v w u' v' w'

/-- The carrier of the `false` index is `Bool`; the carrier of the `true` index is `Fin 3`. -/
abbrev Carrier : Bool → Type
  | false => Bool
  | true => Fin 3

/-- Each index reveals its whole realization. -/
@[instance_reducible] def dependent : OracleFamily Bool Carrier :=
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

-- SourceExample S1 (two examples), restated: the frozen `SourceCtx` with response types `Bool`
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

-- SourceExample S2, restated: the frozen `SourceHom` backward maps become an `OracleMap` whose
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
  toOC.spec := fun _ => Carrier b
  toOC.impl _ := do return (← read).1

/-- Realizations carry a private tag. -/
@[instance_reducible] def tagged : OracleFamily Bool (fun b => Carrier b × Nat) :=
  ⟨taggedInterface⟩

-- SourceExample S3, restated: the frozen `comapEnv Prod.fst` becomes realizations with an
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

/-- Two scalar slots, each revealing its value. -/
@[instance_reducible] def numbers : OracleFamily Bool (fun _ => Nat) :=
  ⟨fun _ => OracleInterface.instDefault⟩

/-- Read the other slot and add three. -/
def shift : OracleMap numbers numbers where
  f x q := x (!q) + 3
  impl q := do
    let a : Nat ← liftM (numbers.spec.query ⟨!q.1, ()⟩)
    pure (a + 3)
  law _ _ := rfl

/-- Double the answer of the same slot. -/
def double : OracleMap numbers numbers where
  f x q := x q * 2
  impl q := do
    let a : Nat ← liftM (numbers.spec.query ⟨q.1, ()⟩)
    pure (a * 2)
  law _ _ := rfl

/-- Distinct answers reject a route that always reads one slot. -/
def answers : ∀ _ : Bool, Nat
  | false => 2
  | true => 5

/-- Both observations, in order. -/
def twoQueries : OracleComp numbers.spec (Nat × Nat) := do
  let a : Nat ← liftM (numbers.spec.query ⟨false, ()⟩)
  let b : Nat ← liftM (numbers.spec.query ⟨true, ()⟩)
  return (a, b)

-- SourceExample S5 (two examples), restated: `SourceHom.comp` becomes `OracleMap.comp`, which
-- composes in function order (`g.comp h` applies `h` first), so the frozen
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

/-- A pair interface: one query selects a slot of each component and returns both answers. -/
@[reducible] def pairInterface : OracleInterface ((∀ b, Carrier b) × (∀ _ : Bool, Nat)) where
  Query := Bool × Bool
  toOC.spec := fun q => Carrier q.1 × Nat
  toOC.impl q := do
    let x ← read
    return (x.1 q.1, x.2 q.2)

/-- The resources whose data the pair interface packages. -/
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

/-- A family of function oracles indexed by a bit. -/
def functions : OracleFamily Bool (fun _ => Bool → Nat) :=
  ⟨fun _ => OracleInterface.instFunction⟩

-- SourceExample S9, restated: `SourceCtx.sigma` becomes a `Bool`-indexed family of function
-- oracles; the query `⟨true, false⟩` is answered by the data at index `true`. Not weaker.
example : functions.behaviorOfRealizations
    (fun | false => fun b => answers b | true => fun _ => 29) ⟨true, false⟩ = (29 : Nat) := rfl

section Universes

-- SourceExample S10: response universe v is shared, while query universes u and u' and data
-- universes w and w' are independent, exactly as for the disjoint sum of reader sources.
/-- Disjoint resources preserve the independent query and data universes of both sources. -/
example (S : Resources.{v, u, w}) (T : Resources.{v, u', w'}) :
    Resources.{v, max u u', max w w'} := S.sum T

/-- Disjoint queries retain their original index carriers. -/
example (S : Resources.{v, u, w}) (T : Resources.{v, u', w'}) :
    OracleSpec.{max u u', v} (S.Index ⊕ T.Index) := (S.sum T).spec

/-- Disjoint data remains a pair of the original carriers. -/
example (S : Resources.{v, u, w}) (T : Resources.{v, u', w'}) :
    (S.sum T).Data = (S.Data × T.Data) := rfl

/-- Each query is answered from its own component of the pair. -/
example (S : Resources.{v, u, w}) (T : Resources.{v, u', w'})
    (x : S.Data × T.Data) : (S.sum T).answer x = S.answer x.1 + T.answer x.2 := rfl

-- SourceExample S11: the two sources retain independent query, response and data universes.
/-- A paired query and answer resource has the maxima of the independent component universes. -/
example (S : Resources.{v, u, w}) (T : Resources.{v', u', w'}) :
    Resources.{max v v', max u u', max w w'} := S.tensor T

/-- Tensor queries use the exact product of the two original query carriers. -/
example (S : Resources.{v, u, w}) (T : Resources.{v', u', w'}) :
    OracleSpec.{max u u', max v v'} (S.Index × T.Index) := (S.tensor T).spec

/-- Tensor backing data remains the exact product of the two original data carriers. -/
example (S : Resources.{v, u, w}) (T : Resources.{v', u', w'}) :
    (S.tensor T).Data = (S.Data × T.Data) := rfl

-- SourceExample S12: lifting responses preserves the original query and backing-data universes.
/-- The response universe can be raised independently of the query and data universes. -/
example (S : Resources.{v, u, w}) : Resources.{max v v', u, w} :=
  S.liftResponse.{v, u, w, v'}

-- SourceExample S13: coherent raw maps are inverse even when response universes differ.
/-- Response lifting gives an equivalence of queries, responses and backing data. -/
example (S : Resources.{v, u, w}) : ResourceEquiv S (S.liftResponse.{v, u, w, v'}) :=
  ResourceEquiv.liftResponse S

/-- The forward route leaves each backing datum unchanged. -/
example (S : Resources.{v, u, w}) (data : S.Data) :
    (ResourceEquiv.liftResponse.{v, u, w, v'} S).toHom.pullData data = data := rfl

/-- The inverse route leaves each backing datum unchanged. -/
example (S : Resources.{v, u, w}) (data : S.Data) :
    (ResourceEquiv.liftResponse.{v, u, w, v'} S).invHom.pullData data = data := rfl

-- SourceExample S14: the concrete response universe is raised from 0 to 2, with no data change.
/-- Unwrapping the raised answer at index true recovers five. -/
example : (ResourceHom.toLiftResponse.{0, 0, 0, 2} (Resources.ofFamily numbers)).pull
    (((Resources.ofFamily numbers).liftResponse.{0, 0, 0, 2}).answer answers)
    ⟨true, ()⟩ = (5 : Nat) := rfl

-- SourceExample S15: the inverse raw route rewraps the same answer in response universe 2.
/-- Rewrapping the answer at index true has underlying value five. -/
example : ((ResourceEquiv.liftResponse.{0, 0, 0, 2} (Resources.ofFamily numbers)).invHom.pull
    (numbers.behaviorOfRealizations answers) ⟨true, ()⟩).down = (5 : Nat) := rfl

end Universes

end Interaction.Core.SourceExampleTests
