/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vuk Dolijanovic, Claude(Anthropic)
-/

import Mathlib.Data.Fin.Basic
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Basic -- for the `Fintype`/`DecidableEq` instances on `Index k`

/-!
# Layered arithmetic circuits

The combinatorial substrate for the GKR protocol: no polynomials, no protocols, just circuits.

A `Circuit k d` is `d` layers deep with `2 ^ k` gates per layer, gates indexed by
`Index k = Fin k → Bool`. Each gate at layer `l` adds or multiplies two gates at layer `l + 1`.

* `evalLayer` / `evalCircuit` / `layerValues` — evaluation, one layer, all of it, and layer by
  layer respectively.
* `layerValues_castSucc` — the recurrence relating consecutive layers of `layerValues`.
* `addPred` / `mulPred` — the wiring predicates, `1` exactly when `z` is an add (resp. mul) gate
  with inputs `x` and `y`. These describe the circuit's shape and are public.

Multilinear extensions of the wiring predicates, and everything protocol-related, live in
`ArkLib/ProofSystem/GKR/SingleRound.lean`.
-/

namespace GKR

abbrev Index (k : ℕ) := Fin k → Bool

/--
A gate in a layered circuit

k is the width of the layer below (layer below has 2 ^ k gates)
-/
inductive Gate (k : ℕ) where
  | add : Index k → Index k → Gate k
  | mul : Index k → Index k → Gate k
/--
The whole circuit where 2 ^ k is the number of nodes in each layer

d is the depth of the circuit
-/
structure Circuit (k : ℕ) (d : ℕ) where
  gate : Fin d → Index k → Gate k

/--
Peel the layer of a circuit
-/
def Circuit.tail
 {k : ℕ}
 {d : ℕ}
 (c : Circuit k (d + 1)) : Circuit k d where
  gate := fun i z => c.gate i.succ z -- i.succ takes in Fin n and returns Fin n + 1

/--
Evaluate one layer of an arithmetic circuit
-/
def evalLayer
 {k : ℕ}
 {F : Type} [CommSemiring F]
 (thisLayer : Index k → Gate k)
 (lowerLayer : Index k -> F)
 : Index k → F :=
 fun z =>
  match thisLayer z with
  | Gate.add a b => lowerLayer a + lowerLayer b
  | Gate.mul a b => lowerLayer a * lowerLayer b

/--
Evaluate the whole arithmetic circuit
-/
def evalCircuit
  {k : ℕ}
  {d : ℕ}
  {F : Type} [CommSemiring F]
  (c : Circuit k d)
  (input : Index k → F)
  : Index k → F :=
  match d , c with
  | 0, _ => input
  | (_ + 1), c => evalLayer (c.gate 0) (evalCircuit c.tail input)

/--
get a value at every layer
-/
def layerValues
  {k : ℕ}
  {d : ℕ}
  {F : Type} [CommSemiring F]
  (c : Circuit k d)
  (input : Index k → F)
  : (Fin (d + 1)) → (Index k) → F :=
  match d, c with
  | 0, _ => fun _ => input
  | _ + 1, c =>
    let below := layerValues c.tail input
    Fin.cons (evalLayer (c.gate 0) (below 0)) below

/--
Layer `l`'s values are what layer `l`'s gates compute from layer `l+1`'s values.
Morally the definition of `layerValues`, but that definition recurses with `Fin.cons` and
`Circuit.tail`, so extracting it in this form takes an induction on depth.
-/
theorem layerValues_castSucc
  {k d : ℕ}
  {F : Type} [CommSemiring F]
  (c : Circuit k d) (input : Index k → F) (l : Fin d) :
    layerValues c input l.castSucc = evalLayer (c.gate l) (layerValues c input l.succ) := by
  induction d with
  | zero => exact absurd l.2 (by omega)
  | succ m ih =>
    refine Fin.cases ?_ ?_ l
    · rfl
    · intro i
      exact ih c.tail i

/--
layer 0 is the output of the circuit
-/
theorem layerValues_zero
  {k d : ℕ}
  {F : Type} [CommSemiring F]
  (c : Circuit k d) (input : Index k → F) :
    layerValues c input 0 = evalCircuit c input := by
  induction d with
  | zero => rfl
  | succ m ih => exact congrArg (evalLayer (c.gate 0)) (ih c.tail)

/--
the last layer is the input
-/
theorem layerValues_last
  {k d : ℕ}
  {F : Type} [CommSemiring F]
  (c : Circuit k d) (input : Index k → F) :
    layerValues c input (Fin.last d) = input := by
  induction d with
  | zero => rfl
  | succ m ih =>
    rw [← Fin.succ_last]
    exact ih c.tail

/--
add predicate
at level l, we have a gate z and at level l + 1 we have gates x and y
we return wether z is an add gate
-/
def addPred
  {k d : ℕ}
  (F : Type) [CommSemiring F]
  (c : Circuit k d)
  (l : Fin (d))
  (z x y : Index k) : F :=
  match c.gate l z with
  | Gate.add a b => if a = x ∧ b = y then 1 else 0
  | Gate.mul _ _ => 0

/--
mul predicate
at level l, we have a gate z and at level l + 1 we have gates x and y
we return wether z is a mul gate
-/
def mulPred
  {k d : ℕ}
  (F : Type) [CommSemiring F]
  (c : Circuit k d)
  (l : Fin (d))
  (z x y : Index k) : F :=
  match c.gate l z with
  | Gate.mul a b => if a = x ∧ b = y then 1 else 0
  | Gate.add _ _ => 0

end GKR
