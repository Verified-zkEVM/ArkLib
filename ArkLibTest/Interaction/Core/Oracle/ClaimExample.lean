/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Core.OracleVerifier

/-!
# Relations over concrete oracle data that observe only answers

Concrete oracle data may carry unobservable information. A relation that reads only the behavior
of its data cannot see that information, and two oracle maps with the same answers give it the same
input. Oracle maps substitute: routing through a composite map and closing with a handler equals
closing the outer map with the evaluated inner map.
-/

open PFunctor Interaction.Core Interaction.Oracle OracleComp

namespace Interaction.Core.ClaimExampleTests

/-- A concrete representation carries an unobservable Boolean tag. -/
@[instance_reducible] def tagged : OracleFamily Unit (fun _ => Nat × Bool) where
  interface := fun _ =>
    { Query := Unit
      toOC := { spec := fun _ => Nat, impl := fun _ value => value.1 } }

-- ClaimExample 1, restated: the frozen row compares two closed claims. Claims are concrete data,
-- so the restated row compares the behavior of the two realizations: the unobservable tag
-- vanishes.
example : tagged.behaviorOfRealizations (fun _ => (7, true)) =
    tagged.behaviorOfRealizations (fun _ => (7, false)) := rfl

/-- Claims are a statement with concrete data for the tagged family. -/
def claims : ClaimFamily Unit := ⟨fun _ => Nat × (∀ i, tagged.Realization i)⟩

/-- The observable answer of a claim's data equals its statement. -/
def observed (c : Nat × (∀ i, tagged.Realization i)) : Prop :=
  tagged.behaviorOfRealizations c.2 ⟨(), ()⟩ = c.1

/-- A witness is bounded by the actual statement, so its type depends on the claim. The relation
reads the data only through its behavior. -/
def answerProblem : Problem claims where
  Witness := fun _ claim => Fin (claim.1 + 1)
  admissible := fun _ claim => observed claim
  rel := fun _ claim wit => observed claim ∧ wit.val = claim.1
  rel_admissible := fun _ _ _ h => h.1

-- ClaimExample 2, restated: the claim-dependent witness relation holds on the concrete claim
-- with statement 7 and tagged data `(7, true)`.
example : answerProblem.language () (7, fun _ => (7, true)) :=
  ⟨⟨7, by decide⟩, rfl, rfl⟩

/-- Language membership depends on the data only through its behavior. -/
theorem language_congr (s : Nat) (x y : ∀ i, tagged.Realization i)
    (h : tagged.behaviorOfRealizations x = tagged.behaviorOfRealizations y) :
    answerProblem.language () (s, x) ↔ answerProblem.language () (s, y) := by
  simp only [Problem.language, answerProblem, observed, h]

/-- A program that queries twice answers as the identity. -/
def repeated : OracleMap tagged tagged where
  f := id
  impl q := do
    let _ ← liftM (tagged.spec.query q)
    liftM (tagged.spec.query q)
  law x q := by
    simp only [simulateQ_bind]
    rfl

/-- The identity oracle map. -/
def identity : OracleMap tagged tagged := OracleMap.embedding tagged id

-- ClaimExample 3, restated: the frozen row states `SemEquiv (.id tagged) repeated`, equality of
-- the two programs' evaluations under every deterministic handler. The same equality holds here
-- for the query-twice map and the identity embedding, under every handler, not only those
-- induced by data.
example (impl : QueryImpl tagged.spec Id) (q : tagged.spec.Domain) :
    simulateQ impl (repeated.impl q) = simulateQ impl (identity.impl q) := by
  simp only [repeated, identity, OracleMap.embedding, simulateQ_bind]
  rfl

-- Through the maps' laws, routing any program through either map agrees with answering from the
-- same materialized data.
example (x : ∀ i, tagged.Realization i) {α : Type} (program : OracleComp tagged.spec α) :
    simulateQ (tagged.behaviorOfRealizations x) (simulateQ repeated.impl program) =
      simulateQ (tagged.behaviorOfRealizations x) (simulateQ identity.impl program) := by
  rw [OracleMap.simulate_eq, OracleMap.simulate_eq]
  rfl

-- ClaimExample 4, restated: the frozen row closes a substituted open claim. Substitution is
-- `OracleMap.comp`: under every deterministic handler of the inner inputs, the composite answers
-- as the outer program closed with the evaluated inner map, and its concrete data is the outer
-- data map applied to the inner data.
example {I : Type} {A : I → Type} {In : OracleFamily I A} (view : OracleMap In tagged)
    (impl : QueryImpl In.spec Id) (q : tagged.spec.Domain) :
    simulateQ impl ((repeated.comp view).impl q) =
      simulateQ (fun r => simulateQ impl (view.impl r)) (repeated.impl q) := by
  change simulateQ impl (simulateQ view.impl (repeated.impl q)) = _
  rw [← QueryImpl.simulateQ_compose]
  rfl

example {I : Type} {A : I → Type} {In : OracleFamily I A} (view : OracleMap In tagged)
    (x : ∀ i, A i) : (repeated.comp view).f x = repeated.f (view.f x) := rfl

-- ClaimExample 5, restated: the frozen row shows that the relation cannot distinguish derivations
-- with equal statements and equal semantics. Two maps whose simulated answers agree on all input
-- data give claims with the same language membership, because by their laws the materialized
-- outputs have the same behavior.
example {I : Type} {A : I → Type} {In : OracleFamily I A} (a b : OracleMap In tagged)
    (ho : ∀ x q, simulateQ (In.behaviorOfRealizations x) (a.impl q) =
      simulateQ (In.behaviorOfRealizations x) (b.impl q))
    (s : Nat) (x : ∀ i, A i) :
    answerProblem.language () (s, a.f x) ↔ answerProblem.language () (s, b.f x) := by
  refine language_congr s _ _ (funext fun q => ?_)
  rw [← a.law, ← b.law, ho]

end Interaction.Core.ClaimExampleTests
