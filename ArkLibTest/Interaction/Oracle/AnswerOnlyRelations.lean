/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.OracleVerifier

/-!
# Relations over concrete oracle data that observe only answers

Concrete oracle data may carry unobservable information. A relation that reads only the behavior
of its data cannot see that information, and two oracle maps with the same answers give it the same
input. Oracle maps substitute: routing through a composite map and closing with a handler equals
closing the outer map with the evaluated inner map.
-/

open PFunctor Interaction Interaction.Oracle OracleComp

namespace Interaction.AnswerOnlyRelationsTests

/-- The interface answers the number and ignores the Boolean tag. -/
@[instance_reducible]
def taggedInterface : OracleInterface (Nat × Bool) :=
  { Query := Unit
    spec := fun _ => Nat
    answer := fun value _ => value.1 }

/-- The single oracle of the tagged bundle. -/
abbrev taggedSlot (_ : Unit) : OracleBundle := OracleBundle.of (Nat × Bool) taggedInterface

/-- A concrete representation carries an unobservable Boolean tag. -/
def tagged : OracleBundle := OracleBundle.indexed taggedSlot

-- ClaimExample 1, restated: the old-layer row compares two closed claims. A closed claim is a
-- statement with the behavior of the realizations: the unobservable tag vanishes.
example : ((7 : Nat), tagged.answer (fun _ => (7, true))) =
    ((7 : Nat), tagged.answer (fun _ => (7, false))) := rfl

/-- Claims are a statement with concrete data for the tagged bundle. -/
def claims : ClaimFamily Unit := ⟨fun _ => Nat × tagged.Data⟩

/-- The observable answer of a claim's data equals its statement. -/
def observed (c : Nat × tagged.Data) : Prop :=
  tagged.answer c.2 ⟨(), ()⟩ = c.1

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

/-- Closed claims: a statement with arbitrary deterministic answers for the tagged bundle, which
need not come from any realization. -/
def closedClaims : ClaimFamily Unit := ⟨fun _ => Nat × tagged.Behavior⟩

/-- The observable answer of a closed claim equals its statement. -/
def observedClosed (c : Nat × tagged.Behavior) : Prop := c.2 ⟨(), ()⟩ = c.1

/-- The same claim-dependent witness relation, over closed claims. -/
def closedProblem : Problem closedClaims where
  Witness := fun _ claim => Fin (claim.1 + 1)
  admissible := fun _ claim => observedClosed claim
  rel := fun _ claim wit => observedClosed claim ∧ wit.val = claim.1
  rel_admissible := fun _ _ _ h => h.1

-- The old-layer relation reads closed claims; on concrete data it is the relation above.
example (s : Nat) (x : tagged.Data) :
    answerProblem.language () (s, x) ↔
      closedProblem.language () (s, tagged.answer x) := Iff.rfl

-- ClaimExample 2, at the old-layer relation: the closed claim of statement 7 and tagged data
-- `(7, true)` is in the language.
example : closedProblem.language () (7, tagged.answer fun _ => (7, true)) :=
  ⟨⟨7, by decide⟩, rfl, rfl⟩

/-- Language membership depends on the data only through its behavior. -/
theorem language_congr (s : Nat) (x y : tagged.Data)
    (h : tagged.answer x = tagged.answer y) :
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
def identity : OracleMap tagged tagged := OracleMap.reindex taggedSlot id

-- ClaimExample 3, restated: the old-layer row states `SemEquiv (.id tagged) repeated`, equality
-- of the two programs' evaluations under every deterministic handler. The same equality holds here
-- for the query-twice map and the identity reindexing, under every handler, not only those
-- induced by data.
example (impl : QueryImpl tagged.spec Id) (q : tagged.spec.Domain) :
    simulateQ impl (repeated.impl q) = simulateQ impl (identity.impl q) := by
  simp only [repeated, identity, OracleMap.reindex, simulateQ_bind]
  rfl

-- Through the maps' laws, routing any program through either map agrees with answering from the
-- same materialized data.
example (x : tagged.Data) {α : Type} (program : OracleComp tagged.spec α) :
    simulateQ (tagged.answer x) (simulateQ repeated.impl program) =
      simulateQ (tagged.answer x) (simulateQ identity.impl program) :=
  (repeated.simulate_eq x program).trans (identity.simulate_eq x program).symm

-- ClaimExample 4, restated: the old-layer row closes a substituted open claim. Substitution is
-- `OracleMap.comp`. Under every deterministic handler of the inner inputs, the composite answers
-- as the outer program closed with the evaluated inner map. Its concrete data is the outer data
-- map applied to the inner data.
example {In : OracleBundle} (view : OracleMap In tagged)
    (impl : QueryImpl In.spec Id) (q : tagged.spec.Domain) :
    simulateQ impl ((repeated.comp view).impl q) =
      simulateQ (fun r => simulateQ impl (view.impl r)) (repeated.impl q) := by
  change simulateQ impl (simulateQ view.impl (repeated.impl q)) = _
  rw [← QueryImpl.simulateQ_compose]
  rfl

example {In : OracleBundle} (view : OracleMap In tagged)
    (x : In.Data) : (repeated.comp view).f x = repeated.f (view.f x) := rfl

-- ClaimExample 5, restated: the old-layer row shows that the relation cannot distinguish
-- derivations with equal statements and equal semantics. Take two maps whose simulated answers
-- agree on all input data. They give claims with the same language membership, because by their
-- laws the materialized outputs have the same behavior.
example {In : OracleBundle} (a b : OracleMap In tagged)
    (ho : ∀ x q, simulateQ (In.answer x) (a.impl q) =
      simulateQ (In.answer x) (b.impl q))
    (s : Nat) (x : In.Data) :
    answerProblem.language () (s, a.f x) ↔ answerProblem.language () (s, b.f x) := by
  exact language_congr s _ _ (funext fun q => (a.law x q).symm.trans ((ho x q).trans (b.law x q)))

-- ClaimExample 4, at full strength. Take an arbitrary source specification, an arbitrary virtual
-- program `view` for the tagged queries and an arbitrary deterministic source handler. Closing the
-- claim with substituted programs equals closing the original programs with the evaluated view.
example {I : Type} {spec : OracleSpec I} (view : QueryImpl tagged.spec (OracleComp spec))
    (impl : QueryImpl spec Id) :
    (((7 : Nat), QueryImpl.compose impl (QueryImpl.compose view repeated.impl)) :
        Nat × tagged.Behavior) =
      (7, QueryImpl.compose (QueryImpl.compose impl view) repeated.impl) := by
  congr 1
  funext q
  exact (QueryImpl.simulateQ_compose impl view (repeated.impl q)).symm

-- ClaimExample 5, at full strength. Take an arbitrary source specification and two claims made of
-- a statement and virtual programs, with equal statements and equal answers under every
-- deterministic source handler. Under any handler, they close to inputs with the same membership
-- in the old-layer closed-claim language.
example {I : Type} {spec : OracleSpec I} (a b : Nat × QueryImpl tagged.spec (OracleComp spec))
    (hs : a.1 = b.1)
    (ho : ∀ impl : QueryImpl spec Id, QueryImpl.compose impl a.2 = QueryImpl.compose impl b.2)
    (impl : QueryImpl spec Id) :
    closedProblem.language () (a.1, QueryImpl.compose impl a.2) ↔
      closedProblem.language () (b.1, QueryImpl.compose impl b.2) := by
  rw [hs, ho impl]

end Interaction.AnswerOnlyRelationsTests
