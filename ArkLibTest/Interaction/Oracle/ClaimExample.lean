/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Interaction.Oracle.Claim

/-!
# Closed-claim acceptance clients

A relation with a claim-dependent witness observes only answers. Concrete realizations may carry
unobservable information, and two different query programs can produce the same relation input.
-/

namespace Interaction.Oracle.ClaimExample

/-- A concrete representation carries an unobservable Boolean tag. -/
def tagged : OracleFamily Unit (fun _ => Nat × Bool) where
  interface := fun _ =>
    { Query := Unit
      toOC := { spec := fun _ => Nat, impl := fun _ value => value.1 } }

/-- Only the natural-number answer is exposed. -/
def observed (c : ClosedClaim Nat tagged) : Prop := c.oracles ⟨(), ()⟩ = c.stmt

example : ConcreteClaim.toClosed (⟨7, fun _ => (7, true)⟩ : ConcreteClaim Nat tagged) =
    ConcreteClaim.toClosed (⟨7, fun _ => (7, false)⟩ : ConcreteClaim Nat tagged) := rfl

/-- A witness is bounded by the actual statement, so its type depends on the claim. -/
def answerProblem : Problem (ClaimFamily.closedOracle Unit (fun _ => Nat) (fun _ => tagged)) where
  Witness := fun _ claim => Fin (claim.stmt + 1)
  admissible := fun _ claim => observed claim
  rel := fun _ claim wit => observed claim ∧ wit.val = claim.stmt
  rel_admissible := fun _ _ _ h => h.1

example : answerProblem.language ()
    (ConcreteClaim.toClosed (⟨7, fun _ => (7, true)⟩ : ConcreteClaim Nat tagged)) :=
  ⟨⟨7, by decide⟩, rfl, rfl⟩

/-- An identity program and a program that queries twice have the same deterministic meaning. -/
def repeated : VirtualOracle tagged.spec tagged := .ofQuery (fun q => do
  let _ ← liftM (tagged.spec.query q)
  liftM (tagged.spec.query q))

example : VirtualOracle.SemEquiv (.id tagged) repeated := by
  intro impl
  funext q
  simp [repeated, VirtualOracle.ofQuery, VirtualOracle.eval, VirtualOracle.id,
    QueryImpl.compose, QueryImpl.id']
  rfl

example {I : Type} {spec : OracleSpec I} (view : VirtualOracle spec tagged)
    (impl : QueryImpl spec Id) :
    (OpenClaim.subst (⟨7, repeated⟩ : OpenClaim tagged.spec Nat tagged) view).closeWith impl =
      OpenClaim.closeWith (⟨7, repeated⟩ : OpenClaim tagged.spec Nat tagged) (view.eval impl) :=
  OpenClaim.closeWith_subst _ _ _

/-- The relation cannot distinguish different derivations with the same closed answers. -/
example {I : Type} {spec : OracleSpec I} (a b : OpenClaim spec Nat tagged)
    (hs : a.stmt = b.stmt) (ho : VirtualOracle.SemEquiv a.oracles b.oracles)
    (impl : QueryImpl spec Id) :
    answerProblem.language () (a.closeWith impl) ↔
      answerProblem.language () (b.closeWith impl) := by
  rw [OpenClaim.closeWith_congr hs ho impl]

end Interaction.Oracle.ClaimExample
