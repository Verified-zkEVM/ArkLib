/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.OracleReduction.OracleInterface

/-!
# Claims and relations

This file defines indexed claims, witness relations with an explicit admissibility boundary,
and families of concrete oracle data with their observable interfaces. None depends on a
protocol tree or an execution strategy.
-/

@[expose] public section

universe u v w u'

namespace Interaction.Oracle

/-- An indexed family of realization types with explicitly selected oracle interfaces. -/
structure OracleFamily (Index : Type u) (Realization : Index → Type v) where
  /-- Observable interface, supplied as data rather than inferred. -/
  interface : ∀ i, OracleInterface.{v, w} (Realization i)

namespace OracleFamily

variable {I : Type u} {Data : I → Type v}

/-- Index carrier of the interface family. -/
abbrev Index (_ : OracleFamily.{u, v, w} I Data) := I

/-- The admissible realization type at each index. -/
abbrev Realization (O : OracleFamily.{u, v, w} I Data) : O.Index → Type v := Data

/-- The dependent query signature of the explicit interfaces. -/
abbrev spec (O : OracleFamily.{u, v, w} I Data) := [O.Realization]ₒ' O.interface

/-- Arbitrary deterministic answers, without a representability assumption. -/
abbrev Behavior (O : OracleFamily.{u, v, w} I Data) := QueryImpl O.spec Id

/-- Interpret a family of admissible realizations through its declared interfaces. -/
def behaviorOfRealizations (O : OracleFamily.{u, v, w} I Data)
    (data : ∀ i, O.Realization i) : O.Behavior :=
  fun q => (O.interface q.1).answer (data q.1) q.2

/-- Pull back the indexed interface family along an arbitrary map.

Repeated indices copy interface types; they do not force independently supplied realizations or
behaviors to agree. Use a named-context view when aliases must share a realization. -/
def reindex (O : OracleFamily.{u, v, w} I Data) {J : Type u'} (f : J → O.Index) :
    OracleFamily J (O.Realization ∘ f) := ⟨fun j => O.interface (f j)⟩

end OracleFamily

/-- Public contexts and the claim type visible in each context. -/
structure ClaimFamily (PublicCtx : Type u) where
  /-- Claims indexed by the public context. -/
  Claim : PublicCtx → Type v

/-- A claim-dependent witness relation with an explicit admissibility boundary. -/
structure Problem {PublicCtx : Type u} (S : ClaimFamily.{u, v} PublicCtx) where
  /-- Witnesses can depend on both context and claim. -/
  Witness : ∀ ctx, S.Claim ctx → Type w
  /-- Claim-level promises and well-formedness. -/
  admissible : ∀ ctx, S.Claim ctx → Prop
  /-- The relation observes only the declared claim. -/
  rel : ∀ ctx claim, Witness ctx claim → Prop
  /-- Every related claim satisfies the declared promise. -/
  rel_admissible : ∀ ctx claim wit, rel ctx claim wit → admissible ctx claim

/-- Membership means existence of a related witness. -/
def Problem.language {PublicCtx : Type u} {S : ClaimFamily.{u, v} PublicCtx}
    (P : Problem.{u, v, w} S)
    (ctx : PublicCtx) (claim : S.Claim ctx) : Prop := ∃ wit, P.rel ctx claim wit

/-- Language membership entails the claim's admissibility. -/
theorem Problem.language_admissible {PublicCtx : Type u} {S : ClaimFamily.{u, v} PublicCtx}
    (P : Problem.{u, v, w} S)
    {ctx : PublicCtx} {claim : S.Claim ctx} (h : P.language ctx claim) :
    P.admissible ctx claim := by
  obtain ⟨wit, hw⟩ := h
  exact P.rel_admissible ctx claim wit hw

/-- A promise-free relation is the special case with universally true admissibility. -/
abbrev Relation {PublicCtx : Type u} (S : ClaimFamily.{u, v} PublicCtx) :=
  { P : Problem.{u, v, w} S // P.admissible = fun _ _ => True }

/-- Build a promise-free problem from a claim-dependent witness family and predicate. -/
def Relation.ofPredicate {PublicCtx : Type u} {S : ClaimFamily.{u, v} PublicCtx}
    (Witness : ∀ ctx, S.Claim ctx → Type w)
    (rel : ∀ ctx claim, Witness ctx claim → Prop) : Relation S :=
  ⟨{ Witness := Witness, admissible := fun _ _ => True, rel := rel,
      rel_admissible := fun _ _ _ _ => trivial }, rfl⟩

end Interaction.Oracle
