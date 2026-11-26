/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Relation.OracleInterface

/-!
# Claims and relations

This file defines indexed claims and witness relations with an explicit admissibility boundary.
Neither depends on a protocol tree or an execution strategy.
-/

@[expose] public section

namespace Interaction.Oracle

/-- Public contexts and the claim type visible in each context. -/
structure ClaimFamily (PublicCtx : Type) : Type 1 where
  /-- Claims indexed by the public context. -/
  Claim : PublicCtx → Type

/-- A claim-dependent witness relation with an explicit admissibility boundary.

A `Problem` is a promise relation: a witness relation together with an admissibility promise on
claims. -/
structure Problem {PublicCtx : Type} (S : ClaimFamily PublicCtx) : Type 1 where
  /-- Witnesses can depend on both context and claim. -/
  Witness : ∀ ctx, S.Claim ctx → Type
  /-- Claim-level promises and well-formedness. -/
  admissible : ∀ ctx, S.Claim ctx → Prop
  /-- The relation observes only the declared claim. -/
  rel : ∀ ctx claim, Witness ctx claim → Prop
  /-- Every related claim satisfies the declared promise. -/
  rel_admissible : ∀ ctx claim wit, rel ctx claim wit → admissible ctx claim

/-- Membership means existence of a related witness. -/
def Problem.language {PublicCtx : Type} {S : ClaimFamily PublicCtx}
    (P : Problem S)
    (ctx : PublicCtx) (claim : S.Claim ctx) : Prop := ∃ wit, P.rel ctx claim wit

/-- Language membership entails the claim's admissibility. -/
theorem Problem.language_admissible {PublicCtx : Type} {S : ClaimFamily PublicCtx}
    (P : Problem S)
    {ctx : PublicCtx} {claim : S.Claim ctx} (h : P.language ctx claim) :
    P.admissible ctx claim := by
  obtain ⟨wit, hw⟩ := h
  exact P.rel_admissible ctx claim wit hw

/-- A promise-free relation is the special case with universally true admissibility. -/
abbrev Relation {PublicCtx : Type} (S : ClaimFamily PublicCtx) :=
  { P : Problem S // P.admissible = fun _ _ => True }

/-- Build a promise-free problem from a claim-dependent witness family and predicate. -/
def Relation.ofPredicate {PublicCtx : Type} {S : ClaimFamily PublicCtx}
    (Witness : ∀ ctx, S.Claim ctx → Type)
    (rel : ∀ ctx claim, Witness ctx claim → Prop) : Relation S :=
  ⟨{ Witness := Witness, admissible := fun _ _ => True, rel := rel,
      rel_admissible := fun _ _ _ _ => trivial }, rfl⟩

end Interaction.Oracle
