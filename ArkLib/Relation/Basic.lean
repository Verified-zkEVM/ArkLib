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

universe u v w

namespace Interaction.Oracle

/-- Public contexts and the claim type visible in each context. -/
structure ClaimFamily (PublicCtx : Type u) where
  /-- Claims indexed by the public context. -/
  Claim : PublicCtx → Type v

/-- A claim-dependent witness relation with an explicit admissibility boundary.

A `Problem` is a promise relation: a witness relation together with an admissibility promise on
claims. -/
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
