/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Fri.Spec.Extraction.Selection

/-!
# A single scan of the initial domain

The program generates each position once and counts its actual local-check result. The complete
accepting-position list appears only in correctness propositions; executable state retains the
count and the bounded sample caches.
-/

@[expose] public section

namespace Fri.Spec.Extractor
open Domain OracleComp OracleSpec CompPoly
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (o : ∀ j, FinalOracleStatement s ω j)
variable (α : FinalStatement F k)

/-- The accepting members of an explicit index list, in their original order. -/
noncomputable def acceptedList (hs : (∑ j, (s j).val) ≤ n)
    (xs : List (Fin (2 ^ n))) : List (Fin (2 ^ n)) := by
  classical
  exact xs.filter (· ∈ acceptingQueries s hs o α)

/-- Scan an explicit index list, preserving the cache's relation to all earlier acceptances. -/
def scanAux (hs : (∑ j, (s j).val) ≤ n) (gen : Generator ω)
    (check : (z : Fin (2 ^ n)) →
      {x : (ω.subdomain 0).toFinset // x = initialQuery z} →
      OracleComp (InstructionSpec s o α)
        {b : Bool // b = true ↔ z ∈ acceptingQueries s hs o α})
    {D : ℕ} : (xs : List (Fin (2 ^ n))) → (state : Selection s o D) →
    OracleComp (InstructionSpec s o α) {result : Selection s o D //
      ∀ accepted, state.Valid s o accepted →
        result.Valid s o (accepted ++ acceptedList s o α hs xs)}
  | [], state => do
    liftComp (Arithmetic.tick (F := F)) _
    pure ⟨state, by intro accepted hstate; simpa [acceptedList] using hstate⟩
  | z :: zs, state => do
    liftComp (Arithmetic.tick (F := F)) _
    let x ← generateInitialQuery s o α gen z
    let b ← check z x
    if hb : b.val = true then
      let next ← selectSample s o α state z x
      let rest ← scanAux hs gen check zs next.val
      pure ⟨rest.val, by
        intro accepted hstate
        have hnext := next.property accepted hstate
        have hrest := rest.property (accepted ++ [z]) hnext
        have hz := b.property.mp hb
        classical
        simpa [acceptedList, hz, List.append_assoc] using hrest⟩
    else
      let rest ← scanAux hs gen check zs state
      pure ⟨rest.val, by
        intro accepted hstate
        have hrest := rest.property accepted hstate
        have hz : z ∉ acceptingQueries s hs o α := by
          intro hz
          exact hb (b.property.mpr hz)
        classical
        simpa [acceptedList, hz] using hrest⟩

/-- Scan the complete initial domain in index order, caching only the requested prefix. -/
def scan (hs : (∑ j, (s j).val) ≤ n) (gen : Generator ω)
    (check : (z : Fin (2 ^ n)) →
      {x : (ω.subdomain 0).toFinset // x = initialQuery z} →
      OracleComp (InstructionSpec s o α)
        {b : Bool // b = true ↔ z ∈ acceptingQueries s hs o α}) (D : ℕ) :
    OracleComp (InstructionSpec s o α) {state : Selection s o D //
      state.Valid s o (acceptedList s o α hs (List.finRange (2 ^ n)))} := do
  let result ← scanAux s o α hs gen check (List.finRange (2 ^ n)) (emptySelection s o D)
  pure ⟨result.val, by simpa using result.property [] (emptySelection_valid s o D)⟩

end Fri.Spec.Extractor
