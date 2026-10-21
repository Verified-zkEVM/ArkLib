/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Fri.Spec.Extraction.Readers

/-!
# Streaming counts and caches for accepting positions

The runtime state stores only a count and the bounded selected cache. Its relation to the full
list of previously accepted positions is a proposition, without an executable history parameter.
-/

@[expose] public section

namespace Fri.Spec.Extractor
open Domain OracleComp OracleSpec CompPoly
variable {F : Type} [NonBinaryField F] [Fintype F] [DecidableEq F]
variable {n k : ℕ} {ω : SmoothCosetFftDomain n F}
variable (s : Fin (k + 1) → ℕ+) (o : ∀ j, FinalOracleStatement s ω j)
variable (α : FinalStatement F k)

/-- The count and bounded caches retained during a domain scan. -/
structure Selection (D : ℕ) where
  count : ℕ
  selected : List (Fin (2 ^ n))
  nodes : Array F
  values : Array F
  selected_le : selected.length ≤ D
  nodes_eq : nodes = (selected.map ω).toArray
  values_eq : values = (selected.map (initialWord s o)).toArray

/-- The count and selected prefix describe exactly the given accepted positions. -/
def Selection.Valid {D : ℕ} (state : Selection s o D)
    (accepted : List (Fin (2 ^ n))) : Prop :=
  state.count = accepted.length ∧ state.selected = accepted.take D

/-- An empty streaming cache. -/
def emptySelection (D : ℕ) : Selection s o D :=
  ⟨0, [], #[], #[], by simp, rfl, rfl⟩

/-- The empty cache describes the empty list of accepting positions. -/
theorem emptySelection_valid (D : ℕ) : (emptySelection s o D).Valid s o [] := by
  simp [Selection.Valid, emptySelection]

/-- Count an acceptance, retaining its generated node and value while cache space remains. -/
def selectSample {D : ℕ} (state : Selection s o D) (z : Fin (2 ^ n))
    (x : {q : (ω.subdomain 0).toFinset // q = initialQuery z}) :
    OracleComp (InstructionSpec s o α) {result : Selection s o D //
      ∀ accepted, state.Valid s o accepted → result.Valid s o (accepted ++ [z])} := do
  liftComp (Arithmetic.tick (F := F)) _
  if hcap : state.selected.length < D then
    let y ← readSample s o α z x
    pure ⟨{
      count := state.count + 1
      selected := state.selected ++ [z]
      nodes := state.nodes.push x.val.val
      values := state.values.push y.val
      selected_le := by simp; omega
      nodes_eq := by
        rw [state.nodes_eq]
        have hx : x.val.val = ω z := congrArg Subtype.val x.property
        simp [hx]
      values_eq := by rw [state.values_eq, y.property]; simp }, by
        intro accepted hstate
        obtain ⟨hcount, hselected⟩ := hstate
        constructor
        · simp [hcount]
        · change state.selected ++ [z] = (accepted ++ [z]).take D
          have hlen : accepted.length < D := by
            rw [hselected, List.length_take] at hcap
            omega
          rw [List.take_of_length_le (by simp; omega), hselected,
            List.take_of_length_le (by omega)]⟩
  else
    pure ⟨{
      count := state.count + 1
      selected := state.selected
      nodes := state.nodes
      values := state.values
      selected_le := state.selected_le
      nodes_eq := state.nodes_eq
      values_eq := state.values_eq }, by
        intro accepted hstate
        obtain ⟨hcount, hselected⟩ := hstate
        constructor
        · simp [hcount]
        · change state.selected = (accepted ++ [z]).take D
          have hlen : D ≤ accepted.length := by
            rw [hselected, List.length_take] at hcap
            omega
          rw [List.take_append_of_le_length hlen]
          exact hselected⟩

end Fri.Spec.Extractor
