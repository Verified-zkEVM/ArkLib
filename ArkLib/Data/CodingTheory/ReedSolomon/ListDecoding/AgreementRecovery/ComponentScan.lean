/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Data.List.Count
public import Mathlib.Data.List.Nodup
public import Mathlib.Tactic.SplitIfs

/-!
# Recorded-position scan for finite components

This is the position traversal in `RecoverAgreement`. An algebraic splitter provides tagged
children; `true` records an agreement and `false` records a rejection. The scan stops after
`k` agreements. The geometric lemmas are reusable for univariate factors and two-level towers;
they do not construct candidates or replace the algebraic splitter.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.AgreementRecovery.ComponentScan

variable {S I P : Type*}

/-- A live finite component and its recorded positions, in reverse traversal order. -/
structure Block (S I : Type*) where
  component : S
  positions : List I

/-- Traverse remaining positions using the actual tagged component splitter. Empty components
are removed by `alive`; a surviving component stops as soon as it records `k` agreements. -/
def scan (alive : S → Bool) (split : S → I → List (Bool × S)) (k : ℕ) :
    List I → Block S I → List (Block S I)
  | rows, block =>
    if !alive block.component then []
    else if k ≤ block.positions.length then [block]
    else match rows with
      | [] => []
      | i :: rest => (split block.component i).flatMap fun child =>
          scan alive split k rest
            ⟨child.2, if child.1 then i :: block.positions else block.positions⟩

/-- Each emitted sample has exactly `k` positions when the initial sample has at most `k`. -/
theorem positions_length (alive : S → Bool) (split : S → I → List (Bool × S))
    (k : ℕ) (rows : List I) (block out : Block S I)
    (hstart : block.positions.length ≤ k) (hout : out ∈ scan alive split k rows block) :
    out.positions.length = k := by
  induction rows generalizing block with
  | nil =>
      simp only [scan] at hout
      split_ifs at hout with hempty hstop
      · simp at hout
      · obtain rfl := List.mem_singleton.mp hout
        omega
      · simp at hout
  | cons i rest ih =>
      simp only [scan] at hout
      split_ifs at hout with hempty hstop
      · simp at hout
      · obtain rfl := List.mem_singleton.mp hout
        omega
      · obtain ⟨child, _, hout⟩ := List.mem_flatMap.mp hout
        apply ih _ ?_ hout
        cases child.1 <;> simp <;> omega

/-- Recorded positions preserve input order and therefore are distinct for distinct input rows. -/
theorem positions_sublist (alive : S → Bool) (split : S → I → List (Bool × S))
    (k : ℕ) (rows : List I) (block out : Block S I)
    (hout : out ∈ scan alive split k rows block) :
    out.positions.Sublist (rows.reverse ++ block.positions) := by
  induction rows generalizing block with
  | nil =>
      simp only [scan] at hout
      split_ifs at hout
      · simp at hout
      · obtain rfl := List.mem_singleton.mp hout
        simp
      · simp at hout
  | cons i rest ih =>
      simp only [scan] at hout
      split_ifs at hout
      · simp at hout
      · obtain rfl := List.mem_singleton.mp hout
        exact List.sublist_append_right _ _
      · obtain ⟨child, _, hout⟩ := List.mem_flatMap.mp hout
        have h := ih _ hout
        cases hc : child.1
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at h
          apply h.trans
          simp only [List.reverse_cons, List.append_assoc, List.singleton_append]
          exact (List.sublist_cons_self i block.positions).append_left _
        · simpa only [hc, ↓reduceIte, List.reverse_cons, List.append_assoc,
            List.singleton_append] using h

/-- Every returned component is nonempty according to the executable test. -/
theorem alive_of_mem (alive : S → Bool) (split : S → I → List (Bool × S))
    (k : ℕ) (rows : List I) (block out : Block S I)
    (hout : out ∈ scan alive split k rows block) : alive out.component = true := by
  induction rows generalizing block with
  | nil =>
      simp only [scan] at hout
      split_ifs at hout with hempty hstop
      · simp at hout
      · obtain rfl := List.mem_singleton.mp hout
        simpa using hempty
      · simp at hout
  | cons i rest ih =>
      simp only [scan] at hout
      split_ifs at hout with hempty hstop
      · simp at hout
      · obtain rfl := List.mem_singleton.mp hout
        simpa using hempty
      · obtain ⟨child, _, hout⟩ := List.mem_flatMap.mp hout
        exact ih _ hout

/-- Algebraic validity of components is preserved by the scan when each executed split
preserves it. This is used with monicity and fiberwise squarefreeness of finite towers. -/
theorem invariant (alive : S → Bool) (split : S → I → List (Bool × S))
    (valid : S → Prop)
    (hstep : ∀ s i child, valid s → child ∈ split s i → valid child.2)
    (k : ℕ) (rows : List I) (block out : Block S I) (hv : valid block.component)
    (hout : out ∈ scan alive split k rows block) : valid out.component := by
  induction rows generalizing block with
  | nil =>
      simp only [scan] at hout
      split_ifs at hout
      · simp at hout
      · obtain rfl := List.mem_singleton.mp hout
        exact hv
      · simp at hout
  | cons i rest ih =>
      simp only [scan] at hout
      split_ifs at hout
      · simp at hout
      · obtain rfl := List.mem_singleton.mp hout
        exact hv
      · obtain ⟨child, hc, hout⟩ := List.mem_flatMap.mp hout
        exact ih _ (hstep _ _ _ hv hc) hout

/-- A geometric point of an emitted component comes from the original component, and every
recorded position is either inherited or an actual agreement at that point. -/
theorem point_sound (alive : S → Bool) (split : S → I → List (Bool × S))
    (point : S → P → Prop) (good : P → I → Prop)
    (hstep : ∀ s i child θ, child ∈ split s i → point child.2 θ →
      point s θ ∧ (child.1 = true → good θ i))
    (k : ℕ) (rows : List I) (block out : Block S I) (θ : P)
    (hout : out ∈ scan alive split k rows block) (hpoint : point out.component θ) :
    point block.component θ ∧ ∀ i ∈ out.positions, i ∈ block.positions ∨ good θ i := by
  induction rows generalizing block with
  | nil =>
      simp only [scan] at hout
      split_ifs at hout
      · simp at hout
      · obtain rfl := List.mem_singleton.mp hout
        exact ⟨hpoint, fun _ hi => Or.inl hi⟩
      · simp at hout
  | cons i rest ih =>
      simp only [scan] at hout
      split_ifs at hout
      · simp at hout
      · obtain rfl := List.mem_singleton.mp hout
        exact ⟨hpoint, fun _ hi => Or.inl hi⟩
      · obtain ⟨child, hc, hout⟩ := List.mem_flatMap.mp hout
        obtain ⟨hchild, hrecorded⟩ := ih _ hout
        have hs := hstep _ _ _ θ hc hchild
        refine ⟨hs.1, ?_⟩
        intro j hj
        rcases hrecorded j hj with hold | hgood
        · cases ht : child.1
          · exact Or.inl (by simpa [ht] using hold)
          · simp only [ht, ↓reduceIte, List.mem_cons] at hold
            rcases hold with rfl | hold
            · exact Or.inr (hs.2 ht)
            · exact Or.inl hold
        · exact Or.inr hgood

/-- A point with enough remaining agreements follows an executed child at every row and reaches
a stopped component. The splitter's point coverage is local; no decoded list is assumed. -/
theorem point_complete (alive : S → Bool) (split : S → I → List (Bool × S))
    (point : S → P → Prop) (good : P → I → Prop)
    (halive : ∀ s θ, point s θ → alive s = true)
    (hstep : ∀ s i θ, point s θ → ∃ child ∈ split s i,
      point child.2 θ ∧ (child.1 = true ↔ good θ i))
    (k : ℕ) (rows : List I) (block : Block S I) (θ : P)
    (hpoint : point block.component θ)
    (hrecorded : ∀ i ∈ block.positions, good θ i)
    [DecidablePred (good θ)]
    (henough : k ≤ block.positions.length + rows.countP (fun i => decide (good θ i))) :
    ∃ out ∈ scan alive split k rows block,
      point out.component θ ∧ ∀ i ∈ out.positions, good θ i := by
  induction rows generalizing block with
  | nil =>
      have hstop : k ≤ block.positions.length := by simpa using henough
      exact ⟨block, by simp [scan, halive _ _ hpoint, hstop], hpoint, hrecorded⟩
  | cons i rest ih =>
      by_cases hstop : k ≤ block.positions.length
      · exact ⟨block, by simp [scan, halive _ _ hpoint, hstop], hpoint, hrecorded⟩
      · obtain ⟨child, hc, hp, ht⟩ := hstep _ i θ hpoint
        let next : Block S I :=
          ⟨child.2, if child.1 then i :: block.positions else block.positions⟩
        have hnrecorded : ∀ j ∈ next.positions, good θ j := by
          intro j hj
          cases hb : child.1
          · exact hrecorded j (by simpa [next, hb] using hj)
          · simp only [next, hb, ↓reduceIte, List.mem_cons] at hj
            rcases hj with rfl | hj
            · exact ht.mp hb
            · exact hrecorded j hj
        have hnenough : k ≤ next.positions.length +
            rest.countP (fun j => decide (good θ j)) := by
          cases hb : child.1
          · have hbad : ¬good θ i := by simpa [hb] using ht.symm
            simpa [next, hb, hbad, List.countP_cons] using henough
          · have hg := ht.mp hb
            simpa [next, hb, hg, List.countP_cons, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using henough
        obtain ⟨out, hout, hpout, hgood⟩ := ih next hp hnrecorded hnenough
        refine ⟨out, ?_, hpout, hgood⟩
        simp only [scan, halive _ _ hpoint, Bool.not_true, Bool.false_eq_true,
          ↓reduceIte, hstop]
        exact List.mem_flatMap.mpr ⟨child, hc, hout⟩

/-- One row of the collection scan. Stopped components retain their place in the ordered list;
only live components invoke the algebraic splitter. -/
def advance (alive : S → Bool) (split : S → I → List (Bool × S)) (k : ℕ)
    (i : I) (block : Block S I) : List (Block S I) :=
  if !alive block.component then []
  else if k ≤ block.positions.length then [block]
  else (split block.component i).map fun child =>
    ⟨child.2, if child.1 then i :: block.positions else block.positions⟩

/-- The row scan is the paper's collection traversal: all live components see one received
position before the next position is processed. -/
def scanMany (alive : S → Bool) (split : S → I → List (Bool × S)) (k : ℕ) :
    List I → List (Block S I) → List (Block S I)
  | [], blocks => blocks.flatMap (scan alive split k [])
  | i :: rest, blocks =>
      scanMany alive split k rest (blocks.flatMap (advance alive split k i))

/-- One depth-first step can be reassociated into the row-wise collection traversal. -/
theorem scan_cons (alive : S → Bool) (split : S → I → List (Bool × S))
    (k : ℕ) (i : I) (rest : List I) (block : Block S I) :
    scan alive split k (i :: rest) block =
      (advance alive split k i block).flatMap (scan alive split k rest) := by
  by_cases he : alive block.component = false
  · simp [scan, advance, he]
  have ha : alive block.component = true := by
    cases h : alive block.component <;> simp_all
  by_cases hs : k ≤ block.positions.length
  · cases rest <;> simp [scan, advance, ha, hs]
  · simp [scan, advance, ha, hs, List.flatMap_map]

/-- Collection scanning and per-component scanning return exactly the same ordered components
and samples. This permits batching algebraic reductions while reusing pointwise proofs. -/
theorem scanMany_eq (alive : S → Bool) (split : S → I → List (Bool × S))
    (k : ℕ) (rows : List I) (blocks : List (Block S I)) :
    scanMany alive split k rows blocks = blocks.flatMap (scan alive split k rows) := by
  induction rows generalizing blocks with
  | nil => rfl
  | cons i rest ih =>
      rw [scanMany, ih, List.flatMap_assoc]
      apply List.flatMap_congr
      intro block _
      exact (scan_cons alive split k i rest block).symm

end ReedSolomon.ListDecoding.AgreementRecovery.ComponentScan
