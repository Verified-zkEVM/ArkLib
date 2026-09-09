/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.SquareSystems.ComputablePool
import Mathlib.Data.List.Sublists

/-!
# Executable lists of square systems

`enumerateSquareSystems` is a convenient duplicate-free `Finset` specification. This file gives
the actual list producer used by a solver: sort the finite label type, enumerate its length-`r`
sublists, and form one square system per selected sublist. Coincident polynomial rows may therefore
produce duplicate systems, which is harmless before the solver's final candidate deduplication.
-/

namespace ReedSolomon.HiddenDerivative.SquareSystems

/-- The canonical embedding represented by a duplicate-free selected sublist. -/
def sublistEmbedding {ι : Type*} [LinearOrder ι] {r : ℕ} (labels selected : List ι)
    (hlabels : labels.Nodup) (hsub : selected.Sublist labels) (hlen : selected.length = r) :
    Fin r ↪ ι :=
  rowSubsetEmbedding selected.toFinset (by
    rw [List.toFinset_card_of_nodup (hsub.nodup hlabels)]
    exact hlen)

/-- Executably enumerate all square systems, in lexicographic label-sublist order. -/
def enumerateSquareSystemsList {P ι : Type*} [Fintype ι] [LinearOrder ι]
    (r : ℕ) (initial : P) (pool : ι → P) : List (Fin (r + 1) → P) :=
  let labels := Finset.univ.sort (fun x y : ι => x ≤ y)
  (labels.sublistsLen r).attach.map fun selected =>
    squareSystemRows initial pool
      (sublistEmbedding labels selected.val (Finset.sort_nodup _ _)
        (List.mem_sublistsLen.mp selected.property).1
        (List.length_of_sublistsLen selected.property))

/-- The executable list denotes exactly the existing duplicate-free family specification. -/
theorem mem_enumerateSquareSystemsList_iff {P ι : Type*} [DecidableEq P]
    [Fintype ι] [LinearOrder ι] (r : ℕ) (initial : P) (pool : ι → P)
    (rows : Fin (r + 1) → P) :
    rows ∈ enumerateSquareSystemsList r initial pool ↔
      rows ∈ enumerateSquareSystems r initial pool := by
  classical
  let labels := Finset.univ.sort (fun x y : ι => x ≤ y)
  constructor
  · intro hrows
    rw [enumerateSquareSystemsList, List.mem_map] at hrows
    obtain ⟨selected, _, rfl⟩ := hrows
    apply squareSystemRows_mem_enumerate
  · intro hrows
    rw [enumerateSquareSystems, Finset.mem_image] at hrows
    obtain ⟨selected, _, hselectedRows⟩ := hrows
    let chosen := labels.filter fun x => x ∈ selected.val
    have hchosenSub : chosen.Sublist labels := List.filter_sublist
    have hchosenNodup : chosen.Nodup := hchosenSub.nodup (Finset.sort_nodup _ _)
    have hchosenFinset : chosen.toFinset = selected.val := by
      ext x
      simp [chosen, labels]
    have hselectedCard : selected.val.card = r :=
      (mem_rowSubsets_iff selected.val).mp selected.property
    have hchosenLength : chosen.length = r := by
      rw [← List.toFinset_card_of_nodup hchosenNodup, hchosenFinset]
      exact hselectedCard
    have hchosenMem : chosen ∈ labels.sublistsLen r :=
      List.mem_sublistsLen.mpr ⟨hchosenSub, hchosenLength⟩
    have hembedding :
        sublistEmbedding labels chosen (Finset.sort_nodup _ _) hchosenSub hchosenLength =
          rowSubsetEmbedding selected.val hselectedCard := by
      apply Function.Embedding.ext
      intro i
      unfold sublistEmbedding
      simp only [hchosenFinset]
    rw [enumerateSquareSystemsList, List.mem_map]
    let chosenAttached : {s // s ∈ labels.sublistsLen r} := ⟨chosen, hchosenMem⟩
    refine ⟨chosenAttached, List.mem_attach _ _, ?_⟩
    rw [← hselectedRows]
    rw [hembedding]

/-- The list has one entry per `r`-subset of the finite label type. -/
theorem length_enumerateSquareSystemsList {P ι : Type*} [Fintype ι] [LinearOrder ι]
    (r : ℕ) (initial : P) (pool : ι → P) :
    (enumerateSquareSystemsList r initial pool).length = (Fintype.card ι).choose r := by
  simp only [enumerateSquareSystemsList, List.length_map, List.length_attach,
    List.length_sublistsLen, Finset.length_sort, Finset.card_univ]

local instance systemListSumFinLinearOrder (a b : ℕ) : LinearOrder (Fin a ⊕ Fin b) :=
  finSumFinEquiv.linearOrder

/-- Compute the concrete Taylor table once, then list all resulting square systems. -/
def squareSystemsListFromEquation {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    [DecidableEq F] {r : ℕ} (center : F) (Q : CPoly.CMvPolynomial (r + 2) F)
    (K τ k n : ℕ) (hk : k ≤ K) (domain : Fin n ↪ F) (received : Fin n → F) :
    List (Fin (r + 1) → CPoly.CMvPolynomial (r + 1) F) :=
  let table := computableRationalTaylorTable center Q K
  enumerateSquareSystemsList r (computableInitialJetEquation center Q)
    (computableFullPool center
      (fun l : Fin K => table[l.val]'(by simp [table]))
      (computableInitialJetSeparant center Q) τ k n hk domain received)

/-- The concrete list and finite-family view contain exactly the same square systems. -/
theorem mem_squareSystemsListFromEquation_iff {F : Type*} [Field F] [BEq F]
    [LawfulBEq F] [DecidableEq F] {r : ℕ} (center : F)
    (Q : CPoly.CMvPolynomial (r + 2) F) (K τ k n : ℕ) (hk : k ≤ K)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (rows : Fin (r + 1) → CPoly.CMvPolynomial (r + 1) F) :
    rows ∈ squareSystemsListFromEquation center Q K τ k n hk domain received ↔
      rows ∈ squareSystemsFromEquation center Q K τ k n hk domain received := by
  simp only [squareSystemsListFromEquation, squareSystemsFromEquation,
    computableSquareSystems, mem_enumerateSquareSystemsList_iff]

end ReedSolomon.HiddenDerivative.SquareSystems
