/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.SquareSystems.ComputablePool
public import Mathlib.Data.List.Sublists
public import Mathlib.Data.Nat.Choose.Bounds

/-!
# Executable lists of square systems

`enumerateSquareSystems` is a convenient duplicate-free `Finset` specification. This file gives
the actual list producer used by a solver: sort the finite label type, enumerate its length-`r`
sublists, and form one square system per selected sublist. Each system keeps the initial Taylor
chart equation as its first row and adds `r` rows from the agreement-and-tail pool. It is therefore
square in the `r+1` jet coordinates. Coincident polynomial rows may produce duplicate systems,
which is harmless before the solver's final candidate deduplication.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.SquareSystems

/-- Turn an ordered selected sublist into the canonical `Fin r` row embedding. The sublist inherits
no repetitions from the sorted label list, while its length proof supplies the required cardinality
without inspecting polynomial rows. -/
def sublistEmbedding {ι : Type*} [LinearOrder ι] {r : ℕ} (labels selected : List ι)
    (hlabels : labels.Nodup) (hsub : selected.Sublist labels) (hlen : selected.length = r) :
    Fin r ↪ ι :=
  rowSubsetEmbedding selected.toFinset (by
    rw [List.toFinset_card_of_nodup (hsub.nodup hlabels)]
    exact hlen)

/-- Executably enumerate all square systems, in lexicographic label-sublist order. The initial row
is fixed because it normalizes the Taylor chart; only the remaining `r` equations participate in
the capture theorem's row selection. -/
def enumerateSquareSystemsList {P ι : Type*} [Fintype ι] [LinearOrder ι]
    (r : ℕ) (initial : P) (pool : ι → P) : List (Fin (r + 1) → P) :=
  let labels := Finset.univ.sort (fun x y : ι => x ≤ y)
  (labels.sublistsLen r).attach.map fun selected =>
    squareSystemRows initial pool
      (sublistEmbedding labels selected.val (Finset.sort_nodup _ _)
        (List.mem_sublistsLen.mp selected.property).1
        (List.length_of_sublistsLen selected.property))

/-- The executable list denotes exactly the existing duplicate-free family specification. Forward
membership forgets the selected list's order. For reverse membership, filtering the sorted universe
by a specified finite subset reconstructs its unique increasing representative. -/
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
    -- Reconstruct a computable list representative of the finite subset returned by the
    -- specification. Filtering preserves label order and introduces no repetitions.
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

/-- The list has one entry per `r`-subset of the finite label type. This counts solver calls before
coincident systems are deduplicated: exactly `choose |ι| r`, including the empty selection at
`r = 0`. -/
theorem length_enumerateSquareSystemsList {P ι : Type*} [Fintype ι] [LinearOrder ι]
    (r : ℕ) (initial : P) (pool : ι → P) :
    (enumerateSquareSystemsList r initial pool).length = (Fintype.card ι).choose r := by
  simp only [enumerateSquareSystemsList, List.length_map, List.length_attach,
    List.length_sublistsLen, Finset.length_sort, Finset.card_univ]

local instance systemListSumFinLinearOrder (a b : ℕ) : LinearOrder (Fin a ⊕ Fin b) :=
  finSumFinEquiv.linearOrder

/-- Compute the concrete Taylor table once, then list all resulting square systems. The table
contains the cleared Taylor numerators shared by every agreement and tail row, so placing the
`let` outside the pool function prevents reconstructing the recurrence for each selected label. -/
def squareSystemsListFromEquation {F : Type*} [Field F] [BEq F] [LawfulBEq F]
    [DecidableEq F] {r : ℕ} (center : F) (Q : CPoly.CMvPolynomial (r + 2) F)
    (K τ k n : ℕ) (hk : k ≤ K) (domain : Fin n ↪ F) (received : Fin n → F) :
    List (Fin (r + 1) → CPoly.CMvPolynomial (r + 1) F) :=
  let table := computableRationalTaylorTable center Q K
  enumerateSquareSystemsList r (computableInitialJetEquation center Q)
    (computableFullPool center
      (fun l : Fin K => table[l.val]'(by simp [table]))
      (computableInitialJetSeparant center Q) τ k n hk domain received)

/-- The concrete producer makes exactly one solver call per `r`-subset of its `n + (K-k)` pool
labels. This count is before any coincident polynomial systems are deduplicated. -/
theorem length_squareSystemsListFromEquation {F : Type*} [Field F] [BEq F]
    [LawfulBEq F] [DecidableEq F] {r : ℕ} (center : F)
    (Q : CPoly.CMvPolynomial (r + 2) F) (K τ k n : ℕ) (hk : k ≤ K)
    (domain : Fin n ↪ F) (received : Fin n → F) :
    (squareSystemsListFromEquation center Q K τ k n hk domain received).length =
      (n + (K - k)).choose r := by
  rw [squareSystemsListFromEquation, length_enumerateSquareSystemsList]
  simp only [Fintype.card_sum, Fintype.card_fin]

/-- When `K ≤ n`, the actual list producer satisfies the paper's `(2n)^r` solver-call bound. -/
theorem length_squareSystemsListFromEquation_le {F : Type*} [Field F] [BEq F]
    [LawfulBEq F] [DecidableEq F] {r : ℕ} (center : F)
    (Q : CPoly.CMvPolynomial (r + 2) F) (K τ k n : ℕ) (hk : k ≤ K)
    (hKn : K ≤ n) (domain : Fin n ↪ F) (received : Fin n → F) :
    (squareSystemsListFromEquation center Q K τ k n hk domain received).length ≤
      (2 * n) ^ r := by
  rw [length_squareSystemsListFromEquation]
  apply (Nat.choose_le_pow _ _).trans
  apply Nat.pow_le_pow_left
  omega

/-- The concrete list and finite-family view contain exactly the same square systems. Thus the
existing square-capture proof transfers directly to the list consumed by `flatMap` over solver
outputs. -/
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
