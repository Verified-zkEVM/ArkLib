/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
import ArkLib.Data.Vector.Lookup
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.FinCases
import Lean.Compiler.IR

/-! Acceptance checks for executable finite fibers and lookup histograms. -/

namespace HistogramTest

/-- An external executable caller requires equality only on keys. -/
def fiberCaller {κ R : Type} [DecidableEq κ] [AddCommMonoid R]
    (keys : Vector κ 3) (weights : Vector R 3) (k : κ) : R :=
  Finset.univ.sumFiber (fun i : Fin 3 ↦ keys[i.val]) (fun i ↦ weights[i.val]) k

/-- An external executable caller computes index multiplicities. -/
def histogramCaller {n m : ℕ} (indices : Vector (Fin n) m) : Vector ℕ n :=
  indices.histogram

example : fiberCaller #v["a", "a", "b"] #v[2, 4, 9] "a" = 6 := by decide
example : fiberCaller #v["a", "a", "b"] #v[2, 4, 9] "absent" = 0 := by decide
example : fiberCaller #v["a", "a", "b"] (#v[1, -1, 3] : Vector ℤ 3) "a" = 0 := by
  decide
example : histogramCaller (#v[] : Vector (Fin 0) 0) = #v[] := by decide
example : histogramCaller (#v[] : Vector (Fin 3) 0) = #v[0, 0, 0] := by decide
example : fiberCaller #v["a", "a", "b"] (#v[1, 1, 1] : Vector (ZMod 2) 3) "a" = 0 := by
  decide
example : histogramCaller (#v[0, 1, 2, 1] : Vector (Fin 3) 4) = #v[1, 2, 1] := by decide

example : Finset.univ.sumFiber (fun j : Fin 3 ↦ (#v[7, 7, 9] : Vector ℕ 3)[j.val])
    (fun j ↦ (histogramCaller (#v[0, 1, 2, 1] : Vector (Fin 3) 4))[j.val]) 7 = 3 := by
  exact (Vector.sumFiber_histogram #v[7, 7, 9] #v[7, 7, 9, 7] #v[0, 1, 2, 1]
    (by intro i; fin_cases i <;> decide) 7).trans (by decide)

/-- The encoding isolates zero while merging all three other occurring keys. -/
def encode (k : ℕ) : Bool := decide (k = 0)

example : encode 1 = encode 2 ∧ (1 : ℕ) ≠ 2 := by decide

example : Finset.univ.sumFiber (fun i : Fin 4 ↦ encode i.val)
    (fun i ↦ (#v[5, 2, -2, 9] : Vector ℤ 4)[i.val]) (encode 0) = 5 := by
  exact (Finset.sumFiber_comp_eq_of_isolated Finset.univ (fun i : Fin 4 ↦ i.val)
    (fun i ↦ (#v[5, 2, -2, 9] : Vector ℤ 4)[i.val]) encode 0
    (by intro i _ hi; simpa [encode] using hi)).trans (by decide)

/-- At a merged key the encoded and original fiber weights can differ. -/
example : Finset.univ.sumFiber (fun i : Fin 4 ↦ encode i.val)
    (fun i ↦ (#v[5, 2, -2, 9] : Vector ℤ 4)[i.val]) (encode 1) = 9 ∧
    Finset.univ.sumFiber (fun i : Fin 4 ↦ i.val)
      (fun i ↦ (#v[5, 2, -2, 9] : Vector ℤ 4)[i.val]) 1 = 2 := by decide

/-- The natural correctness law casts even when a positive query count becomes zero. -/
example : Finset.univ.sumFiber (fun j : Fin 1 ↦ (#v[7] : Vector ℕ 1)[j.val])
    (fun j ↦ ((histogramCaller (#v[0, 0] : Vector (Fin 1) 2))[j.val] : ZMod 2)) 7 = 0 := by
  exact (Vector.sumFiber_cast_histogram (R := ZMod 2) #v[7] #v[7, 7] #v[0, 0]
    (by intro i; fin_cases i <;> decide) 7).trans (by decide)

/-- Natural histogram weights satisfy the converse without a characteristic assumption. -/
example {κ : Type} [DecidableEq κ] {n m : ℕ} (table : Vector κ n)
    (queries : Vector κ m) (indices : Vector (Fin n) m)
    (hlookup : ∀ i : Fin m, table[(indices[i.val]).val] = queries[i.val]) (i : Fin m) :
    ∃ j : Fin n, table[j.val] = queries[i.val] := by
  exact Vector.exists_getElem_eq_of_sumFiber_eq_count table queries
    (fun j ↦ (indices.histogram)[j.val])
    (Vector.sumFiber_histogram table queries indices hlookup)
    (fun _ hpos ↦ Nat.ne_of_gt hpos) i

/-- Directly checked balance with arbitrary signed weights establishes lookup inclusion. -/
example (i : Fin 2) : ∃ j : Fin 3,
    (#v[0, 0, 1] : Vector (Fin 2) 3)[j.val] = (#v[0, 1] : Vector (Fin 2) 2)[i.val] := by
  exact Vector.exists_getElem_eq_of_sumFiber_eq_count #v[0, 0, 1] #v[0, 1]
    (fun j ↦ (#v[5, -4, 1] : Vector ℤ 3)[j.val]) (by decide) (by decide) i

/-- In characteristic two an absent query appearing twice can satisfy field balance,
even with a nonempty table. -/
example : (∀ k : ℕ, Finset.univ.sumFiber
    (fun j : Fin 1 ↦ (#v[8] : Vector ℕ 1)[j.val]) (fun _ ↦ (0 : ZMod 2)) k =
      ((#v[7, 7] : Vector ℕ 2).toList.count k : ZMod 2)) ∧
    ¬ ∃ j : Fin 1, (#v[8] : Vector ℕ 1)[j.val] = 7 := by
  constructor
  · intro k
    simp only [Finset.sumFiber, Finset.sum_const_zero]
    change 0 = (List.count k [7, 7] : ZMod 2)
    by_cases hk : k = 7
    · subst k
      decide
    · have hcount : List.count k [7, 7] = 0 :=
        List.count_eq_zero_of_not_mem (by simp [hk])
      rw [hcount]
      rfl
  · decide

#eval fiberCaller #v["a", "a", "b"] #v[2, 4, 9] "a"
#eval fiberCaller #v["a", "a", "b"] (#v[1, 1, 1] : Vector (ZMod 2) 3) "a"
#eval histogramCaller (#v[0, 1, 2, 1] : Vector (Fin 3) 4)

open Lean Elab Command

run_cmd do
  for n in #[``Finset.sumFiber, ``Vector.histogram, ``fiberCaller, ``histogramCaller] do
    unless (Lean.IR.findEnvDecl (← getEnv) n).isSome do
      throwError "Expected compiler IR for `{n}`"

run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for n in #[``Finset.sum_sumFiber, ``Finset.sumFiber_map,
      ``Finset.sumFiber_comp_eq_of_isolated, ``Vector.getElem_histogram,
      ``Vector.sumFiber_histogram, ``Vector.sumFiber_cast_histogram,
      ``Vector.exists_getElem_eq_of_sumFiber_eq_count] do
    let axioms ← collectAxioms n
    unless axioms.all allowed.contains do
      throwError "`{n}` depends on unexpected axioms: {axioms}"

end HistogramTest
