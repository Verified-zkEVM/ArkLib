/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Cast.Defs

/-!
# Net multiplicities of keyed lists

A keyed list is a list of pairs (k, m): a key k carrying a multiplicity m.

The net multiplicity of a key is the sum of the multiplicities it carries.

A keyed list is balanced when every key has net multiplicity zero.

## Results

- Net multiplicities are additive in the list and commute with additive maps.
- A sum over the pairs, additive in the multiplicity, regroups as a sum over the keys.
- With unit multiplicities, the net multiplicity of a value is its count.
- Given a query list f and a table t, a multiplicity list for t puts each count of f
  on the last occurrence of its value in t.

All definitions here are executable.
-/

@[expose] public section

namespace List

open Finset

variable {κ R M : Type*} [DecidableEq κ]

section AddCommMonoid

variable [AddCommMonoid R] [AddCommMonoid M]

/-- The net multiplicity of a key: the sum of the multiplicities it carries. -/
def netMult (l : List (κ × R)) (k : κ) : R :=
  ((l.filter (·.1 = k)).map (·.2)).sum

/-- A keyed list is balanced when every key has net multiplicity zero. -/
def Balanced (l : List (κ × R)) : Prop :=
  ∀ k, netMult l k = 0

@[simp] theorem netMult_nil (k : κ) : netMult ([] : List (κ × R)) k = 0 := rfl

theorem netMult_cons (p : κ × R) (l : List (κ × R)) (k : κ) :
    netMult (p :: l) k = (if p.1 = k then p.2 else 0) + netMult l k := by
  unfold netMult; by_cases h : p.1 = k <;> simp [h]

theorem netMult_append (l l' : List (κ × R)) (k : κ) :
    netMult (l ++ l') k = netMult l k + netMult l' k := by
  simp [netMult, filter_append]

/-- A key that no pair carries has net multiplicity zero. -/
theorem netMult_of_not_mem {l : List (κ × R)} {k : κ} (h : k ∉ l.map (·.1)) :
    netMult l k = 0 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [map_cons, mem_cons, not_or] at h
    simp [netMult_cons, Ne.symm h.1, ih h.2]

/-- An additive map of the multiplicities maps the net multiplicities. -/
theorem netMult_map_snd (g : R →+ M) (l : List (κ × R)) (k : κ) :
    netMult (l.map fun p => (p.1, g p.2)) k = g (netMult l k) := by
  induction l with
  | nil => simp
  | cons p l ih => rw [map_cons, netMult_cons, netMult_cons, ih, map_add]; split_ifs <;> simp

/-- A sum over the pairs, additive in the multiplicity, regroups by key. -/
theorem sum_map_eq_sum_netMult (g : κ → R →+ M) (l : List (κ × R)) (S : Finset κ)
    (hS : ∀ p ∈ l, p.1 ∈ S) :
    (l.map fun p => g p.1 p.2).sum = ∑ k ∈ S, g k (netMult l k) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [map_cons, sum_cons, netMult_cons, map_add, sum_add_distrib]
    rw [ih fun q hq => hS q (mem_cons_of_mem _ hq)]
    congr 1
    rw [sum_eq_single_of_mem p.1 (hS p mem_cons_self) fun k _ hk => by simp [Ne.symm hk]]
    simp

end AddCommMonoid

section Count

variable [AddCommMonoidWithOne R]

/-- With unit multiplicities, the net multiplicity of a value is its count. -/
theorem netMult_map_one (f : List κ) (v : κ) :
    netMult (f.map (·, (1 : R))) v = (f.count v : R) := by
  induction f with
  | nil => simp
  | cons a f ih =>
    rw [map_cons, netMult_cons, ih, count_cons]; by_cases h : a = v <;> simp [h, add_comm]

variable (R) in
/-- Multiplicities for a table t: each count of f sits on the last occurrence of its value. -/
def lastMults (f : List κ) : List κ → List R
  | [] => []
  | v :: t => (if v ∈ t then 0 else (f.count v : R)) :: lastMults f t

@[simp] theorem length_lastMults (f t : List κ) : (lastMults R f t).length = t.length := by
  induction t <;> simp_all [lastMults]

theorem netMult_zip_lastMults (f t : List κ) (w : κ) :
    netMult (t.zip (lastMults R f t)) w = if w ∈ t then (f.count w : R) else 0 := by
  induction t with
  | nil => simp
  | cons v t ih =>
    simp only [lastMults, zip_cons_cons, netMult_cons, ih, mem_cons]
    rcases eq_or_ne v w with rfl | hw
    · by_cases ht : v ∈ t <;> simp_all
    · have := hw.symm
      by_cases ht : w ∈ t <;> simp_all

end Count

end List
