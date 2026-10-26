/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.Algebra.Group.Defs
public import Mathlib.Algebra.BigOperators.Group.List.Defs

/-!
# Shared local arithmetic for native Sumcheck checks

The native verifier and its arithmetic interpretation use the same sum and comparison drivers.
The sum reads the head before its tail and adds after the recursive tail, preserving the explicit
final addition to zero. Its Boolean-domain instance therefore makes two additions. Equality
invokes its supplied comparison callback once at the existing verifier comparison site.
-/

@[expose] public section

namespace Sumcheck.Impl.VerifierChecks
universe v
variable {R : Type} {m : Type → Type v} [Monad m]

/-- Read the domain in order, then add each head to its recursively obtained tail sum. -/
@[specialize]
def sumM [Zero R] (read : R → m R) (add : R → R → m R) : List R → m R
  | [] => pure 0
  | x :: xs => do
    let value ← read x
    let rest ← sumM read add xs
    add value rest

/-- One explicit comparison callback, shared by ordinary and arithmetic interpretations. -/
@[inline]
def equalM (equal : R → R → m Bool) (left right : R) : m Bool := equal left right

/-- Only the actual domain's readers can affect its sum, including their effects. -/
theorem sumM_congr_read [Zero R] (left right : R → m R) (add : R → R → m R)
    (domain : List R) (hread : ∀ x ∈ domain, left x = right x) :
    sumM left add domain = sumM right add domain := by
  induction domain with
  | nil => rfl
  | cons x xs ih =>
    simp only [sumM]
    rw [hread x (by simp)]
    congr 1
    funext value
    rw [ih (fun y hy => hread y (by simp [hy]))]

/-- Ordinary addition has exactly the current right-associated domain-sum value. -/
theorem sumM_id_eq_sum [AddMonoid R] (read : R → R) (domain : List R) :
    (sumM (m := Id) read (fun a b => a + b) domain).run = (domain.map read).sum := by
  induction domain with
  | nil => rfl
  | cons x xs ih =>
    change read x + (sumM (m := Id) read (fun a b => a + b) xs).run =
      read x + (xs.map read).sum
    rw [ih]

end Sumcheck.Impl.VerifierChecks
