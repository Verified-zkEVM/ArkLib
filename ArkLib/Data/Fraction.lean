/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Data.List.Perm.Basic
public import Mathlib.Tactic.Ring

/-!
# Folding numerator and denominator pairs

`FractionPair` retains an unnormalized numerator and denominator, including a possibly zero
denominator. Its explicit `combine` operation computes the usual cross-products without division.
The list fold respects regrouping even at poles. Evaluating the result as a fraction agrees with
the sum of the input fractions when their denominators are nonzero.

All data operations in this module are executable over the supplied coefficient operations.
-/

@[expose] public section

/-- An unnormalized numerator and denominator. The denominator may be zero. -/
structure FractionPair (R : Type*) where
  /-- The numerator. -/
  numerator : R
  /-- The denominator. -/
  denominator : R
deriving DecidableEq, Repr

namespace FractionPair

variable {R S : Type*}

/-- The neutral pair for adding fractions. -/
def unit [Zero R] [One R] : FractionPair R := ⟨0, 1⟩

/-- Add two pairs by cross-multiplication, without testing or dividing by a denominator. -/
def combine [Add R] [Mul R] (p q : FractionPair R) : FractionPair R :=
  ⟨p.numerator * q.denominator + q.numerator * p.denominator,
    p.denominator * q.denominator⟩

/-- Fold a finite list of fractions by cross-multiplication. -/
def sum [Zero R] [One R] [Add R] [Mul R] (ps : List (FractionPair R)) : FractionPair R :=
  ps.foldr combine unit

/-- Apply a function separately to a numerator and its denominator. -/
def map (f : R → S) (p : FractionPair R) : FractionPair S :=
  ⟨f p.numerator, f p.denominator⟩

/-- Evaluate an unnormalized pair using the supplied division operation. -/
def value [Div R] (p : FractionPair R) : R := p.numerator / p.denominator

@[ext]
theorem ext {p q : FractionPair R} (hnum : p.numerator = q.numerator)
    (hden : p.denominator = q.denominator) : p = q := by
  cases p
  cases q
  simp_all

section CommSemiring

variable [CommSemiring R]

@[simp]
theorem unit_numerator : (unit : FractionPair R).numerator = 0 := rfl

@[simp]
theorem unit_denominator : (unit : FractionPair R).denominator = 1 := rfl

@[simp]
theorem combine_numerator (p q : FractionPair R) :
    (combine p q).numerator =
      p.numerator * q.denominator + q.numerator * p.denominator := rfl

@[simp]
theorem combine_denominator (p q : FractionPair R) :
    (combine p q).denominator = p.denominator * q.denominator := rfl

/-- Cross-multiplication is associative, including when denominators vanish. -/
theorem combine_assoc (p q r : FractionPair R) :
    combine (combine p q) r = combine p (combine q r) := by
  apply ext <;> simp only [combine_numerator, combine_denominator] <;> ring

/-- Cross-multiplication is commutative, including when denominators vanish. -/
theorem combine_comm (p q : FractionPair R) : combine p q = combine q p := by
  apply ext <;> simp [add_comm, mul_comm]

@[simp]
theorem unit_combine (p : FractionPair R) : combine unit p = p := by
  apply ext <;> simp

@[simp]
theorem combine_unit (p : FractionPair R) : combine p unit = p := by
  rw [combine_comm, unit_combine]

@[simp]
theorem sum_nil : sum ([] : List (FractionPair R)) = unit := rfl

@[simp]
theorem sum_cons (p : FractionPair R) (ps : List (FractionPair R)) :
    sum (p :: ps) = combine p (sum ps) := rfl

@[simp]
theorem sum_singleton (p : FractionPair R) : sum [p] = p := by
  simp

/-- Appending lists combines their already-folded pairs. -/
theorem sum_append (ps qs : List (FractionPair R)) :
    sum (ps ++ qs) = combine (sum ps) (sum qs) := by
  induction ps with
  | nil => simp
  | cons p ps ih => simp [ih, combine_assoc]

/-- Folding each group first gives the same pair as folding the flattened list. -/
theorem sum_flatten (groups : List (List (FractionPair R))) :
    sum groups.flatten = sum (groups.map sum) := by
  induction groups with
  | nil => rfl
  | cons ps groups ih => simp [sum_append, ih]

/-- Reordering terms does not change either component of their folded pair. -/
theorem sum_eq_of_perm {ps qs : List (FractionPair R)} (h : ps.Perm qs) :
    sum ps = sum qs := by
  induction h with
  | nil => rfl
  | cons p _ ih => simpa only [sum_cons] using congrArg (combine p) ih
  | swap p q ps =>
    simp only [sum_cons, ← combine_assoc, combine_comm q p]
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The folded denominator is the product of all input denominators. -/
theorem sum_denominator (ps : List (FractionPair R)) :
    (sum ps).denominator = (ps.map denominator).prod := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [ih]

/-- Nonzero input denominators give a nonzero folded denominator in a nontrivial semiring
without zero divisors. -/
theorem sum_denominator_ne_zero [NoZeroDivisors R] [Nontrivial R]
    (ps : List (FractionPair R)) (hden : ∀ p ∈ ps, p.denominator ≠ 0) :
    (sum ps).denominator ≠ 0 := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [sum_cons, combine_denominator]
    exact mul_ne_zero (hden p List.mem_cons_self)
      (ih fun q hq => hden q (List.mem_cons_of_mem p hq))

/-- The relation of a numerator to its denominator is preserved by combining pairs, with
the two scalar factors added. This identity does not divide by either denominator. -/
theorem combine_numerator_eq_add_mul_denominator (p q : FractionPair R) (h k : R)
    (hp : p.numerator = h * p.denominator) (hq : q.numerator = k * q.denominator) :
    (combine p q).numerator = (h + k) * (combine p q).denominator := by
  simp only [combine_numerator, combine_denominator, hp, hq]
  ring

/-- If each numerator is a scalar times its denominator, the folded numerator is the sum of
those scalars times the folded denominator. No denominator needs to be nonzero. -/
theorem sum_map_numerator_eq_sum_mul_denominator {ι : Type*} (is : List ι)
    (f : ι → FractionPair R) (h : ι → R)
    (hnum : ∀ i ∈ is, (f i).numerator = h i * (f i).denominator) :
    (sum (is.map f)).numerator = (is.map h).sum * (sum (is.map f)).denominator := by
  induction is with
  | nil => simp
  | cons i is ih =>
    have hi := hnum i List.mem_cons_self
    have hrest : ∀ j ∈ is, (f j).numerator = h j * (f j).denominator :=
      fun j hj => hnum j (List.mem_cons_of_mem i hj)
    simp only [List.map_cons, sum_cons, List.sum_cons]
    exact combine_numerator_eq_add_mul_denominator (f i) (sum (is.map f)) (h i)
      (is.map h).sum hi (ih hrest)

/-- Regrouped denominator-cleared identities imply a global identity, including when some
block denominators are zero. The group indices allow different helper values for equal blocks. -/
theorem sum_flatten_numerator_eq_sum_mul_denominator {ι : Type*} (is : List ι)
    (groups : ι → List (FractionPair R)) (h : ι → R)
    (hnum : ∀ i ∈ is, (sum (groups i)).numerator = h i * (sum (groups i)).denominator) :
    (sum (is.map groups).flatten).numerator =
      (is.map h).sum * (sum (is.map groups).flatten).denominator := by
  rw [sum_flatten, List.map_map]
  exact sum_map_numerator_eq_sum_mul_denominator is (fun i => sum (groups i)) h hnum

/-- A zero total of the helper values forces the global cleared numerator to vanish. -/
theorem sum_flatten_numerator_eq_zero {ι : Type*} (is : List ι)
    (groups : ι → List (FractionPair R)) (h : ι → R)
    (hnum : ∀ i ∈ is, (sum (groups i)).numerator = h i * (sum (groups i)).denominator)
    (htotal : (is.map h).sum = 0) : (sum (is.map groups).flatten).numerator = 0 := by
  rw [sum_flatten_numerator_eq_sum_mul_denominator is groups h hnum, htotal, zero_mul]

/-- A ring homomorphism preserves cross-multiplication. -/
theorem map_combine [CommSemiring S] (f : R →+* S) (p q : FractionPair R) :
    map f (combine p q) = combine (map f p) (map f q) := by
  apply ext <;> simp [map, map_add, map_mul]

/-- A ring homomorphism commutes with the complete pair fold. -/
theorem map_sum [CommSemiring S] (f : R →+* S) (ps : List (FractionPair R)) :
    map f (sum ps) = sum (ps.map (map f)) := by
  induction ps with
  | nil => apply ext <;> simp [map]
  | cons p ps ih => simp only [sum_cons, List.map_cons, map_combine, ih]

end CommSemiring

section Field

variable [Field R]

/-- At nonzero denominators, the cross-product pair evaluates to the sum of its inputs. -/
theorem value_combine (p q : FractionPair R) (hp : p.denominator ≠ 0)
    (hq : q.denominator ≠ 0) : value (combine p q) = value p + value q := by
  simp only [value, combine_numerator, combine_denominator]
  simpa only [mul_comm] using (div_add_div p.numerator q.numerator hp hq).symm

/-- With nonzero input denominators, evaluating the fold gives the sum of input fractions. -/
theorem value_sum (ps : List (FractionPair R)) (hden : ∀ p ∈ ps, p.denominator ≠ 0) :
    value (sum ps) = (ps.map value).sum := by
  induction ps with
  | nil => simp [value]
  | cons p ps ih =>
    have hrest : ∀ q ∈ ps, q.denominator ≠ 0 :=
      fun q hq => hden q (List.mem_cons_of_mem p hq)
    simp only [sum_cons, List.map_cons, List.sum_cons]
    rw [value_combine p (sum ps) (hden p List.mem_cons_self)
      (sum_denominator_ne_zero ps hrest), ih hrest]

end Field

end FractionPair
