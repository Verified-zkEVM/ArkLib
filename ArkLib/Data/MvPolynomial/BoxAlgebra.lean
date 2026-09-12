/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.BoxTruncation
public import Mathlib.Algebra.Ring.InjSurj

/-!
# Canonical executable parameter box algebra

Canonical sparse representatives carry truncated arithmetic and a commutative ring
structure. Coefficients need only form a commutative ring; this algebra is not treated
as a field.
-/

@[expose] public section

namespace CPoly.BoxAlgebra

open BoxTruncation

variable (r N : ℕ) (R : Type*) [CommRing R] [BEq R] [LawfulBEq R]

/-- Stored polynomial representatives fixed by coordinatewise box reduction. -/
abbrev Carrier := {p : CMvPolynomial r R // truncate N p = p}

variable {r N R}

/-- Reduce an arbitrary stored polynomial to its canonical representative. -/
def reduce (p : CMvPolynomial r R) : Carrier r N R :=
  ⟨truncate N p, truncate_idempotent N p⟩

instance : DecidableEq (Carrier r N R) := by
  letI : DecidableEq R := instDecidableEqOfLawfulBEq
  infer_instance

instance : BEq (Carrier r N R) := ⟨fun p q => decide (p = q)⟩
instance : LawfulBEq (Carrier r N R) where
  eq_of_beq := by intro p q h; exact of_decide_eq_true h
  rfl := by intro p; exact decide_eq_true rfl

@[ext] theorem ext (p q : Carrier r N R) (h : p.val = q.val) : p = q := Subtype.ext h

@[simp] theorem reduce_val (p : Carrier r N R) : reduce p.val = p := by
  apply ext
  exact p.property

theorem reduce_surjective : Function.Surjective (reduce (r := r) (N := N) (R := R)) :=
  fun p => ⟨p.val, reduce_val p⟩

instance : Zero (Carrier r N R) := ⟨reduce 0⟩
instance : One (Carrier r N R) := ⟨reduce 1⟩
instance : Add (Carrier r N R) := ⟨fun p q => reduce (p.val + q.val)⟩
instance : Mul (Carrier r N R) := ⟨fun p q => reduce (p.val * q.val)⟩
instance : Neg (Carrier r N R) := ⟨fun p => reduce (-p.val)⟩
instance : Sub (Carrier r N R) := ⟨fun p q => p + -q⟩
instance : NatCast (Carrier r N R) := ⟨fun n => reduce n⟩
instance : IntCast (Carrier r N R) := ⟨fun n => reduce n⟩
instance : SMul ℕ (Carrier r N R) := ⟨nsmulRec⟩
instance : SMul ℤ (Carrier r N R) := ⟨zsmulRec⟩
instance : Pow (Carrier r N R) ℕ := ⟨fun p n => npowRec n p⟩

@[simp] theorem reduce_zero : reduce (0 : CMvPolynomial r R) = (0 : Carrier r N R) := rfl
@[simp] theorem reduce_one : reduce (1 : CMvPolynomial r R) = (1 : Carrier r N R) := rfl

@[simp] theorem reduce_add (p q : CMvPolynomial r R) :
    reduce (p + q) = (reduce p + reduce q : Carrier r N R) := by
  apply ext
  exact (add_truncate N p q).symm

@[simp] theorem reduce_mul (p q : CMvPolynomial r R) :
    reduce (p * q) = (reduce p * reduce q : Carrier r N R) := by
  apply ext
  change mul N p q = mul N (truncate N p) (truncate N q)
  rw [mul_truncate_left, mul_truncate_right]

@[simp] theorem reduce_neg (p : CMvPolynomial r R) :
    reduce (-p) = (-reduce p : Carrier r N R) := by
  apply ext
  apply eq_iff_fromCMvPolynomial.mpr
  apply MvPolynomial.ext
  intro m
  change MvPolynomial.coeff m (fromCMvPolynomial (truncate N (-p))) =
    MvPolynomial.coeff m (fromCMvPolynomial (truncate N (-truncate N p)))
  simp only [coeff_semantics, CPoly.map_neg, MvPolynomial.coeff_neg]
  split_ifs <;> simp

@[simp] theorem reduce_sub (p q : CMvPolynomial r R) :
    reduce (p - q) = (reduce p - reduce q : Carrier r N R) := by
  change reduce (p - q) = reduce p + -reduce q
  rw [sub_eq_add_neg, reduce_add, reduce_neg]

theorem reduce_nsmul (n : ℕ) (p : CMvPolynomial r R) :
    reduce (n • p) = (n • reduce p : Carrier r N R) := by
  change reduce (n • p) = nsmulRec n (reduce p)
  induction n with
  | zero => rw [zero_nsmul]; rfl
  | succ n ih => rw [succ_nsmul, reduce_add, ih]; rfl

theorem reduce_zsmul (n : ℤ) (p : CMvPolynomial r R) :
    reduce (n • p) = (n • reduce p : Carrier r N R) := by
  change reduce (n • p) = zsmulRec nsmulRec n (reduce p)
  cases n with
  | ofNat n =>
    change reduce ((n : ℤ) • p) = nsmulRec n (reduce p)
    rw [natCast_zsmul]
    exact reduce_nsmul n p
  | negSucc n =>
    simp only [negSucc_zsmul, reduce_neg, reduce_nsmul, zsmulRec]
    rfl

theorem reduce_pow (p : CMvPolynomial r R) (n : ℕ) :
    reduce (p ^ n) = (reduce p ^ n : Carrier r N R) := by
  change reduce (p ^ n) = npowRec n (reduce p)
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih => rw [pow_succ, reduce_mul, ih]; rfl

instance : CommRing (Carrier r N R) :=
  reduce_surjective.commRing reduce reduce_zero reduce_one reduce_add reduce_mul
    reduce_neg reduce_sub reduce_nsmul reduce_zsmul reduce_pow (fun _ => rfl) (fun _ => rfl)

/-- The canonical projection is a ring homomorphism. -/
def projection : CMvPolynomial r R →+* Carrier r N R where
  toFun := reduce
  map_zero' := reduce_zero
  map_one' := reduce_one
  map_add' := reduce_add
  map_mul' := reduce_mul

/-- The canonical nilpotent parameter represented by the indicated variable. -/
def eps (i : Fin r) : Carrier r N R := reduce (CMvPolynomial.X i)

/-- Each parameter is nilpotent at the chosen coordinate precision. -/
theorem eps_pow (i : Fin r) : (eps i : Carrier r N R) ^ N = 0 := by
  change reduce (CMvPolynomial.X i) ^ N = reduce 0
  rw [← reduce_pow]
  apply ext
  apply eq_iff_fromCMvPolynomial.mpr
  apply MvPolynomial.ext
  intro m
  change MvPolynomial.coeff m (fromCMvPolynomial (truncate N (CMvPolynomial.X i ^ N))) =
    MvPolynomial.coeff m (fromCMvPolynomial (truncate N 0))
  have hp : fromCMvPolynomial ((CMvPolynomial.X i : CMvPolynomial r R) ^ N) =
      MvPolynomial.X i ^ N := by
    exact (map_pow (polyRingEquiv (n := r) (R := R)) _ _).trans
      (congrArg (fun p => p ^ N) (CMvPolynomial.fromCMvPolynomial_X i))
  rw [coeff_semantics, coeff_semantics, hp, CPoly.map_zero, MvPolynomial.coeff_zero]
  by_cases hm : ∀ j, m j < N
  · rw [if_pos hm, if_pos hm, MvPolynomial.coeff_X_pow, if_neg]
    intro he
    have hi := hm i
    rw [← he, Finsupp.single_eq_same] at hi
    exact Nat.lt_irrefl _ hi
  · simp [hm]

/-- Positive precision preserves the nontrivial constant coefficient ring. -/
theorem nontrivial_of_pos [Nontrivial R] (hN : 0 < N) : Nontrivial (Carrier r N R) := by
  apply nontrivial_of_ne (0 : Carrier r N R) 1
  intro h
  have hc := congrArg (fun p : Carrier r N R =>
    MvPolynomial.coeff 0 (fromCMvPolynomial p.val)) h
  change MvPolynomial.coeff 0 (fromCMvPolynomial (truncate N 0)) =
    MvPolynomial.coeff 0 (fromCMvPolynomial (truncate N 1)) at hc
  have hb : ∀ i : Fin r, (0 : Fin r →₀ ℕ) i < N := fun _ => hN
  simp only [coeff_semantics, if_pos hb, CPoly.map_zero, CPoly.map_one,
    MvPolynomial.coeff_zero, MvPolynomial.coeff_one] at hc
  exact zero_ne_one hc

instance [Nontrivial R] [Fact (0 < N)] : Nontrivial (Carrier r N R) :=
  nontrivial_of_pos Fact.out

end CPoly.BoxAlgebra
