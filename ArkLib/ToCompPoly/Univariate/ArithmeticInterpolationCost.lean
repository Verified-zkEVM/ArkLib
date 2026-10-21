/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ToCompPoly.Univariate.ArithmeticInterpolation
public import ArkLib.ToCompPoly.Univariate.ArithmeticPolynomialCost

/-!
# Profiles of cached Lagrange interpolation

Inversions and cached-array requests follow the executed finite-index folds. Their counts
hold for arbitrary node and value arrays, including repeated nodes and zero values.
-/

@[expose] public section

namespace CompPoly.Arithmetic
open OracleComp OracleSpec

section Operations
variable {F : Type} [Zero F] [Add F] [Sub F] [Mul F] [Inv F] [DecidableEq F]

@[simp]
private theorem profileArithmetic_trimRaw_zero (p : CPolynomial.Raw F)
    (kind : ArithmeticCostKind) (hc : kind ≠ .coefficientRead)
    (he : kind ≠ .eq) (hm : kind ≠ .metadata) :
    (profileArithmetic (trimRaw p)).2 kind = 0 := by
  have h := profileArithmetic_trimRaw_le p kind
  simp only [hc, he, hm, false_or, ↓reduceIte] at h
  exact Nat.eq_zero_of_le_zero h

/-- A right fold with a constant cell profile sums that count and its control ticks. -/
theorem profileArithmetic_certifiedFoldr_of_constant {A B : Type} (f : A → B → B)
    (step : (a : A) → (b : B) → OracleComp (ArithmeticSpec F) {c : B // c = f a b})
    (xs : List A) (b : B) (kind : ArithmeticCostKind) (c : ℕ)
    (hstep : ∀ a b, (profileArithmetic (step a b)).2 kind = c) :
    (profileArithmetic (certifiedFoldr f step xs b)).2 kind =
      xs.length * c + if kind = .metadata then xs.length + 1 else 0 := by
  induction xs with
  | nil =>
    cases kind <;> simp [certifiedFoldr, arithmeticCost, ArithmeticOp.costKind]
  | cons x xs ih =>
    rw [profileArithmetic_certifiedFoldr_cons]
    cases kind <;>
      simp [hstep, ih, arithmeticCost, ArithmeticOp.costKind, Nat.add_mul]
    omega

/-- A uniform bound for each suffix-selected cell bounds the complete right-fold profile. -/
theorem profileArithmetic_certifiedFoldr_le {A B : Type} (f : A → B → B)
    (step : (a : A) → (b : B) → OracleComp (ArithmeticSpec F) {c : B // c = f a b})
    (xs : List A) (b : B) (kind : ArithmeticCostKind) (c : ℕ)
    (hstep : ∀ a (ys : List A), (profileArithmetic (step a (ys.foldr f b))).2 kind ≤ c) :
    (profileArithmetic (certifiedFoldr f step xs b)).2 kind ≤
      xs.length * c + if kind = .metadata then xs.length + 1 else 0 := by
  induction xs with
  | nil =>
    cases kind <;> simp [certifiedFoldr, arithmeticCost, ArithmeticOp.costKind]
  | cons x xs ih =>
    rw [profileArithmetic_certifiedFoldr_cons]
    have hs := hstep x xs
    cases kind <;>
      simp [arithmeticCost, ArithmeticOp.costKind, Nat.add_mul] at ih hs ⊢ <;> omega

@[simp]
private theorem profileArithmetic_mulRawFrom_zero (p q : CPolynomial.Raw F)
    (i : ℕ) (acc : CPolynomial.Raw F) (t : ℕ) (kind : ArithmeticCostKind)
    (ha : kind ≠ .add) (hm : kind ≠ .mul) (hc : kind ≠ .coefficientRead)
    (ht : kind ≠ .metadata) :
    (profileArithmetic (mulRawFrom p q i acc t)).2 kind = 0 := by
  induction t generalizing i acc with
  | zero => simp [mulRawFrom, arithmeticCost, ArithmeticOp.costKind, ht]
  | succ t ih =>
    simp [mulRawFrom, profileArithmetic_bind, profileArithmetic_smulRaw,
      profileArithmetic_addRaw, ih,
      arithmeticCost, ArithmeticOp.costKind, ha, hm, hc, ht]

end Operations

section Semiring
variable {F : Type} [Semiring F] [Sub F] [Inv F] [DecidableEq F]

@[simp]
private theorem profileArithmetic_mulRaw_zero (p q : CPolynomial.Raw F)
    (kind : ArithmeticCostKind) (ha : kind ≠ .add) (hm : kind ≠ .mul)
    (hc : kind ≠ .coefficientRead) (ht : kind ≠ .metadata) :
    (profileArithmetic (mulRaw p q)).2 kind = 0 := by
  simp [mulRaw, ha, hm, hc, ht]

end Semiring

section Field
variable {F : Type} [Field F] [DecidableEq F]

private theorem profileArithmetic_basisDivisor_inv (x y : F) :
    (profileArithmetic (basisDivisor x y)).2 .inv = 1 := by
  have htrim (p : CPolynomial.Raw F) : (profileArithmetic (trimRaw p)).2 .inv = 0 :=
    profileArithmetic_trimRaw_zero p .inv (by decide) (by decide) (by decide)
  simp [basisDivisor, profileArithmetic_constant, profileArithmetic_subPolynomial,
    profileArithmetic_mulPolynomial,
    profileArithmetic_negRaw, profileArithmetic_addRaw, htrim,
    arithmeticCost, ArithmeticOp.costKind]

private theorem profileArithmetic_basisListRaw_inv (nodes : Array F) {m : ℕ}
    (i : Fin m) (l : List (Fin m)) :
    (profileArithmetic (basisListRaw nodes i l)).2 .inv = l.length := by
  simp only [basisListRaw, profileArithmetic_bind_certified, profileArithmetic_pure, add_zero]
  apply (profileArithmetic_certifiedFoldr_of_constant _ _ _ _ .inv 1 ?_).trans (by simp)
  intro j acc
  simp [profileArithmetic_basisDivisor_inv,
    arithmeticCost, ArithmeticOp.costKind]

private theorem profileArithmetic_basis_inv (nodes : Array F) {m : ℕ} (i : Fin m) :
    (profileArithmetic (basis nodes i)).2 .inv = m - 1 := by
  have htrim (p : CPolynomial.Raw F) : (profileArithmetic (trimRaw p)).2 .inv = 0 :=
    profileArithmetic_trimRaw_zero p .inv (by decide) (by decide) (by decide)
  simp [basis, profileArithmetic_canonicalRaw, profileArithmetic_basisListRaw_inv, htrim,
    List.length_erase_of_mem (by simp : i ∈ List.finRange m)]

/-- Interpolation requests one inverse for every ordered pair of distinct indices. -/
theorem profileArithmetic_interpolate_inv (nodes values : Array F) (m : ℕ) :
    (profileArithmetic (interpolate nodes values m)).2 .inv = m * (m - 1) := by
  have htrim (p : CPolynomial.Raw F) : (profileArithmetic (trimRaw p)).2 .inv = 0 :=
    profileArithmetic_trimRaw_zero p .inv (by decide) (by decide) (by decide)
  simp only [interpolate, profileArithmetic_bind_certified, profileArithmetic_pure,
    profileArithmetic_canonicalRaw, Pi.add_apply, htrim, add_zero]
  apply (profileArithmetic_certifiedFoldr_of_constant _ _ _ _ .inv (m - 1) ?_).trans (by simp)
  intro i acc
  simp [profileArithmetic_basis_inv, profileArithmetic_addRaw,
    arithmeticCost, ArithmeticOp.costKind]

private theorem profileArithmetic_basisDivisor_cache (x y : F)
    (kind : ArithmeticCostKind) (hk : kind = .nodeRead ∨ kind = .valueRead) :
    (profileArithmetic (basisDivisor x y)).2 kind = 0 := by
  rcases hk with rfl | rfl <;>
    simp [basisDivisor, profileArithmetic_constant, profileArithmetic_subPolynomial,
    profileArithmetic_mulPolynomial,
      profileArithmetic_negRaw, profileArithmetic_addRaw, arithmeticCost, ArithmeticOp.costKind]

private theorem profileArithmetic_basisListRaw_cache (nodes : Array F) {m : ℕ}
    (i : Fin m) (l : List (Fin m)) (kind : ArithmeticCostKind)
    (hk : kind = .nodeRead ∨ kind = .valueRead) :
    (profileArithmetic (basisListRaw nodes i l)).2 kind =
      l.length * if kind = .nodeRead then 2 else 0 := by
  have hm : kind ≠ .metadata := by rcases hk with rfl | rfl <;> decide
  simp only [basisListRaw, profileArithmetic_bind_certified, profileArithmetic_pure, add_zero]
  apply (profileArithmetic_certifiedFoldr_of_constant _ _ _ _ kind
    (if kind = .nodeRead then 2 else 0) ?_).trans (by simp [hm])
  intro j acc
  rcases hk with rfl | rfl <;>
    simp [profileArithmetic_basisDivisor_cache, arithmeticCost, ArithmeticOp.costKind]

private theorem profileArithmetic_basis_cache (nodes : Array F) {m : ℕ} (i : Fin m)
    (kind : ArithmeticCostKind) (hk : kind = .nodeRead ∨ kind = .valueRead) :
    (profileArithmetic (basis nodes i)).2 kind =
      (m - 1) * if kind = .nodeRead then 2 else 0 := by
  rcases hk with rfl | rfl <;>
    simp [basis, profileArithmetic_canonicalRaw, profileArithmetic_basisListRaw_cache,
      List.length_erase_of_mem (by simp : i ∈ List.finRange m)]

private theorem profileArithmetic_interpolate_cache (nodes values : Array F) (m : ℕ)
    (kind : ArithmeticCostKind) (hk : kind = .nodeRead ∨ kind = .valueRead) :
    (profileArithmetic (interpolate nodes values m)).2 kind =
      m * if kind = .nodeRead then (m - 1) * 2 else 1 := by
  have htrim (p : CPolynomial.Raw F) : (profileArithmetic (trimRaw p)).2 kind = 0 := by
    rcases hk with rfl | rfl <;> simp
  simp only [interpolate, profileArithmetic_bind_certified, profileArithmetic_pure,
    profileArithmetic_canonicalRaw, Pi.add_apply, htrim, add_zero]
  have hm : kind ≠ .metadata := by rcases hk with rfl | rfl <;> decide
  apply (profileArithmetic_certifiedFoldr_of_constant _ _ _ _ kind
    (if kind = .nodeRead then (m - 1) * 2 else 1) ?_).trans (by simp [hm])
  intro i acc
  rcases hk with rfl | rfl <;>
    simp [profileArithmetic_basis_cache, profileArithmetic_addRaw, arithmeticCost,
      ArithmeticOp.costKind]

/-- Each Lagrange factor reads its two cached nodes once. -/
theorem profileArithmetic_interpolate_nodeRead (nodes values : Array F) (m : ℕ) :
    (profileArithmetic (interpolate nodes values m)).2 .nodeRead = 2 * m * (m - 1) := by
  simpa [Nat.mul_comm, Nat.mul_left_comm] using
    profileArithmetic_interpolate_cache nodes values m .nodeRead (Or.inl rfl)

/-- Interpolation reads each cached sample value once. -/
theorem profileArithmetic_interpolate_valueRead (nodes values : Array F) (m : ℕ) :
    (profileArithmetic (interpolate nodes values m)).2 .valueRead = m := by
  simpa using profileArithmetic_interpolate_cache nodes values m .valueRead (Or.inr rfl)

end Field
end CompPoly.Arithmetic
