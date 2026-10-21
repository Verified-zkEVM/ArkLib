/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finsupp.Weight

/-!
# Local variables and weights for hidden-derivative interpolation

After translating a differential polynomial to an agreement point, the hidden-derivative argument
works with polynomials in the following local variables:

* `localT d`, the displacement `T`;
* `localU d = localE d`, one auxiliary slot, called `U` before the hidden-derivative rewrite and
  `E` (the hidden error) afterwards;
* `localY j` for `j : Fin d`, the visible jet `Y_(j+1)`.

Two weights on these variables govern the local constraints. The contact weight gives `T`
weight one, `E` weight `d`, and every visible jet weight zero, so the monomial `T^i E^b Y^c` has
contact order `i + d * b`. The `T`-weight counts only the exponent of `T`. The jet weights
`localFirstJetWeight`, `localHigherJetWeight`, `localDerivativeJetWeight`, and
`localJetDegreeWeight` measure the visible jets.

For `d > 0`, `localExponentCoordinatesEquiv` identifies a local exponent with its `T`, `U`, and
`Y₁` degrees and the degree vector of `Y₂, ..., Y_d`. The weight lemmas
`weight_localFirstJetWeight`, `weight_localHigherJetWeight`, and `weight_localJetDegreeWeight`
compute the jet weights in these coordinates, and `localContactOrder_eq` computes the contact
order.

## References

* [Brakensiek, J., Chen, Y., Putterman, A., Zhang, Z., and Zheng, K. Z., *Algorithmic List
  Decoding of Reed–Solomon Codes up to Capacity in the Low-Rate Regime*][BCPZZ26], Section 3.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon.HiddenDerivative

variable {d : ℕ}

/-- Variables of a local expansion: `none` is `T`, `some none` is the auxiliary slot, and
`some (some j)` is the visible jet `Y_(j+1)`. -/
abbrev LocalVariable (d : ℕ) := Option (Option (Fin d))

/-- Polynomials in `T`, one auxiliary variable, and the visible jets `Y₁, ..., Y_d`. -/
abbrev LocalPolynomial (R : Type*) [CommSemiring R] (d : ℕ) :=
  MvPolynomial (LocalVariable d) R

/-- The local displacement variable `T`. -/
def localT (d : ℕ) : LocalVariable d := none

/-- The shared auxiliary slot. -/
def localAux (d : ℕ) : LocalVariable d := some none

/-- The auxiliary slot before it is rewritten in terms of the hidden error. -/
abbrev localU (d : ℕ) : LocalVariable d := localAux d

/-- The auxiliary slot after the rewrite, where it holds the hidden error. -/
abbrev localE (d : ℕ) : LocalVariable d := localAux d

/-- The local variable for the visible jet `Y_(j+1)`. -/
def localY {d : ℕ} (j : Fin d) : LocalVariable d := some (some j)

/-- Contact weights: `T` has weight one, `E` has weight `d`, and visible jets have weight zero. -/
def localContactWeight (d : ℕ) : LocalVariable d → ℕ
  | none => 1
  | some none => d
  | some (some _) => 0

/-- The contact weight of `T` is `1`. -/
@[simp]
theorem localContactWeight_T (d : ℕ) : localContactWeight d (localT d) = 1 := rfl

/-- The contact weight of `E` is `d`. -/
@[simp]
theorem localContactWeight_E (d : ℕ) : localContactWeight d (localE d) = d := rfl

/-- The contact weight of a visible jet is `0`. -/
@[simp]
theorem localContactWeight_Y (j : Fin d) : localContactWeight d (localY j) = 0 := rfl

/-- The contact order of a local monomial: `T^i E^b Y^c` has contact order `i + d * b`. -/
def localContactOrder (d : ℕ) (e : LocalVariable d →₀ ℕ) : ℕ :=
  Finsupp.weight (localContactWeight d) e

/-- The weight that counts only the exponent of `T`. -/
def localTWeight (d : ℕ) : LocalVariable d → ℕ
  | none => 1
  | some _ => 0

/-- The `T`-weight of `T` is `1`. -/
@[simp]
theorem localTWeight_T (d : ℕ) : localTWeight d (localT d) = 1 := rfl

/-- The `T`-weight of `E` is `0`. -/
@[simp]
theorem localTWeight_E (d : ℕ) : localTWeight d (localE d) = 0 := rfl

/-- The `T`-weight of a visible jet is `0`. -/
@[simp]
theorem localTWeight_Y (j : Fin d) : localTWeight d (localY j) = 0 := rfl

/-- The `T`-weight of an exponent is its `T` exponent. -/
theorem weight_localTWeight (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (localTWeight d) e = e (localT d) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp), Fintype.sum_option]
  simp [localTWeight, localT]

/-! ### Jet weights and degrees -/

/-- The weight counting the exponent of the visible jet `Y₁ = localY 0`. It is zero on every
variable when `d = 0`. -/
def localFirstJetWeight (d : ℕ) : LocalVariable d → ℕ
  | some (some j) => if j.val = 0 then 1 else 0
  | _ => 0

/-- The higher-jet weight on local variables: `Y_(j+1) = localY j` has weight `j`, and `T`, `U`,
and `Y₁` have weight zero. -/
def localHigherJetWeight (d : ℕ) : LocalVariable d → ℕ
  | some (some j) => j.val
  | _ => 0

/-- The derivative-order weight on local variables: `Y_(j+1) = localY j` has weight `j + 1`, and
`T` and `U` have weight zero. Unlike `localHigherJetWeight` it charges `Y₁`. -/
def localDerivativeJetWeight (d : ℕ) : LocalVariable d → ℕ
  | some (some j) => j.val + 1
  | _ => 0

/-- The weight counting every variable except `T`, so that `e.weight (localJetDegreeWeight d)` is
the total degree of `e` in the auxiliary slot and the visible jets. -/
def localJetDegreeWeight (d : ℕ) : LocalVariable d → ℕ
  | none => 0
  | some _ => 1

/-- Contact order is the `T` exponent plus `d` times the `E` exponent. -/
theorem localContactOrder_eq (e : LocalVariable d →₀ ℕ) :
    localContactOrder d e = e (localT d) + d * e (localE d) := by
  simp [localContactOrder, Finsupp.weight_eq_sum, Fintype.sum_option, localContactWeight, localT,
    localE, localAux, mul_comm]

/-! ### Exponent coordinates -/

private theorem sum_fin_eq_zero_add_sum_succ {M : Type*} [AddCommMonoid M] (hd : 0 < d)
    (f : Fin d → M) :
    ∑ j, f j = f ⟨0, hd⟩ + ∑ i : Fin (d - 1), f ⟨i.val + 1, by omega⟩ := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  exact Fin.sum_univ_succ f

/-- For `d > 0`, a local exponent is determined by its `T`, `U`, and `Y₁` degrees and the degrees
of `Y₂, ..., Y_d`, where coordinate `i : Fin (d - 1)` of the last component is the degree of
`Y_(i+2) = localY ⟨i + 1, _⟩`. The hypothesis `0 < d` provides `Y₁`; for `d = 0` there is no
visible jet. -/
def localExponentCoordinatesEquiv (hd : 0 < d) :
    (LocalVariable d →₀ ℕ) ≃ ℕ × ℕ × ℕ × (Fin (d - 1) → ℕ) where
  toFun e := (e (localT d), e (localU d), e (localY ⟨0, hd⟩),
    fun i => e (localY ⟨i.val + 1, by omega⟩))
  invFun p := Finsupp.equivFunOnFinite.symm fun
    | none => p.1
    | some none => p.2.1
    | some (some j) => if h : j.val = 0 then p.2.2.1 else p.2.2.2 ⟨j.val - 1, by omega⟩
  left_inv e := by
    ext v
    rcases v with _ | _ | ⟨j, hj⟩
    · rfl
    · rfl
    · simp only [Finsupp.coe_equivFunOnFinite_symm]
      split_ifs with h
      · subst h; rfl
      · simp only [localY]
        congr 3
        exact Fin.ext (Nat.sub_add_cancel (Nat.pos_of_ne_zero h))
  right_inv p := by
    obtain ⟨t, u, b, c⟩ := p
    simp only [localT, localU, localAux, localY, Finsupp.coe_equivFunOnFinite_symm,
      ↓reduceDIte, Nat.add_one_ne_zero, Nat.add_sub_cancel]

/-- The coordinates of an exponent are its `T`, `U`, `Y₁` exponents and its exponents of
`Y₂, ..., Y_d`. -/
@[simp]
theorem localExponentCoordinatesEquiv_apply (hd : 0 < d) (e : LocalVariable d →₀ ℕ) :
    localExponentCoordinatesEquiv hd e = (e (localT d), e (localU d), e (localY ⟨0, hd⟩),
      fun i => e (localY ⟨i.val + 1, by omega⟩)) :=
  rfl

/-- The `Y₁` weight of an exponent is its `Y₁` coordinate. -/
theorem weight_localFirstJetWeight (hd : 0 < d) (e : LocalVariable d →₀ ℕ) :
    e.weight (localFirstJetWeight d) = e (localY ⟨0, hd⟩) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, localFirstJetWeight,
    sum_fin_eq_zero_add_sum_succ hd, localY]

/-- The higher-jet weight of an exponent is the weighted sum `∑ i, (i + 1) c_i` of its
higher-jet coordinates. -/
theorem weight_localHigherJetWeight (hd : 0 < d) (e : LocalVariable d →₀ ℕ) :
    e.weight (localHigherJetWeight d) =
      ∑ i : Fin (d - 1), (i.val + 1) * e (localY ⟨i.val + 1, by omega⟩) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, localHigherJetWeight,
    sum_fin_eq_zero_add_sum_succ hd, localY, mul_comm]

/-- The local jet degree of an exponent is its `U` degree plus its `Y₁` degree plus the sum of its
higher-jet coordinates. -/
theorem weight_localJetDegreeWeight (hd : 0 < d) (e : LocalVariable d →₀ ℕ) :
    e.weight (localJetDegreeWeight d) = e (localU d) + e (localY ⟨0, hd⟩) +
      ∑ i : Fin (d - 1), e (localY ⟨i.val + 1, by omega⟩) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, localJetDegreeWeight,
    sum_fin_eq_zero_add_sum_succ hd, localY, localU, localAux, add_assoc]

end ReedSolomon.HiddenDerivative
