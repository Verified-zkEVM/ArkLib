/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.JetPrefix

/-!
# Descent in a jet variable

The recursion of [Kop15] for polynomial differential equations repeatedly replaces an equation `Q`
by a partial derivative of `Q` in its highest active jet variable `Y_s`. This file proves the degree
and nonvanishing facts that make this recursion work, for one derivative (the separant) and for the
full descent `∂^t Q / ∂Y_s^t`, where `t` is the degree of `Q` in `Y_s`.

The degree bounds hold over every commutative semiring. In particular, the full descent never
depends on `Y_s`, and if `Y_s` was the highest active jet of `Q`, every jet variable on which the
full descent depends has order below `s`. Only nonvanishing needs more: `F` has no zero divisors
and every positive integer up to the degree in `Y_s` is nonzero in `F`
(`JetDegreeCastsNeZero Q s`). Both inputs are needed: over `ZMod 2` the derivative of `Y_s ^ 2`
is `2 * Y_s = 0`, and over `ZMod 4` the derivative of `2 * Y_s ^ 2` is `4 * Y_s = 0`.

## Main statements

* `JetDegreeCastsNeZero`: every positive integer up to `jetDegree Q s` is nonzero in `F`, with
  `jetDegreeCastsNeZero_of_ringChar` for the usual characteristic guard and
  `jetDegreeCastsNeZero_of_jetTotalDegree_charGuard` for a total-degree bound.
* `characteristic_bounds_of_max`: split a joint cutoff into total-degree and pivot bounds.
* `jetDegree_separant_le_sub_one`, `jetDegree_separant_eq_sub_one` and `separant_ne_zero`: one
  derivative in `Y_s`.
* `jetDerivative`: the `a`-fold partial derivative in `Y_s`, with
  `jetDegree_jetDerivative_eq_sub` and `jetDerivative_ne_zero`.
* `derivativeDescent`: the `t`-fold derivative, where `t = jetDegree Q s`.
  `jetDegree_derivativeDescent_eq_zero` and `active_lt_of_derivativeDescent` hold in every
  characteristic; `derivativeDescent_ne_zero` needs the cast hypothesis.
* `derivativeDescent_spec_of_highestActiveJet_eq_some`: the descent from the computed highest
  active jet is nonzero and depends only on jets of lower order.

## References

* [Kop15]
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

variable {F : Type*} {d : ℕ} [CommSemiring F]

/-! ### The cast hypothesis -/

/-- Every positive integer `k ≤ jetDegree Q s` is nonzero in `F`.

This is the hypothesis under which differentiating `Q` in `Y_s` up to `jetDegree Q s` times loses
exactly one degree in `Y_s` per derivative: the `k`-th derivative multiplies the leading
coefficient by the current degree `jetDegree Q s - k + 1`. It holds in characteristic zero, and in
characteristic `p > 0` when `jetDegree Q s < p` (see `jetDegreeCastsNeZero_of_ringChar`). It holds
trivially when `Q` does not depend on `Y_s`. -/
def JetDegreeCastsNeZero (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) : Prop :=
  ∀ k : ℕ, 0 < k → k ≤ jetDegree Q s → (k : F) ≠ 0

/-- The usual characteristic guard implies `JetDegreeCastsNeZero`. The disjunct
`ringChar F = 0` covers characteristic zero. -/
theorem jetDegreeCastsNeZero_of_ringChar {Q : DifferentialPolynomial F d} {s : Fin (d + 1)}
    (h : ringChar F = 0 ∨ jetDegree Q s < ringChar F) : JetDegreeCastsNeZero Q s :=
  fun _ hk hkt ↦ natCast_ne_zero_of_ringChar_eq_zero_or_lt h hk hkt

/-- A total jet-degree bound and characteristic guard give the cast condition at every jet. -/
theorem jetDegreeCastsNeZero_of_jetTotalDegree_charGuard {Q : DifferentialPolynomial F d}
    {ν : ℕ} (hdegree : jetTotalDegree Q ≤ ν)
    (hchar : ringChar F = 0 ∨ ν < ringChar F) :
    ∀ s, JetDegreeCastsNeZero Q s := by
  intro s
  apply jetDegreeCastsNeZero_of_ringChar
  exact hchar.imp_right (fun hc ↦
    (jetDegree_le_total Q s).trans_lt (hdegree.trans_lt hc))

/-- A joint characteristic cutoff yields separate total-degree and pivot bounds. -/
theorem characteristic_bounds_of_max {ν K : ℕ}
    (hchar : ringChar F = 0 ∨ max (K - 1) ν < ringChar F) :
    (ringChar F = 0 ∨ ν < ringChar F) ∧ (ringChar F = 0 ∨ K ≤ ringChar F) := by
  constructor
  · exact hchar.imp_right (Nat.le_max_right (K - 1) ν |>.trans_lt)
  · apply hchar.imp_right
    intro hc
    have hpred : K - 1 < ringChar F := (Nat.le_max_left (K - 1) ν).trans_lt hc
    omega

/-- `JetDegreeCastsNeZero` passes to any polynomial of no larger degree in `Y_s`. -/
theorem JetDegreeCastsNeZero.mono {Q Q' : DifferentialPolynomial F d} {s : Fin (d + 1)}
    (h : JetDegreeCastsNeZero Q s) (hle : jetDegree Q' s ≤ jetDegree Q s) :
    JetDegreeCastsNeZero Q' s :=
  fun k hk hkt ↦ h k hk (hkt.trans hle)

/-- If `Q` depends on `Y_s`, the cast hypothesis gives `(jetDegree Q s : F) ≠ 0`, the input of a
single separant step. -/
theorem JetDegreeCastsNeZero.natCast_jetDegree_ne_zero {Q : DifferentialPolynomial F d}
    {s : Fin (d + 1)} (h : JetDegreeCastsNeZero Q s) (hs : DependsOnJet Q s) :
    (jetDegree Q s : F) ≠ 0 :=
  h _ hs le_rfl

/-- The cast hypothesis in the form used by
`MvPolynomial.degreeOf_iterate_pderiv_eq_sub_of_natCast_ne_zero`. -/
private theorem JetDegreeCastsNeZero.sub {Q : DifferentialPolynomial F d} {s : Fin (d + 1)}
    (h : JetDegreeCastsNeZero Q s) {a : ℕ} (ha : a ≤ jetDegree Q s) :
    ∀ k < a, ((Q.degreeOf (some s) - k : ℕ) : F) ≠ 0 :=
  fun k hk ↦ h _ (by rw [jetDegree] at ha; omega) (Nat.sub_le _ _)

/-! ### One derivative -/

/-- A separant does not increase the degree in any jet variable. Holds over every commutative
semiring. -/
theorem jetDegree_separant_le (Q : DifferentialPolynomial F d) (s j : Fin (d + 1)) :
    jetDegree (separant Q s) j ≤ jetDegree Q j :=
  MvPolynomial.degreeOf_pderiv_le (some s) (some j) Q

/-- The separant in `Y_s` has degree at most `jetDegree Q s - 1` in `Y_s`, in every
characteristic. Equality can fail: over `ZMod 2`, the separant of `Y_s ^ 2` is zero. -/
theorem jetDegree_separant_le_sub_one (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) :
    jetDegree (separant Q s) s ≤ jetDegree Q s - 1 :=
  MvPolynomial.degreeOf_pderiv_le_sub_one (some s) Q

/-- If `F` has no zero divisors and `(jetDegree Q s : F) ≠ 0`, the separant in `Y_s` has degree
exactly `jetDegree Q s - 1` in `Y_s`.

The cast hypothesis implies that `Q` depends on `Y_s`. It is needed: over `ZMod 2` the separant of
`Y_s ^ 2` is zero. `NoZeroDivisors` is needed: over `ZMod 4` the separant of `2 * Y_s ^ 2` is
zero although `(2 : ZMod 4) ≠ 0`. -/
theorem jetDegree_separant_eq_sub_one [NoZeroDivisors F] (Q : DifferentialPolynomial F d)
    (s : Fin (d + 1)) (hcast : (jetDegree Q s : F) ≠ 0) :
    jetDegree (separant Q s) s = jetDegree Q s - 1 :=
  MvPolynomial.degreeOf_pderiv_eq_sub_one_of_natCast_ne_zero (some s) Q hcast

/-- If `F` has no zero divisors and `(jetDegree Q s : F) ≠ 0`, the separant in `Y_s` is nonzero.
The hypotheses are needed for the reasons given in `jetDegree_separant_eq_sub_one`. -/
theorem separant_ne_zero [NoZeroDivisors F] (Q : DifferentialPolynomial F d) (s : Fin (d + 1))
    (hcast : (jetDegree Q s : F) ≠ 0) : separant Q s ≠ 0 :=
  MvPolynomial.pderiv_ne_zero_of_natCast_ne_zero (some s) Q hcast

/-! ### Iterated derivatives -/

/-- The `a`-fold partial derivative of `Q` in the jet variable `Y_s`. -/
def jetDerivative (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (a : ℕ) :
    DifferentialPolynomial F d :=
  (MvPolynomial.pderiv (some s))^[a] Q

/-- `jetDerivative` is the iterate of `MvPolynomial.pderiv (some s)`. -/
theorem jetDerivative_eq_iterate (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (a : ℕ) :
    jetDerivative Q s a = (MvPolynomial.pderiv (some s))^[a] Q :=
  rfl

/-- Zero derivatives leave `Q` unchanged. -/
@[simp]
theorem jetDerivative_zero (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) :
    jetDerivative Q s 0 = Q :=
  rfl

/-- The `(a + 1)`-fold derivative is the separant of the `a`-fold derivative. -/
@[simp]
theorem jetDerivative_succ (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (a : ℕ) :
    jetDerivative Q s (a + 1) = separant (jetDerivative Q s a) s :=
  Function.iterate_succ_apply' _ _ _

/-- The first jet derivative is the separant. -/
theorem jetDerivative_one (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) :
    jetDerivative Q s 1 = separant Q s :=
  rfl

/-- `a` derivatives in `Y_s` lower the degree in `Y_s` by at least `a`, in every
characteristic. -/
theorem jetDegree_jetDerivative_le_sub (Q : DifferentialPolynomial F d) (s : Fin (d + 1))
    (a : ℕ) : jetDegree (jetDerivative Q s a) s ≤ jetDegree Q s - a :=
  MvPolynomial.degreeOf_iterate_pderiv_le_sub (some s) a Q

/-- Differentiating in one jet variable does not increase the degree in any jet variable. -/
theorem jetDegree_jetDerivative_le (Q : DifferentialPolynomial F d) (s j : Fin (d + 1))
    (a : ℕ) : jetDegree (jetDerivative Q s a) j ≤ jetDegree Q j :=
  MvPolynomial.degreeOf_iterate_pderiv_le (some s) (some j) a Q

/-- If `F` has no zero divisors and the cast hypothesis holds, then `a` derivatives in `Y_s`
lower the degree in `Y_s` by exactly `a`, in truncated subtraction.

For `a > jetDegree Q s` both sides are zero. The cast hypothesis is needed: over `ZMod 2`, the
separant of `Y_s ^ 2` is zero, of degree `0 ≠ 2 - 1`. -/
theorem jetDegree_jetDerivative_eq_sub [NoZeroDivisors F] (Q : DifferentialPolynomial F d)
    (s : Fin (d + 1)) (a : ℕ) (hcast : JetDegreeCastsNeZero Q s) :
    jetDegree (jetDerivative Q s a) s = jetDegree Q s - a := by
  rcases le_or_gt a (jetDegree Q s) with ha | ha
  · exact MvPolynomial.degreeOf_iterate_pderiv_eq_sub_of_natCast_ne_zero (some s) a Q
      (hcast.sub ha)
  · have := jetDegree_jetDerivative_le_sub Q s a
    omega

/-- If `Q ≠ 0`, `F` has no zero divisors, the cast hypothesis holds, and `a ≤ jetDegree Q s`,
then the `a`-fold derivative of `Q` in `Y_s` is nonzero. Differentiating more than
`jetDegree Q s` times gives zero in every characteristic. -/
theorem jetDerivative_ne_zero [NoZeroDivisors F] {Q : DifferentialPolynomial F d} (hQ : Q ≠ 0)
    (s : Fin (d + 1)) {a : ℕ} (ha : a ≤ jetDegree Q s) (hcast : JetDegreeCastsNeZero Q s) :
    jetDerivative Q s a ≠ 0 :=
  MvPolynomial.iterate_pderiv_ne_zero_of_natCast_ne_zero (some s) a hQ (hcast.sub ha)

/-! ### Full descent -/

/-- The full descent of `Q` in `Y_s`: the derivative of order `jetDegree Q s` in `Y_s`. -/
def derivativeDescent (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) :
    DifferentialPolynomial F d :=
  jetDerivative Q s (jetDegree Q s)

/-- The full descent in `Y_s` does not depend on `Y_s`. This holds in every characteristic; in
positive characteristic the descent may be zero. -/
theorem jetDegree_derivativeDescent_eq_zero (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) :
    jetDegree (derivativeDescent Q s) s = 0 := by
  have := jetDegree_jetDerivative_le_sub Q s (jetDegree Q s)
  rw [Nat.sub_self] at this
  exact Nat.eq_zero_of_le_zero this

/-- The full descent in `Y_s` does not depend on `Y_s`, stated with `DependsOnJet`. -/
theorem not_dependsOnJet_derivativeDescent (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) :
    ¬DependsOnJet (derivativeDescent Q s) s := by
  rw [DependsOnJet, jetDegree_derivativeDescent_eq_zero]
  exact lt_irrefl 0

/-- If `Q ≠ 0`, `F` has no zero divisors and the cast hypothesis holds, the full descent of `Q`
in `Y_s` is nonzero.

`Q ≠ 0` suffices: if `Q` does not depend on `Y_s`, the descent is `Q`. The cast hypothesis is
needed: over `ZMod 2`, the full descent of `Y_s ^ 2` is zero. -/
theorem derivativeDescent_ne_zero [NoZeroDivisors F] {Q : DifferentialPolynomial F d}
    (hQ : Q ≠ 0) (s : Fin (d + 1)) (hcast : JetDegreeCastsNeZero Q s) :
    derivativeDescent Q s ≠ 0 :=
  jetDerivative_ne_zero hQ s le_rfl hcast

/-- The full descent does not increase the degree in any jet variable. -/
theorem jetDegree_derivativeDescent_le (Q : DifferentialPolynomial F d) (s j : Fin (d + 1)) :
    jetDegree (derivativeDescent Q s) j ≤ jetDegree Q j :=
  jetDegree_jetDerivative_le Q s j _

/-- If `Y_s` is the highest active jet of `Q`, every jet variable on which the full descent in
`Y_s` depends has order below `s`. This holds in every characteristic. -/
theorem active_lt_of_derivativeDescent {Q : DifferentialPolynomial F d} {s j : Fin (d + 1)}
    (hs : IsHighestActiveJet Q s) (hj : DependsOnJet (derivativeDescent Q s) j) : j < s := by
  rcases lt_trichotomy j s with hjs | rfl | hsj
  · exact hjs
  · exact (not_dependsOnJet_derivativeDescent Q j hj).elim
  · exact (hs.2 j hsj (lt_of_lt_of_le hj (jetDegree_derivativeDescent_le Q s j))).elim

/-- If `Y_s` is the highest active jet of `Q` and the full descent still has a highest active
jet `Y_j`, then `j < s`. This holds in every characteristic. -/
theorem highestActiveJet_derivativeDescent_lt {Q : DifferentialPolynomial F d}
    {s j : Fin (d + 1)} (hs : IsHighestActiveJet Q s)
    (hj : highestActiveJet (derivativeDescent Q s) = some j) : j < s :=
  active_lt_of_derivativeDescent hs (isHighestActiveJet_of_highestActiveJet_eq_some hj).1

/-- If `Y_s` is the computed highest active jet of `Q`, `F` has no zero divisors, and the cast
hypothesis holds at `s`, then the full descent in `Y_s` is nonzero and depends only on jet
variables of order below `s`.

`Q ≠ 0` is not assumed: it follows from `Q` depending on `Y_s`. -/
theorem derivativeDescent_spec_of_highestActiveJet_eq_some [NoZeroDivisors F]
    {Q : DifferentialPolynomial F d} {s : Fin (d + 1)} (hs : highestActiveJet Q = some s)
    (hcast : JetDegreeCastsNeZero Q s) :
    derivativeDescent Q s ≠ 0 ∧ ∀ j, DependsOnJet (derivativeDescent Q s) j → j < s := by
  have hhighest := isHighestActiveJet_of_highestActiveJet_eq_some hs
  have hQ : Q ≠ 0 := by
    rintro rfl
    have := hhighest.1
    simp [DependsOnJet, jetDegree] at this
  exact ⟨derivativeDescent_ne_zero hQ s hcast,
    fun _ hj ↦ active_lt_of_derivativeDescent hhighest hj⟩

end

end PolynomialDifferential
