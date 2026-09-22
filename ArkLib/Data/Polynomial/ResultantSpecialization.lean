/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Polynomial.Resultant.Basic

/-!
# Resultants with declared degrees under coefficient specialization

Let `φ : R →+* S` be a ring homomorphism and let `f, g : R[X]` have degrees at most `m` and `n`.
This file relates the value `φ (resultant f g m n)` to common roots, coprimality, and
separability of the mapped polynomials `f.map φ` and `g.map φ`. The declared degrees `m` and `n`
are fixed before `φ` is applied, so `φ` may lower the actual degree of `f` or `g`.

## Main statements

* `map_resultant_eq_zero_of_common_root`: a common root of `f.map φ` and `g.map φ` forces
  `φ (resultant f g m n) = 0`. Both `R` and `S` are arbitrary commutative rings.
* `eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero`: if
  `φ (resultant f f.derivative m (m - 1)) ≠ 0`, every root of `f.map φ` is a simple root.
* `natDegree_map_eq_of_resultant_derivative_padded_ne_zero`: the same hypothesis forces
  `(f.map φ).natDegree = m`. A specialization that lowers the degree of `f` therefore makes the
  padded derivative resultant vanish.
* `isCoprime_map_of_resultant_padded_ne_zero` and
  `separable_map_of_resultant_derivative_padded_ne_zero`: over a field target, a nonzero image of
  the resultant gives coprimality, and a nonzero image of the padded derivative resultant gives
  separability.
* `resultant_comm_sub_one`: `resultant g f (m - 1) m = resultant f g m (m - 1)`.

## Proof outline

Mathlib's `exists_mul_add_mul_eq_C_resultant` gives `p, q : R[X]` with
`f * p + g * q = C (resultant f g m n)`, provided `f.natDegree ≤ m`, `g.natDegree ≤ n` and
`m ≠ 0 ∨ n ≠ 0`. Mapping this identity through `φ` and evaluating at a common root gives the
first statement. Mapping it into a field and multiplying by the inverse of the constant gives
coprimality. The derivative statements take `g = f.derivative` and `n = m - 1`, which is a valid
degree bound because `f.derivative.natDegree ≤ f.natDegree - 1`. The bound need not be attained:
in characteristic `p` the derivative of `Y ^ p - Y` is `-1`. The actual-degree forms
`isCoprime_map_of_resultant_ne_zero` and `separable_map_of_resultant_derivative_ne_zero` in
`ArkLib.Data.Polynomial.FractionFieldResultant` are derived from the declared-degree forms here.

## Relation to the source definitions

The source defines `separableResultant A b := resultant A.derivative A (b - 1) b` for
`A : R[X][X]`, and `paddedDerivativeResultant A b` by the same formula for `A : R[X]`. This file
uses neither definition and writes `resultant f f.derivative m (m - 1)`, the argument order used
elsewhere on ArkLib main. The two orders give the same value: `resultant_comm` introduces the sign
`(-1) ^ (m * (m - 1))`, and `m * (m - 1)` is even (`resultant_comm_sub_one`). A source statement
about `separableResultant A b` at a point `w` is the case `R := F[X]`, `f := A`, `m := b`,
`φ := evalRingHom w` of the statements here.

## References

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`:

* `ArkLib/ToMathlib/Polynomial/SeparableResultant.lean`:
  `eval_derivative_ne_zero_of_separableResultant_eval_ne_zero`,
  `eval_derivative_ne_zero_of_separableResultant_map_ne_zero` and
  `specialization_separable_of_separableResultant_eval_ne_zero`;
* `ArkLib/ToMathlib/Polynomial/PaddedDerivativeResultantCommonRoot.lean`:
  `paddedDerivativeResultant_map_eq_zero_of_common_root`;
* `ArkLib/ToMathlib/Polynomial/DerivativeResultantDegree.lean`:
  `separableResultant_map_eq_zero_of_common_root`.

The source states these results separately for `R[X]` and `R[X][X]` and assumes `IsDomain` for
the rings involved. The statements here hold over any commutative rings and for any declared
degrees.

Not ported in this file: the total-degree bounds `natDegree_separableResultant_add_sq_le*` and
`natDegree_separableResultant_le_totalDegree*` of `DerivativeResultantDegree.lean`, which are in
`ArkLib.Data.Polynomial.ResultantDegree`; the entry point
`separableResultant_ne_zero_of_irreducible`, which is
`resultant_derivative_ne_zero_of_irreducible` in `ArkLib.Data.Polynomial.FractionFieldResultant`;
and the consumers `Ordinary/Factors/RootPresentation.lean` and `ContentExceptions.lean`.
-/

@[expose] public section

namespace Polynomial

variable {R S K : Type*} [CommRing R] [CommRing S] [Field K] {m n : ℕ}

/-- Swapping the arguments of a resultant with declared degrees `m` and `m - 1` does not change
its value. `resultant_comm` contributes the sign `(-1) ^ (m * (m - 1))`, and `m * (m - 1)` is
even for every natural number `m`, including `m = 0`. Consequently the source definition
`separableResultant A b = resultant A.derivative A (b - 1) b` equals
`resultant A A.derivative b (b - 1)`. -/
theorem resultant_comm_sub_one (f g : R[X]) (m : ℕ) :
    resultant g f (m - 1) m = resultant f g m (m - 1) := by
  rw [resultant_comm f g m (m - 1), (Nat.even_mul_pred_self m).neg_one_pow, one_mul]

/-- A common root of `f.map φ` and `g.map φ` forces `φ (resultant f g m n) = 0`.

The hypotheses `hf` and `hg` bound the degrees of `f` and `g` before `φ` is applied. They are
the hypotheses of the Bezout identity `f * p + g * q = C (resultant f g m n)`. The map `φ` may
lower either degree, including to `0`, and `m`, `n` stay fixed. The hypothesis `hmn` cannot be
dropped: `resultant f g 0 0 = 1`, since the Sylvester matrix is empty, but `f = g = 0` has every
point as a common root. `R` and `S` need not be domains or nontrivial; in the zero ring the
conclusion holds trivially. -/
theorem map_resultant_eq_zero_of_common_root (φ : R →+* S) (f g : R[X])
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (hmn : m ≠ 0 ∨ n ≠ 0) (u : S)
    (hfu : (f.map φ).eval u = 0) (hgu : (g.map φ).eval u = 0) :
    φ (resultant f g m n) = 0 := by
  obtain ⟨p, q, -, -, hbezout⟩ := exists_mul_add_mul_eq_C_resultant f g hf hg hmn
  have heval := congrArg (fun r : R[X] ↦ (r.map φ).eval u) hbezout
  simp only [Polynomial.map_add, Polynomial.map_mul, map_C, eval_add, eval_mul, eval_C, hfu, hgu,
    zero_mul, add_zero] at heval
  exact heval.symm

/-- If `φ (resultant f f.derivative m (m - 1)) ≠ 0`, every root `u` of `f.map φ` is a simple
root: the derivative of `f.map φ` does not vanish at `u`.

`hf` makes `m` a degree bound for `f`, and then `m - 1` is a degree bound for `f.derivative`.
`hm` is needed because for `m = 0` the resultant is `1`: a constant `f` with `φ (f.coeff 0) = 0`
maps to `0`, whose derivative vanishes everywhere. The derivative may have degree below `m - 1`,
as in small characteristic, where the derivative of `Y ^ p - Y` is `-1`. If `φ` lowers the
degree of `f` itself, the hypothesis `hres` fails
(`natDegree_map_eq_of_resultant_derivative_padded_ne_zero`). The zero polynomial has a vanishing
resultant for `0 < m`, so it is excluded by `hres`. `R` and `S` are arbitrary commutative rings.
-/
theorem eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero (φ : R →+* S)
    (f : R[X]) (hf : f.natDegree ≤ m) (hm : 0 < m)
    (hres : φ (resultant f f.derivative m (m - 1)) ≠ 0) (u : S)
    (hfu : (f.map φ).eval u = 0) : (f.map φ).derivative.eval u ≠ 0 := by
  intro hderivative
  refine hres (map_resultant_eq_zero_of_common_root φ f f.derivative hf
    ((natDegree_derivative_le f).trans (Nat.sub_le_sub_right hf 1)) (Or.inl hm.ne') u hfu ?_)
  rwa [← derivative_map]

/-- If `φ (resultant f f.derivative m (m - 1)) ≠ 0`, then `f.map φ` has degree exactly `m`.

If the degree of `f.map φ` were below `m`, its coefficient at `m` would vanish, so the
coefficient of its derivative at `m - 1` would vanish too, and a resultant whose inputs both have
degree below the declared degrees is zero. Hence the padded derivative resultant vanishes at
every specialization that lowers the degree of `f`; only the degree of the derivative may drop.
`hm` excludes `m = 0`, where the resultant is `1` for every constant `f`. -/
theorem natDegree_map_eq_of_resultant_derivative_padded_ne_zero (φ : R →+* S) (f : R[X])
    (hf : f.natDegree ≤ m) (hm : 0 < m)
    (hres : φ (resultant f f.derivative m (m - 1)) ≠ 0) : (f.map φ).natDegree = m := by
  rw [← resultant_map_map, ← derivative_map] at hres
  have hle : (f.map φ).natDegree ≤ m := natDegree_map_le.trans hf
  refine le_antisymm hle (not_lt.mp fun hlt ↦ hres ?_)
  rcases m with _ | _ | k
  · omega
  · rw [eq_C_of_natDegree_eq_zero (Nat.lt_one_iff.mp hlt)]
    simp
  · exact resultant_eq_zero_of_lt_lt _ _ _ _ hlt
      ((natDegree_derivative_le _).trans_lt (by omega))

/-- Over a field target, `φ (resultant f g m n) ≠ 0` makes `f.map φ` and `g.map φ` coprime.

The degree hypotheses concern `f` and `g` before `φ` is applied, so `φ` may lower either degree.
`hmn` excludes `m = n = 0`: then the resultant is `1`, while `0` and `0` are not coprime. -/
theorem isCoprime_map_of_resultant_padded_ne_zero (φ : R →+* K) (f g : R[X])
    (hf : f.natDegree ≤ m) (hg : g.natDegree ≤ n) (hmn : m ≠ 0 ∨ n ≠ 0)
    (hres : φ (resultant f g m n) ≠ 0) : IsCoprime (f.map φ) (g.map φ) := by
  obtain ⟨a, b, -, -, hab⟩ := exists_mul_add_mul_eq_C_resultant f g hf hg hmn
  have hmap := congrArg (Polynomial.map φ) hab
  simp only [Polynomial.map_add, Polynomial.map_mul, map_C] at hmap
  refine ⟨C (φ (resultant f g m n))⁻¹ * a.map φ, C (φ (resultant f g m n))⁻¹ * b.map φ, ?_⟩
  calc
    _ = C (φ (resultant f g m n))⁻¹ * (f.map φ * a.map φ + g.map φ * b.map φ) := by ring
    _ = 1 := by rw [hmap, ← C_mul, inv_mul_cancel₀ hres, C_1]

/-- Over a field target, `φ (resultant f f.derivative m (m - 1)) ≠ 0` makes `f.map φ`
separable.

`hf` and `hm` play the same roles as in
`eval_derivative_map_ne_zero_of_resultant_derivative_padded_ne_zero`. The derivative of
`f.map φ` may have degree below `m - 1`, as for `Y ^ 2 + Y` over `ZMod 2`, whose derivative
is `1`. -/
theorem separable_map_of_resultant_derivative_padded_ne_zero (φ : R →+* K) (f : R[X])
    (hf : f.natDegree ≤ m) (hm : 0 < m)
    (hres : φ (resultant f f.derivative m (m - 1)) ≠ 0) : (f.map φ).Separable := by
  rw [separable_def, derivative_map]
  exact isCoprime_map_of_resultant_padded_ne_zero φ f f.derivative hf
    ((natDegree_derivative_le f).trans (Nat.sub_le_sub_right hf 1)) (Or.inl hm.ne') hres

end Polynomial
