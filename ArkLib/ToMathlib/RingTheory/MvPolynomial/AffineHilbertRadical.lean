/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertAlgHom
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.RingTheory.Finiteness.Ideal

/-!
# The affine Hilbert polynomial of a radical

Let `k` be a field, `σ` a finite type with `n` elements, and `I`, `J` ideals of
`MvPolynomial σ k` with `J ^ t ≤ I`. Write `H(I, N)` for `affineHilbertFunction I N`. Then
`H(I, N) ≤ t ^ n * H(J, N)` for every `N`, so the affine Hilbert polynomial of `I` has natural
degree at most that of `J`. When moreover `I ≤ J`, the two natural degrees are equal. Every ideal
`J` with `I ≤ J ≤ I.radical` has such a power, because `J` is finitely generated; in particular
`I` and `I.radical` have affine Hilbert polynomials of the same natural degree. The leading
coefficients can differ: `span {X ^ 2}` in one variable has polynomial `2` and its radical
`span {X}` has polynomial `1`.

The bound on Hilbert functions comes from the standard exponents of a monomial order `m`. If `e`
is standard for `I`, then the coordinatewise floor quotient `e ⌊/⌋ t` is standard for `J`: a
nonzero `p ∈ J` whose leading exponent divides `e ⌊/⌋ t` has `p ^ t ∈ I` with leading exponent
`t • m.degree p ≤ e`. The pair of quotient `e ⌊/⌋ t` and remainders `e i % t` determines `e`,
and for a graded order the quotient has total degree at most that of `e`, which gives an
injection from the standard exponents of `I` of degree at most `N` into the product of those of
`J` with `Fin t`-valued functions on `σ`.

## Main statements

* `MonomialOrder.floorDiv_mem_standardExponents`: floor division by `t` maps standard exponents
  of `I` to standard exponents of `J`.
* `MvPolynomial.affineHilbertFunction_le_pow_mul_of_pow_le`: `H(I, N) ≤ t ^ n * H(J, N)`.
* `MvPolynomial.natDegree_affineHilbertPolynomial_le_of_pow_le`: the degree comparison.
* `MvPolynomial.natDegree_affineHilbertPolynomial_eq_of_le_of_le_radical`: equality of natural
  degrees between `I ≤ J ≤ I.radical`.
* `MvPolynomial.natDegree_affineHilbertPolynomial_radical`: the radical has the same natural
  degree.

## References

Ported from ArkLib revision `a5aa2677fee4e3a79d6bb05136631cce4a08587d`, file
`ArkLib/ToMathlib/AlgebraicGeometry/Hilbert/RadicalDegree.lean`, namespace `AffineHilbert`. The
source's `exponentDiv t e`, with `exponentDiv_apply` and `exponentDiv_le`, is Mathlib's floor
division `e ⌊/⌋ t` on `σ →₀ ℕ` (`Finsupp.floorDiv_apply`, `Nat.floorDiv_eq_div`), so it has no
new definition; `exponentDiv_le` is `Finsupp.floorDiv_le_self`. The source's
`exponentDiv_mem_standardExponents` is `MonomialOrder.floorDiv_mem_standardExponents`, stated for
every monomial order instead of `degLex` and without the hypothesis `0 < t`: for `t = 0`,
`J ^ 0 ≤ I` forces `I = ⊤`, which has no standard exponents. The source's
`hilbertFunction_le_mul_of_pow_le` is `affineHilbertFunction_le_pow_mul_of_pow_le`, with the
factor `t ^ Nat.card σ` on the left, for finite `σ` without a chosen `Fintype` or `LinearOrder`,
and again without `0 < t`. The source's `hilbertPolynomial_radical_natDegree` is
`natDegree_affineHilbertPolynomial_radical`, a corollary of the comparison
`natDegree_affineHilbertPolynomial_le_of_pow_le` for arbitrary `J ^ t ≤ I` and of the equality
`natDegree_affineHilbertPolynomial_eq_of_le_of_le_radical` for every `I ≤ J ≤ I.radical`.
-/

@[expose] public section

noncomputable section

open Filter
open scoped MonomialOrder

namespace Finsupp

variable {ι : Type*}

/-- Coordinatewise floor division by a natural number does not increase an exponent vector. -/
theorem floorDiv_le_self (e : ι →₀ ℕ) (t : ℕ) : e ⌊/⌋ t ≤ e :=
  fun i ↦ by simpa using Nat.div_le_self (e i) t

/-- `t • (e ⌊/⌋ t) ≤ e` for every natural number `t`, including `t = 0`, where both sides of the
Galois connection degenerate to `0 ≤ e`. -/
theorem smul_floorDiv_le_self (e : ι →₀ ℕ) (t : ℕ) : t • (e ⌊/⌋ t) ≤ e := by
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · simp
  · exact smul_floorDiv_le ht

end Finsupp

namespace MonomialOrder

variable {σ k : Type*} [Field k] (m : MonomialOrder σ)

/-- If `J ^ t ≤ I`, floor division by `t` maps the standard exponents of `I` to standard
exponents of `J`, for every monomial order `m`. A nonzero `p ∈ J` with
`m.degree p ≤ e ⌊/⌋ t` would give the nonzero element `p ^ t ∈ I` with leading exponent
`t • m.degree p ≤ e`, so `e` would not be standard for `I`. -/
theorem floorDiv_mem_standardExponents {I J : Ideal (MvPolynomial σ k)} {t : ℕ}
    (hpow : J ^ t ≤ I) {e : σ →₀ ℕ} (he : e ∈ m.standardExponents I) :
    e ⌊/⌋ t ∈ m.standardExponents J := by
  intro p hp hp0 hle
  refine he (p ^ t) (hpow (Ideal.pow_mem_pow hp t)) (pow_ne_zero _ hp0) ?_
  rw [m.degree_pow]
  exact (nsmul_le_nsmul_right hle t).trans (Finsupp.smul_floorDiv_le_self e t)

end MonomialOrder

namespace MvPolynomial

variable {k σ : Type*} [Field k] [Finite σ]

/-- If `J ^ t ≤ I`, then `H(I, N) ≤ t ^ n * H(J, N)` for every `N`, where `n = Nat.card σ`.

Choose a graded monomial order. The map `e ↦ (e ⌊/⌋ t, fun i ↦ e i % t)` sends the standard
exponents of `I` of degree at most `N` injectively to pairs of a standard exponent of `J` of
degree at most `N` and a function `σ → Fin t` (`MonomialOrder.floorDiv_mem_standardExponents`).
For `t = 0` the hypothesis forces `I = ⊤`, and both sides are `0`. -/
theorem affineHilbertFunction_le_pow_mul_of_pow_le {I J : Ideal (MvPolynomial σ k)} {t : ℕ}
    (hpow : J ^ t ≤ I) (N : ℕ) :
    affineHilbertFunction I N ≤ t ^ Nat.card σ * affineHilbertFunction J N := by
  classical
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rw [pow_zero, Ideal.one_eq_top, top_le_iff] at hpow
    rw [hpow, affineHilbertFunction_top]
    exact Nat.zero_le _
  have := Fintype.ofFinite σ
  let _ : LinearOrder σ := LinearOrder.lift' _ (Fintype.equivFin σ).injective
  have : WellFoundedGT σ := Finite.to_wellFoundedGT
  let m : MonomialOrder σ := MonomialOrder.degLex
  let SI := {e : σ →₀ ℕ | e ∈ m.standardExponents I ∧ e.degree ≤ N}
  let SJ := {e : σ →₀ ℕ | e ∈ m.standardExponents J ∧ e.degree ≤ N}
  have hSJ : SJ.Finite := (Finsupp.finite_of_degree_le N).subset fun _ he ↦ he.2
  have : Finite SJ := hSJ.to_subtype
  let φ : SI → SJ × (σ → Fin t) := fun e ↦
    (⟨e.1 ⌊/⌋ t, m.floorDiv_mem_standardExponents hpow e.2.1,
      (Finsupp.degree_mono (Finsupp.floorDiv_le_self e.1 t)).trans e.2.2⟩,
      fun i ↦ ⟨e.1 i % t, Nat.mod_lt _ ht⟩)
  have hφ : Function.Injective φ := by
    intro e f h
    refine Subtype.ext (Finsupp.ext fun i ↦ ?_)
    have hdiv : e.1 i / t = f.1 i / t :=
      congrArg (fun z : SJ × (σ → Fin t) ↦ z.1.1 i) h
    have hmod : e.1 i % t = f.1 i % t :=
      congrArg (fun z : SJ × (σ → Fin t) ↦ (z.2 i).val) h
    rw [← Nat.mod_add_div (e.1 i) t, ← Nat.mod_add_div (f.1 i) t, hdiv, hmod]
  have hcard := Nat.card_le_card_of_injective φ hφ
  rw [m.affineHilbertFunction_eq_ncard_standardExponents
      (fun _ _ ↦ degree_le_degree_of_degLex_le) I N,
    m.affineHilbertFunction_eq_ncard_standardExponents
      (fun _ _ ↦ degree_le_degree_of_degLex_le) J N]
  simpa only [Nat.card_prod, Nat.card_fun, Nat.card_fin, Nat.card_coe_set_eq, SI, SJ,
    mul_comm] using hcard

/-- If `J ^ t ≤ I`, the affine Hilbert polynomial of `I` has natural degree at most that of `J`.
This follows from `affineHilbertFunction_le_pow_mul_of_pow_le` and
`natDegree_affineHilbertPolynomial_le_of_eventually_le_mul`. No inclusion between `I` and `J`
is assumed. -/
theorem natDegree_affineHilbertPolynomial_le_of_pow_le {I J : Ideal (MvPolynomial σ k)} {t : ℕ}
    (hpow : J ^ t ≤ I) :
    (affineHilbertPolynomial I).natDegree ≤ (affineHilbertPolynomial J).natDegree :=
  natDegree_affineHilbertPolynomial_le_of_eventually_le_mul (τ := σ) (m := t ^ Nat.card σ)
    (c := 1) Nat.one_pos
    (Eventually.of_forall fun N ↦ (one_mul N).symm ▸
      affineHilbertFunction_le_pow_mul_of_pow_le hpow N)

/-- If `J ^ t ≤ I ≤ J`, then `I` and `J` have affine Hilbert polynomials of the same natural
degree. The inclusion `I ≤ J` gives one inequality
(`natDegree_affineHilbertPolynomial_le_of_le`) and the power the other. -/
theorem natDegree_affineHilbertPolynomial_eq_of_pow_le_of_le {I J : Ideal (MvPolynomial σ k)}
    {t : ℕ} (hpow : J ^ t ≤ I) (hIJ : I ≤ J) :
    (affineHilbertPolynomial J).natDegree = (affineHilbertPolynomial I).natDegree :=
  le_antisymm (natDegree_affineHilbertPolynomial_le_of_le hIJ)
    (natDegree_affineHilbertPolynomial_le_of_pow_le hpow)

/-- Every ideal `J` with `I ≤ J ≤ I.radical` has an affine Hilbert polynomial of the same natural
degree as `I`. The ring `MvPolynomial σ k` is Noetherian, so `J` is finitely generated and some
power of `J` lies in `I` (`Ideal.exists_pow_le_of_le_radical_of_fg`). -/
theorem natDegree_affineHilbertPolynomial_eq_of_le_of_le_radical
    {I J : Ideal (MvPolynomial σ k)} (hIJ : I ≤ J) (hJ : J ≤ I.radical) :
    (affineHilbertPolynomial J).natDegree = (affineHilbertPolynomial I).natDegree :=
  have ⟨_, hpow⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJ (IsNoetherian.noetherian J)
  natDegree_affineHilbertPolynomial_eq_of_pow_le_of_le hpow hIJ

/-- Taking the radical does not change the natural degree of the affine Hilbert polynomial. The
leading coefficient can change: `span {X ^ 2}` in one variable has polynomial `2`, and its
radical `span {X}` has polynomial `1`. -/
@[simp]
theorem natDegree_affineHilbertPolynomial_radical (I : Ideal (MvPolynomial σ k)) :
    (affineHilbertPolynomial I.radical).natDegree = (affineHilbertPolynomial I).natDegree :=
  natDegree_affineHilbertPolynomial_eq_of_le_of_le_radical I.le_radical le_rfl

/-- Ideals with the same radical have affine Hilbert polynomials of the same natural degree. -/
theorem natDegree_affineHilbertPolynomial_eq_of_radical_eq {I J : Ideal (MvPolynomial σ k)}
    (h : I.radical = J.radical) :
    (affineHilbertPolynomial I).natDegree = (affineHilbertPolynomial J).natDegree := by
  rw [← natDegree_affineHilbertPolynomial_radical I, h, natDegree_affineHilbertPolynomial_radical]

end MvPolynomial
