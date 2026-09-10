/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.Polynomial
public import Mathlib.RingTheory.Finiteness.Ideal

/-!
# Hilbert polynomial degree is unchanged by taking radicals

A uniform nilpotence exponent bounds standard-monomial counts through coordinatewise
Euclidean division. This controls actual filtration growth without a multiplicity theory.
-/

@[expose] public section

noncomputable section

namespace AffineHilbert

open MvPolynomial MonomialOrder
open scoped MonomialOrder

variable {F σ : Type*} [Field F] [Fintype σ] [LinearOrder σ]

/-- Divide each exponent coordinate by a fixed natural number. -/
def exponentDiv (t : ℕ) (e : σ →₀ ℕ) : σ →₀ ℕ :=
  e.mapRange (fun a ↦ a / t) (Nat.zero_div t)

omit [Fintype σ] [LinearOrder σ] in
@[simp]
theorem exponentDiv_apply (t : ℕ) (e : σ →₀ ℕ) (i : σ) :
    exponentDiv t e i = e i / t := rfl

omit [Fintype σ] [LinearOrder σ] in
theorem exponentDiv_le (t : ℕ) (e : σ →₀ ℕ) : exponentDiv t e ≤ e :=
  fun i ↦ Nat.div_le_self (e i) t

omit [Fintype σ] in
/-- A standard exponent for I becomes standard for J after division by an exponent
whose ideal power is contained in I. -/
theorem exponentDiv_mem_standardExponents [Finite σ] {I J : Ideal (MvPolynomial σ F)}
    {t : ℕ} (ht : 0 < t) (hpow : J ^ t ≤ I) {e : σ →₀ ℕ}
    (he : e ∈ standardExponents I) : exponentDiv t e ∈ standardExponents J := by
  intro p hp hp0 hlead
  apply he (p ^ t) (hpow (Ideal.pow_mem_pow hp t)) (pow_ne_zero _ hp0)
  rw [degLex.degree_pow]
  intro i
  change t * degLex.degree p i ≤ e i
  simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le ht).mp (hlead i)

end AffineHilbert

namespace AffineHilbert

open MvPolynomial MonomialOrder
open scoped MonomialOrder

variable {F σ : Type*} [Field F] [Fintype σ] [LinearOrder σ]

/-- Euclidean quotients and remainders give an injection controlling the actual
standard-monomial count whenever a power of J lies in I. -/
theorem hilbertFunction_le_mul_of_pow_le {I J : Ideal (MvPolynomial σ F)}
    {t : ℕ} (ht : 0 < t) (hpow : J ^ t ≤ I) (N : ℕ) :
    hilbertFunction I N ≤ hilbertFunction J N * t ^ Fintype.card σ := by
  classical
  let SI := {e : σ →₀ ℕ | e ∈ standardExponents I ∧ e.degree ≤ N}
  let SJ := {e : σ →₀ ℕ | e ∈ standardExponents J ∧ e.degree ≤ N}
  have hSJ : SJ.Finite := (Finsupp.finite_of_degree_le N).subset (fun _ he ↦ he.2)
  let _ : Fintype SJ := hSJ.fintype
  let φ : SI → SJ × (σ → Fin t) := fun e ↦
    (⟨exponentDiv t e.val,
      exponentDiv_mem_standardExponents ht hpow e.property.1,
      (Finsupp.degree_mono (exponentDiv_le t e.val)).trans e.property.2⟩,
      fun i ↦ ⟨e.val i % t, Nat.mod_lt _ ht⟩)
  have hφ : Function.Injective φ := by
    intro e f h
    apply Subtype.ext
    ext i
    have hdiv : e.val i / t = f.val i / t :=
      congrArg (fun z : SJ × (σ → Fin t) ↦ z.1.val i) h
    have hmod : e.val i % t = f.val i % t :=
      congrArg (fun z : SJ × (σ → Fin t) ↦ (z.2 i).val) h
    have he := Nat.mod_add_div (e.val i) t
    have hf := Nat.mod_add_div (f.val i) t
    rw [hdiv, hmod] at he
    exact he.symm.trans hf
  have hcard := Nat.card_le_card_of_injective φ hφ
  rw [hilbertFunction_eq_standard_count, hilbertFunction_eq_standard_count]
  have hσ : Nat.card σ = Fintype.card σ := Nat.card_eq_fintype_card
  simpa only [Nat.card_prod, Nat.card_fun, Nat.card_fin, hσ, Nat.card_coe_set_eq, SI, SJ]
    using hcard

end AffineHilbert

namespace AffineHilbert

open Polynomial Filter

variable {F σ : Type*} [Field F] [Finite σ]

/-- Taking a radical leaves the degree of the actual affine Hilbert polynomial unchanged. -/
theorem hilbertPolynomial_radical_natDegree (I : Ideal (MvPolynomial σ F)) :
    (hilbertPolynomial I.radical).natDegree = (hilbertPolynomial I).natDegree := by
  classical
  by_cases hI : I = ⊤
  · subst I
    rw [Ideal.radical_eq_top.mpr rfl]
  have hrad : I.radical ≠ ⊤ := fun h ↦ hI (Ideal.radical_eq_top.mp h)
  have hlower := (hilbertPolynomial_degree_and_leadingCoeff_antitone Ideal.le_radical hrad).1
  apply le_antisymm hlower
  let _ : Fintype σ := Fintype.ofFinite σ
  let _ : LinearOrder σ := (Fintype.equivFin σ).linearOrder
  obtain ⟨n, hn⟩ := I.exists_radical_pow_le_of_fg I.radical.fg_of_isNoetherianRing
  let t := n + 1
  have ht : 0 < t := Nat.succ_pos n
  have hpow : I.radical ^ t ≤ I :=
    (Ideal.pow_le_pow_right (Nat.le_succ n)).trans hn
  let C : ℚ := (t ^ Fintype.card σ : ℕ)
  have hC : C ≠ 0 := by
    dsimp [C]
    exact_mod_cast pow_ne_zero (Fintype.card σ) (Nat.ne_of_gt ht)
  have hnonneg : ∀ᶠ N : ℕ in atTop, 0 ≤ (hilbertPolynomial I).eval (N : ℚ) := by
    filter_upwards [hilbertPolynomial_eventually_eval I] with N hN
    rw [hN]
    positivity
  have hle : ∀ᶠ N : ℕ in atTop,
      (hilbertPolynomial I).eval (N : ℚ) ≤
        (Polynomial.C C * hilbertPolynomial I.radical).eval (N : ℚ) := by
    filter_upwards [hilbertPolynomial_eventually_eval I,
      hilbertPolynomial_eventually_eval I.radical] with N hIN hJN
    rw [Polynomial.eval_mul, Polynomial.eval_C, hIN, hJN]
    have h := hilbertFunction_le_mul_of_pow_le ht hpow N
    change (hilbertFunction I N : ℚ) ≤
      (t ^ Fintype.card σ : ℕ) * (hilbertFunction I.radical N : ℚ)
    rw [mul_comm]
    exact_mod_cast h
  have hdegree :=
    (natDegree_le_of_eventually_eval_nat_le (hilbertPolynomial_ne_zero hI) hnonneg hle).1
  rwa [Polynomial.natDegree_C_mul hC] at hdegree

end AffineHilbert
