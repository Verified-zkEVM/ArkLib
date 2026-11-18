/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import Mathlib.Algebra.Polynomial.Eval.SMul
public import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.UniqueFactorizationDomain.Defs

/-!
# Linear independence of families of polynomials

## Main statements

* `Polynomial.linearIndependent_of_linearIndependent_map`: linear independence is reflected along
  a ring homomorphism whose kernel lies in the principal ideal of a non-unit, over a domain with
  well-founded divisibility.
* `Polynomial.linearIndependent_map_algebraMap_iff`: over a domain, linear independence of
  polynomials is the same over the domain and over its fraction field.
* `Polynomial.linearIndependent_option_of_dvd`: adjoining a polynomial that does not vanish at `c`
  to a linearly independent family of multiples of `X - C c`.
* `Polynomial.linearIndependent_iff_det_coeff_ne_zero`: `m` polynomials of degree `< m` are
  linearly independent iff their coefficient matrix has nonzero determinant.
* `Polynomial.linearIndependent_map_of_det_coeff_ne_zero`: specialising such a family along a
  ring homomorphism that does not kill the determinant.
-/

@[expose] public section

namespace Polynomial

variable {R β : Type*} [CommRing R]

/-- Linear independence is reflected along a ring homomorphism whose kernel lies in the principal
ideal of a non-unit, over a domain with well-founded divisibility. -/
theorem linearIndependent_of_linearIndependent_map [IsDomain R] [WfDvdMonoid R] {S : Type*}
    [CommRing S] (φ : R →+* S) {π : R} (hπ : ¬ IsUnit π) (hker : ∀ r, φ r = 0 → π ∣ r)
    {f : β → R[X]} (h : LinearIndependent S fun b => (f b).map φ) : LinearIndependent R f := by
  classical
  rw [linearIndependent_iff']
  intro s g hg i₀ hi₀
  by_contra hne
  let A : Set R := {r | r ≠ 0 ∧ ∃ g : β → R, ∑ i ∈ s, g i • f i = 0 ∧ g i₀ = r}
  obtain ⟨r, ⟨hr0, g, hgs, rfl⟩, hmin⟩ :=
    (wellFounded_dvdNotUnit (α := R)).has_min A ⟨g i₀, hne, g, hg, rfl⟩
  have hφ : ∀ i ∈ s, φ (g i) = 0 := by
    have hmap : ∑ i ∈ s, φ (g i) • (f i).map φ = 0 := by
      have := congrArg (Polynomial.map φ) hgs
      simpa [Polynomial.map_sum, Polynomial.smul_eq_C_mul, Polynomial.map_mul] using this
    exact (linearIndependent_iff'.1 h) s (fun i => φ (g i)) hmap
  choose! g' hg' using fun i (hi : i ∈ s) => hker (g i) (hφ i hi)
  have hπ0 : π ≠ 0 := by
    rintro rfl
    exact hr0 (by simpa using hg' i₀ hi₀)
  have hsum' : ∑ i ∈ s, g' i • f i = 0 := by
    have hC : C π * ∑ i ∈ s, g' i • f i = 0 := by
      rw [Finset.mul_sum, ← hgs]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [hg' i hi, smul_eq_C_mul, smul_eq_C_mul, C_mul]
      ring
    exact (mul_eq_zero.1 hC).resolve_left (by simpa using hπ0)
  have hg'0 : g' i₀ ≠ 0 := by
    intro h0
    apply hr0
    rw [hg' i₀ hi₀, h0, mul_zero]
  exact hmin (g' i₀) ⟨hg'0, g', hsum', rfl⟩ ⟨hg'0, π, hπ, by rw [hg' i₀ hi₀, mul_comm]⟩

/-- Polynomials over a domain are linearly independent over the fraction field iff they are
linearly independent over the domain. -/
theorem linearIndependent_map_algebraMap_iff [IsDomain R] {K : Type*} [Field K] [Algebra R K]
    [IsFractionRing R K] {f : β → R[X]} :
    LinearIndependent K (fun b => (f b).map (algebraMap R K)) ↔ LinearIndependent R f := by
  rw [← LinearIndependent.iff_fractionRing R K]
  let φ : R[X] →ₗ[R] K[X] := (Polynomial.mapAlgHom (Algebra.ofId R K)).toLinearMap
  have hinj : LinearMap.ker φ = ⊥ := LinearMap.ker_eq_bot.2 fun p q h =>
    Polynomial.map_injective _ (IsFractionRing.injective R K) h
  exact LinearMap.linearIndependent_iff φ hinj

/-- Adjoining to a linearly independent family of multiples of `X - C c` a polynomial that does
not vanish at `c` keeps the family linearly independent. -/
theorem linearIndependent_option_of_dvd [IsDomain R] {f : β → R[X]}
    (hf : LinearIndependent R f) {c : R} (hdvd : ∀ b, X - C c ∣ f b) {p : R[X]}
    (hp : p.eval c ≠ 0) : LinearIndependent R (fun o : Option β => o.elim p f) := by
  rw [← linearIndependent_map_algebraMap_iff (K := FractionRing R)] at hf ⊢
  rw [linearIndependent_option]
  refine ⟨hf, fun hmem => hp ?_⟩
  have hle : Submodule.span (FractionRing R)
      (Set.range fun b => (f b).map (algebraMap R (FractionRing R))) ≤
      LinearMap.ker (Polynomial.leval (algebraMap R (FractionRing R) c)) := by
    rw [Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    have hb : (f b).eval c = 0 := Polynomial.dvd_iff_isRoot.1 (hdvd b)
    rw [SetLike.mem_coe, LinearMap.mem_ker, leval_apply, Polynomial.eval_map,
      Polynomial.eval₂_at_apply, hb, map_zero]
  have := hle hmem
  simp only [LinearMap.mem_ker, Polynomial.leval, LinearMap.coe_mk, AddHom.coe_mk,
    Option.elim, Polynomial.eval_map, Polynomial.eval₂_at_apply] at this
  exact IsFractionRing.injective R (FractionRing R) (this.trans (map_zero _).symm)

/-- `m` polynomials of degree `< m` over a domain are linearly independent iff their coefficient
matrix has nonzero determinant. -/
theorem linearIndependent_iff_det_coeff_ne_zero [IsDomain R] {m : ℕ} {f : Fin m → R[X]}
    (hf : ∀ ℓ, f ℓ ∈ degreeLT R m) :
    LinearIndependent R f ↔ (Matrix.of fun ℓ (i : Fin m) => (f ℓ).coeff i).det ≠ 0 := by
  classical
  have hcoeff : ∀ (g : Fin m → R) (n : ℕ),
      (∑ ℓ, g ℓ • f ℓ).coeff n = ∑ ℓ, g ℓ * (f ℓ).coeff n := fun g n => by
    simp [Polynomial.finsetSum_coeff, Polynomial.coeff_smul]
  have hkey : ∀ g : Fin m → R, ∑ ℓ, g ℓ • f ℓ = 0 ↔
      Matrix.vecMul g (Matrix.of fun ℓ (i : Fin m) => (f ℓ).coeff i) = 0 := by
    intro g
    constructor
    · intro h
      funext i
      have := congrArg (fun p => p.coeff i) h
      simp only [hcoeff, Polynomial.coeff_zero] at this
      simpa [Matrix.vecMul, dotProduct] using this
    · intro h
      ext n
      rw [hcoeff, Polynomial.coeff_zero]
      by_cases hn : n < m
      · have := congrFun h ⟨n, hn⟩
        simpa [Matrix.vecMul, dotProduct] using this
      · refine Finset.sum_eq_zero fun ℓ _ => ?_
        rw [Polynomial.coeff_eq_zero_of_degree_lt, mul_zero]
        exact (mem_degreeLT.1 (hf ℓ)).trans_le (by exact_mod_cast not_lt.1 hn)
  rw [Fintype.linearIndependent_iff, Ne, ← Matrix.exists_vecMul_eq_zero_iff]
  constructor
  · rintro H ⟨v, hv, hvM⟩
    apply hv
    funext i
    exact H v ((hkey v).2 hvM) i
  · intro H g hg i
    by_contra hgi
    exact H ⟨g, fun h => hgi (congrFun h i), (hkey g).1 hg⟩

/-- If a ring homomorphism to a field does not kill the coefficient determinant of `m` polynomials
of degree `< m`, the mapped polynomials are linearly independent. -/
theorem linearIndependent_map_of_det_coeff_ne_zero {K : Type*} [Field K] (φ : R →+* K) {m : ℕ}
    {f : Fin m → R[X]} (hf : ∀ ℓ, f ℓ ∈ degreeLT R m)
    (hdet : φ (Matrix.of fun ℓ (i : Fin m) => (f ℓ).coeff i).det ≠ 0) :
    LinearIndependent K fun ℓ => (f ℓ).map φ := by
  have hf' : ∀ ℓ, (f ℓ).map φ ∈ degreeLT K m := fun ℓ =>
    mem_degreeLT.2 (degree_map_le.trans_lt (mem_degreeLT.1 (hf ℓ)))
  refine (linearIndependent_iff_det_coeff_ne_zero hf').2 ?_
  rw [RingHom.map_det] at hdet
  convert hdet using 2
  ext ℓ i
  simp [coeff_map]

end Polynomial
