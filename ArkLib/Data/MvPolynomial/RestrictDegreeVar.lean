/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.RingTheory.MvPolynomial.Basic
import ArkLib.Data.MvPolynomial.Degrees

/-!
# Per-variable degree restriction ("prismalinear" polynomials)

`MvPolynomial.restrictDegree σ R m` is the submodule of polynomials whose degree in *every* variable
is `≤ m` — a *uniform* per-variable bound. Some protocols need a degree bound that **varies by
variable**: SWIRL's hyperprism / univariate-skip extension is *prismalinear* — degree `≤ |D|-1` in
the univariate "skip" coordinate and degree `≤ 1` (multilinear) in the Boolean coordinates.

This file defines `MvPolynomial.restrictDegreeVar σ R b` for a per-variable bound `b : σ → ℕ`, the
common generalisation: `restrictDegree σ R m` is the constant case `b = fun _ => m` (`rfl`), and the
plain multilinear case is `b = fun _ => 1`. The degree machinery (`degreeOf`) is already
per-coordinate, so the characterisation `mem_restrictDegreeVar_iff_degreeOf_le` is immediate.
-/

-- The `sumToIter_monomial_aux` lemma below + the two helper lemmas mirror the (private) uniform
-- proofs in `RestrictDegree.lean`. The `multiGoal` linter fires on a `congr! 2` split inside
-- `sumToIter_monomial_aux`; scope-suppress it file-wide.
set_option linter.style.multiGoal false

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R]

/-- The submodule of polynomials whose degree in each variable `i` is at most `b i`, for a
per-variable bound `b : σ → ℕ`. Generalises `restrictDegree` (the constant-`b` case). -/
def restrictDegreeVar (σ : Type*) (R : Type*) [CommSemiring R] (b : σ → ℕ) :
    Submodule R (MvPolynomial σ R) :=
  restrictSupport R { n | ∀ i, n i ≤ b i }

theorem mem_restrictDegreeVar {b : σ → ℕ} (p : MvPolynomial σ R) :
    p ∈ restrictDegreeVar σ R b ↔ ∀ s ∈ p.support, ∀ i, (s : σ →₀ ℕ) i ≤ b i := by
  simp only [restrictDegreeVar, mem_restrictSupport_iff, Set.subset_def, Finset.mem_coe,
    Set.mem_setOf_eq]

/-- The uniform bound `b = fun _ => m` recovers `restrictDegree σ R m` definitionally. So
`restrictDegreeVar` is a drop-in generalisation: existing `restrictDegree`/`R⦃≤ m⦄[X σ]` users are
the constant case. -/
@[simp] theorem restrictDegreeVar_const (m : ℕ) :
    restrictDegreeVar σ R (fun _ => m) = restrictDegree σ R m := rfl

/-- Characterisation by per-variable degree: `p` is prismalinear with bound `b` iff `degreeOf i p ≤
b i` for every variable `i`. The per-variable analogue of `mem_restrictDegree_iff_degreeOf_le`. -/
theorem mem_restrictDegreeVar_iff_degreeOf_le {b : σ → ℕ} (p : MvPolynomial σ R) :
    p ∈ restrictDegreeVar σ R b ↔ ∀ i, degreeOf i p ≤ b i := by
  rw [mem_restrictDegreeVar]
  exact ⟨fun h i => degreeOf_le_iff.mpr (fun s hs => h s hs i),
         fun h s hs i => degreeOf_le_iff.mp (h i) s hs⟩

/-- `restrictDegreeVar` is monotone in the per-variable bound. -/
theorem restrictDegreeVar_mono {b₁ b₂ : σ → ℕ} (h : ∀ i, b₁ i ≤ b₂ i) :
    restrictDegreeVar σ R b₁ ≤ restrictDegreeVar σ R b₂ := by
  intro p hp
  rw [mem_restrictDegreeVar_iff_degreeOf_le] at hp ⊢
  exact fun i => (hp i).trans (h i)

/-- A prismalinear polynomial whose per-variable bound is everywhere `≤ m` lies in the uniform
`restrictDegree σ R m` (i.e. `R⦃≤ m⦄[X σ]`). -/
theorem restrictDegreeVar_le_restrictDegree {b : σ → ℕ} {m : ℕ} (h : ∀ i, b i ≤ m) :
    restrictDegreeVar σ R b ≤ restrictDegree σ R m := by
  rw [← restrictDegreeVar_const (σ := σ) (R := R) m]
  exact restrictDegreeVar_mono h

/-- The SWIRL **prismalinear** degree bound on `Fin (k+1)` variables: degree `2^ℓ − 1` in the
univariate-skip coordinate (coord `0`) and degree `≤ 1` in each of the remaining `k` Boolean
coordinates. The hyperprism multiplier (the `eq`-polynomial of SWIRL/Gru24) lies in
`restrictDegreeVar (Fin (k+1)) R (prismalinearBound ℓ k)`. -/
def prismalinearBound (ℓ k : ℕ) : Fin (k + 1) → ℕ :=
  Fin.cons (2 ^ ℓ - 1) (fun _ : Fin k => 1)

/-! ## Helper lemmas: variable-renaming and sum-algebra preserve per-variable bounds

Per-variable analogs of the (private) uniform helpers `rename_equiv_mem_restrictDegree` and
`sumAlgEquiv_mem_restrictDegree` in `RestrictDegree.lean`. Used by
`fixFirstVariablesOfMQP_degreeVarLE` (the prismalinear analog of `fixFirstVariablesOfMQP_degreeLE`).
-/

lemma sumToIter_monomial_aux {R : Type*} [CommSemiring R]
    {S₁ S₂ : Type*}
    (m : (S₁ ⊕ S₂) →₀ ℕ) (c : R) :
    MvPolynomial.sumToIter R S₁ S₂ (MvPolynomial.monomial m c) =
      MvPolynomial.monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
        (MvPolynomial.monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) c) := by
  simp only [sumToIter, eval₂Hom_monomial]
  simp only [RingHom.coe_comp, Function.comp_apply, Finsupp.prod, Finsupp.comapDomain,
    Finset.preimage_inl, Finset.preimage_inr]
  convert congr_arg₂ (· * ·) rfl ?_ using 1
  rotate_left
  exact ∏ x ∈ m.support,
    Sum.rec (fun a => MvPolynomial.X a)
      (fun b => MvPolynomial.C (MvPolynomial.X b)) x ^ m x
  · rfl
  · simp only [monomial_eq, C_mul]
    simp only [Finsupp.prod, Finsupp.coe_mk, map_prod, C_pow, mul_assoc]
    rw [← Finset.prod_filter_mul_prod_filter_not m.support (fun x => x.isRight)]
    congr! 2
    · exact Finset.prod_bij (fun x hx => Sum.inr x) (by aesop) (by aesop)
        (by aesop) (by aesop)
    · exact Finset.prod_bij (fun x hx => Sum.inl x) (by aesop) (by aesop)
        (by aesop) (by aesop)

/-- Renaming by an equivalence `e : σ ≃ τ` transports a per-variable degree bound `b` to the
pulled-back bound `b ∘ e.symm` on the target. -/
lemma rename_equiv_mem_restrictDegreeVar {R : Type*} [CommSemiring R]
    {σ τ : Type*} (e : σ ≃ τ) (p : MvPolynomial σ R) {b : σ → ℕ}
    (hp : p ∈ restrictDegreeVar σ R b) :
    MvPolynomial.rename e p ∈ restrictDegreeVar τ R (b ∘ e.symm) := by
  intro m hm
  obtain ⟨n', hn', hm_eq⟩ : ∃ n' ∈ p.support, m = n'.mapDomain e := by
    simp only [SetLike.mem_coe, Finsupp.mem_support_iff, ne_eq, mem_support_iff] at *
    rw [MvPolynomial.rename_eq] at hm
    contrapose! hm
    rw [Finsupp.mapDomain, Finsupp.sum, Finsupp.finsetSum_apply]
    exact Finset.sum_eq_zero fun x hx =>
      Finsupp.single_eq_of_ne (hm x (by aesop))
  intro i
  subst hm_eq
  rw [Finsupp.mapDomain_equiv_apply]
  exact hp hn' (e.symm i)

/-- Currying via `sumAlgEquiv` preserves the per-variable bound on the outer (`S₁`) coordinates
restricted to `Sum.inl`. -/
lemma sumAlgEquiv_mem_restrictDegreeVar {R : Type*} [CommSemiring R]
    {S₁ S₂ : Type*} (p : MvPolynomial (S₁ ⊕ S₂) R) {b : S₁ ⊕ S₂ → ℕ}
    (hp : p ∈ restrictDegreeVar (S₁ ⊕ S₂) R b) :
    (MvPolynomial.sumAlgEquiv R S₁ S₂) p ∈
      restrictDegreeVar S₁ (MvPolynomial S₂ R) (b ∘ Sum.inl) := by
  intro s hs
  obtain ⟨m, hm, hs_eq⟩ : ∃ m : (S₁ ⊕ S₂) →₀ ℕ,
      m ∈ p.support ∧ s = m.comapDomain Sum.inl Sum.inl_injective.injOn := by
    have h_sum : (MvPolynomial.sumAlgEquiv R S₁ S₂) p =
        ∑ m ∈ p.support,
          (MvPolynomial.monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn))
            (MvPolynomial.monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn)
              (p.coeff m)) := by
      conv_lhs => rw [p.as_sum]
      rw [map_sum]
      exact Finset.sum_congr rfl fun _ _ => sumToIter_monomial_aux _ _
    contrapose! hs
    simp only [h_sum, SetLike.mem_coe, Finsupp.mem_support_iff, ne_eq, not_not]
    erw [Finsupp.finsetSum_apply]
    refine Finset.sum_eq_zero fun x hx => ?_
    erw [AddMonoidAlgebra.lsingle_apply, AddMonoidAlgebra.lsingle_apply]; aesop
  intro i
  subst hs_eq
  rw [Finsupp.comapDomain_apply]
  exact hp hm (Sum.inl i)

end MvPolynomial
