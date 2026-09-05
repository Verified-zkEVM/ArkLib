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

-- The `sumAlgEquiv_monomial_aux` lemma below and its two helpers mirror the private uniform
-- proofs in `RestrictDegree.lean`.

namespace MvPolynomial

variable {σ : Type*} {R : Type*} [CommSemiring R]

/-- The submodule of polynomials whose degree in each variable `i` is at most `b i`, for a
per-variable bound `b : σ → ℕ`. Generalises `restrictDegree` (the constant-`b` case). -/
noncomputable def restrictDegreeVar (σ : Type*) (R : Type*) [CommSemiring R] (b : σ → ℕ) :
    Submodule R (MvPolynomial σ R) :=
  restrictSupport R { n | ∀ i, n i ≤ b i }

theorem mem_restrictDegreeVar {b : σ → ℕ} (p : MvPolynomial σ R) :
    p ∈ restrictDegreeVar σ R b ↔ ∀ s ∈ p.support, ∀ i, (s : σ →₀ ℕ) i ≤ b i := by
  simp only [restrictDegreeVar, mem_restrictSupport_iff, Set.subset_def, Finset.mem_coe,
    Set.mem_ofPred_eq]

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

lemma sumAlgEquiv_monomial_aux {R : Type*} [CommSemiring R]
    {S₁ S₂ : Type*}
    (m : (S₁ ⊕ S₂) →₀ ℕ) (c : R) :
    MvPolynomial.sumAlgEquiv R S₁ S₂ (MvPolynomial.monomial m c) =
      MvPolynomial.monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
        (MvPolynomial.monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn) c) := by
  ext s
  simp [MvPolynomial.sumAlgEquiv, MvPolynomial.monomial, MvPolynomial.coeff,
    Finsupp.comapDomain]

@[deprecated sumAlgEquiv_monomial_aux (since := "2026-08-15")]
alias sumToIter_monomial_aux := sumAlgEquiv_monomial_aux

/-- Renaming by an equivalence `e : σ ≃ τ` transports a per-variable degree bound `b` to the
pulled-back bound `b ∘ e.symm` on the target. -/
lemma rename_equiv_mem_restrictDegreeVar {R : Type*} [CommSemiring R]
    {σ τ : Type*} (e : σ ≃ τ) (p : MvPolynomial σ R) {b : σ → ℕ}
    (hp : p ∈ restrictDegreeVar σ R b) :
    MvPolynomial.rename e p ∈ restrictDegreeVar τ R (b ∘ e.symm) := by
  classical
  rw [mem_restrictDegreeVar] at hp ⊢
  intro m hm
  rw [MvPolynomial.support_rename_of_injective e.injective] at hm
  obtain ⟨n', hn', rfl⟩ := Finset.mem_image.mp hm
  intro i
  rw [Finsupp.mapDomain_equiv_apply]
  exact hp n' hn' (e.symm i)

/-- Currying via `sumAlgEquiv` preserves the per-variable bound on the outer (`S₁`) coordinates
restricted to `Sum.inl`. -/
lemma sumAlgEquiv_mem_restrictDegreeVar {R : Type*} [CommSemiring R]
    {S₁ S₂ : Type*} (p : MvPolynomial (S₁ ⊕ S₂) R) {b : S₁ ⊕ S₂ → ℕ}
    (hp : p ∈ restrictDegreeVar (S₁ ⊕ S₂) R b) :
    (MvPolynomial.sumAlgEquiv R S₁ S₂) p ∈
      restrictDegreeVar S₁ (MvPolynomial S₂ R) (b ∘ Sum.inl) := by
  classical
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
      exact Finset.sum_congr rfl fun _ _ => sumAlgEquiv_monomial_aux _ _
    rw [h_sum] at hs
    have hs_union := (MvPolynomial.support_sum (s := p.support)
      (f := fun m =>
        MvPolynomial.monomial (m.comapDomain Sum.inl Sum.inl_injective.injOn)
          (MvPolynomial.monomial (m.comapDomain Sum.inr Sum.inr_injective.injOn)
            (p.coeff m)))) hs
    obtain ⟨m, hm, hsm⟩ := Finset.mem_biUnion.mp hs_union
    have hs_eq := MvPolynomial.support_monomial_subset hsm
    exact ⟨m, hm, Finset.mem_singleton.mp hs_eq⟩
  intro i
  subst hs_eq
  rw [Finsupp.comapDomain_apply]
  exact hp hm (Sum.inl i)

end MvPolynomial
