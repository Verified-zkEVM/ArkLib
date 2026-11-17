/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import CompPoly.Univariate.ToPoly.Degree

/-!
# Finite enumeration of bounded computable polynomials

`CompPoly.CPolynomial.degreeLTEquiv` identifies polynomials of degree below `k` with `Fin k → R`.
It gives a computable `Fintype` from an executable enumeration and equality on the coefficients.

The noncomputable `CompPoly.CPolynomial.toPolyLinearEquiv` converts between CompPoly and
Mathlib polynomials.
`CompPoly.CPolynomial.degreeLTToPolyEquiv` restricts this conversion to degree below `k`.
It is used only in correctness proofs, where surjectivity certifies exhaustive finite searches.
-/

@[expose] public section

namespace CompPoly.CPolynomial

variable {R : Type*} [Semiring R] [BEq R] [LawfulBEq R]

/-- Enumerate bounded-degree polynomials through their finite coefficient vectors. -/
instance instFintypeDegreeLT [DecidableEq R] [Fintype R] (k : ℕ) : Fintype ↥(degreeLT (R := R) k) :=
  Fintype.ofEquiv (Fin k → R) (degreeLTEquiv (R := R) k).symm.toEquiv

/-- Conversion to Mathlib polynomials restricts to each strict degree bound. -/
noncomputable def degreeLTToPolyEquiv (k : ℕ) :
    ↥(degreeLT (R := R) k) ≃ ↥(Polynomial.degreeLT R k) :=
  Equiv.subtypeEquiv toPolyLinearEquiv.toEquiv fun p ↦ by
    change p ∈ degreeLT (R := R) k ↔ toPolyLinearEquiv p ∈ Polynomial.degreeLT R k
    rw [toPolyLinearEquiv_apply]
    exact degreeLT_toPoly

@[simp]
theorem degreeLTToPolyEquiv_apply (k : ℕ) (p : ↥(degreeLT (R := R) k)) :
    (degreeLTToPolyEquiv k p).val = p.val.toPoly := by
  change toPolyLinearEquiv p.val = p.val.toPoly
  exact toPolyLinearEquiv_apply p.val

/-- Searching bounded computable polynomials covers every Mathlib polynomial of that degree. -/
theorem exists_degreeLT_toPoly_iff (k : ℕ) (Q : Polynomial R → Prop) :
    (∃ p : ↥(degreeLT (R := R) k), Q p.val.toPoly) ↔
      ∃ p : Polynomial R, p.degree < k ∧ Q p := by
  constructor
  · rintro ⟨p, hQ⟩
    exact ⟨p.val.toPoly, Polynomial.mem_degreeLT.mp (degreeLT_toPoly.mp p.property), hQ⟩
  · rintro ⟨p, hp, hQ⟩
    let q := (degreeLTToPolyEquiv (R := R) k).symm ⟨p, Polynomial.mem_degreeLT.mpr hp⟩
    refine ⟨q, ?_⟩
    have h := congrArg Subtype.val
      ((degreeLTToPolyEquiv (R := R) k).apply_symm_apply ⟨p, Polynomial.mem_degreeLT.mpr hp⟩)
    change (degreeLTToPolyEquiv k q).val = p at h
    rw [degreeLTToPolyEquiv_apply] at h
    rwa [h]

/-- Checking every bounded representation covers every polynomial below the degree bound. -/
theorem forall_degreeLT_toPoly_iff (k : ℕ) (Q : Polynomial R → Prop) :
    (∀ p : ↥(degreeLT (R := R) k), Q p.val.toPoly) ↔
      ∀ p : Polynomial R, p.degree < k → Q p := by
  constructor
  · intro h p hp
    obtain ⟨q, hq⟩ := (exists_degreeLT_toPoly_iff k (fun q ↦ q = p)).mpr ⟨p, hp, rfl⟩
    simpa only [hq] using h q
  · intro h p
    exact h p.val.toPoly (Polynomial.mem_degreeLT.mp (degreeLT_toPoly.mp p.property))

/-- Finite searches over two bounded polynomials cover all pairs within those degree bounds. -/
theorem forall_pair_degreeLT_toPoly_iff (k l : ℕ) (Q : Polynomial R → Polynomial R → Prop) :
    (∀ f : ↥(degreeLT (R := R) k), ∀ g : ↥(degreeLT (R := R) l),
      Q f.val.toPoly g.val.toPoly) ↔
      ∀ f g : Polynomial R, f.degree < k → g.degree < l → Q f g := by
  constructor
  · intro h f g hf hg
    apply (forall_degreeLT_toPoly_iff k
      (fun f ↦ ∀ g : Polynomial R, g.degree < l → Q f g)).mp ?_ f hf g hg
    intro f
    exact (forall_degreeLT_toPoly_iff l (Q f.val.toPoly)).mp (h f)
  · intro h f g
    exact h f.val.toPoly g.val.toPoly
      (Polynomial.mem_degreeLT.mp (degreeLT_toPoly.mp f.property))
      (Polynomial.mem_degreeLT.mp (degreeLT_toPoly.mp g.property))

/-- A predicate implying a strict degree bound can be searched through finite representations. -/
theorem exists_degreeLT_toPoly_iff_of_degree_lt (k : ℕ) (Q : Polynomial R → Prop)
    (hQ : ∀ p, Q p → p.degree < k) :
    (∃ p : ↥(degreeLT (R := R) k), Q p.val.toPoly) ↔ ∃ p : Polynomial R, Q p := by
  rw [exists_degreeLT_toPoly_iff]
  constructor
  · rintro ⟨p, _, hp⟩
    exact ⟨p, hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p, hQ p hp, hp⟩

end CompPoly.CPolynomial
