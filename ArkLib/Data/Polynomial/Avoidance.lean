/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Data.Finset.Prod

/-!
# Avoiding finitely many polynomial root sets

A nonzero degree-d polynomial has at most d roots, even in an extension field. Consequently,
a sufficiently long distinct list of base-field candidates contains a point avoiding an entire
finite family. The root sets occur only in the proof; no executable root enumeration is required.
-/

@[expose] public section

namespace Polynomial

section FinitePolynomialAvoidance

variable {F K : Type*} [Field F] [Field K]

/-- Roots of any finite collection of nonzero degree-`d` polynomials occupy at
most `number of polynomials * d` points. -/
theorem exists_avoiding_finite_polynomials
    (ι : F →+* K) (polynomials : Finset K[X]) (degreeBound : ℕ)
    (hnonzero : ∀ polynomial ∈ polynomials, polynomial ≠ 0)
    (hdegree : ∀ polynomial ∈ polynomials, polynomial.natDegree ≤ degreeBound)
    (candidates : List F) (hnodup : candidates.Nodup)
    (hlength : polynomials.card * degreeBound < candidates.length) :
    ∃ ε ∈ candidates, ∀ polynomial ∈ polynomials,
      polynomial.eval (ι ε) ≠ 0 := by
  classical
  let bad : Finset K := polynomials.biUnion fun polynomial ↦ polynomial.roots.toFinset
  have hbadCard : bad.card ≤ polynomials.card * degreeBound := by
    refine (Finset.card_biUnion_le_card_mul polynomials
      (fun polynomial ↦ polynomial.roots.toFinset) degreeBound ?_).trans_eq rfl
    intro polynomial hpolynomial
    exact (Multiset.toFinset_card_le polynomial.roots).trans
      ((Polynomial.card_roots' polynomial).trans (hdegree polynomial hpolynomial))
  by_contra hcontra
  simp only [not_exists, not_and, not_forall, not_not] at hcontra
  have hsubset : (candidates.map ι).toFinset ⊆ bad := by
    intro value hvalue
    obtain ⟨ε, hε, rfl⟩ := List.mem_map.mp (by simpa using hvalue)
    obtain ⟨polynomial, hpolynomial, heval⟩ := hcontra ε hε
    exact Finset.mem_biUnion.mpr ⟨polynomial, hpolynomial, by
      simpa [Polynomial.mem_roots (hnonzero polynomial hpolynomial)] using heval⟩
  have hmappedNodup : (candidates.map ι).Nodup := hnodup.map ι.injective
  have hcandidatesCard : candidates.length ≤ bad.card := by
    calc
      candidates.length = (candidates.map ι).toFinset.card := by
        rw [List.toFinset_card_of_nodup hmappedNodup]
        simp
      _ ≤ bad.card := Finset.card_le_card hsubset
  omega

end FinitePolynomialAvoidance

end Polynomial
