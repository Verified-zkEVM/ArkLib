/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.Machine

/-!
# Completeness and finite size of agreement splitting

A wanted represented root follows exactly one child at each gcd split. If it has enough
remaining agreements, that path reaches a stopped block. The proof follows the actual recursive
program; it does not supply a list of roots to the runtime.

The number of interpolation attempts is bounded by the degree of the initial modulus. Each
nonconstant stopped factor spends at least one degree, and an exact gcd split preserves the sum
of the two child degrees. Repeated representations may still yield the same message, so final
coefficient-vector deduplication remains necessary.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.AgreementRecovery

open CompPoly Polynomial

variable {E index : Type*} [Field E] [BEq E] [LawfulBEq E]

/-- Stopping a branch removes its factor from later scans without increasing the total retained
degree. This invariant is stronger than an output count: it also accounts for nonlinear factors
whose roots all produce the same message. -/
theorem split_degree_sum_le (k : ℕ) (equations : List (index × CPolynomial E))
    (block : Block E index) :
    ((split k equations block).map fun out => out.factor.natDegree).sum ≤
      block.factor.natDegree := by
  classical
  induction equations generalizing block with
  | nil =>
      simp only [split]
      split_ifs <;> simp
  | cons row rest ih =>
      rcases row with ⟨i, e⟩
      simp only [split]
      split_ifs with hzero hstop
      · simp
      · simp
      · rw [List.map_append, List.sum_append]
        have hne : block.factor ≠ 0 := by
          intro h
          apply hzero
          rw [h, CPolynomial.natDegree_toPoly, CPolynomial.toPoly_zero]
          exact Polynomial.natDegree_zero
        have hsum := CPolynomial.natDegree_gcdFactor_add_gcdComplement
          (h := block.factor) (e := e) hne
        rw [← CPolynomial.natDegree_toPoly, ← CPolynomial.natDegree_toPoly,
          ← CPolynomial.natDegree_toPoly] at hsum
        exact (Nat.add_le_add
          (ih ⟨CPolynomial.gcdFactor block.factor e, i :: block.positions⟩)
          (ih ⟨CPolynomial.gcdComplement block.factor e, block.positions⟩)).trans_eq hsum

/-- The split tree produces at most one interpolation attempt per degree of the initial
modulus. No assumption about the number of distinct message images is used. -/
theorem split_length_le (k : ℕ) (equations : List (index × CPolynomial E))
    (block : Block E index) : (split k equations block).length ≤ block.factor.natDegree := by
  have hlength : ∀ outputs : List (Block E index),
      (∀ out ∈ outputs, 0 < out.factor.natDegree) →
      outputs.length ≤ (outputs.map fun out => out.factor.natDegree).sum := by
    intro outputs
    induction outputs with
    | nil => simp
    | cons out rest ih =>
        intro hpos
        have hhead := hpos out (by simp)
        have htail := ih (fun b hb => hpos b (List.mem_cons_of_mem _ hb))
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        omega
  exact (hlength _ (fun out hout => split_factor_natDegree_pos k equations block out hout)).trans
    (split_degree_sum_le k equations block)

noncomputable section

variable {L : Type*} [Field L]

/-- A represented root with at least `k` agreements survives to a stopped block. The predicate
`good` records genuine agreement positions; each indexed residual must test that predicate at
this root. The caller derives that equivalence from `FiniteRepresentation.residual_eq_zero_iff`.
-/
theorem exists_mem_split_of_enough_agreements (k : ℕ)
    (equations : List (index × CPolynomial E)) (block : Block E index)
    (ι : E →+* L) (θ : L) (good : index → Prop) [DecidablePred good]
    (hsquarefree : Squarefree block.factor.toPoly)
    (hroot : block.factor.toPoly.eval₂ ι θ = 0)
    (hrecorded : ∀ i ∈ block.positions, good i)
    (hequations : ∀ row ∈ equations, row.2.toPoly.eval₂ ι θ = 0 ↔ good row.1)
    (henough : k ≤ block.positions.length + equations.countP (fun row => decide (good row.1))) :
    ∃ out ∈ split k equations block,
      out.factor.toPoly.eval₂ ι θ = 0 ∧ ∀ i ∈ out.positions, good i := by
  classical
  have hpos : 0 < block.factor.natDegree := by
    rw [CPolynomial.natDegree_toPoly]
    exact Polynomial.natDegree_pos_of_eval₂_root hsquarefree.ne_zero ι hroot
      (fun x hx => ι.injective (hx.trans ι.map_zero.symm))
  induction equations generalizing block with
  | nil =>
      have hstop : k ≤ block.positions.length := by simpa using henough
      refine ⟨block, ?_, hroot, hrecorded⟩
      simp [split, Nat.ne_of_gt hpos, hstop]
  | cons row rest ih =>
      rcases row with ⟨i, e⟩
      by_cases hstop : k ≤ block.positions.length
      · refine ⟨block, ?_, hroot, hrecorded⟩
        simp [split, Nat.ne_of_gt hpos, hstop]
      · have hne : block.factor ≠ 0 := by
          exact (CPolynomial.toPoly_eq_zero_iff _).not.mp hsquarefree.ne_zero
        have htest : e.toPoly.eval₂ ι θ = 0 ↔ good i :=
          hequations (i, e) (by simp)
        have hrest : ∀ row ∈ rest, row.2.toPoly.eval₂ ι θ = 0 ↔ good row.1 := by
          intro row hrow
          exact hequations row (List.mem_cons_of_mem _ hrow)
        by_cases hgood : good i
        · have hgroot := (CPolynomial.eval₂_gcdFactor_eq_zero_iff_left_right
            ι θ block.factor e).mpr ⟨hroot, htest.mpr hgood⟩
          have hgfree := CPolynomial.gcdFactor_squarefree (e := e) hsquarefree
          have hgpos : 0 < (CPolynomial.gcdFactor block.factor e).natDegree := by
            rw [CPolynomial.natDegree_toPoly]
            exact Polynomial.natDegree_pos_of_eval₂_root hgfree.ne_zero ι hgroot
              (fun x hx => ι.injective (hx.trans ι.map_zero.symm))
          obtain ⟨out, hout, hr, hm⟩ := ih
            ⟨CPolynomial.gcdFactor block.factor e, i :: block.positions⟩ hgfree hgroot
            (by simpa using And.intro hgood hrecorded) hrest
            (by simp [hgood] at henough ⊢; omega) hgpos
          refine ⟨out, ?_, hr, hm⟩
          simp only [split, if_neg (Nat.ne_of_gt hpos), if_neg hstop]
          exact List.mem_append_left _ hout
        · have hqroot := (CPolynomial.eval₂_gcdComplement_eq_zero_iff_left_and_right_ne_zero
            ι θ hne hsquarefree).mpr ⟨hroot, fun hz => hgood (htest.mp hz)⟩
          have hqfree := CPolynomial.gcdComplement_squarefree (e := e) hne hsquarefree
          have hqpos : 0 < (CPolynomial.gcdComplement block.factor e).natDegree := by
            rw [CPolynomial.natDegree_toPoly]
            exact Polynomial.natDegree_pos_of_eval₂_root hqfree.ne_zero ι hqroot
              (fun x hx => ι.injective (hx.trans ι.map_zero.symm))
          obtain ⟨out, hout, hr, hm⟩ := ih
            ⟨CPolynomial.gcdComplement block.factor e, block.positions⟩ hqfree hqroot
            hrecorded hrest (by simpa [List.countP_cons, hgood] using henough) hqpos
          refine ⟨out, ?_, hr, hm⟩
          simp only [split, if_neg (Nat.ne_of_gt hpos), if_neg hstop]
          exact List.mem_append_right _ hout

end
end ReedSolomon.ListDecoding.AgreementRecovery
