/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerAlgebra.SplitZeroUnit
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Positive tower normalization

Positive base factors have proof-only geometric roots. Specializing at one such root proves
that a monic D5 quotient is nonzero and that canonical coefficient reduction preserves its fiber
degree. These facts justify discarding precisely empty components in `SplitZeroUnit` and
`PreprocessFiber`.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.TowerAlgebra

open CompPoly Polynomial FirstOrderNormDecoder.D5

variable {F : Type} [Field F] [BEq F] [LawfulBEq F]

/-- A monic positive-degree base factor has a root in the algebraic closure. This is a semantic
witness only; none of the finite-tower programs computes or stores it. -/
theorem exists_base_root (G : CPolynomial F) (_hG : G.monic) (hpos : 0 < G.natDegree) :
    ∃ u : AlgebraicClosure F, G.toPoly.eval₂ (algebraMap F (AlgebraicClosure F)) u = 0 := by
  apply IsAlgClosed.exists_eval₂_eq_zero_of_injective _
    (algebraMap F (AlgebraicClosure F)).injective
  apply ne_of_gt
  rw [← Polynomial.natDegree_pos_iff_degree_pos]
  simpa only [CPolynomial.natDegree_toPoly] using hpos

/-- Monic coefficient reduction preserves the exact fiber degree on a positive base factor. -/
theorem natDegree_reduceBase (G : CPolynomial F) (hG : G.monic) (hpos : 0 < G.natDegree)
    (p : CPolynomial (CPolynomial F)) (hp : p.monic) :
    (TowerRepresentation.reduceBase G p).natDegree = p.natDegree := by
  obtain ⟨u, hu⟩ := exists_base_root G hG hpos
  have he := specialize_reduceFiberCoefficients
    (algebraMap F (AlgebraicClosure F)) u hG hu p
  have hleft := (CPolynomial.monic_toPoly_iff _).mp
    (TowerRepresentation.monic_reduceBase hG hpos hp)
  change (reduceFiberCoefficients G p).toPoly.Monic at hleft
  have hright := (CPolynomial.monic_toPoly_iff _).mp hp
  have hn := congrArg Polynomial.natDegree he
  simpa only [TowerRepresentation.reduceBase, specializeFiberCPolynomial, hleft.natDegree_map,
    hright.natDegree_map,
    ← CPolynomial.natDegree_toPoly] using hn

/-- Dividing a monic dividend by its terminal D5 gcd never produces a zero quotient on a
positive base branch. -/
theorem terminalQuotientPolynomial_ne_zero (state : TowerState (F := F))
    (hmonic : state.dividend.toCPolynomial.monic)
    (terminal : TerminalGCDBranch (F := F)) (ht : terminal ∈ factorTower state)
    (hpos : 0 < terminal.modulus.natDegree) : terminalQuotientPolynomial state terminal ≠ 0 := by
  have hi := factorTower_terminal_invariants state terminal ht
  obtain ⟨u, hu⟩ := exists_base_root terminal.modulus hi.2.1 hpos
  have hm : (state.dividend.specialize (algebraMap F (AlgebraicClosure F)) u).Monic :=
    ((CPolynomial.monic_toPoly_iff _).mp hmonic).map _
  have he := terminal_gcd_mul_terminalQuotient_specialize
    state hmonic terminal ht (algebraMap F (AlgebraicClosure F)) u hu
  intro hz
  have hquot : (makeTerminalQuotientBranch state terminal).quotient.specialize
      (algebraMap F (AlgebraicClosure F)) u = 0 := by
    change (FiberPolynomial.ofCPolynomial
      (terminalQuotientPolynomial state terminal)).specialize _ _ = 0
    rw [FiberPolynomial.specialize_ofCPolynomial, hz]
    simp [specializeFiberCPolynomial, CPolynomial.toPoly_zero]
  rw [hquot, mul_zero] at he
  exact hm.ne_zero he.symm

/-- The two terminal D5 fibers partition the parent's fiber degree exactly. -/
theorem terminal_fiber_degree_sum (state : TowerState (F := F))
    (hmonic : state.dividend.toCPolynomial.monic)
    (terminal : TerminalGCDBranch (F := F)) (ht : terminal ∈ factorTower state)
    (hpos : 0 < terminal.modulus.natDegree) :
    terminal.gcdPolynomial.toCPolynomial.natDegree +
      (terminalQuotientPolynomial state terminal).natDegree =
        state.dividend.toCPolynomial.natDegree := by
  have hi := factorTower_terminal_invariants state terminal ht
  obtain ⟨u, hu⟩ := exists_base_root terminal.modulus hi.2.1 hpos
  have hg := factorTower_terminal_gcd_monic state hmonic terminal ht
  have hq := terminalQuotientPolynomial_monic_of_ne_zero state hmonic terminal ht hpos
    (terminalQuotientPolynomial_ne_zero state hmonic terminal ht hpos)
  have he := terminal_gcd_mul_terminalQuotient_specialize
    state hmonic terminal ht (algebraMap F (AlgebraicClosure F)) u hu
  have hg' := ((CPolynomial.monic_toPoly_iff _).mp hg).map
    (coefficientEval (algebraMap F (AlgebraicClosure F)) u)
  have hq' := ((CPolynomial.monic_toPoly_iff _).mp hq).map
    (coefficientEval (algebraMap F (AlgebraicClosure F)) u)
  simp only [makeTerminalQuotientBranch, FiberPolynomial.specialize,
    FiberPolynomial.toCPolynomial_ofCPolynomial, specializeFiberCPolynomial] at he
  have hn := congrArg Polynomial.natDegree he
  rw [Polynomial.natDegree_mul hg'.ne_zero hq'.ne_zero] at hn
  simpa only [makeTerminalQuotientBranch, FiberPolynomial.specialize_ofCPolynomial,
    FiberPolynomial.specialize, specializeFiberCPolynomial,
    ((CPolynomial.monic_toPoly_iff _).mp hg).natDegree_map,
    ((CPolynomial.monic_toPoly_iff _).mp hq).natDegree_map,
    ((CPolynomial.monic_toPoly_iff _).mp hmonic).natDegree_map,
    ← CPolynomial.natDegree_toPoly] using hn

end ReedSolomon.ListDecoding.TowerAlgebra
