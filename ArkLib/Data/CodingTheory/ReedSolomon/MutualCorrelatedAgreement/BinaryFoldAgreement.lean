/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.FullAgreement
public import ArkLib.Data.Polynomial.SplitFold
public import Mathlib.Tactic.FinCases
/-!
# Exact binary-fold agreement on square-paired domains

This module bridges exact mutual correlated agreement (MCA) for one binary FRI fold back to
agreement of the parent polynomial. The domain is not an arbitrary pair of words: a
`SquarePairedDomain` supplies parent points `x` and `-x`, child point `x ^ 2`, nonzero roots, and
an embedded child domain. The assumption `NeZero (2 : F)` makes the even/odd change of basis
invertible and makes the two parent points distinct.

The parameter convention is child-facing. A theorem instantiated with child length `n`, child
degree bound `k`, and child agreement `AChild` reconstructs a parent word of length `2 * n`, a
parent polynomial of natural degree below `2 * k`, and at least `2 * AChild` parent agreements.
Consequently `AParent ≤ 2 * AChild` is exactly the backward-chain condition. In the LambdaVM
profile, the last curve certificate has child length `256` and child dimension `128`; it recovers
the parent stage of length `512`. No additional length-`128` certificate is introduced. The
argument assumes no commitment to the child word, so it also applies to the terminal uncommitted
fold.

## References

* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated
  Agreement up to Capacity*][DKTZ26], LambdaVM application and Appendix D.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial
open scoped BigOperators

noncomputable section

variable {F : Type} [Field F] {n : ℕ}

/-! ## Square-paired evaluation domains -/

/-- Data for one binary FRI domain step. The parent points above child coordinate `i` are
`root i` and `-root i`, while the child evaluation point is their common square. -/
structure SquarePairedDomain (F : Type) [Field F] (n : ℕ) where
  /-- A selected square root for each child coordinate. -/
  root : Fin n → F
  /-- The embedded child evaluation domain. -/
  child : Fin n ↪ F
  /-- FRI multiplicative-coset points are nonzero. -/
  root_ne_zero : ∀ i, root i ≠ 0
  /-- Squaring either member of a parent pair gives the child point. -/
  root_sq : ∀ i, root i ^ 2 = child i

/-- The parent point selected by a child coordinate and a binary side: side zero is `x` and side
one is `-x`. -/
def SquarePairedDomain.parentPoint (domain : SquarePairedDomain F n)
    (index : Fin n × Fin 2) : F :=
  if index.2 = 0 then domain.root index.1 else -domain.root index.1

/-- In characteristic different from two, the two square roots over every child coordinate form
an embedded parent domain. Child injectivity rules out collisions between different pairs. -/
theorem SquarePairedDomain.parentPoint_injective [NeZero (2 : F)]
    (domain : SquarePairedDomain F n) : Function.Injective domain.parentPoint := by
  rintro ⟨i, side⟩ ⟨j, side'⟩ hpoint
  have hsquare : domain.child i = domain.child j := by
    have hpow := congrArg (fun x : F ↦ x ^ 2) hpoint
    fin_cases side <;> fin_cases side' <;>
      simpa [SquarePairedDomain.parentPoint, domain.root_sq] using hpow
  have hij : i = j := domain.child.injective hsquare
  subst j
  have hroot_ne_neg : domain.root i ≠ -domain.root i := by
    intro hneg
    have hmul : (2 : F) * domain.root i = 0 := by
      calc
        (2 : F) * domain.root i = domain.root i + domain.root i := two_mul _
        _ = -domain.root i + domain.root i := congrArg (fun x ↦ x + domain.root i) hneg
        _ = 0 := neg_add_cancel _
    exact (mul_ne_zero (NeZero.ne 2) (domain.root_ne_zero i)) hmul
  have hside : side = side' := by
    fin_cases side <;> fin_cases side'
    · rfl
    · exact absurd (by simpa [SquarePairedDomain.parentPoint] using hpoint) hroot_ne_neg
    · exact absurd (by simpa [SquarePairedDomain.parentPoint] using hpoint.symm) hroot_ne_neg
    · rfl
  exact Prod.ext rfl hside

/-- The actual parent evaluation domain of cardinality `2 * n`. -/
def SquarePairedDomain.parent [NeZero (2 : F)]
    (domain : SquarePairedDomain F n) : Fin n × Fin 2 ↪ F :=
  ⟨domain.parentPoint, domain.parentPoint_injective⟩

@[simp]
theorem SquarePairedDomain.parent_apply [NeZero (2 : F)]
    (domain : SquarePairedDomain F n) (index : Fin n × Fin 2) :
    domain.parent index = domain.parentPoint index := rfl

/-- The square-paired parent index type has exactly twice the child cardinality. -/
theorem squarePairedParent_card : Fintype.card (Fin n × Fin 2) = 2 * n := by
  simp [Nat.mul_comm]

/-! ## Even/odd splitting of a parent word -/

/-- Even/odd child words derived from evaluations at the actual parent pair `x,-x`. Coordinate
zero is `(w(x) + w(-x)) / 2`; coordinate one is `(w(x) - w(-x)) / (2x)`. -/
def binarySplitWord (domain : SquarePairedDomain F n) (word : Fin n × Fin 2 → F) :
    Fin 2 → Fin n → F :=
  fun component i ↦
    if component = 0 then
      (word (i, 0) + word (i, 1)) / 2
    else
      (word (i, 0) - word (i, 1)) / (2 * domain.root i)

/-- The child word sent to the next FRI round at challenge `gamma`. -/
def binaryFoldedWord (domain : SquarePairedDomain F n) (word : Fin n × Fin 2 → F)
    (gamma : F) : Fin n → F :=
  powerBatchedWord (binarySplitWord domain word) gamma

/-- Recompose even and odd child polynomials into their parent polynomial
`P₀(X²) + X P₁(X²)`. -/
def binaryRecomposition (parts : Fin 2 → F[X]) : F[X] :=
  (parts 0).comp (X ^ 2) + X * (parts 1).comp (X ^ 2)

/-- ArkLib's `polyFold` of the recomposed parent is exactly the power-batched child polynomial. -/
theorem polyFold_binaryRecomposition (parts : Fin 2 → F[X]) (gamma : F) :
    FoldingPolynomial.polyFold (binaryRecomposition parts) 2 gamma =
      powerBatchedPolynomial parts gamma := by
  have h := Polynomial.polyFold_sum (u := parts) (r := gamma)
  simpa [binaryRecomposition, powerBatchedPolynomial, Polynomial.smul_eq_C_mul] using h

/-- Recomposition doubles the degree bound: child parts of natural degree below `k` give a
parent polynomial of natural degree below `2 * k`. Positivity of `k` handles zero parts
uniformly. -/
theorem binaryRecomposition_natDegree_lt {k : ℕ} (hk : 0 < k) (parts : Fin 2 → F[X])
    (hparts : ∀ component, (parts component).degree < k) :
    (binaryRecomposition parts).natDegree < 2 * k := by
  have hnat : ∀ component, (parts component).natDegree < k := by
    intro component
    by_cases hzero : parts component = 0
    · simpa [hzero] using hk
    · exact (Polynomial.natDegree_lt_iff_degree_lt hzero).mpr (hparts component)
  apply (Polynomial.natDegree_add_le _ _).trans_lt
  apply max_lt
  · calc
      ((parts 0).comp (X ^ 2)).natDegree
          ≤ (parts 0).natDegree * (X ^ 2 : F[X]).natDegree :=
        Polynomial.natDegree_comp_le
      _ = (parts 0).natDegree * 2 := by simp
      _ < 2 * k := by
        simpa [Nat.mul_comm] using Nat.mul_lt_mul_of_pos_right (hnat 0) (by omega)
  · calc
      (X * (parts 1).comp (X ^ 2)).natDegree
          ≤ X.natDegree + ((parts 1).comp (X ^ 2)).natDegree :=
        Polynomial.natDegree_mul_le
      _ ≤ 1 + (parts 1).natDegree * (X ^ 2 : F[X]).natDegree := by
        exact Nat.add_le_add (by simp) Polynomial.natDegree_comp_le
      _ = 1 + (parts 1).natDegree * 2 := by simp
      _ < 2 * k := by
        have hone := hnat (1 : Fin 2)
        omega

open Classical in
/-- Agreement positions of a parent polynomial against a square-paired parent word. -/
def pairedPolynomialAgreementSet [NeZero (2 : F)] (domain : SquarePairedDomain F n)
    (word : Fin n × Fin 2 → F) (parentPolynomial : F[X]) : Finset (Fin n × Fin 2) :=
  Finset.univ.filter fun index ↦ parentPolynomial.eval (domain.parent index) = word index

/-- If both even and odd child polynomials agree at `i`, their recomposition agrees with the
parent word at both points `x` and `-x` above `i`. -/
theorem binaryRecomposition_eval_eq_of_components [NeZero (2 : F)]
    (domain : SquarePairedDomain F n) (word : Fin n × Fin 2 → F)
    (parts : Fin 2 → F[X]) (i : Fin n)
    (hparts : ∀ component,
      (parts component).eval (domain.child i) = binarySplitWord domain word component i)
    (side : Fin 2) :
    (binaryRecomposition parts).eval (domain.parent (i, side)) = word (i, side) := by
  have htwo : (2 : F) ≠ 0 := NeZero.ne 2
  have hroot : domain.root i ≠ 0 := domain.root_ne_zero i
  fin_cases side <;>
    simp [binaryRecomposition, SquarePairedDomain.parent,
      SquarePairedDomain.parentPoint, Polynomial.eval_comp, domain.root_sq,
      hparts, binarySplitWord] <;>
    field_simp <;> ring

/-- Every common child agreement yields both parent agreements, so parent agreement cardinality
is at least twice the common child agreement cardinality. -/
theorem two_mul_commonAgreement_card_le_pairedAgreement_card [NeZero (2 : F)]
    (domain : SquarePairedDomain F n) (word : Fin n × Fin 2 → F)
    (parts : Fin 2 → F[X]) :
    2 * (commonCurveAgreementSet domain.child (binarySplitWord domain word) parts).card ≤
      (pairedPolynomialAgreementSet domain word (binaryRecomposition parts)).card := by
  classical
  let common := commonCurveAgreementSet domain.child (binarySplitWord domain word) parts
  have hsubset : common ×ˢ (Finset.univ : Finset (Fin 2)) ⊆
      pairedPolynomialAgreementSet domain word (binaryRecomposition parts) := by
    rintro ⟨i, side⟩ hindex
    have hi := (Finset.mem_product.mp hindex).1
    have hcomponents : ∀ component,
        (parts component).eval (domain.child i) =
          binarySplitWord domain word component i := by
      change i ∈ commonCurveAgreementSet domain.child (binarySplitWord domain word) parts at hi
      exact (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      binaryRecomposition_eval_eq_of_components domain word parts i hcomponents side⟩
  calc
    2 * common.card = (common ×ˢ (Finset.univ : Finset (Fin 2))).card := by
      simp [Nat.mul_comm]
    _ ≤ (pairedPolynomialAgreementSet domain word (binaryRecomposition parts)).card :=
      Finset.card_le_card hsubset

/-! ## Exact MCA and backward transfer -/

/-- Exact binary-fold MCA reconstructs a parent polynomial whose fold is the child candidate and
whose parent agreement cardinality is at least twice the child's full agreement cardinality. -/
theorem exists_binaryRecomposition_of_exactAgreement [NeZero (2 : F)]
    [DecidableEq F]
    (domain : SquarePairedDomain F n) (word : Fin n × Fin 2 → F)
    {k : ℕ} (hk : 0 < k) (gamma : F) (childPolynomial : F[X])
    (hexact : HasExactPowerAgreement domain.child (binarySplitWord domain word)
      (RingHom.id F) k gamma childPolynomial) :
    ∃ parts : Fin 2 → F[X],
      (∀ component, (parts component).degree < k) ∧
      childPolynomial = FoldingPolynomial.polyFold (binaryRecomposition parts) 2 gamma ∧
      (binaryRecomposition parts).natDegree < 2 * k ∧
      2 * (polynomialAgreementSet domain.child (binaryFoldedWord domain word gamma)
        childPolynomial).card ≤
        (pairedPolynomialAgreementSet domain word (binaryRecomposition parts)).card := by
  obtain ⟨parts, hdegree, hpolynomial, hagreement⟩ := hexact
  refine ⟨parts, hdegree, ?_, binaryRecomposition_natDegree_lt hk parts hdegree, ?_⟩
  · rw [polyFold_binaryRecomposition]
    simpa using hpolynomial
  · have hcard := two_mul_commonAgreement_card_le_pairedAgreement_card domain word parts
    have hagreement' :
        polynomialAgreementSet domain.child (binaryFoldedWord domain word gamma)
            childPolynomial =
          commonCurveAgreementSet domain.child (binarySplitWord domain word) parts := by
      simpa [binaryFoldedWord, mappedDomain] using hagreement
    rw [hagreement']
    exact hcard

/-- Backward transfer through one binary fold. All parameters `n`, `k`, and `AChild` describe the
child profile; the conclusion has parent cardinality `2 * n`, degree bound `2 * k`, and agreement
threshold `AParent`. No commitment hypothesis on the child word is used. -/
theorem exists_parentPolynomial_of_exactAgreement [NeZero (2 : F)]
    [DecidableEq F]
    (domain : SquarePairedDomain F n) (word : Fin n × Fin 2 → F)
    {k AChild AParent : ℕ} (hk : 0 < k) (hthreshold : AParent ≤ 2 * AChild)
    (gamma : F) (childPolynomial : F[X])
    (hchild : AChild ≤
      (polynomialAgreementSet domain.child (binaryFoldedWord domain word gamma)
        childPolynomial).card)
    (hexact : HasExactPowerAgreement domain.child (binarySplitWord domain word)
      (RingHom.id F) k gamma childPolynomial) :
    ∃ parentPolynomial : F[X],
      parentPolynomial.natDegree < 2 * k ∧
      childPolynomial = FoldingPolynomial.polyFold parentPolynomial 2 gamma ∧
      AParent ≤ (pairedPolynomialAgreementSet domain word parentPolynomial).card := by
  obtain ⟨parts, -, hfold, hdegree, hagreement⟩ :=
    exists_binaryRecomposition_of_exactAgreement domain word hk gamma childPolynomial hexact
  refine ⟨binaryRecomposition parts, hdegree, hfold, ?_⟩
  calc
    AParent ≤ 2 * AChild := hthreshold
    _ ≤ 2 * (polynomialAgreementSet domain.child (binaryFoldedWord domain word gamma)
        childPolynomial).card := Nat.mul_le_mul_left 2 hchild
    _ ≤ (pairedPolynomialAgreementSet domain word (binaryRecomposition parts)).card :=
      hagreement

end

end ReedSolomon
