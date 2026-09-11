/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5.RemainderStep

/-!
# Canonical bounded-fiber representatives

This file converts an executable nested `CPolynomial` back to the descending coefficient-list
representation used by the D5 remainder step.  The zero polynomial is represented by the empty
list; a nonzero polynomial of degree `d` is represented by exactly `d + 1` coefficients.  The
conversion is executable and is an exact inverse to `FiberPolynomial.toCPolynomial` on its image.

The final definitions package the next Euclidean pair on a unit-leading branch.  They do not yet
build the recursive factor tower or claim a complete D5 gcd algorithm.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5

open CompPoly Polynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

local instance : DecidableEq F := instDecidableEqOfLawfulBEq
local instance : DecidableEq (CPolynomial F) := instDecidableEqOfLawfulBEq

/-- Descending coefficients of a canonical polynomial, with zero represented by the empty list. -/
def descendingCoefficients (p : CPolynomial (CPolynomial F)) : List (CPolynomial F) :=
  if p == 0 then []
  else List.ofFn fun i : Fin (p.natDegree + 1) => p.coeff (p.natDegree - i)

/-- Canonically convert a nested executable polynomial back to bounded-fiber form. -/
def FiberPolynomial.ofCPolynomial (p : CPolynomial (CPolynomial F)) :
    FiberPolynomial (F := F) :=
  ⟨descendingCoefficients p⟩

/-- Coefficients of a polynomial assembled from a descending list. -/
theorem coeff_ofDescending (coefficients : List (CPolynomial F)) (i : ℕ) :
    (ofDescending coefficients).coeff i =
      if i < coefficients.length then
        coefficients.getD (coefficients.length - 1 - i) 0
      else 0 := by
  induction coefficients with
  | nil => rw [ofDescending, CPolynomial.coeff_zero]; rfl
  | cons coefficient coefficients ih =>
      rw [ofDescending, CPolynomial.coeff_add, CPolynomial.coeff_monomial, ih]
      by_cases hi : i < coefficients.length
      · have hne : i ≠ coefficients.length := by omega
        have hpos : 0 < coefficients.length - i := by omega
        simp only [hne, if_false, hi, if_true, zero_add, List.length_cons]
        rw [show coefficients.length + 1 - 1 - i =
            (coefficients.length - 1 - i) + 1 by omega,
          List.getD_cons_succ]
        simp [Nat.lt_succ_of_lt hi]
      · by_cases heq : i = coefficients.length
        · subst i
          simp
        · have hgt : coefficients.length < i := by omega
          simp [hi, heq, hgt, List.length_cons]

/-- The canonical descending list has width `natDegree + 1` for every nonzero polynomial. -/
theorem length_descendingCoefficients_of_ne_zero
    {p : CPolynomial (CPolynomial F)} (hp : p ≠ 0) :
    (descendingCoefficients p).length = p.natDegree + 1 := by
  simp [descendingCoefficients, hp]

/-- Zero has the explicit empty descending representation. -/
@[simp] theorem descendingCoefficients_zero :
    descendingCoefficients (0 : CPolynomial (CPolynomial F)) = [] := by
  simp [descendingCoefficients]

/-- The canonical conversion exactly reconstructs every nested executable polynomial. -/
theorem ofDescending_descendingCoefficients (p : CPolynomial (CPolynomial F)) :
    ofDescending (descendingCoefficients p) = p := by
  by_cases hp : p = 0
  · subst p
    simp [ofDescending]
  · apply (CPolynomial.eq_iff_coeff).2
    intro i
    have hdescending : descendingCoefficients p =
        List.ofFn fun i : Fin (p.natDegree + 1) => p.coeff (p.natDegree - i) := by
      simp [descendingCoefficients, hp]
    rw [coeff_ofDescending, hdescending, List.length_ofFn]
    by_cases hi : i < p.natDegree + 1
    · rw [if_pos hi]
      simp only [List.getD_eq_getElem?_getD]
      have hindex : p.natDegree + 1 - 1 - i < p.natDegree + 1 := by omega
      have hindex' : p.natDegree + 1 - 1 - i <
          (List.ofFn fun i : Fin (p.natDegree + 1) =>
            p.coeff (p.natDegree - i)).length := by simp
      rw [List.getElem?_eq_getElem hindex', Option.getD_some, List.getElem_ofFn]
      change p.coeff (p.natDegree - (p.natDegree + 1 - 1 - i)) = p.coeff i
      congr 1
      omega
    · rw [if_neg hi]
      symm
      by_contra hcoeff
      have hile := CPolynomial.le_natDegree_of_ne_zero hcoeff
      omega

/-- Converting to canonical fiber form and back is an exact executable roundtrip. -/
@[simp] theorem FiberPolynomial.toCPolynomial_ofCPolynomial
    (p : CPolynomial (CPolynomial F)) :
    (FiberPolynomial.ofCPolynomial p).toCPolynomial = p :=
  ofDescending_descendingCoefficients p

/-- Canonical conversion preserves specialization over every coefficient-field extension. -/
theorem FiberPolynomial.specialize_ofCPolynomial
    {K : Type*} [Field K] (p : CPolynomial (CPolynomial F))
    (phi : F →+* K) (x : K) :
    (FiberPolynomial.ofCPolynomial p).specialize phi x =
      specializeFiberCPolynomial p phi x := by
  rw [FiberPolynomial.specialize, FiberPolynomial.toCPolynomial_ofCPolynomial]

/-- Canonical conversion of zero is the explicit empty bounded-fiber polynomial. -/
@[simp] theorem FiberPolynomial.ofCPolynomial_zero :
    FiberPolynomial.ofCPolynomial (0 : CPolynomial (CPolynomial F)) = ⟨[]⟩ := by
  simp [FiberPolynomial.ofCPolynomial]

/-- Width of the canonical bounded-fiber representative of a nonzero polynomial. -/
theorem FiberPolynomial.coefficients_length_ofCPolynomial_of_ne_zero
    {p : CPolynomial (CPolynomial F)} (hp : p ≠ 0) :
    (FiberPolynomial.ofCPolynomial p).coefficients.length = p.natDegree + 1 :=
  length_descendingCoefficients_of_ne_zero hp

/-- Coefficient reduction of zero remains zero, including the canonical empty-array boundary. -/
theorem reduceFiberCoefficients_zero (g : CPolynomial F) (hgmonic : g.monic) :
    reduceFiberCoefficients g (0 : CPolynomial (CPolynomial F)) = 0 := by
  apply (CPolynomial.eq_zero_iff_coeff_zero).2
  intro i
  rw [coeff_reduceFiberCoefficients]
  split
  · rw [CPolynomial.coeff_zero]
    apply (CPolynomial.toPoly_eq_zero_iff _).mp
    rw [CPolynomial.modByMonic_toPoly_eq_modByMonic _ _ hgmonic]
    rw [CPolynomial.toPoly_zero]
    exact Polynomial.zero_modByMonic g.toPoly
  · rfl

/-- Canonical coefficient reduction cannot increase outer natural degree when its result is
nonzero. -/
theorem natDegree_reduceFiberCoefficients_le (g : CPolynomial F)
    (p : CPolynomial (CPolynomial F))
    (hreduce : reduceFiberCoefficients g p ≠ 0) :
    (reduceFiberCoefficients g p).natDegree ≤ p.natDegree := by
  by_contra hdegree
  have houtside : ¬(reduceFiberCoefficients g p).natDegree < p.natDegree + 1 := by omega
  have hcoefficient := coeff_reduceFiberCoefficients g p
    (reduceFiberCoefficients g p).natDegree
  simp only [houtside] at hcoefficient
  have hleading := CPolynomial.leadingCoeff_ne_zero hreduce
  rw [CPolynomial.leadingCoeff_eq_coeff_natDegree, hcoefficient] at hleading
  exact hleading rfl

/-- Executable monic remainder has strictly smaller outer natural degree whenever it is nonzero. -/
theorem natDegree_modByMonic_lt (p q : CPolynomial (CPolynomial F))
    (hqmonic : q.monic) (hremainder : p.modByMonic q ≠ 0) :
    (p.modByMonic q).natDegree < q.natDegree := by
  have hqpoly : q.toPoly.Monic := (CPolynomial.monic_toPoly_iff q).mp hqmonic
  have hdegree : (p.modByMonic q).toPoly.degree < q.toPoly.degree := by
    rw [CPolynomial.modByMonic_toPoly_eq_modByMonic p q hqmonic]
    exact Polynomial.degree_modByMonic_lt p.toPoly hqpoly
  rw [← CPolynomial.degree_toPoly, ← CPolynomial.degree_toPoly,
    CPolynomial.degree_eq_natDegree _ hremainder,
    CPolynomial.degree_eq_natDegree _
      ((CPolynomial.toPoly_eq_zero_iff q).not.mp hqpoly.ne_zero)] at hdegree
  exact WithBot.coe_lt_coe.mp hdegree

/-- The next normalized Euclidean pair on one unit-leading base branch. -/
structure EuclideanPair where
  dividend : FiberPolynomial (F := F)
  divisor : FiberPolynomial (F := F)

/-- Build the next Euclidean pair: normalized old divisor followed by its reduced remainder. -/
def nextUnitPair (modulus inverse leading : CPolynomial F)
    (lower : List (CPolynomial F)) (dividend : FiberPolynomial (F := F)) :
    EuclideanPair (F := F) :=
  let normalized := normalizedDivisor modulus inverse (leading :: lower)
  let remainder := reduceFiberCoefficients modulus
    (dividend.toCPolynomial.modByMonic normalized)
  ⟨FiberPolynomial.ofCPolynomial normalized, FiberPolynomial.ofCPolynomial remainder⟩

/-- One regularized branch paired with its optional next Euclidean state. -/
structure PairUpdateBranch where
  leading : LeadingBranch (F := F)
  nextPair : Option (EuclideanPair (F := F))

/-- Turn one leading-coefficient branch into a recursive Euclidean state.  Terminal zero branches
carry `none`; unit-leading branches carry the normalized divisor/remainder pair. -/
def makePairUpdateBranch (dividend : FiberPolynomial (F := F))
    (branch : LeadingBranch (F := F)) : PairUpdateBranch (F := F) :=
  match branch.coefficients, branch.leadingInverse with
  | [], none => ⟨branch, none⟩
  | leading :: lower, some inverse =>
      ⟨branch, some (nextUnitPair branch.modulus inverse leading lower dividend)⟩
  | _, _ => ⟨branch, none⟩

/-- Compute the next recursive Euclidean state on every regularized base branch. -/
def pairUpdate (g : CPolynomial F) (dividend divisor : FiberPolynomial (F := F)) :
    List (PairUpdateBranch (F := F)) :=
  (splitLeading divisor.coefficients g).map (makePairUpdateBranch dividend)

/-- Every unit-leading regularization branch appears with its executable next pair. -/
theorem unitBranch_mem_pairUpdate (g : CPolynomial F)
    (dividend divisor : FiberPolynomial (F := F))
    (modulus leading inverse : CPolynomial F) (lower : List (CPolynomial F))
    (hbranch : (⟨modulus, leading :: lower, some inverse⟩ : LeadingBranch (F := F)) ∈
      splitLeading divisor.coefficients g) :
    (⟨⟨modulus, leading :: lower, some inverse⟩,
      some (nextUnitPair modulus inverse leading lower dividend)⟩ :
        PairUpdateBranch (F := F)) ∈ pairUpdate g dividend divisor := by
  simpa [pairUpdate, makePairUpdateBranch] using List.mem_map_of_mem hbranch

/-- Every terminal zero regularization branch appears without a recursive division state. -/
theorem zeroBranch_mem_pairUpdate (g : CPolynomial F)
    (dividend divisor : FiberPolynomial (F := F)) (modulus : CPolynomial F)
    (hbranch : (⟨modulus, [], none⟩ : LeadingBranch (F := F)) ∈
      splitLeading divisor.coefficients g) :
    (⟨⟨modulus, [], none⟩, none⟩ : PairUpdateBranch (F := F)) ∈
      pairUpdate g dividend divisor := by
  simpa [pairUpdate, makePairUpdateBranch] using List.mem_map_of_mem hbranch

/-- The first member of the next pair is exactly the executable normalized divisor. -/
@[simp] theorem nextUnitPair_dividend_toCPolynomial
    (modulus inverse leading : CPolynomial F) (lower : List (CPolynomial F))
    (dividend : FiberPolynomial (F := F)) :
    (nextUnitPair modulus inverse leading lower dividend).dividend.toCPolynomial =
      normalizedDivisor modulus inverse (leading :: lower) := by
  simp [nextUnitPair]

/-- The second member of the next pair is exactly the reduced executable remainder. -/
@[simp] theorem nextUnitPair_divisor_toCPolynomial
    (modulus inverse leading : CPolynomial F) (lower : List (CPolynomial F))
    (dividend : FiberPolynomial (F := F)) :
    (nextUnitPair modulus inverse leading lower dividend).divisor.toCPolynomial =
      reduceFiberCoefficients modulus
        (dividend.toCPolynomial.modByMonic
          (normalizedDivisor modulus inverse (leading :: lower))) := by
  simp [nextUnitPair]

/-- Every nonzero unit-branch pair update strictly decreases the syntactic outer-degree measure,
independently of later geometric specialization. -/
theorem nextUnitPair_divisor_natDegree_lt_dividend
    (modulus inverse leading : CPolynomial F) (lower : List (CPolynomial F))
    (dividend : FiberPolynomial (F := F))
    (hmodulusMonic : modulus.monic)
    (hremainder : reduceFiberCoefficients modulus
        (dividend.toCPolynomial.modByMonic
          (normalizedDivisor modulus inverse (leading :: lower))) ≠ 0) :
    (nextUnitPair modulus inverse leading lower dividend).divisor.toCPolynomial.natDegree <
      (nextUnitPair modulus inverse leading lower dividend).dividend.toCPolynomial.natDegree := by
  rw [nextUnitPair_divisor_toCPolynomial, nextUnitPair_dividend_toCPolynomial]
  let normalized := normalizedDivisor modulus inverse (leading :: lower)
  let rawRemainder := dividend.toCPolynomial.modByMonic normalized
  have hraw : rawRemainder ≠ 0 := by
    intro hzero
    apply hremainder
    change reduceFiberCoefficients modulus rawRemainder = 0
    rw [hzero]
    exact reduceFiberCoefficients_zero modulus hmodulusMonic
  exact (natDegree_reduceFiberCoefficients_le modulus rawRemainder hremainder).trans_lt
    (natDegree_modByMonic_lt dividend.toCPolynomial normalized
      ((CPolynomial.monic_toPoly_iff normalized).mpr
        (normalizedDivisor_monic modulus inverse leading lower)) hraw)

/-- Every nonzero recursive state returned from a genuine unit branch strictly decreases outer
degree.  Parent monicity and squarefreeness supply the child-modulus guard required above. -/
theorem unitBranch_pairUpdate_measure_decreases
    {g : CPolynomial F} (hg : g ≠ 0) (hgmonic : g.monic)
    (hgfree : Squarefree g.toPoly)
    (dividend divisor : FiberPolynomial (F := F))
    (modulus leading inverse : CPolynomial F) (lower : List (CPolynomial F))
    (hbranch : (⟨modulus, leading :: lower, some inverse⟩ : LeadingBranch (F := F)) ∈
      splitLeading divisor.coefficients g)
    (hremainder : reduceFiberCoefficients modulus
        (dividend.toCPolynomial.modByMonic
          (normalizedDivisor modulus inverse (leading :: lower))) ≠ 0) :
    (nextUnitPair modulus inverse leading lower dividend).divisor.toCPolynomial.natDegree <
      (nextUnitPair modulus inverse leading lower dividend).dividend.toCPolynomial.natDegree := by
  have hmodulusMonic :=
    (splitLeading_monic_squarefree divisor.coefficients hg hgmonic hgfree
      (⟨modulus, leading :: lower, some inverse⟩ : LeadingBranch (F := F)) hbranch).1
  exact nextUnitPair_divisor_natDegree_lt_dividend modulus inverse leading lower dividend
    hmodulusMonic hremainder

end ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5
