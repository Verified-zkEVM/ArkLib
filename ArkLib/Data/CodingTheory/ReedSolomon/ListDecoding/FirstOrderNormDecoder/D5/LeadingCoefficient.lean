/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5.CoefficientSplit

/-!
# Dynamic leading-coefficient descent

The Euclidean algorithm in the bounded fiber variable cannot inspect a leading coefficient in
`E[u] / g` as though that quotient were a field.  This module supplies the terminating D5 descent
that makes the inspection valid.  Coefficients are listed from highest to lowest fiber degree.
At each step the current squarefree base modulus is split into the locus where the leading
coefficient is a unit and the locus where it vanishes.  The unit branch stops with a computed
inverse; the zero branch deletes that coefficient and recurses on the shorter list.

The returned base factors preserve the exact degree budget and partition every geometric root of
the input modulus.  This is the degree-regularization step needed inside a later bounded-fiber
Euclidean algorithm; it neither implements that complete gcd nor makes a runtime claim.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5

open CompPoly Polynomial

variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- One base component on which a descending coefficient list is either zero or has an invertible
leading coefficient. -/
structure LeadingBranch where
  modulus : CPolynomial F
  coefficients : List (CPolynomial F)
  leadingInverse : Option (CPolynomial F)

/-- Follow zero leading coefficients until the first unit coefficient, splitting the squarefree
base modulus whenever the current coefficient is a zero divisor. -/
def splitLeading : List (CPolynomial F) → CPolynomial F → List (LeadingBranch (F := F))
  | [], g => [⟨g, [], none⟩]
  | a :: coefficients, g =>
      match coefficientSplit? g a with
      | none => []
      | some split =>
          ⟨split.unitModulus, a :: coefficients, some split.unitInverse⟩ ::
            splitLeading coefficients split.zeroModulus

/-- Semantic leaf condition at one geometric base point: all deleted leading coefficients vanish,
and the first retained coefficient has the returned scalar inverse. -/
def LeadingBranch.Follows (branch : LeadingBranch (F := F))
    (input : List (CPolynomial F)) {K : Type*} [Field K] (phi : F →+* K) (x : K) : Prop :=
  ∃ dropped, input = dropped ++ branch.coefficients ∧
    (∀ coefficient ∈ dropped, coefficient.toPoly.eval₂ phi x = 0) ∧
    match branch.coefficients, branch.leadingInverse with
    | [], none => True
    | leading :: _, some inverse =>
        leading.toPoly.eval₂ phi x * inverse.toPoly.eval₂ phi x = 1
    | _, _ => False

/-- Executable leaf invariant: a nonzero fiber polynomial carries an inverse of its leading
coefficient modulo the returned base factor; the zero polynomial carries no inverse. -/
def LeadingBranch.Ready (branch : LeadingBranch (F := F)) : Prop :=
  match branch.coefficients, branch.leadingInverse with
  | [], none => True
  | leading :: _, some inverse =>
      CPolynomial.inverseMod? leading branch.modulus = some inverse
  | _, _ => False

/-- Successful coefficient splitting exposes the unit branch and the strictly shorter zero
branch used by the recursive descent. -/
theorem splitLeading_cons_of_eq_some
    {g a : CPolynomial F} {coefficients : List (CPolynomial F)}
    {split : CoefficientSplit (F := F)} (hsplit : coefficientSplit? g a = some split) :
    splitLeading (a :: coefficients) g =
      ⟨split.unitModulus, a :: coefficients, some split.unitInverse⟩ ::
        splitLeading coefficients split.zeroModulus := by
  simp [splitLeading, hsplit]

/-- Every branch returned by the descent satisfies its executable zero-or-unit leaf invariant. -/
theorem splitLeading_ready (coefficients : List (CPolynomial F)) (g : CPolynomial F) :
    ∀ branch ∈ splitLeading coefficients g, branch.Ready := by
  induction coefficients generalizing g with
  | nil =>
      intro branch hbranch
      simp only [splitLeading, List.mem_singleton] at hbranch
      subst branch
      trivial
  | cons a coefficients ih =>
      cases hsplit : coefficientSplit? g a with
      | none => simp [splitLeading, hsplit]
      | some split =>
          intro branch hbranch
          simp only [splitLeading, hsplit, List.mem_cons] at hbranch
          rcases hbranch with rfl | hbranch
          · obtain ⟨_, hinverse, hsplitEq⟩ := coefficientSplit?_eq_some_iff.mp hsplit
            rw [hsplitEq]
            exact hinverse
          · exact ih split.zeroModulus branch hbranch

/-- The descent always computes a branch family for a nonzero squarefree base modulus. -/
theorem splitLeading_ne_nil (coefficients : List (CPolynomial F))
    {g : CPolynomial F} (hg : g ≠ 0) (hgfree : Squarefree g.toPoly) :
    splitLeading coefficients g ≠ [] := by
  cases coefficients with
  | nil => simp [splitLeading]
  | cons a coefficients =>
      obtain ⟨split, hsplit⟩ := exists_coefficientSplit g a hg hgfree
      simp [splitLeading, hsplit]

/-- Every returned factor is monic and squarefree when the parent is. -/
theorem splitLeading_monic_squarefree (coefficients : List (CPolynomial F))
    {g : CPolynomial F} (hg : g ≠ 0) (hgmonic : g.monic) (hgfree : Squarefree g.toPoly) :
    ∀ branch ∈ splitLeading coefficients g,
      branch.modulus.monic ∧ Squarefree branch.modulus.toPoly := by
  induction coefficients generalizing g with
  | nil =>
      intro branch hbranch
      simp only [splitLeading, List.mem_singleton] at hbranch
      subst branch
      exact ⟨hgmonic, hgfree⟩
  | cons a coefficients ih =>
      obtain ⟨split, hsplit⟩ := exists_coefficientSplit g a hg hgfree
      have hchildren := coefficientSplit_monic hsplit hg hgmonic
      have hchildrenFree := coefficientSplit_squarefree hsplit hg hgfree
      have hzeroNe : split.zeroModulus ≠ 0 :=
        (CPolynomial.toPoly_eq_zero_iff _).not.mp
          ((CPolynomial.monic_toPoly_iff _).mp hchildren.1).ne_zero
      intro branch hbranch
      simp only [splitLeading, hsplit, List.mem_cons] at hbranch
      rcases hbranch with rfl | hbranch
      · exact ⟨hchildren.2, hchildrenFree.2⟩
      · exact ih hzeroNe hchildren.1 hchildrenFree.1 branch hbranch

/-- The product of all returned base factors is exactly the input modulus. -/
theorem splitLeading_modulus_product (coefficients : List (CPolynomial F))
    {g : CPolynomial F} (hg : g ≠ 0) (hgfree : Squarefree g.toPoly) :
    ((splitLeading coefficients g).map LeadingBranch.modulus).prod = g := by
  induction coefficients generalizing g with
  | nil => simp [splitLeading]
  | cons a coefficients ih =>
      obtain ⟨split, hsplit⟩ := exists_coefficientSplit g a hg hgfree
      obtain ⟨_, _, hsplitEq⟩ := coefficientSplit?_eq_some_iff.mp hsplit
      have hzeroMonic : split.zeroModulus.monic := by
        rw [hsplitEq]
        exact CPolynomial.gcdFactor_monic hg
      have hchildrenFree := coefficientSplit_squarefree hsplit hg hgfree
      have hzeroNe : split.zeroModulus ≠ 0 :=
        (CPolynomial.toPoly_eq_zero_iff _).not.mp
          ((CPolynomial.monic_toPoly_iff _).mp hzeroMonic).ne_zero
      rw [splitLeading, hsplit, List.map_cons, List.prod_cons,
        ih hzeroNe hchildrenFree.1]
      rw [mul_comm]
      exact coefficientSplit_factorization hsplit hg

/-- The descent preserves the complete sum of base degrees. -/
theorem splitLeading_natDegree_sum (coefficients : List (CPolynomial F))
    {g : CPolynomial F} (hg : g ≠ 0) (hgfree : Squarefree g.toPoly) :
    ((splitLeading coefficients g).map fun branch => branch.modulus.natDegree).sum =
      g.natDegree := by
  induction coefficients generalizing g with
  | nil => simp [splitLeading]
  | cons a coefficients ih =>
      obtain ⟨split, hsplit⟩ := exists_coefficientSplit g a hg hgfree
      obtain ⟨_, _, hsplitEq⟩ := coefficientSplit?_eq_some_iff.mp hsplit
      have hzeroMonic : split.zeroModulus.monic := by
        rw [hsplitEq]
        exact CPolynomial.gcdFactor_monic hg
      have hchildrenFree := coefficientSplit_squarefree hsplit hg hgfree
      have hzeroNe : split.zeroModulus ≠ 0 :=
        (CPolynomial.toPoly_eq_zero_iff _).not.mp
          ((CPolynomial.monic_toPoly_iff _).mp hzeroMonic).ne_zero
      rw [splitLeading, hsplit, List.map_cons, List.sum_cons,
        ih hzeroNe hchildrenFree.1]
      simpa only [Nat.add_comm] using coefficientSplit_natDegree_add hsplit hg

/-- Every root of a returned branch is a root of the original modulus and follows the branch's
zero/unit coefficient decisions. -/
theorem splitLeading_branch_root
    (coefficients : List (CPolynomial F)) {g : CPolynomial F}
    (hg : g ≠ 0) (hgfree : Squarefree g.toPoly)
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (branch : LeadingBranch (F := F)) (hbranch : branch ∈ splitLeading coefficients g)
    (hroot : branch.modulus.toPoly.eval₂ phi x = 0) :
    g.toPoly.eval₂ phi x = 0 ∧ branch.Follows coefficients phi x := by
  induction coefficients generalizing g branch with
  | nil =>
      simp only [splitLeading, List.mem_singleton] at hbranch
      subst branch
      refine ⟨hroot, ?_⟩
      exact ⟨[], rfl, by simp, trivial⟩
  | cons a coefficients ih =>
      obtain ⟨split, hsplit⟩ := exists_coefficientSplit g a hg hgfree
      obtain ⟨_, _, hsplitEq⟩ := coefficientSplit?_eq_some_iff.mp hsplit
      have hchildrenFree := coefficientSplit_squarefree hsplit hg hgfree
      have hzeroMonic : split.zeroModulus.monic := by
        rw [hsplitEq]
        exact CPolynomial.gcdFactor_monic hg
      have hzeroNe : split.zeroModulus ≠ 0 :=
        (CPolynomial.toPoly_eq_zero_iff _).not.mp
          ((CPolynomial.monic_toPoly_iff _).mp hzeroMonic).ne_zero
      simp only [splitLeading, hsplit, List.mem_cons] at hbranch
      rcases hbranch with rfl | hbranch
      · have hdecision := (eval₂_unitModulus_eq_zero_iff hsplit hg hgfree phi x).mp hroot
        refine ⟨hdecision.1, ?_⟩
        exact ⟨[], rfl, by simp, eval₂_mul_unitInverse_eq_one hsplit phi x hroot⟩
      · obtain ⟨hzeroRoot, dropped, hinput, hdropped, hleading⟩ :=
          ih hzeroNe hchildrenFree.1 branch hbranch hroot
        have hdecision := (eval₂_zeroModulus_eq_zero_iff hsplit phi x).mp hzeroRoot
        refine ⟨hdecision.1, a :: dropped, ?_, ?_, hleading⟩
        · simp only [List.cons_append, List.cons.injEq, true_and]
          exact hinput
        · intro coefficient hcoefficient
          simp only [List.mem_cons] at hcoefficient
          rcases hcoefficient with rfl | hcoefficient
          · exact hdecision.2
          · exact hdropped coefficient hcoefficient

/-- Every geometric root of the input modulus reaches a returned branch, and membership in a
returned rooted branch is sound. -/
theorem eval₂_splitLeading_root_iff
    (coefficients : List (CPolynomial F)) {g : CPolynomial F}
    (hg : g ≠ 0) (hgfree : Squarefree g.toPoly)
    {K : Type*} [Field K] (phi : F →+* K) (x : K) :
    g.toPoly.eval₂ phi x = 0 ↔
      ∃ branch ∈ splitLeading coefficients g,
        branch.modulus.toPoly.eval₂ phi x = 0 ∧ branch.Follows coefficients phi x := by
  constructor
  · intro hroot
    induction coefficients generalizing g with
    | nil =>
        refine ⟨⟨g, [], none⟩, by simp [splitLeading], hroot, ?_⟩
        exact ⟨[], rfl, by simp, trivial⟩
    | cons a coefficients ih =>
        obtain ⟨split, hsplit⟩ := exists_coefficientSplit g a hg hgfree
        obtain ⟨_, _, hsplitEq⟩ := coefficientSplit?_eq_some_iff.mp hsplit
        have hchildrenFree := coefficientSplit_squarefree hsplit hg hgfree
        have hzeroMonic : split.zeroModulus.monic := by
          rw [hsplitEq]
          exact CPolynomial.gcdFactor_monic hg
        have hzeroNe : split.zeroModulus ≠ 0 :=
          (CPolynomial.toPoly_eq_zero_iff _).not.mp
            ((CPolynomial.monic_toPoly_iff _).mp hzeroMonic).ne_zero
        by_cases ha : a.toPoly.eval₂ phi x = 0
        · have hzeroRoot := (eval₂_zeroModulus_eq_zero_iff hsplit phi x).2 ⟨hroot, ha⟩
          obtain ⟨branch, hbranch, hbranchRoot, hfollow⟩ :=
            ih hzeroNe hchildrenFree.1 hzeroRoot
          obtain ⟨dropped, hinput, hdropped, hleading⟩ := hfollow
          refine ⟨branch, ?_, hbranchRoot, a :: dropped, ?_, ?_, hleading⟩
          · simp only [splitLeading, hsplit, List.mem_cons]
            exact Or.inr hbranch
          · simp only [List.cons_append, List.cons.injEq, true_and]
            exact hinput
          · intro coefficient hcoefficient
            simp only [List.mem_cons] at hcoefficient
            rcases hcoefficient with rfl | hcoefficient
            · exact ha
            · exact hdropped coefficient hcoefficient
        · have hunitRoot := (eval₂_unitModulus_eq_zero_iff hsplit hg hgfree phi x).2
            ⟨hroot, ha⟩
          refine ⟨⟨split.unitModulus, a :: coefficients, some split.unitInverse⟩, ?_,
            hunitRoot, ?_⟩
          · simp [splitLeading, hsplit]
          · exact ⟨[], rfl, by simp,
              eval₂_mul_unitInverse_eq_one hsplit phi x hunitRoot⟩
  · rintro ⟨branch, hbranch, hroot, _⟩
    exact (splitLeading_branch_root coefficients hg hgfree phi x branch hbranch hroot).1

/-- Every geometric root follows exactly one returned base branch.  Thus the degree-preserving
factor family is an actual root partition, not only a covering family. -/
theorem existsUnique_splitLeading_branch_of_root
    (coefficients : List (CPolynomial F)) {g : CPolynomial F}
    (hg : g ≠ 0) (hgfree : Squarefree g.toPoly)
    {K : Type*} [Field K] (phi : F →+* K) (x : K)
    (hroot : g.toPoly.eval₂ phi x = 0) :
    ∃! branch : LeadingBranch (F := F),
      branch ∈ splitLeading coefficients g ∧
        branch.modulus.toPoly.eval₂ phi x = 0 := by
  induction coefficients generalizing g with
  | nil =>
      refine ⟨⟨g, [], none⟩, ⟨by simp [splitLeading], hroot⟩, ?_⟩
      intro branch hbranch
      simpa only [splitLeading, List.mem_singleton] using hbranch.1
  | cons a coefficients ih =>
      obtain ⟨split, hsplit⟩ := exists_coefficientSplit g a hg hgfree
      obtain ⟨_, _, hsplitEq⟩ := coefficientSplit?_eq_some_iff.mp hsplit
      have hchildrenFree := coefficientSplit_squarefree hsplit hg hgfree
      have hzeroMonic : split.zeroModulus.monic := by
        rw [hsplitEq]
        exact CPolynomial.gcdFactor_monic hg
      have hzeroNe : split.zeroModulus ≠ 0 :=
        (CPolynomial.toPoly_eq_zero_iff _).not.mp
          ((CPolynomial.monic_toPoly_iff _).mp hzeroMonic).ne_zero
      by_cases ha : a.toPoly.eval₂ phi x = 0
      · have hzeroRoot := (eval₂_zeroModulus_eq_zero_iff hsplit phi x).2 ⟨hroot, ha⟩
        obtain ⟨branch, hbranch, hunique⟩ :=
          ih hzeroNe hchildrenFree.1 hzeroRoot
        refine ⟨branch, ⟨?_, hbranch.2⟩, ?_⟩
        · simp only [splitLeading, hsplit, List.mem_cons]
          exact Or.inr hbranch.1
        · intro other hother
          simp only [splitLeading, hsplit, List.mem_cons] at hother
          rcases hother.1 with rfl | hotherMem
          · have hunitDecision :=
              (eval₂_unitModulus_eq_zero_iff hsplit hg hgfree phi x).mp hother.2
            exact False.elim (hunitDecision.2 ha)
          · exact hunique other ⟨hotherMem, hother.2⟩
      · have hunitRoot := (eval₂_unitModulus_eq_zero_iff hsplit hg hgfree phi x).2
          ⟨hroot, ha⟩
        let unitBranch : LeadingBranch (F := F) :=
          ⟨split.unitModulus, a :: coefficients, some split.unitInverse⟩
        refine ⟨unitBranch, ⟨?_, hunitRoot⟩, ?_⟩
        · simp [unitBranch, splitLeading, hsplit]
        · intro other hother
          simp only [splitLeading, hsplit, List.mem_cons] at hother
          rcases hother.1 with hotherEq | hotherMem
          · exact hotherEq
          · have hzeroRoot :=
              (splitLeading_branch_root coefficients hzeroNe hchildrenFree.1
                phi x other hotherMem hother.2).1
            have hzeroDecision :=
              (eval₂_zeroModulus_eq_zero_iff hsplit phi x).mp hzeroRoot
            exact False.elim (ha hzeroDecision.2)

end ReedSolomon.ListDecoding.FirstOrderNormDecoder.D5
