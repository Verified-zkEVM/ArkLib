/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.OrdinaryQuotientDecoder

/-!
# One regular center for dedicated zeroth-order decoding

Search a supplied deterministic centers and use only its first regular fiber. The
check preserves the value-variable degree and computes a Bézout inverse of the
slope in the entire fiber. Global squarefree normalization and construction of a
sufficient centers remain upstream obligations; no unavailable case is interpreted
as a successful empty output. This is a sequential search slice, not yet the
paper's batched obstruction evaluation algorithm.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.ZerothOrderDecoder

open CompPoly Polynomial ReedSolomon.HiddenDerivative.Ordinary.QuotientLift

variable {E : Type*} [Field E] [BEq E] [LawfulBEq E]

/-- Executable regular-fiber test, including the leading-degree obstruction. -/
def goodCenter (Q : CPoly.CMvPolynomial 2 E) (center : E) : Bool :=
  sectionPolynomial Q center != 0 &&
    (sectionPolynomial Q center).natDegree == Q.degreeOf 1 &&
    (CPolynomial.inverseMod? (slope Q center) (sectionPolynomial Q center)).isSome

/-- Select one center, stopping at the first successful fiber test. -/
def selectCenter (Q : CPoly.CMvPolynomial 2 E) (centers : List E) : Option E :=
  centers.find? (goodCenter Q)

/-- The checked fiber is nonzero, degree-preserving, and has an executed slope inverse. -/
theorem goodCenter_iff (Q : CPoly.CMvPolynomial 2 E) (center : E) :
    goodCenter Q center = true ↔
      sectionPolynomial Q center ≠ 0 ∧
      (sectionPolynomial Q center).natDegree = Q.degreeOf 1 ∧
      ∃ inverse, CPolynomial.inverseMod? (slope Q center)
        (sectionPolynomial Q center) = some inverse := by
  simp [goodCenter, Bool.and_eq_true, Option.isSome_iff_exists, and_assoc]

/-- A selected center belongs to the centers and passed the actual test. -/
theorem selectCenter_sound {Q : CPoly.CMvPolynomial 2 E} {centers : List E} {center : E}
    (h : selectCenter Q centers = some center) :
    center ∈ centers ∧ goodCenter Q center = true :=
  ⟨List.mem_of_find?_eq_some h, (List.find?_eq_some_iff_append.mp h).1⟩

/-- Earlier centers elements all failed: selection is a single-center procedure. -/
theorem selectCenter_first {Q : CPoly.CMvPolynomial 2 E} {centers : List E} {center : E}
    (h : selectCenter Q centers = some center) :
    ∃ before after, centers = before ++ center :: after ∧
      ∀ a ∈ before, goodCenter Q a = false := by
  obtain ⟨_, before, after, heq, hbefore⟩ := List.find?_eq_some_iff_append.mp h
  exact ⟨before, after, heq, by simpa using hbefore⟩

/-- A centers containing a good fiber makes the executable search succeed. -/
theorem selectCenter_exists {Q : CPoly.CMvPolynomial 2 E} {centers : List E}
    (h : ∃ center ∈ centers, goodCenter Q center = true) :
    ∃ center, selectCenter Q centers = some center := by
  cases hs : selectCenter Q centers with
  | some center => exact ⟨center, rfl⟩
  | none =>
      obtain ⟨center, hmem, hgood⟩ := h
      have hnone := List.find?_eq_none.mp hs
      exact False.elim (hnone center hmem hgood)

/-- Every geometric point in a checked fiber has nonzero value derivative. -/
theorem goodCenter_regular {L : Type*} [Field L] (base : E →+* L)
    {Q : CPoly.CMvPolynomial 2 E} {center : E} (hgood : goodCenter Q center = true)
    (value : L)
    (hroot : MvPolynomial.eval₂ base ![base center, value] (CPoly.fromCMvPolynomial Q) = 0) :
    MvPolynomial.eval₂ base ![base center, value]
      (MvPolynomial.pderiv 1 (CPoly.fromCMvPolynomial Q)) ≠ 0 := by
  obtain ⟨_, _, inverse, hinverse⟩ := (goodCenter_iff Q center).mp hgood
  have hsection : (sectionPolynomial Q center).toPoly.eval₂ base value = 0 := by
    rwa [eval₂_sectionPolynomial]
  have hinv := CPolynomial.eval₂_mul_inverseMod_eq_one base value hsection hinverse
  rw [eval₂_slope] at hinv
  exact left_ne_zero_of_mul_eq_one hinv

variable (pchar : ℕ) [Fact pchar.Prime] [CharP E pchar] [Fintype E]

/-- Decode a supplied normalized equation at the selected center using existing quotient Newton.
`none` reports exhausted center search; `some []` is a successful empty agreement list. -/
def runNormalized? {F : Type*} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] {n : ℕ}
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (Q : CPoly.CMvPolynomial 2 E) (centers : List E) : Option (List (List F)) :=
  (selectCenter Q centers).map fun center =>
    OrdinaryQuotientDecoder.run pchar base domain received k A Q center

/-- Conditional producer completeness for the single-center normalized-equation slice.
The polynomial-solution and good-centers hypotheses must be supplied by normalization and
field/obstruction producers before this becomes the dedicated decoder's public theorem. -/
theorem runNormalized?_exact {F : Type*} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F]
    {n : ℕ} (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (hAk : k ≤ A) (Q : CPoly.CMvPolynomial 2 E) (centers : List E)
    (hprefix : ∃ center ∈ centers, goodCenter Q center = true)
    (hsolutions : ∀ P : F[X], P.degree < k →
      A ≤ Code.agree (evalOnPoints domain P) received →
      MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P.map base]
        (CPoly.fromCMvPolynomial Q) = 0) :
    ∃ output, runNormalized? pchar base domain received k A Q centers = some output ∧
      ExactOutput domain received k A output := by
  obtain ⟨center, hcenter⟩ := selectCenter_exists hprefix
  have hgood := (selectCenter_sound hcenter).2
  refine ⟨OrdinaryQuotientDecoder.run pchar base domain received k A Q center,
    by simp [runNormalized?, hcenter], ?_⟩
  apply OrdinaryQuotientDecoder.run_exact_of_regular_cover base domain received k A hAk
    Q center ((goodCenter_iff Q center).mp hgood).1 hsolutions
  intro P hdegree hagree
  apply goodCenter_regular (RingHom.id E) hgood
  exact solution_at_center (RingHom.id E) (CPoly.fromCMvPolynomial Q) (P.map base) center
    (by simpa using hsolutions P hdegree hagree)

end ReedSolomon.ListDecoding.ZerothOrderDecoder
