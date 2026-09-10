/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.SquareSystems.TaylorNumerator
/-!
# Bottom-up computation of rational Taylor numerators

The defining recurrence for `computableRationalTaylorNumerator` refers to every lower coordinate.
Evaluating that definition independently for each coordinate repeats the same recursive work. This
module instead builds one array from low to high order. At step `l`, the already-computed prefix
supplies exactly the `Fin l` numerator family in the paper's denominator-cleared recurrence.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.SquareSystems

variable {F : Type*} [Field F] [DecidableEq F]

/-- Compute Taylor numerator `l`, taking every lower numerator from a shared prefix array. -/
def computableRationalTaylorStep {r : ℕ} (center : F)
    (Q : CPoly.CMvPolynomial (r + 2) F)
    (prior : Array (CPoly.CMvPolynomial (r + 1) F)) :
    CPoly.CMvPolynomial (r + 1) F :=
  let l := prior.size
  if hl : l < r + 1 then CPoly.CMvPolynomial.X ⟨l, hl⟩ else
    -CPoly.CMvPolynomial.C ((l.choose r : F)⁻¹) *
      CPoly.CMvPolynomial.clearedSubstitution
        (computableInitialJetSeparant center Q) (fun i : Fin l => prior[i])
        (fun i => 2 * (i.val - r) - 1) (2 * (l - r) - 2)
        (computableTaylorResidualCoefficient l center Q)

/-- Build the first `K` Taylor numerators once, in increasing coordinate order. -/
def computableRationalTaylorTable {r : ℕ} (center : F)
    (Q : CPoly.CMvPolynomial (r + 2) F) :
    (K : ℕ) → Array (CPoly.CMvPolynomial (r + 1) F)
  | 0 => #[]
  | K + 1 =>
      let prior := computableRationalTaylorTable center Q K
      prior.push (computableRationalTaylorStep center Q prior)

@[simp]
theorem computableRationalTaylorTable_size {r : ℕ} (center : F)
    (Q : CPoly.CMvPolynomial (r + 2) F) (K : ℕ) :
    (computableRationalTaylorTable center Q K).size = K := by
  induction K with
  | zero => rfl
  | succ K ih => simp only [computableRationalTaylorTable, Array.size_push, ih]

/-- A table step agrees with the defining recurrence whenever its prefix does. -/
theorem computableRationalTaylorStep_eq {r : ℕ} (center : F)
    (Q : CPoly.CMvPolynomial (r + 2) F)
    (prior : Array (CPoly.CMvPolynomial (r + 1) F))
    (hprior : ∀ i : Fin prior.size,
      prior[i] = computableRationalTaylorNumerator center Q i.val) :
    computableRationalTaylorStep center Q prior =
      computableRationalTaylorNumerator center Q prior.size := by
  rw [computableRationalTaylorStep, computableRationalTaylorNumerator]
  split_ifs
  · rfl
  · congr 2
    funext i
    exact hprior i

/-- Every array entry is the corresponding recursively specified Taylor numerator. -/
theorem computableRationalTaylorTable_get {r : ℕ} (center : F)
    (Q : CPoly.CMvPolynomial (r + 2) F) (K i : ℕ) (hi : i < K) :
    (computableRationalTaylorTable center Q K)[i]'(by
      simpa only [computableRationalTaylorTable_size] using hi) =
      computableRationalTaylorNumerator center Q i := by
  induction K generalizing i with
  | zero => omega
  | succ K ih =>
      change (computableRationalTaylorTable center Q K |>.push
        (computableRationalTaylorStep center Q
          (computableRationalTaylorTable center Q K)))[i]'(by
            rw [Array.size_push, computableRationalTaylorTable_size]
            omega) =
        computableRationalTaylorNumerator center Q i
      rw [Array.getElem_push]
      split_ifs with hprior
      · apply ih i
        simpa only [computableRationalTaylorTable_size] using hprior
      · have hnot : ¬i < K := by
          simpa only [computableRationalTaylorTable_size] using hprior
        have hilast : i = (computableRationalTaylorTable center Q K).size := by
          rw [computableRationalTaylorTable_size]
          omega
        rw [hilast]
        apply computableRationalTaylorStep_eq center Q
        intro j
        apply ih j.val
        simpa only [computableRationalTaylorTable_size] using j.isLt

end ReedSolomon.HiddenDerivative.SquareSystems
