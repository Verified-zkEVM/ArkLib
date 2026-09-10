/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.JetRootsSemantics
/-!
# Per-center root uniqueness

Preservation of every initial jet coordinate makes successful tuples injective in their global
polynomial. A duplicate-free alphabet therefore yields duplicate-free per-center polynomials.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.JetRootsMachine

open Polynomial CompPoly PolynomialDifferential

variable {F : Type*} [Field F] [DecidableEq F]

omit [DecidableEq F] in
/-- Equal functional jets recover the same materialized tuple when its width is exact. -/
theorem jetFunction_injective_width (r : ℕ) (xs ys : List F)
    (hx : xs.length = r + 1) (hy : ys.length = r + 1)
    (h : jetFunction r xs = jetFunction r ys) : xs = ys := by
  apply List.ext_getElem (hx.trans hy.symm)
  intro i hi hj
  have he := congrFun h ⟨i, by omega⟩
  simpa only [jetFunction, List.getD_eq_getElem xs 0 hi,
    List.getD_eq_getElem ys 0 hj] using he

/-- A successful global polynomial determines its unique enumerated jet tuple at this center. -/
theorem jetSolution_unique {r : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (D : ℕ) (xs ys : List F) (f : F[X])
    (hx : xs.length = r + 1) (hy : ys.length = r + 1)
    (hsx : jetSolution Q center D xs = some f)
    (hsy : jetSolution Q center D ys = some f) : xs = ys := by
  exact jetFunction_injective_width r xs ys hx hy
    ((jetSolution_sound Q center D xs f hsx).2.symm.trans
      (jetSolution_sound Q center D ys f hsy).2)

/-- Filtering a duplicate-free list of exact-width jets preserves polynomial uniqueness. -/
theorem filterMap_jetSolution_nodup {r : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (D : ℕ) (jets : List (List F))
    (hn : jets.Nodup) (hw : ∀ js ∈ jets, js.length = r + 1) :
    (jets.filterMap (jetSolution Q center D)).Nodup := by
  induction jets with
  | nil => simp
  | cons js jets ih =>
      obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hn
      have htwidth : ∀ xs ∈ jets, xs.length = r + 1 := fun xs hm ↦ hw xs (by simp [hm])
      cases hs : jetSolution Q center D js with
      | none => simpa [List.filterMap_cons, hs] using ih htail htwidth
      | some f =>
          simp only [List.filterMap_cons, hs, List.nodup_cons]
          refine ⟨?_, ih htail htwidth⟩
          intro hm
          obtain ⟨xs, hxs, hsol⟩ := List.mem_filterMap.mp hm
          have he := jetSolution_unique Q center D js xs f (hw js (by simp))
            (htwidth xs hxs) hs hsol
          exact hnot (he ▸ hxs)

/-- The exact per-center specification has no repeated global polynomial. -/
theorem tuples_jetSolution_nodup {r : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (D : ℕ) (alphabet : List F) (hn : alphabet.Nodup) :
    ((tuples alphabet (r + 1)).filterMap (jetSolution Q center D)).Nodup :=
  filterMap_jetSolution_nodup Q center D _ (tuples_nodup alphabet (r + 1) hn)
    (tuples_width alphabet (r + 1))

/-- Uniqueness attaches to the same actual bounded execution as its semantic specification. -/
theorem computation_runFuel_nodup {r D L : ℕ} (Q : CPoly.CMvPolynomial (r + 2) F)
    (center : F) (alphabet : List F) (terms : List (MvPolynomial.EvaluationMachine.Term F))
    (points : Fin L ↪ F) (samples : List F)
    (hsamples : samples = List.ofFn (fun i ↦ points i)) (hq : 0 < alphabet.length)
    (hn : alphabet.Nodup)
    (hQ : MvPolynomial.EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q))
    (hr : r ≤ D) (hlookup : D - r < L)
    (hweight : differentialWeightedDegree D (semanticEquation Q) < L) :
    let input : Input F := ⟨alphabet, terms, center, r⟩
    ∃ out c, runFuel input D L (fuel input D L samples.length) (.start samples) =
      (.done (some out), c) ∧ (out.map JetHornerMachine.coefficientPolynomial).Nodup ∧
      out.Nodup ∧ totalCost c ≤ workBound input D L samples.length := by
  obtain ⟨out, c, hrun, hspec, _hwidth, _hcount, hcost⟩ := computation_runFuel_correct Q
    center alphabet terms points samples hsamples hq hQ hr hlookup hweight
  have hout : (out.map JetHornerMachine.coefficientPolynomial).Nodup := by
    rw [hspec]
    exact tuples_jetSolution_nodup Q center D alphabet hn
  exact ⟨out, c, hrun, hout, hout.of_map _, hcost⟩

end ReedSolomon.HiddenDerivative.JetRootsMachine
