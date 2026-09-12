/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ZerothOrderDecoder.CenterSearch
public import ArkLib.Data.Polynomial.NonvanishingSearch

/-!
# Batched obstruction search followed by one-center decoding

The stored obstruction is evaluated with an actual subproduct tree. A single selected
center is then checked and passed to quotient Newton. Constructing a nonzero obstruction
from the normalized equation remains a separate producer obligation.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.ZerothOrderDecoder

open CompPoly Polynomial

variable {E : Type*} [Field E] [BEq E] [LawfulBEq E]

/-- Execute subproduct-tree evaluation and select the first nonzero obstruction value. -/
def selectObstructionCenter (obstruction : CPolynomial E) (centers : List E) : Option E :=
  CPolynomial.findNonzeroEvaluation?
    (.subproduct E .naive .remainderOnly) obstruction centers

/-- Enough distinct centers guarantee a selected nonzero value for a nonzero obstruction. -/
theorem selectObstructionCenter_exists (obstruction : CPolynomial E) (centers : List E)
    (hne : obstruction ≠ 0) (hnodup : centers.Nodup)
    (hdegree : obstruction.natDegree < centers.length) :
    ∃ center, selectObstructionCenter obstruction centers = some center :=
  CPolynomial.findNonzeroEvaluation?_exists _ obstruction hne centers hnodup hdegree

/-- Selection comes from the supplied prefix and has nonzero obstruction value. -/
theorem selectObstructionCenter_sound (obstruction : CPolynomial E) (centers : List E)
    (center : E) (h : selectObstructionCenter obstruction centers = some center) :
    center ∈ centers ∧ obstruction.eval center ≠ 0 :=
  CPolynomial.findNonzeroEvaluation?_sound _ obstruction centers center h

variable (pchar : ℕ) [Fact pchar.Prime] [CharP E pchar] [Fintype E]

/-- Batched search, one checked center, then the existing quotient Newton and recovery path.
An invalid obstruction certificate cannot bypass the executable regular-fiber check. -/
def runFromObstruction? {F : Type*} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] {n : ℕ}
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (Q : CPoly.CMvPolynomial 2 E) (obstruction : CPolynomial E)
    (centers : List E) : Option (List (List F)) :=
  (selectObstructionCenter obstruction centers).bind fun center =>
    runNormalized? pchar base domain received k A Q [center]

/-- The executed batched path succeeds and is exact under explicit normalization,
obstruction-validity, and sufficient-prefix hypotheses. There is no supplied good-center
witness: polynomial degree and prefix distinctness make the search succeed. -/
theorem runFromObstruction?_exact {F : Type*} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F]
    {n : ℕ} (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (k A : ℕ) (hAk : k ≤ A) (Q : CPoly.CMvPolynomial 2 E)
    (obstruction : CPolynomial E) (centers : List E)
    (hne : obstruction ≠ 0) (hnodup : centers.Nodup)
    (hdegree : obstruction.natDegree < centers.length)
    (hvalid : ∀ center, obstruction.eval center ≠ 0 → goodCenter Q center = true)
    (hsolutions : ∀ P : F[X], P.degree < k →
      A ≤ Code.agree (evalOnPoints domain P) received →
      MvPolynomial.eval₂ Polynomial.C ![Polynomial.X, P.map base]
        (CPoly.fromCMvPolynomial Q) = 0) :
    ∃ output, runFromObstruction? pchar base domain received k A Q obstruction centers =
      some output ∧ ExactOutput domain received k A output := by
  obtain ⟨center, hcenter⟩ := selectObstructionCenter_exists obstruction centers hne hnodup hdegree
  have hgood := hvalid center (selectObstructionCenter_sound obstruction centers center hcenter).2
  obtain ⟨output, hout, hexact⟩ := runNormalized?_exact pchar base domain received k A hAk Q
    [center] ⟨center, by simp, hgood⟩ hsolutions
  exact ⟨output, by simpa [runFromObstruction?, hcenter] using hout, hexact⟩

end ReedSolomon.ListDecoding.ZerothOrderDecoder
