/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TowerRepresentation
public import ArkLib.Data.Polynomial.BatchRemainder

/-!
# Batched coefficient restriction for tower recovery

For each received position, `RecoverAgreement` reduces the same bounded-fiber residual into
all live base factors. Each scalar coefficient is sent through a product/remainder tree.
Repeated base factors are retained; coprimality is neither assumed nor needed.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.AgreementRecovery.TowerBatch

open CompPoly CompPoly.CPolynomial FirstOrderNormDecoder.D5

variable {E : Type*} [Field E] [BEq E] [LawfulBEq E]

/-- Restrict a nested residual to every live base modulus using one product/remainder tree per
fiber coefficient. The output order, including repeated moduli, matches the input order. -/
def restrictBases (M : MulContext E) (D : ModContext E)
    (p : CPolynomial (CPolynomial E)) (moduli : List (CPolynomial E)) :
    List (CPolynomial (CPolynomial E)) :=
  let columns := List.ofFn fun j : Fin (p.natDegree + 1) =>
    BatchRemainder.remainders M D (p.coeff j) moduli
  List.ofFn fun i : Fin moduli.length =>
    CPolynomial.ofFn fun j : Fin (p.natDegree + 1) =>
      ((columns[j.val]?.getD [])[i.val]?).getD 0

/-- Batched restriction computes precisely the canonical coefficientwise remainder in each
base factor. The theorem allows repeated and noncoprime moduli. -/
theorem restrictBases_eq (M : MulContext E) (D : ModContext E)
    (p : CPolynomial (CPolynomial E)) (moduli : List (CPolynomial E))
    (hm : ∀ g ∈ moduli, g.monic) :
    restrictBases M D p moduli = moduli.map (fun g => reduceFiberCoefficients g p) := by
  unfold restrictBases
  conv_rhs => rw [← List.ofFn_get moduli, List.map_ofFn]
  dsimp only
  apply congrArg List.ofFn
  funext i
  unfold reduceFiberCoefficients
  congr 1
  funext j
  simp only [List.getElem?_ofFn, j.isLt, ↓reduceDIte,
    Option.getD_some]
  rw [BatchRemainder.remainders_eq M D _ moduli hm]
  simp

/-- Each batched remainder preserves the value at a geometric root of its corresponding base
factor, which is the restriction-map law used by the tower split scan. -/
theorem restrictBases_specialize (M : MulContext E) (D : ModContext E)
    (p : CPolynomial (CPolynomial E)) (moduli : List (CPolynomial E))
    (hm : ∀ g ∈ moduli, g.monic) (i : Fin moduli.length)
    {L : Type*} [Field L] (ι : E →+* L) (u : L)
    (hroot : (moduli[i]).toPoly.eval₂ ι u = 0) :
    specializeFiberCPolynomial ((restrictBases M D p moduli)[i.val]?.getD 0) ι u =
      specializeFiberCPolynomial p ι u := by
  rw [restrictBases_eq M D p moduli hm]
  simp only [List.getElem?_map, List.getElem?_eq_getElem i.isLt, Option.map_some,
    Option.getD_some]
  exact specialize_reduceFiberCoefficients ι u (hm _ (List.getElem_mem _)) hroot p

end ReedSolomon.ListDecoding.AgreementRecovery.TowerBatch
