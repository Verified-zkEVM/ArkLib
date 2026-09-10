/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Geometry.SolutionEmbedding
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Geometry.HighCutGeometry


/-! # Field-independent counting of regular differential solutions with agreement -/

@[expose] public section

open PolynomialDifferential


noncomputable section
open MvPolynomial AffineHilbert
namespace ReedSolomon.HiddenDerivative
variable {F : Type*} [Field F] {r : ℕ}

open Classical in
/-- The regular branch of a differential equation has a field-independent agreement
bound, obtained from the actual Taylor chart over the algebraic closure. -/
theorem finite_regular_solutions_card_le
    (Q : DifferentialPolynomial F r) (K k : ℕ) (hK : r < K) (hkK : k ≤ K)
    (hv : 0 < Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)))
    {n A : ℕ} (domain : Fin n ↪ F) (received : Fin n → F)
    (hk : 0 < k) (hkA : k ≤ A) (hAn : A ≤ n)
    (S : Finset (Polynomial F))
    (hdegree : ∀ P ∈ S, P.degree < k)
    (hsol : ∀ P ∈ S, differentialSpecialization Q P = 0)
    (hsep : ∀ P ∈ S, differentialSpecialization (separant Q (Fin.last r)) P ≠ 0)
    (hbin : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    (hagree : ∀ P ∈ S,
      A ≤ (Finset.univ.filter fun i ↦ P.eval (domain i) = received i).card) :
    (S.card : ℚ) ≤
      (Q.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) : ℕ) *
        ((((n * rationalTaylorCutDegreeBound Q K : ℕ) : ℚ) /
          ((A - k + 1 : ℕ) : ℚ)) ^ r) := by
  classical
  let E := AlgebraicClosure F
  let f := algebraMap F E
  let QE := MvPolynomial.map f Q
  obtain ⟨center, J, hcard, hJ⟩ := exists_regular_solution_jet_family
    f Q K k hkK S domain received hdegree hsol hsep hbin hagree
  by_cases hJempty : J = ∅
  · have hScard : S.card = 0 := by simpa [hJempty] using hcard.symm
    rw [hScard, Nat.cast_zero]
    positivity
  have hsepE : initialJetSeparant center QE ≠ 0 := by
    obtain ⟨jet, hjet⟩ := Finset.nonempty_iff_ne_empty.mpr hJempty
    intro hz
    exact (hJ jet hjet).2.1 (by rw [hz, map_zero])
  have hvE : 0 < QE.weightedTotalDegree (fun i ↦ i.elim (0 : ℕ) (fun _ ↦ 1)) := by
    rwa [totalJetDegree_map_eq f Q]
  let domainE : Fin n ↪ E := domain.trans ⟨f, f.injective⟩
  have hcount := finite_regularHighCutJets_card_le center QE K k hK hsepE hvE
    domainE (fun i ↦ f (received i)) hk hkA hAn J
    (fun jet hjet ↦ ⟨(hJ jet hjet).1, (hJ jet hjet).2.1,
      fun l ↦ (hJ jet hjet).2.2.1 l.val l.property⟩)
    (fun jet hjet ↦ (hJ jet hjet).2.2.2)
  rw [hcard] at hcount
  simpa only [QE, rationalTaylorCutDegreeBound, totalJetDegree_map_eq f Q] using hcount

end ReedSolomon.HiddenDerivative
