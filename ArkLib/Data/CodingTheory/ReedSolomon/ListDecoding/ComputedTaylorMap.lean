/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.TaylorChartMap
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.SquareSystems.TaylorTable
/-!
# Applying a computed differential Taylor chart

A raw solver representation describes the initial jet, not the complete message. Starting from
the concrete differential equation Q, compute the rational Taylor table, pad its numerators to
the common separant power S^τ, and pass that chart to the finite-representation materializer.

The coverage theorem discharges the chart identities using the differential equation satisfied
by the message. The only solver premise is that its raw map represents the initial jet; this
module does not construct that map or assert the still-missing toric solver theorem.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.ComputedTaylorMap
open PolynomialDifferential ReedSolomon.HiddenDerivative ReedSolomon.HiddenDerivative.SquareSystems
open CompPoly CPoly CPoly.CMvPolynomial ArkLib.UnivariateRepresentation
universe u
variable {E : Type u} [Field E] [DecidableEq E] {r : ℕ}
variable (pchar : ℕ) [Fact pchar.Prime] [CharP E pchar]

/-- Build the shared numerator table once, then pad every entry to denominator S^τ. -/
def computedChartNumerators (center : E) (Q : CMvPolynomial (r + 2) E) (K τ : ℕ) :
    List (CMvPolynomial (r + 1) E) :=
  let table := computableRationalTaylorTable center Q K
  let S := computableInitialJetSeparant center Q
  List.ofFn (fun l : Fin K =>
    table[l.val]'(by simp [table]) * S ^ (τ - (2 * (l.val - r) - 1)))

@[simp]
theorem computedChartNumerators_length (center : E) (Q : CMvPolynomial (r + 2) E)
    (K τ : ℕ) : (computedChartNumerators center Q K τ).length = K := by
  simp [computedChartNumerators]

/-- Each table-produced coordinate denotes the paper's padded numerator N_i. -/
theorem computedChartNumerators_get (center : E) (Q : CMvPolynomial (r + 2) E)
    (K τ i : ℕ) (hi : i < K) :
    fromCMvPolynomial ((computedChartNumerators center Q K τ)[i]'(by simpa using hi)) =
      commonTaylorNumerator center (semanticEquation Q) K ⟨i, hi⟩ τ := by
  simp only [computedChartNumerators, List.getElem_ofFn]
  rw [fromCMvPolynomial_mul', fromCMvPolynomial_pow,
    computableRationalTaylorTable_get center Q K i hi,
    fromCMvPolynomial_computableRationalTaylorNumerator,
    fromCMvPolynomial_computableInitialJetSeparant]
  rfl

variable [Fintype E]

/-- Materialize one solver-produced jet map using the chart computed from Q. -/
def fromEquationJet? (center : E) (Q : CMvPolynomial (r + 2) E) (K τ k : ℕ)
    (input : MapData (F := E)) : Option (FiniteRepresentation E) :=
  TaylorChartMap.fromJet? pchar center k input (computedChartNumerators center Q K τ)
    (computableTaylorDenominator center Q τ)

/-- Apply one computed chart to every raw jet map, then invoke the shared agreement decoder. -/
def run
    {F : Type*} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] {n : ℕ}
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (center : E) (Q : CMvPolynomial (r + 2) E) (K τ k A : ℕ)
    (inputs : List (MapData (F := E))) : List (List F) :=
  let numerators := computedChartNumerators center Q K τ
  let denominator := computableTaylorDenominator center Q τ
  AgreementRecovery.decode base domain received k A
    (inputs.filterMap fun input =>
      TaylorChartMap.fromJet? pchar center k input numerators denominator)

variable {L : Type*} [Field L]

omit [Fintype E] [DecidableEq E] in
private theorem eval₂_mapped_point (ι : E →+* L) (point : Fin (r + 1) → E)
    (poly : MvPolynomial (Fin (r + 1)) E) :
    MvPolynomial.eval₂ ι (fun i => ι (point i)) poly =
      ι (MvPolynomial.aeval point poly) := by
  simpa [MvPolynomial.aeval_eq_eval₂Hom, Function.comp_def] using
    (MvPolynomial.eval₂_comp_left ι (RingHom.id E) point poly).symm

/-- A regular solution whose jet is represented by the solver survives the computed chart.
The parameter may lie in an arbitrary extension L. The solution is over E, which can itself be
an auxiliary extension of the message field; its coefficients are mapped to L only for this
coverage statement. -/
theorem fromEquationJet?_covers (center : E) (Q : CMvPolynomial (r + 2) E)
    (K τ k : ℕ) (hk : k ≤ K) (hτ : TaylorExponentSufficient r K τ)
    (input : MapData (F := E)) (hnonzero : input.modulus ≠ 0)
    (ι : E →+* L) (θ : L) (P : Polynomial E)
    (hdegree : P.degree < k)
    (hpoint : MapData.RepresentsPoint input ι θ
      (fun i : Fin (r + 1) => ι (polynomialJet center P i)))
    (hsolution : differentialSpecialization (semanticEquation Q) P = 0)
    (hseparant : jetEvaluation (separant (semanticEquation Q) (Fin.last r)) center
      (polynomialJet center P) ≠ 0)
    (hbinomial : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0) :
    ∃ representation, fromEquationJet? pchar center Q K τ k input = some representation ∧
      representation.WellFormed k ∧ representation.Represents ι θ (P.map ι) := by
  have hS : MvPolynomial.aeval (polynomialJet center P)
      (initialJetSeparant center (semanticEquation Q)) ≠ 0 := by
    rwa [aeval_initialJetSeparant]
  apply TaylorChartMap.fromJet?_covers pchar center k input
    (computedChartNumerators center Q K τ) (computableTaylorDenominator center Q τ)
    hnonzero (by simpa [computedChartNumerators] using hk) ι θ _ (P.map ι)
    (by simpa using hdegree) hpoint
  · rw [fromCMvPolynomial_computableTaylorDenominator, eval₂_mapped_point]
    simpa using pow_ne_zero τ ((map_ne_zero ι).mpr hS)
  · intro i
    have hi : i.val < K := by simpa [computedChartNumerators] using i.isLt
    have hget : fromCMvPolynomial (computedChartNumerators center Q K τ)[i] =
        commonTaylorNumerator center (semanticEquation Q) K ⟨i.val, hi⟩ τ :=
      computedChartNumerators_get center Q K τ i.val hi
    rw [hget,
      fromCMvPolynomial_computableTaylorDenominator, eval₂_mapped_point, eval₂_mapped_point,
      commonTaylorNumerator_solution_of_exponent center (semanticEquation Q) P
        hsolution hseparant K τ hτ hbinomial]
    simp only [_root_.map_mul, map_pow]
    rw [mul_div_cancel_left₀ _ (pow_ne_zero τ ((map_ne_zero ι).mpr hS))]
    rw [← Polynomial.map_taylor, Polynomial.coeff_map]

/-- Exact recovery from solver-covered jets of all sufficiently agreeing messages.
The differential equation, chart and final agreement test are computed. The coverage hypothesis
isolates the outstanding obligation of the sparse solver: supply a raw rational map containing
each required initial jet. Extra represented jets are harmless because recovery checks agreement.
-/
theorem run_exact_of_jet_cover
    {F : Type*} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] {n : ℕ}
    (base : F →+* E) (ι : E →+* L) (domain : Fin n ↪ F) (received : Fin n → F)
    (center : E) (Q : CMvPolynomial (r + 2) E) (K τ k A : ℕ)
    -- K is the retained Taylor width. At least k agreements determine a degree-<k message.
    -- τ covers all individual denominator powers; the paper takes τ=2K and B=S^τ.
    (hk : k ≤ K) (hAk : k ≤ A) (hτ : TaylorExponentSufficient r K τ)
    -- Nonzero binomial pivots make the coefficient recurrence valid in this characteristic.
    (hbinomial : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0)
    (inputs : List (MapData (F := E)))
    -- Every wanted message solves Q regularly, and the raw solver maps cover its initial jet.
    -- This is the remaining producer premise, not an extra acceptance filter on the output.
    (hcover : ∀ P : Polynomial F, P.degree < k →
      A ≤ Code.agree (evalOnPoints domain P) received →
      differentialSpecialization (semanticEquation Q) (P.map base) = 0 ∧
      jetEvaluation (separant (semanticEquation Q) (Fin.last r)) center
        (polynomialJet center (P.map base)) ≠ 0 ∧
      ∃ input ∈ inputs, input.modulus ≠ 0 ∧ ∃ θ : L,
        MapData.RepresentsPoint input ι θ
          (fun i : Fin (r + 1) => ι (polynomialJet center (P.map base) i))) :
    ExactOutput domain received k A
      (run pchar base domain received center Q K τ k A inputs) := by
  apply AgreementRecovery.decode_exact_of_coverage base ι domain received k A hAk
  · intro representation hrepresentation
    obtain ⟨input, _, hinput⟩ := List.mem_filterMap.mp hrepresentation
    exact (TaylorChartMap.fromJet?_properties pchar center k input _ _ representation hinput).1
  · intro P hP
    obtain ⟨hsolution, hseparant, input, hmem, hnonzero, θ, hpoint⟩ := hcover P hP.1 hP.2
    obtain ⟨representation, hrun, _, hrepresented⟩ :=
      fromEquationJet?_covers pchar center Q K τ k hk hτ input hnonzero ι θ (P.map base)
        (by simpa using hP.1) hpoint hsolution hseparant hbinomial
    refine ⟨representation, List.mem_filterMap.mpr ⟨input, hmem, hrun⟩, θ, ?_⟩
    simpa only [Polynomial.map_map] using hrepresented

/-- Neither chart filtering nor final recovery increases the total raw eliminant degree. -/
theorem run_length_le
    {F : Type*} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] {n : ℕ}
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (center : E) (Q : CMvPolynomial (r + 2) E) (K τ k A : ℕ)
    (inputs : List (MapData (F := E))) :
    (run pchar base domain received center Q K τ k A inputs).length ≤
      (inputs.map fun input => input.modulus.natDegree).sum := by
  apply (AgreementRecovery.decode_length_le base domain received k A _).trans
  induction inputs with
  | nil => simp
  | cons input inputs ih =>
      cases hout : fromEquationJet? pchar center Q K τ k input with
      | none =>
          change TaylorChartMap.fromJet? pchar center k input _ _ = none at hout
          simp only [List.filterMap_cons, hout, List.map_cons, List.sum_cons]
          exact ih.trans (Nat.le_add_left _ _)
      | some representation =>
          change TaylorChartMap.fromJet? pchar center k input _ _ = some representation at hout
          simp only [List.filterMap_cons, hout, List.map_cons, List.sum_cons]
          exact Nat.add_le_add
            (TaylorChartMap.fromJet?_properties pchar center k input _ _ representation hout).2 ih

end ReedSolomon.ListDecoding.ComputedTaylorMap
