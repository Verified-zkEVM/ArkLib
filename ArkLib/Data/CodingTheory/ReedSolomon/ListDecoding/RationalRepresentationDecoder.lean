/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.UnivariateRepresentation.FromRaw
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.AgreementRecovery.Decoder
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.Ordinary.QuotientLift.Materialize

/-!
# Shared decoding from rational Taylor-coordinate maps

A symbolic solver supplies an eliminant `h(U)`, a common denominator `B(U)`, and ascending Taylor
numerators `N_0(U), …, N_{K-1}(U)`. At each represented root, the ratios `N_j/B` are the
coefficients of a branch around the chosen center.

`fromRational?` first computes the squarefree support of `h`. It retains `B ≠ 0`, imposes the tail
conditions `N_k = … = N_{K-1} = 0`, and inverts `B` on the surviving modulus. The resulting
polynomial coordinates are shifted back to the original variable and materialized as a reduced,
fixed-width finite representation. The final `run` uses the same batched agreement recovery as
the ordinary quotient decoder; there is no additional differential-equation output filter.

`run_exact_of_cover` states exactly what remains for a solver producer: its actual finite maps
must cover every wanted message. It does not assume that represented parameter roots belong to
the coefficient field, or that every represented specialization is wanted. Constructing the
Rojas eliminants and their Taylor-coordinate maps is a separate producer obligation.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.RationalRepresentationDecoder
open CompPoly CompPoly.CPolynomial
open ArkLib.UnivariateRepresentation
open ReedSolomon.HiddenDerivative.Ordinary.QuotientLift
universe u
variable {E : Type u} [Field E] [Fintype E] [BEq E] [LawfulBEq E]
variable (pchar : ℕ) [Fact pchar.Prime] [CharP E pchar]

/-- Store ascending Taylor coordinates as coefficients of the centered series variable. -/
def seriesOfCoordinates (coordinates : List (CPolynomial E)) : Series E :=
  CPolynomial.ofArray coordinates.toArray

/-- Normalize the eliminant, filter the denominator and tails, then materialize the message. -/
def fromRational? (center : E) (k : ℕ) (input : MapData (F := E)) :
    Option (FiniteRepresentation E) := do
  let output ← postprocessRaw? pchar input (input.numerators.drop k)
  return ReedSolomon.HiddenDerivative.Ordinary.QuotientLift.materialize
    output.modulus center k (seriesOfCoordinates output.coordinates)

/-- Apply rational-map conversion to each solver output and invoke shared exact agreement
recovery. -/
def run {F : Type*} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] {n : ℕ}
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (center : E) (k A : ℕ) (inputs : List (MapData (F := E))) : List (List F) :=
  AgreementRecovery.decode base domain received k A
    (inputs.filterMap (fromRational? pchar center k))

noncomputable section
variable {L : Type*} [Field L]
omit [Fintype E] [Fact pchar.Prime] [CharP E pchar] in
/-- The raw rational coordinates are the Taylor coefficients of P at the specified center. -/
def Represents (input : MapData (F := E)) (ι : E →+* L) (θ center : L)
    (P : Polynomial L) : Prop :=
  input.modulus.toPoly.eval₂ ι θ = 0 ∧
  input.denominator.toPoly.eval₂ ι θ ≠ 0 ∧
  ∀ i : Fin input.numerators.length,
    input.numerators[i].toPoly.eval₂ ι θ / input.denominator.toPoly.eval₂ ι θ =
      (Polynomial.taylor center P).coeff i

omit [Fintype E] [Fact pchar.Prime] [CharP E pchar] in
/-- Reading a materialized series coefficient reads the same coordinate from the ascending list. -/
theorem coeff_seriesOfCoordinates (ι : E →+* L) (θ : L)
    (coordinates : List (CPolynomial E)) (i : ℕ) :
    (specialize ι θ (seriesOfCoordinates coordinates)).coeff i =
      (coordinates[i]?.getD 0).toPoly.eval₂ ι θ := by
  rw [coeff_specialize, seriesOfCoordinates, CPolynomial.coeff_ofArray]
  by_cases hi : i < coordinates.length
  · simp [Array.getD, hi]
  · simp [Array.getD, hi]

omit [Fintype E] [BEq E] [LawfulBEq E] [Fact pchar.Prime] [CharP E pchar] in
/-- A degree-`< k` polynomial has zero Taylor tail, so a covered message survives all tail
filters. -/
theorem tail_vanishes (input : MapData (F := E)) (ι : E →+* L) (θ center : L)
    (P : Polynomial L) (k : ℕ) (hdegree : P.degree < k)
    (hrep : Represents input ι θ center P) :
    ∀ equation ∈ input.numerators.drop k, equation.toPoly.eval₂ ι θ = 0 := by
  intro equation heq
  obtain ⟨i, hi, heq⟩ := List.mem_iff_getElem.mp heq
  have hirange : k + i < input.numerators.length := by
    rw [List.length_drop] at hi
    omega
  have hcoord := hrep.2.2 ⟨k+i, hirange⟩
  have hzero : (Polynomial.taylor center P).coeff (k+i) = 0 :=
    Polynomial.coeff_eq_zero_of_degree_lt (by
      rw [Polynomial.degree_taylor]
      exact hdegree.trans_le (by exact_mod_cast Nat.le_add_right k i))
  rw [hzero] at hcoord
  have hn := (div_eq_zero_iff).mp hcoord
  have : input.numerators[k+i].toPoly.eval₂ ι θ = 0 := hn.resolve_right hrep.2.1
  rw [List.getElem_drop] at heq
  simpa only [heq] using this

/-- A covered polynomial survives normalization and filtering and is represented after
shift-back. -/
theorem fromRational?_covers (center : E) (k : ℕ) (input : MapData (F := E))
    (hnonzero : input.modulus ≠ 0) (hwidth : k ≤ input.numerators.length)
    (ι : E →+* L) (θ : L) (P : Polynomial L) (hdegree : P.degree < k)
    (hrep : Represents input ι θ (ι center) P) :
    ∃ r, fromRational? pchar center k input = some r ∧ r.WellFormed k ∧ r.Represents ι θ P := by
  -- Empty retained root sets are encoded by modulus 1, so nonzero input still produces a result.
  obtain ⟨output, houtput, hcorrect⟩ := postprocessRaw?_exists_correct pchar input
    (input.numerators.drop k) hnonzero
  -- P has no coefficients beyond k, and its denominator is nonzero: every filter keeps theta.
  have hretained : output.modulus.toPoly.eval₂ ι θ = 0 :=
    (hcorrect.roots ι θ).mpr ⟨hrep.1, hrep.2.1, tail_vanishes input ι θ (ι center) P k hdegree hrep⟩
  have hcoords := hcorrect.coordinates ι θ hretained
  have hlength : output.coordinates.length = input.numerators.length := hcoords.length_eq.symm
  -- The postprocessor returns N_j/B in the same order, including leading and trailing zeros.
  have hseries : specialize ι θ (seriesOfCoordinates output.coordinates) =
      Polynomial.taylor (ι center) P := by
    ext j
    rw [coeff_seriesOfCoordinates]
    by_cases hj : j < input.numerators.length
    · have hjout : j < output.coordinates.length := by simpa [hlength] using hj
      have hcoord := hcoords.get hj hjout
      have hvalue := hrep.2.2 ⟨j, hj⟩
      simpa [hjout] using hcoord.trans hvalue
    · have hjout : ¬ j < output.coordinates.length := by simpa [hlength] using hj
      have hpzero : (Polynomial.taylor (ι center) P).coeff j = 0 :=
        Polynomial.coeff_eq_zero_of_degree_lt (by
          rw [Polynomial.degree_taylor]
          exact hdegree.trans_le (by exact_mod_cast (hwidth.trans (Nat.le_of_not_gt hj))))
      simp [hjout, hpzero, toPoly_zero]
  refine ⟨ReedSolomon.HiddenDerivative.Ordinary.QuotientLift.materialize output.modulus center k
    (seriesOfCoordinates output.coordinates), ?_, ?_, ?_⟩
  · simp [fromRational?, houtput]
  · exact materialize_wellFormed output.modulus center k _
      ((monic_toPoly_iff _).mp hcorrect.modulus_monic) hcorrect.modulus_squarefree
  · exact ⟨hretained, materialize_specialize ι θ output.modulus center k _ P
      ((monic_toPoly_iff _).mp hcorrect.modulus_monic) hretained hseries hdegree⟩

/-- Every emitted representation is well formed, and filtering never increases its modulus
degree. -/
theorem fromRational?_properties (center : E) (k : ℕ) (input : MapData (F := E))
    (r : FiniteRepresentation E) (hr : fromRational? pchar center k input = some r) :
    r.WellFormed k ∧ r.modulus.natDegree ≤ input.modulus.natDegree := by
  unfold fromRational? at hr
  cases hpost : postprocessRaw? pchar input (input.numerators.drop k) with
  | none => simp [hpost] at hr
  | some output =>
      rw [hpost] at hr
      change some (ReedSolomon.HiddenDerivative.Ordinary.QuotientLift.materialize
        output.modulus center k (seriesOfCoordinates output.coordinates)) = some r at hr
      have heq := Option.some.inj hr
      subst r
      have hnonzero : input.modulus ≠ 0 := by
        intro hz
        simp [postprocessRaw?, hz] at hpost
      have hc := postprocessRaw?_correct.{u, u, u} pchar hnonzero hpost
      exact ⟨materialize_wellFormed output.modulus center k _
        ((monic_toPoly_iff _).mp hc.modulus_monic) hc.modulus_squarefree, hc.modulus_natDegree_le⟩

/-- **Exact decoding from rational Taylor maps.** Covering every wanted polynomial suffices for
the executable pipeline to return precisely its duplicate-free width-k coefficient list. -/
theorem run_exact_of_cover
    {F : Type*} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] {n : ℕ}
    (base : F →+* E) (ι : E →+* L) (domain : Fin n ↪ F) (received : Fin n → F)
    (center : E) (k A : ℕ) (hAk : k ≤ A) (inputs : List (MapData (F := E)))
    (hcover : ∀ P : Polynomial F, P.degree < k →
      A ≤ Code.agree (evalOnPoints domain P) received →
      ∃ input ∈ inputs, input.modulus ≠ 0 ∧ k ≤ input.numerators.length ∧
        ∃ θ : L, Represents input ι θ (ι center) (P.map (ι.comp base))) :
    ExactOutput domain received k A (run pchar base domain received center k A inputs) := by
  apply AgreementRecovery.decode_exact_of_coverage base ι domain received k A hAk
  · intro r hr
    obtain ⟨input, _, hinput⟩ := List.mem_filterMap.mp hr
    exact (fromRational?_properties pchar center k input r hinput).1
  · intro P hP
    obtain ⟨input, hmem, hnonzero, hwidth, θ, hrep⟩ := hcover P hP.1 hP.2
    have hdegree : (P.map (ι.comp base)).degree < k := by
      simpa only [Polynomial.degree_map_eq_of_injective (ι.comp base).injective] using hP.1
    obtain ⟨r, hrun, _, hrepresented⟩ := fromRational?_covers pchar center k input hnonzero hwidth
      ι θ (P.map (ι.comp base)) hdegree hrep
    exact ⟨r, List.mem_filterMap.mpr ⟨input, hmem, hrun⟩, θ, hrepresented⟩

/-- The sum of raw eliminant degrees bounds the final message count; normalization only lowers
it. -/
theorem run_length_le
    {F : Type*} [Field F] [DecidableEq F] [BEq F] [LawfulBEq F] {n : ℕ}
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (center : E) (k A : ℕ) (inputs : List (MapData (F := E))) :
    (run pchar base domain received center k A inputs).length ≤
      (inputs.map fun input => input.modulus.natDegree).sum := by
  apply (AgreementRecovery.decode_length_le base domain received k A _).trans
  induction inputs with
  | nil => simp
  | cons input inputs ih =>
      cases hout : fromRational? pchar center k input with
      | none =>
          simp only [List.filterMap_cons, hout, List.map_cons, List.sum_cons]
          exact ih.trans (Nat.le_add_left _ _)
      | some r =>
          simp only [List.filterMap_cons, hout, List.map_cons, List.sum_cons]
          exact Nat.add_le_add (fromRational?_properties pchar center k input r hout).2 ih

end
end ReedSolomon.ListDecoding.RationalRepresentationDecoder
