/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.ComputedTaylorMap
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.FieldTransport
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.SquareSystems.SystemList
public import ArkLib.Data.Polynomial.Rojas.AffineSolver
public import ArkLib.ToCompPoly.Multivariate.BaseChange

/-!
# Square-system decoding with an explicit torus backend

Starting with a differential equation Q and a regular Taylor center, the program computes the
agreement-and-tail pool, enumerates its square subsystems, and runs the affine wrapper on each.
The resulting rational maps describe initial jets. The computed Taylor chart extends them to
message coefficients, and shared agreement recovery returns precisely the qualifying messages.

The torus backend is an explicit program argument. Its isolated-root coverage contract is the
remaining sparse-elimination obligation; the wrapper does not manufacture a resultant algorithm
or a runtime theorem. Extra roots need no differential-equation filter: the final agreement test
is exactly the acceptance condition in the paper.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.SquareSystemDecoder
open PolynomialDifferential ReedSolomon.HiddenDerivative ReedSolomon.HiddenDerivative.SquareSystems
open CompPoly CPoly CPoly.CMvPolynomial ArkLib.UnivariateRepresentation
open ArkLib.Rojas.AffineSolver FieldTransport
variable {F E : Type*} [Field F] [Field E] [Fintype E]
variable [DecidableEq F] [BEq F] [LawfulBEq F] [DecidableEq E] [BEq E] [LawfulBEq E]
variable {r n : ℕ}

/-- Enumerate the square systems and concatenate the maps from their affine charts.
Each system has r+1 unknown jet coordinates. More than r+1 distinct shifts suffice to move every
such point into at least one torus chart, where the backend's completeness contract applies. -/
def jetMaps (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (center : E) (Q : CMvPolynomial (r + 2) E) (K τ k : ℕ) (hk : k ≤ K)
    (backend : TorusBackend (F := E) (s := r + 1)) (shifts : List E) :
    List (MapData (F := E)) :=
  (squareSystemsListFromEquation center Q K τ k n hk
    (liftedDomain base domain) (fun i => base (received i))).flatMap
      (solveAffine backend shifts)

/-- Compute the jet maps, extend through the common-denominator Taylor chart, and recover F-lists.
Here K is the retained Taylor width and τ is the common separant exponent; the paper uses τ=2K. -/
def run (pchar : ℕ) [Fact pchar.Prime] [CharP E pchar]
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (center : E) (Q : CMvPolynomial (r + 2) E) (K τ k A : ℕ) (hk : k ≤ K)
    (backend : TorusBackend (F := E) (s := r + 1)) (shifts : List E) : List (List F) :=
  ComputedTaylorMap.run pchar base domain received center Q K τ k A
    (jetMaps base domain received center Q K τ k hk backend shifts)

omit [Fintype E] [DecidableEq F] [BEq F] [LawfulBEq F] in
/-- The concrete square-family bound also controls how many raw maps the program handles.
There are at most (2n)^r systems when K≤n, and each affine wrapper makes one call per shift.
The bound B remains the torus backend's output-count guarantee, not an assumed runtime bound. -/
theorem jetMaps_length_le (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (center : E) (Q : CMvPolynomial (r + 2) E) (K τ k : ℕ) (hk : k ≤ K) (hKn : K ≤ n)
    (backend : TorusBackend (F := E) (s := r + 1)) (shifts : List E)
    (B : ℕ) (hbackend : ∀ system, (backend system).length ≤ B) :
    (jetMaps base domain received center Q K τ k hk backend shifts).length ≤
      (2 * n) ^ r * (shifts.length * B) := by
  have hlist : ∀ systems : List (Fin (r + 1) → CMvPolynomial (r + 1) E),
      (systems.flatMap (solveAffine backend shifts)).length ≤
        systems.length * (shifts.length * B) := by
    intro systems
    induction systems with
    | nil => simp
    | cons system systems ih =>
      have h := solveAffine_length_le backend shifts B hbackend system
      simp only [List.flatMap_cons, List.length_append, List.length_cons,
        Nat.add_mul, one_mul]
      omega
  exact (hlist _).trans (Nat.mul_le_mul_right _
    (length_squareSystemsListFromEquation_le center Q K τ k n hk hKn
      (liftedDomain base domain) (fun i => base (received i))))

/-- Final filtering and recovery cannot increase the sum of raw eliminant degrees. -/
theorem run_length_le (pchar : ℕ) [Fact pchar.Prime] [CharP E pchar]
    (base : F →+* E) (domain : Fin n ↪ F) (received : Fin n → F)
    (center : E) (Q : CMvPolynomial (r + 2) E) (K τ k A : ℕ) (hk : k ≤ K)
    (backend : TorusBackend (F := E) (s := r + 1)) (shifts : List E) :
    (run pchar base domain received center Q K τ k A hk backend shifts).length ≤
      ((jetMaps base domain received center Q K τ k hk backend shifts).map
        fun input => input.modulus.natDegree).sum :=
  ComputedTaylorMap.run_length_le pchar base domain received center Q K τ k A _

omit [BEq F] [LawfulBEq F] in
/-- A degree threshold expressed as an agreement count supplies distinct agreeing positions.
This witness is used only in the completeness proof; the decoder enumerates pool-row subsets
without knowing the message or its agreeing positions. -/
private theorem exists_agreementPositions (domain : Fin n ↪ F) (received : Fin n → F)
    (P : Polynomial F) (k : ℕ) (h : k ≤ Code.agree (evalOnPoints domain P) received) :
    ∃ positions : Fin k ↪ Fin n,
      ∀ i, P.eval (domain (positions i)) = received (positions i) := by
  let positions : Finset (Fin n) := Finset.univ.filter fun i => P.eval (domain i) = received i
  have hcard : k ≤ positions.card := h
  refine ⟨(positions.orderEmbOfCardLe hcard).toEmbedding, ?_⟩
  intro i
  exact (Finset.mem_filter.mp (positions.orderEmbOfCardLe_mem hcard i)).2

/-- Exact decoding from a regular differential equation and an isolated-root-complete torus
backend. The square-capture theorem supplies a nonsingular system for every wanted message;
affine coverage supplies its jet map, and the common recovery stage enforces degree and agreement.
No hypothesis asks the backend to exclude extraneous roots or positive-dimensional components. -/
theorem run_exact_of_torus_cover (pchar : ℕ) [Fact pchar.Prime] [CharP E pchar]
    {L : Type*} [Field L] (base : F →+* E) (ι : E →+* L)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (center : E) (Q : CMvPolynomial (r + 2) E) (K τ k A : ℕ)
    -- Retaining K coefficients provides both the r+1 initial coordinates and the k message slots.
    (hK : r < K) (hk : k ≤ K) (hAk : k ≤ A)
    -- B=S^τ clears every Taylor coefficient denominator; τ=2K is the paper's uniform choice.
    (hτ : TaylorExponentSufficient r K τ)
    (hbinomial : ∀ i, r < i → i < K → (i.choose r : E) ≠ 0)
    (backend : TorusBackend (F := E) (s := r + 1))
    (hbackend : CoversTorusIsolatedRoots backend ι)
    -- One more scalar shift than jet coordinates guarantees an affine-to-torus chart.
    (shifts : List E) (hnodup : shifts.Nodup) (hlength : r + 1 < shifts.length)
    -- These are the given-Q and regular-center premises, before sparse root finding begins.
    (hsolution : ∀ P : Polynomial F, P.degree < k →
      A ≤ Code.agree (evalOnPoints domain P) received →
      differentialSpecialization (semanticEquation Q) (P.map base) = 0)
    (hregular : ∀ P : Polynomial F, P.degree < k →
      A ≤ Code.agree (evalOnPoints domain P) received →
      jetEvaluation (separant (semanticEquation Q) (Fin.last r)) center
        (polynomialJet center (P.map base)) ≠ 0) :
    ExactOutput domain received k A
      (run pchar base domain received center Q K τ k A hk backend shifts) := by
  apply ComputedTaylorMap.run_exact_of_jet_cover pchar base ι domain received center Q K τ k A
    hk hAk hτ hbinomial
  intro P hdegree hagreement
  have hsol := hsolution P hdegree hagreement
  have hreg := hregular P hdegree hagreement
  refine ⟨hsol, hreg, ?_⟩
  obtain ⟨positions, hpositions⟩ := exists_agreementPositions domain received P k
    (hAk.trans hagreement)
  have hmappedAgreement : ∀ i,
      (P.map base).eval ((liftedDomain base domain) (positions i)) =
        base (received (positions i)) := by
    intro i
    change (P.map base).eval (base (domain (positions i))) = _
    rw [Polynomial.eval_map_apply, hpositions i]
  obtain ⟨rows, hrows, hroot, hjacobian⟩ := squareSystemsFromEquation_covers center Q
    K k n k τ hK hk le_rfl hτ (liftedDomain base domain) (fun i => base (received i))
    positions (P.map base) hsol hreg hbinomial (by simpa using hdegree) hmappedAgreement
  have hrootConcrete : ∀ j,
      (rows j).eval₂ (RingHom.id E) (polynomialJet center (P.map base)) = 0 := by
    intro j
    simpa [CPoly.eval₂_equiv] using hroot j
  have hjacobianConcrete : Matrix.det (fun j i =>
      (partialDerivative i (rows j)).eval₂ (RingHom.id E)
        (polynomialJet center (P.map base))) ≠ 0 := by
    unfold ReedSolomon.HiddenDerivative.SquareSystems.formalJacobian at hjacobian
    simpa [
      MvPolynomial.aeval_eq_eval₂Hom, CPoly.eval₂_equiv,
      fromCMvPolynomial_partialDerivative] using hjacobian
  -- The field embedding transports the root and nonzero determinant to the backend's field.
  have hrootExtension : ∀ j,
      (rows j).eval₂ ι (fun i => ι (polynomialJet center (P.map base) i)) = 0 := by
    intro j
    rw [eval₂_map_point]
    exact (congrArg ι (hrootConcrete j)).trans (map_zero ι)
  have hjacobianExtension : Matrix.det (fun j i =>
      (partialDerivative i (rows j)).eval₂ ι
        (fun i => ι (polynomialJet center (P.map base) i))) ≠ 0 := by
    exact jacobian_det_ne_zero_map ι _ rows hjacobianConcrete
  obtain ⟨theta, output, houtput, hnonzero, hpoint⟩ := solveAffine_covers_nonsingular ι backend
    hbackend shifts hnodup hlength rows _ hrootExtension hjacobianExtension
  refine ⟨output, ?_, hnonzero, theta, hpoint⟩
  apply List.mem_flatMap.mpr
  exact ⟨rows, (mem_squareSystemsListFromEquation_iff center Q K τ k n hk
    (liftedDomain base domain) (fun i => base (received i)) rows).mpr hrows, houtput⟩

end ReedSolomon.ListDecoding.SquareSystemDecoder
