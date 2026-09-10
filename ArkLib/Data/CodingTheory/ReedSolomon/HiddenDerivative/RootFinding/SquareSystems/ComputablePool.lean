/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.SquareSystems.TaylorTable
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.RootFinding.SquareSystems.SystemEnumeration

/-!
# Executable agreement and coefficient-tail rows

The Taylor recurrence produces an unpadded numerator for each coefficient, with denominator
S^(2(l-r)-1), where S is the initial separant. To compare coefficients in one polynomial
system, pad every numerator to denominator S^τ. Agreement at (x,y) then becomes
Σ_l (x-center)^l N_l - y B = 0, where B=S^τ and N_l is the padded numerator printed in
the decoder section. The degree-<k condition becomes N_k=...=N_(K-1)=0.

These constructors accept the computed recurrence output. The semantic lemmas identify their
results with the paper equations used by the square-system capture proof. Sufficient-exponent
and nonzero-separant hypotheses belong to that capture proof; the polynomial identities below
hold for every τ.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.SquareSystems
open PolynomialDifferential CPoly CPoly.CMvPolynomial
open scoped BigOperators
variable {F : Type*} [Field F] [DecidableEq F] {r K : ℕ}

/-- Multiply the unpadded coefficient numerator by the missing separant power to form N_l. -/
def paddedNumerator (numerators : Fin K → CMvPolynomial (r + 1) F)
    (separant : CMvPolynomial (r + 1) F) (τ : ℕ) (l : Fin K) :
    CMvPolynomial (r + 1) F :=
  numerators l * separant ^ (τ - (2 * (l.val - r) - 1))

/-- Clear the common denominator in the Taylor evaluation equation at one received position. -/
def agreementRow (center : F) (numerators : Fin K → CMvPolynomial (r + 1) F)
    (separant : CMvPolynomial (r + 1) F) (τ : ℕ) (x y : F) :
    CMvPolynomial (r + 1) F :=
  (∑ l : Fin K, C ((x - center) ^ l.val) * paddedNumerator numerators separant τ l) -
    C y * separant ^ τ

private theorem denote_pow (p : CMvPolynomial (r + 1) F) (m : ℕ) :
    fromCMvPolynomial (p ^ m) = fromCMvPolynomial p ^ m :=
  _root_.map_pow (polyRingEquiv (n := r + 1) (R := F)) p m

/-- Padding the concrete numerator gives exactly the decoder section's N_l. -/
theorem paddedNumerator_semantics (center : F)
    (Q : PolynomialDifferential.DifferentialPolynomial F r)
    (numerators : Fin K → CMvPolynomial (r + 1) F)
    (separant : CMvPolynomial (r + 1) F) (τ : ℕ)
    (hN : ∀ l, fromCMvPolynomial (numerators l) = rationalTaylorNumerator center Q l.val)
    (hS : fromCMvPolynomial separant = initialJetSeparant center Q) (l : Fin K) :
    fromCMvPolynomial (paddedNumerator numerators separant τ l) =
      commonTaylorNumerator center Q K l (τ := τ) := by
  rw [paddedNumerator, fromCMvPolynomial_mul', denote_pow, hN, hS]
  rfl

/-- The executable agreement row denotes the same cleared equation as the capture theorem. -/
theorem agreementRow_semantics (center : F)
    (Q : PolynomialDifferential.DifferentialPolynomial F r)
    (numerators : Fin K → CMvPolynomial (r + 1) F)
    (separant : CMvPolynomial (r + 1) F) (τ : ℕ)
    (hN : ∀ l, fromCMvPolynomial (numerators l) = rationalTaylorNumerator center Q l.val)
    (hS : fromCMvPolynomial separant = initialJetSeparant center Q) (x y : F) :
    fromCMvPolynomial (agreementRow center numerators separant τ x y) =
      taylorAgreementEquation center Q K x y (τ := τ) := by
  simp only [agreementRow, fromCMvPolynomial_sub', fromCMvPolynomial_sum,
    fromCMvPolynomial_mul', fromCMvPolynomial_C, denote_pow, hS,
    paddedNumerator_semantics center Q numerators separant τ hN hS,
    taylorAgreementEquation]


/-- All n agreement rows followed by the K-k tail rows, retaining their original labels. -/
def computableFullPool (center : F) (numerators : Fin K → CMvPolynomial (r + 1) F)
    (separant : CMvPolynomial (r + 1) F) (τ k n : ℕ) (hk : k ≤ K)
    (domain : Fin n ↪ F) (received : Fin n → F) :
    Fin n ⊕ Fin (K - k) → CMvPolynomial (r + 1) F
  | Sum.inl i => agreementRow center numerators separant τ (domain i) (received i)
  | Sum.inr j => paddedNumerator numerators separant τ (tailIndex hk j)

/-- Pointwise denotation identifies the complete executable pool with the semantic pool. -/
theorem computableFullPool_semantics (center : F)
    (Q : PolynomialDifferential.DifferentialPolynomial F r)
    (numerators : Fin K → CMvPolynomial (r + 1) F)
    (separant : CMvPolynomial (r + 1) F) (τ k n : ℕ) (hk : k ≤ K)
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hN : ∀ l, fromCMvPolynomial (numerators l) = rationalTaylorNumerator center Q l.val)
    (hS : fromCMvPolynomial separant = initialJetSeparant center Q)
    (i : Fin n ⊕ Fin (K - k)) :
    fromCMvPolynomial (computableFullPool center numerators separant τ k n hk domain received i) =
      fullCandidatePoolEquation center Q K k n τ hk domain received i := by
  cases i with
  | inl i => exact agreementRow_semantics center Q numerators separant τ hN hS _ _
  | inr i => exact paddedNumerator_semantics center Q numerators separant τ hN hS _

local instance sumFinOrderForConcretePool (a b : ℕ) : LinearOrder (Fin a ⊕ Fin b) :=
  finSumFinEquiv.linearOrder

/-- Enumerate literal concrete square systems from a supplied Taylor numerator family. -/
def computableSquareSystems (center : F) (Q : CMvPolynomial (r + 2) F)
    (numerators : Fin K → CMvPolynomial (r + 1) F)
    (τ k n : ℕ) (hk : k ≤ K) (domain : Fin n ↪ F) (received : Fin n → F) :
    Finset (Fin (r + 1) → CMvPolynomial (r + 1) F) :=
  enumerateSquareSystems r (computableInitialJetEquation center Q)
    (computableFullPool center numerators (computableInitialJetSeparant center Q)
      τ k n hk domain received)

/-- Every regular agreeing polynomial solution is a simple zero of one emitted concrete system. -/
theorem exists_computableSquareSystem (center : F) (Q : CMvPolynomial (r + 2) F)
    (numerators : Fin K → CMvPolynomial (r + 1) F)
    (hN : ∀ l, fromCMvPolynomial (numerators l) =
      rationalTaylorNumerator center (semanticEquation Q) l.val)
    (k n A τ : ℕ) (hK : r < K) (hk : k ≤ K) (hkA : k ≤ A)
    -- τ dominates every coefficient denominator exponent 2(l-r)-1 for l<K; τ=2K suffices.
    (hτ : TaylorExponentSufficient r K τ)
    (domain : Fin n ↪ F) (received : Fin n → F) (agreementPositions : Fin A ↪ Fin n)
    (P : Polynomial F) (hsolution : differentialSpecialization (semanticEquation Q) P = 0)
    (hseparant : jetEvaluation (separant (semanticEquation Q) (Fin.last r)) center
      (polynomialJet center P) ≠ 0)
    -- The pivot binomial(i,r) must be invertible to solve each higher Taylor coefficient.
    (hbinomial : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    (hdegree : P.degree < k)
    (hagreement : ∀ i, P.eval (domain (agreementPositions i)) =
      received (agreementPositions i)) :
    ∃ rows ∈ computableSquareSystems center Q numerators τ k n hk domain received,
      (∀ i, MvPolynomial.aeval (polynomialJet center P) (fromCMvPolynomial (rows i)) = 0) ∧
      (formalJacobian (polynomialJet center P)
        (fun i => fromCMvPolynomial (rows i))).det ≠ 0 := by
  obtain ⟨selected, hselected, hzero, _, hdet⟩ :=
    exists_emittedCandidateSquareSystem center (semanticEquation Q) K k n A τ hK hk hkA hτ
      domain received agreementPositions P hsolution hseparant hbinomial hdegree hagreement
  let pool := computableFullPool center numerators (computableInitialJetSeparant center Q)
    τ k n hk domain received
  let rows := squareSystemRows (computableInitialJetEquation center Q) pool
    (rowSubsetEmbedding selected hselected)
  have hrows : (fun i => fromCMvPolynomial (rows i)) =
      squareSystemRows (initialJetEquation center (semanticEquation Q))
        (fullCandidatePoolEquation center (semanticEquation Q) K k n τ hk domain received)
        (rowSubsetEmbedding selected hselected) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · exact fromCMvPolynomial_computableInitialJetEquation center Q
    · exact computableFullPool_semantics center (semanticEquation Q) numerators
        (computableInitialJetSeparant center Q) τ k n hk domain received hN
        (fromCMvPolynomial_computableInitialJetSeparant center Q) _
  refine ⟨rows, squareSystemRows_mem_enumerate _ _ selected hselected, ?_, ?_⟩
  · intro i
    exact (congrArg (fun f => MvPolynomial.aeval (polynomialJet center P) (f i)) hrows).trans
      (hzero i)
  · simpa only [hrows] using hdet

/-- Compute every Taylor numerator and then every square system from the concrete equation. -/
def squareSystemsFromEquation (center : F) (Q : CMvPolynomial (r + 2) F)
    (K τ k n : ℕ) (hk : k ≤ K) (domain : Fin n ↪ F) (received : Fin n → F) :
    Finset (Fin (r + 1) → CMvPolynomial (r + 1) F) :=
  let table := computableRationalTaylorTable center Q K
  computableSquareSystems center Q
    (fun l : Fin K => table[l.val]'(by simp [table]))
    τ k n hk domain received

/-- The computed numerator recurrence discharges the representation hypothesis in square capture.
The remaining hypotheses are the paper's regularity, truncation, characteristic and agreement
conditions; no equations or polynomial roots are supplied by an oracle. -/
theorem squareSystemsFromEquation_covers (center : F) (Q : CMvPolynomial (r + 2) F)
    (K k n A τ : ℕ) (hK : r < K) (hk : k ≤ K) (hkA : k ≤ A)
    -- τ dominates every coefficient denominator exponent 2(l-r)-1 for l<K; τ=2K suffices.
    (hτ : TaylorExponentSufficient r K τ)
    (domain : Fin n ↪ F) (received : Fin n → F) (agreementPositions : Fin A ↪ Fin n)
    (P : Polynomial F) (hsolution : differentialSpecialization (semanticEquation Q) P = 0)
    (hseparant : jetEvaluation (separant (semanticEquation Q) (Fin.last r)) center
      (polynomialJet center P) ≠ 0)
    -- The pivot binomial(i,r) must be invertible to solve each higher Taylor coefficient.
    (hbinomial : ∀ i, r < i → i < K → (i.choose r : F) ≠ 0)
    (hdegree : P.degree < k)
    (hagreement : ∀ i, P.eval (domain (agreementPositions i)) =
      received (agreementPositions i)) :
    ∃ rows ∈ squareSystemsFromEquation center Q K τ k n hk domain received,
      (∀ i, MvPolynomial.aeval (polynomialJet center P) (fromCMvPolynomial (rows i)) = 0) ∧
      (formalJacobian (polynomialJet center P)
        (fun i => fromCMvPolynomial (rows i))).det ≠ 0 := by
  apply exists_computableSquareSystem center Q _ ?_
    k n A τ hK hk hkA hτ domain received agreementPositions P hsolution hseparant hbinomial
    hdegree hagreement
  intro l
  rw [computableRationalTaylorTable_get center Q K l.val l.isLt]
  exact fromCMvPolynomial_computableRationalTaylorNumerator center Q l.val

end ReedSolomon.HiddenDerivative.SquareSystems
