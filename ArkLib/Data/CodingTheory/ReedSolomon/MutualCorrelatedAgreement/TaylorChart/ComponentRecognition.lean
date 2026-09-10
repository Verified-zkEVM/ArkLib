/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TaylorChart.PointRecognition
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.GraphPullback
/-!
# Recognizing prime components of the symbolic source chart

Flattening the retained challenge commutes with point evaluation. A positive-dimensional
regular prime component containing high-coefficient cuts and a common sample lies on an
actual base-field pair graph. Restriction to that graph preserves every ideal equation
and keeps the separant nonzero.
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

namespace MvPolynomial

variable {E σ : Type*} [Field E]

/-- Evaluating after separating the challenge coordinate is evaluation of the original
joint polynomial. -/
theorem aeval_map_optionEquivRight (x : Option σ → E)
    (p : MvPolynomial (Option σ) E) :
    aeval (fun j ↦ x (some j))
      (MvPolynomial.map (Polynomial.evalRingHom (x none)) (optionEquivRight E σ p)) =
        aeval x p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
      simp only [map_mul, hp]
      congr 1
      cases i <;> simp

/-- Evaluating a flattened symbolic polynomial specializes its challenge coefficient first. -/
theorem aeval_optionEquivRight_symm (x : Option σ → E)
    (p : MvPolynomial σ (Polynomial E)) :
    aeval x ((optionEquivRight E σ).symm p) =
      aeval (fun j ↦ x (some j))
        (MvPolynomial.map (Polynomial.evalRingHom (x none)) p) := by
  simpa only [AlgEquiv.apply_symm_apply] using
    (aeval_map_optionEquivRight x ((optionEquivRight E σ).symm p)).symm

end MvPolynomial

namespace ReedSolomon

open Polynomial MvPolynomial HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n k K r : ℕ}

/-- The initial differential equation in joint source coordinates. -/
def symbolicSourceInitialEquation (center : E) (Q : DifferentialPolynomial E[X] r) :
    MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E _).symm (initialJetEquationOver (Polynomial.C center) Q)

/-- The separant viewed as a polynomial in challenge and initial jets. -/
def symbolicSourceSeparant (center : E) (Q : DifferentialPolynomial E[X] r) :
    MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E _).symm (initialJetSeparantOver (Polynomial.C center) Q)

/-- One high-coefficient numerator in joint source coordinates. -/
def symbolicSourceNumerator (center : E) (Q : DifferentialPolynomial E[X] r)
    (K : ℕ) (l : Fin K) (τ : ℕ := 2 * K) : MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E _).symm
    (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K l (τ := τ))

/-- One polynomial-valued received-word agreement cut in joint source coordinates.  The
challenge variable of `received` is identified with the source challenge coordinate. -/
def symbolicSourcePolynomialAgreement (center : E) (Q : DifferentialPolynomial E[X] r)
    (K : ℕ) (alpha : E) (received : E[X]) (τ : ℕ := 2 * K) :
    MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E _).symm
    (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K (Polynomial.C alpha)
      received (τ := τ))

/-- One received-line agreement cut in joint source coordinates. -/
def symbolicSourceAgreement (center : E) (Q : DifferentialPolynomial E[X] r)
    (K : ℕ) (alpha f g : E) (τ : ℕ := 2 * K) :
    MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E _).symm
    (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K (Polynomial.C alpha)
      (Polynomial.C f + Polynomial.X * Polynomial.C g) (τ := τ))

/-- The cleared identity identifying one reconstructed coefficient with an affine pair. -/
def symbolicSourceReconstructionError (center : E) (Q : DifferentialPolynomial E[X] r)
    (K : ℕ) (P₀ P₁ : E[X]) (l : Fin K) (τ : ℕ := 2 * K) :
    MvPolynomial (Option (Fin (r + 1))) E :=
  symbolicSourceNumerator center Q K l (τ := τ) - symbolicSourceSeparant center Q ^ τ *
    (MvPolynomial.C ((Polynomial.taylor center P₀).coeff l.val) +
      MvPolynomial.X none * MvPolynomial.C ((Polynomial.taylor center P₁).coeff l.val))

/-- Exponent-aware pointwise graph recognition.  One sample determines a base-field pair
uniformly for every regular symbolic chart point satisfying the high cuts and agreement cuts at
the same common exponent `τ`. -/
theorem exists_graphLine_pair_of_symbolic_sample_of_exponent
    {F E : Type*} [Field F] [Field E] {n k K r : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (sample : Finset (Fin n)) (hsample : sample.card = k)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (hK : r < K) (τ : ℕ) (hτ : TaylorExponentSufficient r K τ) :
    ∃ P₀ P₁ : F[X], P₀.degree < k ∧ P₁.degree < k ∧
      (∀ i ∈ sample, P₀.eval (domain i) = f i ∧ P₁.eval (domain i) = g i) ∧
      ∀ (z : E) (jet : Fin (r + 1) → E),
        aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
          (initialJetSeparantOver (Polynomial.C center) Q)) ≠ 0 →
        (∀ l : Fin K, k ≤ l.val →
          aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
            (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K l
              (τ := τ))) = 0) →
        (∀ i ∈ sample,
          aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
            (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
              (Polynomial.C (iota (domain i)))
              (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i)))
              (τ := τ))) = 0) →
        rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom z) Q) K jet =
            P₀.map iota + Polynomial.C z * P₁.map iota ∧
          jet = (fun j ↦ polynomialJet (d := r) center (P₀.map iota) j +
            z * polynomialJet (d := r) center (P₁.map iota) j) ∧
          ∀ l : Fin K,
            aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
              (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K l
                (τ := τ))) =
              aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
                (initialJetSeparantOver (Polynomial.C center) Q)) ^ τ *
                (Polynomial.taylor center
                  (P₀.map iota + Polynomial.C z * P₁.map iota)).coeff l.val := by
  obtain ⟨P₀, P₁, hP₀, hP₁, hsamplePair, hrecognize⟩ :=
    exists_graphLine_polynomials_of_sample domain f g sample hsample
  refine ⟨P₀, P₁, hP₀, hP₁, hsamplePair, ?_⟩
  intro z jet hS hhigh hcuts
  let φ : E[X] →ₐ[E] E := Polynomial.aeval z
  have hcenter : φ (Polynomial.C center) = center := by simp [φ]
  have hφ : φ.toRingHom = Polynomial.evalRingHom z := by
    ext a <;> simp [φ]
  have hdegree :
      (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom z) Q)
        K jet).degree < k := by
    simpa only [hcenter, hφ] using
      degree_rationalTaylorPolynomial_lt_of_symbolic_high_cuts_and_exponent φ
        (Polynomial.C center) Q K k τ hτ jet hS hhigh
  have hagree : ∀ i ∈ sample,
      (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom z) Q)
        K jet).eval (mappedDomain domain iota i) = iota (f i) + z * iota (g i) := by
    intro i hi
    have heval := (aeval_map_taylorAgreementEquationOver_eq_zero_iff_of_exponent φ
      (Polynomial.C center) Q K τ hτ jet hS (Polynomial.C (iota (domain i)))
      (Polynomial.C (iota (f i)) + Polynomial.X * Polynomial.C (iota (g i)))).mp
        (hcuts i hi)
    have heval' :
        (rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom z) Q)
          K jet).eval (mappedDomain domain iota i) = iota (f i) + iota (g i) * z := by
      simpa [hφ, φ, mappedDomain] using heval
    exact heval'.trans (by ring)
  have hpoly := hrecognize iota z _ hdegree hagree
  refine ⟨hpoly, ?_, ?_⟩
  · rw [← polynomialJet_affine_combination, ← hpoly,
      polynomialJet_rationalTaylorPolynomial center _ K hK]
  · intro l
    have hcoeff := aeval_map_commonTaylorNumeratorOver_reconstruction_of_exponent φ
      (Polynomial.C center) Q K τ hτ jet hS l
    simpa only [hcenter, hφ, hpoly] using hcoeff

/-- Exponent-aware prime-component recognition on a common sample.  All high cuts,
agreement cuts, and reconstruction identities retain the same sufficient exponent `τ`. -/
theorem exists_graphLine_pair_of_symbolic_prime_sample_of_exponent
    [IsAlgClosed E] (domain : Fin n ↪ F) (f g : Fin n → F)
    (sample : Finset (Fin n)) (hsample : sample.card = k)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (hK : r < K) (τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (P : Ideal (MvPolynomial (Option (Fin (r + 1))) E))
    (hP : P.IsPrime) (hs : symbolicSourceSeparant center Q ∉ P)
    (hd : 0 < (hilbertPolynomial P).natDegree)
    (hinit : symbolicSourceInitialEquation center Q ∈ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val → symbolicSourceNumerator center Q K l (τ := τ) ∈ P)
    (hcuts : ∀ i ∈ sample,
      symbolicSourceAgreement center Q K (iota (domain i)) (iota (f i)) (iota (g i)) (τ := τ) ∈ P) :
    ∃ P₀ P₁ : F[X], P₀.degree < k ∧ P₁.degree < k ∧
      (∀ i ∈ sample, P₀.eval (domain i) = f i ∧ P₁.eval (domain i) = g i) ∧
      (∀ x ∈ principalOpenZeroLocus P (symbolicSourceSeparant center Q),
        x = affineGraphPoint (polynomialJet (d := r) center (P₀.map iota))
          (polynomialJet (d := r) center (P₁.map iota)) (x none)) ∧
      (∀ p ∈ P,
        affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
          (polynomialJet (d := r) center (P₁.map iota)) p = 0) ∧
      affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
        (polynomialJet (d := r) center (P₁.map iota))
        (symbolicSourceInitialEquation center Q) = 0 ∧
      (∀ l : Fin K, k ≤ l.val →
        affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
          (polynomialJet (d := r) center (P₁.map iota))
          (symbolicSourceNumerator center Q K l (τ := τ)) = 0) ∧
      affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
        (polynomialJet (d := r) center (P₁.map iota)) (symbolicSourceSeparant center Q) ≠ 0 ∧
      ∀ l : Fin K,
        affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
          (polynomialJet (d := r) center (P₁.map iota))
          (symbolicSourceReconstructionError center Q K (P₀.map iota) (P₁.map iota) l
            (τ := τ)) = 0 := by
  obtain ⟨P₀, P₁, hP₀, hP₁, hsamplePair, hrecognize⟩ :=
    exists_graphLine_pair_of_symbolic_sample_of_exponent domain f g sample hsample iota
      center Q hK τ hτ
  have hpoint (x : Option (Fin (r + 1)) → E)
      (hx : x ∈ principalOpenZeroLocus P (symbolicSourceSeparant center Q)) :=
    hrecognize (x none) (fun j ↦ x (some j))
      (by simpa only [symbolicSourceSeparant, aeval_optionEquivRight_symm] using hx.2)
      (fun l hl ↦ by
        have hz := hx.1 _ (hhigh l hl)
        simpa only [symbolicSourceNumerator, aeval_optionEquivRight_symm] using hz)
      (fun i hi ↦ by
        have hz := hx.1 _ (hcuts i hi)
        simpa only [symbolicSourceAgreement, aeval_optionEquivRight_symm] using hz)
  have hgraph : ∀ x ∈ principalOpenZeroLocus P (symbolicSourceSeparant center Q),
      x = affineGraphPoint (polynomialJet (d := r) center (P₀.map iota))
        (polynomialJet (d := r) center (P₁.map iota)) (x none) := by
    intro x hx
    have hjet := (hpoint x hx).2.1
    funext j
    cases j with
    | none => rfl
    | some j => exact congrFun hjet j
  obtain ⟨hvanish, hsep⟩ := graphPullback_vanishes_of_principalOpen hP hs hd
    (polynomialJet (d := r) center (P₀.map iota))
    (polynomialJet (d := r) center (P₁.map iota)) hgraph
  refine ⟨P₀, P₁, hP₀, hP₁, hsamplePair, hgraph, hvanish, hvanish _ hinit,
    (fun l hl ↦ hvanish _ (hhigh l hl)), hsep, ?_⟩
  intro l
  have hinfinite : (principalOpenZeroLocus P (symbolicSourceSeparant center Q)).Infinite := by
    intro hfinite
    have hz := hilbertPolynomial_natDegree_zero_of_finite_principalOpen hP hs hfinite
    omega
  apply affineGraphPullback_eq_zero_of_infinite _ _ hinfinite hgraph
  intro x hx
  have hcoeff := (hpoint x hx).2.2 l
  have hlinear : (Polynomial.taylor center
      (P₀.map iota + Polynomial.C (x none) * P₁.map iota)).coeff l.val =
        (Polynomial.taylor center (P₀.map iota)).coeff l.val +
          x none * (Polynomial.taylor center (P₁.map iota)).coeff l.val := by
    rw [← Polynomial.smul_eq_C_mul, map_add, map_smul]
    simp only [Polynomial.coeff_add, Polynomial.coeff_smul, smul_eq_mul]
  simp only [symbolicSourceReconstructionError, map_sub, map_mul, map_pow, map_add,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply,
    symbolicSourceNumerator, symbolicSourceSeparant, aeval_optionEquivRight_symm]
  rw [hcoeff, hlinear, sub_self]


/-- Actual prime components supported on a common sample lie on a base-field pair graph.
Every polynomial in the component ideal restricts to zero and the restricted separant
is nonzero. The component hypotheses concern explicit symbolic cuts. -/
theorem exists_graphLine_pair_of_symbolic_prime_sample
    [IsAlgClosed E] (domain : Fin n ↪ F) (f g : Fin n → F)
    (sample : Finset (Fin n)) (hsample : sample.card = k)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (hK : r < K) (P : Ideal (MvPolynomial (Option (Fin (r + 1))) E))
    (hP : P.IsPrime) (hs : symbolicSourceSeparant center Q ∉ P)
    (hd : 0 < (hilbertPolynomial P).natDegree)
    (hinit : symbolicSourceInitialEquation center Q ∈ P)
    (hhigh : ∀ l : Fin K, k ≤ l.val → symbolicSourceNumerator center Q K l ∈ P)
    (hcuts : ∀ i ∈ sample,
      symbolicSourceAgreement center Q K (iota (domain i)) (iota (f i)) (iota (g i)) ∈ P) :
    ∃ P₀ P₁ : F[X], P₀.degree < k ∧ P₁.degree < k ∧
      (∀ i ∈ sample, P₀.eval (domain i) = f i ∧ P₁.eval (domain i) = g i) ∧
      (∀ x ∈ principalOpenZeroLocus P (symbolicSourceSeparant center Q),
        x = affineGraphPoint (polynomialJet (d := r) center (P₀.map iota))
          (polynomialJet (d := r) center (P₁.map iota)) (x none)) ∧
      (∀ p ∈ P,
        affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
          (polynomialJet (d := r) center (P₁.map iota)) p = 0) ∧
      affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
        (polynomialJet (d := r) center (P₁.map iota))
        (symbolicSourceInitialEquation center Q) = 0 ∧
      (∀ l : Fin K, k ≤ l.val →
        affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
          (polynomialJet (d := r) center (P₁.map iota))
          (symbolicSourceNumerator center Q K l) = 0) ∧
      affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
        (polynomialJet (d := r) center (P₁.map iota)) (symbolicSourceSeparant center Q) ≠ 0 ∧
      ∀ l : Fin K,
        affineGraphPullback (polynomialJet (d := r) center (P₀.map iota))
          (polynomialJet (d := r) center (P₁.map iota))
          (symbolicSourceReconstructionError center Q K (P₀.map iota) (P₁.map iota) l) = 0 := by
  obtain ⟨P₀, P₁, hP₀, hP₁, hsamplePair, hrecognize⟩ :=
    exists_graphLine_pair_of_symbolic_sample domain f g sample hsample iota center Q hK
  have hpoint (x : Option (Fin (r + 1)) → E)
      (hx : x ∈ principalOpenZeroLocus P (symbolicSourceSeparant center Q)) :=
    hrecognize (x none) (fun j ↦ x (some j))
      (by simpa only [symbolicSourceSeparant, aeval_optionEquivRight_symm] using hx.2)
      (fun l hl ↦ by
        have hz := hx.1 _ (hhigh l hl)
        simpa only [symbolicSourceNumerator, aeval_optionEquivRight_symm] using hz)
      (fun i hi ↦ by
        have hz := hx.1 _ (hcuts i hi)
        simpa only [symbolicSourceAgreement, aeval_optionEquivRight_symm] using hz)
  have hgraph : ∀ x ∈ principalOpenZeroLocus P (symbolicSourceSeparant center Q),
      x = affineGraphPoint (polynomialJet (d := r) center (P₀.map iota))
        (polynomialJet (d := r) center (P₁.map iota)) (x none) := by
    intro x hx
    have hjet := (hpoint x hx).2.1
    funext j
    cases j with
    | none => rfl
    | some j => exact congrFun hjet j
  obtain ⟨hvanish, hsep⟩ := graphPullback_vanishes_of_principalOpen hP hs hd
    (polynomialJet (d := r) center (P₀.map iota))
    (polynomialJet (d := r) center (P₁.map iota)) hgraph
  refine ⟨P₀, P₁, hP₀, hP₁, hsamplePair, hgraph, hvanish, hvanish _ hinit,
    (fun l hl ↦ hvanish _ (hhigh l hl)), hsep, ?_⟩
  intro l
  have hinfinite : (principalOpenZeroLocus P (symbolicSourceSeparant center Q)).Infinite := by
    intro hfinite
    have hz := hilbertPolynomial_natDegree_zero_of_finite_principalOpen hP hs hfinite
    omega
  apply affineGraphPullback_eq_zero_of_infinite _ _ hinfinite hgraph
  intro x hx
  have hcoeff := (hpoint x hx).2.2 l
  have hlinear : (Polynomial.taylor center
      (P₀.map iota + Polynomial.C (x none) * P₁.map iota)).coeff l.val =
        (Polynomial.taylor center (P₀.map iota)).coeff l.val +
          x none * (Polynomial.taylor center (P₁.map iota)).coeff l.val := by
    rw [← Polynomial.smul_eq_C_mul, map_add, map_smul]
    simp only [Polynomial.coeff_add, Polynomial.coeff_smul, smul_eq_mul]
  simp only [symbolicSourceReconstructionError, map_sub, map_mul, map_pow, map_add,
    MvPolynomial.aeval_C, MvPolynomial.aeval_X, Algebra.algebraMap_self, RingHom.id_apply,
    symbolicSourceNumerator, symbolicSourceSeparant, aeval_optionEquivRight_symm]
  rw [hcoeff, hlinear, sub_self]

end ReedSolomon
