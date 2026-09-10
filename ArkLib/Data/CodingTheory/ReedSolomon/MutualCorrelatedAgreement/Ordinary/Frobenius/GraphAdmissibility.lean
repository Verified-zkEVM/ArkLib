/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Frobenius.Recognition
/-!
# Admissible Frobenius graphs

A retained pair satisfies actual polynomial identities along its initial-value graph.
These identities include a common original-size sample, so every regular specialization
reconstructs the same base-field pair.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n k K : ℕ}

/-- Literal source, sparse, and sampled agreement identities defining a retained pair. -/
structure IsAdmissibleFrobeniusPair
    (domain : Fin n ↪ F) (f g : Fin n → F) (ι : F →+* E)
    (roots : Fin n → E) (center : E) (Q : DifferentialPolynomial E[X] 0)
    (K k τ s : ℕ) (F₀ G₀ : F[X]) : Prop where
  degree_left : F₀.degree < ↑k
  degree_right : G₀.degree < ↑k
  initial : polynomialGraphPullback
    (frobeniusInitialGraph center s (F₀.map ι) (G₀.map ι))
    (symbolicSourceInitialEquation center Q) = 0
  regular : polynomialGraphPullback
    (frobeniusInitialGraph center s (F₀.map ι) (G₀.map ι))
    (symbolicSourceSeparant center Q) ≠ 0
  sparse : ∀ l : Fin K, ¬s ∣ l.val → polynomialGraphPullback
    (frobeniusInitialGraph center s (F₀.map ι) (G₀.map ι))
    (symbolicSourceNumerator center Q K l (τ := τ)) = 0
  sample : ∃ sample : Finset (Fin n), sample.card = k ∧
    (∀ i ∈ sample, F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i) ∧
    ∀ i ∈ sample, polynomialGraphPullback
      (frobeniusInitialGraph center s (F₀.map ι) (G₀.map ι))
      (symbolicSourceFrobeniusAgreement center Q K τ s
        (roots i) (ι (f i)) (ι (g i))) = 0

/-- Every recognized prime component supplies the full admissibility identities. -/
theorem exists_admissibleFrobeniusPair_of_symbolic_prime_sample [IsAlgClosed E]
    (domain : Fin n ↪ F) (f g : Fin n → F) (sample : Finset (Fin n))
    (hsample : sample.card = k) (ι : F →+* E) (p e : ℕ) [ExpChar E p]
    (roots : Fin n → E) (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (center : E) (Q : DifferentialPolynomial E[X] 0)
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (τ : ℕ)
    (hτ : TaylorExponentSufficient 0 K τ)
    (I : Ideal (MvPolynomial (Option (Fin 1)) E)) (hI : I.IsPrime)
    (hs : symbolicSourceSeparant center Q ∉ I)
    (hi : symbolicSourceInitialEquation center Q ∈ I)
    (hd : 0 < (hilbertPolynomial I).natDegree)
    (hsparse : ∀ l : Fin K, ¬p ^ e ∣ l.val →
      symbolicSourceNumerator center Q K l (τ := τ) ∈ I)
    (hcuts : ∀ i ∈ sample, symbolicSourceFrobeniusAgreement center Q K τ (p ^ e)
      (roots i) (ι (f i)) (ι (g i)) ∈ I) :
    ∃ F₀ G₀ : F[X],
      IsAdmissibleFrobeniusPair domain f g ι roots center Q K k τ (p ^ e) F₀ G₀ ∧
      ∀ x ∈ principalOpenZeroLocus I (symbolicSourceSeparant center Q),
        x = polynomialGraphPoint
          (frobeniusInitialGraph center (p ^ e) (F₀.map ι) (G₀.map ι)) (x none) := by
  obtain ⟨F₀, G₀, hF, hG, hagree, hgraph, hvanish, hsep⟩ :=
    exists_frobeniusGraph_of_symbolic_prime_sample domain f g sample hsample ι p e roots
      hroots center Q hK hKk τ hτ I hI hs hd hsparse hcuts
  exact ⟨F₀, G₀, ⟨hF, hG, hvanish _ hi, hsep,
    fun l hl ↦ hvanish _ (hsparse l hl),
    sample, hsample, hagree, fun i hi ↦ hvanish _ (hcuts i hi)⟩, hgraph⟩

/-- At every regular challenge, the actual Taylor reconstruction equals the pulled
polynomial of the retained base-field pair. -/
theorem IsAdmissibleFrobeniusPair.specialize
    {domain : Fin n ↪ F} {f g : Fin n → F} {ι : F →+* E}
    {roots : Fin n → E} {center : E} {Q : DifferentialPolynomial E[X] 0}
    {τ p e : ℕ} [ExpChar E p] {F₀ G₀ : F[X]}
    (hP : IsAdmissibleFrobeniusPair domain f g ι roots center Q K k τ (p ^ e) F₀ G₀)
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (w : E)
    (hw : (polynomialGraphPullback
      (frobeniusInitialGraph center (p ^ e) (F₀.map ι) (G₀.map ι))
      (symbolicSourceSeparant center Q)).eval w ≠ 0) :
    rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom w) Q) K
      (fun j ↦ (frobeniusInitialGraph center (p ^ e) (F₀.map ι) (G₀.map ι) j).eval w) =
      expand E (p ^ e) (F₀.map ι + Polynomial.C (w ^ (p ^ e)) * G₀.map ι) := by
  obtain ⟨sample, hcard, hagree, hcuts⟩ := hP.sample
  obtain ⟨F₁, G₁, hF₁, hG₁, hagree₁, hrecognize⟩ :=
    exists_frobeniusGraphLine_of_symbolic_sample domain f g sample hcard
      ι p e roots hroots center Q hK hKk τ hτ
  have hF : F₁ = F₀ := Polynomial.eq_of_degrees_lt_of_eval_index_eq sample
    domain.injective.injOn (by simpa only [hcard] using hF₁)
    (by simpa only [hcard] using hP.degree_left)
    (fun i hi ↦ (hagree₁ i hi).1.trans (hagree i hi).1.symm)
  have hG : G₁ = G₀ := Polynomial.eq_of_degrees_lt_of_eval_index_eq sample
    domain.injective.injOn (by simpa only [hcard] using hG₁)
    (by simpa only [hcard] using hP.degree_right)
    (fun i hi ↦ (hagree₁ i hi).2.trans (hagree i hi).2.symm)
  subst F₁
  subst G₁
  apply (hrecognize w _ ?_ ?_ ?_).1
  · simpa only [eval_polynomialGraphPullback, symbolicSourceSeparant,
      aeval_optionEquivRight_symm, polynomialGraphPoint, Option.elim_none,
      Option.elim_some] using hw
  · intro l hl
    have hz := congrArg (fun R : E[X] ↦ R.eval w) (hP.sparse l hl)
    simpa only [eval_polynomialGraphPullback, symbolicSourceNumerator,
      aeval_optionEquivRight_symm, polynomialGraphPoint, Option.elim_none,
      Option.elim_some, Polynomial.eval_zero] using hz
  · intro i hi
    have hz := congrArg (fun R : E[X] ↦ R.eval w) (hcuts i hi)
    simpa only [eval_polynomialGraphPullback, symbolicSourceFrobeniusAgreement,
      aeval_optionEquivRight_symm, polynomialGraphPoint, Option.elim_none,
      Option.elim_some, Polynomial.eval_zero] using hz

/-- Actual reconstruction makes the initial graph injective on admissible base-field pairs.
This uses infinitely many regular challenges, not injectivity of evaluation at the center. -/
theorem IsAdmissibleFrobeniusPair.eq_of_initialGraph_eq [Infinite E]
    {domain : Fin n ↪ F} {f g : Fin n → F} {ι : F →+* E}
    {roots : Fin n → E} {center : E} {Q : DifferentialPolynomial E[X] 0}
    {τ p e : ℕ} [ExpChar E p] {F₀ G₀ F₁ G₁ : F[X]}
    (hP : IsAdmissibleFrobeniusPair domain f g ι roots center Q K k τ (p ^ e) F₀ G₀)
    (hR : IsAdmissibleFrobeniusPair domain f g ι roots center Q K k τ (p ^ e) F₁ G₁)
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hgraph : frobeniusInitialGraph center (p ^ e) (F₀.map ι) (G₀.map ι) =
      frobeniusInitialGraph center (p ^ e) (F₁.map ι) (G₁.map ι)) :
    F₀ = F₁ ∧ G₀ = G₁ := by
  let sep := polynomialGraphPullback
    (frobeniusInitialGraph center (p ^ e) (F₀.map ι) (G₀.map ι))
    (symbolicSourceSeparant center Q)
  have hinfinite : Set.Infinite {w : E | sep.eval w ≠ 0} := by
    exact (Set.infinite_univ.sdiff
      (Polynomial.finite_setOfPred_isRoot hP.regular)).mono (fun _ hw ↦ hw.2)
  have hs : 0 < p ^ e := pow_pos (expChar_pos E p) e
  have heq (w : E) (hw : sep.eval w ≠ 0) :
      F₀.map ι + Polynomial.C (w ^ (p ^ e)) * G₀.map ι =
      F₁.map ι + Polynomial.C (w ^ (p ^ e)) * G₁.map ι := by
    apply Polynomial.expand_injective hs
    rw [← hP.specialize hroots hK hKk hτ w hw]
    have hw' : (polynomialGraphPullback
        (frobeniusInitialGraph center (p ^ e) (F₁.map ι) (G₁.map ι))
        (symbolicSourceSeparant center Q)).eval w ≠ 0 := by
      simpa only [sep, hgraph] using hw
    rw [hgraph, hR.specialize hroots hK hKk hτ w hw']
  have hcoeff (l : ℕ) :
      Polynomial.C ((F₀.map ι).coeff l) + Polynomial.X ^ (p ^ e) *
          Polynomial.C ((G₀.map ι).coeff l) =
      Polynomial.C ((F₁.map ι).coeff l) + Polynomial.X ^ (p ^ e) *
          Polynomial.C ((G₁.map ι).coeff l) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hinfinite.mono
    intro w hw
    have h := congrArg (fun R : E[X] ↦ R.coeff l) (heq w hw)
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.coeff_add,
      Polynomial.coeff_C_mul, Set.mem_ofPred_eq] using h
  constructor
  · ext l
    apply ι.injective
    have h := congrArg (fun R : E[X] ↦ R.coeff 0) (hcoeff l)
    simpa [Polynomial.coeff_X_pow_mul, Polynomial.coeff_C,
      ne_of_gt hs, (ne_of_gt hs).symm, (expChar_pos E p).ne',
      Polynomial.coeff_map] using h
  · ext l
    apply ι.injective
    have h := congrArg (fun R : E[X] ↦ R.coeff (p ^ e)) (hcoeff l)
    simpa [Polynomial.coeff_X_pow_mul, Polynomial.coeff_C,
      ne_of_gt hs, (ne_of_gt hs).symm, (expChar_pos E p).ne',
      Polynomial.coeff_map] using h

end ReedSolomon
