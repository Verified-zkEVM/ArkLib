/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.PolynomialCurve.Graph
/-!
# Admissible Frobenius power graphs

An admissible tuple carries the literal source, sparse, and sampled agreement identities on its
pulled initial-value graph.  Sparse reconstruction identifies every regular specialization with
the same original-degree base-field tuple.
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n k K ℓ : ℕ}

/-- Literal source, sparse, and sampled agreement identities for a retained power tuple. -/
structure IsAdmissibleFrobeniusPowerTuple
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F) (ι : F →+* E)
    (roots : Fin n → E) (center : E) (Q : DifferentialPolynomial E[X] 0)
    (K k τ s : ℕ) (P : Fin (ℓ + 1) → F[X]) : Prop where
  degree : ∀ t, (P t).degree < k
  initial : polynomialGraphPullback
    (frobeniusPowerInitialGraph center s (fun t ↦ (P t).map ι))
    (symbolicSourceInitialEquation center Q) = 0
  regular : polynomialGraphPullback
    (frobeniusPowerInitialGraph center s (fun t ↦ (P t).map ι))
    (symbolicSourceSeparant center Q) ≠ 0
  sparse : ∀ l : Fin K, ¬s ∣ l.val → polynomialGraphPullback
    (frobeniusPowerInitialGraph center s (fun t ↦ (P t).map ι))
    (symbolicSourceNumerator center Q K l (τ := τ)) = 0
  sample : ∃ sample : Finset (Fin n), sample.card = k ∧
    (∀ i ∈ sample, ∀ t, (P t).eval (domain i) = values t i) ∧
    ∀ i ∈ sample, polynomialGraphPullback
      (frobeniusPowerInitialGraph center s (fun t ↦ (P t).map ι))
      (symbolicSourceFrobeniusPowerAgreement center Q K τ s
        (roots i) (fun t ↦ ι (values t i))) = 0

/-- Every recognized regular prime component supplies an admissible original-degree tuple. -/
theorem exists_admissibleFrobeniusPowerTuple_of_symbolic_prime_sample [IsAlgClosed E]
    (domain : Fin n ↪ F) (values : Fin (ℓ + 1) → Fin n → F)
    (sample : Finset (Fin n)) (hsample : sample.card = k)
    (ι : F →+* E) (p e : ℕ) [ExpChar E p]
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
    (hcuts : ∀ i ∈ sample,
      symbolicSourceFrobeniusPowerAgreement center Q K τ (p ^ e)
        (roots i) (fun t ↦ ι (values t i)) ∈ I) :
    ∃ P : Fin (ℓ + 1) → F[X],
      IsAdmissibleFrobeniusPowerTuple domain values ι roots center Q K k τ (p ^ e) P ∧
      ∀ x ∈ principalOpenZeroLocus I (symbolicSourceSeparant center Q),
        x = polynomialGraphPoint
          (frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (P t).map ι)) (x none) := by
  obtain ⟨P, hdegree, hagree, hgraph, hvanish, hsep⟩ :=
    exists_frobeniusPowerGraph_of_symbolic_prime_sample domain values sample hsample
      ι p e roots hroots center Q hK hKk τ hτ I hI hs hd hsparse hcuts
  exact ⟨P, ⟨hdegree, hvanish _ hi, hsep,
    fun l hl ↦ hvanish _ (hsparse l hl),
    sample, hsample, hagree, fun i hi ↦ hvanish _ (hcuts i hi)⟩, hgraph⟩

/-- Every regular specialization reconstructs the pulled polynomial of the retained tuple. -/
theorem IsAdmissibleFrobeniusPowerTuple.specialize
    {domain : Fin n ↪ F} {values : Fin (ℓ + 1) → Fin n → F} {ι : F →+* E}
    {roots : Fin n → E} {center : E} {Q : DifferentialPolynomial E[X] 0}
    {τ p e : ℕ} [ExpChar E p] {P : Fin (ℓ + 1) → F[X]}
    (hP : IsAdmissibleFrobeniusPowerTuple
      domain values ι roots center Q K k τ (p ^ e) P)
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (z : E)
    (hz : (polynomialGraphPullback
      (frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (P t).map ι))
      (symbolicSourceSeparant center Q)).eval z ≠ 0) :
    rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom z) Q) K
      (fun j ↦ (frobeniusPowerInitialGraph center (p ^ e)
        (fun t ↦ (P t).map ι) j).eval z) =
      expand E (p ^ e)
        (powerBatchedPolynomial (fun t ↦ (P t).map ι) (z ^ (p ^ e))) := by
  obtain ⟨sample, hcard, hagree, hcuts⟩ := hP.sample
  obtain ⟨R, hRdegree, hagreeR, hrecognize⟩ :=
    exists_frobeniusPowerGraph_of_symbolic_sample domain values sample hcard
      ι p e roots hroots center Q hK hKk τ hτ
  have hRP : R = P := polynomialTuple_eq_of_common_samples
    domain values R P k sample hcard hRdegree hP.degree hagreeR hagree
  subst R
  apply (hrecognize z _ ?_ ?_ ?_).1
  · simpa only [eval_polynomialGraphPullback, symbolicSourceSeparant,
      aeval_optionEquivRight_symm, polynomialGraphPoint, Option.elim_none,
      Option.elim_some] using hz
  · intro l hl
    have hzero := congrArg (fun R : E[X] ↦ R.eval z) (hP.sparse l hl)
    simpa only [eval_polynomialGraphPullback, symbolicSourceNumerator,
      aeval_optionEquivRight_symm, polynomialGraphPoint, Option.elim_none,
      Option.elim_some, Polynomial.eval_zero] using hzero
  · intro i hi
    have hzero := congrArg (fun R : E[X] ↦ R.eval z) (hcuts i hi)
    simpa only [eval_polynomialGraphPullback, symbolicSourceFrobeniusPowerAgreement,
      aeval_optionEquivRight_symm, polynomialGraphPoint, Option.elim_none,
      Option.elim_some, Polynomial.eval_zero] using hzero

/-- Equality of initial graphs determines admissible tuples.  The proof specializes on the
infinite regular locus, contracts the Frobenius power, and compares every batching coefficient. -/
theorem IsAdmissibleFrobeniusPowerTuple.eq_of_initialGraph_eq [Infinite E]
    {domain : Fin n ↪ F} {values : Fin (ℓ + 1) → Fin n → F} {ι : F →+* E}
    {roots : Fin n → E} {center : E} {Q : DifferentialPolynomial E[X] 0}
    {τ p e : ℕ} [ExpChar E p] {P R : Fin (ℓ + 1) → F[X]}
    (hP : IsAdmissibleFrobeniusPowerTuple
      domain values ι roots center Q K k τ (p ^ e) P)
    (hR : IsAdmissibleFrobeniusPowerTuple
      domain values ι roots center Q K k τ (p ^ e) R)
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hgraph : frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (P t).map ι) =
      frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (R t).map ι)) : P = R := by
  let sep := polynomialGraphPullback
    (frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (P t).map ι))
    (symbolicSourceSeparant center Q)
  have hinfinite : Set.Infinite {z : E | sep.eval z ≠ 0} :=
    (Set.infinite_univ.sdiff
      (Polynomial.finite_setOfPred_isRoot hP.regular)).mono (fun _ hz ↦ hz.2)
  have hs : 0 < p ^ e := pow_pos (expChar_pos E p) e
  have heq (z : E) (hz : sep.eval z ≠ 0) :
      powerBatchedPolynomial (fun t ↦ (P t).map ι) (z ^ (p ^ e)) =
        powerBatchedPolynomial (fun t ↦ (R t).map ι) (z ^ (p ^ e)) := by
    apply Polynomial.expand_injective hs
    rw [← hP.specialize hroots hK hKk hτ z hz]
    have hzR : (polynomialGraphPullback
        (frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (R t).map ι))
        (symbolicSourceSeparant center Q)).eval z ≠ 0 := by
      simpa only [sep, hgraph] using hz
    rw [hgraph, hR.specialize hroots hK hKk hτ z hzR]
  funext t
  apply Polynomial.map_injective ι ι.injective
  ext l
  let left := frobeniusPowerCoordinate (p ^ e) (fun j ↦ ((P j).map ι).coeff l)
  let right := frobeniusPowerCoordinate (p ^ e) (fun j ↦ ((R j).map ι).coeff l)
  have hcoordinates : left = right := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hinfinite.mono
    intro z hz
    change left.eval z = right.eval z
    have hcoeff := congrArg (fun S : E[X] ↦ S.coeff l) (heq z hz)
    simpa only [left, right, frobeniusPowerCoordinate_eval, powerBatchedPolynomial,
      Polynomial.finsetSum_coeff, Polynomial.coeff_smul, smul_eq_mul, pow_mul] using hcoeff
  have hcoefficient :=
    congrArg (fun S : E[X] ↦ S.coeff (p ^ e * t.val)) hcoordinates
  have hmul (j : Fin (ℓ + 1)) : p ^ e * t.val = p ^ e * j.val ↔ t = j := by
    constructor
    · intro h
      apply Fin.ext
      exact Nat.eq_of_mul_eq_mul_left hs h
    · rintro rfl
      rfl
  simpa [left, right, frobeniusPowerCoordinate, Polynomial.finsetSum_coeff,
    Polynomial.coeff_monomial, hmul, Fin.val_inj, (expChar_pos E p).ne'] using hcoefficient

end ReedSolomon
