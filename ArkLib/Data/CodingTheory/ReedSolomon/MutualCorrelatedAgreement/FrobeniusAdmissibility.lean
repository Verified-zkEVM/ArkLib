/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FrobeniusComponentRecognition
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.PrincipalOpenParametrization
/-!
# Admissible Frobenius graph pairs

A retained pair satisfies the initial, sparse, and sampled agreement equations along its
Frobenius graph. Every regular specialization reconstructs the same base-field pair.

## Main statements

* `ReedSolomon.IsAdmissibleFrobeniusPair`: the polynomial identities and sample attached to a
  Frobenius graph pair.
* `ReedSolomon.exists_admissibleFrobeniusPair_of_symbolic_prime_sample`: admissible graph
  extraction from a positive-dimensional prime component.
* `ReedSolomon.IsAdmissibleFrobeniusPair.specialize` and
  `ReedSolomon.IsAdmissibleFrobeniusPair.eq_of_initialGraph_eq`: reconstruction and uniqueness.

## References

* [DKT26]
-/

@[expose] public section

open Polynomial MvPolynomial PolynomialDifferential

namespace ReedSolomon

noncomputable section

variable {F E ι : Type*} [Field F] [Field E] {k K : ℕ}

private theorem eval_aeval_frobeniusGraph (graph : Option (Fin 1) → E[X]) (w : E)
    (hgraph : graph none = Polynomial.X) (q : MvPolynomial (Option (Fin 1)) E) :
    (aeval graph q).eval w =
      aeval (fun i ↦ (graph (some i)).eval w)
        (map (Polynomial.evalRingHom w) (optionEquivRight E (Fin 1) q)) := by
  rw [MvPolynomial.polynomial_eval_aeval]
  let point : Option (Fin 1) → E := fun i ↦ (graph i).eval w
  have hpoint : point none = w := by simp [point, hgraph]
  have hmap : (Polynomial.aeval (point none)).toRingHom = Polynomial.evalRingHom w := by
    rw [hpoint]
    ext a <;> simp [Polynomial.evalRingHom]
  calc
    MvPolynomial.eval point q = aeval point q := by simp only [MvPolynomial.aeval_eq_eval]
    _ = aeval (fun j ↦ point (some j))
        (map (Polynomial.aeval (point none)).toRingHom (optionEquivRight E (Fin 1) q)) :=
          (aeval_map_optionEquivRight (R := E) point q).symm
    _ = _ := by rw [hmap]

/-- The initial, sparse, and sampled agreement identities along a Frobenius graph. -/
structure IsAdmissibleFrobeniusPair
    (domain : ι ↪ F) (f g : ι → F) (iota : F →+* E) (roots : ι → E)
    (center : E) (Q : DifferentialPolynomial E[X] 0)
    (K k τ s : ℕ) (F₀ G₀ : F[X]) : Prop where
  /-- The left retained polynomial has degree below the sample size. -/
  degree_left : F₀.degree < ↑k
  /-- The right retained polynomial has degree below the sample size. -/
  degree_right : G₀.degree < ↑k
  /-- The initial Taylor equation vanishes on the Frobenius graph. -/
  initial : aeval (frobeniusInitialGraph center s (F₀.map iota) (G₀.map iota))
    (jointInitialJetEquation center Q) = 0
  /-- The initial Taylor separant is nonzero on the Frobenius graph. -/
  regular : aeval (frobeniusInitialGraph center s (F₀.map iota) (G₀.map iota))
    (jointInitialJetSeparant center Q) ≠ 0
  /-- Every sparse common Taylor numerator vanishes on the Frobenius graph. -/
  sparse : ∀ l : Fin K, ¬s ∣ l.val →
    aeval (frobeniusInitialGraph center s (F₀.map iota) (G₀.map iota))
      (jointCommonTaylorNumerator center Q τ l) = 0
  /-- A sample of size `k` satisfies the root, interpolation, and agreement conditions. -/
  sample : ∃ sample : Finset ι, sample.card = k ∧ ∀ i ∈ sample,
    roots i ^ s = iota (domain i) ∧
    F₀.eval (domain i) = f i ∧ G₀.eval (domain i) = g i ∧
    aeval (frobeniusInitialGraph center s (F₀.map iota) (G₀.map iota))
      (jointTaylorAgreementEquation center Q K τ (Polynomial.C (roots i))
        (Polynomial.C (iota (f i)) + Polynomial.X ^ s * Polynomial.C (iota (g i)))) = 0

/-- A regular challenge reconstructs the polynomial pulled back from the retained pair. -/
theorem IsAdmissibleFrobeniusPair.specialize
    {domain : ι ↪ F} {f g : ι → F} {iota : F →+* E} {roots : ι → E}
    {center : E} {Q : DifferentialPolynomial E[X] 0} {τ p e : ℕ} [ExpChar E p]
    {F₀ G₀ : F[X]}
    (hP : IsAdmissibleFrobeniusPair domain f g iota roots center Q K k τ (p ^ e) F₀ G₀)
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (w : E)
    (hw : (aeval (frobeniusInitialGraph center (p ^ e) (F₀.map iota) (G₀.map iota))
      (jointInitialJetSeparant center Q)).eval w ≠ 0) :
    rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom w) Q) K
      (fun j ↦ (frobeniusInitialGraph center (p ^ e) (F₀.map iota) (G₀.map iota)
        (some j)).eval w) =
      expand E (p ^ e) (F₀.map iota + Polynomial.C (w ^ (p ^ e)) * G₀.map iota) := by
  obtain ⟨sample, hcard, hsample⟩ := hP.sample
  obtain ⟨F₁, G₁, hF₁, hG₁, hagree₁, hrecognize⟩ :=
    exists_frobeniusGraphLine_of_symbolic_sample domain f g sample hcard iota p e roots
      (fun i hi ↦ (hsample i hi).1) center Q hK hKk τ hτ
  have hF : F₁ = F₀ := Polynomial.eq_of_degrees_lt_of_eval_index_eq sample
    domain.injective.injOn (by simpa only [hcard] using hF₁)
    (by simpa only [hcard] using hP.degree_left)
    (fun i hi ↦ (hagree₁ i hi).1.trans (hsample i hi).2.1.symm)
  have hG : G₁ = G₀ := Polynomial.eq_of_degrees_lt_of_eval_index_eq sample
    domain.injective.injOn (by simpa only [hcard] using hG₁)
    (by simpa only [hcard] using hP.degree_right)
    (fun i hi ↦ (hagree₁ i hi).2.trans (hsample i hi).2.2.1.symm)
  subst F₁
  subst G₁
  have hgraph :
      frobeniusInitialGraph center (p ^ e) (F₀.map iota) (G₀.map iota) none =
        Polynomial.X := by
    simp [frobeniusInitialGraph]
  apply (hrecognize w _ ?_ ?_ ?_).1
  · rw [eval_aeval_frobeniusGraph _ w hgraph] at hw
    simpa only [jointInitialJetSeparant, AlgEquiv.apply_symm_apply] using hw
  · intro l hl
    have hz := congrArg (fun R : E[X] ↦ R.eval w) (hP.sparse l hl)
    rw [eval_aeval_frobeniusGraph _ w hgraph] at hz
    simpa only [jointCommonTaylorNumerator, AlgEquiv.apply_symm_apply,
      Polynomial.eval_zero] using hz
  · intro i hi
    have hz := congrArg (fun R : E[X] ↦ R.eval w) (hsample i hi).2.2.2
    rw [eval_aeval_frobeniusGraph _ w hgraph] at hz
    simpa only [jointTaylorAgreementEquation, AlgEquiv.apply_symm_apply,
      map_taylorAgreementEquationOver_eq,
      Polynomial.eval_C, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_zero] using hz

/-- A positive-dimensional prime component supplies a pair satisfying all admissibility
identities, and its regular locus is parametrized by that pair's Frobenius graph. -/
theorem exists_admissibleFrobeniusPair_of_symbolic_prime_sample [IsAlgClosed E]
    (domain : ι ↪ F) (f g : ι → F) (sample : Finset ι) (hsample : sample.card = k)
    (iota : F →+* E) (p e : ℕ) [ExpChar E p] (roots : ι → E)
    (hroots : ∀ i ∈ sample, roots i ^ (p ^ e) = iota (domain i))
    (center : E) (Q : DifferentialPolynomial E[X] 0)
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (τ : ℕ)
    (hτ : TaylorExponentSufficient 0 K τ)
    (I : Ideal (MvPolynomial (Option (Fin 1)) E)) [I.IsPrime]
    (hs : jointInitialJetSeparant center Q ∉ I)
    (hi : jointInitialJetEquation center Q ∈ I)
    (hd : 0 < (affineHilbertPolynomial I).natDegree)
    (hsparse : ∀ l : Fin K, ¬p ^ e ∣ l.val →
      jointCommonTaylorNumerator center Q τ l ∈ I)
    (hcuts : ∀ i ∈ sample,
      jointTaylorAgreementEquation center Q K τ (Polynomial.C (roots i))
        (Polynomial.C (iota (f i)) + Polynomial.X ^ (p ^ e) * Polynomial.C (iota (g i))) ∈ I) :
    ∃ F₀ G₀ : F[X],
      IsAdmissibleFrobeniusPair domain f g iota roots center Q K k τ (p ^ e) F₀ G₀ ∧
      ∀ x ∈ {x | x ∈ zeroLocus E I ∧ aeval x (jointInitialJetSeparant center Q) ≠ 0},
        x = fun i ↦
          (frobeniusInitialGraph center (p ^ e)
            (F₀.map iota) (G₀.map iota) i).eval (x none) := by
  obtain ⟨F₀, G₀, hF, hG, hagree, hgraph, hvanish, hsep⟩ :=
    exists_frobeniusGraph_of_symbolic_prime_sample domain f g sample hsample iota p e roots
      hroots center Q hK hKk τ hτ I hs hd hsparse hcuts
  refine ⟨F₀, G₀, ⟨hF, hG, hvanish _ hi, hsep,
    fun l hl ↦ hvanish _ (hsparse l hl), sample, hsample, ?_⟩, hgraph⟩
  intro i hi
  exact ⟨hroots i hi, (hagree i hi).1, (hagree i hi).2, hvanish _ (hcuts i hi)⟩

/-- Two admissible pairs with the same initial graph are equal. -/
theorem IsAdmissibleFrobeniusPair.eq_of_initialGraph_eq [Infinite E]
    {domain : ι ↪ F} {f g : ι → F} {iota : F →+* E}
    {roots : ι → E} {center : E} {Q : DifferentialPolynomial E[X] 0}
    {τ p e : ℕ} [ExpChar E p] {F₀ G₀ F₁ G₁ : F[X]}
    (hP : IsAdmissibleFrobeniusPair domain f g iota roots center Q K k τ (p ^ e) F₀ G₀)
    (hR : IsAdmissibleFrobeniusPair domain f g iota roots center Q K k τ (p ^ e) F₁ G₁)
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hgraph : frobeniusInitialGraph center (p ^ e) (F₀.map iota) (G₀.map iota) =
      frobeniusInitialGraph center (p ^ e) (F₁.map iota) (G₁.map iota)) :
    F₀ = F₁ ∧ G₀ = G₁ := by
  let sep := aeval
    (frobeniusInitialGraph center (p ^ e) (F₀.map iota) (G₀.map iota))
    (jointInitialJetSeparant center Q)
  have hinfinite : Set.Infinite {w : E | sep.eval w ≠ 0} := by
    exact (Set.infinite_univ.sdiff (Polynomial.finite_setOfPred_isRoot hP.regular)).mono
      (fun _ hw ↦ hw.2)
  have hs : 0 < p ^ e := pow_pos (expChar_pos E p) e
  have heq (w : E) (hw : sep.eval w ≠ 0) :
      F₀.map iota + Polynomial.C (w ^ (p ^ e)) * G₀.map iota =
        F₁.map iota + Polynomial.C (w ^ (p ^ e)) * G₁.map iota := by
    apply Polynomial.expand_injective hs
    rw [← hP.specialize hK hKk hτ w hw]
    have hw' :
        (aeval (frobeniusInitialGraph center (p ^ e) (F₁.map iota) (G₁.map iota))
          (jointInitialJetSeparant center Q)).eval w ≠ 0 := by
      simpa only [sep, hgraph] using hw
    rw [hgraph, hR.specialize hK hKk hτ w hw']
  have hcoeff (l : ℕ) :
      Polynomial.C ((F₀.map iota).coeff l) + Polynomial.X ^ (p ^ e) *
          Polynomial.C ((G₀.map iota).coeff l) =
        Polynomial.C ((F₁.map iota).coeff l) + Polynomial.X ^ (p ^ e) *
          Polynomial.C ((G₁.map iota).coeff l) := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hinfinite.mono
    intro w hw
    have h := congrArg (fun R : E[X] ↦ R.coeff l) (heq w hw)
    simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.coeff_add,
      Polynomial.coeff_C_mul, Set.mem_ofPred_eq] using h
  constructor
  · ext l
    apply iota.injective
    have h := congrArg (fun R : E[X] ↦ R.coeff 0) (hcoeff l)
    simpa [Polynomial.coeff_X_pow_mul, Polynomial.coeff_C, ne_of_gt hs, (ne_of_gt hs).symm,
      (expChar_pos E p).ne', Polynomial.coeff_map] using h
  · ext l
    apply iota.injective
    have h := congrArg (fun R : E[X] ↦ R.coeff (p ^ e)) (hcoeff l)
    simpa [Polynomial.coeff_X_pow_mul, Polynomial.coeff_C, ne_of_gt hs, (ne_of_gt hs).symm,
      (expChar_pos E p).ne', Polynomial.coeff_map] using h

end

end ReedSolomon
