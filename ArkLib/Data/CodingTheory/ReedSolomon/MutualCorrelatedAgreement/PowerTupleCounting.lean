/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PowerBatchedComponentRecognition
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.TupleSpecialization
public import ArkLib.ToMathlib.MvPolynomial.OptionRoots

/-!
# Counting admissible Frobenius power tuples

An admissible tuple lies on the initial equation's polynomial graph. Sparse reconstruction makes
the tuple unique for each graph, so the generic polynomial graph root count bounds every finite
family of admissible tuples.

## Main statements

* `ReedSolomon.IsAdmissibleFrobeniusPowerTuple`: the initial, sparse, and sampled conditions for a
  tuple on a Frobenius power graph.
* `ReedSolomon.IsAdmissibleFrobeniusPowerTuple.specialize`: reconstruction at every regular
  challenge.
* `ReedSolomon.IsAdmissibleFrobeniusPowerTuple.eq_of_initialGraph_eq`: uniqueness from the initial
  graph.
* `ReedSolomon.admissibleFrobeniusPowerTuples_card_le_degreeOf`: the finite-family root-degree
  bound.

## References

* [DKT26]
-/

@[expose] public section

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential

variable {F E α : Type*} [Field F] [Field E] {k K ℓ : ℕ}

/-- The source, sparse, and sampled equations that make a power tuple admissible. -/
structure IsAdmissibleFrobeniusPowerTuple
    (domain : α ↪ F) (values : Fin (ℓ + 1) → α → F) (ι : F →+* E)
    (roots : α → E) (center : E) (Q : DifferentialPolynomial E[X] 0)
    (K k τ s : ℕ) (P : Fin (ℓ + 1) → F[X]) : Prop where
  /-- Every constituent has degree below the sample size. -/
  degree : ∀ t, (P t).degree < k
  /-- The initial equation vanishes on the tuple's polynomial graph. -/
  initial : aeval (frobeniusPowerGraphMap center s (fun t ↦ (P t).map ι))
    (jointInitialJetEquation center Q) = 0
  /-- The initial separant is nonzero on the tuple's polynomial graph. -/
  regular : aeval (frobeniusPowerGraphMap center s (fun t ↦ (P t).map ι))
    (jointInitialJetSeparant center Q) ≠ 0
  /-- Every sparse common Taylor numerator vanishes on the tuple's polynomial graph. -/
  sparse : ∀ l : Fin K, ¬s ∣ l.val →
    aeval (frobeniusPowerGraphMap center s (fun t ↦ (P t).map ι))
      (jointCommonTaylorNumerator center Q τ l) = 0
  /-- A sample of size `k` satisfies the interpolation and agreement equations. -/
  sample : ∃ sample : Finset α, sample.card = k ∧
    (∀ i ∈ sample, ∀ t, (P t).eval (domain i) = values t i) ∧
    ∀ i ∈ sample, aeval (frobeniusPowerGraphMap center s (fun t ↦ (P t).map ι))
      (jointTaylorAgreementEquation center Q K τ (Polynomial.C (roots i))
        (frobeniusPowerCoordinate s (fun t ↦ ι (values t i)))) = 0

/-- Every regular specialization reconstructs the tuple's power-batched polynomial. -/
theorem IsAdmissibleFrobeniusPowerTuple.specialize
    {domain : α ↪ F} {values : Fin (ℓ + 1) → α → F} {ι : F →+* E}
    {roots : α → E} {center : E} {Q : DifferentialPolynomial E[X] 0}
    {τ p e : ℕ} [ExpChar E p] {P : Fin (ℓ + 1) → F[X]}
    (hP : IsAdmissibleFrobeniusPowerTuple
      domain values ι roots center Q K k τ (p ^ e) P)
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (z : E)
    (hz : (aeval (frobeniusPowerGraphMap center (p ^ e) (fun t ↦ (P t).map ι))
      (jointInitialJetSeparant center Q)).eval z ≠ 0) :
    rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom z) Q) K
      (fun j ↦ (frobeniusPowerGraphMap center (p ^ e) (fun t ↦ (P t).map ι)
        (some j)).eval z) =
      Polynomial.expand E (p ^ e)
        (powerBatchedPolynomial (fun t ↦ (P t).map ι) (z ^ (p ^ e))) := by
  obtain ⟨sample, hcard, hsample, hcuts⟩ := hP.sample
  obtain ⟨R, hRdegree, hRsample, hrecognize⟩ :=
    exists_frobeniusPowerGraph_of_symbolic_sample domain values sample hcard
      ι p e roots (fun i hi ↦ hroots i) center Q hK hKk τ hτ
  have hRP : R = P := polynomialTuple_eq_of_common_samples
    domain values R P sample hcard.ge hRdegree hP.degree hRsample hsample
  subst R
  let graph := frobeniusPowerGraphMap center (p ^ e) (fun t ↦ (P t).map ι)
  let point : Option (Fin 1) → E := fun i ↦ (graph i).eval z
  let jet : Fin 1 → E := fun j ↦ point (some j)
  have hpointNone : point none = z := by
    simp [point, graph, frobeniusPowerGraphMap]
  let φ : E[X] →ₐ[E] E := Polynomial.aeval z
  let Qz : DifferentialPolynomial E 0 := MvPolynomial.map φ.toRingHom Q
  have hcenter : φ (Polynomial.C center) = center := by simp [φ]
  have hcenterRing : φ.toRingHom (Polynomial.C center) = center := hcenter
  have hφ : φ.toRingHom = Polynomial.evalRingHom z := by
    ext a <;> simp [φ, Polynomial.evalRingHom]
  have hS_eq : MvPolynomial.aeval point (jointInitialJetSeparant center Q) =
      MvPolynomial.aeval jet (initialJetSeparant center Qz) := by
    simpa only [jet, Qz, φ, hpointNone] using
      aeval_jointInitialJetSeparant center Q point
  have hEval := MvPolynomial.polynomial_eval_aeval graph z (jointInitialJetSeparant center Q)
  rw [hEval] at hz
  have hS_point : MvPolynomial.aeval point (jointInitialJetSeparant center Q) ≠ 0 := by
    simpa only [MvPolynomial.aeval_eq_eval, Polynomial.eval_zero] using hz
  have hS_field : MvPolynomial.aeval jet (initialJetSeparant center Qz) ≠ 0 := by
    rw [← hS_eq]
    exact hS_point
  have hS : MvPolynomial.aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
      (initialJetSeparant (Polynomial.C center) Q)) ≠ 0 := by
    rw [← hφ, map_initialJetSeparant]
    rw [hcenterRing]
    simpa only [Qz] using hS_field
  have hsparse : ∀ l : Fin K, ¬p ^ e ∣ l.val →
      MvPolynomial.aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
        (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q τ l.val)) = 0 := by
    intro l hl
    have hz' := congrArg (fun f : E[X] ↦ f.eval z) (hP.sparse l hl)
    have hEval := MvPolynomial.polynomial_eval_aeval graph z
      (jointCommonTaylorNumerator center Q τ l)
    rw [hEval] at hz'
    have hz'' : MvPolynomial.aeval point (jointCommonTaylorNumerator center Q τ l) = 0 := by
      simpa only [MvPolynomial.aeval_eq_eval, Polynomial.eval_zero] using hz'
    have hnum_eq : MvPolynomial.aeval point (jointCommonTaylorNumerator center Q τ l) =
        MvPolynomial.aeval jet (commonTaylorNumerator center Qz τ l.val) := by
      simpa only [jet, Qz, φ, hpointNone] using
        aeval_jointCommonTaylorNumerator center Q τ l point
    rw [hnum_eq] at hz''
    rw [← hφ, map_commonTaylorNumeratorOver_eq, hcenter]
    simpa only [Qz] using hz''
  have hcuts' : ∀ i ∈ sample,
      MvPolynomial.aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
        (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
          (Polynomial.C (roots i))
          (frobeniusPowerCoordinate (p ^ e) (fun t ↦ ι (values t i)))
          (τ := τ))) = 0 := by
    intro i hi
    have hz' := congrArg (fun f : E[X] ↦ f.eval z) (hcuts i hi)
    have hEval := MvPolynomial.polynomial_eval_aeval graph z
      (jointTaylorAgreementEquation center Q K τ (Polynomial.C (roots i))
        (frobeniusPowerCoordinate (p ^ e) (fun t ↦ ι (values t i))))
    rw [hEval] at hz'
    have hz'' : MvPolynomial.aeval point (jointTaylorAgreementEquation center Q K τ
        (Polynomial.C (roots i))
        (frobeniusPowerCoordinate (p ^ e) (fun t ↦ ι (values t i)))) = 0 := by
      simpa only [MvPolynomial.aeval_eq_eval, Polynomial.eval_zero] using hz'
    have hagree_eq : MvPolynomial.aeval point (jointTaylorAgreementEquation center Q K τ
        (Polynomial.C (roots i))
        (frobeniusPowerCoordinate (p ^ e) (fun t ↦ ι (values t i)))) =
        MvPolynomial.aeval jet (taylorAgreementEquation center Qz K τ (roots i)
          (Polynomial.eval z (frobeniusPowerCoordinate (p ^ e)
            (fun t ↦ ι (values t i))))) := by
      simpa only [jet, Qz, φ, hpointNone, Polynomial.eval_C] using
        aeval_jointTaylorAgreementEquation center Q K τ (Polynomial.C (roots i))
          (frobeniusPowerCoordinate (p ^ e) (fun t ↦ ι (values t i))) point
    rw [hagree_eq] at hz''
    have hmap : MvPolynomial.map (Polynomial.evalRingHom z)
        (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
          (Polynomial.C (roots i))
          (frobeniusPowerCoordinate (p ^ e) (fun t ↦ ι (values t i))) (τ := τ)) =
        taylorAgreementEquation center Qz K τ (roots i)
          (Polynomial.eval z (frobeniusPowerCoordinate (p ^ e)
            (fun t ↦ ι (values t i)))) := by
      rw [← hφ, map_taylorAgreementEquationOver_eq (τ := τ)]
      simp [φ, hcenter, Qz]
    rw [hmap]
    exact hz''
  simpa only [jet, point, graph] using (hrecognize z jet hS hsparse hcuts').1

/-- Equality of initial graphs determines admissible power tuples. -/
theorem IsAdmissibleFrobeniusPowerTuple.eq_of_initialGraph_eq [Infinite E]
    {domain : α ↪ F} {values : Fin (ℓ + 1) → α → F} {ι : F →+* E}
    {roots : α → E} {center : E} {Q : DifferentialPolynomial E[X] 0}
    {τ p e : ℕ} [ExpChar E p] {P R : Fin (ℓ + 1) → F[X]}
    (hP : IsAdmissibleFrobeniusPowerTuple
      domain values ι roots center Q K k τ (p ^ e) P)
    (hR : IsAdmissibleFrobeniusPowerTuple
      domain values ι roots center Q K k τ (p ^ e) R)
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hgraph : frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (P t).map ι) =
      frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (R t).map ι)) : P = R := by
  let graphP := frobeniusPowerGraphMap center (p ^ e) (fun t ↦ (P t).map ι)
  let graphR := frobeniusPowerGraphMap center (p ^ e) (fun t ↦ (R t).map ι)
  let sep := aeval graphP (jointInitialJetSeparant center Q)
  have hinfinite : {z : E | sep.eval z ≠ 0}.Infinite :=
    (Set.infinite_univ.sdiff (Polynomial.finite_setOfPred_isRoot hP.regular)).mono
      (fun _ hz ↦ hz.2)
  have hs : 0 < p ^ e := pow_pos (expChar_pos E p) e
  have hgraphs : graphP = graphR := by
    funext i
    cases i with
    | none => rfl
    | some i =>
      have hi : i = 0 := Subsingleton.elim _ _
      subst i
      exact congrFun hgraph 0
  have heq (z : E) (hz : sep.eval z ≠ 0) :
      powerBatchedPolynomial (fun t ↦ (P t).map ι) (z ^ (p ^ e)) =
        powerBatchedPolynomial (fun t ↦ (R t).map ι) (z ^ (p ^ e)) := by
    apply Polynomial.expand_injective hs
    let jetP : Fin 1 → E := fun j ↦ (graphP (some j)).eval z
    let jetR : Fin 1 → E := fun j ↦ (graphR (some j)).eval z
    let T : (Fin 1 → E) → E[X] := fun jet ↦
      rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom z) Q) K jet
    have hjet : jetP = jetR := by
      funext j
      exact congrArg (fun f : E[X] ↦ f.eval z) (congrFun hgraphs (some j))
    have hT := congrArg T hjet
    have hPspec : T jetP =
        Polynomial.expand E (p ^ e)
          (powerBatchedPolynomial (fun t ↦ (P t).map ι) (z ^ (p ^ e))) := by
      simpa only [T, jetP, graphP] using hP.specialize hroots hK hKk hτ z
        (by simpa [sep, graphP] using hz)
    have hzR : (aeval graphR (jointInitialJetSeparant center Q)).eval z ≠ 0 := by
      simpa [sep, graphP, graphR, hgraphs] using hz
    have hRspec : T jetR =
        Polynomial.expand E (p ^ e)
          (powerBatchedPolynomial (fun t ↦ (R t).map ι) (z ^ (p ^ e))) := by
      simpa only [T, jetR, graphR] using hR.specialize hroots hK hKk hτ z hzR
    have hExpanded :
        Polynomial.expand E (p ^ e)
          (powerBatchedPolynomial (fun t ↦ (P t).map ι) (z ^ (p ^ e))) =
        Polynomial.expand E (p ^ e)
          (powerBatchedPolynomial (fun t ↦ (R t).map ι) (z ^ (p ^ e))) :=
      hPspec.symm.trans (hT.trans hRspec)
    exact hExpanded
  funext t
  apply Polynomial.map_injective ι ι.injective
  ext l
  let left :=
    frobeniusPowerCoordinate (p ^ e) (fun j ↦ ((P j).map ι).coeff l)
  let right :=
    frobeniusPowerCoordinate (p ^ e) (fun j ↦ ((R j).map ι).coeff l)
  have hcoordinates : left = right := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply hinfinite.mono
    intro z hz
    change left.eval z = right.eval z
    have hcoeff := congrArg (fun S : E[X] ↦ S.coeff l) (heq z hz)
    simpa only [left, right, frobeniusPowerCoordinate_eval, powerBatchedPolynomial,
      Polynomial.finsetSum_coeff, Polynomial.coeff_smul, smul_eq_mul, pow_mul] using hcoeff
  have hbase :
      powerBatchedCoordinate (fun j ↦ ((P j).map ι).coeff l) =
        powerBatchedCoordinate (fun j ↦ ((R j).map ι).coeff l) := by
    apply Polynomial.expand_injective hs
    simpa only [left, right, frobeniusPowerCoordinate] using hcoordinates
  have hcoefficient := congrArg (fun S : E[X] ↦ S.coeff t) hbase
  simpa only [powerBatchedCoordinate_coeff, Polynomial.coeff_map] using hcoefficient

/-- The graph-coordinate degree of the nonzero initial equation bounds every finite family of
admissible Frobenius power tuples. -/
theorem admissibleFrobeniusPowerTuples_card_le_degreeOf [Infinite E]
    (domain : α ↪ F) (values : Fin (ℓ + 1) → α → F) (ι : F →+* E)
    (roots : α → E) (center : E) (Q : DifferentialPolynomial E[X] 0)
    (p e τ : ℕ) [ExpChar E p]
    (hroots : ∀ i, roots i ^ (p ^ e) = ι (domain i))
    (hK : 0 < K) (hKk : K ≤ p ^ e * k) (hτ : TaylorExponentSufficient 0 K τ)
    (hinit : jointInitialJetEquation center Q ≠ 0)
    (tuples : Finset (Fin (ℓ + 1) → F[X]))
    (htuples : ∀ P ∈ tuples,
      IsAdmissibleFrobeniusPowerTuple
        domain values ι roots center Q K k τ (p ^ e) P) :
    tuples.card ≤ (jointInitialJetEquation center Q).degreeOf (some 0) := by
  classical
  let graph : (Fin (ℓ + 1) → F[X]) → E[X] := fun P ↦
    frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (P t).map ι) 0
  have hinj : Set.InjOn graph (tuples : Set (Fin (ℓ + 1) → F[X])) := by
    intro P hP R hR heq
    have hgraphs :
        frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (P t).map ι) =
          frobeniusPowerInitialGraph center (p ^ e) (fun t ↦ (R t).map ι) := by
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst j
      exact heq
    exact (htuples P hP).eq_of_initialGraph_eq (htuples R hR)
      hroots hK hKk hτ hgraphs
  have hcount := MvPolynomial.card_le_degreeOf_some_of_aeval_eq_zero
    (R := E) (ι := Fin 1) (g := jointInitialJetEquation center Q) hinit
    (tuples.image graph) (by
      intro q hq
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.mp hq
      have hgraph :
          frobeniusPowerGraphMap center (p ^ e) (fun t ↦ (P t).map ι) =
            fun o ↦ o.elim Polynomial.X fun _ ↦ graph P := by
        funext o
        cases o with
        | none => rfl
        | some j =>
          have hj : j = 0 := Subsingleton.elim _ _
          subst j
          rfl
      rw [← hgraph]
      exact (htuples P hP).initial)
  rwa [Finset.card_image_of_injOn hinj] at hcount

end ReedSolomon
