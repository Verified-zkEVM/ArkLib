/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.PowerAgreement
public import ArkLib.Data.Polynomial.Differential.TaylorChart
public import ArkLib.Data.Polynomial.Differential.TaylorChartAlgebra
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.PrincipalOpenParametrization

/-!
# Polynomial graphs of power-batched Taylor components

A common sample determines a tuple of base-field polynomials. Regular Taylor-chart points
satisfying the high cuts and sample agreement equations lie on the graph of its power-batched
initial jet. A positive-dimensional prime component with those cuts therefore has all its ideal
equations vanish on that graph, while its separant stays nonzero there.

## Main statements

* `ReedSolomon.exists_powerBatchedTaylorGraph_of_sample`: pointwise recognition from Taylor cuts.
* `ReedSolomon.exists_polynomialGraph_of_primeTaylorComponent`: recognition of a prime component
  and its graph identities.

## References

* [DKT26]
-/

@[expose] public section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential

noncomputable section

variable {F E : Type*} [Field F] [Field E] {n k K r ℓ : ℕ}

/-- The polynomial-valued initial-jet graph of a tuple of message polynomials. -/
def powerBatchedJetGraph (center : E) (P : Fin (ℓ + 1) → E[X]) :
    Fin (r + 1) → E[X] :=
  fun j ↦ powerBatchedCoordinate (fun t ↦ polynomialJet (d := r) center (P t) j)

/-- The initial Hasse jet of a power-batched polynomial is evaluation of its graph at the
challenge. -/
theorem polynomialJet_powerBatched (center z : E) (P : Fin (ℓ + 1) → E[X]) :
    polynomialJet (d := r) center (powerBatchedPolynomial P z) =
      fun j ↦ (powerBatchedJetGraph (r := r) center P j).eval z := by
  funext j
  rw [powerBatchedJetGraph, powerBatchedCoordinate_eval]
  simp only [polynomialJet, powerBatchedPolynomial, map_sum, map_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- The separant polynomial in the joint challenge and initial-jet coordinates. -/
def powerBatchedTaylorSeparant (center : E) (Q : DifferentialPolynomial E[X] r) :
    MvPolynomial (Fin (r + 1)) (Polynomial E) :=
  initialJetSeparant (Polynomial.C center) Q

/-- A high Taylor numerator in the joint challenge and initial-jet coordinates. -/
def powerBatchedTaylorNumerator (center : E) (Q : DifferentialPolynomial E[X] r)
    (K τ : ℕ) (l : Fin K) : MvPolynomial (Fin (r + 1)) (Polynomial E) :=
  commonTaylorNumeratorOver E (Polynomial.C center) Q τ l.val

/-- The Taylor-chart agreement equation for the power-batched received value at `alpha`. -/
def powerBatchedTaylorAgreement (center : E) (Q : DifferentialPolynomial E[X] r)
    (K τ : ℕ) (alpha : E) (w : Fin (ℓ + 1) → E) :
    MvPolynomial (Fin (r + 1)) (Polynomial E) :=
  taylorAgreementEquationOver E (Polynomial.C center) Q K τ (Polynomial.C alpha)
    (powerBatchedCoordinate w)

/-- A polynomial map from the challenge line to the joint challenge and initial-jet coordinates.
The challenge is the `none` coordinate, and each `some j` coordinate is the `j`-th polynomial
of the power-batched jet graph. -/
def powerBatchedJetGraphMap (center : E) (P : Fin (ℓ + 1) → E[X]) :
    Option (Fin (r + 1)) → E[X] :=
  fun i ↦ i.elim Polynomial.X (powerBatchedJetGraph (r := r) center P)

/-- The point on the power-batched jet graph at challenge `z`. -/
def powerBatchedJetGraphPoint (center z : E) (P : Fin (ℓ + 1) → E[X]) :
    Option (Fin (r + 1)) → E :=
  fun i ↦ (powerBatchedJetGraphMap (r := r) center P i).eval z

/-- Restriction of a joint polynomial to the power-batched jet graph. -/
def powerBatchedJetGraphPullback (center : E) (P : Fin (ℓ + 1) → E[X])
    (p : MvPolynomial (Option (Fin (r + 1))) E) : E[X] :=
  MvPolynomial.aeval (powerBatchedJetGraphMap (r := r) center P) p

/-- Flatten a Taylor chart into joint challenge and initial-jet coordinates. -/
def flattenTaylorChart (p : MvPolynomial (Fin (r + 1)) (Polynomial E)) :
    MvPolynomial (Option (Fin (r + 1))) E :=
  (optionEquivRight E _).symm p

/-- The separant cut in joint challenge and initial-jet coordinates. -/
def powerBatchedTaylorSeparantCut (center : E) (Q : DifferentialPolynomial E[X] r) :
    MvPolynomial (Option (Fin (r + 1))) E :=
  flattenTaylorChart (powerBatchedTaylorSeparant (r := r) center Q)

/-- A high Taylor numerator cut in joint challenge and initial-jet coordinates. -/
def powerBatchedTaylorNumeratorCut (center : E) (Q : DifferentialPolynomial E[X] r)
    (K τ : ℕ) (l : Fin K) : MvPolynomial (Option (Fin (r + 1))) E :=
  flattenTaylorChart (powerBatchedTaylorNumerator (r := r) center Q K τ l)

/-- The power-batched agreement cut in joint challenge and initial-jet coordinates. -/
def powerBatchedTaylorAgreementCut (center : E) (Q : DifferentialPolynomial E[X] r)
    (K τ : ℕ) (alpha : E) (w : Fin (ℓ + 1) → E) :
    MvPolynomial (Option (Fin (r + 1))) E :=
  flattenTaylorChart (powerBatchedTaylorAgreement (r := r) center Q K τ alpha w)

/-- A common sample recognizes every regular Taylor-chart point as the same power-batched
polynomial graph. The agreement cuts and high cuts use one sufficient exponent. -/
theorem exists_powerBatchedTaylorGraph_of_sample (domain : Fin n ↪ F)
    (w : Fin (ℓ + 1) → Fin n → F) (sample : Finset (Fin n)) (hsample : sample.card = k)
    (φ : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r) (hK : r < K)
    (τ : ℕ) (hτ : TaylorExponentSufficient r K τ) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
      (∀ i ∈ sample, ∀ t, (P t).eval (domain i) = w t i) ∧
      ∀ (z : E) (jet : Fin (r + 1) → E),
        MvPolynomial.aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
          (powerBatchedTaylorSeparant (r := r) center Q)) ≠ 0 →
        (∀ l : Fin K, k ≤ l.val →
          MvPolynomial.aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
            (powerBatchedTaylorNumerator (r := r) center Q K τ l)) = 0) →
        (∀ i ∈ sample,
          MvPolynomial.aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
            (powerBatchedTaylorAgreement (r := r) center Q K τ (φ (domain i))
              (fun t ↦ φ (w t i)))) = 0) →
        rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom z) Q) K jet =
            powerBatchedPolynomial (fun t ↦ (P t).map φ) z ∧
        jet = (fun j ↦
          (powerBatchedJetGraph (r := r) center (fun t ↦ (P t).map φ) j).eval z) ∧
        ∀ l : Fin K,
          MvPolynomial.aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
            (powerBatchedTaylorNumerator (r := r) center Q K τ l)) =
          MvPolynomial.aeval jet (MvPolynomial.map (Polynomial.evalRingHom z)
            (powerBatchedTaylorSeparant (r := r) center Q)) ^ τ *
            (Polynomial.taylor center
              (powerBatchedPolynomial (fun t ↦ (P t).map φ) z)).coeff l.val := by
  obtain ⟨P, hP, hs, hrecognize⟩ :=
    exists_polynomialGraph_of_sample domain w (k := k) sample hsample
  refine ⟨P, hP, hs, ?_⟩
  intro z jet hS hhigh hcuts
  let ψ : E[X] →ₐ[E] E := Polynomial.aeval z
  have hcenter : ψ (Polynomial.C center) = center := by simp [ψ]
  have hcenter' : ψ.toRingHom (Polynomial.C center) = center := hcenter
  have hψ : ψ.toRingHom = Polynomial.evalRingHom z := by ext a <;> simp [ψ]
  have hS' : MvPolynomial.aeval jet
      (initialJetSeparant center (MvPolynomial.map ψ.toRingHom Q)) ≠ 0 := by
    simpa only [powerBatchedTaylorSeparant, ← hψ, map_initialJetSeparant, hcenter'] using hS
  have hhigh' : ∀ l : Fin K, k ≤ l.val →
      MvPolynomial.aeval jet
        (commonTaylorNumerator center (MvPolynomial.map ψ.toRingHom Q) τ l.val) = 0 := by
    intro l hl
    have hcommon : commonTaylorNumeratorOver E center (MvPolynomial.map ψ.toRingHom Q)
        τ l.val = commonTaylorNumerator center (MvPolynomial.map ψ.toRingHom Q) τ l.val := by
      simp [commonTaylorNumeratorOver, commonTaylorNumerator, rationalTaylorNumeratorOver_eq]
    have hnum : MvPolynomial.map (Polynomial.evalRingHom z)
        (powerBatchedTaylorNumerator (r := r) center Q K τ l) =
          commonTaylorNumerator center (MvPolynomial.map ψ.toRingHom Q) τ l.val := by
      change MvPolynomial.map (Polynomial.evalRingHom z)
        (commonTaylorNumeratorOver E (Polynomial.C center) Q τ l.val) = _
      calc
        _ = commonTaylorNumeratorOver E (ψ (Polynomial.C center))
            (MvPolynomial.map ψ.toRingHom Q) τ l.val := by
          rw [← hψ]
          exact map_commonTaylorNumeratorOver (F := E) ψ (Polynomial.C center) Q τ l.val
        _ = _ := by rw [hcenter]; exact hcommon
    rw [← hnum]
    exact hhigh l hl
  have hdegree :
      (rationalTaylorPolynomial center (MvPolynomial.map ψ.toRingHom Q) K jet).degree < k := by
    exact degree_rationalTaylorPolynomial_lt center (MvPolynomial.map ψ.toRingHom Q) hτ k jet hS'
      (fun l hl hlK ↦ hhigh' ⟨l, hlK⟩ hl)
  have hagree : ∀ i ∈ sample,
      (rationalTaylorPolynomial center (MvPolynomial.map ψ.toRingHom Q) K jet).eval
          (φ (domain i)) = ∑ t, z ^ t.val * φ (w t i) := by
    intro i hi
    have hmap' : MvPolynomial.map (Polynomial.evalRingHom z)
        (powerBatchedTaylorAgreement (r := r) center Q K τ (φ (domain i))
          (fun t ↦ φ (w t i))) =
        taylorAgreementEquation center (MvPolynomial.map ψ.toRingHom Q) K τ
          (φ (domain i)) (∑ t, z ^ t.val * φ (w t i)) := by
      calc
        _ = MvPolynomial.map ψ.toRingHom
            (powerBatchedTaylorAgreement (r := r) center Q K τ (φ (domain i))
              (fun t ↦ φ (w t i))) := by rw [hψ]
        _ = taylorAgreementEquationOver E center (MvPolynomial.map ψ.toRingHom Q) K τ
            (φ (domain i)) (∑ t, z ^ t.val * φ (w t i)) := by
          rw [powerBatchedTaylorAgreement, map_taylorAgreementEquationOver (F := E) ψ]
          simp [ψ, hcenter, powerBatchedCoordinate_eval]
        _ = _ := taylorAgreementEquationOver_eq center (MvPolynomial.map ψ.toRingHom Q) K τ
          (φ (domain i)) (∑ t, z ^ t.val * φ (w t i))
    have hcut : MvPolynomial.aeval jet
        (taylorAgreementEquation center (MvPolynomial.map ψ.toRingHom Q) K τ
          (φ (domain i)) (∑ t, z ^ t.val * φ (w t i))) = 0 := by
      rw [← hmap']
      exact hcuts i hi
    exact (taylorAgreementEquation_eq_zero_iff center (MvPolynomial.map ψ.toRingHom Q)
      hτ jet hS' (φ (domain i)) _).mp hcut
  have hpoly := hrecognize φ z _ hdegree hagree
  refine ⟨hpoly, ?_, ?_⟩
  · rw [← polynomialJet_powerBatched, ← hpoly,
      polynomialJet_rationalTaylorPolynomial center _ hK]
  · intro l
    have hcommon : commonTaylorNumeratorOver E center (MvPolynomial.map ψ.toRingHom Q)
        τ l.val = commonTaylorNumerator center (MvPolynomial.map ψ.toRingHom Q) τ l.val := by
      simp [commonTaylorNumeratorOver, commonTaylorNumerator, rationalTaylorNumeratorOver_eq]
    have hnum : MvPolynomial.map (Polynomial.evalRingHom z)
        (powerBatchedTaylorNumerator (r := r) center Q K τ l) =
          commonTaylorNumerator center (MvPolynomial.map ψ.toRingHom Q) τ l.val := by
      change MvPolynomial.map (Polynomial.evalRingHom z)
        (commonTaylorNumeratorOver E (Polynomial.C center) Q τ l.val) = _
      calc
        _ = commonTaylorNumeratorOver E (ψ (Polynomial.C center))
            (MvPolynomial.map ψ.toRingHom Q) τ l.val := by
          rw [← hψ]
          exact map_commonTaylorNumeratorOver (F := E) ψ (Polynomial.C center) Q τ l.val
        _ = _ := by rw [hcenter]; exact hcommon
    have hsep : MvPolynomial.map (Polynomial.evalRingHom z)
        (powerBatchedTaylorSeparant (r := r) center Q) =
          initialJetSeparant center (MvPolynomial.map ψ.toRingHom Q) := by
      change MvPolynomial.map (Polynomial.evalRingHom z)
        (initialJetSeparant (Polynomial.C center) Q) = _
      calc
        _ = MvPolynomial.map ψ.toRingHom
            (initialJetSeparant (Polynomial.C center) Q) := by rw [hψ]
        _ = initialJetSeparant (ψ.toRingHom (Polynomial.C center))
            (MvPolynomial.map ψ.toRingHom Q) :=
          map_initialJetSeparant ψ.toRingHom (Polynomial.C center) Q
        _ = _ := by rw [hcenter']
    have hcoeffTaylor :=
      coeff_taylor_rationalTaylorPolynomial center (MvPolynomial.map ψ.toRingHom Q) K jet l.val
    rw [ite_eq_left l.isLt] at hcoeffTaylor
    rw [hnum, hsep, aeval_commonTaylorNumerator center _ jet (hτ l) hS', ← hpoly,
      ← hcoeffTaylor]

/-- The regular points of an ideal's zero locus where a specified polynomial is nonzero. -/
def regularTaylorComponentLocus {E σ : Type*} [Field E]
    (I : Ideal (MvPolynomial σ E)) (s : MvPolynomial σ E) : Set (σ → E) :=
  {x | x ∈ zeroLocus E I ∧ MvPolynomial.aeval x s ≠ 0}

/-- A positive-dimensional prime component containing the high Taylor cuts and sample agreement
cuts lies on the graph of one base-field message tuple. Its ideal vanishes on that graph and the
separant remains nonzero after restriction. -/
theorem exists_polynomialGraph_of_primeTaylorComponent [IsAlgClosed E]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F)
    (sample : Finset (Fin n)) (hsample : sample.card = k) (φ : F →+* E) (center : E)
    (Q : DifferentialPolynomial E[X] r) (hK : r < K) (τ : ℕ)
    (hτ : TaylorExponentSufficient r K τ)
    (I : Ideal (MvPolynomial (Option (Fin (r + 1))) E)) [hI : I.IsPrime]
    (hsep : powerBatchedTaylorSeparantCut (r := r) center Q ∉ I)
    (hdim : 0 < (affineHilbertPolynomial I).natDegree)
    (hhigh : ∀ l : Fin K, k ≤ l.val →
      powerBatchedTaylorNumeratorCut (r := r) center Q K τ l ∈ I)
    (hcuts : ∀ i ∈ sample,
      powerBatchedTaylorAgreementCut (r := r) center Q K τ (φ (domain i))
        (fun t ↦ φ (w t i)) ∈ I) :
    ∃ P : Fin (ℓ + 1) → F[X], (∀ t, (P t).degree < k) ∧
      (∀ i ∈ sample, ∀ t, (P t).eval (domain i) = w t i) ∧
      (∀ x ∈ regularTaylorComponentLocus I
          (powerBatchedTaylorSeparantCut (r := r) center Q),
        x = powerBatchedJetGraphPoint (r := r) center (x none)
          (fun t ↦ (P t).map φ)) ∧
      (∀ x ∈ regularTaylorComponentLocus I
          (powerBatchedTaylorSeparantCut (r := r) center Q),
        rationalTaylorPolynomial center (MvPolynomial.map (Polynomial.evalRingHom (x none)) Q)
          K (fun j ↦ x (some j)) = powerBatchedPolynomial (fun t ↦ (P t).map φ) (x none)) ∧
      (∀ p ∈ I, powerBatchedJetGraphPullback (r := r) center (fun t ↦ (P t).map φ) p = 0) ∧
      powerBatchedJetGraphPullback (r := r) center (fun t ↦ (P t).map φ)
        (powerBatchedTaylorSeparantCut (r := r) center Q) ≠ 0 := by
  obtain ⟨P, hP, hsampleP, hrecognize⟩ :=
    exists_powerBatchedTaylorGraph_of_sample domain w sample hsample φ center Q hK τ hτ
  let graph := powerBatchedJetGraphMap (r := r) center (fun t ↦ (P t).map φ)
  have hpoint (x : Option (Fin (r + 1)) → E)
      (hx : x ∈ regularTaylorComponentLocus I
        (powerBatchedTaylorSeparantCut (r := r) center Q)) :=
    hrecognize (x none) (fun j ↦ x (some j))
      (by
        simpa only [regularTaylorComponentLocus, powerBatchedTaylorSeparantCut,
          flattenTaylorChart, MvPolynomial.aeval_optionEquivRight_symm] using hx.2)
      (fun l hl ↦ by
        have hz := hx.1 _ (hhigh l hl)
        simpa only [powerBatchedTaylorNumeratorCut, flattenTaylorChart,
          MvPolynomial.aeval_optionEquivRight_symm] using hz)
      (fun i hi ↦ by
        have hz := hx.1 _ (hcuts i hi)
        simpa only [powerBatchedTaylorAgreementCut, flattenTaylorChart,
          MvPolynomial.aeval_optionEquivRight_symm] using hz)
  have hgraph : ∀ x ∈ regularTaylorComponentLocus I
      (powerBatchedTaylorSeparantCut (r := r) center Q),
      x = powerBatchedJetGraphPoint (r := r) center (x none) (fun t ↦ (P t).map φ) := by
    intro x hx
    have hjet := (hpoint x hx).2.1
    funext i
    cases i with
    | none =>
      change x none = Polynomial.X.eval (x none)
      simp
    | some j => exact congrFun hjet j
  have hregular : IsLeftRegular (Ideal.Quotient.mk I
      (powerBatchedTaylorSeparantCut (r := r) center Q)) := by
    intro x y hxy
    exact mul_left_cancel₀
      (fun h ↦ hsep (Ideal.Quotient.eq_zero_iff_mem.mp h)) hxy
  have hrange : ∀ x : Option (Fin (r + 1)) → E,
      x ∈ zeroLocus E I →
      MvPolynomial.aeval x (powerBatchedTaylorSeparantCut (r := r) center Q) ≠ 0 →
      ∃ z : E, x = fun i ↦ (graph i).eval z := by
    intro x hx hxs
    have hgraphx := hgraph x ⟨hx, hxs⟩
    change x = fun i ↦ (powerBatchedJetGraphMap (r := r) center
      (fun t ↦ (P t).map φ) i).eval (x none) at hgraphx
    exact ⟨x none, by
      exact hgraphx⟩
  have hvanish : ∀ p ∈ I,
      MvPolynomial.aeval graph p = 0 := by
    intro p hp
    apply MvPolynomial.aeval_eq_zero_of_principalOpen_subset_range hregular hdim graph hrange
    intro x hx hxs
    have hpker : p ∈ RingHom.ker (MvPolynomial.aeval x) :=
      (MvPolynomial.mem_zeroLocus_iff_le_ker_aeval.mp hx) hp
    exact RingHom.mem_ker.mp hpker
  have hopenInfinite :
      (regularTaylorComponentLocus I
        (powerBatchedTaylorSeparantCut (r := r) center Q)).Infinite := by
    intro hfinite
    have hzero := (finite_principalOpen_iff_natDegree_affineHilbertPolynomial_eq_zero
      hregular).mp (by simpa [regularTaylorComponentLocus] using hfinite)
    omega
  obtain ⟨x, hx⟩ := hopenInfinite.nonempty
  obtain ⟨z, hparam⟩ := hrange x hx.1 hx.2
  have heval : (MvPolynomial.aeval graph
      (powerBatchedTaylorSeparantCut (r := r) center Q)).eval z =
        MvPolynomial.aeval x (powerBatchedTaylorSeparantCut (r := r) center Q) := by
    rw [MvPolynomial.polynomial_eval_aeval, ← hparam, MvPolynomial.aeval_eq_eval]
  refine ⟨P, hP, hsampleP, hgraph, ?_, hvanish, ?_⟩
  · intro x hx
    exact (hpoint x hx).1
  · intro hzero
    apply hx.2
    change MvPolynomial.aeval graph (powerBatchedTaylorSeparantCut (r := r) center Q) = 0
      at hzero
    calc
      MvPolynomial.aeval x (powerBatchedTaylorSeparantCut (r := r) center Q) =
          (MvPolynomial.aeval graph
            (powerBatchedTaylorSeparantCut (r := r) center Q)).eval z := heval.symm
      _ = 0 := by rw [hzero]; simp

end

end ReedSolomon
