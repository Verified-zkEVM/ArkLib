/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Equations.Equation
public import
ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.Factors.SharpFactorSolutions
public import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.EquationDescent
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
/-!
# Sharp exceptional bound for arbitrary ordinary equations

When the original root degree is at most `mu ≤ D`, every separable Frobenius pullback factor
has degree at most `D`.  Thus the exact sharp factor comparison applies factor by factor, and
the distinct-factor degree and height sums recover the sharp charge of the original equation.
-/

@[expose] public section

open scoped BigOperators

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative

noncomputable section

open Classical in
/-- Combine content and distinct positive-root-degree factors using the sharp charge. -/
theorem exists_exceptional_ordinaryFactorAssembly_sharp
    {F W V R sigma : Type*} [Field F] [CommRing R] [IsDomain R]
    (Q : MvPolynomial (Option sigma) F) (hQ : Q ≠ 0)
    (ev : W → V → MvPolynomial (Option sigma) F →+* R)
    (Good : W → V → Prop) (height : MvPolynomial (Option sigma) F → ℕ)
    (theta : ℚ) (n D mu H : ℕ) (htheta : 0 ≤ theta) (hmu : 1 ≤ mu)
    (hroot : Q.degreeOf none ≤ mu)
    (hheight : height (ordinaryContent Q) +
      ∑ a ∈ ordinaryRootFactorClasses Q, height (ordinaryFactorRepresentative a) ≤ H)
    (hcontent : ∃ ex : Finset W, ex.card ≤ height (ordinaryContent Q) ∧
      ∀ w ∉ ex, ∀ v, ev w v (ordinaryContent Q) ≠ 0)
    (hfactors : ∀ a ∈ ordinaryRootFactorClasses Q, ∃ ex : Finset W,
      (ex.card : ℚ) ≤ ordinaryFactorSharpRaw theta n D
        (degreeOf none (ordinaryFactorRepresentative a))
        (height (ordinaryFactorRepresentative a)) ∧
      ∀ w ∉ ex, ∀ v, ev w v (ordinaryFactorRepresentative a) = 0 → Good w v) :
    ∃ ex : Finset W, (ex.card : ℚ) ≤ ordinaryFactorSharpRaw theta n D mu H ∧
      ∀ w ∉ ex, ∀ v, ev w v Q = 0 → Good w v := by
  classical
  obtain ⟨contentEx, hcCard, hc⟩ := hcontent
  let S := ordinaryRootFactorClasses Q
  choose factorEx hfCard hf using hfactors
  let allEx := contentEx ∪ S.biUnion fun a =>
    if ha : a ∈ S then factorEx a ha else ∅
  refine ⟨allEx, ?_, ?_⟩
  · have hUnion : allEx.card ≤ contentEx.card +
        ∑ a ∈ S, (if ha : a ∈ S then factorEx a ha else ∅).card :=
      (Finset.card_union_le _ _).trans (Nat.add_le_add_left Finset.card_biUnion_le _)
    have hsum : (∑ a ∈ S, ((if ha : a ∈ S then factorEx a ha else ∅).card : ℚ)) ≤
        ∑ a ∈ S, ordinaryFactorSharpRaw theta n D
          (degreeOf none (ordinaryFactorRepresentative a))
          (height (ordinaryFactorRepresentative a)) := by
      apply Finset.sum_le_sum
      intro a ha
      simpa only [dif_pos ha] using hfCard a ha
    have hUnionQ : (allEx.card : ℚ) ≤ contentEx.card +
        ∑ a ∈ S, ((if ha : a ∈ S then factorEx a ha else ∅).card : ℚ) := by
      exact_mod_cast hUnion
    apply hUnionQ.trans
    apply (add_le_add (show (contentEx.card : ℚ) ≤ height (ordinaryContent Q) by
      exact_mod_cast hcCard) hsum).trans
    exact ordinaryFactorSharpRaw_sum_le S
      (fun a => degreeOf none (ordinaryFactorRepresentative a))
      (fun a => height (ordinaryFactorRepresentative a)) theta n D mu H
      (height (ordinaryContent Q)) htheta hmu
      ((ordinary_root_degree_sum_le Q hQ).trans hroot) hheight
  · intro w hw v hzero
    have hwc : w ∉ contentEx := fun hm => hw (Finset.mem_union_left _ hm)
    have hsplit := (ordinary_split_zero_iff Q hQ (ev w v)).mpr hzero
    rw [map_mul] at hsplit
    have hr := (mul_eq_zero.mp hsplit).resolve_left (hc w hwc v)
    rw [ordinaryRootProduct, map_prod, Finset.prod_eq_zero_iff] at hr
    obtain ⟨a, ha, hazero⟩ := hr
    apply hf a ha w _ v hazero
    intro hmem
    apply hw
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    exact ⟨a, ha, by simpa only [dif_pos (show a ∈ S from ha)] using hmem⟩

open Classical in
/-- Every positive-root-degree irreducible ordinary equation with root degree at most `D`
has the sharp ordinary exception bound in all characteristics. -/
theorem exists_exceptional_irreducibleOrdinaryEquation_sharp
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E] {n : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (D h A : ℕ)
    (hD : 0 < D) (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h)
    (hirr : Irreducible Q) (hpos : 0 < Q.degreeOf (some 0))
    (hdegreeD : Q.degreeOf (some 0) ≤ D) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ ordinaryFactorSharpRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D
          (Q.degreeOf (some 0)) h ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (fun i => iota (f i) + z * iota (g i)) P).card →
        HasExactCorrelatedPair domain f g iota (D + 1) z P := by
  classical
  let p := ringExpChar E
  obtain ⟨e, H, hHirr, hHder, hHdegree, _, hHheight, htransport⟩ :=
    exists_frobeniusEquation p hpos hirr hheight
  have hHpos : 0 < H.degreeOf (some 0) := by
    by_contra! hz
    have hz' := Nat.eq_zero_of_le_zero hz
    rw [hz', zero_mul] at hHdegree
    omega
  have hs : 1 ≤ p ^ e := pow_pos (expChar_pos E p) e
  have hHD : H.degreeOf (some 0) ≤ D := by
    calc
      H.degreeOf (some 0) ≤ H.degreeOf (some 0) * p ^ e := by
        simpa only [Nat.mul_one] using Nat.mul_le_mul_left (H.degreeOf (some 0)) hs
      _ = Q.degreeOf (some 0) := hHdegree
      _ ≤ D := hdegreeD
  obtain ⟨ex, hexCard, hex⟩ := exists_exceptional_frobeniusFactorSolutions_sharp
    domain f g iota H p e D h (H.degreeOf (some 0)) A hD hHpos hDA hAn hHheight
    (by rw [ordinary_jetWeight_eq_degreeOf]) hHirr hHder rfl hHD
  have heq : p ^ e * H.degreeOf (some 0) = Q.degreeOf (some 0) := by
    simpa only [Nat.mul_comm] using hHdegree
  refine ⟨ex, ?_, ?_⟩
  · simpa only [heq] using hexCard
  · intro z hz P hP hroot hagree
    let w := (iterateFrobeniusEquiv E p e).symm z
    have hw : w ^ (p ^ e) = z :=
      (iterateFrobeniusEquiv E p e).apply_symm_apply z
    have hEval (x : E) : (Polynomial.aeval x).toRingHom = Polynomial.evalRingHom x := by
      apply Polynomial.ringHom_ext
      · intro a
        simp
      · simp
    have hHroot : differentialSpecialization (challengeSpecialization H w)
        (expand E (p ^ e) P) = 0 := by
      rw [challengeSpecialization, hEval]
      apply htransport P w
      rw [hw]
      simpa only [challengeSpecialization, hEval] using hroot
    have hout := hex w (by simpa only [hw] using hz) P hP hHroot
      (by simpa only [hw] using hagree)
    simpa only [hw] using hout

open Classical in
/-- Every nonzero ordinary equation of root degree at most `mu ≤ D` has the sharp ordinary
exception bound. Factor extraction, Frobenius transport, and finite union are internal. -/
theorem exists_exceptional_ordinaryEquation_sharp
    {F E : Type*} [Field F] [Field E] [IsAlgClosed E] {n : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F) (iota : F →+* E)
    (Q : DifferentialPolynomial E[X] 0) (D h mu A : ℕ)
    (hQ : Q ≠ 0) (hD : 0 < D) (hmu : 1 ≤ mu) (hmuD : mu ≤ D)
    (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h) (hdegree : Q.degreeOf (some 0) ≤ mu) :
    ∃ exceptional : Finset E,
      (exceptional.card : ℚ) ≤ ordinaryFactorSharpRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D mu h ∧
      ∀ z ∉ exceptional, ∀ P : E[X], P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        A ≤ (polynomialAgreementSet (mappedDomain domain iota)
          (fun i => iota (f i) + z * iota (g i)) P).card →
        HasExactCorrelatedPair domain f g iota (D + 1) z P := by
  classical
  let flat := ordinaryFlatten E Q
  let height (R : MvPolynomial (Option (Fin 2)) E) := R.degreeOf (some 1)
  let ev (z : E) (P : E[X]) :=
    ((differentialSpecializationHom P).toRingHom.comp
      (MvPolynomial.map (σ := JetVariable 0) (Polynomial.aeval z).toRingHom)).comp
        (ordinaryUnflatten E).toRingHom
  let Good (z : E) (P : E[X]) := P.degree < D + 1 →
    A ≤ (polynomialAgreementSet (mappedDomain domain iota)
      (fun i => iota (f i) + z * iota (g i)) P).card →
    HasExactCorrelatedPair domain f g iota (D + 1) z P
  have hflat : flat ≠ 0 := (ordinaryFlatten E).map_ne_zero_iff.mpr hQ
  have hdegUnflat (R : MvPolynomial (Option (Fin 2)) E) :
      (ordinaryUnflatten E R).degreeOf (some 0) = R.degreeOf none := by
    rw [← degreeOf_none_ordinaryFlatten]
    simp [ordinaryUnflatten]
  have hev (z : E) (P : E[X]) (R : MvPolynomial (Option (Fin 2)) E) :
      ev z P R = differentialSpecialization
        (challengeSpecialization (ordinaryUnflatten E R) z) P := rfl
  have hc : ∃ ex : Finset E, ex.card ≤ height (ordinaryContent flat) ∧
      ∀ z ∉ ex, ∀ P, ev z P (ordinaryContent flat) ≠ 0 := by
    obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_ordinaryContent
      (ordinaryUnflatten E (ordinaryContent flat))
      ((ordinaryUnflatten E).map_ne_zero_iff.mpr (ordinaryContent_ne_zero flat))
      (by rw [hdegUnflat, degreeOf_ordinaryContent_none])
      (challengeHeightLE_ordinaryUnflatten_of_degreeOf_le _ le_rfl)
    exact ⟨ex, hcard, hgood⟩
  have hrootSum :
      ∑ a ∈ ordinaryRootFactorClasses flat,
          degreeOf none (ordinaryFactorRepresentative a) ≤ mu :=
    (ordinary_root_degree_sum_le flat hflat).trans
      (by simpa only [flat, degreeOf_none_ordinaryFlatten] using hdegree)
  have hf : ∀ a ∈ ordinaryRootFactorClasses flat, ∃ ex : Finset E,
      (ex.card : ℚ) ≤ ordinaryFactorSharpRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D
        (degreeOf none (ordinaryFactorRepresentative a))
        (height (ordinaryFactorRepresentative a)) ∧
      ∀ z ∉ ex, ∀ P, ev z P (ordinaryFactorRepresentative a) = 0 → Good z P := by
    intro a ha
    obtain ⟨hirr, hpos⟩ := ordinaryRootFactorClasses_spec flat ha
    have haMu : degreeOf none (ordinaryFactorRepresentative a) ≤ mu :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) ha).trans hrootSum
    obtain ⟨ex, hcard, hgood⟩ := exists_exceptional_irreducibleOrdinaryEquation_sharp
      domain f g iota (ordinaryUnflatten E (ordinaryFactorRepresentative a)) D
      (height (ordinaryFactorRepresentative a)) A hD hDA hAn
      (challengeHeightLE_ordinaryUnflatten_of_degreeOf_le _ le_rfl)
      (hirr.map (ordinaryUnflatten E)) (by simpa only [hdegUnflat] using hpos)
      (by simpa only [hdegUnflat] using haMu.trans hmuD)
    refine ⟨ex, ?_, ?_⟩
    · simpa only [hdegUnflat] using hcard
    · intro z hz P hroot hP hagree
      exact hgood z hz P hP hroot hagree
  obtain ⟨ex, hcard, hgood⟩ :=
    exists_exceptional_ordinaryFactorAssembly_sharp flat hflat ev Good height
      (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D mu h (by positivity) hmu
      (by simpa only [flat, degreeOf_none_ordinaryFlatten] using hdegree)
      ((ordinary_degree_sum_le flat hflat (some 1)).trans
        (degreeOf_challenge_ordinaryFlatten_le Q hheight)) hc hf
  refine ⟨ex, hcard, ?_⟩
  intro z hz P hP hroot hagree
  apply hgood z hz P _ hP hagree
  rw [hev]
  simpa only [flat, ordinaryUnflatten, AlgEquiv.symm_apply_apply] using hroot

open Classical in
/-- Base-field form of the sharp ordinary equation theorem. The algebraic closure and all
Frobenius choices are internal, while the conclusion retains base-field candidates and the
full original agreement sets. -/
theorem exists_exceptional_ordinaryEquation_sharp_base
    {F : Type*} [Field F] {n : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (Q : DifferentialPolynomial F[X] 0) (D h mu A : ℕ)
    (hQ : Q ≠ 0) (hD : 0 < D) (hmu : 1 ≤ mu) (hmuD : mu ≤ D)
    (hDA : D + 1 ≤ A) (hAn : A ≤ n)
    (hheight : ChallengeHeightLE Q h) (hdegree : Q.degreeOf (some 0) ≤ mu) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ ordinaryFactorSharpRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D mu h ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        differentialSpecialization (challengeSpecialization Q z) P = 0 →
        A ≤ (polynomialAgreementSet domain (fun i => f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) (D + 1) z P := by
  classical
  let E := AlgebraicClosure F
  let iota := algebraMap F E
  let QE := MvPolynomial.map (Polynomial.mapRingHom iota) Q
  have hQE : QE ≠ 0 := by
    intro hz
    apply hQ
    apply MvPolynomial.map_injective (Polynomial.mapRingHom iota)
      (Polynomial.map_injective iota iota.injective)
    simpa only [map_zero] using hz
  have hQheight : ChallengeHeightLE QE h := hheight.map_coefficients iota
  have hQdegree : QE.degreeOf (some 0) ≤ mu := by
    apply MvPolynomial.degreeOf_le_iff.mpr
    intro u hu
    exact (MvPolynomial.monomial_le_degreeOf (some 0)
      (MvPolynomial.support_map_subset _ _ hu)).trans hdegree
  obtain ⟨ex, hexCard, hex⟩ := exists_exceptional_ordinaryEquation_sharp
    domain f g iota QE D h mu A hQE hD hmu hmuD hDA hAn hQheight hQdegree
  obtain ⟨baseEx, hbaseCard, hbase⟩ := exists_exceptional_equation_correlatedAgreement_descend
    domain f g iota Q (D + 1) A ex (fun z hz P hP hagree hroot =>
      hex z hz P hP hroot hagree)
  refine ⟨baseEx, le_trans (by exact_mod_cast hbaseCard) hexCard, ?_⟩
  intro z hz P hP hroot hagree
  exact hbase z hz P hP hagree hroot

end

end ReedSolomon
