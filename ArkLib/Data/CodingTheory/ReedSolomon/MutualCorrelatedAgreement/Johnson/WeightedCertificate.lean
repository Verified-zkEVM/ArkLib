/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Ordinary.Weighted
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Ordinary.UnifiedCurve
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.PowerToLine
public import ArkLib.Data.CodingTheory.ReedSolomon.AgreementList
public import ArkLib.Data.CodingTheory.ListDecodability.PairAgreementBound

/-!
# Semantic consequences of weighted Johnson certificates

The weighted finite certificate constructs the same primitive ordinary equation used by the
all-characteristic geometric transfer.  This file connects those two layers without hiding the
agreement subset: the exceptional set is chosen before the candidate and before every qualifying
subset, while the conclusion identifies the candidate's full agreement set.
-/

@[expose] public section

namespace ReedSolomon

open Polynomial MvPolynomial PolynomialDifferential HiddenDerivative CoreDefinitions LinearCode

noncomputable section

open scoped BigOperators ProbabilityTheory ENNReal

private theorem card_mul_johnsonDenominator_le
    {κ ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : Finset κ) (S : κ → Finset ι) (A D : ℕ)
    (hDA : D ≤ A) (hpositive : Fintype.card ι * D < A * A)
    (hclose : ∀ x ∈ T, A ≤ (S x).card)
    (hpair : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → ((S x) ∩ (S y)).card ≤ D) :
    T.card * (A * A - Fintype.card ι * D) ≤ Fintype.card ι * (A - D) := by
  classical
  let L : ℝ := T.card
  let n : ℝ := Fintype.card ι
  let a : ℝ := A
  let d : ℝ := D
  let Z : ℝ := ∑ x ∈ T, ((S x).card : ℝ)
  let Q : ℝ := ∑ x ∈ T, ∑ y ∈ T, (((S x) ∩ (S y)).card : ℝ)
  have hsum : Z = ∑ i : ι, ((T.filter fun x => i ∈ S x).card : ℝ) := by
    dsimp only [Z]
    calc
      (∑ x ∈ T, ((S x).card : ℝ)) =
          ∑ x ∈ T, ∑ i : ι, if i ∈ S x then (1 : ℝ) else 0 := by
            apply Finset.sum_congr rfl
            intro x hx
            symm
            simp
      _ = ∑ i : ι, ∑ x ∈ T, if i ∈ S x then (1 : ℝ) else 0 := by
            rw [Finset.sum_comm]
      _ = ∑ i : ι, ((T.filter fun x => i ∈ S x).card : ℝ) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact Finset.sum_boole (R := ℝ) (fun x => i ∈ S x) T
  have hsquares :
      (∑ i : ι, ((T.filter fun x => i ∈ S x).card : ℝ) ^ 2) = Q := by
    dsimp only [Q]
    symm
    calc
      (∑ x ∈ T, ∑ y ∈ T, (((S x) ∩ (S y)).card : ℝ)) =
          ∑ x ∈ T, ∑ y ∈ T, ∑ i : ι,
            if i ∈ S x ∩ S y then (1 : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro x hx
              apply Finset.sum_congr rfl
              intro y hy
              have h := Finset.sum_boole (R := ℝ)
                (fun i : ι => i ∈ S x ∩ S y) Finset.univ
              have hf : (Finset.univ.filter fun i : ι => i ∈ S x ∩ S y) = S x ∩ S y := by
                ext i
                simp
              rw [hf] at h
              exact h.symm
      _ = ∑ x ∈ T, ∑ i : ι, ∑ y ∈ T,
            if i ∈ S x ∩ S y then (1 : ℝ) else 0 := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [Finset.sum_comm]
      _ = ∑ i : ι, ∑ x ∈ T, ∑ y ∈ T,
            if i ∈ S x ∩ S y then (1 : ℝ) else 0 := by
              rw [Finset.sum_comm]
      _ = ∑ i : ι, ∑ x ∈ T, ∑ y ∈ T,
            (if i ∈ S x then (1 : ℝ) else 0) *
              (if i ∈ S y then (1 : ℝ) else 0) := by
              apply Finset.sum_congr rfl
              intro i hi
              apply Finset.sum_congr rfl
              intro x hx
              apply Finset.sum_congr rfl
              intro y hy
              simp only [Finset.mem_inter]
              by_cases hix : i ∈ S x <;> by_cases hiy : i ∈ S y <;> simp [hix, hiy]
      _ = ∑ i : ι,
            (∑ x ∈ T, if i ∈ S x then (1 : ℝ) else 0) ^ 2 := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [sq, Finset.sum_mul_sum]
      _ = ∑ i : ι, ((T.filter fun x => i ∈ S x).card : ℝ) ^ 2 := by
              apply Finset.sum_congr rfl
              intro i hi
              rw [Finset.sum_boole (R := ℝ) (fun x => i ∈ S x) T]
  have hZlower : L * a ≤ Z := by
    have h := Finset.sum_le_sum (fun x hx => show (A : ℝ) ≤ (S x).card by
      exact_mod_cast hclose x hx)
    simpa [L, a, Z] using h
  have hQupper : Q ≤ Z + L * (L - 1) * d := by
    have hrow : ∀ x ∈ T,
        (∑ y ∈ T, (((S x) ∩ (S y)).card : ℝ)) ≤
          (S x).card + (L - 1) * d := by
      intro x hx
      rw [(Finset.add_sum_erase T
        (fun y => (((S x) ∩ (S y)).card : ℝ)) hx).symm]
      have herase :
          (∑ y ∈ T.erase x, (((S x) ∩ (S y)).card : ℝ)) ≤ (L - 1) * d := by
        have hterms : ∀ y ∈ T.erase x,
            ((((S x) ∩ (S y)).card : ℕ) : ℝ) ≤ d := by
          intro y hy
          dsimp only [d]
          exact_mod_cast hpair x hx y (Finset.mem_of_mem_erase hy)
            (Ne.symm (Finset.ne_of_mem_erase hy))
        have h := Finset.sum_le_card_nsmul (T.erase x)
          (fun y => (((S x) ∩ (S y)).card : ℝ)) d hterms
        rw [nsmul_eq_mul] at h
        have hcard : ((T.erase x).card : ℝ) = L - 1 := by
          rw [Finset.card_erase_of_mem hx]
          have hone : 1 ≤ T.card := Finset.card_pos.mpr ⟨x, hx⟩
          push_cast [Nat.cast_sub hone]
          simp [L]
        simpa [hcard] using h
      simpa using add_le_add_left herase ((S x).card : ℝ)
    calc
      Q ≤ ∑ x ∈ T, (((S x).card : ℝ) + (L - 1) * d) := by
        exact Finset.sum_le_sum hrow
      _ = Z + L * (L - 1) * d := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
        simp [L, Z]
        ring
  have hCauchy : Z ^ 2 ≤ n * Q := by
    have h := sq_sum_le_card_mul_sum_sq
      (s := (Finset.univ : Finset ι))
      (f := fun i => ((T.filter fun x => i ∈ S x).card : ℝ))
    rw [← hsum, hsquares] at h
    simpa [n] using h
  have hLnonneg : 0 ≤ L := by positivity
  have hAnonneg : 0 ≤ a := by positivity
  have hnnonneg : 0 ≤ n := by positivity
  have hdnonneg : 0 ≤ d := by positivity
  have hreal : L * (a ^ 2 - n * d) ≤ n * (a - d) := by
    by_cases hLzero : L = 0
    · have hda : d ≤ a := by
        dsimp only [d, a]
        exact_mod_cast hDA
      rw [hLzero, zero_mul]
      exact mul_nonneg hnnonneg (sub_nonneg.mpr hda)
    have hLpos : 0 < L := lt_of_le_of_ne hLnonneg (Ne.symm hLzero)
    by_cases hsmall : L * a ≤ n
    · have hLone : 1 ≤ L := by
        have : 1 ≤ T.card := Nat.one_le_iff_ne_zero.mpr (by
          intro h
          apply hLzero
          simp [L, h])
        dsimp only [L]
        exact_mod_cast this
      have hfirst : 0 ≤ a * (n - L * a) :=
        mul_nonneg hAnonneg (sub_nonneg.mpr hsmall)
      have hsecond : 0 ≤ n * d * (L - 1) :=
        mul_nonneg (mul_nonneg hnnonneg hdnonneg) (sub_nonneg.mpr hLone)
      nlinarith only [hsmall, hfirst, hsecond]
    · have hlarge : n < L * a := lt_of_not_ge hsmall
      have hmono : (L * a) ^ 2 - n * (L * a) ≤ Z ^ 2 - n * Z := by
        have hzsub : 0 ≤ Z - L * a := sub_nonneg.mpr hZlower
        have hzsum : 0 ≤ Z + L * a - n := by nlinarith
        have hfactor : 0 ≤ (Z - L * a) * (Z + L * a - n) :=
          mul_nonneg hzsub hzsum
        nlinarith only [hfactor]
      have hkey : Z ^ 2 - n * Z ≤ n * (L * (L - 1) * d) := by
        calc
          Z ^ 2 - n * Z ≤ n * Q - n * Z := sub_le_sub_right hCauchy _
          _ ≤ n * (Z + L * (L - 1) * d) - n * Z :=
            sub_le_sub_right (mul_le_mul_of_nonneg_left hQupper hnnonneg) _
          _ = n * (L * (L - 1) * d) := by ring
      have hmulgoal :
          L * (L * (a ^ 2 - n * d)) ≤ L * (n * (a - d)) := by
        nlinarith only [hmono.trans hkey]
      exact le_of_mul_le_mul_left hmulgoal hLpos
  have hcastDen :
      ((A * A - Fintype.card ι * D : ℕ) : ℝ) = a ^ 2 - n * d := by
    rw [Nat.cast_sub hpositive.le]
    simp [a, n, d, pow_two]
  have hcastGap : ((A - D : ℕ) : ℝ) = a - d := by
    rw [Nat.cast_sub hDA]
  exact_mod_cast (show
    (T.card : ℝ) * (A * A - Fintype.card ι * D : ℕ) ≤
      (Fintype.card ι : ℝ) * (A - D : ℕ) by
    rw [hcastDen, hcastGap]
    simpa [L, n] using hreal)

open Classical in
/-- Exact integral pairwise Johnson bound for complete Reed--Solomon agreement lists.

The statement is field-independent and includes the zero polynomial.  Its hypotheses force the
positive Johnson denominator, so the natural-number quotient is the literal floor used in the
finite table. -/
theorem closePolynomialSet_finite_and_ncard_le_johnsonPairwise
    {F : Type*} [Field F] {n D A : ℕ}
    (domain : Fin n ↪ F) (received : Fin n → F)
    (hDA : D + 1 ≤ A) (hpositive : n * D < A * A) :
    (closePolynomialSet domain received (D + 1) A).Finite ∧
      (closePolynomialSet domain received (D + 1) A).ncard ≤
        johnsonPairwiseListFloor n D A := by
  classical
  let candidates := closePolynomialSet domain received (D + 1) A
  have hfinite : candidates.Finite := closePolynomialSet_finite domain received hDA
  let T := hfinite.toFinset
  let S : F[X] → Finset (Fin n) := polynomialAgreementSet domain received
  have hclose : ∀ P ∈ T, A ≤ (S P).card := by
    intro P hP
    exact (hfinite.mem_toFinset.mp hP).2
  have hpair : ∀ P ∈ T, ∀ Q ∈ T, P ≠ Q → ((S P) ∩ (S Q)).card ≤ D := by
    intro P hP Q hQ hne
    by_contra hcard
    have hDcard : D + 1 ≤ ((S P) ∩ (S Q)).card := by omega
    apply hne
    apply Polynomial.eq_of_degrees_lt_of_eval_index_eq
      ((S P) ∩ (S Q)) domain.injective.injOn
    · exact (hfinite.mem_toFinset.mp hP).1.trans_le (by exact_mod_cast hDcard)
    · exact (hfinite.mem_toFinset.mp hQ).1.trans_le (by exact_mod_cast hDcard)
    · intro i hi
      have hiP := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).1).2
      have hiQ := (Finset.mem_filter.mp (Finset.mem_inter.mp hi).2).2
      exact hiP.trans hiQ.symm
  have hmul := card_mul_johnsonDenominator_le T S A D (by omega)
    (by simpa using hpositive) hclose hpair
  refine ⟨hfinite, ?_⟩
  rw [Set.ncard_eq_toFinset_card _ hfinite]
  rw [johnsonPairwiseListFloor]
  apply (Nat.le_div_iff_mul_le (by omega : 0 < A * A - n * D)).2
  simpa [T] using hmul

/-- Below the sharp cutoff, the unified ordinary charge is the weighted table expression. -/
theorem ordinaryUnifiedPowerFactorRaw_one_eq_johnsonWeightedSharpException
    {n D A B H : ℕ} (hBD : B ≤ D) :
    ordinaryUnifiedPowerFactorRaw
        (((n - D : ℕ) : ℚ) / ((A - D : ℕ) : ℚ)) n D 1 B H =
      johnsonWeightedSharpException n D A B H := by
  have hB : B ≤ 2 * D + 1 := by omega
  unfold ordinaryUnifiedPowerFactorRaw
  rw [ordinaryPsi_eq_sharp hB]
  unfold johnsonWeightedSharpException
  push_cast
  ring

open Classical in
/-- A checked weighted Johnson certificate gives characteristic-free exact line recovery.

The exceptional set precedes the scalar, polynomial, and agreement subset.  Consequently the
statement applies directly to a projected-code witness: any qualifying subset of the candidate's
full agreement set forces recovery, and `HasExactCorrelatedPair` retains equality of that full
agreement set. -/
theorem exists_exceptional_weightedJohnsonMCA
    {F : Type*} [Field F] {n D A m B H : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (hcert : IsJohnsonWeightedCertificate n D A m B H)
    (hD : 1 ≤ D) (hDA : D + 1 ≤ A) (hAn : A ≤ n) (hBD : B ≤ D) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ johnsonWeightedSharpException n D A B H ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        ∀ indices : Finset (Fin n), A ≤ indices.card →
          (∀ i ∈ indices, P.eval (domain i) = f i + z * g i) →
          HasExactCorrelatedPair domain f g (RingHom.id F) (D + 1) z P := by
  classical
  obtain ⟨cert⟩ := hcert.exists_symbolic hD le_rfl domain f g
  have hQ : cert.Q ≠ 0 := by
    intro hz
    have hspec := (cert.specialization_sound (RingHom.id F) 0).1
    apply hspec
    rw [hz, map_zero]
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_ordinaryPowerEquation_base_unified
      domain ![f, g] cert.Q D H B A hQ hD (by omega) hcert.2.1 hDA hAn
        cert.challengeDegree_le cert.jetDegree_le
  refine ⟨exceptional, ?_, ?_⟩
  · simpa [ordinaryUnifiedPowerFactorRaw_one_eq_johnsonWeightedSharpException hBD] using hcard
  · intro z hz P hP indices hindices hagree
    have hline : powerBatchedWord (ℓ := 1) ![f, g] z =
        (fun i ↦ f i + z * g i) := by
      funext i
      simp [powerBatchedWord, Fin.sum_univ_two]
    have hsubset : indices ⊆
        polynomialAgreementSet domain (powerBatchedWord (ℓ := 1) ![f, g] z) P := by
      intro i hi
      rw [hline]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, hagree i hi⟩
    have hagreeFull : A ≤
        (polynomialAgreementSet domain (powerBatchedWord (ℓ := 1) ![f, g] z) P).card :=
      hindices.trans (Finset.card_le_card hsubset)
    have hroot := (cert.specialization_sound (RingHom.id F) z).2
      indices P hP hindices hagree
    have hroot' : differentialSpecialization (challengeSpecialization cert.Q z) P = 0 := by
      have heval : Polynomial.eval₂RingHom (RingHom.id F) z =
          (Polynomial.aeval z).toRingHom := by
        apply Polynomial.ringHom_ext
        · intro a
          simp
        · simp
      simpa only [heval, challengeSpecialization] using hroot
    exact exactCorrelatedPair_of_powerAgreement_one domain ![f, g]
      (RingHom.id F) z P (hgood z hz P hP hroot' hagreeFull)

open Classical in
/-- Full-agreement specialization of `exists_exceptional_weightedJohnsonMCA`. -/
theorem exists_exceptional_weightedJohnsonMCA_fullAgreement
    {F : Type*} [Field F] {n D A m B H : ℕ}
    (domain : Fin n ↪ F) (f g : Fin n → F)
    (hcert : IsJohnsonWeightedCertificate n D A m B H)
    (hD : 1 ≤ D) (hDA : D + 1 ≤ A) (hAn : A ≤ n) (hBD : B ≤ D) :
    ∃ exceptional : Finset F,
      (exceptional.card : ℚ) ≤ johnsonWeightedSharpException n D A B H ∧
      ∀ z ∉ exceptional, ∀ P : F[X], P.degree < D + 1 →
        A ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id F) (D + 1) z P := by
  obtain ⟨exceptional, hcard, hgood⟩ :=
    exists_exceptional_weightedJohnsonMCA domain f g hcert hD hDA hAn hBD
  refine ⟨exceptional, hcard, ?_⟩
  intro z hz P hP hagree
  exact hgood z hz P hP
    (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P) hagree
    (fun i hi ↦ (Finset.mem_filter.mp hi).2)

open Classical in
/-- Over a finite field, a weighted certificate bounds the canonical affine-line MCA error by
its exact raw exceptional count divided by the field cardinality. -/
theorem weightedJohnson_mcaError_le
    {F : Type} [Field F] [Fintype F] {n D A m B H : ℕ}
    (domain : Fin n ↪ F)
    (hcert : IsJohnsonWeightedCertificate n D A m B H)
    (hD : 1 ≤ D) (hDA : D + 1 ≤ A) (hAn : A ≤ n) (hBD : B ≤ D)
    (radius : ℝ) (hthreshold : A ≤ ⌈(n : ℝ) * (1 - radius)⌉₊) :
    mcaError (AffineLineGenerator F) (code domain (D + 1)) radius ≤
      min 1 (ENNReal.ofReal
        ((johnsonWeightedSharpException n D A B H : ℝ) /
          (Fintype.card F : ℝ))) := by
  classical
  have hline : LineExactAgreementBound domain (D + 1) A
      (johnsonWeightedSharpException n D A B H : ℝ) := by
    intro f g
    obtain ⟨exceptional, hcard, hgood⟩ :=
      exists_exceptional_weightedJohnsonMCA_fullAgreement
        domain f g hcert hD hDA hAn hBD
    refine ⟨exceptional, ?_, ?_⟩
    · exact_mod_cast hcard
    · intro z hz P hP hagree
      obtain ⟨pair, hp0, hp1, heq, hset⟩ := hgood z hz P hP hagree
      refine ⟨pair.1, pair.2, hp0, hp1, ?_, ?_⟩
      · simpa [correlatedPairSpecialization] using heq
      · simpa [mappedDomain] using hset
  exact mcaError_affineLine_le_min_one_of_exactAgreement
    domain _ hline radius hthreshold

end

end ReedSolomon
