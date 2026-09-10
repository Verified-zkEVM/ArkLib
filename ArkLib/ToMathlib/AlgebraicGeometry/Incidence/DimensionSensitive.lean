/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.SharpRatio
public import ArkLib.ToMathlib.AlgebraicGeometry.Incidence.EvaluationDimension
public import ArkLib.ToMathlib.AlgebraicGeometry.CutFamily.Iteration
public import ArkLib.ToMathlib.Set.Finite

/-!
# Dimension-sensitive agreement incidence

The usual sharp incidence induction uses one fixed upper bound on the number of equations that
may contain a positive-dimensional component.  In coefficient spaces, the sharper hereditary
statement depends on the component dimension: a component of dimension `t` can be contained in
at most `k - t` independent equations.  Recording that bound at every retained principal cut
replaces a power of one worst-case ratio by a product of the ratios at the actual dimensions.

This module isolates the generic induction.  Applications must prove the hereditary component
hypothesis on their actual retained source locus; the theorem does not assume a target dimension
bound merely from pointwise uniqueness.
-/

@[expose] public section

noncomputable section

open MvPolynomial
open scoped BigOperators

namespace AffineHilbert

variable {F σ : Type*} [Field F] [Finite σ]

/-- A finite union of finite loci is bounded by the sum of their supplied rational cardinality
bounds.  This packages the final passage from retained primes to their joint point family. -/
theorem finite_biUnion_and_ncard_le_sum {ι X : Type*}
    (T : Finset ι) (S : ι → Set X) (w : ι → ℚ)
    (hfinite : ∀ i ∈ T, (S i).Finite)
    (hcard : ∀ i ∈ T, ((S i).ncard : ℚ) ≤ w i) :
    (⋃ i ∈ T, S i).Finite ∧ (((⋃ i ∈ T, S i).ncard : ℕ) : ℚ) ≤ ∑ i ∈ T, w i := by
  classical
  induction T using Finset.induction_on with
  | empty => simp
  | @insert a T ha ih =>
      have hSa := hfinite a (Finset.mem_insert_self a T)
      have hST : ∀ i ∈ T, (S i).Finite := fun i hi ↦
        hfinite i (Finset.mem_insert_of_mem hi)
      have hcT : ∀ i ∈ T, ((S i).ncard : ℚ) ≤ w i := fun i hi ↦
        hcard i (Finset.mem_insert_of_mem hi)
      obtain ⟨hfiniteT, hboundT⟩ := ih hST hcT
      rw [Finset.set_biUnion_insert]
      refine ⟨hSa.union hfiniteT, ?_⟩
      rw [Finset.sum_insert ha]
      calc
        (((S a ∪ ⋃ i ∈ T, S i).ncard : ℕ) : ℚ) ≤
            ((S a).ncard : ℚ) + (((⋃ i ∈ T, S i).ncard : ℕ) : ℚ) := by
          exact_mod_cast Set.ncard_union_le (S a) (⋃ i ∈ T, S i)
        _ ≤ w a + ∑ i ∈ T, w i := add_le_add
          (hcard a (Finset.mem_insert_self a T)) hboundT

/-- Sum per-prime finite locus bounds over a retained family using its affine-degree potential. -/
theorem retainedPrimeFamily_finite_biUnion_and_ncard_le
    {X : Type*} (T : Finset (Ideal (MvPolynomial σ F)))
    (S : Ideal (MvPolynomial σ F) → Set X) (B V : ℚ)
    (hB : 0 ≤ B)
    (hfinite : ∀ i ∈ T, (S i).Finite)
    (hcard : ∀ i ∈ T, ((S i).ncard : ℚ) ≤ affineDegree i * B)
    (hpotential : ∑ i ∈ T, affineDegree i ≤ V) :
    (⋃ i ∈ T, S i).Finite ∧ (((⋃ i ∈ T, S i).ncard : ℕ) : ℚ) ≤ V * B := by
  obtain ⟨hfin, hsum⟩ := finite_biUnion_and_ncard_le_sum T S
    (fun i ↦ affineDegree i * B) hfinite hcard
  refine ⟨hfin, hsum.trans ?_⟩
  rw [← Finset.sum_mul]
  exact mul_le_mul_of_nonneg_right hpotential hB

/-- The product of the successive incidence ratios in dimensions `1, ..., d`.

The factor `b` is the degree bound for each cutting equation.  For affine hyperplanes, specialize
to `b = 1` to obtain the product used for Reed--Solomon evaluation incidence. -/
def dimensionSensitiveIncidenceProduct (n A k b : ℕ) : ℕ → ℚ
  | 0 => 1
  | d + 1 => dimensionSensitiveIncidenceProduct n A k b d *
      ((((n - k + d + 1) * b : ℕ) : ℚ) / ((A - k + d + 1 : ℕ) : ℚ))

@[simp]
theorem dimensionSensitiveIncidenceProduct_zero (n A k b : ℕ) :
    dimensionSensitiveIncidenceProduct n A k b 0 = 1 := rfl

theorem dimensionSensitiveIncidenceProduct_succ (n A k b d : ℕ) :
    dimensionSensitiveIncidenceProduct n A k b (d + 1) =
      dimensionSensitiveIncidenceProduct n A k b d *
        ((((n - k + d + 1) * b : ℕ) : ℚ) /
          ((A - k + d + 1 : ℕ) : ℚ)) := rfl

@[simp]
theorem dimensionSensitiveIncidenceProduct_one (n A k b : ℕ) :
    dimensionSensitiveIncidenceProduct n A k b 1 =
      ((((n - k + 1) * b : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  simp [dimensionSensitiveIncidenceProduct]

theorem dimensionSensitiveIncidenceProduct_nonneg (n A k b d : ℕ) :
    0 ≤ dimensionSensitiveIncidenceProduct n A k b d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [dimensionSensitiveIncidenceProduct_succ]
      exact mul_nonneg ih (div_nonneg (by positivity) (by positivity))

/-- The cut-degree contribution separates from the evaluation ratios. -/
theorem dimensionSensitiveIncidenceProduct_eq_pow_mul (n A k b d : ℕ) :
    dimensionSensitiveIncidenceProduct n A k b d =
      (b : ℚ) ^ d * dimensionSensitiveIncidenceProduct n A k 1 d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [dimensionSensitiveIncidenceProduct_succ,
        dimensionSensitiveIncidenceProduct_succ, ih, pow_succ]
      push_cast
      ring

/-- Each incidence factor is at least one when its threshold lies below the agreement target. -/
theorem one_le_incidenceFactor {n A T b : ℕ} (hTA : T ≤ A) (hAn : A ≤ n)
    (hb : 0 < b) :
    (1 : ℚ) ≤ ((((n - T + 1) * b : ℕ) : ℚ) / ((A - T + 1 : ℕ) : ℚ)) := by
  rw [one_le_div₀ (by exact_mod_cast (show 0 < A - T + 1 by omega))]
  exact_mod_cast (show A - T + 1 ≤ (n - T + 1) * b from
    (by omega : A - T + 1 ≤ n - T + 1).trans (Nat.le_mul_of_pos_right _ hb))

/-- In a first-order fiber, every component of dimension at most one is uniformly charged by
the single fiber ratio. -/
theorem dimensionSensitiveIncidenceProduct_le_one
    {n A k d : ℕ} (hd : d ≤ 1) (hkA : k ≤ A) (hAn : A ≤ n) :
    dimensionSensitiveIncidenceProduct n A k 1 d ≤
      ((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ) := by
  interval_cases d
  · simpa using one_le_incidenceFactor (T := k) (b := 1) hkA hAn (by omega)
  · simp

/-- The ratio of proper cuts at dimension `d` is controlled by the dimension-`d` factor
when at most `k - d` cuts vanish identically. -/
theorem goodCuts_div_agreements_le_dimension
    {n A k d m : ℕ} (hd : 0 < d) (hdk : d ≤ k) (hm : m ≤ k - d)
    (hkA : k ≤ A) (hAn : A ≤ n) :
    ((n - m : ℕ) : ℚ) / ((A - m : ℕ) : ℚ) ≤
      ((n - k + d : ℕ) : ℚ) / ((A - k + d : ℕ) : ℚ) := by
  have hm' : m < (k - d) + 1 := by omega
  have hk' : (k - d) + 1 ≤ A := by omega
  have hratio := goodCuts_div_agreements_le hm' hk' hAn
  simpa only [show n - (k - d + 1) + 1 = n - k + d by omega,
    show A - (k - d + 1) + 1 = A - k + d by omega] using hratio

/-- Every positive-dimensional prime in ordinary degree-`< k` coefficient space satisfies the
hereditary fiber budget: a dimension-`d` component is contained in at most `k - d` evaluation
hyperplanes at distinct points. -/
theorem fixedCoefficientEvaluation_dimensionSensitive_component
    {n k : ℕ} (α : Fin n ↪ F) (y : Fin n → F)
    (P : Ideal (MvPolynomial (Fin k) F)) (hP : P.IsPrime)
    (hd : 0 < (hilbertPolynomial P).natDegree) :
    let cuts : Fin n → MvPolynomial (Fin k) F := fun i ↦
      fixedCoefficientEvaluation k (α i) (y i)
    (hilbertPolynomial P).natDegree ≤ k ∧
      (cutsInIdeal P cuts).card ≤ k - (hilbertPolynomial P).natDegree := by
  classical
  dsimp only
  let cuts : Fin n → MvPolynomial (Fin k) F := fun i ↦
    fixedCoefficientEvaluation k (α i) (y i)
  let Bad := cutsInIdeal P cuts
  have hpartial (indices : Finset (Fin n)) (hcard : indices.card ≤ k)
      (hsub : indices ⊆ Bad) :
      (hilbertPolynomial P).natDegree ≤ k - indices.card := by
    let sample : Fin indices.card ↪ Fin n :=
      ⟨fun j ↦ (indices.equivFin.symm j).val,
        fun i j hij ↦ indices.equivFin.symm.injective (Subtype.ext hij)⟩
    let α' : Fin indices.card ↪ F :=
      ⟨fun j ↦ α (sample j), fun i j hij ↦ sample.injective (α.injective hij)⟩
    let y' : Fin indices.card → F := fun j ↦ y (sample j)
    apply fixedCoefficientEvaluation_hilbertPolynomial_natDegree_le hcard α' y' hP.ne_top
    intro j
    change cuts (sample j) ∈ P
    rw [← mem_cutsInIdeal]
    exact hsub (indices.equivFin.symm j).property
  have hdim : (hilbertPolynomial P).natDegree ≤ k := by
    simpa using hpartial ∅ (by simp) (by simp)
  refine ⟨hdim, ?_⟩
  change Bad.card ≤ k - (hilbertPolynomial P).natDegree
  by_cases hBadk : Bad.card ≤ k
  · have hle := hpartial Bad hBadk le_rfl
    omega
  · have hkBad : k ≤ Bad.card := by omega
    obtain ⟨indices, hindices, hcard⟩ := Finset.exists_subset_card_eq hkBad
    have hle := hpartial indices (by omega) hindices
    rw [hcard] at hle
    omega

/-- Dimension-sensitive incidence product with a separate terminal threshold in dimension
one.  The first factor is the persistent-component threshold `L`; dimensions two and above use
the joint coefficient-space budget `k + 1 - d`. -/
def hybridDimensionSensitiveIncidenceProduct (n A L k b : ℕ) : ℕ → ℚ
  | 0 => 1
  | d + 1 => hybridDimensionSensitiveIncidenceProduct n A L k b d *
      (((((n - (if d = 0 then L else k + 1 - d) + 1) * b : ℕ) : ℚ) /
        ((A - (if d = 0 then L else k + 1 - d) + 1 : ℕ) : ℚ)))

@[simp]
theorem hybridDimensionSensitiveIncidenceProduct_zero (n A L k b : ℕ) :
    hybridDimensionSensitiveIncidenceProduct n A L k b 0 = 1 := rfl

theorem hybridDimensionSensitiveIncidenceProduct_succ (n A L k b d : ℕ) :
    hybridDimensionSensitiveIncidenceProduct n A L k b (d + 1) =
      hybridDimensionSensitiveIncidenceProduct n A L k b d *
        (((((n - (if d = 0 then L else k + 1 - d) + 1) * b : ℕ) : ℚ) /
          ((A - (if d = 0 then L else k + 1 - d) + 1 : ℕ) : ℚ))) := rfl

@[simp]
theorem hybridDimensionSensitiveIncidenceProduct_one (n A L k b : ℕ) :
    hybridDimensionSensitiveIncidenceProduct n A L k b 1 =
      ((((n - L + 1) * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) := by
  simp [hybridDimensionSensitiveIncidenceProduct]

@[simp]
theorem hybridDimensionSensitiveIncidenceProduct_two (n A L k b : ℕ) :
    hybridDimensionSensitiveIncidenceProduct n A L k b 2 =
      ((((n - L + 1) * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        ((((n - k + 1) * b : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  simp [hybridDimensionSensitiveIncidenceProduct]

theorem hybridDimensionSensitiveIncidenceProduct_nonneg (n A L k b d : ℕ) :
    0 ≤ hybridDimensionSensitiveIncidenceProduct n A L k b d := by
  induction d with
  | zero => simp
  | succ d ih =>
      rw [hybridDimensionSensitiveIncidenceProduct_succ]
      exact mul_nonneg ih (div_nonneg (by positivity) (by positivity))

/-- The hybrid product is monotone in the ambient dimension when every incidence threshold is
at most the agreement target. -/
theorem hybridDimensionSensitiveIncidenceProduct_mono_dimension
    {n A L k b : ℕ} (hLA : L ≤ A) (hkA : k ≤ A) (hAn : A ≤ n) (hb : 0 < b) :
    Monotone (hybridDimensionSensitiveIncidenceProduct n A L k b) := by
  apply monotone_nat_of_le_succ
  intro d
  rw [hybridDimensionSensitiveIncidenceProduct_succ]
  apply le_mul_of_one_le_right
  · exact hybridDimensionSensitiveIncidenceProduct_nonneg n A L k b d
  · by_cases hd : d = 0
    · simpa only [if_pos hd] using one_le_incidenceFactor hLA hAn hb
    · simpa only [if_neg hd] using
        one_le_incidenceFactor (T := k + 1 - d) (by omega) hAn hb

/-- In the first-order joint family, every component of dimension at most two is uniformly
charged by the graph-recognition factor followed by the direct coefficient-space factor. -/
theorem hybridDimensionSensitiveIncidenceProduct_le_two
    {n A L k b d : ℕ} (hd : d ≤ 2) (hLA : L ≤ A) (hkA : k ≤ A)
    (hAn : A ≤ n) (hb : 0 < b) :
    hybridDimensionSensitiveIncidenceProduct n A L k b d ≤
      (((((n - L + 1) * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ))) *
        (((((n - k + 1) * b : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ))) := by
  have hL := one_le_incidenceFactor (T := L) hLA hAn hb
  have hk := one_le_incidenceFactor (T := k) hkA hAn hb
  interval_cases d
  · simpa using (one_le_mul_of_one_le_of_one_le hL hk)
  · simpa using (mul_le_mul_of_nonneg_left hk (by positivity :
      0 ≤ (((((n - L + 1) * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)))))
  · simp

/-- Incidence with an explicit current dimension and a hereditary dimension-sensitive bound
on identically vanishing cuts. -/
private theorem affineAgreementIncidence_bound_dimensionSensitive_aux
    {n A k b d : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (hcomponent : ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (hilbertPolynomial Q).natDegree →
      (hilbertPolynomial Q).natDegree ≤ k ∧
        (cutsInIdeal Q cuts).card ≤ k - (hilbertPolynomial Q).natDegree)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, x ∈ zeroLocus F P ∧ aeval x s ≠ 0)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card)
    (hd : (hilbertPolynomial P).natDegree = d) :
    (S.card : ℚ) ≤ affineDegree P * dimensionSensitiveIncidenceProduct n A k b d := by
  classical
  induction d using Nat.strong_induction_on generalizing P S with
  | h d ih =>
      cases d with
      | zero =>
          have ht := finite_zeroLocus_and_ncard_le_affineDegree (F := F) (E := F) P hd
          have hc : S.card ≤ (zeroLocus F P).ncard := by
            simpa using Set.ncard_le_ncard (fun x hx ↦ (hS x hx).1) ht.1
          have hc' : (S.card : ℚ) ≤ ((zeroLocus F P).ncard : ℚ) := by
            exact_mod_cast hc
          simpa using hc'.trans ht.2
      | succ e =>
          let Bad := cutsInIdeal P cuts
          let good := Finset.univ.filter fun i ↦ i ∉ Bad
          let R : ℚ := (((n - k + e + 1) * b : ℕ) : ℚ) /
            ((A - k + e + 1 : ℕ) : ℚ)
          have hdpos : 0 < (hilbertPolynomial P).natDegree := by rw [hd]; omega
          have hPcomponent := hcomponent P le_rfl hP hs hdpos
          have hed : e + 1 ≤ k := by simpa only [hd] using hPcomponent.1
          have hBad : Bad.card ≤ k - (e + 1) := by
            simpa only [Bad, hd] using hPcomponent.2
          have hlowerNat : S.card * (A - Bad.card) ≤
              ∑ i ∈ good, (cutPoints S (cuts i)).card := by
            exact finiteAgreementIncidence_lower_sharp S Bad
              (fun x i ↦ aeval x (cuts i) = 0) (fun x hx ↦ hA x hx)
          have hlower : (S.card : ℚ) * (A - Bad.card : ℕ) ≤
              ∑ i ∈ good, ((cutPoints S (cuts i)).card : ℚ) := by
            exact_mod_cast hlowerNat
          have hchild : ∀ i, cuts i ∉ P →
              ∀ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
                ((componentPoints S Q).card : ℚ) ≤ affineDegree Q *
                  dimensionSensitiveIncidenceProduct n A k b e := by
            intro i hiP Q hQ
            have hQdata := (Ideal.mem_retainedMinimalPrimes _ _ _).mp hQ
            have hQP : P ≤ Q := le_sup_left.trans hQdata.1.le
            have hQdegree : (hilbertPolynomial Q).natDegree = e := by
              have hpure := principalCut_component_hilbertPolynomial_natDegree_add_one
                hP hiP hQdata.1
              rw [hd] at hpure
              omega
            apply ih e (by omega) (P := Q) (S := componentPoints S Q)
              hQdata.1.isPrime hQdata.2
            · intro J hQJ hJ hsJ hdJ
              exact hcomponent J (hQP.trans hQJ) hJ hsJ hdJ
            · intro x hx
              rw [mem_componentPoints] at hx
              exact ⟨hx.2, (hS x hx.1).2⟩
            · intro x hx
              rw [mem_componentPoints] at hx
              exact hA x hx.1
            · exact hQdegree
          have hone (i : Fin n) (hi : i ∈ good) :
              ((cutPoints S (cuts i)).card : ℚ) ≤
                b * affineDegree P * dimensionSensitiveIncidenceProduct n A k b e := by
            have hiP : cuts i ∉ P := by
              simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and,
                Bad, mem_cutsInIdeal] using hi
            have hc := card_filter_cut_le_sum_retained P s (cuts i) S hS
            have hsdeg := sum_retained_affineDegree_le (s := s) hP hiP (hdeg i)
            calc
              ((cutPoints S (cuts i)).card : ℚ) ≤
                  ∑ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
                    ((componentPoints S Q).card : ℚ) := by exact_mod_cast hc
              _ ≤ ∑ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
                    affineDegree Q * dimensionSensitiveIncidenceProduct n A k b e :=
                Finset.sum_le_sum (fun Q hQ ↦ hchild i hiP Q hQ)
              _ = (∑ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
                    affineDegree Q) * dimensionSensitiveIncidenceProduct n A k b e := by
                rw [Finset.sum_mul]
              _ ≤ ((b : ℚ) * affineDegree P) *
                    dimensionSensitiveIncidenceProduct n A k b e :=
                mul_le_mul_of_nonneg_right hsdeg
                  (dimensionSensitiveIncidenceProduct_nonneg n A k b e)
              _ = (b : ℚ) * affineDegree P *
                    dimensionSensitiveIncidenceProduct n A k b e := rfl
          have hgoodcard : good.card = n - Bad.card := by
            rw [show good = Finset.univ \ Bad by ext i; simp [good]]
            rw [Finset.card_sdiff]
            simp
          have hupper : ∑ i ∈ good, ((cutPoints S (cuts i)).card : ℚ) ≤
              ((n - Bad.card : ℕ) : ℚ) * ((b : ℚ) * affineDegree P *
                dimensionSensitiveIncidenceProduct n A k b e) := by
            calc
              _ ≤ ∑ _i ∈ good, ((b : ℚ) * affineDegree P *
                    dimensionSensitiveIncidenceProduct n A k b e) :=
                Finset.sum_le_sum hone
              _ = _ := by simp [hgoodcard]
          have hden : (0 : ℚ) < (A - Bad.card : ℕ) := by
            exact_mod_cast Nat.sub_pos_of_lt (hBad.trans_lt (by omega : k - (e + 1) < A))
          have hratio := goodCuts_div_agreements_le_dimension (by omega) hed hBad hkA hAn
          have hlocal : ((n - Bad.card : ℕ) : ℚ) * b ≤
              R * (A - Bad.card : ℕ) := by
            refine (div_le_iff₀ hden).mp ?_
            dsimp only [R]
            calc
              ((n - Bad.card : ℕ) : ℚ) * b / (A - Bad.card : ℕ) =
                  (b : ℚ) * (((n - Bad.card : ℕ) : ℚ) /
                    (A - Bad.card : ℕ)) := by ring
              _ ≤ (b : ℚ) * (((n - k + e + 1 : ℕ) : ℚ) /
                    (A - k + e + 1 : ℕ)) :=
                mul_le_mul_of_nonneg_left hratio (by positivity)
              _ = (((n - k + e + 1) * b : ℕ) : ℚ) /
                    (A - k + e + 1 : ℕ) := by
                rw [Nat.cast_mul]
                ring
          apply le_of_mul_le_mul_right _ hden
          calc
            (S.card : ℚ) * (A - Bad.card : ℕ) ≤
                ∑ i ∈ good, ((cutPoints S (cuts i)).card : ℚ) := hlower
            _ ≤ ((n - Bad.card : ℕ) : ℚ) * ((b : ℚ) * affineDegree P *
                  dimensionSensitiveIncidenceProduct n A k b e) := hupper
            _ ≤ (affineDegree P * dimensionSensitiveIncidenceProduct n A k b (e + 1)) *
                  (A - Bad.card : ℕ) := by
              rw [dimensionSensitiveIncidenceProduct_succ]
              calc
                ((n - Bad.card : ℕ) : ℚ) * ((b : ℚ) * affineDegree P *
                    dimensionSensitiveIncidenceProduct n A k b e) =
                    (((n - Bad.card : ℕ) : ℚ) * b) *
                      (affineDegree P *
                        dimensionSensitiveIncidenceProduct n A k b e) := by ring
                _ ≤ (R * (A - Bad.card : ℕ)) *
                      (affineDegree P *
                        dimensionSensitiveIncidenceProduct n A k b e) :=
                  mul_le_mul_of_nonneg_right hlocal
                    (mul_nonneg (affineDegree_nonneg P)
                      (dimensionSensitiveIncidenceProduct_nonneg n A k b e))
                _ = (affineDegree P *
                      (dimensionSensitiveIncidenceProduct n A k b e * R)) *
                    (A - Bad.card : ℕ) := by ring

/-- Dimension-sensitive incidence outside a hereditary excluded locus.  At each retained prime,
the dimension-dependent cut budget may fail only when that prime's whole principal open lies in
the excluded set. -/
private theorem affineAgreementIncidence_bound_dimensionSensitive_off_excluded_aux
    {n A k b d : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (excluded : Set (σ → F))
    (hcomponent : ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (hilbertPolynomial Q).natDegree →
      (hilbertPolynomial Q).natDegree ≤ k ∧
        ((cutsInIdeal Q cuts).card ≤ k - (hilbertPolynomial Q).natDegree ∨
          principalOpenZeroLocus Q s ⊆ excluded))
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, x ∈ principalOpenZeroLocus P s ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card)
    (hd : (hilbertPolynomial P).natDegree = d) :
    (S.card : ℚ) ≤ affineDegree P * dimensionSensitiveIncidenceProduct n A k b d := by
  classical
  induction d using Nat.strong_induction_on generalizing P S with
  | h d ih =>
      by_cases hSempty : S = ∅
      · subst S
        simp only [Finset.card_empty, Nat.cast_zero]
        exact mul_nonneg (affineDegree_nonneg P)
          (dimensionSensitiveIncidenceProduct_nonneg n A k b d)
      obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hSempty
      cases d with
      | zero =>
          have ht := finite_zeroLocus_and_ncard_le_affineDegree (F := F) (E := F) P hd
          have hc : S.card ≤ (zeroLocus F P).ncard := by
            simpa using Set.ncard_le_ncard (fun x hx ↦ (hS x hx).1.1) ht.1
          have hc' : (S.card : ℚ) ≤ ((zeroLocus F P).ncard : ℚ) := by
            exact_mod_cast hc
          simpa using hc'.trans ht.2
      | succ e =>
          let Bad := cutsInIdeal P cuts
          let good := Finset.univ.filter fun i ↦ i ∉ Bad
          let R : ℚ := (((n - k + e + 1) * b : ℕ) : ℚ) /
            ((A - k + e + 1 : ℕ) : ℚ)
          have hdpos : 0 < (hilbertPolynomial P).natDegree := by rw [hd]; omega
          have hPcomponent := hcomponent P le_rfl hP hs hdpos
          have hed : e + 1 ≤ k := by simpa only [hd] using hPcomponent.1
          have hBad : Bad.card ≤ k - (e + 1) := by
            rcases hPcomponent.2 with hbound | hcovered
            · simpa only [Bad, hd] using hbound
            · exact False.elim ((hS x₀ hx₀).2 (hcovered (hS x₀ hx₀).1))
          have hlowerNat : S.card * (A - Bad.card) ≤
              ∑ i ∈ good, (cutPoints S (cuts i)).card := by
            exact finiteAgreementIncidence_lower_sharp S Bad
              (fun x i ↦ aeval x (cuts i) = 0) (fun x hx ↦ hA x hx)
          have hlower : (S.card : ℚ) * (A - Bad.card : ℕ) ≤
              ∑ i ∈ good, ((cutPoints S (cuts i)).card : ℚ) := by
            exact_mod_cast hlowerNat
          have hchild : ∀ i, cuts i ∉ P →
              ∀ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
                ((componentPoints S Q).card : ℚ) ≤ affineDegree Q *
                  dimensionSensitiveIncidenceProduct n A k b e := by
            intro i hiP Q hQ
            have hQdata := (Ideal.mem_retainedMinimalPrimes _ _ _).mp hQ
            have hQP : P ≤ Q := le_sup_left.trans hQdata.1.le
            have hQdegree : (hilbertPolynomial Q).natDegree = e := by
              have hpure := principalCut_component_hilbertPolynomial_natDegree_add_one
                hP hiP hQdata.1
              rw [hd] at hpure
              omega
            apply ih e (by omega) (P := Q) (S := componentPoints S Q)
              hQdata.1.isPrime hQdata.2
            · intro J hQJ hJ hsJ hdJ
              exact hcomponent J (hQP.trans hQJ) hJ hsJ hdJ
            · intro x hx
              rw [mem_componentPoints] at hx
              exact ⟨⟨hx.2, (hS x hx.1).1.2⟩, (hS x hx.1).2⟩
            · intro x hx
              rw [mem_componentPoints] at hx
              exact hA x hx.1
            · exact hQdegree
          have hone (i : Fin n) (hi : i ∈ good) :
              ((cutPoints S (cuts i)).card : ℚ) ≤
                b * affineDegree P * dimensionSensitiveIncidenceProduct n A k b e := by
            have hiP : cuts i ∉ P := by
              simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and,
                Bad, mem_cutsInIdeal] using hi
            have hc := card_filter_cut_le_sum_retained P s (cuts i) S (fun x hx ↦ (hS x hx).1)
            have hsdeg := sum_retained_affineDegree_le (s := s) hP hiP (hdeg i)
            calc
              ((cutPoints S (cuts i)).card : ℚ) ≤
                  ∑ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
                    ((componentPoints S Q).card : ℚ) := by exact_mod_cast hc
              _ ≤ ∑ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
                    affineDegree Q * dimensionSensitiveIncidenceProduct n A k b e :=
                Finset.sum_le_sum (fun Q hQ ↦ hchild i hiP Q hQ)
              _ = (∑ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
                    affineDegree Q) * dimensionSensitiveIncidenceProduct n A k b e := by
                rw [Finset.sum_mul]
              _ ≤ ((b : ℚ) * affineDegree P) *
                    dimensionSensitiveIncidenceProduct n A k b e :=
                mul_le_mul_of_nonneg_right hsdeg
                  (dimensionSensitiveIncidenceProduct_nonneg n A k b e)
              _ = (b : ℚ) * affineDegree P *
                    dimensionSensitiveIncidenceProduct n A k b e := rfl
          have hgoodcard : good.card = n - Bad.card := by
            rw [show good = Finset.univ \ Bad by ext i; simp [good]]
            rw [Finset.card_sdiff]
            simp
          have hupper : ∑ i ∈ good, ((cutPoints S (cuts i)).card : ℚ) ≤
              ((n - Bad.card : ℕ) : ℚ) * ((b : ℚ) * affineDegree P *
                dimensionSensitiveIncidenceProduct n A k b e) := by
            calc
              _ ≤ ∑ _i ∈ good, ((b : ℚ) * affineDegree P *
                    dimensionSensitiveIncidenceProduct n A k b e) :=
                Finset.sum_le_sum hone
              _ = _ := by simp [hgoodcard]
          have hden : (0 : ℚ) < (A - Bad.card : ℕ) := by
            exact_mod_cast Nat.sub_pos_of_lt (hBad.trans_lt (by omega : k - (e + 1) < A))
          have hratio := goodCuts_div_agreements_le_dimension (by omega) hed hBad hkA hAn
          have hlocal : ((n - Bad.card : ℕ) : ℚ) * b ≤
              R * (A - Bad.card : ℕ) := by
            refine (div_le_iff₀ hden).mp ?_
            dsimp only [R]
            calc
              ((n - Bad.card : ℕ) : ℚ) * b / (A - Bad.card : ℕ) =
                  (b : ℚ) * (((n - Bad.card : ℕ) : ℚ) /
                    (A - Bad.card : ℕ)) := by ring
              _ ≤ (b : ℚ) * (((n - k + e + 1 : ℕ) : ℚ) /
                    (A - k + e + 1 : ℕ)) :=
                mul_le_mul_of_nonneg_left hratio (by positivity)
              _ = (((n - k + e + 1) * b : ℕ) : ℚ) /
                    (A - k + e + 1 : ℕ) := by
                rw [Nat.cast_mul]
                ring
          apply le_of_mul_le_mul_right _ hden
          calc
            (S.card : ℚ) * (A - Bad.card : ℕ) ≤
                ∑ i ∈ good, ((cutPoints S (cuts i)).card : ℚ) := hlower
            _ ≤ ((n - Bad.card : ℕ) : ℚ) * ((b : ℚ) * affineDegree P *
                  dimensionSensitiveIncidenceProduct n A k b e) := hupper
            _ ≤ (affineDegree P * dimensionSensitiveIncidenceProduct n A k b (e + 1)) *
                  (A - Bad.card : ℕ) := by
              rw [dimensionSensitiveIncidenceProduct_succ]
              calc
                ((n - Bad.card : ℕ) : ℚ) * ((b : ℚ) * affineDegree P *
                    dimensionSensitiveIncidenceProduct n A k b e) =
                    (((n - Bad.card : ℕ) : ℚ) * b) *
                      (affineDegree P *
                        dimensionSensitiveIncidenceProduct n A k b e) := by ring
                _ ≤ (R * (A - Bad.card : ℕ)) *
                      (affineDegree P *
                        dimensionSensitiveIncidenceProduct n A k b e) :=
                  mul_le_mul_of_nonneg_right hlocal
                    (mul_nonneg (affineDegree_nonneg P)
                      (dimensionSensitiveIncidenceProduct_nonneg n A k b e))
                _ = (affineDegree P *
                      (dimensionSensitiveIncidenceProduct n A k b e * R)) *
                    (A - Bad.card : ℕ) := by ring

/-- Hybrid joint incidence: terminal graph components are excluded in dimension one, while
higher-dimensional retained components use the coefficient-space dimension budget. -/
private theorem affineAgreementIncidence_bound_hybrid_off_excluded_aux
    {n A L k b d : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hLA : L ≤ A) (hkA : k ≤ A) (hAn : A ≤ n)
    (excluded : Set (σ → F))
    (hdimension : ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (hilbertPolynomial Q).natDegree →
      (hilbertPolynomial Q).natDegree ≤ k + 1 ∧
        (1 < (hilbertPolynomial Q).natDegree →
          (cutsInIdeal Q cuts).card ≤ k + 1 - (hilbertPolynomial Q).natDegree))
    (hterminal : ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (hilbertPolynomial Q).natDegree →
      L ≤ (cutsInIdeal Q cuts).card → principalOpenZeroLocus Q s ⊆ excluded)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, x ∈ principalOpenZeroLocus P s ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card)
    (hd : (hilbertPolynomial P).natDegree = d) :
    (S.card : ℚ) ≤ affineDegree P * hybridDimensionSensitiveIncidenceProduct n A L k b d := by
  classical
  induction d using Nat.strong_induction_on generalizing P S with
  | h d ih =>
      by_cases hSempty : S = ∅
      · subst S
        simp only [Finset.card_empty, Nat.cast_zero]
        exact mul_nonneg (affineDegree_nonneg P)
          (hybridDimensionSensitiveIncidenceProduct_nonneg n A L k b d)
      obtain ⟨x₀, hx₀⟩ := Finset.nonempty_iff_ne_empty.mpr hSempty
      cases d with
      | zero =>
          have ht := finite_zeroLocus_and_ncard_le_affineDegree (F := F) (E := F) P hd
          have hc : S.card ≤ (zeroLocus F P).ncard := by
            simpa using Set.ncard_le_ncard (fun x hx ↦ (hS x hx).1.1) ht.1
          have hc' : (S.card : ℚ) ≤ ((zeroLocus F P).ncard : ℚ) := by
            exact_mod_cast hc
          simpa using hc'.trans ht.2
      | succ e =>
          let Bad := cutsInIdeal P cuts
          let T := if e = 0 then L else k + 1 - e
          let good := Finset.univ.filter fun i ↦ i ∉ Bad
          let R : ℚ := (((n - T + 1) * b : ℕ) : ℚ) /
            ((A - T + 1 : ℕ) : ℚ)
          have hdpos : 0 < (hilbertPolynomial P).natDegree := by rw [hd]; omega
          have hPdimension := hdimension P le_rfl hP hs hdpos
          have hBad : Bad.card < T := by
            by_cases he : e = 0
            · subst e
              simp only [T, if_pos]
              by_contra hnot
              have hcovered := hterminal P le_rfl hP hs hdpos
                (by simpa only [Bad] using Nat.le_of_not_gt hnot)
              exact (hS x₀ hx₀).2 (hcovered (hS x₀ hx₀).1)
            · simp only [T, if_neg he]
              have hbound := hPdimension.2 (by rw [hd]; omega)
              rw [hd] at hbound
              change Bad.card ≤ k + 1 - (e + 1) at hbound
              omega
          have hTA : T ≤ A := by
            by_cases he : e = 0
            · simp only [T, if_pos he]
              exact hLA
            · simp only [T, if_neg he]
              have hedim : e + 1 ≤ k + 1 := by simpa only [hd] using hPdimension.1
              omega
          have hlowerNat : S.card * (A - Bad.card) ≤
              ∑ i ∈ good, (cutPoints S (cuts i)).card := by
            exact finiteAgreementIncidence_lower_sharp S Bad
              (fun x i ↦ aeval x (cuts i) = 0) (fun x hx ↦ hA x hx)
          have hlower : (S.card : ℚ) * (A - Bad.card : ℕ) ≤
              ∑ i ∈ good, ((cutPoints S (cuts i)).card : ℚ) := by
            exact_mod_cast hlowerNat
          have hchild : ∀ i, cuts i ∉ P →
              ∀ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
                ((componentPoints S Q).card : ℚ) ≤ affineDegree Q *
                  hybridDimensionSensitiveIncidenceProduct n A L k b e := by
            intro i hiP Q hQ
            have hQdata := (Ideal.mem_retainedMinimalPrimes _ _ _).mp hQ
            have hQP : P ≤ Q := le_sup_left.trans hQdata.1.le
            have hQdegree : (hilbertPolynomial Q).natDegree = e := by
              have hpure := principalCut_component_hilbertPolynomial_natDegree_add_one
                hP hiP hQdata.1
              rw [hd] at hpure
              omega
            apply ih e (by omega) (P := Q) (S := componentPoints S Q)
              hQdata.1.isPrime hQdata.2
            · intro J hQJ hJ hsJ hdJ
              exact hdimension J (hQP.trans hQJ) hJ hsJ hdJ
            · intro J hQJ hJ hsJ hdJ hcutsJ
              exact hterminal J (hQP.trans hQJ) hJ hsJ hdJ hcutsJ
            · intro x hx
              rw [mem_componentPoints] at hx
              exact ⟨⟨hx.2, (hS x hx.1).1.2⟩, (hS x hx.1).2⟩
            · intro x hx
              rw [mem_componentPoints] at hx
              exact hA x hx.1
            · exact hQdegree
          have hone (i : Fin n) (hi : i ∈ good) :
              ((cutPoints S (cuts i)).card : ℚ) ≤
                b * affineDegree P * hybridDimensionSensitiveIncidenceProduct n A L k b e := by
            have hiP : cuts i ∉ P := by
              simpa only [good, Finset.mem_filter, Finset.mem_univ, true_and,
                Bad, mem_cutsInIdeal] using hi
            have hc := card_filter_cut_le_sum_retained P s (cuts i) S (fun x hx ↦ (hS x hx).1)
            have hsdeg := sum_retained_affineDegree_le (s := s) hP hiP (hdeg i)
            calc
              ((cutPoints S (cuts i)).card : ℚ) ≤
                  ∑ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
                    ((componentPoints S Q).card : ℚ) := by exact_mod_cast hc
              _ ≤ ∑ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
                    affineDegree Q * hybridDimensionSensitiveIncidenceProduct n A L k b e :=
                Finset.sum_le_sum (fun Q hQ ↦ hchild i hiP Q hQ)
              _ = (∑ Q ∈ (P ⊔ Ideal.span {cuts i}).retainedMinimalPrimes s,
                    affineDegree Q) * hybridDimensionSensitiveIncidenceProduct n A L k b e := by
                rw [Finset.sum_mul]
              _ ≤ ((b : ℚ) * affineDegree P) *
                    hybridDimensionSensitiveIncidenceProduct n A L k b e :=
                mul_le_mul_of_nonneg_right hsdeg
                  (hybridDimensionSensitiveIncidenceProduct_nonneg n A L k b e)
              _ = (b : ℚ) * affineDegree P *
                    hybridDimensionSensitiveIncidenceProduct n A L k b e := rfl
          have hgoodcard : good.card = n - Bad.card := by
            rw [show good = Finset.univ \ Bad by ext i; simp [good]]
            rw [Finset.card_sdiff]
            simp
          have hupper : ∑ i ∈ good, ((cutPoints S (cuts i)).card : ℚ) ≤
              ((n - Bad.card : ℕ) : ℚ) * ((b : ℚ) * affineDegree P *
                hybridDimensionSensitiveIncidenceProduct n A L k b e) := by
            calc
              _ ≤ ∑ _i ∈ good, ((b : ℚ) * affineDegree P *
                    hybridDimensionSensitiveIncidenceProduct n A L k b e) :=
                Finset.sum_le_sum hone
              _ = _ := by simp [hgoodcard]
          have hden : (0 : ℚ) < (A - Bad.card : ℕ) := by
            exact_mod_cast Nat.sub_pos_of_lt (hBad.trans_le hTA)
          have hratio := goodCuts_div_agreements_le hBad hTA hAn
          have hlocal : ((n - Bad.card : ℕ) : ℚ) * b ≤
              R * (A - Bad.card : ℕ) := by
            refine (div_le_iff₀ hden).mp ?_
            dsimp only [R]
            calc
              ((n - Bad.card : ℕ) : ℚ) * b / (A - Bad.card : ℕ) =
                  (b : ℚ) * (((n - Bad.card : ℕ) : ℚ) /
                    (A - Bad.card : ℕ)) := by ring
              _ ≤ (b : ℚ) * (((n - T + 1 : ℕ) : ℚ) /
                    (A - T + 1 : ℕ)) :=
                mul_le_mul_of_nonneg_left hratio (by positivity)
              _ = (((n - T + 1) * b : ℕ) : ℚ) /
                    (A - T + 1 : ℕ) := by
                rw [Nat.cast_mul]
                ring
          apply le_of_mul_le_mul_right _ hden
          calc
            (S.card : ℚ) * (A - Bad.card : ℕ) ≤
                ∑ i ∈ good, ((cutPoints S (cuts i)).card : ℚ) := hlower
            _ ≤ ((n - Bad.card : ℕ) : ℚ) * ((b : ℚ) * affineDegree P *
                  hybridDimensionSensitiveIncidenceProduct n A L k b e) := hupper
            _ ≤ (affineDegree P * hybridDimensionSensitiveIncidenceProduct n A L k b (e + 1)) *
                  (A - Bad.card : ℕ) := by
              rw [hybridDimensionSensitiveIncidenceProduct_succ]
              calc
                ((n - Bad.card : ℕ) : ℚ) * ((b : ℚ) * affineDegree P *
                    hybridDimensionSensitiveIncidenceProduct n A L k b e) =
                    (((n - Bad.card : ℕ) : ℚ) * b) *
                      (affineDegree P *
                        hybridDimensionSensitiveIncidenceProduct n A L k b e) := by ring
                _ ≤ (R * (A - Bad.card : ℕ)) *
                      (affineDegree P *
                        hybridDimensionSensitiveIncidenceProduct n A L k b e) :=
                  mul_le_mul_of_nonneg_right hlocal
                    (mul_nonneg (affineDegree_nonneg P)
                      (hybridDimensionSensitiveIncidenceProduct_nonneg n A L k b e))
                _ = (affineDegree P *
                      (hybridDimensionSensitiveIncidenceProduct n A L k b e * R)) *
                    (A - Bad.card : ℕ) := by ring

/-- A finite set on an affine principal-open component satisfies the dimension-sensitive
product bound once the component bound on identically vanishing cuts is proved hereditarily. -/
theorem affineAgreementIncidence_bound_dimensionSensitive
    {n A k b : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (hcomponent : ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (hilbertPolynomial Q).natDegree →
      (hilbertPolynomial Q).natDegree ≤ k ∧
        (cutsInIdeal Q cuts).card ≤ k - (hilbertPolynomial Q).natDegree)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, x ∈ zeroLocus F P ∧ aeval x s ≠ 0)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card) :
    (S.card : ℚ) ≤ affineDegree P *
      dimensionSensitiveIncidenceProduct n A k b (hilbertPolynomial P).natDegree := by
  exact affineAgreementIncidence_bound_dimensionSensitive_aux hP hs cuts hdeg hkA hAn
    hcomponent S hS hA rfl

/-- A finite set outside an excluded locus satisfies the dimension-sensitive product bound.
The component cut budget is required at every retained prime unless that prime's entire regular
principal open is already excluded. -/
theorem affineAgreementIncidence_bound_dimensionSensitive_off_excluded
    {n A k b : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (excluded : Set (σ → F))
    (hcomponent : ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (hilbertPolynomial Q).natDegree →
      (hilbertPolynomial Q).natDegree ≤ k ∧
        ((cutsInIdeal Q cuts).card ≤ k - (hilbertPolynomial Q).natDegree ∨
          principalOpenZeroLocus Q s ⊆ excluded))
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, x ∈ principalOpenZeroLocus P s ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card) :
    (S.card : ℚ) ≤ affineDegree P *
      dimensionSensitiveIncidenceProduct n A k b (hilbertPolynomial P).natDegree := by
  exact affineAgreementIncidence_bound_dimensionSensitive_off_excluded_aux hP hs cuts hdeg
    hkA hAn excluded hcomponent S hS hA rfl

/-- Hybrid finite incidence bound.  Dimension one uses the excluded-locus threshold `L`, while
dimensions at least two use the joint coefficient-space budget `k + 1 - dim`. -/
theorem affineAgreementIncidence_bound_hybrid_off_excluded
    {n A L k b : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hLA : L ≤ A) (hkA : k ≤ A) (hAn : A ≤ n)
    (excluded : Set (σ → F))
    (hdimension : ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (hilbertPolynomial Q).natDegree →
      (hilbertPolynomial Q).natDegree ≤ k + 1 ∧
        (1 < (hilbertPolynomial Q).natDegree →
          (cutsInIdeal Q cuts).card ≤ k + 1 - (hilbertPolynomial Q).natDegree))
    (hterminal : ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (hilbertPolynomial Q).natDegree →
      L ≤ (cutsInIdeal Q cuts).card → principalOpenZeroLocus Q s ⊆ excluded)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S, x ∈ principalOpenZeroLocus P s ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card) :
    (S.card : ℚ) ≤ affineDegree P *
      hybridDimensionSensitiveIncidenceProduct n A L k b
        (hilbertPolynomial P).natDegree := by
  exact affineAgreementIncidence_bound_hybrid_off_excluded_aux hP hs cuts hdeg
    hLA hkA hAn excluded hdimension hterminal S hS hA rfl

/-- The full agreement locus on a principal-open prime component is finite and satisfies the
same dimension-sensitive bound as each of its finite subsets.  This is the form needed before
projecting a retained source family to its challenge coordinates. -/
theorem finite_agreementLocus_and_ncard_le_dimensionSensitive
    {n A k b : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (hcomponent : ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (hilbertPolynomial Q).natDegree →
      (hilbertPolynomial Q).natDegree ≤ k ∧
        (cutsInIdeal Q cuts).card ≤ k - (hilbertPolynomial Q).natDegree) :
    let T := {x : σ → F | x ∈ principalOpenZeroLocus P s ∧
      A ≤ (agreementIndices cuts x).card}
    T.Finite ∧ (T.ncard : ℚ) ≤ affineDegree P *
      dimensionSensitiveIncidenceProduct n A k b (hilbertPolynomial P).natDegree := by
  classical
  dsimp only
  let T := {x : σ → F | x ∈ principalOpenZeroLocus P s ∧
    A ≤ (agreementIndices cuts x).card}
  have hbound (S : Finset (σ → F)) (hST : (S : Set (σ → F)) ⊆ T) :
      (S.card : ℚ) ≤ affineDegree P *
        dimensionSensitiveIncidenceProduct n A k b (hilbertPolynomial P).natDegree := by
    apply affineAgreementIncidence_bound_dimensionSensitive hP hs cuts hdeg hkA hAn
      hcomponent S
    · intro x hx
      exact (hST hx).1
    · intro x hx
      exact (hST hx).2
  have hfinite : T.Finite := Set.finite_of_forall_finset_card_le hbound
  refine ⟨hfinite, ?_⟩
  rw [Set.ncard_eq_toFinset_card T hfinite]
  exact hbound hfinite.toFinset (fun _ hx ↦ hfinite.mem_toFinset.mp hx)

/-- The full high-agreement locus outside an excluded set is finite and satisfies the
dimension-sensitive product bound. -/
theorem finite_agreementLocus_off_excluded_and_ncard_le_dimensionSensitive
    {n A k b : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hkA : k ≤ A) (hAn : A ≤ n)
    (excluded : Set (σ → F))
    (hcomponent : ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (hilbertPolynomial Q).natDegree →
      (hilbertPolynomial Q).natDegree ≤ k ∧
        ((cutsInIdeal Q cuts).card ≤ k - (hilbertPolynomial Q).natDegree ∨
          principalOpenZeroLocus Q s ⊆ excluded)) :
    let T := {x : σ → F | x ∈ principalOpenZeroLocus P s ∧ x ∉ excluded ∧
      A ≤ (agreementIndices cuts x).card}
    T.Finite ∧ (T.ncard : ℚ) ≤ affineDegree P *
      dimensionSensitiveIncidenceProduct n A k b (hilbertPolynomial P).natDegree := by
  classical
  dsimp only
  let T := {x : σ → F | x ∈ principalOpenZeroLocus P s ∧ x ∉ excluded ∧
    A ≤ (agreementIndices cuts x).card}
  have hbound (S : Finset (σ → F)) (hST : (S : Set (σ → F)) ⊆ T) :
      (S.card : ℚ) ≤ affineDegree P *
        dimensionSensitiveIncidenceProduct n A k b (hilbertPolynomial P).natDegree := by
    apply affineAgreementIncidence_bound_dimensionSensitive_off_excluded hP hs cuts hdeg
      hkA hAn excluded hcomponent S
    · intro x hx
      exact ⟨(hST hx).1, (hST hx).2.1⟩
    · intro x hx
      exact (hST hx).2.2
  have hfinite : T.Finite := Set.finite_of_forall_finset_card_le hbound
  refine ⟨hfinite, ?_⟩
  rw [Set.ncard_eq_toFinset_card T hfinite]
  exact hbound hfinite.toFinset (fun _ hx ↦ hfinite.mem_toFinset.mp hx)

/-- The full high-agreement locus outside the terminal graph locus is finite and obeys the
hybrid dimension-sensitive product. -/
theorem finite_agreementLocus_off_excluded_and_ncard_le_hybrid
    {n A L k b : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hLA : L ≤ A) (hkA : k ≤ A) (hAn : A ≤ n)
    (excluded : Set (σ → F))
    (hdimension : ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (hilbertPolynomial Q).natDegree →
      (hilbertPolynomial Q).natDegree ≤ k + 1 ∧
        (1 < (hilbertPolynomial Q).natDegree →
          (cutsInIdeal Q cuts).card ≤ k + 1 - (hilbertPolynomial Q).natDegree))
    (hterminal : ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (hilbertPolynomial Q).natDegree →
      L ≤ (cutsInIdeal Q cuts).card → principalOpenZeroLocus Q s ⊆ excluded) :
    let T := {x : σ → F | x ∈ principalOpenZeroLocus P s ∧ x ∉ excluded ∧
      A ≤ (agreementIndices cuts x).card}
    T.Finite ∧ (T.ncard : ℚ) ≤ affineDegree P *
      hybridDimensionSensitiveIncidenceProduct n A L k b
        (hilbertPolynomial P).natDegree := by
  classical
  dsimp only
  let T := {x : σ → F | x ∈ principalOpenZeroLocus P s ∧ x ∉ excluded ∧
    A ≤ (agreementIndices cuts x).card}
  have hbound (S : Finset (σ → F)) (hST : (S : Set (σ → F)) ⊆ T) :
      (S.card : ℚ) ≤ affineDegree P *
        hybridDimensionSensitiveIncidenceProduct n A L k b
          (hilbertPolynomial P).natDegree := by
    apply affineAgreementIncidence_bound_hybrid_off_excluded hP hs cuts hdeg
      hLA hkA hAn excluded hdimension hterminal S
    · intro x hx
      exact ⟨(hST hx).1, (hST hx).2.1⟩
    · intro x hx
      exact (hST hx).2.2
  have hfinite : T.Finite := Set.finite_of_forall_finset_card_le hbound
  refine ⟨hfinite, ?_⟩
  rw [Set.ncard_eq_toFinset_card T hfinite]
  exact hbound hfinite.toFinset (fun _ hx ↦ hfinite.mem_toFinset.mp hx)

/-- First-order joint specialization of the hybrid finite bound.  Components of dimension at
most two are uniformly charged by the graph-recognition factor and the direct coefficient-space
factor. -/
theorem finite_agreementLocus_off_excluded_and_ncard_le_hybrid_two
    {n A L k b : ℕ} {P : Ideal (MvPolynomial σ F)} (hP : P.IsPrime)
    {s : MvPolynomial σ F} (hs : s ∉ P)
    (cuts : Fin n → MvPolynomial σ F) (hdeg : ∀ i, (cuts i).totalDegree ≤ b)
    (hLA : L ≤ A) (hkA : k ≤ A) (hAn : A ≤ n) (hb : 0 < b)
    (hPdim : (hilbertPolynomial P).natDegree ≤ 2)
    (excluded : Set (σ → F))
    (hdimension : ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (hilbertPolynomial Q).natDegree →
      (hilbertPolynomial Q).natDegree ≤ k + 1 ∧
        (1 < (hilbertPolynomial Q).natDegree →
          (cutsInIdeal Q cuts).card ≤ k + 1 - (hilbertPolynomial Q).natDegree))
    (hterminal : ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      0 < (hilbertPolynomial Q).natDegree →
      L ≤ (cutsInIdeal Q cuts).card → principalOpenZeroLocus Q s ⊆ excluded) :
    let T := {x : σ → F | x ∈ principalOpenZeroLocus P s ∧ x ∉ excluded ∧
      A ≤ (agreementIndices cuts x).card}
    T.Finite ∧ (T.ncard : ℚ) ≤ affineDegree P *
      (((((n - L + 1) * b : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ))) *
        (((((n - k + 1) * b : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ))) := by
  dsimp only
  obtain ⟨hfinite, hbound⟩ := finite_agreementLocus_off_excluded_and_ncard_le_hybrid
    hP hs cuts hdeg hLA hkA hAn excluded hdimension hterminal
  refine ⟨hfinite, hbound.trans ?_⟩
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    (hybridDimensionSensitiveIncidenceProduct_le_two hPdim hLA hkA hAn hb)
      (affineDegree_nonneg P)

/-- Arbitrary-dimensional hybrid incidence after a finite list of fixed nonlinear cuts. The
fixed cuts contribute `B^d` through the retained-family degree potential; the later affine-linear
agreement cuts contribute the terminal factor at `L` followed by the dimension-sensitive
coefficient-space product. -/
theorem iteratedRetainedCutFamily_incidence_off_excluded_hybrid
    {n A L k B d : ℕ} (T₀ : Finset (Ideal (MvPolynomial σ F)))
    (s : MvPolynomial σ F)
    (hprime : ∀ P ∈ T₀, P.IsPrime) (hopen : ∀ P ∈ T₀, s ∉ P)
    (hdim : ∀ P ∈ T₀, (hilbertPolynomial P).natDegree = d)
    {V : ℚ} (hsum : ∑ P ∈ T₀, affineDegree P ≤ V)
    (highCuts : List (MvPolynomial σ F))
    (hhighDegree : ∀ f ∈ highCuts, f.totalDegree ≤ B) (hB : 0 < B)
    (cuts : Fin n → MvPolynomial σ F) (hcutsDegree : ∀ i, (cuts i).totalDegree ≤ 1)
    (hLA : L ≤ A) (hkA : k ≤ A) (hAn : A ≤ n)
    (excluded : Set (σ → F))
    (hdimension : ∀ P ∈ T₀, ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      (∀ f ∈ highCuts, f ∈ Q) →
      0 < (hilbertPolynomial Q).natDegree →
      (hilbertPolynomial Q).natDegree ≤ k + 1 ∧
        (1 < (hilbertPolynomial Q).natDegree →
          (cutsInIdeal Q cuts).card ≤ k + 1 - (hilbertPolynomial Q).natDegree))
    (hterminal : ∀ P ∈ T₀, ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      (∀ f ∈ highCuts, f ∈ Q) →
      0 < (hilbertPolynomial Q).natDegree →
      L ≤ (cutsInIdeal Q cuts).card → principalOpenZeroLocus Q s ⊆ excluded)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S,
      (∃ P ∈ T₀, x ∈ zeroLocus F P) ∧ aeval x s ≠ 0 ∧
        (∀ f ∈ highCuts, aeval x f = 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card) :
    (S.card : ℚ) ≤ V * (B : ℚ) ^ d *
      hybridDimensionSensitiveIncidenceProduct n A L k 1 (min (d - 1) k + 1) := by
  classical
  let T := iteratedRetainedCutFamily T₀ s highCuts
  have hT (Q : Ideal (MvPolynomial σ F)) (hQ : Q ∈ T) :
      Q.IsPrime ∧ s ∉ Q ∧ (∀ f ∈ highCuts, f ∈ Q) ∧ ∃ P ∈ T₀, P ≤ Q := by
    have hpo := iteratedRetainedCutFamily_prime_open T₀ hprime hopen highCuts Q hQ
    obtain ⟨P, hP, hPQ, hhigh⟩ := mem_iteratedRetainedCutFamily_contains T₀ highCuts hQ
    exact ⟨hpo.1, hpo.2, hhigh, P, hP, hPQ⟩
  have hTdim (Q : Ideal (MvPolynomial σ F)) (hQ : Q ∈ T) :
      (hilbertPolynomial Q).natDegree ≤ d := by
    obtain ⟨hQprime, _, _, P, hP, hPQ⟩ := hT Q hQ
    exact (hilbertPolynomial_degree_and_leadingCoeff_antitone hPQ hQprime.ne_top).1
      |>.trans_eq (hdim P hP)
  have hpotential :
      ∑ Q ∈ T, affineDegree Q * (B : ℚ) ^ (hilbertPolynomial Q).natDegree ≤
        V * (B : ℚ) ^ d := by
    exact (sum_iteratedRetainedCutFamily_affineDegree_mul_pow_le T₀ hprime hopen
      (Nat.succ_le_iff.mpr hB) highCuts hhighDegree).trans (by
        calc
          ∑ P ∈ T₀, affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree =
              (∑ P ∈ T₀, affineDegree P) * (B : ℚ) ^ d := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro P hP
            rw [hdim P hP]
          _ ≤ V * (B : ℚ) ^ d :=
            mul_le_mul_of_nonneg_right hsum (by positivity))
  have hcover : S.card ≤ ∑ Q ∈ T, (componentPoints S Q).card := by
    apply le_trans _ Finset.card_biUnion_le
    apply Finset.card_le_card
    intro x hx
    obtain ⟨P, hP, hxP⟩ := (hS x hx).1
    obtain ⟨Q, hQ, hxQ⟩ := exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus T₀
      highCuts x ⟨P, hP, hxP⟩ (hS x hx).2.1 (hS x hx).2.2.1
    exact Finset.mem_biUnion.mpr ⟨Q, hQ, by rw [mem_componentPoints]; exact ⟨hx, hxQ⟩⟩
  let R := hybridDimensionSensitiveIncidenceProduct n A L k 1 (min (d - 1) k + 1)
  have hcomponent (Q : Ideal (MvPolynomial σ F)) (hQ : Q ∈ T) :
      ((componentPoints S Q).card : ℚ) ≤ affineDegree Q * R := by
    obtain ⟨hQprime, hsQ, hhighQ, P, hP, hPQ⟩ := hT Q hQ
    have hbound := affineAgreementIncidence_bound_hybrid_off_excluded hQprime hsQ
      cuts hcutsDegree hLA hkA hAn excluded
      (fun J hQJ hJ hsJ hdJ ↦ hdimension P hP J (hPQ.trans hQJ) hJ hsJ
        (fun f hf ↦ hQJ (hhighQ f hf)) hdJ)
      (fun J hQJ hJ hsJ hdJ hcJ ↦ hterminal P hP J
        (hPQ.trans hQJ) hJ hsJ (fun f hf ↦ hQJ (hhighQ f hf)) hdJ hcJ)
      (componentPoints S Q)
      (fun x hx ↦ by
        rw [mem_componentPoints] at hx
        exact ⟨⟨hx.2, (hS x hx.1).2.1⟩, (hS x hx.1).2.2.2⟩)
      (fun x hx ↦ by rw [mem_componentPoints] at hx; exact hA x hx.1)
    refine hbound.trans (mul_le_mul_of_nonneg_left ?_ (affineDegree_nonneg Q))
    apply hybridDimensionSensitiveIncidenceProduct_mono_dimension hLA hkA hAn
      Nat.zero_lt_one
    by_cases hQzero : (hilbertPolynomial Q).natDegree = 0
    · omega
    · have hQpos : 0 < (hilbertPolynomial Q).natDegree := Nat.pos_of_ne_zero hQzero
      have hkdim := (hdimension P hP Q hPQ hQprime hsQ hhighQ hQpos).1
      have hddim := hTdim Q hQ
      omega
  have hdegreeSum : ∑ Q ∈ T, affineDegree Q ≤ V * (B : ℚ) ^ d := by
    calc
      ∑ Q ∈ T, affineDegree Q ≤
          ∑ Q ∈ T, affineDegree Q * (B : ℚ) ^ (hilbertPolynomial Q).natDegree := by
        apply Finset.sum_le_sum
        intro Q hQ
        exact le_mul_of_one_le_right (affineDegree_nonneg Q)
          (one_le_pow₀ (by exact_mod_cast hB))
      _ ≤ V * (B : ℚ) ^ d := hpotential
  calc
    (S.card : ℚ) ≤ ∑ Q ∈ T, ((componentPoints S Q).card : ℚ) := by exact_mod_cast hcover
    _ ≤ ∑ Q ∈ T, affineDegree Q * R := Finset.sum_le_sum hcomponent
    _ = (∑ Q ∈ T, affineDegree Q) * R := by rw [Finset.sum_mul]
    _ ≤ (V * (B : ℚ) ^ d) * R :=
      mul_le_mul_of_nonneg_right hdegreeSum
        (hybridDimensionSensitiveIncidenceProduct_nonneg n A L k 1 (min (d - 1) k + 1))
    _ = _ := rfl

/-- First-order hybrid incidence after a finite list of fixed nonlinear cuts.  The nonlinear
cuts contribute their degree bound `B` through the retained-family potential, while the later
agreement cuts are affine-linear and therefore contribute only the two sharp incidence ratios.
This separation is the form used by the bidegree presentation. -/
theorem iteratedRetainedCutFamily_incidence_off_excluded_hybrid_two
    {n A L k B : ℕ} (T₀ : Finset (Ideal (MvPolynomial σ F)))
    (s : MvPolynomial σ F)
    (hprime : ∀ P ∈ T₀, P.IsPrime) (hopen : ∀ P ∈ T₀, s ∉ P)
    (hdim : ∀ P ∈ T₀, (hilbertPolynomial P).natDegree = 2)
    {V : ℚ} (hsum : ∑ P ∈ T₀, affineDegree P ≤ V)
    (highCuts : List (MvPolynomial σ F))
    (hhighDegree : ∀ f ∈ highCuts, f.totalDegree ≤ B) (hB : 0 < B)
    (cuts : Fin n → MvPolynomial σ F) (hcutsDegree : ∀ i, (cuts i).totalDegree ≤ 1)
    (hLA : L ≤ A) (hkA : k ≤ A) (hAn : A ≤ n)
    (excluded : Set (σ → F))
    (hdimension : ∀ P ∈ T₀, ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      (∀ f ∈ highCuts, f ∈ Q) →
      0 < (hilbertPolynomial Q).natDegree →
      (hilbertPolynomial Q).natDegree ≤ k + 1 ∧
        (1 < (hilbertPolynomial Q).natDegree →
          (cutsInIdeal Q cuts).card ≤ k + 1 - (hilbertPolynomial Q).natDegree))
    (hterminal : ∀ P ∈ T₀, ∀ Q : Ideal (MvPolynomial σ F),
      P ≤ Q → Q.IsPrime → s ∉ Q →
      (∀ f ∈ highCuts, f ∈ Q) →
      0 < (hilbertPolynomial Q).natDegree →
      L ≤ (cutsInIdeal Q cuts).card → principalOpenZeroLocus Q s ⊆ excluded)
    (S : Finset (σ → F))
    (hS : ∀ x ∈ S,
      (∃ P ∈ T₀, x ∈ zeroLocus F P) ∧ aeval x s ≠ 0 ∧
        (∀ f ∈ highCuts, aeval x f = 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card) :
    (S.card : ℚ) ≤ V * (B : ℚ) ^ 2 *
      (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
        (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  classical
  let T := iteratedRetainedCutFamily T₀ s highCuts
  have hT (Q : Ideal (MvPolynomial σ F)) (hQ : Q ∈ T) :
      Q.IsPrime ∧ s ∉ Q ∧ (∀ f ∈ highCuts, f ∈ Q) ∧ ∃ P ∈ T₀, P ≤ Q := by
    have hpo := iteratedRetainedCutFamily_prime_open T₀ hprime hopen highCuts Q hQ
    obtain ⟨P, hP, hPQ, hhigh⟩ := mem_iteratedRetainedCutFamily_contains T₀ highCuts hQ
    exact ⟨hpo.1, hpo.2, hhigh, P, hP, hPQ⟩
  have hTdim (Q : Ideal (MvPolynomial σ F)) (hQ : Q ∈ T) :
      (hilbertPolynomial Q).natDegree ≤ 2 := by
    obtain ⟨_, _, _, P, hP, hPQ⟩ := hT Q hQ
    exact (hilbertPolynomial_degree_and_leadingCoeff_antitone hPQ (hT Q hQ).1.ne_top).1
      |>.trans_eq (hdim P hP)
  have hpotential :
      ∑ Q ∈ T, affineDegree Q * (B : ℚ) ^ (hilbertPolynomial Q).natDegree ≤
        V * (B : ℚ) ^ 2 := by
    exact (sum_iteratedRetainedCutFamily_affineDegree_mul_pow_le T₀ hprime hopen
      (Nat.succ_le_iff.mpr hB) highCuts hhighDegree).trans (by
        calc
          ∑ P ∈ T₀, affineDegree P * (B : ℚ) ^ (hilbertPolynomial P).natDegree =
              (∑ P ∈ T₀, affineDegree P) * (B : ℚ) ^ 2 := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro P hP
            rw [hdim P hP]
          _ ≤ V * (B : ℚ) ^ 2 :=
            mul_le_mul_of_nonneg_right hsum (by positivity))
  have hcover : S.card ≤ ∑ Q ∈ T, (componentPoints S Q).card := by
    apply le_trans _ Finset.card_biUnion_le
    apply Finset.card_le_card
    intro x hx
    obtain ⟨P, hP, hxP⟩ := (hS x hx).1
    obtain ⟨Q, hQ, hxQ⟩ := exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus T₀
      highCuts x ⟨P, hP, hxP⟩ (hS x hx).2.1 (hS x hx).2.2.1
    exact Finset.mem_biUnion.mpr ⟨Q, hQ, by rw [mem_componentPoints]; exact ⟨hx, hxQ⟩⟩
  let R : ℚ :=
    (((n - L + 1 : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) *
      (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ))
  have hcomponent (Q : Ideal (MvPolynomial σ F)) (hQ : Q ∈ T) :
      ((componentPoints S Q).card : ℚ) ≤ affineDegree Q * R := by
    obtain ⟨hQprime, hsQ, hhighQ, P, hP, hPQ⟩ := hT Q hQ
    have hbound := affineAgreementIncidence_bound_hybrid_off_excluded hQprime hsQ
      cuts hcutsDegree hLA hkA hAn excluded
      (fun J hQJ hJ hsJ hdJ ↦ hdimension P hP J (hPQ.trans hQJ) hJ hsJ
        (fun f hf ↦ hQJ (hhighQ f hf)) hdJ)
      (fun J hQJ hJ hsJ hdJ hcJ ↦ hterminal P hP J
        (hPQ.trans hQJ) hJ hsJ (fun f hf ↦ hQJ (hhighQ f hf)) hdJ hcJ)
      (componentPoints S Q)
      (fun x hx ↦ by
        rw [mem_componentPoints] at hx
        exact ⟨⟨hx.2, (hS x hx.1).2.1⟩, (hS x hx.1).2.2.2⟩)
      (fun x hx ↦ by rw [mem_componentPoints] at hx; exact hA x hx.1)
    refine hbound.trans ?_
    have hprod := hybridDimensionSensitiveIncidenceProduct_le_two
      (n := n) (A := A) (L := L) (k := k) (b := 1)
      (d := (hilbertPolynomial Q).natDegree)
      (hTdim Q hQ) hLA hkA hAn Nat.zero_lt_one
    have hprod' :
        hybridDimensionSensitiveIncidenceProduct n A L k 1
            (hilbertPolynomial Q).natDegree ≤ R := by
      simpa only [R, Nat.mul_one] using hprod
    exact mul_le_mul_of_nonneg_left hprod' (affineDegree_nonneg Q)
  have hdegreeSum : ∑ Q ∈ T, affineDegree Q ≤ V * (B : ℚ) ^ 2 := by
    calc
      ∑ Q ∈ T, affineDegree Q ≤
          ∑ Q ∈ T, affineDegree Q * (B : ℚ) ^ (hilbertPolynomial Q).natDegree := by
        apply Finset.sum_le_sum
        intro Q hQ
        exact le_mul_of_one_le_right (affineDegree_nonneg Q)
          (one_le_pow₀ (by exact_mod_cast hB))
      _ ≤ V * (B : ℚ) ^ 2 := hpotential
  calc
    (S.card : ℚ) ≤ ∑ Q ∈ T, ((componentPoints S Q).card : ℚ) := by exact_mod_cast hcover
    _ ≤ ∑ Q ∈ T, affineDegree Q * R := Finset.sum_le_sum hcomponent
    _ = (∑ Q ∈ T, affineDegree Q) * R := by rw [Finset.sum_mul]
    _ ≤ (V * (B : ℚ) ^ 2) * R :=
      mul_le_mul_of_nonneg_right hdegreeSum (by positivity)
    _ = _ := by dsimp only [R]; ring

/-- Fiber incidence in ordinary degree-`< k` coefficient space, with the hereditary dimension
premise discharged by Vandermonde elimination.  The retained principal-open prime may come from
any geometric envelope; no Taylor-chart hypothesis is needed at this stage. -/
theorem finite_fixedCoefficientAgreementLocus_and_ncard_le_dimensionSensitive
    {n A k : ℕ} (α : Fin n ↪ F) (y : Fin n → F)
    {P : Ideal (MvPolynomial (Fin k) F)} (hP : P.IsPrime)
    {s : MvPolynomial (Fin k) F} (hs : s ∉ P)
    (hkA : k ≤ A) (hAn : A ≤ n) :
    let cuts : Fin n → MvPolynomial (Fin k) F := fun i ↦
      fixedCoefficientEvaluation k (α i) (y i)
    let T := {x : Fin k → F | x ∈ principalOpenZeroLocus P s ∧
      A ≤ (agreementIndices cuts x).card}
    T.Finite ∧ (T.ncard : ℚ) ≤ affineDegree P *
      dimensionSensitiveIncidenceProduct n A k 1 (hilbertPolynomial P).natDegree := by
  dsimp only
  apply finite_agreementLocus_and_ncard_le_dimensionSensitive hP hs
    (fun i ↦ fixedCoefficientEvaluation k (α i) (y i))
    (fun i ↦ fixedCoefficientEvaluation_totalDegree_le_one k (α i) (y i))
    hkA hAn
  intro Q _ hQ _ hd
  exact fixedCoefficientEvaluation_dimensionSensitive_component α y Q hQ hd

/-- First-order fiber specialization.  A coefficient-space component of dimension at most one
is charged by exactly the single ratio `(n-k+1)/(A-k+1)`. -/
theorem finite_fixedCoefficientAgreementLocus_and_ncard_le_firstOrderFiberRatio
    {n A k : ℕ} (α : Fin n ↪ F) (y : Fin n → F)
    {P : Ideal (MvPolynomial (Fin k) F)} (hP : P.IsPrime)
    {s : MvPolynomial (Fin k) F} (hs : s ∉ P)
    (hPdim : (hilbertPolynomial P).natDegree ≤ 1)
    (hkA : k ≤ A) (hAn : A ≤ n) :
    let cuts : Fin n → MvPolynomial (Fin k) F := fun i ↦
      fixedCoefficientEvaluation k (α i) (y i)
    let T := {x : Fin k → F | x ∈ principalOpenZeroLocus P s ∧
      A ≤ (agreementIndices cuts x).card}
    T.Finite ∧ (T.ncard : ℚ) ≤ affineDegree P *
      (((n - k + 1 : ℕ) : ℚ) / ((A - k + 1 : ℕ) : ℚ)) := by
  dsimp only
  obtain ⟨hfinite, hbound⟩ :=
    finite_fixedCoefficientAgreementLocus_and_ncard_le_dimensionSensitive
      α y hP hs hkA hAn
  refine ⟨hfinite, hbound.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (dimensionSensitiveIncidenceProduct_le_one hPdim hkA hAn)
    (affineDegree_nonneg P)

end AffineHilbert
