/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.MvPolynomial.WeightedDegree
public import ArkLib.ToMathlib.Combinatorics.Enumerative.MonomialCount
public import ArkLib.ToMathlib.MvPolynomial.PowerMomentLift
public import ArkLib.ToMathlib.Polynomial.EventualGrowth
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineDegree
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertAlgHom
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertComap
public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertPolynomial
public import ArkLib.ToMathlib.RingTheory.Nullstellensatz.AgreementIncidence
public import Mathlib.SetTheory.Cardinal.NatCard
/-!
# Geometry of power-moment coordinates

The power-moment map identifies a polynomial ring in lifted coordinates with a polynomial ring
in one challenge variable and the source variables. Weighted filtrations bound the Hilbert
function and affine degree of its kernel. The point maps identify the lifted zero locus with the
source coordinates, and the incidence theorem transfers finite agreement bounds through this
parametrization.

## Main statements

* `MvPolynomial.powerMomentMap_weightedTotalDegree_le` and
  `MvPolynomial.powerMomentIdeal_affineDegree_le`: weighted degree and affine-degree bounds.
* `MvPolynomial.powerMomentPoint`, `MvPolynomial.powerMomentSourcePoint`, and their evaluation
  theorems: pointwise relations between the lift and source spaces.
* `MvPolynomial.powerMomentMap_incidence_off_excluded`: incidence bounds transferred through
  the power-moment map.

## References

* [DKT26]
-/

@[expose] public section

open Filter Polynomial

noncomputable section

namespace MvPolynomial

variable {E : Type*} [Field E]

/-- Give the challenge variable weight one and each source variable weight `D`. -/
def powerMomentWeight {σ : Type*} (D : ℕ) : Option σ → ℕ
  | none => 1
  | some _ => D

/-- Power-moment substitution sends lifted total degree `N` to weighted degree `D * N`. -/
theorem powerMomentMap_weightedTotalDegree_le {σ : Type*} [Finite σ] (D : ℕ)
    (P : MvPolynomial (PowerMomentIndex D σ) E) :
    (powerMomentMap D P).weightedTotalDegree (powerMomentWeight D) ≤ D * P.totalDegree := by
  let _ : Fintype (PowerMomentIndex D σ) := Fintype.ofFinite _
  apply (weightedTotalDegree_aeval_le_of_le
    (fun _ : PowerMomentIndex D σ ↦ D) (powerMomentWeight D)
    (fun i ↦ i.elim (fun j ↦ (X none) ^ j.val) (fun j ↦ X (some j))) P ?_).trans
  · unfold weightedTotalDegree
    rw [Finset.sup_le_iff]
    intro m hm
    calc
      Finsupp.weight (fun _ : PowerMomentIndex D σ ↦ D) m = D * m.degree := by
        rw [Finsupp.weight_apply, Finsupp.degree_eq_sum]
        simp only [Finsupp.sum, nsmul_eq_mul, Finset.mul_sum, Nat.mul_comm]
        rw [← Finsupp.sum_fintype m (fun _ n ↦ D * n) (by simp)]
        rfl
      _ ≤ D * P.totalDegree := Nat.mul_le_mul_left D (MvPolynomial.le_totalDegree hm)
  · intro i
    cases i with
    | inl j =>
        change weightedTotalDegree (powerMomentWeight D) ((X none : MvPolynomial
          (Option σ) E) ^ j.val) ≤ D
        rw [← mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
        apply restrictWeightedDegree_mono (powerMomentWeight D)
          (show j.val ≤ D by omega)
        simpa only [Nat.mul_one] using pow_mem_restrictWeightedDegree
          (X_mem_restrictWeightedDegree (powerMomentWeight D) 1 none (by
            simp [powerMomentWeight])) j.val
    | inr j =>
        change weightedTotalDegree (powerMomentWeight D)
          (X (some j) : MvPolynomial (Option σ) E) ≤ D
        rw [← mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
        exact X_mem_restrictWeightedDegree (powerMomentWeight D) D (some j) (by
          simp [powerMomentWeight])

/-- The Hilbert function of the moment ideal injects into the weighted source filtration. -/
theorem powerMomentIdeal_hilbertFunction_le_weightedFinrank
    {σ : Type*} [Finite σ] (D N : ℕ) (hD : 0 < D) :
    affineHilbertFunction (powerMomentIdeal (R := E) (σ := σ) D) N ≤
      Module.finrank E
        (restrictWeightedDegree (R := E) (powerMomentWeight (σ := σ) D) (D * N)) := by
  let _ : Module.Finite E
      (restrictWeightedDegree (R := E) (powerMomentWeight (σ := σ) D) (D * N)) :=
    Module.Finite.iff_fg.mpr (restrictWeightedDegree_fg (R := E)
      (powerMomentWeight (σ := σ) D)
      (fun i ↦ by cases i <;> simp [powerMomentWeight, hD.ne']) (D * N))
  let e₀ : (MvPolynomial (PowerMomentIndex D σ) E ⧸
      powerMomentIdeal (R := E) (σ := σ) D) ≃ₐ[E]
      MvPolynomial (Option σ) E :=
    Ideal.quotientKerAlgEquivOfSurjective
      (powerMomentMap_surjective (R := E) (σ := σ) D hD)
  let L : quotientDegreeLE (powerMomentIdeal (R := E) (σ := σ) D) N →ₗ[E]
      restrictWeightedDegree (R := E) (powerMomentWeight (σ := σ) D) (D * N) :=
    (e₀.toLinearMap.domRestrict
        (quotientDegreeLE (powerMomentIdeal (R := E) (σ := σ) D) N)).codRestrict _
      (fun x ↦ by
        obtain ⟨P, hP, hPx⟩ := x.property
        have hdeg : P.totalDegree ≤ N :=
          (mem_restrictTotalDegree (PowerMomentIndex D σ) N P).mp hP
        have he : e₀ x = powerMomentMap (R := E) D P := by
          rw [← hPx]
          exact Ideal.quotientKerAlgEquivOfSurjective_mk
            (powerMomentMap_surjective (R := E) (σ := σ) D hD) P
        rw [mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
        change (e₀ x).weightedTotalDegree (powerMomentWeight D) ≤ D * N
        rw [he]
        exact (powerMomentMap_weightedTotalDegree_le D P).trans
          (Nat.mul_le_mul_left D hdeg))
  rw [affineHilbertFunction]
  apply LinearMap.finrank_le_finrank_of_injective (f := L)
  intro x y hxy
  apply Subtype.ext
  have heq := congrArg Subtype.val hxy
  simp only [L, LinearMap.codRestrict_apply, LinearMap.domRestrict_apply] at heq
  change e₀ x = e₀ y at heq
  exact e₀.injective heq

/-- Euclidean division injects the weighted exponent ball into `D` copies of the ordinary
degree ball. -/
theorem powerMomentWeight_exponent_ncard_le
    {σ : Type*} [Finite σ] (D N : ℕ) (hD : 0 < D) :
    Set.ncard {m : Option σ →₀ ℕ | m.weight (powerMomentWeight D) ≤ D * N} ≤
      D * (N + Nat.card (Option σ)).choose (Nat.card (Option σ)) := by
  classical
  let _ : Fintype σ := Fintype.ofFinite σ
  let A := {m : Option σ →₀ ℕ // m.weight (powerMomentWeight D) ≤ D * N}
  let B := Fin D × {b : Option σ →₀ ℕ // b.degree ≤ N}
  let _ : Finite A := (weightedDegreeSupport_finite (powerMomentWeight (σ := σ) D)
    (fun i ↦ by cases i <;> simp [powerMomentWeight, hD.ne']) (D * N)).to_subtype
  let _ : Finite {b : Option σ →₀ ℕ // b.degree ≤ N} :=
    (Finsupp.finite_of_degree_le N).to_subtype
  let compress (m : Option σ →₀ ℕ) : Option σ →₀ ℕ := m.update none (m none / D)
  have hcompress (m : A) : (compress m).degree ≤ N := by
    have hw : m.val none * 1 + ∑ i : σ, m.val (some i) * D ≤ D * N := by
      have hw0 : m.val.weight (powerMomentWeight D) ≤ D * N := m.property
      rw [Finsupp.weight_eq_sum, Fintype.sum_option] at hw0
      change m.val none * 1 + ∑ i : σ, m.val (some i) * D ≤ D * N at hw0
      exact hw0
    have hdegree : (compress m).degree = m.val none / D + ∑ i : σ, m.val (some i) := by
      simp only [compress, Finsupp.degree_eq_sum, Fintype.sum_option, Finsupp.update_apply,
        ↓reduceIte, Option.some_ne_none]
    have hq : D * (m.val none / D) ≤ m.val none := Nat.mul_div_le _ _
    rw [hdegree]
    have hscaled : D * (m.val none / D + ∑ i : σ, m.val (some i)) ≤ D * N := by
      rw [Nat.mul_add]
      calc
        D * (m.val none / D) + D * ∑ i : σ, m.val (some i) ≤
            m.val none + D * ∑ i : σ, m.val (some i) := Nat.add_le_add_right hq _
        _ = m.val none * 1 + ∑ i : σ, m.val (some i) * D := by
          rw [Nat.mul_one, Finset.mul_sum]
          apply congrArg (m.val none + ·)
          apply Finset.sum_congr rfl
          intro i _
          rw [Nat.mul_comm]
        _ ≤ D * N := hw
    exact Nat.le_of_mul_le_mul_left hscaled hD
  let f : A → B := fun m ↦
    (⟨m.val none % D, Nat.mod_lt _ hD⟩, ⟨compress m, hcompress m⟩)
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    cases i with
    | none =>
        have hfst := congrArg Prod.fst hab
        have hmod : a.val none % D = b.val none % D := congrArg Fin.val hfst
        have hdiv : a.val none / D = b.val none / D := by
          have hc := congrArg (fun x ↦ x.2.val none) hab
          simpa only [f, compress, Finsupp.update_apply, ↓reduceIte] using hc
        rw [← Nat.mod_add_div (a.val none) D, ← Nat.mod_add_div (b.val none) D, hmod, hdiv]
    | some i =>
        have hc := congrArg (fun x ↦ x.2.val (some i)) hab
        simpa only [f, compress, Finsupp.update_apply, Option.some_ne_none, ite_false] using hc
  have hcard : Nat.card A ≤ Nat.card B := Nat.card_le_card_of_injective f hf
  rw [show Set.ncard {m : Option σ →₀ ℕ | m.weight (powerMomentWeight D) ≤ D * N} =
      Nat.card A by exact (Nat.card_coe_set_eq _).symm]
  calc
    Nat.card A ≤ Nat.card B := hcard
    _ = D * Set.ncard {b : Option σ →₀ ℕ | b.degree ≤ N} := by
      rw [show Nat.card B = D * Nat.card {b : Option σ →₀ ℕ // b.degree ≤ N} by
        simp only [B, Nat.card_prod, Nat.card_fin]]
      exact congrArg (D * ·) (Nat.card_coe_set_eq _)
    _ = D * (N + Nat.card (Option σ)).choose (Nat.card (Option σ)) := by
      exact congrArg (D * ·) (Finsupp.ncard_setOf_degree_le (Option σ) N)

/-- The moment ideal's Hilbert function is bounded by `D` copies of the ordinary degree ball. -/
theorem powerMomentIdeal_hilbertFunction_le
    {σ : Type*} [Finite σ] (D N : ℕ) (hD : 0 < D) :
    affineHilbertFunction (powerMomentIdeal (R := E) (σ := σ) D) N ≤
      D * (N + Nat.card (Option σ)).choose (Nat.card (Option σ)) := by
  calc
    affineHilbertFunction (powerMomentIdeal (R := E) (σ := σ) D) N ≤
        Module.finrank E (restrictWeightedDegree (R := E) (powerMomentWeight D) (D * N)) :=
      powerMomentIdeal_hilbertFunction_le_weightedFinrank D N hD
    _ = Set.ncard {m : Option σ →₀ ℕ | m.weight (powerMomentWeight D) ≤ D * N} :=
      finrank_restrictWeightedDegree (K := E) (powerMomentWeight (σ := σ) D)
        (fun i ↦ by cases i <;> simp [powerMomentWeight, hD.ne']) (D * N)
    _ ≤ _ := powerMomentWeight_exponent_ncard_le D N hD

/-- The power-moment variety has affine degree at most `D`. -/
theorem powerMomentIdeal_affineDegree_le
    {σ : Type*} [Finite σ] (D : ℕ) (hD : 0 < D) :
    affineDegree (powerMomentIdeal (R := E) (σ := σ) D) ≤ (D : ℚ) := by
  let I : Ideal (MvPolynomial (PowerMomentIndex D σ) E) := powerMomentIdeal D
  let s := Nat.card (Option σ)
  let R : ℚ[X] := Polynomial.C (D : ℚ) * Polynomial.preHilbertPoly ℚ s 0
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hkerEq : I = RingHom.ker (powerMomentMap (R := E) (σ := σ) D) := by
    change RingHom.ker (powerMomentMap (R := E) (σ := σ) D).toRingHom =
      RingHom.ker (powerMomentMap (R := E) (σ := σ) D)
    exact congrArg RingHom.ker
      (AlgHom.toRingHom_eq_coe (powerMomentMap (R := E) (σ := σ) D))
  have hIdeg : (affineHilbertPolynomial I).natDegree = s := by
    rw [hkerEq]
    exact natDegree_affineHilbertPolynomial_ker_of_surjective
      (powerMomentMap (R := E) (σ := σ) D)
      (powerMomentMap_surjective (R := E) (σ := σ) D hD)
  have hRdeg : R.natDegree = s := by
    simp only [R, Polynomial.natDegree_C_mul hDq, Polynomial.natDegree_preHilbertPoly]
  have hInonneg : ∀ᶠ N : ℕ in atTop,
      0 ≤ (affineHilbertPolynomial I).eval (N : ℚ) :=
    (eventually_eval_affineHilbertPolynomial_nonneg I)
  have hIR : ∀ᶠ N : ℕ in atTop,
      (affineHilbertPolynomial I).eval (N : ℚ) ≤ R.eval (N : ℚ) := by
    filter_upwards [eventually_eval_affineHilbertPolynomial I] with N hN
    rw [hN]
    simp only [R, Polynomial.eval_mul, Polynomial.eval_C]
    rw [Polynomial.preHilbertPoly_eq_choose_add_sub ℚ s (k := 0) (n := N) (by omega)]
    simp only [Nat.sub_zero]
    exact_mod_cast powerMomentIdeal_hilbertFunction_le (E := E) (σ := σ) D N hD
  have hdeg : (affineHilbertPolynomial I).natDegree = R.natDegree := hIdeg.trans hRdeg.symm
  have hlc := (natDegree_le_of_eventually_eval_natCast_le hInonneg hIR).2 hdeg
  have hRlc : R.leadingCoeff = (D : ℚ) * (s.factorial : ℚ)⁻¹ := by
    simp only [R, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_preHilbertPoly]
  rw [hRlc] at hlc
  change affineDegree I ≤ (D : ℚ)
  rw [affineDegree, hIdeg]
  calc
    (s.factorial : ℚ) * (affineHilbertPolynomial I).leadingCoeff ≤
        (s.factorial : ℚ) * ((D : ℚ) * (s.factorial : ℚ)⁻¹) :=
      mul_le_mul_of_nonneg_left hlc (by positivity)
    _ = (D : ℚ) := by field_simp

/-- The canonical lifted point above a challenge and source-variable assignment. -/
def powerMomentPoint {σ : Type*} (D : ℕ) (x : Option σ → E) :
    PowerMomentIndex D σ → E
  | Sum.inl j => x none ^ j.val
  | Sum.inr i => x (some i)

/-- Recover the challenge and source assignment from a lifted point using its degree-one
challenge coordinate. -/
def powerMomentSourcePoint {σ : Type*} (D : ℕ) (hD : 0 < D)
    (x : PowerMomentIndex D σ → E) : Option σ → E
  | none => x (Sum.inl ⟨1, by omega⟩)
  | some i => x (Sum.inr i)

/-- The source point recovered from a canonical lifted point is the original point. -/
@[simp]
theorem powerMomentSourcePoint_powerMomentPoint {σ : Type*} (D : ℕ) (hD : 0 < D)
    (x : Option σ → E) : powerMomentSourcePoint D hD (powerMomentPoint D x) = x := by
  funext i
  cases i <;> simp [powerMomentSourcePoint, powerMomentPoint]

/-- Evaluation at a canonical lifted point factors through the power-moment map. -/
theorem aeval_powerMomentPoint {σ : Type*} (D : ℕ) (x : Option σ → E)
    (P : MvPolynomial (PowerMomentIndex D σ) E) :
    aeval (powerMomentPoint D x) P =
      aeval x (powerMomentMap (R := E) (σ := σ) D P) := by
  let lhs : MvPolynomial (PowerMomentIndex D σ) E →ₐ[E] E :=
    MvPolynomial.aeval (powerMomentPoint D x)
  let rhs : MvPolynomial (PowerMomentIndex D σ) E →ₐ[E] E :=
    (MvPolynomial.aeval x).comp (powerMomentMap (R := E) (σ := σ) D)
  have he : lhs = rhs := by
    ext i
    cases i with
    | inl j => simp [lhs, rhs, powerMomentPoint, powerMomentMap]
    | inr i => simp [lhs, rhs, powerMomentPoint, powerMomentMap]
  exact DFunLike.congr_fun he P

/-- Every canonical lifted point satisfies the moment relations. -/
theorem powerMomentPoint_mem_zeroLocus {σ : Type*} (D : ℕ) (x : Option σ → E) :
    powerMomentPoint D x ∈ zeroLocus E (powerMomentIdeal (R := E) (σ := σ) D) := by
  intro P hP
  rw [aeval_powerMomentPoint]
  have hz : powerMomentMap (R := E) (σ := σ) D P = 0 := RingHom.mem_ker.mp hP
  rw [hz, map_zero]

/-- On the moment variety, evaluation at a lifted point factors through its recovered source
point. -/
theorem aeval_eq_aeval_powerMomentMap_of_mem_zeroLocus
    {σ : Type*} (D : ℕ) (hD : 0 < D) (x : PowerMomentIndex D σ → E)
    (hx : x ∈ zeroLocus E (powerMomentIdeal (R := E) (σ := σ) D))
    (P : MvPolynomial (PowerMomentIndex D σ) E) :
    aeval x P = aeval (powerMomentSourcePoint D hD x)
      (powerMomentMap (R := E) (σ := σ) D P) := by
  let lhs : MvPolynomial (PowerMomentIndex D σ) E →ₐ[E] E := MvPolynomial.aeval x
  let rhs : MvPolynomial (PowerMomentIndex D σ) E →ₐ[E] E :=
    (MvPolynomial.aeval (powerMomentSourcePoint D hD x)).comp
      (powerMomentMap (R := E) (σ := σ) D)
  have he : lhs = rhs := by
    ext i
    cases i with
    | inr i => simp [lhs, rhs, powerMomentSourcePoint, powerMomentMap]
    | inl j =>
      let relation : MvPolynomial (PowerMomentIndex D σ) E :=
        X (Sum.inl j) - X (Sum.inl ⟨1, by omega⟩) ^ j.val
      have hrel : relation ∈ powerMomentIdeal (R := E) (σ := σ) D := by
        rw [powerMomentIdeal, RingHom.mem_ker]
        simp [relation, powerMomentMap]
      have hz := hx relation hrel
      simp only [relation, map_sub, MvPolynomial.aeval_X, map_pow, sub_eq_zero] at hz
      simpa [lhs, rhs, powerMomentSourcePoint, powerMomentMap] using hz
  exact DFunLike.congr_fun he P

/-- Bound source incidence after lifting its equations into power-moment coordinates.

If the lifted initial equation has degree at most `initialDegree` and all other lifted equations
have degree at most `B`, the moment base contributes a factor `D` and the incidence ratio is
raised only to the source dimension. -/
theorem powerMomentMap_incidence_off_excluded
    {σ ι : Type*} [Finite σ] [Finite ι]
    {D M d initialDegree B A L n : ℕ} (hD : 0 < D)
    (g s : MvPolynomial σ E[X])
    (hgHeight : CoeffNatDegreeLE g D) (hsHeight : CoeffNatDegreeLE s D)
    (hgSource : (optionEquivRight E σ).symm g ≠ 0)
    (hsSource : (optionEquivRight E σ).symm s ≠ 0)
    (hgDegree : g.totalDegree + 1 ≤ initialDegree)
    (high : ι → MvPolynomial σ E[X])
    (hhighHeight : ∀ i, CoeffNatDegreeLE (high i) (M * D))
    (hhighDegree : ∀ i, (high i).totalDegree + M + 1 ≤ B)
    (cuts : Fin n → MvPolynomial σ E[X])
    (hcutsHeight : ∀ i, CoeffNatDegreeLE (cuts i) (M * D))
    (hcutsDegree : ∀ i, (cuts i).totalDegree + M + 1 ≤ B)
    (hdim : Nat.card σ = d) (hB : 0 < B)
    (hL : 0 < L) (hLA : L ≤ A) (hAn : A ≤ n)
    (excluded : Set (Option σ → E))
    (hterminal : ∀ J : Ideal (MvPolynomial (Option σ) E),
      J.IsPrime → (optionEquivRight E σ).symm s ∉ J →
      (optionEquivRight E σ).symm g ∈ J →
      (∀ i, (optionEquivRight E σ).symm (high i) ∈ J) →
      0 < (affineHilbertPolynomial J).natDegree →
      L ≤ {i | (optionEquivRight E σ).symm (cuts i) ∈ J}.ncard →
      {x | x ∈ zeroLocus E J ∧ aeval x ((optionEquivRight E σ).symm s) ≠ 0} ⊆ excluded)
    (S : Finset (Option σ → E))
    (hS : ∀ x ∈ S,
      aeval x ((optionEquivRight E σ).symm g) = 0 ∧
      aeval x ((optionEquivRight E σ).symm s) ≠ 0 ∧
      (∀ i, aeval x ((optionEquivRight E σ).symm (high i)) = 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S,
      A ≤ {i | aeval x ((optionEquivRight E σ).symm (cuts i)) = 0}.ncard) :
    (S.card : ℚ) ≤ (D : ℚ) * (initialDegree : ℚ) *
      (((n * B : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^ d := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let P : Ideal (MvPolynomial (PowerMomentIndex D σ) E) := powerMomentIdeal D
  let gl := polynomialPowerLift D g hgHeight
  let sl := polynomialPowerLift D s hsHeight
  let flatten : MvPolynomial σ E[X] → MvPolynomial (Option σ) E :=
    (optionEquivRight E σ).symm
  let highl : List (MvPolynomial (PowerMomentIndex D σ) E) :=
    (Finset.univ : Finset ι).toList.map fun i ↦
      chunkedPolynomialPowerLift D M hD (high i) (hhighHeight i)
  let cutsl : Fin n → MvPolynomial (PowerMomentIndex D σ) E := fun i ↦
    chunkedPolynomialPowerLift D M hD (cuts i) (hcutsHeight i)
  let excludedl : Set (PowerMomentIndex D σ → E) :=
    {x | powerMomentSourcePoint D hD x ∈ excluded}
  let Sl : Finset (PowerMomentIndex D σ → E) := S.image (powerMomentPoint D)
  have hmapg : powerMomentMap D gl = flatten g :=
    powerMomentMap_polynomialPowerLift D g hgHeight
  have hmaps : powerMomentMap D sl = flatten s :=
    powerMomentMap_polynomialPowerLift D s hsHeight
  have hgP : gl ∉ P := by
    intro hg
    have hz : powerMomentMap D gl = 0 := RingHom.mem_ker.mp hg
    exact hgSource (hmapg.symm.trans hz)
  have hsP : sl ∉ P := by
    intro hs
    have hz : powerMomentMap D sl = 0 := RingHom.mem_ker.mp hs
    exact hsSource (hmaps.symm.trans hz)
  have hhighl : ∀ f ∈ highl, f.totalDegree ≤ B := by
    intro f hf
    simp only [highl, List.mem_map, Finset.mem_toList] at hf
    obtain ⟨i, _, rfl⟩ := hf
    exact (chunkedPolynomialPowerLift_totalDegree_le D M (high i).totalDegree hD
      (high i) (hhighHeight i) le_rfl).trans (hhighDegree i)
  have hcutsl : ∀ i, (cutsl i).totalDegree ≤ B := by
    intro i
    exact (chunkedPolynomialPowerLift_totalDegree_le D M (cuts i).totalDegree hD
      (cuts i) (hcutsHeight i) le_rfl).trans (hcutsDegree i)
  have hterminalLift : ∀ Q : Ideal (MvPolynomial (PowerMomentIndex D σ) E),
      P ≤ Q → Q.IsPrime → sl ∉ Q → gl ∈ Q → (∀ f ∈ highl, f ∈ Q) →
      0 < (affineHilbertPolynomial Q).natDegree →
      L ≤ {i | cutsl i ∈ Q}.ncard →
      {x | x ∈ zeroLocus E Q ∧ aeval x sl ≠ 0} ⊆ excludedl := by
    intro Q hPQ hQ hsQ hgQ hhighQ hdQ hcutsQ
    let J : Ideal (MvPolynomial (Option σ) E) := Q.map (powerMomentMap D).toRingHom
    let _ : Q.IsPrime := hQ
    have hkerQ : RingHom.ker (powerMomentMap D).toRingHom ≤ Q := by
      simpa only [P, powerMomentIdeal] using hPQ
    have hJ : J.IsPrime := Ideal.map_isPrime_of_surjective
      (f := (powerMomentMap D).toRingHom) (powerMomentMap_surjective D hD) hkerQ
    have hcomap : J.comap (powerMomentMap D).toRingHom = Q := by
      change (Q.map (powerMomentMap D).toRingHom).comap (powerMomentMap D).toRingHom = Q
      rw [Ideal.comap_map_of_surjective (powerMomentMap D).toRingHom
        (powerMomentMap_surjective D hD) Q]
      apply sup_eq_left.mpr
      rw [← RingHom.ker_eq_comap_bot]
      exact hkerQ
    have hsJ : flatten s ∉ J := by
      intro hs
      have hsl : sl ∈ J.comap (powerMomentMap D).toRingHom := by
        change powerMomentMap D sl ∈ J
        rwa [hmaps]
      rw [hcomap] at hsl
      exact hsQ hsl
    have hgJ : flatten g ∈ J := by
      have hmem : powerMomentMap D gl ∈ J :=
        Ideal.mem_map_of_mem (powerMomentMap D).toRingHom hgQ
      simpa only [hmapg] using hmem
    have hhighJ : ∀ i, flatten (high i) ∈ J := by
      intro i
      change (optionEquivRight E σ).symm (high i) ∈ J
      rw [← powerMomentMap_chunkedPolynomialPowerLift D M hD (high i) (hhighHeight i)]
      apply Ideal.mem_map_of_mem (powerMomentMap D).toRingHom
      apply hhighQ
      simp only [highl, List.mem_map, Finset.mem_toList]
      exact ⟨i, Finset.mem_univ _, rfl⟩
    have hdJ : 0 < (affineHilbertPolynomial J).natDegree := by
      have hdegree : (affineHilbertPolynomial Q).natDegree =
          (affineHilbertPolynomial J).natDegree := by
        rw [← hcomap]
        exact natDegree_affineHilbertPolynomial_comap_of_surjective
          (powerMomentMap (R := E) (σ := σ) D)
          (powerMomentMap_surjective (R := E) (σ := σ) D hD) J
      rw [← hdegree]
      exact hdQ
    have hcutsEq : {i | flatten (cuts i) ∈ J} = {i | cutsl i ∈ Q} := by
      ext i
      constructor
      · intro hi
        have hil : cutsl i ∈ J.comap (powerMomentMap D).toRingHom := by
          change powerMomentMap D
            (chunkedPolynomialPowerLift D M hD (cuts i) (hcutsHeight i)) ∈ J
          rw [powerMomentMap_chunkedPolynomialPowerLift]
          exact hi
        rwa [hcomap] at hil
      · intro hi
        have hmem : cutsl i ∈ J.comap (powerMomentMap D).toRingHom := by
          rw [hcomap]
          exact hi
        change powerMomentMap D
          (chunkedPolynomialPowerLift D M hD (cuts i) (hcutsHeight i)) ∈ J at hmem
        rw [powerMomentMap_chunkedPolynomialPowerLift] at hmem
        exact hmem
    have hcutsSrc : L ≤ {i | flatten (cuts i) ∈ J}.ncard := by
      simpa only [← hcutsEq] using hcutsQ
    have hsource := hterminal J hJ hsJ hgJ hhighJ hdJ hcutsSrc
    intro x hx
    have hxP : x ∈ zeroLocus E P := zeroLocus_anti_mono hPQ hx.1
    let y := powerMomentSourcePoint D hD x
    have hyJ : y ∈ zeroLocus E J := by
      intro p hp
      obtain ⟨q, hq, rfl⟩ :=
        (Ideal.mem_map_iff_of_surjective (powerMomentMap D).toRingHom
          (powerMomentMap_surjective D hD)).mp hp
      change aeval y (powerMomentMap D q) = 0
      rw [← aeval_eq_aeval_powerMomentMap_of_mem_zeroLocus D hD x hxP]
      exact hx.1 q hq
    have hys : aeval y (flatten s) ≠ 0 := by
      rw [← hmaps, ← aeval_eq_aeval_powerMomentMap_of_mem_zeroLocus D hD x hxP]
      exact hx.2
    exact hsource ⟨hyJ, hys⟩
  have hSl : Sl.card = S.card := by
    change (S.image (powerMomentPoint D)).card = S.card
    rw [Finset.card_image_iff]
    intro x hx y hy hxy
    have hxy' := congrArg (powerMomentSourcePoint D hD) hxy
    simpa using hxy'
  have hSlS : ∀ x ∈ Sl,
      x ∈ zeroLocus E P ∧ aeval x gl = 0 ∧ aeval x sl ≠ 0 ∧
        (∀ f ∈ highl, aeval x f = 0) ∧ x ∉ excludedl := by
    intro x hx
    simp only [Sl, Finset.mem_image] at hx
    obtain ⟨y, hyS, rfl⟩ := hx
    refine ⟨powerMomentPoint_mem_zeroLocus D y, ?_, ?_, ?_, ?_⟩
    · rw [aeval_powerMomentPoint, hmapg]
      exact (hS y hyS).1
    · rw [aeval_powerMomentPoint, hmaps]
      exact (hS y hyS).2.1
    · intro f hf
      simp only [highl, List.mem_map, Finset.mem_toList] at hf
      obtain ⟨i, _, rfl⟩ := hf
      rw [aeval_powerMomentPoint, powerMomentMap_chunkedPolynomialPowerLift]
      exact (hS y hyS).2.2.1 i
    · change powerMomentSourcePoint D hD (powerMomentPoint D y) ∉ excluded
      simpa using (hS y hyS).2.2.2
  have hASl : ∀ x ∈ Sl, A ≤ {i | aeval x (cutsl i) = 0}.ncard := by
    intro x hx
    simp only [Sl, Finset.mem_image] at hx
    obtain ⟨y, hyS, rfl⟩ := hx
    have heq : {i | aeval (powerMomentPoint D y) (cutsl i) = 0} =
        {i | aeval y (flatten (cuts i)) = 0} := by
      ext i
      change aeval (powerMomentPoint D y)
          (chunkedPolynomialPowerLift D M hD (cuts i) (hcutsHeight i)) = 0 ↔
        aeval y (flatten (cuts i)) = 0
      rw [aeval_powerMomentPoint, powerMomentMap_chunkedPolynomialPowerLift]
    rw [heq]
    exact hA y hyS
  have hbound := card_le_of_agreement_off_excluded_of_principalCut
    (P := P) (hP := powerMomentIdeal_isPrime (R := E) (σ := σ) D)
    (d := d) (baseDegree := D) (initialDegree := initialDegree) (B := B)
    (A := A) (L := L)
    (by
      change (affineHilbertPolynomial
        (RingHom.ker (powerMomentMap (R := E) (σ := σ) D).toRingHom)).natDegree =
        d + 1
      have hkerEq : RingHom.ker (powerMomentMap (R := E) (σ := σ) D).toRingHom =
          RingHom.ker (powerMomentMap (R := E) (σ := σ) D) := by
        exact congrArg RingHom.ker
          (AlgHom.toRingHom_eq_coe (powerMomentMap (R := E) (σ := σ) D))
      rw [hkerEq]
      rw [natDegree_affineHilbertPolynomial_ker_of_surjective
        (powerMomentMap (R := E) (σ := σ) D)
        (powerMomentMap_surjective (R := E) (σ := σ) D hD)]
      rw [Finite.card_option, hdim])
    (by simpa only [P] using powerMomentIdeal_affineDegree_le (E := E) D hD)
    gl sl hgP
    ((polynomialPowerLift_totalDegree_le D g.totalDegree g hgHeight le_rfl).trans hgDegree)
    hB highl hhighl cutsl hcutsl hL hLA (by
      simpa only [Fintype.card_fin] using hAn)
    excludedl hterminalLift Sl hSlS hASl
  rw [hSl] at hbound
  simpa only [Fintype.card_fin] using hbound

end MvPolynomial
