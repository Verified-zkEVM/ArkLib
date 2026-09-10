/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.Coordinates
public import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Translation and base change of interpolation constraints

Translation acts on the two received-point coordinates and preserves support bounds whose
generator weights are nonnegative there. Opposite translation is its inverse. Local substitution
at a received point therefore factors through the zero-point map. These facts are independent
of the interpolation support used by an application.
-/

@[expose] public section

open PolynomialDifferential
open scoped BigOperators Pointwise

noncomputable section
namespace ReedSolomon.HiddenDerivative
open MvPolynomial
variable {R : Type*} [CommRing R] {d m : ℕ}

section MatrixBaseChange

/-- Extending the coefficient field cannot increase the rank of a finite matrix. -/
theorem Matrix.rank_map_algebraMap_le
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    {ι κ : Type*} [Fintype κ]
    (A : Matrix ι κ F) :
    (A.map (algebraMap F E)).rank ≤ A.rank := by
  classical
  let p := Submodule.span F (Set.range A.col)
  let _ : Module.Finite F p := Module.Finite.span_of_finite F (Set.finite_range A.col)
  let b := Module.Free.chooseBasis F p
  let _ : Fintype (Module.Free.ChooseBasisIndex F p) := Fintype.ofFinite _
  let mapVec : (ι → F) →ₗ[F] (ι → E) :=
    LinearMap.pi fun i => (Algebra.linearMap F E).comp (LinearMap.proj i)
  let mapP : p →ₗ[F] (ι → E) := mapVec.comp p.subtype
  let v : Module.Free.ChooseBasisIndex F p → (ι → E) := fun q => mapP (b q)
  let _ : Module.Finite E (Submodule.span E (Set.range v)) :=
    Module.Finite.span_of_finite E (Set.finite_range v)
  rw [Matrix.rank_eq_finrank_span_cols, Matrix.rank_eq_finrank_span_cols]
  calc
    Module.finrank E (Submodule.span E (Set.range (A.map (algebraMap F E)).col))
        ≤ Module.finrank E (Submodule.span E (Set.range v)) := by
      apply Submodule.finrank_mono
      apply Submodule.span_le.mpr
      rintro _ ⟨j, rfl⟩
      have hcol : A.col j ∈ p := Submodule.subset_span (Set.mem_range_self j)
      have hmap : (A.map (algebraMap F E)).col j = mapVec (A.col j) := by
        ext i
        rfl
      rw [hmap]
      change mapP ⟨A.col j, hcol⟩ ∈ Submodule.span E (Set.range v)
      rw [← b.sum_repr ⟨A.col j, hcol⟩]
      simp only [map_sum, map_smul]
      apply Submodule.sum_mem
      intro q _
      rw [Algebra.smul_def]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self q))
    _ ≤ Fintype.card (Module.Free.ChooseBasisIndex F p) := finrank_range_le_card v
    _ = Module.finrank F p := (Module.finrank_eq_card_basis b).symm

end MatrixBaseChange

section SupportWeights

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
variable {σ τ : Type*}

omit [PartialOrder M] [IsOrderedAddMonoid M] in
private theorem support_weight_C_eq_zero (w : τ → M) (a : R)
    {e : τ →₀ ℕ} (he : e ∈ (C a : MvPolynomial τ R).support) :
    Finsupp.weight w e = 0 := by
  classical
  have he' : e ∈ ({0} : Finset (τ →₀ ℕ)) := MvPolynomial.support_monomial_subset he
  have : e = 0 := Finset.mem_singleton.mp he'
  subst e
  exact map_zero (Finsupp.weight w)

omit [PartialOrder M] [IsOrderedAddMonoid M] in
private theorem support_weight_X_eq (w : τ → M) (i : τ)
    {e : τ →₀ ℕ} (he : e ∈ (X i : MvPolynomial τ R).support) :
    Finsupp.weight w e = w i := by
  classical
  have he' : e ∈ ({Finsupp.single i 1} : Finset (τ →₀ ℕ)) :=
    MvPolynomial.support_monomial_subset he
  have : e = Finsupp.single i 1 := Finset.mem_singleton.mp he'
  subst e
  rw [Finsupp.weight_single]
  exact one_nsmul (w i)

omit [IsOrderedAddMonoid M] in
private theorem support_weight_add_le (w : τ → M)
    {P Q : MvPolynomial τ R} {a : M}
    (hP : ∀ e ∈ P.support, Finsupp.weight w e ≤ a)
    (hQ : ∀ e ∈ Q.support, Finsupp.weight w e ≤ a)
    {e : τ →₀ ℕ} (he : e ∈ (P + Q).support) :
    Finsupp.weight w e ≤ a := by
  classical
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with heP | heQ
  · exact hP e heP
  · exact hQ e heQ

private theorem support_weight_mul_le (w : τ → M)
    {P Q : MvPolynomial τ R} {a b : M}
    (hP : ∀ e ∈ P.support, Finsupp.weight w e ≤ a)
    (hQ : ∀ e ∈ Q.support, Finsupp.weight w e ≤ b)
    {e : τ →₀ ℕ} (he : e ∈ (P * Q).support) :
    Finsupp.weight w e ≤ a + b := by
  classical
  obtain ⟨eP, heP, eQ, heQ, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul P Q he)
  simpa using add_le_add (hP eP heP) (hQ eQ heQ)

private theorem support_weight_pow_le (w : τ → M)
    {P : MvPolynomial τ R} {a : M}
    (hP : ∀ e ∈ P.support, Finsupp.weight w e ≤ a) (n : ℕ)
    {e : τ →₀ ℕ} (he : e ∈ (P ^ n).support) :
    Finsupp.weight w e ≤ n • a := by
  induction n generalizing e with
  | zero => simpa using le_of_eq (support_weight_C_eq_zero w (1 : R) he)
  | succ n ih =>
      rw [pow_succ] at he
      simpa [succ_nsmul] using support_weight_mul_le w (fun e he => ih he) hP he

private theorem support_weight_prod_le (w : τ → M)
    {ι : Type*} (s : Finset ι) (P : ι → MvPolynomial τ R) (a : ι → M)
    (hP : ∀ i ∈ s, ∀ e ∈ (P i).support, Finsupp.weight w e ≤ a i)
    {e : τ →₀ ℕ} (he : e ∈ (s.prod P).support) :
    Finsupp.weight w e ≤ s.sum a := by
  classical
  induction s using Finset.induction_on generalizing e with
  | empty => simpa using le_of_eq (support_weight_C_eq_zero w (1 : R) he)
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi] at he
      rw [Finset.sum_insert hi]
      exact support_weight_mul_le w
        (hP i (Finset.mem_insert_self i s))
        (fun e he => ih (fun j hj => hP j (Finset.mem_insert_of_mem hj)) he) he

private theorem support_weight_bind₁_le (wSource : σ → M) (wTarget : τ → M)
    (f : σ → MvPolynomial τ R)
    (hf : ∀ i, ∀ e ∈ (f i).support, Finsupp.weight wTarget e ≤ wSource i)
    {P : MvPolynomial σ R} {a : M}
    (hP : ∀ u ∈ P.support, Finsupp.weight wSource u ≤ a)
    {e : τ →₀ ℕ} (he : e ∈ (MvPolynomial.bind₁ f P).support) :
    Finsupp.weight wTarget e ≤ a := by
  classical
  rw [MvPolynomial.as_sum P, map_sum] at he
  obtain ⟨u, hu, heu⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum he)
  rw [MvPolynomial.bind₁_monomial] at heu
  have hprod : ∀ v ∈ (u.support.prod fun i => f i ^ u i).support,
      Finsupp.weight wTarget v ≤ Finsupp.weight wSource u := by
    intro v hv
    simpa only [Finsupp.weight_apply, Finsupp.sum] using
      (support_weight_prod_le wTarget u.support
        (fun i => f i ^ u i) (fun i => u i • wSource i)
        (fun i hi v hv => support_weight_pow_le wTarget (hf i) (u i) hv) hv)
  have hmul := support_weight_mul_le wTarget
    (a := (0 : M)) (b := Finsupp.weight wSource u)
    (fun v hv => le_of_eq (support_weight_C_eq_zero wTarget _ hv)) hprod heu
  have hmono : Finsupp.weight wTarget e ≤ Finsupp.weight wSource u := by
    simpa using hmul
  exact hmono.trans (hP u hu)

end SupportWeights

/-- Translate the two point coordinates in a differential polynomial. -/
def globalPointTranslation (center received : R) :
    DifferentialPolynomial R d →ₐ[R] DifferentialPolynomial R d :=
  bind₁ fun
    | none => C center + X none
    | some j => Fin.cases (C received + X (some 0)) (fun i => X (some i.succ)) j

@[simp] theorem globalPointTranslation_X (center received : R) :
    globalPointTranslation (d := d) center received (X none) = C center + X none := by
  simp [globalPointTranslation]

@[simp] theorem globalPointTranslation_Y_zero (center received : R) :
    globalPointTranslation (d := d) center received (X (some 0)) =
      C received + X (some 0) := by
  simp [globalPointTranslation]

@[simp] theorem globalPointTranslation_Y_succ (center received : R) (j : Fin d) :
    globalPointTranslation (d := d) center received (X (some j.succ)) = X (some j.succ) := by
  simp [globalPointTranslation]

private theorem globalPointTranslation_generator_weight_le
    {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
    (w : JetVariable d → M) (hX : 0 ≤ w none) (hY₀ : 0 ≤ w (some 0))
    (center received : R) (v : JetVariable d) {e : JetVariable d →₀ ℕ}
    (he : e ∈ ((fun
      | none => C center + X none
      | some j => Fin.cases (C received + X (some 0))
          (fun i => X (some i.succ)) j) v : DifferentialPolynomial R d).support) :
    Finsupp.weight w e ≤ w v := by
  rcases v with _ | j
  · apply support_weight_add_le w ?_ ?_ he
    · intro u hu
      simpa [support_weight_C_eq_zero w _ hu] using hX
    · intro u hu
      exact (support_weight_X_eq w none hu).le
  · induction j using Fin.cases with
    | zero =>
      simp only [Fin.cases_zero] at he ⊢
      apply support_weight_add_le w ?_ ?_ he
      · intro u hu
        simpa [support_weight_C_eq_zero w _ hu] using hY₀
      · intro u hu
        exact (support_weight_X_eq w (some 0) hu).le
    | succ i =>
      simpa only [Fin.cases_succ] using (support_weight_X_eq w (some i.succ) he).le

/-- Translation in `X` and `Y₀` preserves every support bound defined by nonnegative generator
weights. This generic form is shared by the graded local-image construction. -/
theorem globalPointTranslation_support_weight_le
    {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
    (w : JetVariable d → M) (hX : 0 ≤ w none) (hY₀ : 0 ≤ w (some 0))
    (center received : R) {Q : DifferentialPolynomial R d} {a : M}
    (hQ : ∀ u ∈ Q.support, Finsupp.weight w u ≤ a)
    {e : JetVariable d →₀ ℕ} (he : e ∈ (globalPointTranslation center received Q).support) :
    Finsupp.weight w e ≤ a :=
  support_weight_bind₁_le w w _
    (globalPointTranslation_generator_weight_le w hX hY₀ center received) hQ he

/-- Translation by opposite point coordinates is inverse to point translation. -/
theorem globalPointTranslation_neg_comp (center received : R) :
    (globalPointTranslation (d := d) (-center) (-received)).comp
      (globalPointTranslation center received) = AlgHom.id R _ := by
  apply MvPolynomial.algHom_ext
  intro v
  rcases v with _ | j
  · simp
  · refine Fin.cases ?_ (fun i => ?_) j <;> simp

/-- Local substitution at a point is zero-point substitution after global translation. -/
theorem unscaledLocalSubstitution_zero_comp_globalPointTranslation
    (center received : R) :
    (unscaledLocalSubstitution (R := R) d 0 0).comp
      (globalPointTranslation center received) =
        unscaledLocalSubstitution d center received := by
  apply MvPolynomial.algHom_ext
  intro v
  rcases v with _ | j
  · simp
  · refine Fin.cases ?_ (fun i => ?_) j
    · simp
      ring
    · simp

/-- The arbitrary-point local constraint is obtained from the zero-point map by translation. -/
theorem localConstraintAt_eq_zero_comp_globalPointTranslation
    (center received : R) (Q : DifferentialPolynomial R d) :
    localConstraintAt m center received Q =
      localConstraintAt m 0 0 (globalPointTranslation center received Q) := by
  unfold localConstraintAt
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply]
  rw [← AlgHom.comp_apply,
    unscaledLocalSubstitution_zero_comp_globalPointTranslation center received]


end ReedSolomon.HiddenDerivative
