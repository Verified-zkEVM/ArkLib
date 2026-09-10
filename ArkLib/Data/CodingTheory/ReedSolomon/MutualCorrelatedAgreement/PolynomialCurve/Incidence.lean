/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.ChunkedPowerLift
public import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.PolynomialCurve.GraphAdmissibility
public import ArkLib.ToMathlib.AlgebraicGeometry.CutFamily.Hypersurface
public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.FiniteAlgebraGrowth
public import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.PolynomialGrowthRescaling
public import ArkLib.Data.MvPolynomial.WeightedDegree
public import Mathlib.SetTheory.Cardinal.NatCard
/-!
# Incidence away from admissible polynomial graphs

The excluded locus is the union of actual admissible power-batched polynomial graphs.
Component recognition supplies a tuple for every positive-dimensional prime containing at least
`L` agreement cuts, with `L` independent of the interpolation dimension `k`.

The power-moment lift charges the batching degree once in the affine degree of its prime base.
Its source-level incidence theorem retains stage order `r`, has overall linear batching-degree
dependence, and raises only the batching-independent lifted cut degree to `r + 1`.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon

open Polynomial MvPolynomial HiddenDerivative AffineHilbert

variable {F E : Type*} [Field F] [Field E] {n r ℓ : ℕ}

/-- The concrete positive-degree power-moment base has exactly one challenge dimension in
addition to the jet dimensions. -/
theorem powerMomentIdeal_hilbertPolynomial_natDegree
    {σ : Type*} [Finite σ] (D : ℕ) (hD : 0 < D) :
    (hilbertPolynomial (powerMomentIdeal (F := E) (σ := σ) D)).natDegree =
      Nat.card σ + 1 := by
  let e₀ : (MvPolynomial (PowerLiftIndex D σ) E ⧸ powerMomentIdeal D) ≃ₐ[E]
      MvPolynomial (Option σ) E :=
    Ideal.quotientKerAlgEquivOfSurjective (powerMomentMap_surjective D hD)
  let e : (MvPolynomial (PowerLiftIndex D σ) E ⧸ powerMomentIdeal D) ≃ₐ[E]
      (MvPolynomial (Option σ) E ⧸ (⊥ : Ideal (MvPolynomial (Option σ) E))) :=
    e₀.trans (AlgEquiv.quotientBot E (MvPolynomial (Option σ) E)).symm
  apply le_antisymm
  · have hle := hilbertPolynomial_natDegree_le_of_injective_algHom e.toAlgHom e.injective
      (powerMomentIdeal_isPrime (F := E) (σ := σ) D).ne_top
    simpa only [hilbertPolynomial_bot_natDegree, Finite.card_option] using hle
  · have hle := hilbertPolynomial_natDegree_le_of_injective_algHom e.symm.toAlgHom
      e.symm.injective (show (⊥ : Ideal (MvPolynomial (Option σ) E)) ≠ ⊤ by
        exact bot_ne_top)
    simpa only [hilbertPolynomial_bot_natDegree, Finite.card_option] using hle

/-- Give challenge exponent weight one and each jet exponent weight `D`. -/
def powerMomentWeight {σ : Type*} (D : ℕ) : Option σ → ℕ
  | none => 1
  | some _ => D

/-- The moment substitution sends ordinary lifted degree `N` to weighted source degree `D*N`. -/
theorem powerMomentMap_weightedTotalDegree_le {σ : Type*} [Finite σ] (D : ℕ)
    (P : MvPolynomial (PowerLiftIndex D σ) E) :
    (powerMomentMap D P).weightedTotalDegree (powerMomentWeight D) ≤ D * P.totalDegree := by
  let _ : Fintype (PowerLiftIndex D σ) := Fintype.ofFinite _
  apply (MvPolynomial.weightedTotalDegree_aeval_le_of_le
    (fun _ : PowerLiftIndex D σ ↦ D) (powerMomentWeight D)
    (fun i ↦ i.elim (fun j ↦ (MvPolynomial.X none) ^ j.val)
      (fun j ↦ MvPolynomial.X (some j))) P ?_).trans
  · unfold MvPolynomial.weightedTotalDegree
    rw [Finset.sup_le_iff]
    intro m hm
    calc
      Finsupp.weight (fun _ : PowerLiftIndex D σ ↦ D) m = D * m.degree := by
        rw [Finsupp.weight_apply, Finsupp.degree_eq_sum]
        simp only [Finsupp.sum, nsmul_eq_mul, Finset.mul_sum, Nat.mul_comm]
        rw [← Finsupp.sum_fintype m (fun _ n ↦ D * n) (by simp)]
        rfl
      _ ≤ D * P.totalDegree := Nat.mul_le_mul_left D (MvPolynomial.le_totalDegree hm)
  · intro i
    cases i with
    | inl j =>
        change MvPolynomial.weightedTotalDegree (powerMomentWeight D)
          ((MvPolynomial.X none : MvPolynomial (Option σ) E) ^ j.val) ≤ D
        rw [← MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
        apply MvPolynomial.restrictWeightedDegree_mono (powerMomentWeight D)
          (show j.val ≤ D by omega)
        simpa only [Nat.mul_one] using MvPolynomial.pow_mem_restrictWeightedDegree
          (MvPolynomial.X_mem_restrictWeightedDegree (powerMomentWeight D) 1 none (by
            simp [powerMomentWeight])) j.val
    | inr j =>
        change MvPolynomial.weightedTotalDegree (powerMomentWeight D)
          (MvPolynomial.X (some j) : MvPolynomial (Option σ) E) ≤ D
        rw [← MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
        exact MvPolynomial.X_mem_restrictWeightedDegree (powerMomentWeight D) D (some j) (by
          simp [powerMomentWeight])

/-- The actual quotient filtration of the moment ideal injects into the weighted source
filtration. -/
theorem powerMomentIdeal_hilbertFunction_le_weightedFinrank
    {σ : Type*} [Finite σ] (D N : ℕ) (hD : 0 < D) :
    hilbertFunction (powerMomentIdeal (F := E) (σ := σ) D) N ≤
      Module.finrank E
        (MvPolynomial.restrictWeightedDegree (R := E) (powerMomentWeight (σ := σ) D)
          (D * N)) := by
  let _ : Module.Finite E
      (MvPolynomial.restrictWeightedDegree (R := E) (powerMomentWeight (σ := σ) D) (D * N)) :=
    Module.Finite.iff_fg.mpr (MvPolynomial.restrictWeightedDegree_fg
      (powerMomentWeight (σ := σ) D) (fun i ↦ by cases i <;> simp [powerMomentWeight, hD.ne'])
      (D * N))
  let e₀ : (MvPolynomial (PowerLiftIndex D σ) E ⧸ powerMomentIdeal D) ≃ₐ[E]
      MvPolynomial (Option σ) E :=
    Ideal.quotientKerAlgEquivOfSurjective (powerMomentMap_surjective D hD)
  let L : quotientDegreeLE (powerMomentIdeal (F := E) (σ := σ) D) N →ₗ[E]
      MvPolynomial.restrictWeightedDegree (R := E) (powerMomentWeight (σ := σ) D) (D * N) :=
    (e₀.toLinearMap.domRestrict (quotientDegreeLE (powerMomentIdeal D) N)).codRestrict _
      (fun x ↦ by
        obtain ⟨P, hP, hPx⟩ := x.property
        have hdeg : P.totalDegree ≤ N :=
          (MvPolynomial.mem_restrictTotalDegree _ _ P).mp hP
        have he : e₀ x = powerMomentMap D P := by
          rw [← hPx]
          exact Ideal.quotientKerAlgEquivOfSurjective_mk
            (powerMomentMap_surjective D hD) P
        rw [MvPolynomial.mem_restrictWeightedDegree_iff_weightedTotalDegree_le]
        change (e₀ x).weightedTotalDegree (powerMomentWeight D) ≤ D * N
        rw [he]
        exact (powerMomentMap_weightedTotalDegree_le D P).trans
          (Nat.mul_le_mul_left D hdeg))
  rw [hilbertFunction]
  apply LinearMap.finrank_le_finrank_of_injective (f := L)
  intro x y hxy
  apply Subtype.ext
  have heq := congrArg Subtype.val hxy
  simp only [L, LinearMap.codRestrict_apply, LinearMap.domRestrict_apply] at heq
  change e₀ x = e₀ y at heq
  exact e₀.injective heq

/-- Euclidean division of the challenge exponent injects the weighted exponent ball into `D`
copies of the ordinary total-degree ball. -/
theorem powerMomentWeight_exponent_ncard_le
    {σ : Type*} [Finite σ] (D N : ℕ) (hD : 0 < D) :
    Set.ncard {m : Option σ →₀ ℕ | m.weight (powerMomentWeight D) ≤ D * N} ≤
      D * (N + Nat.card (Option σ)).choose (Nat.card (Option σ)) := by
  classical
  let _ : Fintype σ := Fintype.ofFinite σ
  let A := {m : Option σ →₀ ℕ // m.weight (powerMomentWeight D) ≤ D * N}
  let B := Fin D × {b : Option σ →₀ ℕ // b.degree ≤ N}
  let _ : Finite A := (MvPolynomial.weightedDegreeSupport_finite
    (powerMomentWeight (σ := σ) D) (fun i ↦ by cases i <;> simp [powerMomentWeight, hD.ne'])
    (D * N)).to_subtype
  let _ : Finite {b : Option σ →₀ ℕ // b.degree ≤ N} :=
    (Finsupp.finite_of_degree_le N).to_subtype
  let compress (m : Option σ →₀ ℕ) : Option σ →₀ ℕ :=
    m.update none (m none / D)
  have hcompress (m : A) : (compress m).degree ≤ N := by
    have hw : m.val none * 1 + ∑ i : σ, m.val (some i) * D ≤ D * N := by
      have hw0 : Finsupp.weight (powerMomentWeight D) m.val ≤ D * N := m.property
      rw [Finsupp.weight_eq_sum, Fintype.sum_option] at hw0
      change m.val none * 1 + ∑ i : σ, m.val (some i) * D ≤ D * N at hw0
      exact hw0
    have hdegree : (compress m).degree = m.val none / D + ∑ i : σ, m.val (some i) := by
      simp only [compress, Finsupp.degree_eq_sum, Fintype.sum_option,
        Finsupp.update_apply, ↓reduceIte, Option.some_ne_none]
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
        rw [← Nat.mod_add_div (a.val none) D, ← Nat.mod_add_div (b.val none) D,
          hmod, hdiv]
    | some i =>
        have hc := congrArg (fun x ↦ x.2.val (some i)) hab
        simpa only [f, compress, Finsupp.update_apply, Option.some_ne_none, if_false] using hc
  have hcard : Nat.card A ≤ Nat.card B := Nat.card_le_card_of_injective f hf
  rw [show Set.ncard {m : Option σ →₀ ℕ |
      m.weight (powerMomentWeight D) ≤ D * N} = Nat.card A by
        exact (Nat.card_coe_set_eq _).symm]
  calc
    Nat.card A ≤ Nat.card B := hcard
    _ = D * Set.ncard {b : Option σ →₀ ℕ | b.degree ≤ N} := by
      rw [show Nat.card B = D * Nat.card {b : Option σ →₀ ℕ // b.degree ≤ N} by
        simp only [B, Nat.card_prod, Nat.card_fin]]
      exact congrArg (D * ·) (Nat.card_coe_set_eq _)
    _ = _ := by
      let _ : Fintype (Option σ) := Fintype.ofFinite _
      rw [show {b : Option σ →₀ ℕ | b.degree ≤ N} =
          (MonomialHilbertCounting.degreeBall (Option σ) N : Set (Option σ →₀ ℕ)) by
        ext b
        simp only [Set.mem_ofPred_eq, Finset.mem_coe,
          MonomialHilbertCounting.mem_degreeBall]]
      simp only [Set.ncard_coe_finset]
      rw [MonomialHilbertCounting.card_degreeBall]
      simp only [Nat.card_eq_fintype_card]

/-- The Hilbert function of the power-moment base is bounded by `D` copies of the ordinary
degree ball in the source variables. -/
theorem powerMomentIdeal_hilbertFunction_le
    {σ : Type*} [Finite σ] (D N : ℕ) (hD : 0 < D) :
    hilbertFunction (powerMomentIdeal (F := E) (σ := σ) D) N ≤
      D * (N + Nat.card (Option σ)).choose (Nat.card (Option σ)) := by
  calc
    hilbertFunction (powerMomentIdeal (F := E) (σ := σ) D) N ≤
        Module.finrank E
          (MvPolynomial.restrictWeightedDegree (R := E) (powerMomentWeight (σ := σ) D)
            (D * N)) := powerMomentIdeal_hilbertFunction_le_weightedFinrank D N hD
    _ = Set.ncard {m : Option σ →₀ ℕ |
          m.weight (powerMomentWeight D) ≤ D * N} :=
      MvPolynomial.finrank_restrictWeightedDegree (powerMomentWeight D)
        (fun i ↦ by cases i <;> simp [powerMomentWeight, hD.ne']) (D * N)
    _ ≤ _ := powerMomentWeight_exponent_ncard_le D N hD

/-- The power-moment variety has affine degree at most `D`.  This is the sharp geometric input:
the batching degree is charged once in the base degree, while lifted agreement equations have
degree independent of `D`. -/
theorem powerMomentIdeal_affineDegree_le
    {σ : Type*} [Finite σ] (D : ℕ) (hD : 0 < D) :
    affineDegree (powerMomentIdeal (F := E) (σ := σ) D) ≤ (D : ℚ) := by
  let I : Ideal (MvPolynomial (PowerLiftIndex D σ) E) := powerMomentIdeal D
  let s := Nat.card (Option σ)
  let R : ℚ[X] := Polynomial.C (D : ℚ) * Polynomial.preHilbertPoly ℚ s 0
  have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD.ne'
  have hIdeg : (hilbertPolynomial I).natDegree = s := by
    simpa only [I, s, Finite.card_option] using
      powerMomentIdeal_hilbertPolynomial_natDegree (E := E) D hD
  have hRdeg : R.natDegree = s := by
    simp only [R, Polynomial.natDegree_C_mul hDq,
      Polynomial.natDegree_preHilbertPoly]
  have hInonneg : ∀ᶠ N : ℕ in Filter.atTop,
      0 ≤ (hilbertPolynomial I).eval (N : ℚ) := by
    filter_upwards [hilbertPolynomial_eventually_eval I] with N hN
    rw [hN]
    positivity
  have hIR : ∀ᶠ N : ℕ in Filter.atTop,
      (hilbertPolynomial I).eval (N : ℚ) ≤ R.eval (N : ℚ) := by
    filter_upwards [hilbertPolynomial_eventually_eval I] with N hN
    rw [hN]
    simp only [R, Polynomial.eval_mul, Polynomial.eval_C,
      Polynomial.preHilbertPoly_eq_choose_sub_add ℚ s (Nat.zero_le N), Nat.sub_zero]
    exact_mod_cast powerMomentIdeal_hilbertFunction_le (E := E) D N hD
  have hdeg : (hilbertPolynomial I).natDegree = R.natDegree := hIdeg.trans hRdeg.symm
  have hlc := (natDegree_le_of_eventually_eval_nat_le
    (hilbertPolynomial_ne_zero
      (powerMomentIdeal_isPrime (F := E) (σ := σ) D).ne_top)
    hInonneg hIR).2 hdeg
  have hRlc : R.leadingCoeff = (D : ℚ) * (s.factorial : ℚ)⁻¹ := by
    simp only [R, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C,
      Polynomial.leadingCoeff_preHilbertPoly]
  rw [hRlc] at hlc
  change affineDegree I ≤ (D : ℚ)
  rw [affineDegree, hIdeg]
  calc
    (s.factorial : ℚ) * (hilbertPolynomial I).leadingCoeff ≤
        (s.factorial : ℚ) * ((D : ℚ) * (s.factorial : ℚ)⁻¹) :=
      mul_le_mul_of_nonneg_left hlc (by positivity)
    _ = (D : ℚ) := by
      field_simp

/-- Passing a prime containing the kernel through a surjective polynomial-algebra map preserves
the Hilbert-polynomial degree.  Although the two standard filtrations need not be identified,
the quotient algebras are isomorphic, so finite-algebra growth compares them in both directions. -/
theorem hilbertPolynomial_natDegree_map_eq_of_surjective
    {σ τ : Type*} [Finite σ] [Finite τ]
    (f : MvPolynomial σ E →ₐ[E] MvPolynomial τ E) (hf : Function.Surjective f)
    (I : Ideal (MvPolynomial σ E)) (hI : I.IsPrime)
    (hker : RingHom.ker f.toRingHom ≤ I) :
    (hilbertPolynomial (I.map f)).natDegree = (hilbertPolynomial I).natDegree := by
  let J : Ideal (MvPolynomial τ E) := I.map f.toRingHom
  have hcomap : J.comap f.toRingHom = I := by
    change (I.map f.toRingHom).comap f.toRingHom = I
    rw [Ideal.comap_map_of_surjective f.toRingHom hf I]
    exact sup_eq_left.mpr (by simpa only [RingHom.ker_eq_comap_bot] using hker)
  have hIJ : I ≤ J.comap f := by
    intro p hp
    exact Ideal.mem_map_of_mem f.toRingHom hp
  let qmap : (MvPolynomial σ E ⧸ I) →ₐ[E] (MvPolynomial τ E ⧸ J) :=
    Ideal.quotientMapₐ J f hIJ
  have hqinj : Function.Injective qmap := by
    intro x y hxy
    rw [← sub_eq_zero]
    have hz : qmap (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (I := I) (x - y)
    rw [← hp] at hz ⊢
    change Ideal.Quotient.mk J (f p) = 0 at hz
    rw [Ideal.Quotient.eq_zero_iff_mem] at hz ⊢
    have hp : p ∈ J.comap f.toRingHom := hz
    rwa [hcomap] at hp
  have hqsurj : Function.Surjective qmap := by
    intro y
    obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (I := J) y
    obtain ⟨q, hq⟩ := hf p
    exact ⟨Ideal.Quotient.mk I q, by simp [qmap, ← hp, ← hq]⟩
  let e : (MvPolynomial σ E ⧸ I) ≃ₐ[E] (MvPolynomial τ E ⧸ J) :=
    AlgEquiv.ofBijective qmap ⟨hqinj, hqsurj⟩
  let _ : I.IsPrime := hI
  have hJ : J.IsPrime := Ideal.map_isPrime_of_surjective hf hker
  apply le_antisymm
  · exact hilbertPolynomial_natDegree_le_of_injective_algHom e.symm.toAlgHom e.symm.injective
      hJ.ne_top
  · exact hilbertPolynomial_natDegree_le_of_injective_algHom e.toAlgHom e.injective hI.ne_top

/-- The canonical point of the power-moment variety above a source challenge/jet point. -/
def powerMomentPoint {σ : Type*} (D : ℕ) (x : Option σ → E) : PowerLiftIndex D σ → E
  | Sum.inl j => (x none) ^ j.val
  | Sum.inr i => x (some i)

/-- Recover the source challenge and jets from a lifted point, using the degree-one power
coordinate. -/
def powerMomentSourcePoint {σ : Type*} (D : ℕ) (hD : 0 < D)
    (x : PowerLiftIndex D σ → E) : Option σ → E
  | none => x (Sum.inl ⟨1, by omega⟩)
  | some i => x (Sum.inr i)

@[simp]
theorem powerMomentSourcePoint_powerMomentPoint {σ : Type*} (D : ℕ) (hD : 0 < D)
    (x : Option σ → E) : powerMomentSourcePoint D hD (powerMomentPoint D x) = x := by
  funext i
  cases i <;> simp [powerMomentSourcePoint, powerMomentPoint]

/-- Polynomial evaluation on a canonical moment point factors through the moment map. -/
theorem aeval_powerMomentPoint {σ : Type*} (D : ℕ) (x : Option σ → E)
    (P : MvPolynomial (PowerLiftIndex D σ) E) :
    aeval (powerMomentPoint D x) P = aeval x (powerMomentMap (F := E) D P) := by
  let lhs : MvPolynomial (PowerLiftIndex D σ) E →ₐ[E] E :=
    MvPolynomial.aeval (powerMomentPoint D x)
  let rhs : MvPolynomial (PowerLiftIndex D σ) E →ₐ[E] E :=
    (MvPolynomial.aeval x).comp (powerMomentMap (F := E) D)
  have he : lhs = rhs := by
    ext i
    cases i with
    | inl j => simp [lhs, rhs, powerMomentPoint, powerMomentMap]
    | inr i => simp [lhs, rhs, powerMomentPoint, powerMomentMap]
  exact DFunLike.congr_fun he P

/-- Canonical moment points lie on the concrete moment variety. -/
theorem powerMomentPoint_mem_zeroLocus {σ : Type*} (D : ℕ) (x : Option σ → E) :
    powerMomentPoint D x ∈ zeroLocus E (powerMomentIdeal (F := E) D) := by
  intro P hP
  rw [aeval_powerMomentPoint]
  have hz : powerMomentMap (F := E) D P = 0 := by
    exact RingHom.mem_ker.mp hP
  rw [hz, map_zero]

/-- On the moment variety, evaluation at a lifted point agrees with evaluation of the moment-map
image at its recovered source point. -/
theorem aeval_eq_aeval_powerMomentMap_of_mem_zeroLocus
    {σ : Type*} (D : ℕ) (hD : 0 < D) (x : PowerLiftIndex D σ → E)
    (hx : x ∈ zeroLocus E (powerMomentIdeal (F := E) D))
    (P : MvPolynomial (PowerLiftIndex D σ) E) :
    aeval x P = aeval (powerMomentSourcePoint D hD x)
      (powerMomentMap (F := E) D P) := by
  let lhs : MvPolynomial (PowerLiftIndex D σ) E →ₐ[E] E := MvPolynomial.aeval x
  let rhs : MvPolynomial (PowerLiftIndex D σ) E →ₐ[E] E :=
    (MvPolynomial.aeval (powerMomentSourcePoint D hD x)).comp
      (powerMomentMap (F := E) D)
  have he : lhs = rhs := by
    ext i
    cases i with
    | inr i => simp [lhs, rhs, powerMomentSourcePoint, powerMomentMap]
    | inl j =>
        let relation : MvPolynomial (PowerLiftIndex D σ) E :=
          MvPolynomial.X (Sum.inl j) - MvPolynomial.X (Sum.inl ⟨1, by omega⟩) ^ j.val
        have hrel : relation ∈ powerMomentIdeal (F := E) D := by
          rw [powerMomentIdeal, RingHom.mem_ker]
          simp [relation, powerMomentMap]
        have hz := hx relation hrel
        simp only [relation, map_sub, MvPolynomial.aeval_X, map_pow, sub_eq_zero] at hz
        simpa [lhs, rhs, powerMomentSourcePoint, powerMomentMap] using hz
  exact DFunLike.congr_fun he P

/-- Incidence after a proper hypersurface cut of an arbitrary prime base variety.

This is the geometric consumer needed by the lifted-power argument.  If the base has dimension
`d + 1` and affine degree at most `baseDegree`, the initial equation costs `initialDegree` once,
while the agreement degree `B` is raised only to `d`.  In particular, a batching-linear bound on
`baseDegree` remains batching-linear in the conclusion. -/
theorem primeBaseHypersurface_incidence_off_excluded
    {σ : Type*} [Finite σ] [IsAlgClosed E]
    {P : Ideal (MvPolynomial σ E)} (hP : P.IsPrime)
    (g s : MvPolynomial σ E) (hsP : s ∉ P) (hgP : g ∉ P)
    {d baseDegree initialDegree B A L : ℕ}
    (hdim : (hilbertPolynomial P).natDegree = d + 1)
    (hbaseDegree : affineDegree P ≤ (baseDegree : ℚ))
    (hgDegree : g.totalDegree ≤ initialDegree) (hB : 0 < B)
    (highCuts : List (MvPolynomial σ E))
    (hhigh : ∀ f ∈ highCuts, f.totalDegree ≤ B)
    (cuts : Fin n → MvPolynomial σ E) (hcuts : ∀ i, (cuts i).totalDegree ≤ B)
    (hL : 0 < L) (hLA : L ≤ A) (hAn : A ≤ n)
    (excluded : Set (σ → E))
    (hterminal : ∀ Q : Ideal (MvPolynomial σ E),
      Q.IsPrime → P ≤ Q → s ∉ Q → g ∈ Q → (∀ f ∈ highCuts, f ∈ Q) →
      0 < (hilbertPolynomial Q).natDegree →
      L ≤ (cutsInIdeal Q cuts).card → principalOpenZeroLocus Q s ⊆ excluded)
    (S : Finset (σ → E))
    (hS : ∀ x ∈ S, x ∈ zeroLocus E P ∧ aeval x g = 0 ∧ aeval x s ≠ 0 ∧
      (∀ f ∈ highCuts, aeval x f = 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices cuts x).card) :
    (S.card : ℚ) ≤ (baseDegree : ℚ) * (initialDegree : ℚ) *
      (((n * B : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^ d := by
  classical
  let T₀ := retainedCutChildren P s g
  let T := iteratedRetainedCutFamily T₀ s highCuts
  let t : ℚ := (n : ℚ) / ((A - L + 1 : ℕ) : ℚ)
  have hden : 0 < A - L + 1 := by omega
  have hdenn : A - L + 1 ≤ n := by omega
  have ht : 1 ≤ t := by
    apply (le_div_iff₀ (by exact_mod_cast hden)).2
    simpa using (show ((A - L + 1 : ℕ) : ℚ) ≤ (n : ℚ) by exact_mod_cast hdenn)
  have hratio : (((n * B : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) = (B : ℚ) * t := by
    dsimp [t]
    push_cast
    ring
  have hT₀ (Q : Ideal (MvPolynomial σ E)) (hQ : Q ∈ T₀) :
      Q.IsPrime ∧ P ≤ Q ∧ g ∈ Q ∧ s ∉ Q :=
    mem_retainedCutChildren hP hsP hQ
  have hT (Q : Ideal (MvPolynomial σ E)) (hQ : Q ∈ T) :
      Q.IsPrime ∧ P ≤ Q ∧ s ∉ Q ∧ g ∈ Q ∧ ∀ f ∈ highCuts, f ∈ Q := by
    have hpo := iteratedRetainedCutFamily_prime_open T₀
      (fun J hJ ↦ (hT₀ J hJ).1) (fun J hJ ↦ (hT₀ J hJ).2.2.2) highCuts Q hQ
    obtain ⟨Q₀, hQ₀, hQ₀Q, hh⟩ := mem_iteratedRetainedCutFamily_contains T₀ highCuts hQ
    exact ⟨hpo.1, (hT₀ Q₀ hQ₀).2.1.trans hQ₀Q, hpo.2,
      hQ₀Q (hT₀ Q₀ hQ₀).2.2.1, hh⟩
  have hTdim (Q : Ideal (MvPolynomial σ E)) (hQ : Q ∈ T) :
      (hilbertPolynomial Q).natDegree ≤ d := by
    obtain ⟨Q₀, hQ₀, hQ₀Q, _⟩ := mem_iteratedRetainedCutFamily_contains T₀ highCuts hQ
    have hQ₀dim : (hilbertPolynomial Q₀).natDegree = d := by
      have hQ₀' : Q₀ ∈ (P ⊔ Ideal.span {g}).retainedMinimalPrimes s := by
        simpa only [T₀, retainedCutChildren, hgP, if_false] using hQ₀
      have hpure := principalCut_component_hilbertPolynomial_natDegree_add_one
        hP hgP ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hQ₀').1
      rw [hdim] at hpure
      omega
    exact (hilbertPolynomial_degree_and_leadingCoeff_antitone hQ₀Q (hT Q hQ).1.ne_top).1
      |>.trans_eq hQ₀dim
  have hT₀potential :
      ∑ Q ∈ T₀, affineDegree Q * (B : ℚ) ^ (hilbertPolynomial Q).natDegree ≤
        (initialDegree : ℚ) * affineDegree P * (B : ℚ) ^ d := by
    have hsum : ∑ Q ∈ T₀, affineDegree Q ≤ (initialDegree : ℚ) * affineDegree P := by
      simpa only [T₀, retainedCutChildren, hgP, if_false] using
        sum_retained_affineDegree_le hP hgP hgDegree
    calc
      _ = (∑ Q ∈ T₀, affineDegree Q) * (B : ℚ) ^ d := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro Q hQ
        have hQ' : Q ∈ (P ⊔ Ideal.span {g}).retainedMinimalPrimes s := by
          simpa only [T₀, retainedCutChildren, hgP, if_false] using hQ
        have hpure := principalCut_component_hilbertPolynomial_natDegree_add_one
          hP hgP ((Ideal.mem_retainedMinimalPrimes _ _ _).mp hQ').1
        rw [hdim] at hpure
        have he : (hilbertPolynomial Q).natDegree = d := by omega
        rw [he]
      _ ≤ _ := mul_le_mul_of_nonneg_right hsum (by positivity)
  have hTpotential :
      ∑ Q ∈ T, affineDegree Q * (B : ℚ) ^ (hilbertPolynomial Q).natDegree ≤
        (initialDegree : ℚ) * affineDegree P * (B : ℚ) ^ d := by
    exact (sum_iteratedRetainedCutFamily_affineDegree_mul_pow_le T₀
      (fun Q hQ ↦ (hT₀ Q hQ).1) (fun Q hQ ↦ (hT₀ Q hQ).2.2.2)
      (Nat.succ_le_iff.mpr hB) highCuts hhigh).trans hT₀potential
  have hcover : S.card ≤ ∑ Q ∈ T, (componentPoints S Q).card := by
    apply le_trans _ Finset.card_biUnion_le
    apply Finset.card_le_card
    intro x hx
    obtain ⟨Q₀, hQ₀, hxQ₀, _⟩ := exists_mem_retainedCutChildren_of_mem_zeroLocus x
      (hS x hx).1 (hS x hx).2.1 (hS x hx).2.2.1
    obtain ⟨Q, hQ, hxQ⟩ := exists_mem_iteratedRetainedCutFamily_of_mem_zeroLocus T₀
      highCuts x ⟨Q₀, hQ₀, hxQ₀⟩ (hS x hx).2.2.1 (hS x hx).2.2.2.1
    exact Finset.mem_biUnion.mpr ⟨Q, hQ, by rw [mem_componentPoints]; exact ⟨hx, hxQ⟩⟩
  have hcomponent (Q : Ideal (MvPolynomial σ E)) (hQ : Q ∈ T) :
      ((componentPoints S Q).card : ℚ) ≤
        affineDegree Q * (B : ℚ) ^ (hilbertPolynomial Q).natDegree * t ^ d := by
    have hq := hT Q hQ
    have hi := affineAgreementIncidence_bound_off_excluded hq.1 hq.2.2.1 cuts hcuts hB hLA
      excluded (fun J hQJ hJ hsJ hdJ hcJ ↦ hterminal J hJ (hq.2.1.trans hQJ) hsJ
        (hQJ hq.2.2.2.1) (fun f hf ↦ hQJ (hq.2.2.2.2 f hf)) hdJ hcJ)
      (componentPoints S Q)
      (fun x hx ↦ by
        rw [mem_componentPoints] at hx
        exact ⟨⟨hx.2, (hS x hx.1).2.2.1⟩, (hS x hx.1).2.2.2.2⟩)
      (fun x hx ↦ by rw [mem_componentPoints] at hx; exact hA x hx.1)
    rw [hratio, mul_pow, ← mul_assoc] at hi
    exact hi.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ ht (hTdim Q hQ))
      (mul_nonneg (affineDegree_nonneg Q) (by positivity)))
  calc
    (S.card : ℚ) ≤ ∑ Q ∈ T, ((componentPoints S Q).card : ℚ) := by exact_mod_cast hcover
    _ ≤ ∑ Q ∈ T,
        affineDegree Q * (B : ℚ) ^ (hilbertPolynomial Q).natDegree * t ^ d :=
      Finset.sum_le_sum hcomponent
    _ = (∑ Q ∈ T, affineDegree Q * (B : ℚ) ^ (hilbertPolynomial Q).natDegree) *
        t ^ d := by rw [Finset.sum_mul]
    _ ≤ ((initialDegree : ℚ) * affineDegree P * (B : ℚ) ^ d) * t ^ d :=
      mul_le_mul_of_nonneg_right hTpotential (by positivity)
    _ ≤ ((initialDegree : ℚ) * (baseDegree : ℚ) * (B : ℚ) ^ d) * t ^ d := by
      gcongr
    _ = _ := by rw [hratio, mul_pow]; ring

/-- Lifted-power incidence stated entirely in terms of the genuine source equations.  The
initial equation and separant use the linear coefficient lift over the degree-`D` moment base.
High and agreement equations of height at most `M*D` use the chunked lift, so their ordinary
lifted degree grows only by `M+1`. -/
theorem powerMoment_incidence_off_source_excluded
    {σ ι : Type*} [Finite σ] [Finite ι] [IsAlgClosed E]
    {D M d initialDegree B A L : ℕ} (hD : 0 < D)
    (g s : MvPolynomial σ E[X])
    (hgHeight : ChallengeHeightLE g D) (hsHeight : ChallengeHeightLE s D)
    (hgSource : flattenChallenge g ≠ 0) (hsSource : flattenChallenge s ≠ 0)
    (hgDegree : g.totalDegree + 1 ≤ initialDegree)
    (high : ι → MvPolynomial σ E[X])
    (hhighHeight : ∀ i, ChallengeHeightLE (high i) (M * D))
    (hhighDegree : ∀ i, (high i).totalDegree + M + 1 ≤ B)
    (cuts : Fin n → MvPolynomial σ E[X])
    (hcutsHeight : ∀ i, ChallengeHeightLE (cuts i) (M * D))
    (hcutsDegree : ∀ i, (cuts i).totalDegree + M + 1 ≤ B)
    (hdim : Nat.card σ = d) (hB : 0 < B)
    (hL : 0 < L) (hLA : L ≤ A) (hAn : A ≤ n)
    (excluded : Set (Option σ → E))
    (hterminal : ∀ J : Ideal (MvPolynomial (Option σ) E),
      J.IsPrime → flattenChallenge s ∉ J → flattenChallenge g ∈ J →
      (∀ i, flattenChallenge (high i) ∈ J) →
      0 < (hilbertPolynomial J).natDegree →
      L ≤ (cutsInIdeal J (fun i ↦ flattenChallenge (cuts i))).card →
      principalOpenZeroLocus J (flattenChallenge s) ⊆ excluded)
    (S : Finset (Option σ → E))
    (hS : ∀ x ∈ S, aeval x (flattenChallenge g) = 0 ∧
      aeval x (flattenChallenge s) ≠ 0 ∧
      (∀ i, aeval x (flattenChallenge (high i)) = 0) ∧ x ∉ excluded)
    (hA : ∀ x ∈ S,
      A ≤ (agreementIndices (fun i ↦ flattenChallenge (cuts i)) x).card) :
    (S.card : ℚ) ≤ (D : ℚ) * (initialDegree : ℚ) *
      (((n * B : ℕ) : ℚ) / ((A - L + 1 : ℕ) : ℚ)) ^ d := by
  classical
  let _ : Fintype ι := Fintype.ofFinite ι
  let P : Ideal (MvPolynomial (PowerLiftIndex D σ) E) := powerMomentIdeal D
  let gl := polynomialPowerLift D g hgHeight
  let sl := polynomialPowerLift D s hsHeight
  let highl : List (MvPolynomial (PowerLiftIndex D σ) E) :=
    (Finset.univ : Finset ι).toList.map fun i ↦
      chunkedPolynomialPowerLift D M hD (high i) (hhighHeight i)
  let cutsl : Fin n → MvPolynomial (PowerLiftIndex D σ) E :=
    fun i ↦ chunkedPolynomialPowerLift D M hD (cuts i) (hcutsHeight i)
  let excludedl : Set (PowerLiftIndex D σ → E) :=
    {x | powerMomentSourcePoint D hD x ∈ excluded}
  let Sl : Finset (PowerLiftIndex D σ → E) := S.image (powerMomentPoint D)
  have hmapg : powerMomentMap D gl = flattenChallenge g := by
    exact powerMomentMap_polynomialPowerLift D g hgHeight
  have hmaps : powerMomentMap D sl = flattenChallenge s := by
    exact powerMomentMap_polynomialPowerLift D s hsHeight
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
  have hterminalLift : ∀ Q : Ideal (MvPolynomial (PowerLiftIndex D σ) E),
      Q.IsPrime → P ≤ Q → sl ∉ Q → gl ∈ Q → (∀ f ∈ highl, f ∈ Q) →
      0 < (hilbertPolynomial Q).natDegree →
      L ≤ (cutsInIdeal Q cutsl).card → principalOpenZeroLocus Q sl ⊆ excludedl := by
    intro Q hQ hPQ hsQ hgQ hhighQ hdQ hcutsQ
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
    have hsJ : flattenChallenge s ∉ J := by
      intro hs
      have hsl : sl ∈ J.comap (powerMomentMap D).toRingHom := by
        change powerMomentMap D sl ∈ J
        rwa [hmaps]
      rw [hcomap] at hsl
      exact hsQ hsl
    have hgJ : flattenChallenge g ∈ J := by
      rw [← hmapg]
      exact Ideal.mem_map_of_mem (powerMomentMap D).toRingHom hgQ
    have hhighJ : ∀ i, flattenChallenge (high i) ∈ J := by
      intro i
      rw [← powerMomentMap_chunkedPolynomialPowerLift D M hD (high i) (hhighHeight i)]
      apply Ideal.mem_map_of_mem (powerMomentMap D).toRingHom
      apply hhighQ
      simp only [highl, List.mem_map, Finset.mem_toList]
      exact ⟨i, Finset.mem_univ _, rfl⟩
    have hdJ : 0 < (hilbertPolynomial J).natDegree := by
      rw [show (hilbertPolynomial J).natDegree = (hilbertPolynomial Q).natDegree by
        exact hilbertPolynomial_natDegree_map_eq_of_surjective (powerMomentMap D)
          (powerMomentMap_surjective D hD) Q hQ
          (by simpa only [P, powerMomentIdeal] using hPQ)]
      exact hdQ
    have hcutsEq : cutsInIdeal J (fun i ↦ flattenChallenge (cuts i)) =
        cutsInIdeal Q cutsl := by
      ext i
      simp only [mem_cutsInIdeal]
      constructor
      · intro hi
        have hil : cutsl i ∈ J.comap (powerMomentMap D).toRingHom := by
          change powerMomentMap D
            (chunkedPolynomialPowerLift D M hD (cuts i) (hcutsHeight i)) ∈ J
          rw [powerMomentMap_chunkedPolynomialPowerLift]
          exact hi
        rwa [hcomap] at hil
      · intro hi
        rw [← powerMomentMap_chunkedPolynomialPowerLift D M hD (cuts i) (hcutsHeight i)]
        exact Ideal.mem_map_of_mem (powerMomentMap D).toRingHom hi
    have hsource := hterminal J hJ hsJ hgJ hhighJ hdJ (by rwa [hcutsEq])
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
    have hys : aeval y (flattenChallenge s) ≠ 0 := by
      rw [← hmaps, ← aeval_eq_aeval_powerMomentMap_of_mem_zeroLocus D hD x hxP]
      exact hx.2
    exact hsource ⟨hyJ, hys⟩
  have hSl : Sl.card = S.card := by
    change (S.image (powerMomentPoint D)).card = S.card
    rw [Finset.card_image_iff]
    intro x hx y hy hxy
    have := congrArg (powerMomentSourcePoint D hD) hxy
    simpa using this
  have hSlS : ∀ x ∈ Sl, x ∈ zeroLocus E P ∧ aeval x gl = 0 ∧ aeval x sl ≠ 0 ∧
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
    · simpa only [excludedl, Set.mem_ofPred_eq,
        powerMomentSourcePoint_powerMomentPoint] using (hS y hyS).2.2.2
  have hASl : ∀ x ∈ Sl, A ≤ (agreementIndices cutsl x).card := by
    intro x hx
    simp only [Sl, Finset.mem_image] at hx
    obtain ⟨y, hyS, rfl⟩ := hx
    have heq : agreementIndices cutsl (powerMomentPoint D y) =
        agreementIndices (fun i ↦ flattenChallenge (cuts i)) y := by
      ext i
      simp only [mem_agreementIndices, cutsl, aeval_powerMomentPoint,
        powerMomentMap_chunkedPolynomialPowerLift]
    rw [heq]
    exact hA y hyS
  have hbound := primeBaseHypersurface_incidence_off_excluded
    (powerMomentIdeal_isPrime (F := E) (σ := σ) D) gl sl hsP hgP
    (d := d) (baseDegree := D) (initialDegree := initialDegree) (B := B)
    (by
      rw [powerMomentIdeal_hilbertPolynomial_natDegree D hD, hdim])
    (by simpa only [P] using powerMomentIdeal_affineDegree_le (E := E) D hD)
    ((polynomialPowerLift_totalDegree_le D g.totalDegree g hgHeight le_rfl).trans hgDegree)
    hB highl hhighl cutsl hcutsl hL hLA hAn excludedl hterminalLift Sl hSlS hASl
  rwa [hSl] at hbound

/-- The finite list of actual high-coefficient equations in joint source coordinates. -/
def sourceCurveHighCuts (center : E) (Q : DifferentialPolynomial E[X] r) (K k : ℕ) :
    List (MvPolynomial (Option (Fin (r + 1))) E) :=
  ((Finset.univ : Finset {l : Fin K // k ≤ l.val}).toList.map
    fun l ↦ symbolicSourceNumerator center Q K l.val)

/-- The finite list of high-coefficient equations at an explicit common Taylor exponent. -/
def sourceCurveHighCuts_of_exponent (center : E) (Q : DifferentialPolynomial E[X] r)
    (K k τ : ℕ) : List (MvPolynomial (Option (Fin (r + 1))) E) :=
  ((Finset.univ : Finset {l : Fin K // k ≤ l.val}).toList.map fun l ↦
    (optionEquivRight E _).symm
      (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K l.val (τ := τ)))

/-- Every high source numerator at exponent `τ` occurs in its finite high-cut list. -/
theorem commonTaylorNumeratorOver_mem_sourceCurveHighCuts_of_exponent
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k τ : ℕ)
    (l : Fin K) (hl : k ≤ l.val) :
    (optionEquivRight E _).symm
        (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K l (τ := τ)) ∈
      sourceCurveHighCuts_of_exponent center Q K k τ := by
  classical
  simp only [sourceCurveHighCuts_of_exponent, List.mem_map, Finset.mem_toList]
  exact ⟨⟨l, hl⟩, Finset.mem_univ _, rfl⟩

/-- Every high source numerator occurs in the finite curve high-cut list. -/
theorem symbolicSourceNumerator_mem_sourceCurveHighCuts
    (center : E) (Q : DifferentialPolynomial E[X] r) (K k : ℕ)
    (l : Fin K) (hl : k ≤ l.val) :
    symbolicSourceNumerator center Q K l ∈ sourceCurveHighCuts center Q K k := by
  classical
  simp only [sourceCurveHighCuts, List.mem_map, Finset.mem_toList]
  exact ⟨⟨l, hl⟩, Finset.mem_univ _, rfl⟩

/-- Source points on admissible tuple graphs whose Taylor numerators all use exponent `τ`. -/
def sourceCurveTupleLocus_of_exponent [DecidableEq F]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (K k L τ : ℕ) : Set (Option (Fin (r + 1)) → E) :=
  {x | ∃ P : Fin (ℓ + 1) → F[X],
    IsAdmissibleChartTupleAtExponent domain w iota center Q K k L τ P ∧
      x = polynomialGraphPoint
        (powerBatchedJetGraph (r := r) center (fun t ↦ (P t).map iota)) (x none)}

/-- Source points on graphs satisfying the actual chart identities at the standard exponent
`2K`. This name is retained as the broad arbitrary-order source-incidence interface. -/
def sourceCurveTupleLocus [DecidableEq F]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (K k L : ℕ) : Set (Option (Fin (r + 1)) → E) :=
  sourceCurveTupleLocus_of_exponent domain w iota center Q K k L (2 * K)

/-- The explicitly parameterized tuple locus at `2K` is definitionally the broad source
incidence locus. -/
theorem sourceCurveTupleLocus_of_exponent_two_mul_eq [DecidableEq F]
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F)
    (iota : F →+* E) (center : E) (Q : DifferentialPolynomial E[X] r)
    (K k L : ℕ) :
    sourceCurveTupleLocus_of_exponent domain w iota center Q K k L (2 * K) =
      sourceCurveTupleLocus domain w iota center Q K k L := rfl

/-- A positive-dimensional prime containing at least `L` curve agreement cuts has all its
regular points on one actual admissible polynomial graph. -/
theorem principalOpen_subset_sourceCurveTupleLocus_of_exponent
    [IsAlgClosed E] [DecidableEq F] {K k L : ℕ}
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r)
    (hK : r < K) (hkL : k ≤ L) (τ : ℕ) (hτ : TaylorExponentSufficient r K τ)
    (I : Ideal (MvPolynomial (Option (Fin (r + 1))) E))
    (hI : I.IsPrime) (hs : symbolicSourceSeparant center Q ∉ I)
    (hinit : symbolicSourceInitialEquation center Q ∈ I)
    (hhigh : ∀ q ∈ sourceCurveHighCuts_of_exponent center Q K k τ, q ∈ I)
    (hd : 0 < (hilbertPolynomial I).natDegree)
    (hcuts : L ≤ (cutsInIdeal I (fun i ↦
      symbolicSourceCurveAgreement_of_exponent center Q K τ (iota (domain i))
        (fun t ↦ iota (w t i)))).card) :
    principalOpenZeroLocus I (symbolicSourceSeparant center Q) ⊆
      sourceCurveTupleLocus_of_exponent domain w iota center Q K k L τ := by
  classical
  obtain ⟨indices, hsub, hcard⟩ := Finset.exists_subset_card_eq hcuts
  obtain ⟨P, hP, hgraph⟩ :=
    exists_admissibleChartTuple_of_symbolic_prime_agreements_of_exponent
      domain w indices hcard hkL iota center Q hK τ hτ I hI hs hd hinit
      (fun l hl ↦ hhigh _ (commonTaylorNumeratorOver_mem_sourceCurveHighCuts_of_exponent
        center Q K k τ l hl))
      (fun i hi ↦ mem_cutsInIdeal.mp (hsub hi))
  intro x hx
  exact ⟨P, hP, hgraph x hx⟩

/-- Chunked-power incidence for actual polynomial-curve agreement cuts.  The batching degree
appears only in the moment-base factor `ℓ + h`; the degree raised to the geometric exponent
`r + 1` is independent of `ℓ`.  This is a numerically looser substitute for the paper's exact
mixed-bidegree formula, but it has the same qualitative `n` exponent and linear `ℓ` dependence. -/
theorem finite_sourceCurve_points_off_tuples_card_le
    [IsAlgClosed E] [DecidableEq F] {K k L A v h : ℕ}
    (domain : Fin n ↪ F) (w : Fin (ℓ + 1) → Fin n → F) (iota : F →+* E)
    (center : E) (Q : DifferentialPolynomial E[X] r)
    (hK : r < K) (hkL : k ≤ L) (hL : 0 < L) (hLA : L ≤ A) (hAn : A ≤ n)
    (hD : 0 < ℓ + h)
    (hinit : symbolicSourceInitialEquation center Q ≠ 0)
    (hsep : symbolicSourceSeparant center Q ≠ 0)
    (hv : 0 < v)
    (hjet : Q.weightedTotalDegree (fun i ↦ i.elim 0 (fun _ ↦ 1)) ≤ v)
    (hheight : ChallengeHeightLE Q h)
    (S : Finset (Option (Fin (r + 1)) → E))
    (hS : ∀ x ∈ S, aeval x (symbolicSourceInitialEquation center Q) = 0 ∧
      aeval x (symbolicSourceSeparant center Q) ≠ 0 ∧
      (∀ l : Fin K, k ≤ l.val → aeval x (symbolicSourceNumerator center Q K l) = 0) ∧
      x ∉ sourceCurveTupleLocus domain w iota center Q K k L)
    (hA : ∀ x ∈ S, A ≤ (agreementIndices (fun i ↦
      symbolicSourceCurveAgreement center Q K (iota (domain i))
        (fun t ↦ iota (w t i))) x).card) :
    (S.card : ℚ) ≤ ((ℓ + h : ℕ) : ℚ) * ((v + 1 : ℕ) : ℚ) *
      (((n * (2 + 2 * K * v) : ℕ) : ℚ) /
        ((A - L + 1 : ℕ) : ℚ)) ^ (r + 1) := by
  let D := ℓ + h
  let M := 2 * K
  let B := 2 + 2 * K * v
  let g := initialJetEquationOver (Polynomial.C center) Q
  let s := initialJetSeparantOver (Polynomial.C center) Q
  let high : {l : Fin K // k ≤ l.val} → MvPolynomial (Fin (r + 1)) E[X] :=
    fun l ↦ commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K l.val
  let cuts : Fin n → MvPolynomial (Fin (r + 1)) E[X] := fun i ↦
    taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
      (Polynomial.C (iota (domain i))) (powerBatchedCoordinate fun t ↦ iota (w t i))
  have hKh : h ≤ D := by dsimp only [D]; omega
  have hgHeight : ChallengeHeightLE g D :=
    (challengeHeightLE_initialJetEquationOver center Q hheight).mono hKh
  have hsHeight : ChallengeHeightLE s D :=
    (challengeHeightLE_initialJetSeparantOver Q center hheight).mono hKh
  have hhighHeight : ∀ i, ChallengeHeightLE (high i) (M * D) := by
    intro i
    exact (challengeHeightLE_commonTaylorNumeratorOver Q center hheight K i.val).mono (by
      exact Nat.mul_le_mul_left (2 * K) hKh)
  have hcutsHeight : ∀ i, ChallengeHeightLE (cuts i) (M * D) := by
    intro i
    apply (taylorCurveAgreementEquationOver_bidegree center Q v h hv hjet hheight K
      (iota (domain i)) (powerBatchedCoordinate fun t ↦ iota (w t i))
      (powerBatchedCoordinate_natDegree_le _)).1.mono
    have hell : ℓ ≤ 2 * K * ℓ := Nat.le_mul_of_pos_left ℓ (by omega)
    dsimp only [M, D]
    calc
      ℓ + 2 * K * h ≤ 2 * K * ℓ + 2 * K * h := Nat.add_le_add_right hell _
      _ = 2 * K * (ℓ + h) := by ring
  have hgDegree : g.totalDegree + 1 ≤ v + 1 := by
    exact Nat.add_le_add_right ((totalDegree_initialJetEquationOver_le
      (Polynomial.C center) Q).trans hjet) 1
  have hhighDegree : ∀ i, (high i).totalDegree + M + 1 ≤ B := by
    intro i
    have hi := (commonTaylorNumeratorOver_bidegree center Q v h hv hjet hheight K i.val).2
    change (commonTaylorNumeratorOver (F := E) (Polynomial.C center) Q K i.val).totalDegree +
      M + 1 ≤ B
    have he : 2 * K * (v - 1) + 2 * K = 2 * K * v := by
      calc
        _ = 2 * K * (v - 1) + (2 * K) * 1 := by rw [Nat.mul_one]
        _ = 2 * K * (v - 1 + 1) := by rw [Nat.mul_add]
        _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ v)]
    dsimp only [M, B]
    omega
  have hcutsDegree : ∀ i, (cuts i).totalDegree + M + 1 ≤ B := by
    intro i
    have hi := (taylorCurveAgreementEquationOver_bidegree center Q v h hv hjet hheight K
      (iota (domain i)) (powerBatchedCoordinate fun t ↦ iota (w t i))
      (powerBatchedCoordinate_natDegree_le _)).2
    change (taylorAgreementEquationOver (F := E) (Polynomial.C center) Q K
      (Polynomial.C (iota (domain i)))
      (powerBatchedCoordinate fun t ↦ iota (w t i))).totalDegree + M + 1 ≤ B
    have he : 2 * K * (v - 1) + 2 * K = 2 * K * v := by
      calc
        _ = 2 * K * (v - 1) + (2 * K) * 1 := by rw [Nat.mul_one]
        _ = 2 * K * (v - 1 + 1) := by rw [Nat.mul_add]
        _ = _ := by rw [Nat.sub_add_cancel (by omega : 1 ≤ v)]
    dsimp only [M, B]
    omega
  apply powerMoment_incidence_off_source_excluded
    (D := D) (M := M) (d := r + 1) (initialDegree := v + 1) (B := B)
    (ι := {l : Fin K // k ≤ l.val}) (g := g) (s := s) (high := high) (cuts := cuts)
    (excluded := sourceCurveTupleLocus domain w iota center Q K k L) (S := S)
    hD hgHeight hsHeight
  · simpa only [g, symbolicSourceInitialEquation, flattenChallenge] using hinit
  · simpa only [s, symbolicSourceSeparant, flattenChallenge] using hsep
  · exact hgDegree
  · exact hhighHeight
  · exact hhighDegree
  · exact hcutsHeight
  · exact hcutsDegree
  · simp
  · dsimp only [B]
    omega
  · exact hL
  · exact hLA
  · exact hAn
  · intro J hJ hsJ hgJ hhighJ hdJ hcutsJ
    rw [← sourceCurveTupleLocus_of_exponent_two_mul_eq]
    apply principalOpen_subset_sourceCurveTupleLocus_of_exponent domain w iota center Q hK hkL
      (2 * K) (taylorExponentSufficient_two_mul r K) J hJ
    · simpa only [s, symbolicSourceSeparant, flattenChallenge] using hsJ
    · simpa only [g, symbolicSourceInitialEquation, flattenChallenge] using hgJ
    · intro q hq
      simp only [sourceCurveHighCuts_of_exponent, List.mem_map, Finset.mem_toList] at hq
      obtain ⟨l, _, rfl⟩ := hq
      simpa only [high, symbolicSourceNumerator, flattenChallenge] using
        hhighJ ⟨l.val, l.property⟩
    · exact hdJ
    · simpa only [cuts, symbolicSourceCurveAgreement,
        symbolicSourceCurveAgreement_of_exponent, flattenChallenge] using hcutsJ
  · intro x hx
    refine ⟨?_, ?_, ?_, (hS x hx).2.2.2⟩
    · simpa only [g, symbolicSourceInitialEquation, flattenChallenge] using (hS x hx).1
    · simpa only [s, symbolicSourceSeparant, flattenChallenge] using (hS x hx).2.1
    · intro i
      simpa only [high, symbolicSourceNumerator, flattenChallenge] using
        (hS x hx).2.2.1 i.val i.property
  · intro x hx
    simpa only [cuts, symbolicSourceCurveAgreement, flattenChallenge] using hA x hx

end ReedSolomon
