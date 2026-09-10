/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Quang Dao, Justin Thaler
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Index
public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.Identity
public import Mathlib.Data.Finsupp.SMul


/-!
# Linear maps for the hidden-derivative local constraints

This file defines the exact homogeneous linear constraints imposed at one received point.  The
polynomial formulation retains precisely the monomials `T^i E^b Y^e` of contact order
`i + d * b < m`; the coordinate formulation extracts the same coefficients.  It also separates
the point-dependent map `localConstraintAt` from the point-independent intermediate map
`enlargedLocalConstraintMap`.

The factorization first translates `X = center + T` and `Y₀ = received + T U`, reduces modulo
`T^m`, and only then rewrites `U = E + localJetSum`.  The preliminary truncation is sound because
the rewrite cannot turn a term of `T`-degree at least `m` into one of contact order below `m`.

The maps on `ExactInterpolationCoefficients` are proof-facing: their domain uses the canonical
finite support from `Interpolation/Index.lean`. These maps specify the linear constraints
mathematically; they do not assert an executable enumeration or linear solver.

The support arguments are adapted, with permission, from Kai Zhe Zheng's `rs-ld-mca`
formalization at commit `9699ee7a6143f6efe1d8cfed84998a4f8c79c40f`, files
`Defs/ConstraintMap.lean`, `Lemmas/ConstraintMap.lean`, and
`Lemmas/ConstraintFactorization.lean`.  The exact interpolation-coordinate adapters are new.

## References

* Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed--Solomon
  Codes up to Capacity in the Low-Rate Regime*, ECCC TR26-164, Section 3.
* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26].
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

open scoped BigOperators Pointwise

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R : Type*} [CommRing R]
variable {d D A m M W : ℕ}

/-! ### Coefficient projections -/

/-- Coefficientwise projection onto the local monomials satisfying `predicate`. -/
def filterLocalMonomials (predicate : (LocalVariable d →₀ ℕ) → Prop)
    [DecidablePred predicate] :
    LocalPolynomial R d →ₗ[R] LocalPolynomial R d where
  toFun F := AddMonoidAlgebra.ofCoeff
    (Finsupp.filter predicate (AddMonoidAlgebra.coeff F))
  map_add' F G := by
    apply AddMonoidAlgebra.coeff_injective
    exact Finsupp.filter_add
  map_smul' a F := by
    apply AddMonoidAlgebra.coeff_injective
    exact Finsupp.filter_smul

@[simp]
theorem coeff_filterLocalMonomials
    (predicate : (LocalVariable d →₀ ℕ) → Prop)
    [DecidablePred predicate] (F : LocalPolynomial R d)
    (e : LocalVariable d →₀ ℕ) :
    MvPolynomial.coeff e (filterLocalMonomials (R := R) predicate F) =
      if predicate e then MvPolynomial.coeff e F else 0 := by
  change Finsupp.filter predicate (AddMonoidAlgebra.coeff F) e = _
  exact Finsupp.filter_apply _ _ _

/-- Truncation modulo `T^m`, represented by retaining monomials of `T`-degree below `m`. -/
def truncateLocalT (m : ℕ) : LocalPolynomial R d →ₗ[R] LocalPolynomial R d :=
  filterLocalMonomials (R := R) fun e ↦ e (localT d) < m

/-- Retain precisely the monomials of contact order below `m`. -/
def projectLowContact (m : ℕ) : LocalPolynomial R d →ₗ[R] LocalPolynomial R d :=
  filterLocalMonomials (R := R) fun e ↦ localContactOrder d e < m

/-- Exponent vectors of contact order strictly below `m`. -/
abbrev LowContactIndex (d m : ℕ) :=
  {e : LocalVariable d →₀ ℕ // localContactOrder d e < m}

/-- Simultaneous extraction of every coefficient of contact order below `m`. -/
def lowContactCoefficients (m : ℕ) :
    LocalPolynomial R d →ₗ[R] (LowContactIndex d m → R) :=
  LinearMap.pi fun e : LowContactIndex d m ↦ MvPolynomial.lcoeff R e.1

theorem filterLocalMonomials_eq_zero_iff
    (predicate : (LocalVariable d →₀ ℕ) → Prop)
    [DecidablePred predicate] (F : LocalPolynomial R d) :
    filterLocalMonomials (R := R) predicate F = 0 ↔
      ∀ e, predicate e → MvPolynomial.coeff e F = 0 := by
  rw [← AddMonoidAlgebra.coeff_eq_zero]
  change Finsupp.filter predicate (AddMonoidAlgebra.coeff F) = 0 ↔ _
  simpa only [MvPolynomial.coeff] using
    (Finsupp.filter_eq_zero_iff (p := predicate)
      (f := AddMonoidAlgebra.coeff F))

theorem projectLowContact_eq_zero_iff (m : ℕ) (F : LocalPolynomial R d) :
    projectLowContact (R := R) (d := d) m F = 0 ↔
      ∀ e, localContactOrder d e < m → MvPolynomial.coeff e F = 0 := by
  exact filterLocalMonomials_eq_zero_iff
    (R := R) (d := d) (fun e ↦ localContactOrder d e < m) F

theorem lowContactCoefficients_eq_zero_iff (m : ℕ) (F : LocalPolynomial R d) :
    lowContactCoefficients (R := R) (d := d) m F = 0 ↔
      ∀ e, localContactOrder d e < m → MvPolynomial.coeff e F = 0 := by
  constructor
  · intro h e he
    have happ := congrFun h ⟨e, he⟩
    simpa [lowContactCoefficients] using happ
  · intro h
    ext e
    simpa [lowContactCoefficients] using h e.1 e.2

theorem projectLowContact_eq_zero_iff_lowContactCoefficients_eq_zero
    (m : ℕ) (F : LocalPolynomial R d) :
    projectLowContact (R := R) (d := d) m F = 0 ↔
      lowContactCoefficients (R := R) (d := d) m F = 0 := by
  rw [projectLowContact_eq_zero_iff, lowContactCoefficients_eq_zero_iff]

/-! ### Point-dependent and enlarged maps -/

/-- The point-independent enlarged local map: rewrite `U` in terms of `E` and the visible jets,
then retain only coefficients of contact order below `m`. -/
def enlargedLocalConstraintMap (m : ℕ) :
    LocalPolynomial R d →ₗ[R] LocalPolynomial R d :=
  (projectLowContact (R := R) (d := d) m).comp
    (rewriteUToE (R := R) (d := d)).toLinearMap

/-- Translation to local `T,U,Y` coordinates followed by reduction modulo `T^m`. -/
def translatedLocalTruncation (m : ℕ) (center received : R) :
    DifferentialPolynomial R d →ₗ[R] LocalPolynomial R d :=
  (truncateLocalT (R := R) (d := d) m).comp
    (translateToU d center received).toLinearMap

/-- The homogeneous local constraint map at the received point `(center, received)`. -/
def localConstraintAt (m : ℕ) (center received : R) :
    DifferentialPolynomial R d →ₗ[R] LocalPolynomial R d :=
  (projectLowContact (R := R) (d := d) m).comp
    (unscaledLocalSubstitution d center received).toLinearMap

/-- Coordinate form of the homogeneous local constraints. -/
def localConstraintCoordinatesAt (m : ℕ) (center received : R) :
    DifferentialPolynomial R d →ₗ[R] (LowContactIndex d m → R) :=
  (lowContactCoefficients (R := R) (d := d) m).comp
    (unscaledLocalSubstitution d center received).toLinearMap

/-- A polynomial satisfies the local constraints precisely when the point-dependent polynomial
projection vanishes. -/
def SatisfiesLocalConstraints (m : ℕ) (center received : R)
    (Q : DifferentialPolynomial R d) : Prop :=
  localConstraintAt (d := d) m center received Q = 0

theorem satisfiesLocalConstraints_iff_coordinates_eq_zero
    (m : ℕ) (center received : R) (Q : DifferentialPolynomial R d) :
    SatisfiesLocalConstraints m center received Q ↔
      localConstraintCoordinatesAt (d := d) m center received Q = 0 := by
  rw [SatisfiesLocalConstraints, localConstraintAt, localConstraintCoordinatesAt,
    LinearMap.comp_apply, LinearMap.comp_apply,
    projectLowContact_eq_zero_iff_lowContactCoefficients_eq_zero]

/-! ### Truncation factorization -/

private theorem support_weight_C_eq_zero {M₀ : Type*} [AddCommMonoid M₀]
    (w : LocalVariable d → M₀) (a : R)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (C a : LocalPolynomial R d).support) :
    Finsupp.weight w e = 0 := by
  classical
  have he' : e ∈ ({0} : Finset (LocalVariable d →₀ ℕ)) :=
    MvPolynomial.support_monomial_subset he
  have : e = 0 := Finset.mem_singleton.mp he'
  subst e
  exact map_zero (Finsupp.weight w)

private theorem support_weight_X_eq {M₀ : Type*} [AddCommMonoid M₀]
    (w : LocalVariable d → M₀) (i : LocalVariable d)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (X i : LocalPolynomial R d).support) :
    Finsupp.weight w e = w i := by
  classical
  have he' : e ∈ ({Finsupp.single i 1} : Finset (LocalVariable d →₀ ℕ)) :=
    MvPolynomial.support_monomial_subset he
  have : e = Finsupp.single i 1 := Finset.mem_singleton.mp he'
  subst e
  rw [Finsupp.weight_single]
  exact one_nsmul (w i)

private theorem support_weight_add_le {M₀ : Type*} [AddCommMonoid M₀]
    [PartialOrder M₀] (w : LocalVariable d → M₀)
    {P Q : LocalPolynomial R d} {a : M₀}
    (hP : ∀ e ∈ P.support, Finsupp.weight w e ≤ a)
    (hQ : ∀ e ∈ Q.support, Finsupp.weight w e ≤ a)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (P + Q).support) :
    Finsupp.weight w e ≤ a := by
  classical
  rcases Finset.mem_union.mp (MvPolynomial.support_add he) with heP | heQ
  · exact hP e heP
  · exact hQ e heQ

private theorem support_weight_sum_le {M₀ : Type*} [AddCommMonoid M₀]
    [PartialOrder M₀] (w : LocalVariable d → M₀)
    {ι : Type*} (s : Finset ι)
    (P : ι → LocalPolynomial R d) {a : M₀}
    (hP : ∀ i ∈ s, ∀ e ∈ (P i).support, Finsupp.weight w e ≤ a)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (s.sum P).support) :
    Finsupp.weight w e ≤ a := by
  classical
  rcases Finset.mem_biUnion.mp (MvPolynomial.support_sum he) with ⟨i, hi, hei⟩
  exact hP i hi e hei

private theorem support_weight_mul_le {M₀ : Type*} [AddCommMonoid M₀]
    [PartialOrder M₀] [IsOrderedAddMonoid M₀]
    (w : LocalVariable d → M₀) {P Q : LocalPolynomial R d} {a b : M₀}
    (hP : ∀ e ∈ P.support, Finsupp.weight w e ≤ a)
    (hQ : ∀ e ∈ Q.support, Finsupp.weight w e ≤ b)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (P * Q).support) :
    Finsupp.weight w e ≤ a + b := by
  classical
  have he' : e ∈ P.support + Q.support := MvPolynomial.support_mul P Q he
  rcases Finset.mem_add.mp he' with ⟨eP, heP, eQ, heQ, rfl⟩
  simpa using add_le_add (hP eP heP) (hQ eQ heQ)

private theorem support_weight_pow_le {M₀ : Type*} [AddCommMonoid M₀]
    [PartialOrder M₀] [IsOrderedAddMonoid M₀]
    (w : LocalVariable d → M₀) {P : LocalPolynomial R d} {a : M₀}
    (hP : ∀ e ∈ P.support, Finsupp.weight w e ≤ a) (n : ℕ)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (P ^ n).support) :
    Finsupp.weight w e ≤ n • a := by
  induction n generalizing e with
  | zero => simpa using le_of_eq (support_weight_C_eq_zero w (1 : R) he)
  | succ n ih =>
      rw [pow_succ] at he
      simpa [succ_nsmul] using support_weight_mul_le w
        (fun e he ↦ ih he) hP he

private theorem support_weight_prod_le {M₀ : Type*} [AddCommMonoid M₀]
    [PartialOrder M₀] [IsOrderedAddMonoid M₀]
    (w : LocalVariable d → M₀) {ι : Type*} (s : Finset ι)
    (P : ι → LocalPolynomial R d) (a : ι → M₀)
    (hP : ∀ i ∈ s, ∀ e ∈ (P i).support, Finsupp.weight w e ≤ a i)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (s.prod P).support) :
    Finsupp.weight w e ≤ s.sum a := by
  classical
  induction s using Finset.induction_on generalizing e with
  | empty => simpa using le_of_eq (support_weight_C_eq_zero w (1 : R) he)
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi] at he
      rw [Finset.sum_insert hi]
      exact support_weight_mul_le w
        (hP i (Finset.mem_insert_self i s))
        (fun e he ↦ ih (fun j hj ↦ hP j (Finset.mem_insert_of_mem hj)) he) he

private theorem support_weight_bind₁_le {M₀ : Type*} [AddCommMonoid M₀]
    [PartialOrder M₀] [IsOrderedAddMonoid M₀]
    (wSource wTarget : LocalVariable d → M₀)
    (f : LocalVariable d → LocalPolynomial R d)
    (hf : ∀ i, ∀ e ∈ (f i).support, Finsupp.weight wTarget e ≤ wSource i)
    {P : LocalPolynomial R d} {a : M₀}
    (hP : ∀ u ∈ P.support, Finsupp.weight wSource u ≤ a)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (MvPolynomial.bind₁ f P).support) :
    Finsupp.weight wTarget e ≤ a := by
  classical
  rw [MvPolynomial.as_sum P, map_sum] at he
  rcases Finset.mem_biUnion.mp (MvPolynomial.support_sum he) with ⟨u, hu, heu⟩
  rw [MvPolynomial.bind₁_monomial] at heu
  have hprod : ∀ v ∈ (u.support.prod fun i ↦ f i ^ u i).support,
      Finsupp.weight wTarget v ≤ Finsupp.weight wSource u := by
    intro v hv
    simpa only [Finsupp.weight_apply, Finsupp.sum] using
      (support_weight_prod_le wTarget u.support
        (fun i ↦ f i ^ u i) (fun i ↦ u i • wSource i)
        (fun i hi v hv ↦ support_weight_pow_le wTarget (hf i) (u i) hv) hv)
  have hmul := support_weight_mul_le wTarget
    (a := (0 : M₀)) (b := Finsupp.weight wSource u)
    (fun v hv ↦ le_of_eq (support_weight_C_eq_zero wTarget _ hv)) hprod heu
  have hmono : Finsupp.weight wTarget e ≤ Finsupp.weight wSource u := by
    simpa using hmul
  exact hmono.trans (hP u hu)

/-- Negative contact order after the `U`-to-`E` rewrite. -/
private def negContactWeight (d : ℕ) : LocalVariable d → ℤ
  | none => -1
  | some none => -(d : ℤ)
  | some (some _) => 0

/-- Negative `T`-degree before the rewrite. -/
private def negTWeight (d : ℕ) : LocalVariable d → ℤ
  | none => -1
  | some _ => 0

private theorem weight_negContactWeight (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (negContactWeight d) e = -(localContactOrder d e : ℤ) := by
  classical
  rw [Finsupp.weight_apply, localContactOrder,
    Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp),
    Finsupp.sum_fintype _ _ (by simp)]
  simp_rw [Fintype.sum_option]
  simp [negContactWeight, localContactWeight, Nat.cast_mul, mul_comm]
  ring

private theorem weight_negTWeight (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (negTWeight d) e = -(e (localT d) : ℤ) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp),
    Fintype.sum_option, Fintype.sum_option]
  simp [negTWeight, localT]

private def rewriteLocalGenerator : LocalVariable d → LocalPolynomial R d
  | none => X (localT d)
  | some none => X (localE d) + localJetSum d
  | some (some j) => X (localY j)

private theorem localJetSummand_negContact_nonpos (j : Fin d)
    {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (C ((-1 : R) ^ j.val) * X (localT d) ^ j.val * X (localY j)).support) :
    Finsupp.weight (negContactWeight d) e ≤ 0 := by
  have hpow : ∀ z ∈ (X (localT d) ^ j.val : LocalPolynomial R d).support,
      Finsupp.weight (negContactWeight d) z ≤ 0 := by
    intro z hz
    have h := support_weight_pow_le (negContactWeight d)
      (a := (-1 : ℤ))
      (fun z hz ↦ (support_weight_X_eq _ (localT d) hz).le) j.val hz
    simpa [negContactWeight, localT] using h.trans (by simp : j.val • (-1 : ℤ) ≤ 0)
  have hleft : ∀ z ∈
      (C ((-1 : R) ^ j.val) * X (localT d) ^ j.val).support,
      Finsupp.weight (negContactWeight d) z ≤ 0 := by
    intro z hz
    simpa using support_weight_mul_le (negContactWeight d)
      (a := (0 : ℤ)) (b := (0 : ℤ))
      (fun z hz ↦ (support_weight_C_eq_zero _ _ hz).le) hpow hz
  simpa [negContactWeight, localY] using support_weight_mul_le
    (negContactWeight d) (a := (0 : ℤ)) (b := (0 : ℤ)) hleft
    (fun z hz ↦ (support_weight_X_eq _ (localY j) hz).le) he

private theorem rewriteLocalGenerator_negContact_le_negT
    (v : LocalVariable d) {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (rewriteLocalGenerator (R := R) v).support) :
    Finsupp.weight (negContactWeight d) e ≤ negTWeight d v := by
  rcases v with (_ | (_ | j))
  · rw [support_weight_X_eq _ (localT d) he]
    simp [negContactWeight, negTWeight, localT]
  · exact support_weight_add_le (negContactWeight d)
      (fun z hz ↦ by
        rw [support_weight_X_eq _ (localE d) hz]
        simp [negContactWeight, negTWeight, localE, localAux])
      (fun z hz ↦ by
        rw [localJetSum] at hz
        exact support_weight_sum_le (negContactWeight d) Finset.univ
          (fun j : Fin d ↦
            C ((-1 : R) ^ j.val) * X (localT d) ^ j.val * X (localY j))
          (fun j _ z hz ↦ localJetSummand_negContact_nonpos j hz) hz) he
  · rw [support_weight_X_eq _ (localY j) he]
    simp [negContactWeight, negTWeight, localY]

private theorem mem_support_filterLocalMonomials
    (predicate : (LocalVariable d →₀ ℕ) → Prop) [DecidablePred predicate]
    (F : LocalPolynomial R d) {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (filterLocalMonomials (R := R) predicate F).support) :
    predicate e ∧ e ∈ F.support := by
  have hc := he
  rw [MvPolynomial.mem_support_iff, coeff_filterLocalMonomials] at hc
  by_cases h : predicate e
  · simpa only [h, if_true, MvPolynomial.mem_support_iff] using And.intro h hc
  · simp [h] at hc

private theorem truncateLocalT_add_highPart (F : LocalPolynomial R d) :
    truncateLocalT (R := R) (d := d) m F +
      filterLocalMonomials (R := R) (fun e ↦ ¬e (localT d) < m) F = F := by
  classical
  apply MvPolynomial.ext
  intro e
  rw [MvPolynomial.coeff_add, truncateLocalT, coeff_filterLocalMonomials,
    coeff_filterLocalMonomials]
  by_cases h : e (localT d) < m <;> simp [h]

private theorem projectLowContact_rewrite_highPart_eq_zero (F : LocalPolynomial R d) :
    projectLowContact (R := R) (d := d) m
        (rewriteUToE d (filterLocalMonomials (R := R)
          (fun e ↦ ¬e (localT d) < m) F)) = 0 := by
  classical
  let H : LocalPolynomial R d :=
    filterLocalMonomials (R := R) (fun e ↦ ¬e (localT d) < m) F
  change projectLowContact (R := R) (d := d) m (rewriteUToE d H) = 0
  have hSource : ∀ u ∈ H.support,
      Finsupp.weight (negTWeight d) u ≤ -(m : ℤ) := by
    intro u hu
    have hu' := mem_support_filterLocalMonomials
      (R := R) (d := d) (fun e ↦ ¬e (localT d) < m) F hu
    rw [weight_negTWeight]
    omega
  have hRewrite : ∀ e ∈ (rewriteUToE d H).support,
      Finsupp.weight (negContactWeight d) e ≤ -(m : ℤ) := by
    intro e he
    change e ∈ (MvPolynomial.bind₁ (rewriteLocalGenerator (R := R)) H).support at he
    exact support_weight_bind₁_le (negTWeight d) (negContactWeight d)
      (rewriteLocalGenerator (R := R)) rewriteLocalGenerator_negContact_le_negT hSource he
  apply MvPolynomial.ext
  intro e
  rw [MvPolynomial.coeff_zero, projectLowContact, coeff_filterLocalMonomials]
  by_cases hcontact : localContactOrder d e < m
  · simp only [hcontact, if_true]
    by_contra hcoeff
    have he : e ∈ (rewriteUToE d H).support := MvPolynomial.mem_support_iff.mpr hcoeff
    have hbound := hRewrite e he
    rw [weight_negContactWeight] at hbound
    omega
  · simp [hcontact]

private theorem projectLowContact_rewrite_eq_truncated (F : LocalPolynomial R d) :
    projectLowContact (R := R) (d := d) m (rewriteUToE d F) =
      projectLowContact (R := R) (d := d) m
        (rewriteUToE d (truncateLocalT (R := R) (d := d) m F)) := by
  let H : LocalPolynomial R d :=
    filterLocalMonomials (R := R) (fun e ↦ ¬e (localT d) < m) F
  have hdecomp : truncateLocalT (R := R) (d := d) m F + H = F :=
    truncateLocalT_add_highPart F
  have hzero : projectLowContact (R := R) (d := d) m (rewriteUToE d H) = 0 :=
    projectLowContact_rewrite_highPart_eq_zero F
  calc
    projectLowContact (R := R) (d := d) m (rewriteUToE d F) =
        projectLowContact (R := R) (d := d) m
          (rewriteUToE d (truncateLocalT (R := R) (d := d) m F + H)) :=
      congrArg (fun G ↦ projectLowContact (R := R) (d := d) m (rewriteUToE d G))
        hdecomp.symm
    _ = projectLowContact (R := R) (d := d) m
          (rewriteUToE d (truncateLocalT (R := R) (d := d) m F)) +
        projectLowContact (R := R) (d := d) m (rewriteUToE d H) := by
      rw [map_add, map_add]
    _ = _ := by rw [hzero, add_zero]

/-- Truncation modulo `T^m` does not change the enlarged low-contact constraints. -/
@[simp]
theorem enlargedLocalConstraintMap_truncateLocalT (m : ℕ) (F : LocalPolynomial R d) :
    enlargedLocalConstraintMap (R := R) (d := d) m
      (truncateLocalT (R := R) (d := d) m F) =
        enlargedLocalConstraintMap (R := R) (d := d) m F := by
  exact (projectLowContact_rewrite_eq_truncated F).symm

/-- The exact point-dependent map factors through the point-independent enlarged map. -/
theorem localConstraintAt_eq_enlarged_comp_translated
    (m : ℕ) (center received : R) :
    localConstraintAt (d := d) m center received =
      (enlargedLocalConstraintMap (R := R) (d := d) m).comp
        (translatedLocalTruncation (d := d) m center received) := by
  apply LinearMap.ext
  intro Q
  change projectLowContact (R := R) (d := d) m
      (unscaledLocalSubstitution d center received Q) =
    projectLowContact (R := R) (d := d) m
      (rewriteUToE d (truncateLocalT (R := R) (d := d) m
        (translateToU d center received Q)))
  rw [unscaledLocalSubstitution_eq_rewrite_comp_translate]
  exact projectLowContact_rewrite_eq_truncated (translateToU d center received Q)

@[simp]
theorem localConstraintAt_apply_eq_enlarged_translated
    (m : ℕ) (center received : R) (Q : DifferentialPolynomial R d) :
    localConstraintAt (d := d) m center received Q =
      enlargedLocalConstraintMap (R := R) (d := d) m
        (translatedLocalTruncation (d := d) m center received Q) := by
  exact DFunLike.congr_fun
    (localConstraintAt_eq_enlarged_comp_translated (d := d) m center received) Q

/-! ### Canonical finite interpolation coordinates -/

/-- The local constraint map restricted to the exact finite interpolation space. -/
def exactLocalConstraintAt (hdD : d < D) (m : ℕ) (center received : R) :
    exactInterpolationSpace R D A d m M W hdD →ₗ[R] LocalPolynomial R d :=
  (localConstraintAt (d := d) m center received).domRestrict
    (exactInterpolationSpace R D A d m M W hdD)

/-- The local constraint map on canonical finite interpolation coefficients. -/
def exactCoefficientLocalConstraintAt (hdD : d < D) (m : ℕ)
    (center received : R) :
    ExactInterpolationCoefficients R D A d m M W hdD →ₗ[R] LocalPolynomial R d :=
  exactInterpolationCoefficientEvaluator hdD
    (localConstraintAt (d := d) m center received)

/-- The coefficient-coordinate map evaluates a singleton column as the corresponding global
monomial and then imposes the local constraint. -/
@[simp]
theorem exactCoefficientLocalConstraintAt_single (hdD : d < D)
    (u : ExactInterpolationIndex D A d m M W hdD) (a center received : R) :
    exactCoefficientLocalConstraintAt (D := D) (A := A) (M := M) (W := W)
      hdD m center received (Finsupp.single u a) =
        localConstraintAt (d := d) m center received (MvPolynomial.monomial u.1 a) := by
  simp [exactCoefficientLocalConstraintAt]

/-- Aggregate the exact local maps over an arbitrary finite received-word index set. -/
def globalExactCoefficientConstraintMap {ι : Type*} [Fintype ι]
    (hdD : d < D) (centers received : ι → R) :
    ExactInterpolationCoefficients R D A d m M W hdD →ₗ[R]
      (ι → LocalPolynomial R d) :=
  LinearMap.pi fun i ↦
    exactCoefficientLocalConstraintAt (D := D) (A := A) (M := M) (W := W)
      hdD m (centers i) (received i)

@[simp]
theorem globalExactCoefficientConstraintMap_apply {ι : Type*} [Fintype ι]
    (hdD : d < D) (centers received : ι → R)
    (v : ExactInterpolationCoefficients R D A d m M W hdD) (i : ι) :
    globalExactCoefficientConstraintMap hdD centers received v i =
      exactCoefficientLocalConstraintAt (D := D) (A := A) (M := M) (W := W)
        hdD m (centers i) (received i) v := by
  rfl

end ReedSolomon.HiddenDerivative
