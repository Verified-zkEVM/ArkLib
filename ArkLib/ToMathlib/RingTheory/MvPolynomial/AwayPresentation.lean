/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertAlgHom
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# A presentation of a principal localization and its affine Hilbert function

Let `R` be a commutative ring, `I` an ideal of `MvPolynomial σ R` and `s` a polynomial, and write
`A = MvPolynomial σ R ⧸ I` and `A_s` for the localization of `A` away from the class of `s`. The
algebra map `awayPresentation I s : MvPolynomial (Option σ) R →ₐ[R] A_s` sends the variable
`some i` to the class of `X i` and the new variable `none` to the inverse of the class of `s`. It
is surjective, so `A_s` is the quotient of `MvPolynomial (Option σ) R` by its kernel
`awayPresentationIdeal I s` (`awayPresentationEquiv`).

Over a field `k`, write `H(I, N)` for `affineHilbertFunction I N` and `K` for
`awayPresentationIdeal I s`. With `d = totalDegree s`:

* `H(K, N) ≤ H(I, (d + 1) * N)` for every `I` and `s`. Multiplying a fraction of presentation
  degree at most `N` by `s ^ N` clears the denominators and leaves the class of a polynomial of
  total degree at most `(d + 1) * N`, and multiplication by the unit `s ^ N` is injective.
* `H(I, N) ≤ H(K, N)` when the class of `s` is a non-zero-divisor on `A`. Then `A → A_s` is
  injective and sends the class of `X i` to the class of the variable `some i`, of degree `1`.

So the Hilbert polynomials of `I` and `K` have the same natural degree when `s` is regular on
`A`. A consequence is that a surjection onto `A_s` from the coordinate ring of an ideal `J`
bounds the natural degree for `I` by the natural degree for `J`; in particular a surjection from a
polynomial ring in `τ` bounds it by `Nat.card τ`.

The regularity hypothesis is needed for the lower bounds: for `I = ⊥` in one variable and `s = 0`,
the localization is the zero ring, `K = ⊤`, and `H(K, N) = 0 < N + 1 = H(I, N)`.

## Main statements

* `IsLocalization.Away.algebraMap_injective_of_isLeftRegular`: localizing away from a regular
  element is injective.
* `MvPolynomial.awayPresentation`, `MvPolynomial.awayPresentation_surjective`,
  `MvPolynomial.awayPresentationIdeal`, `MvPolynomial.awayPresentationEquiv`: the presentation.
* `MvPolynomial.affineHilbertFunction_awayPresentationIdeal_le`,
  `MvPolynomial.affineHilbertFunction_le_awayPresentationIdeal`: the two Hilbert-function bounds.
* `MvPolynomial.natDegree_affineHilbertPolynomial_awayPresentationIdeal`: equality of natural
  degrees for a regular `s`.
* `MvPolynomial.natDegree_affineHilbertPolynomial_le_of_surjective_away`,
  `MvPolynomial.natDegree_affineHilbertPolynomial_le_of_surjective_away_away`,
  `MvPolynomial.natDegree_affineHilbertPolynomial_le_of_away_range`: bounds from localized
  polynomial presentations.
* `MvPolynomial.natDegree_affineHilbertPolynomial_le_card_of_surjective_away`,
  `MvPolynomial.natDegree_affineHilbertPolynomial_le_card_of_adjoin_eq_top_away`: dimension
  bounds from surjections onto a principal localization.
-/

@[expose] public section

noncomputable section

open Filter

namespace IsLocalization.Away

/-- Localizing away from a regular element `x` is injective: if `x ^ n * a = x ^ n * b` then
`a = b`, because every power of a regular element is regular. -/
theorem algebraMap_injective_of_isLeftRegular {R S : Type*} [CommSemiring R] [CommSemiring S]
    [Algebra R S] {x : R} [IsLocalization.Away x S] (hx : IsLeftRegular x) :
    Function.Injective (algebraMap R S) :=
  IsLocalization.injectiveₛ S fun _ hm ↦ by
    obtain ⟨n, rfl⟩ := Submonoid.mem_powers_iff _ _ |>.mp hm
    exact (isLeftRegular_iff_isRegular.mp hx).pow n

end IsLocalization.Away

namespace MvPolynomial

section Presentation

variable {R σ : Type*} [CommRing R] (I : Ideal (MvPolynomial σ R)) (s : MvPolynomial σ R)

/-- The presentation of the localization of `MvPolynomial σ R ⧸ I` away from the class of `s`: the
variable `some i` goes to the class of `X i`, and the new variable `none` goes to the inverse of
the class of `s`. -/
def awayPresentation :
    MvPolynomial (Option σ) R →ₐ[R] Localization.Away (Ideal.Quotient.mk I s) :=
  aeval fun o ↦ o.elim (IsLocalization.Away.invSelf (Ideal.Quotient.mk I s))
    fun i ↦ algebraMap (MvPolynomial σ R ⧸ I) _ (Ideal.Quotient.mk I (X i))

/-- The new variable goes to the inverse of the class of `s`. -/
@[simp]
theorem awayPresentation_X_none :
    awayPresentation I s (X none) = IsLocalization.Away.invSelf (Ideal.Quotient.mk I s) :=
  aeval_X _ _

/-- The variable `some i` goes to the class of `X i`. -/
@[simp]
theorem awayPresentation_X_some (i : σ) :
    awayPresentation I s (X (some i)) =
      algebraMap (MvPolynomial σ R ⧸ I) _ (Ideal.Quotient.mk I (X i)) :=
  aeval_X _ _

/-- A polynomial in the original variables goes to the image of its class in the localization. -/
theorem awayPresentation_rename_some (p : MvPolynomial σ R) :
    awayPresentation I s (rename some p) =
      algebraMap (MvPolynomial σ R ⧸ I) (Localization.Away (Ideal.Quotient.mk I s))
        (Ideal.Quotient.mk I p) := by
  have h : (awayPresentation I s).comp (rename some) =
      (IsScalarTower.toAlgHom R (MvPolynomial σ R ⧸ I)
        (Localization.Away (Ideal.Quotient.mk I s))).comp (Ideal.Quotient.mkₐ R I) := by
    refine algHom_ext fun i ↦ ?_
    simp
  exact DFunLike.congr_fun h p

/-- The presentation is surjective: a fraction `a / s ^ n` with `a` the class of `p` is the image
of `rename some p * X none ^ n`. -/
theorem awayPresentation_surjective : Function.Surjective (awayPresentation I s) := by
  intro z
  obtain ⟨n, a, hz⟩ := IsLocalization.Away.surj (Ideal.Quotient.mk I s) z
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective a
  refine ⟨rename some p * X none ^ n, ?_⟩
  rw [map_mul, map_pow, awayPresentation_rename_some, awayPresentation_X_none, ← hz, mul_assoc,
    ← mul_pow, IsLocalization.Away.mul_invSelf, one_pow, mul_one]

/-- The kernel of the presentation: `MvPolynomial (Option σ) R` modulo this ideal is the
localization (`awayPresentationEquiv`). -/
def awayPresentationIdeal : Ideal (MvPolynomial (Option σ) R) :=
  RingHom.ker (awayPresentation I s)

/-- Membership in the presentation ideal is vanishing under the presentation. -/
theorem mem_awayPresentationIdeal {p : MvPolynomial (Option σ) R} :
    p ∈ awayPresentationIdeal I s ↔ awayPresentation I s p = 0 :=
  RingHom.mem_ker

/-- The image of an element of `I` in the original variables lies in the presentation ideal. -/
theorem rename_some_mem_awayPresentationIdeal {p : MvPolynomial σ R} (hp : p ∈ I) :
    rename some p ∈ awayPresentationIdeal I s := by
  rw [mem_awayPresentationIdeal, awayPresentation_rename_some,
    Ideal.Quotient.eq_zero_iff_mem.mpr hp, map_zero]

/-- The relation saying that the new variable inverts `s` lies in the presentation ideal. -/
theorem X_none_mul_rename_some_sub_one_mem_awayPresentationIdeal :
    X none * rename some s - 1 ∈ awayPresentationIdeal I s := by
  rw [mem_awayPresentationIdeal, map_sub, map_mul, awayPresentation_X_none,
    awayPresentation_rename_some, map_one, mul_comm, IsLocalization.Away.mul_invSelf, sub_self]

/-- The localization of `MvPolynomial σ R ⧸ I` away from the class of `s` is the quotient of
`MvPolynomial (Option σ) R` by the presentation ideal. -/
def awayPresentationEquiv :
    (MvPolynomial (Option σ) R ⧸ awayPresentationIdeal I s) ≃ₐ[R]
      Localization.Away (Ideal.Quotient.mk I s) :=
  Ideal.quotientKerAlgEquivOfSurjective (awayPresentation_surjective I s)

/-- The equivalence sends the class of `p` to its image under the presentation. -/
@[simp]
theorem awayPresentationEquiv_mk (p : MvPolynomial (Option σ) R) :
    awayPresentationEquiv I s (Ideal.Quotient.mk _ p) = awayPresentation I s p :=
  Ideal.quotientKerAlgEquivOfSurjective_mk _ p

end Presentation

section Hilbert

variable {k σ τ : Type*} [Field k]

/-- Let `d` be the total degree of `s`. The presentation ideal `K` of the localization away from
`s` satisfies `H(K, N) ≤ H(I, (d + 1) * N)`, with no hypothesis on `I` or `s`.

A fraction of presentation degree at most `M` becomes, after multiplication by `s ^ M`, the image
of the class of a polynomial of total degree at most `(d + 1) * M`: multiplying by `X none`
cancels one factor of `s`, and multiplying by `X (some i)` adds a factor of `s * X i`, of degree at
most `d + 1`. Multiplication by the unit `s ^ N` is injective, and the image of the `N`-th piece of
the filtration of `A` in the localization has dimension at most `H(I, N)`. -/
theorem affineHilbertFunction_awayPresentationIdeal_le [Finite σ] (I : Ideal (MvPolynomial σ k))
    (s : MvPolynomial σ k) (N : ℕ) :
    affineHilbertFunction (awayPresentationIdeal I s) N ≤
      affineHilbertFunction I ((s.totalDegree + 1) * N) := by
  set A := MvPolynomial σ k ⧸ I
  set S := Localization.Away (Ideal.Quotient.mk I s)
  let : CommRing S := inferInstance
  let : Algebra A S := inferInstance
  let : AddCommMonoid S := NonUnitalNonAssocSemiring.toAddCommMonoid
  let : Module k S := Algebra.toModule
  set d := s.totalDegree
  set u : S := algebraMap A S (Ideal.Quotient.mk I s)
  set ι := (IsScalarTower.toAlgHom k A S).toLinearMap
  have hι : ∀ a, ι a = algebraMap A S a := fun _ ↦ rfl
  -- `T M`: fractions whose product with `u ^ M` has a numerator in degree `(d + 1) * M`.
  let T : ℕ → Submodule k S := fun M ↦
    ((quotientDegreeLE I ((d + 1) * M)).map ι).comap (LinearMap.mulLeft k (u ^ M))
  have hmemT : ∀ M z, z ∈ T M ↔
      ∃ a ∈ quotientDegreeLE I ((d + 1) * M), algebraMap A S a = u ^ M * z := by
    intro M z
    simp only [T, Submodule.mem_comap, Submodule.mem_map, LinearMap.mulLeft_apply, hι]
    exact Iff.rfl
  have hs_pow : ∀ j, Ideal.Quotient.mk I s ^ j ∈ quotientDegreeLE I (d * j) := fun j ↦ by
    rw [← map_pow]
    exact mk_mem_quotientDegreeLE ((totalDegree_pow s j).trans (Nat.mul_comm j d).le)
  have hT : Monotone T := by
    intro M M' hMM' z hz
    obtain ⟨a, ha, haz⟩ := (hmemT M z).mp hz
    refine (hmemT M' z).mpr ⟨Ideal.Quotient.mk I s ^ (M' - M) * a,
      quotientDegreeLE_mono I ?_ (mul_mem_quotientDegreeLE (hs_pow (M' - M)) ha), ?_⟩
    · have := Nat.mul_le_mul_left d (Nat.sub_le M' M)
      rw [Nat.mul_sub, Nat.add_mul, Nat.add_mul, one_mul, one_mul]
      have := Nat.mul_le_mul_left d hMM'
      omega
    · rw [map_mul, haz, map_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hMM']
  have h1 : (1 : S) ∈ T 0 :=
    (hmemT 0 1).mpr ⟨1, one_mem_quotientDegreeLE I _, by simp⟩
  have hmul : ∀ (o : Option σ) M z, z ∈ T M →
      (fun o ↦ o.elim (IsLocalization.Away.invSelf (Ideal.Quotient.mk I s))
        fun i ↦ algebraMap A S (Ideal.Quotient.mk I (X i)) : Option σ → S) o * z ∈ T (M + 1) := by
    intro o M z hz
    obtain ⟨a, ha, haz⟩ := (hmemT M z).mp hz
    refine (hmemT (M + 1) _).mpr ?_
    cases o with
    | none =>
      refine ⟨a, quotientDegreeLE_mono I (Nat.mul_le_mul_left _ M.le_succ) ha, ?_⟩
      change _ = u ^ (M + 1) * (IsLocalization.Away.invSelf (Ideal.Quotient.mk I s) * z)
      rw [haz, pow_succ, mul_assoc, ← mul_assoc u, IsLocalization.Away.mul_invSelf, one_mul]
    | some i =>
      refine ⟨Ideal.Quotient.mk I s * Ideal.Quotient.mk I (X i) * a, ?_, ?_⟩
      · refine quotientDegreeLE_mono I (le_of_eq ?_) (mul_mem_quotientDegreeLE
          (mul_mem_quotientDegreeLE (mk_mem_quotientDegreeLE le_rfl)
            (mk_X_mem_quotientDegreeLE I i)) ha)
        ring
      · change _ = u ^ (M + 1) * (algebraMap A S (Ideal.Quotient.mk I (X i)) * z)
        rw [map_mul, map_mul, haz, pow_succ]
        ring
  -- Clear denominators by `u ^ N`.
  have hmem : ∀ x ∈ quotientDegreeLE (awayPresentationIdeal I s) N,
      u ^ N * awayPresentationEquiv I s x ∈ (quotientDegreeLE I ((d + 1) * N)).map ι := by
    intro x hx
    obtain ⟨p, hp, rfl⟩ := mem_quotientDegreeLE.mp hx
    have hpT : awayPresentation I s p ∈ T (1 * N) := aeval_mem_of_forall_mul_mem _ hT h1 hmul hp
    rw [one_mul] at hpT
    obtain ⟨a, ha, hap⟩ := (hmemT N _).mp hpT
    rw [awayPresentationEquiv_mk, ← hap]
    exact ⟨a, ha, rfl⟩
  let L : quotientDegreeLE (awayPresentationIdeal I s) N →ₗ[k]
      (quotientDegreeLE I ((d + 1) * N)).map ι :=
    (((LinearMap.mulLeft k (u ^ N)).comp (awayPresentationEquiv I s).toLinearMap).domRestrict
      _).codRestrict _ fun x ↦ hmem x.1 x.2
  have hL : Function.Injective L := by
    intro x y hxy
    have h := congrArg Subtype.val hxy
    change u ^ N * awayPresentationEquiv I s x.1 = u ^ N * awayPresentationEquiv I s y.1 at h
    have hu : IsUnit (u ^ N) :=
      (IsLocalization.Away.algebraMap_isUnit (Ideal.Quotient.mk I s)).pow N
    exact Subtype.ext ((awayPresentationEquiv I s).injective (hu.mul_left_cancel h))
  calc affineHilbertFunction (awayPresentationIdeal I s) N
      ≤ Module.finrank k ((quotientDegreeLE I ((d + 1) * N)).map ι) :=
        LinearMap.finrank_le_finrank_of_injective hL
    _ ≤ affineHilbertFunction I ((d + 1) * N) := Submodule.finrank_map_le _ _

variable {I : Ideal (MvPolynomial σ k)} {s : MvPolynomial σ k}

/-- If the class of `s` is a non-zero-divisor on `MvPolynomial σ k ⧸ I`, the presentation ideal
`K` of the localization away from `s` satisfies `H(I, N) ≤ H(K, N)`.

The map from the quotient to the localization is injective
(`IsLocalization.Away.algebraMap_injective_of_isLeftRegular`) and sends the class of `X i` to the
class of the variable `some i`, which has degree `1`. Regularity is needed: for `I = ⊥` in one
variable and `s = 0`, the localization is zero and `H(K, N) = 0`. -/
theorem affineHilbertFunction_le_awayPresentationIdeal [Finite σ]
    (hs : IsLeftRegular (Ideal.Quotient.mk I s)) (N : ℕ) :
    affineHilbertFunction I N ≤ affineHilbertFunction (awayPresentationIdeal I s) N := by
  let g : (MvPolynomial σ k ⧸ I) →ₐ[k]
      (MvPolynomial (Option σ) k ⧸ awayPresentationIdeal I s) :=
    (awayPresentationEquiv I s).symm.toAlgHom.comp (IsScalarTower.toAlgHom k _ _)
  have hg : Function.Injective g := (awayPresentationEquiv I s).symm.injective.comp
    (IsLocalization.Away.algebraMap_injective_of_isLeftRegular hs)
  have hX : ∀ i, g (Ideal.Quotient.mk I (X i)) ∈
      quotientDegreeLE (awayPresentationIdeal I s) 1 := by
    intro i
    have h : g (Ideal.Quotient.mk I (X i)) = Ideal.Quotient.mk _ (X (some i)) := by
      apply (awayPresentationEquiv I s).injective
      simp [g]
    rw [h]
    exact mk_X_mem_quotientDegreeLE _ _
  simpa using affineHilbertFunction_le_of_injective g hg hX N

/-- If the class of `s` is a non-zero-divisor on the quotient, the Hilbert polynomial of `I` has
natural degree at most that of the presentation ideal of the localization away from `s`. -/
theorem natDegree_affineHilbertPolynomial_le_awayPresentationIdeal [Finite σ]
    (hs : IsLeftRegular (Ideal.Quotient.mk I s)) :
    (affineHilbertPolynomial I).natDegree ≤
      (affineHilbertPolynomial (awayPresentationIdeal I s)).natDegree :=
  natDegree_affineHilbertPolynomial_le_of_eventually_le_mul (m := 1) (c := 1) one_pos
    (Eventually.of_forall fun N ↦ by
      simpa using affineHilbertFunction_le_awayPresentationIdeal hs N)

/-- The presentation ideal of a localization away from any `s` has Hilbert polynomial of natural
degree at most that of `I`: the new variable is tied to `s` by a relation and adds no dimension. -/
theorem natDegree_affineHilbertPolynomial_awayPresentationIdeal_le [Finite σ]
    (I : Ideal (MvPolynomial σ k)) (s : MvPolynomial σ k) :
    (affineHilbertPolynomial (awayPresentationIdeal I s)).natDegree ≤
      (affineHilbertPolynomial I).natDegree :=
  natDegree_affineHilbertPolynomial_le_of_eventually_le_mul (m := 1) (Nat.succ_pos _)
    (Eventually.of_forall fun N ↦ by
      simpa using affineHilbertFunction_awayPresentationIdeal_le I s N)

/-- If the class of `s` is a non-zero-divisor on the quotient, the localization away from `s` has
the same dimension as the quotient: the Hilbert polynomials of `I` and of the presentation ideal
have the same natural degree. -/
theorem natDegree_affineHilbertPolynomial_awayPresentationIdeal [Finite σ]
    (hs : IsLeftRegular (Ideal.Quotient.mk I s)) :
    (affineHilbertPolynomial (awayPresentationIdeal I s)).natDegree =
      (affineHilbertPolynomial I).natDegree :=
  le_antisymm (natDegree_affineHilbertPolynomial_awayPresentationIdeal_le I s)
    (natDegree_affineHilbertPolynomial_le_awayPresentationIdeal hs)

/-- A surjection from the coordinate ring of `J` onto the localization of the coordinate ring of
`I` away from a regular `s` gives `natDegree P_I ≤ natDegree P_J`: the localization has the
dimension of `I`, and a quotient of the coordinate ring of `J` has no larger dimension. -/
theorem natDegree_affineHilbertPolynomial_le_of_surjective_away [Finite σ] [Finite τ]
    {J : Ideal (MvPolynomial τ k)} (hs : IsLeftRegular (Ideal.Quotient.mk I s))
    (g : (MvPolynomial τ k ⧸ J) →ₐ[k] Localization.Away (Ideal.Quotient.mk I s))
    (hg : Function.Surjective g) :
    (affineHilbertPolynomial I).natDegree ≤ (affineHilbertPolynomial J).natDegree :=
  (natDegree_affineHilbertPolynomial_le_awayPresentationIdeal hs).trans
    (natDegree_affineHilbertPolynomial_le_of_surjective
      ((awayPresentationEquiv I s).symm.toAlgHom.comp g)
      ((awayPresentationEquiv I s).symm.surjective.comp hg))

/-- A surjection between two principal localizations of coordinate rings,
`(MvPolynomial τ k ⧸ J)_t → (MvPolynomial σ k ⧸ I)_s`, gives `natDegree P_I ≤ natDegree P_J` when
the class of `s` is a non-zero-divisor. Nothing is assumed about `J` or `t`: localizing can only
lower the dimension of the source. -/
theorem natDegree_affineHilbertPolynomial_le_of_surjective_away_away [Finite σ] [Finite τ]
    {J : Ideal (MvPolynomial τ k)} {t : MvPolynomial τ k}
    (hs : IsLeftRegular (Ideal.Quotient.mk I s))
    (g : Localization.Away (Ideal.Quotient.mk J t) →ₐ[k]
      Localization.Away (Ideal.Quotient.mk I s))
    (hg : Function.Surjective g) :
    (affineHilbertPolynomial I).natDegree ≤ (affineHilbertPolynomial J).natDegree :=
  (natDegree_affineHilbertPolynomial_le_of_surjective_away hs
      (g.comp (awayPresentationEquiv J t).toAlgHom)
      (hg.comp (awayPresentationEquiv J t).surjective)).trans
    (natDegree_affineHilbertPolynomial_awayPresentationIdeal_le J t)

/-- If every class in a regular principal localization lies in the range of a
polynomial map whose kernel has Hilbert degree at most `d`, then the original ideal has Hilbert
degree at most `d`. -/
theorem natDegree_affineHilbertPolynomial_le_of_away_range
    {κ : Type*} [Finite σ] [Finite κ]
    (P : Ideal (MvPolynomial σ k)) (u : MvPolynomial σ k)
    (hregular : IsLeftRegular (Ideal.Quotient.mk P u))
    (Φ : MvPolynomial κ k →ₐ[k] Localization.Away (Ideal.Quotient.mk P u))
    (hrange : ∀ p : MvPolynomial σ k,
      algebraMap (MvPolynomial σ k ⧸ P) (Localization.Away (Ideal.Quotient.mk P u))
        (Ideal.Quotient.mk P p) ∈ Set.range Φ)
    {d : ℕ}
    (hbound : (affineHilbertPolynomial (RingHom.ker Φ.toRingHom)).natDegree ≤ d) :
    (affineHilbertPolynomial P).natDegree ≤ d := by
  classical
  let J := RingHom.ker Φ.toRingHom
  let L := Localization.Away (Ideal.Quotient.mk P u)
  obtain ⟨t, ht⟩ := hrange u
  let qΦ : (MvPolynomial κ k ⧸ J) →ₐ[k] L :=
    Ideal.Quotient.liftₐ J Φ fun p hp ↦ hp
  have hqt : qΦ (Ideal.Quotient.mk J t) =
      algebraMap (MvPolynomial σ k ⧸ P) L (Ideal.Quotient.mk P u) := by
    rw [show qΦ (Ideal.Quotient.mk J t) = Φ t by rfl]
    exact ht
  have hqtUnit : IsUnit (qΦ (Ideal.Quotient.mk J t)) := by
    apply isUnit_iff_exists_inv.mpr
    refine ⟨IsLocalization.Away.invSelf (Ideal.Quotient.mk P u), ?_⟩
    rw [hqt]
    exact IsLocalization.Away.mul_invSelf (S := L) (Ideal.Quotient.mk P u)
  let gRing : Localization.Away (Ideal.Quotient.mk J t) →+* L :=
    IsLocalization.Away.lift (g := qΦ.toRingHom) (Ideal.Quotient.mk J t) hqtUnit
  let locMap : Localization.Away (Ideal.Quotient.mk J t) →ₐ[k] L :=
    { toRingHom := gRing
      commutes' := by
        intro a
        change gRing (algebraMap k (Localization.Away (Ideal.Quotient.mk J t)) a) =
          algebraMap k L a
        rw [IsScalarTower.algebraMap_apply k (MvPolynomial κ k ⧸ J)
          (Localization.Away (Ideal.Quotient.mk J t))]
        rw [show gRing (algebraMap (MvPolynomial κ k ⧸ J)
          (Localization.Away (Ideal.Quotient.mk J t))
          (algebraMap k (MvPolynomial κ k ⧸ J) a)) =
            qΦ (algebraMap k (MvPolynomial κ k ⧸ J) a) by
          exact IsLocalization.Away.lift_eq
            (S := Localization.Away (Ideal.Quotient.mk J t))
            (g := qΦ.toRingHom) (Ideal.Quotient.mk J t) hqtUnit _]
        exact qΦ.commutes a }
  have hlocMap : Function.Surjective locMap := by
    intro z
    obtain ⟨m, a, hza⟩ := IsLocalization.Away.surj (Ideal.Quotient.mk P u) z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    obtain ⟨p, hp⟩ := hrange a
    let x : Localization.Away (Ideal.Quotient.mk J t) :=
      Localization.mk (Ideal.Quotient.mk J p) ⟨Ideal.Quotient.mk J t ^ m, m, rfl⟩
    refine ⟨x, ?_⟩
    have hbase :
        algebraMap (MvPolynomial σ k ⧸ P) L (Ideal.Quotient.mk P u) *
          IsLocalization.Away.invSelf (Ideal.Quotient.mk P u) = 1 :=
      IsLocalization.Away.mul_invSelf (S := L) (Ideal.Quotient.mk P u)
    have hz : algebraMap (MvPolynomial σ k ⧸ P) L (Ideal.Quotient.mk P a) *
        IsLocalization.Away.invSelf (Ideal.Quotient.mk P u) ^ m = z := by
      have h := congrArg
        (fun q : L ↦ q * IsLocalization.Away.invSelf (Ideal.Quotient.mk P u) ^ m) hza
      simpa only [← mul_pow, hbase, one_pow, mul_one, mul_assoc] using h.symm
    have hqbase : qΦ (Ideal.Quotient.mk J t) *
        IsLocalization.Away.invSelf (Ideal.Quotient.mk P u) = 1 := by
      rw [hqt]
      exact hbase
    change gRing x = z
    rw [show gRing x = qΦ (Ideal.Quotient.mk J p) *
        IsLocalization.Away.invSelf (Ideal.Quotient.mk P u) ^ m by
      dsimp only [gRing, x]
      exact Localization.awayLift_mk qΦ.toRingHom (Ideal.Quotient.mk J t)
        (Ideal.Quotient.mk J p) (IsLocalization.Away.invSelf (Ideal.Quotient.mk P u))
          hqbase m]
    rw [show qΦ (Ideal.Quotient.mk J p) = Φ p by rfl, hp]
    exact hz
  exact (natDegree_affineHilbertPolynomial_le_of_surjective_away_away
    hregular locMap hlocMap).trans hbound

/-- A surjection from a polynomial ring in `τ` onto the localization away from a regular `s`
bounds the natural degree of the Hilbert polynomial of `I` by `Nat.card τ`. Regularity is needed:
for `I = ⊥` in one variable and `s = 0` the localization is zero, so the polynomial ring in no
variables surjects onto it, while the Hilbert polynomial of `⊥` has natural degree `1`. -/
theorem natDegree_affineHilbertPolynomial_le_card_of_surjective_away [Finite σ] [Finite τ]
    (hs : IsLeftRegular (Ideal.Quotient.mk I s))
    (g : MvPolynomial τ k →ₐ[k] Localization.Away (Ideal.Quotient.mk I s))
    (hg : Function.Surjective g) :
    (affineHilbertPolynomial I).natDegree ≤ Nat.card τ :=
  (natDegree_affineHilbertPolynomial_le_of_surjective_away hs
      (Ideal.quotientKerAlgEquivOfSurjective hg).toAlgHom
      (Ideal.quotientKerAlgEquivOfSurjective hg).surjective).trans
    (natDegree_affineHilbertPolynomial_le _)

/-- If finitely many elements `x i`, indexed by `τ`, generate the localization away from a
regular `s` as a `k`-algebra, the natural degree of the Hilbert polynomial of `I` is at most
`Nat.card τ`. This is the generator form of
`natDegree_affineHilbertPolynomial_le_card_of_surjective_away`. -/
theorem natDegree_affineHilbertPolynomial_le_card_of_adjoin_eq_top_away [Finite σ] [Finite τ]
    (hs : IsLeftRegular (Ideal.Quotient.mk I s))
    (x : τ → Localization.Away (Ideal.Quotient.mk I s))
    (hx : Algebra.adjoin k (Set.range x) = ⊤) :
    (affineHilbertPolynomial I).natDegree ≤ Nat.card τ := by
  refine natDegree_affineHilbertPolynomial_le_card_of_surjective_away hs (aeval x) ?_
  rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
  exact hx

end Hilbert

end MvPolynomial
