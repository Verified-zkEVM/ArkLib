/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.ConstraintMap
public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Space
public import ArkLib.Data.MvPolynomial.WeightAtMost

/-!
# Reachable coordinates of the local constraint map

The unscaled local substitution sends `X ↦ center + T`, `Y₀ ↦ received + ∑_j ± T^(j+1) Y_(j+1) +
T E`, and `Y_(j+1) ↦ Y_(j+1)`. This file bounds the exponents that can occur in the image, and
uses the bounds to count a finite set of local exponents that contains the support of every local
constraint.

The bounds are all instances of one statement,
`unscaledLocalSubstitution_mem_restrictWeightAtMost`: if a source weight `v` and a local weight
`w` with values in an ordered additive monoid satisfy

```text
0 ≤ v X,   w T ≤ v X,   0 ≤ v Y₀,   w T + w E ≤ v Y₀,
(j + 1) w T + w Y_(j+1) ≤ v Y₀,   w Y_(j+1) ≤ v Y_(j+1),
```

then the substitution maps polynomials of `v`-weight at most `a` to polynomials of `w`-weight at
most `a`. The integer weight `T ↦ -1` lets the negative weight of `T` absorb the higher jets that
the substitution introduces in `Y₀`, which gives, for every monomial `T^t E^h ⋯` in the image:

* `h ≤ t`;
* its higher-jet weight is at most `W + (t - h)` if the source has higher-jet weight at most `W`,
  and the same for the derivative-order weight;
* its jet degree (the degree in `E` and the `Y_j`) is at most the source's total jet degree.

After projecting to contact order `t + d h < m`, the residual `r = t - h` is below `m` and
`h < ⌈(m - r)/(d + 1)⌉`. The finite set `localResidualExponents hd m W B` collects the exponents
allowed by these bounds, and its cardinality is at most `localResidualCoordinateBudget d m W B`.

## Main statements

* `unscaledLocalImage_mem_restrictWeightAtMost` and
  `unscaledLocalSubstitution_mem_restrictWeightAtMost`: the weight transport.
* `localE_le_localT_of_mem_support`, `localHigherJetWeight_le_of_mem_support`,
  `localDerivativeJetWeight_le_of_mem_support`, `localJetDegree_le_of_mem_support`, and
  `localJetDegree_lt_of_mem_support`: the bounds on the unscaled image.
* `localConstraintAt_support_of_derivative_weight` and
  `localConstraintAt_support_of_weight_bounds`: the bounds on the support of a local constraint.
* `card_localResidualExponents_le` and `mem_localResidualExponents_of_bounds`.
* `finrank_range_localConstraintAt_domRestrict_le` and
  `finrank_range_exactLocalConstraintAt_le_localResidualCoordinateBudget`: the rank of the local
  constraint map on a space with these bounds is at most the residual budget.

## References

* [Brakensiek, J., Chen, Y., Putterman, A., Zhang, Z., and Zheng, K. Z., *Algorithmic List
  Decoding of Reed–Solomon Codes up to Capacity in the Low-Rate Regime*][BCPZZ26], Section 3.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial Finset

variable {R : Type*} [CommRing R] {d : ℕ}

/-! ### Weight transport through the unscaled substitution -/

section Transport

variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
  {w : LocalVariable d → M} {v : JetVariable d → M}

/-- Each generator image of the unscaled substitution has `w`-weight at most the `v`-weight of
its variable. The nonnegativity hypotheses on `v X` and `v Y₀` are needed for the constants
`center` and `received`; the hypothesis on `(j + 1) w T + w Y_(j+1)` bounds the correction terms
`± T^(j+1) Y_(j+1)` in the image of `Y₀`. -/
theorem unscaledLocalImage_mem_restrictWeightAtMost
    (hX₀ : 0 ≤ v none) (hX : w (localT d) ≤ v none)
    (hY₀ : 0 ≤ v (some 0)) (hE : w (localT d) + w (localE d) ≤ v (some 0))
    (hcorr : ∀ j : Fin d, (j.val + 1) • w (localT d) + w (localY j) ≤ v (some 0))
    (hjet : ∀ j : Fin d, w (localY j) ≤ v (some j.succ))
    (center received : R) (x : JetVariable d) :
    unscaledLocalImage d center received x ∈ restrictWeightAtMost w (v x) := by
  have hXw := fun i => X_mem_restrictWeightAtMost (R := R) w i le_rfl
  rcases x with _ | j
  · exact add_mem (C_mem_restrictWeightAtMost w hX₀ _)
      (X_mem_restrictWeightAtMost w _ hX)
  induction j using Fin.cases with
  | zero =>
    refine add_mem (add_mem (C_mem_restrictWeightAtMost w hY₀ _) ?_)
      (restrictWeightAtMost_mono w hE (mul_mem_restrictWeightAtMost (hXw _) (hXw _)))
    refine Submodule.sum_mem _ fun j _ => restrictWeightAtMost_mono w ?_
      (mul_mem_restrictWeightAtMost (mul_mem_restrictWeightAtMost
        (C_mem_restrictWeightAtMost w le_rfl _) (pow_mem_restrictWeightAtMost (hXw _) _))
        (hXw (localY j)))
    simpa using hcorr j
  | succ j =>
    simpa [unscaledLocalImage] using X_mem_restrictWeightAtMost (R := R) w _ (hjet j)

/-- The unscaled substitution sends polynomials of `v`-weight at most `a` to polynomials of
`w`-weight at most `a`, under the generator hypotheses of
`unscaledLocalImage_mem_restrictWeightAtMost`. -/
theorem unscaledLocalSubstitution_mem_restrictWeightAtMost
    (hX₀ : 0 ≤ v none) (hX : w (localT d) ≤ v none)
    (hY₀ : 0 ≤ v (some 0)) (hE : w (localT d) + w (localE d) ≤ v (some 0))
    (hcorr : ∀ j : Fin d, (j.val + 1) • w (localT d) + w (localY j) ≤ v (some 0))
    (hjet : ∀ j : Fin d, w (localY j) ≤ v (some j.succ))
    (center received : R) {a : M} {Q : DifferentialPolynomial R d}
    (hQ : Q ∈ restrictWeightAtMost v a) :
    unscaledLocalSubstitution d center received Q ∈ restrictWeightAtMost w a :=
  bind₁_mem_restrictWeightAtMost
    (unscaledLocalImage_mem_restrictWeightAtMost hX₀ hX hY₀ hE hcorr hjet center received) hQ

end Transport

/-! ### Bounds on the unscaled image -/

/-- The local weight `T ↦ -1`, `E ↦ 1`, `Y_(j+1) ↦ a j`. -/
private def balancedJetWeight (a : Fin d → ℕ) : LocalVariable d → ℤ
  | none => -1
  | some none => 1
  | some (some j) => a j

/-- The local weight `Y_(j+1) ↦ a j`, zero on `T` and `E`. -/
private def localJetWeight (a : Fin d → ℕ) : LocalVariable d → ℕ
  | some (some j) => a j
  | _ => 0

/-- The source weight `Y_(j+1) ↦ a j`, zero on `X` and `Y₀`. -/
private def sourceJetWeight (a : Fin d → ℕ) : JetVariable d → ℕ
  | none => 0
  | some j => Fin.cases 0 a j

private theorem weight_balancedJetWeight (a : Fin d → ℕ) (e : LocalVariable d →₀ ℕ) :
    e.weight (balancedJetWeight a) =
      (e.weight (localJetWeight a) : ℤ) + e (localE d) - e (localT d) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, balancedJetWeight, localJetWeight, localT,
    localAux]
  ring

/-- If the source has `Y_(j+1)`-weights `a j ≤ j + 1` and weight at most `W`, then every image
monomial `T^t E^h ⋯` has `localJetWeight a` plus `h` at most `W + t`. -/
private theorem localJetWeight_add_le {a : Fin d → ℕ} (ha : ∀ j : Fin d, a j ≤ j.val + 1)
    (center received : R) {W : ℕ} {Q : DifferentialPolynomial R d}
    (hQ : ∀ u ∈ Q.support, u.weight (sourceJetWeight a) ≤ W) {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (unscaledLocalSubstitution d center received Q).support) :
    e.weight (localJetWeight a) + e (localE d) ≤ W + e (localT d) := by
  have h := unscaledLocalSubstitution_mem_restrictWeightAtMost
    (w := balancedJetWeight a) (v := fun x => (sourceJetWeight a x : ℤ))
    le_rfl (by simp [balancedJetWeight, localT]) le_rfl
    (by simp [balancedJetWeight, sourceJetWeight, localT, localAux])
    (fun j => by
      have := ha j
      simp [balancedJetWeight, sourceJetWeight, localT, localY]
      omega)
    (fun j => by simp [balancedJetWeight, sourceJetWeight, localY]) center received
    (mem_restrictWeightAtMost_natCast_iff.mpr hQ) he
  simp only [Set.mem_ofPred_eq, weight_balancedJetWeight] at h
  omega

/-- Every monomial `T^t E^h ⋯` of the unscaled image has `h ≤ t`: the error variable appears only
in the product `T E`. This holds for every polynomial and every center and received value. -/
theorem localE_le_localT_of_mem_support (center received : R) (Q : DifferentialPolynomial R d)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (unscaledLocalSubstitution d center received Q).support) :
    e (localE d) ≤ e (localT d) := by
  have h := localJetWeight_add_le (a := fun _ => 0) (fun _ => Nat.zero_le _) center received
    (W := 0) (fun u _ => by
      rw [show sourceJetWeight (d := d) (fun _ => 0) = 0 from funext fun x => by
        rcases x with _ | j
        · rfl
        · induction j using Fin.cases <;> rfl]
      simp [Finsupp.weight_apply]) he
  omega

/-- If every source monomial has higher-jet weight at most `W`, then every image monomial
`T^t E^h ⋯` has higher-jet weight at most `W + (t - h)`. The substitution trades powers of `T`
for higher jets in the image of `Y₀`, and each factor `E` uses one power of `T`. -/
theorem localHigherJetWeight_le_of_mem_support (center received : R) {W : ℕ}
    {Q : DifferentialPolynomial R d} (hQ : ∀ u ∈ Q.support, fullHigherJetWeight u ≤ W)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (unscaledLocalSubstitution d center received Q).support) :
    e.weight (localHigherJetWeight d) ≤ W + (e (localT d) - e (localE d)) := by
  have hw : sourceJetWeight (fun j : Fin d => j.val) = jetHigherWeight := by
    funext x
    rcases x with _ | j
    · rfl
    · induction j using Fin.cases <;> simp [sourceJetWeight, jetHigherWeight]
  have hl : localJetWeight (fun j : Fin d => j.val) = localHigherJetWeight d := by
    funext x; rcases x with _ | _ | j <;> rfl
  have h := localJetWeight_add_le (a := fun j : Fin d => j.val) (fun j => Nat.le_succ _)
    center received (W := W) (fun u hu => hw ▸ hQ u hu) he
  rw [hl] at h
  have := localE_le_localT_of_mem_support center received Q he
  omega

/-- If every source monomial has derivative-order weight at most `W`, then every image monomial
`T^t E^h ⋯` has derivative-order weight at most `W + (t - h)`. -/
theorem localDerivativeJetWeight_le_of_mem_support (center received : R) {W : ℕ}
    {Q : DifferentialPolynomial R d} (hQ : ∀ u ∈ Q.support, fullDerivativeJetWeight u ≤ W)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (unscaledLocalSubstitution d center received Q).support) :
    e.weight (localDerivativeJetWeight d) ≤ W + (e (localT d) - e (localE d)) := by
  have hw : sourceJetWeight (fun j : Fin d => j.val + 1) = jetDerivativeWeight := by
    funext x
    rcases x with _ | j
    · rfl
    · induction j using Fin.cases <;> simp [sourceJetWeight, jetDerivativeWeight]
  have hl : localJetWeight (fun j : Fin d => j.val + 1) = localDerivativeJetWeight d := by
    funext x; rcases x with _ | _ | j <;> rfl
  have h := localJetWeight_add_le (a := fun j : Fin d => j.val + 1) (fun j => le_rfl)
    center received (W := W) (fun u hu => hw ▸ hQ u hu) he
  rw [hl] at h
  have := localE_le_localT_of_mem_support center received Q he
  omega

/-- If every source monomial has total jet degree at most `B`, then every image monomial has
degree at most `B` in `E` and the visible jets. -/
theorem localJetDegree_le_of_mem_support (center received : R) {B : ℕ}
    {Q : DifferentialPolynomial R d} (hQ : ∀ u ∈ Q.support, totalJetDegree u ≤ B)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (unscaledLocalSubstitution d center received Q).support) :
    e.weight (localJetDegreeWeight d) ≤ B :=
  unscaledLocalSubstitution_mem_restrictWeightAtMost (w := localJetDegreeWeight d)
    (v := jetDegreeWeight) le_rfl le_rfl (Nat.zero_le _) le_rfl
    (fun _ => by simp [localJetDegreeWeight, localT, localY, jetDegreeWeight])
    (fun _ => le_rfl) center received hQ he

/-- The strict form of `localJetDegree_le_of_mem_support`: a strict total-jet-degree cutoff `B`
on the source is a strict cutoff on the image. -/
theorem localJetDegree_lt_of_mem_support (center received : R) {B : ℕ}
    {Q : DifferentialPolynomial R d} (hQ : ∀ u ∈ Q.support, totalJetDegree u < B)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (unscaledLocalSubstitution d center received Q).support) :
    e.weight (localJetDegreeWeight d) < B := by
  have hQ0 : Q ≠ 0 := by rintro rfl; simp at he
  obtain ⟨u, hu⟩ := support_nonempty.mpr hQ0
  have := hQ u hu
  have := localJetDegree_le_of_mem_support center received (B := B - 1)
    (fun u hu => Nat.le_sub_one_of_lt (hQ u hu)) he
  omega

/-! ### Supports of local constraints -/

/-- A monomial of a local constraint has contact order below `m` and occurs in the unscaled
image. -/
theorem mem_support_of_mem_support_localConstraintAt {m : ℕ} {center received : R}
    {Q : DifferentialPolynomial R d} {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (localConstraintAt m center received Q).support) :
    localContactOrder d e < m ∧ e ∈ (unscaledLocalSubstitution d center received Q).support := by
  rw [mem_support_iff, localConstraintAt, LinearMap.comp_apply, coeff_projectLowContact] at he
  split_ifs at he with h
  · exact ⟨h, mem_support_iff.mpr he⟩
  · exact absurd rfl he

/-- The support of a local constraint of a polynomial with derivative-order weight at most `W`:
every monomial `T^t E^h ⋯` has `h ≤ t`, derivative-order weight at most `W + (t - h)`, and contact
order below `m`. -/
theorem localConstraintAt_support_of_derivative_weight {m W : ℕ} (center received : R)
    {Q : DifferentialPolynomial R d} (hQ : ∀ u ∈ Q.support, fullDerivativeJetWeight u ≤ W)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (localConstraintAt m center received Q).support) :
    e (localE d) ≤ e (localT d) ∧
      e.weight (localDerivativeJetWeight d) ≤ W + (e (localT d) - e (localE d)) ∧
      localContactOrder d e < m := by
  obtain ⟨hc, hs⟩ := mem_support_of_mem_support_localConstraintAt he
  exact ⟨localE_le_localT_of_mem_support center received Q hs,
    localDerivativeJetWeight_le_of_mem_support center received hQ hs, hc⟩

/-- The support of a local constraint of a polynomial with higher-jet weight at most `W` and total
jet degree below `B`: every monomial `T^t E^h ⋯` has `h ≤ t`, higher-jet weight at most
`W + (t - h)`, contact order below `m`, and jet degree below `B`. -/
theorem localConstraintAt_support_of_weight_bounds {m W B : ℕ} (center received : R)
    {Q : DifferentialPolynomial R d} (hQ : ∀ u ∈ Q.support, fullHigherJetWeight u ≤ W)
    (hB : ∀ u ∈ Q.support, totalJetDegree u < B)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ (localConstraintAt m center received Q).support) :
    e (localE d) ≤ e (localT d) ∧
      e.weight (localHigherJetWeight d) ≤ W + (e (localT d) - e (localE d)) ∧
      localContactOrder d e < m ∧ e.weight (localJetDegreeWeight d) < B := by
  obtain ⟨hc, hs⟩ := mem_support_of_mem_support_localConstraintAt he
  exact ⟨localE_le_localT_of_mem_support center received Q hs,
    localHigherJetWeight_le_of_mem_support center received hQ hs, hc,
    localJetDegree_lt_of_mem_support center received hB hs⟩

/-! ### Counting the reachable exponents -/

/-- The local exponents allowed by the bounds of `localConstraintAt_support_of_weight_bounds`, in
the coordinates `(t, h, b, z)` of `localExponentCoordinatesEquiv`: the residual `r = t - h` is
below `m`, `h < ⌈(m - r)/(d + 1)⌉`, the higher-jet exponent `z` has weight at most `W + r`, and the
`Y₁`-degree `b` is below `B - ∑ z`. -/
def localResidualExponents (hd : 0 < d) (m W B : ℕ) : Finset (LocalVariable d →₀ ℕ) :=
  ((range m).sigma fun r => range (contactThreshold (d + 1) m r) ×ˢ
      (natWeightedSimplex (fun i : Fin (d - 1) => i.val + 1) (W + r)).sigma
        fun z => range (B - ∑ i, z i)).image
    fun p => (localExponentCoordinatesEquiv hd).symm (p.1 + p.2.1, p.2.1, p.2.2.2, p.2.2.1)

/-- There are at most `localResidualCoordinateBudget d m W B` residual exponents. -/
theorem card_localResidualExponents_le (hd : 0 < d) (m W B : ℕ) :
    (localResidualExponents hd m W B).card ≤ localResidualCoordinateBudget d m W B := by
  refine card_image_le.trans_eq ?_
  simp only [card_sigma, card_product, card_range, localResidualCoordinateBudget]

/-- Every exponent satisfying the bounds of `localConstraintAt_support_of_weight_bounds` is a
residual exponent. -/
theorem mem_localResidualExponents_of_bounds (hd : 0 < d) {m W B : ℕ} {e : LocalVariable d →₀ ℕ}
    (hbalance : e (localE d) ≤ e (localT d))
    (hweight : e.weight (localHigherJetWeight d) ≤ W + (e (localT d) - e (localE d)))
    (hcontact : localContactOrder d e < m) (htotal : e.weight (localJetDegreeWeight d) < B) :
    e ∈ localResidualExponents hd m W B := by
  rw [localContactOrder_eq] at hcontact
  rw [weight_localHigherJetWeight hd] at hweight
  rw [weight_localJetDegreeWeight hd] at htotal
  refine mem_image.mpr ⟨⟨e (localT d) - e (localE d), e (localE d),
    fun i => e (localY ⟨i.val + 1, by omega⟩), e (localY ⟨0, hd⟩)⟩, ?_, ?_⟩
  · simp only [mem_sigma, mem_range, mem_product,
      mem_natWeightedSimplex (fun i : Fin (d - 1) => Nat.add_one_ne_zero i.val)]
    refine ⟨by omega, ?_, hweight, by omega⟩
    by_contra hle
    have h1 : m ≤ e (localT d) - e (localE d) + (d + 1) *
        contactThreshold (d + 1) m (e (localT d) - e (localE d)) :=
      multiplicity_le_add_mul_contactThreshold (Nat.succ_pos d) m _
    have h2 := Nat.mul_le_mul_left (d + 1) (Nat.le_of_not_lt hle)
    have h3 : (d + 1) * e (localE d) = e (localE d) + d * e (localE d) := by ring
    omega
  · apply (localExponentCoordinatesEquiv hd).injective
    simp [Nat.sub_add_cancel hbalance]

/-- The rank of the local constraint map on a space whose members have higher-jet weight at most
`W` and total jet degree below `B` is at most `localResidualCoordinateBudget d m W B`. The
hypothesis `0 < d` is needed for the coordinates `localExponentCoordinatesEquiv`. -/
theorem finrank_range_localConstraintAt_domRestrict_le {F : Type*} [Field F] (hd : 0 < d)
    (m W B : ℕ) (center received : F) (S : Submodule F (DifferentialPolynomial F d))
    (hS : ∀ Q ∈ S, ∀ u ∈ Q.support, fullHigherJetWeight u ≤ W ∧ totalJetDegree u < B) :
    Module.finrank F (LinearMap.range ((localConstraintAt m center received).domRestrict S)) ≤
      localResidualCoordinateBudget d m W B := by
  have hle : LinearMap.range ((localConstraintAt m center received).domRestrict S) ≤
      restrictSupport F ↑(localResidualExponents hd m W B) := by
    rintro _ ⟨⟨Q, hQ⟩, rfl⟩
    rw [LinearMap.domRestrict_apply, mem_restrictSupport_iff]
    intro e he
    obtain ⟨h1, h2, h3, h4⟩ := localConstraintAt_support_of_weight_bounds center received
      (fun u hu => (hS Q hQ u hu).1) (fun u hu => (hS Q hQ u hu).2) (mem_coe.mpr he)
    exact mem_localResidualExponents_of_bounds hd h1 h2 h3 h4
  have := restrictSupport_finite (R := F) (localResidualExponents hd m W B).finite_toSet
  refine (Submodule.finrank_mono hle).trans ?_
  rw [finrank_restrictSupport_finset]
  exact card_localResidualExponents_le hd m W B

/-- On the exact interpolation space, the rank of the local constraint map is at most the
residual budget with the jet-degree cutoff `⌊(mA - 1)/(D - d)⌋ + 1`. -/
theorem finrank_range_exactLocalConstraintAt_le_localResidualCoordinateBudget {F : Type*}
    [Field F] {D A M W : ℕ} (hd : 0 < d) (hdD : d < D) (m : ℕ) (center received : F) :
    Module.finrank F (LinearMap.range
        (exactLocalConstraintAt (A := A) (M := M) (W := W) hdD m center received)) ≤
      localResidualCoordinateBudget d m W (exactInterpolationJetDegreeFloor D A d m + 1) :=
  finrank_range_localConstraintAt_domRestrict_le hd m W _ center received _ fun _ hQ u hu =>
    have h := mem_exactInterpolationSpace_iff.mp hQ u hu
    ⟨h.2.1, Nat.lt_succ_of_le (totalJetDegree_le_floor_of_weight_lt hdD h.2.2)⟩

end ReedSolomon.HiddenDerivative
