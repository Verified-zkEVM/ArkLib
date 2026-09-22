/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Justin Thaler
-/
module

public import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.Local.ConstraintKernel
public import ArkLib.Data.MvPolynomial.WeightAtMost

/-!
# The local intermediate space and the bounded kernel slices

For parameters `m, M, W`, the local intermediate space `localIntermediateSpace F d m M W` is
spanned by the local monomials `T^t U^a Y₁^b Y₂^(c₂) ⋯ Y_d^(c_d)` with

```text
t < m,   a ≤ t,   b ≤ M,   ∑_{j ≥ 2} (j - 1) c_j ≤ W + t.
```

It contains the reduction modulo `T^m` of the translate of every polynomial in the exact
interpolation space, so it can serve as the space `S` of
`finrank_range_exactLocalConstraintAt_le_sub`. The bounded kernel slice
`kernelSliceSourceSpace F d r M W h` is spanned by the monomials with `t = 0`, `a + h ≤ r`,
`b + h ≤ M`, and higher-jet weight at most `W + r`; multiplying it by `T^r (U - localJetSum d)^h`
and reducing modulo `T^m` lands in the intermediate space.

Both memberships are weight bounds. With the integer weights `T ↦ -1, U ↦ 1` (for `a ≤ t`),
`Y₁ ↦ 1` (for `b ≤ M`), and `T ↦ -1, Y_(j+1) ↦ j` (for the higher-jet bound), the translation
generators and the factors of the exhibited product have bounded weight, and
`MvPolynomial.bind₁_mem_restrictWeightAtMost` and `MvPolynomial.mul_mem_restrictWeightAtMost`
carry the bounds through.

Both spaces are defined by their support conditions for every `d`; only the dimension formulas
assume `d > 0`.

## Main statements

* `finrank_localIntermediateSpace`: for `d > 0`, the intermediate space has dimension
  `∑_{r < m} weightedHigherJetCount d (W + r) * (r + 1)(M + 1)`.
* `finrank_kernelSliceSourceSpace`: for `d > 0`, the slice has dimension
  `weightedHigherJetCount d (W + r) * (r + 1 - h)(M + 1 - h)`.
* `translatedLocalTruncation_mem_localIntermediateSpace`: translated truncations of exact
  interpolation polynomials lie in the intermediate space.
* `truncateLocalT_exhibitedKernelMultiplier_mem_localIntermediateSpace`: truncated exhibited
  products lie in the intermediate space.

## References

* [Brakensiek, J., Chen, Y., Putterman, A., Zhang, Z., and Zheng, K. Z., *Algorithmic List
  Decoding of Reed–Solomon Codes up to Capacity in the Low-Rate Regime*][BCPZZ26], Section 3.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial Finset

variable {d : ℕ}

/-! ### The two spaces -/

/-- The support condition of the intermediate space: `T`-degree below `m`, `U`-degree at most the
`T`-degree, `Y₁`-degree at most `M`, and higher-jet weight at most `W` plus the `T`-degree. -/
def LocalIntermediateExponent (d m M W : ℕ) (e : LocalVariable d →₀ ℕ) : Prop :=
  e (localT d) < m ∧ e (localU d) ≤ e (localT d) ∧
    e.weight (localFirstJetWeight d) ≤ M ∧
      e.weight (localHigherJetWeight d) ≤ W + e (localT d)

/-- The local intermediate space: local polynomials supported on `LocalIntermediateExponent`. -/
def localIntermediateSpace (F : Type*) [CommSemiring F] (d m M W : ℕ) :
    Submodule F (LocalPolynomial F d) :=
  restrictSupport F {e | LocalIntermediateExponent d m M W e}

/-- `P` lies in `localIntermediateSpace F d m M W` iff every exponent in its support satisfies
`LocalIntermediateExponent d m M W`. -/
theorem mem_localIntermediateSpace_iff {F : Type*} [CommSemiring F] {m M W : ℕ}
    {P : LocalPolynomial F d} :
    P ∈ localIntermediateSpace F d m M W ↔
      ∀ e ∈ P.support, LocalIntermediateExponent d m M W e :=
  Iff.rfl

/-- The support condition of a bounded kernel slice: no `T`, `U`-degree `a` with `a + h ≤ r`,
`Y₁`-degree `b` with `b + h ≤ M`, and higher-jet weight at most `W + r`. -/
def KernelSliceSourceExponent (d r M W h : ℕ) (e : LocalVariable d →₀ ℕ) : Prop :=
  e (localT d) = 0 ∧ e (localU d) + h ≤ r ∧
    e.weight (localFirstJetWeight d) + h ≤ M ∧ e.weight (localHigherJetWeight d) ≤ W + r

/-- The bounded kernel slice: local polynomials supported on `KernelSliceSourceExponent`. -/
def kernelSliceSourceSpace (F : Type*) [CommSemiring F] (d r M W h : ℕ) :
    Submodule F (LocalPolynomial F d) :=
  restrictSupport F {e | KernelSliceSourceExponent d r M W h e}

/-- `G` lies in `kernelSliceSourceSpace F d r M W h` iff every exponent in its support satisfies
`KernelSliceSourceExponent d r M W h`. -/
theorem mem_kernelSliceSourceSpace_iff {F : Type*} [CommSemiring F] {r M W h : ℕ}
    {G : LocalPolynomial F d} :
    G ∈ kernelSliceSourceSpace F d r M W h ↔
      ∀ e ∈ G.support, KernelSliceSourceExponent d r M W h e :=
  Iff.rfl

/-- A bounded kernel slice contains no `T`. -/
theorem tDegree_eq_zero_of_mem_kernelSliceSourceSpace {F : Type*} [CommSemiring F]
    {r M W h : ℕ} {G : LocalPolynomial F d} (hG : G ∈ kernelSliceSourceSpace F d r M W h)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ G.support) : e (localT d) = 0 :=
  (hG he).1

/-! ### Dimensions -/

/-- The exponent tuples `(t, a, b, c)` of the intermediate space, in the coordinates of
`localExponentCoordinatesEquiv`. -/
private def intermediateTuples (d m M W : ℕ) : Finset (ℕ × ℕ × ℕ × (Fin (d - 1) → ℕ)) :=
  ((range m).sigma fun t => range (t + 1) ×ˢ range (M + 1) ×ˢ
      natWeightedSimplex (fun i : Fin (d - 1) => i.val + 1) (W + t)).map
    (Equiv.sigmaEquivProd ℕ (ℕ × ℕ × (Fin (d - 1) → ℕ))).toEmbedding

private theorem intermediate_set_eq (hd : 0 < d) (m M W : ℕ) :
    {e | LocalIntermediateExponent d m M W e} =
      ↑((intermediateTuples d m M W).map (localExponentCoordinatesEquiv hd).symm.toEmbedding) := by
  ext e
  rw [coe_map, Equiv.coe_toEmbedding, Equiv.image_symm_eq_preimage]
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, mem_coe, intermediateTuples, mem_map_equiv,
    Equiv.sigmaEquivProd_symm_apply, mem_sigma, mem_range, mem_product,
    localExponentCoordinatesEquiv_apply,
    mem_natWeightedSimplex (fun i : Fin (d - 1) => Nat.add_one_ne_zero i.val)]
  rw [LocalIntermediateExponent, weight_localFirstJetWeight hd, weight_localHigherJetWeight hd]
  omega

/-- The exponent tuples of a bounded kernel slice, in the coordinates of
`localExponentCoordinatesEquiv`. -/
private def kernelSliceTuples (d r M W h : ℕ) : Finset (ℕ × ℕ × ℕ × (Fin (d - 1) → ℕ)) :=
  {0} ×ˢ range (r + 1 - h) ×ˢ range (M + 1 - h) ×ˢ
    natWeightedSimplex (fun i : Fin (d - 1) => i.val + 1) (W + r)

private theorem kernelSlice_set_eq (hd : 0 < d) (r M W h : ℕ) :
    {e | KernelSliceSourceExponent d r M W h e} =
      ↑((kernelSliceTuples d r M W h).map (localExponentCoordinatesEquiv hd).symm.toEmbedding) := by
  ext e
  rw [coe_map, Equiv.coe_toEmbedding, Equiv.image_symm_eq_preimage]
  simp only [Set.mem_ofPred_eq, Set.mem_preimage, mem_coe, kernelSliceTuples, mem_product,
    mem_singleton, mem_range, localExponentCoordinatesEquiv_apply,
    mem_natWeightedSimplex (fun i : Fin (d - 1) => Nat.add_one_ne_zero i.val)]
  rw [KernelSliceSourceExponent, weight_localFirstJetWeight hd, weight_localHigherJetWeight hd]
  omega

/-- For `d > 0` the intermediate space is finite-dimensional. -/
theorem localIntermediateSpace_finite {F : Type*} [CommSemiring F] (hd : 0 < d) (m M W : ℕ) :
    Module.Finite F (localIntermediateSpace F d m M W) := by
  rw [localIntermediateSpace, intermediate_set_eq hd]
  exact restrictSupport_finite (Finset.finite_toSet _)

/-- For `d > 0` the intermediate space has dimension
`∑_{r < m} weightedHigherJetCount d (W + r) * (r + 1)(M + 1)`: at `T`-degree `r` there are
`r + 1` choices of the `U`-degree, `M + 1` of the `Y₁`-degree, and one higher-jet exponent for
each point of the weighted simplex. The hypothesis `0 < d` is needed: for `d = 0` there is no
`Y₁`, so the factor `M + 1` overcounts. -/
theorem finrank_localIntermediateSpace {F : Type*} [Field F] (hd : 0 < d) (m M W : ℕ) :
    Module.finrank F (localIntermediateSpace F d m M W) =
      ∑ r ∈ range m, weightedHigherJetCount d (W + r) * ambientContactCount r M := by
  rw [localIntermediateSpace, intermediate_set_eq hd, finrank_restrictSupport_finset, card_map,
    intermediateTuples, card_map, card_sigma]
  refine sum_congr rfl fun r _ => ?_
  rw [card_product, card_product, card_range, card_range, weightedHigherJetCount,
    ambientContactCount]
  ring

/-- For `d > 0` a bounded kernel slice is finite-dimensional. -/
theorem kernelSliceSourceSpace_finite {F : Type*} [CommSemiring F] (hd : 0 < d) (r M W h : ℕ) :
    Module.Finite F (kernelSliceSourceSpace F d r M W h) := by
  rw [kernelSliceSourceSpace, kernelSlice_set_eq hd]
  exact restrictSupport_finite (Finset.finite_toSet _)

/-- For `d > 0` a bounded kernel slice has dimension
`weightedHigherJetCount d (W + r) * (r + 1 - h)(M + 1 - h)`. -/
theorem finrank_kernelSliceSourceSpace {F : Type*} [Field F] (hd : 0 < d) (r M W h : ℕ) :
    Module.finrank F (kernelSliceSourceSpace F d r M W h) =
      weightedHigherJetCount d (W + r) * exhibitedKernelContactCount r M h := by
  rw [kernelSliceSourceSpace, kernelSlice_set_eq hd, finrank_restrictSupport_finset, card_map,
    kernelSliceTuples, card_product, card_product, card_product, card_singleton, card_range,
    card_range, weightedHigherJetCount, exhibitedKernelContactCount]
  ring

/-! ### Integer weights -/

/-- `T ↦ -1`, `U ↦ 1`, visible jets `↦ 0`: the weight of `e` is `e U - e T`. -/
private def balanceWeight (d : ℕ) : LocalVariable d → ℤ
  | none => -1
  | some none => 1
  | some (some _) => 0

/-- The first-jet weight with integer values. -/
private def firstWeight (d : ℕ) (v : LocalVariable d) : ℤ :=
  localFirstJetWeight d v

/-- `T ↦ -1`, `U ↦ 0`, `Y_(j+1) ↦ j`: the higher-jet weight minus the `T`-degree. -/
private def higherBalanceWeight (d : ℕ) : LocalVariable d → ℤ
  | none => -1
  | some none => 0
  | some (some j) => j.val

private theorem weight_balanceWeight (e : LocalVariable d →₀ ℕ) :
    e.weight (balanceWeight d) = (e (localU d) : ℤ) - e (localT d) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, balanceWeight, localU, localAux, localT]
  ring

private theorem weight_firstWeight (e : LocalVariable d →₀ ℕ) :
    e.weight (firstWeight d) = (e.weight (localFirstJetWeight d) : ℤ) := by
  simp [Finsupp.weight_eq_sum, firstWeight]

private theorem weight_higherBalanceWeight (e : LocalVariable d →₀ ℕ) :
    e.weight (higherBalanceWeight d) =
      (e.weight (localHigherJetWeight d) : ℤ) - e (localT d) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, higherBalanceWeight, localHigherJetWeight,
    localT]
  ring

variable {R : Type*} [CommRing R]

/-- Reduction modulo `T^m` of a polynomial satisfying the three integer weight bounds lies in the
intermediate space. -/
private theorem truncateLocalT_mem_localIntermediateSpace {m M W : ℕ} {q : LocalPolynomial R d}
    (hb : q ∈ restrictWeightAtMost (balanceWeight d) 0)
    (hf : q ∈ restrictWeightAtMost (firstWeight d) (M : ℤ))
    (hh : q ∈ restrictWeightAtMost (higherBalanceWeight d) (W : ℤ)) :
    truncateLocalT m q ∈ localIntermediateSpace R d m M W := by
  refine mem_localIntermediateSpace_iff.mpr fun e he => ?_
  have hc := mem_support_iff.mp he
  rw [coeff_truncateLocalT] at hc
  split_ifs at hc with hT
  · have heq : e ∈ q.support := mem_support_iff.mpr hc
    have h1 := hb heq
    have h2 := hf heq
    have h3 := hh heq
    simp only [Set.mem_ofPred_eq, weight_balanceWeight, weight_firstWeight,
      weight_higherBalanceWeight] at h1 h2 h3
    exact ⟨hT, by omega, by omega, by omega⟩
  · exact absurd rfl hc

/-- A bound on the visible-jet sum from bounds on its terms `± T^j Y_(j+1)`. -/
private theorem localJetSum_mem {w : LocalVariable d → ℤ} {a : ℤ}
    (h : ∀ j : Fin d, (j.val : ℤ) * w (localT d) + w (localY j) ≤ a) :
    localJetSum (R := R) d ∈ restrictWeightAtMost w a := by
  refine Submodule.sum_mem _ fun j _ => restrictWeightAtMost_mono w ?_
    (mul_mem_restrictWeightAtMost (mul_mem_restrictWeightAtMost
      (C_mem_restrictWeightAtMost w le_rfl _)
      (pow_mem_restrictWeightAtMost (X_mem_restrictWeightAtMost w (localT d) le_rfl) j.val))
      (X_mem_restrictWeightAtMost w (localY j) le_rfl))
  simpa [nsmul_eq_mul] using h j

/-- A bound on `U - localJetSum d` from bounds on `U` and on the jet sum. -/
private theorem hiddenErrorFactor_mem {w : LocalVariable d → ℤ} {a : ℤ} (hU : w (localU d) ≤ a)
    (h : ∀ j : Fin d, (j.val : ℤ) * w (localT d) + w (localY j) ≤ a) :
    hiddenErrorFactor (R := R) d ∈ restrictWeightAtMost w a :=
  sub_mem (X_mem_restrictWeightAtMost w _ hU) (localJetSum_mem h)

/-! ### Membership of translated truncations -/

/-- The translation generators satisfy the three weight bounds, relative to the source weights
`0`, the first-jet weight, and the higher-jet weight. -/
private theorem translateToUImage_mem (center received : R) (v : JetVariable d) :
    translateToUImage d center received v ∈ restrictWeightAtMost (balanceWeight d) 0 ∧
      translateToUImage d center received v ∈
        restrictWeightAtMost (firstWeight d) (jetFirstWeight v : ℤ) ∧
      translateToUImage d center received v ∈
        restrictWeightAtMost (higherBalanceWeight d) (jetHigherWeight v : ℤ) := by
  have hC := fun (w : LocalVariable d → ℤ) => C_mem_restrictWeightAtMost (R := R) w le_rfl
  rcases v with _ | j
  · refine ⟨add_mem (hC _ _) (X_mem_restrictWeightAtMost _ _ ?_),
      add_mem (hC _ _) (X_mem_restrictWeightAtMost _ _ ?_),
      add_mem (hC _ _) (X_mem_restrictWeightAtMost _ _ ?_)⟩ <;>
    simp [balanceWeight, firstWeight, localFirstJetWeight, higherBalanceWeight, jetFirstWeight,
      jetHigherWeight, localT]
  refine Fin.cases ?_ (fun i => ?_) j
  · have hTU := fun (w : LocalVariable d → ℤ) => mul_mem_restrictWeightAtMost (R := R)
      (X_mem_restrictWeightAtMost w (localT d) le_rfl)
      (X_mem_restrictWeightAtMost w (localU d) le_rfl)
    simp only [translateToUImage, Fin.cases_zero]
    refine ⟨add_mem (hC _ _) (restrictWeightAtMost_mono _ ?_ (hTU _)),
      add_mem (hC _ _) (restrictWeightAtMost_mono _ ?_ (hTU _)),
      add_mem (hC _ _) (restrictWeightAtMost_mono _ ?_ (hTU _))⟩ <;>
    simp [balanceWeight, firstWeight, localFirstJetWeight, higherBalanceWeight, jetFirstWeight,
      jetHigherWeight, localT, localU, localAux]
  · simp only [translateToUImage, Fin.cases_succ]
    refine ⟨X_mem_restrictWeightAtMost _ _ ?_, X_mem_restrictWeightAtMost _ _ ?_,
      X_mem_restrictWeightAtMost _ _ ?_⟩ <;>
    simp [balanceWeight, firstWeight, localFirstJetWeight, higherBalanceWeight, jetFirstWeight,
      jetHigherWeight, localY]

/-- Translating an exact interpolation polynomial to the local variables and reducing modulo
`T^m` lands in the intermediate space, at every center and received value. The translation
`X = center + T`, `Y₀ = received + T U` raises the `U`-degree only together with the `T`-degree,
does not change the `Y₁`-degree, and preserves the higher-jet weight, so the bounds `M` and `W`
of the exact space carry over. -/
theorem translatedLocalTruncation_mem_localIntermediateSpace {D A m M W : ℕ} (hdD : d < D)
    (center received : R) {Q : DifferentialPolynomial R d}
    (hQ : Q ∈ exactInterpolationSpace R D A d m M W hdD) :
    translatedLocalTruncation m center received Q ∈ localIntermediateSpace R d m M W := by
  have hQ' := mem_exactInterpolationSpace_iff.mp hQ
  refine truncateLocalT_mem_localIntermediateSpace
    (bind₁_mem_restrictWeightAtMost (w := fun _ => (0 : ℤ))
      (fun v => (translateToUImage_mem center received v).1) fun e _ => ?_)
    (bind₁_mem_restrictWeightAtMost (fun v => (translateToUImage_mem center received v).2.1)
      (mem_restrictWeightAtMost_natCast_iff.mpr fun u hu => (hQ' u hu).1))
    (bind₁_mem_restrictWeightAtMost (fun v => (translateToUImage_mem center received v).2.2)
      (mem_restrictWeightAtMost_natCast_iff.mpr fun u hu => (hQ' u hu).2.1))
  simp [Finsupp.weight_eq_sum]

/-! ### Membership of truncated exhibited products -/

/-- Multiplying a bounded kernel slice by `T^r (U - localJetSum d)^h` and reducing modulo `T^m`
lands in the intermediate space. The truncation is needed because the expanded product has
monomials of `T`-degree up to `r + (d - 1) h`. -/
theorem truncateLocalT_exhibitedKernelMultiplier_mem_localIntermediateSpace {m r M W h : ℕ}
    {G : LocalPolynomial R d} (hG : G ∈ kernelSliceSourceSpace R d r M W h) :
    truncateLocalT m (exhibitedKernelMultiplier d r h G) ∈ localIntermediateSpace R d m M W := by
  have hsrc : ∀ e ∈ G.support, KernelSliceSourceExponent d r M W h e := fun _ he => hG he
  have hT := fun (w : LocalVariable d → ℤ) => pow_mem_restrictWeightAtMost (R := R)
    (X_mem_restrictWeightAtMost w (localT d) le_rfl) r
  rw [exhibitedKernelMultiplier_apply, exhibitedKernelFactor]
  refine truncateLocalT_mem_localIntermediateSpace
    (restrictWeightAtMost_mono _ ?_ (mul_mem_restrictWeightAtMost (mul_mem_restrictWeightAtMost
      (hT _) (pow_mem_restrictWeightAtMost (hiddenErrorFactor_mem (a := 1) ?_ ?_) h))
      (mem_restrictWeightAtMost.mpr fun e he => (?_ : _ ≤ (r : ℤ) - h))))
    (restrictWeightAtMost_mono _ ?_ (mul_mem_restrictWeightAtMost (mul_mem_restrictWeightAtMost
      (hT _) (pow_mem_restrictWeightAtMost (hiddenErrorFactor_mem (a := 1) ?_ ?_) h))
      (mem_restrictWeightAtMost.mpr fun e he => (?_ : _ ≤ (M : ℤ) - h))))
    (restrictWeightAtMost_mono _ ?_ (mul_mem_restrictWeightAtMost (mul_mem_restrictWeightAtMost
      (hT _) (pow_mem_restrictWeightAtMost (hiddenErrorFactor_mem (a := 0) ?_ ?_) h))
      (mem_restrictWeightAtMost.mpr fun e he => (?_ : _ ≤ (W : ℤ) + r))))
  all_goals first
    | (intro j; simp [balanceWeight, firstWeight, localFirstJetWeight, higherBalanceWeight,
        localT, localY] <;> split_ifs <;> omega)
    | (simp [balanceWeight, firstWeight, localFirstJetWeight, higherBalanceWeight,
        localT, localU, localAux])
    | (obtain ⟨h1, h2, h3, h4⟩ := hsrc e he
       simp only [weight_balanceWeight, weight_firstWeight, weight_higherBalanceWeight]
       omega)

/-! ### Bounded exhibited maps -/

/-- Multiplication by `T^r (U - localJetSum d)^h` followed by reduction modulo `T^m`, from a
bounded kernel slice to the intermediate space. -/
def boundedExhibitedKernelMap (m r M W h : ℕ) :
    kernelSliceSourceSpace R d r M W h →ₗ[R] localIntermediateSpace R d m M W :=
  ((truncateLocalT m).comp ((exhibitedKernelMultiplier d r h).domRestrict
    (kernelSliceSourceSpace R d r M W h))).codRestrict (localIntermediateSpace R d m M W)
      fun G => truncateLocalT_exhibitedKernelMultiplier_mem_localIntermediateSpace G.2

/-- `boundedExhibitedKernelMap m r M W h G` is the reduction modulo `T^m` of
`exhibitedKernelFactor d r h * G`. -/
@[simp]
theorem boundedExhibitedKernelMap_apply (m r M W h : ℕ) (G : kernelSliceSourceSpace R d r M W h) :
    (boundedExhibitedKernelMap m r M W h G : LocalPolynomial R d) =
      truncateLocalT m (exhibitedKernelFactor d r h * (G : LocalPolynomial R d)) :=
  rfl

/-- The enlarged local constraint map restricted to the intermediate space. -/
def intermediateConstraintMap (m M W : ℕ) :
    localIntermediateSpace R d m M W →ₗ[R] LocalPolynomial R d :=
  (enlargedLocalConstraintMap m).domRestrict (localIntermediateSpace R d m M W)

/-- At the threshold `h = contactThreshold d m r`, the bounded exhibited map lands in the kernel
of the intermediate constraint map. The hypothesis `0 < d` is inherited from
`exhibitedKernelMultiplier_mem_ker_contactThreshold`. -/
theorem intermediateConstraintMap_boundedExhibitedKernelMap_eq_zero (hd : 0 < d) (m r M W : ℕ)
    (G : kernelSliceSourceSpace R d r M W (contactThreshold d m r)) :
    intermediateConstraintMap m M W (boundedExhibitedKernelMap m r M W _ G) = 0 := by
  change enlargedLocalConstraintMap m (truncateLocalT m (exhibitedKernelMultiplier d r _ G.1)) = 0
  rw [enlargedLocalConstraintMap_truncateLocalT]
  exact exhibitedKernelMultiplier_mem_ker_contactThreshold hd m r G.1

end ReedSolomon.HiddenDerivative
