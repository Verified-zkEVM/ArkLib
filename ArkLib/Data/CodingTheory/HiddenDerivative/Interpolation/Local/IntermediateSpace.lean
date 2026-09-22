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

Ported from
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/Interpolation/Local/IntermediateSpace.lean`
at ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d: `localFirstJetExponent` (here the
weight `localFirstJetWeight`), `LocalIntermediateEligibleExponent`, `localIntermediateSpace`,
`finrank_localIntermediateSpace`, `KernelSliceSourceEligibleExponent`, `kernelSliceSourceSpace`,
`tDegree_eq_zero_of_mem_kernelSliceSourceSpace`, `finrank_kernelSliceSourceSpace`,
`translatedLocalTruncation_mem_localIntermediateSpace`,
`truncate_exhibitedKernelMultiplier_mem_localIntermediateSpace` (here
`truncateLocalT_exhibitedKernelMultiplier_mem_localIntermediateSpace`), `boundedExhibitedKernelMap`,
`intermediateConstraintMap`, and `intermediateConstraintMap_boundedExhibitedKernelMap_eq_zero`.
The global weight `localHigherJetWeight` comes from the source's `Variables.lean`. The source
defined both spaces by explicit finite exponent sets built from coordinate equivalences, and so
required `0 < d` in the definitions; here the spaces are defined by their support predicates for
every `d`, and `0 < d` is assumed only in the dimension formulas. The source's hypothesis `r < m`
on the exhibited map is dropped, since the truncation alone keeps the product in the space. The
coordinate equivalences (`localExponentCoordinatesEquiv` and the index equivalences) are private
here. The source's private signed support-weight lemmas are replaced by
`ArkLib.Data.MvPolynomial.WeightAtMost`. The source's `translatedExactLocalTruncation` and
`exactLocalConstraintAt_eq_intermediate_comp_translated` are already in
`Interpolation/Local/Rank.lean`, stated there for an arbitrary space `S`.

Deferred: the public coordinate API of the source (`localExponentCoordinatesEquiv`,
`LocalIntermediateIndex`, `localIntermediateExponents`, `localIntermediateSpaceBasis`, the
kernel-slice analogues, and their cardinality lemmas). The dimension formulas here do not need it,
and no later slice ported so far uses it.

* Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed--Solomon
  Codes up to Capacity in the Low-Rate Regime*, ECCC TR26-164, Section 3.
-/

@[expose] public section

open PolynomialDifferential

noncomputable section

namespace ReedSolomon.HiddenDerivative

open MvPolynomial Finset

variable {d : ℕ}

/-! ### Local jet weights and the two spaces -/

/-- The weight counting the exponent of the visible jet `Y₁ = localY 0`. It is zero on every
variable when `d = 0`. -/
def localFirstJetWeight (d : ℕ) : LocalVariable d → ℕ
  | some (some j) => if j.val = 0 then 1 else 0
  | _ => 0

/-- The higher-jet weight on local variables: `Y_(j+1) = localY j` has weight `j`, and `T`, `U`,
and `Y₁` have weight zero. -/
def localHigherJetWeight (d : ℕ) : LocalVariable d → ℕ
  | some (some j) => j.val
  | _ => 0

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

/-- For `d = n + 1`, an exponent is its `T`, `U`, and `Y₁` degrees and the degrees of
`Y₂, ..., Y_(n+1)`. -/
private def localExponentEquiv (n : ℕ) :
    (LocalVariable (n + 1) →₀ ℕ) ≃ ℕ × ℕ × ℕ × (Fin n → ℕ) :=
  Finsupp.equivFunOnFinite.trans <| Equiv.piOptionEquivProd.trans <|
    Equiv.prodCongr (Equiv.refl ℕ) <| Equiv.piOptionEquivProd.trans <|
      Equiv.prodCongr (Equiv.refl ℕ) (Fin.consEquiv fun _ => ℕ).symm

private theorem localExponentEquiv_apply (n : ℕ) (e : LocalVariable (n + 1) →₀ ℕ) :
    localExponentEquiv n e =
      (e (localT _), e (localU _), e (localY 0), fun i => e (localY i.succ)) :=
  rfl

private theorem weight_localFirstJetWeight_succ {n : ℕ} (e : LocalVariable (n + 1) →₀ ℕ) :
    e.weight (localFirstJetWeight (n + 1)) = e (localY 0) := by
  simp [Finsupp.weight_eq_sum, Fintype.sum_option, localFirstJetWeight, localY]

private theorem weight_localHigherJetWeight_succ {n : ℕ} (e : LocalVariable (n + 1) →₀ ℕ) :
    e.weight (localHigherJetWeight (n + 1)) = ∑ i : Fin n, (i.val + 1) * e (localY i.succ) := by
  simp only [Finsupp.weight_eq_sum, Fintype.sum_option, Fin.sum_univ_succ, localHigherJetWeight,
    smul_eq_mul, Fin.val_zero, Fin.val_succ, mul_zero, zero_add, localY]
  exact sum_congr rfl fun i _ => mul_comm _ _

/-- The exponent tuples of the intermediate space for `d = n + 1`. -/
private def intermediateTuples (n m M W : ℕ) : Finset (ℕ × ℕ × ℕ × (Fin n → ℕ)) :=
  ((range m).sigma fun t => range (t + 1) ×ˢ range (M + 1) ×ˢ
      natWeightedSimplex (fun i : Fin n => i.val + 1) (W + t)).map
    (Equiv.sigmaEquivProd ℕ (ℕ × ℕ × (Fin n → ℕ))).toEmbedding

private theorem intermediate_set_eq (n m M W : ℕ) :
    {e | LocalIntermediateExponent (n + 1) m M W e} =
      ↑((intermediateTuples n m M W).map (localExponentEquiv n).symm.toEmbedding) := by
  ext e
  simp only [Set.mem_ofPred_eq, coe_map, Set.mem_image, mem_coe, Equiv.coe_toEmbedding]
  rw [show (∃ x ∈ intermediateTuples n m M W, (localExponentEquiv n).symm x = e) ↔
      localExponentEquiv n e ∈ intermediateTuples n m M W from
    ⟨fun ⟨x, hx, hxe⟩ => by rwa [← hxe, Equiv.apply_symm_apply],
      fun h => ⟨_, h, Equiv.symm_apply_apply _ _⟩⟩]
  simp only [intermediateTuples, mem_map_equiv, Equiv.sigmaEquivProd_symm_apply, mem_sigma,
    mem_range, mem_product, localExponentEquiv_apply,
    mem_natWeightedSimplex (fun i : Fin n => Nat.succ_ne_zero i.val), Nat.succ_eq_add_one]
  rw [LocalIntermediateExponent, weight_localFirstJetWeight_succ,
    weight_localHigherJetWeight_succ]
  omega

/-- The exponent tuples of a bounded kernel slice for `d = n + 1`. -/
private def kernelSliceTuples (n r M W h : ℕ) : Finset (ℕ × ℕ × ℕ × (Fin n → ℕ)) :=
  {0} ×ˢ range (r + 1 - h) ×ˢ range (M + 1 - h) ×ˢ
    natWeightedSimplex (fun i : Fin n => i.val + 1) (W + r)

private theorem kernelSlice_set_eq (n r M W h : ℕ) :
    {e | KernelSliceSourceExponent (n + 1) r M W h e} =
      ↑((kernelSliceTuples n r M W h).map (localExponentEquiv n).symm.toEmbedding) := by
  ext e
  simp only [Set.mem_ofPred_eq, coe_map, Set.mem_image, mem_coe, Equiv.coe_toEmbedding]
  rw [show (∃ x ∈ kernelSliceTuples n r M W h, (localExponentEquiv n).symm x = e) ↔
      localExponentEquiv n e ∈ kernelSliceTuples n r M W h from
    ⟨fun ⟨x, hx, hxe⟩ => by rwa [← hxe, Equiv.apply_symm_apply],
      fun h => ⟨_, h, Equiv.symm_apply_apply _ _⟩⟩]
  simp only [kernelSliceTuples, mem_product, mem_singleton, mem_range, localExponentEquiv_apply,
    mem_natWeightedSimplex (fun i : Fin n => Nat.succ_ne_zero i.val), Nat.succ_eq_add_one]
  rw [KernelSliceSourceExponent, weight_localFirstJetWeight_succ,
    weight_localHigherJetWeight_succ]
  omega

/-- For `d > 0` the intermediate space is finite-dimensional. -/
theorem localIntermediateSpace_finite {F : Type*} [CommSemiring F] (hd : 0 < d) (m M W : ℕ) :
    Module.Finite F (localIntermediateSpace F d m M W) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  rw [localIntermediateSpace, intermediate_set_eq]
  exact restrictSupport_finite (Finset.finite_toSet _)

/-- For `d > 0` the intermediate space has dimension
`∑_{r < m} weightedHigherJetCount d (W + r) * (r + 1)(M + 1)`: at `T`-degree `r` there are
`r + 1` choices of the `U`-degree, `M + 1` of the `Y₁`-degree, and one higher-jet exponent for
each point of the weighted simplex. The hypothesis `0 < d` is needed: for `d = 0` there is no
`Y₁`, so the factor `M + 1` overcounts. -/
theorem finrank_localIntermediateSpace {F : Type*} [Field F] (hd : 0 < d) (m M W : ℕ) :
    Module.finrank F (localIntermediateSpace F d m M W) =
      ∑ r ∈ range m, weightedHigherJetCount d (W + r) * ambientContactCount r M := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  rw [localIntermediateSpace, intermediate_set_eq, finrank_restrictSupport_finset, card_map,
    intermediateTuples, card_map, card_sigma]
  refine sum_congr rfl fun r _ => ?_
  rw [card_product, card_product, card_range, card_range, weightedHigherJetCount_succ,
    ambientContactCount]
  ring

/-- For `d > 0` a bounded kernel slice is finite-dimensional. -/
theorem kernelSliceSourceSpace_finite {F : Type*} [CommSemiring F] (hd : 0 < d) (r M W h : ℕ) :
    Module.Finite F (kernelSliceSourceSpace F d r M W h) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  rw [kernelSliceSourceSpace, kernelSlice_set_eq]
  exact restrictSupport_finite (Finset.finite_toSet _)

/-- For `d > 0` a bounded kernel slice has dimension
`weightedHigherJetCount d (W + r) * (r + 1 - h)(M + 1 - h)`. -/
theorem finrank_kernelSliceSourceSpace {F : Type*} [Field F] (hd : 0 < d) (r M W h : ℕ) :
    Module.finrank F (kernelSliceSourceSpace F d r M W h) =
      weightedHigherJetCount d (W + r) * exhibitedKernelContactCount r M h := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  rw [kernelSliceSourceSpace, kernelSlice_set_eq, finrank_restrictSupport_finset, card_map,
    kernelSliceTuples, card_product, card_product, card_product, card_singleton, card_range,
    card_range, weightedHigherJetCount_succ, exhibitedKernelContactCount]
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
