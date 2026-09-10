/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Justin Thaler
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Space
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Data.Fintype.BigOperators


/-!
# Exact finite counts for hidden-derivative interpolation

This file defines the integer-valued counts in the exact hidden-derivative interpolation
certificate.  It deliberately stops at combinatorics: `certifiedEnlargedRankBound` is the residual
dimension obtained from the exhibited kernel family.  A later linear-algebra theorem must prove
that it bounds the rank of the enlarged local map, and then that the actual local map factors
through that enlarged map.  No equality with the actual local rank is asserted here.

The executable representatives use ordinary tuples.  The equivalence
`weightedHigherJetExponentEquiv` connects them to the canonical finitely supported
`HigherJetExponent` representation used by the interpolation code.

## References

* [Brakensiek, J., Chen, Y., Putterman, A., Zhang, Z., and Zheng, K. Z., *Algorithmic List
  Decoding of Reed-Solomon Codes up to Capacity in the Low-Rate Regime*][BCPZZ26]
* [Dao, Q., Kominers, S. D., Thaler, J., and Zheng, K. Z., *Reed--Solomon List Decoding and Mutual
  Correlated Agreement up to Capacity*][DKTZ26]
-/

@[expose] public section

open PolynomialDifferential


namespace ReedSolomon
namespace HiddenDerivative

open scoped BigOperators

/-! ### Executable higher-jet simplices and shells -/

/-- A tuple presentation of the exponents of `Y₂, ..., Y_d`. -/
abbrev HigherJetTuple (d : ℕ) := Fin (d - 1) → ℕ

/-- The anisotropic weight `Σ i, (i + 1) c_i` in the tuple presentation. -/
def higherJetTupleWeight {d : ℕ} (c : HigherJetTuple d) : ℕ :=
  ∑ i, (i.val + 1) * c i

/-- The ordinary degree `Σ i, c_i` in the tuple presentation. -/
def higherJetTupleDegree {d : ℕ} (c : HigherJetTuple d) : ℕ :=
  ∑ i, c i

/-- A finite coordinate box containing every tuple of anisotropic weight at most `W`. -/
def higherJetTupleBox (d W : ℕ) : Finset (HigherJetTuple d) :=
  Fintype.piFinset fun _ : Fin (d - 1) ↦ Finset.range (W + 1)

/-- The executable anisotropic simplex of higher-jet exponent tuples of weight at most `W`. -/
def weightedHigherJetTuples (d W : ℕ) : Finset (HigherJetTuple d) :=
  (higherJetTupleBox d W).filter fun c ↦ higherJetTupleWeight c ≤ W

/-- The executable shell of higher-jet exponent tuples of weight exactly `w`. -/
def weightedHigherJetShell (d w : ℕ) : Finset (HigherJetTuple d) :=
  (higherJetTupleBox d w).filter fun c ↦ higherJetTupleWeight c = w

/-- The weighted-simplex count `Λ_d(W)`. -/
def weightedHigherJetCount (d W : ℕ) : ℕ :=
  (weightedHigherJetTuples d W).card

/-- The number of higher-jet exponent tuples having anisotropic weight exactly `w`. -/
def weightedHigherJetShellCount (d w : ℕ) : ℕ :=
  (weightedHigherJetShell d w).card

/-- Every coordinate of a tuple is at most its anisotropic weight. -/
theorem higherJetTuple_apply_le_weight {d : ℕ} (c : HigherJetTuple d) (i : Fin (d - 1)) :
    c i ≤ higherJetTupleWeight c := by
  classical
  rw [higherJetTupleWeight]
  calc
    c i ≤ (i.val + 1) * c i := by
      simpa using Nat.mul_le_mul_right (c i) (Nat.succ_le_succ (Nat.zero_le i.val))
    _ ≤ ∑ j, (j.val + 1) * c j :=
      Finset.single_le_sum (f := fun j : Fin (d - 1) ↦ (j.val + 1) * c j)
        (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ i)

@[simp]
theorem mem_weightedHigherJetTuples {d W : ℕ} {c : HigherJetTuple d} :
    c ∈ weightedHigherJetTuples d W ↔ higherJetTupleWeight c ≤ W := by
  constructor
  · simp [weightedHigherJetTuples]
  · intro hc
    simp only [weightedHigherJetTuples, Finset.mem_filter, hc, and_true]
    simp only [higherJetTupleBox, Fintype.mem_piFinset, Finset.mem_range]
    intro i
    exact Nat.lt_succ_of_le ((higherJetTuple_apply_le_weight c i).trans hc)

@[simp]
theorem mem_weightedHigherJetShell {d w : ℕ} {c : HigherJetTuple d} :
    c ∈ weightedHigherJetShell d w ↔ higherJetTupleWeight c = w := by
  constructor
  · simp [weightedHigherJetShell]
  · intro hc
    simp only [weightedHigherJetShell, Finset.mem_filter, hc, and_true]
    simp only [higherJetTupleBox, Fintype.mem_piFinset, Finset.mem_range]
    intro i
    exact Nat.lt_succ_of_le ((higherJetTuple_apply_le_weight c i).trans hc.le)

/-- The tuple anisotropic weight agrees with `higherJetWeight` under the canonical finite-support
equivalence. -/
theorem higherJetTupleWeight_equivFunOnFinite {d : ℕ} (c : HigherJetExponent d) :
    higherJetTupleWeight (Finsupp.equivFunOnFinite c) = higherJetWeight c := by
  classical
  rw [higherJetTupleWeight, higherJetWeight, Finsupp.weight_eq_sum]
  simp only [Finsupp.equivFunOnFinite_apply, nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact Nat.mul_comm _ _

/-- The tuple ordinary degree agrees with `higherJetDegree` under the canonical finite-support
equivalence. -/
theorem higherJetTupleDegree_equivFunOnFinite {d : ℕ} (c : HigherJetExponent d) :
    higherJetTupleDegree (Finsupp.equivFunOnFinite c) = higherJetDegree c := by
  classical
  simp [higherJetTupleDegree, higherJetDegree, Finsupp.degree_eq_sum]

/-- The ordinary degree is bounded by the anisotropic weight. -/
theorem higherJetDegree_le_weight {d : ℕ} (c : HigherJetExponent d) :
    higherJetDegree c ≤ higherJetWeight c := by
  rw [← higherJetTupleDegree_equivFunOnFinite c,
    ← higherJetTupleWeight_equivFunOnFinite c]
  classical
  apply Finset.sum_le_sum
  intro i _
  simpa using Nat.mul_le_mul_right
    (Finsupp.equivFunOnFinite c i) (Nat.succ_le_succ (Nat.zero_le i.val))

/-- The executable weighted simplex is equivalent to the canonical subtype of bounded
`HigherJetExponent`s. -/
noncomputable def weightedHigherJetExponentEquiv (d W : ℕ) :
    {c : HigherJetExponent d // higherJetWeight c ≤ W} ≃
      ↑(weightedHigherJetTuples d W) :=
  Equiv.subtypeEquiv Finsupp.equivFunOnFinite fun c ↦ by
    rw [mem_weightedHigherJetTuples, higherJetTupleWeight_equivFunOnFinite]

/-- The executable weighted shell is equivalent to the canonical subtype of finite-support
exponents of exactly that weight. -/
noncomputable def weightedHigherJetShellEquiv (d w : ℕ) :
    {c : HigherJetExponent d // higherJetWeight c = w} ≃
      ↑(weightedHigherJetShell d w) :=
  Equiv.subtypeEquiv Finsupp.equivFunOnFinite fun c ↦ by
    rw [mem_weightedHigherJetShell, higherJetTupleWeight_equivFunOnFinite]

/-- `weightedHigherJetCount` is the cardinality of the canonical bounded finite-support type. -/
theorem card_weightedHigherJetExponent_eq_count (d W : ℕ) :
    Nat.card {c : HigherJetExponent d // higherJetWeight c ≤ W} =
      weightedHigherJetCount d W := by
  classical
  calc
    Nat.card {c : HigherJetExponent d // higherJetWeight c ≤ W} =
        Nat.card ↑(weightedHigherJetTuples d W) :=
      Nat.card_congr (weightedHigherJetExponentEquiv d W)
    _ = Fintype.card ↑(weightedHigherJetTuples d W) := Nat.card_eq_fintype_card
    _ = weightedHigherJetCount d W := Fintype.card_coe _

/-- `weightedHigherJetShellCount` is the cardinality of the canonical exact-weight subtype. -/
theorem card_weightedHigherJetShellExponent_eq_count (d w : ℕ) :
    Nat.card {c : HigherJetExponent d // higherJetWeight c = w} =
      weightedHigherJetShellCount d w := by
  classical
  calc
    Nat.card {c : HigherJetExponent d // higherJetWeight c = w} =
        Nat.card ↑(weightedHigherJetShell d w) :=
      Nat.card_congr (weightedHigherJetShellEquiv d w)
    _ = Fintype.card ↑(weightedHigherJetShell d w) := Nat.card_eq_fintype_card
    _ = weightedHigherJetShellCount d w := Fintype.card_coe _

/-- Taking ordinary-degree cutoff `W` does not remove a higher-jet exponent of weight at most
`W`.  This bridges the executable simplex to the landed support-first API. -/
theorem goodHigherExponents_self_eq_weighted_count (d W : ℕ) :
    (goodHigherExponents d W W).card = weightedHigherJetCount d W := by
  classical
  let e : ↑(goodHigherExponents d W W) ≃
      {c : HigherJetExponent d // higherJetWeight c ≤ W} :=
    Equiv.subtypeEquiv (Equiv.refl _) fun c ↦ by
      rw [mem_goodHigherExponents]
      constructor
      · exact fun h ↦ h.1
      · exact fun h ↦ ⟨h, (higherJetDegree_le_weight c).trans h⟩
  calc
    (goodHigherExponents d W W).card =
        Nat.card ↑(goodHigherExponents d W W) := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = Nat.card {c : HigherJetExponent d // higherJetWeight c ≤ W} :=
      Nat.card_congr e
    _ = weightedHigherJetCount d W := card_weightedHigherJetExponent_eq_count d W

/-- The weighted simplex is the disjoint union of its shells from `0` through `W`, at the level
of cardinalities. -/
theorem weightedHigherJetCount_eq_sum_shellCount (d W : ℕ) :
    weightedHigherJetCount d W =
      ∑ w ∈ Finset.range (W + 1), weightedHigherJetShellCount d w := by
  classical
  have hmaps : (weightedHigherJetTuples d W : Set (HigherJetTuple d)).MapsTo
      higherJetTupleWeight (Finset.range (W + 1) : Set ℕ) := by
    intro c hc
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (mem_weightedHigherJetTuples.mp hc))
  rw [weightedHigherJetCount,
    Finset.card_eq_sum_card_fiberwise (f := higherJetTupleWeight) hmaps]
  apply Finset.sum_congr rfl
  intro w hw
  congr 1
  ext c
  simp only [Finset.mem_filter, mem_weightedHigherJetTuples, mem_weightedHigherJetShell]
  constructor
  · exact fun h ↦ h.2
  · intro hc
    have hw' : w ≤ W := Nat.le_of_lt_succ (Finset.mem_range.mp hw)
    exact ⟨hc.le.trans hw', hc⟩

/-! ### Staircase pairs -/

/-- The finite dependent index for pairs `(x, b₀)` with `x + D b₀ < L`.

The `b₀ < L` outer bound is exhaustive when `D > 0`. -/
abbrev StaircaseIndex (D L : ℕ) :=
  Σ b₀ : Fin L, Fin (L - D * b₀.val)

/-- The staircase count `N_D(L) = Σ_{b₀ < L} (L - D b₀)`. -/
def staircaseCount (D L : ℕ) : ℕ :=
  Finset.sum (Finset.range L) fun b₀ ↦ L - D * b₀

/-- Cardinality of the dependent staircase index. -/
theorem card_staircaseIndex (D L : ℕ) :
    Fintype.card (StaircaseIndex D L) = staircaseCount D L := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin, staircaseCount]
  exact Fin.sum_univ_eq_sum_range (fun b₀ ↦ L - D * b₀) L

/-- For positive `D`, the finite staircase index is equivalent to the paper's unbounded natural
pair description. -/
def staircaseIndexEquiv (D L : ℕ) (hD : 0 < D) :
    StaircaseIndex D L ≃ {p : ℕ × ℕ // p.1 + D * p.2 < L} where
  toFun p := ⟨(p.2.val, p.1.val), by
    exact Nat.lt_sub_iff_add_lt.mp p.2.isLt⟩
  invFun p :=
    ⟨⟨p.1.2, by
        have hbD : p.1.2 ≤ D * p.1.2 := by
          simpa [Nat.mul_comm] using Nat.mul_le_mul_right p.1.2 (Nat.succ_le_iff.mpr hD)
        exact hbD.trans_lt (lt_of_le_of_lt (Nat.le_add_left _ _) p.2)⟩,
      ⟨p.1.1, Nat.lt_sub_iff_add_lt.mpr p.2⟩⟩
  left_inv p := by
    cases p
    rfl
  right_inv p := by
    apply Subtype.ext
    rfl

/-- The staircase sum really counts all natural pairs satisfying the strict weighted bound. -/
theorem card_staircasePairs (D L : ℕ) (hD : 0 < D) :
    Nat.card {p : ℕ × ℕ // p.1 + D * p.2 < L} =
      staircaseCount D L := by
  calc
    Nat.card {p : ℕ × ℕ // p.1 + D * p.2 < L} =
        Nat.card (StaircaseIndex D L) :=
      Nat.card_congr (staircaseIndexEquiv D L hD).symm
    _ = Fintype.card (StaircaseIndex D L) := Nat.card_eq_fintype_card
    _ = staircaseCount D L := card_staircaseIndex D L

/-! ### The exact derivative-weighted dimension sum -/

/-- The specialization cost `Σ_i (D - (i + 2)) c_i` of the higher jets in tuple form. -/
def higherJetTupleSpecializationCost {d : ℕ} (D : ℕ) (c : HigherJetTuple d) : ℕ :=
  ∑ i, (D - (i.val + 2)) * c i

/-- The same higher-jet specialization cost on the canonical finite-support representation. -/
noncomputable def higherJetSpecializationCost {d : ℕ} (D : ℕ)
    (c : HigherJetExponent d) : ℕ :=
  Finsupp.weight (fun i : Fin (d - 1) ↦ D - (i.val + 2)) c

/-- Tuple conversion preserves the higher-jet specialization cost. -/
theorem higherJetTupleSpecializationCost_equivFunOnFinite {d D : ℕ}
    (c : HigherJetExponent d) :
    higherJetTupleSpecializationCost D (Finsupp.equivFunOnFinite c) =
      higherJetSpecializationCost D c := by
  classical
  rw [higherJetTupleSpecializationCost, higherJetSpecializationCost, Finsupp.weight_eq_sum]
  simp only [Finsupp.equivFunOnFinite_apply, nsmul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  exact Nat.mul_comm _ _

/-- Residual budget left for the `(X, Y₀)` staircase after fixing higher jets and `Y₁`. -/
def exactDimensionResidual {d : ℕ} (D m A b₁ : ℕ) (c : HigherJetTuple d) : ℕ :=
  m * A - ((D - 1) * b₁ + higherJetTupleSpecializationCost D c)

/-- The exact finite derivative-weighted interpolation dimension sum.

Its interpretation as the cardinality of the cap-free polynomial support uses `0 < d < D`:
`d > 0` supplies the `Y₁` coordinate, and `d < D` makes all derivative weights positive.  The
natural-number expression remains executable outside that semantic parameter regime. -/
def exactInterpolationDimensionCount (D A d m M W : ℕ) : ℕ :=
  ∑ c ∈ weightedHigherJetTuples d W,
    ∑ b₁ ∈ Finset.range (M + 1),
      staircaseCount D (exactDimensionResidual D m A b₁ c)

/-- A finite index whose cardinality is the exact derivative-weighted dimension sum. -/
abbrev ExactDimensionIndex (D A d m M W : ℕ) :=
  Σ c : ↑(weightedHigherJetTuples d W),
    Σ b₁ : Fin (M + 1),
      StaircaseIndex D (exactDimensionResidual D m A b₁.val c.1)

/-- The exact sum is the cardinality of the finite nested interpolation index. -/
theorem card_exactDimensionIndex (D A d m M W : ℕ) :
    Fintype.card (ExactDimensionIndex D A d m M W) =
      exactInterpolationDimensionCount D A d m M W := by
  classical
  rw [Fintype.card_sigma]
  calc
    (∑ c : ↑(weightedHigherJetTuples d W),
        Fintype.card
          (Σ b₁ : Fin (M + 1),
            StaircaseIndex D (exactDimensionResidual D m A b₁.val c.1))) =
        ∑ c : ↑(weightedHigherJetTuples d W),
          ∑ b₁ : Fin (M + 1),
            staircaseCount D (exactDimensionResidual D m A b₁.val c.1) := by
      apply Finset.sum_congr rfl
      intro c _
      rw [Fintype.card_sigma]
      apply Finset.sum_congr rfl
      intro b₁ _
      exact card_staircaseIndex D (exactDimensionResidual D m A b₁.val c.1)
    _ = ∑ c ∈ weightedHigherJetTuples d W,
          ∑ b₁ : Fin (M + 1),
            staircaseCount D (exactDimensionResidual D m A b₁.val c) := by
      exact Finset.sum_coe_sort (weightedHigherJetTuples d W)
        (fun c : HigherJetTuple d ↦
          ∑ b₁ : Fin (M + 1),
            staircaseCount D (exactDimensionResidual D m A b₁.val c))
    _ = exactInterpolationDimensionCount D A d m M W := by
      rw [exactInterpolationDimensionCount]
      apply Finset.sum_congr rfl
      intro c _
      exact Fin.sum_univ_eq_sum_range
        (fun b₁ ↦ staircaseCount D (exactDimensionResidual D m A b₁ c)) (M + 1)

/-! ### Contact thresholds and the exhibited-kernel rank budget -/

/-- Least remainder exponent crossing the contact threshold: `ceil((m - r) / d)`. -/
def contactThreshold (d m r : ℕ) : ℕ :=
  (m - r) ⌈/⌉ d

/-- The contact threshold crosses multiplicity whenever `r < m` and `d > 0`. -/
theorem multiplicity_le_add_mul_contactThreshold {d m r : ℕ} (hd : 0 < d)
    (hr : r < m) :
    m ≤ r + d * contactThreshold d m r := by
  have hcover : m - r ≤ d * contactThreshold d m r := by
    exact le_smul_ceilDiv hd
  omega

/-- Every smaller remainder exponent stays strictly below multiplicity. -/
theorem add_mul_lt_multiplicity_of_lt_contactThreshold {d m r b : ℕ} (hd : 0 < d)
    (hr : r < m) (hb : b < contactThreshold d m r) :
    r + d * b < m := by
  have hnot : ¬m - r ≤ d * b := by
    intro h
    have : contactThreshold d m r ≤ b := (ceilDiv_le_iff_le_mul hd).mpr h
    omega
  omega

/-- Ambient `(U,Y₁)` monomials at one `T`-degree. -/
abbrev AmbientContactIndex (r M : ℕ) := Fin (r + 1) × Fin (M + 1)

/-- The rectangular contact indices contributed by the exhibited kernel at threshold `h`. -/
abbrev ExhibitedKernelContactIndex (r M h : ℕ) :=
  Fin (r + 1 - h) × Fin (M + 1 - h)

/-- Number of ambient `(U,Y₁)` monomials at one `T`-degree. -/
def ambientContactCount (r M : ℕ) : ℕ :=
  (r + 1) * (M + 1)

/-- Number of contact indices in the exhibited kernel rectangle.

The positive parts are encoded as `r + 1 - h` and `M + 1 - h`.  Writing `r - h + 1` would be
wrong over natural numbers when `h > r`. -/
def exhibitedKernelContactCount (r M h : ℕ) : ℕ :=
  (r + 1 - h) * (M + 1 - h)

/-- Residual dimension after subtracting the exhibited kernel rectangle from the ambient contact
rectangle.  This is a numerical rank budget, not an assertion about the actual local map. -/
def exhibitedKernelResidualCount (r M h : ℕ) : ℕ :=
  ambientContactCount r M - exhibitedKernelContactCount r M h

@[simp]
theorem card_ambientContactIndex (r M : ℕ) :
    Fintype.card (AmbientContactIndex r M) = ambientContactCount r M := by
  simp [AmbientContactIndex, ambientContactCount]

@[simp]
theorem card_exhibitedKernelContactIndex (r M h : ℕ) :
    Fintype.card (ExhibitedKernelContactIndex r M h) =
      exhibitedKernelContactCount r M h := by
  simp [ExhibitedKernelContactIndex, exhibitedKernelContactCount]

/-- The exhibited kernel rectangle never has more indices than its ambient rectangle. -/
theorem exhibitedKernelContactCount_le_ambientContactCount (r M h : ℕ) :
    exhibitedKernelContactCount r M h ≤ ambientContactCount r M := by
  unfold exhibitedKernelContactCount ambientContactCount
  exact Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)

/-- The one-degree residual count at the canonical contact threshold. -/
def certifiedContactRankBudget (d m M r : ℕ) : ℕ :=
  exhibitedKernelResidualCount r M (contactThreshold d m r)

/-- The finite sum certified by the exhibited-kernel argument as an upper bound for the
enlarged local map once its kernel inclusion and independence are proved.  It is not the actual
local rank. -/
def certifiedEnlargedRankBound (d m M W : ℕ) : ℕ :=
  ∑ r ∈ Finset.range m,
    weightedHigherJetCount d (W + r) * certifiedContactRankBudget d m M r

/-- A finite bookkeeping type realizing `certifiedEnlargedRankBound` as a cardinality.

Its final `Fin` coordinate labels only a residual dimension budget.  In particular, this type is
not claimed to be a basis of the image of the actual or enlarged local constraint map. -/
abbrev CertifiedEnlargedRankBudgetIndex (d m M W : ℕ) :=
  Σ r : Fin m,
    ↑(weightedHigherJetTuples d (W + r.val)) ×
      Fin (certifiedContactRankBudget d m M r.val)

/-- The certified enlarged-map rank budget is the cardinality of its finite bookkeeping type. -/
theorem card_certifiedEnlargedRankBudgetIndex (d m M W : ℕ) :
    Fintype.card (CertifiedEnlargedRankBudgetIndex d m M W) =
      certifiedEnlargedRankBound d m M W := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_coe, Fintype.card_fin]
  exact Fin.sum_univ_eq_sum_range
    (fun r ↦ weightedHigherJetCount d (W + r) * certifiedContactRankBudget d m M r) m

/-- The full exact finite numerical certificate compares the exact dimension count with `n`
copies of the certified enlarged-map rank budget.

A later semantic theorem must separately assume the interpolation and contact-map preconditions,
including `0 < d < D`; this predicate records only the strict integer inequality. -/
def ExactFiniteCertificate (n D A d m M W : ℕ) : Prop :=
  n * certifiedEnlargedRankBound d m M W <
    exactInterpolationDimensionCount D A d m M W

end HiddenDerivative
end ReedSolomon
