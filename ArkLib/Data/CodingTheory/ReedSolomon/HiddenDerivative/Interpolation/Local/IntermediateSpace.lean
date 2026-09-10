/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kai Zhe Zheng, Quang Dao, Justin Thaler
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.Local.ConstraintKernel
public import Mathlib.Algebra.BigOperators.Finsupp.Fin


/-!
# The finite intermediate space for local hidden-derivative constraints

After the first local change of variables and reduction modulo `T^m`, an exact interpolation
polynomial lands in the span of

```text
T^r U^a Y₁^b Y^c,   r < m, a ≤ r, b ≤ M, ω(c) ≤ W + r.
```

This file defines that space as an exact finite support restriction.  It also defines the bounded
source rectangles for the exhibited factors `T^r (U - localJetSum)^h`.  Those factors are
truncated modulo `T^m` before membership is asserted: without truncation their expansion can
contain terms of `T`-degree at least `m` and therefore need not belong to the intermediate space.

The translation-support proof is adapted, with permission, from Kai Zhe Zheng's `rs-ld-mca`
formalization at commit `9699ee7a6143f6efe1d8cfed84998a4f8c79c40f`, file
`RSListDecoding/Lemmas/ConstraintFactorization.lean`.  The exact finite coordinate and exhibited
kernel interfaces are new.

## References

* [Brakensiek, Chen, Putterman, Zhang, and Zheng, *Algorithmic List Decoding of Reed--Solomon
  Codes up to Capacity in the Low-Rate Regime*][BCPZZ26], ECCC TR26-164, Section 3.
* [Dao, Kominers, Thaler, and Zheng, *Reed--Solomon List Decoding and Mutual Correlated Agreement
  up to Capacity*][DKTZ26], exact finite interpolation analysis.
-/

@[expose] public section

open PolynomialDifferential


noncomputable section

open scoped BigOperators Pointwise

namespace ReedSolomon.HiddenDerivative

open MvPolynomial

variable {R F : Type*} [CommRing R]
variable {d D A m M W r h : ℕ}

/-! ### Exact monomial predicate -/

/-- Exponent of the visible first jet `Y₁`.  This sum formulation is total at `d = 0`. -/
def localFirstJetExponent (e : LocalVariable d →₀ ℕ) : ℕ :=
  e.sum fun v n ↦ match v with
    | some (some j) => if j.val = 0 then n else 0
    | _ => 0

/-- Exact support predicate for the finite intermediate space. -/
def LocalIntermediateEligibleExponent (d m M W : ℕ)
    (e : LocalVariable d →₀ ℕ) : Prop :=
  e (localT d) < m ∧
    e (localU d) ≤ e (localT d) ∧
    localFirstJetExponent e ≤ M ∧
    Finsupp.weight (localHigherJetWeight d) e ≤ W + e (localT d)

/-! ### Coordinate equivalence and exact finite index -/

/-- Split the visible jets into `Y₁` and `Y₂,...,Y_d`. -/
def localJetIndexSplitEquiv (hd : 0 < d) :
    Fin d ≃ Fin 1 ⊕ Fin (d - 1) :=
  (finCongr (by omega : d = 1 + (d - 1))).trans finSumFinEquiv.symm

/-- Coordinates `(T,U,Y₁,c)` of a local monomial exponent. -/
abbrev LocalExponentCoordinates (d : ℕ) := ℕ × (ℕ × (ℕ × HigherJetTuple d))

/-- Every local exponent splits into its `T`, `U`, `Y₁`, and higher-jet coordinates. -/
def localExponentCoordinatesEquiv (hd : 0 < d) :
    (LocalVariable d →₀ ℕ) ≃ LocalExponentCoordinates d :=
  Finsupp.optionEquiv.trans <|
    Equiv.prodCongr (Equiv.refl ℕ) <|
      Finsupp.optionEquiv.trans <|
        Equiv.prodCongr (Equiv.refl ℕ) <|
          (Finsupp.domCongr (localJetIndexSplitEquiv hd)).toEquiv.trans <|
            Finsupp.sumFinsuppEquivProdFinsupp.trans <|
              Equiv.prodCongr
                (Finsupp.equivFunOnFinite.trans (Equiv.funUnique (Fin 1) ℕ))
                Finsupp.equivFunOnFinite

@[simp]
theorem localExponentCoordinatesEquiv_T (hd : 0 < d) (e : LocalVariable d →₀ ℕ) :
    (localExponentCoordinatesEquiv hd e).1 = e (localT d) :=
  rfl

@[simp]
theorem localExponentCoordinatesEquiv_U (hd : 0 < d) (e : LocalVariable d →₀ ℕ) :
    (localExponentCoordinatesEquiv hd e).2.1 = e (localU d) :=
  rfl

@[simp]
theorem localExponentCoordinatesEquiv_Y₁ (hd : 0 < d) (e : LocalVariable d →₀ ℕ) :
    (localExponentCoordinatesEquiv hd e).2.2.1 = e (localY ⟨0, hd⟩) := by
  simp only [localExponentCoordinatesEquiv, localJetIndexSplitEquiv,
    AddEquiv.toEquiv_eq_coe, Equiv.trans_apply, Finsupp.optionEquiv_apply,
    Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.coe_trans, EquivLike.coe_coe,
    Prod.map_apply, id_eq, Function.comp_apply, Finsupp.domCongr_apply,
    Finsupp.sumFinsuppEquivProdFinsupp_apply, Finsupp.equivFunOnFinite_apply,
    Equiv.funUnique_apply, Finsupp.comapDomain_apply, Finsupp.equivMapDomain_apply,
    Equiv.symm_trans, Equiv.symm_symm, finCongr_symm, finSumFinEquiv_apply_left,
    finCongr_apply, Finsupp.some_apply, localY]
  congr 3

@[simp]
theorem localExponentCoordinatesEquiv_higher (hd : 0 < d)
    (e : LocalVariable d →₀ ℕ) (i : Fin (d - 1)) :
    (localExponentCoordinatesEquiv hd e).2.2.2 i =
      e (localY ⟨i.val + 1, by omega⟩) := by
  simp only [localExponentCoordinatesEquiv, localJetIndexSplitEquiv,
    AddEquiv.toEquiv_eq_coe, Equiv.trans_apply, Finsupp.optionEquiv_apply,
    Equiv.prodCongr_apply, Equiv.coe_refl, Equiv.coe_trans, EquivLike.coe_coe,
    Prod.map_apply, id_eq, Function.comp_apply, Finsupp.domCongr_apply,
    Finsupp.sumFinsuppEquivProdFinsupp_apply, Finsupp.equivFunOnFinite_apply,
    Finsupp.comapDomain_apply, Finsupp.equivMapDomain_apply, Equiv.symm_trans,
    Equiv.symm_symm, finCongr_symm, finSumFinEquiv_apply_right, finCongr_apply,
    Finsupp.some_apply, localY]
  congr 3
  apply Fin.ext
  simp [Nat.add_comm]

/-- Split a sum over visible jets into `Y₁` and `Y₂,...,Y_d`. -/
theorem sum_localJet_eq_first_add_higher (hd : 0 < d) (f : Fin d → ℕ) :
    (∑ j, f j) = f ⟨0, hd⟩ +
      ∑ i : Fin (d - 1), f ⟨i.val + 1, by omega⟩ := by
  calc
    (∑ j, f j) =
        ∑ z : Fin 1 ⊕ Fin (d - 1), f ((localJetIndexSplitEquiv hd).symm z) := by
      symm
      exact Equiv.sum_comp (localJetIndexSplitEquiv hd).symm f
    _ = (∑ i : Fin 1, f ((localJetIndexSplitEquiv hd).symm (Sum.inl i))) +
          ∑ i : Fin (d - 1), f ((localJetIndexSplitEquiv hd).symm (Sum.inr i)) := by
      rw [Fintype.sum_sum_type]
    _ = _ := by
      rw [Fin.sum_univ_one]
      apply congrArg₂ (· + ·)
      · congr 2
      · apply Finset.sum_congr rfl
        intro i hi
        congr 2
        apply Fin.ext
        simp [localJetIndexSplitEquiv, Nat.add_comm]

/-- The first-jet statistic is exactly the `Y₁` coordinate. -/
theorem localFirstJetExponent_eq_coordinate (hd : 0 < d)
    (e : LocalVariable d →₀ ℕ) :
    localFirstJetExponent e = (localExponentCoordinatesEquiv hd e).2.2.1 := by
  rw [localFirstJetExponent, Finsupp.sum_fintype _ _ (by
    intro v
    rcases v with (_ | (_ | j)) <;> simp)]
  simp_rw [Fintype.sum_option]
  rw [zero_add, zero_add, sum_localJet_eq_first_add_higher hd]
  simp only [↓reduceIte, Nat.add_one_ne_zero, Finset.sum_const_zero, add_zero]
  exact (localExponentCoordinatesEquiv_Y₁ hd e).symm

/-- The anisotropic statistic is exactly the weight of the higher tuple. -/
theorem localHigherJetWeight_eq_coordinate (hd : 0 < d)
    (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (localHigherJetWeight d) e =
      higherJetTupleWeight (localExponentCoordinatesEquiv hd e).2.2.2 := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp),
    Fintype.sum_option, Fintype.sum_option, higherJetTupleWeight]
  simp only [localHigherJetWeight, nsmul_eq_mul, mul_zero, zero_add]
  rw [sum_localJet_eq_first_add_higher hd]
  simp [localY, Nat.mul_comm]

/-- Exact finite indices for one fixed `T`-degree. -/
abbrev LocalIntermediateSliceIndex (d r M W : ℕ) :=
  AmbientContactIndex r M × ↑(weightedHigherJetTuples d (W + r))

/-- Exact finite indices for the whole intermediate space. -/
abbrev LocalIntermediateIndex (d m M W : ℕ) :=
  Σ r : Fin m, LocalIntermediateSliceIndex d r.val M W

/-- Coordinate form of exact intermediate-space eligibility. -/
def LocalIntermediateCoordinatesEligible (m M W : ℕ)
    (p : LocalExponentCoordinates d) : Prop :=
  p.1 < m ∧ p.2.1 ≤ p.1 ∧ p.2.2.1 ≤ M ∧
    higherJetTupleWeight p.2.2.2 ≤ W + p.1

/-- Predicate membership is the exact coordinate rectangle at the recorded `T`-degree. -/
theorem localIntermediateEligibleExponent_iff_coordinates (hd : 0 < d)
    (e : LocalVariable d →₀ ℕ) :
    LocalIntermediateEligibleExponent d m M W e ↔
      LocalIntermediateCoordinatesEligible m M W (localExponentCoordinatesEquiv hd e) := by
  simp [LocalIntermediateEligibleExponent, localFirstJetExponent_eq_coordinate hd,
    localHigherJetWeight_eq_coordinate hd, LocalIntermediateCoordinatesEligible]

/-- Eligible exponents are equivalent to eligible split coordinates. -/
def localIntermediateEligibleCoordinateEquiv (hd : 0 < d) :
    {e : LocalVariable d →₀ ℕ // LocalIntermediateEligibleExponent d m M W e} ≃
      {p : LocalExponentCoordinates d // LocalIntermediateCoordinatesEligible m M W p} :=
  Equiv.subtypeEquiv (localExponentCoordinatesEquiv hd) fun e ↦
    localIntermediateEligibleExponent_iff_coordinates hd e

/-- Eligible split coordinates are equivalent to the nested paper index. -/
def localIntermediateCoordinateIndexEquiv :
    {p : LocalExponentCoordinates d // LocalIntermediateCoordinatesEligible m M W p} ≃
      LocalIntermediateIndex d m M W where
  toFun p :=
    ⟨⟨p.1.1, p.2.1⟩,
      (⟨⟨p.1.2.1, Nat.lt_succ_of_le p.2.2.1⟩,
        ⟨p.1.2.2.1, Nat.lt_succ_of_le p.2.2.2.1⟩⟩,
       ⟨p.1.2.2.2, mem_weightedHigherJetTuples.mpr p.2.2.2.2⟩)⟩
  invFun p :=
    ⟨(p.1.val, (p.2.1.1.val, (p.2.1.2.val, p.2.2.1))),
      ⟨p.1.isLt, Nat.le_of_lt_succ p.2.1.1.isLt,
        Nat.le_of_lt_succ p.2.1.2.isLt, mem_weightedHigherJetTuples.mp p.2.2.2⟩⟩
  left_inv p := by
    apply Subtype.ext
    rfl
  right_inv p := by
    rcases p with ⟨r, ⟨⟨a, b⟩, c⟩⟩
    simp

/-- Eligible local exponents are equivalent to the paper's nested finite index. -/
def localIntermediateEligibleEquiv (hd : 0 < d) :
    {e : LocalVariable d →₀ ℕ // LocalIntermediateEligibleExponent d m M W e} ≃
      LocalIntermediateIndex d m M W :=
  (localIntermediateEligibleCoordinateEquiv hd).trans
    localIntermediateCoordinateIndexEquiv

/-! ### The finite intermediate space and its dimension -/

/-- Inject the nested paper index into local monomial exponents. -/
def localIntermediateExponentEmbedding (hd : 0 < d) (m M W : ℕ) :
    LocalIntermediateIndex d m M W ↪ (LocalVariable d →₀ ℕ) :=
  (localIntermediateEligibleEquiv hd).symm.toEmbedding.trans
    ⟨Subtype.val, Subtype.val_injective⟩

/-- The finite set of exact intermediate exponents. -/
def localIntermediateExponents (hd : 0 < d) (m M W : ℕ) :
    Finset (LocalVariable d →₀ ℕ) :=
  Finset.univ.map (localIntermediateExponentEmbedding hd m M W)

@[simp]
theorem mem_localIntermediateExponents (hd : 0 < d) {e : LocalVariable d →₀ ℕ} :
    e ∈ localIntermediateExponents hd m M W ↔
      LocalIntermediateEligibleExponent d m M W e := by
  constructor
  · intro he
    rw [localIntermediateExponents, Finset.mem_map] at he
    rcases he with ⟨i, -, rfl⟩
    exact ((localIntermediateEligibleEquiv hd).symm i).2
  · intro he
    rw [localIntermediateExponents, Finset.mem_map]
    let e' : {e : LocalVariable d →₀ ℕ // LocalIntermediateEligibleExponent d m M W e} :=
      ⟨e, he⟩
    refine ⟨localIntermediateEligibleEquiv hd e', Finset.mem_univ _, ?_⟩
    exact Subtype.ext_iff.mp ((localIntermediateEligibleEquiv hd).symm_apply_apply e')

/-- The paper's exact finite intermediate monomial space `V`. -/
def localIntermediateSpace (F : Type*) [CommSemiring F]
    (hd : 0 < d) (m M W : ℕ) : Submodule F (LocalPolynomial F d) :=
  MvPolynomial.restrictSupport F
    (↑(localIntermediateExponents hd m M W) : Set (LocalVariable d →₀ ℕ))

/-- Membership is the exact paper bound on every support exponent. -/
theorem mem_localIntermediateSpace_iff [CommSemiring F] (hd : 0 < d)
    {P : LocalPolynomial F d} :
    P ∈ localIntermediateSpace F hd m M W ↔
      ∀ e ∈ P.support, LocalIntermediateEligibleExponent d m M W e := by
  rw [localIntermediateSpace, MvPolynomial.mem_restrictSupport_iff]
  simp only [Set.subset_def, Finset.mem_coe, mem_localIntermediateExponents]

/-- Canonical monomial basis of the intermediate space. -/
def localIntermediateSpaceBasis (F : Type*) [CommSemiring F]
    (hd : 0 < d) (m M W : ℕ) :=
  MvPolynomial.basisRestrictSupport (R := F)
    (↑(localIntermediateExponents hd m M W) : Set (LocalVariable d →₀ ℕ))

/-- The exact finite monomial basis supplies the finite-module instance used by rank-nullity. -/
noncomputable instance localIntermediateSpace_moduleFinite
    [CommSemiring F] (hd : 0 < d) :
    Module.Finite F (localIntermediateSpace F hd m M W) :=
  Module.Finite.of_basis (localIntermediateSpaceBasis F hd m M W)

/-- The finite exponent set has the nested paper cardinality. -/
theorem card_localIntermediateExponents (hd : 0 < d) :
    (localIntermediateExponents hd m M W).card =
      ∑ r ∈ Finset.range m,
        weightedHigherJetCount d (W + r) * ambientContactCount r M := by
  rw [localIntermediateExponents, Finset.card_map, Finset.card_univ]
  calc
    Fintype.card (LocalIntermediateIndex d m M W) = ∑ r : Fin m,
          weightedHigherJetCount d (W + r.val) * ambientContactCount r.val M := by
      rw [Fintype.card_sigma]
      apply Finset.sum_congr rfl
      intro r hr
      simp [LocalIntermediateSliceIndex, ambientContactCount, weightedHigherJetCount,
        Nat.mul_comm]
    _ = _ := by
      exact Fin.sum_univ_eq_sum_range
        (fun r ↦ weightedHigherJetCount d (W + r) * ambientContactCount r M) m

/-- The canonical basis identifies finrank with the finite support cardinality. -/
theorem finrank_localIntermediateSpace_eq_card [Field F] (hd : 0 < d) :
    Module.finrank F (localIntermediateSpace F hd m M W) =
      (localIntermediateExponents hd m M W).card := by
  rw [← Fintype.card_coe]
  exact Module.finrank_eq_card_basis (localIntermediateSpaceBasis F hd m M W)

/-- Exact finite dimension of the intermediate space. -/
theorem finrank_localIntermediateSpace [Field F] (hd : 0 < d) :
    Module.finrank F (localIntermediateSpace F hd m M W) =
      ∑ r ∈ Finset.range m,
        weightedHigherJetCount d (W + r) * ambientContactCount r M := by
  rw [finrank_localIntermediateSpace_eq_card hd]
  exact card_localIntermediateExponents hd

/-! ### Bounded source rectangles for the exhibited kernel -/

/-- The finite source coordinates multiplied by `T^r (U - localJetSum)^h`.

The two `Fin` bounds are the positive-part conventions from `Counting.lean`.  Thus an inhabited
index supplies the robust inequalities `a + h ≤ r` and `b + h ≤ M`, without rewriting truncated
subtraction as ordinary subtraction. -/
abbrev KernelSliceSourceIndex (d r M W h : ℕ) :=
  ExhibitedKernelContactIndex r M h × ↑(weightedHigherJetTuples d (W + r))

/-- Exact support predicate for a bounded kernel-slice source polynomial. -/
def KernelSliceSourceEligibleExponent (d r M W h : ℕ)
    (e : LocalVariable d →₀ ℕ) : Prop :=
  e (localT d) = 0 ∧
    e (localU d) < r + 1 - h ∧
    localFirstJetExponent e < M + 1 - h ∧
    Finsupp.weight (localHigherJetWeight d) e ≤ W + r

/-- Coordinate form of bounded source eligibility. -/
def KernelSliceSourceCoordinatesEligible (r M W h : ℕ)
    (p : LocalExponentCoordinates d) : Prop :=
  p.1 = 0 ∧ p.2.1 < r + 1 - h ∧ p.2.2.1 < M + 1 - h ∧
    higherJetTupleWeight p.2.2.2 ≤ W + r

/-- Bounded source eligibility is exactly its split-coordinate rectangle. -/
theorem kernelSliceSourceEligibleExponent_iff_coordinates (hd : 0 < d)
    (e : LocalVariable d →₀ ℕ) :
    KernelSliceSourceEligibleExponent d r M W h e ↔
      KernelSliceSourceCoordinatesEligible r M W h (localExponentCoordinatesEquiv hd e) := by
  simp [KernelSliceSourceEligibleExponent, KernelSliceSourceCoordinatesEligible,
    localFirstJetExponent_eq_coordinate hd, localHigherJetWeight_eq_coordinate hd]

/-- Eligible source exponents in split coordinates. -/
def kernelSliceSourceEligibleCoordinateEquiv (hd : 0 < d) :
    {e : LocalVariable d →₀ ℕ // KernelSliceSourceEligibleExponent d r M W h e} ≃
      {p : LocalExponentCoordinates d // KernelSliceSourceCoordinatesEligible r M W h p} :=
  Equiv.subtypeEquiv (localExponentCoordinatesEquiv hd) fun e ↦
    kernelSliceSourceEligibleExponent_iff_coordinates hd e

/-- Eligible split source coordinates are exactly the executable rectangle index. -/
def kernelSliceSourceCoordinateIndexEquiv :
    {p : LocalExponentCoordinates d // KernelSliceSourceCoordinatesEligible r M W h p} ≃
      KernelSliceSourceIndex d r M W h where
  toFun p :=
    (⟨⟨p.1.2.1, p.2.2.1⟩, ⟨p.1.2.2.1, p.2.2.2.1⟩⟩,
      ⟨p.1.2.2.2, mem_weightedHigherJetTuples.mpr p.2.2.2.2⟩)
  invFun p :=
    ⟨(0, (p.1.1.val, (p.1.2.val, p.2.1))),
      ⟨rfl, p.1.1.isLt, p.1.2.isLt, mem_weightedHigherJetTuples.mp p.2.2⟩⟩
  left_inv p := by
    apply Subtype.ext
    rcases p with ⟨⟨t, u, b, c⟩, ht, hu, hb, hc⟩
    simp only at ht
    subst t
    rfl
  right_inv p := by
    rcases p with ⟨⟨a, b⟩, c⟩
    rfl

/-- Eligible source exponents are equivalent to the exact finite rectangle index. -/
def kernelSliceSourceEligibleEquiv (hd : 0 < d) :
    {e : LocalVariable d →₀ ℕ // KernelSliceSourceEligibleExponent d r M W h e} ≃
      KernelSliceSourceIndex d r M W h :=
  (kernelSliceSourceEligibleCoordinateEquiv hd).trans
    kernelSliceSourceCoordinateIndexEquiv

/-- Inject bounded source coordinates into local monomial exponents. -/
def kernelSliceSourceExponentEmbedding (hd : 0 < d) (r M W h : ℕ) :
    KernelSliceSourceIndex d r M W h ↪ (LocalVariable d →₀ ℕ) :=
  (kernelSliceSourceEligibleEquiv hd).symm.toEmbedding.trans
    ⟨Subtype.val, Subtype.val_injective⟩

/-- Finite support set of one bounded kernel-slice source. -/
def kernelSliceSourceExponents (hd : 0 < d) (r M W h : ℕ) :
    Finset (LocalVariable d →₀ ℕ) :=
  Finset.univ.map (kernelSliceSourceExponentEmbedding hd r M W h)

@[simp]
theorem mem_kernelSliceSourceExponents (hd : 0 < d) {e : LocalVariable d →₀ ℕ} :
    e ∈ kernelSliceSourceExponents hd r M W h ↔
      KernelSliceSourceEligibleExponent d r M W h e := by
  constructor
  · intro he
    rw [kernelSliceSourceExponents, Finset.mem_map] at he
    rcases he with ⟨i, -, rfl⟩
    exact ((kernelSliceSourceEligibleEquiv hd).symm i).2
  · intro he
    rw [kernelSliceSourceExponents, Finset.mem_map]
    let e' : {e : LocalVariable d →₀ ℕ // KernelSliceSourceEligibleExponent d r M W h e} :=
      ⟨e, he⟩
    refine ⟨kernelSliceSourceEligibleEquiv hd e', Finset.mem_univ _, ?_⟩
    exact Subtype.ext_iff.mp ((kernelSliceSourceEligibleEquiv hd).symm_apply_apply e')

/-- Polynomial sources with no `T`, bounded `U` and `Y₁` degrees, and bounded higher-jet weight. -/
def kernelSliceSourceSpace (F : Type*) [CommSemiring F]
    (hd : 0 < d) (r M W h : ℕ) : Submodule F (LocalPolynomial F d) :=
  MvPolynomial.restrictSupport F
    (↑(kernelSliceSourceExponents hd r M W h) : Set (LocalVariable d →₀ ℕ))

/-- Membership in a bounded source space is its exact pointwise support predicate. -/
theorem mem_kernelSliceSourceSpace_iff [CommSemiring F] (hd : 0 < d)
    {G : LocalPolynomial F d} :
    G ∈ kernelSliceSourceSpace F hd r M W h ↔
      ∀ e ∈ G.support, KernelSliceSourceEligibleExponent d r M W h e := by
  rw [kernelSliceSourceSpace, MvPolynomial.mem_restrictSupport_iff]
  simp only [Set.subset_def, Finset.mem_coe, mem_kernelSliceSourceExponents]

/-- Every bounded source support monomial has zero `T`-degree. -/
theorem tDegree_eq_zero_of_mem_kernelSliceSourceSpace [CommSemiring F]
    (hd : 0 < d) {G : LocalPolynomial F d}
    (hG : G ∈ kernelSliceSourceSpace F hd r M W h)
    {e : LocalVariable d →₀ ℕ} (he : e ∈ G.support) :
    e (localT d) = 0 :=
  (mem_kernelSliceSourceSpace_iff hd).mp hG e he |>.1

/-- The source rectangle has the exact exhibited-kernel cardinality from `Counting.lean`. -/
theorem card_kernelSliceSourceExponents (hd : 0 < d) :
    (kernelSliceSourceExponents hd r M W h).card =
      exhibitedKernelContactCount r M h * weightedHigherJetCount d (W + r) := by
  rw [kernelSliceSourceExponents, Finset.card_map, Finset.card_univ]
  simp [KernelSliceSourceIndex, exhibitedKernelContactCount, weightedHigherJetCount]

/-- Canonical monomial basis of a bounded source rectangle. -/
def kernelSliceSourceSpaceBasis (F : Type*) [CommSemiring F]
    (hd : 0 < d) (r M W h : ℕ) :=
  MvPolynomial.basisRestrictSupport (R := F)
    (↑(kernelSliceSourceExponents hd r M W h) : Set (LocalVariable d →₀ ℕ))

/-- Each bounded source rectangle is finite-dimensional over a field. -/
noncomputable instance kernelSliceSourceSpace_moduleFinite
    [CommSemiring F] (hd : 0 < d) :
    Module.Finite F (kernelSliceSourceSpace F hd r M W h) :=
  Module.Finite.of_basis (kernelSliceSourceSpaceBasis F hd r M W h)

/-- Exact finite dimension of a bounded kernel-slice source. -/
theorem finrank_kernelSliceSourceSpace [Field F] (hd : 0 < d) :
    Module.finrank F (kernelSliceSourceSpace F hd r M W h) =
      exhibitedKernelContactCount r M h * weightedHigherJetCount d (W + r) := by
  rw [show Module.finrank F (kernelSliceSourceSpace F hd r M W h) =
      (kernelSliceSourceExponents hd r M W h).card by
    rw [← Fintype.card_coe]
    exact Module.finrank_eq_card_basis (kernelSliceSourceSpaceBasis F hd r M W h)]
  exact card_kernelSliceSourceExponents hd

section SupportWeights

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommMonoid M] [PartialOrder M] [IsOrderedAddMonoid M]
variable {σ τ : Type*}

omit [PartialOrder M] [IsOrderedAddMonoid M] in
private theorem support_weight_C_eq_zero (w : τ → M) (a : R)
    {e : τ →₀ ℕ} (he : e ∈ (C a : MvPolynomial τ R).support) :
    Finsupp.weight w e = 0 := by
  classical
  have he' : e ∈ ({0} : Finset (τ →₀ ℕ)) :=
    MvPolynomial.support_monomial_subset he
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

omit [IsOrderedAddMonoid M] in
private theorem support_weight_sum_le (w : τ → M)
    {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial τ R) {a : M}
    (hP : ∀ i ∈ s, ∀ e ∈ (P i).support, Finsupp.weight w e ≤ a)
    {e : τ →₀ ℕ} (he : e ∈ (s.sum P).support) :
    Finsupp.weight w e ≤ a := by
  classical
  have he' := MvPolynomial.support_sum he
  rcases Finset.mem_biUnion.mp he' with ⟨i, hi, hei⟩
  exact hP i hi e hei

private theorem support_weight_mul_le (w : τ → M)
    {P Q : MvPolynomial τ R} {a b : M}
    (hP : ∀ e ∈ P.support, Finsupp.weight w e ≤ a)
    (hQ : ∀ e ∈ Q.support, Finsupp.weight w e ≤ b)
    {e : τ →₀ ℕ} (he : e ∈ (P * Q).support) :
    Finsupp.weight w e ≤ a + b := by
  classical
  have he' : e ∈ P.support + Q.support := MvPolynomial.support_mul P Q he
  rcases Finset.mem_add.mp he' with ⟨eP, heP, eQ, heQ, rfl⟩
  simpa using add_le_add (hP eP heP) (hQ eQ heQ)

private theorem support_weight_pow_le (w : τ → M)
    {P : MvPolynomial τ R} {a : M}
    (hP : ∀ e ∈ P.support, Finsupp.weight w e ≤ a) (n : ℕ)
    {e : τ →₀ ℕ} (he : e ∈ (P ^ n).support) :
    Finsupp.weight w e ≤ n • a := by
  induction n generalizing e with
  | zero =>
      simpa using le_of_eq (support_weight_C_eq_zero w (1 : R) he)
  | succ n ih =>
      rw [pow_succ] at he
      simpa [succ_nsmul] using support_weight_mul_le w
        (fun e he => ih he) hP he

private theorem support_weight_prod_le (w : τ → M)
    {ι : Type*} (s : Finset ι)
    (P : ι → MvPolynomial τ R) (a : ι → M)
    (hP : ∀ i ∈ s, ∀ e ∈ (P i).support, Finsupp.weight w e ≤ a i)
    {e : τ →₀ ℕ} (he : e ∈ (s.prod P).support) :
    Finsupp.weight w e ≤ s.sum a := by
  classical
  induction s using Finset.induction_on generalizing e with
  | empty =>
      simpa using le_of_eq (support_weight_C_eq_zero w (1 : R) he)
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi] at he
      rw [Finset.sum_insert hi]
      exact support_weight_mul_le w
        (hP i (Finset.mem_insert_self i s))
        (fun e he => ih
          (fun j hj => hP j (Finset.mem_insert_of_mem hj)) he) he

/-- Substitution cannot increase a support weight if every substituted
variable has support weight at most the weight assigned to that variable. -/
private theorem support_weight_bind₁_le (wSource : σ → M) (wTarget : τ → M)
    (f : σ → MvPolynomial τ R)
    (hf : ∀ i, ∀ e ∈ (f i).support,
      Finsupp.weight wTarget e ≤ wSource i)
    {P : MvPolynomial σ R} {a : M}
    (hP : ∀ u ∈ P.support, Finsupp.weight wSource u ≤ a)
    {e : τ →₀ ℕ} (he : e ∈ (MvPolynomial.bind₁ f P).support) :
    Finsupp.weight wTarget e ≤ a := by
  classical
  rw [MvPolynomial.as_sum P, map_sum] at he
  have he' := MvPolynomial.support_sum he
  rcases Finset.mem_biUnion.mp he' with ⟨u, hu, heu⟩
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
    (fun v hv => le_of_eq (support_weight_C_eq_zero wTarget _ hv))
    hprod heu
  have hmono : Finsupp.weight wTarget e ≤ Finsupp.weight wSource u := by
    simpa using hmul
  exact hmono.trans (hP u hu)

end SupportWeights

private def uMinusTWeight (d : ℕ) : LocalVariable d → ℤ
  | none => -1
  | some none => 1
  | some (some _) => 0

/-- Weight selecting the visible first jet `Y₁`. -/
private def visibleFirstWeight (d : ℕ) : LocalVariable d → ℕ
  | some (some j) => if (j : ℕ) = 0 then 1 else 0
  | _ => 0

/-- Anisotropic weight of the visible jets. -/
private def visibleAnisotropicWeight (d : ℕ) : LocalVariable d → ℕ
  | some (some j) => (j : ℕ)
  | _ => 0

private def globalFirstWeight (d : ℕ) : JetVariable d → ℕ
  | none => 0
  | some j => if (j : ℕ) = 1 then 1 else 0

/-- Direct higher-jet weight on the global `Option`-indexed variables. -/
private def globalHigherWeight (d : ℕ) : JetVariable d → ℕ
  | none => 0
  | some j => (j : ℕ) - 1

private theorem weight_uMinusTWeight {d : ℕ} (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (uMinusTWeight d) e =
      (e (localU d) : ℤ) - e (localT d) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp),
    Fintype.sum_option, Fintype.sum_option]
  simp [uMinusTWeight, localU, localT, localAux]
  ring

private theorem weight_visibleFirstWeight {d : ℕ} (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (visibleFirstWeight d) e = localFirstJetExponent e := by
  classical
  rw [Finsupp.weight_apply, localFirstJetExponent,
    Finsupp.sum_fintype _ _ (by simp),
    Finsupp.sum_fintype _ _ (by
      intro i
      rcases i with (_ | (_ | j)) <;> simp)]
  apply Finset.sum_congr rfl
  intro v hv
  rcases v with (_ | (_ | j))
  · simp [visibleFirstWeight]
  · simp [visibleFirstWeight]
  · simp [visibleFirstWeight]

private theorem weight_visibleAnisotropicWeight {d : ℕ}
    (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (visibleAnisotropicWeight d) e =
      Finsupp.weight (localHigherJetWeight d) e := rfl

private theorem weight_globalFirstWeight {d : ℕ} (u : JetVariable d →₀ ℕ) :
    Finsupp.weight (globalFirstWeight d) u = firstJetExponent u := by
  classical
  rw [Finsupp.weight_apply, firstJetExponent, Finsupp.weight_apply,
    Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp),
    Fintype.sum_option]
  simp only [globalFirstWeight, nsmul_eq_mul, mul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases h : (j : ℕ) = 1 <;> simp [h]

private theorem weight_globalHigherWeight {d : ℕ} (u : JetVariable d →₀ ℕ) :
    Finsupp.weight (globalHigherWeight d) u = fullHigherJetWeight u := by
  classical
  rw [Finsupp.weight_apply, fullHigherJetWeight, Finsupp.weight_apply,
    Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp),
    Fintype.sum_option]
  simp [globalHigherWeight, Nat.mul_comm]

/-! ## Support of the first coordinate change -/

private def translateGenerator {R : Type*} [CommRing R] {d : ℕ}
    (alpha y : R) : JetVariable d → LocalPolynomial R d
  | none => C alpha + X (localT d)
  | some j => Fin.cases
      (C y + X (localT d) * X (localU d))
      (fun i => X (localY i)) j

private theorem translateVariable_uMinusT_nonpos
    {R : Type*} [CommRing R] {d : ℕ} (alpha y : R)
    (v : JetVariable d) {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (translateGenerator alpha y v).support) :
    Finsupp.weight (uMinusTWeight d) e ≤ 0 := by
  cases v with
  | none =>
    exact support_weight_add_le (uMinusTWeight d)
      (fun z hz => (support_weight_C_eq_zero _ _ hz).le)
      (fun z hz => by
        rw [support_weight_X_eq _ (localT d) hz]
        simp [uMinusTWeight, localT]) he
  | some j =>
    cases j using Fin.cases with
    | zero =>
      exact support_weight_add_le (uMinusTWeight d)
        (fun z hz => (support_weight_C_eq_zero _ _ hz).le)
        (fun z hz => by
          have hmul := support_weight_mul_le (uMinusTWeight d)
            (a := (-1 : ℤ)) (b := (1 : ℤ))
            (fun z hz => (support_weight_X_eq _ (localT d) hz).le)
            (fun z hz => (support_weight_X_eq _ (localU d) hz).le) hz
          simpa [uMinusTWeight, localT, localU] using hmul) he
    | succ i =>
      rw [support_weight_X_eq _ (localY i) he]
      simp [uMinusTWeight, localY]

private theorem translateVariable_first_le
    {R : Type*} [CommRing R] {d : ℕ} (alpha y : R)
    (v : JetVariable d) {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (translateGenerator alpha y v).support) :
    Finsupp.weight (visibleFirstWeight d) e ≤ globalFirstWeight d v := by
  cases v with
  | none =>
    exact support_weight_add_le (visibleFirstWeight d)
      (fun z hz => by simpa [globalFirstWeight] using
        (support_weight_C_eq_zero (visibleFirstWeight d) _ hz).le)
      (fun z hz => by
        rw [support_weight_X_eq _ (localT d) hz]
        simp [visibleFirstWeight, globalFirstWeight, localT]) he
  | some j =>
    cases j using Fin.cases with
    | zero =>
      exact support_weight_add_le (visibleFirstWeight d)
        (fun z hz => by simpa [globalFirstWeight] using
          (support_weight_C_eq_zero (visibleFirstWeight d) _ hz).le)
        (fun z hz => by
          have hmul := support_weight_mul_le (visibleFirstWeight d)
            (a := 0) (b := 0)
            (fun z hz => (support_weight_X_eq _ (localT d) hz).le)
            (fun z hz => (support_weight_X_eq _ (localU d) hz).le) hz
          simpa [visibleFirstWeight, globalFirstWeight, localT, localU] using hmul) he
    | succ i =>
      rw [support_weight_X_eq _ (localY i) he]
      simp [visibleFirstWeight, globalFirstWeight, localY]

private theorem translateVariable_higher_le
    {R : Type*} [CommRing R] {d : ℕ} (alpha y : R)
    (v : JetVariable d) {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (translateGenerator alpha y v).support) :
    Finsupp.weight (visibleAnisotropicWeight d) e ≤ globalHigherWeight d v := by
  cases v with
  | none =>
    exact support_weight_add_le (visibleAnisotropicWeight d)
      (fun z hz => by simpa [globalHigherWeight] using
        (support_weight_C_eq_zero (visibleAnisotropicWeight d) _ hz).le)
      (fun z hz => by
        rw [support_weight_X_eq _ (localT d) hz]
        simp [visibleAnisotropicWeight, globalHigherWeight, localT]) he
  | some j =>
    cases j using Fin.cases with
    | zero =>
      exact support_weight_add_le (visibleAnisotropicWeight d)
        (fun z hz => by simpa [globalHigherWeight] using
          (support_weight_C_eq_zero (visibleAnisotropicWeight d) _ hz).le)
        (fun z hz => by
          have hmul := support_weight_mul_le (visibleAnisotropicWeight d)
            (a := 0) (b := 0)
            (fun z hz => (support_weight_X_eq _ (localT d) hz).le)
            (fun z hz => (support_weight_X_eq _ (localU d) hz).le) hz
          simpa [visibleAnisotropicWeight, globalHigherWeight, localT, localU] using hmul) he
    | succ i =>
      rw [support_weight_X_eq _ (localY i) he]
      simp [visibleAnisotropicWeight, globalHigherWeight, localY]

/-! ## Global support factors through the intermediate local space -/

private theorem mem_support_filterLocalMonomials
    {R : Type*} [CommRing R] {d : ℕ}
    (predicate : (LocalVariable d →₀ ℕ) → Prop) [DecidablePred predicate]
    (F : LocalPolynomial R d) {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (filterLocalMonomials (R := R) predicate F).support) :
    predicate e ∧ e ∈ F.support := by
  have hc := he
  rw [MvPolynomial.mem_support_iff, coeff_filterLocalMonomials] at hc
  by_cases h : predicate e
  · simp only [h, if_true] at hc
    exact ⟨h, MvPolynomial.mem_support_iff.mpr hc⟩
  · simp only [h, if_false, ne_eq, not_true_eq_false] at hc

/-- Translating an eligible global polynomial to `T,U,Y` coordinates and
discarding `T`-degree at least `m` lands in the finite intermediate space
`V`. -/
theorem translatedLocalTruncation_mem_localIntermediateSpace
    {R : Type*} [CommRing R] {d D A m M W : ℕ}
    (hd : 0 < d) (hdD : d < D)
    (Q : exactInterpolationSpace R D A d m M W hdD) (center received : R) :
    translatedLocalTruncation (d := d) m center received Q.1 ∈
      localIntermediateSpace R hd m M W := by
  classical
  rw [mem_localIntermediateSpace_iff]
  intro e he
  have heFilter := mem_support_filterLocalMonomials
    (R := R) (d := d) (fun z => z (localT d) < m)
    (translateToU d center received Q.1) he
  rcases heFilter with ⟨hT, heTranslate⟩
  change e ∈ (MvPolynomial.bind₁ (translateGenerator center received) Q.1).support at heTranslate
  have hBalance : Finsupp.weight (uMinusTWeight d) e ≤ 0 :=
    support_weight_bind₁_le (fun _ : JetVariable d => (0 : ℤ))
      (uMinusTWeight d) (translateGenerator center received)
      (translateVariable_uMinusT_nonpos center received)
      (fun u hu => by
        rw [Finsupp.weight_apply]
        simp [Finsupp.sum]) heTranslate
  have hFirst : Finsupp.weight (visibleFirstWeight d) e ≤ M :=
    support_weight_bind₁_le (globalFirstWeight d) (visibleFirstWeight d)
      (translateGenerator center received) (translateVariable_first_le center received)
      (fun u hu => by
        rw [weight_globalFirstWeight]
        exact (mem_exactInterpolationSpace_iff.mp Q.2 u hu).1) heTranslate
  have hHigher : Finsupp.weight (visibleAnisotropicWeight d) e ≤ W :=
    support_weight_bind₁_le (globalHigherWeight d)
      (visibleAnisotropicWeight d) (translateGenerator center received)
      (translateVariable_higher_le center received)
      (fun u hu => by
        rw [weight_globalHigherWeight]
        exact (mem_exactInterpolationSpace_iff.mp Q.2 u hu).2.1) heTranslate
  refine ⟨hT, ?_, ?_, ?_⟩
  · rw [weight_uMinusTWeight] at hBalance
    exact_mod_cast (sub_nonpos.mp hBalance)
  · rw [weight_visibleFirstWeight] at hFirst
    exact hFirst
  · rw [weight_visibleAnisotropicWeight] at hHigher
    exact hHigher.trans (Nat.le_add_right W (e (localT d)))

/-! ## Truncated exhibited products land in the intermediate space -/

/-- Signed higher-jet-minus-`T` weight.  Every summand of `localJetSum` has weight zero. -/
private def higherMinusTWeight (d : ℕ) : LocalVariable d → ℤ
  | none => -1
  | some none => 0
  | some (some j) => j.val

private theorem weight_higherMinusTWeight {d : ℕ} (e : LocalVariable d →₀ ℕ) :
    Finsupp.weight (higherMinusTWeight d) e =
      (Finsupp.weight (localHigherJetWeight d) e : ℤ) - e (localT d) := by
  classical
  rw [Finsupp.weight_apply, Finsupp.weight_apply,
    Finsupp.sum_fintype _ _ (by simp), Finsupp.sum_fintype _ _ (by simp)]
  simp_rw [Fintype.sum_option]
  simp [higherMinusTWeight, localHigherJetWeight, localT, Nat.cast_sum,
    Nat.cast_mul, sub_eq_add_neg, mul_comm]
  ring

private theorem localJetTerm_uMinusT_nonpos (j : Fin d)
    {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (C ((-1 : R) ^ j.val) * X (localT d) ^ j.val * X (localY j) :
      LocalPolynomial R d).support) :
    Finsupp.weight (uMinusTWeight d) e ≤ 0 := by
  have hpow : ∀ z ∈ (X (localT d) ^ j.val : LocalPolynomial R d).support,
      Finsupp.weight (uMinusTWeight d) z ≤ 0 := by
    intro z hz
    have hz' := support_weight_pow_le (uMinusTWeight d)
      (a := (-1 : ℤ))
      (fun z hz ↦ (support_weight_X_eq _ (localT d) hz).le) j.val hz
    simpa [uMinusTWeight, localT] using hz'.trans (by simp : j.val • (-1 : ℤ) ≤ 0)
  have hleft : ∀ z ∈
      (C ((-1 : R) ^ j.val) * X (localT d) ^ j.val : LocalPolynomial R d).support,
      Finsupp.weight (uMinusTWeight d) z ≤ 0 := by
    intro z hz
    simpa using support_weight_mul_le (uMinusTWeight d)
      (a := (0 : ℤ)) (b := (0 : ℤ))
      (fun z hz ↦ (support_weight_C_eq_zero _ _ hz).le) hpow hz
  simpa [uMinusTWeight, localY] using support_weight_mul_le
    (uMinusTWeight d) (a := (0 : ℤ)) (b := (0 : ℤ)) hleft
    (fun z hz ↦ (support_weight_X_eq _ (localY j) hz).le) he

private theorem localJetTerm_first_le_one (j : Fin d)
    {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (C ((-1 : R) ^ j.val) * X (localT d) ^ j.val * X (localY j) :
      LocalPolynomial R d).support) :
    Finsupp.weight (visibleFirstWeight d) e ≤ 1 := by
  have hpow : ∀ z ∈ (X (localT d) ^ j.val : LocalPolynomial R d).support,
      Finsupp.weight (visibleFirstWeight d) z ≤ 0 := by
    intro z hz
    simpa [visibleFirstWeight, localT] using
      support_weight_pow_le (visibleFirstWeight d) (a := 0)
        (fun z hz ↦ (support_weight_X_eq _ (localT d) hz).le) j.val hz
  have hleft : ∀ z ∈
      (C ((-1 : R) ^ j.val) * X (localT d) ^ j.val : LocalPolynomial R d).support,
      Finsupp.weight (visibleFirstWeight d) z ≤ 0 := by
    intro z hz
    simpa using support_weight_mul_le (visibleFirstWeight d)
      (a := 0) (b := 0)
      (fun z hz ↦ (support_weight_C_eq_zero _ _ hz).le) hpow hz
  exact support_weight_mul_le (visibleFirstWeight d) (a := 0) (b := 1) hleft
    (fun z hz ↦ by
      rw [support_weight_X_eq _ (localY j) hz]
      by_cases hj : j.val = 0 <;> simp [visibleFirstWeight, localY, hj]) he

private theorem localJetTerm_higherMinusT_nonpos (j : Fin d)
    {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (C ((-1 : R) ^ j.val) * X (localT d) ^ j.val * X (localY j) :
      LocalPolynomial R d).support) :
    Finsupp.weight (higherMinusTWeight d) e ≤ 0 := by
  have hpow : ∀ z ∈ (X (localT d) ^ j.val : LocalPolynomial R d).support,
      Finsupp.weight (higherMinusTWeight d) z ≤ -(j.val : ℤ) := by
    intro z hz
    simpa [higherMinusTWeight, localT] using
      support_weight_pow_le (higherMinusTWeight d) (a := (-1 : ℤ))
        (fun z hz ↦ (support_weight_X_eq _ (localT d) hz).le) j.val hz
  have hleft : ∀ z ∈
      (C ((-1 : R) ^ j.val) * X (localT d) ^ j.val : LocalPolynomial R d).support,
      Finsupp.weight (higherMinusTWeight d) z ≤ -(j.val : ℤ) := by
    intro z hz
    simpa using support_weight_mul_le (higherMinusTWeight d)
      (a := (0 : ℤ)) (b := -(j.val : ℤ))
      (fun z hz ↦ (support_weight_C_eq_zero _ _ hz).le) hpow hz
  have hright : ∀ z ∈ (X (localY j) : LocalPolynomial R d).support,
      Finsupp.weight (higherMinusTWeight d) z ≤ (j.val : ℤ) := by
    intro z hz
    rw [support_weight_X_eq _ (localY j) hz]
    simp [higherMinusTWeight, localY]
  have := support_weight_mul_le (higherMinusTWeight d)
    (a := -(j.val : ℤ)) (b := (j.val : ℤ)) hleft hright he
  simpa using this

private theorem hiddenErrorFactor_uMinusT_le_one {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (hiddenErrorFactor (R := R) d).support) :
    Finsupp.weight (uMinusTWeight d) e ≤ 1 := by
  rw [hiddenErrorFactor, sub_eq_add_neg] at he
  apply support_weight_add_le (uMinusTWeight d)
    (fun z hz ↦ by
      rw [support_weight_X_eq _ (localU d) hz]
      simp [uMinusTWeight, localU, localAux])
    (fun z hz ↦ ?_) he
  rw [MvPolynomial.support_neg] at hz
  rw [localJetSum] at hz
  exact support_weight_sum_le (uMinusTWeight d) Finset.univ _
    (fun j _ z hz ↦ (localJetTerm_uMinusT_nonpos j hz).trans (by omega)) hz

private theorem hiddenErrorFactor_first_le_one {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (hiddenErrorFactor (R := R) d).support) :
    Finsupp.weight (visibleFirstWeight d) e ≤ 1 := by
  rw [hiddenErrorFactor, sub_eq_add_neg] at he
  apply support_weight_add_le (visibleFirstWeight d)
    (fun z hz ↦ by
      rw [support_weight_X_eq _ (localU d) hz]
      simp [visibleFirstWeight, localU, localAux])
    (fun z hz ↦ ?_) he
  rw [MvPolynomial.support_neg] at hz
  rw [localJetSum] at hz
  exact support_weight_sum_le (visibleFirstWeight d) Finset.univ _
    (fun j _ z hz ↦ localJetTerm_first_le_one j hz) hz

private theorem hiddenErrorFactor_higherMinusT_nonpos {e : LocalVariable d →₀ ℕ}
    (he : e ∈ (hiddenErrorFactor (R := R) d).support) :
    Finsupp.weight (higherMinusTWeight d) e ≤ 0 := by
  rw [hiddenErrorFactor, sub_eq_add_neg] at he
  apply support_weight_add_le (higherMinusTWeight d)
    (fun z hz ↦ by
      rw [support_weight_X_eq _ (localU d) hz]
      simp [higherMinusTWeight, localU, localAux])
    (fun z hz ↦ ?_) he
  rw [MvPolynomial.support_neg] at hz
  rw [localJetSum] at hz
  exact support_weight_sum_le (higherMinusTWeight d) Finset.univ _
    (fun j _ z hz ↦ localJetTerm_higherMinusT_nonpos j hz) hz

/-- A bounded exhibited product lands in the exact intermediate space after reduction modulo
`T^m`.  The truncation is essential: the untruncated expansion can contain higher `T` powers. -/
theorem truncate_exhibitedKernelMultiplier_mem_localIntermediateSpace
    (hd : 0 < d) (_hr : r < m)
    (G : kernelSliceSourceSpace R hd r M W h) :
    truncateLocalT (R := R) (d := d) m
        (exhibitedKernelMultiplier (R := R) d r h G.1) ∈
      localIntermediateSpace R hd m M W := by
  classical
  rw [mem_localIntermediateSpace_iff]
  intro e he
  have heFilter := mem_support_filterLocalMonomials
    (R := R) (d := d) (fun z ↦ z (localT d) < m)
    (exhibitedKernelMultiplier (R := R) d r h G.1) he
  rcases heFilter with ⟨hT, heProduct⟩
  rw [exhibitedKernelMultiplier_apply, exhibitedKernelFactor] at heProduct
  have hG := mem_kernelSliceSourceSpace_iff hd |>.mp G.2
  have heSum := MvPolynomial.support_mul
    (X (localT d) ^ r * hiddenErrorFactor (R := R) d ^ h) G.1 heProduct
  rcases Finset.mem_add.mp heSum with ⟨eFactor, heFactor, eSource, heSource, heEq⟩
  have heSource' := hG eSource heSource
  have hhr : h ≤ r := by
    have := Nat.lt_sub_iff_add_lt.mp heSource'.2.1
    omega
  have hhM : h ≤ M := by
    have := Nat.lt_sub_iff_add_lt.mp heSource'.2.2.1
    omega
  have hBalance : Finsupp.weight (uMinusTWeight d) e ≤ 0 := by
    have hTpow : ∀ z ∈ (X (localT d) ^ r : LocalPolynomial R d).support,
        Finsupp.weight (uMinusTWeight d) z ≤ -(r : ℤ) := by
      intro z hz
      simpa [uMinusTWeight, localT] using support_weight_pow_le
        (uMinusTWeight d) (a := (-1 : ℤ))
          (fun z hz ↦ (support_weight_X_eq _ (localT d) hz).le) r hz
    have hHidden : ∀ z ∈ (hiddenErrorFactor (R := R) d ^ h).support,
        Finsupp.weight (uMinusTWeight d) z ≤ (h : ℤ) := by
      intro z hz
      simpa using support_weight_pow_le (uMinusTWeight d) (a := (1 : ℤ))
        (fun z hz ↦ hiddenErrorFactor_uMinusT_le_one hz) h hz
    have hFactor : ∀ z ∈
        (X (localT d) ^ r * hiddenErrorFactor (R := R) d ^ h).support,
        Finsupp.weight (uMinusTWeight d) z ≤ -(r : ℤ) + h :=
      fun z hz ↦ support_weight_mul_le (uMinusTWeight d) hTpow hHidden hz
    have hSource : ∀ z ∈ G.1.support,
        Finsupp.weight (uMinusTWeight d) z ≤ (r : ℤ) - h := by
      intro z hz
      have hz' := hG z hz
      rw [weight_uMinusTWeight, hz'.1]
      have huz : z (localU d) + h ≤ r := by
        have := Nat.lt_sub_iff_add_lt.mp hz'.2.1
        omega
      have huz' : (z (localU d) : ℤ) + h ≤ r := by exact_mod_cast huz
      omega
    simpa [sub_eq_add_neg, add_assoc, add_comm, add_left_comm] using
      support_weight_mul_le (uMinusTWeight d) hFactor hSource heProduct
  have hFirst : Finsupp.weight (visibleFirstWeight d) e ≤ M := by
    have hFactor : ∀ z ∈
        (X (localT d) ^ r * hiddenErrorFactor (R := R) d ^ h).support,
        Finsupp.weight (visibleFirstWeight d) z ≤ h := by
      intro z hz
      have hTpow : ∀ v ∈ (X (localT d) ^ r : LocalPolynomial R d).support,
          Finsupp.weight (visibleFirstWeight d) v ≤ 0 := by
        intro v hv
        simpa [visibleFirstWeight, localT] using support_weight_pow_le
          (visibleFirstWeight d) (a := 0)
            (fun v hv ↦ (support_weight_X_eq _ (localT d) hv).le) r hv
      simpa using support_weight_mul_le (visibleFirstWeight d) hTpow
        (fun v hv ↦ support_weight_pow_le (visibleFirstWeight d) (a := 1)
          (fun v hv ↦ hiddenErrorFactor_first_le_one hv) h hv) hz
    have hSource : ∀ z ∈ G.1.support,
        Finsupp.weight (visibleFirstWeight d) z ≤ M - h := by
      intro z hz
      have hz' := hG z hz
      rw [weight_visibleFirstWeight]
      apply Nat.le_sub_of_add_le
      have := Nat.lt_sub_iff_add_lt.mp hz'.2.2.1
      omega
    have := support_weight_mul_le (visibleFirstWeight d) hFactor hSource heProduct
    simpa [Nat.add_sub_of_le hhM] using this
  have hHigher : Finsupp.weight (visibleAnisotropicWeight d) e ≤
      W + e (localT d) := by
    have hFactor : ∀ z ∈
        (X (localT d) ^ r * hiddenErrorFactor (R := R) d ^ h).support,
        Finsupp.weight (higherMinusTWeight d) z ≤ -(r : ℤ) := by
      intro z hz
      have hTpow : ∀ v ∈ (X (localT d) ^ r : LocalPolynomial R d).support,
          Finsupp.weight (higherMinusTWeight d) v ≤ -(r : ℤ) := by
        intro v hv
        simpa [higherMinusTWeight, localT] using support_weight_pow_le
          (higherMinusTWeight d) (a := (-1 : ℤ))
            (fun v hv ↦ (support_weight_X_eq _ (localT d) hv).le) r hv
      simpa using support_weight_mul_le (higherMinusTWeight d) hTpow
        (fun v hv ↦ support_weight_pow_le (higherMinusTWeight d) (a := (0 : ℤ))
          (fun v hv ↦ hiddenErrorFactor_higherMinusT_nonpos hv) h hv) hz
    have hSource : ∀ z ∈ G.1.support,
        Finsupp.weight (higherMinusTWeight d) z ≤ (W + r : ℕ) := by
      intro z hz
      have hz' := hG z hz
      rw [weight_higherMinusTWeight, hz'.1]
      norm_num
      exact_mod_cast hz'.2.2.2
    have hBound := support_weight_mul_le (higherMinusTWeight d) hFactor hSource heProduct
    rw [weight_higherMinusTWeight] at hBound
    rw [weight_visibleAnisotropicWeight]
    have hBound' : (Finsupp.weight (localHigherJetWeight d) e : ℤ) ≤
        (W : ℤ) + e (localT d) := by
      omega
    exact_mod_cast hBound'
  exact ⟨hT, by
    rw [weight_uMinusTWeight] at hBalance
    exact_mod_cast sub_nonpos.mp hBalance,
    by simpa [weight_visibleFirstWeight] using hFirst,
    by simpa [weight_visibleAnisotropicWeight] using hHigher⟩

/-- The bounded exhibited multiplier as a map into the exact intermediate space. -/
def boundedExhibitedKernelMap (hd : 0 < d) (hr : r < m) :
    kernelSliceSourceSpace R hd r M W h →ₗ[R] localIntermediateSpace R hd m M W :=
  (((truncateLocalT (R := R) (d := d) m).comp
    ((exhibitedKernelMultiplier (R := R) d r h).domRestrict
      (kernelSliceSourceSpace R hd r M W h))).codRestrict
        (localIntermediateSpace R hd m M W)
          (fun G ↦ truncate_exhibitedKernelMultiplier_mem_localIntermediateSpace hd hr G))

@[simp]
theorem boundedExhibitedKernelMap_apply (hd : 0 < d) (hr : r < m)
    (G : kernelSliceSourceSpace R hd r M W h) :
    (boundedExhibitedKernelMap (R := R) hd hr G : LocalPolynomial R d) =
      truncateLocalT (R := R) (d := d) m
        (exhibitedKernelMultiplier (R := R) d r h G.1) :=
  rfl


/-- The enlarged contact map restricted to the finite intermediate space. -/
def intermediateConstraintMap {R : Type*} [CommRing R] {d : ℕ}
    (hd : 0 < d) (m M W : ℕ) :
    localIntermediateSpace R hd m M W →ₗ[R] LocalPolynomial R d :=
  (enlargedLocalConstraintMap (R := R) (d := d) m).domRestrict
    (localIntermediateSpace R hd m M W)

/-- Exact interpolation polynomials translated into the finite intermediate space. -/
def translatedExactLocalTruncation {R : Type*} [CommRing R] {d D A m M W : ℕ}
    (hd : 0 < d) (hdD : d < D) (center received : R) :
    exactInterpolationSpace R D A d m M W hdD →ₗ[R]
      localIntermediateSpace R hd m M W :=
  ((translatedLocalTruncation (d := d) m center received).domRestrict
    (exactInterpolationSpace R D A d m M W hdD)).codRestrict
      (localIntermediateSpace R hd m M W)
        (fun Q ↦ translatedLocalTruncation_mem_localIntermediateSpace hd hdD Q center received)

/-- The actual point constraint factors through the finite intermediate map. -/
theorem exactLocalConstraintAt_eq_intermediate_comp_translated
    {R : Type*} [CommRing R] {d D A m M W : ℕ}
    (hd : 0 < d) (hdD : d < D) (center received : R) :
    exactLocalConstraintAt (D := D) (A := A) (M := M) (W := W) hdD m center received =
      (intermediateConstraintMap (R := R) hd m M W).comp
        (translatedExactLocalTruncation hd hdD center received) := by
  apply LinearMap.ext
  intro Q
  exact localConstraintAt_apply_eq_enlarged_translated m center received Q.1

/-- Every bounded exhibited value is killed by the restricted intermediate map at the canonical
contact threshold. -/
theorem intermediateConstraintMap_boundedExhibitedKernelMap_eq_zero
    (hd : 0 < d) (hr : r < m)
    (G : kernelSliceSourceSpace R hd r M W (contactThreshold d m r)) :
    intermediateConstraintMap (R := R) hd m M W
        (boundedExhibitedKernelMap (R := R) hd hr G) = 0 := by
  change enlargedLocalConstraintMap (R := R) (d := d) m
      (truncateLocalT (R := R) (d := d) m
        (exhibitedKernelMultiplier (R := R) d r (contactThreshold d m r) G.1)) = 0
  rw [enlargedLocalConstraintMap_truncateLocalT]
  exact LinearMap.mem_ker.mp
    (canonicalExhibitedKernelMultiplier_mem_ker hd hr G.1)

end ReedSolomon.HiddenDerivative
