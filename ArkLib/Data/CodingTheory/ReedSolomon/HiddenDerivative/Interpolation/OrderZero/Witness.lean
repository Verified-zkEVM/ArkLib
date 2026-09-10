/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.OrderZero.DimensionCount
public import
ArkLib.Data.CodingTheory.ReedSolomon.HiddenDerivative.Interpolation.OrderZero.LocalImage
public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Solution.Basis
/-!
# Actual order-zero interpolation witnesses from finite rank-nullity

The source monomials are exactly the strict executable support. The global map applies the
actual local constraint map and only restricts its codomain to its proved triangular image.
The resulting kernel element is an actual nonzero polynomial, not a list-cardinality argument.
The quarter-gap endpoint covers n≥3; the separate n=1,2 decoder cases remain outside this file.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative

noncomputable section

open MvPolynomial PolynomialDifferential
open scoped BigOperators

/-- Embed a finite strict interpolation column into the two source variables. -/
def zeroSourceExponent (x b : ℕ) : JetVariable 0 →₀ ℕ :=
  Finsupp.single none x + Finsupp.single (some 0) b

/-- There are exactly two source coordinates at order zero. -/
theorem zeroSourceExponent_reconstruct (e : JetVariable 0 →₀ ℕ) :
    zeroSourceExponent (e none) (e (some 0)) = e := by
  ext v
  cases v with
  | none => simp [zeroSourceExponent]
  | some j =>
    have hj : j = 0 := by apply Fin.ext; omega
    subst j
    simp [zeroSourceExponent]

/-- Finite strict source support, including ambient degree zero. -/
def zeroSourceExponents (D m A : ℕ) : Finset (JetVariable 0 →₀ ℕ) :=
  Finset.univ.image (fun p : ZeroInterpolationIndex D m A ↦
    zeroSourceExponent p.2.val p.1.val)

/-- The finite source set has exactly the executable strict support predicate. -/
theorem mem_zeroSourceExponents (D m A : ℕ) (e : JetVariable 0 →₀ ℕ) :
    e ∈ zeroSourceExponents D m A ↔
      e (some 0) < 2 * m ∧ e none + D * e (some 0) < m * A := by
  constructor
  · intro he
    obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp he
    simpa [zeroSourceExponent] using
      And.intro p.1.isLt (Nat.lt_sub_iff_add_lt.mp p.2.isLt)
  · rintro ⟨hb, hx⟩
    exact Finset.mem_image.mpr ⟨⟨⟨_, hb⟩, ⟨_, Nat.lt_sub_iff_add_lt.mpr hx⟩⟩,
      Finset.mem_univ _, zeroSourceExponent_reconstruct e⟩

/-- Distinct finite columns remain distinct source monomials. -/
theorem card_zeroSourceExponents (D m A : ℕ) :
    (zeroSourceExponents D m A).card = Fintype.card (ZeroInterpolationIndex D m A) := by
  unfold zeroSourceExponents
  rw [Finset.card_image_of_injective, Finset.card_univ]
  intro p q he
  have hx := congrArg (fun e : JetVariable 0 →₀ ℕ ↦ e none) he
  have hb := congrArg (fun e : JetVariable 0 →₀ ℕ ↦ e (some 0)) he
  have hx' : p.2.val = q.2.val := by simpa [zeroSourceExponent] using hx
  have hb' : p.1.val = q.1.val := by simpa [zeroSourceExponent] using hb
  apply (zeroInterpolationIndexEquiv D m A).injective
  apply Subtype.ext
  exact Prod.ext hx' hb'

variable {F : Type*} [Field F]

/-- The finite source polynomial space used by the global linear system. -/
def zeroSourceSpace (F : Type*) [Field F] (D m A : ℕ) :
    Submodule F (DifferentialPolynomial F 0) :=
  MvPolynomial.restrictSupport F (zeroSourceExponents D m A : Set (JetVariable 0 →₀ ℕ))

/-- Source-space membership is precisely the executable interpolation eligibility contract. -/
theorem mem_zeroSourceSpace (D m A : ℕ) (Q : DifferentialPolynomial F 0) :
    Q ∈ zeroSourceSpace F D m A ↔ NonzeroInterpolationMachine.Eligible D m A Q := by
  rw [zeroSourceSpace, MvPolynomial.mem_restrictSupport_iff]
  constructor
  · intro h
    apply (NonzeroInterpolationMachine.eligible_iff (d := 0) D m A Q).mpr
    intro e he
    have hh := (mem_zeroSourceExponents D m A e).mp (h he)
    simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Nat.sub_zero] using hh
  · intro h e he
    apply (mem_zeroSourceExponents D m A e).mpr
    have hh := (NonzeroInterpolationMachine.eligible_iff (d := 0) D m A Q).mp h e he
    simpa only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero, Fin.val_zero, Nat.sub_zero] using hh

instance zeroSourceSpace_finite (D m A : ℕ) : Module.Finite F (zeroSourceSpace F D m A) :=
  Module.Finite.of_basis (MvPolynomial.basisRestrictSupport (R := F)
    (zeroSourceExponents D m A : Set (JetVariable 0 →₀ ℕ)))

/-- Source dimension equals the exact finite column cardinality. -/
theorem finrank_zeroSourceSpace (D m A : ℕ) :
    Module.finrank F (zeroSourceSpace F D m A) = Fintype.card (ZeroInterpolationIndex D m A) := by
  rw [← card_zeroSourceExponents, ← Fintype.card_coe]
  exact Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport (R := F)
    (zeroSourceExponents D m A : Set (JetVariable 0 →₀ ℕ)))

/-- The finite triangular target of each exact local map. -/
def zeroTargetSpace (F : Type*) [Field F] (m : ℕ) : Submodule F (LocalPolynomial F 0) :=
  MvPolynomial.restrictSupport F (zeroLocalExponents m : Set (LocalVariable 0 →₀ ℕ))

instance zeroTargetSpace_finite (m : ℕ) : Module.Finite F (zeroTargetSpace F m) :=
  Module.Finite.of_basis (MvPolynomial.basisRestrictSupport (R := F)
    (zeroLocalExponents m : Set (LocalVariable 0 →₀ ℕ)))

/-- Restrict only the codomain of the actual local constraint map to its proved finite image. -/
def zeroLocalFiniteMap (m : ℕ) (a y : F) :
    DifferentialPolynomial F 0 →ₗ[F] zeroTargetSpace F m :=
  (localConstraintAt (d := 0) m a y).codRestrict (zeroTargetSpace F m) (fun Q ↦
    range_localConstraint_zero_le m a y ⟨Q, rfl⟩)

/-- The exact received-point global map, with finite source and finite triangular targets. -/
def zeroGlobalMap {n : ℕ} (D m A : ℕ) (centers values : Fin n → F) :
    zeroSourceSpace F D m A →ₗ[F] (Fin n → zeroTargetSpace F m) :=
  LinearMap.pi fun i ↦ (zeroLocalFiniteMap m (centers i) (values i)).comp
    (zeroSourceSpace F D m A).subtype

/-- Finite target dimension bounds the actual global range by n triangular local budgets. -/
theorem finrank_zeroGlobalMap_le {n : ℕ} (D m A : ℕ) (centers values : Fin n → F) :
    Module.finrank F (zeroGlobalMap D m A centers values).range ≤ n * (m * (m + 1) / 2) := by
  have ht : Module.finrank F (zeroTargetSpace F m) ≤ m * (m + 1) / 2 := by
    have he : Module.finrank F (zeroTargetSpace F m) = (zeroLocalExponents m).card := by
      rw [← Fintype.card_coe]
      exact Module.finrank_eq_card_basis (MvPolynomial.basisRestrictSupport (R := F)
        (zeroLocalExponents m : Set (LocalVariable 0 →₀ ℕ)))
    rw [he]
    exact card_zeroLocalExponents_le m
  calc
    _ ≤ Module.finrank F (Fin n → zeroTargetSpace F m) := Submodule.finrank_le _
    _ = n * Module.finrank F (zeroTargetSpace F m) := by
      rw [Module.finrank_pi_fintype]
      simp
    _ ≤ _ := Nat.mul_le_mul_left n ht

/-- Strict column surplus gives an actual nonzero eligible polynomial in the global kernel. -/
theorem exists_zero_witness_of_count {n : ℕ} (D m A : ℕ) (centers values : Fin n → F)
    (hcount : n * (m * (m + 1) / 2) < Fintype.card (ZeroInterpolationIndex D m A)) :
    ∃ Q : DifferentialPolynomial F 0, Q ≠ 0 ∧ NonzeroInterpolationMachine.Eligible D m A Q ∧
      ∀ i, localConstraintAt m (centers i) (values i) Q = 0 := by
  let φ := zeroGlobalMap D m A centers values
  have hr := finrank_zeroGlobalMap_le D m A centers values
  have hnull := LinearMap.finrank_range_add_finrank_ker φ
  rw [finrank_zeroSourceSpace] at hnull
  have hk : φ.ker ≠ ⊥ := by
    intro h
    rw [h] at hnull
    simp only [finrank_bot] at hnull
    change Module.finrank F φ.range ≤ _ at hr
    omega
  obtain ⟨Q, hker, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hk
  refine ⟨Q.val, ?_, (mem_zeroSourceSpace D m A Q.val).mp Q.property, ?_⟩
  · intro h
    apply hne
    exact Subtype.ext h
  · intro i
    have h := congrArg (fun z : Fin n → zeroTargetSpace F m ↦ (z i).val)
      (LinearMap.mem_ker.mp hker)
    exact h

/-- Eligibility and nonzero support give a strict individual jet-degree bound. -/
theorem eligible_zero_jetDegree (D m A : ℕ) (Q : DifferentialPolynomial F 0) (hn : Q ≠ 0)
    (he : NonzeroInterpolationMachine.Eligible D m A Q) : jetDegree Q 0 < 2 * m := by
  have h : ∀ e ∈ Q.support, e (some 0) < 2 * m := by
    have hs := (mem_zeroSourceSpace D m A Q).mpr he
    rw [zeroSourceSpace, MvPolynomial.mem_restrictSupport_iff] at hs
    exact fun e he ↦ ((mem_zeroSourceExponents D m A e).mp (hs he)).1
  obtain ⟨e, he'⟩ := MvPolynomial.support_nonempty.mpr hn
  exact (MvPolynomial.degreeOf_lt_iff (Nat.zero_lt_of_lt (h e he'))).mpr h

/-- Quarter-gap parameters construct a genuine strict-support order-zero interpolant for n≥3.
Half-length multiplicity preserves the jet cap 2m≤n needed by the existing root pipeline. -/
theorem exists_quarter_zero_witness (delta : ℝ) (hdelta : (1 / 4 : ℝ) ≤ delta)
    (n k A : ℕ) (hn : 3 ≤ n) (hk : 0 < k)
    (hA : ReedSolomon.agreementThreshold delta n k ≤ A) (centers values : Fin n → F) :
    let D := k - 1
    let m := n / 2
    ∃ Q : DifferentialPolynomial F 0, Q ≠ 0 ∧ NonzeroInterpolationMachine.Eligible D m A Q ∧
      jetDegree Q 0 < 2 * m ∧ differentialWeightedDegree D Q < m * A ∧
      2 * m ≤ n ∧ ∀ p ∈ List.ofFn (fun i ↦ (centers i, values i)),
        localConstraintAt m p.1 p.2 Q = 0 := by
  obtain ⟨_, hcap, hcount⟩ := zero_quarter_columns delta hdelta n k A hn hk hA
  obtain ⟨Q, hne, he, hl⟩ := exists_zero_witness_of_count (k - 1) (n / 2) A centers values hcount
  refine ⟨Q, hne, he, eligible_zero_jetDegree _ _ _ Q hne he,
    NonzeroInterpolationMachine.eligible_weightedDegree _ _ _ Q he hne, hcap, ?_⟩
  intro p hp
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
  exact hl i

/-- The root pipeline characteristic condition follows from the strict cap and characteristic. -/
theorem eligible_zero_characteristic (D m A : ℕ) (Q : DifferentialPolynomial F 0)
    (hne : Q ≠ 0) (he : NonzeroInterpolationMachine.Eligible D m A Q)
    (hchar : 2 * m ≤ ringChar F) : ∀ j, jetDegree Q j < ringChar F := by
  intro j
  have hj : j = 0 := by apply Fin.ext; omega
  subst j
  exact (eligible_zero_jetDegree D m A Q hne he).trans_le hchar

/-- The quarter-gap witness is below characteristic whenever n≤ringChar F.
This is deliberately a characteristic bound, not a field-cardinality bound for extension fields. -/
theorem exists_quarter_zero_witness_characteristic (delta : ℝ)
    (hdelta : (1 / 4 : ℝ) ≤ delta) (n k A : ℕ) (hn : 3 ≤ n) (hk : 0 < k)
    (hA : ReedSolomon.agreementThreshold delta n k ≤ A) (hchar : n ≤ ringChar F)
    (centers values : Fin n → F) :
    let D := k - 1
    let m := n / 2
    ∃ Q : DifferentialPolynomial F 0, Q ≠ 0 ∧ NonzeroInterpolationMachine.Eligible D m A Q ∧
      (∀ j, jetDegree Q j < ringChar F) ∧ differentialWeightedDegree D Q < m * A ∧
      ∀ p ∈ List.ofFn (fun i ↦ (centers i, values i)), localConstraintAt m p.1 p.2 Q = 0 := by
  obtain ⟨Q, hne, he, _, hw, hcap, hl⟩ :=
    exists_quarter_zero_witness delta hdelta n k A hn hk hA centers values
  exact ⟨Q, hne, he, eligible_zero_characteristic _ _ _ Q hne he (hcap.trans hchar), hw, hl⟩

end
end ReedSolomon.HiddenDerivative
