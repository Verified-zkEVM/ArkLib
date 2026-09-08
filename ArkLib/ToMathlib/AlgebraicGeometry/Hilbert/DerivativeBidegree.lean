/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.ToMathlib.AlgebraicGeometry.Hilbert.Bidegree

/-!
# A challenge/jet filtration with a capped derivative coordinate

For three source coordinates `Z,Y,V`, this file refines the challenge/total-jet rectangle by
also bounding the exponent of `V`.  The degree-`N` jet monomials form a truncated triangle:

```text
S(B,C) = (C+1)(B+1) - C(C+1)/2,    C ≤ B.
```

The resulting joint and fixed-challenge leading coefficients are respectively

```text
h(2bc-c²) + 2a(jc+r(b-c)),    jc+r(b-c).
```

These bounds retain the actual derivative degree `r` instead of charging every source-jet
factor at the total jet degree `j`.
-/

noncomputable section

namespace AffineHilbert

open MvPolynomial Polynomial Filter
open scoped BigOperators Topology

variable {F : Type*} [Field F]

/-- The second jet coordinate `V` has weight one; `Z` and `Y` have weight zero. -/
def derivativeWeight : Option (Fin 2) → ℕ
  | some i => if i = 1 then 1 else 0
  | none => 0

@[simp] theorem derivativeWeight_none : derivativeWeight none = 0 := rfl
@[simp] theorem derivativeWeight_zero : derivativeWeight (some 0) = 0 := by
  simp [derivativeWeight]
@[simp] theorem derivativeWeight_one : derivativeWeight (some 1) = 1 := by
  simp [derivativeWeight]

/-- Polynomials with challenge degree at most `a`, total jet degree at most `b`, and
`V`-degree at most `c`. -/
def restrictDerivativeBidegree (a b c : ℕ) :
    Submodule F (MvPolynomial (Option (Fin 2)) F) :=
  restrictSupport F {m | m.weight (challengeWeight (σ := Fin 2)) ≤ a ∧
    m.weight (jetWeight (σ := Fin 2)) ≤ b ∧ m.weight derivativeWeight ≤ c}

theorem mem_restrictDerivativeBidegree {a b c : ℕ}
    {P : MvPolynomial (Option (Fin 2)) F} :
    P ∈ restrictDerivativeBidegree (F := F) a b c ↔
      ∀ m ∈ P.support, m.weight (challengeWeight (σ := Fin 2)) ≤ a ∧
        m.weight (jetWeight (σ := Fin 2)) ≤ b ∧ m.weight derivativeWeight ≤ c := by
  rfl

/-- Capped derivative rectangles are closed under multiplication. -/
theorem mul_mem_restrictDerivativeBidegree {a b c a' b' c' : ℕ}
    {P Q : MvPolynomial (Option (Fin 2)) F}
    (hP : P ∈ restrictDerivativeBidegree (F := F) a b c)
    (hQ : Q ∈ restrictDerivativeBidegree (F := F) a' b' c') :
    P * Q ∈ restrictDerivativeBidegree (F := F) (a + a') (b + b') (c + c') := by
  classical
  rw [mem_restrictDerivativeBidegree] at hP hQ ⊢
  intro m hm
  obtain ⟨i, hi, j, hj, rfl⟩ := Finset.mem_add.mp (support_mul P Q hm)
  simpa only [map_add] using
    ⟨Nat.add_le_add (hP i hi).1 (hQ j hj).1,
      Nat.add_le_add (hP i hi).2.1 (hQ j hj).2.1,
      Nat.add_le_add (hP i hi).2.2 (hQ j hj).2.2⟩

/-- Number of two-variable monomials of total degree at most `B` and `V`-degree at most `C`.
The formula is intended for `C ≤ B`. -/
def twoJetMonomialCount (B C : ℕ) : ℕ :=
  (C + 1) * (B + 1) - C * (C + 1) / 2

/-- The mixed degree bound for a source equation of degrees `(h,j,r)` and a map of degrees
`(a,b,c)`. -/
def mixedDerivativeImageDegree (h j r a b c : ℕ) : ℕ :=
  h * (2 * b * c - c ^ 2) + 2 * a * (j * c + r * (b - c))

/-- The corresponding degree bound after fixing the challenge coordinate. -/
def fixedFiberDerivativeImageDegree (j r b c : ℕ) : ℕ :=
  j * c + r * (b - c)

theorem fixedFiberDerivativeImageDegree_eq
    {j r b c : ℕ} (hrj : r ≤ j) (hcb : c ≤ b) :
    fixedFiberDerivativeImageDegree j r b c = (j - r) * c + r * b := by
  unfold fixedFiberDerivativeImageDegree
  apply Nat.cast_injective (R := ℤ)
  push_cast [Nat.cast_sub hrj, Nat.cast_sub hcb]
  ring

theorem fixedFiberDerivativeImageDegree_mono_source
    {j r j' r' b c : ℕ} (hjj' : j ≤ j') (hrr' : r ≤ r') :
    fixedFiberDerivativeImageDegree j r b c ≤
      fixedFiberDerivativeImageDegree j' r' b c := by
  unfold fixedFiberDerivativeImageDegree
  exact Nat.add_le_add (Nat.mul_le_mul_right c hjj')
    (Nat.mul_le_mul_right (b - c) hrr')

theorem fixedFiberDerivativeImageDegree_mono_map
    {j r b c b' c' : ℕ} (hrj : r ≤ j) (hcb : c ≤ b)
    (hc'b' : c' ≤ b') (hbb' : b ≤ b') (hcc' : c ≤ c') :
    fixedFiberDerivativeImageDegree j r b c ≤
      fixedFiberDerivativeImageDegree j r b' c' := by
  rw [fixedFiberDerivativeImageDegree_eq hrj hcb,
    fixedFiberDerivativeImageDegree_eq hrj hc'b']
  exact Nat.add_le_add (Nat.mul_le_mul_left (j - r) hcc')
    (Nat.mul_le_mul_left r hbb')

theorem le_fixedFiberDerivativeImageDegree
    {j r b c : ℕ} (hc : 0 < c) :
    j ≤ fixedFiberDerivativeImageDegree j r b c := by
  unfold fixedFiberDerivativeImageDegree
  have : j ≤ j * c := by
    simpa only [Nat.mul_one j] using Nat.mul_le_mul_left j hc
  omega

theorem cappedTriangleDegree_le {b c b' c' : ℕ}
    (hcb : c ≤ b) (hc'b' : c' ≤ b') (hbb' : b ≤ b') (hcc' : c ≤ c') :
    2 * b * c - c ^ 2 ≤ 2 * b' * c' - c' ^ 2 := by
  have hsq : c ^ 2 ≤ 2 * b * c := by
    nlinarith
  have hsq' : c' ^ 2 ≤ 2 * b' * c' := by
    nlinarith
  rw [← Nat.cast_le (α := ℤ)]
  rw [Nat.cast_sub hsq, Nat.cast_sub hsq']
  push_cast
  nlinarith

theorem b_le_cappedTriangleDegree {b c : ℕ} (hc : 0 < c) (hcb : c ≤ b) :
    b ≤ 2 * b * c - c ^ 2 := by
  have hsq : c ^ 2 ≤ 2 * b * c := by
    nlinarith
  rw [← Nat.cast_le (α := ℤ)]
  rw [Nat.cast_sub hsq]
  push_cast
  nlinarith

theorem mixedDerivativeImageDegree_mono_source
    {h j r h' j' r' a b c : ℕ}
    (hhh' : h ≤ h') (hjj' : j ≤ j') (hrr' : r ≤ r') :
    mixedDerivativeImageDegree h j r a b c ≤
      mixedDerivativeImageDegree h' j' r' a b c := by
  unfold mixedDerivativeImageDegree
  exact Nat.add_le_add
    (Nat.mul_le_mul_right (2 * b * c - c ^ 2) hhh')
    (Nat.mul_le_mul_left (2 * a)
      (fixedFiberDerivativeImageDegree_mono_source hjj' hrr'))

private theorem finTwo_degree_eq (m : Fin 2 →₀ ℕ) :
    m.degree = m 0 + m 1 := by
  rw [Finsupp.degree_eq_sum]
  simp [Fin.sum_univ_two]

/-- Exponents in the capped two-jet triangle. -/
abbrev CappedTwoJetIndex (B C : ℕ) :=
  {m : Fin 2 →₀ ℕ // m.degree ≤ B ∧ m 1 ≤ C}

noncomputable instance (B C : ℕ) : Fintype (CappedTwoJetIndex B C) :=
  ((Finsupp.finite_of_degree_le B).subset fun _ hm ↦ hm.1).fintype

private def cappedTwoJetEquiv (B C : ℕ) (hCB : C ≤ B) :
    CappedTwoJetIndex B C ≃ Σ v : Fin (C + 1), Fin (B - v.val + 1) where
  toFun m :=
    ⟨⟨m.val 1, by omega⟩, ⟨m.val 0, by
      have hm := m.property.1
      rw [finTwo_degree_eq] at hm
      exact Nat.lt_succ_of_le (le_tsub_of_add_le_right hm)⟩⟩
  invFun p :=
    ⟨Finsupp.single 0 p.2.val + Finsupp.single 1 p.1.val, by
      constructor
      · rw [finTwo_degree_eq]
        simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.single_eq_same,
          ne_eq, zero_ne_one, not_false_eq_true, Finsupp.single_eq_of_ne,
          add_zero, one_ne_zero, zero_add]
        have hvB : p.1.val ≤ B := (Nat.le_of_lt_succ p.1.isLt).trans hCB
        have hy : p.2.val ≤ B - p.1.val := Nat.le_of_lt_succ p.2.isLt
        exact (Nat.add_le_add_right hy p.1.val).trans_eq (Nat.sub_add_cancel hvB)
      · simpa using Nat.le_of_lt_succ p.1.isLt⟩
  left_inv m := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    fin_cases i <;> simp
  right_inv p := by
    rcases p with ⟨⟨v, hv⟩, ⟨y, hy⟩⟩
    apply Sigma.ext
    · apply Fin.ext
      simp
    · apply (Fin.heq_ext_iff (by simp)).2
      change (Finsupp.single (0 : Fin 2) y + Finsupp.single (1 : Fin 2) v) 0 = y
      simp

/-- Cardinality of the capped two-jet exponent triangle. -/
theorem natCard_cappedTwoJetIndex (B C : ℕ) (hCB : C ≤ B) :
    Nat.card (CappedTwoJetIndex B C) = twoJetMonomialCount B C := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_congr (cappedTwoJetEquiv B C hCB),
    Fintype.card_sigma]
  simp only [Fintype.card_fin]
  have hfin :
      Finset.univ.sum (fun v : Fin (C + 1) ↦ B - v.val + 1) =
        Finset.sum (Finset.range (C + 1)) (fun v ↦ B - v + 1) :=
    Fin.sum_univ_eq_sum_range (fun v ↦ B - v + 1) (C + 1)
  rw [hfin]
  rw [twoJetMonomialCount]
  have hsub : ∀ v ∈ Finset.range (C + 1), B - v + 1 = B + 1 - v := by
    intro v hv
    simp only [Finset.mem_range] at hv
    omega
  rw [Finset.sum_congr rfl hsub]
  rw [Finset.sum_tsub_distrib]
  · rw [Finset.sum_const, Finset.card_range, Nat.nsmul_eq_mul, Finset.sum_range_id]
    simp only [Nat.add_sub_cancel]
    rw [Nat.mul_comm (C + 1) C]
  · intro v hv
    simp only [Finset.mem_range] at hv
    omega

/-! ## The capped three-variable embedding -/

/-- Coordinates of the capped challenge/jet embedding. -/
abbrev DerivativeBidegreeIndex (a b c : ℕ) :=
  {m : Option (Fin 2) →₀ ℕ //
    m.weight (challengeWeight (σ := Fin 2)) ≤ a ∧
      m.weight (jetWeight (σ := Fin 2)) ≤ b ∧ m.weight derivativeWeight ≤ c}

private theorem challengeWeight_eq_none (m : Option (Fin 2) →₀ ℕ) :
    m.weight (challengeWeight (σ := Fin 2)) = m none := by
  rw [Finsupp.weight_eq_sum, Fintype.sum_option]
  simp [challengeWeight]

private theorem jetWeight_eq_some_degree (m : Option (Fin 2) →₀ ℕ) :
    m.weight (jetWeight (σ := Fin 2)) = m.some.degree := by
  rw [Finsupp.weight_eq_sum, Fintype.sum_option, Finsupp.degree_eq_sum]
  simp [jetWeight]

private theorem derivativeWeight_eq_one (m : Option (Fin 2) →₀ ℕ) :
    m.weight derivativeWeight = m (some 1) := by
  rw [Finsupp.weight_eq_sum, Fintype.sum_option]
  simp [derivativeWeight]

/-- The capped exponent set is finite. -/
theorem derivativeBidegreeExponentSet_finite (a b c : ℕ) :
    Set.Finite {m : Option (Fin 2) →₀ ℕ |
      m.weight (challengeWeight (σ := Fin 2)) ≤ a ∧
        m.weight (jetWeight (σ := Fin 2)) ≤ b ∧ m.weight derivativeWeight ≤ c} := by
  apply (Finsupp.finite_of_degree_le (a + b)).subset
  intro m hm
  change m.degree ≤ a + b
  rw [Finsupp.degree_eq_sum, Fintype.sum_option]
  have hc : m.weight (challengeWeight (σ := Fin 2)) = m none :=
    challengeWeight_eq_none m
  have hj : m.weight (jetWeight (σ := Fin 2)) = ∑ i : Fin 2, m (some i) := by
    rw [Finsupp.weight_eq_sum, Fintype.sum_option]
    simp [jetWeight]
  change m.weight (challengeWeight (σ := Fin 2)) ≤ a ∧
    m.weight (jetWeight (σ := Fin 2)) ≤ b ∧ m.weight derivativeWeight ≤ c at hm
  rw [hc, hj] at hm
  omega

instance (a b c : ℕ) :
    Module.Finite F (restrictDerivativeBidegree (F := F) a b c) := by
  let S : Set (Option (Fin 2) →₀ ℕ) := {m |
    m.weight (challengeWeight (σ := Fin 2)) ≤ a ∧
      m.weight (jetWeight (σ := Fin 2)) ≤ b ∧ m.weight derivativeWeight ≤ c}
  have hS : S.Finite := derivativeBidegreeExponentSet_finite a b c
  let _ : Finite S := hS.to_subtype
  let basis := basisRestrictSupport F S
  change Module.Finite F (restrictSupport F S)
  exact Module.Finite.of_basis basis

private def derivativeBidegreeIndexEquiv (a b c : ℕ) :
    DerivativeBidegreeIndex a b c ≃ Fin (a + 1) × CappedTwoJetIndex b c where
  toFun m :=
    (⟨m.val none, by
      have hm := m.property.1
      rw [challengeWeight_eq_none] at hm
      exact Nat.lt_succ_of_le hm⟩,
    ⟨m.val.some, by
      have hj := m.property.2.1
      have hv := m.property.2.2
      rw [jetWeight_eq_some_degree] at hj
      rw [derivativeWeight_eq_one] at hv
      exact ⟨hj, hv⟩⟩)
  invFun p :=
    ⟨Finsupp.optionElim p.1.val p.2.val, by
      rw [challengeWeight_eq_none, jetWeight_eq_some_degree, derivativeWeight_eq_one]
      simpa using ⟨Nat.le_of_lt_succ p.1.isLt, p.2.property⟩⟩
  left_inv m := by
    apply Subtype.ext
    exact Finsupp.optionElim_some m.val
  right_inv p := by
    apply Prod.ext
    · apply Fin.ext
      simp
    · apply Subtype.ext
      simp

noncomputable instance (a b c : ℕ) : Fintype (DerivativeBidegreeIndex a b c) :=
  Fintype.ofEquiv (Fin (a + 1) × CappedTwoJetIndex b c)
    (derivativeBidegreeIndexEquiv a b c).symm

/-- Dimension of the capped challenge/jet polynomial space. -/
theorem finrank_restrictDerivativeBidegree (a b c : ℕ) (hcb : c ≤ b) :
    Module.finrank F (restrictDerivativeBidegree (F := F) a b c) =
      (a + 1) * twoJetMonomialCount b c := by
  classical
  let S : Set (Option (Fin 2) →₀ ℕ) := {m |
    m.weight (challengeWeight (σ := Fin 2)) ≤ a ∧
      m.weight (jetWeight (σ := Fin 2)) ≤ b ∧ m.weight derivativeWeight ≤ c}
  have hS : S.Finite := derivativeBidegreeExponentSet_finite a b c
  let _ : Fintype S := hS.fintype
  let basis := basisRestrictSupport F S
  have hfinrank : Module.finrank F (restrictDerivativeBidegree (F := F) a b c) =
      Nat.card S := by
    change Module.finrank F (restrictSupport F S) = Nat.card S
    rw [Module.finrank_eq_card_basis basis, Nat.card_eq_fintype_card]
  rw [hfinrank]
  change Nat.card (DerivativeBidegreeIndex a b c) = _
  rw [Nat.card_congr (derivativeBidegreeIndexEquiv a b c), Nat.card_prod,
    Nat.card_fin, natCard_cappedTwoJetIndex b c hcb]

/-- Evaluate a polynomial in capped embedding coordinates at its source monomials. -/
def derivativeBidegreeMap (a b c : ℕ) :
    MvPolynomial (DerivativeBidegreeIndex a b c) F →ₐ[F]
      MvPolynomial (Option (Fin 2)) F :=
  MvPolynomial.aeval fun m ↦ MvPolynomial.monomial m.val 1

/-- Positive caps make the capped monomial map surjective. -/
theorem derivativeBidegreeMap_surjective (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    Function.Surjective (derivativeBidegreeMap (F := F) a b c) := by
  intro P
  induction P using MvPolynomial.induction_on with
  | C d => exact ⟨MvPolynomial.C d, by simp [derivativeBidegreeMap]⟩
  | add P Q hP hQ =>
      obtain ⟨P', rfl⟩ := hP
      obtain ⟨Q', rfl⟩ := hQ
      exact ⟨P' + Q', by simp⟩
  | mul_X P i hP =>
      obtain ⟨P', rfl⟩ := hP
      let exponent : Option (Fin 2) →₀ ℕ := Finsupp.single i 1
      have hexponent :
          exponent.weight (challengeWeight (σ := Fin 2)) ≤ a ∧
            exponent.weight (jetWeight (σ := Fin 2)) ≤ b ∧
              exponent.weight derivativeWeight ≤ c := by
        rw [challengeWeight_eq_none, jetWeight_eq_some_degree,
          derivativeWeight_eq_one]
        cases i with
        | none =>
            simp [exponent]
            omega
        | some i =>
            fin_cases i <;> simp [exponent] <;> omega
      refine ⟨P' * MvPolynomial.X
        (⟨exponent, hexponent⟩ : DerivativeBidegreeIndex a b c), ?_⟩
      simp only [map_mul, derivativeBidegreeMap, MvPolynomial.aeval_X]
      congr 1

/-- The linear coordinate lift of a source polynomial in the capped filtration. -/
def derivativeBidegreeLift (a b c : ℕ) (P : MvPolynomial (Option (Fin 2)) F)
    (hP : P ∈ restrictDerivativeBidegree (F := F) a b c) :
    MvPolynomial (DerivativeBidegreeIndex a b c) F :=
  ∑ m : P.support, MvPolynomial.C (MvPolynomial.coeff m.val P) *
    MvPolynomial.X (⟨m.val, (mem_restrictDerivativeBidegree.mp hP) m.val m.property⟩ :
      DerivativeBidegreeIndex a b c)

theorem derivativeBidegreeMap_derivativeBidegreeLift
    (a b c : ℕ) (P : MvPolynomial (Option (Fin 2)) F)
    (hP : P ∈ restrictDerivativeBidegree (F := F) a b c) :
    derivativeBidegreeMap a b c (derivativeBidegreeLift a b c P hP) = P := by
  classical
  rw [derivativeBidegreeLift, map_sum]
  simp only [map_mul, derivativeBidegreeMap, MvPolynomial.aeval_C, algebraMap_eq,
    MvPolynomial.aeval_X]
  calc
    ∑ m : P.support, MvPolynomial.C (MvPolynomial.coeff m.val P) *
        MvPolynomial.monomial m.val 1 =
        ∑ m ∈ P.support, MvPolynomial.C (MvPolynomial.coeff m P) *
          MvPolynomial.monomial m 1 := by
            simpa using Finset.sum_attach P.support (fun m ↦
              MvPolynomial.C (MvPolynomial.coeff m P) * MvPolynomial.monomial m 1)
    _ = P := by simpa [monomial_eq] using P.as_sum.symm

theorem derivativeBidegreeLift_totalDegree_le_one
    (a b c : ℕ) (P : MvPolynomial (Option (Fin 2)) F)
    (hP : P ∈ restrictDerivativeBidegree (F := F) a b c) :
    (derivativeBidegreeLift a b c P hP).totalDegree ≤ 1 := by
  classical
  rw [derivativeBidegreeLift]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro m hm
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

/-- The defining ideal of the capped embedding. -/
def derivativeBidegreeIdeal (a b c : ℕ) :
    Ideal (MvPolynomial (DerivativeBidegreeIndex a b c) F) :=
  RingHom.ker (derivativeBidegreeMap (F := F) a b c).toRingHom

theorem derivativeBidegreeIdeal_isPrime (a b c : ℕ) :
    (derivativeBidegreeIdeal (F := F) a b c).IsPrime :=
  RingHom.ker_isPrime (derivativeBidegreeMap a b c).toRingHom

/-- The image of a capped source space in an affine quotient. -/
def quotientDerivativeBidegreeLE
    (I : Ideal (MvPolynomial (Option (Fin 2)) F)) (a b c : ℕ) :
    Submodule F (MvPolynomial (Option (Fin 2)) F ⧸ I) :=
  (restrictDerivativeBidegree (F := F) a b c).map
    (Ideal.Quotient.mkₐ F I).toLinearMap

instance (I : Ideal (MvPolynomial (Option (Fin 2)) F)) (a b c : ℕ) :
    Module.Finite F (quotientDerivativeBidegreeLE I a b c) := by
  unfold quotientDerivativeBidegreeLE
  infer_instance

private def derivativeBidegreeQuotientMap
    (I : Ideal (MvPolynomial (Option (Fin 2)) F)) (a b c : ℕ) :
    restrictDerivativeBidegree (F := F) a b c →ₗ[F]
      quotientDerivativeBidegreeLE I a b c :=
  ((Ideal.Quotient.mkₐ F I).toLinearMap.domRestrict
    (restrictDerivativeBidegree (F := F) a b c)).codRestrict _ (fun p ↦
      ⟨p.val, ⟨p.property, rfl⟩⟩)

private theorem derivativeBidegreeQuotientMap_surjective
    (I : Ideal (MvPolynomial (Option (Fin 2)) F)) (a b c : ℕ) :
    Function.Surjective (derivativeBidegreeQuotientMap I a b c) := by
  rintro ⟨x, ⟨p, hp⟩⟩
  exact ⟨⟨p, hp.1⟩, Subtype.ext hp.2⟩

private def derivativeBidegreeMulToBig
    {g : MvPolynomial (Option (Fin 2)) F} {h j r A B C : ℕ}
    (hg : g ∈ restrictDerivativeBidegree (F := F) h j r)
    (hhA : h ≤ A) (hjB : j ≤ B) (hrC : r ≤ C) :
    restrictDerivativeBidegree (F := F) (A - h) (B - j) (C - r) →ₗ[F]
      restrictDerivativeBidegree (F := F) A B C :=
  ((LinearMap.mulLeft F g).domRestrict
    (restrictDerivativeBidegree (F := F) (A - h) (B - j) (C - r))).codRestrict _
      (fun p ↦ by
        have hp := mul_mem_restrictDerivativeBidegree hg p.property
        change g * p.val ∈ restrictDerivativeBidegree (F := F) A B C
        simpa only [Nat.add_sub_of_le hhA, Nat.add_sub_of_le hjB,
          Nat.add_sub_of_le hrC] using hp)

set_option maxHeartbeats 800000 in
-- The nested quotient and subtype maps require extra elaboration heartbeats.
theorem quotientDerivativeBidegreeLE_finrank_add_le
    {g : MvPolynomial (Option (Fin 2)) F} {h j r A B C : ℕ}
    (hne : g ≠ 0) (hg : g ∈ restrictDerivativeBidegree (F := F) h j r)
    (hhA : h ≤ A) (hjB : j ≤ B) (hrC : r ≤ C) :
    Module.finrank F (quotientDerivativeBidegreeLE (Ideal.span {g}) A B C) +
        Module.finrank F
          (restrictDerivativeBidegree (F := F) (A - h) (B - j) (C - r)) ≤
      Module.finrank F (restrictDerivativeBidegree (F := F) A B C) := by
  let cut := derivativeBidegreeQuotientMap (Ideal.span {g}) A B C
  let mulToKer :
      restrictDerivativeBidegree (F := F) (A - h) (B - j) (C - r) →ₗ[F]
        LinearMap.ker cut :=
    (derivativeBidegreeMulToBig hg hhA hjB hrC).codRestrict _ (fun p ↦ by
      change cut (derivativeBidegreeMulToBig hg hhA hjB hrC p) = 0
      dsimp only [cut]
      apply Subtype.ext
      change Ideal.Quotient.mk (Ideal.span {g}) (g * p.val) = 0
      rw [Ideal.Quotient.eq_zero_iff_mem]
      simpa [mul_comm] using
        (Ideal.span {g}).mul_mem_left p.val (Ideal.subset_span (Set.mem_singleton g)))
  have hmul : Function.Injective mulToKer := by
    intro x y hxy
    apply Subtype.ext
    have hval := congrArg (fun p : LinearMap.ker cut ↦ p.val.val) hxy
    change g * x.val = g * y.val at hval
    exact mul_left_cancel₀ hne hval
  have hsmall : Module.finrank F
      (restrictDerivativeBidegree (F := F) (A - h) (B - j) (C - r)) ≤
      Module.finrank F (LinearMap.ker cut) :=
    LinearMap.finrank_le_finrank_of_injective hmul
  have hsurj : Function.Surjective cut := derivativeBidegreeQuotientMap_surjective _ _ _ _
  have hrank := cut.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hsurj, finrank_top] at hrank
  omega

theorem quotientDerivativeBidegreeLE_finrank_le
    {g : MvPolynomial (Option (Fin 2)) F} {h j r A B C : ℕ}
    (hCB : C ≤ B) (hshift : C - r ≤ B - j)
    (hne : g ≠ 0) (hg : g ∈ restrictDerivativeBidegree (F := F) h j r)
    (hhA : h ≤ A) (hjB : j ≤ B) (hrC : r ≤ C) :
    Module.finrank F (quotientDerivativeBidegreeLE (Ideal.span {g}) A B C) ≤
      (A + 1) * twoJetMonomialCount B C -
        (A - h + 1) * twoJetMonomialCount (B - j) (C - r) := by
  have hbound := quotientDerivativeBidegreeLE_finrank_add_le hne hg hhA hjB hrC
  rw [finrank_restrictDerivativeBidegree A B C hCB,
    finrank_restrictDerivativeBidegree (A - h) (B - j) (C - r) hshift] at hbound
  omega

end AffineHilbert
