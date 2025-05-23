/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao, Chung Thai Nguyen
-/

import ArkLib.Data.FieldTheory.BinaryTowerField.Prelude

/-!
# Binary Tower Fields

Define the binary tower field GF(2^{2^k}) as an iterated quadratic extension of GF(2).

## Main Definitions

- `BinaryTower k` : the binary tower field GF(2^{2^k}) as an iterated quadratic extension of GF(2),
  where BinaryTower 0 = GF(2)

- `ConcreteBinaryTower k` : the concrete implementation of `BinaryTower k` using `BitVec`.

## TODOs

- Define additive NTT basis

## References

- [Wie88] Doug Wiedemann. “An Iterated Quadratic Extension of GF(2)”. In: The Fibonacci Quarterly
  26.4 (1988), pp. 290–295.

- [FP97] John L. Fan and Christof Paar. “On efficient inversion in tower fields of characteristic
  two”. In: Proceedings of IEEE International Symposium on Information Theory. 1997.

- [LCH14] Sian-Jheng Lin, Wei-Ho Chung, and Yunghsiang S. Han. “Novel Polynomial Basis and Its
  Application to Reed–Solomon Erasure Codes”. In: IEEE 55th Annual Symposium on Foundations of
  Computer Science. 2014, pp. 316–325. doi: 10.1109/FOCS.2014.41.

- [DP23] Diamond, Benjamin E., and Jim Posen. "Succinct arguments over towers of binary fields."
  Cryptology ePrint Archive (2023).

- [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over Binary
  Towers." Cryptology ePrint Archive (2024).

-/

noncomputable section

open Polynomial
open AdjoinRoot

structure BinaryTowerResult (F : Type _) (k : ℕ) where
  vec       : (List.Vector F (k + 1))
  instField : (Field F)
  newPoly   : (Polynomial F)
  specialElement: F
  specialElementNeZero: specialElement ≠ 0
  newPolyForm: newPoly = X^2 + (C specialElement * X + 1)
  degNewPolyIs2: (newPoly.degree = 2)
  newPolyIsMonic: (Monic newPoly)
  firstElementOfVecIsSpecialElement [Inhabited F] : vec.1.headI = specialElement
  isNotUnitPoly: (¬IsUnit newPoly)
  instIrreduciblePoly : (Irreducible (p := (newPoly : Polynomial F)))
  sumZeroIffEq: ∀ (x y : F), x + y = 0 ↔ x = y
  instFintype   : Fintype F
  fieldFintypeCard     : Fintype.card F = 2^(2^k)
  traceMapEvalAtRootsIs1 : (∑ i ∈ Finset.range (2^k), specialElement^(2^i)) =
    1 ∧ (∑ i ∈ Finset.range (2^k), (specialElement⁻¹)^(2^i)) = 1

structure BinaryTowerInductiveStepResult (k : ℕ) (prevBTField : Type _)
  (prevBTResult: BinaryTowerResult prevBTField k) [instPrevBTFieldIsField: Field prevBTField]
  (prevPoly : Polynomial prevBTField) (F : Type _)  where
  binaryTowerResult: BinaryTowerResult F (k+1)
  eq_adjoin: F = AdjoinRoot prevPoly
  u_is_root: Eq.mp (eq_adjoin) binaryTowerResult.specialElement = AdjoinRoot.root prevPoly
  eval_defining_poly_at_root: Eq.mp (eq_adjoin) binaryTowerResult.specialElement^2 +
    Eq.mp (eq_adjoin) binaryTowerResult.specialElement * (of prevPoly) prevBTResult.specialElement
    + 1 = 0
set_option maxHeartbeats 1000000 in
def binary_tower_inductive_step
  (k : Nat)
  (prevBTField : Type _) [Field prevBTField]
  (prevBTResult: BinaryTowerResult prevBTField k)
:  Σ' (F : Type _), BinaryTowerInductiveStepResult (k:=k) (prevBTField:=prevBTField)
  (prevBTResult:=prevBTResult) (prevPoly:=prevBTResult.newPoly) (F:=F)
  (instPrevBTFieldIsField:=prevBTResult.instField) := by
  let prevInstField := prevBTResult.instField
  let elts := prevBTResult.vec
  let prevPoly := prevBTResult.newPoly -- poly over prevBTField
  let prevPolyDegIs2 := prevBTResult.degNewPolyIs2
  let prevPolyIsMonic: (Monic prevPoly) := prevBTResult.newPolyIsMonic
  have prevPolyNatDegIs2 : prevPoly.natDegree = 2 := by
    have h_pos : 0 < 2 := by norm_num
    exact (degree_eq_iff_natDegree_eq_of_pos h_pos).mp prevPolyDegIs2
  have degPrevPolyNe0 : prevPoly.degree ≠ 0 := by
    intro h_deg_eq_0
    rw [prevPolyDegIs2] at h_deg_eq_0
    contradiction
  let instPrevPolyIrreducible := prevBTResult.instIrreduciblePoly
  let prevSpecialElement: prevBTField := prevBTResult.specialElement
  let prevPolyForm: prevPoly = X^2 + (C prevSpecialElement * X + 1) := prevBTResult.newPolyForm
  let t1: prevBTField := prevSpecialElement
  have t1_ne_zero_in_prevBTField: t1 ≠ 0 := prevBTResult.specialElementNeZero
  have h_inj_of_prevPoly : Function.Injective (AdjoinRoot.of prevPoly) :=
    AdjoinRoot.of.injective_of_degree_ne_zero degPrevPolyNe0
  have prevSpecialElementNeZero: of prevPoly t1 ≠ 0 := by
    by_contra h -- h: of prevPoly t1 = 0
    rw [map_eq_zero_iff (AdjoinRoot.of prevPoly) h_inj_of_prevPoly] at h
    contradiction -- with t1_ne_zero_in_prevBTField
  have t1_ne_zero: (AdjoinRoot.of prevPoly) t1 ≠ 0 := by
    by_contra h_t1_eq_zero_in_curBTField
    -- def Injective (f : α → β) : Prop :=
      -- ∀ ⦃a₁ a₂⦄, f a₁ = f a₂ → a₁ = a₂
    have h_t1_eq_zero_in_prevBTField: t1 = 0 := by
      exact h_inj_of_prevPoly (by rw [h_t1_eq_zero_in_curBTField, map_zero])
    contradiction
  let instPrevBTFieldIsFinType: Fintype prevBTField := prevBTResult.instFintype
  let prevBTFieldCard: Fintype.card prevBTField = 2^(2^k) := prevBTResult.fieldFintypeCard
  let instFactIrrPoly : Fact (Irreducible prevPoly) := ⟨instPrevPolyIrreducible⟩
  let sumZeroIffEqPrevBTField : ∀ (x y : prevBTField), x + y = (0: prevBTField)
    ↔ x = y := by exact prevBTResult.sumZeroIffEq

  let curBTField := AdjoinRoot prevPoly
  let instFieldAdjoinRootOfPoly : Field curBTField := by
    exact AdjoinRoot.instField (f := prevPoly)
  let instNoZeroDiv : NoZeroDivisors curBTField := inferInstance
  -- Lift to new BTField level
  let u: curBTField := AdjoinRoot.root prevPoly -- adjoined root and generator of curBTField
  let adjoinRootOfPoly : AdjoinRoot prevPoly = curBTField := by
    simp [curBTField]
  have u_is_inv_of_u1: u = u⁻¹⁻¹ := (inv_inv u).symm
  let polyInstances := PolyInstances curBTField u
  let coeffOfX_0: polyInstances.poly.coeff 0 = 1 := polyInstances.coeffOfX_0
  let coeffOfX_1: polyInstances.poly.coeff 1 = u := polyInstances.coeffOfX_1
  let newPoly: curBTField[X] := polyInstances.poly -- = X^2 + (t1 * X + 1)
  let newPolyIsMonic := polyInstances.monic
  let instNotUnitPoly: ¬IsUnit newPoly := polyInstances.not_unit
  let newElts := elts.map (fun x => (AdjoinRoot.of prevPoly).toFun x)
  let polyRingIsMulZero: MulZeroClass (Polynomial prevBTField) := inferInstance
  let instFieldcurBTField : Field curBTField := by exact AdjoinRoot.instField (f := prevPoly)
  let instMulZeroClass : MulZeroClass curBTField := inferInstance

  have unique_linear_form_of_elements_in_curBTField: ∀ (c1 : AdjoinRoot prevPoly),
    ∃! (p : prevBTField × prevBTField), c1 = (of prevPoly) p.1 * root prevPoly + (of prevPoly) p.2
      := unique_linear_form_of_elements_in_adjoined_commring
        (hf_deg := prevPolyNatDegIs2) (hf_monic := prevPolyIsMonic)

  have selfSumEqZero: ∀ (x : curBTField), x + x = 0 := self_sum_eq_zero
    (sumZeroIffEqPrevBTField) (prevPoly) (prevPolyNatDegIs2) (prevPolyIsMonic)

  have sumZeroIffEq: ∀ (x y : curBTField), x + y = 0 ↔ x = y :=
    sum_zero_iff_eq_of_self_sum_zero (selfSumEqZero)

  have u_is_root: u = AdjoinRoot.root prevPoly := rfl
  have h_eval : ∀ (x: curBTField), eval₂ (of prevPoly) x (X^2 + (C t1 * X + 1)) =
    x^2 + (of prevPoly) t1 * x + 1 := eval₂_quadratic_prevField_coeff (of_prev := of prevPoly) t1

  have eval_prevPoly_at_root : u^2 + (of prevPoly) t1 * u + 1 = 0 := by -- u^2 + t1 * u + 1 = 0
      have h_root : eval₂ (of prevPoly) u prevPoly = 0 := by
        rw [u_is_root]
        exact eval₂_root prevPoly
      have h_expand : eval₂ (of prevPoly) u (X^2 + (C t1 * X + 1)) = 0 := by
        rw [←prevPolyForm]
        exact h_root
      rw [h_eval u] at h_expand
      exact h_expand
  have h_u_square: u^2 = u*t1 + 1 := by
    have h1 := eval_prevPoly_at_root
    rw [←add_right_inj (u^2), ←add_assoc, ←add_assoc] at h1
    rw [selfSumEqZero (u^2), zero_add, add_zero, mul_comm] at h1
    exact h1.symm
  have one_ne_zero: (1: curBTField) ≠ (0: curBTField) := by exact NeZero.out
  have specialElementNeZero: u ≠ 0 := by
    by_contra h_eq
    rw [h_eq] at eval_prevPoly_at_root
    have two_pos : 2 ≠ 0 := by norm_num
    rw [zero_pow two_pos, mul_zero, zero_add, zero_add] at eval_prevPoly_at_root
    exact one_ne_zero eval_prevPoly_at_root

    -- Step 2: transform the equations in curBTField and create new value equalitiy bounds
    -- (1) c1 + c2 = (a + c) * u + (b + d) = u
    -- <=> u * (1 - a - c) = b + d
  let u1 := u⁻¹

  have u1_is_root := inverse_is_root_of_prevPoly (of_prev:=of prevPoly) (u:=u) (t1:=t1)
    (specialElementNeZero) (eval_prevPoly_at_root) (h_eval)

  have u_plus_u1_eq_t1: u + u⁻¹ = t1 := sum_of_root_and_inverse_is_t1 (u:=u)
    (t1:=(of prevPoly) t1) (specialElementNeZero)
    (eval_prevPoly_at_root) (sumZeroIffEq)

  have linear_comb_of_prevBTField_is_in_curBTField:
    ∀ (a b : prevBTField), (of prevPoly) a * root prevPoly
    + (of prevPoly) b = (of prevPoly) a * u + (of prevPoly) b := by
    intro a b
    rw [u_is_root]

  let f : curBTField → prevBTField × prevBTField := fun c1 =>
    let h := unique_linear_form_of_elements_in_curBTField c1  -- Get the unique existential proof
    Classical.choose h

  have inj_f : Function.Injective f := by
    intros c1 c2 h_eq
    unfold f at h_eq
    -- h_eq is now (a1, b1) = (a2, b2), where a1, b1, a2, b2 are defined with Classical.choose
    let h1 := unique_linear_form_of_elements_in_curBTField c1
    let h2 := unique_linear_form_of_elements_in_curBTField c2
    let a1 := (Classical.choose h1).1
    let b1 := (Classical.choose h1).2
    let a2 := (Classical.choose h2).1
    let b2 := (Classical.choose h2).2
    -- Assert that h_eq matches the pair equality
    have pair_eq : (a1, b1) = (a2, b2) := h_eq
    have ha : a1 = a2 := (Prod.ext_iff.mp pair_eq).1
    have hb : b1 = b2 := (Prod.ext_iff.mp pair_eq).2
    have h1_eq : c1 = (of prevPoly) a1 * root prevPoly + (of prevPoly) b1 :=
      (Classical.choose_spec h1).1
    have h2_eq : c2 = (of prevPoly) a2 * root prevPoly + (of prevPoly) b2 :=
      (Classical.choose_spec h2).1
    rw [h1_eq, h2_eq, ha, hb]

  have surj_f : Function.Surjective f := by
    intro (p : prevBTField × prevBTField)
    let c1 := (of prevPoly) p.1 * root prevPoly + (of prevPoly) p.2
    use c1
    have h_ex : c1 = (of prevPoly) p.1 * root prevPoly + (of prevPoly) p.2 := rfl
    have h_uniq := unique_linear_form_of_elements_in_curBTField c1
    have p_spec : c1 = (of prevPoly) p.1 * root prevPoly + (of prevPoly) p.2 := h_ex
    -- Show that f c1 = p by using the uniqueness property
    have h_unique := (Classical.choose_spec h_uniq).2 p p_spec
    -- The function f chooses the unique representation, so f c1 must equal p
    exact h_unique.symm

  have bij_f: Function.Bijective f := by
    constructor
    · exact inj_f  -- Injectivity from instFintype
    · exact surj_f

  have equivRelation: curBTField ≃ prevBTField × prevBTField := by
    exact Equiv.ofBijective (f := f) (hf := bij_f)

  let instFintype : Fintype curBTField := by
    exact Fintype.ofEquiv (prevBTField × prevBTField) equivRelation.symm

  let fieldFintypeCard: Fintype.card curBTField = 2^(2^(k + 1)) := by
    let e : curBTField ≃ prevBTField × prevBTField := Equiv.ofBijective f bij_f
    -- ⊢ Fintype.card curBTField = 2 ^ 2 ^ (k + 1)
    have equivCard := Fintype.ofEquiv_card equivRelation.symm
    rw [Fintype.card_prod] at equivCard
    rw [prevBTFieldCard] at equivCard -- equivCard : Fintype.card curBTField = 2 ^ 2 ^ k * 2 ^ 2 ^ k
    have card_simp : 2 ^ 2 ^ k * 2 ^ 2 ^ k = 2 ^ (2 ^ k + 2 ^ k) := by rw [Nat.pow_add]
    have exp_simp : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by
      rw [←Nat.mul_two, Nat.pow_succ]
    rw [card_simp, exp_simp] at equivCard
    exact equivCard
  have mul_eq_implies_eq_of_nonzero {F : Type*} [Field F]
    (x y a b : F) (hx : x * a = b) (hy : y * a = b) (ha : a ≠ 0) : x = y := by
    -- Since x * a = b and y * a = b, we have x * a = y * a
    have h : x * a = y * a := by rw [hx, hy]

    -- Subtract y * a from both sides: x * a - y * a = 0
    have h_diff : x * a - y * a = 0 := by rw [h]; simp

    -- Factorize: (x - y) * a = 0
    have h_factor : (x - y) * a = 0 := by rw [sub_mul]; exact h_diff

    -- In a field, if (x - y) * a = 0 and a ≠ 0, then x - y = 0 (no zero divisors)
    have h_xy : x - y = 0 := by apply (mul_eq_zero.mp h_factor).resolve_right ha

    -- Rearranging gives x = y
    exact sub_eq_zero.mp h_xy

  have prevTraceMapEvalAtRootsIs1: ∑ i ∈ Finset.range (2 ^ k), t1 ^ 2 ^ i = 1
    ∧ ∑ i ∈ Finset.range (2 ^ k), t1⁻¹ ^ 2 ^ i = 1 := by
    exact prevBTResult.traceMapEvalAtRootsIs1

  have liftedPrevTraceMapEvalAtRootsIs1: ∑ i ∈ Finset.range (2 ^ k), (of prevPoly) t1 ^ 2 ^ i = 1
    ∧ ∑ i ∈ Finset.range (2 ^ k), (of prevPoly t1)⁻¹ ^ 2 ^ i = 1 := by
    constructor
    · -- First part: sum of t1^(2^i)
      have h_coe: (of prevPoly) (∑ i ∈ Finset.range (2 ^ k), t1 ^ 2 ^ i) = 1 := by
        rw [prevTraceMapEvalAtRootsIs1.1, map_one]
      have h_map := map_sum (of prevPoly) (fun i => t1 ^ 2 ^ i) (Finset.range (2 ^ k))
      rw [h_map] at h_coe
      rw [Finset.sum_congr rfl (fun i hi => by
        rw [map_pow (f := of prevPoly) (a := t1) (n := 2 ^ i)]
      )] at h_coe
      exact h_coe
    · -- Second part: sum of (t1⁻¹)^(2^i)
      have h_coe: (of prevPoly) (∑ i ∈ Finset.range (2 ^ k), t1⁻¹ ^ 2 ^ i) = 1 := by
        rw [prevTraceMapEvalAtRootsIs1.2, map_one]
      have h_map := map_sum (of prevPoly) (fun i => t1⁻¹ ^ 2 ^ i) (Finset.range (2 ^ k))
      rw [h_map] at h_coe
      rw [Finset.sum_congr rfl (fun i hi => by
        rw [map_pow (f := of prevPoly) (a := t1⁻¹) (n := 2 ^ i)]
      )] at h_coe
      rw [Finset.sum_congr rfl (fun i hi => by -- map_inv₀ here
        rw [map_inv₀ (f := of prevPoly) (a := t1)]
      )] at h_coe
      exact h_coe

  have h_prev_pow_card_sub_one: ∀ (x: prevBTField) (hx: x ≠ 0), x^(2^(2^k)-1) = 1 := by
    intro x hx
    calc
      x^(2^(2^k)-1) = x^(Fintype.card prevBTField - 1) := by rw [prevBTResult.fieldFintypeCard]
      _ = 1 := by exact FiniteField.pow_card_sub_one_eq_one (a:=x) (ha:=hx)
  have h_lifted_prev_pow_card_sub_one: ∀ (x: prevBTField) (hx: x ≠ 0),
    (of prevPoly) x^(2^(2^k)-1) = 1 := by
    intro x hx
    have h1: x^(2^(2^k)-1) = 1 := h_prev_pow_card_sub_one x hx
    have h_coe: (of prevPoly) (x^(2^(2^k)-1)) = 1 := by rw [h1]; rfl
    rw [map_pow (f := of prevPoly) (a := x) (n := 2^(2^k)-1)] at h_coe
    exact h_coe

  have h_t1_pow: (of prevPoly) t1^(2^(2^k)-1) = 1 ∧ (of prevPoly t1)⁻¹^(2^(2^k)-1) = 1 := by
    constructor
    · rw [h_lifted_prev_pow_card_sub_one t1 t1_ne_zero_in_prevBTField]
    · have t1_inv_ne_zero: t1⁻¹ ≠ 0 := by
        intro h
        rw [inv_eq_zero] at h
        contradiction
      rw [←h_lifted_prev_pow_card_sub_one t1⁻¹ t1_inv_ne_zero]
      rw [map_inv₀ (f := of prevPoly) (a := t1)]

  have galoisAutomorphism: u^(2^(2^k)) = u⁻¹ ∧ (u⁻¹)^(2^(2^k)) = u := by
    exact galois_automorphism_power (u:=u) (t1:=t1) (k:=k) (sumZeroIffEq)
      (specialElementNeZero) (prevSpecialElementNeZero) (u_plus_u1_eq_t1)
      (h_u_square) (h_t1_pow) (liftedPrevTraceMapEvalAtRootsIs1)

  have traceMapEvalAtRootsIs1 : (∑ i  ∈ Finset.range (2^(k+1)), u^(2^i)) = 1
    ∧ (∑ i  ∈ Finset.range (2^(k+1)), (u⁻¹)^(2^i)) = 1 := by
    constructor
    · have res := lifted_trace_map_eval_at_roots_prev_BTField (u:=u) (t1:=t1) (k:=k)
        (sumZeroIffEq) (u_plus_u1_eq_t1)
        (galoisAutomorphism) (liftedPrevTraceMapEvalAtRootsIs1.1)
      exact res
    · have u1_plus_u11_eq_t1: u⁻¹ + u⁻¹⁻¹ = (of prevPoly) t1 := by
        rw [←u_plus_u1_eq_t1]
        rw [←u_is_inv_of_u1]
        rw [add_comm]
      have galoisAutomorphismRev: (u⁻¹)^(2^(2^k)) = u⁻¹⁻¹ ∧ (u⁻¹⁻¹)^(2^(2^k)) = u⁻¹ := by
        rw [←u_is_inv_of_u1]
        exact ⟨galoisAutomorphism.2, galoisAutomorphism.1⟩
      have res := lifted_trace_map_eval_at_roots_prev_BTField (u:=u⁻¹) (t1:=t1) (k:=k)
        (sumZeroIffEq) (u1_plus_u11_eq_t1)
        (galoisAutomorphismRev) (liftedPrevTraceMapEvalAtRootsIs1.1)
      exact res

  let instIrreduciblePoly : Irreducible newPoly := by
    by_contra h_not_irreducible
    -- Viet theorem: ¬Irreducible p ↔ ∃ c₁ c₂, p.coeff 0 = c₁ * c₂ ∧ p.coeff 1 = c₁ + c₂
    obtain ⟨c1, c2, h_mul, h_add⟩ :=
      (Monic.not_irreducible_iff_exists_add_mul_eq_coeff
        newPolyIsMonic polyInstances.nat_deg_poly_is_2).mp h_not_irreducible
    rw [polyInstances.coeffOfX_0] at h_mul
    rw [polyInstances.coeffOfX_1] at h_add
    rw [←coeffOfX_1, coeffOfX_1] at h_add -- u = c1 + c2
    rw [←coeffOfX_0, coeffOfX_0] at h_mul -- (1: curBTField) = c1 * c2

    have c1_ne_zero : c1 ≠ 0 := by
      by_contra h_c1_zero
      rw [h_c1_zero, zero_mul] at h_mul
      contradiction

    have c2_is_c1_inv: c2 = c1⁻¹ := by
      apply mul_left_cancel₀ (ha:=c1_ne_zero)
      rw [←h_mul, mul_inv_cancel₀ (a:=c1) (h:=c1_ne_zero)]

    have h_c1_square: c1^2 = c1 * u + 1 := by
      have eq: c1 + c1⁻¹ = u := by
        rw [c2_is_c1_inv] at h_add
        exact h_add.symm
      rw [←mul_right_inj' c1_ne_zero (b:=(c1 + c1⁻¹)) (c:=u)] at eq
      rw [left_distrib] at eq
      rw [←pow_two, mul_inv_cancel₀ (a:=c1) (c1_ne_zero)] at eq
      -- theorem mul_left_inj (a : G) {b c : G} : b * a = c * a ↔ b = c :=
      rw [← add_left_inj (a:=1)] at eq
      rw [add_assoc] at eq
      rw [selfSumEqZero (1: curBTField), add_zero] at eq
      exact eq

    have x_pow_card: ∀ (x: curBTField), x^(2^2^(k + 1)) = x := by
      intro x
      calc
        x^(2^2^(k + 1)) = x^(Fintype.card curBTField) := by rw [fieldFintypeCard]
        _ = x := by exact FiniteField.pow_card x

    have x_pow_exp_of_2_repr := pow_exp_of_2_repr_given_x_square_repr (sumZeroIffEq := sumZeroIffEq)

    have c1_pow_card_eq_c1:= x_pow_card c1 -- Fermat's little theorem
    have two_to_k_plus_1_ne_zero: 2^(k + 1) ≠ 0 := by norm_num
    have c1_pow_card_eq := x_pow_exp_of_2_repr (x:=c1) (z:=u)
      (h_z_non_zero:=specialElementNeZero) (h_x_square:=h_c1_square) (i:=2^(k+1))
    rw [c1_pow_card_eq_c1] at c1_pow_card_eq

    have h_1_le_fin_card: 1 ≤ Fintype.card curBTField := by
      rw [fieldFintypeCard] -- ⊢ 1 ≤ 2 ^ 2 ^ (k + 1)
      apply Nat.one_le_pow
      apply Nat.zero_lt_two
    let instDivisionRing: DivisionRing curBTField := inferInstance
    let instDivisionSemiring: DivisionSemiring curBTField := instDivisionRing.toDivisionSemiring
    let instGroupWithZero: GroupWithZero curBTField := instDivisionSemiring.toGroupWithZero

    have u_pow_card_sub_one: u^(2^2^(k+1) - 1) = 1 := by
      rw [←FiniteField.pow_card_sub_one_eq_one (a:=u) (ha:=specialElementNeZero)]
      rw [fieldFintypeCard]

    rw [u_pow_card_sub_one, mul_one] at c1_pow_card_eq -- u_pow_card_eq : u = u * 1
    -- + ∑ j ∈ Finset.range (2 ^ (k + 1)), (of prevPoly) t1 ^ (2 ^ 2 ^ (k + 1) - 2 ^ (j + 1))
    set rsum := ∑ j ∈ Finset.Icc 1 (2 ^ (k + 1)), u ^ (2 ^ 2 ^ (k + 1) - 2 ^ j) with rsum_def
    have rsum_eq_zero: rsum = 0 := by
      have sum_eq_2: -c1 + c1 = -c1 + (c1 + rsum) := (add_right_inj (a := -c1)).mpr c1_pow_card_eq
      have sum_eq_3: 0 = -c1 + (c1 + rsum) := by
        rw [neg_add_cancel] at sum_eq_2
        exact sum_eq_2
      rw [←add_assoc, neg_add_cancel, zero_add] at sum_eq_3
      exact sum_eq_3.symm

    have rsum_eq_u: rsum = u := rsum_eq_t1_square_aux (u:=u) (k:=k) (x_pow_card:=x_pow_card)
      (u_ne_zero:=specialElementNeZero) (traceMapEvalAtRootsIs1)

    have rsum_ne_zero: rsum ≠ 0 := by
      rw [rsum_eq_u]
      exact specialElementNeZero

    rw [rsum_eq_zero] at rsum_ne_zero
    contradiction

  let newVec := u ::ᵥ newElts
  let firstElementOfVecIsSpecialElement: newVec.1.headI = u := rfl

  let btResult: BinaryTowerResult curBTField (k + 1) := {
    vec := newVec,
    instField := instFieldAdjoinRootOfPoly,
    newPoly := newPoly,
    firstElementOfVecIsSpecialElement := firstElementOfVecIsSpecialElement,
    isNotUnitPoly := instNotUnitPoly,
    instIrreduciblePoly := instIrreduciblePoly,
    sumZeroIffEq := sumZeroIffEq,
    specialElement := u,
    specialElementNeZero := specialElementNeZero,
    newPolyForm := polyInstances.poly_form,
    degNewPolyIs2 := polyInstances.deg_poly_is_2,
    newPolyIsMonic := newPolyIsMonic,
    instFintype := instFintype,
    fieldFintypeCard := fieldFintypeCard,
    traceMapEvalAtRootsIs1 := traceMapEvalAtRootsIs1
  }

  have u_eq_btResult_specialElement: u = btResult.specialElement := rfl
  have t1_eq_prevBTResult_specialElement: t1 = prevBTResult.specialElement := rfl
  rw [←mul_comm] at eval_prevPoly_at_root

  let btInductiveStepResult: BinaryTowerInductiveStepResult (k:=k) (prevBTField:=prevBTField)
    (prevBTResult:=prevBTResult) (prevPoly:=prevBTResult.newPoly)
    (F:=curBTField) (instPrevBTFieldIsField:=prevBTResult.instField) := {
    binaryTowerResult := btResult,
    eq_adjoin := adjoinRootOfPoly
    u_is_root := u_is_root,
    eval_defining_poly_at_root := eval_prevPoly_at_root
  }

  exact ⟨curBTField, btInductiveStepResult⟩

-- def BinaryTower (k : ℕ) : Σ' (F : Type _), BinaryTowerResult F k :=
def BinaryTowerAux (k : ℕ) (rec : ∀ m : ℕ, m < k → Σ' (F : Type _), BinaryTowerResult F m) :
    Σ' (F : Type _), BinaryTowerResult F k :=
  match k with
  | 0 =>
    let curBTField := GF(2)
    let newList : List.Vector (GF(2)) 1 := List.Vector.cons (1 : GF(2)) List.Vector.nil
    let specialElement : GF(2) := newList.1.headI
    let firstElementOfVecIsSpecialElement: newList.1.headI = specialElement := rfl
    let specialElementIs1: specialElement = 1 := by
      unfold specialElement
      rfl
    let specialElementNeZero: specialElement ≠ 0 := by
      rw [specialElementIs1]
      norm_num
    let polyInstances := PolyInstances curBTField specialElement
    let newPoly := polyInstances.poly
    let newPolyIsMonic := polyInstances.monic
    let instNotUnitPoly := polyInstances.not_unit

    let instNoZeroDiv : NoZeroDivisors (GF(2)) := inferInstance
    let instNontrivial : Nontrivial (GF(2)) := inferInstance
    let polyRingIsMulZero: MulZeroClass (Polynomial (GF(2))) := inferInstance
    let polyRingIsCommGroupWithZero : CommMonoidWithZero (Polynomial (GF(2))) := inferInstance
    let polyRingIsNontrivial : Nontrivial (Polynomial (GF(2))) := inferInstance

    let instIrreduciblePoly : Irreducible newPoly := by
      by_contra h_not_irreducible
      -- ¬Irreducible p ↔ ∃ c₁ c₂, p.coeff 0 = c₁ * c₂ ∧ p.coeff 1 = c₁ + c₂
      obtain ⟨c₁, c₂, h_mul, h_add⟩ :=
        (Monic.not_irreducible_iff_exists_add_mul_eq_coeff
          newPolyIsMonic polyInstances.nat_deg_poly_is_2).mp h_not_irreducible
      rw [polyInstances.coeffOfX_0] at h_mul -- 1 = c₁ * c₂
      rw [polyInstances.coeffOfX_1] at h_add -- specialElement = c₁ + c₂
      -- since c₁, c₂ ∈ GF(2), c₁ * c₂ = 1 => c₁ = c₂ = 1
      have c1_c2_eq_one : c₁ = 1 ∧ c₂ = 1 := by
        -- In GF(2), elements are only 0 or 1
        have c1_cases : c₁ = 0 ∨ c₁ = 1 := by exact GF_2_value_eq_zero_or_one c₁
        have c2_cases : c₂ = 0 ∨ c₂ = 1 := by exact GF_2_value_eq_zero_or_one c₂

        -- Case analysis on c₁ and c₂
        rcases c1_cases with c1_zero | c1_one
        · -- If c₁ = 0
          rw [c1_zero] at h_mul
          -- Then 0 * c₂ = 1, contradiction
          simp at h_mul
        · -- If c₁ = 1
          rcases c2_cases with c2_zero | c2_one
          · -- If c₂ = 0
            rw [c2_zero] at h_mul
            -- Then 1 * 0 = 1, contradiction
            simp at h_mul
          · -- If c₂ = 1
            -- Then we have our result
            exact ⟨c1_one, c2_one⟩

      -- Now we can show specialElement = 0
      have specialElement_eq_zero : specialElement = 0 := by
        rw [h_add]  -- Use c₁ + c₂ = specialElement
        rw [c1_c2_eq_one.1, c1_c2_eq_one.2]  -- Replace c₁ and c₂ with 1
        -- In GF(2), 1 + 1 = 0
        apply GF_2_one_add_one_eq_zero

      -- But we know specialElement = 1
      have specialElement_eq_one : specialElement = 1 := by
        unfold specialElement
        simp [newList]

      rw [specialElement_eq_zero] at specialElement_eq_one
      -- (0: GF(2)) = (1: GF(2))

      have one_ne_zero_in_gf2 : (1: GF(2)) ≠ (0: GF(2)) := by
        exact NeZero.out
      contradiction

    let sumZeroIffEq: ∀ (x y : GF(2)), x + y = 0 ↔ x = y := by
      intro x y
      constructor
      · -- (→) If x + y = 0, then x = y
        intro h_sum_zero
        -- Case analysis on x
        rcases GF_2_value_eq_zero_or_one x with x_zero | x_one
        · -- Case x = 0
          rcases GF_2_value_eq_zero_or_one y with y_zero | y_one
          · -- Case y = 0
            rw [x_zero, y_zero]
          · -- Case y = 1
            rw [x_zero, y_one] at h_sum_zero
            -- 0 + 1 = 0
            simp at h_sum_zero
        · -- Case x = 1
          rcases GF_2_value_eq_zero_or_one y with y_zero | y_one
          · -- Case y = 0
            rw [x_one, y_zero] at h_sum_zero
            -- 1 + 0 = 0
            simp at h_sum_zero
          · -- Case y = 1
            rw [x_one, y_one]
      · -- (←) If x = y, then x + y = 0
        intro h_eq
        rw [h_eq]
        -- In GF(2), x + x = 0 for any x
        rcases GF_2_value_eq_zero_or_one y with y_zero | y_one
        · rw [y_zero]
          simp
        · rw [y_one]
          exact GF_2_one_add_one_eq_zero
    let instFintype: Fintype (GF(2)) := GF_2_fintype
    let fieldFintypeCard: Fintype.card (GF(2)) = 2^(2^0) := by exact GF_2_card
    have traceMapEvalAtRootsIs1 : (∑ i ∈ Finset.range (2^0), specialElement^(2^i)) = 1
      ∧ (∑ i ∈ Finset.range (2^0), (specialElement⁻¹)^(2^i)) = 1 := by
      constructor
      · -- Prove first part: (∑ i ∈ Finset.range (2^0), specialElement^(2^i)) = 1
        rw [Nat.pow_zero] -- 2^0 = 1
        rw [Finset.range_one] -- range 1 = {0}
        rw [specialElementIs1] -- specialElement = 1
        norm_num
      · -- Prove second part: (∑ i ∈ Finset.range (2^0), (specialElement⁻¹)^(2^i)) = 1
        rw [Nat.pow_zero] -- 2^0 = 1
        simp [Finset.range_one] -- range 1 = {0}
        exact specialElementIs1

    let result: BinaryTowerResult curBTField 0 :={
      vec := newList,
      instField := inferInstance,
      newPoly := newPoly,
      specialElement := specialElement,
      specialElementNeZero := specialElementNeZero,
      newPolyForm := polyInstances.poly_form,
      degNewPolyIs2 := polyInstances.deg_poly_is_2,
      newPolyIsMonic := newPolyIsMonic,
      firstElementOfVecIsSpecialElement := firstElementOfVecIsSpecialElement,
      isNotUnitPoly := instNotUnitPoly,
      instIrreduciblePoly := instIrreduciblePoly,
      sumZeroIffEq := sumZeroIffEq,
      instFintype := instFintype,
      fieldFintypeCard := fieldFintypeCard,
      traceMapEvalAtRootsIs1 := traceMapEvalAtRootsIs1
    }

    ⟨ curBTField, result ⟩
  | k + 1 =>
    let prevBTResult := rec k (Nat.lt_succ_self k)
    let instPrevBTield := prevBTResult.2.instField
    let inductive_result := binary_tower_inductive_step (k:=k)
      (prevBTField:=prevBTResult.fst) (prevBTResult:=prevBTResult.snd)
    let res := ⟨ inductive_result.fst, inductive_result.snd.binaryTowerResult ⟩
    res

def BinaryTower (k : ℕ) : Σ' (F : Type _), BinaryTowerResult F k :=
  WellFounded.fix (measure id).wf (fun k rec => BinaryTowerAux k rec) k

namespace BinaryTower

@[simp]
def BTField (k : ℕ) := (BinaryTower k).1

lemma BTField_is_BTFieldAux (k : ℕ) :
  BTField k = (BinaryTowerAux k (fun m _ => BinaryTower m)).1 := by
  unfold BTField
  rw [BinaryTower]
  rw [WellFounded.fix_eq]
  rfl

@[simp]
instance BTFieldIsField (k : ℕ) : Field (BTField k) := (BinaryTower k).2.instField

@[simp]
instance CommRing (k : ℕ) : CommRing (BTField k) := Field.toCommRing

@[simp]
instance Nontrivial (k : ℕ) : Nontrivial (BTField k) := inferInstance

@[simp]
instance Inhabited (k : ℕ) : Inhabited (BTField k) where
  default := (0: BTField k)

@[simp]
instance BTFieldNeZero1 (k: ℕ): NeZero (1 : BTField k) := by
  unfold BTField
  exact @neZero_one_of_nontrivial_comm_monoid_zero (BTField k) _ (Nontrivial k)

@[simp]
instance Fintype (k : ℕ) : Fintype (BTField k) := (BinaryTower k).2.instFintype

@[simp]
def BTFieldCard (k : ℕ): Fintype.card (BTField k) = 2^(2^k) := (BinaryTower k).2.fieldFintypeCard

@[simp]
instance BTFieldIsDomain (k : ℕ) : IsDomain (BTField k) := inferInstance

@[simp]
instance BTFieldNoZeroDiv (k : ℕ) : NoZeroDivisors (BTField k) := by
  unfold BTField
  infer_instance

@[simp]
def sumZeroIffEq (k : ℕ) : ∀ (x y : BTField k), x + y = 0 ↔ x = y := (BinaryTower k).2.sumZeroIffEq

@[simp]
instance BTFieldChar2 (k : ℕ): CharP (BTField k) 2 := by
  have h_two : (2 : (BTField k)) = 0 := by
    have h := sumZeroIffEq 1 1
    simp only [true_iff] at h
    exact two_eq_zero_in_char2_field (sumZeroIffEq k)
  have cast_eq_zero_iff : ∀ x : ℕ, (x : (BTField k)) = 0 ↔ 2 ∣ x  := by
    intro x
    constructor
    · intro h
      have h_one : (1 : BTField k) ≠ 0 := (BTFieldNeZero1 k).out
      by_cases hx : x = 0
      · simp [hx]
      · have : x = 2 * (x / 2) + x % 2 := (Nat.div_add_mod x 2).symm
        rw [this, Nat.cast_add, Nat.cast_mul, Nat.cast_two, h_two, zero_mul, zero_add] at h
        have h_mod : x % 2 < 2 := Nat.mod_lt x two_pos
        interval_cases n : x % 2
        · exact Nat.dvd_of_mod_eq_zero n
        · rw [←n] at h
          rw [n] at h
          rw [Nat.cast_one] at h
          contradiction
    · intro h
      obtain ⟨m, rfl⟩ := h
      rw [Nat.cast_mul, Nat.cast_two, h_two]
      norm_num
  let res : CharP (BTField k) 2 := { cast_eq_zero_iff := cast_eq_zero_iff }
  exact res

@[simp]
theorem BTField_0_is_GF_2 : (BTField 0) = (GF(2)) := by
  unfold BTField
  rw [BinaryTower]
  rw [WellFounded.fix_eq]
  rfl

@[simp]
def list (k : ℕ) : List.Vector (BTField k) (k + 1) := (BinaryTower k).2.vec

@[simp]
def poly (k : ℕ) : Polynomial (BTField k) := (BinaryTower k).2.newPoly

@[simp]
def Z (k : ℕ) : BTField k := (list k).1.headI -- the special extension field elements Z_k

@[coe]
theorem field_eq_adjoinRoot_poly (k : ℕ) : AdjoinRoot (poly k) = BTField (k+1) := by
  let prevBTResult := BinaryTower k
  let _instPrevBTield := prevBTResult.2.instField
  let step := binary_tower_inductive_step k prevBTResult.fst prevBTResult.snd
  let eq := step.snd.eq_adjoin
  exact eq

instance coe_field_adjoinRoot (k : ℕ): Coe (AdjoinRoot (poly k)) (BTField (k+1)) where
  coe := Eq.mp (field_eq_adjoinRoot_poly k)

@[simp]
theorem Z_eq_adjointRoot_root (k : ℕ): Z (k+1) = AdjoinRoot.root (poly k) := by
  let prevBTResult := BinaryTower k
  let _instPrevBTield := prevBTResult.2.instField
  let step := binary_tower_inductive_step k prevBTResult.fst prevBTResult.snd
  let eq := step.snd.u_is_root
  exact eq

lemma poly_eq (k: ℕ): poly k = (BinaryTower k).2.newPoly := rfl
@[simp]

lemma list_0: list 0 = List.Vector.cons (1 : GF(2)) List.Vector.nil := by
  unfold list
  rfl

@[simp]
lemma list_eq (k : ℕ):
  list (k+1) = (Z (k+1)) ::ᵥ (list k).map (AdjoinRoot.of (poly k)) := by
  unfold list
  rfl

lemma Z_is_special_element (k: ℕ): Z k = (BinaryTower k).2.specialElement := by
  unfold Z
  match k with
  | 0 => rfl
  | k+1 =>
    -- u ::ᵥ newElts
    have head_eq: (list (k+1)).1.headI = (AdjoinRoot.root (poly k)) := by
      unfold list
      rfl
    have root_eq: (AdjoinRoot.root (poly k)) = (BinaryTower (k+1)).2.specialElement := by
      let prevBTResult := BinaryTower k
      let _instPrevBTield := prevBTResult.2.instField
      let step := binary_tower_inductive_step k prevBTResult.fst prevBTResult.snd
      have res := Eq.symm step.snd.u_is_root
      exact res
    rw [head_eq, root_eq]

@[simp]
theorem traceMapEvalAtRootsIs1 (k : ℕ) : (∑ i ∈ Finset.range (2^k), (Z k)^(2^i))
  = 1 ∧ (∑ i ∈ Finset.range (2^k), ((Z k)⁻¹)^(2^i)) = 1 := by
  rw [Z_is_special_element]
  exact (BinaryTower k).2.traceMapEvalAtRootsIs1

@[simp]
theorem eval_poly_at_root (k : ℕ) : (Z (k+1))^2 + (Z (k+1)) * Z k + 1 = 0 := by
  let btResult := BinaryTower k
  let _instPrevBTield := btResult.2.instField
  let step := binary_tower_inductive_step k btResult.fst btResult.snd
  let eq := step.snd.eval_defining_poly_at_root
  rw [←Z_is_special_element] at eq
  exact eq

@[simp]
theorem poly_form (k : ℕ) : poly k = X^2 + (C (Z k) * X + 1) := by
  have res := (BinaryTower k).2.newPolyForm
  rw [←poly_eq] at res
  rw [←Z_is_special_element] at res
  exact res

@[simp]
lemma list_length (k : ℕ) : (list k).length = k + 1 := by
  unfold list
  rfl

@[simp]
theorem list_nonempty (k : ℕ) : (list k).1 ≠ [] := by
  by_contra h_empty
  have h_len := list_length k -- h_len : (list k).length = k + 1
  have h_len_zero := List.length_eq_zero_iff.mpr h_empty -- h_len_zero : (↑(list k)).length = 0
  have h_len_eq : (list k).length = List.length ((list k).1) := by
    simp [List.Vector.toList_length (list k)]
  rw [h_len_eq, h_len_zero] at h_len
  have : k + 1 ≠ 0 := Nat.succ_ne_zero k
  contradiction

instance polyIrreducible (n : ℕ) : Irreducible (poly n) := (BinaryTower n).2.instIrreduciblePoly

instance polyIrreducibleFact (n : ℕ) : Fact (Irreducible (poly n)) := ⟨polyIrreducible n⟩

-- TODO: multilinear basis
-- -- Possible direction: definition of BTF as Quotient of MvPolynomial (Fin n) GF(2)
-- -- by the ideal generated by special field elements
-- -- What would this definition give us?

end BinaryTower

end

/- TODO: Concrete implementation of BTF uses BitVec -/

def ConcreteBinaryTower (k : ℕ) :=
  match k with
  | 0 => BitVec 1
  | k + 1 => BitVec (2^k)

-- Define all arithmetic operations
-- Define cross-field operations
-- Define a field isomorphism
