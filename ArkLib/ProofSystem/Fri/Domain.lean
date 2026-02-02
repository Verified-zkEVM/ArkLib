import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic

import ArkLib.Data.FieldTheory.NonBinaryField.Basic
import ArkLib.Data.GroupTheory.Smooth

variable {F : Type} [NonBinaryField F] [Finite F]
variable (D : Subgroup Fˣ) {n : ℕ} [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D]

namespace Fri

namespace Domain

/-- Constructs the subgroups of `Fˣ` which we will use to construct
    the domains over which the code words sent by the prover to the
    verifier in the FRI protocol are defined. These cyclic subgroups of
    `Fˣ` are constructed based on `DIsCyclicC.gen : Fˣ` which is of order
    `2 ^ n`, which we know from the `DSmooth` instance.
-/
@[simp]
def evalDomain (i : ℕ) : Subgroup Fˣ :=
  Subgroup.zpowers (DIsCyclicC.gen ^ (2 ^ i))

/-- Allows us to enumerate the elements of the subgroup defined above. -/
def domain (n : ℕ) (i : ℕ) : Fin (2 ^ (n - i)) → evalDomain D i :=
  fun j => ⟨(DIsCyclicC.gen ^ (2 ^ i)) ^ j.1, by simp⟩

omit [Finite F] in
lemma domain_surjective (i : ℕ) : i ≤ n → Function.Surjective (domain D n i) := by
  intros h
  unfold Function.Surjective
  intros b
  have := b.2
  simp only [evalDomain] at this
  have : ∃ j, b.1 = (DIsCyclicC.gen ^ (2 ^ i)) ^ j ∧ j < 2 ^ (n - i) := by
    rw [Subgroup.mem_zpowers_iff] at this
    rcases this with ⟨k, b_def⟩
    have : ∃ k : ℕ, (DIsCyclicC.gen ^ 2 ^ i) ^ k = b.1 := by
      exists Int.toNat (k % (2 ^ (n - i)))
      have k_rel : ∃ m, k = k % (2 ^ (n - i)) + m * (2 ^ (n - i)) := by
        exists (k / (2 ^ (n - i)))
        exact Eq.symm (Int.emod_add_ediv' k (2 ^ (n - i)))
      rcases k_rel with ⟨m, k_rel⟩
      rw [k_rel] at b_def
      have cast_rw {a : Fˣ} {n : ℕ} : a ^ n = a ^ (n : ℤ) := by
        exact rfl
      rw [cast_rw]
      have : 0 ≤ k % 2 ^ (n - i) := by
        apply Int.emod_nonneg k
        exact Ne.symm (NeZero.ne' (2 ^ (n - i)))
      simp only [Int.ofNat_toNat, this, sup_of_le_left, evalDomain]
      rw [←b_def, zpow_add, mul_comm m, zpow_mul]
      norm_cast
      rw
        [
          (pow_mul DIsCyclicC.gen (2 ^ i) (2 ^ (n - i))).symm,
          ←pow_add, Nat.add_sub_of_le h, ←DSmooth.smooth, pow_orderOf_eq_one
        ]
      simp
    rcases this with ⟨k, b_def⟩
    exists (k % (2 ^ (n - i)))
    apply And.intro
    · rw [←b_def]
      have k_rel : ∃ m, k = k % (2 ^ (n - i)) + m * (2 ^ (n - i)) := by
        exists (k / (2 ^ (n - i)))
        exact Eq.symm (Nat.mod_add_div' k (2 ^ (n - i)))
      rcases k_rel with ⟨m, k_rel⟩
      rw (occs := .pos [1]) [k_rel]
      rw [pow_add, mul_comm m, pow_mul]
      norm_cast
      rw
        [
          (pow_mul DIsCyclicC.gen (2 ^ i) (2 ^ (n - i))).symm,
          ←pow_add, Nat.add_sub_of_le h, ←DSmooth.smooth, pow_orderOf_eq_one
        ]
      simp
    · apply Nat.mod_lt _
      exact Nat.two_pow_pos _
  rcases this with ⟨j, h⟩
  exists ⟨j, h.2⟩
  unfold domain
  rcases b with ⟨b, hb⟩
  simp only at h
  simp [h]

lemma pow_inj {i : ℕ} {a b : Fin (2 ^ (n - i))} :
    i ≤ n → (DIsCyclicC.gen.1 ^ 2 ^ i) ^ a.1 = (DIsCyclicC.gen.1 ^ 2 ^ i) ^ b.1 → a = b := by
  intros h h'
  have ha := a.2
  have hb := b.2
  by_contra a_neq_b
  rcases Fin.lt_or_lt_of_ne a_neq_b with a_le_b | a_gt_b
  · have h' := h'.symm
    rw [←mul_inv_eq_one] at h'
    have cast_eq {a : Fˣ} (n : ℕ) : a ^ n = a ^ (Int.ofNat n) := by
      exact rfl
    rw [cast_eq a.1, cast_eq b.1, ←zpow_neg, ←zpow_add] at h'
    have h₁ : 0 < (Int.ofNat b.1 + -Int.ofNat a.1) := by
      apply Int.lt_add_of_neg_add_lt
      rw [add_zero]
      simp only [Int.ofNat_eq_coe, neg_lt_neg_iff, Nat.cast_lt, Fin.val_fin_lt]
      exact a_le_b
    have h₂ : (Int.ofNat b.1 + -Int.ofNat a.1) < 2 ^ (n - i) := by
      simp only [Int.ofNat_eq_coe, add_neg_lt_iff_lt_add]
      apply lt_add_of_lt_of_nonneg
      · norm_cast
      · simp
    have : Int.ofNat b.1 + -Int.ofNat a.1 = Int.ofNat (b.1 - a.1) := by
      simp
      have : Int.ofNat b.1 + - Int.ofNat a.1 = Int.ofNat b.1 - Int.ofNat a.1 := by
        ring
      rw [Int.ofNat_eq_coe, Int.ofNat_eq_coe] at this
      rw [this, Int.sub_eq_iff_eq_add']
      norm_cast
      refine Eq.symm (Nat.add_sub_of_le ?_)
      exact Nat.le_of_succ_le a_le_b
    rw [this] at h' h₁ h₂
    rw [Int.ofNat_eq_coe, zpow_natCast] at h'
    have h' := orderOf_dvd_of_pow_eq_one h'
    have : orderOf (DIsCyclicC.gen.1 ^ 2 ^ i)  = 2 ^ (n - i) := by
      rw [orderOf_pow]
      norm_cast
      rw [DSmooth.smooth]
      have : n = (n - i) + i := by
        exact (Nat.sub_eq_iff_eq_add h).mp rfl
      rw (occs := .pos [2]) [this]
      rw [pow_add, Nat.gcd_mul_left_left]
      exact Nat.pow_div h (by decide)
    rw [this] at h'
    have : 2 ^ (n - i) ≤ b.1 - a.1 := by
      rcases h' with ⟨m, h'⟩
      rw [Int.ofNat_eq_coe, Int.natCast_pos] at h₁
      have : m > 0 := by
        by_contra h
        simp at h
        rw [h, mul_zero] at h'
        rw [h', lt_self_iff_false] at h₁
        exact h₁
      nlinarith
    have :  b.1 - a.1 < 2 ^ (n - i) := by
      exact Nat.sub_lt_of_lt hb
    linarith
  · rw [←mul_inv_eq_one] at h'
    have cast_eq {a : Fˣ} (n : ℕ) : a ^ n = a ^ (Int.ofNat n) := by
      exact rfl
    rw [cast_eq a.1, cast_eq b.1, ←zpow_neg, ←zpow_add] at h'
    have h₁ : 0 < (Int.ofNat a.1 + -Int.ofNat b.1) := by
      apply Int.lt_add_of_neg_add_lt
      rw [add_zero]
      simp only [Int.ofNat_eq_coe, neg_lt_neg_iff, Nat.cast_lt, Fin.val_fin_lt]
      exact a_gt_b
    have h₂ : (Int.ofNat a.1 + -Int.ofNat b.1) < 2 ^ (n - i) := by
      simp only [Int.ofNat_eq_coe, add_neg_lt_iff_lt_add]
      apply lt_add_of_lt_of_nonneg
      · norm_cast
      · simp
    have : Int.ofNat a.1 + -Int.ofNat b.1 = Int.ofNat (a.1 - b.1) := by
      simp
      have : Int.ofNat a.1 + - Int.ofNat b.1 = Int.ofNat a.1 - Int.ofNat b.1 := by
        ring
      rw [Int.ofNat_eq_coe, Int.ofNat_eq_coe] at this
      rw [this, Int.sub_eq_iff_eq_add']
      norm_cast
      refine Eq.symm (Nat.add_sub_of_le ?_)
      exact Nat.le_of_succ_le a_gt_b
    rw [this] at h' h₁ h₂
    rw [Int.ofNat_eq_coe, zpow_natCast] at h'
    have h' := orderOf_dvd_of_pow_eq_one h'
    have : orderOf (DIsCyclicC.gen.1 ^ 2 ^ i)  = 2 ^ (n - i) := by
      rw [orderOf_pow]
      norm_cast
      rw [DSmooth.smooth]
      have : n = (n - i) + i := by
        exact (Nat.sub_eq_iff_eq_add h).mp rfl
      rw (occs := .pos [2]) [this]
      rw [pow_add, Nat.gcd_mul_left_left]
      exact Nat.pow_div h (by decide)
    rw [this] at h'
    have : 2 ^ (n - i) ≤ a.1 - b.1 := by
      rcases h' with ⟨m, h'⟩
      rw [Int.ofNat_eq_coe, Int.natCast_pos] at h₁
      have : m > 0 := by
        by_contra h
        simp at h
        rw [h, mul_zero] at h'
        rw [h', lt_self_iff_false] at h₁
        exact h₁
      nlinarith
    have :  a.1 - b.1 < 2 ^ (n - i) := by
      exact Nat.sub_lt_of_lt ha
    linarith

lemma domain_injective (i : ℕ) : i ≤ n → Function.Injective (domain D n i) := by
  intros h a b h'
  unfold domain at h'
  simp at h'
  exact pow_inj D h h'

/-- This embedding will be used to construct the appropriate Reed-Solomon code against
    which we test codewords for proximity. -/
def domainEnum (i : Fin (n + 1)) : Fin (2 ^ (n - i)) ↪ evalDomain D i :=
  ⟨domain D n i.1, domain_injective D i.1 (by have := i.2; linarith)⟩

/- Embedding of elements of these subgroups into the field `F`. -/
def domainEmb {i : ℕ} : evalDomain D i ↪ F :=
  ⟨
    fun x => x.1.1,
    by
      intros a b
      simp only
      intros h
      norm_cast at h
  ⟩

/- Proof the first subgroup is `D`, the cyclic group generated by `DIsCyclicC.gen : Fˣ` -/
omit [Finite F] in
lemma D_def : D = evalDomain D 0 := by
  unfold evalDomain
  simp only [pow_zero, pow_one]
  have := DIsCyclicC.zpow_surjective
  unfold Function.Surjective at this
  ext x
  apply Iff.intro
  · intros h
    rcases this ⟨x, h⟩ with ⟨a, h⟩
    simp only at h
    refine Subgroup.mem_zpowers_iff.mpr ?_
    exists a
    have : x = (DIsCyclicC.gen ^ a) := by
      norm_cast
      rw [h]
    rw [this]
  · intros h
    rw [Subgroup.mem_zpowers_iff] at h
    rcases h with ⟨k, h⟩
    norm_cast at h
    rw [←h]
    exact (DIsCyclicC.gen ^ k).2

/- Proof each on of these groups is cyclic (with a computable generator) -/
instance {i : ℕ} : IsCyclicWithGen (evalDomain D i) := by
  unfold evalDomain
  constructor
  swap
  · refine ⟨DIsCyclicC.gen.1 ^ 2 ^ i, ?_⟩
    simp
  · unfold Function.Surjective
    rintro ⟨b, h⟩
    have : ∃ n : ℤ, b = (DIsCyclicC.gen.1 ^ 2 ^ i) ^ n := by
      refine Subgroup.exists_mem_zpowers.mp ?_
      exists b
    rcases this with ⟨a, h'⟩
    exists a
    simp only [h']
    rfl

omit [Finite F] in
lemma pow_2_pow_i_mem_Di_of_mem_D :
  ∀ {x : Fˣ} (i : ℕ),
    x ∈ D → x ^ (2 ^ i) ∈ evalDomain D i := by
  intros x i h
  simp only [evalDomain]
  have := DIsCyclicC.2
  unfold Function.Surjective at this
  rcases this ⟨x, h⟩ with ⟨a, h⟩
  simp only at h
  have : x = DIsCyclicC.gen ^ a := by
    norm_cast
    rw [h]
  rw [this]
  refine Subgroup.mem_zpowers_iff.mpr ?_
  exists a
  rw [←zpow_natCast, ←zpow_natCast, zpow_comm]

omit [Finite F] in
lemma sqr_mem_D_succ_i_of_mem_D_i : ∀ {x : Fˣ} {i : ℕ},
  x ∈ evalDomain D i → x ^ 2 ∈ evalDomain D (i + 1) := by
  intros x i h
  simp only [evalDomain] at h
  simp only [evalDomain]
  rw [Subgroup.mem_zpowers_iff] at h ⊢
  rcases h with ⟨k, h⟩
  exists k
  rw [←h]
  have {x : Fˣ} {n : ℕ} : x ^ n = x ^ (n : ℤ) := by rfl
  rw [this, this, this, ←zpow_mul, ←zpow_mul, ←zpow_mul]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [@mul_comm ℤ _ k 2, ←mul_assoc]
  rfl

omit [Finite F] in
private lemma gen_def {i : ℕ} :
    (IsCyclicWithGen.gen : evalDomain D i) =
      ⟨
        DIsCyclicC.gen ^ (2 ^ i),
        by
          apply pow_2_pow_i_mem_Di_of_mem_D
          exact DIsCyclicC.gen.2
      ⟩ := by
  rfl

/- Proof that the `i`th subgroup has order `2 ^ (n - i)` -/
instance {i : ℕ} : SmoothPowerOfTwo (n - i) (evalDomain D i) where
  smooth := by
    simp
    rw [gen_def]
    by_cases h : i ≤ n
    · have : (2 ^ n).gcd (2 ^ i) = 2 ^ i := by
        refine Eq.symm (Nat.gcd_greatest ?_ ?_ fun e a a ↦ a)
        · exact (Nat.pow_dvd_pow_iff_le_right (by decide)).mpr h
        · exact dvd_refl _
      rw [Subgroup.orderOf_mk, orderOf_pow', orderOf_submonoid, DSmooth.smooth, this]
      · exact Nat.pow_div h (by decide)
      · aesop
    · rw [not_le] at h
      have : ∃ k : ℕ, i = n + k := Nat.exists_eq_add_of_le (by linarith)
      rcases this with ⟨k, h'⟩
      have : n - i = 0 := by
        refine Nat.sub_eq_zero_of_le (by linarith)
      rw
        [
          this, h', pow_zero, Subgroup.orderOf_mk, orderOf_eq_one_iff,
           Nat.pow_add 2 n k, pow_mul, ←DSmooth.smooth
        ]
      norm_cast
      rw [pow_orderOf_eq_one]
      exact one_pow _

/- Proof each of the subgroups contains the identity element `1 : Fˣ` -/
omit [Finite F] in
lemma one_in_doms (i : ℕ) : 1 ∈ evalDomain D i := by
  simp only [evalDomain]
  apply OneMemClass.one_mem

/- Proof that the `i`th subgroup, for `i < n` contains `-1 ∈ Fˣ` -/
omit [Finite F] in
lemma minus_one_in_doms {i : ℕ} (h : i < n) :
    -1 ∈ evalDomain D i := by
  unfold evalDomain
  rw [Subgroup.mem_zpowers_iff]
  exists ((2 ^ (n - (i + 1))))
  norm_cast
  rw [←pow_mul, ←pow_add]
  have : (i + (n - (i + 1))) = n - 1 := by
    refine Eq.symm ((fun {b a c} h ↦ (Nat.sub_eq_iff_eq_add' h).mp) (Nat.le_sub_one_of_lt h) ?_)
    exact Eq.symm (Nat.Simproc.sub_add_eq_comm n i 1)
  rw [this]
  have : ((DIsCyclicC.gen.1 ^ 2 ^ (n - 1)) ^ 2) = 1 := by
    rw [←pow_mul]
    have : 2 ^ (n - 1) * 2 = 2 ^ n := by
      apply Nat.two_pow_pred_mul_two
      linarith
    rw [this, ←DSmooth.smooth]
    norm_cast
    rw [pow_orderOf_eq_one]
  have alg {x : Fˣ} : x^2 = 1 → x = 1 ∨ x = -1 := by
    intros h
    refine (Units.inv_eq_self_iff x).mp ?_
    have {a b : Fˣ} (c : Fˣ) : c * a = c * b → a = b := by
      intros h
      have : c⁻¹ * (c * a) = c⁻¹ * (c * a) := by rfl
      rw (occs := .pos [2]) [h] at this
      rw [←mul_assoc, ←mul_assoc, inv_mul_cancel, one_mul, one_mul] at this
      exact this
    apply this x
    simp only [mul_inv_cancel, h.symm, pow_two]
  have cast : (DIsCyclicC.gen ^ 2 ^ (n - 1)).1 = (DIsCyclicC.gen.1 ^ 2 ^ (n - 1)) := by rfl
  rw [cast]
  specialize alg this
  rcases alg with alg | alg
  · have gen_ord := DSmooth.smooth
    rw [orderOf_eq_iff (by simp)] at gen_ord
    have gen_ord :=
      gen_ord.2
        (2 ^ (n - 1))
        (by apply Nat.two_pow_pred_lt_two_pow; linarith)
        (by simp)
    exfalso
    apply gen_ord
    norm_cast at alg
  · assumption

omit [Finite F] in
lemma dom_n_eq_triv : evalDomain D n = ⊥ := by
  unfold evalDomain
  rw [Subgroup.zpowers_eq_bot, ←DSmooth.smooth]
  norm_cast
  exact pow_orderOf_eq_one IsCyclicWithGen.gen

instance {i : Fin (n + 1)} : OfNat (evalDomain D i) 1 where
  ofNat := ⟨1, one_in_doms D i⟩

/- Neg instance for the subgroups, as a consequence of `minus_one_in_doms` -/
instance domain_neg_inst {i : Fin n} : Neg (evalDomain D i.1) where
  neg := fun x => ⟨_, minus_one_in_doms D i.2⟩ * x

/- Enumerates the `2^s` roots of unity of `Fˣ`, which corresponds to the
   elemens of the `(n - s)`th subgroup (for `s ≤ n`). -/
def rootsOfUnity (n s : ℕ) : List (Domain.evalDomain D (n - s)) :=
  List.map
    (fun i =>
      ⟨
        (DIsCyclicC.gen.1 ^ (2 ^ (n - s))) ^ i,
        by
          unfold evalDomain
          apply Subgroup.mem_zpowers_iff.mpr
          exists i
      ⟩
    )
    (List.range (2 ^ s))

end Domain

namespace CosetDomain

open Pointwise

omit [Finite F] in
private lemma op_der_eq : Monoid.toMulAction Fˣ = Units.mulAction' := by
  unfold Units.mulAction' Monoid.toMulAction
  congr
  ext g m
  simp only [Units.val_mul]
  unfold_projs
  rfl

/- Element of `Fˣ` we will use to define our coset -/
variable (x : Fˣ)

/- Cosets that will form domains of evaluation for the FRI codewords. -/
@[simp]
def evalDomain (i : ℕ) : Set Fˣ :=
  (x ^ (2 ^ i)) • (Domain.evalDomain D i)

/- Enumeration of the elements of the `i`th coset. -/
def domain (n : ℕ) (i : ℕ) : Fin (2 ^ (n - i)) → evalDomain D x i :=
  fun j =>
    ⟨
      x ^ 2 ^ i * (DIsCyclicC.gen ^ (2 ^ i)) ^ j.1,
      by
        simp
        rw [←Domain.evalDomain]
        have h :
            (x ^ 2 ^ i)⁻¹ * (x ^ 2 ^ i * (DIsCyclicC.gen.1 ^ 2 ^ i) ^ j.1) ∈
              Domain.evalDomain D i := by
          rw [←mul_assoc]
          simp
        convert (mem_leftCoset_iff _).mpr h
        expose_names
        exact (@op_der_eq F inst).symm
    ⟩

lemma domain_injective {i : ℕ} : i ≤ n → Function.Injective (domain D x n i) := by
  intros h
  intros a b
  unfold domain
  intros h'
  simp only [evalDomain, Domain.evalDomain, Subtype.mk.injEq, mul_right_inj] at h'
  exact Domain.pow_inj D h h'

/- Used to construct Reed-Solomon codes with respect to which we are testing proximity. -/
def domainEnum (i : Fin (n + 1)) : Fin (2 ^ (n - i)) ↪ evalDomain D x i :=
  ⟨domain D x n i, domain_injective (i := i.1) D x (by have := i.2; linarith)⟩

def domainEmb {i : ℕ} : evalDomain D x i ↪ F :=
  ⟨
    fun x => x.1.1,
    by
      intros a b
      simp only
      intros h
      norm_cast at h
      rcases a with ⟨a, ha⟩
      rcases b with ⟨b, hb⟩
      simp at h
      simp only [h]
  ⟩

/- Helper lemmas for constructing operations on/lifting between domains. -/

omit [Finite F] in
lemma D_def : evalDomain D x 0 = x • D := by simp [Domain.D_def D]

lemma pow_2_pow_i_mem_Di_of_mem_D {F : Type} [NonBinaryField F] [Finite F] {D : Subgroup Fˣ}
  [DIsCyclicC : IsCyclicWithGen ↥D] {x : Fˣ} :
  ∀ {a : Fˣ} (i : ℕ),
    a ∈ evalDomain D x 0 → a ^ (2 ^ i) ∈ evalDomain D x i := by
  unfold evalDomain
  intros a i h
  have h : x⁻¹ * a ∈ Domain.evalDomain D 0 := by
    simp only [pow_zero, pow_one] at h
    apply (mem_leftCoset_iff _).mp
    convert h
    exact op_der_eq
  rw [←Domain.D_def] at h
  have h := Domain.pow_2_pow_i_mem_Di_of_mem_D D i h
  have : (x⁻¹ * a) ^ 2 ^ i = (x ^ (2 ^ i))⁻¹ * (a ^ (2 ^ i)) := by sorry --field_simp
  rw [this] at h
  convert (mem_leftCoset_iff _).mpr h
  exact op_der_eq.symm

omit [Finite F] in
lemma sqr_mem_D_succ_i_of_mem_D_i : ∀ {a : Fˣ} {i : ℕ},
    a ∈ evalDomain D x i → a ^ 2 ∈ evalDomain D x (i + 1) := by
  unfold evalDomain
  intros a i h
  have h : (x ^ 2 ^ i)⁻¹ * a ∈ Domain.evalDomain D i := by
    apply (mem_leftCoset_iff _).mp
    convert h
    exact op_der_eq
  have h := Domain.sqr_mem_D_succ_i_of_mem_D_i D h
  have : ((x ^ 2 ^ i)⁻¹ * a) ^ 2 = (x ^ 2 ^ (i + 1))⁻¹ * (a ^ 2) := by
    have : ((x ^ 2 ^ i)⁻¹ * a) ^ 2 = ((x ^ 2 ^ i) ^ 2)⁻¹ * (a ^ 2) := by sorry --field_simp
    rw [this]
    have : (x ^ 2 ^ i) ^ 2 = x ^ 2 ^ (i + 1) := by
      rw [pow_two, ←pow_add]
      congr 1
      grind
    rw [this]
  rw [this] at h
  convert (mem_leftCoset_iff _).mpr h
  exact op_der_eq.symm

omit [Finite F] in
lemma pow_lift : ∀ {a : Fˣ} {i : ℕ} (s : ℕ),
    a ∈ evalDomain D x i → a ^ (2 ^ s) ∈ evalDomain D x (i + s) := by
  intros a i s
  induction s with
  | zero => simp
  | succ s ih =>
    intros h
    specialize ih h
    have : a ^ (2 ^ (s + 1)) = (a ^ (2 ^ s)) ^ 2 := by
      rw [←pow_mul]; ring_nf
    rw [←add_assoc, this]
    exact sqr_mem_D_succ_i_of_mem_D_i _ _ ih

omit [Finite F] in
lemma neg_mem_dom_of_mem_dom : ∀ {a : Fˣ} (i : Fin n),
    a ∈ evalDomain D x i → - a ∈ evalDomain D x i := by
  unfold evalDomain
  rintro a ⟨i, i_prop⟩ h
  have mem : (x ^ 2 ^ i)⁻¹ * a ∈ Domain.evalDomain D i := by
    apply (mem_leftCoset_iff _).mp
    convert h
    exact op_der_eq

  have : (x ^ 2 ^ i)⁻¹ * -a ∈ ↑(Domain.evalDomain D i) := by
    have : (x ^ 2 ^ i)⁻¹ * -a = ((x ^ 2 ^ i)⁻¹ * a) * (- 1) := by sorry --field_simp
    rw [this]
    exact
      (
        Subgroup.mul_mem_cancel_right
          (Domain.evalDomain D i)
          (Domain.minus_one_in_doms D i_prop)
      ).mpr mem
  convert (mem_leftCoset_iff _).mpr this
  exact op_der_eq.symm

omit [Finite F] in
lemma mul_root_of_unity {x : Fˣ} :
  ∀ {a b : Fˣ} {i j : ℕ},
    i ≤ j → a ∈ evalDomain D x i → b ∈ Domain.evalDomain D j →
      a * b ∈ evalDomain D x i := by
  intros a b i j i_le_j a_in b_in
  unfold evalDomain Domain.evalDomain at *
  have : (x ^ 2 ^ i)⁻¹ * a ∈ (Subgroup.zpowers (DIsCyclicC.gen.1 ^ 2 ^ i)) := by
    apply (mem_leftCoset_iff _).mp
    convert a_in
    exact op_der_eq
  have : (x ^ 2 ^ i)⁻¹ * (a * b) ∈ (Subgroup.zpowers (DIsCyclicC.gen.1 ^ 2 ^ i)) := by
    rw [Subgroup.mem_zpowers_iff] at b_in this
    rcases this with ⟨ka, a_in⟩
    rcases b_in with ⟨kb, b_in⟩
    apply Subgroup.mem_zpowers_iff.mpr
    exists (ka + (2 ^ (j - i)) * kb)
    rw [
      ←@mul_assoc Fˣ _ _ a b, ←a_in, ←b_in, zpow_add,
      Eq.symm (pow_mul_pow_sub 2 i_le_j), pow_mul, zpow_mul
    ]
    norm_cast
  have := (mem_leftCoset_iff (x ^ 2 ^ i)).mpr this
  convert this
  exact op_der_eq.symm

omit [Finite F] in
lemma dom_n_eq_triv : evalDomain D x n = {x ^ (2 ^ n)} := by
  unfold evalDomain
  rw [Domain.dom_n_eq_triv]
  simp

instance domain_neg_inst {F : Type} [NonBinaryField F] [Finite F] {D : Subgroup Fˣ} {n : ℕ}
    [DIsCyclicC : IsCyclicWithGen ↥D] [DSmooth : SmoothPowerOfTwo n ↥D]
    {x : Fˣ} (i : Fin n) : Neg (evalDomain D x i) where
  neg := fun a => ⟨_, neg_mem_dom_of_mem_dom D x i a.2⟩

end CosetDomain

end Fri
