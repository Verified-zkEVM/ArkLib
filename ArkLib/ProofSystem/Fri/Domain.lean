import Mathlib.GroupTheory.Coset.Basic
import Mathlib.GroupTheory.GroupAction.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

import CompPoly.Fields.Basic
import ArkLib.Data.GroupTheory.Smooth
import ArkLib.ToMathlib.Finset.Basic

import Mathlib.Data.FinEnum

variable {F : Type} [NonBinaryField F] [Finite F]
variable (D : Subgroup Fˣ) {n : ℕ} [DIsCyclicC : IsCyclicWithGen D] [DSmooth : SmoothPowerOfTwo n D]

namespace Fri

section

/-
For `[CommMonoid K], (Monoid.toMulAction _ : MulAction Kˣ Kˣ) = Units.mulAction'` is not defeq.
This leads to some typeclass friction that is ameliorated, albeit not resolved, by some automation.

Viz. the discussion here:
https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/class.2Flemmas.20for.20smul.20distributing.20over.20smul
-/

omit [Finite F] in
@[simp, grind _=_]
private lemma op_der_eq : Monoid.toMulAction Fˣ = Units.mulAction' := by ext; rfl

open Lean Elab in
/--
A variation on `rw [op_der_eq] at *`.

Ensures that once `Fˣ` is fixed, we use `Monoid.toMulAction Fˣ`, not `Units.mulAction'`.
-/
private def reconcile (goal : MVarId) : MetaM (Option MVarId) := goal.withContext do
  let mut goal ← go goal
  for const in ←getLCtx do
    if const.isImplementationDetail then continue
    goal ← go goal (mkIdent const.userName)
  pure (.some goal)
  where go (goal : MVarId) (loc : Option Ident := .none) : MetaM MVarId := do
    let tac : MetaM _ :=
      match loc with
      | .none => `(tactic|try rewrite [op_der_eq])
      | .some loc => `(tactic|try rewrite [op_der_eq] at $loc:ident)
    let ([goal'], _) ← runTactic goal (←tac)
      | throwError "Failed to reconcile `Monoid.toMulAction` and `Units.mulAction`."
    return goal'

open Lean Elab Tactic in
/--
Reconciles `Monoid.toMulAction Fˣ = Units.mulAction'` across the goal.
-/
scoped elab "reconcile" : tactic => liftMetaTactic1 reconcile

/--
`reconcile`-aware `aesop` that deals with coset membership.

Can be trivially extended to recognise more than just `mem_leftCoset_iff`.
-/
syntax (name := reconcileStx) "aesop_reconcile" : tactic

set_option hygiene false in
open Lean Elab Tactic PrettyPrinter Delaborator in
@[tactic reconcileStx, inherit_doc reconcileStx]
private def elabReconcileStx : Tactic := fun stx => withMainContext do
  match stx with
  | `(tactic|aesop_reconcile) =>
    evalTactic (←
      `(tactic|(have := fun A A₁ X₁ X₂ X₃ ↦ @mem_leftCoset_iff.{0} A A₁ X₁ X₂ X₃
                reconcile
                specialize this (Units ‹_›) inferInstance
                aesop)))
  | _ => throwError "Unsupported syntax."

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
lemma domain_surjective {i : ℕ} : Function.Surjective (domain D n i) := by
  by_cases h : i ≤ n
  · intros b
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
  · intros b
    simp only [not_le] at h
    have : n - i = 0 := by omega
    use ⟨0, by rw [this]; decide⟩
    unfold domain
    simp
    have h : DIsCyclicC.gen.1 ^ (2 ^ i) = 1 := by
      have h : ∃ j : ℕ, i = n + j := by
        apply Nat.exists_eq_add_of_le
        exact Nat.le_of_succ_le h
      rcases h with ⟨j, h⟩
      rw [h, Nat.pow_add, pow_mul]
      have : DIsCyclicC.gen.1 ^ (2 ^ n) = 1 := by
        apply orderOf_dvd_iff_pow_eq_one.mp
        norm_cast
        rw [DSmooth.smooth]
      rw [this]
      simp
    rcases b with ⟨b, h'⟩
    rw [evalDomain, h, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at h'
    simp [h']

lemma pow_inj {i : ℕ} {a b : Fin (2 ^ (n - i))} :
    i ≤ n → (DIsCyclicC.gen.1 ^ 2 ^ i) ^ a.1 = (DIsCyclicC.gen.1 ^ 2 ^ i) ^ b.1 → a = b := by
  intros h₁ h₂
  rw [pow_inj_mod] at h₂
  have : orderOf (DIsCyclicC.gen.1 ^ 2 ^ i)  = 2 ^ (n - i) := by
    calc orderOf (DIsCyclicC.gen.1 ^ 2 ^ i)
      _ = 2 ^ n / (2 ^ n).gcd (2 ^ i)               := by simp [orderOf_pow, DSmooth.smooth]
      _ = 2 ^ n / (2 ^ (n - i + i)).gcd (2 ^ i)     := by aesop
      _ = 2 ^ n / (2 ^ (n - i) * 2 ^ i).gcd (2 ^ i) := by grind
      _ = 2 ^ n / 2 ^ i                             := by rw [Nat.gcd_mul_left_left _ _]
      _ = 2 ^ (n - i)                               := Nat.pow_div h₁ (by decide)
  grind [Fin.val_inj, Nat.mod_eq_of_lt, cases Fin]

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
@[simp]
lemma D_def : evalDomain D 0 = D := by
  unfold evalDomain
  symm
  ext x
  rw [Subgroup.mem_zpowers_iff]
  simp only [pow_zero, pow_one]
  norm_cast
  refine ⟨fun h ↦ ?p₁, fun h ↦ h.choose_spec ▸ (DIsCyclicC.gen ^ h.choose).2⟩
  have := DIsCyclicC.zpow_surjective ⟨x, h⟩
  grind

/- Proof each on of these groups is cyclic (with a computable generator) -/
instance {i : ℕ} : IsCyclicWithGen (evalDomain D i) :=
  ⟨
    ⟨DIsCyclicC.gen.1 ^ 2 ^ i, by simp⟩,
    by rintro ⟨b, h⟩
       have := Subgroup.exists_mem_zpowers.1 ⟨b, ⟨h, rfl⟩⟩
       aesop
  ⟩

omit [Finite F] in
lemma pow_2_pow_i_mem_Di_of_mem_D :
  ∀ {x : Fˣ} {i : ℕ},
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
  rw [show i + (n - (i + 1)) = n - 1 by omega]
  have : (DIsCyclicC.gen.1 ^ 2 ^ (n - 1)) ^ 2 = 1 := by
    rw [
      ←pow_mul,
      show 2 ^ (n - 1) * 2 = 2 ^ n by grind [Nat.two_pow_pred_mul_two],
      ←DSmooth.smooth
    ]
    norm_cast
    rw [pow_orderOf_eq_one]
  have alg {x : Fˣ} : x^2 = 1 → x = 1 ∨ x = -1 := by
    intros h₁
    have := sq_eq_one_iff (a := (x : F))
    norm_cast at this
    aesop
  specialize alg this
  have gen_ord := DSmooth.smooth
  rw [orderOf_eq_iff (by simp)] at gen_ord
  norm_cast at alg
  have gen_ord :=
    gen_ord.2
      (2 ^ (n - 1))
      (by apply Nat.two_pow_pred_lt_two_pow; linarith)
      (by simp)
  tauto

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

end Domain

namespace CosetDomain

open Pointwise

/- Element of `Fˣ` we will use to define our coset -/
variable (x : Fˣ)

/- Cosets that will form domains of evaluation for the FRI codewords. -/
@[simp]
def evalDomain (i : ℕ) : Set Fˣ :=
  x ^ (2 ^ i) • Domain.evalDomain D i

abbrev evalDomainSigma (s : Fin (n + 1) → ℕ+) (i : ℕ) :=
  evalDomain D x (∑ j' ∈ finRangeTo i, s j')

/- Enumeration of the elements of the `i`th coset. -/
def domain (n : ℕ) (i : ℕ) : Fin (2 ^ (n - i)) → evalDomain D x i :=
  fun j =>
    ⟨
      x ^ 2 ^ i * (DIsCyclicC.gen ^ (2 ^ i)) ^ j.1,
      by aesop_reconcile
    ⟩

omit [Finite F] in
lemma domain_surjective {i : ℕ} : Function.Surjective (domain D x n i) := by
  rintro ⟨b, hb⟩
  unfold evalDomain at hb
  unfold domain
  have h' : (x ^ (2 ^ i))⁻¹ * b ∈ Domain.evalDomain D i := by
    aesop_reconcile
  rcases Domain.domain_surjective (n := n) _ ⟨_, h'⟩ with ⟨a, h''⟩
  use a
  unfold Domain.domain at h''
  simp only [Domain.evalDomain, Subtype.mk.injEq] at h''
  simp only [mul_eq_of_eq_inv_mul h'']

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

noncomputable def domainToFin {i : Fin (n + 1)} : evalDomain D x i → Fin (2 ^ (n - i)) :=
  fun g =>
    have : ∃ ind : Fin (2 ^ (n - i)),
            g.1.1 = x.1 ^ (2 ^ i.1) * ((DIsCyclicC.gen.1 ^ (2 ^ i.1)) ^ ind.1) := by
      have h := g.2
      unfold evalDomain at h
      have h' : (x ^ 2 ^ i.1)⁻¹ * ↑g ∈ ↑(Domain.evalDomain D ↑i) := by aesop_reconcile
      unfold Domain.evalDomain at h'
      rw [Subgroup.mem_zpowers_iff] at h'
      rcases h' with ⟨ind, h'⟩
      have h' :
        ∃ ind : ℕ,
          (DIsCyclicC.gen.1 ^ 2 ^ i.1) ^ ind = (x ^ 2 ^ i.1)⁻¹ * ↑g ∧ ind < 2 ^ (n - i) := by
        exists Int.toNat (ind % (2 ^ (n - i)))
        have k_rel : ∃ m, ind = ind % (2 ^ (n - i)) + m * (2 ^ (n - i)) := by
          exists (ind / (2 ^ (n - i)))
          exact Eq.symm (Int.emod_add_ediv' ind (2 ^ (n - i)))
        rcases k_rel with ⟨m, k_rel⟩
        rw [k_rel] at h'
        have cast_rw {a : Fˣ} {n : ℕ} : a ^ n = a ^ (n : ℤ) := by
          exact rfl
        rw [cast_rw]
        have : 0 ≤ ind % 2 ^ (n - i) := by
          apply Int.emod_nonneg ind
          exact Ne.symm (NeZero.ne' (2 ^ (n - i)))
        simp only [Int.ofNat_toNat, this, sup_of_le_left, evalDomain]
        rw [←h', zpow_add, mul_comm m, zpow_mul]
        norm_cast
        rw
          [
            (pow_mul DIsCyclicC.gen (2 ^ i.1) (2 ^ (n - i.1))).symm,
            ←pow_add, Nat.add_sub_of_le (by omega), ←DSmooth.smooth, pow_orderOf_eq_one
          ]
        simp only [Nat.cast_pow, Nat.cast_ofNat, one_zpow, mul_one, Nat.ofNat_pos, pow_pos,
          Int.toNat_lt', true_and, gt_iff_lt]
        have h' := @Int.emod_lt ind (2 ^ (n - i.1)) (by simp)
        simp only [Int.natAbs_pow, Int.reduceAbs, Nat.cast_pow, Nat.cast_ofNat] at h'
        exact h'
      rcases h' with ⟨ind, h', cond⟩
      exists ⟨ind, cond⟩
      have h' : g.1 = (x ^ 2 ^ i.1) * (DIsCyclicC.gen ^ 2 ^ i.1) ^ ind := by
        apply Eq.symm
        rw [h']
        simp
      rw [h']
      rfl
    Classical.choose this

/- Helper lemmas for constructing operations on/lifting between domains. -/

omit [Finite F] in
@[simp]
lemma D_def : evalDomain D x 0 = x • D := by
  unfold evalDomain
  rw [Domain.D_def]
  simp

lemma pow_2_pow_i_mem_Di_of_mem_D {F : Type} [NonBinaryField F] [Finite F] {D : Subgroup Fˣ}
  [DIsCyclicC : IsCyclicWithGen ↥D] {x : Fˣ} :
  ∀ {a : Fˣ} {i : ℕ},
    a ∈ evalDomain D x 0 → a ^ (2 ^ i) ∈ evalDomain D x i := by
  unfold evalDomain
  intros a i h
  have h : x⁻¹ * a ∈ Domain.evalDomain D 0 := by aesop_reconcile
  simp only [Domain.D_def] at h
  have : (x ^ (2 ^ i))⁻¹ * (a ^ (2 ^ i)) ∈ Domain.evalDomain D i := by
    simpa [mul_pow, inv_pow, mul_assoc, mul_left_comm, mul_comm] using
      (Domain.pow_2_pow_i_mem_Di_of_mem_D D (i := i) h)
  aesop_reconcile

omit [Finite F] in
lemma sqr_mem_D_succ_i_of_mem_D_i : ∀ {a : Fˣ} {i : ℕ},
    a ∈ evalDomain D x i → a ^ 2 ∈ evalDomain D x (i + 1) := by
  unfold evalDomain
  intros a i h
  have h : (x ^ 2 ^ i)⁻¹ * a ∈ Domain.evalDomain D i := by aesop_reconcile
  have : ((x ^ 2 ^ i)⁻¹ * a) ^ 2 = (x ^ 2 ^ (i + 1))⁻¹ * (a ^ 2) := by
    have : ((x ^ 2 ^ i)⁻¹ * a) ^ 2 = ((x ^ 2 ^ i) ^ 2)⁻¹ * (a ^ 2) := by
      simp [mul_pow, inv_pow]
    rw [this]
    have : (x ^ 2 ^ i) ^ 2 = x ^ 2 ^ (i + 1) := by
      rw [pow_two, ←pow_add]
      congr 1
      grind
    rw [this]
  have h := Domain.sqr_mem_D_succ_i_of_mem_D_i D h
  aesop_reconcile

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
    aesop_reconcile
  have : (x ^ 2 ^ i)⁻¹ * -a ∈ ↑(Domain.evalDomain D i) := by
    have : (x ^ 2 ^ i)⁻¹ * -a = ((x ^ 2 ^ i)⁻¹ * a) * (- 1) := by
      simp [mul_neg]
    rw [this]
    exact
      (
        Subgroup.mul_mem_cancel_right
          _
          (Domain.minus_one_in_doms D i_prop)
      ).mpr mem
  aesop_reconcile

omit [Finite F] in
lemma mul_root_of_unity {x : Fˣ} :
  ∀ {a b : Fˣ} {i j : ℕ},
    i ≤ j → a ∈ evalDomain D x i → b ∈ Domain.evalDomain D j →
      a * b ∈ evalDomain D x i := by
  intros a b i j i_le_j a_in b_in
  unfold evalDomain Domain.evalDomain at *
  have : (x ^ 2 ^ i)⁻¹ * a ∈ (Subgroup.zpowers (DIsCyclicC.gen.1 ^ 2 ^ i)) := by
    aesop_reconcile
  have : (x ^ 2 ^ i)⁻¹ * (a * b) ∈ (Subgroup.zpowers (DIsCyclicC.gen.1 ^ 2 ^ i)) := by
    rw [Subgroup.mem_zpowers_iff] at b_in this
    rcases this with ⟨ka, a_in⟩
    rcases b_in with ⟨kb, b_in⟩
    apply Subgroup.mem_zpowers_iff.mpr
    exists (ka + (2 ^ (j - i)) * kb)
    rw [
      ←@mul_assoc _ _ _ a b, ←a_in, ←b_in, zpow_add,
      (pow_mul_pow_sub 2 i_le_j).symm, pow_mul, zpow_mul
    ]
    norm_cast
  aesop_reconcile

omit [Finite F] in
lemma dom_n_eq_triv : evalDomain D x n = {x ^ (2 ^ n)} := by
  unfold evalDomain
  rw [Domain.dom_n_eq_triv]
  simp

noncomputable local instance : Fintype F := Fintype.ofFinite _

noncomputable instance : Nonempty ↑(CosetDomain.evalDomain D x 0) :=
  ⟨x, by aesop_reconcile⟩

noncomputable instance : Fintype ↑(CosetDomain.evalDomain D x 0) := inferInstance

instance domain_neg_inst {F : Type} [NonBinaryField F] [Finite F] {D : Subgroup Fˣ} {n : ℕ}
    [DIsCyclicC : IsCyclicWithGen ↥D] [DSmooth : SmoothPowerOfTwo n ↥D]
    {x : Fˣ} (i : Fin n) : Neg (evalDomain D x i) where
  neg := fun a => ⟨_, neg_mem_dom_of_mem_dom D x i a.2⟩

instance {i : Fin (n + 1)} : Fintype (evalDomain D x i) where
  elems := Finset.univ.map (domainEnum D x (i := i))
  complete := by
    intros y
    apply Finset.mem_map.mpr
    simp only [domainEnum]
    rcases @domain_surjective (n := n) _ _ D _ _ _ _ y with ⟨a, h⟩
    use a
    rw [←h]
    simp

end CosetDomain

end

end Fri
