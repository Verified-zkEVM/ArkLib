/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.MvPolynomial.SupportWeight
public import ArkLib.Data.MvPolynomial.WeightedDegree

/-!
# Support weights with an additive allowance

Taylor substitution preserves the difference between coefficient index and Taylor order.
The allowance below records the source jet index. Allowances add under multiplication,
so substitution charges a monomial exactly its weighted source degree.
-/

@[expose] public section

namespace MvPolynomial

noncomputable section

variable {R σ τ : Type*} [CommSemiring R]

/-- Every monomial has first weight at most its second weight plus `d`. -/
def SupportWeightOffset (a b : (σ →₀ ℕ) →+ ℕ) (d : ℕ)
    (p : MvPolynomial σ R) : Prop := ∀ m ∈ p.support, a m ≤ b m + d

namespace SupportWeightOffset

variable {a b : (σ →₀ ℕ) →+ ℕ} {d e : ℕ} {p q : MvPolynomial σ R}

theorem mono (hp : SupportWeightOffset a b d p) (h : d ≤ e) :
    SupportWeightOffset a b e p := fun m hm ↦ (hp m hm).trans (Nat.add_le_add_left h _)

theorem monomial (m : σ →₀ ℕ) (r : R) (h : a m ≤ b m + d) :
    SupportWeightOffset a b d (MvPolynomial.monomial m r) := by
  intro n hn
  have : n = m := by simpa using support_monomial_subset hn
  simpa [this] using h

theorem C (r : R) : SupportWeightOffset a b d (MvPolynomial.C r) :=
  monomial 0 r (by simp)

theorem add (hp : SupportWeightOffset a b d p) (hq : SupportWeightOffset a b d q) :
    SupportWeightOffset a b d (p + q) := by
  classical
  intro m hm
  rcases Finset.mem_union.mp (support_add hm) with hm | hm
  · exact hp m hm
  · exact hq m hm

theorem mul (hp : SupportWeightOffset a b d p) (hq : SupportWeightOffset a b e q) :
    SupportWeightOffset a b (d + e) (p * q) := by
  classical
  intro m hm
  obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp (support_mul p q hm)
  simpa only [map_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    Nat.add_le_add (hp u hu) (hq v hv)

theorem pow (hp : SupportWeightOffset a b d p) (n : ℕ) :
    SupportWeightOffset a b (n * d) (p ^ n) := by
  induction n with
  | zero => simpa using (C (a := a) (b := b) (d := 0) (1 : R))
  | succ n ih => simpa [pow_succ, Nat.succ_mul] using ih.mul hp

theorem sum {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ R)
    (hp : ∀ i ∈ s, SupportWeightOffset a b d (p i)) :
    SupportWeightOffset a b d (∑ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [SupportWeightOffset]
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact (hp i (Finset.mem_insert_self _ _)).add
      (ih fun j hj ↦ hp j (Finset.mem_insert_of_mem hj))

theorem prod {ι : Type*} (s : Finset ι) (p : ι → MvPolynomial σ R) (d : ι → ℕ)
    (hp : ∀ i ∈ s, SupportWeightOffset a b (d i) (p i)) :
    SupportWeightOffset a b (∑ i ∈ s, d i) (∏ i ∈ s, p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (C (a := a) (b := b) (d := 0) (1 : R))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    exact (hp i (Finset.mem_insert_self _ _)).mul
      (ih fun j hj ↦ hp j (Finset.mem_insert_of_mem hj))

end SupportWeightOffset

/-- Substitution adds the allowances of the variables with their monomial multiplicities. -/
theorem supportWeightOffset_aeval
    (a b : (τ →₀ ℕ) →+ ℕ) (w : σ → ℕ) (v : σ → MvPolynomial τ R)
    (hv : ∀ i, SupportWeightOffset a b (w i) (v i)) (p : MvPolynomial σ R) :
    SupportWeightOffset a b (p.weightedTotalDegree w) (aeval v p) := by
  classical
  conv_rhs => rw [p.as_sum, map_sum]
  apply SupportWeightOffset.sum
  intro m hm
  rw [aeval_monomial]
  have hp := SupportWeightOffset.prod (a := a) (b := b) m.support
    (fun i ↦ v i ^ m i) (fun i ↦ m i * w i) (fun i _ ↦ (hv i).pow (m i))
  have hmul := (SupportWeightOffset.C (a := a) (b := b) (d := 0) (coeff m p)).mul hp
  simp only [zero_add] at hmul
  apply hmul.mono
  simpa [Finsupp.weight_apply, Finsupp.sum, smul_eq_mul] using
    (le_weightedTotalDegree w hm)

end

end MvPolynomial
