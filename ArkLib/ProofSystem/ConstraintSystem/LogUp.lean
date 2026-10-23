/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.ProofSystem.ConstraintSystem.Lookup
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Lookups by logarithmic derivatives

LogUp checks a lookup with one identity of rational functions.

The definitions follow Haböck, eprint 2022/1530.

That paper is "Multivariate lookups based on logarithmic derivatives".

## Results

- A sum of m / (X - v) vanishes in F(X) exactly when every key has net multiplicity zero.
- Set inclusion (Lemma 5): the lookup relation holds exactly when, for some m,
  sum_j 1 / (X - f_j) = sum_i m_i / (X - t_i).
- Permutations (Lemma 3): two lists are permutations exactly when their sums of 1 / (X - x) agree.
- Both need a characteristic above the number of queries: p equal queries cancel.
-/

@[expose] public section

namespace Lookup.LogUp

open Polynomial Finset

set_option linter.unusedSectionVars false

/-- The net multiplicity of a key: the sum of the multiplicities of its messages. -/
def netMult {κ R : Type*} [DecidableEq κ] [AddCommMonoid R] (msgs : List (κ × R)) (k : κ) :
    R :=
  ((msgs.filter (·.1 = k)).map (·.2)).sum

/-- Messages balance when every key has net multiplicity zero. -/
def Balanced {κ R : Type*} [DecidableEq κ] [AddCommMonoid R] (msgs : List (κ × R)) : Prop :=
  ∀ k, netMult msgs k = 0

/-- The logarithmic-derivative sum: sum_k m_k / (X - v_k) in F(X). -/
noncomputable def logDerivSum {F : Type*} [Field F] (msgs : List (F × F)) : RatFunc F :=
  (msgs.map fun p => algebraMap F[X] (RatFunc F) (C p.2) /
    algebraMap F[X] (RatFunc F) (X - C p.1)).sum

section Net

variable {κ R M : Type _} [DecidableEq κ] [AddCommMonoid R] [AddCommMonoid M]

@[simp] theorem netMult_nil (k : κ) : netMult ([] : List (κ × R)) k = 0 := rfl

theorem netMult_cons (p : κ × R) (l : List (κ × R)) (k : κ) :
    netMult (p :: l) k = (if p.1 = k then p.2 else 0) + netMult l k := by
  unfold netMult; by_cases h : p.1 = k <;> simp [h]

theorem netMult_append (l l' : List (κ × R)) (k : κ) :
    netMult (l ++ l') k = netMult l k + netMult l' k := by
  simp [netMult, List.filter_append]

/-- A key no message carries has net multiplicity zero. -/
theorem netMult_of_not_mem {l : List (κ × R)} {k : κ} (h : k ∉ l.map (·.1)) :
    netMult l k = 0 := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    simp [netMult_cons, Ne.symm h.1, ih h.2]

/-- A map of the multiplicities maps the net multiplicities. -/
theorem netMult_map {S : Type _} [AddCommMonoid S] (g : R →+ S) (l : List (κ × R)) (k : κ) :
    netMult (l.map fun p => (p.1, g p.2)) k = g (netMult l k) := by
  induction l with
  | nil => simp
  | cons p l ih => rw [List.map_cons, netMult_cons, netMult_cons, ih, map_add]; split_ifs <;> simp

/-- A sum over messages, additive in the multiplicity, regroups by key. -/
theorem sum_map_eq_sum_netMult (g : κ → R →+ M) (l : List (κ × R)) (S : Finset κ)
    (hS : ∀ p ∈ l, p.1 ∈ S) :
    (l.map fun p => g p.1 p.2).sum = ∑ k ∈ S, g k (netMult l k) := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons, netMult_cons, map_add, sum_add_distrib]
    rw [ih fun q hq => hS q (List.mem_cons_of_mem _ hq)]
    congr 1
    rw [sum_eq_single_of_mem p.1 (hS p List.mem_cons_self) fun k _ hk => by simp [Ne.symm hk]]
    simp

end Net

variable {F : Type*} [Field F] [DecidableEq F]

local notation "ι" => algebraMap F[X] (RatFunc F)

theorem logDerivSum_append (l l' : List (F × F)) :
    logDerivSum (l ++ l') = logDerivSum l + logDerivSum l' := by
  simp [logDerivSum]

theorem logDerivSum_neg (l : List (F × F)) :
    logDerivSum (l.map fun p => (p.1, -p.2)) = -logDerivSum l := by
  induction l with
  | nil => simp [logDerivSum]
  | cons p l ih =>
    simp only [logDerivSum, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, C_neg, map_neg, neg_div, neg_add]

/-- The sum regrouped over any set of keys covering the messages. -/
theorem logDerivSum_eq_sum (l : List (F × F)) (S : Finset F) (hS : ∀ p ∈ l, p.1 ∈ S) :
    logDerivSum l = ∑ v ∈ S, ι (C (netMult l v)) / ι (X - C v) := by
  let g : F → F →+ RatFunc F := fun v =>
    { toFun := fun m => ι (C m) / ι (X - C v)
      map_zero' := by simp
      map_add' := fun a b => by simp [add_div] }
  exact sum_map_eq_sum_netMult g l S hS

/-- Distinct poles: sum_v n_v / (X - v) vanishes only when every n_v does. -/
theorem sum_div_X_sub_C_eq_zero_iff (S : Finset F) (n : F → F) :
    ∑ v ∈ S, ι (C (n v)) / ι (X - C v) = 0 ↔ ∀ v ∈ S, n v = 0 := by
  refine ⟨fun h v₀ hv₀ => ?_, fun h => sum_eq_zero fun v hv => by simp [h v hv]⟩
  have hne : ∀ v, ι (X - C v) ≠ 0 := fun v =>
    (map_ne_zero_iff _ (IsFractionRing.injective F[X] (RatFunc F))).2 (X_sub_C_ne_zero v)
  -- Clear the denominators: multiply by prod_w (X - w).
  set P : F[X] := ∑ v ∈ S, C (n v) * ∏ w ∈ S.erase v, (X - C w)
  have hP : P = 0 := by
    apply IsFractionRing.injective F[X] (RatFunc F)
    have : ι P = (∑ v ∈ S, ι (C (n v)) / ι (X - C v)) * ι (∏ w ∈ S, (X - C w)) := by
      simp only [P, map_sum, map_mul, map_prod, sum_mul]
      refine sum_congr rfl fun v hv => ?_
      rw [← prod_erase_mul S _ hv]
      have := hne v
      field_simp
    rw [this, h, zero_mul, map_zero]
  -- Evaluate at v₀: only the v₀ term survives.
  have := congrArg (eval v₀) hP
  rw [eval_finsetSum, sum_eq_single_of_mem v₀ hv₀ fun v hv hvne => by
    rw [eval_mul, eval_prod, prod_eq_zero (mem_erase.2 ⟨Ne.symm hvne, hv₀⟩) (by simp),
      mul_zero],
    eval_mul, eval_C, eval_prod, eval_zero] at this
  refine (mul_eq_zero.1 this).resolve_right ?_
  rw [prod_eq_zero_iff]; rintro ⟨w, hw, h0⟩
  simp only [eval_sub, eval_X, eval_C, sub_eq_zero] at h0
  exact (mem_erase.1 hw).1 h0.symm

/-- **The log-derivative identity.**

The sum of m / (X - v) vanishes in F(X) exactly when the messages balance. -/
theorem logDerivSum_eq_zero_iff (l : List (F × F)) : logDerivSum l = 0 ↔ Balanced l := by
  classical
  rw [logDerivSum_eq_sum l (l.map (·.1)).toFinset (fun p hp => by simpa using ⟨p.2, hp⟩),
    sum_div_X_sub_C_eq_zero_iff]
  refine ⟨fun h k => ?_, fun h v _ => h v⟩
  by_cases hk : k ∈ (l.map (·.1)).toFinset
  · exact h k hk
  · exact netMult_of_not_mem (by simpa using hk)

/-- Two message lists have the same sum exactly when every key has the same net multiplicity. -/
theorem logDerivSum_eq_iff (l l' : List (F × F)) :
    logDerivSum l = logDerivSum l' ↔ ∀ v, netMult l v = netMult l' v := by
  rw [← sub_eq_zero, sub_eq_add_neg, ← logDerivSum_neg, ← logDerivSum_append,
    logDerivSum_eq_zero_iff]
  refine forall_congr' fun v => ?_
  have h := netMult_map (-(AddMonoidHom.id F)) l' v
  simp only [AddMonoidHom.neg_apply, AddMonoidHom.id_apply] at h
  rw [netMult_append, h, ← sub_eq_add_neg, sub_eq_zero]

/-! ## Counts -/

/-- The net multiplicity of unit messages is the count, read in F. -/
theorem netMult_units (f : List F) (v : F) : netMult (f.map (·, (1 : F))) v = (f.count v : F) := by
  induction f with
  | nil => simp
  | cons a f ih =>
    rw [List.map_cons, netMult_cons, ih, List.count_cons]; by_cases h : a = v <;> simp [h, add_comm]

/-- Counts up to L inject into F when no positive count up to L vanishes. -/
theorem cast_inj_of_le {L : ℕ} (hp : ∀ n : ℕ, 0 < n → n ≤ L → (n : F) ≠ 0) {a b : ℕ}
    (ha : a ≤ L) (hb : b ≤ L) (h : (a : F) = b) : a = b := by
  rcases le_total a b with hab | hab
  · by_contra hne
    exact hp (b - a) (by omega) (by omega) (by push_cast [Nat.cast_sub hab]; rw [h, sub_self])
  · by_contra hne
    exact hp (a - b) (by omega) (by omega) (by push_cast [Nat.cast_sub hab]; rw [h, sub_self])

/-- In characteristic p, no positive count below p vanishes. -/
theorem cast_ne_zero_of_lt (p : ℕ) [CharP F p] {L : ℕ} (hL : L < p) :
    ∀ n : ℕ, 0 < n → n ≤ L → (n : F) ≠ 0 := fun n hn hnL h =>
  absurd (Nat.le_of_dvd hn ((CharP.cast_eq_zero_iff F p n).1 h)) (by omega)

/-- The multiplicities that put each value's query count on its last occurrence in the table. -/
def lastMults (f : List F) : List F → List F
  | [] => []
  | v :: t => (if v ∈ t then 0 else (f.count v : F)) :: lastMults f t

theorem length_lastMults (f t : List F) : (lastMults f t).length = t.length := by
  induction t <;> simp_all [lastMults]

theorem netMult_lastMults (f t : List F) (w : F) :
    netMult (t.zip (lastMults f t)) w = if w ∈ t then (f.count w : F) else 0 := by
  induction t with
  | nil => simp
  | cons v t ih =>
    simp only [lastMults, List.zip_cons_cons, netMult_cons, ih, List.mem_cons]
    rcases eq_or_ne v w with rfl | hw
    · by_cases ht : v ∈ t <;> simp_all
    · have := hw.symm
      by_cases ht : w ∈ t <;> simp_all

/-- **Set inclusion (Lemma 5).**

In characteristic above the number of queries, the queries lie in the table exactly when,
for some multiplicities, sum_j 1 / (X - f_j) = sum_i m_i / (X - t_i). -/
theorem lookupRelation_iff_logDeriv (f t : List F)
    (hp : ∀ n : ℕ, 0 < n → n ≤ f.length → (n : F) ≠ 0) :
    (f, t) ∈ Lookup.relation ↔
      ∃ m : List F, m.length = t.length ∧
        logDerivSum (f.map (·, 1)) = logDerivSum (t.zip m) := by
  constructor
  · intro hf
    replace hf : ∀ v ∈ f, v ∈ t := hf
    refine ⟨lastMults f t, length_lastMults f t, ?_⟩
    rw [logDerivSum_eq_iff]; intro v
    rw [netMult_units, netMult_lastMults]
    split_ifs with hv
    · rfl
    · rw [List.count_eq_zero.2 fun hvf => hv (hf v hvf), Nat.cast_zero]
  · rintro ⟨m, hm, h⟩
    show ∀ v ∈ f, v ∈ t
    intro v hv
    by_contra hvt
    rw [logDerivSum_eq_iff] at h
    have h1 := h v
    rw [netMult_units, netMult_of_not_mem (show v ∉ (t.zip m).map Prod.fst by
      rw [List.map_fst_zip (by omega)]; exact hvt)] at h1
    exact hp _ (List.count_pos_iff.2 hv) (List.count_le_length) h1

/-- **Permutations (Lemma 3).**

In characteristic above both lengths, two lists are permutations of each other exactly when
sum_j 1 / (X - a_j) = sum_j 1 / (X - b_j). -/
theorem perm_iff_logDeriv (a b : List F) {L : ℕ} (ha : a.length ≤ L)
    (hb : b.length ≤ L) (hp : ∀ n : ℕ, 0 < n → n ≤ L → (n : F) ≠ 0) :
    a.Perm b ↔ logDerivSum (a.map (·, 1)) = logDerivSum (b.map (·, 1)) := by
  rw [logDerivSum_eq_iff, List.perm_iff_count]
  refine forall_congr' fun v => ?_
  rw [netMult_units, netMult_units]
  exact ⟨fun h => by rw [h], cast_inj_of_le hp ((List.count_le_length).trans ha)
    ((List.count_le_length).trans hb)⟩

/-- **Overflow.**

In characteristic p, p queries of one value satisfy the identity against an empty table. -/
theorem logDeriv_overflow (p : ℕ) [CharP F p] (v : F) :
    logDerivSum ((List.replicate p v).map (·, (1 : F))) = logDerivSum [] := by
  classical
  rw [logDerivSum_eq_iff]; intro w
  rw [netMult_units, List.count_replicate]; split_ifs <;> simp

end Lookup.LogUp
