/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.List.NetMult
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Sums of logarithmic derivatives

For a keyed list of pairs (v_k, m_k) over a field F, consider the rational function

  sum_k m_k / (X - v_k)  in F(X).

It is the logarithmic derivative of prod_k (X - v_k)^(m_k) when the m_k are integers.

These identities underlie lookups by logarithmic derivatives.

That is Haböck, "Multivariate lookups based on logarithmic derivatives", eprint 2022/1530.

## Results

- The sum vanishes exactly when every key has net multiplicity zero.
- Set inclusion (Lemma 5): f ⊆ t exactly when, for some multiplicities m,
  sum_j 1 / (X - f_j) = sum_i m_i / (X - t_i).
- Permutations (Lemma 3): two lists are permutations exactly when their sums of
  1 / (X - x) agree.
- Both need a characteristic above the number of queries.

The reason: in characteristic p, p equal queries cancel.

## Computability

The sum is a noncomputable mathematical view.

Mathlib builds polynomials on finitely supported functions with classical decidability.

So it marks polynomial constants and polynomial addition noncomputable.

Division in Mathlib's rational functions, and the embedding of polynomials into them,
are noncomputable too.

The executable content is the net multiplicity and the witness multiplicities.

Every statement here reduces the rational identity to those.
-/

@[expose] public section

namespace RatFunc

open Polynomial Finset
open List (netMult Balanced lastMults length_lastMults netMult_append netMult_map_snd
  netMult_of_not_mem netMult_map_one netMult_zip_lastMults sum_map_eq_sum_netMult)

variable {F : Type*} [Field F]

local notation "ι" => algebraMap F[X] (RatFunc F)

/-- The logarithmic-derivative sum: sum_k m_k / (X - v_k) in F(X). -/
noncomputable def logDerivSum (l : List (F × F)) : RatFunc F :=
  (l.map fun p => ι (C p.2) / ι (X - C p.1)).sum

theorem logDerivSum_append (l l' : List (F × F)) :
    logDerivSum (l ++ l') = logDerivSum l + logDerivSum l' := by
  simp [logDerivSum]

theorem logDerivSum_map_neg (l : List (F × F)) :
    logDerivSum (l.map fun p => (p.1, -p.2)) = -logDerivSum l := by
  induction l with
  | nil => simp [logDerivSum]
  | cons p l ih =>
    simp only [logDerivSum, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, C_neg, map_neg, neg_div, neg_add]

/-- The sum regrouped over any set of keys covering the list. -/
theorem logDerivSum_eq_sum [DecidableEq F] (l : List (F × F)) (S : Finset F)
    (hS : ∀ p ∈ l, p.1 ∈ S) :
    logDerivSum l = ∑ v ∈ S, ι (C (netMult l v)) / ι (X - C v) := by
  let g : F → F →+ RatFunc F := fun v =>
    { toFun := fun m => ι (C m) / ι (X - C v)
      map_zero' := by simp
      map_add' := fun a b => by simp [add_div] }
  exact sum_map_eq_sum_netMult g l S hS

/-- Distinct poles: sum_v n_v / (X - v) vanishes only when every n_v does. -/
theorem sum_div_X_sub_C_eq_zero_iff (S : Finset F) (n : F → F) :
    ∑ v ∈ S, ι (C (n v)) / ι (X - C v) = 0 ↔ ∀ v ∈ S, n v = 0 := by
  classical
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

The sum of m / (X - v) vanishes in F(X) exactly when the list is balanced. -/
theorem logDerivSum_eq_zero_iff [DecidableEq F] (l : List (F × F)) :
    logDerivSum l = 0 ↔ Balanced l := by
  rw [logDerivSum_eq_sum l (l.map (·.1)).toFinset (fun p hp => by simpa using ⟨p.2, hp⟩),
    sum_div_X_sub_C_eq_zero_iff]
  refine ⟨fun h k => ?_, fun h v _ => h v⟩
  by_cases hk : k ∈ (l.map (·.1)).toFinset
  · exact h k hk
  · exact netMult_of_not_mem (by simpa using hk)

/-- Two lists have the same sum exactly when every key has the same net multiplicity. -/
theorem logDerivSum_eq_iff [DecidableEq F] (l l' : List (F × F)) :
    logDerivSum l = logDerivSum l' ↔ ∀ v, netMult l v = netMult l' v := by
  rw [← sub_eq_zero, sub_eq_add_neg, ← logDerivSum_map_neg, ← logDerivSum_append,
    logDerivSum_eq_zero_iff]
  refine forall_congr' fun v => ?_
  have h := netMult_map_snd (-(AddMonoidHom.id F)) l' v
  simp only [AddMonoidHom.neg_apply, AddMonoidHom.id_apply] at h
  rw [netMult_append, h, ← sub_eq_add_neg, sub_eq_zero]

/-! ## Counts in small characteristic -/

/-- Counts up to L inject into F when no positive count up to L vanishes. -/
theorem natCast_inj_of_le {L : ℕ} (hp : ∀ n : ℕ, 0 < n → n ≤ L → (n : F) ≠ 0) {a b : ℕ}
    (ha : a ≤ L) (hb : b ≤ L) (h : (a : F) = b) : a = b := by
  rcases le_total a b with hab | hab
  · by_contra hne
    exact hp (b - a) (by omega) (by omega) (by push_cast [Nat.cast_sub hab]; rw [h, sub_self])
  · by_contra hne
    exact hp (a - b) (by omega) (by omega) (by push_cast [Nat.cast_sub hab]; rw [h, sub_self])

/-- In characteristic p, no positive count below p vanishes. -/
theorem natCast_ne_zero_of_lt (p : ℕ) [CharP F p] {L : ℕ} (hL : L < p) :
    ∀ n : ℕ, 0 < n → n ≤ L → (n : F) ≠ 0 := fun n hn hnL h =>
  absurd (Nat.le_of_dvd hn ((CharP.cast_eq_zero_iff F p n).1 h)) (by omega)

/-! ## Lookups -/

/-- **Set inclusion (Lemma 5).**

In characteristic above the number of queries, f ⊆ t exactly when, for some multiplicities,
sum_j 1 / (X - f_j) = sum_i m_i / (X - t_i). -/
theorem subset_iff_exists_logDerivSum_eq (f t : List F)
    (hp : ∀ n : ℕ, 0 < n → n ≤ f.length → (n : F) ≠ 0) :
    f ⊆ t ↔ ∃ m : List F, m.length = t.length ∧
      logDerivSum (f.map (·, 1)) = logDerivSum (t.zip m) := by
  classical
  refine ⟨fun hf => ⟨lastMults F f t, length_lastMults f t, ?_⟩, ?_⟩
  · rw [logDerivSum_eq_iff]; intro v
    rw [netMult_map_one, netMult_zip_lastMults]
    split_ifs with hv
    · rfl
    · rw [List.count_eq_zero.2 fun hvf => hv (hf hvf), Nat.cast_zero]
  · rintro ⟨m, hm, h⟩ v hv
    by_contra hvt
    have h1 := (logDerivSum_eq_iff _ _).1 h v
    rw [netMult_map_one, netMult_of_not_mem (by rwa [List.map_fst_zip (by omega)])] at h1
    exact hp _ (List.count_pos_iff.2 hv) List.count_le_length h1

/-- **Permutations (Lemma 3).**

In characteristic above both lengths, two lists are permutations of each other exactly when
sum_j 1 / (X - a_j) = sum_j 1 / (X - b_j). -/
theorem perm_iff_logDerivSum_eq (a b : List F) {L : ℕ} (ha : a.length ≤ L)
    (hb : b.length ≤ L) (hp : ∀ n : ℕ, 0 < n → n ≤ L → (n : F) ≠ 0) :
    a.Perm b ↔ logDerivSum (a.map (·, 1)) = logDerivSum (b.map (·, 1)) := by
  classical
  rw [logDerivSum_eq_iff, List.perm_iff_count]
  refine forall_congr' fun v => ?_
  rw [netMult_map_one, netMult_map_one]
  exact ⟨fun h => by rw [h], natCast_inj_of_le hp (List.count_le_length.trans ha)
    (List.count_le_length.trans hb)⟩

/-- **Overflow.**

In characteristic p, p queries of one value balance against an empty table. -/
theorem logDerivSum_replicate_eq_zero (p : ℕ) [CharP F p] (v : F) :
    logDerivSum ((List.replicate p v).map (·, (1 : F))) = 0 := by
  classical
  rw [logDerivSum_eq_zero_iff]; intro w
  rw [netMult_map_one, List.count_replicate]; split_ifs <;> simp

end RatFunc
