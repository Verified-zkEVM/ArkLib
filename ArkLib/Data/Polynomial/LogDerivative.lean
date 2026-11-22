/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import ArkLib.Data.List.NetMult
public import Mathlib.FieldTheory.RatFunc.Basic
public import ArkLib.ToMathlib.Algebra.CharP.NatCast
public import Mathlib.Algebra.Polynomial.BigOperators

/-!
# Sums of logarithmic derivatives

A keyed list of pairs `(v_k, m_k)` over a field `F` gives the sum `sum_k m_k / (X - v_k)` in `F(X)`.

For integer `m_k`, it is the logarithmic derivative of `prod_k (X - v_k)^(m_k)`.

This file is the algebra core of lookups by logarithmic derivatives (LogUp) [Hab22].

A LogUp protocol spec should build on it, not on a second proof.

## Main statements

- `RatFunc.logDerivSum_eq_zero_iff`: the sum vanishes exactly when every key nets to zero.
- `RatFunc.subset_iff_exists_logDerivSum_eq`: set inclusion ([Hab22], Lemma 5).
- `RatFunc.perm_iff_logDerivSum_eq`: permutations ([Hab22], Lemma 3).
- `RatFunc.logDerivSum_replicate_eq_nil_and_not_subset`: the converse fails without a bound.

## The two identities

Set inclusion: `f ⊆ t` exactly when `sum_j 1 / (X - f_j) = sum_i m_i / (X - t_i)` for some `m`.

Permutations: two lists are permutations exactly when their sums of `1 / (X - x)` agree.

## Characteristic hypotheses

Only one direction of each equivalence needs a hypothesis on `F`.

Set inclusion gives equal sums in every field, and so does a permutation.

Going back needs each of `1, 2, ...` up to the largest count of a value to be nonzero in `F`.

Characteristic zero, or a characteristic above the largest count, is enough.

The number of queries bounds the largest count, so a characteristic above it is enough too.

Without the bound the converse fails: in characteristic `p > 0`, `p` equal queries cancel.

## Computability

The sum is a noncomputable mathematical view.

Mathlib builds polynomials on finitely supported functions with classical decidability.

So it marks polynomial constants and polynomial addition noncomputable.

Division of rational functions and the embedding of polynomials into them are noncomputable too.

The executable content is the net multiplicity and the witness multiplicities.

Every statement here reduces the rational identity to those.

## References

* [Haböck, U., *Multivariate lookups based on logarithmic derivatives*][Hab22]
-/

@[expose] public section

namespace RatFunc

open Polynomial Finset
open List (netMult Balanced lastMults length_lastMults netMult_append netMult_map_snd
  netMult_of_not_mem netMult_map_one netMult_zip_lastMults sum_map_eq_sum_netMult
  count_le_maxCount maxCount_le_length)

variable {F : Type*} [Field F]

local notation "ι" => algebraMap F[X] (RatFunc F)

/-- The logarithmic-derivative sum `sum_k m_k / (X - v_k)` in `F(X)`. -/
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

/-- Distinct poles: `sum_v n_v / (X - v)` vanishes only when every `n_v` does. -/
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

The sum of `m / (X - v)` vanishes in `F(X)` exactly when the list is balanced. -/
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

/-! ## Lookups -/

/-- With the last-occurrence multiplicities, queries inside the table give equal sums.

This holds in every characteristic. -/
theorem logDerivSum_eq_zip_lastMults_of_subset [DecidableEq F] {f t : List F} (hf : f ⊆ t) :
    logDerivSum (f.map (·, 1)) = logDerivSum (t.zip (lastMults F f t)) := by
  rw [logDerivSum_eq_iff]; intro v
  rw [netMult_map_one, netMult_zip_lastMults]
  split_ifs with hv
  · rfl
  · rw [List.count_eq_zero.2 fun hvf => hv (hf hvf), Nat.cast_zero]

/-- Queries inside the table have multiplicities giving equal sums, in every characteristic. -/
theorem exists_logDerivSum_eq_of_subset {f t : List F} (hf : f ⊆ t) :
    ∃ m : List F, m.length = t.length ∧
      logDerivSum (f.map (·, 1)) = logDerivSum (t.zip m) := by
  classical
  exact ⟨lastMults F f t, length_lastMults f t, logDerivSum_eq_zip_lastMults_of_subset hf⟩

/-- Equal sums force the queries into the table when no count of a query vanishes in `F`.

The multiplicities are arbitrary field elements.

Only the query counts must stay nonzero. -/
theorem subset_of_logDerivSum_eq [DecidableEq F] {f t m : List F}
    (hp : NatCastNeZeroUpTo F f.maxCount)
    (h : logDerivSum (f.map (·, 1)) = logDerivSum (t.zip m)) : f ⊆ t := by
  intro v hv
  by_contra hvt
  have h1 := (logDerivSum_eq_iff _ _).1 h v
  have hkey : v ∉ (t.zip m).map Prod.fst := fun hk => hvt <| by
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.1 hk
    exact (List.of_mem_zip hab).1
  rw [netMult_map_one, netMult_of_not_mem hkey] at h1
  exact hp _ (List.count_pos_iff.2 hv) (f.count_le_maxCount v) h1

/-- **Set inclusion.**

When no count of a query vanishes in `F`, these are equivalent:
- `f ⊆ t`;
- `sum_j 1 / (X - f_j) = sum_i m_i / (X - t_i)` for some multiplicities `m`. -/
theorem subset_iff_exists_logDerivSum_eq [DecidableEq F] (f t : List F)
    (hp : NatCastNeZeroUpTo F f.maxCount) :
    f ⊆ t ↔ ∃ m : List F, m.length = t.length ∧
      logDerivSum (f.map (·, 1)) = logDerivSum (t.zip m) :=
  ⟨exists_logDerivSum_eq_of_subset, fun ⟨_, _, h⟩ => subset_of_logDerivSum_eq hp h⟩

/-- Set inclusion, with the number of queries as the bound. -/
theorem subset_iff_exists_logDerivSum_eq_of_length (f t : List F)
    (hp : NatCastNeZeroUpTo F f.length) :
    f ⊆ t ↔ ∃ m : List F, m.length = t.length ∧
      logDerivSum (f.map (·, 1)) = logDerivSum (t.zip m) := by
  classical
  exact subset_iff_exists_logDerivSum_eq f t (hp.mono f.maxCount_le_length)

/-- Set inclusion in characteristic zero. -/
theorem subset_iff_exists_logDerivSum_eq_of_charZero [CharZero F] (f t : List F) :
    f ⊆ t ↔ ∃ m : List F, m.length = t.length ∧
      logDerivSum (f.map (·, 1)) = logDerivSum (t.zip m) := by
  classical
  exact subset_iff_exists_logDerivSum_eq f t (.of_charZero F _)

/-- Permuting a keyed list keeps its sum, in every characteristic. -/
theorem logDerivSum_eq_of_perm {l l' : List (F × F)} (h : l.Perm l') :
    logDerivSum l = logDerivSum l' :=
  (h.map _).sum_eq

/-- Equal sums force a permutation when no count in either list vanishes in `F`. -/
theorem perm_of_logDerivSum_eq [DecidableEq F] {a b : List F}
    (hp : NatCastNeZeroUpTo F (max a.maxCount b.maxCount))
    (h : logDerivSum (a.map (·, 1)) = logDerivSum (b.map (·, 1))) : a.Perm b := by
  rw [List.perm_iff_count]; intro v
  have h1 := (logDerivSum_eq_iff _ _).1 h v
  rw [netMult_map_one, netMult_map_one] at h1
  exact hp.natCast_inj ((a.count_le_maxCount v).trans (le_max_left _ _))
    ((b.count_le_maxCount v).trans (le_max_right _ _)) h1

/-- **Permutations.**

When no count in either list vanishes in `F`, these are equivalent:
- `a` and `b` are permutations of each other;
- `sum_j 1 / (X - a_j) = sum_j 1 / (X - b_j)`. -/
theorem perm_iff_logDerivSum_eq [DecidableEq F] (a b : List F)
    (hp : NatCastNeZeroUpTo F (max a.maxCount b.maxCount)) :
    a.Perm b ↔ logDerivSum (a.map (·, 1)) = logDerivSum (b.map (·, 1)) :=
  ⟨fun h => logDerivSum_eq_of_perm (h.map _), perm_of_logDerivSum_eq hp⟩

/-- Permutations, with a common bound on both lengths. -/
theorem perm_iff_logDerivSum_eq_of_length (a b : List F) {L : ℕ} (ha : a.length ≤ L)
    (hb : b.length ≤ L) (hp : NatCastNeZeroUpTo F L) :
    a.Perm b ↔ logDerivSum (a.map (·, 1)) = logDerivSum (b.map (·, 1)) := by
  classical
  exact perm_iff_logDerivSum_eq a b (hp.mono (max_le (a.maxCount_le_length.trans ha)
    (b.maxCount_le_length.trans hb)))

/-- Permutations in characteristic zero. -/
theorem perm_iff_logDerivSum_eq_of_charZero [CharZero F] (a b : List F) :
    a.Perm b ↔ logDerivSum (a.map (·, 1)) = logDerivSum (b.map (·, 1)) := by
  classical
  exact perm_iff_logDerivSum_eq a b (.of_charZero F _)

/-- **Overflow.**

In characteristic `p > 0`, `p` queries of one value match the empty table.

The value is not in the empty table, so equal sums alone do not give set inclusion. -/
theorem logDerivSum_replicate_eq_nil_and_not_subset (p : ℕ) [CharP F p] (hp : 0 < p) (v : F) :
    logDerivSum ((List.replicate p v).map (·, 1)) = logDerivSum (([] : List F).zip []) ∧
      ¬ List.replicate p v ⊆ [] := by
  classical
  refine ⟨?_, fun h => List.not_mem_nil (h (List.mem_replicate.2 ⟨hp.ne', rfl⟩))⟩
  rw [logDerivSum_eq_iff]; intro w
  rw [netMult_map_one, List.count_replicate]; split_ifs <;> simp

end RatFunc
