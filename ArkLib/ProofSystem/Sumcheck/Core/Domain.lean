/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.Types

/-! # Indexed evaluation domains for Sumcheck

Domain indices retain multiplicities of evaluation points. The honest round polynomial sums
restrictions over all assignments of suffix indices. Polynomial evaluation uses Mathlib's
noncomputable polynomial representations.
-/

@[expose] public section

namespace Sumcheck.Core
open Polynomial MvPolynomial Finset

variable {R : Type} [CommSemiring R] {d n deg : ℕ}

omit [CommSemiring R] in
/-- Summing over domain indices agrees with the finite-set sum for an injective domain. -/
theorem sum_domain_embedding {M : Type*} [AddCommMonoid M] (D : Fin d ↪ R) (k : ℕ)
    (f : (Fin k → R) → M) :
    (∑ x : Fin k → Fin d, f (D ∘ x)) = ∑ x ∈ (univ.map D) ^ᶠ k, f x := by
  classical
  refine sum_bij (fun x _ => D ∘ x) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro x _
    simp only [Fintype.mem_piFinset, mem_map, mem_univ, true_and]
    exact fun j => ⟨x j, rfl⟩
  · intro x _ y _ h
    exact funext fun j => D.injective (congrFun h j)
  · intro x hx
    simp only [Fintype.mem_piFinset, mem_map, mem_univ, true_and] at hx
    choose y hy using hx
    exact ⟨y, mem_univ _, funext hy⟩

omit [CommSemiring R] in
/-- Summing over a list's indices retains exactly its list-sum multiplicities. -/
theorem sum_domain_list {M : Type*} [AddCommMonoid M] (domain : List R) (f : R → M) :
    (∑ i : Fin domain.length, f (domain.get i)) = (domain.map f).sum := by
  simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_def] using
    congrArg (fun xs : List R => (xs.map f).sum) (List.ofFn_get domain)

/-- The remaining sum after fixing a prefix of challenges, counting domain multiplicities. -/
noncomputable def roundSum (D : Fin d → R) (i : Fin (n + 1)) (c : Fin i → R)
    (p : MvPolynomial (Fin n) R) : R :=
  ∑ x : Fin (n - i) → Fin d, p.eval
    (Fin.append c (D ∘ x) ∘ Fin.cast (by have := i.isLt; omega))

/-- The honest round polynomial, summed over assignments of suffix domain indices. -/
noncomputable def projectedRoundPolynomial (D : Fin d → R) (i : Fin n)
    (c : Fin i.castSucc → R) (p : R⦃≤ deg⦄[X Fin n]) : R⦃≤ deg⦄[X] :=
  ⟨∑ x : Fin (n - 1 - i) → Fin d,
      p.val.evalExcept i (roundSuffix i c (D ∘ x)),
    Submodule.sum_mem _ fun _ _ => MvPolynomial.evalExcept_mem_degreeLE i _ p.property⟩

/-- Splitting an indexed assignment into its first index and suffix preserves the sum. -/
theorem sum_evalExcept_indices {l : ℕ} (D : Fin d → R) (i : Fin (n + 1))
    (c : Fin i → R) (h : n = i + l) (p : MvPolynomial (Fin (n + 1)) R) :
    (∑ a : Fin d, ∑ x : Fin l → Fin d,
      (p.evalExcept i (Fin.append c (D ∘ x) ∘ Fin.cast h)).eval (D a)) =
      ∑ x : Fin (l + 1) → Fin d,
        p.eval (Fin.append c (D ∘ x) ∘ Fin.cast (by omega)) := by
  have hs := Fin.sum_piFinset_cons (fun _ : Fin (l + 1) => (univ : Finset (Fin d)))
    (fun x => p.eval (Fin.append c (D ∘ x) ∘ Fin.cast (by omega)))
  simp only [Fintype.piFinset_univ] at hs
  rw [hs]
  simp_rw [MvPolynomial.eval_evalExcept_append i c _ h]
  apply sum_congr rfl
  intro a _
  apply sum_congr rfl
  intro x _
  have hc : D ∘ Fin.cons a x = Fin.cons (D a) (D ∘ x) := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  rw [hc, Fin.append_left_snoc]
  rfl

/-- The indexed sum of the honest round polynomial equals the current remaining sum. -/
theorem sum_projectedRoundPolynomial (D : Fin d → R) (i : Fin n)
    (c : Fin i.castSucc → R) (p : R⦃≤ deg⦄[X Fin n]) :
    (∑ a : Fin d, (projectedRoundPolynomial D i c p).val.eval (D a)) =
      roundSum D i.castSucc c p.val := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
      simp only [projectedRoundPolynomial, Polynomial.eval_finsetSum]
      refine (sum_evalExcept_indices D i c (by omega) p.val).trans ?_
      unfold roundSum
      have hs := Fin.sum_piFinset_cast (univ : Finset (Fin d))
        (show n + 1 - i.val = (n - i.val) + 1 by omega)
        (fun x => p.val.eval (Fin.append c (D ∘ x) ∘ Fin.cast (by simp)))
      simp only [Fintype.piFinset_univ] at hs
      refine Eq.trans ?_ hs.symm
      apply sum_congr rfl
      intro x _
      congr 2
      symm
      change (Fin.append c ((D ∘ x) ∘ Fin.cast (by omega)) ∘
        Fin.cast (by simp only [Fin.val_castSucc]; omega)) = _
      rw [Fin.append_cast_right]
      rfl

/-- Updating the prefix and evaluating the honest polynomial gives the successor sum. -/
theorem roundSum_succ (D : Fin d → R) (i : Fin n) (c : Fin i.castSucc → R)
    (p : R⦃≤ deg⦄[X Fin n]) (r : R) :
    roundSum D i.succ (Fin.snoc c r) p.val =
      (projectedRoundPolynomial D i c p).val.eval r := by
  cases n with
  | zero => exact i.elim0
  | succ n =>
      simp only [roundSum, projectedRoundPolynomial, Polynomial.eval_finsetSum,
        roundSuffix, MvPolynomial.eval_evalExcept_append]
      have hs := Fin.sum_piFinset_cast (univ : Finset (Fin d))
        (show n + 1 - (i.val + 1) = n - i.val by omega)
        (fun x => p.val.eval (Fin.append (Fin.snoc c r) (D ∘ x) ∘ Fin.cast (by simp; omega)))
      simp only [Fintype.piFinset_univ] at hs
      refine Eq.trans hs ?_
      apply sum_congr rfl
      intro x _
      congr 2
      change (Fin.append (Fin.snoc c r) ((D ∘ x) ∘ Fin.cast (by omega)) ∘
        Fin.cast (by simp only [Fin.val_castSucc]; omega)) = _
      rw [Fin.append_cast_right]
      rfl

/-- The indexed relation for the current round counts every assignment of domain indices. -/
def indexedRelation (D : Fin d → R) (i : Fin (n + 1))
    (stmt : RoundStatement R n i) (p : R⦃≤ deg⦄[X Fin n]) : Prop :=
  roundSum D i stmt.challenges p.val = stmt.target

/-- The last indexed relation is the full evaluation claim, independent of the domain. -/
theorem indexedRelation_last (D : Fin d → R)
    (stmt : RoundStatement R n (Fin.last n)) (p : R⦃≤ deg⦄[X Fin n]) :
    indexedRelation D (Fin.last n) stmt p ↔ p.val.eval stmt.challenges = stmt.target := by
  let : Unique (Fin (n - (Fin.last n).val) → Fin d) := by
    simpa using (show Unique (Fin 0 → Fin d) from
      ⟨⟨Fin.elim0⟩, fun _ => funext fun j => j.elim0⟩)
  unfold indexedRelation roundSum
  rw [Fintype.sum_unique]
  have h : Fin.append stmt.challenges (D ∘ (default : Fin (n - (Fin.last n).val) → Fin d)) ∘
      Fin.cast (show n = n + (n - n) by omega) = stmt.challenges := by
    funext j
    change Fin.append stmt.challenges _ (Fin.cast _ j) = _
    exact Fin.append_left_of_lt j.val (by omega) j.isLt
  change _ = stmt.target ↔ _ = stmt.target
  rw [h]

/-- The input sum predicate for arbitrary evaluation behavior, without a polynomial realization. -/
def behaviorInputRelation (domain : List R) (target : R) (evaluate : R → R) : Prop :=
  (domain.map evaluate).sum = target

/-- The output evaluation predicate for arbitrary behavior, without a polynomial realization. -/
def behaviorOutputRelation {X : Type} (target : R) (point : X) (evaluate : X → R) : Prop :=
  evaluate point = target

end Sumcheck.Core
