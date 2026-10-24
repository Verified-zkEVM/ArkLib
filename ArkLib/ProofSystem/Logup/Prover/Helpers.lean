/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Logup.Interaction.Config
public import ArkLib.ProofSystem.Logup.Algebra.Grouped
public import ArkLib.ToCompPoly.Multilinear.Basic
public import ArkLib.Data.Finset.SumFiber

/-!
# Executable honest denominator and helper tables

The private prover maps base entries and caches each alpha-minus-value denominator once.
Helpers sum the individual weighted total inverses, including at poles. They are not computed
by dividing a folded fraction pair, which has different behavior at a pole.

Each local residual vanishes off poles. The global helper total vanishes for every alpha when
weighted fibers balance, including at poles: regroup equal values before applying total inverse.
The formal denominator MLE identity uses Boolean multilinear uniqueness in every characteristic.
These are table algorithms and algebraic facts, not a complete honest-strategy or resource bound.
Initialization, helper inversion, table folding and coefficient costs require separate measured
ledger entries tied to their actual control flow.
-/

@[expose] public section

open CompPoly
open scoped BigOperators

namespace Logup.Prover

variable {B E : Type} [CommRing B] [Field E] {n T K ell : Nat}

/-- Cache every denominator directly from its base entry, without retaining mapped values. -/
def denominatorTables (f : B →+* E) (alpha : E)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) : Vector (CMlPolynomialEval E n) T :=
  Vector.ofFn fun i => Vector.map (fun v => alpha - f v) (data (0, i))

/-- Map each original weight once into the challenge field. -/
def weightTables (f : B →+* E) (data : Fin 2 × Fin T → CMlPolynomialEval B n) :
    Vector (CMlPolynomialEval E n) T :=
  Vector.ofFn fun i => Vector.map f (data (1, i))

/-- Sum termwise total inverses at each Boolean row of each retained helper table. -/
def helpers (groups : Vector (List (Fin T)) K)
    (denominator weight : Vector (CMlPolynomialEval E n) T) :
    Vector (CMlPolynomialEval E n) K :=
  Vector.ofFn fun k => Vector.ofFn fun u =>
    (groups[k.val].map fun i => weight[i.val].get u * (denominator[i.val].get u)⁻¹).sum

/-- The cached denominator is exactly alpha minus the mapped original value. -/
@[simp] theorem get_denominatorTables (f : B →+* E) (alpha : E)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) (i : Fin T) (u : Fin (2 ^ n)) :
    (denominatorTables f alpha data)[i.val].get u = alpha - f ((data (0, i)).get u) := by
  simp [denominatorTables, Vector.get_eq_getElem]

/-- Cached weights are the mapped original weights. -/
@[simp] theorem get_weightTables (f : B →+* E)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) (i : Fin T) (u : Fin (2 ^ n)) :
    (weightTables f data)[i.val].get u = f ((data (1, i)).get u) := by
  simp [weightTables, Vector.get_eq_getElem]

/-- Helper entries are sums of individual quotients, with no off-pole restriction. -/
@[simp] theorem get_helpers (groups : Vector (List (Fin T)) K)
    (denominator weight : Vector (CMlPolynomialEval E n) T) (k : Fin K) (u : Fin (2 ^ n)) :
    (helpers groups denominator weight)[k.val].get u =
      (groups[k.val].map fun i => weight[i.val].get u / denominator[i.val].get u).sum := by
  simp [helpers, Vector.get_eq_getElem, div_eq_mul_inv]

/-- Caching denominators commutes with the formal multilinear polynomial interpretation. -/
theorem MLE_denominatorTables (f : B →+* E) (alpha : E)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) (i : Fin T) :
    MvPolynomial.MLE (fun u => (denominatorTables f alpha data)[i.val].get
      (finFunctionFinEquiv u)) =
      MvPolynomial.C alpha - MvPolynomial.MLE (fun u =>
        f ((data (0, i)).get (finFunctionFinEquiv u))) := by
  symm
  apply MvPolynomial.eq_MLE_of_degreeOf_le_one_of_eval_zeroOne_eq
  · intro j
    exact (MvPolynomial.degreeOf_sub_le j _ _).trans
      (max_le (by simp) (MvPolynomial.MLE_degreeOf _ j))
  · intro u
    simp [MvPolynomial.MLE_eval_zeroOne]

/-- Honest helper entries satisfy the local cleared constraint when its denominators are nonzero. -/
theorem groupResidual_helpers (groups : Vector (List (Fin T)) K) (f : B →+* E) (alpha : E)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n) (k : Fin K) (u : Fin (2 ^ n))
    (hoff : ∀ i ∈ groups[k.val], alpha - f ((data (0, i)).get u) ≠ 0) :
    Logup.groupResidual groups[k.val] alpha
      (fun i => f ((data (0, i)).get u)) (fun i => f ((data (1, i)).get u))
      ((helpers groups (denominatorTables f alpha data) (weightTables f data))[k.val].get u) =
      0 := by
  let ps := groups[k.val].map fun i =>
    (⟨f ((data (1, i)).get u), alpha - f ((data (0, i)).get u)⟩ : FractionPair E)
  have hden : ∀ p ∈ ps, p.denominator ≠ 0 := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hp
    exact hoff i hi
  have hv := FractionPair.value_sum ps hden
  have hn := FractionPair.sum_denominator_ne_zero ps hden
  have he : (helpers groups (denominatorTables f alpha data) (weightTables f data))[k.val].get u
      = (ps.map FractionPair.value).sum := by
    simp [ps, get_helpers, List.map_map, FractionPair.value, Function.comp_def]
  rw [he]
  change (ps.map FractionPair.value).sum * (FractionPair.sum ps).denominator -
    (FractionPair.sum ps).numerator = 0
  rw [sub_eq_zero]
  exact ((div_eq_iff hn).mp hv).symm

private theorem sum_group_rows (cfg : Logup.Interaction.Config n T ell)
    (term : Fin T → E) :
    (∑ k : Fin (T ⌈/⌉ ell), (cfg.groups[k.val].map term).sum) = ∑ i, term i := by
  have hvec : cfg.groups.toList =
      (List.finRange (T ⌈/⌉ ell)).map (fun k => cfg.groups[k.val]) := by
    have h := congrArg Vector.toList (Vector.ofFn_getElem (xs := cfg.groups))
    simpa only [Vector.toList_ofFn, List.ofFn_eq_map] using h.symm
  rw [Fin.sum_univ_def]
  have h := congrArg (fun xs : List (Fin T) => (xs.map term).sum) cfg.flatten_groups
  simpa only [List.map_flatten, List.sum_flatten, hvec, List.map_map, Fin.sum_univ_def,
    Function.comp_def] using h

private theorem sum_mul_key_eq_zero [DecidableEq E] {ι : Type}
    (s : Finset ι) (value weight : ι → E) (c : E → E)
    (hbalanced : ∀ v, s.sumFiber value weight v = 0) :
    ∑ i ∈ s, weight i * c (value i) = 0 := by
  classical
  rw [← s.sum_sumFiber (s.image value) value (fun i => weight i * c (value i))
    (fun i hi => Finset.mem_image_of_mem value hi)]
  apply Finset.sum_eq_zero
  intro v hv
  have h : s.sumFiber value (fun i => weight i * c (value i)) v =
      s.sumFiber value weight v * c v := by
    unfold Finset.sumFiber
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only
    rw [(Finset.mem_filter.mp hi).2]
  rw [h, hbalanced, zero_mul]

/-- Balanced challenge-field fibers give zero global helper total at every alpha, even poles. -/
theorem sum_helpers_eq_zero [DecidableEq E] (cfg : Logup.Interaction.Config n T ell) (f : B →+* E)
    (alpha : E) (data : Fin 2 × Fin T → CMlPolynomialEval B n)
    (hbalanced : ∀ v,
      ((Finset.univ : Finset (Fin n → Fin 2)).product (Finset.univ : Finset (Fin T))).sumFiber
        (fun p => f ((data (0, p.2)).get (finFunctionFinEquiv p.1)))
        (fun p => f ((data (1, p.2)).get (finFunctionFinEquiv p.1))) v = 0) :
    (∑ u : Fin n → Fin 2, ∑ k : Fin (T ⌈/⌉ ell),
      (helpers cfg.groups (denominatorTables f alpha data) (weightTables f data))[k.val].get
        (finFunctionFinEquiv u)) = 0 := by
  classical
  simp only [get_helpers, get_denominatorTables, get_weightTables]
  simp_rw [sum_group_rows cfg]
  have h := sum_mul_key_eq_zero
    ((Finset.univ : Finset (Fin n → Fin 2)).product (Finset.univ : Finset (Fin T)))
    (fun p => f ((data (0, p.2)).get (finFunctionFinEquiv p.1)))
    (fun p => f ((data (1, p.2)).get (finFunctionFinEquiv p.1)))
    (fun v => (alpha-v)⁻¹) hbalanced
  have h' := (Finset.sum_product (Finset.univ : Finset (Fin n → Fin 2))
    (Finset.univ : Finset (Fin T)) (fun p =>
      f ((data (1, p.2)).get (finFunctionFinEquiv p.1)) *
        (alpha - f ((data (0, p.2)).get (finFunctionFinEquiv p.1)))⁻¹)).symm.trans h
  simpa only [div_eq_mul_inv] using h'


/-- Base-field balance suffices without injectivity of the map into the challenge field. -/
theorem sum_helpers_eq_zero_of_base_balance [DecidableEq B]
    (cfg : Logup.Interaction.Config n T ell) (f : B →+* E) (alpha : E)
    (data : Fin 2 × Fin T → CMlPolynomialEval B n)
    (hbalanced : ∀ v,
      ((Finset.univ : Finset (Fin n → Fin 2)).product (Finset.univ : Finset (Fin T))).sumFiber
        (fun p => (data (0, p.2)).get (finFunctionFinEquiv p.1))
        (fun p => (data (1, p.2)).get (finFunctionFinEquiv p.1)) v = 0) :
    (∑ u : Fin n → Fin 2, ∑ k : Fin (T ⌈/⌉ ell),
      (helpers cfg.groups (denominatorTables f alpha data) (weightTables f data))[k.val].get
        (finFunctionFinEquiv u)) = 0 := by
  classical
  apply sum_helpers_eq_zero cfg f alpha data
  intro v
  apply Finset.sumFiber_comp_eq_zero
    ((Finset.univ : Finset (Fin n → Fin 2)).product (Finset.univ : Finset (Fin T)))
    (fun p => (data (0, p.2)).get (finFunctionFinEquiv p.1))
    (fun p => f ((data (1, p.2)).get (finFunctionFinEquiv p.1))) f
  intro b
  exact (Finset.sumFiber_map f.toAddMonoidHom
    ((Finset.univ : Finset (Fin n → Fin 2)).product (Finset.univ : Finset (Fin T)))
    (fun p => (data (0, p.2)).get (finFunctionFinEquiv p.1))
    (fun p => (data (1, p.2)).get (finFunctionFinEquiv p.1)) b).trans (by
      rw [hbalanced, map_zero])

end Logup.Prover
