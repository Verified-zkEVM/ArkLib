/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Lookup.Tuple.Source
public import ArkLib.Data.Polynomial.TaggedTupleProbability
public import Mathlib.Algebra.CharP.Algebra
/-!
# Tuple compression soundness and semantic balance

Semantic keys and the actual retained multiplicity weights are fixed before the fingerprint
challenge. A false lookup then has a nonzero semantic-key fiber under the explicit query-count
budget. Encoding can erase every such fiber only within the selected-key isolation bound over
original occurring keys. The argument does not union over all key pairs or reconstruction groups.

Correct indexed histograms instead balance every semantic fiber in every characteristic and
remain balanced for every challenge, including collisions. These initial-relation facts concern
fixed data and messages; they do not assume or replace an actual native protocol execution law.
-/

@[expose] public section
open CompPoly OracleComp
open scoped BigOperators ProbabilityTheory ENNReal
namespace Logup.Lookup.Tuple
section Algebra

variable {B E : Type} [CommRing B] [CommRing E]
variable {b W n M P : Nat} {schema : TaggedTuple.Schema B b W}
variable {layout : ProviderLayout b P}

/-- Occurring semantic keys include query rows and all physical table rows. -/
def PreparedProvider.occurringKeys [DecidableEq B]
    (prepared : PreparedProvider schema layout n M) : Finset schema.Key :=
  ((Finset.univ : Finset (Fin n → Fin 2)).product
    (Finset.univ : Finset (Fin (M + P)))).image
      (fun i => (prepared.keyData (finSumFinEquiv.symm i.2)).get (finFunctionFinEquiv i.1))

private theorem sum_rows_columns {R : Type} [AddCommMonoid R] {K : Nat}
    (g : Fin K → Fin (2 ^ n) → R) :
    (∑ c, ∑ u : Fin n → Fin 2, g c (finFunctionFinEquiv u)) =
      ∑ i : Fin (K * 2 ^ n), g (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2 := by
  simp_rw [finFunctionFinEquiv.sum_comp]
  rw [← Fintype.sum_prod_type (fun p => g p.1 p.2)]
  exact Fintype.sum_equiv finProdFinEquiv _ _ (by intro i; simp)

private theorem sumFiber_one_eq_count {K : Type} [DecidableEq K] {R : Type}
    [AddCommMonoidWithOne R] {L : Nat} (xs : Vector K L) (key : K) :
    Finset.univ.sumFiber (fun i : Fin L => xs[i.val]) (fun _ => (1 : R)) key =
      (xs.toList.count key : R) := by
  have h := Vector.sumFiber_cast_histogram (R := R) xs xs (Vector.ofFn id)
    (by intro i; simp) key
  simpa [Vector.getElem_histogram, Vector.toList_ofFn, List.ofFn_id, List.count_finRange] using h

/-- The table weight is fixed by the retained multiplicity before the fingerprint challenge. -/
theorem PreparedProvider.weightedData_weight_eq (prepared : PreparedProvider schema layout n M)
    (f : B →+* E) (mu : Vector (CMlPolynomialEval B n) P) (beta beta' : E) (i : Fin (M + P)) :
    prepared.weightedData f beta mu (1, i) = prepared.weightedData f beta' mu (1, i) := by
  simp [PreparedProvider.weightedData, Logup.Lookup.weightedData]

private theorem semantic_fiber_eq_sub [DecidableEq B]
    (prepared : PreparedProvider schema layout n M) (f : B →+* E)
    (mu : Vector (CMlPolynomialEval B n) P) (key : schema.Key) :
    ((Finset.univ : Finset (Fin n → Fin 2)).product
      (Finset.univ : Finset (Fin (M + P)))).sumFiber
      (fun i => (prepared.keyData (finSumFinEquiv.symm i.2)).get (finFunctionFinEquiv i.1))
      (fun i => (prepared.weightedData f 0 mu (1, i.2)).get (finFunctionFinEquiv i.1)) key =
    ((columnEntries fun q => prepared.keyData (.inl q)).toList.count key : E) -
      Finset.univ.sumFiber
        (fun i : Fin (P * 2 ^ n) => (columnEntries fun p => prepared.keyData (.inr p))[i.val])
        (fun i => f ((columnEntries fun p => mu[p.val])[i.val])) key := by
  rw [Finset.sumFiber_eq_sum_ite, Finset.product_eq_sprod, Finset.sum_product]
  simp only [PreparedProvider.weightedData, Logup.Lookup.weightedData]
  rw [Finset.sum_comm, Fin.sum_univ_add]
  simp only [finSumFinEquiv_symm_apply_castAdd, finSumFinEquiv_symm_apply_natAdd,
    Sum.elim_inl, Sum.elim_inr, show (1 : Fin 2) ≠ 0 by decide, ↓reduceIte,
    Vector.get_eq_getElem, Vector.getElem_replicate, Vector.getElem_map,
    CMlPolynomialEval.map]
  have hneg (p : Prop) [Decidable p] (a : E) :
      (if p then -a else 0) = -(if p then a else 0) := by split_ifs <;> simp
  simp_rw [hneg, Finset.sum_neg_distrib]
  rw [sum_rows_columns (fun c r =>
      if (prepared.keyData (.inl c))[r.val] = key then (1 : E) else 0),
    sum_rows_columns (fun c r =>
      if (prepared.keyData (.inr c))[r.val] = key then f mu[c.val][r.val] else 0)]
  rw [← sumFiber_one_eq_count]
  simp only [Finset.sumFiber_eq_sum_ite, columnEntries, Vector.getElem_ofFn]
  simp only [Vector.get_eq_getElem, sub_eq_add_neg]

/-- A compressed fiber is exactly the fingerprint encoding of fixed semantic-key weights. -/
theorem PreparedProvider.weighted_fiber_eq_fingerprint [DecidableEq E]
    (prepared : PreparedProvider schema layout n M) (f : B →+* E)
    (mu : Vector (CMlPolynomialEval B n) P) (beta encoded : E) :
    ((Finset.univ : Finset (Fin n → Fin 2)).product
      (Finset.univ : Finset (Fin (M + P)))).sumFiber
      (fun i => (prepared.weightedData f beta mu (0, i.2)).get (finFunctionFinEquiv i.1))
      (fun i => (prepared.weightedData f beta mu (1, i.2)).get (finFunctionFinEquiv i.1)) encoded =
    ((Finset.univ : Finset (Fin n → Fin 2)).product
      (Finset.univ : Finset (Fin (M + P)))).sumFiber
      (schema.fingerprint f beta ∘
        fun i => (prepared.keyData (finSumFinEquiv.symm i.2)).get (finFunctionFinEquiv i.1))
      (fun i => (prepared.weightedData f 0 mu (1, i.2)).get (finFunctionFinEquiv i.1)) encoded := by
  have hw : (fun i : (Fin n → Fin 2) × Fin (M + P) =>
      (prepared.weightedData f beta mu (1, i.2)).get (finFunctionFinEquiv i.1)) =
      fun i => (prepared.weightedData f 0 mu (1, i.2)).get (finFunctionFinEquiv i.1) := by
    funext i
    rw [prepared.weightedData_weight_eq f mu beta 0]
  rw [hw]
  congr 1
  funext i
  simp [PreparedProvider.weightedData, PreparedProvider.fingerprintData,
    Logup.Lookup.weightedData_value, Vector.get_eq_getElem]

/-- Zero semantic weighted fibers remain zero after every fingerprint, including collisions. -/
theorem PreparedProvider.weighted_fiber_eq_zero_of_semantic [DecidableEq B] [DecidableEq E]
    (prepared : PreparedProvider schema layout n M) (f : B →+* E)
    (mu : Vector (CMlPolynomialEval B n) P)
    (hzero : ∀ key, ((Finset.univ : Finset (Fin n → Fin 2)).product
      (Finset.univ : Finset (Fin (M + P)))).sumFiber
      (fun i => (prepared.keyData (finSumFinEquiv.symm i.2)).get (finFunctionFinEquiv i.1))
      (fun i => (prepared.weightedData f 0 mu (1, i.2)).get (finFunctionFinEquiv i.1)) key = 0)
    (beta encoded : E) :
    ((Finset.univ : Finset (Fin n → Fin 2)).product
      (Finset.univ : Finset (Fin (M + P)))).sumFiber
      (fun i => (prepared.weightedData f beta mu (0, i.2)).get (finFunctionFinEquiv i.1))
      (fun i => (prepared.weightedData f beta mu (1, i.2)).get (finFunctionFinEquiv i.1))
      encoded = 0 := by
  rw [prepared.weighted_fiber_eq_fingerprint]
  exact Finset.sumFiber_comp_eq_zero _ _ _ _ hzero encoded

/-- Correct indexed histograms balance every compressed fiber in every characteristic. -/
theorem PreparedProvider.weighted_fiber_multiplicities_eq_zero [DecidableEq E]
    (prepared : PreparedProvider schema layout n M) (f : B →+* E)
    (indices : Vector (Fin (P * 2 ^ n)) (M * 2 ^ n))
    (hvalid : ValidIndices prepared.keyData indices) (beta encoded : E) :
    ((Finset.univ : Finset (Fin n → Fin 2)).product
      (Finset.univ : Finset (Fin (M + P)))).sumFiber
      (fun i => (prepared.weightedData f beta (multiplicities indices) (0, i.2)).get
        (finFunctionFinEquiv i.1))
      (fun i => (prepared.weightedData f beta (multiplicities indices) (1, i.2)).get
        (finFunctionFinEquiv i.1)) encoded = 0 := by
  classical
  apply prepared.weighted_fiber_eq_zero_of_semantic f (multiplicities indices) ?_ beta encoded
  intro key
  rw [semantic_fiber_eq_sub, columnEntries_multiplicities]
  simp only [Vector.getElem_map, map_natCast]
  rw [Vector.sumFiber_cast_histogram _ _ indices hvalid key, sub_self]

end Algebra

variable {B E : Type} [Field B] [Field E] [DecidableEq B]
variable {b W n M P : Nat} {schema : TaggedTuple.Schema B b W}
variable {layout : ProviderLayout b P}

/-- A false semantic lookup retains a nonzero semantic weighted fiber for every fixed mu. -/
theorem exists_semantic_weighted_fiber_ne_zero
    (prepared : PreparedProvider schema layout n M) (f : B →+* E)
    (p : Nat) [CharP B p] (mu : Vector (CMlPolynomialEval B n) P)
    (hbudget : M * 2 ^ n < p) (hfalse : ¬ InLanguage prepared.keyData) :
    ∃ key, ((Finset.univ : Finset (Fin n → Fin 2)).product
      (Finset.univ : Finset (Fin (M + P)))).sumFiber
      (fun i => (prepared.keyData (finSumFinEquiv.symm i.2)).get (finFunctionFinEquiv i.1))
      (fun i => (prepared.weightedData f 0 mu (1, i.2)).get (finFunctionFinEquiv i.1)) key ≠ 0 := by
  let : CharP E p := charP_of_injective_ringHom f.injective p
  by_contra! hzero
  apply hfalse
  rw [inLanguage_iff_entries]
  apply Vector.exists_getElem_eq_of_sumFiber_eq_count_of_length_lt_char (R := E) p
    (columnEntries fun p => prepared.keyData (.inr p))
    (columnEntries fun q => prepared.keyData (.inl q))
    (fun i => f ((columnEntries fun p => mu[p.val])[i.val]))
  · intro key
    exact (sub_eq_zero.mp ((semantic_fiber_eq_sub prepared f mu key).symm.trans (hzero key))).symm
  · exact hbudget

variable [Fintype E] [SampleableType E] [DecidableEq E]

/-- Fixed pre-challenge multiplicities compress a false semantic lookup to balanced fibers
only with the selected-key isolation error over the original occurring key set. -/
theorem prob_weightedData_balanced_le (prepared : PreparedProvider schema layout n M)
    (f : B →+* E) (p : Nat) [CharP B p] (mu : Vector (CMlPolynomialEval B n) P)
    (hbudget : M * 2 ^ n < p) (hfalse : ¬ InLanguage prepared.keyData) :
    Pr{let beta ← $ᵗ E}[∀ encoded,
      ((Finset.univ : Finset (Fin n → Fin 2)).product
        (Finset.univ : Finset (Fin (M + P)))).sumFiber
        (fun i => (prepared.weightedData f beta mu (0, i.2)).get (finFunctionFinEquiv i.1))
        (fun i => (prepared.weightedData f beta mu (1, i.2)).get (finFunctionFinEquiv i.1))
        encoded = 0] ≤
      (((prepared.occurringKeys.card - 1) * W : Nat) : ℝ≥0∞) / Fintype.card E := by
  have hfalseFiber := exists_semantic_weighted_fiber_ne_zero prepared f p mu hbudget hfalse
  have hprob := schema.prob_fingerprint_balanced_le f f.injective
    ((Finset.univ : Finset (Fin n → Fin 2)).product
      (Finset.univ : Finset (Fin (M + P))))
    (fun i => (prepared.keyData (finSumFinEquiv.symm i.2)).get (finFunctionFinEquiv i.1))
    (fun i => (prepared.weightedData f 0 mu (1, i.2)).get (finFunctionFinEquiv i.1)) hfalseFiber
  simpa only [prepared.weighted_fiber_eq_fingerprint f mu,
    PreparedProvider.occurringKeys] using hprob

end Logup.Lookup.Tuple
