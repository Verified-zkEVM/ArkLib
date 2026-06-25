/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/

import ArkLib.Commitments.Functional.KZG.FunctionBinding.Support

/-!
# Degree-Conflict Branch for KZG Function Binding

Branch-specific interpolation search and ARSDH extraction when the deduplicated transcript has no
degree-`n` interpolant, following the ARSDH reduction in [CGKY25].

## Notation

* `queryReps` selects one representative for each queried point.
* `findA` and `findS` implement the finite searches used by the degree-conflict branch.
* `function_binding_interpolation_branch_maps_to_arsdh` is the branch proof.

## References

* [Chiesa, A., Guan, Z., Knabenhans, C., and Yu, Z.,
  *On the Fiat-Shamir Security of Succinct Arguments from Functional Commitments*][CGKY25]
-/

open CompPoly CompPoly.CPolynomial

namespace KZG

variable {G : Type} [Group G] {p : outParam ℕ} [hp : Fact (Nat.Prime p)]
  [PrimeOrderWith G p] {g : G}

variable {G₁ : Type} [Group G₁] [PrimeOrderWith G₁ p] [DecidableEq G₁] {g₁ : G₁}
  {G₂ : Type} [Group G₂] [PrimeOrderWith G₂ p] {g₂ : G₂}
  {Gₜ : Type} [Group Gₜ] [PrimeOrderWith Gₜ p] [DecidableEq Gₜ]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)]
  [Module (ZMod p) (Additive Gₜ)]
  (pairing : (Additive G₁) →ₗ[ZMod p] (Additive G₂) →ₗ[ZMod p] (Additive Gₜ))

variable {n : ℕ} -- the maximal degree of polynomials that can be committed to/opened.

open Commitment

/-- Local oracle interface for evaluating coefficient vectors as computable polynomials. -/
local instance functionBindingDegreeConflictOracleInterface :
    OracleInterface (Fin (n + 1) → ZMod p) where
  Query := ZMod p
  toOC.spec := ZMod p →ₒ ZMod p
  toOC.impl z := do return (CPolynomial.ofFn (← read)).eval z

open scoped NNReal

namespace CommitmentScheme

open OracleSpec _root_.OracleComp SubSpec ProtocolSpec

section FunctionBinding

omit hp [PrimeOrderWith G₁ p] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
/-- If no query matches the second SRS power, then no query is equal to `τ`. -/
lemma query_ne_tau_of_find_query_with_srs_power_none {L : ℕ}
    (hn : 1 ≤ n) (τ : ZMod p) (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (queryOf : Fin L → ZMod p)
    (hsrs : srs = Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ)
    (hfs_none : List.findSome?
        (fun i ↦ if srs.1[0] ^ (queryOf i).val
                      = srs.1[1]'(Nat.lt_add_of_pos_left hn)
                  then some (queryOf i) else none)
        (List.finRange L) = none) :
    ∀ i : Fin L, queryOf i ≠ τ := by
  intro i hqτ
  have hall := List.findSome?_eq_none_iff.mp hfs_none
  have h_at_i := hall i (List.mem_finRange i)
  have h_srs0 : srs.1[0] = g₁ := by
    rw [hsrs]
    simp [Groups.PowerSrs.generate, Groups.PowerSrs.tower]
  have h_srs1 : srs.1[1]'(Nat.lt_add_of_pos_left hn) = g₁ ^ τ.val := by
    rw [hsrs]
    simp [Groups.PowerSrs.generate, Groups.PowerSrs.tower]
  have hpow : srs.1[0] ^ (queryOf i).val = srs.1[1]'(Nat.lt_add_of_pos_left hn) := by
    rw [h_srs0, h_srs1, hqτ]
  simp [hpow] at h_at_i

/-- If no degree-`n` coefficient vector fits the data, interpolation has degree at least `n + 1`. -/
lemma interpolate_degree_ge_of_no_data {n L : ℕ} (S : Finset (Fin L))
    {queryOf responseOf : Fin L → ZMod p}
    (hquery : Set.InjOn queryOf ↑S)
    (hNoData : ¬ ∃ d : Fin (n + 1) → ZMod p,
      ∀ i ∈ S, (CPolynomial.ofFn d).eval (queryOf i) = responseOf i) :
    (↑(n + 1) : WithBot ℕ) ≤
      (CLagrange.interpolate S queryOf responseOf).degree := by
  by_contra hlt
  push Not at hlt
  set Q : Polynomial (ZMod p) :=
    Lagrange.interpolate S queryOf responseOf with hQ_def
  have hQdeg_lt : Q.degree < (↑(n + 1) : WithBot ℕ) := by
    have h := hlt
    rw [show
        (CLagrange.interpolate S
          queryOf responseOf).degree
          = Q.degree from by
          rw [hQ_def, ← CLagrange.cinterpolate_eq_interpolate, ← degree_toPoly]] at h
    exact h
  have hQ_mem : Q ∈ Polynomial.degreeLT (ZMod p) (n + 1) :=
    Polynomial.mem_degreeLT.mpr hQdeg_lt
  apply hNoData
  refine ⟨Polynomial.degreeLTEquiv (ZMod p) (n + 1) ⟨Q, hQ_mem⟩, ?_⟩
  intro i hi
  have hQ_eval : Q.eval (queryOf i) = responseOf i := by
    rw [hQ_def]
    exact Lagrange.eval_interpolate_at_node responseOf
      hquery hi
  have hQ_sum :
      Q.eval (queryOf i) =
        ∑ k : Fin (n + 1),
          Polynomial.degreeLTEquiv (ZMod p) (n + 1) ⟨Q, hQ_mem⟩ k *
            (queryOf i) ^ (k : ℕ) :=
    Polynomial.eval_eq_sum_degreeLTEquiv hQ_mem (queryOf i)
  set d : Fin (n + 1) → ZMod p :=
    Polynomial.degreeLTEquiv (ZMod p) (n + 1) ⟨Q, hQ_mem⟩ with hd_def
  let P_C : CPolynomial (ZMod p) :=
    ⟨(CompPoly.CPolynomial.Raw.mk (Array.ofFn d)).trim,
      CompPoly.CPolynomial.Raw.Trim.isCanonical_trim _⟩
  change CPolynomial.eval (queryOf i) P_C = responseOf i
  rw [eval_toPoly]
  have hPC_eq : P_C.toPoly = Q := by
    apply Polynomial.ext
    intro k
    rw [← coeff_toPoly]
    change ((CompPoly.CPolynomial.Raw.mk (Array.ofFn d)).trim).coeff k = Q.coeff k
    rw [CompPoly.CPolynomial.Raw.Trim.coeff_eq_coeff]
    change (Array.ofFn d).getD k 0 = Q.coeff k
    rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn]
    by_cases hk : k < n + 1
    · simp [hk, hd_def, Polynomial.degreeLTEquiv]
    · push Not at hk
      simp only [hk.not_gt, dite_false, Option.getD_none]
      symm
      exact Polynomial.coeff_eq_zero_of_degree_lt
        (lt_of_lt_of_le hQdeg_lt (by exact_mod_cast hk))
  rw [hPC_eq]
  exact hQ_eval

/-- A high interpolation degree forces the interpolation set to have more than `n + 1` points. -/
lemma finset_card_gt_of_interpolate_degree_ge {n L : ℕ} (S : Finset (Fin L))
    (queryOf : Fin L → ZMod p) (responseOf : Fin L → ZMod p)
    (hquery : Set.InjOn queryOf ↑S)
    (hS_deg : (↑(n + 1) : WithBot ℕ) ≤
      (CLagrange.interpolate S queryOf responseOf).degree) :
    n + 1 < S.card := by
  have h_lt :=
    Lagrange.degree_interpolate_lt responseOf
      hquery
  have h_ge : (↑(n + 1) : WithBot ℕ) ≤
      (Lagrange.interpolate S
        queryOf responseOf).degree := by
    have h := hS_deg
    rwa [show
        (CLagrange.interpolate S
          queryOf responseOf).degree
          = (Lagrange.interpolate S
              queryOf responseOf).degree from by
          rw [← CLagrange.cinterpolate_eq_interpolate, ← degree_toPoly]] at h
  have h_card_gt :
      (↑(n + 1) : WithBot ℕ) < (S.card : WithBot ℕ) :=
    lt_of_le_of_lt h_ge h_lt
  exact_mod_cast h_card_gt

/-! ### Interpolation Branch -/

/- First, deduplicate the queries to obtain an injective query mapping used for interpolation. -/

/-- One representative index for every distinct query value. -/
def queryReps {L : ℕ} (query : Fin L → ZMod p) : Finset (Fin L) :=
  Finset.univ.filter fun i => ∀ j : Fin L, query j = query i → i ≤ j

omit hp in
/-- The selected query representatives have pairwise distinct query values. -/
lemma queryReps_injOn {L : ℕ} (query : Fin L → ZMod p) :
    Set.InjOn query ↑(queryReps query) := by
  intro i hi j hj hq
  have hi' : ∀ k : Fin L, query k = query i → i ≤ k := by
    simpa [queryReps] using hi
  have hj' : ∀ k : Fin L, query k = query j → j ≤ k := by
    simpa [queryReps] using hj
  exact le_antisymm (hi' j hq.symm) (hj' i hq)

omit hp in
/-- Every query value is represented by some index in `queryReps`. -/
lemma queryReps_exists {L : ℕ} (query : Fin L → ZMod p) (i : Fin L) :
    ∃ j ∈ queryReps query, query j = query i := by
  let same : Finset (Fin L) := Finset.univ.filter fun j => query j = query i
  have hsame_nonempty : same.Nonempty := ⟨i, by simp [same]⟩
  let j := same.min' hsame_nonempty
  have hjsame : j ∈ same := Finset.min'_mem same hsame_nonempty
  have hjquery : query j = query i := (Finset.mem_filter.mp hjsame).2
  refine ⟨j, ?_, hjquery⟩
  simp only [queryReps, Finset.mem_filter, Finset.mem_univ, true_and]
  intro k hk
  exact Finset.min'_le same k (by simp [same, hk.trans hjquery])

/-- Function-binding failure rules out fitting the deduplicated query representatives. -/
lemma no_data_queryReps_of_function_binding_cond {n L : ℕ}
    {queryOf responseOf : Fin L → ZMod p} {accepts : Fin L → Bool}
    (hFBcond : Commitment.functionBindingCondition (Data := Fin (n + 1) → ZMod p)
      ⟨queryOf, responseOf, accepts⟩)
    (hfc : findConflict queryOf responseOf = none) :
    ¬ ∃ d : Fin (n + 1) → ZMod p,
      ∀ i ∈ queryReps queryOf, (CPolynomial.ofFn d).eval (queryOf i) = responseOf i := by
  intro h
  apply hFBcond.2
  obtain ⟨d, hd⟩ := h
  refine ⟨d, ?_⟩
  intro i _
  obtain ⟨j, hj, hq⟩ := queryReps_exists queryOf i
  have hresp : responseOf j = responseOf i :=
    response_eq_of_find_conflict_none queryOf responseOf hfc hq
  rw [← hq]
  change (CPolynomial.ofFn d).eval (queryOf j) = responseOf i
  rw [hd j hj, hresp]

/-- Step 4a (from the paper reduction):
    find a subset whose interpolation polynomial has degree `n`. -/
def findA {L : ℕ} (U : Finset (Fin L)) (n : ℕ)
    (query : Fin L → ZMod p) (response : Fin L → ZMod p) :
    Option (Finset (Fin L)) :=
  let candidateslist := (U.sort (· ≤ ·)).sublistsLen (n + 1)
  let candidates := candidateslist.map List.toFinset
  candidates.find? fun s => (CLagrange.interpolate s query response).degree = n

/-- A successful `findA` result is a subset of the search universe. -/
lemma find_a_subset {L : ℕ} (U A : Finset (Fin L)) (n : ℕ)
    (query : Fin L → ZMod p) (response : Fin L → ZMod p)
    (hres : some A = findA U n query response) :
    A ⊆ U := by
  unfold findA at hres
  have hmem := List.mem_of_find?_eq_some hres.symm
  rw [List.mem_map] at hmem
  obtain ⟨l, hl_mem, hl_eq⟩ := hmem
  rw [List.mem_sublistsLen] at hl_mem
  obtain ⟨hl_sub, _⟩ := hl_mem
  intro x hx
  rw [← hl_eq] at hx
  have hx_l : x ∈ l := by simpa using hx
  simpa using (hl_sub.subset hx_l)

/-- A successful `findA` result has cardinality `n + 1`. -/
lemma find_a_card {L : ℕ} (U A : Finset (Fin L)) (n : ℕ)
    (query : Fin L → ZMod p) (response : Fin L → ZMod p)
    (hres : some A = findA U n query response) :
    A.card = n + 1 := by
  unfold findA at hres
  have hmem := List.mem_of_find?_eq_some hres.symm
  rw [List.mem_map] at hmem
  obtain ⟨l, hl_mem, hl_eq⟩ := hmem
  rw [List.mem_sublistsLen] at hl_mem
  obtain ⟨hl_sub, hl_len⟩ := hl_mem
  rw [← hl_eq, List.toFinset_card_of_nodup ((U.sort_nodup (· ≤ ·)).sublist hl_sub), hl_len]

/-- A successful `findA` result has interpolation degree exactly `n`. -/
lemma find_a_deg {L : ℕ} (U A : Finset (Fin L)) (n : ℕ)
    (query : Fin L → ZMod p) (response : Fin L → ZMod p)
    (hres : some A = findA U n query response) :
    (CLagrange.interpolate A query response).degree = n := by
  unfold findA at hres
  have hpred := List.find?_some hres.symm
  simp only [decide_eq_true_eq] at hpred
  exact hpred

/-- Sorted finite-set inclusion gives a sublist relation between sorted lists. -/
lemma sorted_finset_sort_sublist_sort {L : ℕ} (S A : Finset (Fin L)) (hSA : S ⊆ A) :
    List.Sublist (S.sort (· ≤ ·)) (A.sort (· ≤ ·)) :=
  List.sublist_of_subperm_of_sortedLE
    ((Finset.sort_nodup (s := S) (r := (· ≤ ·))).subperm
      (fun x hx => by simpa using hSA (by simpa using hx)))
    (Finset.sortedLT_sort S).sortedLE
    (Finset.sortedLT_sort A).sortedLE

/-- A subset with the requested cardinality appears in the `sublistsLen` candidate list. -/
lemma finset_subset_mem_sublists_len_map {L : ℕ} (S A : Finset (Fin L))
    (hSA : S ⊆ A) (hn : S.card = n) :
    S ∈ ((A.sort (· ≤ ·)).sublistsLen n).map List.toFinset := by
  rw [List.mem_map]
  exact ⟨S.sort (· ≤ ·), List.mem_sublistsLen.mpr
    ⟨sorted_finset_sort_sublist_sort S A hSA,
     by rw [Finset.length_sort]; exact hn⟩,
    Finset.sort_toFinset (s := S) (r := (· ≤ ·))⟩

/-- Interpolation over `n + 1` injective points has degree at most `n`. -/
lemma interp_degree_le_of_card {L : ℕ} (s : Finset (Fin L))
    (query : Fin L → ZMod p) (response : Fin L → ZMod p)
    (hquery : Set.InjOn query ↑s) (hn : s.card = n + 1) :
    (CLagrange.interpolate s query response).degree ≤ ↑n := by
  rw [degree_toPoly, CLagrange.cinterpolate_eq_interpolate]
  have hle : (Lagrange.interpolate s query response).degree ≤ ↑(s.card - 1) :=
    Lagrange.degree_interpolate_le response hquery
  simp only [hn, Nat.add_sub_cancel] at hle
  exact hle

/-- If the interpolation over `U` has degree at least `n`, then `findA` succeeds. -/
lemma find_a_successful {L : ℕ} (U : Finset (Fin L)) (n : ℕ)
    (query : Fin L → ZMod p) (response : Fin L → ZMod p)
    (hUcard : n < U.card) (hqueryU : Set.InjOn query ↑U)
    (hinterp : (CLagrange.interpolate U query response).degree ≥ n) :
    (findA U n query response).isSome := by
  by_contra h_not
  have h_none : findA U n query response = none := by
    match hc : findA U n query response with
    | none => rfl
    | some _ => simp [hc] at h_not
  unfold findA at h_none
  rw [List.find?_eq_none] at h_none
  simp only [decide_eq_true_eq] at h_none
  have h_deg_lt : ∀ (s : Finset (Fin L)), s ⊆ U → s.card = n + 1 →
      (CLagrange.interpolate s query response).degree < ↑n := by
    intro s hsU hs
    exact lt_of_le_of_ne
      (interp_degree_le_of_card s query response (hqueryU.mono hsU) hs)
      (h_none s (finset_subset_mem_sublists_len_map s U hsU hs))
  -- Core argument: construct a polynomial of degree < n agreeing with all L values
  -- Pick a subset T of size n
  obtain ⟨T, hTU, hTcard⟩ :=
    Finset.exists_subset_card_eq (n := n) (s := U) (by omega)
  -- Let Q_T be the Mathlib interpolation over T
  set Q_T := Lagrange.interpolate T query response with hQ_T_def
  have hQ_T_deg : Q_T.degree < ↑n := by
    rw [← hTcard]
    exact Lagrange.degree_interpolate_lt response (hqueryU.mono hTU)
  -- Show Q_T agrees with response on all of Fin L
  have hQ_T_eval : ∀ i ∈ U, Q_T.eval (query i) = response i := by
    intro i hiU
    by_cases hiT : i ∈ T
    · exact Lagrange.eval_interpolate_at_node response (hqueryU.mono hTU) hiT
    · -- Use the `(n + 1)`-subset `T ∪ {i}`.
      set Si := insert i T with hSi_def
      have hSiU : Si ⊆ U := by
        intro x hx
        simp only [hSi_def, Finset.mem_insert] at hx
        rcases hx with rfl | hxT
        · exact hiU
        · exact hTU hxT
      have hSicard : Si.card = n + 1 := by
        rw [Finset.card_insert_of_notMem hiT, hTcard]
      -- The interpolation over Si also has degree < n (via CPolynomial bridge)
      have hSi_deg_lt : (CLagrange.interpolate Si query response).degree < ↑n :=
        h_deg_lt Si hSiU hSicard
      -- Transfer to Polynomial world
      set Q_Si := Lagrange.interpolate Si query response with hQ_Si_def
      have hQ_Si_deg : Q_Si.degree < ↑n := by
        have h := hSi_deg_lt
        rw [degree_toPoly, CLagrange.cinterpolate_eq_interpolate] at h
        exact h
      -- Q_T and Q_Si agree on T
      have hagree : ∀ j ∈ T, Q_T.eval (query j) = Q_Si.eval (query j) := by
        intro j hjT
        rw [Lagrange.eval_interpolate_at_node response (hqueryU.mono hTU) hjT,
            Lagrange.eval_interpolate_at_node response
              (hqueryU.mono hSiU)
              (Finset.mem_insert_of_mem hjT)]
      -- By uniqueness (both degree < |T| = n, agree on T), Q_T = Q_Si
      have hTn : (↑n : WithBot ℕ) = ↑(T.card) := by
        rw [hTcard]
      have heq : Q_T = Q_Si := by
        rw [hTn] at hQ_T_deg hQ_Si_deg
        exact Polynomial.eq_of_degrees_lt_of_eval_index_eq T
          (hqueryU.mono hTU) hQ_T_deg hQ_Si_deg hagree
      -- Hence Q_T.eval(query i) = Q_Si.eval(query i) = response i
      rw [heq]
      exact Lagrange.eval_interpolate_at_node response
        (hqueryU.mono hSiU) (Finset.mem_insert_self i T)
  -- Derive n < U.card from hinterp and degree_interpolate_lt
  have hinterp_poly : (Lagrange.interpolate U query response).degree ≥ ↑n := by
    have h := hinterp
    rw [degree_toPoly, CLagrange.cinterpolate_eq_interpolate] at h
    exact h
  have hScard_gt : n < U.card := by
    have h2 : (Lagrange.interpolate U query response).degree < ↑U.card :=
      Lagrange.degree_interpolate_lt response hqueryU
    exact_mod_cast lt_of_le_of_lt hinterp_poly h2
  -- Q_T = interpolation over U, since Q_T has degree < U.card and agrees on U
  have hQ_T_deg_S : Q_T.degree < ↑U.card :=
    lt_trans hQ_T_deg (by exact_mod_cast hScard_gt)
  have hP_eq : Q_T = Lagrange.interpolate U query response :=
    Lagrange.eq_interpolate_of_eval_eq (s := U) response
      hqueryU hQ_T_deg_S hQ_T_eval
  -- Contradiction: interp over S has degree ≥ n but Q_T has degree < n
  exact absurd (hP_eq ▸ hQ_T_deg) (not_lt.mpr hinterp_poly)

/-- Step 4b (from the paper reduction): find a subset whose interpolation commitment differs from
the adversary's commitment `c`. -/
def findS {L : ℕ} (n : ℕ) (A : Finset (Fin L)) (c : G₁)
    (srs : Vector G₁ (n + 1) × Vector G₂ 2) (query : Fin L → ZMod p)
    (response : Fin L → ZMod p) :
    Option (Finset (Fin L)) :=
  let candidateslist := (A.sort (· ≤ ·)).sublistsLen (n + 1)
  let candidates := candidateslist.map List.toFinset
  candidates.find? fun s =>
    commit srs.1 ((CLagrange.interpolate s query response).val.coeff ∘ Fin.val) ≠ c

/-- Some `n + 1` subset has interpolation value at `τ` different from `c`. -/
lemma find_s_existence {L : ℕ} (n : ℕ) (τ c : ZMod p) (A : Finset (Fin L))
    (query : Fin L → ZMod p) (response : Fin L → ZMod p)
    (hA : (CLagrange.interpolate A query response).degree = n + 1)
    (hquery : Set.InjOn query ↑A) (hn : 1 ≤ n) :
    ∃ S ⊆ A, S.card = n + 1
      ∧ (CLagrange.interpolate S query response).eval τ ≠ c := by
  by_contra h_all
  push Not at h_all
  -- Bridge h_all to Polynomial world
  have h_poly : ∀ S ⊆ A, S.card = n + 1 →
      (Lagrange.interpolate S query response).eval τ = c := by
    intro S hS hcard
    have h := h_all S hS hcard
    rwa [eval_toPoly, CLagrange.cinterpolate_eq_interpolate] at h
  -- Bridge hA to Polynomial world
  have hA_poly : (Lagrange.interpolate A query response).degree = ↑(n + 1) := by
    rw [← CLagrange.cinterpolate_eq_interpolate, ← degree_toPoly]; exact_mod_cast hA
  -- Step A: n + 1 < A.card
  have hn_lt : n + 1 < A.card := by
    have h := Lagrange.degree_interpolate_lt response hquery
    rw [hA_poly] at h; exact_mod_cast h
  -- Step B: Pick A' ⊆ A with |A'| = n + 2
  obtain ⟨A', hA'_sub, hA'_card⟩ :=
    Finset.exists_subset_card_eq (show n + 2 ≤ A.card by omega)
  -- Step C: interpolate A = interpolate A' (by uniqueness, since deg < |A'| and agrees on A')
  have hA'_eq : Lagrange.interpolate A query response =
      Lagrange.interpolate A' query response :=
    Lagrange.eq_interpolate_of_eval_eq response
      (hquery.mono hA'_sub)
      (by rw [hA_poly, hA'_card]; exact_mod_cast (show n + 1 < n + 2 by omega))
      (fun i hi => Lagrange.eval_interpolate_at_node response
        hquery (hA'_sub hi))
  -- Degree of interpolate A' equals n + 1
  have hA'_deg : (Lagrange.interpolate A' query response).degree = ↑(n + 1) := by
    rw [← hA'_eq]; exact hA_poly
  -- Step D: Pick two distinct elements `i`, `j ∈ A'` (possible since `|A'| = n + 2 ≥ 2`).
  obtain ⟨i, j, hi, hj, hij⟩ := Finset.one_lt_card_iff.mp (show 1 < A'.card by omega)
  -- Erase subset/cardinality facts
  have hej_sub : A'.erase j ⊆ A := (Finset.erase_subset j A').trans hA'_sub
  have hei_sub : A'.erase i ⊆ A := (Finset.erase_subset i A').trans hA'_sub
  have hej_card : (A'.erase j).card = n + 1 := by
    rw [Finset.card_erase_of_mem hj, hA'_card]; omega
  have hei_card : (A'.erase i).card = n + 1 := by
    rw [Finset.card_erase_of_mem hi, hA'_card]; omega
  -- Step E: Show (interpolate A').eval τ = c via decomposition
  --   PA' = P_{A'\j} · basisDivisor(qi,qj) + P_{A'\i} · basisDivisor(qj,qi)
  --   Evaluating at τ and using h_poly gives c · (bd + bd') = c · 1 = c
  have hA'_eval_tau : (Lagrange.interpolate A' query response).eval τ = c := by
    have hdecomp := Lagrange.interpolate_eq_add_interpolate_erase response
      (hquery.mono hA'_sub) hi hj hij
    have h1 := congr_arg (Polynomial.eval τ) hdecomp
    simp only [Polynomial.eval_add, Polynomial.eval_mul] at h1
    rw [h_poly (A'.erase j) hej_sub hej_card,
        h_poly (A'.erase i) hei_sub hei_card] at h1
    rw [h1, ← _root_.mul_add, ← Polynomial.eval_add,
        Lagrange.basisDivisor_add_symm
          (show query i ≠ query j from fun h => hij (hquery (hA'_sub hi) (hA'_sub hj) h))]
    simp
  -- Step F: Choose k ∈ A' such that τ ∉ (A'.erase k).image query
  obtain ⟨k, hk, hk_fresh⟩ : ∃ k ∈ A', τ ∉ (A'.erase k).image query := by
    by_cases hτ : ∃ k ∈ A', query k = τ
    · obtain ⟨k, hk, hkq⟩ := hτ
      exact ⟨k, hk, by
        simp only [Finset.mem_image]
        rintro ⟨x, hxe, hxq⟩
        exact Finset.ne_of_mem_erase hxe
          (hquery (hA'_sub (Finset.mem_of_mem_erase hxe)) (hA'_sub hk)
            (hxq.trans hkq.symm))⟩
    · push Not at hτ
      obtain ⟨k, hk⟩ := Finset.card_pos.mp (show 0 < A'.card by omega)
      exact ⟨k, hk, by
        simp only [Finset.mem_image]
        rintro ⟨x, hxe, hxq⟩
        exact hτ x (Finset.mem_of_mem_erase hxe) hxq⟩
  -- Erase-k facts
  have hek_card : (A'.erase k).card = n + 1 := by
    rw [Finset.card_erase_of_mem hk, hA'_card]; omega
  have hek_sub : A'.erase k ⊆ A := (Finset.erase_subset k A').trans hA'_sub
  -- Degree of interpolate (A'.erase k) < n + 1
  have h_deg_ek : (Lagrange.interpolate (A'.erase k) query response).degree < ↑(n + 1) := by
    rw [← hek_card]
    exact Lagrange.degree_interpolate_lt response
      (hquery.mono ((Finset.erase_subset k A').trans hA'_sub))
  -- Step G: The difference polynomial vanishes at `n + 2` distinct field values, so it is zero.
  have hQ_zero : Lagrange.interpolate A' query response -
      Lagrange.interpolate (A'.erase k) query response = 0 := by
    apply Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero
      ((A'.erase k).image query ∪ {τ})
    · -- degree < |T|
      have hT_card : ((A'.erase k).image query ∪ {τ}).card = n + 2 := by
        rw [Finset.card_union_of_disjoint (Finset.disjoint_singleton_right.mpr hk_fresh),
            Finset.card_image_of_injOn
              (hquery.mono ((Finset.erase_subset k A').trans hA'_sub)),
            hek_card, Finset.card_singleton]
      rw [hT_card]
      calc (Lagrange.interpolate A' query response -
              Lagrange.interpolate (A'.erase k) query response).degree
          ≤ max (Lagrange.interpolate A' query response).degree
                (Lagrange.interpolate (A'.erase k) query response).degree :=
            Polynomial.degree_sub_le _ _
        _ ≤ ↑(n + 1) := max_le (le_of_eq hA'_deg) (le_of_lt h_deg_ek)
        _ < ↑(n + 2) := by exact_mod_cast (show n + 1 < n + 2 by omega)
    · -- vanishes on T
      intro x hx
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_singleton] at hx
      rw [Polynomial.eval_sub, sub_eq_zero]
      rcases hx with ⟨m, hm, rfl⟩ | rfl
      · rw [Lagrange.eval_interpolate_at_node response
              (hquery.mono hA'_sub) (Finset.mem_of_mem_erase hm),
            Lagrange.eval_interpolate_at_node response
              (hquery.mono ((Finset.erase_subset k A').trans hA'_sub)) hm]
      · rw [hA'_eval_tau, h_poly (A'.erase k) hek_sub hek_card]
  -- But they can't be equal (degrees n vs < n)
  have hne : Lagrange.interpolate A' query response ≠
      Lagrange.interpolate (A'.erase k) query response := by
    intro h
    rw [h] at hA'_deg
    exact absurd hA'_deg (ne_of_lt h_deg_ek)
  exact hne (sub_eq_zero.mp hQ_zero)

omit [PrimeOrderWith G₂ p] [Module (ZMod p) (Additive G₁)]
  [Module (ZMod p) (Additive G₂)] in
/-- Under the degree hypotheses, `findS` finds a diverging subset. -/
lemma find_s_successful {L : ℕ} (n : ℕ) (τ : ZMod p) (c : G₁) (A : Finset (Fin L))
    (query : Fin L → ZMod p) (response : Fin L → ZMod p)
    (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hsrs : srs = Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ)
    (hgen : srs.1[0] ≠ 1)
    (hA : (CLagrange.interpolate A query response).degree = n + 1)
    (hquery : Set.InjOn query ↑A) (hn : 1 ≤ n) :
    (findS n A c srs query response).isSome := by
  by_contra h_not
  have h_none : findS n A c srs query response = none := by
    match hc : findS n A c srs query response with
    | none => rfl
    | some _ => simp [hc] at h_not
  unfold findS at h_none
  rw [List.find?_eq_none] at h_none
  simp only [decide_eq_true_eq, not_not] at h_none
  have hg₁ : g₁ ≠ 1 :=
    Groups.PowerSrs.generator_ne_one_of_generate (g₁ := g₁) (g₂ := g₂) hsrs hgen
  have hpG1 : Nat.card G₁ = p := PrimeOrderWith.hCard
  have hord : orderOf g₁ = p := Groups.orderOf_eq_prime_of_ne_one g₁ hg₁
  obtain ⟨c', hc_eq⟩ := Groups.exists_zmod_power_of_generator hpG1 hg₁ hord c
  -- For every candidate S, commit = c means eval τ = c'
  have h_all_eq : ∀ S ⊆ A, S.card = n + 1 →
      (CLagrange.interpolate S query response).eval τ = c' := by
    intro S hSA hScard
    -- S is in the candidate list
    have hS_mem := finset_subset_mem_sublists_len_map S A hSA hScard
    -- The hypothesis says commit = c for S
    have hcommit_eq := h_none S hS_mem
    -- Degree bound for interpolation over S
    have hdeg : (CLagrange.interpolate S query response).degree ≤ ↑n :=
      interp_degree_le_of_card S query response (hquery.mono hSA) hScard
    -- Rewrite commit using commit_eq_c_polynomial
    have hcommit_rw : commit srs.1 ((CLagrange.interpolate S query response).val.coeff ∘ Fin.val)
        = g₁ ^ ((CLagrange.interpolate S query response).eval τ).val := by
      conv_lhs => rw [hsrs, Groups.PowerSrs.generate]
      exact commit_eq_c_polynomial (g₁ := g₁) hpG1
        (CLagrange.interpolate S query response) hdeg
    -- So g₁ ^ (eval τ ...).val = g₁ ^ c'.val
    rw [hcommit_rw, hc_eq] at hcommit_eq
    -- Injectivity: g₁ ^ a = g₁ ^ b with a, b < orderOf g₁ implies a = b
    have hinj : ((CLagrange.interpolate S query response).eval τ).val = c'.val :=
      pow_injOn_Iio_orderOf
        (show ((CLagrange.interpolate S query response).eval τ).val ∈ Set.Iio (orderOf g₁)
          from by rw [hord]; exact ZMod.val_lt _)
        (show c'.val ∈ Set.Iio (orderOf g₁)
          from by rw [hord]; exact ZMod.val_lt _)
        hcommit_eq
    exact ZMod.val_injective p hinj
  -- But find_s_existence gives an S with eval τ ≠ c'
  obtain ⟨S₀, hS₀_sub, hS₀_card, hS₀_ne⟩ :=
    find_s_existence n τ c' A query response hA hquery hn
  exact hS₀_ne (h_all_eq S₀ hS₀_sub hS₀_card)

omit [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
/-- A successful `findS` result has cardinality `n + 1`. -/
lemma find_s_card
    {L : ℕ} (n : ℕ) (c : G₁) (A S : Finset (Fin L))
    (srs : Vector G₁ (n + 1) × Vector G₂ 2) (query : Fin L → ZMod p)
    (response : Fin L → ZMod p) (hres : some (S) = findS n A c srs query response) :
    S.card = n + 1 := by
    unfold findS at hres
    have hS_mem := List.mem_of_find?_eq_some hres.symm
    rw [List.mem_map] at hS_mem
    obtain ⟨l, hl_mem, hl_eq⟩ := hS_mem
    rw [List.mem_sublistsLen] at hl_mem
    obtain ⟨hl_sub, hl_len⟩ := hl_mem
    rw [← hl_eq, List.toFinset_card_of_nodup ((A.sort_nodup (· ≤ ·)).sublist hl_sub), hl_len]

omit [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
/-- A successful `findS` result is a subset of the input set. -/
lemma find_s_subset
    {L : ℕ} (n : ℕ) (c : G₁) (A S : Finset (Fin L))
    (srs : Vector G₁ (n + 1) × Vector G₂ 2) (query : Fin L → ZMod p)
    (response : Fin L → ZMod p) (hres : some S = findS n A c srs query response) :
    S ⊆ A := by
  unfold findS at hres
  have hS_mem := List.mem_of_find?_eq_some hres.symm
  rw [List.mem_map] at hS_mem
  obtain ⟨l, hl_mem, hl_eq⟩ := hS_mem
  rw [List.mem_sublistsLen] at hl_mem
  obtain ⟨hl_sub, _⟩ := hl_mem
  intro x hx
  rw [← hl_eq] at hx
  have hx_l : x ∈ l := by simpa using hx
  simpa using (hl_sub.subset hx_l)

omit [Group G₂] [PrimeOrderWith G₂ p]
  [Module (ZMod p) (Additive G₁)] [Module (ZMod p) (Additive G₂)] in
/-- A successful `findS` result has a commitment different from the adversary's commitment. -/
lemma find_s_diverges
    {L : ℕ} (n : ℕ) (c : G₁) (A S : Finset (Fin L))
    (query : Fin L → ZMod p) (response : Fin L → ZMod p)
    (srs : Vector G₁ (n + 1) × Vector G₂ 2)
    (hres : some (S) = findS n A c srs query response) :
    commit srs.1 ((CLagrange.interpolate S query response).val.coeff ∘ Fin.val) ≠ c := by
  unfold findS at hres
  have h := List.find?_some hres.symm
  simp only [decide_eq_true_eq] at h
  exact h

/-- Convert the computable vanishing product on query images to `Lagrange.nodal`. -/
lemma zs_to_poly_eq_nodal {L : ℕ} (S : Finset (Fin L))
    (query : Fin L → ZMod p) (hquery : Set.InjOn query ↑S) :
    (∏ s ∈ S.image query, (X - C s) : CPolynomial (ZMod p)).toPoly
      = Lagrange.nodal S query := by
  rw [toPoly_prod]
  simp only [CPolynomial.toPoly_sub, X_toPoly, C_toPoly]
  rw [Lagrange.nodal_eq]
  exact Finset.prod_image (f := fun s => Polynomial.X - Polynomial.C s)
    hquery

/-- Dividing the vanishing product by one node gives the erased nodal polynomial. -/
lemma div_by_monic_zs_to_poly_eq_nodal_erase {L : ℕ}
    (S : Finset (Fin L)) (query : Fin L → ZMod p)
    (hquery : Set.InjOn query ↑S) (i : Fin L) (hi : i ∈ S) :
    let Zₛ := ∏ s ∈ S.image query, (X - C s)
    (Zₛ.divByMonic (X - C (query i))).toPoly
      = Lagrange.nodal (S.erase i) query := by
  intro Zₛ
  have hq_toPoly : (X - C (query i) : CPolynomial (ZMod p)).toPoly
      = Polynomial.X - Polynomial.C (query i) := by
    rw [CPolynomial.toPoly_sub, X_toPoly, C_toPoly]
  have hmonic : (X - C (query i) : CPolynomial (ZMod p)).toPoly.Monic := by
    rw [hq_toPoly]; exact Polynomial.monic_X_sub_C _
  rw [CPolynomial.toPoly_divByMonic _ _ hmonic, zs_to_poly_eq_nodal S query hquery, hq_toPoly,
    Lagrange.nodal_eq_mul_nodal_erase hi]
  exact Polynomial.mul_divByMonic_cancel_left _ (Polynomial.monic_X_sub_C _)

/-- Barycentric conversion for interpolation divided by the vanishing polynomial at `τ`. -/
lemma lagrange_zs_conversion {L : ℕ} (τ : ZMod p) (S : Finset (Fin L))
    (query : Fin L → ZMod p) (response : Fin L → ZMod p)
    (hτ : ∀ i ∈ S, (query i) ≠ τ) (hquery : Set.InjOn query ↑S) :
    let Zₛ := ∏ s ∈ S.image query, (X - C s)
    ((CLagrange.interpolate S query response).eval τ) / (Zₛ.eval τ)
      = ∑ x ∈ S, response x /
        (eval (query x) (Zₛ.divByMonic (X - C (query x))) * (τ - query x)) := by
  intro Zₛ
  -- Derive τ ≠ query i (Mathlib direction)
  have hτ' : ∀ i ∈ S, τ ≠ query i := fun i hi => Ne.symm (hτ i hi)
  -- Convert CPolynomial evals to Polynomial evals
  have hZₛ_toPoly : Zₛ.toPoly = Lagrange.nodal S query := zs_to_poly_eq_nodal S query hquery
  have hZₛ_eval : Zₛ.eval τ = Polynomial.eval τ (Lagrange.nodal S query) := by
    rw [eval_toPoly, hZₛ_toPoly]
  have hinterp_eval : (CLagrange.interpolate S query response).eval τ
      = Polynomial.eval τ (Lagrange.interpolate S query response) := by
    rw [eval_toPoly, CLagrange.cinterpolate_eq_interpolate]
  rw [hinterp_eval, hZₛ_eval]
  -- Apply first barycentric form
  rw [Lagrange.eval_interpolate_not_at_node response hτ']
  -- Cancel nodal(τ)
  have hne : Polynomial.eval τ (Lagrange.nodal S query) ≠ 0 :=
    Lagrange.eval_nodal_not_at_node hτ'
  rw [mul_div_cancel_left₀ _ hne]
  -- Match summands
  apply Finset.sum_congr rfl
  intro i hi
  -- Rewrite nodalWeight using eval of nodal (S.erase i)
  rw [Lagrange.nodalWeight_eq_eval_nodal_erase_inv]
  -- Connect divByMonic eval to nodal (S.erase i) eval
  have hdiv_eval : eval (query i) (Zₛ.divByMonic (X - C (query i)))
      = Polynomial.eval (query i) (Lagrange.nodal (S.erase i) query) := by
    rw [eval_toPoly, div_by_monic_zs_to_poly_eq_nodal_erase S query hquery i hi]
  rw [hdiv_eval]
  -- Field algebra: a⁻¹ * b⁻¹ * c = c / (a * b)
  have heval_ne : Polynomial.eval (query i) (Lagrange.nodal (S.erase i) query) ≠ 0 :=
    Lagrange.eval_nodal_not_at_node (fun j hj =>
      fun h => (Finset.ne_of_mem_erase hj) (hquery hi (Finset.mem_of_mem_erase hj) h).symm)
  have hτqi_ne : τ - query i ≠ 0 := sub_ne_zero.mpr (hτ' i hi)
  field_simp

omit [DecidableEq G₁] in
/-- The interpolation-branch output satisfies the ARSDH exponent equation. -/
lemma h1_zs_eq_h2_prime {L : ℕ} (n : ℕ) (τ : ZMod p) (cm : G₁) (S : Finset (Fin L))
    (query : Fin L → ZMod p) (response : Fin L → ZMod p) (proofs : Fin L → G₁)
    (srs : Vector G₁ (n + 1) × Vector G₂ 2) (hn : 1 ≤ n)
    (hsrs : srs = Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ)
    (hτ : ∀ i ∈ S, (query i) ≠ τ)
    (hVerify : ∀ i ∈ S, verifyOpening (pairing := pairing) (g₁ := g₁) (g₂ := g₂)
      srs.2 cm (proofs i) (query i) (response i))
    (hgen : srs.1[0] ≠ 1) (hpair : pairing g₁ g₂ ≠ 0)
    (hS : (CLagrange.interpolate S query response).degree ≤ n) (hS_ne : S.Nonempty)
    (hquery : Set.InjOn query ↑S) :
    let Zₛ := ∏ s ∈ S.image query, (X - C s)
    let c' : G₁ := commit srs.1 ((CLagrange.interpolate S query response).val.coeff ∘ Fin.val)
    let h₁ := cm / c'
    let d := fun α => 1 / eval α (divByMonic Zₛ (X - C α))
      -- 1/(Z_{S \ {α}}(α))
    let h₂ : G₁ := ∏ i ∈ S, (proofs i) ^ (d (query i)).val
    h₂ = h₁ ^ (1 / Zₛ.eval τ).val := by
    letI := Classical.decEq G₁
    intro Zₛ c' h₁ d h₂
    unfold h₁ h₂
    -- rewrite the equation to g₁^{*equation*} (expose the field values)
    have hpG1 : Nat.card G₁ = p := PrimeOrderWith.hCard
    have hcommit_rw : c' = g₁ ^ ((CLagrange.interpolate S query response).eval τ).val := by
      unfold c'
      conv_lhs => rw [hsrs, Groups.PowerSrs.generate]
      exact commit_eq_c_polynomial (g₁ := g₁) hpG1
        (CLagrange.interpolate S query response) hS
    rw [hcommit_rw]
    have hg₁ : g₁ ≠ 1 :=
      Groups.PowerSrs.generator_ne_one_of_generate (g₁ := g₁) (g₂ := g₂) hsrs hgen
    have hord : orderOf g₁ = p := Groups.orderOf_eq_prime_of_ne_one g₁ hg₁
    obtain ⟨cm', hcm⟩ := Groups.exists_zmod_power_of_generator hpG1 hg₁ hord cm
    have hproofs_pow : ∀ i, ∃ prf : ZMod p, proofs i = g₁ ^ prf.val := by
      intro i
      exact Groups.exists_zmod_power_of_generator hpG1 hg₁ hord (proofs i)
    choose prf hprf using hproofs_pow
    rw [hcm]
    simp_rw [hprf]
    have hprf_eq : ∀ i ∈ S, prf i = (cm' - response i) / (τ - query i) := by
      intro i hi
      exact verify_opening_prf_equation pairing (query i) (response i) τ cm' (prf i)
        cm (proofs i) srs hsrs hpair (hVerify i hi) hcm (hprf i) (Ne.symm (hτ i hi))
    rw [show ∏ x ∈ S, (g₁ ^ (prf x).val) ^ (d (query x)).val
        = ∏ x ∈ S, (g₁ ^ ((cm' - response x) / (τ - query x)).val) ^ (d (query x)).val from
      Finset.prod_congr rfl (fun i hi => by rw [hprf_eq i hi])]
    -- move prod up to sum
    unfold d
    simp_rw [← pow_mul]
    rw [Finset.prod_pow_eq_pow_sum]
    have hlhs_rw : g₁ ^ (∑ x ∈ S,
        ((cm' - response x) / (τ - query x)).val *
        (1 / eval (query x) (Zₛ.divByMonic (X - C (query x)))).val)
      = g₁ ^ (∑ x ∈ S,
        (cm' - response x) /
        (eval (query x) (Zₛ.divByMonic (X - C (query x))) * (τ - query x))).val := by
      conv_lhs => rw [← pow_mod_orderOf g₁, hord]
      congr 1
      have hcast : ((∑ x ∈ S,
          ((cm' - response x) / (τ - query x)).val *
          (1 / eval (query x) (Zₛ.divByMonic (X - C (query x)))).val : ℕ) : ZMod p)
        = (∑ x ∈ S,
          (cm' - response x) /
          (eval (query x) (Zₛ.divByMonic (X - C (query x))) * (τ - query x))) := by
        push_cast [ZMod.natCast_zmod_val]
        congr 1; ext x
        rw [div_mul_div_comm, _root_.mul_one, mul_comm (τ - query x)]
      have := congr_arg ZMod.val hcast
      rw [ZMod.val_natCast] at this
      exact this
    rw [hlhs_rw]
    -- split sum: (cm' - response x) / ... = cm' / ... - response x / ...
    have hsplit : (∑ x ∈ S,
        (cm' - response x) /
        (eval (query x) (Zₛ.divByMonic (X - C (query x))) * (τ - query x)))
      = (∑ x ∈ S,
        cm' / (eval (query x) (Zₛ.divByMonic (X - C (query x))) * (τ - query x)))
      - (∑ x ∈ S,
        response x / (eval (query x) (Zₛ.divByMonic (X - C (query x))) * (τ - query x))) := by
      simp only [sub_div, Finset.sum_sub_distrib]
    rw [hsplit]
    -- Rewrite the response sum using lagrange_zs_conversion
    rw [← lagrange_zs_conversion τ S query response hτ hquery]
    -- Factor cm' from the first sum and simplify to cm' / Zₛ.eval τ
    have hcm_sum : (∑ x ∈ S,
        cm' / (eval (query x) (Zₛ.divByMonic (X - C (query x))) * (τ - query x)))
      = cm' / Zₛ.eval τ := by
      have h1 : ∀ x ∈ S,
          cm' / (eval (query x) (Zₛ.divByMonic (X - C (query x))) * (τ - query x))
        = cm' * (1 / (eval (query x) (Zₛ.divByMonic (X - C (query x))) * (τ - query x))) :=
        fun _ _ => by ring
      rw [Finset.sum_congr rfl h1, ← Finset.mul_sum,
        ← lagrange_zs_conversion τ S query (fun _ => 1) hτ hquery,
        CLagrange.interpolation_of_constants S query (fun _ => 1) 1 (fun _ _ => rfl)
          hquery hS_ne]
      simp only [eval_toPoly, C_toPoly, Polynomial.eval_C]
      ring
    rw [hcm_sum]
    -- Abbreviate
    set r := (CLagrange.interpolate S query response).eval τ
    set z := Zₛ.eval τ
    -- LHS: cm'/z - r/z = (cm' - r) * (1/z)
    conv_lhs => rw [show cm' / z - r / z = (cm' - r) * (1 / z) from by ring]
    -- RHS: use div_pow (CommGroup) and pow_mul
    rw [div_pow, ← pow_mul, ← pow_mul]
    -- Expand powers over the difference of the scaled exponents.
    rw [Groups.gpow_val_mul_eq hord cm' (1 / z),
      Groups.gpow_val_mul_eq hord r (1 / z), Groups.gpow_div_eq hord]
    congr 1
    exact congr_arg ZMod.val (by ring : (cm' - r) * (1 / z) = cm' * (1 / z) - r * (1 / z))

/-- ARSDH output for the interpolation branch of the reduction. -/
def interpolationArsdhOutput {L : ℕ} (S : Finset (Fin L))
    (tr : FunctionBindingExtTranscript (p := p) n L G₁ G₂) :
    FunctionBindingArsdhOutput (p := p) G₁ :=
  let Zₛ := ∏ s ∈ S.image tr.queryOf, (X - C s)
  let c' : G₁ :=
    commit tr.srs.1 ((CLagrange.interpolate S tr.queryOf tr.responseOf).val.coeff ∘ Fin.val)
  let h₁ := tr.cm / c'
  let d := fun α => 1 / eval α (divByMonic Zₛ (X - C α))
    -- 1/(Z_{S \ {α}}(α))
  let h₂ : G₁ := ∏ i ∈ S, (tr.proofs i) ^ (d (tr.queryOf i)).val
  { support := S.image tr.queryOf, base := h₁, solution := h₂ }

include g₁ g₂ pairing in
/-- The interpolation branch maps a function-binding violation to ARSDH. -/
lemma function_binding_interpolation_branch_maps_to_arsdh {n L : ℕ}
    (hn : 1 ≤ n) (hpair : pairing g₁ g₂ ≠ 0)
    {τ : ZMod p} {srs : Vector G₁ (n + 1) × Vector G₂ 2} {cm : G₁}
    {queryOf responseOf : Fin L → ZMod p} {accepts : Fin L → Bool} {proofs : Fin L → G₁}
    (hsrs : srs = Groups.PowerSrs.generate (g₁ := g₁) (g₂ := g₂) n τ)
    (hgen : srs.1[0] ≠ 1)
    (hverify_all : ∀ i : Fin L, accepts i = true →
      KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
        srs.2 cm (proofs i) (queryOf i) (responseOf i))
    (hFBcond : functionBindingCondExt n L (τ, srs, cm, queryOf, responseOf, accepts, proofs))
    {A S : Finset (Fin L)}
    (hqueryS : Set.InjOn queryOf ↑S)
    (hresS : findS n A cm srs queryOf responseOf = some S)
    (hfs_none : List.findSome?
        (fun i ↦ if srs.1[0] ^ (queryOf i).val = srs.1[1]'(Nat.lt_add_of_pos_left hn)
                  then some (queryOf i) else none)
        (List.finRange L) = none) :
    Groups.arsdhCondition n
      (τ, (interpolationArsdhOutput (p := p) (G₂ := G₂) S
        ({ srs := srs, cm := cm, queryOf := queryOf, responseOf := responseOf,
           accepts := accepts, proofs := proofs } :
          FunctionBindingExtTranscript (p := p) n L G₁ G₂)).toTuple) := by
  simp only [interpolationArsdhOutput, FunctionBindingArsdhOutput.toTuple,
    Groups.arsdhCondition, ne_eq, one_div]
  have hresS_symm : some S = findS n A cm srs queryOf responseOf := hresS.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injOn hqueryS]
    exact find_s_card n cm A S srs queryOf responseOf hresS_symm
  · have hτneq_all : ∀ i : Fin L, queryOf i ≠ τ :=
      query_ne_tau_of_find_query_with_srs_power_none
        (g₁ := g₁) hn τ srs queryOf hsrs hfs_none
    have hτ_not_image : τ ∉ S.image queryOf := by
      simp only [Finset.mem_image, not_exists, not_and]
      intro i _
      exact hτneq_all i
    exact prod_x_sub_c_eval_ne_zero hτ_not_image
  · intro hdiv
    have hcm_eq_c' : cm =
        commit srs.1 ((CLagrange.interpolate S queryOf responseOf).val.coeff ∘ Fin.val) :=
      div_eq_one.mp hdiv
    exact (find_s_diverges n cm A S queryOf responseOf srs hresS_symm) hcm_eq_c'.symm
  · have hcard : S.card = n + 1 :=
      find_s_card n cm A S srs queryOf responseOf hresS_symm
    have hdeg : (CLagrange.interpolate S queryOf responseOf).degree ≤ (n : WithBot ℕ) := by
      exact interp_degree_le_of_card S queryOf responseOf hqueryS hcard
    have hS_ne : S.Nonempty := by
      rw [← Finset.card_pos, hcard]; exact Nat.succ_pos _
    have hτneq : ∀ i ∈ S, queryOf i ≠ τ := by
      intro i _
      exact query_ne_tau_of_find_query_with_srs_power_none
        (g₁ := g₁) hn τ srs queryOf hsrs hfs_none i
    have hVer : ∀ i ∈ S,
        KZG.verifyOpening (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
          srs.2 cm (proofs i) (queryOf i) (responseOf i) := by
      intro i _
      exact hverify_all i (hFBcond.1 i (Finset.mem_univ _))
    have key := h1_zs_eq_h2_prime (g₁ := g₁) (g₂ := g₂) (pairing := pairing)
      n τ cm S queryOf responseOf proofs srs hn hsrs hτneq hVer
      hgen hpair hdeg hS_ne hqueryS
    simpa only [one_div] using key

end FunctionBinding

end CommitmentScheme

end KZG
