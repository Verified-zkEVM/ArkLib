/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: XC0R
-/
module

public import ArkLib.Data.CodingTheory.ListDecodability.Bounds.ReedSolomon.FullRank
public import ArkLib.ToMathlib.Combinatorics.Enumerative.Descents
public import ArkLib.ToMathlib.MvPolynomial.PrefixSubstitution

/-!
# Certificates of rank loss for the intersection matrix

Let `H : Fin n → Finset (Fin (s + 1))` be a hypergraph, `k` a degree, and `r` such that `H` is
`(k + 2 * r)`-weakly partition-connected. Two edges `i` and `i'` have the same type if
`H i = H i'`. The construction and the certificates are those of [AGL24], with `t = s + 1`.

For a list `l` of edges, `certificateState F hH l` is the state after `l`: the rows of a maximal
minor of the intersection matrix, a bank of unused edges, and the number of steps since the bank
was last chosen, built along `l` one edge at a time. The construction starts with the bank
`certificateBank H r []`, which holds, for each type, the `r / 2 ^ (s + 1)` largest edges of that
type, and with a nonzero minor whose rows avoid the bank. Such a minor exists since the bank has
at most `r` edges (`exists_det_submatrix_ne_zero_of_card_le`). On the next edge `i` of `l`, the
smallest edge `i'` of the bank of the same type as `i` leaves the bank and the variables `X i` and
`X i'` are swapped in the minor (`det_submatrix_relabel`). If the bank has no edge of the type of
`i`, the bank and the minor are chosen afresh; the rows of the new minor avoid the new bank and
the edges of `l` seen so far whenever such a nonzero minor exists, which is the case while at
most `r` edges have been seen. The minor after `l` depends only on `l`, and it is nonzero.

A certificate for a point `α : Fin n → F` is a tuple `c : Fin m → Fin n` such that, for every
position `j`, the minor after `c 0, …, c (j - 1)` does not vanish after substituting `α i` for
`X i` at every `i < c j`, and vanishes after substituting `α i` for `X i` at every `i ≤ c j`.
A certificate of length at most `r` is injective and has fewer than `2 ^ (s + 1)` descents, and
every point at which the intersection matrix loses rank has a certificate of length `r`.

## Main definitions

* `certificateBank H r used`: for each type, the `r / 2 ^ (s + 1)` largest edges of that type not
  in `used`.
* `rowsAvoiding`: rows of a nonzero maximal minor avoiding given edges, when such a minor exists.
* `CertificateState`, with `CertificateState.refresh` and `CertificateState.step`, and
  `certificateState F hH l`: the rows, the bank and the age after the list `l`.
* `certificateMinor F hH l`: the determinant of the minor with those rows.
* `IsCertificate F hH α c`: `c` is a certificate for `α`.
* `certificatePolynomial F hH c i`: the minor attached to the edge `i` of an injective
  certificate `c`.

## Main statements

* `certificateMinor_ne_zero`, `degreeOf_certificateMinor_le`: the minors are nonzero and have
  degree at most `s * (k - 1)` in each variable.
* `certificateState_nil`, `certificateState_append_singleton`: the state after `[]` is the fresh
  state, and the state after `l ++ [i]` is computed from the state after `l`.
* `IsCertificate.injective`, `IsCertificate.card_descents_lt`: a certificate of length at most
  `r` is injective and has fewer than `2 ^ (s + 1)` descents.
* `exists_isCertificate_of_not_isRigid`: a point at which `H` is not rigid has certificates of
  every length.
* `exists_embedding_isCertificate_of_not_isRigid`: a point at which `H` is not rigid has an
  injective certificate of length `r` with fewer than `2 ^ (s + 1)` descents.
* `certificatePolynomial_apply`, `degreeOf_certificatePolynomial_le`: the polynomial of the edge
  `c j` is the minor after `c 0, …, c (j - 1)`, and every polynomial has degree at most
  `s * (k - 1)` in the variable of its edge.
* `exists_embedding_certificatePolynomial_of_not_isRigid`: a point at which `H` is not rigid has
  an injective certificate of length `r` with fewer than `2 ^ (s + 1)` descents, with the minors
  indexed by its edges.

## References

* [Alrabiah, O., Guruswami, V., and Li, R., *Randomly punctured Reed-Solomon codes achieve
    list-decoding capacity over linear-sized fields*][AGL24]
-/

@[expose] public section

namespace ReedSolomon

open Finset MvPolynomial

section Bank

variable {n s : ℕ} (H : Fin n → Finset (Fin (s + 1))) (r : ℕ) (used : List (Fin n))

/-- The bank for `used`: the edges `i` not in `used` such that fewer than `r / 2 ^ (s + 1)` edges
`j > i` not in `used` have the same type as `i`. For each type these are the
`r / 2 ^ (s + 1)` largest edges of that type not in `used`, or all of them if there are fewer. -/
def certificateBank : Finset (Fin n) :=
  {i | i ∉ used ∧ #{j | j ∉ used ∧ H j = H i ∧ i < j} < r / 2 ^ (s + 1)}

variable {H r used}

/-- Of two edges of the same type outside `used`, the larger has fewer larger edges of that type
outside `used`. -/
private theorem card_filter_lt_card_filter_of_lt {i j : Fin n} (hij : i < j) (hji : H j = H i)
    (hj : j ∉ used) :
    #{l | l ∉ used ∧ H l = H j ∧ j < l} < #{l | l ∉ used ∧ H l = H i ∧ i < l} := by
  refine card_lt_card ((ssubset_iff_of_subset fun l hl ↦ ?_).2 ⟨j, ?_, ?_⟩)
  · simp only [mem_filter, mem_univ, true_and] at hl ⊢
    exact ⟨hl.1, hl.2.1.trans hji, hij.trans hl.2.2⟩
  · simp [hj, hji, hij]
  · simp

/-- The bank has at most `r` edges: at most `r / 2 ^ (s + 1)` of each of the `2 ^ (s + 1)`
types. -/
private theorem card_certificateBank_le : #(certificateBank H r used) ≤ r := by
  have hfib (τ : Finset (Fin (s + 1))) :
      #{b ∈ certificateBank H r used | H b = τ} ≤ r / 2 ^ (s + 1) := by
    refine (card_le_card_of_injOn (fun b ↦ #{l | l ∉ used ∧ H l = H b ∧ b < l})
      (t := range (r / 2 ^ (s + 1))) (fun b hb ↦ ?_) fun b hb b' hb' hbb' ↦ ?_).trans
      (card_range _).le
    · simp only [mem_coe, certificateBank, mem_filter, mem_univ, true_and] at hb
      exact mem_range.2 hb.1.2
    · simp only [mem_coe, certificateBank, mem_filter, mem_univ, true_and] at hb hb'
      have hτ : H b' = H b := hb'.2.trans hb.2.symm
      rcases lt_trichotomy b b' with h | h | h
      · exact absurd hbb' (card_filter_lt_card_filter_of_lt h hτ hb'.1.1).ne'
      · exact h
      · exact absurd hbb' (card_filter_lt_card_filter_of_lt h hτ.symm hb.1.1).ne
  calc #(certificateBank H r used)
      = ∑ τ : Finset (Fin (s + 1)), #{b ∈ certificateBank H r used | H b = τ} :=
        card_eq_sum_card_fiberwise fun _ _ ↦ mem_univ _
    _ ≤ ∑ _τ : Finset (Fin (s + 1)), r / 2 ^ (s + 1) := sum_le_sum fun τ _ ↦ hfib τ
    _ = 2 ^ (s + 1) * (r / 2 ^ (s + 1)) := by simp
    _ ≤ r := Nat.mul_div_le r _

/-- An edge outside `used` and outside the bank is smaller than every edge of the bank of the same
type. -/
private theorem lt_of_mem_certificateBank {i b : Fin n} (hi : i ∉ used)
    (hiB : i ∉ certificateBank H r used) (hb : b ∈ certificateBank H r used) (hbi : H b = H i) :
    i < b := by
  simp only [certificateBank, mem_filter, mem_univ, true_and, not_and, not_lt] at hiB hb
  by_contra hlt
  refine hb.2.not_ge ((hiB hi).trans (card_le_card fun j hj ↦ ?_))
  simp only [mem_filter, mem_univ, true_and] at hj ⊢
  exact ⟨hj.1, hj.2.1.trans hbi.symm, (not_lt.1 hlt).trans_lt hj.2.2⟩

/-- If an edge outside `used` is not in the bank, then the bank holds at least
`r / 2 ^ (s + 1)` edges of its type. -/
private theorem le_card_filter_certificateBank {i : Fin n} (hi : i ∉ used)
    (hiB : i ∉ certificateBank H r used) :
    r / 2 ^ (s + 1) ≤ #{b ∈ certificateBank H r used | H b = H i} := by
  set S : Finset (Fin n) := {j | j ∉ used ∧ H j = H i ∧ j ∉ certificateBank H r used}
  have hiS : i ∈ S := by simp [S, hi, hiB]
  obtain ⟨x, hxS, hxmax⟩ : ∃ x ∈ S, ∀ y ∈ S, y ≤ x :=
    ⟨S.max' ⟨i, hiS⟩, S.max'_mem _, fun y hy ↦ S.le_max' y hy⟩
  obtain ⟨hxu, hxH, hxB⟩ : x ∉ used ∧ H x = H i ∧ x ∉ certificateBank H r used := by
    simpa [S] using hxS
  have hxB' := hxB
  simp only [certificateBank, mem_filter, mem_univ, true_and, not_and, not_lt] at hxB'
  refine (hxB' hxu).trans (card_le_card fun j hj ↦ ?_)
  simp only [mem_filter, mem_univ, true_and] at hj ⊢
  refine ⟨by_contra fun hjB ↦ ?_, hj.2.1.trans hxH⟩
  exact (hxmax j (by simp [S, hj.1, hj.2.1.trans hxH, hjB])).not_gt hj.2.2

end Bank

section Construction

variable (F : Type*) [Field F] {n s k r : ℕ} {H : Fin n → Finset (Fin (s + 1))}

/-- The state of the construction: the rows of a square submatrix of the intersection matrix with
all columns, the edges of the bank not yet used, and the number of steps since the bank was last
chosen. -/
structure CertificateState (H : Fin n → Finset (Fin (s + 1))) (k : ℕ) where
  /-- The rows of the current minor. -/
  rows : Fin s × Fin k → IntersectionRow H
  /-- The edges of the bank not yet swapped into the minor. -/
  bank : Finset (Fin n)
  /-- The number of steps since the bank was last chosen: bookkeeping for counting descents; the
  rows and the bank do not depend on it. -/
  age : ℕ

open Classical in
/-- Rows of a square submatrix of the intersection matrix with all columns, avoiding the edges in
`D`, with nonzero determinant, if there are such rows; otherwise rows of some nonzero maximal
minor. -/
noncomputable def rowsAvoiding (hH : IsWeaklyPartitionConnected H k) (D : Finset (Fin n)) :
    Fin s × Fin k → IntersectionRow H :=
  if h : ∃ ρ : Fin s × Fin k → IntersectionRow H, (∀ c, (ρ c).1.1 ∉ D) ∧
      ((intersectionMatrix F H k).submatrix ρ id).det ≠ 0 then h.choose
  else (exists_det_submatrix_ne_zero_of_isWeaklyPartitionConnected F hH).choose

/-- The rows chosen by `rowsAvoiding` have nonzero determinant. -/
private theorem det_submatrix_rowsAvoiding_ne_zero (hH : IsWeaklyPartitionConnected H k)
    (D : Finset (Fin n)) :
    ((intersectionMatrix F H k).submatrix (rowsAvoiding F hH D) id).det ≠ 0 := by
  unfold rowsAvoiding
  split_ifs with h
  · exact h.choose_spec.2
  · exact (exists_det_submatrix_ne_zero_of_isWeaklyPartitionConnected F hH).choose_spec

/-- If some nonzero maximal minor avoids `D`, the rows chosen by `rowsAvoiding` avoid `D`. -/
private theorem rowsAvoiding_notMem (hH : IsWeaklyPartitionConnected H k) {D : Finset (Fin n)}
    (h : ∃ ρ : Fin s × Fin k → IntersectionRow H, (∀ c, (ρ c).1.1 ∉ D) ∧
      ((intersectionMatrix F H k).submatrix ρ id).det ≠ 0) (c : Fin s × Fin k) :
    (rowsAvoiding F hH D c).1.1 ∉ D := by
  unfold rowsAvoiding
  rw [dite_eq_left h]
  exact h.choose_spec.1 c

variable (hH : IsWeaklyPartitionConnected H (k + 2 * r))

/-- A fresh state after the edges `used`: the bank `certificateBank H r used`, and the rows
`rowsAvoiding` of the bank and `used`, which give a nonzero maximal minor and avoid the bank and
`used` whenever some nonzero maximal minor avoids them, for example when `used` has at most `r`
edges. -/
noncomputable def CertificateState.refresh (used : List (Fin n)) : CertificateState H k where
  rows := rowsAvoiding F (hH.mono (le_add_of_nonneg_right (by positivity)))
    (certificateBank H r used ∪ used.toFinset)
  bank := certificateBank H r used
  age := 0

/-- One step of the construction on the edge `i`, after the edges `used`. If the bank has an edge
of the type of `i`, its smallest such edge `i'` leaves the bank and the variables `X i` and `X i'`
are swapped in the rows; otherwise the state is chosen afresh after `used ++ [i]`. -/
noncomputable def CertificateState.step (st : CertificateState H k) (used : List (Fin n))
    (i : Fin n) : CertificateState H k :=
  if h : {b ∈ st.bank | H b = H i}.Nonempty then
    { rows := fun c ↦ (st.rows c).relabel (Equiv.swap i ({b ∈ st.bank | H b = H i}.min' h))
        (Equiv.apply_swap_eq_self (mem_filter.1 (min'_mem _ h)).2.symm)
      bank := st.bank.erase ({b ∈ st.bank | H b = H i}.min' h)
      age := st.age + 1 }
  else CertificateState.refresh F hH (used ++ [i])

/-- The state after the list of edges `l`: start from `CertificateState.refresh F hH []` and apply
`CertificateState.step` along `l`. -/
noncomputable def certificateState (l : List (Fin n)) : CertificateState H k :=
  (l.foldl (fun p i ↦ (p.1.step F hH p.2 i, p.2 ++ [i])) (CertificateState.refresh F hH [], [])).1

/-- The minor after the list of edges `l`: the determinant of the square submatrix of the
intersection matrix with the rows of `certificateState F hH l`. -/
noncomputable def certificateMinor (l : List (Fin n)) : MvPolynomial (Fin n) F :=
  ((intersectionMatrix F H k).submatrix (certificateState F hH l).rows id).det

/-- `c` is a certificate for `α`: for every position `j`, the minor after `c 0, …, c (j - 1)`
does not vanish after substituting `α i` for `X i` at every `i < c j`, and vanishes after
substituting `α i` for `X i` at every `i ≤ c j`. -/
def IsCertificate (α : Fin n → F) {m : ℕ} (c : Fin m → Fin n) : Prop :=
  ∀ j : Fin m,
    aeval (fun i ↦ if i < c j then C (α i) else X i)
        (certificateMinor F hH ((List.ofFn c).take j)) ≠ 0 ∧
      aeval (fun i ↦ if i ≤ c j then C (α i) else X i)
        (certificateMinor F hH ((List.ofFn c).take j)) = 0

/-- The minor attached to the edge `i` by an injective tuple `c`: the minor after
`c 0, …, c (j - 1)` if `i = c j`, and `1` if `i` is not in the range of `c`. -/
noncomputable def certificatePolynomial (c : Fin r ↪ Fin n) (i : Fin n) :
    MvPolynomial (Fin n) F :=
  if h : ∃ j, c j = i then certificateMinor F hH ((List.ofFn c).take h.choose) else 1

variable (r) in
/-- The invariant of the construction after the edges `used`: the rows avoid `used` and the bank,
the bank avoids `used`, every edge of the rows is smaller than the edges of the bank of its type,
and the bank holds at least `r / 2 ^ (s + 1)` minus the age edges of the type of every edge of the
rows. -/
private structure CertificateState.Inv (st : CertificateState H k) (used : List (Fin n)) :
    Prop where
  rows_notMem_used : ∀ c, (st.rows c).1.1 ∉ used
  rows_notMem_bank : ∀ c, (st.rows c).1.1 ∉ st.bank
  bank_notMem_used : ∀ b ∈ st.bank, b ∉ used
  rows_lt_of_mem_bank : ∀ c, ∀ b ∈ st.bank, H b = H (st.rows c).1.1 → (st.rows c).1.1 < b
  le_card_bank_add_age :
    ∀ c, r / 2 ^ (s + 1) ≤ #{b ∈ st.bank | H b = H (st.rows c).1.1} + st.age

variable {F hH}

/-- The construction starts from a fresh state. -/
theorem certificateState_nil : certificateState F hH [] = CertificateState.refresh F hH [] := rfl

/-- The state after `l ++ [i]` is one step on `i` from the state after `l`. -/
theorem certificateState_append_singleton (l : List (Fin n)) (i : Fin n) :
    certificateState F hH (l ++ [i]) = (certificateState F hH l).step F hH l i := by
  have h2 (l : List (Fin n)) (p : CertificateState H k × List (Fin n)) :
      (l.foldl (fun p i ↦ (p.1.step F hH p.2 i, p.2 ++ [i])) p).2 = p.2 ++ l := by
    induction l generalizing p with
    | nil => simp
    | cons a l ih => simp [List.foldl_cons, ih]
  simp only [certificateState, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rw [h2]
  simp

/-- A swap step renames the minor: if the bank after `l` has an edge of the type of `i`, then the
minor after `l ++ [i]` is the minor after `l` with `X i` and `X i'` swapped, `i'` being the
smallest such edge. -/
private theorem certificateMinor_append_singleton_of_nonempty {l : List (Fin n)} {i : Fin n}
    (h : {b ∈ (certificateState F hH l).bank | H b = H i}.Nonempty) :
    certificateMinor F hH (l ++ [i]) = rename
      (Equiv.swap i ({b ∈ (certificateState F hH l).bank | H b = H i}.min' h))
      (certificateMinor F hH l) := by
  unfold certificateMinor
  rw [certificateState_append_singleton, CertificateState.step, dite_eq_left h]
  exact det_submatrix_relabel _ (Equiv.apply_swap_eq_self (mem_filter.1 (min'_mem _ h)).2.symm) _

/-- Every minor of the construction is a nonzero polynomial. -/
theorem certificateMinor_ne_zero (l : List (Fin n)) : certificateMinor F hH l ≠ 0 := by
  induction l using List.reverseRecOn with
  | nil =>
    exact det_submatrix_rowsAvoiding_ne_zero F
      (hH.mono (le_add_of_nonneg_right (by positivity))) _
  | append_singleton l i ih =>
    by_cases h : {b ∈ (certificateState F hH l).bank | H b = H i}.Nonempty
    · rw [certificateMinor_append_singleton_of_nonempty h]
      exact (map_ne_zero_iff _ (rename_injective _ (Equiv.injective _))).2 ih
    · unfold certificateMinor
      rw [certificateState_append_singleton, CertificateState.step, dite_eq_right h]
      exact det_submatrix_rowsAvoiding_ne_zero F
        (hH.mono (le_add_of_nonneg_right (by positivity))) _

/-- Every minor of the construction has degree at most `s * (k - 1)` in each variable. -/
theorem degreeOf_certificateMinor_le (l : List (Fin n)) (i : Fin n) :
    (certificateMinor F hH l).degreeOf i ≤ s * (k - 1) :=
  degreeOf_det_submatrix_le _ i

/-- A fresh state after at most `r` edges satisfies the invariant. -/
private theorem CertificateState.inv_refresh {used : List (Fin n)} (hlen : used.length ≤ r) :
    (CertificateState.refresh F hH used).Inv r used := by
  have hD : ((#(certificateBank H r used ∪ used.toFinset) : ℕ) : ℝ) ≤ 2 * r := by
    have := (card_union_le (certificateBank H r used) used.toFinset).trans
      (add_le_add card_certificateBank_le (used.toFinset_card_le.trans hlen))
    exact_mod_cast this.trans (by omega)
  have hrows := rowsAvoiding_notMem F (hH.mono (le_add_of_nonneg_right (by positivity)))
    (exists_det_submatrix_ne_zero_of_card_le F hH hD)
  have hu (c) : ((CertificateState.refresh F hH used).rows c).1.1 ∉ used := fun h ↦
    hrows c (mem_union_right _ (List.mem_toFinset.2 h))
  have hb (c) : ((CertificateState.refresh F hH used).rows c).1.1 ∉ certificateBank H r used :=
    fun h ↦ hrows c (mem_union_left _ h)
  refine ⟨hu, hb, fun b hb ↦ ?_,
    fun c b hb' hbc ↦ lt_of_mem_certificateBank (hu c) (hb c) hb' hbc,
    fun c ↦ le_card_filter_certificateBank (hu c) (hb c)⟩
  simp only [CertificateState.refresh, certificateBank, mem_filter] at hb
  exact hb.2.1

/-- A step on an edge of the rows preserves the invariant, as long as at most `r` edges are
used. -/
private theorem CertificateState.Inv.step {st : CertificateState H k} {used : List (Fin n)}
    {i : Fin n} (hst : st.Inv r used) (hi : ∃ c, (st.rows c).1.1 = i)
    (hlen : used.length + 1 ≤ r) : (st.step F hH used i).Inv r (used ++ [i]) := by
  unfold CertificateState.step
  split_ifs with h
  · set i' := {b ∈ st.bank | H b = H i}.min' h
    obtain ⟨hi'B, hi'H⟩ := mem_filter.1 (min'_mem _ h)
    have hi'min (b) (hb : b ∈ st.bank) (hbH : H b = H i) : i' ≤ b :=
      min'_le _ _ (mem_filter.2 ⟨hb, hbH⟩)
    obtain ⟨c₀, rfl⟩ := hi
    have hiB := hst.rows_notMem_bank c₀
    have hii' : (st.rows c₀).1.1 ≠ i' := fun h ↦ hiB (h ▸ hi'B)
    have hσ (c) : Equiv.swap (st.rows c₀).1.1 i' (st.rows c).1.1 =
        if (st.rows c).1.1 = (st.rows c₀).1.1 then i' else (st.rows c).1.1 := by
      rw [Equiv.swap_apply_def, ite_eq_right (show ¬(st.rows c).1.1 = i' from
        fun h ↦ hst.rows_notMem_bank c (h ▸ hi'B))]
    have hHσ (c) : H (Equiv.swap (st.rows c₀).1.1 i' (st.rows c).1.1) = H (st.rows c).1.1 :=
      Equiv.apply_swap_eq_self hi'H.symm _
    refine ⟨fun c ↦ ?_, fun c ↦ ?_, fun b hb ↦ ?_, fun c b hb hbc ↦ ?_, fun c ↦ ?_⟩
    · simp only [IntersectionRow.relabel, List.mem_append, List.mem_singleton, not_or]
      rw [hσ]
      split_ifs with hc
      · exact ⟨hst.bank_notMem_used _ hi'B, Ne.symm hii'⟩
      · exact ⟨hst.rows_notMem_used c, hc⟩
    · simp only [IntersectionRow.relabel, mem_erase, not_and]
      rw [hσ]
      split_ifs with hc
      · exact fun h ↦ absurd rfl h
      · exact fun _ ↦ hst.rows_notMem_bank c
    · obtain ⟨-, hb⟩ := mem_erase.1 hb
      simp only [List.mem_append, List.mem_singleton, not_or]
      exact ⟨hst.bank_notMem_used b hb, fun h ↦ hiB (h ▸ hb)⟩
    · obtain ⟨hbi', hb⟩ := mem_erase.1 hb
      simp only [IntersectionRow.relabel] at hbc ⊢
      rw [hHσ] at hbc
      rw [hσ]
      split_ifs with hc
      · rw [hc] at hbc
        exact lt_of_le_of_ne (hi'min b hb hbc) (Ne.symm hbi')
      · exact hst.rows_lt_of_mem_bank c b hb hbc
    · have hcard : #{b ∈ st.bank.erase i' |
            H b = H (Equiv.swap (st.rows c₀).1.1 i' (st.rows c).1.1)} =
          #{b ∈ st.bank.erase i' | H b = H (st.rows c).1.1} :=
        congrArg card (filter_congr fun b _ ↦ by rw [hHσ c])
      change r / 2 ^ (s + 1) ≤ #{b ∈ st.bank.erase i' |
        H b = H (Equiv.swap (st.rows c₀).1.1 i' (st.rows c).1.1)} + (st.age + 1)
      rw [hcard, filter_erase]
      have := hst.le_card_bank_add_age c
      have := pred_card_le_card_erase (s := {b ∈ st.bank | H b = H (st.rows c).1.1}) (a := i')
      omega
  · exact CertificateState.inv_refresh (by simpa using hlen)

variable {α : Fin n → F}

/-- If a minor does not vanish after substituting `α j` for `X j` at every `j < i` and vanishes
after substituting at every `j ≤ i`, then one of its rows belongs to the edge `i`. -/
private theorem exists_rows_eq_of_aeval {ρ : Fin s × Fin k → IntersectionRow H} {i : Fin n}
    (hlt : aeval (fun j ↦ if j < i then C (α j) else X j)
      ((intersectionMatrix F H k).submatrix ρ id).det ≠ 0)
    (hle : aeval (fun j ↦ if j ≤ i then C (α j) else X j)
      ((intersectionMatrix F H k).submatrix ρ id).det = 0) :
    ∃ c, (ρ c).1.1 = i := by
  by_contra hne
  simp only [not_exists] at hne
  refine hlt ?_
  rw [← hle, AlgHom.map_det, AlgHom.map_det]
  congr 1
  ext c c'
  have hX (e : ℕ) : aeval (fun j ↦ if j < i then C (α j) else X j)
      (X (ρ c).1.1 ^ e : MvPolynomial (Fin n) F) =
      aeval (fun j ↦ if j ≤ i then C (α j) else X j)
        (X (ρ c).1.1 ^ e : MvPolynomial (Fin n) F) := by
    simp [le_iff_lt_or_eq, hne c]
  simp only [AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply, id,
    intersectionMatrix_apply, map_sub]
  split_ifs <;> simp only [hX, map_zero]

/-- The prefix of length `j + 1` of a tuple is its prefix of length `j` followed by its entry
`j`. -/
private theorem take_ofFn_succ {m : ℕ} (c : Fin m → Fin n) (j : ℕ) (hj : j < m) :
    (List.ofFn c).take (j + 1) = (List.ofFn c).take j ++ [c ⟨j, hj⟩] := by
  rw [List.take_add_one, List.getElem?_ofFn]
  simp [hj]

/-- The entry `a` of a tuple lies in its prefix of every length `b > a`. -/
private theorem mem_take_ofFn {m : ℕ} (c : Fin m → Fin n) {a : Fin m} {b : ℕ} (hab : a < b) :
    c a ∈ (List.ofFn c).take b :=
  List.mem_iff_getElem.2 ⟨a, by simp [hab, a.2], by simp⟩

variable {m : ℕ} {c : Fin m → Fin n}

/-- The entry `j` of a certificate is the edge of a row of the minor after its first `j`
entries. -/
private theorem IsCertificate.exists_rows_eq (hc : IsCertificate F hH α c) (j : Fin m) :
    ∃ c', ((certificateState F hH ((List.ofFn c).take j)).rows c').1.1 = c j :=
  exists_rows_eq_of_aeval (hc j).1 (hc j).2

/-- The states along a certificate of length at most `r` satisfy the invariant. -/
private theorem IsCertificate.inv (hc : IsCertificate F hH α c) (hm : m ≤ r) (j : ℕ)
    (hj : j < m) :
    (certificateState F hH ((List.ofFn c).take j)).Inv r ((List.ofFn c).take j) := by
  induction j with
  | zero => exact CertificateState.inv_refresh (hH := hH) (by simp)
  | succ j ih =>
    rw [take_ofFn_succ c j (by omega), certificateState_append_singleton]
    exact (ih (by omega)).step (hc.exists_rows_eq ⟨j, by omega⟩) (by simp; omega)

/-- The entry `j` of a certificate of length at most `r` is not among its first `j` entries. -/
private theorem IsCertificate.notMem_take (hc : IsCertificate F hH α c) (hm : m ≤ r)
    (j : Fin m) : c j ∉ (List.ofFn c).take j := by
  obtain ⟨c', hc'⟩ := hc.exists_rows_eq j
  exact hc' ▸ (hc.inv hm j j.2).rows_notMem_used c'

/-- **Distinct edges.** A certificate of length at most `r` is injective. -/
theorem IsCertificate.injective (hc : IsCertificate F hH α c) (hm : m ≤ r) :
    Function.Injective c := by
  intro a b hab
  rcases lt_trichotomy a b with h | h | h
  · exact absurd (hab ▸ mem_take_ofFn c h) (hc.notMem_take hm b)
  · exact h
  · exact absurd (hab ▸ mem_take_ofFn c h) (hc.notMem_take hm a)

/-- After a swap step the next edge of a certificate is larger: if the bank after
`c 0, …, c (j - 1)` has an edge of the type of `c j`, then `c j < c (j + 1)`. -/
private theorem IsCertificate.lt_of_nonempty (hc : IsCertificate F hH α c) (hm : m ≤ r)
    {j : ℕ} (hj : j + 1 < m)
    (h : {b ∈ (certificateState F hH ((List.ofFn c).take j)).bank |
      H b = H (c ⟨j, by omega⟩)}.Nonempty) :
    c ⟨j, by omega⟩ < c ⟨j + 1, hj⟩ := by
  set a := c ⟨j, by omega⟩
  set b := c ⟨j + 1, hj⟩
  set i' := {b ∈ (certificateState F hH ((List.ofFn c).take j)).bank | H b = H a}.min' h
  obtain ⟨hi'B, hi'H⟩ := mem_filter.1 (min'_mem _ h)
  obtain ⟨c', hc'⟩ := hc.exists_rows_eq ⟨j, by omega⟩
  have hai' : a < i' := by
    have := (hc.inv hm j (by omega)).rows_lt_of_mem_bank c' i' hi'B
      (hi'H.trans (congrArg H hc'.symm))
    rwa [hc'] at this
  have hab : a ≠ b := fun h ↦ by
    have := hc.injective hm h
    simp only [Fin.ext_iff] at this
    omega
  by_contra hba
  have hba : b < a := lt_of_le_of_ne (not_lt.1 hba) (Ne.symm hab)
  have hF := (hc ⟨j + 1, hj⟩).2
  dsimp only at hF
  rw [take_ofFn_succ c j (by omega), certificateMinor_append_singleton_of_nonempty h,
    aeval_ite_le_rename_swap hba (hba.trans hai'),
    map_eq_zero_iff _ (rename_injective _ (Equiv.injective _))] at hF
  exact (hc ⟨j, by omega⟩).1 (aeval_ite_lt_eq_zero_of_aeval_ite_le_eq_zero hba hF)

/-- Along a certificate of length at most `r`, the number of descents before position `j`, times
`r / 2 ^ (s + 1) + 1`, plus the age of the state after the first `j` entries, is at most `j`. -/
private theorem IsCertificate.card_filter_descents_mul_add_age_le
    (hc : IsCertificate F hH α c) (hm : m ≤ r) (j : ℕ) (hj : j < m) :
    #{p ∈ Tuple.descents c | p.val < j} * (r / 2 ^ (s + 1) + 1) +
      (certificateState F hH ((List.ofFn c).take j)).age ≤ j := by
  induction j with
  | zero => simp [certificateState_nil, CertificateState.refresh]
  | succ j ih =>
    have ih := ih (by omega)
    rw [take_ofFn_succ c j (by omega), certificateState_append_singleton]
    by_cases h : {b ∈ (certificateState F hH ((List.ofFn c).take j)).bank |
        H b = H (c ⟨j, by omega⟩)}.Nonempty
    · have hlt := hc.lt_of_nonempty hm hj h
      have hjm : j < m := by omega
      have hD : {p ∈ Tuple.descents c | p.val < j + 1} =
          {p ∈ Tuple.descents c | p.val < j} := by
        refine filter_congr fun p hp ↦ ⟨fun hpj ↦ lt_of_le_of_ne (Nat.lt_succ_iff.1 hpj)
          fun hpj' ↦ ?_, fun hpj ↦ hpj.trans j.lt_succ_self⟩
        obtain ⟨hp1, hp2⟩ := Tuple.mem_descents.1 hp
        obtain rfl : p = ⟨j, hjm⟩ := Fin.ext hpj'
        exact hp2.not_gt hlt
      rw [hD, CertificateState.step, dite_eq_left h]
      dsimp only
      omega
    · obtain ⟨c', hc'⟩ := hc.exists_rows_eq ⟨j, by omega⟩
      have hage := (hc.inv hm j (by omega)).le_card_bank_add_age c'
      rw [hc', not_nonempty_iff_eq_empty.1 h, card_empty, zero_add] at hage
      have hD : #{p ∈ Tuple.descents c | p.val < j + 1} ≤
          #{p ∈ Tuple.descents c | p.val < j} + 1 := by
        refine (card_le_card fun p hp ↦ ?_).trans (card_insert_le ⟨j, by omega⟩ _)
        obtain ⟨hp, hpj⟩ := mem_filter.1 hp
        rcases Nat.lt_succ_iff_lt_or_eq.1 hpj with hpj | hpj
        · exact mem_insert_of_mem (mem_filter.2 ⟨hp, hpj⟩)
        · exact mem_insert.2 (.inl (Fin.ext hpj))
      rw [CertificateState.step, dite_eq_right h]
      simp only [CertificateState.refresh, add_zero]
      nlinarith

/-- **Few descents.** A certificate of length at most `r` has fewer than `2 ^ (s + 1)`
descents. -/
theorem IsCertificate.card_descents_lt (hc : IsCertificate F hH α c) (hm : m ≤ r) :
    #(Tuple.descents c) < 2 ^ (s + 1) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm0
  · simp [Tuple.descents]
  have h := hc.card_filter_descents_mul_add_age_le hm (m - 1) (by omega)
  rw [filter_true_of_mem fun p hp ↦ by
    obtain ⟨hp1, -⟩ := Tuple.mem_descents.1 hp
    omega] at h
  have hr := Nat.lt_mul_div_succ r (pow_pos two_pos (s + 1))
  refine Nat.lt_of_mul_lt_mul_right (a := r / 2 ^ (s + 1) + 1) ?_
  calc #(Tuple.descents c) * (r / 2 ^ (s + 1) + 1) ≤ m - 1 := by omega
    _ < r := by omega
    _ < 2 ^ (s + 1) * (r / 2 ^ (s + 1) + 1) := hr

/-- **Points of rank loss have certificates.** If `H` is not rigid for degree `k` at `α`, then
`α` has a certificate of every length `m`. -/
theorem exists_isCertificate_of_not_isRigid (hα : ¬IsRigid H k α) (m : ℕ) :
    ∃ c : Fin m → Fin n, IsCertificate F hH α c := by
  induction m with
  | zero => exact ⟨Fin.elim0, fun j ↦ j.elim0⟩
  | succ m ih =>
    obtain ⟨c, hc⟩ := ih
    have hzero : aeval α (certificateMinor F hH (List.ofFn c)) = 0 :=
      not_not.1 fun h ↦ hα ((isRigid_iff_exists_aeval_det_ne_zero (R := F)).2 ⟨_, h⟩)
    obtain ⟨i, hi⟩ := exists_aeval_ite_lt_ne_zero_and_aeval_ite_le_eq_zero
      (certificateMinor_ne_zero (List.ofFn c)) hzero
    have hof : List.ofFn (Fin.snoc c i : Fin (m + 1) → Fin n) = List.ofFn c ++ [i] := by
      rw [List.ofFn_succ', List.concat_eq_append]
      simp
    refine ⟨Fin.snoc c i, fun j ↦ ?_⟩
    rw [hof]
    induction j using Fin.lastCases with
    | last => simpa using hi
    | cast j =>
      rw [Fin.snoc_castSucc, Fin.val_castSucc,
        List.take_append_of_le_length (by simp [j.2.le])]
      exact hc j

/-- **Certificates of rank loss.** If `H` is `(k + 2 * r)`-weakly partition-connected and not
rigid for degree `k` at `α`, then `α` has an injective certificate of length `r` with fewer than
`2 ^ (s + 1)` descents. -/
theorem exists_embedding_isCertificate_of_not_isRigid (hα : ¬IsRigid H k α) :
    ∃ c : Fin r ↪ Fin n, #(Tuple.descents c) < 2 ^ (s + 1) ∧ IsCertificate F hH α c := by
  obtain ⟨c, hc⟩ := exists_isCertificate_of_not_isRigid hα r
  exact ⟨⟨c, hc.injective le_rfl⟩, hc.card_descents_lt le_rfl, hc⟩

/-- The polynomial of the edge `c j` of an injective tuple `c` is the minor after
`c 0, …, c (j - 1)`. -/
theorem certificatePolynomial_apply (c : Fin r ↪ Fin n) (j : Fin r) :
    certificatePolynomial F hH c (c j) = certificateMinor F hH ((List.ofFn c).take j) := by
  have h : ∃ j', c j' = c j := ⟨j, rfl⟩
  rw [certificatePolynomial, dite_eq_left h, c.injective h.choose_spec]

/-- The polynomial of every edge has degree at most `s * (k - 1)` in that edge's variable. -/
theorem degreeOf_certificatePolynomial_le (c : Fin r ↪ Fin n) (i : Fin n) :
    (certificatePolynomial F hH c i).degreeOf i ≤ s * (k - 1) := by
  unfold certificatePolynomial
  split_ifs
  · exact degreeOf_certificateMinor_le _ i
  · rw [← C_1, degreeOf_C]
    exact Nat.zero_le _

/-- **Certificates of rank loss, indexed by edges.** If `H` is `(k + 2 * r)`-weakly
partition-connected and not rigid for degree `k` at `α`, then there is an injective
`c : Fin r ↪ Fin n` with fewer than `2 ^ (s + 1)` descents such that, for every edge `i` of `c`,
`certificatePolynomial F hH c i` does not vanish after substituting `α j` for `X j` at every
`j < i`, and vanishes after substituting at every `j ≤ i`. -/
theorem exists_embedding_certificatePolynomial_of_not_isRigid (hα : ¬IsRigid H k α) :
    ∃ c : Fin r ↪ Fin n, #(Tuple.descents c) < 2 ^ (s + 1) ∧ ∀ i ∈ univ.map c,
      aeval (fun j ↦ if j < i then C (α j) else X j) (certificatePolynomial F hH c i) ≠ 0 ∧
        aeval (fun j ↦ if j ≤ i then C (α j) else X j)
          (certificatePolynomial F hH c i) = 0 := by
  obtain ⟨c, hd, hc⟩ := exists_embedding_isCertificate_of_not_isRigid (hH := hH) hα
  refine ⟨c, hd, fun i hi ↦ ?_⟩
  obtain ⟨j, -, rfl⟩ := mem_map.1 hi
  rw [certificatePolynomial_apply]
  exact hc j

end Construction

end ReedSolomon
