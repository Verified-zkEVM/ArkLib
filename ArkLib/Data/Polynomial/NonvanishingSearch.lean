/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Avoidance
public import CompPoly.Univariate.BatchEval.Context
/-!
# Executable nonvanishing search with a batch-evaluation backend

The ordinary decoder must choose a center away from the zeros of its discriminant. Given that
polynomial and an explicit candidate list, this routine evaluates every candidate in one batch
and returns the first nonzero value. The backend can use subproduct trees; the proof does not
assume pointwise Horner evaluation or enumerate the polynomial's roots.

This is the search stage only: constructing and proving nonzero the ordinary discriminant, and
constructing enough distinct candidates in a suitable field, remain separate obligations.
-/

@[expose] public section

namespace CompPoly.CPolynomial
variable {F : Type*} [Field F] [BEq F] [LawfulBEq F]

/-- Batch-evaluate first, then return the first candidate with a nonzero value. -/
def findNonzeroEvaluation? (B : BatchEvalContext F) (p : CPolynomial F)
    (candidates : List F) : Option F :=
  ((candidates.zip (B.evalBatchWith p candidates.toArray).toList).find?
    (fun pair => pair.2 != 0)).map Prod.fst

omit [LawfulBEq F] in
/-- Backend correctness identifies the batched search with the pointwise specification. -/
theorem findNonzeroEvaluation?_eq (B : BatchEvalContext F) (p : CPolynomial F)
    (candidates : List F) :
    findNonzeroEvaluation? B p candidates = candidates.find? (fun x => p.eval x != 0) := by
  simp only [findNonzeroEvaluation?, B.correct, evalBatch, Array.toList_map]
  induction candidates with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.map_cons, List.zip_cons_cons, List.find?_cons]
      split <;> simp_all


/-- A returned point comes from the candidate list and passes the nonvanishing test. -/
theorem findNonzeroEvaluation?_sound (B : BatchEvalContext F) (p : CPolynomial F)
    (candidates : List F) (x : F) (h : findNonzeroEvaluation? B p candidates = some x) :
    x ∈ candidates ∧ p.eval x ≠ 0 := by
  rw [findNonzeroEvaluation?_eq, List.find?_eq_some_iff_getElem] at h
  obtain ⟨hvalue, i, hi, hget, _⟩ := h
  exact ⟨hget ▸ List.getElem_mem hi, by simpa using hvalue⟩

/-- More distinct candidates than the polynomial degree guarantee that the search succeeds. -/
theorem findNonzeroEvaluation?_exists (B : BatchEvalContext F) (p : CPolynomial F)
    (hp : p ≠ 0) (candidates : List F) (hnodup : candidates.Nodup)
    (hlength : p.natDegree < candidates.length) :
    ∃ x, findNonzeroEvaluation? B p candidates = some x := by
  classical
  obtain ⟨x, hx, hnonzero⟩ := Polynomial.exists_avoiding_finite_polynomials
    (RingHom.id F) {p.toPoly} p.natDegree
    (by simpa only [Finset.mem_singleton] using
      fun q hq => hq ▸ (toPoly_eq_zero_iff p).not.mpr hp)
    (by intro q hq; simp only [Finset.mem_singleton] at hq; subst q
        exact (natDegree_toPoly p).symm.le)
    candidates hnodup (by simpa using hlength)
  rw [findNonzeroEvaluation?_eq]
  have hsome : candidates.find? (fun x => p.eval x != 0) ≠ none := by
    intro hnone
    rw [List.find?_eq_none] at hnone
    have h := hnone x hx
    have hn := hnonzero p.toPoly (Finset.mem_singleton_self _)
    simp only [RingHom.id_apply, ← eval_toPoly] at hn
    simp [hn] at h
  exact Option.ne_none_iff_exists'.mp hsome

end CompPoly.CPolynomial
