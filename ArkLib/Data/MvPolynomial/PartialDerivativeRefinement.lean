/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.PartialDerivativeMachine
public import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Sparse derivative execution and refinement

The interpreter implements first-occurrence differentiation for arbitrary factor lists. Its
polynomial interpretation is the partial derivative when each term has distinct variable
indices; this invariant is preserved. Runtime counts repeated additions against the numerical
exponent sum and does not claim polynomial time in binary exponent length alone.
-/

@[expose] public section

namespace MvPolynomial.PartialDerivativeMachine

open EvaluationMachine (factorsPolynomial sparsePolynomial)

variable {F : Type*} [CommSemiring F] [DecidableEq F]

/-- Declarative first-occurrence derivative; used only as an execution specification. -/
def derivativeTerm (j : ℕ) (c : F) : List (ℕ × ℕ) → Option (Term F)
  | [] => none
  | (i, e) :: fs => if i = j then
      if e = 0 then none else if e • c = 0 then none else some (e • c, (i, e - 1) :: fs)
    else (derivativeTerm j c fs).map fun t => (t.1, (i, e) :: t.2)

/-- Preserve input term order, omitting terms whose differentiated coefficient vanishes. -/
def derivativeTerms (j : ℕ) : List (Term F) → List (Term F)
  | [] => []
  | (c, fs) :: ts => (derivativeTerm j c fs).toList ++ derivativeTerms j ts

/-- Prepend a restored factor prefix and store the optional differentiated term. -/
def stored (pre : List (ℕ × ℕ)) (t : Option (Term F)) (out : List (Term F)) : List (Term F) :=
  match t with
  | none => out
  | some (c, fs) => (c, pre.reverse ++ fs) :: out

/-- Numerical work measure for factor traversal and repeated coefficient addition. -/
def factorMass (fs : List (ℕ × ℕ)) : ℕ := 2 * fs.length + (fs.map Prod.snd).sum + 1
/-- Total numerical work measure; every input term contributes at least one. -/
def inputMass (ts : List (Term F)) : ℕ := (ts.map fun t => factorMass t.2).sum
/-- Polynomial bound in term count, factor count, and the numerical exponent sum. -/
def budget (ts : List (Term F)) : ℕ := 40 * inputMass ts + 10

/-- Sum of all charged primitives. -/
def totalCost (c : Cost) : ℕ := c.work.additions + c.work.multiplications + c.work.control +
  c.work.data + c.work.natural + c.work.output + c.equalities
/-- Primitive totals add under trace composition. -/
theorem total_add (a b : Cost) : totalCost (a + b) = totalCost a + totalCost b := by
  simp [totalCost]
  omega
/-- Primitive total of one dispatch. -/
theorem total_charge (a b c e o : ℕ) : totalCost (charge a b c e o) = a + 1 + b + c + e + o := by
  simp [totalCost, charge]
  omega

omit [DecidableEq F] in
private theorem scale_trace (j : ℕ) (c a : F) (k : ℕ) (fs pre : List (ℕ × ℕ))
    (ts out : List (Term F)) :
    Trace j (k + 1) (.scale c k a fs pre ts out)
      ⟨⟨k, 0, k + 1, 5 * k + 1, 2 * k + 1, 0⟩, 0⟩ (.test (a + k • c) fs pre ts out) := by
  induction k generalizing a with
  | zero => simpa [charge] using
      Trace.cons (Step.scaled (j := j) (c := c) (a := a)) (Trace.nil _)
  | succ k ih =>
      simpa [charge, add_nsmul, Nat.mul_add, add_mul, add_assoc, add_comm, add_left_comm] using
        Trace.cons Step.add (ih (a + c))

omit [DecidableEq F] in
private theorem restore_trace (j : ℕ) (c : F) (pre fs : List (ℕ × ℕ)) (ts out : List (Term F)) :
    Trace j (pre.length + 1) (.restore c pre fs ts out)
      ⟨⟨0, 0, pre.length + 1, 5 * pre.length + 5, 0, 1⟩, 0⟩
      (.terms ts ((c, pre.reverse ++ fs) :: out)) := by
  induction pre generalizing fs with
  | nil => simpa [charge] using Trace.cons (Step.store (j := j) (c := c)) (Trace.nil _)
  | cons x xs ih =>
      simpa [charge, List.reverse_cons, List.append_assoc, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons Step.restore (ih (x :: fs))

private theorem test_trace (j : ℕ) (c : F) (fs pre : List (ℕ × ℕ)) (ts out : List (Term F)) :
    ∃ k cost, Trace j k (.test c fs pre ts out) cost
      (.terms ts (stored pre (if c = 0 then none else some (c, fs)) out)) ∧
      k + totalCost cost ≤ 7 * pre.length + 13 := by
  by_cases hc : c = 0
  · subst c
    refine ⟨1, charge 0 2 0 1 0, ?_, ?_⟩
    · simpa [stored] using Trace.cons (Step.zeroCoefficient (j := j) (fs := fs)) (Trace.nil _)
    · simp [total_charge]
  · refine ⟨pre.length + 1 + 1, charge 0 2 0 1 0 +
      ⟨⟨0, 0, pre.length + 1, 5 * pre.length + 5, 0, 1⟩, 0⟩, ?_, ?_⟩
    · simpa [stored, hc] using Trace.cons (Step.nonzero hc) (restore_trace j c pre fs ts out)
    · simp [totalCost, charge]
      omega

private theorem scan_trace (j : ℕ) (c : F) (fs pre : List (ℕ × ℕ)) (ts out : List (Term F)) :
    ∃ k cost, Trace j k (.scan c fs pre ts out) cost
      (.terms ts (stored pre (derivativeTerm j c fs) out)) ∧
      k + totalCost cost ≤ 20 * (factorMass fs + pre.length) := by
  induction fs generalizing pre with
  | nil =>
      refine ⟨1, charge 0 1 0 0 0, ?_, ?_⟩
      · simpa [derivativeTerm, stored] using
          Trace.cons (Step.absent (j := j) (c := c)) (Trace.nil _)
      · simp [total_charge, factorMass]
        omega
  | cons p fs ih =>
      rcases p with ⟨i, e⟩
      by_cases hij : i = j
      · subst i
        cases e with
        | zero =>
            refine ⟨1, charge 0 2 2 0 0, ?_, ?_⟩
            · simpa [derivativeTerm, stored] using
                Trace.cons (Step.zeroExponent (j := j) (c := c)) (Trace.nil _)
            · simp [total_charge, factorMass]
              omega
        | succ e =>
            have hs := scale_trace j c 0 (e + 1) ((j, e) :: fs) pre ts out
            simp only [zero_add] at hs
            obtain ⟨k, cost, ht, hb⟩ := test_trace j ((e + 1) • c) ((j, e) :: fs) pre ts out
            have h := Trace.cons Step.hit (hs.trans ht)
            refine ⟨e + 1 + 1 + k + 1, charge 0 7 3 0 0 +
              (⟨⟨e + 1, 0, e + 1 + 1, 5 * (e + 1) + 1, 2 * (e + 1) + 1, 0⟩, 0⟩ +
                cost), ?_, ?_⟩
            · simpa [derivativeTerm] using h
            · simp only [total_add, total_charge]
              simp only [totalCost, factorMass, List.length_cons, List.map_cons, List.sum_cons]
              unfold totalCost at hb
              omega
      · obtain ⟨k, cost, ht, hb⟩ := ih ((i, e) :: pre)
        have he : stored ((i, e) :: pre) (derivativeTerm j c fs) out =
            stored pre (derivativeTerm j c ((i, e) :: fs)) out := by
          cases hd : derivativeTerm j c fs with
          | none => simp [derivativeTerm, hij, stored, hd]
          | some t =>
              cases t
              simp [derivativeTerm, hij, stored, hd, List.reverse_cons, List.append_assoc]
        refine ⟨k + 1, charge 0 6 1 0 0 + cost, ?_, ?_⟩
        · rw [← he]
          exact Trace.cons (Step.skip hij) ht
        · rw [total_add, total_charge]
          simp only [factorMass, List.length_cons, List.map_cons, List.sum_cons] at hb ⊢
          omega

private theorem terms_trace (j : ℕ) (ts out : List (Term F)) :
    ∃ k cost, Trace j k (.terms ts out) cost (.terms [] ((derivativeTerms j ts).reverse ++ out)) ∧
      k + totalCost cost ≤ 30 * inputMass ts := by
  induction ts generalizing out with
  | nil =>
      exact ⟨0, 0, by simpa [derivativeTerms] using Trace.nil (.terms [] out), by simp [totalCost]⟩
  | cons t ts ih =>
      rcases t with ⟨c, fs⟩
      obtain ⟨ks, cs, hs, hsc⟩ := scan_trace j c fs [] ts out
      obtain ⟨kt, ct, ht, htc⟩ := ih (stored [] (derivativeTerm j c fs) out)
      have h := Trace.cons Step.term (hs.trans ht)
      refine ⟨ks + kt + 1, charge 0 4 0 0 0 + (cs + ct), ?_, ?_⟩
      · convert h using 1
        cases hd : derivativeTerm j c fs with
        | none => simp [derivativeTerms, stored, hd]
        | some t => cases t; simp [derivativeTerms, stored, hd, List.append_assoc]
      · simp only [total_add, total_charge]
        simp only [List.length_nil, Nat.add_zero] at hsc
        have hm : 1 ≤ factorMass fs := by unfold factorMass; omega
        simp only [inputMass, List.map_cons, List.sum_cons]
        unfold inputMass at htc
        omega

omit [DecidableEq F] in
private theorem reverse_trace (j : ℕ) (ts out : List (Term F)) :
    Trace j (ts.length + 1) (.reverse ts out)
      ⟨⟨0, 0, ts.length + 1, 5 * ts.length + 2, 0, 1⟩, 0⟩ (.done (ts.reverse ++ out)) := by
  induction ts generalizing out with
  | nil => simpa [charge] using Trace.cons (Step.emit (j := j) (out := out)) (Trace.nil _)
  | cons t ts ih =>
      simpa [charge, List.reverse_cons, List.append_assoc, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Trace.cons Step.reverse (ih (t :: out))

/-- The output term count is bounded by the numerical input work measure. -/
theorem derivativeTerms_length_le (j : ℕ) (ts : List (Term F)) :
    (derivativeTerms j ts).length ≤ inputMass ts := by
  induction ts with
  | nil => simp [derivativeTerms, inputMass]
  | cons t ts ih =>
      rcases t with ⟨c, fs⟩
      have hh : (derivativeTerm j c fs).toList.length ≤ 1 := by cases derivativeTerm j c fs <;> simp
      have hm : 1 ≤ factorMass fs := by unfold factorMass; omega
      simp only [derivativeTerms, List.length_append, inputMass, List.map_cons, List.sum_cons]
      unfold inputMass at ih
      omega

/-- Actual bounded execution returns first-occurrence differentiation with a numerical
polynomial primitive-cost bound. This operational theorem does not require canonical input. -/
theorem evaluation_runFuel (j : ℕ) (ts : List (Term F)) :
    ∃ cost, runFuel j (budget ts) (.terms ts []) = (.done (derivativeTerms j ts), cost) ∧
      totalCost cost ≤ budget ts := by
  obtain ⟨k, c, ht, hb⟩ := terms_trace j ts []
  simp only [List.append_nil] at ht
  have hr := reverse_trace j (derivativeTerms j ts).reverse []
  simp only [List.reverse_reverse, List.append_nil, List.length_reverse] at hr
  have h := ht.trans (Trace.cons Step.finish hr)
  have hl := derivativeTerms_length_le j ts
  have hw : k + ((derivativeTerms j ts).length + 1 + 1) +
      totalCost (c + (charge 0 3 0 0 0 +
        ⟨⟨0, 0, (derivativeTerms j ts).length + 1,
          5 * (derivativeTerms j ts).length + 2, 0, 1⟩, 0⟩))
        ≤ budget ts := by
    rw [total_add, total_add, total_charge]
    simp only [totalCost] at hb ⊢
    unfold budget
    omega
  have hrun := h.runFuel_done (budget ts - (k + ((derivativeTerms j ts).length + 1 + 1)))
  rw [show k + ((derivativeTerms j ts).length + 1 + 1) +
    (budget ts - (k + ((derivativeTerms j ts).length + 1 + 1))) = budget ts by omega] at hrun
  exact ⟨_, hrun, by omega⟩

/-- Canonicality is local to each factor list. Duplicate terms are permitted. -/
def Canonical (ts : List (Term F)) : Prop := ∀ t ∈ ts, (t.2.map Prod.fst).Nodup

/-- A surviving derivative term retains precisely the same ordered variable indices. -/
theorem derivativeTerm_variables (j : ℕ) (c : F) (fs : List (ℕ × ℕ))
    {t : Term F} (h : derivativeTerm j c fs = some t) : t.2.map Prod.fst = fs.map Prod.fst := by
  induction fs generalizing t with
  | nil => simp [derivativeTerm] at h
  | cons p fs ih =>
      rcases p with ⟨i, e⟩
      by_cases hij : i = j
      · simp only [derivativeTerm, if_pos hij] at h
        split_ifs at h with he hc
        cases h
        rfl
      · simp only [derivativeTerm, if_neg hij] at h
        cases hd : derivativeTerm j c fs with
        | none => simp [hd] at h
        | some u =>
            simp only [hd, Option.map_some, Option.some.injEq] at h
            subst t
            simp [ih hd]

/-- Differentiation preserves the per-term distinct-variable invariant. -/
theorem derivativeTerms_canonical (j : ℕ) (ts : List (Term F)) (h : Canonical ts) :
    Canonical (derivativeTerms j ts) := by
  induction ts with
  | nil => simp [Canonical, derivativeTerms]
  | cons t ts ih =>
      rcases t with ⟨c, fs⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · have hd : derivativeTerm j c fs = some u := by simpa using hu
        rw [derivativeTerm_variables j c fs hd]
        exact h (c, fs) (by simp)
      · exact ih (fun v hv => h v (by simp [hv])) u hu

omit [DecidableEq F] in
private theorem pderiv_factors_eq_zero (j : ℕ) (fs : List (ℕ × ℕ))
    (h : ∀ p ∈ fs, p.1 ≠ j) : pderiv j (factorsPolynomial (F := F) fs) = 0 := by
  induction fs with
  | nil => simp [factorsPolynomial]
  | cons p fs ih =>
      rcases p with ⟨i, e⟩
      have hi := h (i, e) (by simp)
      have ht := ih (fun p hp => h p (by simp [hp]))
      simp [factorsPolynomial, hi, ht]

omit [DecidableEq F] in
private theorem sparsePolynomial_append (a b : List (Term F)) :
    sparsePolynomial (a ++ b) = sparsePolynomial a + sparsePolynomial b := by
  induction a with
  | nil => simp [sparsePolynomial]
  | cons t ts ih => cases t; simp [sparsePolynomial, ih, add_assoc]

omit [DecidableEq F] in
private theorem sparsePolynomial_prepend_factor (p : ℕ × ℕ) (t : Option (Term F)) :
    sparsePolynomial ((t.map fun u => (u.1, p :: u.2)).toList) =
      X p.1 ^ p.2 * sparsePolynomial t.toList := by
  cases t with
  | none => simp [sparsePolynomial]
  | some t => cases t; simp [sparsePolynomial, factorsPolynomial]; ring

/-- First-occurrence differentiation denotes the actual partial derivative when a term has
no repeated variable indices. Arbitrary variable order and zero factors are included. -/
theorem sparsePolynomial_derivativeTerm (j : ℕ) (c : F) (fs : List (ℕ × ℕ))
    (h : (fs.map Prod.fst).Nodup) :
    sparsePolynomial (derivativeTerm j c fs).toList = pderiv j (C c * factorsPolynomial fs) := by
  induction fs with
  | nil => simp [derivativeTerm, sparsePolynomial, factorsPolynomial]
  | cons p fs ih =>
      rcases p with ⟨i, e⟩
      obtain ⟨hn, ht⟩ := List.nodup_cons.mp h
      by_cases hij : i = j
      · subst i
        have hf : pderiv j (factorsPolynomial (F := F) fs) = 0 :=
          pderiv_factors_eq_zero j fs (by
            intro p hp he
            apply hn
            exact List.mem_map.mpr ⟨p, hp, he⟩)
        have hd : pderiv j (C c * factorsPolynomial ((j, e) :: fs)) =
            C (e • c) * (X j ^ (e - 1) * factorsPolynomial fs) := by
          simp [factorsPolynomial, hf, nsmul_eq_mul]
          ring
        rw [hd]
        by_cases he : e = 0
        · subst e
          simp [derivativeTerm, sparsePolynomial]
        · by_cases hc : e • c = 0
          · simp [derivativeTerm, he, hc, sparsePolynomial]
          · rw [derivativeTerm, if_pos rfl, if_neg he, if_neg hc]
            simp [sparsePolynomial, factorsPolynomial]
      · rw [derivativeTerm, if_neg hij, sparsePolynomial_prepend_factor, ih ht]
        simp [factorsPolynomial, hij]
        ring

/-- The complete sparse output denotes the partial derivative; duplicate terms require no
normalization because differentiation is additive. -/
theorem sparsePolynomial_derivativeTerms (j : ℕ) (ts : List (Term F)) (h : Canonical ts) :
    sparsePolynomial (derivativeTerms j ts) = pderiv j (sparsePolynomial ts) := by
  induction ts with
  | nil => simp [derivativeTerms, sparsePolynomial]
  | cons t ts ih =>
      rcases t with ⟨c, fs⟩
      rw [derivativeTerms, sparsePolynomial_append,
        sparsePolynomial_derivativeTerm j c fs (h (c, fs) (by simp)),
        ih (fun t ht => h t (by simp [ht]))]
      simp [sparsePolynomial]

/-- Bounded actual execution computes the formal partial derivative and preserves canonicality.
The bound counts coefficient scaling by numerical exponent, not a unit-cost scalar cast. -/
theorem evaluation_runFuel_eq_pderiv (j : ℕ) (ts : List (Term F)) (h : Canonical ts) :
    ∃ out cost, runFuel j (budget ts) (.terms ts []) = (.done out, cost) ∧
      sparsePolynomial out = pderiv j (sparsePolynomial ts) ∧ Canonical out ∧
      totalCost cost ≤ budget ts := by
  obtain ⟨c, hc, hb⟩ := evaluation_runFuel j ts
  exact ⟨derivativeTerms j ts, c, hc, sparsePolynomial_derivativeTerms j ts h,
    derivativeTerms_canonical j ts h, hb⟩

end MvPolynomial.PartialDerivativeMachine
