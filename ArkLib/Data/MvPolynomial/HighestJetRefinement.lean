/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.MvPolynomial.HighestJetMachine

/-!
# Highest-jet execution, degree correctness and cost

The scan invariant is a lexicographic maximum over positive variable/exponent pairs. Its
mathematical interpretation uses normalization's exact nonzero-coefficient characterization.
-/

@[expose] public section

namespace MvPolynomial.HighestJetMachine

open DenseNormalizeMachine (normalize DenseLayout Normalized factorExponents)
open EvaluationMachine (sparsePolynomial)

/-- Only positive-index variables with positive exponents count as active jets. -/
def Active (p : ℕ × ℕ) : Prop := 0 < p.1 ∧ 0 < p.2

/-- Lexicographic upper bound: index first, then exponent at the same index. -/
def Dominates (p b : ℕ × ℕ) : Prop := p.1 ≤ b.1 ∧ (p.1 = b.1 → p.2 ≤ b.2)

/-- Exact register invariant: either no active pair, or an attained active upper bound. -/
def Register (ps : List (ℕ × ℕ)) : Option (ℕ × ℕ) → Prop
  | none => ∀ p ∈ ps, ¬Active p
  | some b => b ∈ ps ∧ Active b ∧ ∀ p ∈ ps, Active p → Dominates p b

private theorem dominates_trans {p b c : ℕ × ℕ} (h : Dominates p b)
    (h' : Dominates b c) : Dominates p c := by
  unfold Dominates at *
  constructor <;> omega

private theorem register_congr {ps qs : List (ℕ × ℕ)} {b : Option (ℕ × ℕ)}
    (hm : ∀ p, p ∈ ps ↔ p ∈ qs) (h : Register ps b) : Register qs b := by
  cases b with
  | none => exact fun p hp => h p ((hm p).mpr hp)
  | some b => exact ⟨(hm b).mp h.1, h.2.1, fun p hp => h.2.2 p ((hm p).mpr hp)⟩

/-- Each actual local comparison preserves an attained maximum over processed factors. -/
theorem Update.register {p : ℕ × ℕ} {b r : Option (ℕ × ℕ)} (hu : Update p b r)
    (ps : List (ℕ × ℕ)) (h : Register ps b) : Register (p :: ps) r := by
  cases hu with
  | skip hp =>
      have hn : ¬Active p := by unfold Active; omega
      cases b with
      | none =>
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq
          · exact hn
          · exact h q hq
      | some b =>
          refine ⟨by simp [h.1], h.2.1, ?_⟩
          intro q hq ha
          rcases List.mem_cons.mp hq with rfl | hq
          · exact (hn ha).elim
          · exact h.2.2 q hq ha
  | first hp =>
      refine ⟨by simp, by unfold Active; omega, ?_⟩
      intro q hq ha
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨le_rfl, fun _ => le_rfl⟩
      · exact (h q hq ha).elim
  | @higher b hp hi =>
      refine ⟨by simp, by unfold Active; omega, ?_⟩
      intro q hq ha
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨le_rfl, fun _ => le_rfl⟩
      · exact dominates_trans (h.2.2 q hq ha) ⟨by omega, by omega⟩
  | @larger b hp hi he =>
      refine ⟨by simp, by unfold Active; omega, ?_⟩
      intro q hq ha
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨le_rfl, fun _ => le_rfl⟩
      · exact dominates_trans (h.2.2 q hq ha) ⟨by omega, by omega⟩
  | @keep b hp hi he =>
      refine ⟨by simp [h.1], h.2.1, ?_⟩
      intro q hq ha
      rcases List.mem_cons.mp hq with rfl | hq
      · exact ⟨hi, he⟩
      · exact h.2.2 q hq ha

/-- Declarative scan specification; the machine implements every update as a charged step. -/
def scan : List (ℕ × ℕ) → Option (ℕ × ℕ) → Option (ℕ × ℕ)
  | [], b => b
  | p :: ps, b => scan ps (update p b)

/-- Declarative term traversal. -/
def select {F : Type*} : List (Term F) → Option (ℕ × ℕ) → Option (ℕ × ℕ)
  | [], b => b
  | t :: ts, b => select ts (scan t.2 b)

/-- The factor scan computes the exact maximum, including its witness. -/
theorem scan_register (fs ps : List (ℕ × ℕ)) (b : Option (ℕ × ℕ))
    (h : Register ps b) : Register (fs ++ ps) (scan fs b) := by
  induction fs generalizing ps b with
  | nil => exact h
  | cons p fs ih =>
      apply register_congr _ (ih (p :: ps) _ ((update_sound p b).register ps h))
      intro q
      simp only [List.mem_append, List.mem_cons]
      tauto

/-- The term scan computes the exact maximum over all materialized factors. -/
theorem select_register {F : Type*} (ts : List (Term F)) (ps : List (ℕ × ℕ))
    (b : Option (ℕ × ℕ)) (h : Register ps b) :
    Register (ts.flatMap Prod.snd ++ ps) (select ts b) := by
  induction ts generalizing ps b with
  | nil => exact h
  | cons t ts ih =>
      apply register_congr _ (ih (t.2 ++ ps) _ (scan_register t.2 ps b h))
      intro q
      simp only [List.flatMap_cons, List.mem_append]
      tauto

abbrev totalCost := PartialDerivativeMachine.totalCost

private theorem total_add (a b : Cost) : totalCost (a + b) = totalCost a + totalCost b :=
  PartialDerivativeMachine.total_add a b

private theorem total_charge (a d n e o : ℕ) :
    totalCost (charge a d n e o) = a + 1 + d + n + e + o :=
  PartialDerivativeMachine.total_charge a d n e o

/-- Uniform fuel and primitive bound, including normalization and scan initialization. -/
def budget (m L : ℕ) : ℕ := 5 * DenseNormalizeMachine.budget m L + m * (13 * L + 9) + 9

variable {F : Type*} [CommSemiring F] [DecidableEq F]

omit [DecidableEq F] in
private theorem factors_trace (fs : List (ℕ × ℕ)) (ts : List (Term F))
    (b : Option (ℕ × ℕ)) :
    ∃ k c, Trace k (.factors fs ts b) c (.terms ts (scan fs b)) ∧
      k + totalCost c ≤ 13 * fs.length + 4 := by
  induction fs generalizing b with
  | nil =>
      refine ⟨1, charge 0 2 0 0 0, Trace.cons Step.next (Trace.nil _), ?_⟩
      simp [total_charge]
  | cons p fs ih =>
      obtain ⟨k, c, ht, hc⟩ := ih (update p b)
      refine ⟨k + 1, charge 0 6 5 0 0 + c,
        Trace.cons (Step.factor (update_sound p b)) ht, ?_⟩
      rw [total_add, total_charge]
      simp only [List.length_cons]
      omega

omit [DecidableEq F] in
private theorem terms_trace (L : ℕ) (ts : List (Term F)) (b : Option (ℕ × ℕ))
    (hlen : ∀ t ∈ ts, t.2.length ≤ L) :
    ∃ k c, Trace k (.terms ts b) c (.done (select ts b)) ∧
      k + totalCost c ≤ ts.length * (13 * L + 9) + 5 := by
  induction ts generalizing b with
  | nil =>
      refine ⟨1, charge 0 2 0 0 1, Trace.cons Step.emit (Trace.nil _), ?_⟩
      simp [total_charge]
  | cons t ts ih =>
      rcases t with ⟨a, fs⟩
      obtain ⟨kf, cf, hf, hb⟩ := factors_trace fs ts b
      obtain ⟨kt, ct, ht, hc⟩ := ih (scan fs b) (fun t hm => hlen t (by simp [hm]))
      refine ⟨kf + kt + 1, charge 0 3 0 0 0 + (cf + ct),
        Trace.cons Step.term (hf.trans ht), ?_⟩
      simp only [total_add, total_charge, List.length_cons]
      have hl : fs.length ≤ L := hlen (a, fs) (by simp)
      nlinarith

omit [DecidableEq F] in
private theorem lift_normalize {k : ℕ} {s t : DenseNormalizeMachine.Configuration F}
    {c : Cost} (h : DenseNormalizeMachine.Trace k s c t) :
    Trace k (.normalizing s) (⟨⟨0, 0, k, 2 * k, 0, 0⟩, 0⟩ + c) (.normalizing t) := by
  induction h with
  | nil s => simpa using Trace.nil (.normalizing s)
  | @cons n s u t c e head tail ih =>
      have ht := Trace.cons (Step.normalize head) ih
      convert ht using 1
      · simp [charge, PartialDerivativeMachine.charge, Nat.mul_add,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

private theorem normalize_length (ts out : List (Term F)) :
    (normalize ts out).length ≤ ts.length + out.length := by
  induction ts generalizing out with
  | nil => simp [normalize]
  | cons t ts ih =>
      rcases t with ⟨c, fs⟩
      by_cases hc : c = 0
      · simp only [normalize, if_pos hc, List.length_cons]
        have h := ih out
        omega
      · simp only [normalize, if_neg hc, List.length_cons]
        have hi := DenseNormalizeMachine.insertTerm_length_le c fs out
        have h := ih (DenseNormalizeMachine.insertTerm c fs out)
        omega

/-- The combined machine executes normalization and the complete scan within its charged bound. -/
theorem evaluation_runFuel (vars : List ℕ) (ts : List (Term F)) (hl : DenseLayout vars ts) :
    ∃ c, runFuel (budget ts.length vars.length) (.normalizing (.terms ts [])) =
        (.done (select (normalize ts []) none), c) ∧
      totalCost c ≤ budget ts.length vars.length := by
  obtain ⟨cn, hr, hn⟩ := DenseNormalizeMachine.evaluation_runFuel vars.length ts (by
    intro t ht
    have he := congrArg List.length (hl.2 t ht)
    simpa using he.le)
  obtain ⟨kn, hkn, htn⟩ := DenseNormalizeMachine.runFuel_refines
    (DenseNormalizeMachine.budget ts.length vars.length) (.terms ts [])
  rw [hr] at htn
  have hd := DenseNormalizeMachine.normalize_denseLayout vars ts hl
  obtain ⟨ks, cs, hts, hbs⟩ := terms_trace vars.length (normalize ts []) none (by
    intro t ht
    have he := congrArg List.length (hd.2 t ht)
    simpa using he.le)
  have ht := (lift_normalize htn).trans (Trace.cons Step.normalized hts)
  have hlen : (normalize ts []).length ≤ ts.length := by simpa using normalize_length ts []
  let cw : Cost := ⟨⟨0, 0, kn, 2 * kn, 0, 0⟩, 0⟩
  have hw : totalCost cw = 3 * kn := by
    simp [cw, totalCost, PartialDerivativeMachine.totalCost]
    omega
  have hb : kn + (ks + 1) + totalCost ((cw + cn) + (charge 0 2 0 0 0 + cs)) ≤
      budget ts.length vars.length := by
    simp only [total_add, total_charge, hw]
    unfold budget
    have hm := Nat.mul_le_mul_right (13 * vars.length + 9) hlen
    change totalCost cn ≤ _ at hn
    omega
  have he := ht.runFuel_done (budget ts.length vars.length - (kn + (ks + 1)))
  rw [show kn + (ks + 1) + (budget ts.length vars.length - (kn + (ks + 1))) =
    budget ts.length vars.length by omega] at he
  refine ⟨(cw + cn) + (charge 0 2 0 0 0 + cs), he, ?_⟩
  omega

private theorem exponents_absent (fs : List (ℕ × ℕ)) (i : ℕ)
    (h : i ∉ fs.map Prod.fst) : factorExponents fs i = 0 := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
      rcases p with ⟨j, e⟩
      simp only [List.map_cons, List.mem_cons, not_or] at h
      simp [factorExponents, Ne.symm h.1, ih h.2]

/-- A dense key's stored exponent is exactly its semantic monomial coordinate. -/
theorem exponents_of_mem (fs : List (ℕ × ℕ)) (hn : (fs.map Prod.fst).Nodup)
    (i e : ℕ) (hm : (i, e) ∈ fs) : factorExponents fs i = e := by
  induction fs with
  | nil => simp at hm
  | cons p fs ih =>
      rcases p with ⟨j, f⟩
      obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hm with he | hm
      · cases he
        simp [factorExponents, exponents_absent fs i hnot]
      · have hne : j ≠ i := by
          intro he
          apply hnot
          simpa only [he] using List.mem_map_of_mem (f := Prod.fst) hm
        simp [factorExponents, hne, ih htail hm]

/-- Exact individual-degree bounds can be checked against every surviving dense exponent. -/
theorem degree_le_iff (vars : List ℕ) (ts : List (Term F)) (hl : DenseLayout vars ts)
    (i k : ℕ) : (sparsePolynomial ts).degreeOf i ≤ k ↔
      ∀ t ∈ normalize ts [], ∀ e, (i, e) ∈ t.2 → e ≤ k := by
  have hd := DenseNormalizeMachine.normalize_denseLayout vars ts hl
  constructor
  · intro h t ht e he
    have hc := DenseNormalizeMachine.normalize_coefficient vars ts hl t ht
    have hm : factorExponents t.2 ∈ (sparsePolynomial ts).support := by
      rw [mem_support_iff, hc.1]
      exact hc.2
    have hn : (t.2.map Prod.fst).Nodup := hd.2 t ht ▸ hd.1
    rw [← exponents_of_mem t.2 hn i e he]
    exact (monomial_le_degreeOf i hm).trans h
  · intro h
    apply degreeOf_le_iff.mpr
    intro v hv
    obtain ⟨t, ht, rfl⟩ :=
      (DenseNormalizeMachine.normalize_coeff_ne_zero_iff vars ts hl v).mp
        (mem_support_iff.mp hv)
    by_cases ha : i ∈ t.2.map Prod.fst
    · obtain ⟨p, hp, he⟩ := List.mem_map.mp ha
      rcases p with ⟨j, e⟩
      dsimp only at he
      subst j
      have hn : (t.2.map Prod.fst).Nodup := hd.2 t ht ▸ hd.1
      rw [exponents_of_mem t.2 hn i e hp]
      exact h t ht e hp
    · rw [exponents_absent t.2 i ha]
      exact Nat.zero_le _

/-- The scan returns an attained maximum of the normalized factors. -/
theorem normalized_register (ts : List (Term F)) :
    Register ((normalize ts []).flatMap Prod.snd) (select (normalize ts []) none) := by
  simpa only [List.append_nil] using select_register (normalize ts []) [] none (by
    intro p hp
    simp at hp)

/-- A successful selection has positive exact individual degree and no higher active variable. -/
theorem select_some_correct (vars : List ℕ) (ts : List (Term F)) (hl : DenseLayout vars ts)
    (i e : ℕ) (hs : select (normalize ts []) none = some (i, e)) :
    0 < i ∧ 0 < e ∧ (sparsePolynomial ts).degreeOf i = e ∧
      (∀ j, i < j → (sparsePolynomial ts).degreeOf j = 0) ∧ i ∈ vars := by
  have hr := normalized_register ts
  rw [hs] at hr
  obtain ⟨hm, ha, hb⟩ := hr
  obtain ⟨t, ht, he⟩ := List.mem_flatMap.mp hm
  have hd := DenseNormalizeMachine.normalize_denseLayout vars ts hl
  have hv : i ∈ vars := by
    rw [← hd.2 t ht]
    exact List.mem_map_of_mem he
  have hle : (sparsePolynomial ts).degreeOf i ≤ e := by
    apply (degree_le_iff vars ts hl i e).mpr
    intro u hu f hf
    by_cases hz : f = 0
    · omega
    · exact (hb (i, f) (List.mem_flatMap.mpr ⟨u, hu, hf⟩) ⟨ha.1, by omega⟩).2 rfl
  have hge : e ≤ (sparsePolynomial ts).degreeOf i :=
    (degree_le_iff vars ts hl i _).mp le_rfl t ht e he
  refine ⟨ha.1, ha.2, Nat.le_antisymm hle hge, ?_, hv⟩
  intro j hj
  apply Nat.eq_zero_of_le_zero
  apply (degree_le_iff vars ts hl j 0).mpr
  intro u hu f hf
  by_contra hn
  have hp : Active (j, f) := ⟨by omega, by omega⟩
  have hu := (hb (j, f) (List.mem_flatMap.mpr ⟨u, hu, hf⟩) hp).1
  omega

/-- No result is returned exactly when every positive-index variable has individual degree zero. -/
theorem select_none_iff (vars : List ℕ) (ts : List (Term F)) (hl : DenseLayout vars ts) :
    select (normalize ts []) none = none ↔ ∀ i, 0 < i → (sparsePolynomial ts).degreeOf i = 0 := by
  constructor
  · intro hs i hi
    have hr := normalized_register ts
    rw [hs] at hr
    apply Nat.eq_zero_of_le_zero
    apply (degree_le_iff vars ts hl i 0).mpr
    intro t ht e he
    have hn := hr (i, e) (List.mem_flatMap.mpr ⟨t, ht, he⟩)
    unfold Active at hn
    omega
  · intro h
    cases hs : select (normalize ts []) none with
    | none => rfl
    | some p =>
        obtain ⟨hi, he, hd, _⟩ := select_some_correct vars ts hl p.1 p.2 hs
        have hz := h p.1 hi
        omega

/-- Normalization's empty output is an exact zero-polynomial test under the dense layout. -/
theorem normalize_empty_iff (vars : List ℕ) (ts : List (Term F)) (hl : DenseLayout vars ts) :
    normalize ts [] = [] ↔ sparsePolynomial ts = 0 := by
  constructor
  · intro h
    have he := DenseNormalizeMachine.normalize_polynomial ts []
    simpa [h, sparsePolynomial] using he.symm
  · intro h
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro t ht
    obtain ⟨he, hn⟩ := DenseNormalizeMachine.normalize_coefficient vars ts hl t ht
    simp only [h, coeff_zero] at he
    exact hn he.symm

end MvPolynomial.HighestJetMachine
