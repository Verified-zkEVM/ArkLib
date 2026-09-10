/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Polynomial.JetHornerMachine

/-!
# Closed indexed update of descending coefficients

Inputs are a materialized descending coefficient list, a natural index, and a scalar increment.
Traversal copies the prefix into a reversed buffer. One addition updates the selected cell;
restoration copies the prefix back while sharing the untouched suffix. Out-of-range indices
produce failure, and both success and failure have a separately charged emission transition.

Costs use the jet machine's primitive model: a cell read retrieves head and tail, retained
registers are shared, and literals are free. Control, data accesses, index tests/decrements,
addition, and emission are charged. Input padding, computation of a lifting index, host fuel
bookkeeping, and scalar bit costs remain separate obligations. Polynomial operations and bulk
list operations below appear only in specifications and proofs.
-/

@[expose] public section

namespace Polynomial.CoefficientUpdateMachine

abbrev Cost := JetHornerMachine.Cost

/-- Initialize the cursor, index register and empty prefix buffer. -/
def startCost : Cost := ⟨0, 0, 1, 5, 0, 0⟩
/-- Read cell/index/buffer, allocate a prefix cell and update the cursor; test/decrement index. -/
def advanceCost : Cost := ⟨0, 0, 1, 8, 2, 0⟩
/-- Read the selected cell and index, and retain its scalar for the addition phase. -/
def selectCost : Cost := ⟨0, 0, 1, 4, 1, 0⟩
/-- Read scalar and increment, add once, allocate the updated cell and write its root. -/
def addCost : Cost := ⟨1, 0, 1, 5, 0, 0⟩
/-- Read prefix cell and result root, allocate a restored cell and update both roots. -/
def restoreCost : Cost := ⟨0, 0, 1, 6, 0, 0⟩
/-- Read exhausted prefix and result root; retain the success payload for emission. -/
def finishCost : Cost := ⟨0, 0, 1, 3, 0, 0⟩
/-- Read the empty input cursor and write the failure payload. -/
def rejectCost : Cost := ⟨0, 0, 1, 2, 0, 0⟩
/-- Read and emit the result handle, including its success/failure tag. -/
def emitCost : Cost := ⟨0, 0, 1, 2, 0, 1⟩

/-- Fixed phases expose traversal, addition, restoration, and result emission. -/
inductive Configuration (F : Type*) where
  | start (cs : List F) (index : ℕ)
  | scan (index : ℕ) (remaining reversed : List F)
  | add (value : F) (tail reversed : List F)
  | restore (reversed result : List F)
  | emit (result : Option (List F))
  | done (result : Option (List F))
  deriving DecidableEq, Repr

variable {F : Type*} [CommSemiring F]

/-- Independent rules fix every operational step and charge. -/
inductive Step (gamma : F) : Configuration F → Cost → Configuration F → Prop where
  | start {cs j} : Step gamma (.start cs j) startCost (.scan j cs [])
  | reject {j rev} : Step gamma (.scan j [] rev) rejectCost (.emit none)
  | advance {j c cs rev} : Step gamma (.scan (j + 1) (c :: cs) rev) advanceCost
      (.scan j cs (c :: rev))
  | select {c cs rev} : Step gamma (.scan 0 (c :: cs) rev) selectCost (.add c cs rev)
  | add {c cs rev} : Step gamma (.add c cs rev) addCost (.restore rev ((c + gamma) :: cs))
  | restore {c rev out} : Step gamma (.restore (c :: rev) out) restoreCost
      (.restore rev (c :: out))
  | finish {out} : Step gamma (.restore [] out) finishCost (.emit (some out))
  | emit {out} : Step gamma (.emit out) emitCost (.done out)

/-- Literal dispatch neither traverses the suffix nor calls a bulk list update. -/
def step (gamma : F) : Configuration F → Option (Configuration F × Cost)
  | .start cs j => some (.scan j cs [], startCost)
  | .scan _ [] _ => some (.emit none, rejectCost)
  | .scan 0 (c :: cs) rev => some (.add c cs rev, selectCost)
  | .scan (j + 1) (c :: cs) rev => some (.scan j cs (c :: rev), advanceCost)
  | .add c cs rev => some (.restore rev ((c + gamma) :: cs), addCost)
  | .restore (c :: rev) out => some (.restore rev (c :: out), restoreCost)
  | .restore [] out => some (.emit (some out), finishCost)
  | .emit out => some (.done out, emitCost)
  | .done _ => none

/-- Independent operational rules agree with executable dispatch. -/
theorem Step.step_eq {gamma : F} {s t : Configuration F} {c : Cost} (h : Step gamma s c t) :
    step gamma s = some (t, c) := by cases h <;> rfl

/-- Every dispatch branch has an independent operational rule. -/
theorem step_sound {gamma : F} {s t : Configuration F} {c : Cost}
    (h : step gamma s = some (t, c)) : Step gamma s c t := by
  cases s with
  | start cs j => cases h; constructor
  | scan j cs rev => cases cs <;> cases j <;> cases h <;> constructor
  | add c cs rev => cases h; constructor
  | restore rev out => cases rev <;> cases h <;> constructor
  | emit out => cases h; constructor
  | done out => simp [step] at h

/-- Exact transition equivalence includes the charged cost. -/
theorem step_iff {gamma : F} {s t : Configuration F} {c : Cost} :
    step gamma s = some (t, c) ↔ Step gamma s c t := ⟨step_sound, Step.step_eq⟩

/-- Traces accumulate every actual transition charge. -/
inductive Trace (gamma : F) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace gamma 0 s 0 s
  | cons {n s u t c d} (head : Step gamma s c u) (tail : Trace gamma n u d t) :
      Trace gamma (n + 1) s (c + d) t

/-- Insufficient fuel returns the reached state without fabricating a result. -/
def runFuel (gamma : F) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step gamma s with
      | none => (s, 0)
      | some (t, c) => let result := runFuel gamma n t; (result.1, c + result.2)

/-- Every run refines an actual trace, including runs with insufficient fuel. -/
theorem runFuel_refines (gamma : F) (fuel : ℕ) (s : Configuration F) :
    ∃ n ≤ fuel, Trace gamma n s (runFuel gamma fuel s).2 (runFuel gamma fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step gamma s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- A completed trace consumes no additional operations under extra host fuel. -/
theorem Trace.runFuel_done {gamma : F} {n : ℕ} {s : Configuration F} {c : Cost}
    {out : Option (List F)} (h : Trace gamma n s c (.done out)) (extra : ℕ) :
    runFuel gamma (n + extra) s = (.done out, c) := by
  generalize ht : Configuration.done out = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih ht]

/-- Proof-only indexed update specification, rejecting an exhausted input. -/
def updateSpec (gamma : F) : ℕ → List F → Option (List F)
  | _, [] => none
  | 0, c :: cs => some ((c + gamma) :: cs)
  | j + 1, c :: cs => (updateSpec gamma j cs).map (c :: ·)

/-- Exact cost of a successful update at index `j`. -/
def successCost (j : ℕ) : Cost := ⟨1, 0, 2 * j + 5, 14 * j + 19, 2 * j + 1, 1⟩
/-- Exact cost of rejecting an index after traversing `n` cells. -/
def failureCost (n : ℕ) : Cost := ⟨0, 0, n + 3, 8 * n + 9, 2 * n, 1⟩

private theorem restore_trace (gamma : F) (rev out : List F) :
    Trace gamma (rev.length + 2) (.restore rev out)
      ⟨0, 0, rev.length + 2, 6 * rev.length + 5, 0, 1⟩
      (.done (some (rev.reverse ++ out))) := by
  induction rev generalizing out with
  | nil =>
      simpa [finishCost, emitCost] using
        Trace.cons (Step.finish (gamma := gamma))
          (Trace.cons Step.emit (Trace.nil (.done (some out))))
  | cons c rev ih =>
      convert Trace.cons Step.restore (ih (c :: out)) using 1 <;>
        simp [restoreCost, List.reverse_cons, List.append_assoc, Nat.mul_add]
      all_goals omega

private theorem scan_success (gamma : F) (j : ℕ) (cs rev out : List F)
    (h : updateSpec gamma j cs = some out) :
    Trace gamma (2 * j + rev.length + 4) (.scan j cs rev)
      ⟨1, 0, 2 * j + rev.length + 4, 14 * j + 6 * rev.length + 14, 2 * j + 1, 1⟩
      (.done (some (rev.reverse ++ out))) := by
  induction cs generalizing j rev out with
  | nil => simp [updateSpec] at h
  | cons c cs ih =>
      cases j with
      | zero =>
          simp only [updateSpec, Option.some.injEq] at h
          subst out
          convert Trace.cons Step.select
            (Trace.cons Step.add (restore_trace gamma rev ((c + gamma) :: cs))) using 1 <;>
            simp [selectCost, addCost]
          all_goals omega
      | succ j =>
          obtain ⟨tail, ht, rfl⟩ := Option.map_eq_some_iff.mp h
          convert Trace.cons Step.advance (ih j (c :: rev) tail ht) using 1 <;>
            simp [advanceCost, List.reverse_cons, List.append_assoc, Nat.mul_add] <;> omega

private theorem scan_failure (gamma : F) (j : ℕ) (cs rev : List F)
    (h : cs.length ≤ j) :
    Trace gamma (cs.length + 2) (.scan j cs rev)
      ⟨0, 0, cs.length + 2, 8 * cs.length + 4, 2 * cs.length, 1⟩ (.done none) := by
  induction cs generalizing j rev with
  | nil =>
      simpa [rejectCost, emitCost] using
        Trace.cons (Step.reject (gamma := gamma) (j := j) (rev := rev))
          (Trace.cons Step.emit (Trace.nil (.done none)))
  | cons c cs ih =>
      cases j with
      | zero => simp at h
      | succ j =>
          convert Trace.cons Step.advance (ih j (c :: rev) (by simpa using h)) using 1 <;>
            simp [advanceCost, Nat.mul_add]
          all_goals omega

/-- Successful execution performs exactly one scalar addition and restores the copied prefix. -/
theorem success_trace (gamma : F) (j : ℕ) (cs out : List F)
    (h : updateSpec gamma j cs = some out) :
    Trace gamma (2 * j + 5) (.start cs j) (successCost j) (.done (some out)) := by
  convert Trace.cons Step.start (scan_success gamma j cs [] out h) using 1 <;>
    simp [startCost, successCost]
  all_goals omega

/-- Out-of-range execution rejects after traversing the available input, with no scalar addition. -/
theorem failure_trace (gamma : F) (j : ℕ) (cs : List F) (h : cs.length ≤ j) :
    Trace gamma (cs.length + 3) (.start cs j) (failureCost cs.length) (.done none) := by
  convert Trace.cons Step.start (scan_failure gamma j cs [] h) using 1
  simp [startCost, failureCost]
  omega

/-- Sum of all primitive categories in the inherited cost model. -/
def totalCost (c : Cost) : ℕ := c.additions + c.multiplications + c.control + c.data +
  c.natural + c.output

/-- Successful trace costs are linear in the materialized input length. -/
theorem successCost_total_le (j n : ℕ) (h : j < n) :
    totalCost (successCost j) ≤ 27 * (n + 1) := by
  simp only [totalCost, successCost]
  omega

/-- Failure trace costs are linear even for arbitrarily large rejected indices. -/
theorem failureCost_total_le (n : ℕ) : totalCost (failureCost n) ≤ 27 * (n + 1) := by
  simp only [totalCost, failureCost]
  omega

private theorem foldl_horner (cs : List F) (p : F[X]) :
    cs.foldl (fun p c ↦ p * X + C c) p =
      p * X ^ cs.length + JetHornerMachine.coefficientPolynomial cs := by
  induction cs generalizing p with
  | nil => simp [JetHornerMachine.coefficientPolynomial]
  | cons c cs ih =>
      simp only [List.foldl_cons, List.length_cons]
      rw [ih]
      have hz := ih (C c)
      simp only [JetHornerMachine.coefficientPolynomial, List.foldl_cons, zero_mul, zero_add]
        at hz ⊢
      rw [hz, pow_succ]
      ring

/-- Descending coefficient interpretation retains leading zeros and the physical list length. -/
theorem coefficientPolynomial_cons (c : F) (cs : List F) :
    JetHornerMachine.coefficientPolynomial (c :: cs) =
      C c * X ^ cs.length + JetHornerMachine.coefficientPolynomial cs := by
  simpa only [JetHornerMachine.coefficientPolynomial, List.foldl_cons, zero_mul, zero_add] using
    foldl_horner cs (C c)

/-- In-range updates preserve length and add the indexed monomial, including zero scalars. -/
theorem updateSpec_correct (gamma : F) (j : ℕ) (cs : List F) (h : j < cs.length) :
    ∃ out, updateSpec gamma j cs = some out ∧ out.length = cs.length ∧
      JetHornerMachine.coefficientPolynomial out = JetHornerMachine.coefficientPolynomial cs +
        C gamma * X ^ (cs.length - 1 - j) := by
  induction cs generalizing j with
  | nil => simp at h
  | cons c cs ih =>
      cases j with
      | zero =>
          refine ⟨(c + gamma) :: cs, rfl, rfl, ?_⟩
          simp only [coefficientPolynomial_cons, List.length_cons, Nat.add_sub_cancel,
            Nat.sub_zero, map_add]
          ring
      | succ j =>
          obtain ⟨out, hout, hlen, hpoly⟩ := ih j (by simpa using h)
          refine ⟨c :: out, ?_, by simp [hlen], ?_⟩
          · simp [updateSpec, hout]
          · have hexp : (cs.length + 1 - 1 - (j + 1)) = cs.length - 1 - j := by omega
            simp only [coefficientPolynomial_cons, hlen, hpoly, List.length_cons, hexp]
            ring

/-- Uniform host fuel suffices for the certified in-range update, with exact cost. -/
theorem update_runFuel (gamma : F) (j : ℕ) (cs : List F) (h : j < cs.length) :
    ∃ out, runFuel gamma (2 * cs.length + 5) (.start cs j) =
        (.done (some out), successCost j) ∧ out.length = cs.length ∧
      JetHornerMachine.coefficientPolynomial out = JetHornerMachine.coefficientPolynomial cs +
        C gamma * X ^ (cs.length - 1 - j) ∧
      totalCost (successCost j) ≤ 27 * (cs.length + 1) := by
  obtain ⟨out, hout, hlen, hpoly⟩ := updateSpec_correct gamma j cs h
  refine ⟨out, ?_, hlen, hpoly, successCost_total_le j cs.length h⟩
  have ht := (success_trace gamma j cs out hout).runFuel_done (2 * cs.length + 5 - (2 * j + 5))
  have heq : 2 * j + 5 + (2 * cs.length + 5 - (2 * j + 5)) = 2 * cs.length + 5 := by omega
  rw [heq] at ht
  exact ht

/-- The same uniform fuel rejects every out-of-range index instead of truncating the update. -/
theorem reject_runFuel (gamma : F) (j : ℕ) (cs : List F) (h : cs.length ≤ j) :
    runFuel gamma (2 * cs.length + 5) (.start cs j) = (.done none, failureCost cs.length) := by
  have ht := (failure_trace gamma j cs h).runFuel_done (2 * cs.length + 5 - (cs.length + 3))
  have heq : cs.length + 3 + (2 * cs.length + 5 - (cs.length + 3)) =
      2 * cs.length + 5 := by omega
  rw [heq] at ht
  exact ht

/-- A supplied representation equality transfers the actual result to an existing polynomial.
No conversion from a concrete polynomial to a coefficient list is performed. -/
theorem update_runFuel_represents (gamma : F) (j : ℕ) (cs : List F) (P : F[X])
    (hP : JetHornerMachine.coefficientPolynomial cs = P) (h : j < cs.length) :
    ∃ out, runFuel gamma (2 * cs.length + 5) (.start cs j) =
        (.done (some out), successCost j) ∧ out.length = cs.length ∧
      JetHornerMachine.coefficientPolynomial out = P + monomial (cs.length - 1 - j) gamma := by
  obtain ⟨out, hrun, hlen, hpoly, _⟩ := update_runFuel gamma j cs h
  exact ⟨out, hrun, hlen, by simpa only [hP, C_mul_X_pow_eq_monomial] using hpoly⟩

end Polynomial.CoefficientUpdateMachine
