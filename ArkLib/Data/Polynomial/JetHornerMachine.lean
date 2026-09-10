/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Algebra.Polynomial.Taylor

/-!
# Closed simultaneous Hasse-jet Horner evaluation

The input coefficients are materialized in descending order. Initialization constructs the zero
jet explicitly from the supplied entry count `J = r+1`. Each coefficient pass consumes the old jet
in ascending order, carrying its OLD
predecessor; it builds a reversed updated jet and then reverses it by charged list transitions.
Output visits every scalar while retaining the already materialized result list.

The machine uses only literal control phases, list cells, natural zero tests/predecessors, and
scalar addition/multiplication. No polynomial, Hasse derivative, map, power, or reversal primitive
is executed. Costs count scalar arithmetic, dispatch, data accesses, natural operations, and
scalar outputs. A cell read retrieves its head and tail together. Retained registers are shared,
not copied; literals are free. Input preparation, interpreter bookkeeping, and scalar bit costs
are separate obligations. The semantic specification applies in every characteristic.
-/

@[expose] public section

namespace Polynomial.JetHornerMachine

/-- Primitive charges in the closed abstract machine. -/
@[ext] structure Cost where
  additions : ℕ
  multiplications : ℕ
  control : ℕ
  data : ℕ
  natural : ℕ
  output : ℕ
  deriving DecidableEq, Repr

instance : Zero Cost := ⟨⟨0, 0, 0, 0, 0, 0⟩⟩
instance : Add Cost := ⟨fun a b ↦
  ⟨a.additions + b.additions, a.multiplications + b.multiplications,
    a.control + b.control, a.data + b.data, a.natural + b.natural, a.output + b.output⟩⟩

@[simp] theorem cost_zero : (0 : Cost) = ⟨0, 0, 0, 0, 0, 0⟩ := rfl
@[simp] theorem cost_add (a b : Cost) : a + b =
    ⟨a.additions + b.additions, a.multiplications + b.multiplications,
      a.control + b.control, a.data + b.data, a.natural + b.natural, a.output + b.output⟩ := rfl
@[simp] theorem cost_add_zero (a : Cost) : a + 0 = a := by cases a; rfl
private theorem cost_add_assoc (a b c : Cost) : a + b + c = a + (b + c) := by
  ext <;> simp [Nat.add_assoc]

/-- Read/write counter and zero-list root; test and decrement the counter. -/
def initCost : Cost := ⟨0, 0, 1, 4, 2, 0⟩
/-- Read and test the exhausted counter. -/
def initDoneCost : Cost := ⟨0, 0, 1, 1, 1, 0⟩
/-- Read coefficient cell and jet root; write coefficient tail, jet cursor, buffer and carry. -/
def takeCost : Cost := ⟨0, 0, 1, 6, 0, 0⟩
/-- Read old cell, point, carry and buffer; write cursor, buffer and OLD carry. -/
def updateCost : Cost := ⟨1, 1, 1, 7, 0, 0⟩
/-- Read empty old cursor and initialize the reversal destination. -/
def updateDoneCost : Cost := ⟨0, 0, 1, 2, 0, 0⟩
/-- Read pending cell and destination root; write both roots. -/
def reverseCost : Cost := ⟨0, 0, 1, 4, 0, 0⟩
/-- Read empty pending cursor and completed jet root. -/
def reverseDoneCost : Cost := ⟨0, 0, 1, 2, 0, 0⟩
/-- Read empty coefficients and jet root; write output cursor and retained result root. -/
def outputStartCost : Cost := ⟨0, 0, 1, 4, 0, 0⟩
/-- Read an output cell, write its tail, and emit its scalar. -/
def outputCost : Cost := ⟨0, 0, 1, 2, 0, 1⟩
/-- Read empty output cursor and return the retained result root. -/
def outputDoneCost : Cost := ⟨0, 0, 1, 2, 0, 0⟩

/-- Fixed control phases; the only arithmetic registers are the point and carried old scalar. -/
inductive Configuration (F : Type*) where
  | initialize (coefficients : List F) (left : ℕ) (zeros : List F)
  | coefficients (remaining jets : List F)
  | update (coefficients old reversed : List F) (carry : F)
  | reverse (coefficients pending result : List F)
  | emit (pending result : List F)
  | done (result : List F)
  deriving DecidableEq, Repr

variable {F : Type*} [CommSemiring F]

/-- Independent transition rules fix every successor and its primitive charge. -/
inductive Step (x : F) : Configuration F → Cost → Configuration F → Prop where
  | init {cs n zs} : Step x (.initialize cs (n + 1) zs) initCost (.initialize cs n (0 :: zs))
  | initDone {cs zs} : Step x (.initialize cs 0 zs) initDoneCost (.coefficients cs zs)
  | take {c cs js} : Step x (.coefficients (c :: cs) js) takeCost (.update cs js [] c)
  | update {cs h hs rev carry} : Step x (.update cs (h :: hs) rev carry) updateCost
      (.update cs hs ((x * h + carry) :: rev) h)
  | updateDone {cs rev carry} : Step x (.update cs [] rev carry) updateDoneCost (.reverse cs rev [])
  | reverse {cs h hs out} : Step x (.reverse cs (h :: hs) out) reverseCost
      (.reverse cs hs (h :: out))
  | reverseDone {cs out} : Step x (.reverse cs [] out) reverseDoneCost (.coefficients cs out)
  | outputStart {js} : Step x (.coefficients [] js) outputStartCost (.emit js js)
  | output {h hs out} : Step x (.emit (h :: hs) out) outputCost (.emit hs out)
  | outputDone {out} : Step x (.emit [] out) outputDoneCost (.done out)

/-- Literal executable dispatch. -/
def step (x : F) : Configuration F → Option (Configuration F × Cost)
  | .initialize cs (n + 1) zs => some (.initialize cs n (0 :: zs), initCost)
  | .initialize cs 0 zs => some (.coefficients cs zs, initDoneCost)
  | .coefficients (c :: cs) js => some (.update cs js [] c, takeCost)
  | .coefficients [] js => some (.emit js js, outputStartCost)
  | .update cs (h :: hs) rev carry => some (.update cs hs ((x * h + carry) :: rev) h, updateCost)
  | .update cs [] rev _ => some (.reverse cs rev [], updateDoneCost)
  | .reverse cs (h :: hs) out => some (.reverse cs hs (h :: out), reverseCost)
  | .reverse cs [] out => some (.coefficients cs out, reverseDoneCost)
  | .emit (_ :: hs) out => some (.emit hs out, outputCost)
  | .emit [] out => some (.done out, outputDoneCost)
  | .done _ => none

/-- Independent rules agree with executable dispatch. -/
theorem Step.step_eq {x : F} {s t : Configuration F} {c : Cost} (h : Step x s c t) :
    step x s = some (t, c) := by cases h <;> rfl

/-- Every executable transition is one of the independent rules. -/
theorem step_sound {x : F} {s t : Configuration F} {c : Cost}
    (h : step x s = some (t, c)) : Step x s c t := by
  cases s with
  | «initialize» cs n zs => cases n <;> cases h <;> constructor
  | coefficients cs js => cases cs <;> cases h <;> constructor
  | update cs old rev carry => cases old <;> cases h <;> constructor
  | reverse cs pending out => cases pending <;> cases h <;> constructor
  | emit pending out => cases pending <;> cases h <;> constructor
  | done out => simp [step] at h

/-- Both the successor and its charge are uniquely determined. -/
theorem Step.deterministic {x : F} {s t u : Configuration F} {c d : Cost}
    (h : Step x s c t) (h' : Step x s d u) : t = u ∧ c = d := by
  simpa only [Option.some.injEq, Prod.mk.injEq] using h.step_eq.symm.trans h'.step_eq

/-- Finite traces account for every actual step. -/
inductive Trace (x : F) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace x 0 s 0 s
  | cons {n s u t c d} (head : Step x s c u) (tail : Trace x n u d t) :
      Trace x (n + 1) s (c + d) t

/-- Trace composition adds charges without an extra semantic operation. -/
theorem Trace.trans {x : F} {n m : ℕ} {s u t : Configuration F} {c d : Cost}
    (h : Trace x n s c u) (h' : Trace x m u d t) : Trace x (n + m) s (c + d) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, cost_add_assoc] using
        Trace.cons head (ih h')

/-- Fuel exhaustion returns the reached state rather than pretending to have emitted a jet. -/
def runFuel (x : F) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step x s with
      | none => (s, 0)
      | some (t, c) => let result := runFuel x n t; (result.1, c + result.2)

/-- Every interpreter result has a trace consuming at most its supplied fuel. -/
theorem runFuel_refines (x : F) (fuel : ℕ) (s : Configuration F) :
    ∃ n ≤ fuel, Trace x n s (runFuel x fuel s).2 (runFuel x fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step x s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil (x := x) s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- Exact trace fuel realizes the same output and cost. -/
theorem Trace.runFuel_eq {x : F} {n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace x n s c t) : runFuel x n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp [runFuel, head.step_eq, ih]

/-- Mathematical simultaneous update; used only in specifications. -/
def jetUpdate (x : F) : F → List F → List F
  | _, [] => []
  | carry, h :: hs => (x * h + carry) :: jetUpdate x h hs

@[simp] theorem jetUpdate_length (x carry : F) (js : List F) :
    (jetUpdate x carry js).length = js.length := by
  induction js generalizing carry with
  | nil => rfl
  | cons h hs ih => simp [jetUpdate, ih]

/-- Semantic loop on the already materialized input. -/
def jetLoop (x : F) : List F → List F → List F
  | [], js => js
  | c :: cs, js => jetLoop x cs (jetUpdate x c js)

@[simp] theorem jetLoop_length (x : F) (cs js : List F) :
    (jetLoop x cs js).length = js.length := by
  induction cs generalizing js with
  | nil => rfl
  | cons c cs ih => simp [jetLoop, ih]

/-- Exact initialization charges. -/
def initializationCost (J : ℕ) : Cost := ⟨0, 0, J + 1, 4 * J + 1, 2 * J + 1, 0⟩
/-- Exact update-pass charges, before reversal. -/
def updatePassCost (J : ℕ) : Cost := ⟨J, J, J + 1, 7 * J + 2, 0, 0⟩
/-- Exact reversal charges. -/
def reversalCost (J : ℕ) : Cost := ⟨0, 0, J + 1, 4 * J + 2, 0, 0⟩
/-- Exact output traversal charges. -/
def emissionCost (J : ℕ) : Cost := ⟨0, 0, J + 1, 2 * J + 2, 0, J⟩
/-- Charges for processing coefficients and output, after initialization. -/
def loopCost (N J : ℕ) : Cost :=
  ⟨N * J, N * J, N * (2 * J + 3) + J + 2, N * (11 * J + 10) + 2 * J + 6, 0, J⟩
/-- Full exact cost with `J` requested jet entries. -/
def evaluationCost (N J : ℕ) : Cost :=
  ⟨N * J, N * J, (N + 1) * (2 * J + 3), N * (11 * J + 10) + 6 * J + 7, 2 * J + 1, J⟩

/-- Initialization constructs every zero entry through a literal transition. -/
theorem initialization_trace (x : F) (cs zs : List F) (J : ℕ) :
    Trace x (J + 1) (.initialize cs J zs) (initializationCost J)
      (.coefficients cs (List.replicate J 0 ++ zs)) := by
  induction J generalizing zs with
  | zero => simpa [initializationCost, initDoneCost] using
      Trace.cons (Step.initDone (x := x) (cs := cs) (zs := zs)) (Trace.nil _)
  | succ J ih =>
      have h := Trace.cons Step.init (ih (0 :: zs))
      have hlist : List.replicate J (0 : F) ++ 0 :: zs = List.replicate (J + 1) 0 ++ zs := by
        rw [List.replicate_succ']
        simp only [List.append_assoc, List.singleton_append]
      rw [hlist] at h
      simpa [initializationCost, initCost, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h

/-- Update consumes old entries once and retains the old predecessor in its carry. -/
theorem update_trace (x carry : F) (cs old rev : List F) :
    Trace x (old.length + 1) (.update cs old rev carry) (updatePassCost old.length)
      (.reverse cs ((jetUpdate x carry old).reverse ++ rev) []) := by
  induction old generalizing carry rev with
  | nil => simpa [updatePassCost, updateDoneCost, jetUpdate] using
      Trace.cons (Step.updateDone (x := x) (cs := cs) (rev := rev) (carry := carry)) (Trace.nil _)
  | cons h hs ih =>
      simpa [updatePassCost, updateCost, jetUpdate, List.append_assoc,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Trace.cons Step.update (ih h ((x * h + carry) :: rev))

/-- Reversal is a charged traversal, not a list primitive. -/
theorem reversal_trace (x : F) (cs pending out : List F) :
    Trace x (pending.length + 1) (.reverse cs pending out) (reversalCost pending.length)
      (.coefficients cs (pending.reverse ++ out)) := by
  induction pending generalizing out with
  | nil => simpa [reversalCost, reverseDoneCost] using
      Trace.cons (Step.reverseDone (x := x) (cs := cs) (out := out)) (Trace.nil _)
  | cons h hs ih =>
      simpa [reversalCost, reverseCost, List.append_assoc, Nat.mul_add,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          Trace.cons Step.reverse (ih (h :: out))

/-- Emission visits every scalar but does not copy the retained materialized result. -/
theorem emission_trace (x : F) (pending out : List F) :
    Trace x (pending.length + 1) (.emit pending out) (emissionCost pending.length) (.done out) := by
  induction pending with
  | nil => simpa [emissionCost, outputDoneCost] using
      Trace.cons (Step.outputDone (x := x) (out := out)) (Trace.nil _)
  | cons h hs ih =>
      simpa [emissionCost, outputCost, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using Trace.cons Step.output ih

/-- The complete coefficient loop has exact fuel and charges. -/
theorem loop_trace (x : F) (cs js : List F) :
    Trace x (cs.length * (2 * js.length + 3) + js.length + 2) (.coefficients cs js)
      (loopCost cs.length js.length) (.done (jetLoop x cs js)) := by
  induction cs generalizing js with
  | nil =>
      convert Trace.cons Step.outputStart (emission_trace x js js) using 1 <;>
        simp [loopCost, outputStartCost, emissionCost, jetLoop]
      all_goals omega
  | cons c cs ih =>
      have hu := update_trace x c cs js []
      simp only [List.append_nil] at hu
      have hr := reversal_trace x cs (jetUpdate x c js).reverse []
      simp only [List.reverse_reverse, List.append_nil] at hr
      have h := Trace.cons Step.take (hu.trans (hr.trans (ih (jetUpdate x c js))))
      convert h using 1 <;>
        simp [loopCost, takeCost, updatePassCost, reversalCost, jetLoop,
          Nat.mul_add, Nat.add_mul, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
      all_goals omega

/-- Exact full execution, including initialization and output. -/
theorem evaluation_runFuel (x : F) (cs : List F) (r : ℕ) :
    runFuel x ((cs.length + 1) * (2 * (r + 1) + 3)) (.initialize cs (r + 1) []) =
      (.done (jetLoop x cs (List.replicate (r + 1) 0)), evaluationCost cs.length (r + 1)) := by
  have hi := initialization_trace x cs [] (r + 1)
  simp only [List.append_nil] at hi
  have h := hi.trans (loop_trace x cs (List.replicate (r + 1) 0))
  simp only [List.length_replicate] at h
  have hfuel : (r + 1 + 1) + (cs.length * (2 * (r + 1) + 3) + (r + 1) + 2) =
      (cs.length + 1) * (2 * (r + 1) + 3) := by ring
  have hcost : initializationCost (r + 1) + loopCost cs.length (r + 1) =
      evaluationCost cs.length (r + 1) := by
    ext <;> simp only [initializationCost, loopCost, evaluationCost, cost_add] <;> ring
  rw [hfuel, hcost] at h
  exact h.runFuel_eq

/-- Total abstract primitive operations. -/
def Cost.total (c : Cost) : ℕ :=
  c.additions + c.multiplications + c.control + c.data + c.natural + c.output

/-- The literal phase table gives a bound stronger than the proposed constant `100`. -/
theorem evaluationCost_total_le (N r : ℕ) :
    (evaluationCost N (r + 1)).total ≤ 28 * (N + 1) * (r + 1) := by
  simp only [Cost.total, evaluationCost]
  nlinarith [Nat.zero_le (N * r)]

/-- Exact terminating fuel is linear in the coefficient count times jet length. -/
theorem evaluationFuel_le (N r : ℕ) :
    (N + 1) * (2 * (r + 1) + 3) ≤ 5 * (N + 1) * (r + 1) := by
  have h := Nat.mul_le_mul_left (N + 1) (show 2 * (r + 1) + 3 ≤ 5 * (r + 1) by omega)
  nlinarith only [h]

private theorem jetUpdate_getD (x carry : F) (js : List F) (j : ℕ) (hj : j < js.length) :
    (jetUpdate x carry js).getD j 0 = x * js.getD j 0 +
      if j = 0 then carry else js.getD (j - 1) 0 := by
  induction js generalizing carry j with
  | nil => simp at hj
  | cons h hs ih =>
      cases j with
      | zero => simp [jetUpdate]
      | succ j =>
          have hbound : j < hs.length := by simpa using hj
          rw [jetUpdate]
          simp only [List.getD_cons_succ, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
          rw [ih h j hbound]
          cases j <;> simp

/-- The Hasse recurrence has no factorial division and works in every characteristic. -/
theorem hasse_horner (x c : F) (p : F[X]) (j : ℕ) :
    (hasseDeriv j (p * X + C c)).eval x = x * (hasseDeriv j p).eval x +
      if j = 0 then c else (hasseDeriv (j - 1) p).eval x := by
  simp only [← taylor_coeff]
  rw [map_add, taylor_mul, taylor_X, taylor_C, mul_add]
  cases j with
  | zero => simp [mul_comm]
  | succ j => simp [mul_comm, add_comm]

/-- Polynomial represented by a descending coefficient list, including arbitrary zero padding. -/
noncomputable def coefficientPolynomial (cs : List F) : F[X] := cs.foldl (fun p c ↦ p * X + C c) 0

private theorem jetLoop_spec (x : F) (cs js : List F) (p : F[X]) (J : ℕ)
    (hlen : js.length = J)
    (hjs : ∀ j < J, js.getD j 0 = (hasseDeriv j p).eval x) :
    ∀ j < J, (jetLoop x cs js).getD j 0 =
      (hasseDeriv j (cs.foldl (fun p c ↦ p * X + C c) p)).eval x := by
  induction cs generalizing js p with
  | nil => exact hjs
  | cons c cs ih =>
      apply ih (jetUpdate x c js) (p * X + C c) (by simpa using hlen)
      intro j hj
      rw [jetUpdate_getD x c js j (by omega), hasse_horner, hjs j hj]
      by_cases hj0 : j = 0
      · simp [hj0]
      · rw [if_neg hj0, if_neg hj0, hjs (j - 1) (by omega)]

/-- Semantic jet list has exactly the requested length and the true Hasse evaluations. -/
theorem jetLoop_replicate_spec (x : F) (cs : List F) (r : ℕ) :
    (jetLoop x cs (List.replicate (r + 1) 0)).length = r + 1 ∧
      ∀ j ≤ r, (jetLoop x cs (List.replicate (r + 1) 0)).getD j 0 =
        (hasseDeriv j (coefficientPolynomial cs)).eval x := by
  refine ⟨by simp, ?_⟩
  intro j hj
  apply jetLoop_spec x cs (List.replicate (r + 1) 0) 0 (r + 1) (by simp) _ j (by omega)
  intro i hi
  simp [List.getD, hi]

/-- Actual closed execution produces the Hasse jet of the explicitly represented polynomial,
with exact arithmetic, control, data, natural-operation and output counts. -/
theorem evaluation_runFuel_spec (x : F) (cs : List F) (r : ℕ) :
    ∃ js, runFuel x ((cs.length + 1) * (2 * (r + 1) + 3)) (.initialize cs (r + 1) []) =
        (.done js, evaluationCost cs.length (r + 1)) ∧ js.length = r + 1 ∧
      ∀ j ≤ r, js.getD j 0 = (hasseDeriv j (coefficientPolynomial cs)).eval x :=
  ⟨_, evaluation_runFuel x cs r, jetLoop_replicate_spec x cs r⟩

/-- Polynomial-facing refinement with an explicit representation equality. Preparing the list
from another polynomial representation remains outside this machine's cost. -/
theorem evaluation_runFuel_eq_hasse (x : F) (p : F[X]) (cs : List F)
    (hcs : coefficientPolynomial cs = p) (r : ℕ) :
    ∃ js, runFuel x ((cs.length + 1) * (2 * (r + 1) + 3)) (.initialize cs (r + 1) []) =
        (.done js, evaluationCost cs.length (r + 1)) ∧ js.length = r + 1 ∧
      ∀ j ≤ r, js.getD j 0 = (hasseDeriv j p).eval x := by
  simpa only [hcs] using evaluation_runFuel_spec x cs r

end Polynomial.JetHornerMachine
