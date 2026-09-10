/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.FieldTheory.Finite.Basic

/-!
# Closed nonsquare search

Two explicit counter loops enumerate candidates and possible square roots by adding one.
Every candidate scans all roots; a Boolean records whether a square matched. Squaring,
equality/Boolean updates, counter operations, resets, and output are distinct charged transitions.
The proof specifications are not primitives of executable dispatch. No primality decision is
performed: odd primality guarantees success, while returned values are sound for every modulus.
Costs are abstract scalar/register operations, excluding input materialization, host fuel,
reclamation and integer/field bit costs. This does not construct an extension field.
-/

@[expose] public section

namespace ZMod.NonsquareSearchMachine

/-- Primitive counts; tests include scalar equality and Boolean operations. -/
@[ext] structure Cost where
  additions : ℕ
  multiplications : ℕ
  tests : ℕ
  natOperations : ℕ
  constants : ℕ
  control : ℕ
  data : ℕ
  output : ℕ
  deriving DecidableEq, Repr

instance : Zero Cost := ⟨⟨0, 0, 0, 0, 0, 0, 0, 0⟩⟩
instance : Add Cost := ⟨fun a b ↦
  ⟨a.additions + b.additions, a.multiplications + b.multiplications, a.tests + b.tests,
    a.natOperations + b.natOperations, a.constants + b.constants, a.control + b.control,
    a.data + b.data, a.output + b.output⟩⟩

/-- Total unit operations in the explicitly separated cost categories. -/
def Cost.total (c : Cost) : ℕ := c.additions + c.multiplications + c.tests + c.natOperations +
  c.constants + c.control + c.data + c.output

@[simp] theorem cost_zero : (0 : Cost) = ⟨0, 0, 0, 0, 0, 0, 0, 0⟩ := rfl
@[simp] theorem cost_add (a b : Cost) : a + b =
    ⟨a.additions + b.additions, a.multiplications + b.multiplications, a.tests + b.tests,
      a.natOperations + b.natOperations, a.constants + b.constants, a.control + b.control,
      a.data + b.data, a.output + b.output⟩ := rfl
@[simp] theorem cost_add_zero (c : Cost) : c + 0 = c := by cases c; rfl
@[simp] theorem cost_zero_add (c : Cost) : 0 + c = c := by
  cases c
  simp only [cost_add, cost_zero, Nat.zero_add]
@[simp] theorem total_zero : Cost.total 0 = 0 := rfl
@[simp] theorem total_add (a b : Cost) : (a + b).total = a.total + b.total := by
  simp only [cost_add, Cost.total]
  omega

/-- Sequential primitive charges associate componentwise. -/
theorem cost_add_assoc (a b c : Cost) : (a + b) + c = a + (b + c) := by
  simp only [cost_add, Nat.add_assoc]

/-- Read modulus and initialize candidate counter and scalar zero. -/
def startCost : Cost := ⟨0, 0, 0, 0, 1, 1, 3, 0⟩
/-- Test/decrement candidate counter, read modulus, reset root counter, zero root and hit flag. -/
def candidateCost : Cost := ⟨0, 0, 0, 2, 2, 1, 6, 0⟩
/-- Test/decrement root counter, reading and writing its register. -/
def rootCost : Cost := ⟨0, 0, 0, 2, 0, 1, 2, 0⟩
/-- Read both scalar operands, square, and write the product. -/
def squareCost : Cost := ⟨0, 1, 0, 0, 0, 1, 3, 0⟩
/-- Read product, candidate and hit flag; compare, Boolean-or, and write the flag. -/
def testCost : Cost := ⟨0, 0, 2, 0, 0, 1, 4, 0⟩
/-- Materialize one, read/add/write a scalar counter. -/
def incrementCost : Cost := ⟨1, 0, 0, 0, 1, 1, 2, 0⟩
/-- Read and test the exhausted root counter. -/
def finishCost : Cost := ⟨0, 0, 0, 1, 0, 1, 1, 0⟩
/-- Read/test a true hit flag before advancing to the next candidate. -/
def continueCost : Cost := ⟨0, 0, 1, 0, 0, 1, 1, 0⟩
/-- Read/test the hit flag and read/emit a successful candidate. -/
def successCost : Cost := ⟨0, 0, 1, 0, 0, 1, 2, 1⟩
/-- Read/test the exhausted candidate counter and emit failure. -/
def failureCost : Cost := ⟨0, 0, 0, 1, 0, 1, 1, 1⟩

/-- Fixed phases carry counters, scalars, and one Boolean; no bulk enumeration data. -/
inductive Configuration (q : ℕ) where
  | start
  | candidates (remaining : ℕ) (candidate : ZMod q)
  | roots (remainingCandidates : ℕ) (candidate : ZMod q)
      (remainingRoots : ℕ) (root : ZMod q) (hit : Bool)
  | square (remainingCandidates : ℕ) (candidate : ZMod q)
      (remainingRoots : ℕ) (root : ZMod q) (hit : Bool)
  | test (remainingCandidates : ℕ) (candidate : ZMod q)
      (remainingRoots : ℕ) (root product : ZMod q) (hit : Bool)
  | incrementRoot (remainingCandidates : ℕ) (candidate : ZMod q)
      (remainingRoots : ℕ) (root : ZMod q) (hit : Bool)
  | inspect (remainingCandidates : ℕ) (candidate : ZMod q) (hit : Bool)
  | next (remainingCandidates : ℕ) (candidate : ZMod q)
  | done (result : Option (ZMod q))
  deriving DecidableEq, Repr

variable {q : ℕ}

/-- Independent operational rules, including equality and its accumulated Boolean result. -/
inductive Step : Configuration q → Cost → Configuration q → Prop where
  | start : Step .start startCost (.candidates q 0)
  | candidate {n a} : Step (.candidates (n + 1) a) candidateCost (.roots n a q 0 false)
  | root {n a r b hit} : Step (.roots n a (r + 1) b hit) rootCost (.square n a r b hit)
  | square {n a r b hit} : Step (.square n a r b hit) squareCost (.test n a r b (b * b) hit)
  | test {n a r b p hit} : Step (.test n a r b p hit) testCost
      (.incrementRoot n a r b (hit || decide (p = a)))
  | incrementRoot {n a r b hit} : Step (.incrementRoot n a r b hit) incrementCost
      (.roots n a r (b + 1) hit)
  | finish {n a b hit} : Step (.roots n a 0 b hit) finishCost (.inspect n a hit)
  | continue {n a} : Step (.inspect n a true) continueCost (.next n a)
  | success {n a} : Step (.inspect n a false) successCost (.done (some a))
  | next {n a} : Step (.next n a) incrementCost (.candidates n (a + 1))
  | failure {a} : Step (.candidates 0 a) failureCost (.done none)

/-- Closed dispatch uses only primitive scalar, Boolean, counter, and register operations. -/
def step : Configuration q → Option (Configuration q × Cost)
  | .start => some (.candidates q 0, startCost)
  | .candidates 0 _ => some (.done none, failureCost)
  | .candidates (n + 1) a => some (.roots n a q 0 false, candidateCost)
  | .roots n a 0 _ hit => some (.inspect n a hit, finishCost)
  | .roots n a (r + 1) b hit => some (.square n a r b hit, rootCost)
  | .square n a r b hit => some (.test n a r b (b * b) hit, squareCost)
  | .test n a r b p hit => some (.incrementRoot n a r b (hit || decide (p = a)), testCost)
  | .incrementRoot n a r b hit => some (.roots n a r (b + 1) hit, incrementCost)
  | .inspect n a true => some (.next n a, continueCost)
  | .inspect _ a false => some (.done (some a), successCost)
  | .next n a => some (.candidates n (a + 1), incrementCost)
  | .done _ => none

/-- Each rule agrees with executable dispatch and its charge. -/
theorem Step.step_eq {s t : Configuration q} {c : Cost} (h : Step s c t) :
    step s = some (t, c) := by cases h <;> rfl

/-- Executable transitions have no extra unmodeled branches. -/
theorem step_sound {s t : Configuration q} {c : Cost} (h : step s = some (t, c)) :
    Step s c t := by
  cases s with
  | start => cases h; exact Step.start
  | candidates n a =>
      cases n with
      | zero => cases h; exact Step.failure
      | succ n => cases h; exact Step.candidate
  | roots n a r b hit =>
      cases r with
      | zero => cases h; exact Step.finish
      | succ r => cases h; exact Step.root
  | square n a r b hit => cases h; exact Step.square
  | test n a r b p hit => cases h; exact Step.test
  | incrementRoot n a r b hit => cases h; exact Step.incrementRoot
  | inspect n a hit =>
      cases hit with
      | false => cases h; exact Step.success
      | true => cases h; exact Step.continue
  | next n a => cases h; exact Step.next
  | done a => simp [step] at h

/-- Step equivalence exposes both the next state and exact primitive cost. -/
theorem step_iff {s t : Configuration q} {c : Cost} : step s = some (t, c) ↔ Step s c t :=
  ⟨step_sound, Step.step_eq⟩

/-- Actual finite traces accumulate the operation counts. -/
inductive Trace : ℕ → Configuration q → Cost → Configuration q → Prop where
  | nil (s) : Trace 0 s 0 s
  | cons {n s u t c d} (head : Step s c u) (tail : Trace n u d t) :
      Trace (n + 1) s (c + d) t

/-- Concatenate independently verified traces and add their actual charges. -/
theorem Trace.append {n m : ℕ} {s t u : Configuration q} {c d : Cost}
    (h : Trace n s c t) (h' : Trace m t d u) : Trace (n + m) s (c + d) u := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa only [Nat.add_right_comm, cost_add_assoc] using Trace.cons head (ih h')

/-- Execution with insufficient fuel returns an intermediate configuration. -/
def runFuel : ℕ → Configuration q → Configuration q × Cost
  | 0, s => (s, 0)
  | n + 1, s =>
      match step s with
      | none => (s, 0)
      | some (t, c) =>
          let result := runFuel n t
          (result.1, c + result.2)

/-- Actual execution refines the independent trace relation with the same cost. -/
theorem runFuel_refines (fuel : ℕ) (s : Configuration q) :
    ∃ n ≤ fuel, Trace n s (runFuel fuel s).2 (runFuel fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- A trace composes with any remaining executable fuel. -/
theorem Trace.runFuel_add {n : ℕ} {s t : Configuration q} {c : Cost}
    (h : Trace n s c t) (extra : ℕ) :
    runFuel (n + extra) s = ((runFuel extra t).1, c + (runFuel extra t).2) := by
  induction h with
  | nil s => simp
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih]
      simp only [cost_add_assoc]

/-- A complete trace is reproduced with excess fuel and no additional modeled operations. -/
theorem Trace.runFuel_done {n : ℕ} {s : Configuration q} {c : Cost} {result : Option (ZMod q)}
    (h : Trace n s c (.done result)) (extra : ℕ) :
    runFuel (n + extra) s = (.done result, c) := by
  have hr : runFuel extra (.done result) = (.done result, (0 : Cost)) := by cases extra <;> rfl
  rw [h.runFuel_add, hr]
  simp

/-- Every transition uses at most twelve of the stated primitive operations. -/
theorem Step.total_le {s t : Configuration q} {c : Cost} (h : Step s c t) : c.total ≤ 12 := by
  cases h <;> norm_num [Cost.total, startCost, candidateCost, rootCost, squareCost, testCost,
    incrementCost, finishCost, continueCost, successCost, failureCost]

/-- The primitive operation total is bounded by twelve times the actual transition count. -/
theorem Trace.total_le {n : ℕ} {s t : Configuration q} {c : Cost} (h : Trace n s c t) :
    c.total ≤ 12 * n := by
  induction h with
  | nil s => simp [Cost.total]
  | cons head tail ih =>
      rw [total_add]
      have := head.total_le
      omega

/-- Proof specification for a root scan; this recursion is not a dispatch primitive. -/
def rootHits (a b : ZMod q) : ℕ → Bool → Bool
  | 0, hit => hit
  | r + 1, hit => rootHits a (b + 1) r (hit || decide (b * b = a))

/-- The complete inner loop is backed by `4r+1` actual transitions. -/
theorem roots_trace (n r : ℕ) (a b : ZMod q) (hit : Bool) :
    ∃ c, Trace (4 * r + 1) (.roots n a r b hit) c (.inspect n a (rootHits a b r hit)) := by
  induction r generalizing b hit with
  | zero => exact ⟨_, Trace.cons Step.finish (Trace.nil _)⟩
  | succ r ih =>
      obtain ⟨c, h⟩ := ih (b + 1) (hit || decide (b * b = a))
      refine ⟨rootCost + (squareCost + (testCost + (incrementCost + c))), ?_⟩
      have ht := Trace.cons Step.root (Trace.cons Step.square
        (Trace.cons Step.test (Trace.cons Step.incrementRoot h)))
      convert ht using 1 <;> simp [rootHits]; omega

/-- A negative scan result excludes each explicitly scanned root. -/
theorem rootHits_false_excludes (a b : ZMod q) (r : ℕ) (hit : Bool)
    (h : rootHits a b r hit = false) :
    hit = false ∧ ∀ i < r, (b + (i : ZMod q)) * (b + (i : ZMod q)) ≠ a := by
  induction r generalizing b hit with
  | zero => exact ⟨h, by omega⟩
  | succ r ih =>
      obtain ⟨hflag, hrest⟩ := ih (b + 1) (hit || decide (b * b = a)) h
      have hparts : hit = false ∧ b * b ≠ a := by simpa using hflag
      refine ⟨hparts.1, ?_⟩
      intro i hi
      cases i with
      | zero => simpa using hparts.2
      | succ i =>
          have h := hrest i (by omega)
          simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using h

/-- If no field element squares to the candidate, its Boolean scan remains false. -/
theorem rootHits_false_of_nonsquare (a b : ZMod q) (r : ℕ) (ha : ¬IsSquare a) :
    rootHits a b r false = false := by
  induction r generalizing b with
  | zero => rfl
  | succ r ih =>
      have hb : b * b ≠ a := fun h ↦ ha ⟨b, h.symm⟩
      simpa [rootHits, hb] using ih (b + 1)

/-- A full root scan detects nonsquares, using every canonical representative. -/
theorem full_rootHits_false_iff (hq : 0 < q) (a : ZMod q) :
    rootHits a 0 q false = false ↔ ¬IsSquare a := by
  constructor
  · intro h hs
    let : NeZero q := ⟨hq.ne'⟩
    obtain ⟨b, hb⟩ := hs
    have hne := (rootHits_false_excludes a 0 q false h).2 b.val (ZMod.val_lt b)
    simp [hb.symm] at hne
  · exact rootHits_false_of_nonsquare a 0 q

/-- Mathematical result specification; executable dispatch never calls this recursion. -/
def searchSpec : ℕ → ZMod q → Option (ZMod q)
  | 0, _ => none
  | n + 1, a => if rootHits a 0 q false then searchSpec n (a + 1) else some a

/-- Every candidate-loop execution terminates within its explicit quadratic envelope. -/
theorem candidates_trace (n : ℕ) (a : ZMod q) :
    ∃ steps ≤ n * (4 * q + 4) + 1, ∃ c,
      Trace steps (.candidates n a) c (.done (searchSpec n a)) := by
  induction n generalizing a with
  | zero => exact ⟨1, by simp, _, Trace.cons Step.failure (Trace.nil _)⟩
  | succ n ih =>
      obtain ⟨rc, hr⟩ := roots_trace n q a 0 false
      cases hh : rootHits a 0 q false with
      | false =>
          rw [hh] at hr
          have htail := Trace.cons (Step.success (n := n) (a := a)) (Trace.nil _)
          have ht := Trace.cons Step.candidate (hr.append htail)
          refine ⟨4 * q + 1 + (0 + 1) + 1, ?_,
            candidateCost + (rc + (successCost + 0)), ?_⟩
          · simp only [Nat.add_mul]
            omega
          · simpa [searchSpec, hh] using ht
      | true =>
          rw [hh] at hr
          obtain ⟨steps, hs, c, hc⟩ := ih (a + 1)
          have htail := Trace.cons Step.continue (Trace.cons Step.next hc)
          have ht := Trace.cons Step.candidate (hr.append htail)
          refine ⟨4 * q + 1 + (steps + 1 + 1) + 1, ?_,
            candidateCost + (rc + (continueCost + (incrementCost + c))), ?_⟩
          · simp only [Nat.add_mul]
            omega
          · simpa [searchSpec, hh] using ht

/-- Any reported specification value has survived a complete square-root scan. -/
theorem searchSpec_sound (hq : 0 < q) (n : ℕ) (a b : ZMod q)
    (h : searchSpec n a = some b) : ¬IsSquare b := by
  induction n generalizing a with
  | zero => simp [searchSpec] at h
  | succ n ih =>
      cases hh : rootHits a 0 q false with
      | false =>
          have hab : a = b := by simpa [searchSpec, hh] using h
          subst b
          exact (full_rootHits_false_iff hq a).mp hh
      | true => exact ih (a + 1) (by simpa [searchSpec, hh] using h)

/-- If a nonsquare occurs among the candidate representatives, the search succeeds. -/
theorem searchSpec_ne_none_of_witness (n : ℕ) (a : ZMod q) (i : ℕ) (hi : i < n)
    (ha : ¬IsSquare (a + (i : ZMod q))) : searchSpec n a ≠ none := by
  induction n generalizing a i with
  | zero => omega
  | succ n ih =>
      cases hh : rootHits a 0 q false with
      | false => simp [searchSpec, hh]
      | true =>
          cases i with
          | zero =>
              have hf := rootHits_false_of_nonsquare a 0 q (by simpa using ha)
              simp [hh] at hf
          | succ i =>
              have h := ih (a + 1) i (by omega)
                (by simpa [Nat.cast_add, add_assoc, add_comm, add_left_comm] using ha)
              simpa [searchSpec, hh] using h

/-- Odd prime fields contain a nonsquare among the explicitly scanned representatives. -/
theorem searchSpec_prime_ne_none (hq : q.Prime) (hodd : q ≠ 2) :
    searchSpec q (0 : ZMod q) ≠ none := by
  let : Fact q.Prime := ⟨hq⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  have hchar : ringChar (ZMod q) ≠ 2 := by rwa [ringChar.eq (ZMod q) q]
  obtain ⟨a, ha⟩ := FiniteField.exists_nonsquare (F := ZMod q) hchar
  exact searchSpec_ne_none_of_witness q 0 a.val (ZMod.val_lt a) (by simpa using ha)

/-- Worst-case transition fuel, including initialization and exhausted search emission. -/
def searchFuel (q : ℕ) : ℕ := q * (4 * q + 4) + 2

/-- Actual execution terminates with its specified result and a quadratic primitive bound. -/
theorem search_runFuel (q : ℕ) :
    ∃ c, runFuel (searchFuel q) (.start : Configuration q) = (.done (searchSpec q 0), c) ∧
      c.total ≤ 12 * searchFuel q := by
  obtain ⟨steps, hs, c, hc⟩ := candidates_trace q (0 : ZMod q)
  have ht := Trace.cons Step.start hc
  have hbound : steps + 1 ≤ searchFuel q := by dsimp [searchFuel]; omega
  have hrun := ht.runFuel_done (searchFuel q - (steps + 1))
  have heq : steps + 1 + (searchFuel q - (steps + 1)) = searchFuel q := by omega
  rw [heq] at hrun
  exact ⟨startCost + c, hrun,
    ht.total_le.trans (Nat.mul_le_mul_left 12 hbound)⟩

/-- Executable bounded search returns a candidate or failure together with actual charges. -/
def search (q : ℕ) : Option (ZMod q) × Cost :=
  let result := runFuel (searchFuel q) (.start : Configuration q)
  match result.1 with
  | .done a => (a, result.2)
  | _ => (none, result.2)

/-- The public wrapper returns precisely the result of the fully completed search. -/
theorem search_eq_spec (q : ℕ) : (search q).1 = searchSpec q 0 := by
  obtain ⟨c, h, _⟩ := search_runFuel q
  simp [search, h]

/-- No modulus, including zero, can make the machine report a square as a nonsquare. -/
theorem search_sound (q : ℕ) (a : ZMod q) (h : (search q).1 = some a) : ¬IsSquare a := by
  rw [search_eq_spec] at h
  by_cases hq : q = 0
  · subst q
    simp [searchSpec] at h
  · exact searchSpec_sound (Nat.pos_of_ne_zero hq) q 0 a h

/-- Total modeled primitive operations are bounded by an explicit quadratic polynomial. -/
theorem search_cost_le (q : ℕ) : (search q).2.total ≤ 48 * q ^ 2 + 48 * q + 24 := by
  obtain ⟨c, h, hc⟩ := search_runFuel q
  simp only [search, h]
  calc
    c.total ≤ 12 * searchFuel q := hc
    _ = _ := by unfold searchFuel; ring

/-- An odd-prime input returns an executable certified parameter for a quadratic witness field. -/
theorem search_correct (q : ℕ) (hq : q.Prime) (hodd : q ≠ 2) :
    ∃ a : ZMod q, (search q).1 = some a ∧ ¬IsSquare a ∧
      (search q).2.total ≤ 48 * q ^ 2 + 48 * q + 24 := by
  have hne : (search q).1 ≠ none := by
    rw [search_eq_spec]
    exact searchSpec_prime_ne_none hq hodd
  cases h : (search q).1 with
  | none => exact (hne h).elim
  | some a => exact ⟨a, rfl, search_sound q a h, search_cost_le q⟩

/-- Candidates zero and one retain earlier root hits; candidate two has no root modulo three. -/
example : search 3 = (some 2, ⟨11, 9, 21, 27, 18, 48, 131, 1⟩) := by decide

/-- A complete seven-root scan certifies candidate three with its actual scan charges. -/
example : runFuel 30 (.roots 0 3 7 0 false : Configuration 7) =
    (.done (some 3), ⟨7, 7, 15, 15, 7, 30, 80, 1⟩) := by decide

/-- Characteristic two exhausts all candidates and reports failure with its full scan cost. -/
example : search 2 = (none, ⟨6, 4, 10, 15, 11, 26, 68, 1⟩) := by decide

/-- Zero modulus performs no square test and reports failure rather than a false certificate. -/
example : search 0 = (none, ⟨0, 0, 0, 1, 1, 2, 4, 1⟩) := by decide

/-- Insufficient fuel exposes the initialized counters, not a successful candidate. -/
example : runFuel 1 (.start : Configuration 3) =
    (.candidates 3 0, ⟨0, 0, 0, 0, 1, 1, 3, 0⟩) := by decide

end ZMod.NonsquareSearchMachine
