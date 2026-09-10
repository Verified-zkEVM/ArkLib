/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
  ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Residual.ResidualSampleRefinement
/-!
# Closed batches of residual samples

A materialized point list is scanned in order. Each call advances the sample machine by exactly
one transition. Return, point-value pair allocation, list-cell allocation, reversal, and final
emission are explicit phases. Immutable polynomial inputs and untouched list tails are shared.
The emitted pair list is directly usable by a matrix consumer; no uncharged zip is needed.

Costs preserve every sample charge and add wrapper and allocation charges. Cell reads retrieve
head and tail together; retained registers are shared and literals are free, as in the sample
machine. Host fuel, input preparation, point enumeration, scalar bit costs, and linear solving
remain outside this contract. Duplicates are allowed; distinctness is a consumer requirement.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.ResidualBatchMachine

open Polynomial MvPolynomial CompPoly

abbrev Cost := JetHornerMachine.Cost

/-- Immutable materialized polynomial inputs shared across every call. -/
structure Input (F : Type*) where
  coefficients : List F
  terms : List (EvaluationMachine.Term F)
  center : F
  order : ℕ

/-- A call reads the immutable inputs and the current point. -/
def sampleInput {F : Type*} (input : Input F) (u : F) : ResidualSampleMachine.Input F :=
  ⟨input.coefficients, input.terms, input.center, u, input.order⟩

/-- Initialize the point cursor and empty accumulator. -/
def startCost : Cost := ⟨0, 0, 1, 3, 0, 0⟩
/-- Read a point cell, retain the point, and write the next cursor and entry payload. -/
def takeCost : Cost := ⟨0, 0, 1, 4, 0, 0⟩
/-- Read the five callee input registers and initialize its state root. -/
def entryCost : Cost := ⟨0, 0, 1, 6, 0, 0⟩
/-- Read the completed callee, retain its scalar, and write the allocation payload. -/
def returnCost : Cost := ⟨0, 0, 1, 3, 0, 0⟩
/-- Read point and scalar, then allocate both pair-coordinate slots. -/
def pairCost : Cost := ⟨0, 0, 1, 4, 0, 0⟩
/-- Read pair and accumulator roots, allocate a list cell and update the accumulator and phase. -/
def saveCost : Cost := ⟨0, 0, 1, 5, 0, 0⟩
/-- Read the exhausted point cursor and initialize the output root. -/
def beginReverseCost : Cost := ⟨0, 0, 1, 2, 0, 0⟩
/-- Read a cell and output root, allocate the output cell and update both cursors. -/
def reverseCost : Cost := ⟨0, 0, 1, 5, 0, 0⟩
/-- Read the exhausted cursor and emit the retained pair-list handle. -/
def emitCost : Cost := ⟨0, 0, 1, 2, 0, 1⟩

/-- The batch holds the actual suspended scalar-sample configuration. -/
inductive Configuration (F : Type*) where
  | start (points : List F)
  | scan (remaining : List F) (reversed : List (F × F))
  | enter (point : F) (remaining : List F) (reversed : List (F × F))
  | call (point : F) (remaining : List F) (reversed : List (F × F))
      (state : ResidualSampleMachine.Configuration F)
  | pack (point value : F) (remaining : List F) (reversed : List (F × F))
  | save (pair : F × F) (remaining : List F) (reversed : List (F × F))
  | reverse (remaining result : List (F × F))
  | done (result : List (F × F))
  deriving DecidableEq, Repr

variable {F : Type*}

section Semiring

variable [CommSemiring F]

/-- Independent operational rules; callee work requires a single actual sample-machine step. -/
inductive Step (input : Input F) : Configuration F → Cost → Configuration F → Prop where
  | start {ps} : Step input (.start ps) startCost (.scan ps [])
  | take {u ps rev} : Step input (.scan (u :: ps) rev) takeCost (.enter u ps rev)
  | enter {u ps rev} : Step input (.enter u ps rev) entryCost (.call u ps rev .start)
  | call {u ps rev s t c} (h : ResidualSampleMachine.Step (sampleInput input u) s c t) :
      Step input (.call u ps rev s) (c + ResidualSampleMachine.wrapperCost 1) (.call u ps rev t)
  | return {u ps rev v} : Step input (.call u ps rev (.done v)) returnCost (.pack u v ps rev)
  | pack {u v ps rev} : Step input (.pack u v ps rev) pairCost (.save (u, v) ps rev)
  | save {p ps rev} : Step input (.save p ps rev) saveCost (.scan ps (p :: rev))
  | beginReverse {rev} : Step input (.scan [] rev) beginReverseCost (.reverse rev [])
  | reverse {p ps out} : Step input (.reverse (p :: ps) out) reverseCost (.reverse ps (p :: out))
  | emit {out} : Step input (.reverse [] out) emitCost (.done out)

/-- Executable dispatch never invokes a bulk sample run, map, zip, or list reversal. -/
def step (input : Input F) : Configuration F → Option (Configuration F × Cost)
  | .start ps => some (.scan ps [], startCost)
  | .scan (u :: ps) rev => some (.enter u ps rev, takeCost)
  | .scan [] rev => some (.reverse rev [], beginReverseCost)
  | .enter u ps rev => some (.call u ps rev .start, entryCost)
  | .call u ps rev s => match ResidualSampleMachine.step (sampleInput input u) s with
      | some (t, c) => some (.call u ps rev t, c + ResidualSampleMachine.wrapperCost 1)
      | none => match s with
          | .done v => some (.pack u v ps rev, returnCost)
          | _ => none
  | .pack u v ps rev => some (.save (u, v) ps rev, pairCost)
  | .save p ps rev => some (.scan ps (p :: rev), saveCost)
  | .reverse (p :: ps) out => some (.reverse ps (p :: out), reverseCost)
  | .reverse [] out => some (.done out, emitCost)
  | .done _ => none

/-- Independent rules execute with their exact stated charge. -/
theorem Step.step_eq {input : Input F} {s t : Configuration F} {c : Cost}
    (h : Step input s c t) : step input s = some (t, c) := by
  cases h with
  | call h => simp [step, h.step_eq]
  | _ => rfl

/-- Every executable branch is covered by the independent rules. -/
theorem step_sound {input : Input F} {s t : Configuration F} {c : Cost}
    (h : step input s = some (t, c)) : Step input s c t := by
  cases s with
  | start ps => cases h; constructor
  | scan ps rev => cases ps <;> cases h <;> constructor
  | enter u ps rev => cases h; constructor
  | pack u v ps rev => cases h; constructor
  | save p ps rev => cases h; constructor
  | reverse ps out => cases ps <;> cases h <;> constructor
  | done out => simp [step] at h
  | call u ps rev s =>
      cases hs : ResidualSampleMachine.step (sampleInput input u) s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.call (ResidualSampleMachine.step_sound hs)
      | none =>
          cases s <;> simp only [step, hs, Option.some.injEq, Prod.mk.injEq,
            reduceCtorEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.return

/-- Finite traces accumulate actual callee and batch charges. -/
inductive Trace (input : Input F) : ℕ → Configuration F → Cost → Configuration F → Prop where
  | nil (s) : Trace input 0 s 0 s
  | cons {n s u t c d} (head : Step input s c u) (tail : Trace input n u d t) :
      Trace input (n + 1) s (c + d) t

private theorem cost_assoc (a b c : Cost) : (a + b) + c = a + (b + c) := by
  ext <;> simp only [JetHornerMachine.cost_add, Nat.add_assoc]

/-- Trace concatenation preserves exact costs and transition counts. -/
theorem Trace.trans {input : Input F} {n m : ℕ} {s t u : Configuration F} {c d : Cost}
    (h : Trace input n s c t) (h' : Trace input m t d u) :
    Trace input (n + m) s (c + d) u := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa only [Nat.add_right_comm, cost_assoc] using Trace.cons head (ih h')

/-- Fuel exhaustion exposes the current phase rather than fabricating an emitted batch. -/
def runFuel (input : Input F) : ℕ → Configuration F → Configuration F × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step input s with
      | none => (s, 0)
      | some (t, c) => let result := runFuel input n t; (result.1, c + result.2)

/-- Every interpreter result has an actual trace with its accumulated charges. -/
theorem runFuel_refines (input : Input F) (fuel : ℕ) (s : Configuration F) :
    ∃ n ≤ fuel, Trace input n s (runFuel input fuel s).2 (runFuel input fuel s).1 := by
  induction fuel generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ fuel ih =>
      cases hs : step input s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- Exact trace fuel reproduces its endpoint and cost. -/
theorem Trace.runFuel_eq {input : Input F} {n : ℕ} {s t : Configuration F} {c : Cost}
    (h : Trace input n s c t) : runFuel input n s = (t, c) := by
  induction h with
  | nil s => rfl
  | cons head tail ih => simp [runFuel, head.step_eq, ih]

/-- Lift each sample transition with one charged batch dispatch. -/
theorem lift_sample_trace (input : Input F) (u : F) (ps : List F) (rev : List (F × F))
    {n : ℕ} {s t : ResidualSampleMachine.Configuration F} {c : Cost}
    (h : ResidualSampleMachine.Trace (sampleInput input u) n s c t) :
    Trace input n (.call u ps rev s) (c + ResidualSampleMachine.wrapperCost n)
      (.call u ps rev t) := by
  induction h with
  | nil s =>
      simpa [ResidualSampleMachine.wrapperCost] using
        Trace.nil (input := input) (.call u ps rev s)
  | @cons n s u' t c d head tail ih =>
      have heq : (c + ResidualSampleMachine.wrapperCost 1) +
          (d + ResidualSampleMachine.wrapperCost n) =
            (c + d) + ResidualSampleMachine.wrapperCost (n + 1) := by
        ext <;> simp [ResidualSampleMachine.wrapperCost] <;> omega
      rw [← heq]
      exact Trace.cons (Step.call head) ih

/-- The callee fuel is independent of its scalar point. -/
def singleFuel (input : Input F) : ℕ := ResidualSampleMachine.fuel (sampleInput input 0)
/-- The full callee cost is independent of its scalar point. -/
def singleCost (input : Input F) : Cost := ResidualSampleMachine.cost (sampleInput input 0)

/-- Componentwise repeated charges, used only in specifications. -/
def scaleCost (n : ℕ) (c : Cost) : Cost :=
  ⟨n * c.additions, n * c.multiplications, n * c.control, n * c.data,
    n * c.natural, n * c.output⟩

/-- One full sample, all delegated dispatches, and six per-point administrative phases. -/
def itemCost (input : Input F) : Cost := singleCost input +
  ResidualSampleMachine.wrapperCost (singleFuel input) + ⟨0, 0, 6, 27, 0, 0⟩
/-- Exact batch fuel, including final reversal and emission. -/
def fuel (input : Input F) (n : ℕ) : ℕ := n * (singleFuel input + 6) + 3
/-- Exact batch charges, with every scalar-sample output retained in the total. -/
def cost (input : Input F) (n : ℕ) : Cost :=
  scaleCost n (itemCost input) + ⟨0, 0, 3, 7, 0, 1⟩

/-- Mathematical scalar specification of the existing callee. -/
def sampleValue (input : Input F) (u : F) : F :=
  EvaluationMachine.termValue (ResidualSampleMachine.sampleValues (sampleInput input u)) input.terms
/-- Ordered pair-list specification; executable dispatch does not invoke this map. -/
def outputSpec (input : Input F) (points : List F) : List (F × F) :=
  points.map (fun u ↦ (u, sampleValue input u))

private theorem reverse_trace (input : Input F) (rev out : List (F × F)) :
    Trace input (rev.length + 1) (.reverse rev out)
      (scaleCost rev.length reverseCost + emitCost) (.done (rev.reverse ++ out)) := by
  induction rev generalizing out with
  | nil => simpa [scaleCost] using Trace.cons (Step.emit (input := input)) (Trace.nil (.done out))
  | cons p rev ih =>
      convert Trace.cons Step.reverse (ih (p :: out)) using 1 <;>
        simp [scaleCost, reverseCost, emitCost, List.reverse_cons, List.append_assoc, Nat.add_mul]
      all_goals omega

/-- Every point is sampled by a lifted callee trace before its pair and list cell are allocated. -/
theorem scan_trace (input : Input F) (points : List F) (rev : List (F × F)) :
    Trace input (points.length * (singleFuel input + 6) + rev.length + 2) (.scan points rev)
      (scaleCost points.length (itemCost input) + scaleCost rev.length reverseCost +
        (beginReverseCost + emitCost)) (.done (rev.reverse ++ outputSpec input points)) := by
  induction points generalizing rev with
  | nil =>
      convert Trace.cons Step.beginReverse (reverse_trace input rev []) using 1 <;>
        simp [scaleCost, outputSpec, beginReverseCost, emitCost, reverseCost]
      all_goals omega
  | cons u ps ih =>
      have hs := lift_sample_trace input u ps rev
        (ResidualSampleMachine.evaluation_trace (sampleInput input u))
      have ht := Trace.cons Step.take (Trace.cons Step.enter (hs.trans
        (Trace.cons Step.return (Trace.cons Step.pack (Trace.cons Step.save
          (ih ((u, sampleValue input u) :: rev)))))))
      convert ht using 1
      · change (ps.length + 1) * (singleFuel input + 6) + rev.length + 2 =
          singleFuel input +
            (ps.length * (singleFuel input + 6) + (rev.length + 1) + 2 + 1 + 1 + 1) + 1 + 1
        ring
      · ext <;> simp [scaleCost, itemCost, singleCost, singleFuel, sampleInput,
          takeCost, entryCost, returnCost, pairCost, saveCost, reverseCost, beginReverseCost,
          emitCost, ResidualSampleMachine.cost, ResidualSampleMachine.fuel,
          ResidualSampleMachine.jetFuel, ResidualSampleMachine.scalarFuel,
          ResidualSampleMachine.wrapperCost] <;> ring
      · simp [outputSpec, List.reverse_cons, List.append_assoc]

/-- Actual batch execution returns the ordered point-value list and its full primitive cost. -/
theorem batch_runFuel (input : Input F) (points : List F) :
    runFuel input (fuel input points.length) (.start points) =
      (.done (outputSpec input points), cost input points.length) := by
  have ht := Trace.cons Step.start (scan_trace input points [])
  have hrun := ht.runFuel_eq
  convert hrun using 1
  · simp [fuel]
  · ext <;> simp [cost, scaleCost, startCost, beginReverseCost, emitCost] <;> omega

private theorem total_add (a b : Cost) : (a + b).total = a.total + b.total := by
  simp only [JetHornerMachine.Cost.total, JetHornerMachine.cost_add]
  omega

private theorem total_scale (n : ℕ) (c : Cost) : (scaleCost n c).total = n * c.total := by
  simp only [scaleCost, JetHornerMachine.Cost.total]
  ring

/-- Linear batch overhead preserves the full single-sample cost and fuel contributions. -/
theorem cost_total_le (input : Input F) (n : ℕ) :
    (cost input n).total ≤ 33 * (n + 1) * ((singleCost input).total + singleFuel input + 1) := by
  simp only [cost, itemCost, total_add, total_scale]
  simp only [ResidualSampleMachine.wrapperCost, JetHornerMachine.Cost.total]
  nlinarith

/-- The actual batch, not just the declared cost expression, satisfies the linear bound. -/
theorem batch_cost_le (input : Input F) (points : List F) :
    (runFuel input (fuel input points.length) (.start points)).2.total ≤
      33 * (points.length + 1) * ((singleCost input).total + singleFuel input + 1) := by
  rw [batch_runFuel]
  exact cost_total_le input points.length

end Semiring

section Concrete

variable [Field F] [DecidableEq F] {r : ℕ}

/-- A scalar sample agrees with the concrete residual under explicit input representations. -/
theorem sampleValue_eq_effectiveResidual
    (Q : CPoly.CMvPolynomial (r + 2) F) (center u : F) (P : CPolynomial F)
    (cs : List F) (terms : List (EvaluationMachine.Term F))
    (hP : JetHornerMachine.coefficientPolynomial cs = P.toPoly)
    (hQ : EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q)) :
    sampleValue ⟨cs, terms, center, r⟩ u = (effectiveResidual Q center P).toPoly.eval u := by
  have h := (ResidualSampleMachine.evaluation_trace
    (sampleInput (⟨cs, terms, center, r⟩ : Input F) u)).runFuel_eq.symm.trans
      (ResidualSampleMachine.evaluation_runFuel_eq_effectiveResidual Q center u P cs terms hP hQ)
  exact ResidualSampleMachine.Configuration.done.inj (congrArg Prod.fst h)

/-- Actual output is the concrete residual sampled at every supplied point, in original order.
No distinctness or degree bound is needed for this operational refinement. -/
theorem batch_runFuel_eq_effectiveResidual
    (Q : CPoly.CMvPolynomial (r + 2) F) (center : F) (P : CPolynomial F)
    (cs : List F) (terms : List (EvaluationMachine.Term F)) (points : List F)
    (hP : JetHornerMachine.coefficientPolynomial cs = P.toPoly)
    (hQ : EvaluationMachine.sparsePolynomial terms =
      MvPolynomial.rename Fin.val (CPoly.fromCMvPolynomial Q)) :
    let input : Input F := ⟨cs, terms, center, r⟩
    runFuel input (fuel input points.length) (.start points) =
      (.done (points.map (fun u ↦ (u, (effectiveResidual Q center P).toPoly.eval u))),
        cost input points.length) := by
  dsimp only
  rw [batch_runFuel]
  congr 2
  apply List.map_congr_left
  intro u hu
  rw [sampleValue_eq_effectiveResidual Q center u P cs terms hP hQ]

end Concrete

end ReedSolomon.HiddenDerivative.ResidualBatchMachine
