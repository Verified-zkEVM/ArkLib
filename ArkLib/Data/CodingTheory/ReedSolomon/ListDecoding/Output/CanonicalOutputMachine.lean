/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import
ArkLib.Data.CodingTheory.ReedSolomon.Computation.RootFinding.Selection.StageRootsMachine
public import ArkLib.Data.CodingTheory.ReedSolomon.ListDecoding.Output.CanonicalAcceptanceSemantics
/-!
# Closed canonical collection of base-field root candidates

This driver consumes the actual context-tagged stage records. It constructs a guard input from
each record by bounded root accesses, executes canonical acceptance instruction by instruction,
and allocates only accepted base-output cells. Explicit reversal preserves enumeration order.
There is no duplicate search, set conversion, bulk filter, or uncharged acceptance callback.
Duplicate freedom follows separately from the generated records' canonical-witness properties.
-/

@[expose] public section

namespace ReedSolomon.ListDecoding.CanonicalOutputMachine

abbrev Record := HiddenDerivative.StageRootsMachine.Record

namespace Accept
export CanonicalAcceptanceMachine
  (Configuration Step step Trace runFuel runFuel_refines result fuel workBound)
end Accept

/-- The guard retains the original maximum order and exact generated context roots. -/
def guardInput {E : Type*} (order : ℕ) (samples : List E) (record : Record E) :
    HiddenDerivative.CanonicalGuardMachine.Input E :=
  ⟨record.coefficients, samples, order, record.center, record.context.separant⟩

/-- The current acceptance state and immutable unvisited/output lists are explicit. -/
inductive Configuration (F : Type*) (a b : F) where
  | start (records : List (Record (QuadraticAlgebra F a b)))
  | scan (records : List (Record (QuadraticAlgebra F a b))) (saved : List (List F))
  | accept (record : Record (QuadraticAlgebra F a b))
      (records : List (Record (QuadraticAlgebra F a b))) (saved : List (List F))
      (inner : Accept.Configuration F a b)
  | save (coefficients : List F) (records : List (Record (QuadraticAlgebra F a b)))
      (saved : List (List F))
  | reverse (remaining output : List (List F))
  | emit (output : List (List F))
  | done (output : List (List F))
  deriving DecidableEq

variable {F : Type*} [CommSemiring F] [DecidableEq F] {a b : F}

/-- Every record preparation, acceptance instruction and output cell has a fixed local charge. -/
inductive Step (order : ℕ) (samples : List (QuadraticAlgebra F a b)) (w k A : ℕ)
    (rows : List (F × F)) : Configuration F a b → ℕ → Configuration F a b → Prop where
  | start {rs} : Step order samples w k A rows (.start rs) 4 (.scan rs [])
  | next {r rs out} : Step order samples w k A rows (.scan (r :: rs) out) 12
      (.accept r rs out (.start r.context.previous))
  | accept {r rs out s t c} (h : Accept.Step (guardInput order samples r) w k A rows s c t) :
      Step order samples w k A rows (.accept r rs out s) (c + 3) (.accept r rs out t)
  | rejected {r rs out} : Step order samples w k A rows (.accept r rs out (.done none)) 3
      (.scan rs out)
  | accepted {r rs out cs} :
      Step order samples w k A rows (.accept r rs out (.done (some cs))) 3 (.save cs rs out)
  | save {cs rs out} : Step order samples w k A rows (.save cs rs out) 4 (.scan rs (cs :: out))
  | scanned {out} : Step order samples w k A rows (.scan [] out) 3 (.reverse out [])
  | reverse {cs rest out} : Step order samples w k A rows (.reverse (cs :: rest) out) 6
      (.reverse rest (cs :: out))
  | reversed {out} : Step order samples w k A rows (.reverse [] out) 3 (.emit out)
  | emit {out} : Step order samples w k A rows (.emit out) 3 (.done out)

/-- Only one actual callee instruction or bounded cursor/allocation operation is dispatched. -/
def step (order : ℕ) (samples : List (QuadraticAlgebra F a b)) (w k A : ℕ)
    (rows : List (F × F)) : Configuration F a b → Option (Configuration F a b × ℕ)
  | .start rs => some (.scan rs [], 4)
  | .scan (r :: rs) out => some (.accept r rs out (.start r.context.previous), 12)
  | .scan [] out => some (.reverse out [], 3)
  | .accept r rs out s => match Accept.step (guardInput order samples r) w k A rows s with
      | some (t, c) => some (.accept r rs out t, c + 3)
      | none => match s with
          | .done none => some (.scan rs out, 3)
          | .done (some cs) => some (.save cs rs out, 3)
          | _ => none
  | .save cs rs out => some (.scan rs (cs :: out), 4)
  | .reverse (cs :: rest) out => some (.reverse rest (cs :: out), 6)
  | .reverse [] out => some (.emit out, 3)
  | .emit out => some (.done out, 3)
  | .done _ => none

/-- The independent transition rules determine the actual interpreter result. -/
theorem Step.step_eq {order w k A : ℕ} {samples : List (QuadraticAlgebra F a b)}
    {rows : List (F × F)} {s t : Configuration F a b} {c : ℕ}
    (h : Step order samples w k A rows s c t) : step order samples w k A rows s = some (t, c) := by
  cases h with
  | accept h => simp [step, h.step_eq]
  | _ => rfl

/-- Every executable successor is covered by the independent operational rules. -/
theorem step_sound {order w k A : ℕ} {samples : List (QuadraticAlgebra F a b)}
    {rows : List (F × F)} {s t : Configuration F a b} {c : ℕ}
    (h : step order samples w k A rows s = some (t, c)) : Step order samples w k A rows s c t := by
  cases s with
  | accept r rs out s =>
      cases hs : Accept.step (guardInput order samples r) w k A rows s with
      | some pair =>
          simp only [step, hs, Option.some.injEq, Prod.mk.injEq] at h
          rcases h with ⟨rfl, rfl⟩
          exact Step.accept (CanonicalAcceptanceMachine.step_sound hs)
      | none =>
          cases s with
          | done out => cases out <;> cases h <;> constructor
          | _ => simp [step, hs] at h
  | scan rs out => cases rs <;> cases h <;> constructor
  | reverse rs out => cases rs <;> cases h <;> constructor
  | done out => simp [step] at h
  | _ => cases h; constructor

/-- Finite traces retain the sum of every nested and local charge. -/
inductive Trace (order : ℕ) (samples : List (QuadraticAlgebra F a b)) (w k A : ℕ)
    (rows : List (F × F)) : ℕ → Configuration F a b → ℕ → Configuration F a b → Prop where
  | nil (s) : Trace order samples w k A rows 0 s 0 s
  | cons {n s t u c d} (head : Step order samples w k A rows s c t)
      (tail : Trace order samples w k A rows n t d u) :
      Trace order samples w k A rows (n + 1) s (c + d) u

/-- Concatenation preserves trace lengths and all accumulated work. -/
theorem Trace.trans {order w k A n m : ℕ} {samples : List (QuadraticAlgebra F a b)}
    {rows : List (F × F)} {s t u : Configuration F a b} {c d : ℕ}
    (h : Trace order samples w k A rows n s c t) (h' : Trace order samples w k A rows m t d u) :
    Trace order samples w k A rows (n + m) s (c + d) u := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

/-- Host fuel bounds the number of dispatched instructions, not their individual work. -/
def runFuel (order : ℕ) (samples : List (QuadraticAlgebra F a b)) (w k A : ℕ)
    (rows : List (F × F)) : ℕ → Configuration F a b → Configuration F a b × ℕ
  | 0, s => (s, 0)
  | n + 1, s => match step order samples w k A rows s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel order samples w k A rows n t; (r.1, c + r.2)

/-- Every interpreter run produces an actual trace prefix with identical charges. -/
theorem runFuel_refines (order w k A budget : ℕ) (samples : List (QuadraticAlgebra F a b))
    (rows : List (F × F)) (s : Configuration F a b) :
    ∃ n ≤ budget, Trace order samples w k A rows n s
      (runFuel order samples w k A rows budget s).2
      (runFuel order samples w k A rows budget s).1 := by
  induction budget generalizing s with
  | zero => exact ⟨0, le_rfl, Trace.nil s⟩
  | succ budget ih =>
      cases hs : step order samples w k A rows s with
      | none => exact ⟨0, Nat.zero_le _, by simpa [runFuel, hs] using Trace.nil s⟩
      | some pair =>
          obtain ⟨n, hn, ht⟩ := ih pair.1
          exact ⟨n + 1, Nat.succ_le_succ hn, by
            simpa [runFuel, hs] using Trace.cons (step_sound hs) ht⟩

/-- Completed traces remain completed with exactly the same work under additional fuel. -/
theorem Trace.runFuel_done {order w k A n : ℕ} {samples : List (QuadraticAlgebra F a b)}
    {rows : List (F × F)} {s : Configuration F a b} {c : ℕ} {out : List (List F)}
    (h : Trace order samples w k A rows n s c (.done out)) (extra : ℕ) :
    runFuel order samples w k A rows (n + extra) s = (.done out, c) := by
  generalize he : Configuration.done out = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih he]

/-- An acceptance run is embedded one instruction at a time with its caller charge. -/
theorem lift_accept {order w k A n : ℕ} (samples : List (QuadraticAlgebra F a b))
    (rows : List (F × F)) (record : Record (QuadraticAlgebra F a b))
    (records : List (Record (QuadraticAlgebra F a b))) (out : List (List F))
    {s t : Accept.Configuration F a b} {c : ℕ}
    (h : Accept.Trace (guardInput order samples record) w k A rows n s c t) :
    Trace order samples w k A rows n (.accept record records out s) (c + 3 * n)
      (.accept record records out t) := by
  induction h with
  | nil s => exact Trace.nil _
  | cons head tail ih =>
      convert Trace.cons (Step.accept head) ih using 1
      omega

/-- Proof-only ordered output specification; the interpreter never invokes a bulk filter. -/
def result (order : ℕ) (samples : List (QuadraticAlgebra F a b)) (w k A : ℕ)
    (rows : List (F × F)) (records : List (Record (QuadraticAlgebra F a b))) : List (List F) :=
  records.filterMap fun r ↦ Accept.result (guardInput order samples r) r.context.previous w k A rows

/-- Proof-side bound for one fully composed acceptance call. -/
def itemFuel (order : ℕ) (samples : List (QuadraticAlgebra F a b)) (w k n : ℕ)
    (record : Record (QuadraticAlgebra F a b)) : ℕ :=
  Accept.fuel (guardInput order samples record) record.context.previous w k n

/-- Proof-side work of the same actual acceptance call. -/
def itemWork (order : ℕ) (samples : List (QuadraticAlgebra F a b)) (w k n : ℕ)
    (record : Record (QuadraticAlgebra F a b)) : ℕ :=
  Accept.workBound (guardInput order samples record) record.context.previous w k n

/-- Each item pays for its acceptance and at most four local/reversal transitions. -/
def scanFuel (order : ℕ) (samples : List (QuadraticAlgebra F a b)) (w k n : ℕ) :
    List (Record (QuadraticAlgebra F a b)) → ℕ
  | [] => 3
  | r :: rs => itemFuel order samples w k n r + scanFuel order samples w k n rs + 4

/-- The work sum retains caller dispatch and charges every possible emitted outer cell. -/
def scanWork (order : ℕ) (samples : List (QuadraticAlgebra F a b)) (w k n : ℕ) :
    List (Record (QuadraticAlgebra F a b)) → ℕ
  | [] => 12
  | r :: rs => itemWork order samples w k n r + 3 * itemFuel order samples w k n r +
      scanWork order samples w k n rs + 30

/-- The complete host-fuel bound adds initial dispatch to the per-record sum. -/
def fuel (order : ℕ) (samples : List (QuadraticAlgebra F a b)) (w k n : ℕ)
    (records : List (Record (QuadraticAlgebra F a b))) : ℕ :=
  scanFuel order samples w k n records + 1

/-- The complete actual-work bound includes initial input access. -/
def workBound (order : ℕ) (samples : List (QuadraticAlgebra F a b)) (w k n : ℕ)
    (records : List (Record (QuadraticAlgebra F a b))) : ℕ :=
  scanWork order samples w k n records + 4

/-- Reversal visits and charges each saved output cell before final emission. -/
theorem reverse_trace (order w k A : ℕ) (samples : List (QuadraticAlgebra F a b))
    (rows : List (F × F)) (remaining output : List (List F)) :
    ∃ c, Trace order samples w k A rows (remaining.length + 2) (.reverse remaining output) c
      (.done (remaining.reverse ++ output)) ∧ c = 6 * remaining.length + 6 := by
  induction remaining generalizing output with
  | nil =>
      refine ⟨6, ?_, by simp⟩
      simpa using Trace.cons (Step.reversed (order := order) (samples := samples)
        (w := w) (k := k) (A := A) (rows := rows)) (Trace.cons Step.emit (Trace.nil _))
  | cons cs rest ih =>
      obtain ⟨c, ht, hc⟩ := ih (cs :: output)
      refine ⟨6 + c, ?_, ?_⟩
      · simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
          Trace.cons Step.reverse ht
      · simp only [List.length_cons]
        omega

/-- Every tagged candidate is checked by its actual child program, with exact ordered output. -/
theorem scan_trace (order w k A : ℕ) (samples : List (QuadraticAlgebra F a b))
    (rows : List (F × F)) (records : List (Record (QuadraticAlgebra F a b)))
    (hwidth : ∀ r ∈ records, r.coefficients.length = w) (saved : List (List F)) :
    ∃ n c, Trace order samples w k A rows n (.scan records saved) c
      (.done (saved.reverse ++ result order samples w k A rows records)) ∧
      n ≤ scanFuel order samples w k rows.length records + saved.length ∧
      c ≤ scanWork order samples w k rows.length records + 6 * saved.length := by
  induction records generalizing saved with
  | nil =>
      obtain ⟨c, ht, hc⟩ := reverse_trace order w k A samples rows saved []
      refine ⟨saved.length + 2 + 1, 3 + c, ?_, ?_, ?_⟩
      · simpa [result] using Trace.cons Step.scanned ht
      · simp [scanFuel]; omega
      · simp only [scanWork]
        omega
  | cons record records ih =>
      let input := guardInput order samples record
      obtain ⟨ac, har, hac⟩ := CanonicalAcceptanceMachine.evaluation_runFuel input
        record.context.previous w k A rows (hwidth record (by simp))
      obtain ⟨an, han, hat⟩ := Accept.runFuel_refines input w k A
        (Accept.fuel input record.context.previous w k rows.length) rows
          (.start record.context.previous)
      rw [har] at hat
      have htail : ∀ r ∈ records, r.coefficients.length = w :=
        fun r hr ↦ hwidth r (by simp [hr])
      have ha := lift_accept (order := order) samples rows record records saved hat
      cases ho : Accept.result input record.context.previous w k A rows with
      | none =>
          rw [ho] at ha
          obtain ⟨n, c, ht, hn, hc⟩ := ih htail saved
          have hall := Trace.cons Step.next (ha.trans (Trace.cons Step.rejected ht))
          refine ⟨an + (n + 1) + 1, 12 + ((ac + 3 * an) + (3 + c)), ?_, ?_, ?_⟩
          · simpa only [result, List.filterMap_cons, input, ho, Option.map_none,
              Option.getD_none] using hall
          · dsimp [scanFuel, itemFuel, input] at *
            omega
          · dsimp [scanWork, itemWork, itemFuel, input] at *
            omega
      | some cs =>
          rw [ho] at ha
          obtain ⟨n, c, ht, hn, hc⟩ := ih htail (cs :: saved)
          have hall := Trace.cons Step.next (ha.trans
            (Trace.cons Step.accepted (Trace.cons Step.save ht)))
          refine ⟨an + (n + 1 + 1) + 1, 12 + ((ac + 3 * an) + (3 + (4 + c))), ?_, ?_, ?_⟩
          · simpa [result, List.filterMap_cons, input, ho, List.reverse_cons,
              List.append_assoc] using hall
          · dsimp [scanFuel, itemFuel, input] at *
            omega
          · dsimp [scanWork, itemWork, itemFuel, input] at *
            omega

/-- The collector returns precisely its canonical accepted subsequence with the same work bound. -/
theorem evaluation_runFuel (order w k A : ℕ) (samples : List (QuadraticAlgebra F a b))
    (rows : List (F × F)) (records : List (Record (QuadraticAlgebra F a b)))
    (hwidth : ∀ r ∈ records, r.coefficients.length = w) :
    ∃ c, runFuel order samples w k A rows (fuel order samples w k rows.length records)
      (.start records) = (.done (result order samples w k A rows records), c) ∧
      c ≤ workBound order samples w k rows.length records := by
  obtain ⟨n, c, ht, hn, hc⟩ := scan_trace order w k A samples rows records hwidth []
  simp only [List.reverse_nil, List.nil_append, List.length_nil, Nat.add_zero, Nat.mul_zero] at *
  have htrace := Trace.cons Step.start ht
  have hle : n + 1 ≤ fuel order samples w k rows.length records := by dsimp [fuel]; omega
  have he := htrace.runFuel_done (fuel order samples w k rows.length records - (n + 1))
  rw [Nat.add_sub_of_le hle] at he
  exact ⟨4 + c, he, by dsimp [workBound]; omega⟩

end ReedSolomon.ListDecoding.CanonicalOutputMachine
