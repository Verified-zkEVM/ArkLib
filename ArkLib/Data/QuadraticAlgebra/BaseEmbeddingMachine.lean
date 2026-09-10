/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.QuadraticAlgebra.ArithmeticMachine

/-!
# Materialized base-field alphabets in a quadratic algebra

Each instruction embeds one scalar as `(x,0)` and allocates its list cell. A charged reversal
restores the input order. The algebra map occurs only in the semantic specification, not as
an uncharged runtime traversal. Input roots are shared; each newly materialized coordinate and
list cell is charged. This supplies the restricted center/jet alphabet used by the decoder.
-/

@[expose] public section

namespace QuadraticAlgebra.BaseEmbeddingMachine

abbrev Cost := ArithmeticMachine.Cost

def charge (data constants output : ℕ) : Cost :=
  { control := 1, data := data, constants := constants, output := output }

inductive Configuration (F : Type*) [Zero F] (a : F) where
  | scan (remaining : List F) (saved : List (QuadraticAlgebra F a 0))
  | reverse (remaining output : List (QuadraticAlgebra F a 0))
  | done (output : List (QuadraticAlgebra F a 0))
  deriving DecidableEq

variable {F : Type*} [Zero F] {a : F}

/-- One fixed-size allocation or reversal step; no bulk list map is executed. -/
def step : Configuration F a → Option (Configuration F a × Cost)
  | .scan (x :: xs) saved => some (.scan xs (⟨x, 0⟩ :: saved), charge 8 1 0)
  | .scan [] saved => some (.reverse saved [], charge 3 0 0)
  | .reverse (x :: xs) out => some (.reverse xs (x :: out), charge 5 0 0)
  | .reverse [] out => some (.done out, charge 2 0 1)
  | .done _ => none

/-- Exact transitions retain every materialization and output charge. -/
inductive Trace : ℕ → Configuration F a → Cost → Configuration F a → Prop where
  | nil (s) : Trace 0 s 0 s
  | cons {n s u t c e} (head : step s = some (u, c)) (tail : Trace n u e t) :
      Trace (n + 1) s (c + e) t

/-- Fuel executes one actual transition at a time. -/
def runFuel : ℕ → Configuration F a → Configuration F a × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step s with
      | none => (s, 0)
      | some (t, c) => let r := runFuel n t; (r.1, c + r.2)

/-- A completed trace remains complete under extra fuel, with unchanged work. -/
theorem Trace.runFuel_done {n : ℕ} {s : Configuration F a} {c : Cost} {out}
    (h : Trace n s c (.done out)) (extra : ℕ) :
    runFuel (n + extra) s = (.done out, c) := by
  generalize he : Configuration.done out = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head]
      dsimp only
      rw [ih he]

private theorem total_charge_add (data constants output : ℕ) (c : Cost) :
    (charge data constants output + c).total = 1 + data + constants + output + c.total := by
  change 0 + c.additions + (0 + c.multiplications) + (0 + c.negations) +
    (0 + c.inversions) + (0 + c.equalities) + (1 + c.control) +
    (data + c.data) + (constants + c.constants) + (output + c.output) = _
  simp only [ArithmeticMachine.Cost.total]
  omega

private theorem reverse_trace (xs out : List (QuadraticAlgebra F a 0)) :
    ∃ c, Trace (xs.length + 1) (.reverse xs out) c (.done (xs.reverse ++ out)) ∧
      c.total = 6 * xs.length + 4 := by
  induction xs generalizing out with
  | nil => exact ⟨charge 2 0 1 + 0, .cons rfl (.nil _), rfl⟩
  | cons x xs ih =>
      obtain ⟨c, ht, hc⟩ := ih (x :: out)
      refine ⟨charge 5 0 0 + c, ?_, ?_⟩
      · simpa [List.reverse_cons, List.append_assoc] using Trace.cons (by rfl) ht
      · rw [total_charge_add, hc]
        simp only [List.length_cons]
        omega

/-- Proof-only description of the coordinate output. -/
def embedded (xs : List F) : List (QuadraticAlgebra F a 0) := xs.map (fun x ↦ ⟨x, 0⟩)

/-- Every input scalar and output cell is processed, retaining the original order. -/
theorem scan_trace (xs : List F) (out : List (QuadraticAlgebra F a 0)) :
    ∃ c, Trace (2 * xs.length + out.length + 2) (.scan xs out) c
      (.done (out.reverse ++ embedded xs)) ∧ c.total = 16 * xs.length + 6 * out.length + 8 := by
  induction xs generalizing out with
  | nil =>
      obtain ⟨c, ht, hc⟩ := reverse_trace out []
      refine ⟨charge 3 0 0 + c, ?_, ?_⟩
      · simpa [embedded] using Trace.cons (by rfl) ht
      · rw [total_charge_add, hc]
        simp only [List.length_nil]
        omega
  | cons x xs ih =>
      obtain ⟨c, ht, hc⟩ := ih (⟨x, 0⟩ :: out)
      refine ⟨charge 8 1 0 + c, ?_, ?_⟩
      · convert Trace.cons (show step (.scan (x :: xs) out) = _ from rfl) ht using 1
        · simp only [List.length_cons]; omega
        · simp [embedded, List.reverse_cons, List.append_assoc]
      · rw [total_charge_add, hc]
        simp only [List.length_cons]
        omega

/-- Actual embedding uses linear fuel and exact linear allocation work. -/
theorem evaluation_runFuel (xs : List F) :
    ∃ c, runFuel (2 * xs.length + 2) (.scan xs [] : Configuration F a) =
      (.done (embedded xs), c) ∧ c.total = 16 * xs.length + 8 := by
  obtain ⟨c, ht, hc⟩ := scan_trace xs ([] : List (QuadraticAlgebra F a 0))
  exact ⟨c, by simpa using ht.runFuel_done 0, by simpa using hc⟩

end QuadraticAlgebra.BaseEmbeddingMachine
