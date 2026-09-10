/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.ZMod.NonsquareSearchMachine
public import Mathlib.Data.List.OfFn

/-!
# Charged materialized sample prefixes

A natural counter selects the first requested number of list entries. Cell allocation, counter
updates and output-order restoration are explicit steps. `take` and `ofFn` occur only in proofs.
-/

@[expose] public section

namespace List.PrefixMachine

abbrev Cost := ZMod.NonsquareSearchMachine.Cost

/-- A dispatch with natural operations, data operations and optional output emission. -/
def charge (natural data output : ℕ) : Cost := ⟨0, 0, 0, natural, 0, 1, data, output⟩

/-- Prefix traversal and explicit reversal; failure never fabricates missing entries. -/
inductive Configuration (α : Type*) where
  | scan (remaining : ℕ) (input saved : List α) (count : ℕ)
  | reverse (saved output : List α) (count : ℕ)
  | done (result : Option (List α × ℕ))
  deriving DecidableEq

variable {α : Type*}

/-- Independent local rules include each allocated cell and processed-count increment. -/
inductive Step : Configuration α → Cost → Configuration α → Prop where
  | finish {xs pre n} : Step (.scan 0 xs pre n) (charge 1 3 0) (.reverse pre [] n)
  | missing {k pre n} : Step (.scan (k + 1) [] pre n) (charge 1 2 1) (.done none)
  | take {k x xs pre n} : Step (.scan (k + 1) (x :: xs) pre n) (charge 3 6 0)
      (.scan k xs (x :: pre) (n + 1))
  | reverse {x xs out n} : Step (.reverse (x :: xs) out n) (charge 0 5 0)
      (.reverse xs (x :: out) n)
  | emit {out n} : Step (.reverse [] out n) (charge 0 3 1) (.done (some (out, n)))

/-- No whole-list operation occurs in executable dispatch. -/
def step : Configuration α → Option (Configuration α × Cost)
  | .scan 0 _ pre n => some (.reverse pre [] n, charge 1 3 0)
  | .scan (_ + 1) [] _ _ => some (.done none, charge 1 2 1)
  | .scan (k + 1) (x :: xs) pre n => some (.scan k xs (x :: pre) (n + 1), charge 3 6 0)
  | .reverse (x :: xs) out n => some (.reverse xs (x :: out) n, charge 0 5 0)
  | .reverse [] out n => some (.done (some (out, n)), charge 0 3 1)
  | .done _ => none

/-- Independent rules fix both the next state and its exact ledger. -/
theorem Step.step_eq {s t : Configuration α} {c : Cost} (h : Step s c t) :
    step s = some (t, c) := by cases h <;> rfl

/-- Finite traces retain all primitive costs. -/
inductive Trace : ℕ → Configuration α → Cost → Configuration α → Prop where
  | nil (s) : Trace 0 s 0 s
  | cons {n s u t c e} (head : Step s c u) (tail : Trace n u e t) : Trace (n + 1) s (c + e) t

/-- Compose two exact traces. -/
theorem Trace.trans {n m : ℕ} {s u t : Configuration α} {c e : Cost}
    (h : Trace n s c u) (h' : Trace m u e t) : Trace (n + m) s (c + e) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [ZMod.NonsquareSearchMachine.cost_add_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

/-- Fuel exhaustion returns an observable partial prefix configuration. -/
def runFuel : ℕ → Configuration α → Configuration α × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step s with
      | none => (s, 0)
      | some (t, c) => let z := runFuel n t; (z.1, c + z.2)

/-- Continue execution from a trace endpoint. -/
theorem Trace.runFuel_add {k : ℕ} {s t : Configuration α} {c : Cost}
    (h : Trace k s c t) (extra : ℕ) :
    runFuel (k + extra) s = ((runFuel extra t).1, c + (runFuel extra t).2) := by
  induction h with
  | nil s => simp
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih]
      simp only [ZMod.NonsquareSearchMachine.cost_add_assoc]

/-- Completed prefixes are unchanged by additional fuel. -/
theorem Trace.runFuel_done {k : ℕ} {s : Configuration α} {r : Option (List α × ℕ)} {c : Cost}
    (h : Trace k s c (.done r)) (extra : ℕ) : runFuel (k + extra) s = (.done r, c) := by
  have he := h.runFuel_add extra
  have ht : runFuel extra (.done r) = (.done r, (0 : Cost)) := by
    cases extra <;> rfl
  simpa only [ht, ZMod.NonsquareSearchMachine.cost_add_zero] using he

private theorem total_charge (n d o : ℕ) : (charge n d o).total = n + 1 + d + o := by
  simp [charge, ZMod.NonsquareSearchMachine.Cost.total]

private theorem reverse_trace (pre out : List α) (n : ℕ) :
    ∃ k c, Trace k (.reverse pre out n) c (.done (some (pre.reverse ++ out, n))) ∧
      k + c.total ≤ 7 * pre.length + 6 := by
  induction pre generalizing out with
  | nil =>
      refine ⟨1, charge 0 3 1, Trace.cons Step.emit (Trace.nil _), ?_⟩
      simp [total_charge]
  | cons x pre ih =>
      obtain ⟨k, c, ht, hc⟩ := ih (x :: out)
      refine ⟨k + 1, charge 0 5 0 + c, ?_, ?_⟩
      · simpa [List.reverse_cons, List.append_assoc] using Trace.cons Step.reverse ht
      · simp only [ZMod.NonsquareSearchMachine.total_add, total_charge, List.length_cons]
        omega

/-- An available prefix is traversed and restored with its exact processed count. -/
theorem scan_trace (L : ℕ) (xs pre : List α) (n : ℕ) (hL : L ≤ xs.length) :
    ∃ k c, Trace k (.scan L xs pre n) c (.done (some (pre.reverse ++ xs.take L, n + L))) ∧
      k + c.total ≤ 18 * L + 7 * pre.length + 12 := by
  induction L generalizing xs pre n with
  | zero =>
      obtain ⟨k, c, ht, hc⟩ := reverse_trace pre [] n
      refine ⟨k + 1, charge 1 3 0 + c, ?_, ?_⟩
      · simpa using Trace.cons (Step.finish (xs := xs)) ht
      · simp only [ZMod.NonsquareSearchMachine.total_add, total_charge]
        omega
  | succ L ih =>
      cases xs with
      | nil => simp at hL
      | cons x xs =>
          obtain ⟨k, c, ht, hc⟩ := ih xs (x :: pre) (n + 1) (by simpa using hL)
          refine ⟨k + 1, charge 3 6 0 + c, ?_, ?_⟩
          · simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc, Nat.add_comm,
              Nat.add_left_comm] using Trace.cons Step.take ht
          · simp only [ZMod.NonsquareSearchMachine.total_add, total_charge,
              List.length_cons] at hc ⊢
            omega

/-- Uniform fuel and total primitive bound for a prefix of length `L`. -/
def budget (L : ℕ) : ℕ := 18 * L + 12

/-- Same-run success returns the first `L` entries and the actual count `L`. -/
theorem evaluation_runFuel (L : ℕ) (xs : List α) (hL : L ≤ xs.length) :
    ∃ c, runFuel (budget L) (.scan L xs [] 0) = (.done (some (xs.take L, L)), c) ∧
      c.total ≤ budget L := by
  obtain ⟨k, c, ht, hc⟩ := scan_trace L xs [] 0 hL
  simp only [List.reverse_nil, List.nil_append, Nat.zero_add] at ht
  simp only [List.length_nil, Nat.mul_zero, Nat.add_zero] at hc
  change k + c.total ≤ budget L at hc
  have he := ht.runFuel_done (budget L - k)
  rw [show k + (budget L - k) = budget L by omega] at he
  exact ⟨c, he, by omega⟩

/-- A duplicate-free prefix is the ordered image of an explicit finite embedding. -/
theorem prefix_embedding (L : ℕ) (xs : List α) (hn : xs.Nodup) (hL : L ≤ xs.length) :
    ∃ points : Fin L ↪ α, xs.take L = List.ofFn points := by
  have hl : (xs.take L).length = L := List.length_take_of_le hL
  have hp : (xs.take L).Nodup := (List.take_sublist L xs).nodup hn
  suffices ∀ (ys : List α), ys.Nodup → ys.length = L →
      ∃ points : Fin L ↪ α, ys = List.ofFn points from this _ hp hl
  intro ys hy he
  subst L
  exact ⟨⟨_, hy.injective_get⟩, (List.ofFn_get _).symm⟩

end List.PrefixMachine
