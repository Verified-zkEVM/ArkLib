/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.SharedListPreparedRead

/-!
# Literal uncons of a represented shared list

Every pointer bit is popped onto a saved tape and inspected, then physically restored. A finite
Boolean flag selects empty versus the prepared live-cell reader. The modulus-width reference,
original pointer and RAM are preserved; no pointer equality oracle or free word copy runs in
`step`. Both branches use the same sixteen tape positions as the prepared reader.

The correctness input is a represented list, not a separately supplied live cell. The same
bounded run returns either empty or its exact first word and a pointer representing the rest.
For unrepresented nonzero pointers the actual reader may reject or return arbitrary heap data;
no successful list semantics are asserted. The empty branch depends only on pointer bits.
-/

@[expose] public section

namespace Computation.SharedListUncons

open AddressedBits (Memory)
open SharedListHeap (RepList nilPointer)

inductive Control where
  | scan (reference source saved : List Bool) (seen : Bool)
  | restore (reference source pointer : List Bool) (seen : Bool)
  | empty (reference pointer : List Bool)
  | reading (child : SharedListPreparedRead.Control)
  deriving DecidableEq, Repr

structure Configuration where
  memory : Memory
  control : Control
  deriving DecidableEq, Repr

/-- This dispatch inspects only the finite flag accumulated by the literal scan. -/
def dispatch (reference pointer : List Bool) (seen : Bool) : Control :=
  if seen then .reading (.building (.copyTail reference pointer [] []))
  else .empty reference pointer

def step : Configuration → Option Configuration
  | ⟨mem, .scan reference (b :: rest) saved seen⟩ =>
      some ⟨mem, .scan reference rest (b :: saved) (seen || b)⟩
  | ⟨mem, .scan reference [] saved seen⟩ =>
      some ⟨mem, .restore reference saved [] seen⟩
  | ⟨mem, .restore reference (b :: rest) pointer seen⟩ =>
      some ⟨mem, .restore reference rest (b :: pointer) seen⟩
  | ⟨mem, .restore reference [] pointer seen⟩ =>
      some ⟨mem, dispatch reference pointer seen⟩
  | ⟨_, .empty _ _⟩ => none
  | ⟨mem, .reading child⟩ =>
      match SharedListPreparedRead.step ⟨mem, child⟩ with
      | some next => some ⟨next.memory, .reading next.control⟩
      | none => none

/-- Scan uses pointer zero, saved one and retained reference fourteen; the reader uses
these exact positions after restoration. Every other tape is blank at the handoff. -/
def tapes : Control → Fin 16 → List Bool
  | .scan reference source saved _ =>
      ![source, saved, [], [], [], [], [], [], [], [], [], [], [], [], reference, []]
  | .restore reference source pointer _ =>
      ![pointer, source, [], [], [], [], [], [], [], [], [], [], [], [], reference, []]
  | .empty reference pointer =>
      ![pointer, [], [], [], [], [], [], [], [], [], [], [], [], [], reference, []]
  | .reading child => SharedListPreparedRead.tapes child

theorem dispatch_tapes (reference pointer : List Bool) (seen : Bool) :
    tapes (.restore reference [] pointer seen) = tapes (dispatch reference pointer seen) := by
  cases seen <;> rfl

private theorem scan_bank {p s p' s' : List Bool} (reference : List Bool)
    (hp : BitLocalActions.CellStep p p') (hs : BitLocalActions.CellStep s s') :
    BitLocalActions.BankStep
      ![p, s, [], [], [], [], [], [], [], [], [], [], [], [], reference, []]
      ![p', s', [], [], [], [], [], [], [], [], [], [], [], [], reference, []] := by
  intro i
  fin_cases i
  · exact hp
  · exact hs
  all_goals exact .keep _

/-- All sixteen physical tapes obey the same local-bit invariant through both branches. -/
theorem step_local {s t : Configuration} (h : step s = some t) :
    BitLocalActions.BankStep (tapes s.control) (tapes t.control) := by
  rcases s with ⟨mem, control⟩
  cases control with
  | scan reference source saved seen =>
      cases source with
      | nil => cases h; exact scan_bank reference (.keep _) (.keep _)
      | cons b rest => cases h; exact scan_bank reference (.pop _ _) (.push _ _)
  | restore reference source pointer seen =>
      cases source with
      | nil =>
          cases h
          rw [dispatch_tapes]
          intro i
          exact .keep _
      | cons b rest => cases h; exact scan_bank reference (.push _ _) (.pop _ _)
  | empty reference pointer => cases h
  | reading child =>
      cases hs : SharedListPreparedRead.step ⟨mem, child⟩ with
      | some next =>
          simp only [step, hs, Option.some.injEq] at h
          subst t
          exact SharedListPreparedRead.step_local hs
      | none => simp only [step, hs] at h; cases h

inductive Trace : ℕ → Configuration → Configuration → Prop where
  | nil (s) : Trace 0 s s
  | cons {n s u t} (head : step s = some u) (tail : Trace n u t) : Trace (n + 1) s t

def runFuel : ℕ → Configuration → Configuration
  | 0, s => s
  | n + 1, s => match step s with
      | none => s
      | some t => runFuel n t

theorem Trace.append {n m : ℕ} {s u t : Configuration}
    (h : Trace n s u) (h' : Trace m u t) : Trace (n + m) s t := by
  induction h with
  | nil => simpa using h'
  | cons head _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

theorem Trace.runFuel_eq {n : ℕ} {s t : Configuration} (h : Trace n s t) : runFuel n s = t := by
  induction h with
  | nil => rfl
  | cons head _ ih => simpa [runFuel, head] using ih

/-- Proof-side characterization of the finite flag; this recursion is not an instruction. -/
def nonzero : List Bool → Bool
  | [] => false
  | b :: bs => b || nonzero bs

theorem nonzero_false_iff (p : List Bool) :
    nonzero p = false ↔ p = List.replicate p.length false := by
  induction p with
  | nil => simp [nonzero]
  | cons b bs ih => cases b <;> simp [nonzero, List.replicate_succ, ih]

theorem scan_trace (mem : Memory) (reference source saved : List Bool) (seen : Bool) :
    Trace (source.length + 1) ⟨mem, .scan reference source saved seen⟩
      ⟨mem, .restore reference (source.reverse ++ saved) [] (seen || nonzero source)⟩ := by
  induction source generalizing saved seen with
  | nil =>
      simpa [nonzero] using
        Trace.cons (s := ⟨mem, .scan reference [] saved seen⟩) (by rfl) (.nil _)
  | cons b bs ih =>
      simpa [nonzero, List.reverse_cons, List.append_assoc, Bool.or_assoc] using
        Trace.cons (by rfl) (ih (b :: saved) (seen || b))

theorem restore_trace (mem : Memory) (reference source pointer : List Bool) (seen : Bool) :
    Trace (source.length + 1) ⟨mem, .restore reference source pointer seen⟩
      ⟨mem, dispatch reference (source.reverse ++ pointer) seen⟩ := by
  induction source generalizing pointer with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
      simpa [List.reverse_cons, List.append_assoc] using
        Trace.cons (by rfl) (ih (b :: pointer))

/-- Nil scanning and exact pointer restoration take two transitions per bit plus two. -/
theorem dispatch_trace (mem : Memory) (reference p : List Bool) :
    Trace (2 * p.length + 2) ⟨mem, .scan reference p [] false⟩
      ⟨mem, dispatch reference p (nonzero p)⟩ := by
  have hs := scan_trace mem reference p [] false
  have hr := restore_trace mem reference p.reverse [] (nonzero p)
  simp only [Bool.false_or, List.append_nil] at hs
  simp only [List.reverse_reverse, List.append_nil] at hr
  convert hs.append hr using 1
  simp only [List.length_reverse]
  omega

theorem lift_read {n : ℕ} {s t : SharedListPreparedRead.Configuration}
    (h : SharedListPreparedRead.Trace n s t) :
    Trace n ⟨s.memory, .reading s.control⟩ ⟨t.memory, .reading t.control⟩ := by
  induction h with
  | nil => exact .nil _
  | cons head _ ih => exact .cons (by simp only [step, head]) ih

/-- The maximum count for either branch, including full pointer inspection and restoration. -/
def bound (w h : ℕ) : ℕ := 2 * w + 2 + SharedListPreparedRead.steps w h

/-- A represented list determines the branch and output of one actual bounded execution.
The nonempty case derives its cell internally and returns a representation of the exact tail. -/
theorem uncons_execution {mem : Memory} {w h : ℕ} {p : List Bool} {xs : List (List Bool)}
    (hr : RepList mem w h p xs) (reference : List Bool) (href : reference.length = h) :
    ∃ n ≤ bound w h, ∃ final : Configuration,
      Trace n ⟨mem, .scan reference p [] false⟩ final ∧
      runFuel n ⟨mem, .scan reference p [] false⟩ = final ∧
      final.memory = mem ∧
      (∀ old ys, RepList mem w h old ys → RepList final.memory w h old ys) ∧
      match xs with
      | [] => n = 2 * w + 2 ∧ final.control = .empty reference p
      | head :: rest => n = bound w h ∧ ∃ tail,
          final.control = .reading (.reading reference
            (.done p (List.replicate (1 + h + w) true) head tail)) ∧
          RepList final.memory w h tail rest := by
  have hd := dispatch_trace mem reference p
  cases hr with
  | nil =>
      have hz : nonzero (nilPointer w) = false :=
        (nonzero_false_iff _).mpr (by simp [nilPointer])
      simp only [hz, dispatch, Bool.false_eq_true, ↓reduceIte] at hd
      have hw : (nilPointer w).length = w := by simp [nilPointer]
      rw [hw] at hd
      exact ⟨_, by simp [bound], _, hd, hd.runFuel_eq, rfl, fun _ _ h ↦ h, rfl, rfl⟩
  | @cons p head tail rest cell hrest =>
      have hz : nonzero p = true := by
        cases he : nonzero p with
        | false =>
            have hp := (nonzero_false_iff p).mp he
            rw [cell.pointer_width] at hp
            exact (cell.not_nil hp).elim
        | true => rfl
      simp only [hz, dispatch, ↓reduceIte] at hd
      have hc := lift_read (SharedListPreparedRead.read_trace cell reference href)
      have ht := hd.append hc
      rw [cell.pointer_width] at ht
      exact ⟨_, le_rfl, _, ht, ht.runFuel_eq, rfl, fun _ _ h ↦ h, rfl, tail, rfl, hrest⟩

end Computation.SharedListUncons
