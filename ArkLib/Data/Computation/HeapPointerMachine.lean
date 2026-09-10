/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.BitLocalActions

/-!
# Literal fixed-width pointer increment

The four-tape controller preserves every bit position, including high zero padding. It retains
the original pointer and produces the incremented word plus a Boolean overflow flag. Carry,
copying and restoration use single-bit local actions. No successor decodes, re-encodes, trims,
or enumerates addresses. Pointer words remain bit strings used as physical address prefixes;
proof-side numerical labels are supplied separately and are not architectural addresses.

This is the next-pointer operation, not a complete allocator. Freshness, heap writes, and the
same-bank composition with a writer are separate contracts. RAM is unchanged by this controller.
-/

@[expose] public section

namespace Computation.HeapPointerMachine

/-- Finite carry control and four fixed local tapes. -/
inductive Control where
  | scan (remaining originalSaved resultSaved : List Bool) (carry : Bool)
  | restoreOld (source original resultSaved : List Bool) (overflow : Bool)
  | restoreNext (original source next : List Bool) (overflow : Bool)
  | done (original next : List Bool) (overflow : Bool)
  deriving DecidableEq, Repr

/-- A literal half-adder scan followed by two bit-by-bit restorations. -/
def step : Control → Option Control
  | .scan (b :: bs) original result carry =>
      some (.scan bs (b :: original) ((b != carry) :: result) (b && carry))
  | .scan [] original result carry => some (.restoreOld original [] result carry)
  | .restoreOld (b :: bs) original result overflow =>
      some (.restoreOld bs (b :: original) result overflow)
  | .restoreOld [] original result overflow => some (.restoreNext original result [] overflow)
  | .restoreNext original (b :: bs) next overflow =>
      some (.restoreNext original bs (b :: next) overflow)
  | .restoreNext original [] next overflow => some (.done original next overflow)
  | .done _ _ _ => none

/-- Semantic fixed-width increment, with final carry exposed rather than silently discarded. -/
def increment : List Bool → Bool → List Bool × Bool
  | [], carry => ([], carry)
  | b :: bs, carry =>
      let r := increment bs (b && carry)
      ((b != carry) :: r.1, r.2)

/-- Every input position contributes exactly one output position, also on overflow. -/
theorem increment_length (bits : List Bool) (carry : Bool) :
    (increment bits carry).1.length = bits.length := by
  induction bits generalizing carry with
  | nil => rfl
  | cons b bs ih => simp only [increment, List.length_cons, ih]

/-- Exact traces of the actual local bit successors. -/
inductive Trace : ℕ → Control → Control → Prop where
  | nil (s) : Trace 0 s s
  | cons {n s u t} (head : step s = some u) (tail : Trace n u t) : Trace (n + 1) s t

/-- An external observer; the controller has no numeric fuel or width register. -/
def runFuel : ℕ → Control → Control
  | 0, s => s
  | n + 1, s => match step s with
      | none => s
      | some t => runFuel n t

/-- Trace composition retains the precise intermediate tape state. -/
theorem Trace.append {n m : ℕ} {s u t : Control} (h : Trace n s u) (h' : Trace m u t) :
    Trace (n + m) s t := by
  induction h with
  | nil => simpa using h'
  | cons head _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

/-- Exact observation fuel reaches the same final original/next tapes and overflow flag. -/
theorem Trace.runFuel_eq {n : ℕ} {s t : Control} (h : Trace n s t) : runFuel n s = t := by
  induction h with
  | nil => rfl
  | cons head _ ih => simpa [runFuel, head] using ih

/-- The carry scan physically saves original and result bits in reverse order. -/
theorem scan_trace (bits : List Bool) (carry : Bool) (original result : List Bool) :
    Trace (bits.length + 1) (.scan bits original result carry)
      (.restoreOld (bits.reverse ++ original) []
        ((increment bits carry).1.reverse ++ result) (increment bits carry).2) := by
  induction bits generalizing carry original result with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
      simpa [increment, List.reverse_cons, List.append_assoc, Nat.add_assoc] using
        Trace.cons (by rfl) (ih (b && carry) (b :: original) ((b != carry) :: result))

/-- Restore the original pointer before restoring the incremented result. -/
theorem restoreOld_trace (source original result : List Bool) (overflow : Bool) :
    Trace (source.length + 1) (.restoreOld source original result overflow)
      (.restoreNext (source.reverse ++ original) result [] overflow) := by
  induction source generalizing original with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
        Trace.cons (by rfl) (ih (b :: original))

/-- Restore every result position without trimming padding or losing the overflow flag. -/
theorem restoreNext_trace (original source next : List Bool) (overflow : Bool) :
    Trace (source.length + 1) (.restoreNext original source next overflow)
      (.done original (source.reverse ++ next) overflow) := by
  induction source generalizing next with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
      simpa [List.reverse_cons, List.append_assoc, Nat.add_assoc] using
        Trace.cons (by rfl) (ih (b :: next))

/-- Increment by one in exactly three traversals and three phase transitions. -/
theorem increment_trace (bits : List Bool) :
    Trace (3 * bits.length + 3) (.scan bits [] [] true)
      (.done bits (increment bits true).1 (increment bits true).2) := by
  have hs := scan_trace bits true [] []
  have ho := restoreOld_trace bits.reverse []
    (increment bits true).1.reverse (increment bits true).2
  have hn := restoreNext_trace bits (increment bits true).1.reverse [] (increment bits true).2
  simp only [List.append_nil] at hs
  simp only [List.reverse_reverse, List.append_nil] at ho hn
  convert (hs.append ho).append hn using 1
  simp only [List.length_reverse, increment_length]
  omega

/-- The actual bounded observer retains the original word and returns the fixed-width increment. -/
theorem increment_runFuel (bits : List Bool) :
    runFuel (3 * bits.length + 3) (.scan bits [] [] true) =
      .done bits (increment bits true).1 (increment bits true).2 :=
  (increment_trace bits).runFuel_eq

/-- Fixed tape assignments are unchanged across all three phases. -/
def tapes : Control → BitLocalActions.Tapes
  | .scan remaining original result _ => { left := remaining, right := original, saved := result }
  | .restoreOld source original result _ => { left := original, right := source, saved := result }
  | .restoreNext original source next _ => { left := original, saved := source, output := next }
  | .done original next _ => { left := original, output := next }

/-- Each literal successor uses only a single pop/push/keep on each of four fixed bit tapes. -/
theorem step_local {s t : Control} (h : step s = some t) :
    BitLocalActions.Step (tapes s) (tapes t) := by
  cases s with
  | scan remaining original result carry =>
      cases remaining <;> cases h
      · exact ⟨.keep _, .keep _, .keep _, .keep _⟩
      · exact ⟨.pop _ _, .push _ _, .push _ _, .keep _⟩
  | restoreOld source original result overflow =>
      cases source <;> cases h
      · exact ⟨.keep _, .keep _, .keep _, .keep _⟩
      · exact ⟨.push _ _, .pop _ _, .keep _ , .keep _⟩
  | restoreNext original source next overflow =>
      cases source <;> cases h
      · exact ⟨.keep _, .keep _, .keep _, .keep _⟩
      · exact ⟨.keep _, .keep _, .pop _ _, .push _ _⟩
  | done original next overflow => cases h

/-- The same local controller on RAM retains the identical memory in every successor. -/
def ramStep (s : AddressedBits.Memory × Control) : Option (AddressedBits.Memory × Control) :=
  (step s.2).map fun t ↦ (s.1, t)

/-- Literal RAM-state observer of the same pointer controller. -/
def ramRunFuel : ℕ → AddressedBits.Memory × Control → AddressedBits.Memory × Control
  | 0, s => s
  | n + 1, s => match ramStep s with
      | none => s
      | some t => ramRunFuel n t

/-- Every observed local execution preserves the entire original RAM. -/
theorem ramRunFuel_eq (mem : AddressedBits.Memory) (n : ℕ) (s : Control) :
    ramRunFuel n (mem, s) = (mem, runFuel n s) := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => cases hs : step s <;> simp [ramRunFuel, ramStep, runFuel, hs, ih]

end Computation.HeapPointerMachine
