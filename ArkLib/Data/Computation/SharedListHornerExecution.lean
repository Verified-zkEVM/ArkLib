/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.SharedListHornerMachine

/-!
# Same-run correctness of the physical shared-list Horner loop

Every iteration includes actual uncons, cleanup of the old pointer/index, physical tail movement,
multiplication, addition and all handoffs. The coefficient heap is unchanged. The fold below
specifies the output of this one physical run; no abstract list or arithmetic callback executes
inside the controller. The entry accumulator and evaluation point are materialized reduced words.
-/

@[expose] public section

namespace Computation.SharedListHornerMachine

open AddressedBits (Memory)
open BinaryWordMachine (Word value)
open SharedListHeap (RepList nilPointer)

theorem clearPointer_trace (mem : Memory) (q point acc coeff pointer index tail : Word) :
    Trace (pointer.length + 1) ⟨mem, .clearPointer q point acc coeff pointer index tail⟩
      ⟨mem, .clearIndex q point acc coeff index tail⟩ := by
  induction pointer with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih => exact .cons rfl ih

theorem clearIndex_trace (mem : Memory) (q point acc coeff index tail : Word) :
    Trace (index.length + 1) ⟨mem, .clearIndex q point acc coeff index tail⟩
      ⟨mem, .reverseTail q point acc coeff tail []⟩ := by
  induction index with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih => exact .cons rfl ih

theorem reverseTail_trace (mem : Memory) (q point acc coeff source saved : Word) :
    Trace (source.length + 1) ⟨mem, .reverseTail q point acc coeff source saved⟩
      ⟨mem, .restorePointer q point acc coeff (source.reverse ++ saved) []⟩ := by
  induction source generalizing saved with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
      simpa [List.reverse_cons, List.append_assoc] using
        Trace.cons (by rfl) (ih (b :: saved))

theorem restorePointer_trace (mem : Memory) (q point acc coeff source pointer : Word) :
    Trace (source.length + 1) ⟨mem, .restorePointer q point acc coeff source pointer⟩
      ⟨mem, .multiplying coeff (source.reverse ++ pointer)
        (.normalizing q point (.startAdd acc [] false))⟩ := by
  induction source generalizing pointer with
  | nil => exact .cons rfl (.nil _)
  | cons b bs ih =>
      simpa [List.reverse_cons, List.append_assoc] using
        Trace.cons (by rfl) (ih (b :: pointer))

/-- The old pointer and index are cleared; the actual tail is restored in pointer position. -/
theorem cleanup_trace (mem : Memory) (q point acc coeff pointer index tail : Word) :
    Trace (pointer.length + index.length + 2 * tail.length + 4)
      ⟨mem, .clearPointer q point acc coeff pointer index tail⟩
      ⟨mem, .multiplying coeff tail (.normalizing q point (.startAdd acc [] false))⟩ := by
  have hp := clearPointer_trace mem q point acc coeff pointer index tail
  have hi := clearIndex_trace mem q point acc coeff index tail
  have ht := reverseTail_trace mem q point acc coeff tail []
  have hr := restorePointer_trace mem q point acc coeff tail.reverse []
  simp only [List.append_nil] at ht
  simp only [List.reverse_reverse, List.append_nil] at hr
  convert ((hp.append hi).append ht).append hr using 1
  simp only [List.length_reverse]
  omega

/-- A bound for all operations and handoffs of one nonempty loop iteration. -/
def iterationBound (w : ℕ) (q : Word) : ℕ :=
  SharedListUncons.bound w q.length + 4 * w + q.length + 8 +
    (value q * (24 * q.length + 48) + 6 * q.length + 16) + (14 * q.length + 33)

/-- One actual nonempty iteration obtains its coefficient from a represented list, updates the
accumulator, and returns to the loop header with the exact represented tail and unchanged RAM. -/
theorem iteration {mem : Memory} {w : ℕ} {q point acc p coeff : Word} {rest : List Word}
    (hr : RepList mem w q.length p (coeff :: rest))
    (hacc : value acc < value q) (hpoint : value point < value q)
    (hcoeff : value coeff < value q) (hwacc : acc.length = q.length)
    (hwpoint : point.length = q.length) :
    ∃ n ≤ iterationBound w q, ∃ out tail,
      Trace n ⟨mem, .taking acc point (.scan q p [] false)⟩
        ⟨mem, .taking out point (.scan q tail [] false)⟩ ∧
      out.length = q.length ∧ value out < value q ∧
      (value out : ZMod (value q)) =
        (value acc : ZMod (value q)) * (value point : ZMod (value q)) +
          (value coeff : ZMod (value q)) ∧
      RepList mem w q.length tail rest := by
  obtain ⟨nu, _hnu, final, hu, _hru, hm, _hframe, hnu, tail, hc, hrest⟩ :=
    SharedListUncons.uncons_execution hr q rfl
  have hf : final = ⟨mem, .reading (.reading q
      (.done p (List.replicate (1 + q.length + w) true) coeff tail))⟩ := by
    cases final
    simp_all
  rw [hf, hnu] at hu
  rw [hm] at hrest
  have htake : Trace 1
      ⟨mem, .taking acc point (.reading (.reading q
        (.done p (List.replicate (1 + q.length + w) true) coeff tail)))⟩
      ⟨mem, .clearPointer q point acc coeff p
        (List.replicate (1 + q.length + w) true) tail⟩ := .cons rfl (.nil _)
  have hclean := cleanup_trace mem q point acc coeff p
    (List.replicate (1 + q.length + w) true) tail
  have hwcoeff := hr.head_width coeff (by simp)
  obtain ⟨nm, hnm, product, hmul, _hrm, hwm, hvm, hrm⟩ :=
    PaddedMul.multiply_fixed_width q acc point hacc hpoint hwacc hwpoint
  have hmh : Trace 1
      ⟨mem, .multiplying coeff tail (.padding point (.padding q (.done product)))⟩
      ⟨mem, .adding point tail (.adding (.start q product coeff))⟩ := .cons rfl (.nil _)
  obtain ⟨na, hna, out, hadd, _hra, hwa, hva, hra⟩ :=
    PaddedModAdd.add_fixed_width q product coeff hrm hcoeff hwm hwcoeff
  have hah : Trace 1
      ⟨mem, .adding point tail (.padding (.padding q (.done out)))⟩
      ⟨mem, .taking out point (.scan q tail [] false)⟩ := .cons rfl (.nil _)
  have hall := ((((((lift_uncons acc point hu).append htake).append hclean).append
    (lift_mul mem coeff tail hmul)).append hmh).append (lift_add mem point tail hadd)).append hah
  refine ⟨_, ?_, out, tail, hall, hwa, hra, ?_, hrest⟩
  · have hp := hr.pointer_width
    have ht := hrest.pointer_width
    simp only [List.length_replicate, hp, ht]
    unfold iterationBound
    omega
  · rw [hva, hvm]

/-- The final nil test and emission are charged once, after all nonempty iterations. -/
def totalBound (w : ℕ) (q : Word) (length : ℕ) : ℕ :=
  length * iterationBound w q + 2 * w + 3

/-- One physical loop run realizes the Horner fold over the words in the represented heap list. -/
theorem loop_execution {mem : Memory} {w : ℕ} {q point acc p : Word} {xs : List Word}
    (hr : RepList mem w q.length p xs)
    (hacc : value acc < value q) (hpoint : value point < value q)
    (hcoeff : ∀ c ∈ xs, value c < value q)
    (hwacc : acc.length = q.length) (hwpoint : point.length = q.length) :
    ∃ n ≤ totalBound w q xs.length, ∃ out,
      Trace n ⟨mem, .taking acc point (.scan q p [] false)⟩
        ⟨mem, .done q point (nilPointer w) out⟩ ∧
      runFuel n ⟨mem, .taking acc point (.scan q p [] false)⟩ =
        ⟨mem, .done q point (nilPointer w) out⟩ ∧
      out.length = q.length ∧ value out < value q ∧
      (value out : ZMod (value q)) =
        (xs.map (fun c ↦ (value c : ZMod (value q)))).foldl
          (fun a c ↦ a * (value point : ZMod (value q)) + c)
          (value acc : ZMod (value q)) := by
  induction xs generalizing acc p with
  | nil =>
      cases hr
      have hu := SharedListUncons.dispatch_trace mem q (nilPointer w)
      have hz : SharedListUncons.nonzero (nilPointer w) = false :=
        (SharedListUncons.nonzero_false_iff _).mpr (by simp [nilPointer])
      simp only [hz, SharedListUncons.dispatch, Bool.false_eq_true, ↓reduceIte] at hu
      have he : Trace 1 ⟨mem, .taking acc point (.empty q (nilPointer w))⟩
          ⟨mem, .done q point (nilPointer w) acc⟩ := .cons rfl (.nil _)
      have ht := (lift_uncons acc point hu).append he
      exact ⟨_, by simp [totalBound, nilPointer], acc, ht, ht.runFuel_eq,
        hwacc, hacc, rfl⟩
  | cons coeff rest ih =>
      obtain ⟨ni, hni, next, tail, hi, hwn, hrn, hvn, hrest⟩ :=
        iteration hr hacc hpoint (hcoeff coeff (by simp)) hwacc hwpoint
      obtain ⟨nr, hnr, out, ht, _hrt, hwo, hro, hvo⟩ :=
        ih hrest hrn (fun c hc ↦ hcoeff c (by simp [hc])) hwn
      have hall := hi.append ht
      refine ⟨_, ?_, out, hall, hall.runFuel_eq, hwo, hro, ?_⟩
      · simp only [totalBound, List.length_cons, Nat.add_mul, Nat.one_mul] at hnr ⊢
        omega
      · simpa only [List.map_cons, List.foldl_cons, hvn] using hvo

end Computation.SharedListHornerMachine
