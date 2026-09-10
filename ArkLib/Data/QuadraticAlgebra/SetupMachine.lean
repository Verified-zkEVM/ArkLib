/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.QuadraticAlgebra.EnumerationMachine
public import ArkLib.Data.List.PrefixMachine

/-!
# Closed quadratic-field and sample preparation

The runtime enumerates residues, searches for a nonsquare, enumerates coordinate pairs, allocates
quadratic values individually, restores their order, and traverses a sample prefix. The returned
parameter indexes the actual quadratic-value lists; field certification is entirely proof-only.
-/

@[expose] public section

namespace QuadraticAlgebra.SetupMachine

abbrev Cost := ZMod.NonsquareSearchMachine.Cost
abbrev Element (q : ℕ) (a : ZMod q) := QuadraticAlgebra (ZMod q) a 0

/-- Materialized alphabets, samples and their explicit counts for the returned parameter. -/
structure Prepared (q : ℕ) (a : ZMod q) where
  base : List (ZMod q)
  alphabet : List (Element q a)
  samples : List (Element q a)
  baseCount : ℕ
  extensionCount : ℕ
  sampleCount : ℕ
  deriving DecidableEq

/-- The dependent runtime result contains no proofs and no field-instance oracle. -/
abbrev Output (q : ℕ) := (a : ZMod q) × Prepared q a

/-- Lossless embedding of residue/pair enumeration charges into the shared ledger. -/
def embed (c : ZMod.EnumerationMachine.Cost) : Cost :=
  ⟨c.additions, 0, c.equalities, c.natOperations, c.constants, c.control, c.data, c.output⟩

/-- Local natural, constant, data and output operations, plus one control dispatch. -/
def charge (natural constants data output : ℕ) : Cost :=
  ⟨0, 0, 0, natural, constants, 1, data, output⟩

/-- Every delegated instruction pays a parent-state read/write wrapper. -/
def wrapper : Cost := charge 0 0 2 0

/-- Suspended children and explicit quadratic allocation/reversal phases. -/
inductive Configuration (q : ℕ) where
  | base (state : ZMod.EnumerationMachine.Configuration q)
  | search (base : List (ZMod q)) (state : ZMod.NonsquareSearchMachine.Configuration q)
  | pairs (a : ZMod q) (base : List (ZMod q)) (state : EnumerationMachine.Configuration q)
  | decode (a : ZMod q) (base : List (ZMod q)) (remaining : List (ZMod q × ZMod q))
      (saved : List (Element q a)) (count : ℕ)
  | save (a : ZMod q) (base : List (ZMod q)) (remaining : List (ZMod q × ZMod q))
      (value : Element q a) (saved : List (Element q a)) (count : ℕ)
  | reverse (a : ZMod q) (base : List (ZMod q)) (saved output : List (Element q a)) (count : ℕ)
  | prefix (a : ZMod q) (base : List (ZMod q)) (alphabet : List (Element q a)) (count : ℕ)
      (state : List.PrefixMachine.Configuration (Element q a))
  | done (result : Option (Output q))
  deriving DecidableEq

variable {q : ℕ}

/-- Local rules compose actual child instructions and separately charge allocation and emission. -/
inductive Step (L : ℕ) : Configuration q → Cost → Configuration q → Prop where
  | base {s t c} (h : ZMod.EnumerationMachine.step s = some (t, c)) :
      Step L (.base s) (wrapper + embed c) (.base t)
  | based {bs} : Step L (.base (.done bs)) (charge 0 0 3 0) (.search bs .start)
  | search {bs s t c} (h : ZMod.NonsquareSearchMachine.step s = some (t, c)) :
      Step L (.search bs s) (wrapper + c) (.search bs t)
  | noParameter {bs} : Step L (.search bs (.done none)) (charge 0 0 2 1) (.done none)
  | parameter {bs a} : Step L (.search bs (.done (some a))) (charge 0 0 4 0) (.pairs a bs .start)
  | pairs {a bs s t c} (h : EnumerationMachine.step s = some (t, c)) :
      Step L (.pairs a bs s) (wrapper + embed c) (.pairs a bs t)
  | paired {a bs ps} : Step L (.pairs a bs (.done ps)) (charge 0 2 4 0) (.decode a bs ps [] 0)
  | decode {a bs p ps saved n} : Step L (.decode a bs (p :: ps) saved n) (charge 0 0 6 0)
      (.save a bs ps ⟨p.1, p.2⟩ saved n)
  | save {a bs ps z saved n} : Step L (.save a bs ps z saved n) (charge 1 0 5 0)
      (.decode a bs ps (z :: saved) (n + 1))
  | decoded {a bs saved n} : Step L (.decode a bs [] saved n) (charge 0 0 3 0)
      (.reverse a bs saved [] n)
  | reverse {a bs z zs out n} : Step L (.reverse a bs (z :: zs) out n) (charge 0 0 5 0)
      (.reverse a bs zs (z :: out) n)
  | reversed {a bs out n} : Step L (.reverse a bs [] out n) (charge 0 2 5 0)
      (.prefix a bs out n (.scan L out [] 0))
  | prefix {a bs alphabet n s t c} (h : List.PrefixMachine.step s = some (t, c)) :
      Step L (.prefix a bs alphabet n s) (wrapper + c) (.prefix a bs alphabet n t)
  | noSamples {a bs alphabet n} : Step L (.prefix a bs alphabet n (.done none))
      (charge 0 0 2 1) (.done none)
  | prepared {a bs alphabet n samples k} :
      Step L (.prefix a bs alphabet n (.done (some (samples, k)))) (charge 0 0 10 1)
        (.done (some ⟨a, ⟨bs, alphabet, samples, q, n, k⟩⟩))

/-- Closed dispatch never calls bulk conversion, list prefix, field choice or list enumeration. -/
def step (L : ℕ) : Configuration q → Option (Configuration q × Cost)
  | .base (.done bs) => some (.search bs .start, charge 0 0 3 0)
  | .base s => (ZMod.EnumerationMachine.step s).map (fun z => (.base z.1, wrapper + embed z.2))
  | .search _ (.done none) => some (.done none, charge 0 0 2 1)
  | .search bs (.done (some a)) => some (.pairs a bs .start, charge 0 0 4 0)
  | .search bs s => (ZMod.NonsquareSearchMachine.step s).map
      (fun z => (.search bs z.1, wrapper + z.2))
  | .pairs a bs (.done ps) => some (.decode a bs ps [] 0, charge 0 2 4 0)
  | .pairs a bs s => (EnumerationMachine.step s).map
      (fun z => (.pairs a bs z.1, wrapper + embed z.2))
  | .decode a bs (p :: ps) saved n => some (.save a bs ps ⟨p.1, p.2⟩ saved n, charge 0 0 6 0)
  | .decode a bs [] saved n => some (.reverse a bs saved [] n, charge 0 0 3 0)
  | .save a bs ps z saved n => some (.decode a bs ps (z :: saved) (n + 1), charge 1 0 5 0)
  | .reverse a bs (z :: zs) out n => some (.reverse a bs zs (z :: out) n, charge 0 0 5 0)
  | .reverse a bs [] out n => some (.prefix a bs out n (.scan L out [] 0), charge 0 2 5 0)
  | .prefix _ _ _ _ (.done none) => some (.done none, charge 0 0 2 1)
  | .prefix a bs alphabet n (.done (some (samples, k))) =>
      some (.done (some ⟨a, ⟨bs, alphabet, samples, q, n, k⟩⟩), charge 0 0 10 1)
  | .prefix a bs alphabet n s => (List.PrefixMachine.step s).map
      (fun z => (.prefix a bs alphabet n z.1, wrapper + z.2))
  | .done _ => none

/-- Local rules determine the actual next state and cost. -/
theorem Step.step_eq {L : ℕ} {s t : Configuration q} {c : Cost} (h : Step L s c t) :
    step L s = some (t, c) := by
  cases h with
  | base h => rename_i s _ _; cases s <;>
      simp_all only [step, ZMod.EnumerationMachine.step, Option.map_some, reduceCtorEq]
  | search h => rename_i s _ _; cases s <;>
      simp_all only [step, ZMod.NonsquareSearchMachine.step, Option.map_some, reduceCtorEq]
  | pairs h => rename_i s _ _; cases s <;>
      simp_all only [step, EnumerationMachine.step, Option.map_some, reduceCtorEq]
  | «prefix» h => rename_i s _ _; cases s <;>
      simp_all only [step, List.PrefixMachine.step, Option.map_some, reduceCtorEq]
  | _ => rfl

/-- Traces accumulate child, parent, allocation, reversal and emission charges. -/
inductive Trace (L : ℕ) : ℕ → Configuration q → Cost → Configuration q → Prop where
  | nil (s) : Trace L 0 s 0 s
  | cons {n s u t c e} (head : Step L s c u) (tail : Trace L n u e t) :
      Trace L (n + 1) s (c + e) t

/-- Compose exact traces without hidden parent operations. -/
theorem Trace.trans {L n m : ℕ} {s u t : Configuration q} {c e : Cost}
    (h : Trace L n s c u) (h' : Trace L m u e t) : Trace L (n + m) s (c + e) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
      simpa [ZMod.NonsquareSearchMachine.cost_add_assoc, Nat.add_assoc,
        Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

/-- Fuel exhaustion exposes the suspended preparation phase. -/
def runFuel (L : ℕ) : ℕ → Configuration q → Configuration q × Cost
  | 0, s => (s, 0)
  | n + 1, s => match step L s with
      | none => (s, 0)
      | some (t, c) => let z := runFuel L n t; (z.1, c + z.2)

/-- Continue an executable run from a certified trace endpoint. -/
theorem Trace.runFuel_add {L k : ℕ} {s t : Configuration q} {c : Cost}
    (h : Trace L k s c t) (extra : ℕ) :
    runFuel L (k + extra) s = ((runFuel L extra t).1, c + (runFuel L extra t).2) := by
  induction h with
  | nil s => simp
  | cons head tail ih =>
      rw [Nat.add_right_comm, runFuel, head.step_eq]
      dsimp only
      rw [ih]
      simp only [ZMod.NonsquareSearchMachine.cost_add_assoc]

/-- Completed preparation stops charging when additional fuel is supplied. -/
theorem Trace.runFuel_done {L k : ℕ} {s : Configuration q} {r : Option (Output q)} {c : Cost}
    (h : Trace L k s c (.done r)) (extra : ℕ) : runFuel L (k + extra) s = (.done r, c) := by
  have he := h.runFuel_add extra
  have ht : runFuel L extra (.done r) = (.done r, (0 : Cost)) := by cases extra <;> rfl
  simpa only [ht, ZMod.NonsquareSearchMachine.cost_add_zero] using he

end QuadraticAlgebra.SetupMachine
