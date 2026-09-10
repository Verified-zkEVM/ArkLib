/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Local.Translate
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.Range
/-!
# Charged local U expansion and contact projection

Structured recursive instructions expand each U factor into E and the d signed visible-jet
summands. Every coordinate increment, branch allocation, append, predicate test and scalar sign
operation is explicit. Each recursion clause has an upper charge of 32 primitive units, plus the
charges of its executed recursive calls. This includes call/return control, natural operations,
scalar negation/addition, pointer/cell accesses and allocations. Shared tails are immutable.
No list map/filter/append/modify or polynomial primitive is used by the executable definitions.
Garbage collection and arithmetic bit costs are outside this unit-operation model.

Final dense terms have layout [T,E,Y1,...,Yd]. Duplicate exponent vectors and zero coefficients
are retained. Full-vector equality and duplicate-aware lookup are separately charged.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.LocalColumnRewriteMachine

variable {F : Type*}

/-- Structured materialized exponent vector, before allocating its two-coordinate prefix. -/
structure Term (F : Type*) where
  coefficient : F
  t : ℕ
  e : ℕ
  jets : List ℕ
  deriving DecidableEq, Repr

/-- Explicit cell-copy append, including its final pointer return. -/
def appendCells {α : Type*} : List α → List α → List α × ℕ
  | [], ys => (ys, 32)
  | x :: xs, ys =>
      let r := appendCells xs ys
      (x :: r.1, 32 + r.2)

theorem appendCells_correct {α : Type*} (xs ys : List α) :
    appendCells xs ys = (xs ++ ys, 32 * (xs.length + 1)) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [appendCells, ih]; omega

/-- Traverse to one coordinate, increment it, and rebuild exactly the traversed prefix. -/
def bump : ℕ → List ℕ → List ℕ × ℕ
  | _, [] => ([], 32)
  | 0, x :: xs => ((x + 1) :: xs, 32)
  | j + 1, x :: xs =>
      let r := bump j xs
      (x :: r.1, 32 + r.2)

theorem bump_correct (j : ℕ) (xs : List ℕ) :
    (bump j xs).1 = xs.modify j (· + 1) ∧ (bump j xs).2 ≤ 32 * (j + 1) := by
  induction xs generalizing j with
  | nil => simp [bump]
  | cons x xs ih =>
    cases j with
    | zero => simp [bump, List.modify]
    | succ j =>
      have h := ih j
      simp only [bump, List.modify_cons]
      constructor
      · simp [List.modify, h.1]
      · omega

variable [CommRing F]

/-- Negation implements the alternating sign, with no scalar power or division. -/
def signed (j : ℕ) (c : F) : F := if j % 2 = 0 then c else -c

/-- The first n visible branches, emitted in descending variable order. -/
def jetBranches : ℕ → Term F → List (Term F) × ℕ
  | 0, _ => ([], 32)
  | n + 1, term =>
      let changed := bump n term.jets
      let tail := jetBranches n term
      (⟨signed n term.coefficient, term.t + n, term.e, changed.1⟩ :: tail.1,
        32 + changed.2 + tail.2)

/-- One U multiplication: E plus all d visible summands. -/
def multiplyU (d : ℕ) (term : Term F) : List (Term F) × ℕ :=
  let branches := jetBranches d term
  (⟨term.coefficient, term.t, term.e + 1, term.jets⟩ :: branches.1, 32 + branches.2)

/-- Expand all supplied terms once; every concatenated outer cell is charged. -/
def round (d : ℕ) : List (Term F) → List (Term F) × ℕ
  | [] => ([], 32)
  | t :: ts =>
      let head := multiplyU d t
      let tail := round d ts
      let joined := appendCells head.1 tail.1
      (joined.1, 32 + head.2 + tail.2 + joined.2)

/-- Iterate the expansion, retaining duplicate monomials. -/
def power (d : ℕ) : ℕ → List (Term F) → List (Term F) × ℕ
  | 0, ts => (ts, 32)
  | n + 1, ts =>
      let next := round d ts
      let rest := power d n next.1
      (rest.1, 32 + next.2 + rest.2)

/-- The final contact cutoff, not merely the preliminary T cutoff. -/
def project (d m : ℕ) : List (Term F) → List (Term F) × ℕ
  | [] => ([], 32)
  | t :: ts =>
      let rest := project d m ts
      (if t.t + d * t.e < m then t :: rest.1 else rest.1, 32 + rest.2)

/-- Expand and project every translated column term using the shared higher-jet vector. -/
def rewrite (d m : ℕ) (higher : List ℕ) :
    List (LocalColumnTranslationMachine.Term F) → List (Term F) × ℕ
  | [] => ([], 32)
  | t :: ts =>
      let expanded := power d t.u [⟨t.coefficient, t.t, 0, higher⟩]
      let retained := project d m expanded.1
      let rest := rewrite d m higher ts
      let joined := appendCells retained.1 rest.1
      (joined.1, 32 + expanded.2 + retained.2 + rest.2 + joined.2)

/-- Fixed dense layout, ready for distinct-index normalization by the matrix/sparse consumer. -/
abbrev DenseTerm (F : Type*) := F × List ℕ

/-- Allocate the T/E prefixes and output list cells, sharing the existing visible-jet tails. -/
def densify : List (Term F) → List (DenseTerm F) × ℕ
  | [] => ([], 32)
  | t :: ts =>
      let rest := densify ts
      ((t.coefficient, t.t :: t.e :: t.jets) :: rest.1, 32 + rest.2)

/-- Complete rewrite with an explicitly materialized dense result. -/
def execute (d m : ℕ) (higher : List ℕ) (ts : List (LocalColumnTranslationMachine.Term F)) :
    List (DenseTerm F) × ℕ :=
  let r := rewrite d m higher ts
  let out := densify r.1
  (out.1, 32 + r.2 + out.2)

/-- Equality traverses the actual dense coordinate lists, including the length boundary. -/
def equal : List ℕ → List ℕ → Bool × ℕ
  | [], [] => (true, 32)
  | [], _ :: _ => (false, 32)
  | _ :: _, [] => (false, 32)
  | x :: xs, y :: ys =>
      if x = y then let r := equal xs ys; (r.1, 32 + r.2) else (false, 32)

/-- Coefficient lookup sums every matching dense term; duplicate entries need not be merged. -/
def lookup (target : List ℕ) : List (DenseTerm F) → F × ℕ
  | [] => (0, 32)
  | (c, vector) :: ts =>
      let same := equal vector target
      let rest := lookup target ts
      (if same.1 then c + rest.1 else rest.1, 32 + same.2 + rest.2)

/-- Proof-only single-branch specification. -/
def jetBranch (n : ℕ) (t : Term F) : Term F :=
  ⟨signed n t.coefficient, t.t + n, t.e, t.jets.modify n (· + 1)⟩

/-- Branches are enumerated without a free range/map primitive. -/
theorem jetBranches_result (n : ℕ) (t : Term F) :
    (jetBranches n t).1 = (List.ofFn fun j : Fin n => jetBranch j.val t).reverse := by
  induction n with
  | zero => simp [jetBranches]
  | succ n ih =>
    simp only [jetBranches, (bump_correct n t.jets).1, ih, List.ofFn_succ_last,
      List.reverse_append, List.reverse_singleton, List.singleton_append]
    rfl

theorem jetBranches_length (n : ℕ) (t : Term F) : (jetBranches n t).1.length = n := by
  rw [jetBranches_result]
  simp

theorem jetBranches_cost (n : ℕ) (t : Term F) :
    (jetBranches n t).2 ≤ 64 * (n + 1) ^ 2 := by
  induction n with
  | zero => simp [jetBranches]
  | succ n ih =>
    have hb := (bump_correct n t.jets).2
    simp only [jetBranches]
    nlinarith

theorem multiplyU_length (d : ℕ) (t : Term F) : (multiplyU d t).1.length = d + 1 := by
  simp [multiplyU, jetBranches_length]

theorem multiplyU_cost (d : ℕ) (t : Term F) :
    (multiplyU d t).2 ≤ 96 * (d + 1) ^ 2 := by
  have h := jetBranches_cost d t
  simp only [multiplyU]
  nlinarith [Nat.one_le_pow 2 (d + 1) (by omega)]

theorem round_length (d : ℕ) (ts : List (Term F)) :
    (round d ts).1.length = (d + 1) * ts.length := by
  induction ts with
  | nil => simp [round]
  | cons t ts ih => simp [round, appendCells_correct, multiplyU_length, ih]; ring

/-- One expansion round is linear in its supplied list size, with a quadratic order factor. -/
theorem round_cost (d : ℕ) (ts : List (Term F)) :
    (round d ts).2 ≤ 256 * (d + 2) ^ 2 * (ts.length + 1) := by
  induction ts with
  | nil => simp only [round, List.length_nil]; nlinarith [Nat.one_le_pow 2 (d + 2) (by omega)]
  | cons t ts ih =>
    have hm := multiplyU_cost d t
    simp only [round, appendCells_correct, multiplyU_length, List.length_cons]
    nlinarith

theorem power_length (d n : ℕ) (ts : List (Term F)) :
    (power d n ts).1.length = (d + 1) ^ n * ts.length := by
  induction n generalizing ts with
  | zero => simp [power]
  | succ n ih => simp [power, ih, round_length, pow_succ, Nat.mul_assoc]

/-- Exponential dependence is confined to the order and U exponent. -/
theorem power_cost (d n : ℕ) (ts : List (Term F)) :
    (power d n ts).2 ≤ 512 * (n + 1) * (d + 2) ^ (n + 2) * (ts.length + 1) := by
  induction n generalizing ts with
  | zero =>
    simp only [power, Nat.zero_add]
    nlinarith [Nat.one_le_pow 2 (d + 2) (by omega)]
  | succ n ih =>
    have hr := round_cost d ts
    have hp := ih (round d ts).1
    rw [round_length] at hp
    simp only [power]
    have hpow : (d + 2) ^ 2 ≤ (d + 2) ^ (n + 2) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    rw [show n + 1 + 2 = (n + 2) + 1 by omega, pow_succ]
    have hr' : (round d ts).2 ≤ 256 * (d + 2) ^ (n + 2) * (ts.length + 1) :=
      hr.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 256 hpow))
    have hp' : (power d n (round d ts).1).2 ≤
        512 * (n + 1) * (d + 2) ^ (n + 2) * ((d + 2) * (ts.length + 1)) :=
      hp.trans (Nat.mul_le_mul_left _ (by nlinarith))
    let z := (d + 2) ^ (n + 2) * (ts.length + 1)
    have hz : 1 ≤ z := Nat.mul_pos
      (Nat.pow_pos (by omega)) (by omega)
    have hr'' : (round d ts).2 ≤ 256 * z := by simpa only [z, Nat.mul_assoc] using hr'
    have hp'' : (power d n (round d ts).1).2 ≤ 512 * (n + 1) * (d + 2) * z := by
      convert hp' using 1
      dsimp only [z]
      ring
    have hh : 32 + (round d ts).2 + (power d n (round d ts).1).2 ≤
        512 * (n + 2) * (d + 2) * z := by nlinarith
    convert hh using 1
    dsimp only [z]
    ring

omit [CommRing F] in
theorem project_correct (d m : ℕ) (ts : List (Term F)) :
    project d m ts = (ts.filter (fun t => decide (t.t + d * t.e < m)), 32 * (ts.length + 1)) := by
  induction ts with
  | nil => simp [project]
  | cons t ts ih =>
    simp only [project, ih, List.filter_cons, decide_eq_true_eq, List.length_cons]
    congr 1
    omega

omit [CommRing F] in
theorem densify_correct (ts : List (Term F)) :
    densify ts = (ts.map (fun t => (t.coefficient, t.t :: t.e :: t.jets)),
      32 * (ts.length + 1)) := by
  induction ts with
  | nil => simp [densify]
  | cons t ts ih => simp [densify, ih]; omega

theorem equal_correct (xs ys : List ℕ) : (equal xs ys).1 = decide (xs = ys) ∧
    (equal xs ys).2 ≤ 32 * (xs.length + 1) := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp [equal]
  | cons x xs ih =>
    cases ys with
    | nil => simp [equal]
    | cons y ys =>
      have ht := ih ys
      by_cases h : x = y <;> simp [equal, h, ht.1]
      omega

/-- Proof-only duplicate-aware dense coefficient sum. -/
def coordinate (target : List ℕ) (ts : List (DenseTerm F)) : F :=
  (ts.map fun t => if t.2 = target then t.1 else 0).sum

theorem lookup_result (target : List ℕ) (ts : List (DenseTerm F)) :
    (lookup target ts).1 = coordinate target ts := by
  induction ts with
  | nil => simp [lookup, coordinate]
  | cons t ts ih =>
    obtain ⟨c, vector⟩ := t
    by_cases h : vector = target
    · subst vector
      simp [lookup, (equal_correct target target).1, ih, coordinate]
    · simp [lookup, (equal_correct vector target).1, ih, coordinate, h]

/-- Public composition with the actual affine translation program. -/
def column (d m : ℕ) (higher : List ℕ) (a y : F) (x b : ℕ) :
    Option (List (DenseTerm F)) × ℕ :=
  let translated := LocalColumnTranslationMachine.translate a y x b m
  match translated.1 with
  | .done ts =>
      let result := execute d m higher ts
      (some result.1, 32 + translated.2 + result.2)
  | _ => (none, 32 + translated.2)

theorem lookup_cost (target : List ℕ) (ts : List (DenseTerm F)) :
    (lookup target ts).2 ≤ 64 * (target.length + 2) * (ts.length + 1) := by
  induction ts with
  | nil => simp [lookup]; omega
  | cons t ts ih =>
    have he' : (equal t.2 target).2 ≤ 32 * (target.length + 1) := by
      have hs : (equal t.2 target).2 = (equal target t.2).2 := by
        have aux (xs ys : List ℕ) : (equal xs ys).2 = (equal ys xs).2 := by
          induction xs generalizing ys with
          | nil => cases ys <;> rfl
          | cons x xs ih =>
            cases ys with
            | nil => rfl
            | cons y ys => by_cases h : x = y <;> simp [equal, h, eq_comm, ih]
        exact aux _ _
      rw [hs]
      exact (equal_correct target t.2).2
    simp only [lookup, List.length_cons]
    nlinarith

/-- Uniform output and operation bounds when each supplied U exponent is bounded by m. -/
theorem rewrite_bounds (d m : ℕ) (xs : List ℕ)
    (ts : List (LocalColumnTranslationMachine.Term F))
    (ht : ∀ t ∈ ts, t.u ≤ m) :
    (rewrite d m xs ts).1.length ≤ (d + 2) ^ (m + 2) * ts.length ∧
    (rewrite d m xs ts).2 ≤ 4096 * (m + 2) * (d + 2) ^ (m + 2) * (ts.length + 1) := by
  let p := (d + 2) ^ (m + 2)
  have hp : 1 ≤ p := Nat.pow_pos (by omega)
  induction ts with
  | nil => simp only [rewrite, List.length_nil, Nat.mul_zero, Nat.zero_add]; constructor
           · omega
           · change 32 ≤ 4096 * (m + 2) * p * 1; nlinarith
  | cons t ts ih =>
    have hu := ht t (by simp)
    obtain ⟨hl, hc⟩ := ih (fun s hs => ht s (by simp [hs]))
    have hn : (d + 1) ^ t.u ≤ p :=
      (Nat.pow_le_pow_left (by omega) t.u).trans
        (Nat.pow_le_pow_right (by omega) (by omega))
    have hn' : (d + 2) ^ (t.u + 2) ≤ p :=
      Nat.pow_le_pow_right (by omega) (by omega)
    have hpc := power_cost d t.u [⟨t.coefficient, t.t, 0, xs⟩]
    have hpc' : (power d t.u [⟨t.coefficient, t.t, 0, xs⟩]).2 ≤
        1024 * (m + 1) * p := by
      have hh := Nat.mul_le_mul (Nat.mul_le_mul_left 512 (Nat.add_le_add_right hu 1)) hn'
      simp only [List.length_cons, List.length_nil] at hpc
      nlinarith
    have hret : (project d m (power d t.u [⟨t.coefficient, t.t, 0, xs⟩]).1).1.length ≤ p := by
      rw [project_correct]
      exact (List.length_filter_le _ _).trans (by simpa [power_length] using hn)
    simp only [rewrite, appendCells_correct, List.length_append, List.length_cons]
    constructor
    · change _ ≤ p * (ts.length + 1)
      change _ ≤ p * ts.length at hl
      nlinarith
    · have hpr : (project d m (power d t.u [⟨t.coefficient, t.t, 0, xs⟩]).1).2 ≤
          32 * (p + 1) := by
        rw [project_correct]
        simp only [power_length, List.length_cons, List.length_nil, Nat.zero_add, Nat.mul_one]
        omega
      change _ ≤ 4096 * (m + 2) * p * (ts.length + 1) at hc
      change _ ≤ 4096 * (m + 2) * p * (ts.length + 1 + 1)
      nlinarith

theorem execute_bounds (d m : ℕ) (xs : List ℕ)
    (ts : List (LocalColumnTranslationMachine.Term F))
    (ht : ∀ t ∈ ts, t.u ≤ m) :
    (execute d m xs ts).1.length ≤ (d + 2) ^ (m + 2) * ts.length ∧
    (execute d m xs ts).2 ≤ 8192 * (m + 2) * (d + 2) ^ (m + 2) * (ts.length + 1) := by
  obtain ⟨hl, hc⟩ := rewrite_bounds d m xs ts ht
  simp only [execute, densify_correct, List.length_map]
  refine ⟨hl, ?_⟩
  have hp : 1 ≤ (d + 2) ^ (m + 2) := Nat.pow_pos (by omega)
  nlinarith

end ReedSolomon.HiddenDerivative.LocalColumnRewriteMachine
