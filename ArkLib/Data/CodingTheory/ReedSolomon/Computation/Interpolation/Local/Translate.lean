/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.AffinePowerTruncationMachine
/-!
# Materialized truncated local translation

This composed program runs both affine-power kernels, then enumerates their coefficient pairs.
A pair at indices i,k emits coefficient c_i*d_k and exponents (i+k,k) precisely when i+k<m.
Thus it constructs the T-truncated expansion of `(center+T)^x*(received+T*U)^b`.
Zero coefficients are retained; no field equality or polynomial operation is an instruction.
The separate lookup sums all entries at the requested pair of exponents.

Outer instructions charge 32 primitive units for scalar arithmetic, comparisons, counters,
register/cell access, allocation and emission. Nested affine instructions retain their charge
plus four wrapper units. Host fuel, reclamation and arithmetic bit costs are excluded.
U-to-E rewriting and the final contact projection are not implemented by this translation stage.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.LocalColumnTranslationMachine

abbrev Affine := Polynomial.AffinePowerTruncationMachine.Configuration

/-- One materialized bivariate monomial; duplicate entries are allowed. -/
structure Term (F : Type*) where
  coefficient : F
  t : ℕ
  u : ℕ
  deriving DecidableEq, Repr

inductive Configuration (F : Type*) where
  | start (x b : ℕ)
  | left (b : ℕ) (inner : Affine F)
  | right (left : List F) (inner : Affine F)
  | outer (left : List F) (i : ℕ) (right : List F) (out : List (Term F))
  | inner (left : List F) (i : ℕ) (right remaining : List F)
      (k : ℕ) (coefficient : F) (out : List (Term F))
  | reverse (remaining out : List (Term F))
  | done (terms : List (Term F))
  deriving DecidableEq, Repr

variable {F : Type*} [CommSemiring F]

/-- Both nested executions and every coefficient-pair operation are explicitly dispatched. -/
def step (center received : F) (m : ℕ) : Configuration F → Option (Configuration F × ℕ)
  | .start x b => some (.left b (.start x m), 32)
  | .left b (.done cs) => some (.right cs (.start b m), 32)
  | .left b s => match Polynomial.AffinePowerTruncationMachine.step center s with
    | none => none
    | some (next, cost) => some (.left b next, cost + 4)
  | .right cs (.done ds) => some (.outer cs 0 ds [], 32)
  | .right cs s => match Polynomial.AffinePowerTruncationMachine.step received s with
    | none => none
    | some (next, cost) => some (.right cs next, cost + 4)
  | .outer [] _ _ out => some (.reverse out [], 32)
  | .outer (c :: cs) i ds out => some (.inner cs i ds ds 0 c out, 32)
  | .inner cs i ds [] _ _ out => some (.outer cs (i + 1) ds out, 32)
  | .inner cs i ds (c :: rest) k a out =>
      some (.inner cs i ds rest (k + 1) a
        (if i + k < m then ⟨a * c, i + k, k⟩ :: out else out), 32)
  | .reverse (t :: ts) out => some (.reverse ts (t :: out), 32)
  | .reverse [] out => some (.done out, 32)
  | .done _ => none

def runFuel (center received : F) (m : ℕ) : ℕ → Configuration F → Configuration F × ℕ
  | 0, s => (s, 0)
  | n + 1, s => match step center received m s with
    | none => (s, 0)
    | some (next, c) =>
      let result := runFuel center received m n next
      (result.1, c + result.2)

inductive Trace (center received : F) (m : ℕ) :
    ℕ → Configuration F → ℕ → Configuration F → Prop where
  | nil (s) : Trace center received m 0 s 0 s
  | cons {n s v t c k} (head : step center received m s = some (v, c))
      (tail : Trace center received m n v k t) : Trace center received m (n + 1) s (c + k) t

theorem Trace.append {a y : F} {m n r c k : ℕ} {s v t : Configuration F}
    (h : Trace a y m n s c v) (h' : Trace a y m r v k t) :
    Trace a y m (n + r) s (c + k) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

theorem Trace.runFuel_done {a y : F} {m n c : ℕ} {s : Configuration F} {ts : List (Term F)}
    (h : Trace a y m n s c (.done ts)) (extra : ℕ) :
    runFuel a y m (n + extra) s = (.done ts, c) := by
  generalize ht : Configuration.done ts = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
    rw [Nat.add_right_comm, runFuel, head]
    dsimp only
    rw [ih ht]

/-- Nested primitive charges are preserved, including dispatch overhead. -/
theorem left_trace {a y : F} {m b n c : ℕ} {s t : Affine F}
    (h : Polynomial.AffinePowerTruncationMachine.Trace a n s c t) :
    Trace a y m n (.left b s) (c + 4 * n) (.left b t) := by
  induction h with
  | nil s => exact Trace.nil _
  | @cons n s v t c k head tail ih =>
    have hs : step a y m (.left b s) = some (.left b v, c + 4) := by
      cases s with
      | done cs => simp [Polynomial.AffinePowerTruncationMachine.step] at head
      | _ => simp only [step, head]
    convert Trace.cons hs ih using 1
    omega

theorem right_trace {a y : F} {m n c : ℕ} {cs : List F} {s t : Affine F}
    (h : Polynomial.AffinePowerTruncationMachine.Trace y n s c t) :
    Trace a y m n (.right cs s) (c + 4 * n) (.right cs t) := by
  induction h with
  | nil s => exact Trace.nil _
  | @cons n s v t c k head tail ih =>
    have hs : step a y m (.right cs s) = some (.right cs v, c + 4) := by
      cases s with
      | done ds => simp [Polynomial.AffinePowerTruncationMachine.step] at head
      | _ => simp only [step, head]
    convert Trace.cons hs ih using 1
    omega

/-- Proof-only list of terms from one left coefficient. -/
def rowSpec (m i : ℕ) (a : F) : ℕ → List F → List (Term F)
  | _, [] => []
  | k, c :: cs =>
      if i + k < m then ⟨a * c, i + k, k⟩ :: rowSpec m i a (k + 1) cs
      else rowSpec m i a (k + 1) cs

/-- Proof-only ordered expansion of the two supplied coefficient lists. -/
def pairsSpec (m : ℕ) (ds : List F) : ℕ → List F → List (Term F)
  | _, [] => []
  | i, c :: cs => rowSpec m i c 0 ds ++ pairsSpec m ds (i + 1) cs

theorem rowSpec_length_le (m i k : ℕ) (a : F) (cs : List F) :
    (rowSpec m i a k cs).length ≤ cs.length := by
  induction cs generalizing k with
  | nil => rfl
  | cons c cs ih =>
    have ht := ih (k + 1)
    simp only [rowSpec]
    split <;> simp only [List.length_cons] <;> omega

theorem pairsSpec_length_le (m i : ℕ) (cs ds : List F) :
    (pairsSpec m ds i cs).length ≤ cs.length * ds.length := by
  induction cs generalizing i with
  | nil => simp [pairsSpec]
  | cons c cs ih =>
    have hr := rowSpec_length_le m i 0 c ds
    have ht := ih (i + 1)
    simp only [pairsSpec, List.length_append, List.length_cons]
    nlinarith

theorem inner_trace (a y : F) (m : ℕ) (cs : List F) (i : ℕ) (ds rest : List F)
    (k : ℕ) (c : F) (out : List (Term F)) :
    ∃ cost, Trace a y m (rest.length + 1) (.inner cs i ds rest k c out) cost
      (.outer cs (i + 1) ds ((rowSpec m i c k rest).reverse ++ out)) := by
  induction rest generalizing k out with
  | nil => exact ⟨_, Trace.cons rfl (Trace.nil _)⟩
  | cons v rest ih =>
    by_cases h : i + k < m
    · obtain ⟨cost, ht⟩ := ih (k + 1) (⟨c * v, i + k, k⟩ :: out)
      refine ⟨32 + cost, ?_⟩
      simpa [rowSpec, h, List.reverse_cons, List.append_assoc] using
        Trace.cons (s := .inner cs i ds (v :: rest) k c out) (by simp [step, h]) ht
    · obtain ⟨cost, ht⟩ := ih (k + 1) out
      refine ⟨32 + cost, ?_⟩
      simpa [rowSpec, h] using
        Trace.cons (s := .inner cs i ds (v :: rest) k c out) (by simp [step, h]) ht

theorem outer_trace (a y : F) (m i : ℕ) (cs ds : List F) (out : List (Term F)) :
    ∃ cost, Trace a y m (cs.length * (ds.length + 2) + 1) (.outer cs i ds out) cost
      (.reverse ((pairsSpec m ds i cs).reverse ++ out) []) := by
  induction cs generalizing i out with
  | nil =>
    refine ⟨32, ?_⟩
    simpa [pairsSpec] using Trace.cons (center := a) (received := y)
      (s := .outer [] i ds out) (by rfl) (Trace.nil _)
  | cons c cs ih =>
    obtain ⟨ic, hi⟩ := inner_trace a y m cs i ds ds 0 c out
    obtain ⟨cost, ht⟩ := ih (i + 1) ((rowSpec m i c 0 ds).reverse ++ out)
    refine ⟨32 + (ic + cost), ?_⟩
    convert Trace.cons (s := .outer (c :: cs) i ds out) (by rfl) (hi.append ht) using 1
    · simp only [List.length_cons]; ring
    · simp [pairsSpec, List.reverse_append, List.append_assoc]

theorem reverse_trace (a y : F) (m : ℕ) (ts out : List (Term F)) :
    ∃ c, Trace a y m (ts.length + 1) (.reverse ts out) c (.done (ts.reverse ++ out)) := by
  induction ts generalizing out with
  | nil => exact ⟨_, Trace.cons rfl (Trace.nil _)⟩
  | cons t ts ih =>
    obtain ⟨c, ht⟩ := ih (t :: out)
    refine ⟨32 + c, ?_⟩
    simpa [List.reverse_cons, List.append_assoc] using Trace.cons (by rfl) ht


/-- Every affine interpreter execution has a corresponding instruction trace. -/
theorem affine_refines (a : F) (n : ℕ) (s : Affine F) :
    ∃ k ≤ n, Polynomial.AffinePowerTruncationMachine.Trace a k s
      (Polynomial.AffinePowerTruncationMachine.runFuel a n s).2
      (Polynomial.AffinePowerTruncationMachine.runFuel a n s).1 := by
  induction n generalizing s with
  | zero => exact ⟨0, le_rfl, .nil s⟩
  | succ n ih =>
    cases hs : Polynomial.AffinePowerTruncationMachine.step a s with
    | none => exact ⟨0, Nat.zero_le _, by
        simpa [Polynomial.AffinePowerTruncationMachine.runFuel, hs] using
          Polynomial.AffinePowerTruncationMachine.Trace.nil (a := a) s⟩
    | some pair =>
      obtain ⟨k, hk, ht⟩ := ih pair.1
      exact ⟨k + 1, by omega, by
        simpa [Polynomial.AffinePowerTruncationMachine.runFuel, hs] using
          Polynomial.AffinePowerTruncationMachine.Trace.cons hs ht⟩

/-- Every instruction has at most 36 units, including both nested dispatchers. -/
theorem step_cost_le {a y : F} {m c : ℕ} {s t : Configuration F}
    (h : step a y m s = some (t, c)) : c ≤ 36 := by
  cases s with
  | start x b => cases h; omega
  | left b inner =>
    cases inner <;> simp only [step] at h
    all_goals first
      | (cases h; omega)
      | (split at h
         · cases h
         · rename_i next cost heq
           have hh := Polynomial.AffinePowerTruncationMachine.step_cost heq
           cases h
           omega)
  | right cs inner =>
    cases inner <;> simp only [step] at h
    all_goals first
      | (cases h; omega)
      | (split at h
         · cases h
         · rename_i next cost heq
           have hh := Polynomial.AffinePowerTruncationMachine.step_cost heq
           cases h
           omega)
  | outer cs i ds out => cases cs <;> cases h <;> omega
  | inner cs i ds rest k v out => cases rest <;> cases h <;> omega
  | reverse ts out => cases ts <;> cases h <;> omega
  | done ts => cases h

theorem Trace.cost_le {a y : F} {m n c : ℕ} {s t : Configuration F}
    (h : Trace a y m n s c t) : c ≤ 36 * n := by
  induction h with
  | nil s => omega
  | cons head tail ih => have hh := step_cost_le head; omega

/-- Proof-only output specification, using the proved affine coefficient meaning. -/
noncomputable def columnSpec (a y : F) (x b m : ℕ) : List (Term F) :=
  pairsSpec m
    (Polynomial.AffinePowerTruncationMachine.coefficients ((Polynomial.C y + Polynomial.X)^b) m 0)
    0 (Polynomial.AffinePowerTruncationMachine.coefficients
      ((Polynomial.C a + Polynomial.X)^x) m 0)

/-- Uniform host fuel bounds the two scalar kernels, pair scans, reversal and emission. -/
def fuel (x b m : ℕ) : ℕ :=
  Polynomial.AffinePowerTruncationMachine.fuel x m +
    Polynomial.AffinePowerTruncationMachine.fuel b m + 2 * m * m + 2 * m + 5

/-- The complete composed execution materializes the specified truncated translation. -/
theorem construction_correct (a y : F) (x b m : ℕ) :
    ∃ c, runFuel a y m (fuel x b m) (.start x b) = (.done (columnSpec a y x b m), c) ∧
      c ≤ 36 * fuel x b m := by
  let cs := Polynomial.AffinePowerTruncationMachine.coefficients
    ((Polynomial.C a + Polynomial.X)^x) m 0
  let ds := Polynomial.AffinePowerTruncationMachine.coefficients
    ((Polynomial.C y + Polynomial.X)^b) m 0
  have hcs : cs.length = m := Polynomial.AffinePowerTruncationMachine.coefficients_length _ _ _
  have hds : ds.length = m := Polynomial.AffinePowerTruncationMachine.coefficients_length _ _ _
  obtain ⟨ln, hln, hl⟩ := affine_refines a
    (Polynomial.AffinePowerTruncationMachine.fuel x m) (.start x m)
  rw [Polynomial.AffinePowerTruncationMachine.power_runFuel] at hl
  obtain ⟨rn, hrn, hr⟩ := affine_refines y
    (Polynomial.AffinePowerTruncationMachine.fuel b m) (.start b m)
  rw [Polynomial.AffinePowerTruncationMachine.power_runFuel] at hr
  obtain ⟨oc, ho⟩ := outer_trace a y m 0 cs ds []
  simp only [List.append_nil] at ho
  obtain ⟨rc, hv⟩ := reverse_trace a y m (pairsSpec m ds 0 cs).reverse []
  simp only [List.reverse_reverse, List.append_nil] at hv
  have ht := Trace.cons (s := .start x b) (by rfl)
    ((left_trace (y := y) (m := m) (b := b) hl).append
      (Trace.cons (s := .left b (.done cs)) (by rfl)
        ((right_trace (a := a) (m := m) (cs := cs) hr).append
          (Trace.cons (s := .right cs (.done ds)) (by rfl) (ho.append hv)))))
  have hout := pairsSpec_length_le m 0 cs ds
  have hn : 1 + (ln + (1 + (rn + (1 +
      (cs.length * (ds.length + 2) + 1 + ((pairsSpec m ds 0 cs).reverse.length + 1)))))) ≤
      fuel x b m := by
    simp only [hcs, hds, List.length_reverse] at hout ⊢
    unfold fuel
    nlinarith
  let steps := ln + (rn + (cs.length * (ds.length + 2) + 1 +
    ((pairsSpec m ds 0 cs).reverse.length + 1) + 1) + 1) + 1
  have he := ht.runFuel_done (fuel x b m - steps)
  have hn' : steps ≤ fuel x b m := by dsimp only [steps]; omega
  rw [Nat.add_sub_of_le hn'] at he
  exact ⟨_, he, ht.cost_le.trans (Nat.mul_le_mul_left 36 hn')⟩

/-- Public scalar-input translation program. -/
def translate (a y : F) (x b m : ℕ) : Configuration F × ℕ :=
  runFuel a y m (fuel x b m) (.start x b)

/-- A coarse absolute polynomial bound, independent of derivative order. -/
theorem fuel_le (x b m : ℕ) : fuel x b m ≤ 8 * (x + b + m + 2) * (m + 1) := by
  unfold fuel Polynomial.AffinePowerTruncationMachine.fuel
  nlinarith

/-- Duplicate-aware coordinate sum; no field equality is needed. Each recursive cell charges
both natural comparisons, scalar addition, pointer accesses and control. -/
def lookup (t u : ℕ) : List (Term F) → F × ℕ
  | [] => (0, 32)
  | entry :: rest =>
      let result := lookup t u rest
      (if entry.t = t ∧ entry.u = u then entry.coefficient + result.1 else result.1,
        32 + result.2)

/-- Proof-only coefficient sum for the materialized intermediate terms. -/
def coordinate (t u : ℕ) (ts : List (Term F)) : F :=
  (ts.map fun entry => if entry.t = t ∧ entry.u = u then entry.coefficient else 0).sum

/-- Lookup refines the sum of all duplicate contributions and charges every visited cell. -/
theorem lookup_correct (t u : ℕ) (ts : List (Term F)) :
    lookup t u ts = (coordinate t u ts, 32 * (ts.length + 1)) := by
  induction ts with
  | nil => simp [lookup, coordinate]
  | cons entry ts ih =>
    rw [lookup, ih]
    simp only [coordinate, List.map_cons, List.sum_cons, List.length_cons]
    split <;> simp_all [coordinate] <;> omega

end ReedSolomon.HiddenDerivative.LocalColumnTranslationMachine
