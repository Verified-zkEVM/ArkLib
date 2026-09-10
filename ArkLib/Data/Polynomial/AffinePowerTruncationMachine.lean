/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Data.List.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-!
# Charged truncated affine powers

The machine materializes the first M coefficients of `(a + T)^n` in increasing degree order.
It initializes the truncated constant one, then performs n passes `new[i] = a*old[i]+old[i-1]`,
with a zero predecessor at index zero. Every pass explicitly reverses its accumulated output.
No polynomial arithmetic, coefficient extraction, binomial coefficient or power primitive is
executed. Semantics use polynomials only in the proof.

Each instruction has an upper charge of 32 units covering scalar arithmetic, control, natural
counter operations, register/cell access, allocation and output. A multiplication pass cell uses
one scalar multiplication and one addition; every other instruction uses neither. Pointer tails
may be shared. Host interpreter fuel, reclamation and scalar/natural bit costs are outside this
unit-operation model. The scalar parameter is an input, not an uncharged coefficient oracle.

The direct consumer is truncated local interpolation: this supplies coefficients of `(center+T)^x`
and of `(received+Z)^b₀`, where substituting Z=TU gives the diagonal T/U coefficients. Combining
these factors, rewriting U and projecting contact order `i+d*b<m` remain separate assembly steps.
In particular, these coefficients do not assert vanishing of the full local substitution.
-/

@[expose] public section

namespace Polynomial.AffinePowerTruncationMachine

variable {F : Type*}

/-- Materialized coefficient cursors and scalar/counter registers. -/
inductive Configuration (F : Type*) where
  | start (exponent width : ℕ)
  | seed (exponent remaining index : ℕ) (out : List F)
  | round (remaining : ℕ) (coefficients : List F)
  | multiply (rounds : ℕ) (remaining : List F) (previous : F) (out : List F)
  | reverse (rounds : ℕ) (remaining out : List F)
  | done (coefficients : List F)
  deriving DecidableEq, Repr

variable [CommSemiring F]

/-- Closed dispatch: one coefficient update or one list/counter operation per instruction. -/
def step (a : F) : Configuration F → Option (Configuration F × ℕ)
  | .start n M => some (.seed n M 0 [], 32)
  | .seed n 0 _ out => some (.reverse n out [], 32)
  | .seed n (M + 1) i out => some (.seed n M (i + 1) ((if i = 0 then 1 else 0) :: out), 32)
  | .round 0 cs => some (.done cs, 32)
  | .round (n + 1) cs => some (.multiply n cs 0 [], 32)
  | .multiply n [] _ out => some (.reverse n out [], 32)
  | .multiply n (c :: cs) prev out => some (.multiply n cs c ((a * c + prev) :: out), 32)
  | .reverse n [] out => some (.round n out, 32)
  | .reverse n (c :: cs) out => some (.reverse n cs (c :: out), 32)
  | .done _ => none

/-- Fuel is host bookkeeping; the returned work is the sum of dispatched charges. -/
def runFuel (a : F) : ℕ → Configuration F → Configuration F × ℕ
  | 0, s => (s, 0)
  | n + 1, s => match step a s with
    | none => (s, 0)
    | some (next, c) => let result := runFuel a n next; (result.1, c + result.2)

/-- Instruction-level execution records the actual intermediate states and charges. -/
inductive Trace (a : F) : ℕ → Configuration F → ℕ → Configuration F → Prop where
  | nil (s) : Trace a 0 s 0 s
  | cons {n s v t c k} (head : step a s = some (v, c)) (tail : Trace a n v k t) :
      Trace a (n + 1) s (c + k) t

/-- Sequential execution preserves all charges. -/
theorem Trace.append {a : F} {n m c k : ℕ} {s v t : Configuration F}
    (h : Trace a n s c v) (h' : Trace a m v k t) :
    Trace a (n + m) s (c + k) t := by
  induction h with
  | nil s => simpa using h'
  | cons head tail ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Trace.cons head (ih h')

/-- Extra fuel adds no work after the result has been emitted. -/
theorem Trace.runFuel_done {a : F} {n c : ℕ} {s : Configuration F} {cs : List F}
    (h : Trace a n s c (.done cs)) (extra : ℕ) :
    runFuel a (n + extra) s = (.done cs, c) := by
  generalize ht : Configuration.done cs = t at h
  induction h with
  | nil s => subst s; cases extra <;> rfl
  | cons head tail ih =>
    rw [Nat.add_right_comm, runFuel, head]
    dsimp only
    rw [ih ht]

/-- Every instruction uses the documented fixed upper charge. -/
theorem step_cost {a : F} {s t : Configuration F} {c : ℕ}
    (h : step a s = some (t, c)) : c = 32 := by
  cases s with
  | start n M => cases h; rfl
  | seed n M i out => cases M <;> cases h <;> rfl
  | round n cs => cases n <;> cases h <;> rfl
  | multiply n cs prev out => cases cs <;> cases h <;> rfl
  | reverse n cs out => cases cs <;> cases h <;> rfl
  | done cs => cases h

/-- Trace length determines the declared primitive upper charge exactly. -/
theorem Trace.cost_eq {a : F} {n c : ℕ} {s t : Configuration F}
    (h : Trace a n s c t) : c = 32 * n := by
  induction h with
  | nil s => rfl
  | cons head tail ih => rw [step_cost head, ih]; omega

/-- Proof-only coefficient slice. Extraction here is not a dispatched instruction. -/
def coefficients (P : F[X]) : ℕ → ℕ → List F
  | 0, _ => []
  | M + 1, i => P.coeff i :: coefficients P M (i + 1)

/-- Slices retain their physical length even when all coefficients are zero. -/
theorem coefficients_length (P : F[X]) (M i : ℕ) : (coefficients P M i).length = M := by
  induction M generalizing i with
  | zero => rfl
  | succ M ih => simp [coefficients, ih]

/-- The local coefficient recurrence uses only the preceding coefficient. -/
theorem coeff_affine_mul (a : F) (P : F[X]) (i : ℕ) :
    ((C a + X) * P).coeff i = a * P.coeff i + if i = 0 then 0 else P.coeff (i - 1) := by
  cases i with
  | zero => simp [add_mul]
  | succ i => simp [add_mul, coeff_X_mul]

/-- Explicit reversal returns the coefficient buffer to increasing degree order. -/
theorem reverse_trace (a : F) (n : ℕ) (cs out : List F) :
    ∃ c, Trace a (cs.length + 1) (.reverse n cs out) c (.round n (cs.reverse ++ out)) := by
  induction cs generalizing out with
  | nil => exact ⟨_, Trace.cons rfl (Trace.nil _)⟩
  | cons x xs ih =>
    obtain ⟨c, ht⟩ := ih (x :: out)
    refine ⟨32 + c, ?_⟩
    simpa [List.reverse_cons, List.append_assoc] using Trace.cons (by rfl) ht

/-- Initialization writes every zero cell instead of assuming a materialized coefficient list. -/
theorem seed_trace (a : F) (n M i : ℕ) (out : List F) :
    ∃ c, Trace a (M + 1) (.seed n M i out) c
      (.reverse n ((coefficients (1 : F[X]) M i).reverse ++ out) []) := by
  induction M generalizing i out with
  | zero => exact ⟨_, Trace.cons rfl (Trace.nil _)⟩
  | succ M ih =>
    obtain ⟨c, ht⟩ := ih (i + 1) ((if i = 0 then 1 else 0) :: out)
    refine ⟨32 + c, ?_⟩
    simpa [coefficients, coeff_one, List.reverse_cons, List.append_assoc] using
      Trace.cons (s := .seed n (M + 1) i out) (by rfl) ht

/-- A truncated pass agrees with multiplying the full polynomial and then taking its slice.
No coefficients beyond the input slice are required. -/
theorem multiply_trace (a : F) (n : ℕ) (P : F[X]) (M i : ℕ) (out : List F) :
    ∃ c, Trace a (M + 1)
      (.multiply n (coefficients P M i) (if i = 0 then 0 else P.coeff (i - 1)) out) c
      (.reverse n ((coefficients ((C a + X) * P) M i).reverse ++ out) []) := by
  induction M generalizing i out with
  | zero => exact ⟨_, Trace.cons rfl (Trace.nil _)⟩
  | succ M ih =>
    obtain ⟨c, ht⟩ := ih (i + 1)
      ((a * P.coeff i + if i = 0 then 0 else P.coeff (i - 1)) :: out)
    simp only [Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, if_false, Nat.add_sub_cancel]
      at ht
    refine ⟨32 + c, ?_⟩
    simpa only [coefficients, List.reverse_cons, List.append_assoc, List.singleton_append,
      coeff_affine_mul] using
      Trace.cons (s := .multiply n (coefficients P (M + 1) i)
        (if i = 0 then 0 else P.coeff (i - 1)) out) (by rfl) ht

/-- Each complete round is a fixed-width affine multiplication and a charged reversal. -/
theorem rounds_trace (a : F) (n M : ℕ) (P : F[X]) :
    ∃ c, Trace a (n * (2 * M + 3) + 1) (.round n (coefficients P M 0)) c
      (.done (coefficients ((C a + X) ^ n * P) M 0)) := by
  induction n generalizing P with
  | zero => exact ⟨_, by simpa using Trace.cons (a := a) (by rfl) (Trace.nil _)⟩
  | succ n ih =>
    obtain ⟨mc, hm⟩ := multiply_trace a n P M 0 []
    simp only [List.append_nil] at hm
    obtain ⟨rc, hr⟩ := reverse_trace a n (coefficients ((C a + X) * P) M 0).reverse []
    simp only [List.reverse_reverse, List.append_nil] at hr
    obtain ⟨c, ht⟩ := ih ((C a + X) * P)
    refine ⟨32 + (mc + (rc + c)), ?_⟩
    convert Trace.cons (s := .round (n + 1) (coefficients P M 0)) (by rfl)
      (hm.append (hr.append ht)) using 1
    · simp only [List.length_reverse, coefficients_length]
      ring
    · rw [pow_succ, mul_assoc]

/-- Exact host fuel, including allocation of the initial coefficient slice and final emission. -/
def fuel (n M : ℕ) : ℕ := (n + 1) * (2 * M + 3) + 1

/-- The actual program emits exactly the first M coefficients, with its complete declared cost. -/
theorem power_runFuel (a : F) (n M : ℕ) :
    runFuel a (fuel n M) (.start n M) =
      (.done (coefficients ((C a + X) ^ n) M 0), 32 * fuel n M) := by
  obtain ⟨sc, hs⟩ := seed_trace a n M 0 []
  simp only [List.append_nil] at hs
  obtain ⟨rc, hr⟩ := reverse_trace a n (coefficients (1 : F[X]) M 0).reverse []
  simp only [List.reverse_reverse, List.append_nil] at hr
  obtain ⟨c, ht⟩ := rounds_trace a n M (1 : F[X])
  simp only [mul_one] at ht
  have h := Trace.cons (s := .start n M) (by rfl) (hs.append (hr.append ht))
  have hf : (M + 1 + ((coefficients (1 : F[X]) M 0).reverse.length + 1 +
      (n * (2 * M + 3) + 1))) + 1 = fuel n M := by
    simp only [List.length_reverse, coefficients_length, fuel]
    ring
  rw [hf] at h
  have he := h.runFuel_done 0
  rw [Nat.add_zero, h.cost_eq] at he
  exact he

/-- Closed integer-power kernel, requiring no input coefficient materialization. -/
def power (a : F) (n M : ℕ) : Configuration F × ℕ := runFuel a (fuel n M) (.start n M)

/-- The cost is bilinear in exponent and truncation width, with an absolute constant. -/
theorem power_cost_le (a : F) (n M : ℕ) :
    (power a n M).2 ≤ 128 * (n + 1) * (M + 1) := by
  rw [power, power_runFuel]
  unfold fuel
  nlinarith

/-- Every retained coefficient has the claimed ordinary polynomial meaning. -/
theorem coefficients_get (P : F[X]) (M start i : ℕ) (hi : i < M) :
    (coefficients P M start)[i]'(by rw [coefficients_length]; exact hi) = P.coeff (start + i) := by
  induction M generalizing start i with
  | zero => omega
  | succ M ih =>
    cases i with
    | zero => simp [coefficients]
    | succ i =>
      simpa [coefficients, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (start + 1) i (by omega)

end Polynomial.AffinePowerTruncationMachine
