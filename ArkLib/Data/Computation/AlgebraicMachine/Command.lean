/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.Computation.AlgebraicMachine.Basic

/-!
# Structured algebraic programs and charged execution

Programs contain only the closed primitive menu and finite control syntax. In particular,
neither a branch nor a call carries a Lean callback. Calls share the fixed register bank;
their register-preservation requirements belong to the calling convention of each program.

Every transition costs one: primitive execution, sequence dispatch, branch and loop tests,
call entry, and return. A failed primitive or a non-Boolean test is stuck, not a successful
termination. The compositional execution judgment below is connected to these transitions,
so its cost is not an independently assigned annotation on a mathematical function.
-/

@[expose] public section

namespace AlgebraicMachine

/-- Closed structured code; a call contains its finite, nonrecursive body. -/
inductive Command (r : ℕ) where
  | skip
  | primitive (instruction : Primitive r)
  | seq (first second : Command r)
  | branch (test : Fin r) (yes no : Command r)
  | while (test : Fin r) (body : Command r)
  | call (body : Command r)
  deriving DecidableEq, Repr

/-- A pending command or an explicit charged return marker. -/
inductive Frame (r : ℕ) where
  | execute (command : Command r)
  | returnFromCall

/-- The machine's data state and control stack. -/
structure Configuration (F : Type*) (r : ℕ) where
  state : State F r
  pending : List (Frame r)

/-- One unit of abstract machine execution. Empty-stack termination is distinct from failure. -/
def step {F : Type*} {r : ℕ} [Field F] [DecidableEq F] :
    Configuration F r → Option (Configuration F r)
  | ⟨_, []⟩ => none
  | ⟨s, .returnFromCall :: rest⟩ => some ⟨s, rest⟩
  | ⟨s, .execute .skip :: rest⟩ => some ⟨s, rest⟩
  | ⟨s, .execute (.primitive p) :: rest⟩ =>
      (p.eval s).map fun t => ⟨t, rest⟩
  | ⟨s, .execute (.seq a b) :: rest⟩ =>
      some ⟨s, .execute a :: .execute b :: rest⟩
  | ⟨s, .execute (.branch test yes no) :: rest⟩ =>
      match s.registers test with
      | .boolean true => some ⟨s, .execute yes :: rest⟩
      | .boolean false => some ⟨s, .execute no :: rest⟩
      | _ => none
  | ⟨s, .execute (.while test body) :: rest⟩ =>
      match s.registers test with
      | .boolean true => some ⟨s, .execute body :: .execute (.while test body) :: rest⟩
      | .boolean false => some ⟨s, rest⟩
      | _ => none
  | ⟨s, .execute (.call body) :: rest⟩ =>
      some ⟨s, .execute body :: .returnFromCall :: rest⟩

/-- An actual execution trace with exactly the specified number of transitions. -/
inductive Steps {F : Type*} {r : ℕ} [Field F] [DecidableEq F] :
    ℕ → Configuration F r → Configuration F r → Prop where
  | refl (s) : Steps 0 s s
  | next {n s t u} : step s = some t → Steps n t u → Steps (n + 1) s u

/-- Concatenating traces adds their actual transition counts. -/
theorem Steps.trans {F : Type*} {r : ℕ} [Field F] [DecidableEq F]
    {m n : ℕ} {s t u : Configuration F r} (h : Steps m s t) (k : Steps n t u) :
    Steps (m + n) s u := by
  induction h with
  | refl => simpa using k
  | next hs _ ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Steps.next hs (ih k)

/-- Compositional termination and exact work, charging all control operations. -/
inductive Executes {F : Type*} {r : ℕ} [Field F] [DecidableEq F] :
    Command r → State F r → ℕ → State F r → Prop where
  | skip (s) : Executes .skip s 1 s
  | primitive {p s t} : p.eval s = some t → Executes (.primitive p) s 1 t
  | seq {a b s t u m n} : Executes a s m t → Executes b t n u →
      Executes (.seq a b) s (m + n + 1) u
  | branchTrue {test yes no s t n} : s.registers test = .boolean true →
      Executes yes s n t → Executes (.branch test yes no) s (n + 1) t
  | branchFalse {test yes no s t n} : s.registers test = .boolean false →
      Executes no s n t → Executes (.branch test yes no) s (n + 1) t
  | whileFalse {test body s} : s.registers test = .boolean false →
      Executes (.while test body) s 1 s
  | whileTrue {test body s t u m n} : s.registers test = .boolean true →
      Executes body s m t → Executes (.while test body) t n u →
      Executes (.while test body) s (m + n + 1) u
  | call {body s t n} : Executes body s n t → Executes (.call body) s (n + 2) t

/-- Every compositional certificate realizes a trace, in any surrounding continuation. -/
theorem Executes.steps {F : Type*} {r : ℕ} [Field F] [DecidableEq F]
    {c : Command r} {s t : State F r} {n : ℕ} (h : Executes c s n t)
    (rest : List (Frame r)) :
    Steps n ⟨s, .execute c :: rest⟩ ⟨t, rest⟩ := by
  induction h generalizing rest with
  | skip => exact .next rfl (.refl _)
  | primitive hp => exact .next (by simp [step, hp]) (.refl _)
  | seq _ _ ih₁ ih₂ => exact .next rfl ((ih₁ _).trans (ih₂ _))
  | branchTrue ht _ ih => exact .next (by simp [step, ht]) (ih _)
  | branchFalse ht _ ih => exact .next (by simp [step, ht]) (ih _)
  | whileFalse ht => exact .next (by simp [step, ht]) (.refl _)
  | whileTrue ht _ _ ih₁ ih₂ =>
      exact .next (by simp [step, ht]) ((ih₁ _).trans (ih₂ _))
  | call _ ih =>
      exact .next rfl ((ih _).trans (.next rfl (.refl _)))

/-- A fuel-bounded observer of the same transitions, accepting only an empty control stack.
Fuel is an external observation limit, not an instruction or an oracle available to programs. -/
def run {F : Type*} {r : ℕ} [Field F] [DecidableEq F] :
    ℕ → Configuration F r → Option (State F r)
  | _, ⟨s, []⟩ => some s
  | 0, ⟨_, _ :: _⟩ => none
  | fuel + 1, c@⟨_, _ :: _⟩ => (step c).bind (run fuel)

/-- A certified terminating trace is accepted by the executable observer with exact fuel. -/
theorem Steps.run {F : Type*} {r : ℕ} [Field F] [DecidableEq F]
    {n : ℕ} {c : Configuration F r} {t : State F r}
    (h : Steps n c ⟨t, []⟩) : run n c = some t := by
  generalize hz : (⟨t, []⟩ : Configuration F r) = z at h
  induction h with
  | refl => cases hz; rfl
  | @next n c c' z hs _ ih =>
      obtain ⟨s, pending⟩ := c
      cases pending with
      | nil => simp [step] at hs
      | cons a rest =>
          change (step ⟨s, a :: rest⟩).bind (AlgebraicMachine.run n) = some t
          rw [hs]
          exact ih hz

/-- A compositional execution proof guarantees actual execution, not only an output equation. -/
theorem Executes.run {F : Type*} {r : ℕ} [Field F] [DecidableEq F]
    {c : Command r} {s t : State F r} {n : ℕ} (h : Executes c s n t) :
    run n ⟨s, [.execute c]⟩ = some t :=
  (h.steps []).run

/-- Successful observation implies a real terminating trace within the supplied limit. -/
theorem run_sound {F : Type*} {r : ℕ} [Field F] [DecidableEq F]
    {fuel : ℕ} {c : Configuration F r} {t : State F r}
    (h : run fuel c = some t) : ∃ n ≤ fuel, Steps n c ⟨t, []⟩ := by
  induction fuel generalizing c with
  | zero =>
      obtain ⟨s, pending⟩ := c
      cases pending with
      | nil =>
          have ht : s = t := Option.some.inj h
          subst t
          exact ⟨0, Nat.le_refl _, .refl _⟩
      | cons => simp [run] at h
  | succ fuel ih =>
      obtain ⟨s, pending⟩ := c
      cases pending with
      | nil =>
          have ht : s = t := Option.some.inj h
          subst t
          exact ⟨0, Nat.zero_le _, .refl _⟩
      | cons a rest =>
          cases hs : step (⟨s, a :: rest⟩ : Configuration F r) with
          | none => simp [run, hs] at h
          | some c' =>
              have hr : run fuel c' = some t := by simpa [run, hs] using h
              obtain ⟨n, hn, ht⟩ := ih hr
              exact ⟨n + 1, Nat.succ_le_succ hn, .next hs ht⟩

end AlgebraicMachine
