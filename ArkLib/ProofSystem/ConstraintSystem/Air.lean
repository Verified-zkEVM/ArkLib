/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Algebraic intermediate representations

An AIR constrains a trace: a table of field elements with n rows.

Each constraint is a polynomial in the cells of two consecutive rows.

It may also read the public values and the periodic columns.

A trace satisfies the AIR when every constraint vanishes on every row it applies to.

This follows the AIR of the ethSTARK documentation (eprint 2021/582).

Ben-Sasson, Bentov, Horesh and Riabzev introduce it in eprint 2018/046.

Plonky3 writes every constraint as one polynomial that applies on every row.

It restricts the constraint with three selector variables:

```text
    row i of n:     is_first_row = [i = 0]
                    is_last_row  = [i = n - 1]
                    is_transition = [i != n - 1]
                    next row     = row (i + 1) mod n
```

The next row of the last row is row 0.

A constraint with no selector therefore also relates the last row to the first.

A constraint domain is the set of rows a constraint applies to.

The selector form and the domain form describe the same traces.
-/

@[expose] public section

namespace Air

/-- A variable of a constraint.

It is a cell of the current or next row, a public value, a periodic value, or a selector. -/
inductive Var where
  | main (offset : Fin 2) (col : ℕ)
  | prep (offset : Fin 2) (col : ℕ)
  | pub (i : ℕ)
  | periodic (i : ℕ)
  | isFirstRow
  | isLastRow
  | isTransition
  deriving DecidableEq

/-- A trace with its public data.

It holds n rows of main and preprocessed cells, the public values, and the periodic columns. -/
structure Instance (F : Type _) where
  height : ℕ
  main : ℕ → ℕ → F
  prep : ℕ → ℕ → F
  pub : ℕ → F
  periodic : ℕ → ℕ → F

variable {F : Type _} [Field F]

/-- The values of the variables on row i: the next row wraps to row 0. -/
def rowEnv (T : Instance F) (i : ℕ) : Var → F
  | .main 0 c => T.main i c
  | .main 1 c => T.main ((i + 1) % T.height) c
  | .prep 0 c => T.prep i c
  | .prep 1 c => T.prep ((i + 1) % T.height) c
  | .pub j => T.pub j
  | .periodic j => T.periodic j i
  | .isFirstRow => if i = 0 then 1 else 0
  | .isLastRow => if i = T.height - 1 then 1 else 0
  | .isTransition => if i = T.height - 1 then 0 else 1

/-- A trace satisfies polynomial constraints when each one vanishes on each row. -/
def Satisfies (C : List (MvPolynomial Var F)) (T : Instance F) : Prop :=
  ∀ i < T.height, ∀ c ∈ C, MvPolynomial.eval (rowEnv T i) c = 0

/-- The rows a constraint applies to. -/
inductive Domain where
  | everyRow
  | firstRow
  | lastRow
  | transition

/-- Row i of n lies in the domain: every row, row 0, row n - 1, or a row with a successor. -/
def Domain.Contains (n i : ℕ) : Domain → Prop
  | .everyRow => True
  | .firstRow => i = 0
  | .lastRow => i + 1 = n
  | .transition => i + 1 < n

instance (n i : ℕ) (d : Domain) : Decidable (d.Contains n i) := by
  cases d <;> unfold Domain.Contains <;> infer_instance

/-- The selector that restricts a constraint to its domain. -/
noncomputable def Domain.selector : Domain → MvPolynomial Var F
  | .everyRow => 1
  | .firstRow => .X .isFirstRow
  | .lastRow => .X .isLastRow
  | .transition => .X .isTransition

/-- A constraint with a domain. -/
structure Constraint (F : Type _) [CommSemiring F] where
  domain : Domain
  poly : MvPolynomial Var F

/-- A trace satisfies constraints with domains when each one vanishes on each row of its domain. -/
def SatisfiesOn (C : List (Constraint F)) (T : Instance F) : Prop :=
  ∀ c ∈ C, ∀ i < T.height, c.domain.Contains T.height i →
    MvPolynomial.eval (rowEnv T i) c.poly = 0

/-! ## Selectors and domains -/

/-- On a row of the trace, a domain's selector is 1 on the domain and 0 off it. -/
theorem eval_selector (T : Instance F) {i : ℕ} (hi : i < T.height) (d : Domain) :
    MvPolynomial.eval (rowEnv T i) d.selector = if d.Contains T.height i then 1 else 0 := by
  have h1 : i = T.height - 1 ↔ i + 1 = T.height := by omega
  have h2 : i + 1 < T.height ↔ ¬ i + 1 = T.height := by omega
  cases d <;> simp [Domain.selector, Domain.Contains, rowEnv, h1, h2, ite_not]

/-- The selector form and the domain form of an AIR describe the same traces. -/
theorem satisfies_selector_iff (C : List (Constraint F)) (T : Instance F) :
    Satisfies (C.map fun c => c.domain.selector * c.poly) T ↔ SatisfiesOn C T := by
  simp only [Satisfies, SatisfiesOn, List.mem_map, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, map_mul]
  constructor
  · intro h c hc i hi hd
    simpa [eval_selector T hi, hd] using h i hi c hc
  · intro h i hi c hc
    rw [eval_selector T hi]
    split_ifs with hd
    · simp [h c hc i hi hd]
    · simp

/-- On a trace of one row, a transition constraint asks nothing. -/
theorem transition_vacuous_of_height_one (p : MvPolynomial Var F) (T : Instance F)
    (h : T.height = 1) : SatisfiesOn [⟨.transition, p⟩] T := by
  simp [SatisfiesOn, Domain.Contains, h]

end Air
