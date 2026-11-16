/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Coratger
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Algebraic intermediate representations

An AIR constrains a trace: a table of field elements with `n` rows.

Each constraint is a polynomial in two consecutive rows, the public values and periodic columns.

A trace satisfies the AIR when every constraint vanishes on every row of its domain.

This follows the AIR of [EthStark21], which [BBHR18] introduces.

## Main definitions

- `Air.Instance`: a trace with its public data.
- `Air.rowEnv`: the values of the variables on one row.
- `Air.SatisfiesOn`: satisfaction of constraints with domains.
- `Air.Satisfies`: satisfaction of constraints that apply on every row.

## Main statements

- `Air.eval_selector`: on a row of the trace, a selector is the 0/1 indicator of its domain.
- `Air.satisfies_selector_iff`: the selector form and the domain form describe the same traces.
- `Air.transition_vacuous_of_height_one`: on one row, a transition constraint asks nothing.

## Selectors and domains

A constraint domain is the set of rows a constraint applies to.

Plonky3 instead writes every constraint as one polynomial that applies on every row.

It restricts that polynomial with three selector variables:

```text
    row i of n:     is_first_row  = [i = 0]
                    is_last_row   = [i = n - 1]
                    is_transition = [i != n - 1]
                    next row      = row (i + 1) mod n
```

The next row of the last row is row 0.

So a constraint with no selector also relates the last row to the first.

## Selectors are 0/1 indicators

Here a selector is 1 on its domain and 0 off it.

Plonky3 only promises a value that is nonzero on the domain and zero off it.

For instance, its two-adic STARK gives the first-row selector the value `n` on row 0.

Multiplying a whole constraint by a selector means the same under both conventions.

Other uses, such as `is_first_row - 1`, depend on the 0/1 values fixed here.

## Shape of the data

The columns are already-expanded evaluations, one value per row.

The type does not fix the number of columns or of public values.

A periodic column is any table of row values: nothing forces it to repeat.

The caller checks these shapes, for example that each period divides `n`.

Cells are total functions of the column index.

A constraint should read only columns below the trace width: a cell past it is junk.

## Computability

The row environment is executable.

Satisfaction is a proposition, so this file is not an executable constraint checker.

The domain selectors are noncomputable multivariate polynomials.

Mathlib builds those on finitely supported functions, whose zero does not compile.

## References

* [Ben-Sasson, E., *ethSTARK Documentation*][EthStark21]
* [Ben-Sasson, E., Bentov, I., Horesh, Y., and Riabzev, M., *Scalable, transparent, and
    post-quantum secure computational integrity*][BBHR18]
* Plonky3 `p3-air`, the selector convention:
  https://github.com/Plonky3/Plonky3/blob/0d803737b681774186cd283b1fd2d8e493655c82/air/src/builder.rs
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

It holds `n` rows of main and preprocessed cells, the public values and the periodic columns. -/
structure Instance (F : Type _) where
  /-- The number of rows `n`. -/
  height : ℕ
  /-- The main cell at a row and a column, read only on rows below `n`. -/
  main : ℕ → ℕ → F
  /-- The preprocessed cell at a row and a column, read only on rows below `n`. -/
  prep : ℕ → ℕ → F
  /-- The public values, in a number the type does not fix. -/
  pub : ℕ → F
  /-- The value of periodic column `j` on row `i`, already expanded and not forced to repeat. -/
  periodic : ℕ → ℕ → F

variable {F : Type _} [Field F]

/-- The values of the variables on row `i`, where the row after the last is row 0. -/
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

/-- Row `i` lies in the domain of a trace with `n` rows.

The test is meaningful only for `i < n`, a bound the satisfaction predicates add.

Without it, for `n = 0` the every-row domain contains row 100 and the first-row domain row 0. -/
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

/-- A trace satisfies constraints with domains when each vanishes on each row of its domain. -/
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
