/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.Data.QuadraticAlgebra.SetupRefinement

/-!
# Proof-erased certification of the executed field setup

The dependent result takes its nonsquare parameter, alphabets, samples and cost from the actual
setup run. Its proofs certify those observed values and are erased; they do not choose a field,
compute a root or enumerate a list. This interface lets a surrounding executable use the
computable quadratic-field dictionary without an additional nonsquare decision procedure.
-/

@[expose] public section

namespace QuadraticAlgebra.SetupMachine

variable {q : ℕ}

/-- The actual observed result is successful and has the proved integrity and cost contracts. -/
theorem run_certified (L : ℕ) (hq : q.Prime) (hodd : q ≠ 2) (hL : L ≤ q ^ 2) :
    match runFuel (q := q) L (budget q L) (.base .start) with
    | (.done (some ⟨a, data⟩), c) => Correct L a data ∧ c.total ≤ budget q L
    | _ => False := by
  obtain ⟨a, data, c, hr, hc, hb⟩ := setup_correct L hq hodd hL
  rw [hr]
  exact ⟨hc, hb⟩

/-- Materialized runtime values with proof-only integrity and same-run evidence. -/
structure CertifiedOutput (q L : ℕ) where
  parameter : ZMod q
  data : Prepared q parameter
  cost : Cost
  correct : Correct L parameter data
  cost_bound : cost.total ≤ budget q L
  execution : runFuel L (budget q L) (.base .start) =
    (.done (some ⟨parameter, data⟩), cost)

/-- Execute setup once, retaining its observed values. The proof branches only eliminate
unreachable failures; no witness is selected from a proposition into runtime data. The wrapper
itself adds no new arithmetic or traversal; an outer caller must charge its fixed-size handoff. -/
def certifiedRun (L : ℕ) (hq : q.Prime) (hodd : q ≠ 2) (hL : L ≤ q ^ 2) :
    CertifiedOutput q L :=
  match hr : runFuel (q := q) L (budget q L) (.base .start) with
  | (.done (some ⟨a, data⟩), c) =>
      { parameter := a
        data := data
        cost := c
        correct := by have h := run_certified L hq hodd hL; rw [hr] at h; exact h.1
        cost_bound := by have h := run_certified L hq hodd hL; rw [hr] at h; exact h.2
        execution := hr }
  | (.base _, _) | (.search _ _, _) | (.pairs _ _ _, _) | (.decode _ _ _ _ _, _)
  | (.save _ _ _ _ _ _, _) | (.reverse _ _ _ _ _, _) | (.prefix _ _ _ _ _, _)
  | (.done none, _) => by
      have h := run_certified L hq hodd hL
      rw [hr] at h
      contradiction

end QuadraticAlgebra.SetupMachine
