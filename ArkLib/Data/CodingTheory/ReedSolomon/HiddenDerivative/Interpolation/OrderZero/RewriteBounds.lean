/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Local.RewriteSpec
/-!
# Polynomial local-rewrite cost at derivative order zero

At order zero the hidden variable expands only to E: no visible-jet branches are generated.
Every expansion round preserves the number of terms, so its repeated execution is linear in
the exponent rather than exponential. These bounds apply to the existing executable program,
including growing multiplicity. They remove the spurious exponential constant from the local
part of the large-gap interpolation route; matrix and solver cost composition are separate.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.LocalColumnRewriteMachine

variable {F : Type*} [CommRing F]

/-- At order zero every supplied term has exactly one branch, with an exact linear charge. -/
theorem round_zero_cost (ts : List (Term F)) : (round 0 ts).2 = 160 * ts.length + 32 := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [round, multiplyU, jetBranches, appendCells_correct, List.length_cons,
        List.length_nil, ih]
      omega

/-- Repeated order-zero expansion preserves length at every exponent. -/
theorem power_zero_length (n : ℕ) (ts : List (Term F)) :
    (power 0 n ts).1.length = ts.length := by simp [power_length]

/-- The actual repeated expansion has linear cost in exponent and input length. -/
theorem power_zero_cost (n : ℕ) (ts : List (Term F)) :
    (power 0 n ts).2 = n * (160 * ts.length + 64) + 32 := by
  induction n generalizing ts with
  | zero => simp [power]
  | succ n ih =>
      simp only [power, ih, round_zero_cost, round_length, Nat.zero_add, one_mul]
      ring

/-- Projection can only remove a term; one order-zero seed never branches. -/
theorem rewrite_zero_bounds (m : ℕ) (xs : List ℕ)
    (ts : List (LocalColumnTranslationMachine.Term F)) (ht : ∀ t ∈ ts, t.u ≤ m) :
    (rewrite 0 m xs ts).1.length ≤ ts.length ∧
      (rewrite 0 m xs ts).2 ≤ (224 * m + 192) * ts.length + 32 := by
  induction ts with
  | nil => simp [rewrite]
  | cons t ts ih =>
      have hu := ht t (by simp)
      obtain ⟨hl, hc⟩ := ih (fun s hs ↦ ht s (by simp [hs]))
      have hret : (project 0 m (power 0 t.u [⟨t.coefficient, t.t, 0, xs⟩]).1).1.length ≤ 1 := by
        rw [project_correct]
        exact (List.length_filter_le _ _).trans_eq (by simp [power_zero_length])
      have hproject : (project 0 m (power 0 t.u [⟨t.coefficient, t.t, 0, xs⟩]).1).2 = 64 := by
        simp [project_correct, power_zero_length]
      have hpower := power_zero_cost t.u [⟨t.coefficient, t.t, 0, xs⟩]
      simp only [List.length_cons, List.length_nil] at hpower
      simp only [rewrite, appendCells_correct, List.length_append, List.length_cons]
      constructor <;> nlinarith

/-- Dense materialization retains the polynomial multiplicity dependence at order zero. -/
theorem execute_zero_bounds (m : ℕ) (xs : List ℕ)
    (ts : List (LocalColumnTranslationMachine.Term F)) (ht : ∀ t ∈ ts, t.u ≤ m) :
    (execute 0 m xs ts).1.length ≤ ts.length ∧
      (execute 0 m xs ts).2 ≤ (224 * m + 224) * ts.length + 96 := by
  obtain ⟨hl, hc⟩ := rewrite_zero_bounds m xs ts ht
  simp only [execute, densify_correct, List.length_map]
  exact ⟨hl, by nlinarith⟩

/-- The full order-zero column has at most m² terms and polynomial observed work, with no
assumption that multiplicity is independent of block length. Its semantic local constraint is
unchanged from the generic column theorem. -/
theorem column_zero_refines (a y : F) (x b m : ℕ) :
    ∃ ts c, column 0 m [] a y x b = (some ts, c) ∧
      denseRepresented 0 ts = localConstraintAt m a y
        (sourceMonomial x b (fun j : Fin 0 ↦ j.elim0)) ∧
      (∀ t ∈ ts, t.2.length = 2) ∧ ts.length ≤ m * m ∧
      c ≤ 288 * (x + b + m + 2) * (m + 1) + (224 * m + 224) * (m * m) + 128 := by
  obtain ⟨c, hc, hcost⟩ := LocalColumnTranslationMachine.construction_correct a y x b m
  have hl : (LocalColumnTranslationMachine.columnSpec a y x b m).length ≤ m * m := by
    simpa [LocalColumnTranslationMachine.columnSpec,
      Polynomial.AffinePowerTruncationMachine.coefficients_length] using
      LocalColumnTranslationMachine.pairsSpec_length_le m 0
        (Polynomial.AffinePowerTruncationMachine.coefficients
          ((Polynomial.C a + Polynomial.X)^x) m 0)
        (Polynomial.AffinePowerTruncationMachine.coefficients
          ((Polynomial.C y + Polynomial.X)^b) m 0)
  obtain ⟨helen, hecost⟩ := execute_zero_bounds m []
    (LocalColumnTranslationMachine.columnSpec a y x b m) (columnSpec_u_bound a y x b m)
  refine ⟨_, 32 + c +
    (execute 0 m [] (LocalColumnTranslationMachine.columnSpec a y x b m)).2,
    ?_, ?_, ?_, helen.trans hl, ?_⟩
  · simp only [column, LocalColumnTranslationMachine.translate, hc]
  · simpa using execute_column_polynomial a y x b m (fun j : Fin 0 ↦ j.elim0)
  · exact execute_width m [] (by simp) _
  · have hf := LocalColumnTranslationMachine.fuel_le x b m
    have hc' : c ≤ 288 * (x + b + m + 2) * (m + 1) := by nlinarith
    nlinarith

end ReedSolomon.HiddenDerivative.LocalColumnRewriteMachine
