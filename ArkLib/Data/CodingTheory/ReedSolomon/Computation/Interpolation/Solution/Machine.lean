/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.CodingTheory.ReedSolomon.Computation.Interpolation.Matrix.Machine
public import ArkLib.Data.Matrix.NonzeroKernelSemantics
public import ArkLib.Data.MvPolynomial.EvaluationMachine
/-!
# Actual nonzero interpolation solver and sparse emission

The program retains an actually enumerated support, constructs the received matrix, executes the
nonzero-kernel solver using its materialized dimensions, and traverses support and coefficients
together. Each nonzero coefficient allocates its variable-index/exponent pairs explicitly in
order [X,Y0,...,Yd]. Zero coefficients are tested and skipped. No coefficient oracle, symbolic
polynomial, free list length or list map is executed. Solver fuel is the existing function of
materialized row/column counters. The theorem budgets below are proof-side bounds only.

Recursive conversion and composition clauses charge 32 primitive operations plus every executed
callee charge. This includes field equality, natural index updates, data accesses and allocation.
The scalar-field input, arithmetic bit costs, and inherited host-fuel administration remain
outside this unit-operation model.
-/

@[expose] public section

namespace ReedSolomon.HiddenDerivative.NonzeroInterpolationMachine

abbrev Term (F : Type*) := MvPolynomial.EvaluationMachine.Term F

/-- Return the actual solver vector together with its materialized sparse polynomial. -/
structure Output (F : Type*) where
  chosen : ℕ
  coefficients : List F
  terms : List (Term F)
  deriving DecidableEq, Repr

/-- Allocate every factor pair and outer cell; zero exponents retain the common dense layout. -/
def factors : ℕ → List ℕ → List (ℕ × ℕ) × ℕ
  | _, [] => ([], 32)
  | j, e :: es =>
      let r := factors (j + 1) es
      ((j, e) :: r.1, 32 + r.2)

variable {F : Type*} [Field F] [DecidableEq F]

/-- Zip actual support and actual coefficients, rejecting width mismatch. -/
def emit : List (List ℕ) → List F → Option (List (Term F)) × ℕ
  | [], [] => (some [], 32)
  | v :: vs, c :: cs =>
      let rest := emit vs cs
      match rest.1 with
      | none => (none, 32 + rest.2)
      | some out =>
          if c = 0 then (some out, 32 + rest.2)
          else
            let key := factors 0 v
            (some ((c, key.1) :: out), 32 + rest.2 + key.2)
  | _, _ => (none, 32)

/-- Support at strict jet cutoff `J`, matrix, homogeneous solver, and sparse conversion form one
observed run. -/
def runWithBudget (D d m J A : ℕ) (received : List (F × F)) : Option (Output F) × ℕ :=
  let support := InterpolationSupportMachine.enumerateWithBudget D d m J A
  match support.1 with
  | .done vs =>
      let matrix := ReceivedInterpolationMatrixMachine.runWithBudget D d m J A received
      match matrix.1 with
      | none => (none, 32 + support.2 + matrix.2)
      | some mat =>
          let solved := Matrix.NonzeroKernelMachine.runFuel mat.columns
            (Matrix.NonzeroKernelMachine.budget mat.rowCount mat.columns)
            (.check mat.rows mat.rows)
          match solved.1 with
          | .done j cs =>
              let sparse := emit vs cs
              (sparse.1.map (fun ts => ⟨j, cs, ts⟩),
                32 + support.2 + matrix.2 +
                  Matrix.NonzeroKernelMachine.totalCost solved.2 + sparse.2)
          | _ => (none,
              32 + support.2 + matrix.2 + Matrix.NonzeroKernelMachine.totalCost solved.2)
  | _ => (none, 32 + support.2)

/-- Legacy nonzero interpolation specializes the strict jet cutoff to `2 * m`. -/
def run (D d m A : ℕ) (received : List (F × F)) : Option (Output F) × ℕ :=
  runWithBudget D d m (2 * m) A received

/-- Ordered factor layout and exact cell-allocation charge. -/
theorem factors_correct (j : ℕ) (v : List ℕ) :
    factors j v = (List.ofFn (fun i : Fin v.length => (j + i.val, v[i.val])),
      32 * (v.length + 1)) := by
  induction v generalizing j with
  | nil => simp [factors]
  | cons e es ih =>
    rw [factors, ih]
    congr 1
    · rw [List.ofFn_succ]
      simp only [Fin.val_zero, Nat.add_zero, List.getElem_cons_zero,
        Fin.val_succ, List.getElem_cons_succ]
      congr 1
      apply congrArg List.ofFn
      funext i
      congr 1
      omega
    · simp only [List.length_cons]
      omega

/-- Proof-only sparse specification for a materialized vector. -/
def emitSpec : List (List ℕ) → List F → List (Term F)
  | v :: vs, c :: cs =>
      if c = 0 then emitSpec vs cs else (c, (factors 0 v).1) :: emitSpec vs cs
  | _, _ => []

/-- Successful sparse conversion charges all emitted factors and has at most one term per column. -/
theorem emit_correct (w : ℕ) (vs : List (List ℕ)) (cs : List F) (hc : cs.length = vs.length)
    (hv : ∀ v ∈ vs, v.length ≤ w) :
    ∃ c, emit vs cs = (some (emitSpec vs cs), c) ∧ (emitSpec vs cs).length ≤ vs.length ∧
      c ≤ 64 * (w + 2) * (vs.length + 1) := by
  induction vs generalizing cs with
  | nil => cases cs <;> simp_all [emit, emitSpec]; omega
  | cons v vs ih =>
    cases cs with
    | nil => simp at hc
    | cons c cs =>
      have hw := hv v (by simp)
      obtain ⟨k, hk, hl, hb⟩ := ih cs (by simpa using hc) (fun v hm => hv v (by simp [hm]))
      by_cases hz : c = 0
      · refine ⟨32 + k, ?_, ?_, ?_⟩
        · simp [emit, hk, emitSpec, hz]
        · simp [emitSpec, hz]; omega
        · simp only [List.length_cons]; nlinarith
      · refine ⟨32 + k + 32 * (v.length + 1), ?_, ?_, ?_⟩
        · simp [emit, hk, emitSpec, hz, factors_correct]
        · simpa [emitSpec, hz] using hl
        · simp only [List.length_cons]; nlinarith

/-- Reading the emitted factor exponents recovers the supplied support vector. -/
theorem factors_values (j : ℕ) (v : List ℕ) : ((factors j v).1.map Prod.snd) = v := by
  induction v generalizing j with
  | nil => rfl
  | cons e es ih => simp [factors, ih]

/-- Every emitted term comes from one supplied column and has a nonzero coefficient. -/
theorem emitSpec_keys (vs : List (List ℕ)) (cs : List F) :
    ∀ t ∈ emitSpec vs cs, ∃ v ∈ vs, t.2 = (factors 0 v).1 ∧ t.1 ≠ 0 := by
  induction vs generalizing cs with
  | nil => simp [emitSpec]
  | cons v vs ih =>
    cases cs with
    | nil => simp [emitSpec]
    | cons c cs =>
      by_cases hz : c = 0
      · intro t ht
        obtain ⟨u, hu, he, hn⟩ := ih cs t (by simpa [emitSpec, hz] using ht)
        exact ⟨u, by simp [hu], he, hn⟩
      · intro t ht
        simp only [emitSpec, hz, if_false, List.mem_cons] at ht
        rcases ht with rfl | ht
        · exact ⟨v, by simp, rfl, hz⟩
        · obtain ⟨u, hu, he, hn⟩ := ih cs t ht
          exact ⟨u, by simp [hu], he, hn⟩

/-- Distinct support vectors produce distinct emitted keys, so no normalization is required. -/
theorem emitSpec_nodup (vs : List (List ℕ)) (cs : List F) (hv : vs.Nodup) :
    ((emitSpec vs cs).map Prod.snd).Nodup := by
  induction vs generalizing cs with
  | nil => simp [emitSpec]
  | cons v vs ih =>
    cases cs with
    | nil => simp [emitSpec]
    | cons c cs =>
      obtain ⟨hnot, htail⟩ := List.nodup_cons.mp hv
      by_cases hz : c = 0
      · simpa [emitSpec, hz] using ih cs htail
      · simp only [emitSpec, hz, if_false, List.map_cons, List.nodup_cons]
        refine ⟨?_, ih cs htail⟩
        intro hm
        obtain ⟨t, ht, he⟩ := List.mem_map.mp hm
        obtain ⟨u, hu, hkey, _⟩ := emitSpec_keys vs cs t ht
        have huv : u = v := by
          simpa only [factors_values] using congrArg (List.map Prod.snd) (hkey.symm.trans he)
        exact hnot (huv ▸ hu)

end ReedSolomon.HiddenDerivative.NonzeroInterpolationMachine
