/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.Interaction.Oracle.Execution
import ArkLib.ProofSystem.Sumcheck.Spec.SingleRound

/-!
# Typed single-round Sumcheck strategies

The oracle message is degree-refined. The verifier checks its sum by queries and obtains the
new target from the input oracle, matching the legacy `Simple.oracleVerifier` convention.
Challenges are explicit open programs; this module makes no soundness or sampling claim.
-/

namespace Sumcheck.Interaction.SingleRound

open OracleComp OracleSpec Polynomial
open _root_.Interaction.Oracle

noncomputable section

variable (R : Type) [CommSemiring R] (deg : ℕ)

/-- A degree-bounded polynomial message. -/
abbrev Message := R⦃≤ deg⦄[X]

/-- Evaluation is the entire observable interface of the refined polynomial. -/
@[reducible]
def polynomialInterface : OracleInterface (Message R deg) where
  Query := R
  toOC.spec := R →ₒ R
  toOC.impl x := do return (← read).val.eval x

/-- The input polynomial is available through evaluations. -/
abbrev inputSpec : OracleSpec R := R →ₒ R

/-- A degree-refined send followed by a public verifier challenge. -/
abbrev protocol : _root_.Interaction.Oracle.Protocol :=
  .oracleWith (Message R deg) (polynomialInterface R deg) <|
    .public .receiver R fun _ => .done

/-- The two polynomial evaluation resources available after the send. -/
abbrev access : PFunctor :=
  Access.extend (inputSpec R).toPFunctor (polynomialInterface R deg)

variable {ι : Type} (ambient : OracleSpec ι)

/-- Sum the sent polynomial's answers in the supplied domain order. -/
def sumQueries : List R → OracleComp (ambient + OracleSpec.ofPFunctor (access R deg)) R
  | [] => pure 0
  | x :: xs => do
      let y : R ← liftM
        ((ambient + OracleSpec.ofPFunctor (access R deg)).query (.inr (.inr x)))
      let ys ← sumQueries xs
      return y + ys

/-- Query-dependent terminal output; a failed sum check is an explicit rejection. -/
def terminal [DecidableEq R] (domain : List R) (target challenge : R) :
    OracleComp (ambient + OracleSpec.ofPFunctor (access R deg)) (Option (R × R)) := do
  let total ← sumQueries R deg ambient domain
  if total = target then
    let value : R ← liftM
      ((ambient + OracleSpec.ofPFunctor (access R deg)).query (.inr (.inl challenge)))
    return some (value, challenge)
  else return none

/-- The verifier receives no concrete polynomial; all polynomial use is through evaluation. -/
def verifier [DecidableEq R] (domain : List R) (target : R)
    (challenge : OracleComp (ambient + OracleSpec.ofPFunctor (access R deg)) R) :
    Verifier.Strategy ambient (protocol R deg).tree (protocol R deg).roles
      (protocol R deg).oracles (inputSpec R).toPFunctor (fun _ => Option (R × R)) := by
  change OracleComp (ambient + OracleSpec.ofPFunctor (access R deg))
    (OracleComp (ambient + OracleSpec.ofPFunctor (access R deg))
      (Σ _ : R, OracleComp (ambient + OracleSpec.ofPFunctor (access R deg))
        (Option (R × R))))
  exact pure (do
    let r ← challenge
    return ⟨r, terminal R deg ambient domain target r⟩)

/-- An honest prover sends its input polynomial and retains the evaluated output statement. -/
def prover (p : Message R deg) : Prover.Strategy ambient (protocol R deg).tree
    (protocol R deg).roles (fun _ => R × R) :=
  pure ⟨p, fun r => pure (p.val.eval r, r)⟩

/-- Honest input behavior induced by a degree-bounded polynomial. -/
def inputImpl (p : Message R deg) : QueryImpl (inputSpec R) Id := fun x => (p.val.eval x : R)

/-- Reading a list of sent evaluations computes exactly their mathematical sum. -/
theorem simulate_sumQueries (p q : Message R deg) (domain : List R) :
    simulateQ (Verifier.readImpl ambient (access R deg)
      (Access.extendImpl (inputSpec R).toPFunctor (polynomialInterface R deg)
        (inputImpl R deg p) q)) (sumQueries R deg ambient domain) =
      pure (domain.map (fun x => q.val.eval x)).sum := by
  induction domain with
  | nil => rfl
  | cons x xs ih =>
      simp only [sumQueries, simulateQ_bind, simulateQ_pure]
      change (pure (q.val.eval x) >>= fun y =>
        simulateQ (Verifier.readImpl ambient (access R deg)
          (Access.extendImpl (inputSpec R).toPFunctor (polynomialInterface R deg)
            (inputImpl R deg p) q)) (sumQueries R deg ambient xs) >>= fun ys =>
          pure (y + ys)) = _
      rw [ih]
      simp

/-- The terminal program checks the sent polynomial but evaluates the input polynomial. -/
theorem simulate_terminal [DecidableEq R] (p q : Message R deg)
    (domain : List R) (target r : R) :
    simulateQ (Verifier.readImpl ambient (access R deg)
      (Access.extendImpl (inputSpec R).toPFunctor (polynomialInterface R deg)
        (inputImpl R deg p) q)) (terminal R deg ambient domain target r) =
      pure (if (domain.map (fun x => q.val.eval x)).sum = target then
        some (p.val.eval r, r) else none) := by
  simp only [terminal, simulateQ_bind, simulate_sumQueries, pure_bind]
  split
  · change (pure (p.val.eval r) >>= fun value => pure (some (value, r))) = _
    rfl
  · rfl

/-- Execute a prescribed challenge against an arbitrary sent polynomial. -/
def executeAt [DecidableEq R] (p q : Message R deg) (domain : List R) (target r : R) :=
  executeStrategies ambient (protocol R deg).tree (protocol R deg).roles
    (protocol R deg).oracles (inputSpec R).toPFunctor (inputImpl R deg p)
    (prover R deg ambient q) (verifier R deg ambient domain target (pure r))

/-- The exported paired runner returns the checked sum and the input evaluation. -/
theorem executeAt_eq [DecidableEq R] (p q : Message R deg)
    (domain : List R) (target r : R) :
    executeAt R deg ambient p q domain target r =
      pure ⟨⟨q, r, PUnit.unit⟩, (q.val.eval r, r),
        if (domain.map (fun x => q.val.eval x)).sum = target then
          some (p.val.eval r, r) else none⟩ := by
  change (simulateQ (Verifier.readImpl ambient (access R deg)
    (Access.extendImpl (inputSpec R).toPFunctor (polynomialInterface R deg)
      (inputImpl R deg p) q)) (terminal R deg ambient domain target r) >>= fun out =>
        pure (⟨⟨q, r, PUnit.unit⟩, (q.val.eval r, r), out⟩ :
          (path : (protocol R deg).tree.ExecutionPath) × (R × R) × Option (R × R))) = _
  rw [simulate_terminal]
  rfl

/-- Honest execution succeeds at every challenge whenever the input sum claim holds. -/
theorem executeAt_honest [DecidableEq R] (p : Message R deg)
    (domain : List R) (target r : R)
    (h : (domain.map (fun x => p.val.eval x)).sum = target) :
    executeAt R deg ambient p p domain target r =
      pure ⟨⟨p, r, PUnit.unit⟩, (p.val.eval r, r), some (p.val.eval r, r)⟩ := by
  rw [executeAt_eq, if_pos h]

/-- The typed honest terminal statement satisfies the existing single-round output relation. -/
theorem honest_outputRelation (p : Message R deg) (r : R) :
    (((p.val.eval r, r), (fun _ : Unit => p)), ()) ∈
      Spec.SingleRound.Simple.outputRelation R deg := rfl

/-- The legacy input relation supplies exactly the sum condition used by this verifier. -/
theorem legacy_input_sum {m : ℕ} (D : Fin m ↪ R)
    (p : Message R deg) (target : R)
    (h : ((target, (fun _ : Unit => p)), ()) ∈
      Spec.SingleRound.Simple.inputRelation R deg D) :
    ((Finset.univ.map D).toList.map (fun x => p.val.eval x)).sum = target := by
  rw [Finset.sum_map_toList]
  exact h

end
end Sumcheck.Interaction.SingleRound
