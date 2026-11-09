/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import ArkLib.ProofSystem.Sumcheck.Core.Computable
import Mathlib.Algebra.Field.ZMod

/-!
# Compiled computable Sumcheck checks

The sent polynomials are CompPoly coefficient arrays and the input polynomial is a CompPoly
multivariate polynomial. These checks run `Sumcheck.Core.Computable.verifier` against ordinary
provers and observe their effects, the challenge draws, rejection, and the output oracle data. The
challenge handlers answer a fixed value; they are deterministic test fixtures, not randomness
generators.
-/

namespace SumcheckRuntime

open OracleComp OracleSpec PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens
open Sumcheck.Core.Computable

abbrev F := ZMod 17

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- Construct a two-coefficient array, trimming a zero leading coefficient. -/
def affine (a b : F) : Sumcheck.Impl.Representation.Message F 1 :=
  ⟨CompPoly.CPolynomial.ofArray #[b, a], by
    have hsize := CompPoly.CPolynomial.Raw.Trim.size_le_size (#[b, a] : Array F)
    change (CompPoly.CPolynomial.ofArray #[b, a]).val.size ≤ 2 at hsize
    generalize h : (CompPoly.CPolynomial.ofArray #[b, a]).val.size = size at *
    cases size with
    | zero => simp [CompPoly.CPolynomial.degree, h]
    | succ size =>
        simp only [CompPoly.CPolynomial.degree, h]
        exact_mod_cast (show size ≤ 1 by omega)⟩

abbrev events : OracleSpec (Fin 4) := Fin 4 →ₒ F

def event (i : Fin 4) : OracleComp events F := liftM (events.query i)

/-- A logged effect: a prover event `.inl i`, or the `j`-th challenge draw `.inr j`. -/
abbrev Entry := Fin 4 ⊕ ℕ

attribute [local implicit_reducible] FreeM.replicate Node.position challengeSpec

/-- The challenge at every node of the computable protocol is the fixed value `x`. -/
def constChallenge {deg : ℕ} (x : F) : (k : ℕ) →
    (c : ChallengeNode oracleSig (protocol F deg k)) → challengeSpec oracleSig _ c
  | 0, ⟨n, _⟩ => nomatch n
  | _ + 1, ⟨.inl _, h⟩ => nomatch h
  | _ + 1, ⟨.inr ⟨_, .inl _⟩, _⟩ => x
  | k + 1, ⟨.inr ⟨_, .inr ⟨_, c⟩⟩, h⟩ => constChallenge x k ⟨c, h⟩

/-- Answer every challenge with `x`, logging the draw with its position among the draws. -/
def draw {deg : ℕ} (x : F) (k : ℕ) :
    QueryImpl (challengeSpec oracleSig (protocol F deg k)) (StateM (List Entry)) := fun c => do
  modify fun log => log ++ [.inr (log.countP Sum.isRight)]
  return constChallenge x k c

/-- Answer the prover's events from a fixed table, logging each event. -/
def record : QueryImpl events (StateM (List Entry)) := fun i => do
  modify fun log => log ++ [.inl i]
  return ![7, 3, 5, 11] i

/-- The second round sends a message built from both private samples and the first challenge;
its sample is drawn after that challenge, and a last event runs after the second challenge. -/
def lastProver (a r : F) : Prover oracleSig events (protocol F 1 1) (fun _ => Unit) :=
  (do
    let b ← event 2
    return ⟨affine (b + a) (a * r + 1), pure fun _ => (do
      let _ ← event 3
      return () : OracleComp events Unit)⟩ :
    OracleComp events ((_ : Sumcheck.Impl.Representation.Message F 1) ×
      OracleComp events ((_ : F) → OracleComp events Unit)))

/-- Private memory is captured in the continuation, with effects on both sides of a challenge. -/
def adaptive : Prover oracleSig events (protocol F 1 2) (fun _ => Unit) :=
  (do
    let a ← event 0
    return ⟨affine a 1, pure fun r => lastProver a r⟩ :
    OracleComp events ((_ : Sumcheck.Impl.Representation.Message F 1) ×
      OracleComp events ((_ : F) → Prover oracleSig events (protocol F 1 1) (fun _ => Unit))))

theorem zero_degree : ∀ j, (0 : CPoly.CMvPolynomial 2 F).degreeOf j ≤ 1 := by
  intro j
  rw [congrFun (CPoly.degreeOf_equiv (S := F) (p := 0)) j]
  change (CPoly.polyRingEquiv (n := 2) (R := F) 0).degreeOf j ≤ 1
  simp

/-- The output oracle data of the adaptive runs: the zero polynomial. -/
def original : ∀ _ : Unit, Input F 1 2 := fun _ => ⟨0, zero_degree⟩

def initial : Sumcheck.Spec.StatementRound F 2 0 := ⟨1, Fin.elim0⟩

/-- The domain `{0}`. -/
def zeroDomain : Fin 1 ↪ F := ⟨fun _ => 0, fun a b _ => Subsingleton.elim a b⟩

/-- The empty domain: every first-round sum is `0`, so the first check fails. -/
def emptyDomain : Fin 0 ↪ F := ⟨Fin.elim0, fun a => a.elim0⟩

/-- Read the target, both accepted challenges and the output oracle at the accepted point. -/
def readVerdict (v : Option (Sumcheck.Spec.StatementRound F 2 (Fin.last 2) × F)) :
    Option (F × F × F × F) :=
  v.map fun v => (v.1.target, v.1.challenges ⟨0, by decide⟩, v.1.challenges ⟨1, by decide⟩, v.2)

/-- Run the adaptive prover with challenges `3` and observe the verdict and the effect log. -/
def adaptiveObserve {d : ℕ} (D : Fin d ↪ F) : Option (F × F × F × F) × List Entry :=
  (simulateQ (QueryImpl.add record (draw 3 2))
    ((fun obs => readVerdict (observe obs)) <$>
      (verifier F 1 2 D events).run initial original adaptive)).run []

def check (label : String) (ok : Unit → Bool) : IO Unit := do
  unless ok () do throw (IO.userError s!"Sumcheck runtime check failed: {label}")
  IO.println s!"ok: {label}"

def runChecks : IO Unit := do
  check "Horner evaluation, including trimmed zero leading coefficient" fun _ =>
    Sumcheck.Impl.Representation.evaluate F 1 (affine 7 1) 3 == 5 &&
    Sumcheck.Impl.Representation.evaluate F 1 (affine 0 4) 9 == 4
  check "two rounds preserve private memory and effect order" fun _ =>
    adaptiveObserve zeroDomain ==
      (some (7, 3, 3, 0), [.inl 0, .inr 0, .inl 2, .inr 1, .inl 3])
  check "a failed first check still runs every round" fun _ =>
    adaptiveObserve emptyDomain == (none, [.inl 0, .inr 0, .inl 2, .inr 1, .inl 3])

/-- A directly constructed polynomial `x² + 3xy + 2y² + 5`. -/
def quadratic : CPoly.CMvPolynomial 2 F :=
  let x := CPoly.CMvPolynomial.X (0 : Fin 2)
  let y := CPoly.CMvPolynomial.X (1 : Fin 2)
  x ^ 2 + CPoly.CMvPolynomial.C 3 * x * y + CPoly.CMvPolynomial.C 2 * y ^ 2 +
    CPoly.CMvPolynomial.C 5

theorem quadratic_degree : ∀ j, quadratic.degreeOf j ≤ 2 := by
  intro j
  rw [congrFun (CPoly.degreeOf_equiv (S := F) (p := quadratic)) j]
  change (CPoly.polyRingEquiv (n := 2) (R := F) quadratic).degreeOf j ≤ 2
  simp only [quadratic, map_add, map_mul, map_pow, CPoly.coe_polyRingEquiv,
    CPoly.CMvPolynomial.fromCMvPolynomial_X, CPoly.CMvPolynomial.fromCMvPolynomial_C]
  have hx : (MvPolynomial.X (0 : Fin 2) : MvPolynomial (Fin 2) F).degreeOf j ≤ 1 := by
    simp only [MvPolynomial.degreeOf_X]
    split <;> omega
  have hy : (MvPolynomial.X (1 : Fin 2) : MvPolynomial (Fin 2) F).degreeOf j ≤ 1 := by
    simp only [MvPolynomial.degreeOf_X]
    split <;> omega
  refine (MvPolynomial.degreeOf_add_le j _ _).trans (max_le ?_ ?_)
  · refine (MvPolynomial.degreeOf_add_le j _ _).trans (max_le ?_ ?_)
    · refine (MvPolynomial.degreeOf_add_le j _ _).trans (max_le ?_ ?_)
      · exact (MvPolynomial.degreeOf_pow_le j _ 2).trans (by omega)
      · refine (MvPolynomial.degreeOf_mul_le j _ _).trans ?_
        have hcx := (MvPolynomial.degreeOf_C_mul_le _ j (3 : F)).trans hx
        omega
    · exact (MvPolynomial.degreeOf_C_mul_le _ j (2 : F)).trans
        ((MvPolynomial.degreeOf_pow_le j _ 2).trans (by omega))
  · simp

def three : Fin 3 ↪ F := ⟨fun i => (i.val : F), by decide⟩

/-- The input data of the honest runs: the quadratic. -/
def quadraticInput : Input F 2 2 := ⟨quadratic, quadratic_degree⟩

def quadraticInitial : Sumcheck.Spec.StatementRound F 2 0 := ⟨15, Fin.elim0⟩

/-- Run the computable honest prover with challenges `4`; the log records the challenge draws. -/
def quadraticObserve : Option (F × F × F × F) × List Entry :=
  (simulateQ (QueryImpl.add record (draw 4 2))
    ((fun obs => readVerdict (observe obs)) <$>
      (verifier F 2 2 three events).run quadraticInitial (fun _ => quadraticInput)
        (honestProver three quadraticInitial fun _ => quadraticInput))).run []

def quadraticFinal : Sumcheck.Spec.StatementRound F 2 (Fin.last 2) := ⟨16, ![4, 4]⟩

/-- The honest prover state after both rounds. -/
def finalState : RoundState F 2 0 := ⟨Fin.last 2, rfl, quadraticFinal⟩

/-- Run the computable honest prover for zero rounds from the final round state, against a
sampler that logs every draw, and read the output statement and the output oracle at its point. -/
def quadraticZeroObserve : (F × F × F × F) × List Entry :=
  ((fun x => let out := x.2.1.1
      (out.1.target, out.1.challenges ⟨0, by decide⟩, out.1.challenges ⟨1, by decide⟩,
        (out.2 ()).val.eval out.1.challenges)) <$>
    Interaction.TwoParty.Lens.run (protocol F 2 0)
      (honestFrom (m := StateM (List Entry)) three quadraticInput 0 finalState)
      (sampler oracleSig (protocol F 2 0) (draw 4 0))).run []

/-- The total sum `117`, first-round value `109`, and final value `101`, reduced modulo `17`,
are calculated independently of the projection implementation. -/
def quadraticChecks : IO Unit := do
  check "direct multivariate quadratic and cross term" fun _ =>
    (([0, 1, 2] : List F).map fun x =>
      (([0, 1, 2] : List F).map fun y => quadratic.eval ![x, y]).sum).sum == 15 &&
    quadratic.eval ![4, 4] == 16 &&
    (Sumcheck.Impl.Computable.projectedMessage three (0 : Fin 2) Fin.elim0 quadratic
      quadratic_degree).val.evalHorner 4 == 7
  check "honest computable two rounds and retained computational input" fun _ =>
    quadraticObserve == (some (16, 4, 4, 16), [.inr 0, .inr 1])
  check "zero rounds from the final state retain the computational input without sampling"
    fun _ => quadraticZeroObserve == ((16, 4, 4, 16), [])

end SumcheckRuntime

def main : IO Unit := do
  SumcheckRuntime.runChecks
  SumcheckRuntime.quadraticChecks
