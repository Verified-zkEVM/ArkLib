/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/

import ArkLib.ProofSystem.Component.QuotientZeroTest
import Mathlib.Algebra.Field.ZMod
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Algebra.Group.Subgroup.Finite

/-!
# Finite-domain quotient zero tests over a small prime field

The honest nodal polynomial is accepted, whereas the constant one polynomial fails at a
point of the domain. These checks also instantiate the uniform error and subgroup evaluator.
-/

open CompPoly FiniteDomainQuotient OracleComp OracleSpec
open scoped NNReal ENNReal ProbabilityTheory

namespace ArkLibTest.QuotientZeroTest

instance : Fact (Nat.Prime 5) := ⟨by decide⟩

private abbrev F := ZMod 5

private instance : DecidablePred (· ∈ (⊤ : Subgroup Fˣ)) := fun _ => isTrue trivial

private def points : Finset F := {0, 1}

private def domain : _root_.QuotientZeroTest.Domain F :=
  _root_.QuotientZeroTest.finiteDomain F points

private def honestPolynomial : Poly F 2 :=
  ⟨nodal points, by rw [nodal_toPoly, Lagrange.natDegree_nodal]; decide⟩

private def falsePolynomial : Poly F 2 :=
  ⟨CPolynomial.C 1, by simp⟩

private def zeroQuotient : Poly F (2 - points.card) :=
  ⟨0, by simp⟩

private def honestStatement : Unit × ∀ i, _root_.QuotientZeroTest.OStmtIn F 2 i :=
  ((), fun _ => honestPolynomial)

private def falseStatement : Unit × ∀ i, _root_.QuotientZeroTest.OStmtIn F 2 i :=
  ((), fun _ => falsePolynomial)

private def honestTranscript : (_root_.QuotientZeroTest.pSpec F domain 2).FullTranscript :=
  fun | ⟨0, _⟩ => quotient points honestPolynomial
      | ⟨1, _⟩ => (2 : F)

private def falseTranscript : (_root_.QuotientZeroTest.pSpec F domain 2).FullTranscript :=
  fun | ⟨0, _⟩ => zeroQuotient
      | ⟨1, _⟩ => (0 : F)

example : eval (quotient points honestPolynomial) (2 : F) = 1 := by decide +kernel

example : _root_.QuotientZeroTest.check F domain 2 honestStatement honestTranscript := by
  decide +kernel

example : ¬ _root_.QuotientZeroTest.check F domain 2 falseStatement falseTranscript := by
  decide +kernel

run_cmd do
  unless eval (quotient points honestPolynomial) (2 : F) == 1 do
    throwError "The honest quotient must be constant one."
  unless decide (_root_.QuotientZeroTest.check F domain 2 honestStatement honestTranscript) do
    throwError "The honest quotient identity was rejected."
  if decide (_root_.QuotientZeroTest.check F domain 2 falseStatement falseTranscript) then
    throwError "A nonzero domain value was accepted."

example {ι : Type} (oSpec : OracleSpec ι) :
    (_root_.QuotientZeroTest.oracleVerifier F domain 2 oSpec).toVerifier.verify
      honestStatement honestTranscript = pure ((), Empty.elim) := by
  rw [_root_.QuotientZeroTest.oracleVerifier_toVerifier, ite_eq_left (by decide +kernel)]

example {ι : Type} (oSpec : OracleSpec ι) :
    (_root_.QuotientZeroTest.oracleVerifier F domain 2 oSpec).toVerifier.verify
      falseStatement falseTranscript = failure := by
  rw [_root_.QuotientZeroTest.oracleVerifier_toVerifier, ite_eq_right (by decide +kernel)]

example :
    Pr{let z ← $ᵗ F}[eval falsePolynomial z =
      eval zeroQuotient z * domain.evalNodal z] ≤ (2 : ℝ≥0∞) / 5 := by
  have hfalse : ¬ Polynomial.ZeroOn points falsePolynomial.val.toPoly := by
    intro h
    have hzero := h 0 (by decide)
    simp [falsePolynomial] at hzero
  have hbound := Polynomial.prob_eval_eq_mul_nodal_le (S := points) (d := 2)
    (by decide) hfalse falsePolynomial.property zeroQuotient.property
  have hpoints : domain.points = points := rfl
  simpa only [eval_eq, domain.evalNodal_eq, hpoints, ZMod.card, Nat.cast_ofNat] using hbound

example {ι σ : Type} (oSpec : OracleSpec ι) (init : ProbComp σ)
    (impl : QueryImpl oSpec (StateT σ ProbComp)) :
    (_root_.QuotientZeroTest.oracleVerifier F domain 2 oSpec).toVerifier
      |>.rbrKnowledgeSoundness init impl (_root_.QuotientZeroTest.relIn F domain 2)
        _root_.QuotientZeroTest.relOut (fun _ => (2 : ℝ≥0) / 5) := by
  simpa [F] using
    _root_.QuotientZeroTest.oracleVerifier_rbrKnowledgeSoundness
      F domain 2 oSpec init impl (by decide)

example (z : F) :
    (_root_.QuotientZeroTest.subgroupDomain F (⊤ : Subgroup Fˣ)).evalNodal z = z ^ 4 - 1 := by
  simp [_root_.QuotientZeroTest.subgroupDomain, F, Nat.totient_prime (by decide : Nat.Prime 5)]

run_cmd do
  unless (_root_.QuotientZeroTest.subgroupDomain F (⊤ : Subgroup Fˣ)).evalNodal 2 == 0 do
    throwError "Subgroup powering must vanish at a nonzero field element."

end ArkLibTest.QuotientZeroTest
