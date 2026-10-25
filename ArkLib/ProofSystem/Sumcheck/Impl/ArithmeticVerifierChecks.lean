/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Sumcheck.Impl.VerifierChecks
public import ArkLib.ToCompPoly.Univariate.ArithmeticHorner

/-!
# Arithmetic interpretation of native verifier check kernels

These programs execute the same local sum/comparison control selected by native Sumcheck.
Reader programs retain their actual request profiles, including duplicates in the domain. The
sum charges every addition, including the last addition to zero; equality charges one comparison.
Source backends, Boolean branching and natural-number control are separate from these E requests.
-/

@[expose] public section

namespace Sumcheck.Impl.VerifierChecks
open CompPoly OracleComp OracleSpec
variable {R : Type} [Zero R] [Add R] [Sub R] [Mul R] [Inv R] [DecidableEq R]

/-- Interpret the shared domain sum with an actual reader and existing addition requests. -/
def sumProgram (read : R → OracleComp (ArithmeticSpec R) R) (domain : List R) :
    OracleComp (ArithmeticSpec R) R :=
  sumM read (fun a b => Subtype.val <$> Arithmetic.add a b) domain

/-- Interpret the shared single comparison with the existing certified equality request. -/
def equalProgram (left right : R) : OracleComp (ArithmeticSpec R) Bool :=
  equalM (fun a b => Subtype.val <$> Arithmetic.eq a b) left right

/-- The domain's actual reader costs plus one addition for every listed point. -/
def sumCost (domain : List R) (readerCost : R → ArithmeticCost) : ArithmeticCost :=
  fun kind => ((domain.map readerCost).sum) kind + if kind = .add then domain.length else 0

/-- Erasure preserves the actual reader interpretations in the same summation driver. -/
theorem simulateQ_sumProgram (read : R → OracleComp (ArithmeticSpec R) R) (domain : List R) :
    simulateQ arithmeticAnswer (sumProgram read domain) =
      (sumM (m := Id) (fun x => simulateQ arithmeticAnswer (read x))
        (fun a b => a + b) domain).run := by
  have hadd (a b : R) :
      simulateQ arithmeticAnswer (Subtype.val <$> Arithmetic.add a b) = a + b := by
    rw [simulateQ_map]
    exact (simulateQ arithmeticAnswer (Arithmetic.add a b)).property
  unfold sumProgram
  induction domain with
  | nil => rfl
  | cons x xs ih =>
    simp only [sumM, simulateQ_bind, ih, hadd]
    rfl

/-- Exact cost of the actual sum driver, including arbitrary repeated reader requests. -/
theorem profileArithmetic_sumProgram (read : R → OracleComp (ArithmeticSpec R) R)
    (values : R → R) (readerCost : R → ArithmeticCost) (domain : List R)
    (hread : ∀ x ∈ domain, profileArithmetic (read x) = (values x, readerCost x)) :
    profileArithmetic (sumProgram read domain) =
      ((sumM (m := Id) values (fun a b => a + b) domain).run, sumCost domain readerCost) := by
  unfold sumProgram
  induction domain with
  | nil =>
    simp only [sumM, profileArithmetic_pure]
    apply Prod.ext
    · rfl
    · funext kind
      simp [sumCost]
  | cons x xs ih =>
    simp only [sumM, profileArithmetic_bind, profileArithmetic_map, profileArithmetic_add]
    rw [hread x (by simp)]
    dsimp only
    rw [ih (fun y hy => hread y (by simp [hy]))]
    apply Prod.ext
    · rfl
    · funext kind
      cases kind <;> simp [sumCost, arithmeticCost, ArithmeticOp.costKind]
      omega

/-- Arithmetic comparison erases to the same ordinary equality decision. -/
theorem simulateQ_equalProgram (left right : R) :
    simulateQ arithmeticAnswer (equalProgram left right) = decide (left = right) := by
  rw [equalProgram, equalM, simulateQ_map]
  exact (simulateQ arithmeticAnswer (Arithmetic.eq left right)).property

/-- A comparison requests exactly one E equality operation and no other primitive. -/
theorem profileArithmetic_equalProgram (left right : R) :
    profileArithmetic (equalProgram left right) =
      (decide (left = right), fun kind => if kind = .eq then 1 else 0) := by
  simp only [equalProgram, equalM, profileArithmetic_map, profileArithmetic_eq]
  apply Prod.ext
  · rfl
  · funext kind
    rfl

end Sumcheck.Impl.VerifierChecks
