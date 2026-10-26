/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Logup.Prover.RoundCoefficients
public import ArkLib.ProofSystem.Logup.Prover.CoefficientCircuitCost
public import ArkLib.ToCompPoly.Univariate.ArithmeticNormalization

/-!
# Measured execution of direct round-message coefficients

The programs read adjacent table entries, execute the grouped coefficient circuit, stream its
rows into one padded accumulator, and canonicalize the final sum. Their deterministic erasure
is itself an executable message constructor. Selecting that constructor in the honest strategy
runs the same program whose primitive requests are profiled; output equality alone is not used
to transfer a cost claim to a separate algorithm.

Pure correctness constructors and formal projection live in `RoundCoefficients`. The measured
program returns an ordinary canonical polynomial; its execution refinement supplies the erased
degree proof in `messageByProgram`. No mathematical polynomial is constructed at runtime.
-/

@[expose] public section

open CompPoly CPolynomial CMlPolynomialEval OracleComp OracleSpec
namespace Logup.Prover.RoundCoefficients
variable {F : Type} [CommRing F] [Inv F] [DecidableEq F] {r T K : ℕ}

/-- Bind every affine table row through two endpoint reads and a certified subtraction. -/
def affineRowsProgram {m : ℕ} (tables : Vector (CMlPolynomialEval F (r + 1)) m)
    (j : Fin (2 ^ r)) : OracleComp (ArithmeticSpec F) (Vector (Raw F) m) :=
  Vector.ofFnM fun i => Subtype.val <$> affineRowProgram (tables.get i) j

/-- Each bound row has exactly two value reads and one subtraction. -/
theorem profileArithmetic_affineRowsProgram {m : ℕ}
    (tables : Vector (CMlPolynomialEval F (r + 1)) m) (j : Fin (2 ^ r)) :
    profileArithmetic (affineRowsProgram tables j) =
      (Vector.ofFn (fun i => affineRow (tables.get i) j), fun kind =>
        m * (if kind = .valueRead then 2 else if kind = .sub then 1 else 0)) := by
  apply profileArithmetic_ofFnM_uniform
  intro i
  rw [profileArithmetic_map]
  apply Prod.ext
  · exact profileArithmetic_certified_val _
  · exact profileArithmetic_affineRowProgram _ _

/-- Execute one row circuit after binding all input rows once. -/
def rowProgram (groups : Vector (List (Fin T)) K) (lambda : Vector F K)
    (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) (j : Fin (2 ^ r)) :
    OracleComp (ArithmeticSpec F) (Raw F) := do
  let d ← affineRowsProgram denominator j
  let w ← affineRowsProgram weight j
  let h ← affineRowsProgram helper j
  let b ← affineRowProgram kernel j
  CoefficientCircuit.circuitProgram groups b.val lambda d w h

/-- Executing the row program returns the pure padded row coefficients. -/
theorem profileArithmetic_rowProgram_fst (groups : Vector (List (Fin T)) K)
    (lambda : Vector F K) (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) (j : Fin (2 ^ r)) :
    (profileArithmetic (rowProgram groups lambda denominator weight helper kernel j)).1 =
      row groups lambda denominator weight helper kernel j := by
  simp only [rowProgram, profileArithmetic_bind, profileArithmetic_affineRowsProgram,
    profileArithmetic_certified_val, CoefficientCircuit.profileArithmetic_circuitProgram_fst]
  rfl

/-- Stream selected row programs into one padded accumulator using certified additions. -/
def coefficientsFromProgram (rows : List (Fin (2 ^ r)))
    (groups : Vector (List (Fin T)) K) (lambda : Vector F K)
    (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) (acc : Raw F) :
    OracleComp (ArithmeticSpec F) (Raw F) :=
  rows.foldlM (fun a j => do
    Arithmetic.tick
    let p ← rowProgram groups lambda denominator weight helper kernel j
    let next ← Arithmetic.addRaw a p
    pure next.val) acc

/-- Executing the streamed accumulation returns its explicit pure coefficient fold. -/
theorem profileArithmetic_coefficientsFromProgram_fst (rows : List (Fin (2 ^ r)))
    (groups : Vector (List (Fin T)) K) (lambda : Vector F K)
    (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) (acc : Raw F) :
    (profileArithmetic
      (coefficientsFromProgram rows groups lambda denominator weight helper kernel acc)).1 =
      coefficientsFrom rows groups lambda denominator weight helper kernel acc := by
  induction rows generalizing acc with
  | nil => rfl
  | cons j rows ih =>
    simp only [coefficientsFromProgram, List.foldlM_cons, profileArithmetic_bind,
      profileArithmetic_tick, profileArithmetic_rowProgram_fst, profileArithmetic_certified_val,
      profileArithmetic_pure]
    exact ih _

/-- Initialize an empty accumulator and execute every Boolean suffix row. -/
def coefficientsProgram (groups : Vector (List (Fin T)) K) (lambda : Vector F K)
    (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) : OracleComp (ArithmeticSpec F) (Raw F) := do
  Arithmetic.tick
  coefficientsFromProgram (List.finRange (2 ^ r)) groups lambda denominator weight helper kernel #[]

/-- Executing all rows returns the pure padded coefficient sum. -/
theorem profileArithmetic_coefficientsProgram_fst (groups : Vector (List (Fin T)) K)
    (lambda : Vector F K) (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) :
    (profileArithmetic (coefficientsProgram groups lambda denominator weight helper kernel)).1 =
      coefficients groups lambda denominator weight helper kernel := by
  simp [coefficientsProgram, coefficients, profileArithmetic_bind,
    profileArithmetic_coefficientsFromProgram_fst]

/-- Canonicalize the measured coefficient sum once and return its ordinary polynomial data. -/
def messageProgram (groups : Vector (List (Fin T)) K) (lambda : Vector F K)
    (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) : OracleComp (ArithmeticSpec F) (CPolynomial F) := do
  let raw ← coefficientsProgram groups lambda denominator weight helper kernel
  Subtype.val <$> Arithmetic.canonicalRawProgram raw

/-- The profiled program returns exactly the canonical pure coefficient sum. -/
theorem profileArithmetic_messageProgram_fst (groups : Vector (List (Fin T)) K)
    (lambda : Vector F K) (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) :
    (profileArithmetic (messageProgram groups lambda denominator weight helper kernel)).1 =
      CPolynomial.ofArray (coefficients groups lambda denominator weight helper kernel) := by
  simp only [messageProgram, profileArithmetic_bind, profileArithmetic_map,
    profileArithmetic_coefficientsProgram_fst, profileArithmetic_certified_val]

/-- Deterministic arithmetic erasure returns the same canonical coefficient data. -/
theorem simulateQ_messageProgram (groups : Vector (List (Fin T)) K) (lambda : Vector F K)
    (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) :
    simulateQ arithmeticAnswer (messageProgram groups lambda denominator weight helper kernel) =
      CPolynomial.ofArray (coefficients groups lambda denominator weight helper kernel) := by
  rw [← profileArithmetic_fst, profileArithmetic_messageProgram_fst]

/-- Execute the measured program itself and attach its erased round degree proof. -/
def messageByProgram {ell : ℕ} (groups : Vector (List (Fin T)) K)
    (hgroups : ∀ k, (groups.get k).length ≤ ell) (lambda : Vector F K)
    (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) : Sumcheck.Impl.Representation.Message F (ell + 2) :=
  let p := simulateQ arithmeticAnswer
    (messageProgram groups lambda denominator weight helper kernel)
  ⟨p, by
    have hp := simulateQ_messageProgram groups lambda denominator weight helper kernel
    change p = (message (r := r) groups hgroups lambda denominator weight helper kernel).val at hp
    rw [hp]
    exact (message (r := r) groups hgroups lambda denominator weight helper kernel).property⟩

/-- The executing measured constructor has the pure specification message as its value. -/
theorem messageByProgram_eq_message {ell : ℕ} (groups : Vector (List (Fin T)) K)
    (hgroups : ∀ k, (groups.get k).length ≤ ell) (lambda : Vector F K)
    (denominator weight : Vector (CMlPolynomialEval F (r + 1)) T)
    (helper : Vector (CMlPolynomialEval F (r + 1)) K)
    (kernel : CMlPolynomialEval F (r + 1)) :
    messageByProgram groups hgroups lambda denominator weight helper kernel =
      message (r := r) groups hgroups lambda denominator weight helper kernel := by
  apply Subtype.ext
  exact simulateQ_messageProgram groups lambda denominator weight helper kernel

end Logup.Prover.RoundCoefficients
