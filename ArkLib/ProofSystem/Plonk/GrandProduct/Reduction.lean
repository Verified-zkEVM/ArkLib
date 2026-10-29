/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Plonk.GrandProduct.Data
public import ArkLib.ProofSystem.Component.GeneratorBatch

/-! # Plonk permutation grand product: oracle reduction

The univariate accumulator polynomial `Z` over the multiplicative evaluation domain satisfies
`Z(1) = 1` and `Z(ωx) * Q(x) = Z(x) * N(x)`. One joint field-pair challenge precedes its
degree-bounded message. The output retains all wire and accumulator oracles and exposes the gate,
recurrence and boundary as virtual polynomials for the quotient zero test. Only evaluations of the
retained oracles are available to the verifier. The multilinear (GKR-style) grand-product argument
is a different protocol and is not formalized here.
-/

@[expose] public section

namespace Plonk.GrandProduct

open OracleSpec OracleComp OracleQuery ProtocolSpec CompPoly
open scoped NNReal ENNReal ProbabilityTheory BigOperators

variable (F : Type) [Field F] [DecidableEq F] (n : ℕ)

/-- A single joint challenge followed by the accumulator polynomial. -/
@[reducible] def pSpec : ProtocolSpec 2 :=
  ⟨!v[.V_to_P, .P_to_V], !v[F × F, GeneratorBatch.Poly F n]⟩

instance : ∀ i, OracleInterface ((pSpec F n).Message i)
  | ⟨0, h⟩ => nomatch h
  | ⟨1, _⟩ => inferInstanceAs (OracleInterface (GeneratorBatch.Poly F n))

instance [SampleableType F] : ∀ i, SampleableType ((pSpec F n).Challenge i)
  | ⟨0, _⟩ => inferInstanceAs (SampleableType (F × F))
  | ⟨1, h⟩ => nomatch h

/-- Three wire polynomials, fixed before the challenge. -/
abbrev OStmtIn := fun _ : Fin 3 => GeneratorBatch.Poly F n

/-- Retained wires, the accumulator, and the three derived residuals. -/
abbrev OStmtOut : Fin 3 ⊕ (Unit ⊕ Fin 3) → Type :=
  Sum.elim (OStmtIn F n)
    (Sum.elim (fun _ => GeneratorBatch.Poly F n)
      (fun _ => GeneratorBatch.Poly F (residualDegree n + 1)))

instance : ∀ i, OracleInterface (OStmtOut F n i)
  | .inl _ => inferInstanceAs (OracleInterface (GeneratorBatch.Poly F n))
  | .inr (.inl _) => inferInstanceAs (OracleInterface (GeneratorBatch.Poly F n))
  | .inr (.inr _) => inferInstanceAs
      (OracleInterface (GeneratorBatch.Poly F (residualDegree n + 1)))

variable {F n} {m : ℕ} (ω : F) (hω : IsPrimitiveRoot ω n) (hn : 2 ≤ n)
  (cs : ConstraintSystem F m n)
  (L : CosetLabels (EvaluationDomain.primitiveRoot ω hω)) (pi : GeneratorBatch.Poly F n)

/-- Materialized residuals share their underlying retained wire and accumulator data. -/
def outputOracles (a : Fin 3 → GeneratorBatch.Poly F n) (r : F × F)
    (Z : GeneratorBatch.Poly F n) : ∀ i, OStmtOut F n i
  | .inl c => a c
  | .inr (.inl _) => Z
  | .inr (.inr j) => residuals ω hω hn cs L pi a r.1 r.2 Z j

/-- The verifier records the joint challenge alongside its output oracles. -/
def output (a : Fin 3 → GeneratorBatch.Poly F n) (r : F × F) (Z : GeneratorBatch.Poly F n) :=
  (r, outputOracles ω hω hn cs L pi a r Z)

/-- The initial claim includes the gate equation and copy constraints. -/
def relIn : Set ((Unit × ∀ i, OStmtIn F n i) × Unit) :=
  {x | InputRelation ω hω cs pi x.1.2}

/-- All three virtual residuals vanish on the row domain. -/
def relOut : Set (((F × F) × ∀ i, OStmtOut F n i) × Unit) :=
  {x | ∀ j, (EvaluationDomain.primitiveRoot ω hω).Vanishes
    (x.1.2 (.inr (.inr j))).val.toPoly}

variable {ι : Type} (oSpec : OracleSpec ι)

/-- Query one retained wire at one point. -/
def queryWire (c : Fin 3) (z : F) :
    OracleComp (oSpec + ([OStmtIn F n]ₒ + [(pSpec F n).Message]ₒ)) F :=
  liftM <| OracleSpec.query
    (show (oSpec + ([OStmtIn F n]ₒ + [(pSpec F n).Message]ₒ)).Domain from
      .inr (.inl ⟨c, z⟩))

/-- Query the accumulator message at one point. -/
def queryAccumulator (z : F) :
    OracleComp (oSpec + ([OStmtIn F n]ₒ + [(pSpec F n).Message]ₒ)) F :=
  liftM <| OracleSpec.query
    (show (oSpec + ([OStmtIn F n]ₒ + [(pSpec F n).Message]ₒ)).Domain from
      .inr (.inr ⟨⟨1, rfl⟩, z⟩))

omit [DecidableEq F] in
/-- Wire simulation evaluates exactly the requested coefficient array. -/
theorem simulateQ_queryWire (a : ∀ i, OStmtIn F n i)
    (messages : (pSpec F n).Messages) (c : Fin 3) (z : F) :
    simulateQ (OracleInterface.simOracle2 oSpec a messages) (queryWire oSpec c z) =
      pure (CPolynomial.evalHorner z (a c).val) := rfl

omit [DecidableEq F] in
/-- Message simulation evaluates exactly the retained accumulator. -/
theorem simulateQ_queryAccumulator (a : ∀ i, OStmtIn F n i)
    (messages : (pSpec F n).Messages) (z : F) :
    simulateQ (OracleInterface.simOracle2 oSpec a messages)
      (queryAccumulator (n := n) oSpec z) =
      pure (CPolynomial.evalHorner z (messages ⟨1, rfl⟩).val) := rfl

/-- Evaluate a virtual residual using only wire and accumulator evaluations. -/
def queryResidual (r : F × F) (j : Fin 3) (z : F) :
    OracleComp (oSpec + ([OStmtIn F n]ₒ + [(pSpec F n).Message]ₒ)) F := do
  let a ← queryWire (n := n) oSpec 0 z
  let b ← queryWire (n := n) oSpec 1 z
  let c ← queryWire (n := n) oSpec 2 z
  let v ← queryAccumulator (n := n) oSpec z
  let vnext ← queryAccumulator (n := n) oSpec (ω * z)
  let q := Computable.selectorPolynomials (EvaluationDomain.primitiveRoot ω hω) cs
  let s := Computable.permutationPolynomials (EvaluationDomain.primitiveRoot ω hω) cs L.label
  let values : Fin 3 → F := ![a, b, c]
  return ![
    q.qL.evalHorner z * a + q.qR.evalHorner z * b + q.qO.evalHorner z * c +
      q.qM.evalHorner z * (a * b) + q.qC.evalHorner z + pi.val.evalHorner z,
    vnext * (∏ i, (values i + r.1 * (s i).evalHorner z + r.2)) -
      v * (∏ i, (values i + r.1 * L.multiplier i * z + r.2)),
    (Computable.interpolate (EvaluationDomain.primitiveRoot ω hω)
      (fun i => if i = ⟨0, by omega⟩ then 1 else 0)).evalHorner z * (v - 1)] j

/-- Every virtual residual query agrees with its materialized polynomial. -/
theorem simulateQ_queryResidual (a : ∀ i, OStmtIn F n i)
    (messages : (pSpec F n).Messages) (r : F × F) (j : Fin 3) (z : F) :
    simulateQ (OracleInterface.simOracle2 oSpec a messages)
      (queryResidual ω hω hn cs L pi oSpec r j z) =
      pure (CPolynomial.evalHorner z
        (residuals ω hω hn cs L pi a r.1 r.2 (messages ⟨1, rfl⟩) j).val) := by
  simp only [queryResidual, simulateQ_bind, simulateQ_queryWire,
    simulateQ_queryAccumulator, pure_bind, simulateQ_pure]
  fin_cases j <;> simp [residuals, eval_gate, eval_recurrence, eval_boundary,
    eval_numerator, eval_denominator, Fin.prod_univ_succ]

/-- Query-by-query implementation of the retained and virtual output oracles. -/
def outputSimulation : OracleOutputSimulation oSpec (OStmtIn F n) (OStmtOut F n)
    (pSpec F n) where
  materializeOutput chals a messages :=
    outputOracles ω hω hn cs L pi a (chals ⟨0, rfl⟩) (messages ⟨1, rfl⟩)
  simulateOutputQuery chals
    | ⟨.inl c, z⟩ => queryWire oSpec c z
    | ⟨.inr (.inl _), z⟩ => queryAccumulator oSpec z
    | ⟨.inr (.inr j), z⟩ => queryResidual ω hω hn cs L pi oSpec (chals ⟨0, rfl⟩) j z
  simulateOutputQuery_eq chals a messages
    | ⟨.inl c, z⟩ => simulateQ_queryWire oSpec a messages c z
    | ⟨.inr (.inl _), z⟩ => simulateQ_queryAccumulator oSpec a messages z
    | ⟨.inr (.inr j), z⟩ =>
        simulateQ_queryResidual ω hω hn cs L pi oSpec a messages (chals ⟨0, rfl⟩) j z

/-- Forward the joint challenge and expose the derived residual oracles. -/
def oracleVerifier : OracleVerifier oSpec Unit (OStmtIn F n)
    (F × F) (OStmtOut F n) (pSpec F n) where
  verify _ chals := pure (chals ⟨0, rfl⟩)
  outputOracle := .inr (outputSimulation ω hω hn cs L pi oSpec)

/-- Materialization retains the challenge, wires, accumulator and their exact residuals. -/
theorem oracleVerifier_toVerifier (stmt : Unit × ∀ i, OStmtIn F n i)
    (tr : (pSpec F n).FullTranscript) :
    (oracleVerifier ω hω hn cs L pi oSpec).toVerifier.verify stmt tr =
      pure (output ω hω hn cs L pi stmt.2 (tr 0) (tr 1)) := by
  simp only [OracleVerifier.toVerifier, oracleVerifier, outputSimulation]
  erw [simulateQ_optionT_pure]
  rfl

/-- The Plonk permutation grand product stage forwards without a runtime guard. -/
def guardedForm : (oracleVerifier ω hω hn cs L pi oSpec).toVerifier.GuardedForm where
  check _ _ := true
  out stmt tr := output ω hω hn cs L pi stmt.2 (tr 0) (tr 1)
  verify_eq stmt tr := oracleVerifier_toVerifier ω hω hn cs L pi oSpec stmt tr

/-- The honest prover interpolates ratio prefixes, including its total zero-factor fallback. -/
def oracleProver : OracleProver oSpec Unit (OStmtIn F n) Unit
    (F × F) (OStmtOut F n) Unit (pSpec F n) where
  PrvState _ := (Fin 3 → GeneratorBatch.Poly F n) × (F × F)
  input x := (x.1.2, (0, 0))
  sendMessage
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun s => pure (honestAccumulator ω hω hn cs L s.1 s.2.1 s.2.2, s)
  receiveChallenge
    | ⟨0, _⟩ => fun s => pure (fun r => (s.1, r))
    | ⟨1, h⟩ => nomatch h
  output s := pure (output ω hω hn cs L pi s.1 s.2
    (honestAccumulator ω hω hn cs L s.1 s.2.1 s.2.2), ())

instance : (oracleProver ω hω hn cs L pi oSpec).OutputIsPure := ⟨_, fun _ => rfl⟩

/-- The joint-challenge Plonk permutation grand product oracle reduction. -/
def oracleReduction : OracleReduction oSpec Unit (OStmtIn F n) Unit
    (F × F) (OStmtOut F n) Unit (pSpec F n) :=
  ⟨oracleProver ω hω hn cs L pi oSpec, oracleVerifier ω hω hn cs L pi oSpec⟩

end Plonk.GrandProduct
