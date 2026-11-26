/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Plonk.Assembly.Reduction

/-! # Extraction for the original Plonk circuit relation

The prepared polynomial protocol uses separate public-input coefficients. Its designated
extractor decodes the first table message into the original private variables.
-/

@[expose] public section

namespace Plonk.Assembly.Circuit

open OracleSpec OracleComp ProtocolSpec
open scoped NNReal ENNReal

variable {F : Type} [Field F] [DecidableEq F] {m n ℓ : ℕ}
  (ω : F) (hω : IsPrimitiveRoot ω (ℓ + n)) (hn : 2 ≤ ℓ + n)
  (cs : ConstraintSystem F m n) (hℓ : ℓ ≤ m) (x : Fin ℓ → F)
  (L : CosetLabels (EvaluationDomain.primitiveRoot ω hω))
  {ι : Type} (oSpec : OracleSpec ι)

/-- The polynomial protocol with public equality rows and cleared public constants. -/
def oracleReduction := Assembly.oracleReduction ω hω hn (cs.prepare hℓ (fun _ => 0)) L
  (publicInputPolynomial (EvaluationDomain.primitiveRoot ω hω) (by omega) x) oSpec

/-- The original circuit relation, retaining its public input and private suffix. -/
def relIn : Set ((Unit × ∀ i, SendWitness.OStmtIn i) × (Fin (m - ℓ) → F)) :=
  {p | Plonk.relation cs ℓ hℓ x p.2}

/-- Decode the exact polynomial table revealed at the start of the transcript. -/
def transcriptExtractor : Extractor.Straightline oSpec
    (Unit × ∀ i, SendWitness.OStmtIn i) (Fin (m - ℓ) → F) Unit
    (Assembly.pSpec ω hω hn) :=
  fun _ _ tr _ _ => pure
    (Assembly.circuitExtractor (EvaluationDomain.primitiveRoot ω hω) cs hℓ x
      (tr ⟨0, by decide⟩))

/-- Composed backward extraction followed by the computable circuit decoder. -/
def rbrExtractor : Extractor.RoundByRound oSpec
    (Unit × ∀ i, SendWitness.OStmtIn i) (Fin (m - ℓ) → F) Unit (Assembly.pSpec ω hω hn)
    (Extractor.RoundByRound.seqComposeWitMid (Wit F (ℓ + n))
      (StageWitMid (F := F) (n := ℓ + n))) :=
  let E := Assembly.rbrExtractor ω hω hn (cs.prepare hℓ (fun _ => 0)) L
    (publicInputPolynomial (EvaluationDomain.primitiveRoot ω hω) (by omega) x) oSpec
  { E with
    extractIn := fun stmt w =>
      Assembly.circuitExtractor (EvaluationDomain.primitiveRoot ω hω) cs hℓ x
        (E.extractIn stmt w) }

variable [SampleableType F] {σ : Type}
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- The composed knowledge states, with the original circuit relation at the empty prefix. -/
def knowledgeStateFunction :
    (oracleReduction ω hω hn cs hℓ x L oSpec).verifier.toVerifier.KnowledgeStateFunction
      init impl (relIn cs hℓ x)
      (Quotient.relOut (F := F) (n := ℓ + n)) (rbrExtractor ω hω hn cs hℓ x L oSpec) :=
  let K := Assembly.knowledgeStateFunction ω hω hn (cs.prepare hℓ (fun _ => 0)) L
    (publicInputPolynomial (EvaluationDomain.primitiveRoot ω hω) (by omega) x) oSpec init impl
  { K with
    toFun_empty := fun stmt w hw =>
      relation_circuitExtractor ω hω (by omega) cs hℓ x _ (K.toFun_empty stmt w hw) }

variable [Fintype F]

/-- The circuit decoder preserves the composed named fixed-prefix certificate. -/
theorem oracleVerifier_rbrKnowledgeSoundnessWith :
    (oracleReduction ω hω hn cs hℓ x L oSpec).verifier.toVerifier.rbrKnowledgeSoundnessWith
      init impl (relIn cs hℓ x)
        (Quotient.relOut (F := F) (n := ℓ + n)) _ (rbrExtractor ω hω hn cs hℓ x L oSpec)
        (knowledgeStateFunction ω hω hn cs hℓ x L oSpec init impl) (error ω hω hn) := by
  have h := Assembly.oracleVerifier_rbrKnowledgeSoundnessWith ω hω hn
    (cs.prepare hℓ (fun _ => 0)) L
    (publicInputPolynomial (EvaluationDomain.primitiveRoot ω hω) (by omega) x) oSpec init impl
  simpa only [Verifier.rbrKnowledgeSoundnessWith, knowledgeStateFunction,
    rbrExtractor, Stmt, OStmt, OracleIdx] using h

omit [SampleableType F] [Fintype F] in
/-- The ordinary circuit extractor is the backward fold of the named certificate. -/
theorem foldExtractor_eq : (rbrExtractor ω hω hn cs hℓ x L oSpec).foldExtractor =
    transcriptExtractor ω hω hn cs hℓ x oSpec := by
  rfl

/-- The revealed-table decoder extracts the original circuit witness with error
`(7(ℓ + n) - 3) / |F|`, where `ℓ + n` counts all prepared rows. -/
theorem oracleVerifier_knowledgeSoundnessWith :
    (oracleReduction ω hω hn cs hℓ x L oSpec).verifier.knowledgeSoundnessWith init impl
      (relIn cs hℓ x) (Quotient.relOut (F := F) (n := ℓ + n))
      (transcriptExtractor ω hω hn cs hℓ x oSpec)
      (((7 * (ℓ + n) - 3 : ℕ) : ℝ≥0) / Fintype.card F) := by
  have h := OracleVerifier.knowledgeSoundnessWith_of_rbrKnowledgeSoundnessWith_of_guarded
    (Assembly.guardedForm ω hω hn (cs.prepare hℓ (fun _ => 0)) L
      (publicInputPolynomial (EvaluationDomain.primitiveRoot ω hω) (by omega) x) oSpec)
    (knowledgeStateFunction ω hω hn cs hℓ x L oSpec init impl)
    (oracleVerifier_rbrKnowledgeSoundnessWith ω hω hn cs hℓ x L oSpec init impl)
  change (oracleReduction ω hω hn cs hℓ x L oSpec).verifier.knowledgeSoundnessWith init impl
    (relIn cs hℓ x) (Quotient.relOut (F := F) (n := ℓ + n))
    (rbrExtractor ω hω hn cs hℓ x L oSpec).foldExtractor (∑ i, error ω hω hn i) at h
  rw [sum_error ω hω hn, foldExtractor_eq ω hω hn cs hℓ x L oSpec] at h
  exact h

end Plonk.Assembly.Circuit
