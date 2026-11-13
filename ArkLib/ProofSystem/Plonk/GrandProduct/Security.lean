/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Plonk.GrandProduct.Reduction

/-! # Plonk permutation grand product: fixed-prefix knowledge

Immediately after the joint challenge, knowledge asserts existence of a degree-bounded univariate
accumulator over the multiplicative evaluation domain whose three residuals vanish. Its boundary
and recurrence express `Z(1) = 1` and `Z(ωx) * Q(x) = Z(x) * N(x)` for the quotient zero test.
Its later message makes that accumulator concrete. A false initial claim can cross this challenge
only when the labeled permutation fingerprint vanishes.
-/

@[expose] public section

namespace Plonk.GrandProduct

open OracleSpec OracleComp ProtocolSpec
open scoped NNReal ENNReal ProbabilityTheory

variable {F : Type} [Field F] [DecidableEq F] {m n : ℕ}
  (ω : F) (hω : IsPrimitiveRoot ω n) (hn : 2 ≤ n)
  (cs : ConstraintSystem F m n)
  (L : CosetLabels (EvaluationDomain.primitiveRoot ω hω)) (pi : GeneratorBatch.Poly F n)
  {ι : Type} (oSpec : OracleSpec ι)

/-- All witnesses are unique after the initial wire oracles have been revealed. -/
def rbrExtractor : Extractor.RoundByRound oSpec (Unit × ∀ i, OStmtIn F n i)
    Unit Unit (pSpec F n) (fun _ => Unit) where
  extractIn _ w := w
  extractMid _ _ _ _ := ()
  extractOut _ _ _ := ()

variable [SampleableType F] {σ : Type}
  (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- The accumulator exists after the challenge and is fixed by the prover message. -/
def knowledgeStateFunction :
    (oracleVerifier ω hω hn cs L pi oSpec).toVerifier.KnowledgeStateFunction
    init impl (relIn ω hω cs pi) (relOut ω hω) (rbrExtractor (F := F) (n := n) oSpec) where
  toFun
    | 0 => fun stmt _ _ => InputRelation ω hω cs pi stmt.2
    | 1 => fun stmt tr _ => ∃ Z : GeneratorBatch.Poly F n,
        OutputRelation ω hω hn cs L pi stmt.2 (tr ⟨0, by decide⟩).1 (tr ⟨0, by decide⟩).2 Z
    | 2 => fun stmt tr _ =>
        OutputRelation ω hω hn cs L pi stmt.2
          (tr ⟨0, by decide⟩).1 (tr ⟨0, by decide⟩).2 (tr ⟨1, by decide⟩)
  toFun_empty _ _ h := h
  toFun_next := by
    intro i hi stmt tr msg w h
    fin_cases i
    · nomatch hi
    · change ∃ Z : GeneratorBatch.Poly F n,
        OutputRelation ω hω hn cs L pi stmt.2
          (tr ⟨0, by decide⟩).1 (tr ⟨0, by decide⟩).2 Z
      exact ⟨msg, h⟩
  toFun_full stmt tr _ h := by
    exact ((guardedForm ω hω hn cs L pi oSpec).check_and_of_prEvent_pos h).2

variable [Fintype F]

/-- A single joint uniform challenge hides a false copy claim with probability at most
`(3n - 1) / |F|`, for every fixed input and prefix. -/
theorem oracleVerifier_rbrKnowledgeSoundnessWith :
    (oracleVerifier ω hω hn cs L pi oSpec).toVerifier.rbrKnowledgeSoundnessWith
      init impl (relIn ω hω cs pi) (relOut ω hω) (fun _ => Unit)
      (rbrExtractor (F := F) (n := n) oSpec)
      (knowledgeStateFunction ω hω hn cs L pi oSpec init impl)
      (fun _ => ((3 * n - 1 : ℕ) : ℝ≥0) / Fintype.card F) := by
  intro stmt i tr
  obtain ⟨i, hi⟩ := i
  fin_cases i
  · change Pr{let r ← $ᵗ (F × F)}[∃ _ : Unit,
      ¬ InputRelation ω hω cs pi stmt.2 ∧
        ∃ Z : GeneratorBatch.Poly F n, OutputRelation ω hω hn cs L pi stmt.2 r.1 r.2 Z] ≤ _
    simp only [exists_const]
    by_cases hg : (EvaluationDomain.primitiveRoot ω hω).Vanishes
        (gate ω hω cs pi stmt.2).val.toPoly
    · by_cases hc : cs.CopyConstraintsSatisfied
          (polynomialOccurrences (EvaluationDomain.primitiveRoot ω hω) (wires stmt.2))
      · have hin : InputRelation ω hω cs pi stmt.2 := ⟨hg, hc⟩
        simp only [hin, not_true_eq_false, false_and, prEvent_false]
        exact bot_le
      · refine le_trans (prEvent_mono ($ᵗ (F × F)) _ _ ?_)
          (cs.prob_fingerprint_eq_zero_le L _ hc)
        rintro r ⟨_, Z, hZ⟩
        exact fingerprint_eq_zero_of_output ω hω hn cs L pi stmt.2 r.1 r.2 Z hZ
    · rw [prEvent_eq_zero_of_forall_not]
      · exact bot_le
      · rintro r ⟨_, Z, hZ⟩
        exact hg ((outputRelation_iff ω hω hn cs L pi stmt.2 r.1 r.2 Z).mp hZ).1
  · nomatch hi

/-- Existential packaging of the named fixed-prefix certificate. -/
theorem oracleVerifier_rbrKnowledgeSoundness :
    (oracleVerifier ω hω hn cs L pi oSpec).toVerifier.rbrKnowledgeSoundness
      init impl (relIn ω hω cs pi) (relOut ω hω)
      (fun _ => ((3 * n - 1 : ℕ) : ℝ≥0) / Fintype.card F) :=
  ⟨_, rbrExtractor oSpec, knowledgeStateFunction ω hω hn cs L pi oSpec init impl,
    oracleVerifier_rbrKnowledgeSoundnessWith ω hω hn cs L pi oSpec init impl⟩

end Plonk.GrandProduct
