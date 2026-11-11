/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Plonk.GrandProduct.Reduction
public import ArkLib.OracleReduction.Composition.Sequential.GuardedCompleteness

/-! # Plonk permutation grand product: completeness

The honest prover uses one joint challenge and interpolates a univariate accumulator over the
multiplicative evaluation domain. Its boundary and recurrence residuals encode `Z(1) = 1` and
`Z(ωx) * Q(x) = Z(x) * N(x)` for the quotient zero test. The residuals vanish outside the explicit
zero-denominator-factor bad set, giving completeness error at most `3n / |F|`.
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

/-- The honest transcript contains the joint challenge and its computed accumulator. -/
def honestTranscript (a : Fin 3 → GeneratorBatch.Poly F n) (r : F × F) :
    (pSpec F n).FullTranscript :=
  ((default : (pSpec F n).Transcript 0).concat (m := (0 : Fin 2)) r).concat
    (m := (1 : Fin 2)) (honestAccumulator ω hω hn cs L a r.1 r.2)

/-- The honest transcript starts with its joint challenge. -/
@[simp]
theorem honestTranscript_zero (a : Fin 3 → GeneratorBatch.Poly F n) (r : F × F) :
    honestTranscript ω hω hn cs L a r 0 = r := rfl

/-- The honest transcript ends with its computed accumulator. -/
@[simp]
theorem honestTranscript_one (a : Fin 3 → GeneratorBatch.Poly F n) (r : F × F) :
    honestTranscript ω hω hn cs L a r 1 =
      honestAccumulator ω hω hn cs L a r.1 r.2 := rfl

/-- The actual honest prover run samples one joint challenge and sends its accumulator. -/
theorem oracleProver_run (stmt : Unit × ∀ i, OStmtIn F n i) (wit : Unit) :
    (oracleProver ω hω hn cs L pi oSpec).run stmt wit = (do
      let r ← liftComp ((pSpec F n).getChallenge ⟨0, rfl⟩)
        (oSpec + [(pSpec F n).Challenge]ₒ'challengeOracleInterface)
      pure (honestTranscript ω hω hn cs L stmt.2 r,
        (output ω hω hn cs L pi stmt.2 r
          (honestAccumulator ω hω hn cs L stmt.2 r.1 r.2), ()))) := by
  simp [Prover.run, Prover.runToRound, Fin.induction, Fin.induction.go,
    Prover.processRound, oracleProver, ProtocolSpec.getChallenge, Fin.vcons, Fin.dcons,
    honestTranscript, output]
  rfl

variable [SampleableType F]
  {σ : Type} (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))

/-- Simulating the honest run preserves ambient state and samples a joint field pair. -/
theorem simulateQ_oracleProver_run (stmt : Unit × ∀ i, OStmtIn F n i) (wit : Unit)
    (s : σ) :
    (simulateQ (impl.addLift challengeQueryImpl : QueryImpl _ (StateT σ ProbComp))
      ((oracleProver ω hω hn cs L pi oSpec).run stmt wit)).run s = (do
        let r ← $ᵗ (F × F)
        pure ((honestTranscript ω hω hn cs L stmt.2 r,
          (output ω hω hn cs L pi stmt.2 r
            (honestAccumulator ω hω hn cs L stmt.2 r.1 r.2), ())), s)) := by
  rw [oracleProver_run, simulateQ_bind,
    simulateQ_addLift_challengeQueryImpl_getChallenge]
  simp [simulateQ_pure]
  rfl

variable [Fintype F]

/-- The honest Plonk permutation grand product reduction is complete with error at most `3n / |F|`,
for every ambient oracle implementation and initialization distribution. -/
theorem oracleReduction_completeness :
    (oracleReduction ω hω hn cs L pi oSpec).completeness init impl
      (relIn ω hω cs pi) (relOut ω hω)
      (((3 * n : ℕ) : ℝ≥0) / Fintype.card F) := by
  rw [OracleReduction.completeness]
  apply Reduction.completeness_of_guarded_states _ (guardedForm ω hω hn cs L pi oSpec)
  intro s
  rw [Reduction.completeness_iff_of_guarded_verifier _
    (guardedForm ω hω hn cs L pi oSpec)]
  intro stmt wit hstmt
  simp only [pure_bind, OracleReduction.toReduction, oracleReduction,
    simulateQ_oracleProver_run]
  simp only [bind_pure_comp, prEvent_map]
  simp only [guardedForm, honestTranscript_zero, honestTranscript_one,
    true_and, output, relOut, Set.mem_ofPred_eq, outputOracles]
  have hbad := Plonk.prob_badChallenge_le (EvaluationDomain.primitiveRoot ω hω)
    (wires stmt.2)
    (permutationPolynomials (EvaluationDomain.primitiveRoot ω hω) cs L.label)
  have hgood := tsub_le_tsub_left hbad (1 : ℝ≥0∞)
  rw [← prEvent_not_eq_one_sub] at hgood
  refine hgood.trans (prEvent_mono _ _ _ ?_)
  intro r hr
  exact ⟨honest_outputRelation ω hω hn cs L pi stmt.2 hstmt r.1 r.2 hr, trivial⟩

end Plonk.GrandProduct
