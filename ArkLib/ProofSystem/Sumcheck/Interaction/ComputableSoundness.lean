/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Interaction.Computable
public import ArkLib.ProofSystem.Sumcheck.Interaction.ProtocolSoundness

/-!
# Soundness of native Sumcheck with computable messages

The exact whole-execution interpretation transfers the mathematical native soundness bound
against every ordinary computable-message prover, including arbitrary private continuations.
-/

@[expose] public section

namespace Sumcheck.Interaction.Computable

open _root_.Interaction.Oracle OracleComp OracleSpec SingleRound MultivariateRound
open scoped ENNReal

variable (n deg : ℕ) (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
  [BEq F] [LawfulBEq F]

/-- From a false initial claim over a polynomial-realized original oracle, the probability
that the actual computable-message execution outputs a true original evaluation claim is at
most `count * deg / |F|`. The prover is an arbitrary ordinary native strategy. -/
theorem execute_soundness {m : ℕ} (D : Fin m ↪ F)
    (count start : ℕ) (finish : start + count = n) (A : PFunctor)
    (originalOracle : VirtualOracle (OracleSpec.ofPFunctor A) (polynomialFamily F n deg))
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩)
    (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    (prover : Prover.Strategy unifSpec (Computable.protocol F deg count).tree
      (Computable.protocol F deg count).roles (fun _ => Unit)) (p : Spec.OracleStatement F n deg ())
    (horiginal : originalOracle.eval impl =
      (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p))
    (hfalse : ¬ closedRelation F n deg D ⟨start, by omega⟩
      ⟨stmt, originalOracle.eval impl⟩) :
    Pr{let result ← (Computable.execute F n deg unifSpec ($ᵗ F) (Finset.univ.map D).toList
      count start finish A originalOracle stmt impl prover)}[
        result.map (Native.outputRelation F n deg) = some True] ≤
      (count : ENNReal) * deg / Fintype.card F := by
  rw [execute_eq_native]
  exact Native.execute_soundness n deg F D count start finish A originalOracle stmt impl
    (interpretProver F deg unifSpec count prover) p horiginal hfalse

/-- A false polynomial-realized initial claim is accepted by the complete executable verifier
with probability at most `count * deg / |F|`, for every native prover private-output family.
Erasing its final return value preserves the actual path and all ambient effects. -/
theorem executeWithFinalCheck_soundness {m : ℕ} (D : Fin m ↪ F)
    (domain : List F) (hdomain : domain.Perm (Finset.univ.map D).toList)
    (count start : ℕ) (finish : start + count = n) (A : PFunctor)
    (originalOracle : VirtualOracle (OracleSpec.ofPFunctor A) (polynomialFamily F n deg))
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩)
    (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    {OutP : (Computable.protocol F deg count).tree.ExecutionPath → Type}
    (prover : Prover.Strategy unifSpec (Computable.protocol F deg count).tree
      (Computable.protocol F deg count).roles OutP) (p : Spec.OracleStatement F n deg ())
    (horiginal : originalOracle.eval impl =
      (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p))
    (hfalse : ¬ closedRelation F n deg D ⟨start, by omega⟩
      ⟨stmt, originalOracle.eval impl⟩) :
    Pr{let accepted ← (Computable.executeWithFinalCheck F n deg unifSpec ($ᵗ F)
      domain count start finish A originalOracle stmt impl prover)}[
        accepted = true] ≤ (count : ENNReal) * deg / Fintype.card F := by
  unfold Computable.executeWithFinalCheck
  rw [Native.Core.executeWithFinalCheck_eq_of_domain_perm F n deg
    (Impl.Representation.Message F deg) (Impl.Representation.evaluate F deg) unifSpec
    ($ᵗ F) domain (Finset.univ.map D).toList hdomain]
  rw [Native.Core.executeWithFinalCheck_eq_execute_eraseOutput]
  simpa only [prEvent_map, Native.Core.accepts_eq_true_iff, Computable.execute,
    Native.outputRelation] using
    execute_soundness n deg F D count start finish A originalOracle stmt impl
      (Interaction.StrategyOver.TwoParty.Focal.mapOutput (fun _ _ => (() : Unit)) prover)
      p horiginal hfalse

end Sumcheck.Interaction.Computable
