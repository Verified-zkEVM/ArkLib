/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Interaction.Computable
public import ArkLib.ProofSystem.Sumcheck.Interaction.ProtocolCompleteness
public import ArkLib.ProofSystem.Sumcheck.Impl.Projection

/-!
# Completeness of computable native Sumcheck

The ordinary honest prover computes its messages directly from a CompPoly multivariate polynomial.
Its continuation stores the actual public challenge prefix. Mathematical polynomial interpretation
is used only to prove that its complete execution equals the existing native honest execution,
including termination and the public abort branch.
-/

@[expose] public section

open Interaction.Oracle

namespace Sumcheck.Interaction.Computable

open OracleComp OracleSpec CPoly
open SingleRound MultivariateRound
open Impl.Representation Impl.Computable

variable (R : Type) [CommSemiring R] [BEq R] [LawfulBEq R] [Nontrivial R]
  (n deg : ℕ) {m : ℕ} (D : Fin m ↪ R)
variable {ι : Type} (ambient : OracleSpec ι)

/-- Compute each honest round message from the original computational polynomial. Prior challenges
are retained in the ordinary native continuation; a public abort terminates that continuation. -/
def honestProver : (count start : ℕ) → (finish : start + count = n) →
    Spec.StatementRound R n ⟨start, by omega⟩ →
    (poly : CMvPolynomial n R) → (∀ j, poly.degreeOf j ≤ deg) →
    Prover.Strategy ambient (protocol R deg count).tree
      (protocol R deg count).roles (fun _ => Unit)
  | 0, _, _, _, _, _ => ()
  | count + 1, start, finish, stmt, poly, hpoly =>
      let q := projectedMessage D ⟨start, by omega⟩ stmt.challenges poly hpoly
      pure ⟨q, fun choice => match choice with
        | none => pure ()
        | some r => pure (honestProver count (start + 1) (by omega)
            ⟨evaluate R deg q r, Fin.snoc stmt.challenges r⟩ poly hpoly)⟩

/-- The whole computational honest strategy interprets to the existing native honest strategy. -/
theorem interpretProver_honestProver (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (poly : CMvPolynomial n R) (hpoly : ∀ j, poly.degreeOf j ≤ deg) :
    interpretProver R deg ambient count
      (honestProver R n deg D ambient count start finish stmt poly hpoly) =
      Native.honestProver R n deg D ambient count start finish stmt
        (toOracleStatement poly hpoly) := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih =>
    simp only [honestProver, interpretProver, Native.Core.transportProver,
      Native.honestProver, pure_bind]
    rw [projectedMessage_toMessage]
    congr 1
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      funext choice
      cases choice with
      | none => rfl
      | some r =>
        change (pure _ >>= fun next => pure (interpretProver R deg ambient count next)) = pure _
        simp only [pure_bind, projectedMessage_evaluate]
        congr 1
        exact ih (start + 1) (by omega) _

variable [DecidableEq R]

/-- The actual computational honest execution equals the mathematical native honest execution.
The retained original oracle and its deterministic source handler are unchanged by this bridge. -/
theorem execute_honestProver_eq_native (challenge : OracleComp ambient R) (domain : List R)
    (count start : ℕ) (finish : start + count = n) (A : PFunctor)
    (originalOracle : VirtualOracle (OracleSpec.ofPFunctor A) (polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    (poly : CMvPolynomial n R) (hpoly : ∀ j, poly.degreeOf j ≤ deg) :
    execute R n deg ambient challenge domain count start finish A originalOracle stmt impl
      (honestProver R n deg D ambient count start finish stmt poly hpoly) =
      Native.execute R n deg ambient challenge domain count start finish A originalOracle stmt impl
        (Native.honestProver R n deg D ambient count start finish stmt
          (toOracleStatement poly hpoly)) := by
  rw [execute_eq_native, interpretProver_honestProver]

/-- Every supported actual honest execution accepts a true retained-original evaluation claim. -/
theorem execute_support_completeness (challenge : OracleComp ambient R)
    (count start : ℕ) (finish : start + count = n) (A : PFunctor)
    (originalOracle : VirtualOracle (OracleSpec.ofPFunctor A) (polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    (poly : CMvPolynomial n R) (hpoly : ∀ j, poly.degreeOf j ≤ deg)
    (horiginal : originalOracle.eval impl =
      (polynomialFamily R n deg).behaviorOfRealizations
        (fun _ => toOracleStatement poly hpoly))
    (hcurrent : closedRelation R n deg D ⟨start, by omega⟩
      ⟨stmt, originalOracle.eval impl⟩) :
    ∀ result ∈ support (execute R n deg ambient challenge (Finset.univ.map D).toList
      count start finish A originalOracle stmt impl
        (honestProver R n deg D ambient count start finish stmt poly hpoly)),
      result.map (Native.outputRelation R n deg) = some True := by
  rw [execute_honestProver_eq_native]
  exact Native.execute_support_completeness R n deg D ambient challenge count start finish A
    originalOracle stmt impl (toOracleStatement poly hpoly) horiginal hcurrent

/-- For any normalized challenge program, actual computational honest execution is perfectly
complete from a true initial claim and the retained computational polynomial's interpretation. -/
theorem execute_perfectCompleteness (challenge : ProbComp R)
    (count start : ℕ) (finish : start + count = n) (A : PFunctor)
    (originalOracle : VirtualOracle (OracleSpec.ofPFunctor A) (polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (impl : QueryImpl (OracleSpec.ofPFunctor A) Id)
    (poly : CMvPolynomial n R) (hpoly : ∀ j, poly.degreeOf j ≤ deg)
    (horiginal : originalOracle.eval impl =
      (polynomialFamily R n deg).behaviorOfRealizations
        (fun _ => toOracleStatement poly hpoly))
    (hcurrent : closedRelation R n deg D ⟨start, by omega⟩
      ⟨stmt, originalOracle.eval impl⟩) :
    Pr{let result ← (execute R n deg unifSpec challenge (Finset.univ.map D).toList
      count start finish A originalOracle stmt impl
        (honestProver R n deg D unifSpec count start finish stmt poly hpoly))}[
        result.map (Native.outputRelation R n deg) = some True] = 1 := by
  rw [execute_honestProver_eq_native]
  exact Native.execute_perfectCompleteness R n deg D challenge count start finish A
    originalOracle stmt impl (toOracleStatement poly hpoly) horiginal hcurrent

end Sumcheck.Interaction.Computable
