/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Interaction.Protocol
public import VCVio.OracleComp.EvalDist.Measure

/-!
# Completeness of native Sumcheck

The honest ordinary prover sends the existing projected round polynomial and uses the actual
public challenge to select its recursive continuation. From one true initial claim and an
original oracle view realized by a polynomial of individual degree at most `deg`, every supported
native execution returns an accepted true original-oracle evaluation claim. The verifier's
challenge program is arbitrary; no intermediate relation premise is supplied by the caller.
-/

@[expose] public section

open Interaction.Oracle

namespace Sumcheck.Interaction.Native

open OracleComp OracleSpec
open SingleRound MultivariateRound

noncomputable section

variable (R : Type) [CommSemiring R] (n deg : ℕ) {m : ℕ} (D : Fin m ↪ R)
variable {ι : Type} (ambient : OracleSpec ι)

/-- Honest messages use the actual public prefix; memory lives in ordinary native continuations. -/
def honestProver : (count start : ℕ) → (finish : start + count = n) →
    Spec.StatementRound R n ⟨start, by omega⟩ → Spec.OracleStatement R n deg () →
    Prover.Strategy ambient (protocol R deg count).tree
      (protocol R deg count).roles (fun _ => Unit)
  | 0, _, _, _, _ => ()
  | count + 1, start, finish, stmt, p =>
      let q := Spec.SingleRound.projectedRoundPolynomial R n deg D ⟨start, by omega⟩
        stmt.challenges p
      pure ⟨q, fun choice => match choice with
        | none => pure ()
        | some r => pure (honestProver count (start + 1) (by omega)
            ⟨q.val.eval r, Fin.snoc stmt.challenges r⟩ p)⟩

variable [DecidableEq R]

/-- Every supported native honest execution accepts a true original-oracle evaluation claim. -/
theorem execute_support_completeness (challenge : OracleComp ambient R)
    (count start : ℕ) (finish : start + count = n) (A : PFunctor)
    (originalOracle : VirtualOracle (OracleSpec.ofPFunctor A) (polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (impl : QueryImpl (OracleSpec.ofPFunctor A) Id) (p : Spec.OracleStatement R n deg ())
    (horiginal : originalOracle.eval impl =
      (polynomialFamily R n deg).behaviorOfRealizations (fun _ => p))
    (hcurrent : closedRelation R n deg D ⟨start, by omega⟩
      ⟨stmt, originalOracle.eval impl⟩) :
    ∀ result ∈ support (execute R n deg ambient challenge (Finset.univ.map D).toList
      count start finish A originalOracle stmt impl
        (honestProver R n deg D ambient count start finish stmt p)),
      result.map (outputRelation R n deg) = some True := by
  induction count generalizing start A with
  | zero =>
    subst n
    rw [execute_zero]
    intro result hresult
    rw [support_pure] at hresult
    subst result
    have hrel := (closedRelation_last_iff R start deg D
      ⟨stmt, originalOracle.eval impl⟩).mp hcurrent
    change some (outputRelation R (start + 0) deg _) = some True
    have hprefix : stmt.challenges ∘ Fin.cast (rfl : start = start) = stmt.challenges := by
      funext j
      rfl
    simp only [outputRelation, Option.some.injEq, eq_iff_iff, iff_true]
    rw [hprefix]
    exact hrel
  | succ count ih =>
    let i : Fin n := ⟨start, by omega⟩
    let q := Spec.SingleRound.projectedRoundPolynomial R n deg D i stmt.challenges p
    have hconcrete : ((stmt, fun _ => p), ()) ∈ Spec.relationRound R n deg D i.castSucc := by
      rw [horiginal] at hcurrent
      exact hcurrent
    have hcheck : ((Finset.univ.map D).toList.map (fun x => q.val.eval x)).sum = stmt.target :=
      projected_sum_of_relationRound R n deg D i stmt p hconcrete
    rw [execute_succ]
    simp only [honestProver, pure_bind]
    dsimp only [q, i] at hcheck
    rw [ite_eq_left hcheck]
    intro result hresult
    obtain ⟨r, _, hnext⟩ := support_bind_exists hresult
    apply ih (start + 1) (by omega) (Access.extend A (polynomialInterface R deg))
      (originalOracle.sumWeaken (polynomialInterface R deg).spec)
      ⟨q.val.eval r, Fin.snoc stmt.challenges r⟩
      (Access.extendImpl A (polynomialInterface R deg) impl q)
    · rw [VirtualOracle.eval_sumWeaken_extendImpl]
      exact horiginal
    · rw [VirtualOracle.eval_sumWeaken_extendImpl, horiginal]
      exact relationRound_projected_output R n deg D i stmt p r
    · exact hnext

/-- Actual native honest execution has probability-one completeness for any challenge program. -/
theorem execute_perfectCompleteness (challenge : ProbComp R)
    (count start : ℕ) (finish : start + count = n) (A : PFunctor)
    (originalOracle : VirtualOracle (OracleSpec.ofPFunctor A) (polynomialFamily R n deg))
    (stmt : Spec.StatementRound R n ⟨start, by omega⟩)
    (impl : QueryImpl (OracleSpec.ofPFunctor A) Id) (p : Spec.OracleStatement R n deg ())
    (horiginal : originalOracle.eval impl =
      (polynomialFamily R n deg).behaviorOfRealizations (fun _ => p))
    (hcurrent : closedRelation R n deg D ⟨start, by omega⟩
      ⟨stmt, originalOracle.eval impl⟩) :
    Pr{let result ← (execute R n deg unifSpec challenge (Finset.univ.map D).toList
      count start finish A originalOracle stmt impl
        (honestProver R n deg D unifSpec count start finish stmt p))}[
        result.map (outputRelation R n deg) = some True] = 1 :=
  prEvent_eq_one_of_forall_mem_support _ _
    (execute_support_completeness R n deg D unifSpec challenge count start finish A
      originalOracle stmt impl p horiginal hcurrent)

end
end Sumcheck.Interaction.Native
