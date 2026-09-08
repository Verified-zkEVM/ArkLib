/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Packing.FullFamily.Execution

/-!
# Perfect completeness of full-family packing

Honest execution is accepted for every challenge, with the same commitment oracle.
The theorem quantifies over the initial oracle-state distribution, so it also supplies the
state-aware premise at every reachable state of a larger sequential reduction.
-/

noncomputable section

namespace RingSwitching.Packing.FullFamily

open OracleSpec OracleComp ProtocolSpec MvPolynomial ProbabilityTheory

variable {B : Type} [CommRing B] (data : PackingData B) (m : ℕ)
  {C : Type} [CommRing C] [Algebra B C] [Algebra data.P C] [IsScalarTower B data.P C]
  (bat : BatchingStrategy C data.ιE) (pc : PackedCommitment data.P m)

/-- The checked full-family phase is perfectly complete for every initial oracle state. -/
theorem perfectCompleteness {σ : Type} (init : ProbComp σ)
    (impl : QueryImpl []ₒ (StateT σ ProbComp)) :
    (reduction data m bat pc).perfectCompleteness init impl
      (relIn data m pc) (relOut data m bat pc) := by
  classical
  apply Reduction.perfectCompleteness_of_run_support
  intro stmt ps hIn x hx
  rw [Reduction.run_eq_of_guarded_verifier _ (guardedForm data m bat pc)] at hx
  change x ∈ support ((prover data m bat pc).run stmt ps >>= fun r =>
    pure (if (guardedForm data m bat pc).check stmt r.1 then
      some (r, (guardedForm data m bat pc).out stmt r.1) else none)) at hx
  rw [prover_run] at hx
  simp only [bind_assoc, pure_bind, mem_support_bind_iff] at hx
  obtain ⟨c, _, hx⟩ := hx
  have hc := honest_check data m pc hIn
  simp only [guardedForm, FullTranscript.messages, FullTranscript.mk2,
    decide_eq_true_eq, hc, if_true,
    mem_support_pure_iff] at hx
  subst x
  exact ⟨_, rfl, honest_relOut data m bat pc hIn c, rfl⟩

end RingSwitching.Packing.FullFamily

end
