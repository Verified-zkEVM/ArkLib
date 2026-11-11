/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.IntervalCompleteness

/-! # Statement-dependent challenge programs for honest intervals

The handler keeps the honest current claim as shared state. It can choose each challenge from
the current round, target and complete prefix, with no finite-sampling assumption on the ring.
-/

@[expose] public section

namespace Sumcheck.Core
open Polynomial MvPolynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens
  Interaction.Oracle OracleComp OracleSpec
variable {R : Type} [CommSemiring R] [DecidableEq R] {deg n d : ℕ}

omit [DecidableEq R] in
/-- Every challenge node of the fixed Sumcheck tree has coefficient type `R`. -/
theorem protocol_challengeRange : ∀ (k : ℕ) (c : ChallengeNode oracleSig (protocol R deg k)),
    challengeSpec oracleSig (protocol R deg k) c = R
  | 0, ⟨node, _⟩ => nomatch node
  | _ + 1, ⟨.inl _, h⟩ => nomatch h
  | _ + 1, ⟨.inr ⟨_, .inl _⟩, _⟩ => rfl
  | k + 1, ⟨.inr ⟨_, .inr ⟨_, c⟩⟩, h⟩ => protocol_challengeRange k ⟨c, h⟩

/-- Shared challenge memory stores the remaining count and its current public claim. -/
abbrev IntervalMemory (R : Type) (n : ℕ) (stop : Fin (n + 1)) :=
  (k : ℕ) × IntervalClaim R n stop k

/-- Answer every actual draw with the supplied current-statement challenge program and update
shared memory with the honest successor claim. -/
noncomputable def intervalAdaptiveDraw (D : Fin d → R) (p : R⦃≤ deg⦄[X Fin n])
    {stop : Fin (n + 1)} (count : ℕ)
    (challenges : (i : Fin n) → RoundStatement R n i.castSucc → ProbComp R) :
    QueryImpl (challengeSpec oracleSig (protocol R deg count))
      (StateT (IntervalMemory R n stop) ProbComp) := fun c memory =>
  match memory with
  | ⟨0, _⟩ => pure (cast (protocol_challengeRange count c).symm 0, memory)
  | ⟨k + 1, st⟩ => do
      let r ← challenges st.index st.statement
      pure (cast (protocol_challengeRange count c).symm r, ⟨k, intervalNext D p k st r⟩)

/-- Perfect completeness includes every current-statement challenge program from the arbitrary
interval interface, implemented by the actual native challenge oracle. -/
theorem intervalVerifier_adaptive_perfectCompleteness (D : Fin d → R)
    (p : R⦃≤ deg⦄[X Fin n]) {ι : Type} (ambient : OracleSpec ι)
    (start count : ℕ) (bound : start + count ≤ n)
    (impl : QueryImpl ambient (StateT (IntervalMemory R n ⟨count + start, by omega⟩) ProbComp))
    (stmt : RoundStatement R n ⟨start, by omega⟩)
    (challenges : (i : Fin n) → RoundStatement R n i.castSucc → ProbComp R)
    (h : indexedRelation D _ stmt p) :
    Pr{let result ← (intervalExperiment
      (pure (⟨count, intervalInitial start count bound stmt⟩ :
        IntervalMemory R n ⟨count + start, by omega⟩))
      (QueryImpl.addLift impl
        (intervalAdaptiveDraw (stop := ⟨count + start, by omega⟩) D p count challenges))
      ((intervalVerifier R deg n D ambient start count bound).run stmt (fun _ => p)
        (intervalProver D p count (intervalInitial start count bound stmt))))}[
      ∃ t, result.2.2 = some (t, fun _ => p) ∧ indexedRelation D _ t p] = 1 :=
  intervalVerifier_perfectCompleteness D p ambient _ start count bound _ stmt h

end Sumcheck.Core
