/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Interaction.StateRestorationEvaluation
public import ArkLib.Interaction.Oracle.Security.StateRestorationRandomizedKnowledge

/-!
# Native Sumcheck soundness from actual randomized state restoration

An adaptive adversary chooses an input and degree-bounded round messages while interleaving
private coins and restoration-oracle calls. Completion samples the missing field challenges in
the same cache. The acceptance event evaluates the existing aborting native Sumcheck runner on
those very challenges and keeps the original virtual oracle behavior in its closed output.

The `Unit` certificate is an ordinary truth predicate. It supplies no substantive knowledge
extraction claim. Its local degree bound and exact native replay law yield an expected fresh-query
bound, and an actual cached adversary-phase cap yields the familiar `(Q + k) * deg / |F|` form.
-/

@[expose] public section

open Interaction Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec
open scoped ENNReal

namespace Sumcheck.Interaction.Restoration

open SingleRound MultivariateRound
open Interaction.Oracle.Security.StateRestoration

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
variable (k deg : ℕ)

/-- The local field-error bound, including `deg = 0`. -/
noncomputable def fieldError : ENNReal := (deg : ENNReal) / Fintype.card F

omit [DecidableEq F] in
/-- The fixed restoration presentation has exactly `k` field challenges. -/
theorem rounds_length : (rounds F deg k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [rounds, ih]

/-- A constant error vector gives the same challenge schedule as the certificate's schedule. -/
theorem roundErrorSchedule_const (rs : List Security.StateRestoration.Round) (ε : ENNReal) :
    roundErrorSchedule rs (fun _ => ε) = uniformSchedule ε rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
      simp only [roundErrorSchedule, uniformSchedule]
      funext message
      congr 1
      funext challenge
      exact ih

omit [DecidableEq F] in
/-- The certificate's authored-prefix bound in the round-error vector form used by the
randomized restoration theorem. This includes every failed-check prefix. -/
theorem certificate_bounded_constant {m : ℕ} (D : Fin m ↪ F)
    (p : Spec.OracleStatement F k deg ())
    (stmt : Spec.StatementRound F k ⟨0, by omega⟩) :
    (certificate F k deg D p k 0 (by omega) stmt True).IsLocallyBounded
      (Security.StateRestoration.protocol (rounds F deg k)).roles
      (roundErrorSchedule (rounds F deg k) (fun _ => fieldError F deg)) := by
  rw [roundErrorSchedule_const]
  exact certificate_locallyBounded F k deg D p k 0 (by omega) stmt True

omit [DecidableEq F] in
/-- The fixed-round cost is at most `(Q + k)` local errors, even when `k = 0` and the
maximum over rounds is zero. No cancellation of `ENNReal` zero or infinity is used. -/
theorem constant_round_budget_le (Q : ℕ) :
    (Q : ENNReal) * Finset.univ.sup
        (fun _ : Fin (rounds F deg k).length => fieldError F deg) +
      (∑ _ : Fin (rounds F deg k).length, fieldError F deg) ≤
        (Q + k : ℕ) * fieldError F deg := by
  have hmax : Finset.univ.sup
      (fun _ : Fin (rounds F deg k).length => fieldError F deg) ≤ fieldError F deg := by
    apply Finset.sup_le
    intro i hi
    exact le_rfl
  have hsum : (∑ _ : Fin (rounds F deg k).length, fieldError F deg) =
      (k : ENNReal) * fieldError F deg := by
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin,
      rounds_length]
  calc
    _ ≤ (Q : ENNReal) * fieldError F deg +
          (∑ _ : Fin (rounds F deg k).length, fieldError F deg) := by
      gcongr
    _ = (Q + k : ℕ) * fieldError F deg := by
      rw [hsum, Nat.cast_add, add_mul]

omit [DecidableEq F] in
/-- The same constant-round simplification with an arbitrary expected adversary count. -/
theorem constant_round_expected_budget_le (count : ENNReal) :
    Finset.univ.sup
        (fun _ : Fin (rounds F deg k).length => fieldError F deg) * count +
      (∑ _ : Fin (rounds F deg k).length, fieldError F deg) ≤
        fieldError F deg * count + (k : ENNReal) * fieldError F deg := by
  have hmax : Finset.univ.sup
      (fun _ : Fin (rounds F deg k).length => fieldError F deg) ≤ fieldError F deg := by
    apply Finset.sup_le
    intro i hi
    exact le_rfl
  have hsum : (∑ _ : Fin (rounds F deg k).length, fieldError F deg) =
      (k : ENNReal) * fieldError F deg := by
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fin,
      rounds_length]
  rw [hsum]
  gcongr

variable {Input Salt : Type} [DecidableEq Input] [DecidableEq Salt]
variable {m : ℕ} (D : Fin m ↪ F)
variable (A : PFunctor)
variable (stmt : Input → Spec.StatementRound F k ⟨0, by omega⟩)
variable (p : Input → Spec.OracleStatement F k deg ())
variable (originalOracle : Input →
  VirtualOracle (OracleSpec.ofPFunctor A) (polynomialFamily F k deg))
variable (impl : Input → QueryImpl (OracleSpec.ofPFunctor A) Id)

/-- Truth of the initially selected closed Sumcheck claim. -/
def initialClaimTrue (z : Input) : Prop :=
  closedRelation F k deg D ⟨0, by omega⟩
    ⟨stmt z, (polynomialFamily F k deg).behaviorOfRealizations (fun _ => p z)⟩

omit [Fintype F] [DecidableEq F] [SampleableType F] [DecidableEq Input] in
/-- The initial certificate predicate is precisely truth of the selected original claim. -/
theorem initial_certificate_holds_iff (z : Input) (w : Unit) :
    (claimState F k deg D ⟨0, by omega⟩ (stmt z) (p z) True).holds w ↔
      initialClaimTrue F k deg D stmt p z := by
  simp [claimState, initialClaimTrue]

/-- Run the actual aborting native Sumcheck verifier on one completed restoration path. -/
noncomputable def nativeObservedOutput (z : Input)
    (path : (Security.StateRestoration.protocol (rounds F deg k)).tree.ExecutionPath) :
    Option (ClosedClaim (Native.FinalStatement F k) (polynomialFamily F k deg)) :=
  nativeReplayOutput F k deg D k 0 (by omega) A (originalOracle z) (stmt z) (impl z) path

omit [DecidableEq Input] in
/-- The proved deterministic native replay equation supplies the terminal output law.
No probabilistic correspondence is assumed. -/
theorem terminal_certificate_holds_iff_native
    (sourceLaw : ∀ z, (originalOracle z).eval (impl z) =
      (polynomialFamily F k deg).behaviorOfRealizations (fun _ => p z))
    (z : Input)
    (path : (Security.StateRestoration.protocol (rounds F deg k)).tree.ExecutionPath)
    (w : Unit) :
    ((certificate F k deg D (p z) k 0 (by omega) (stmt z) True).terminalState path).holds
      (terminalWitnessEquiv F k deg D (p z) k 0 (by omega) (stmt z) True path w) ↔
    ∃ output, nativeObservedOutput F k deg D A stmt originalOracle impl z path =
      some output ∧ Native.outputRelation F k deg output := by
  simpa only [nativeObservedOutput, true_and] using
    terminal_holds_iff_native F k deg D (p z) k 0 (by omega) A
      (originalOracle z) (stmt z) (impl z) (sourceLaw z) True path w

/-- Source-only native replay game. Its output contains the actual closed claim, if accepted. -/
noncomputable def nativeRestorationGame
    (adversary : RandomizedRestorationAdversary Input Salt Unit (rounds F deg k)) :
    OracleComp (unifSpec + oracleSpec Input Salt (rounds F deg k))
      (Option ((_ : Input) ×
        (_ : (Security.StateRestoration.protocol (rounds F deg k)).tree.ExecutionPath) ×
        Option (ClosedClaim (Native.FinalStatement F k) (polynomialFamily F k deg)) × Unit)) :=
  (fun result => result.map fun outcome =>
    (⟨outcome.1, outcome.2.1,
      nativeObservedOutput F k deg D A stmt originalOracle impl outcome.1 outcome.2.1,
      outcome.2.2⟩ :
      (_ : Input) ×
        (_ : (Security.StateRestoration.protocol (rounds F deg k)).tree.ExecutionPath) ×
        Option (ClosedClaim (Native.FinalStatement F k) (polynomialFamily F k deg)) × Unit)) <$>
    randomizedRestoredExecution (rounds F deg k) adversary

/-- A false selected initial claim with a successful, true native closed output. Rejection and
adversary failure both make this event false. -/
def nativeFalseAccepts :
    Option ((_ : Input) ×
      (_ : (Security.StateRestoration.protocol (rounds F deg k)).tree.ExecutionPath) ×
      Option (ClosedClaim (Native.FinalStatement F k) (polynomialFamily F k deg)) × Unit) → Prop
  | none => False
  | some ⟨z, _, output, _⟩ =>
      ¬ initialClaimTrue F k deg D stmt p z ∧
        ∃ claim, output = some claim ∧ Native.outputRelation F k deg claim

omit [DecidableEq Input] [DecidableEq Salt] in
/-- The native replay game is exactly the source-log erasure of the owner-level joint game.
This equation retains the original source-only execution; it assumes no probability bridge. -/
theorem nativeRestorationGame_eq_observedErase
    (adversary : RandomizedRestorationAdversary Input Salt Unit (rounds F deg k)) :
    nativeRestorationGame F k deg D A stmt originalOracle impl adversary =
      Prod.fst <$> randomizedObservedGameWithAdversaryLog
        (fun _ _ => Option (ClosedClaim (Native.FinalStatement F k)
          (polynomialFamily F k deg)))
        (nativeObservedOutput F k deg D A stmt originalOracle impl) adversary := by
  exact (randomizedObservedGameWithAdversaryLog_erase
    (fun _ _ => Option (ClosedClaim (Native.FinalStatement F k)
      (polynomialFamily F k deg)))
    (nativeObservedOutput F k deg D A stmt originalOracle impl) adversary).symm

/-- The actual native cached output marginal equals the instrumented joint output marginal. -/
theorem nativeRestorationGame_marginal
    (adversary : RandomizedRestorationAdversary Input Salt Unit (rounds F deg k)) :
    (simulateQ (oracleSpec Input Salt (rounds F deg k)).romImpl
      (nativeRestorationGame F k deg D A stmt originalOracle impl adversary)).run' ∅ =
    (fun joint => joint.1.1.1) <$>
      randomOracleLoggedRun
        (randomizedObservedGameWithAdversaryLog
          (fun _ _ => Option (ClosedClaim (Native.FinalStatement F k)
            (polynomialFamily F k deg)))
          (nativeObservedOutput F k deg D A stmt originalOracle impl) adversary) ∅ := by
  rw [nativeRestorationGame_eq_observedErase]
  exact (randomizedObservedGame_actual_marginal
    (fun _ _ => Option (ClosedClaim (Native.FinalStatement F k)
      (polynomialFamily F k deg)))
    (nativeObservedOutput F k deg D A stmt originalOracle impl) adversary).symm

/-- The false-acceptance event has the same probability on the exact logged joint run. -/
theorem nativeRestorationGame_falseAccept_event
    (adversary : RandomizedRestorationAdversary Input Salt Unit (rounds F deg k)) :
    Pr{let result ← (simulateQ (oracleSpec Input Salt (rounds F deg k)).romImpl
      (nativeRestorationGame F k deg D A stmt originalOracle impl adversary)).run' ∅}[
      nativeFalseAccepts F k deg D stmt p result] =
    Pr{let joint ← (randomOracleLoggedRun
      (randomizedObservedGameWithAdversaryLog
        (fun _ _ => Option (ClosedClaim (Native.FinalStatement F k)
          (polynomialFamily F k deg)))
        (nativeObservedOutput F k deg D A stmt originalOracle impl) adversary) ∅)}[
      nativeFalseAccepts F k deg D stmt p joint.1.1.1] := by
  rw [nativeRestorationGame_marginal]
  exact prEvent_map _ _ _

omit [DecidableEq F] [DecidableEq Input] in
/-- The owner relation event specializes to ordinary Sumcheck false-claim acceptance.
Its generic witness argument is `Unit` and carries no extra condition. -/
theorem nativeFalseAccepts_iff_ownerEvent
    (result : Option ((_ : Input) ×
      (_ : (Security.StateRestoration.protocol (rounds F deg k)).tree.ExecutionPath) ×
      Option (ClosedClaim (Native.FinalStatement F k) (polynomialFamily F k deg)) × Unit)) :
    nativeFalseAccepts F k deg D stmt p result ↔
      badObservedRelation
        (fun _ _ => Option (ClosedClaim (Native.FinalStatement F k)
          (polynomialFamily F k deg)))
        (fun z => claimState F k deg D ⟨0, by omega⟩ (stmt z) (p z) True)
        (fun z => certificate F k deg D (p z) k 0 (by omega) (stmt z) True)
        (fun z _ => initialClaimTrue F k deg D stmt p z)
        (fun _ _ output _ => ∃ claim, output = some claim ∧ Native.outputRelation F k deg claim)
        (fun z path => terminalWitnessEquiv F k deg D (p z) k 0 (by omega)
          (stmt z) True path)
        Set.univ result := by
  cases result with
  | none => rfl
  | some data =>
      rcases data with ⟨z, path, output, witness⟩
      simp [nativeFalseAccepts, badObservedRelation, and_comm]

/-- False acceptance of the actual native replay is charged to distinct restoration keys in
the same cached execution. The second bound counts the actual adversary phase, including
branches on which the adversary returns no transcript. -/
theorem nativeRestoration_expected_soundness
    (sourceLaw : ∀ z, (originalOracle z).eval (impl z) =
      (polynomialFamily F k deg).behaviorOfRealizations (fun _ => p z))
    (adversary : RandomizedRestorationAdversary Input Salt Unit (rounds F deg k)) :
    Pr{let result ← (simulateQ (oracleSpec Input Salt (rounds F deg k)).romImpl
      (nativeRestorationGame F k deg D A stmt originalOracle impl adversary)).run' ∅}[
        nativeFalseAccepts F k deg D stmt p result] ≤
      expectedFreshQueryCharge
        (randomizedObservedGameWithAdversaryLog
          (fun _ _ => Option (ClosedClaim (Native.FinalStatement F k)
            (polynomialFamily F k deg)))
          (nativeObservedOutput F k deg D A stmt originalOracle impl) adversary)
        (keyError (fun _ : Fin (rounds F deg k).length => fieldError F deg)) ∧
    expectedFreshQueryCharge
        (randomizedObservedGameWithAdversaryLog
          (fun _ _ => Option (ClosedClaim (Native.FinalStatement F k)
            (polynomialFamily F k deg)))
          (nativeObservedOutput F k deg D A stmt originalOracle impl) adversary)
        (keyError (fun _ : Fin (rounds F deg k).length => fieldError F deg)) ≤
      fieldError F deg * expectedAdversaryFreshKeys (rounds F deg k) adversary +
        (k : ENNReal) * fieldError F deg := by
  let Out := fun (_ : Input)
      (_ : (Security.StateRestoration.protocol (rounds F deg k)).tree.ExecutionPath) =>
    Option (ClosedClaim (Native.FinalStatement F k) (polynomialFamily F k deg))
  let observe := nativeObservedOutput F k deg D A stmt originalOracle impl
  let state := fun z => claimState F k deg D ⟨0, by omega⟩ (stmt z) (p z) True
  let extractor := fun z => certificate F k deg D (p z) k 0 (by omega) (stmt z) True
  let Rin := fun z (_ : Unit) => initialClaimTrue F k deg D stmt p z
  let Rout := fun (_ : Input)
      (_ : (Security.StateRestoration.protocol (rounds F deg k)).tree.ExecutionPath)
      (output : Option (ClosedClaim (Native.FinalStatement F k) (polynomialFamily F k deg)))
      (_ : Unit) =>
    ∃ claim, output = some claim ∧ Native.outputRelation F k deg claim
  let terminalWitness := fun z path =>
    terminalWitnessEquiv F k deg D (p z) k 0 (by omega) (stmt z) True path
  have howner := randomizedObserved_badRelation_le_expectedFreshCharge
    (rounds F deg k) (fun _ => fieldError F deg) adversary Out observe
    state extractor Set.univ
    (by intro z _; exact certificate_preserving F k deg D (p z) k 0 (by omega) (stmt z) True)
    (by intro z _; exact certificate_bounded_constant F k deg D (p z) (stmt z))
    Rin Rout terminalWitness
    (by intro z w; exact initial_certificate_holds_iff F k deg D stmt p z w)
    (by intro z path w
        exact terminal_certificate_holds_iff_native F k deg D A stmt p originalOracle impl
          sourceLaw z path w)
  constructor
  · rw [nativeRestorationGame_falseAccept_event]
    have hevent := prEvent_congr
      (randomOracleLoggedRun
        (randomizedObservedGameWithAdversaryLog Out observe adversary) ∅)
      (fun joint => nativeFalseAccepts F k deg D stmt p joint.1.1.1)
      (fun joint => badObservedRelation Out state extractor Rin Rout terminalWitness
        Set.univ joint.1.1.1)
      (fun joint => nativeFalseAccepts_iff_ownerEvent F k deg D stmt p joint.1.1.1)
    exact hevent.le.trans howner
  · exact (expectedObservedFreshCharge_le_actualAdversary
      (rounds F deg k) (fun _ => fieldError F deg) adversary Out observe).trans
        (constant_round_expected_budget_le F k deg
          (expectedAdversaryFreshKeys (rounds F deg k) adversary))

/-- A cap on distinct keys in the actual cached adversary phase gives the standard native
Sumcheck false-acceptance bound. The cap includes failed selections; `k = 0` and `deg = 0`
are covered by the same `ENNReal` statement. -/
theorem nativeRestoration_queryBound_soundness
    (sourceLaw : ∀ z, (originalOracle z).eval (impl z) =
      (polynomialFamily F k deg).behaviorOfRealizations (fun _ => p z))
    (adversary : RandomizedRestorationAdversary Input Salt Unit (rounds F deg k))
    (Q : ℕ)
    (actualQueryBound : ∀ phase ∈ support (randomOracleLoggedRun adversary.withQueryLog ∅),
      (freshKeysOfLog phase.1.2).card ≤ Q) :
    Pr{let result ← (simulateQ (oracleSpec Input Salt (rounds F deg k)).romImpl
      (nativeRestorationGame F k deg D A stmt originalOracle impl adversary)).run' ∅}[
        nativeFalseAccepts F k deg D stmt p result] ≤
      (Q + k : ℕ) * fieldError F deg := by
  have h := nativeRestoration_expected_soundness F k deg D A stmt p originalOracle impl
    sourceLaw adversary
  have hQ : expectedAdversaryFreshKeys (rounds F deg k) adversary ≤ Q :=
    expectedAdversaryFreshKeys_le_queryBound (rounds F deg k) adversary Q actualQueryBound
  calc
    _ ≤ fieldError F deg * expectedAdversaryFreshKeys (rounds F deg k) adversary +
          (k : ENNReal) * fieldError F deg := h.1.trans h.2
    _ ≤ fieldError F deg * (Q : ENNReal) + (k : ENNReal) * fieldError F deg := by
      gcongr
    _ = (Q + k : ℕ) * fieldError F deg := by
      rw [mul_comm (fieldError F deg) (Q : ENNReal), ← add_mul, Nat.cast_add]

end Sumcheck.Interaction.Restoration
