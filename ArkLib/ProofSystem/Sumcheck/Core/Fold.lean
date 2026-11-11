/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.Interpreted

/-! # Passive folds of round checks

Each check queries only its round polynomial. The verifier runs every interaction before
checking the messages in order, and keeps the input oracle as its output oracle.
-/

@[expose] public section

universe uI wI

namespace Sumcheck.Core
open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec

variable {R : Type} [CommSemiring R] {deg : ℕ}

/-- The result of a round check answered by its message polynomial. -/
noncomputable def roundVerdict {S T : Type} (check : S → R →
    OptionT (OracleComp (R →ₒ R)) T) (stmt : S) (msg : R⦃≤ deg⦄[X]) (r : R) : Option T :=
  simulateQ (r := Id) (fun (x : R) => (pure (msg.val.eval x) : Id R)) (check stmt r).run

/-- Check all messages in order and retain explicit rejection. -/
noncomputable def foldVerdict {State : ℕ → Type} {T : Type}
    (V : RoundChecks R State) (finish : State 0 → T) :
    (k : ℕ) → State k → PathAlong oracleSig (protocol R deg k) → Option T
  | 0, stmt, _ => some (finish stmt)
  | k + 1, stmt, tr =>
      (roundVerdict (V k) stmt (headMessage tr) (headChallenge tr)).bind fun mid =>
        foldVerdict V finish k mid (tailTranscript tr)

/-- The final decision queries every round through its own payload slot. -/
def foldDecision {State : ℕ → Type} {T : Type}
    (V : RoundChecks R State) (finish : State 0 → T) :
    (k : ℕ) → State k → (p : Path (protocol R deg k)) → View (protocol R deg k) p →
      OracleComp (oracles (protocol R deg k) p) (Option T)
  | 0, stmt, _, _ => pure (some (finish stmt))
  | k + 1, stmt, p, v => do
      let mid ← simulateQ (fun r => indexedHeadQuery p r) (V k stmt (indexedViewChallenge v)).run
      match mid with
      | none => return none
      | some mid =>
        simulateQ (indexedTailLift p) (foldDecision V finish k mid
          (indexedTailPath p) (indexedTailView v))

/-- Answering a round query uses that round's message polynomial. -/
theorem simulateQ_foldHead {S T : Type} {k : ℕ}
    (check : S → R → OptionT (OracleComp (R →ₒ R)) T) (stmt : S)
    (tr : PathAlong oracleSig (protocol R deg (k + 1))) :
    simulateQ (payloadImpl _ tr) (simulateQ (fun r => indexedHeadQuery
      (projectPathAlong oracleSig _ tr) r) (check stmt (headChallenge tr)).run) =
        roundVerdict check stmt (headMessage tr) (headChallenge tr) := by
  exact QueryImpl.simulateQ_simulateQ_eq_of_apply
    (fun r => simulateQ_indexedHeadQuery tr r) _

/-- Answering the decision computes the pure verdict of the completed transcript. -/
theorem simulateQ_foldDecision {State : ℕ → Type} {T : Type}
    (V : RoundChecks R State) (finish : State 0 → T) :
    ∀ (k : ℕ) (stmt : State k) (tr : PathAlong oracleSig (protocol R deg k)),
    simulateQ (payloadImpl _ tr) (foldDecision V finish k stmt _ (toView _ tr)) =
      foldVerdict V finish k stmt tr := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro stmt tr
    rcases tr with ⟨msg, r, tail⟩
    rw [foldDecision, simulateQ_bind]
    change (simulateQ (payloadImpl (protocol R deg (k + 1)) (⟨msg, r, tail⟩ : PathAlong oracleSig
      (protocol R deg (k + 1)))) (simulateQ (fun x => indexedHeadQuery _ x)
        (V k stmt (headChallenge ⟨msg, r, tail⟩)).run) >>= _) = _
    rw [simulateQ_foldHead]
    dsimp only [headMessage, headChallenge]
    cases h : roundVerdict (V k) stmt msg r with
    | none =>
      simp [foldVerdict, h, headMessage, headChallenge]
      rfl
    | some mid =>
      change simulateQ _ (simulateQ
        (indexedTailLift (projectPathAlong oracleSig _ ⟨msg, r, tail⟩)) _) = _
      rw [simulateQ_indexedTailLift (R := R) (deg := deg) (k := k)
        (⟨msg, r, tail⟩ : PathAlong oracleSig (protocol R deg (k + 1)))]
      change simulateQ (payloadImpl _ tail)
        (foldDecision V finish k mid _ (toView _ tail)) = _
      rw [ih]
      simp [foldVerdict, h, headMessage, headChallenge, tailTranscript]

/-- A passive verifier that retains its input oracle and checks all messages at the end. -/
def foldVerifier (R : Type) [CommSemiring R] (deg : ℕ) {ι : Type} (ambient : OracleSpec ι)
    {I : Type uI} {A : I → Type} (inputs : OracleFamily.{uI, 0, wI} I A)
    {State : ℕ → Type} {T : Type} (V : RoundChecks R State) (finish : State 0 → T) (k : ℕ) :
    OracleVerifier ambient (protocol R deg k) (State k) (fun _ => T) inputs
      (fun _ => inputs) where
  decide stmt p v := OptionT.mk (simulateQ (pathLift ambient inputs p)
    (foldDecision V finish k stmt p v))
  outputMap _ _ _ := OracleMap.fst _ _

/-- The decision has no ambient effects once the resources are answered. -/
theorem simulateQ_foldVerifier_decide {ι : Type} {ambient : OracleSpec ι}
    {I : Type uI} {A : I → Type} {inputs : OracleFamily.{uI, 0, wI} I A}
    {m : Type → Type} [Monad m] [LawfulMonad m] (impl : QueryImpl ambient m)
    {State : ℕ → Type} {T : Type} (V : RoundChecks R State) (finish : State 0 → T)
    (k : ℕ) (stmt : State k) (data : ∀ i, A i)
    (tr : PathAlong oracleSig (protocol R deg k)) :
    simulateQ (QueryImpl.addLift impl ((pathResources inputs (protocol R deg k)
      (projectPathAlong oracleSig _ tr)).answer (data, payloads _ tr)))
      ((foldVerifier R deg ambient inputs V finish k).decide stmt _ (toView _ tr)).run =
        (pure (foldVerdict V finish k stmt tr) : m _) := by
  change simulateQ _ (simulateQ (pathLift ambient inputs _) _) = _
  rw [simulateQ_pathLift]
  exact congrArg pure (simulateQ_foldDecision V finish k stmt tr)

/-- The actual run keeps the transcript and applies its pure fold verdict. -/
theorem foldVerifier_run {ι : Type} (ambient : OracleSpec ι)
    {I : Type} {A : I → Type} (inputs : OracleFamily.{0, 0, wI} I A)
    {State : ℕ → Type} {T : Type} (V : RoundChecks R State) (finish : State 0 → T)
    (k : ℕ) (stmt : State k) (data : ∀ i, A i)
    {Out : PathAlong oracleSig (protocol R deg k) → Type}
    (prover : Prover oracleSig ambient (protocol R deg k) Out) :
    (foldVerifier R deg ambient inputs V finish k).run stmt data prover = (do
      let ⟨tr, out, _⟩ ← Interaction.TwoParty.Lens.run (protocol R deg k)
        (prover.simulate (fun q =>
          liftM ((ambient + challengeSpec oracleSig (protocol R deg k)).query (.inl q))))
        (sampler oracleSig (protocol R deg k) (fun c =>
          liftM ((ambient + challengeSpec oracleSig (protocol R deg k)).query (.inr c))))
      pure (⟨tr, out, (foldVerdict V finish k stmt tr).map (fun t => (t, data))⟩ :
        Observation oracleSig (protocol R deg k) Out (fun _ => T × (∀ i, A i)))) := by
  unfold Interaction.Core.OracleVerifier.run
  refine bind_congr fun result => ?_
  rcases result with ⟨tr, out, u⟩
  dsimp only
  rw [simulateQ_foldVerifier_decide]
  rfl

end Sumcheck.Core
