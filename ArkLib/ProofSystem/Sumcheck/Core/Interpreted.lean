/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Core.InterpretedPath
public import ArkLib.ProofSystem.Sumcheck.Core.Protocol

/-! # Passive Sumcheck with interpreted message carriers

An evaluation interface allows arbitrary message representations. The interaction-layer decision
reads only that interface; its transcript verdict uses the same interpretation. Neither messages
nor public challenges choose the subsequent shape.
-/

@[expose] public section

universe uI wI

namespace Sumcheck.Core.Interpreted
open Polynomial PFunctor FreeM Interaction.Core Interaction.TwoParty.Lens Interaction.Oracle
  OracleComp OracleSpec

variable {R M : Type} {evaluate : M → R → R}

/-- Interpreting a check uses the message's supplied evaluation function. -/
def roundVerdict {S T : Type} (evaluate : M → R → R)
    (check : S → R → OptionT (OracleComp (R →ₒ R)) T) (stmt : S) (msg : M) (r : R) :
    Option T := simulateQ (r := Id) (fun (x : R) => (pure (evaluate msg x) : Id R))
      (check stmt r).run

/-- The verdict of all interpreted messages, in chronological order. -/
def verdict {State : ℕ → Type} {T : Type} (evaluate : M → R → R)
    (checks : RoundChecks R State) (finish : State 0 → T) :
    (k : ℕ) → State k → PathAlong oracleSig (protocol R M evaluate k) → Option T
  | 0, st, _ => some (finish st)
  | k + 1, st, tr => (roundVerdict evaluate (checks k) st (message tr) (challenge tr)).bind
      fun mid => verdict evaluate checks finish k mid (tail tr)

/-- The interaction-layer final decision queries the declared interface of each message. -/
def decision {State : ℕ → Type} {T : Type} (checks : RoundChecks R State)
    (finish : State 0 → T) : (k : ℕ) → State k → (p : Path (protocol R M evaluate k)) →
      View (protocol R M evaluate k) p →
      OracleComp (oracles (protocol R M evaluate k) p) (Option T)
  | 0, st, _, _ => pure (some (finish st))
  | k + 1, st, p, v => do
      let mid ← simulateQ (headQuery p) (checks k st (viewChallenge v)).run
      match mid with
      | none => return none
      | some mid => simulateQ (tailLift p) (decision checks finish k mid (tailPath p) (tailView v))

/-- Answering the interaction-layer decision computes the verdict for every interpreted carrier. -/
theorem simulate_decision {State : ℕ → Type} {T : Type} (checks : RoundChecks R State)
    (finish : State 0 → T) : ∀ (k : ℕ) (st : State k)
    (tr : PathAlong oracleSig (protocol R M evaluate k)),
    simulateQ (payloadImpl _ tr) (decision checks finish k st _ (toView _ tr)) =
      verdict evaluate checks finish k st tr := by
  intro k
  induction k with
  | zero => intros; rfl
  | succ k ih =>
    intro st tr
    rcases tr with ⟨msg, r, rest⟩
    rw [decision, simulateQ_bind]
    have hh : simulateQ (payloadImpl (protocol R M evaluate (k + 1)) (⟨msg, r, rest⟩ :
        PathAlong oracleSig (protocol R M evaluate (k + 1))))
        (simulateQ (headQuery (projectPathAlong oracleSig _ ⟨msg, r, rest⟩))
          (checks k st r).run) = roundVerdict evaluate (checks k) st msg r :=
      QueryImpl.simulateQ_simulateQ_eq_of_apply (fun x => simulate_head _ x) _
    change (simulateQ _ (simulateQ _ (checks k st r).run) >>= _) = _
    rw [hh]
    cases h : roundVerdict evaluate (checks k) st msg r with
    | none => simp [verdict, h, message, challenge]; rfl
    | some mid =>
      change simulateQ _ (simulateQ (tailLift (projectPathAlong oracleSig _ ⟨msg, r, rest⟩)) _) = _
      rw [simulate_tail (⟨msg, r, rest⟩ : PathAlong oracleSig (protocol R M evaluate (k + 1)))]
      change simulateQ (payloadImpl _ rest) (decision checks finish k mid _ (toView _ rest)) = _
      rw [ih]
      simp [verdict, h, message, challenge, tail]

/-- A passive oracle verifier for any evaluated message representation and retained input. -/
def verifier {ι : Type} (ambient : OracleSpec ι) {I : Type uI} {A : I → Type}
    (inputs : OracleFamily.{uI, 0, wI} I A) {State : ℕ → Type} {T : Type}
    (checks : RoundChecks R State) (finish : State 0 → T) (k : ℕ) :
    OracleVerifier ambient (protocol R M evaluate k) (State k) (fun _ => T) inputs
      (fun _ => inputs) where
  decide st p v := OptionT.mk (simulateQ (pathLift ambient inputs p)
    (decision checks finish k st p v))
  outputMap _ _ _ := OracleMap.fst _ _

/-- The interpreted verifier's final decision is pure once its resources are answered. -/
theorem simulate_verifier {ι : Type} {ambient : OracleSpec ι} {I : Type uI} {A : I → Type}
    {inputs : OracleFamily.{uI, 0, wI} I A} {m : Type → Type} [Monad m] [LawfulMonad m]
    (impl : QueryImpl ambient m) {State : ℕ → Type} {T : Type}
    (checks : RoundChecks R State) (finish : State 0 → T) (k : ℕ) (st : State k)
    (data : ∀ i, A i) (tr : PathAlong oracleSig (protocol R M evaluate k)) :
    simulateQ (QueryImpl.addLift impl ((pathResources inputs _
      (projectPathAlong oracleSig _ tr)).answer (data, payloads _ tr)))
      ((verifier ambient inputs checks finish k).decide st _ (toView _ tr)).run =
      (pure (verdict evaluate checks finish k st tr) : m _) := by
  change simulateQ _ (simulateQ (pathLift ambient inputs _) _) = _
  rw [simulateQ_pathLift]
  exact congrArg pure (simulate_decision checks finish k st tr)

/-- Actual execution preserves the transcript, private output and original oracle data for
any evaluated message carrier. -/
theorem verifier_run {ι : Type} (ambient : OracleSpec ι) {I : Type} {A : I → Type}
    (inputs : OracleFamily.{0, 0, wI} I A) {State : ℕ → Type} {T : Type}
    (checks : RoundChecks R State) (finish : State 0 → T) (k : ℕ) (st : State k)
    (data : ∀ i, A i) {Out : PathAlong oracleSig (protocol R M evaluate k) → Type}
    (prover : Prover oracleSig ambient (protocol R M evaluate k) Out) :
    (verifier ambient inputs checks finish k).run st data prover = (do
      let ⟨tr, out, _⟩ ← Interaction.TwoParty.Lens.run (protocol R M evaluate k)
        (prover.simulate (fun q => liftM
          ((ambient + challengeSpec oracleSig (protocol R M evaluate k)).query (.inl q))))
        (sampler oracleSig _ (fun c => liftM
          ((ambient + challengeSpec oracleSig (protocol R M evaluate k)).query (.inr c))))
      pure (⟨tr, out, (verdict evaluate checks finish k st tr).map (fun t => (t, data))⟩ :
        Observation oracleSig _ Out (fun _ => T × (∀ i, A i)))) := by
  rw [OracleVerifier.run_eq]
  refine bind_congr fun result => ?_
  rcases result with ⟨tr, out, u⟩
  dsimp only
  rw [simulate_verifier]
  rfl

end Sumcheck.Core.Interpreted
