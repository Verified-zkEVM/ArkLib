/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Interaction.Oracle.Security.StateRestorationOracle
public import ArkLib.ProofSystem.Sumcheck.Interaction.ProtocolSoundness

/-!
# Ordinary Sumcheck certificates for fixed field-valued restoration rounds

The state retains the original polynomial and records whether all preceding sum checks passed.
A failed check makes every later state false. Each field challenge therefore has the usual
`degree / card F` false-to-true bound, at every authored prefix, including invalid prefixes.

The witness carrier is `Unit`: this is an ordinary soundness certificate using the common
restoration interface, not a claim of substantive witness extraction. Relating the padded
presentation to the native aborting Sumcheck verifier is a separate execution obligation.
-/

public section
open Interaction.Oracle Interaction.Oracle.Security OracleComp OracleSpec
open scoped ENNReal
namespace Sumcheck.Interaction.Restoration
open SingleRound MultivariateRound
open Interaction.Oracle.Security.StateRestoration (Round)

variable (F : Type) [Field F] [Fintype F] [DecidableEq F] [SampleableType F] (n deg : ℕ)
/-- A degree-bounded oracle polynomial followed by a uniform field challenge. -/
@[expose] noncomputable def round : Round where
  Message := Message F deg
  Challenge := F
  interface := polynomialInterface F deg
  decEqMessage := Classical.decEq _
  finiteMessage := by
    change Finite (Polynomial.degreeLE F deg)
    rw [← Polynomial.degreeLT_succ_eq_degreeLE]
    exact Finite.of_equiv (Fin (deg + 1) → F) (Polynomial.degreeLTEquiv F (deg + 1)).toEquiv.symm
  finiteChallenge := inferInstance
  nonemptyChallenge := inferInstance
  sampleChallenge := inferInstance
/-- The fixed padded round list; early rejection is recorded in the certificate state. -/
@[expose] noncomputable def rounds : ℕ → List Round
  | 0 => []
  | k + 1 => round F deg :: rounds k

/-- Truth of the current claim, provided no earlier sum check failed. -/
@[expose] def claimState {m : ℕ} (D : Fin m ↪ F) (i : Fin (n + 1))
    (stmt : Spec.StatementRound F n i) (p : Spec.OracleStatement F n deg ())
    (checksPassed : Prop) : KnowledgeState where
  Witness := Unit
  holds _ := checksPassed ∧ closedRelation F n deg D i
    ⟨stmt, (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p)⟩

/-- An ordinary predicate certificate with identity Unit witness maps at every move. -/
@[expose] noncomputable def certificate {m : ℕ} (D : Fin m ↪ F)
    (p : Spec.OracleStatement F n deg ()) :
    (count start : ℕ) → (finish : start + count = n) →
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) → (checksPassed : Prop) →
    RoundExtractor (Security.StateRestoration.protocol (rounds F deg count)).tree
      (claimState F n deg D ⟨start, by omega⟩ stmt p checksPassed)
  | 0, _, _, _, _ => PUnit.unit
  | count + 1, start, finish, stmt, checksPassed => fun q =>
      ⟨claimState F n deg D ⟨start, by omega⟩ stmt p checksPassed, id,
        fun r =>
          ⟨claimState F n deg D ⟨start + 1, by omega⟩
            ⟨q.val.eval r, Fin.snoc stmt.challenges r⟩ p
            (checksPassed ∧
              ((Finset.univ.map D).toList.map (fun x => q.val.eval x)).sum = stmt.target),
            (fun _ => ()), certificate D p count (start + 1) (by omega)
              ⟨q.val.eval r, Fin.snoc stmt.challenges r⟩
              (checksPassed ∧
                ((Finset.univ.map D).toList.map (fun x => q.val.eval x)).sum = stmt.target)⟩⟩

omit [DecidableEq F] in
/-- Sending a polynomial cannot turn a false ordinary state into a true one. -/
theorem certificate_preserving {m : ℕ} (D : Fin m ↪ F)
    (p : Spec.OracleStatement F n deg ())
    (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (checksPassed : Prop) :
    (certificate F n deg D p count start finish stmt checksPassed).IsProverPreserving
      (Security.StateRestoration.protocol (rounds F deg count)).roles := by
  induction count generalizing start checksPassed with
  | zero => trivial
  | succ count ih =>
      constructor
      · intro q u hu
        exact hu
      · intro q
        constructor
        · intro r h
          cases h
        · intro r
          exact ih (start + 1) (by omega) _ _


omit [DecidableEq F] in
/-- Every authored verifier prefix has the standard degree-over-field-size local error. -/
theorem certificate_locallyBounded {m : ℕ} (D : Fin m ↪ F)
    (p : Spec.OracleStatement F n deg ())
    (count start : ℕ) (finish : start + count = n)
    (stmt : Spec.StatementRound F n ⟨start, by omega⟩) (checksPassed : Prop) :
    (certificate F n deg D p count start finish stmt checksPassed).IsLocallyBounded
      (Security.StateRestoration.protocol (rounds F deg count)).roles
      (Security.StateRestoration.uniformSchedule
        ((deg : ENNReal) / Fintype.card F) (rounds F deg count)) := by
  induction count generalizing start checksPassed with
  | zero => trivial
  | succ count ih =>
      intro q
      constructor
      · apply (_root_.RoundByRound.GameFamily.isBounded_iff _ _).mpr
        intro _ _
        change Pr{let r ← ($ᵗ F)}[
          RoundExtractor.badChallenge
            ((certificate F n deg D p (count + 1) start finish stmt checksPassed q).2.2) r] ≤
              (deg : ENNReal) / Fintype.card F
        by_cases hp : checksPassed
        · by_cases hc : ((Finset.univ.map D).toList.map
              (fun x => q.val.eval x)).sum = stmt.target
          · by_cases htruth : closedRelation F n deg D ⟨start, by omega⟩
                ⟨stmt, (polynomialFamily F n deg).behaviorOfRealizations (fun _ => p)⟩
            · simp [RoundExtractor.badChallenge, certificate,
                claimState, hp, htruth]
            · have hb := uniform_successor_soundness n deg F D ⟨start, by omega⟩ stmt p q
                htruth hc
              apply le_trans _ hb
              apply prEvent_mono
              intro r hevent
              rcases hevent with ⟨w, _, hgood⟩
              exact hgood.2
          · have hc' : ¬ (∑ x, q.val.eval (D x)) = stmt.target := by simpa using hc
            simp [RoundExtractor.badChallenge, certificate, claimState, hc']
        · simp [RoundExtractor.badChallenge, certificate,
            claimState, hp]
      · intro r
        exact ih (start + 1) (by omega) _ _

end Sumcheck.Interaction.Restoration

