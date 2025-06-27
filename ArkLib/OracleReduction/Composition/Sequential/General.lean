/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Composition.Sequential.Append

/-!
  # Sequential Composition of Many Oracle Reductions

  This file defines the sequential composition of an arbitrary `m + 1` number of oracle reductions.
  This is defined by iterating the composition of two reductions, as defined in `Append.lean`.

  The security properties of the general sequential composition of reductions are then inherited
  from the case of composing two reductions.
-/

open ProtocolSpec

universe u v

variable {ι : Type} {oSpec : OracleSpec ι} {m : ℕ}

section Instances

variable {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}

namespace ProtocolSpec

/-- The equivalence between the challenge indices of the individual protocols and the challenge
    indices of the sequential composition. -/
def composeChallengeEquiv :
    (i : Fin m) × (pSpec i).ChallengeIdx ≃ (compose pSpec).ChallengeIdx where
  -- TODO: write lemmas about `finSigmaFinEquiv` in mathlib with the one defined via `Fin.dfoldl`
  toFun := fun ⟨i, ⟨chalIdx, h⟩⟩ => ⟨finSigmaFinEquiv ⟨i, chalIdx⟩, by
    unfold compose; sorry⟩
  invFun := fun ⟨composedChalIdx, h⟩ =>
    let ⟨i, chalIdx⟩ := finSigmaFinEquiv.symm composedChalIdx
    ⟨i, chalIdx, sorry⟩
  left_inv := by intro ⟨_, _⟩; simp; rw! [finSigmaFinEquiv.left_inv']; simp
  right_inv := by intro ⟨_, _⟩; simp

/-- The equivalence between the message indices of the individual protocols and the message
    indices of the sequential composition. -/
def composeMessageEquiv :
    (i : Fin m) × (pSpec i).MessageIdx ≃ (compose pSpec).MessageIdx where
  toFun := fun ⟨i, ⟨msgIdx, h⟩⟩ => ⟨finSigmaFinEquiv ⟨i, msgIdx⟩, by
    unfold compose; sorry⟩
  invFun := fun ⟨composedMsgIdx, h⟩ =>
    let ⟨i, msgIdx⟩ := finSigmaFinEquiv.symm composedMsgIdx
    ⟨i, msgIdx, sorry⟩
  left_inv := by intro ⟨_, _⟩; simp; rw! [finSigmaFinEquiv.left_inv']; simp
  right_inv := by intro ⟨_, _⟩; simp

end ProtocolSpec

/-- If all protocols have sampleable challenges, then the challenges of their sequential
  composition also have sampleable challenges. -/
instance [inst : ∀ i, ∀ j, Sampleable ((pSpec i).Challenge j)] :
    ∀ j, Sampleable ((compose pSpec).Challenge j) := fun combinedIdx => by
  let combinedIdx' := composeChallengeEquiv.symm combinedIdx
  let this := inst combinedIdx'.1 combinedIdx'.2
  convert this using 1; sorry

/-- If all protocols' messages have oracle interfaces, then the messages of their sequential
  composition also have oracle interfaces. -/
instance [O : ∀ i, ∀ j, OracleInterface.{0, u, v} ((pSpec i).Message j)] :
    ∀ i, OracleInterface.{0, u, v} ((compose pSpec).Message i) := fun combinedIdx => by
  let combinedIdx' := composeMessageEquiv.symm combinedIdx
  let this := O combinedIdx'.1 combinedIdx'.2
  convert this using 1; sorry

end Instances

section Composition

def Prover.compose
    (Stmt : Fin (m + 1) → Type) (Wit : Fin (m + 1) → Type)
    {n : Fin m → ℕ} (pSpec : ∀ i, ProtocolSpec (n i))
    (P : (i : Fin m) → Prover oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ)
      (pSpec i)) :
    Prover oSpec (Stmt 0) (Wit 0) (Stmt (Fin.last m)) (Wit (Fin.last m)) (compose pSpec) :=
  Fin.dfoldl m
    (fun i => Prover
        oSpec (Stmt 0) (Wit 0) (Stmt i.succ) (Wit i.succ)
        (ProtocolSpec.compose (Fin.take i (by omega) pSpec)))
    (fun i Pacc => by
      convert Prover.append Pacc (P i.succ)
      · simp [Fin.sum_univ_castSucc, Fin.last, Fin.succ]
      · simp [ProtocolSpec.compose_append, dcast_eq_root_cast])
    (by simpa using P 0)

def Verifier.compose (m : ℕ) (n : Fin (m + 1) → ℕ) (pSpec : ∀ i, ProtocolSpec (n i))
    (Stmt : Fin (m + 2) → Type)
    (V : (i : Fin (m + 1)) → Verifier (pSpec i) oSpec (Stmt i.castSucc) (Stmt i.succ)) :
      Verifier (ProtocolSpec.compose m n pSpec) oSpec (Stmt 0) (Stmt (Fin.last (m + 1))) :=
  Fin.dfoldl m
    (fun i => Verifier
      (ProtocolSpec.compose i (Fin.take (i + 1) (by omega) n) (Fin.take (i + 1) (by omega) pSpec))
        oSpec (Stmt 0) (Stmt i.succ))
    (fun i Vacc => by
      refine dcast₂ (self := instDepCast₂Verifier) ?_ ?_ (Vacc.append (V i.succ))
      · simp [Fin.sum_univ_castSucc, Fin.last, Fin.succ]
      · simp [ProtocolSpec.compose_append, dcast_eq_root_cast])
    (by simpa using V 0)

def Reduction.compose (m : ℕ) (n : Fin (m + 1) → ℕ) (pSpec : ∀ i, ProtocolSpec (n i))
    (Stmt : Fin (m + 2) → Type) (Wit : Fin (m + 2) → Type)
    (R : (i : Fin (m + 1)) → Reduction (pSpec i) oSpec (Stmt i.castSucc) (Wit i.castSucc)
      (Stmt i.succ) (Wit i.succ)) :
      Reduction (ProtocolSpec.compose m n pSpec) oSpec (Stmt 0) (Wit 0) (Stmt (Fin.last (m + 1)))
        (Wit (Fin.last (m + 1))) :=
  Fin.dfoldl m
    (fun i => Reduction
      (ProtocolSpec.compose i (Fin.take (i + 1) (by omega) n) (Fin.take (i + 1) (by omega) pSpec))
        oSpec (Stmt 0) (Wit 0) (Stmt i.succ) (Wit i.succ))
    (fun i Racc => by
      convert Reduction.append Racc (R i.succ)
      · simp [Fin.sum_univ_castSucc, Fin.last, Fin.succ]
      · simp [ProtocolSpec.compose_append, dcast_eq_root_cast])
    (by simpa using R 0)

end Composition

section Security

open scoped NNReal

namespace Reduction

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i, ∀ j, Sampleable ((pSpec i).Challenge j)]
    {Stmt : Fin (m + 2) → Type} {Wit : Fin (m + 2) → Type} {rel : ∀ i, Stmt i → Wit i → Prop}
    [oSpec.DecidableEq] [oSpec.FiniteRange]

theorem completeness_compose
    (R : ∀ i, Reduction (pSpec i) oSpec (Stmt i.castSucc) (Wit i.castSucc)
      (Stmt i.succ) (Wit i.succ))
    (completenessError : Fin (m + 1) → ℝ≥0)
    (h : ∀ i, (R i).completeness (rel i.castSucc) (rel i.succ) (completenessError i)) :
      (Reduction.compose m n pSpec Stmt Wit R).completeness (rel 0) (rel (Fin.last (m + 1)))
        (∑ i, completenessError i) := by
  induction m with
  | zero =>
    simp_all; convert h 0; sorry
  | succ m ih =>
    sorry

end Reduction

namespace Verifier

variable {m : ℕ} {n : Fin (m + 1) → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [∀ i, ∀ j, Sampleable ((pSpec i).Challenge j)]
    {Stmt : Fin (m + 2) → Type} {Wit : Fin (m + 2) → Type}
    [oSpec.DecidableEq] [oSpec.FiniteRange]

/-- If all verifiers in a sequence satisfy soundness with respective soundness errors, then their
    sequential composition also satisfies soundness.
    The soundness error of the composed verifier is the sum of the individual errors. -/
theorem compose_soundness
    (V : ∀ i, Verifier (pSpec i) oSpec (Stmt i.castSucc) (Stmt i.succ))
    (lang : ∀ i, Set (Stmt i))
    (soundnessError : Fin (m + 1) → ℝ≥0)
    (h : ∀ i, (V i).soundness (lang i.castSucc) (lang i.succ) (soundnessError i)) :
      (Verifier.compose m n pSpec Stmt V).soundness (lang 0) (lang (Fin.last (m + 1)))
        (∑ i, soundnessError i) := by
  sorry

/-- If all verifiers in a sequence satisfy knowledge soundness with respective knowledge errors,
    then their sequential composition also satisfies knowledge soundness.
    The knowledge error of the composed verifier is the sum of the individual errors. -/
theorem compose_knowledgeSoundness
    (V : ∀ i, Verifier (pSpec i) oSpec (Stmt i.castSucc) (Stmt i.succ))
    (rel : ∀ i, Stmt i → Wit i → Prop)
    (knowledgeError : Fin (m + 1) → ℝ≥0)
    (h : ∀ i, (V i).knowledgeSoundness (rel i.castSucc) (rel i.succ) (knowledgeError i)) :
      (Verifier.compose m n pSpec Stmt V).knowledgeSoundness (rel 0) (rel (Fin.last (m + 1)))
        (∑ i, knowledgeError i) := by
  sorry

/-- If all verifiers in a sequence satisfy round-by-round soundness with respective RBR soundness
    errors, then their sequential composition also satisfies round-by-round soundness. -/
theorem compose_rbrSoundness
    (V : ∀ i, Verifier (pSpec i) oSpec (Stmt i.castSucc) (Stmt i.succ))
    (lang : ∀ i, Set (Stmt i))
    (rbrSoundnessError : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrSoundness (lang i.castSucc) (lang i.succ) (rbrSoundnessError i))
    -- Deterministic verifier condition for state function composition
    (verify : ∀ i, Stmt i.castSucc → (pSpec i).FullTranscript → Stmt i.succ)
    (hVerify : ∀ i, V i = ⟨fun stmt tr => pure (verify i stmt tr)⟩) :
      (Verifier.compose m n pSpec Stmt V).rbrSoundness (lang 0) (lang (Fin.last (m + 1)))
        (fun combinedIdx =>
          let ⟨i, idx⟩ := composeChallengeEquiv.symm combinedIdx
          rbrSoundnessError i idx) := by
  sorry

/-- If all verifiers in a sequence satisfy round-by-round knowledge soundness with respective RBR
    knowledge errors, then their sequential composition also satisfies round-by-round knowledge
    soundness. -/
theorem compose_rbrKnowledgeSoundness
    (V : ∀ i, Verifier (pSpec i) oSpec (Stmt i.castSucc) (Stmt i.succ))
    (rel : ∀ i, Stmt i → Wit i → Prop)
    (rbrKnowledgeError : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrKnowledgeSoundness (rel i.castSucc) (rel i.succ) (rbrKnowledgeError i))
    -- Deterministic verifier condition for state function composition
    (verify : ∀ i, Stmt i.castSucc → (pSpec i).FullTranscript → Stmt i.succ)
    (hVerify : ∀ i, V i = ⟨fun stmt tr => pure (verify i stmt tr)⟩) :
      (Verifier.compose m n pSpec Stmt V).rbrKnowledgeSoundness (rel 0) (rel (Fin.last (m + 1)))
        (fun combinedIdx =>
          let ⟨i, idx⟩ := composeChallengeEquiv.symm combinedIdx
          rbrKnowledgeError i idx) := by
  sorry

end Verifier

end Security
