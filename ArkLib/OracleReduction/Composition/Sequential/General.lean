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
def seqComposeChallengeEquiv :
    (i : Fin m) × (pSpec i).ChallengeIdx ≃ (seqCompose pSpec).ChallengeIdx where
  -- TODO: write lemmas about `finSigmaFinEquiv` in mathlib with the one defined via `Fin.dfoldl`
  toFun := fun ⟨i, ⟨chalIdx, h⟩⟩ => ⟨finSigmaFinEquiv ⟨i, chalIdx⟩, by
    unfold seqCompose; sorry⟩
  invFun := fun ⟨seqComposedChalIdx, h⟩ =>
    let ⟨i, chalIdx⟩ := finSigmaFinEquiv.symm seqComposedChalIdx
    ⟨i, chalIdx, sorry⟩
  left_inv := by intro ⟨_, _⟩; simp; rw! [finSigmaFinEquiv.left_inv']; simp
  right_inv := by intro ⟨_, _⟩; simp

/-- The equivalence between the message indices of the individual protocols and the message
    indices of the sequential composition. -/
def seqComposeMessageEquiv :
    (i : Fin m) × (pSpec i).MessageIdx ≃ (seqCompose pSpec).MessageIdx where
  toFun := fun ⟨i, ⟨msgIdx, h⟩⟩ => ⟨finSigmaFinEquiv ⟨i, msgIdx⟩, by
    unfold seqCompose; sorry⟩
  invFun := fun ⟨seqComposedMsgIdx, h⟩ =>
    let ⟨i, msgIdx⟩ := finSigmaFinEquiv.symm seqComposedMsgIdx
    ⟨i, msgIdx, sorry⟩
  left_inv := by intro ⟨_, _⟩; simp; rw! [finSigmaFinEquiv.left_inv']; simp
  right_inv := by intro ⟨_, _⟩; simp

end ProtocolSpec

/-- If all protocols have sampleable challenges, then the challenges of their sequential
  composition also have sampleable challenges. -/
instance [inst : ∀ i, ∀ j, Sampleable ((pSpec i).Challenge j)] :
    ∀ j, Sampleable ((seqCompose pSpec).Challenge j) := fun combinedIdx => by
  let combinedIdx' := seqComposeChallengeEquiv.symm combinedIdx
  let this := inst combinedIdx'.1 combinedIdx'.2
  convert this using 1; sorry

/-- If all protocols' messages have oracle interfaces, then the messages of their sequential
  composition also have oracle interfaces. -/
instance [O : ∀ i, ∀ j, OracleInterface.{0, u, v} ((pSpec i).Message j)] :
    ∀ i, OracleInterface.{0, u, v} ((seqCompose pSpec).Message i) := fun combinedIdx => by
  let combinedIdx' := seqComposeMessageEquiv.symm combinedIdx
  let this := O combinedIdx'.1 combinedIdx'.2
  convert this using 1; sorry

end Instances

section Composition

variable {Stmt : Fin (m + 1) → Type} {Wit : Fin (m + 1) → Type}
  {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}

def Prover.seqCompose
    (P : (i : Fin m) →
      Prover oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i)) :
    Prover oSpec (Stmt 0) (Wit 0) (Stmt (Fin.last m)) (Wit (Fin.last m)) (seqCompose pSpec) :=
  Fin.dfoldl m
    (fun i => Prover
        oSpec (Stmt 0) (Wit 0) (Stmt i) (Wit i)
        (ProtocolSpec.seqCompose (Fin.take i (by omega) pSpec)))
    (fun i Pacc => by
      -- TODO: cast the prover with dependent cast
      convert Prover.append Pacc (P i)
      · simp [Fin.sum_univ_castSucc, Fin.last, Fin.succ]
      · simp [ProtocolSpec.seqCompose_append, dcast_eq_root_cast])
    (Prover.id)

def Verifier.seqCompose
    (V : (i : Fin m) →
      Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i)) :
    Verifier oSpec (Stmt 0) (Stmt (Fin.last m)) (seqCompose pSpec) :=
  Fin.dfoldl m
    (fun i => Verifier oSpec (Stmt 0) (Stmt i)
      (ProtocolSpec.seqCompose (Fin.take i (by omega) pSpec)))
    (fun i Vacc => by
      refine dcast₂ (self := instDCast₂Verifier) ?_ ?_ (Vacc.append (V i))
      · simp [Fin.sum_univ_castSucc, Fin.last, Fin.succ]
      · simp [seqCompose_append, dcast_eq_root_cast])
    (Verifier.id)

def Reduction.seqCompose
    (R : (i : Fin m) →
      Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i)) :
    Reduction oSpec (Stmt 0) (Wit 0) (Stmt (Fin.last m)) (Wit (Fin.last m)) (seqCompose pSpec) :=
  Fin.dfoldl m
    (fun i => Reduction oSpec (Stmt 0) (Wit 0) (Stmt i) (Wit i)
      (ProtocolSpec.seqCompose (Fin.take i (by omega) pSpec)))
    (fun i Racc => by
      convert Reduction.append Racc (R i)
      · simp [Fin.sum_univ_castSucc, Fin.last, Fin.succ]
      · simp [seqCompose_append, dcast_eq_root_cast])
    (Reduction.id)

-- TODO: define the same for `Oracle Prover/Verifier/Reduction`, and extractors and state functions

end Composition

variable {m : ℕ}
    {Stmt : Fin (m + 1) → Type} {Wit : Fin (m + 1) → Type} {rel : ∀ i, Set (Stmt i × Wit i)}
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [oSpec.FiniteRange]
    [∀ i, ∀ j, Sampleable ((pSpec i).Challenge j)]

section Lemmas

-- TODO: `compose_append` for everything, saying that sequential composition for `i + 1` times
-- equals the sequential composition for `i` times followed by appending the `i + 1`-th one

end Lemmas

-- section Execution

-- -- Executing .
-- theorem Reduction.run_seqCompose
--     (stmt : Stmt 0) (wit : Wit 0)
--     (R : ∀ i, Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ)
--       (pSpec i)) :
--       (Reduction.seqCompose R).run stmt wit := by
--   sorry

-- end Execution

section Security

open scoped NNReal

namespace Reduction

theorem completeness_seqCompose
    (completenessError : Fin m → ℝ≥0)
    (R : ∀ i, Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ)
      (pSpec i))
    (h : ∀ i, (R i).completeness (rel i.castSucc) (rel i.succ) (completenessError i)) :
      (Reduction.seqCompose R).completeness (rel 0) (rel (Fin.last m))
        (∑ i, completenessError i) := by
  induction m with
  | zero =>
    simp_all [seqCompose]; sorry
  | succ m ih =>
    sorry

end Reduction

namespace Verifier

/-- If all verifiers in a sequence satisfy soundness with respective soundness errors, then their
    sequential composition also satisfies soundness.
    The soundness error of the seqComposed verifier is the sum of the individual errors. -/
theorem seqCompose_soundness
    (lang : ∀ i, Set (Stmt i))
    (soundnessError : Fin m → ℝ≥0)
    (V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (h : ∀ i, (V i).soundness (lang i.castSucc) (lang i.succ) (soundnessError i)) :
      (Verifier.seqCompose V).soundness (lang 0) (lang (Fin.last m))
        (∑ i, soundnessError i) := by
  sorry

/-- If all verifiers in a sequence satisfy knowledge soundness with respective knowledge errors,
    then their sequential composition also satisfies knowledge soundness.
    The knowledge error of the seqComposed verifier is the sum of the individual errors. -/
theorem seqCompose_knowledgeSoundness
    (rel : ∀ i, Set (Stmt i × Wit i))
    (knowledgeError : Fin m → ℝ≥0)
    (V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (h : ∀ i, (V i).knowledgeSoundness (rel i.castSucc) (rel i.succ) (knowledgeError i)) :
      (Verifier.seqCompose V).knowledgeSoundness (rel 0) (rel (Fin.last m))
        (∑ i, knowledgeError i) := by
  sorry

/-- If all verifiers in a sequence satisfy round-by-round soundness with respective RBR soundness
    errors, then their sequential composition also satisfies round-by-round soundness. -/
theorem seqCompose_rbrSoundness
    (V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (lang : ∀ i, Set (Stmt i))
    (rbrSoundnessError : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrSoundness (lang i.castSucc) (lang i.succ) (rbrSoundnessError i))
    -- Deterministic verifier condition for state function composition
    (verify : ∀ i, Stmt i.castSucc → (pSpec i).FullTranscript → Stmt i.succ)
    (hVerify : ∀ i, V i = ⟨fun stmt tr => pure (verify i stmt tr)⟩) :
      (Verifier.seqCompose V).rbrSoundness (lang 0) (lang (Fin.last m))
        (fun combinedIdx =>
          let ⟨i, idx⟩ := seqComposeChallengeEquiv.symm combinedIdx
          rbrSoundnessError i idx) := by
  sorry

/-- If all verifiers in a sequence satisfy round-by-round knowledge soundness with respective RBR
    knowledge errors, then their sequential composition also satisfies round-by-round knowledge
    soundness. -/
theorem seqCompose_rbrKnowledgeSoundness
    (V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (rel : ∀ i, Set (Stmt i × Wit i))
    (rbrKnowledgeError : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrKnowledgeSoundness (rel i.castSucc) (rel i.succ) (rbrKnowledgeError i))
    -- Deterministic verifier condition for state function composition
    (verify : ∀ i, Stmt i.castSucc → (pSpec i).FullTranscript → Stmt i.succ)
    (hVerify : ∀ i, V i = ⟨fun stmt tr => pure (verify i stmt tr)⟩) :
      (Verifier.seqCompose V).rbrKnowledgeSoundness (rel 0) (rel (Fin.last m))
        (fun combinedIdx =>
          let ⟨i, idx⟩ := seqComposeChallengeEquiv.symm combinedIdx
          rbrKnowledgeError i idx) := by
  sorry

end Verifier

end Security
