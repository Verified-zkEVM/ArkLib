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

open ProtocolSpec OracleComp

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
instance [inst : ∀ i, ∀ j, SelectableType ((pSpec i).Challenge j)] :
    ∀ j, SelectableType ((seqCompose pSpec).Challenge j) := fun combinedIdx => by
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

--  (i_1 : (ProtocolSpec.seqCompose (Fin.take ↑i ?m.69475 pSpec)).MessageIdx) →
--     OracleInterface ((ProtocolSpec.seqCompose (Fin.take ↑i ?m.69475 pSpec)).Message i_1)

end Instances

section Composition

variable (Stmt : Fin (m + 1) → Type)
  {ιₛ : Fin (m + 1) → Type} (OStmt : (i : Fin (m + 1)) → ιₛ i → Type)
  [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
  (Wit : Fin (m + 1) → Type)
  {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
  [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]

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

/-- Sequential composition of reductions, defined via sequential composition of provers and
  verifiers (or equivalently, folding over the append of reductions). -/
def Reduction.seqCompose
    (R : (i : Fin m) →
      Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i)) :
    Reduction oSpec (Stmt 0) (Wit 0) (Stmt (Fin.last m)) (Wit (Fin.last m)) (seqCompose pSpec) where
  prover := Prover.seqCompose Stmt Wit (fun i => (R i).prover)
  verifier := Verifier.seqCompose Stmt (fun i => (R i).verifier)

/-- Alternative definition of sequential composition of reductions, defined via folding over the
  append of reductions. -/
lemma Reduction.seqCompose_eq_foldl
    (R : (i : Fin m) →
      Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ) (pSpec i)) :
    Reduction.seqCompose Stmt Wit R = Fin.dfoldl m
      (fun i => Reduction oSpec (Stmt 0) (Wit 0) (Stmt i) (Wit i)
        (ProtocolSpec.seqCompose (Fin.take i (by omega) pSpec)))
      (fun i Racc => by
        convert Reduction.append Racc (R i)
        · simp [Fin.sum_univ_castSucc, Fin.last, Fin.succ]
        · simp [seqCompose_append, dcast_eq_root_cast])
      (Reduction.id) := by
  induction m with
  | zero =>
    simp [seqCompose, Reduction.append, Reduction.id, Prover.seqCompose, Verifier.seqCompose]
  | succ m ih =>
    simp [Fin.dfoldl_succ_last]
    sorry
    -- simp_rw [ih]
    -- simp [seqCompose, Reduction.append, Reduction.id, Prover.seqCompose, Verifier.seqCompose]

-- TODO: define the same for `Oracle Prover/Verifier/Reduction`, and extractors and state functions

/-- Sequential composition of provers in oracle reductions, defined via sequential composition of
  provers in non-oracle reductions. -/
def OracleProver.seqCompose
    (P : (i : Fin m) →
      OracleProver oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
        (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i)) :
    OracleProver oSpec (Stmt 0) (OStmt 0) (Wit 0) (Stmt (Fin.last m)) (OStmt (Fin.last m))
      (Wit (Fin.last m)) (seqCompose pSpec) :=
  Prover.seqCompose (fun i => Stmt i × (∀ j, OStmt i j)) Wit P

/-- Sequential composition of verifiers in oracle reductions.

TODO: fix this, need to derive `OracleInterface` instances for messages -/
def OracleVerifier.seqCompose
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i)) :
    OracleVerifier oSpec (Stmt 0) (OStmt 0) (Stmt (Fin.last m)) (OStmt (Fin.last m))
      (seqCompose pSpec) := sorry
  -- Fin.dfoldl m
  --   (fun i => OracleVerifier oSpec (Stmt 0) (OStmt 0) (Stmt i) (OStmt i)
  --     (ProtocolSpec.seqCompose (Fin.take i (by omega) pSpec)))
  --   (fun i Vacc => by
  --     convert OracleVerifier.append Vacc (V i)
  --     · simp [Fin.sum_univ_castSucc, Fin.last, Fin.succ]
  --     · simp [seqCompose_append, dcast_eq_root_cast])
  --   (OracleVerifier.id)

/-- Sequential composition of oracle reductions, defined via sequential composition of oracle
  provers and oracle verifiers. -/
def OracleReduction.seqCompose
    (R : (i : Fin m) →
      OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc) (Stmt i.succ)
        (OStmt i.succ) (Wit i.succ) (pSpec i)) :
    OracleReduction oSpec (Stmt 0) (OStmt 0) (Wit 0) (Stmt (Fin.last m)) (OStmt (Fin.last m))
      (Wit (Fin.last m)) (seqCompose pSpec) where
  prover := OracleProver.seqCompose Stmt OStmt Wit (fun i => (R i).prover)
  verifier := OracleVerifier.seqCompose Stmt OStmt (fun i => (R i).verifier)

-- /-- Alternative definition of sequential composition of oracle reductions, defined via folding
--   over the append of oracle reductions. -/
-- lemma OracleReduction.seqCompose_eq_foldl
--     (R : (i : Fin m) →
--       OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc) (Stmt i.succ)
--         (OStmt i.succ) (Wit i.succ) (pSpec i)) :
--     OracleReduction.seqCompose Stmt OStmt Wit R = Fin.dfoldl m
--       (fun i => OracleReduction oSpec (Stmt 0) (OStmt 0) (Wit 0) (Stmt i) (OStmt i) (Wit i)
--         (ProtocolSpec.seqCompose (Fin.take i (by omega) pSpec)))
--       (fun i Racc => by
--         convert OracleReduction.append Racc (R i)
--         · simp [Fin.sum_univ_castSucc, Fin.last, Fin.succ]
--         · simp [seqCompose_append, dcast_eq_root_cast])
--       (OracleReduction.id) := by
--   induction m with
--   | zero =>
--     simp [seqCompose, OracleReduction.append, OracleReduction.id,
--       OracleProver.seqCompose, OracleVerifier.seqCompose]
--   | succ m ih =>
--     simp [Fin.dfoldl_succ_last]
--     sorry

end Composition

variable {m : ℕ}
    {Stmt : Fin (m + 1) → Type}
    {ιₛ : Fin (m + 1) → Type} {OStmt : (i : Fin (m + 1)) → ιₛ i → Type}
    [Oₛ : ∀ i, ∀ j, OracleInterface (OStmt i j)]
    {Wit : Fin (m + 1) → Type}
    {n : Fin m → ℕ} {pSpec : ∀ i, ProtocolSpec (n i)}
    [Oₘ : ∀ i, ∀ j, OracleInterface ((pSpec i).Message j)]
    [∀ i, ∀ j, SelectableType ((pSpec i).Challenge j)]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}

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

theorem seqCompose_completeness (hInit : init.neverFails)
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (R : ∀ i, Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ)
      (pSpec i))
    (completenessError : Fin m → ℝ≥0)
    (h : ∀ i, (R i).completeness init impl (rel i.castSucc) (rel i.succ) (completenessError i)) :
      (Reduction.seqCompose Stmt Wit R).completeness init impl (rel 0) (rel (Fin.last m))
        (∑ i, completenessError i) := by
  induction m with
  | zero =>
    simp_all [seqCompose]; sorry
  | succ m ih =>
    sorry

theorem seqCompose_perfectCompleteness (hInit : init.neverFails)
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (R : ∀ i, Reduction oSpec (Stmt i.castSucc) (Wit i.castSucc) (Stmt i.succ) (Wit i.succ)
      (pSpec i))
    (h : ∀ i, (R i).perfectCompleteness init impl (rel i.castSucc) (rel i.succ)) :
      (Reduction.seqCompose Stmt Wit R).perfectCompleteness
        init impl (rel 0) (rel (Fin.last m)) := by
  unfold perfectCompleteness
  convert seqCompose_completeness hInit rel R 0 h
  simp


end Reduction

namespace Verifier

/-- If all verifiers in a sequence satisfy soundness with respective soundness errors, then their
    sequential composition also satisfies soundness.
    The soundness error of the seqComposed verifier is the sum of the individual errors. -/
theorem seqCompose_soundness
    (lang : (i : Fin (m + 1)) → Set (Stmt i))
    (V : (i : Fin m) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (soundnessError : Fin m → ℝ≥0)
    (h : ∀ i, (V i).soundness init impl (lang i.castSucc) (lang i.succ) (soundnessError i)) :
      (Verifier.seqCompose Stmt V).soundness init impl (lang 0) (lang (Fin.last m))
        (∑ i, soundnessError i) := by
  sorry

/-- If all verifiers in a sequence satisfy knowledge soundness with respective knowledge errors,
    then their sequential composition also satisfies knowledge soundness.
    The knowledge error of the seqComposed verifier is the sum of the individual errors. -/
theorem seqCompose_knowledgeSoundness
    (rel : (i : Fin (m + 1)) → Set (Stmt i × Wit i))
    (V : (i : Fin m) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (knowledgeError : Fin m → ℝ≥0)
    (h : ∀ i, (V i).knowledgeSoundness init impl (rel i.castSucc) (rel i.succ) (knowledgeError i)) :
      (Verifier.seqCompose Stmt V).knowledgeSoundness init impl (rel 0) (rel (Fin.last m))
        (∑ i, knowledgeError i) := by
  sorry

/-- If all verifiers in a sequence satisfy round-by-round soundness with respective RBR soundness
    errors, then their sequential composition also satisfies round-by-round soundness. -/
theorem seqCompose_rbrSoundness
    (lang : (i : Fin (m + 1)) → Set (Stmt i))
    (V : (i : Fin m) → Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (rbrSoundnessError : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrSoundness init impl (lang i.castSucc) (lang i.succ) (rbrSoundnessError i)) :
      (Verifier.seqCompose Stmt V).rbrSoundness init impl (lang 0) (lang (Fin.last m))
        (fun combinedIdx =>
          let ⟨i, idx⟩ := seqComposeChallengeEquiv.symm combinedIdx
          rbrSoundnessError i idx) := by
  sorry

/-- If all verifiers in a sequence satisfy round-by-round knowledge soundness with respective RBR
    knowledge errors, then their sequential composition also satisfies round-by-round knowledge
    soundness. -/
theorem seqCompose_rbrKnowledgeSoundness
    (rel : ∀ i, Set (Stmt i × Wit i))
    (V : ∀ i, Verifier oSpec (Stmt i.castSucc) (Stmt i.succ) (pSpec i))
    (rbrKnowledgeError : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrKnowledgeSoundness init impl
      (rel i.castSucc) (rel i.succ) (rbrKnowledgeError i)) :
      (Verifier.seqCompose Stmt V).rbrKnowledgeSoundness init impl (rel 0) (rel (Fin.last m))
        (fun combinedIdx =>
          let ⟨i, idx⟩ := seqComposeChallengeEquiv.symm combinedIdx
          rbrKnowledgeError i idx) := by
  sorry

end Verifier

namespace OracleReduction

theorem seqCompose_completeness (hInit : init.neverFails)
    (rel : (i : Fin (m + 1)) → Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (R : ∀ i, OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
      (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i))
    (completenessError : Fin m → ℝ≥0)
    (h : ∀ i, (R i).completeness init impl (rel i.castSucc) (rel i.succ) (completenessError i)) :
      (OracleReduction.seqCompose Stmt OStmt Wit R).completeness
        init impl (rel 0) (rel (Fin.last m)) (∑ i, completenessError i) := by
  unfold completeness at h ⊢
  convert Reduction.seqCompose_completeness hInit rel (fun i => (R i).toReduction)
    completenessError h
  sorry

theorem seqCompose_perfectCompleteness (hInit : init.neverFails)
    (rel : (i : Fin (m + 1)) → Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (R : ∀ i, OracleReduction oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Wit i.castSucc)
      (Stmt i.succ) (OStmt i.succ) (Wit i.succ) (pSpec i))
    (h : ∀ i, (R i).perfectCompleteness init impl (rel i.castSucc) (rel i.succ)) :
      (OracleReduction.seqCompose Stmt OStmt Wit R).perfectCompleteness
        init impl (rel 0) (rel (Fin.last m)) := by
  unfold perfectCompleteness Reduction.perfectCompleteness
  convert seqCompose_completeness hInit rel R 0 h
  simp

end OracleReduction

namespace OracleVerifier

/-- If all verifiers in a sequence satisfy soundness with respective soundness errors, then their
  sequential composition also satisfies soundness.
  The soundness error of the sequentially composed oracle verifier is the sum of the individual
  errors. -/
theorem seqCompose_soundness
    (lang : (i : Fin (m + 1)) → Set (Stmt i × ∀ j, OStmt i j))
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i))
    (soundnessError : Fin m → ℝ≥0)
    (h : ∀ i, (V i).soundness init impl (lang i.castSucc) (lang i.succ) (soundnessError i)) :
      (OracleVerifier.seqCompose Stmt OStmt V).soundness init impl (lang 0) (lang (Fin.last m))
        (∑ i, soundnessError i) := by
  unfold OracleVerifier.soundness
  convert Verifier.seqCompose_soundness lang (fun i => (V i).toVerifier) soundnessError h
  sorry

/-- If all verifiers in a sequence satisfy knowledge soundness with respective knowledge errors,
    then their sequential composition also satisfies knowledge soundness.
    The knowledge error of the sequentially composed oracle verifier is the sum of the individual
    errors. -/
theorem seqCompose_knowledgeSoundness
    (rel : (i : Fin (m + 1)) → Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i))
    (knowledgeError : Fin m → ℝ≥0)
    (h : ∀ i, (V i).knowledgeSoundness init impl (rel i.castSucc) (rel i.succ) (knowledgeError i)) :
      (OracleVerifier.seqCompose Stmt OStmt V).knowledgeSoundness
        init impl (rel 0) (rel (Fin.last m)) (∑ i, knowledgeError i) := by
  unfold OracleVerifier.knowledgeSoundness
  convert Verifier.seqCompose_knowledgeSoundness rel (fun i => (V i).toVerifier) knowledgeError h
  sorry

/-- If all verifiers in a sequence satisfy round-by-round soundness with respective RBR soundness
    errors, then their sequential composition also satisfies round-by-round soundness. -/
theorem seqCompose_rbrSoundness
    (lang : (i : Fin (m + 1)) → Set (Stmt i × ∀ j, OStmt i j))
    (V : (i : Fin m) →
      OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc) (Stmt i.succ) (OStmt i.succ)
        (pSpec i))
    (rbrSoundnessError : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrSoundness init impl (lang i.castSucc) (lang i.succ) (rbrSoundnessError i)) :
      (OracleVerifier.seqCompose Stmt OStmt V).rbrSoundness
        init impl (lang 0) (lang (Fin.last m))
        (fun combinedIdx =>
          let ⟨i, idx⟩ := seqComposeChallengeEquiv.symm combinedIdx
          rbrSoundnessError i idx) := by
  unfold OracleVerifier.rbrSoundness
  convert Verifier.seqCompose_rbrSoundness lang (fun i => (V i).toVerifier)
    rbrSoundnessError h
  sorry

/-- If all verifiers in a sequence satisfy round-by-round knowledge soundness with respective RBR
    knowledge errors, then their sequential composition also satisfies round-by-round knowledge
    soundness. -/
theorem seqCompose_rbrKnowledgeSoundness
    (rel : ∀ i, Set ((Stmt i × ∀ j, OStmt i j) × Wit i))
    (V : (i : Fin m) → OracleVerifier oSpec (Stmt i.castSucc) (OStmt i.castSucc)
      (Stmt i.succ) (OStmt i.succ) (pSpec i))
    (rbrKnowledgeError : ∀ i, (pSpec i).ChallengeIdx → ℝ≥0)
    (h : ∀ i, (V i).rbrKnowledgeSoundness init impl
      (rel i.castSucc) (rel i.succ) (rbrKnowledgeError i)) :
    (OracleVerifier.seqCompose Stmt OStmt V).rbrKnowledgeSoundness
        init impl (rel 0) (rel (Fin.last m))
        (fun combinedIdx =>
          let ⟨i, idx⟩ := seqComposeChallengeEquiv.symm combinedIdx
          rbrKnowledgeError i idx) := by
  unfold OracleVerifier.rbrKnowledgeSoundness
  convert Verifier.seqCompose_rbrKnowledgeSoundness rel (fun i => (V i).toVerifier)
    rbrKnowledgeError h
  sorry

end OracleVerifier

end Security
