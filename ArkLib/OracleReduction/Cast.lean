/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.ProtocolSpec.Cast
import ArkLib.OracleReduction.Security.RoundByRound

/-!
  # Casting for structures of oracle reductions

  We define custom dependent casts (registered as `DCast` instances) for the following structures:
  - `(Oracle)Prover`
  - `(Oracle)Verifier`
  - `(Oracle)Reduction`

  Note that casting for `ProtocolSpec`s and related structures are defined in
  `OracleReduction/ProtocolSpec/Cast.lean`.

  We also show that casting preserves execution (up to casting of the transcripts) and thus security
  properties.
-/

open OracleComp

variable {ι : Type} {oSpec : OracleSpec ι}
  {StmtIn : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
  {WitIn : Type}
  {StmtOut : Type} {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type} [Oₛₒ : ∀ i, OracleInterface (OStmtOut i)]
  {WitOut : Type}
  {n₁ n₂ : ℕ} {pSpec₁ : ProtocolSpec n₁} {pSpec₂ : ProtocolSpec n₂}
  (hn : n₁ = n₂) (hSpec : pSpec₁.cast hn = pSpec₂)

open ProtocolSpec

namespace Prover

/-- Casting the prover of a non-oracle reduction across an equality of `ProtocolSpec`s. -/
protected def cast (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec₁) :
    Prover oSpec StmtIn WitIn StmtOut WitOut pSpec₂ where
  PrvState := P.PrvState ∘ Fin.cast (congrArg (· + 1) hn.symm)
  input := P.input
  sendMessage := fun i st => do
    let ⟨msg, newSt⟩ ← P.sendMessage (i.cast hn.symm (cast_symm hSpec)) st
    return ⟨(Message.cast_idx_symm hSpec) ▸ msg, newSt⟩
  receiveChallenge := fun i st => do
    let f ← P.receiveChallenge (i.cast hn.symm (cast_symm hSpec)) st
    return fun chal => f (Challenge.cast_idx hSpec ▸ chal)
  output := P.output ∘ (fun st => _root_.cast (by simp) st)

@[simp]
theorem cast_id :
    Prover.cast rfl rfl = (id : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec₁ → _) := by
  funext; simp [Prover.cast]; ext <;> simp; rfl

instance instDCast₂ : DCast₂ Nat ProtocolSpec
    (fun _ pSpec => Prover oSpec StmtIn WitIn StmtOut WitOut pSpec) where
  dcast₂ := Prover.cast
  dcast₂_id := Prover.cast_id

end Prover

namespace OracleProver

/-- Casting the oracle prover of a non-oracle reduction across an equality of `ProtocolSpec`s.

Internally invokes the `Prover.cast` function. -/
protected def cast (P : OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₁) :
    OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₂ :=
  Prover.cast hn hSpec P

@[simp]
theorem cast_id :
    OracleProver.cast rfl rfl =
      (id : OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₁ → _) := by
  sorry

instance instDCast₂OracleProver : DCast₂ Nat ProtocolSpec
    (fun _ pSpec => OracleProver oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec) where
  dcast₂ := OracleProver.cast
  dcast₂_id := OracleProver.cast_id

end OracleProver

namespace Verifier

/-- Casting the verifier of a non-oracle reduction across an equality of `ProtocolSpec`s.

This boils down to casting the (full) transcript. -/
protected def cast (V : Verifier oSpec StmtIn StmtOut pSpec₁) :
    Verifier oSpec StmtIn StmtOut pSpec₂ where
  verify := fun stmt transcript => V.verify stmt (dcast₂ hn.symm (dcast_symm hn hSpec) transcript)

@[simp]
theorem cast_id : Verifier.cast rfl rfl = (id : Verifier oSpec StmtIn StmtOut pSpec₁ → _) := by
  ext; simp [Verifier.cast]

instance instDCast₂Verifier :
    DCast₂ Nat ProtocolSpec (fun _ pSpec => Verifier oSpec StmtIn StmtOut pSpec) where
  dcast₂ := Verifier.cast
  dcast₂_id := by intros; funext; simp

theorem cast_eq_dcast₂ {V : Verifier oSpec StmtIn StmtOut pSpec₁} :
    V.cast hn hSpec = dcast₂ hn hSpec V := rfl

end Verifier

namespace OracleVerifier

variable [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
  [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]

open Function in
/-- Casting the oracle verifier of a non-oracle reduction across an equality of `ProtocolSpec`s.

TODO: need a cast of the oracle interfaces as well (i.e. the oracle interface instance is not
necessarily unique for every type) -/
protected def cast
    (hOₘ : ∀ i, Oₘ₁ i = dcast (Message.cast_idx hSpec) (Oₘ₂ (i.cast hn hSpec)))
    (V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec₁) :
    OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec₂ where
  verify := fun stmt challenges =>
    simulateQ sorry (V.verify stmt (dcast₂ hn.symm (dcast_symm hn hSpec) challenges))
  embed := V.embed.trans
    (Embedding.sumMap
      (Equiv.refl _).toEmbedding
      ⟨MessageIdx.cast hn hSpec, MessageIdx.cast_injective hn hSpec⟩)
  hEq := fun i => by
    simp [Embedding.sumMap, Equiv.refl]
    have := V.hEq i
    rw [this]
    split
    next a b h' => simp [h']
    next a b h' => simp [h']; exact (Message.cast_idx hSpec).symm

variable (hOₘ : ∀ i, Oₘ₁ i = dcast (Message.cast_idx hSpec) (Oₘ₂ (i.cast hn hSpec)))

@[simp]
theorem cast_id :
    OracleVerifier.cast rfl rfl (fun i => rfl) =
      (id : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec₁ → _) := by
  sorry

-- Need to cast oracle interface as well
-- instance instDCast₂OracleVerifier : DCast₃ Nat ProtocolSpec
--     (fun _ pSpec => OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec) where
--   dcast₂ := OracleVerifier.cast
--   dcast₂_id := OracleVerifier.cast_id

@[simp]
theorem cast_toVerifier (V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec₁) :
    (OracleVerifier.cast hn hSpec hOₘ V).toVerifier = Verifier.cast hn hSpec V.toVerifier := by
  sorry

end OracleVerifier

namespace Reduction

/-- Casting the reduction of a non-oracle reduction across an equality of `ProtocolSpec`s, which
  casts the underlying prover and verifier. -/
protected def cast (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec₁) :
    Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec₂ where
  prover := R.prover.cast hn hSpec
  verifier := R.verifier.cast hn hSpec

@[simp]
theorem cast_id :
    Reduction.cast rfl rfl = (id : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec₁ → _) := by
  funext; simp [Reduction.cast]

instance instDCast₂Reduction :
    DCast₂ Nat ProtocolSpec (fun _ pSpec => Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec) where
  dcast₂ := Reduction.cast
  dcast₂_id := Reduction.cast_id

end Reduction

namespace OracleReduction

variable [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
  [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  (hOₘ : ∀ i, Oₘ₁ i = dcast (Message.cast_idx hSpec) (Oₘ₂ (i.cast hn hSpec)))

/-- Casting the oracle reduction across an equality of `ProtocolSpec`s, which casts the underlying
  prover and verifier. -/
protected def cast (R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₁) :
    OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₂ where
  prover := R.prover.cast hn hSpec
  verifier := R.verifier.cast hn hSpec hOₘ

@[simp]
theorem cast_id :
    OracleReduction.cast rfl rfl (fun _ => rfl) =
      (id : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₁ → _) := by
  ext : 2 <;> simp [OracleReduction.cast]

-- Need to cast oracle interface as well
-- instance instDCast₂OracleReduction :
--     DCast₂ Nat ProtocolSpec
--     (fun _ pSpec => OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec)
-- where
--   dcast₂ := OracleReduction.cast
--   dcast₂_id := OracleReduction.cast_id

@[simp]
theorem cast_toReduction
    (R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₁) :
    (R.cast hn hSpec hOₘ).toReduction = Reduction.cast hn hSpec R.toReduction := by
  simp [OracleReduction.cast, Reduction.cast, OracleReduction.toReduction, OracleProver.cast]

end OracleReduction

section Execution

-- TODO: show that the execution of everything is the same, modulo casting of transcripts
variable {pSpec₁ : ProtocolSpec n₁} {pSpec₂ : ProtocolSpec n₂} (hSpec : pSpec₁.cast hn = pSpec₂)

namespace Prover

-- TODO: need to cast [pSpec₁.Challenge]ₒ to [pSpec₂.Challenge]ₒ, where they have the default
-- instance `challengeOracleInterface`

theorem cast_processRound (j : Fin n₁)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec₁)
    (currentResult : OracleComp (oSpec ++ₒ [pSpec₁.Challenge]ₒ)
      (Transcript j.castSucc pSpec₁ × P.PrvState j.castSucc)) :
    P.processRound j currentResult =
      cast (sorry) ((P.cast hn hSpec).processRound (Fin.cast hn j) sorry) := by
  sorry

theorem cast_runToRound (j : Fin (n₁ + 1)) (stmt : StmtIn) (wit : WitIn)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec₁) :
    P.runToRound j stmt wit =
      cast (sorry) ((P.cast hn hSpec).runToRound (Fin.cast (congrArg (· + 1) hn) j) stmt wit) := by
  sorry

theorem cast_run (stmt : StmtIn) (wit : WitIn)
    (P : Prover oSpec StmtIn WitIn StmtOut WitOut pSpec₁) :
    P.run stmt wit =
      cast (sorry) ((P.cast hn hSpec).run stmt wit) := by
  sorry

end Prover

namespace Verifier

variable (V : Verifier oSpec StmtIn StmtOut pSpec₁)

/-- The casted verifier produces the same output as the original verifier. -/
@[simp]
theorem cast_run (stmt : StmtIn) (transcript : FullTranscript pSpec₁) :
    V.run stmt transcript = (V.cast hn hSpec).run stmt (transcript.cast hn hSpec) := by
  simp only [Verifier.run, Verifier.cast, FullTranscript.cast, dcast₂]
  unfold Transcript.cast
  simp

end Verifier

namespace Reduction

variable (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec₁)

theorem cast_run (stmt : StmtIn) (wit : WitIn) :
    R.run stmt wit = cast (sorry) ((R.cast hn hSpec).run stmt wit) := by
  sorry

end Reduction

end Execution

section Security

open NNReal

variable {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
  [inst₁ : ∀ i, SelectableType (pSpec₁.Challenge i)]
  [inst₂ : ∀ i, SelectableType (pSpec₂.Challenge i)]
  (hChallenge : ∀ i, inst₁ i = dcast (by simp) (inst₂ (i.cast hn hSpec)))

section Protocol

variable {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}

namespace Reduction

variable (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec₁)

@[simp]
theorem cast_completeness (ε : ℝ≥0) (hComplete : R.completeness init impl relIn relOut ε) :
    (R.cast hn hSpec).completeness init impl relIn relOut ε := by
  sorry

@[simp]
theorem cast_perfectCompleteness (hComplete : R.perfectCompleteness init impl relIn relOut) :
    (R.cast hn hSpec).perfectCompleteness init impl relIn relOut :=
  cast_completeness hn hSpec R 0 hComplete

end Reduction

namespace Verifier

variable (V : Verifier oSpec StmtIn StmtOut pSpec₁)

@[simp]
theorem cast_rbrKnowledgeSoundness (ε : pSpec₁.ChallengeIdx → ℝ≥0)
    (hRbrKs : V.rbrKnowledgeSoundness init impl relIn relOut ε) :
    (V.cast hn hSpec).rbrKnowledgeSoundness init impl relIn relOut
      (ε ∘ (ChallengeIdx.cast hn.symm (cast_symm hSpec))) := by
  sorry

end Verifier

end Protocol

section OracleProtocol

variable [Oₘ₁ : ∀ i, OracleInterface (pSpec₁.Message i)]
  [Oₘ₂ : ∀ i, OracleInterface (pSpec₂.Message i)]
  (hOₘ : ∀ i, Oₘ₁ i = dcast (Message.cast_idx hSpec) (Oₘ₂ (i.cast hn hSpec)))
  {relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn)}
  {relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut)}

namespace OracleReduction

variable (R : OracleReduction oSpec StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut pSpec₁)

@[simp]
theorem cast_completeness (ε : ℝ≥0) (hComplete : R.completeness init impl relIn relOut ε) :
    (R.cast hn hSpec hOₘ).completeness init impl relIn relOut ε := by
  unfold completeness
  rw [cast_toReduction]
  exact Reduction.cast_completeness hn hSpec R.toReduction ε hComplete

@[simp]
theorem cast_perfectCompleteness (hComplete : R.perfectCompleteness init impl relIn relOut) :
    (R.cast hn hSpec hOₘ).perfectCompleteness init impl relIn relOut :=
  cast_completeness hn hSpec hOₘ R 0 hComplete

end OracleReduction

namespace OracleVerifier

variable (V : OracleVerifier oSpec StmtIn OStmtIn StmtOut OStmtOut pSpec₁)

@[simp]
theorem cast_rbrKnowledgeSoundness (ε : pSpec₁.ChallengeIdx → ℝ≥0)
    (hRbrKs : V.rbrKnowledgeSoundness init impl relIn relOut ε) :
    (V.cast hn hSpec hOₘ).rbrKnowledgeSoundness init impl relIn relOut
      (ε ∘ (ChallengeIdx.cast hn.symm (cast_symm hSpec))) := by
  unfold rbrKnowledgeSoundness
  rw [cast_toVerifier]
  exact Verifier.cast_rbrKnowledgeSoundness hn hSpec V.toVerifier ε hRbrKs

end OracleVerifier

end OracleProtocol

end Security
