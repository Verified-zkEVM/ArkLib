/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.OracleReduction.Security.RoundByRound
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.Basic

/-!
  # Simple Oracle Reduction - SendChallenge (the fold challenge round)

  A one-round, verifier-first (`V_to_P`) oracle reduction: the verifier samples a **challenge
  vector** `c : Fin ℓ → C`, sends it to the prover, and appends it to the output statement. There is
  no witness and **no check** — this is the definitional challenge-round building block of the
  Greyhound [NS24] / Hachi [NOZ26] fold ([NOZ26, Figure 3]), where `ℓ = 2ʳ` and `C ⊆ Rq`.

  A lone challenge round has no relation to extract into, so it is *not* coordinate-wise special
  sound on its own; its CWSS is established only as part of the surrounding fold block
  ([NOZ26, Lemma 8], out of scope here). What this file provides is:

  - the component itself (`oracleProver` / `oracleVerifier` / `oracleReduction`);
  - `instIsPure`: the verifier is pure — it reads the challenge off the transcript and appends it,
    with no runtime check — so it can be a left factor in a CWSS `append`;
  - `foldBlockStructure`: the `CWSSStructure` this round contributes to the block — one challenge
    round with `coordIndex = ℓ`, `alphabet = C`, `soundnessParam = 2` (so `arity = ℓ·(2−1)+1 = ℓ+1`
    and `nodeOk = IsSpecialSoundFamily ℓ 2`), matching [NOZ26, Lemma 4 / Definition 3] exactly.

  To *run* the reduction (completeness / soundness) one additionally needs
  `[SampleableType (Fin ℓ → C)]` (available from `[SampleableType C]` via the derived `Fin`-domain
  product instance); it is not required for the definitions, `IsPure`, or the structure above.

  ## References

  * [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

open OracleSpec OracleComp OracleQuery OracleInterface ProtocolSpec Function

namespace SendChallenge

variable {ι : Type} (oSpec : OracleSpec ι) (Statement : Type)
  {ιₛ : Type} (OStatement : ιₛ → Type) [∀ i, OracleInterface (OStatement i)]
  (C : Type) (ℓ : ℕ)

/-- One `V_to_P` challenge round carrying the fold challenge vector `c : Fin ℓ → C`. -/
@[reducible]
def pSpec : ProtocolSpec 1 := ⟨!v[.V_to_P], !v[Fin ℓ → C]⟩

/-- The oracle prover receives the challenge `c` and appends it to the statement (the oracle
statements pass through). It has no message to send. -/
@[inline, specialize]
def oracleProver : OracleProver oSpec
    Statement OStatement Unit
    (Statement × (Fin ℓ → C)) OStatement Unit (pSpec C ℓ) where
  PrvState
  | 0 => Statement × (∀ i, OStatement i)
  | 1 => (Statement × (∀ i, OStatement i)) × (Fin ℓ → C)
  input := Prod.fst
  sendMessage | ⟨0, h⟩ => nomatch h
  receiveChallenge | ⟨0, _⟩ => fun st => pure fun c => (st, c)
  output := fun ⟨⟨stmt, oStmt⟩, c⟩ => pure (((stmt, c), oStmt), ())

/-- The oracle verifier samples the challenge `c` (as the `V_to_P` round), reads it off the
transcript, and appends it to the output statement — no check. This keeps it pure. -/
def outputEmbedding : OracleOutputEmbedding OStatement (pSpec C ℓ).Message OStatement where
  embed := Function.Embedding.inl
  hEq := by
    intro i
    rw [show Function.Embedding.inl i = Sum.inl i from rfl]
  outputInterface_heq := by
    intro i
    rw [show Function.Embedding.inl i = Sum.inl i from rfl]

@[inline, specialize]
def oracleVerifier : OracleVerifier oSpec
    Statement OStatement (Statement × (Fin ℓ → C)) OStatement (pSpec C ℓ) where
  verify := fun stmt chal => pure (stmt, chal ⟨0, rfl⟩)
  outputOracle := .inl (outputEmbedding OStatement C ℓ)

@[simp]
theorem oracleVerifier_materializeOutput (challenges : (pSpec C ℓ).Challenges)
    (oStmt : ∀ i, OStatement i) (messages : (pSpec C ℓ).Messages) :
    (oracleVerifier oSpec Statement OStatement C ℓ).materializeOutput
        challenges oStmt messages = oStmt := by
  unfold OracleVerifier.materializeOutput oracleVerifier
  change OracleVerifier.materializeOutputOracle
      (Sum.inl (outputEmbedding OStatement C ℓ)) challenges oStmt messages = oStmt
  simp only [OracleVerifier.materializeOutputOracle]
  funext i
  simp only [outputEmbedding]
  rfl

/-- The oracle reduction for `SendChallenge`. -/
@[inline, specialize]
def oracleReduction : OracleReduction oSpec
    Statement OStatement Unit
    (Statement × (Fin ℓ → C)) OStatement Unit (pSpec C ℓ) where
  prover := oracleProver oSpec Statement OStatement C ℓ
  verifier := oracleVerifier oSpec Statement OStatement C ℓ

instance : VerifierOnly (pSpec C ℓ) where
  verifier_first' := by simp

variable {Statement} {OStatement} {C} {ℓ}

/-- The pure verifier's underlying non-oracle verifier returns the statement together with the
sampled challenge (read off the transcript), with the oracle statements passed through. -/
theorem oracleVerifier_toVerifier_run {stmt : Statement} {oStmt : ∀ i, OStatement i}
    {tr : (pSpec C ℓ).FullTranscript} :
    (oracleVerifier oSpec Statement OStatement C ℓ).toVerifier.run ⟨stmt, oStmt⟩ tr =
      pure ⟨(stmt, tr.challenges ⟨0, rfl⟩), oStmt⟩ := by
  simp only [Verifier.run, OracleVerifier.toVerifier]
  rw [oracleVerifier_materializeOutput]
  rfl

/-- The `SendChallenge` oracle verifier is pure: it deterministically appends the (transcript-read)
challenge to the statement. This discharges the deterministic-left hypothesis of the CWSS append,
letting the challenge round sit as a left factor in the fold block. -/
instance instIsPure : (oracleVerifier oSpec Statement OStatement C ℓ).toVerifier.IsPure :=
  ⟨fun p tr => ⟨(p.1, tr.challenges ⟨0, rfl⟩), p.2⟩,
   fun ⟨_, _⟩ _ => oracleVerifier_toVerifier_run (oSpec := oSpec)⟩

/-- The **fold-block coordinate-wise structure**: the single challenge round of `SendChallenge`
carries `ℓ` coordinates over the alphabet `C`, decomposed by the identity (`Challenge = Fin ℓ → C`
already), with soundness parameter `k = 2`. Hence `arity = ℓ·(2−1)+1 = ℓ+1` and the node predicate
is `IsSpecialSoundFamily ℓ 2` — exactly the branching required by [NOZ26, Lemma 4 / Definition 3]
(with `ℓ = 2ʳ`). This is the shape the fold block's CWSS ([NOZ26, Lemma 8]) is proven against.

The component is deliberately generic over `ℓ` (only `0 < ℓ` is needed): the power-of-two
instantiation `ℓ = 2ʳ` of Figure 3 is imposed by the caller in the `QuadEval` composition layer,
not here. -/
def foldBlockStructure (hℓ : 0 < ℓ) : CWSSStructure (pSpec C ℓ) where
  coordIndex := fun _ => ⟨ℓ, hℓ⟩
  alphabet := fun _ => C
  decompose := fun i => Equiv.cast (by rcases i with ⟨j, hj⟩; fin_cases j; rfl)
  soundnessParam := fun _ => ⟨2, le_refl 2⟩
  arity := fun _ => ℓ * (2 - 1) + 1
  arity_eq := rfl

end SendChallenge
