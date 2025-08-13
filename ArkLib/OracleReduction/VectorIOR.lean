/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.OracleReduction.Security.RoundByRound

/-!
# Vector Interactive Oracle Reductions

We define vector interactive oracle reductions (V-IOR) and vector interactive oracle proofs
(V-IOPs), as special cases IORs/IOPs where all messages and oracle statements are vectors over some
alphabet. We also define their proximity versions, V-IORP and V-IOPP, which exhibit a gap between
the relation for completeness and the relation for soundness.

This is the original formulation of IOPs in [BCS16]. Many IOPs of interest in the literature are of
this form, and so we isolate this special case for ease of notation and reasoning.

We also define complexity measures for V-IORs, such as proof length and verifier's query complexity.

-/

namespace ProtocolSpec

/-- The protocol specification for a V-IOR, which consists of the direction of each message and its
  length.

(assumed to be working over a fixed alphabet) -/
@[ext]
structure VectorSpec (n : ℕ) where
  dir : Fin n → Direction
  length : Fin n → Nat

namespace VectorSpec

variable {n : ℕ}

/-- Convert a `VectorSpec` into a `ProtocolSpec` for a given alphabet type `A`. The `i`-th message
  is a vector of length `vPSpec i.2` over `A`.

Note that we give the `Vector A n` type for this, instead of `Fin n → A`, for better performance in
(future) implementations. We may revisit this choice in the future. -/
@[reducible, simp]
def toProtocolSpec (A : Type) (vPSpec : VectorSpec n) : ProtocolSpec n :=
  ⟨vPSpec.dir, fun i => Vector A (vPSpec.length i)⟩

/-- The type of indices for messages in a `VectorSpec`. -/
@[reducible, inline, specialize, simp]
def MessageIdx (vPSpec : VectorSpec n) := {i : Fin n // vPSpec.dir i = .P_to_V}

/-- The type of indices for challenges in a `VectorSpec`. -/
@[reducible, inline, specialize, simp]
def ChallengeIdx (vPSpec : VectorSpec n) := {i : Fin n // vPSpec.dir i = .V_to_P}

/-- The length of the `i`-th prover's message in a `VectorSpec`. -/
@[reducible]
def messageLength (vPSpec : VectorSpec n) (i : MessageIdx vPSpec) : Nat := vPSpec.length i

/-- The length of the `i`-th challenge in a `VectorSpec`. -/
@[reducible]
def challengeLength (vPSpec : VectorSpec n) (i : ChallengeIdx vPSpec) : Nat := vPSpec.length i

/-- The total length of all messages in a `VectorSpec`. -/
@[reducible]
def totalMessageLength (vPSpec : VectorSpec n) : Nat := ∑ i, vPSpec.messageLength i

/-- The total length of all challenges in a `VectorSpec`
  (i.e. the verifier's randomness complexity). -/
@[reducible]
def totalChallengeLength (vPSpec : VectorSpec n) : Nat := ∑ i, vPSpec.challengeLength i

variable {A : Type} {vPSpec : VectorSpec n}

/-- All messages in an V-IOR have the same vector oracle interface. -/
instance : OracleInterfaces (vPSpec.toProtocolSpec A) where
  oracleInterfaces := fun _ => some instOracleInterfaceVector

instance : ∀ i, OracleInterface ((vPSpec.toProtocolSpec A).Message i) :=
  fun _ => instOracleInterfaceVector

instance [VCVCompatible A] : ∀ i, VCVCompatible ((vPSpec.toProtocolSpec A).Challenge i) :=
  fun _ => by dsimp; infer_instance

end VectorSpec

end ProtocolSpec

variable {n : ℕ} {ι : Type}

/-- Vector Interactive Oracle Reductions.

  This is just a specialization of `OracleReduction` to the case where all messages and oracle
  statements are vectors over some alphabet, and there is no shared oracle.

  We do _not_ require the (oracle) statements and witnesses to be vectors as well, though this can
  be done if needed. -/
@[reducible]
def VectorIOR
    (StmtIn : Type) {ιₛᵢ : Type} (OStmtIn : ιₛᵢ → Type) (WitIn : Type)
    (StmtOut : Type) {ιₛₒ : Type} (OStmtOut : ιₛₒ → Type) (WitOut : Type)
    (vPSpec : ProtocolSpec.VectorSpec n) (A : Type)
    [∀ i, OracleInterface (OStmtIn i)] :=
  OracleReduction []ₒ StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut (vPSpec.toProtocolSpec A)

/-- Vector Interactive Oracle Proofs

This is just a specialization of `OracleProof` to the case where all messages and oracle statements
are vectors over some alphabet. We do _not_ require the (oracle) statements and witnesses to be
vectors as well, though this can be done if needed. -/
@[reducible]
def VectorIOP
    (Statement : Type) {ιₛ : Type} (OStatement : ιₛ → Type) (Witness : Type)
    (vPSpec : ProtocolSpec.VectorSpec n) (A : Type)
    [∀ i, OracleInterface (OStatement i)] :=
  OracleProof []ₒ Statement OStatement Witness (vPSpec.toProtocolSpec A)

variable {n : ℕ} {vPSpec : ProtocolSpec.VectorSpec n} {A : Type}
  [OracleComp.SelectableType A]

open scoped NNReal

namespace VectorIOR

variable {StmtIn WitIn StmtOut WitOut : Type} {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type}
  [∀ i, OracleInterface (OStmtIn i)] {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}

/-- A vector IOR is **secure** with respect to input relation `relIn`, output relation `relOut`, and
    round-by-round knowledge error `ε_rbr` if it satisfies (perfect) completeness and round-by-round
    knowledge soundness with respect to `relIn`, `relOut`, and `ε_rbr`. -/
class IsSecure
    (relIn : Set ((StmtIn × ∀ i, OStmtIn i) × WitIn))
    (relOut : Set ((StmtOut × ∀ i, OStmtOut i) × WitOut))
    (ε_rbr : vPSpec.ChallengeIdx → ℝ≥0)
    (vectorIOR : VectorIOR StmtIn OStmtIn WitIn StmtOut OStmtOut WitOut vPSpec A) where

  /-- The reduction is perfectly complete. -/
  is_complete : vectorIOR.perfectCompleteness (pure ()) ⟨isEmptyElim⟩ relIn relOut

  /-- The reduction is round-by-round knowledge sound with respect to `relIn`, `relOut`,
    `ε_rbr`, and the state function. -/
  is_rbr_knowledge_sound :
    vectorIOR.verifier.rbrKnowledgeSoundness (pure ()) ⟨isEmptyElim⟩ relIn relOut ε_rbr

-- TODO: define V-IOR of proximity

end VectorIOR

namespace VectorIOP

variable {Statement Witness : Type} {ιₛ : Type} {OStatement : ιₛ → Type}
  [∀ i, OracleInterface (OStatement i)]

/-- A vector IOP is **secure** with respect to relation `relation` and round-by-round knowledge
    error `ε_rbr` if it satisfies (perfect) completeness and round-by-round knowledge soundness
    with respect to `relation` and `ε_rbr`. -/
class IsSecure
    (relation : Set ((Statement × ∀ i, OStatement i) × Witness))
    (ε_rbr : vPSpec.ChallengeIdx → ℝ≥0)
    (vectorIOP : VectorIOP Statement OStatement Witness vPSpec A) where

  /-- The reduction is perfectly complete. -/
  is_complete : vectorIOP.perfectCompleteness (pure ()) ⟨isEmptyElim⟩ relation

  /-- The reduction is round-by-round knowledge sound with respect to `relIn`, `relOut`,
    `ε_rbr`, and the state function. -/
  is_rbr_knowledge_sound :
    OracleProof.rbrKnowledgeSoundness (pure ()) ⟨isEmptyElim⟩ relation vectorIOP.verifier ε_rbr

/-- A vector IOP **of proximity** is **secure** with respect to completeness relation
  `completeRelation`, soundness relation `soundRelation`, and round-by-round knowledge error
  `ε_rbr` if it satisfies:
  - (perfect) completeness with respect to `completeRelation`,
  - round-by-round knowledge soundness with respect to `soundRelation` and `ε_rbr`. -/
class IsSecureWithGap
    (completeRelation : Set ((Statement × ∀ i, OStatement i) × Witness))
    (soundRelation : Set ((Statement × ∀ i, OStatement i) × Witness))
    (ε_rbr : vPSpec.ChallengeIdx → ℝ≥0)
    (vectorIOP : VectorIOP Statement OStatement Witness vPSpec A) where

  /-- The reduction is perfectly complete. -/
  is_complete : vectorIOP.perfectCompleteness (pure ()) ⟨isEmptyElim⟩ completeRelation

  /-- The reduction is round-by-round knowledge sound with respect to `relIn`, `relOut`,
    `ε_rbr`, and the state function. -/
  is_rbr_knowledge_sound :
    OracleProof.rbrKnowledgeSoundness (pure ()) ⟨isEmptyElim⟩ soundRelation vectorIOP.verifier ε_rbr

end VectorIOP
