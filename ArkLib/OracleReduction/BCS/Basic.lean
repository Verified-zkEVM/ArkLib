/-
Copyright (c) 2024 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.CommitmentScheme.Basic
import ArkLib.OracleReduction.Composition.Sequential.General

/-!
  # The BCS Transformation

  This file defines the (generalized) BCS transformation. This transformation was first described by
  Ben-Sasson - Chiesa - Spooner in TCC'16 for IOPs with vector queries + Merkle trees. Our
  generalized version transforms any Interactive Oracle Reduction (IOR) into an Interactive
  Reduction (IR) using commitment schemes for the respective oracle messages of the protocol. This
  captures both the original BCS transformation as well as the Polynomial IOP + Polynomial
  Commitments transform (described in Plonk, Marlin, etc.).

  More precisely, the transformation works as follows:

  1. We take in an IOR `R`.

  2. We replace every oracle statement and every prover's message with a commitment (using the
     specified corresponding commitment scheme).

  3. We look at the oracle verifier's list of queries to the prover's messages. For each query, we
     run the opening argument for the query (which is itself an interactive proof).

  After defining the transformation, our goal is to show that the transformed protocol inherits the
  security properties of its building blocks (i.e. completeness, all notions of soundness, HVZK,
  etc.)

  ## Notes

  The BCS transform has a lot of degrees of freedom. For instance, we can choose to run the opening
  arguments for each verifier's query in any order.

  There are also a lot of variants and avenues for optimization:

  - We can ``batch'' many opening arguments together (using homomorphic properties of the commitment
    scheme, or via another round of interaction, or via specialized techniques like Merkle capping).
-/

variable {n : ℕ}

namespace ProtocolSpec

/-- Switch the type of prover's messages in a protocol specification. The directions are preserved.
-/
def renameMessage (pSpec : ProtocolSpec n) (NewMessage : pSpec.MessageIdx → Type) :
    ProtocolSpec n :=
  ⟨ pSpec.dir,
    fun i => if h : pSpec.dir i = Direction.P_to_V then NewMessage ⟨i, h⟩ else pSpec.«Type» i⟩

-- def BCSTransform (pSpec : ProtocolSpec n)
--     {queries : List ((i : pSpec.MessageIdx) × (pSpec.Message i))}
  --   (pSpecCom : ∀ i, ProtocolSpec (nCom i)) (CommType : pSpec.MessageIdx → Type) :
  --     ProtocolSpec (n + ∑ i, nCom i) :=
  -- .append (pSpec.renameMessage CommType) (sorry)

end ProtocolSpec

namespace OracleReduction

variable {pSpec : ProtocolSpec n} {ι : Type} {oSpec : OracleSpec ι}
    [Oₘ : ∀ i, OracleInterface (pSpec.Message i)]

variable {nCom : pSpec.MessageIdx → ℕ} {pSpecCom : ∀ i, ProtocolSpec (nCom i)}
    {Randomness : pSpec.MessageIdx → Type} {CommitmentType : pSpec.MessageIdx → Type}

variable {StmtIn StmtOut WitIn WitOut : Type}
    {ιₛᵢ : Type} {OStmtIn : ιₛᵢ → Type} [Oₛᵢ : ∀ i, OracleInterface (OStmtIn i)]
    {ιₛₒ : Type} {OStmtOut : ιₛₒ → Type}

-- def BCSTransform (reduction : OracleReduction pSpec oSpec StmtIn StmtOut WitIn WitOut OStmtIn OStmtOut) :
--     Reduction (pSpec.BCSTransform commitmentScheme) oSpec StmtIn StmtOut WitIn WitOut :=
--     sorry

end OracleReduction
