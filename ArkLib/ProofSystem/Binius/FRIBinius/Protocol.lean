/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.Opening

/-!
# FRI-Binius opening composition

The modular protocol runs the full ring-switching reduction before opening its packed evaluation
claim with the equality multiplier. The unrolled protocol runs only the batching head before
opening its product claim with the ring-switching multiplier. Both pass the original input
oracle unchanged to the same Binary Basefold opening schedule.

The opening starts with a zero-message adapter: it formats the claim and initializes the prover's
opening witness without adding a round. The abstract prefixes pass a packed polynomial; the
executable prefixes pass its Boolean evaluation table, interpreted by multilinear extension.
-/

@[expose] public section

namespace Binius.FRIBinius

open AdditiveNTT OracleSpec ProtocolSpec Sumcheck.Structured
open BinaryBasefold

variable {r m R ϑ : ℕ} [NeZero r] [NeZero m] [NeZero R] [NeZero ϑ] [Fact (ϑ ∣ m)]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [SampleableType L]
variable (K : Type) [Field K] [Fintype K] [DecidableEq K] [Fact (Fintype.card K = 2)]
  [Algebra K L] (β : Fin r → L) [Fact (LinearIndependent K β)]
variable (hRate : m + R < r)

local instance [Finite K] : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩

/-- The input codeword oracle family for opening packed-polynomial claims. -/
abbrev openingOracles := OracleStatement K β (h_ℓ_add_R_rate := hRate) ϑ 0

/-- The zero-message claim adapter followed by the Binary Basefold sum-check-and-fold and query
phases. -/
abbrev openingWire (γ : ℕ) :=
  (!p[] : ProtocolSpec 0) ++ₚ fullPSpec K β γ (ϑ := ϑ) (h_ℓ_add_R_rate := hRate)

variable [Fact (β 0 = 1)]
variable {n : ℕ} {pPrefix : ProtocolSpec n} [∀ j, OracleInterface (pPrefix.Message j)]
variable {StmtIn StmtMid Context : Type}

/-- Verify the prefix, then use `toProductClaim` and `multiplier` to open its claim against
the oracle family forwarded by the prefix. -/
def appendOpeningVerifier
    (prefixVerifier : OracleVerifier []ₒ StmtIn (openingOracles K β (ϑ := ϑ) hRate)
      StmtMid (openingOracles K β (ϑ := ϑ) hRate) pPrefix)
    (multiplier : Multiplier Context L m) (toProductClaim : StmtMid → Context × L) (γ : ℕ) :
    OracleProofVerifier []ₒ StmtIn (openingOracles K β (ϑ := ϑ) hRate)
      (pPrefix ++ₚ openingWire K β (ϑ := ϑ) hRate γ)
      (Oₘ := instOracleInterfaceMessageAppend (pSpec₁ := pPrefix)
        (pSpec₂ := openingWire K β (ϑ := ϑ) hRate γ)) :=
  OracleVerifier.append (Oₛ₃ := fun i : Empty => nomatch i) prefixVerifier
    (ProductClaim.openingVerifier K β multiplier toProductClaim γ (ϑ := ϑ) (h_rate := hRate))

/-- Run the prefix, then use `witnessEquiv` to interpret its packed witness as the multilinear
polynomial for the Binary Basefold opening. -/
def appendOpeningReduction {WitIn WitMid : Type}
    (prefixReduction : OracleReduction []ₒ StmtIn (openingOracles K β (ϑ := ϑ) hRate) WitIn
      StmtMid (openingOracles K β (ϑ := ϑ) hRate) WitMid pPrefix)
    (multiplier : Multiplier Context L m) (toProductClaim : StmtMid → Context × L)
    (witnessEquiv : WitMid ≃ MultilinearPoly L m) (γ : ℕ) :
    OracleProof []ₒ StmtIn (openingOracles K β (ϑ := ϑ) hRate) WitIn
      (pPrefix ++ₚ openingWire K β (ϑ := ϑ) hRate γ)
      (Oₘ := instOracleInterfaceMessageAppend (pSpec₁ := pPrefix)
        (pSpec₂ := openingWire K β (ϑ := ϑ) hRate γ)) :=
  OracleReduction.append (Oₛ₃ := fun i : Empty => nomatch i) prefixReduction
    (ProductClaim.openingReduction K β multiplier toProductClaim witnessEquiv γ
      (ϑ := ϑ) (h_rate := hRate))

end Binius.FRIBinius
