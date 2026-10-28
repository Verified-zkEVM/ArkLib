/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
import ArkLib.ProofSystem.Binius.BinaryBasefold.Spec

/-! # Point-query interfaces of Binary Basefold commitment messages -/

namespace Binius.BinaryBasefold

noncomputable section
open OracleSpec ProtocolSpec AdditiveNTT

variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L] [CharP L 2]
  [SampleableType L]
variable (𝔽q : Type) [Field 𝔽q] [Fintype 𝔽q] [DecidableEq 𝔽q]
  [h_Fq_char_prime : Fact (Nat.Prime (ringChar 𝔽q))] [hF₂ : Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [hβ_lin_indep : Fact (LinearIndependent 𝔽q β)]
  [h_β₀_eq_1 : Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} (γ_repetitions : ℕ) [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ]
variable {h_ℓ_add_R_rate : ℓ + 𝓡 < r} -- ℓ ∈ {1, ..., r-1}
variable [hdiv : Fact (ϑ ∣ ℓ)]


-- Commitment messages expose point queries, never the entire codeword.
example (i : Fin ℓ) : @OracleInterface.Query _
    (instOracleInterfaceMessagePSpecCommit 𝔽q β
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) ⟨0, rfl⟩) =
    sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + 1, by omega⟩ := rfl

example (i : Fin ℓ) (x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + 1, by omega⟩) :
    @OracleInterface.Response _
      (instOracleInterfaceMessagePSpecCommit 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) ⟨0, rfl⟩) x = L := rfl

example (i : Fin ℓ)
    (f : (pSpecCommit 𝔽q β (h_ℓ_add_R_rate := h_ℓ_add_R_rate) i).Message ⟨0, rfl⟩)
    (x : sDomain 𝔽q β h_ℓ_add_R_rate ⟨i.val + 1, by omega⟩) :
    @OracleInterface.answer _
      (instOracleInterfaceMessagePSpecCommit 𝔽q β
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (i := i) ⟨0, rfl⟩) f x = f x := rfl

end

end Binius.BinaryBasefold
