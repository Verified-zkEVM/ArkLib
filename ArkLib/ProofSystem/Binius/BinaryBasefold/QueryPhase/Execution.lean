/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao, Alexander Hicks
-/
module

public import ArkLib.ProofSystem.Binius.BinaryBasefold.QueryPhase.Folding

/-!
# Exact execution of Binary Basefold's query checks

These identities retain the input/message oracle simulation and its rejection behavior.
They use the public simulation laws for the concrete Binary Basefold query programs.
-/

@[expose] public section

open OracleSpec OracleComp ProtocolSpec AdditiveNTT

namespace Binius.BinaryBasefold.QueryPhase
noncomputable section
variable {r : ℕ} [NeZero r]
variable {L : Type} [Field L] [Fintype L] [DecidableEq L]
variable (𝔽q : Type) [Field 𝔽q]
local instance [Finite 𝔽q] : Fact (Nat.Prime (ringChar 𝔽q)) :=
  ⟨CharP.prime_ringChar 𝔽q⟩
variable [Fintype 𝔽q] [DecidableEq 𝔽q]
  [Fact (Fintype.card 𝔽q = 2)]
variable [Algebra 𝔽q L]
variable (β : Fin r → L) [Fact (LinearIndependent 𝔽q β)] [Fact (β 0 = 1)]
variable {ℓ 𝓡 ϑ : ℕ} [NeZero ℓ] [NeZero 𝓡] [NeZero ϑ] {h_ℓ_add_R_rate : ℓ + 𝓡 < r}
variable [hdiv : Fact (ϑ ∣ ℓ)]

omit [Fact (Fintype.card 𝔽q = 2)] in
/-- Each step simulation queries its fiber, checks the carried value, and returns the local fold.
-/
theorem checkSingleFoldingStep_simulate (γ : ℕ)
    (oStmt : ∀ j, OracleStatement 𝔽q β (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) (Fin.last ℓ) j)
    (messages : ∀ i, (pSpecQuery 𝔽q β γ (h_ℓ_add_R_rate := h_ℓ_add_R_rate)).Message i)
    (k : Fin (ℓ / ϑ)) (v : sDomain 𝔽q β h_ℓ_add_R_rate ⟨0, by omega⟩)
    (c : L) (stmt : FinalSumcheckStatementOut (L := L) (ℓ := ℓ)) :
    simulateQ (OracleInterface.simOracle2 []ₒ oStmt messages)
      (checkSingleFoldingStep 𝔽q β (γ_repetitions := γ) (ϑ := ϑ)
        (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k c v stmt).run =
      (do
        if k.val * ϑ > 0 then
          guard (c = logicalQueryFiberPoints 𝔽q β oStmt k v
            (extractMiddleFinMask 𝔽q β v
              ⟨k.val * ϑ, by
                have hh := k_succ_mul_ϑ_le_ℓ_₂ (k := k)
                omega⟩ ϑ))
        pure (logicalComputeFoldedValue 𝔽q β k v stmt
          (logicalQueryFiberPoints 𝔽q β oStmt k v)) : OptionT (OracleComp []ₒ) L).run := by
  let so := OracleInterface.simOracle2 []ₒ oStmt messages
  let vec := (⟨Array.finRange (2 ^ ϑ), by simp⟩ : Vector (Fin (2 ^ ϑ)) (2 ^ ϑ)).map
    (logicalQueryFiberPoints 𝔽q β oStmt k v)
  have hf : (simulateQ so (queryFiberPoints 𝔽q β (γ_repetitions := γ) (ϑ := ϑ)
      (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k v) : OptionT (OracleComp []ₒ) (Vector L (2 ^ ϑ))) =
      (pure vec : OptionT (OracleComp []ₒ) (Vector L (2 ^ ϑ))) :=
    queryFiberPoints_simulate 𝔽q β γ oStmt messages k v
  have hget : vec.get = logicalQueryFiberPoints 𝔽q β oStmt k v := by
    funext u
    simp [vec, Vector.get_eq_getElem]
  change (simulateQ so (checkSingleFoldingStep 𝔽q β (γ_repetitions := γ) (ϑ := ϑ)
    (h_ℓ_add_R_rate := h_ℓ_add_R_rate) k c v stmt) : OptionT (OracleComp []ₒ) L) = _
  dsimp only [checkSingleFoldingStep]
  rw [simulateQ_optionT_bind, hf, pure_bind, hget]
  dsimp only [logicalComputeFoldedValue]
  simp only [guard_eq]
  split_ifs <;> rfl

end
end Binius.BinaryBasefold.QueryPhase
