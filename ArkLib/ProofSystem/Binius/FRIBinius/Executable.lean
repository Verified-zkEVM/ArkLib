/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.ProofSystem.Binius.FRIBinius.Prelude
public import ArkLib.ProofSystem.Binius.BinaryBasefold.Opening
public import ArkLib.ProofSystem.RingSwitching.Packing.Computable

/-!
# Executable small-field Binius openings

The ring-switching message carries column coordinates. The honest prover carries the Boolean
evaluation table until Binary Basefold needs the multilinear witness. The verifier uses the
matrix multiplier evaluator, not the Boolean table of the multiplier.
-/

@[expose] public section

namespace Binius.FRIBinius.Executable

open AdditiveNTT Module OracleSpec ProtocolSpec RingSwitching RingSwitching.Packing
open BinaryBasefold Sumcheck.Structured

variable {κ ℓ ℓ' R ϑ : ℕ}
variable {K L : Type} [Field K] [Fintype K] [DecidableEq K] [Fact (Fintype.card K = 2)]
  [Field L] [Fintype L] [DecidableEq L] [SampleableType L] [Algebra K L]
variable [NeZero κ] [NeZero ℓ'] [NeZero R] [NeZero ϑ] [Fact (ϑ ∣ ℓ')]
variable (β : Fin (2 ^ κ) → L)
  [hIndependent : Fact (LinearIndependent K β)] [Fact (β 0 = 1)]
variable (coordinates : L → (Fin κ → Fin 2) → K)

/-- The supplied arithmetic operations are the vectors and coordinate map of a basis. -/
def CoordinatesAgree : Prop :=
  ∃ b : Basis (Fin (2 ^ κ)) K L, (⇑b) = β ∧
    coordinates = fun x u => b.repr x (finFunctionFinEquiv u)

local instance [Finite K] : Fact (Nat.Prime (ringChar K)) :=
  ⟨CharP.prime_ringChar K⟩

/-- The unchanged family of Binary BaseFold input codeword oracles. -/
abbrev inputOracleFamily (hRate : ℓ' + R < 2 ^ κ) :=
  OracleStatement K β (h_ℓ_add_R_rate := hRate) ϑ 0

/-- The Binary BaseFold opening suffix, including its zero-message input adapter. -/
abbrev openingPSpec (hRate : ℓ' + R < 2 ^ κ) (γ : ℕ) :=
  (!p[] : ProtocolSpec 0) ++ₚ fullPSpec K β γ (ϑ := ϑ) (h_ℓ_add_R_rate := hRate)

/-- A coordinate batching message followed by the original Binary BaseFold opening. -/
abbrev unrolledPSpec (hRate : ℓ' + R < 2 ^ κ) (γ : ℕ) :=
  Packing.Computable.headPSpec L κ ++ₚ openingPSpec (K := K) (ϑ := ϑ) β hRate γ

/-- The full coordinate ring-switching prefix followed by the original Binary BaseFold opening. -/
abbrev modularPSpec (hRate : ℓ' + R < 2 ^ κ) (γ : ℕ) :=
  Packing.Computable.ringSwitchPSpec L κ ℓ' ++ₚ openingPSpec (K := K) (ϑ := ϑ) β hRate γ

instance (hRate : ℓ' + R < 2 ^ κ) (γ : ℕ) : ∀ i, OracleInterface
    ((unrolledPSpec (K := K) (ϑ := ϑ) β hRate γ).Message i) :=
  instOracleInterfaceMessageAppend (pSpec₁ := Packing.Computable.headPSpec L κ)

instance (hRate : ℓ' + R < 2 ^ κ) (γ : ℕ) : ∀ i, SampleableType
    ((unrolledPSpec (K := K) (ϑ := ϑ) β hRate γ).Challenge i) :=
  instSampleableTypeChallengeAppend (pSpec₁ := Packing.Computable.headPSpec L κ)

instance (hRate : ℓ' + R < 2 ^ κ) (γ : ℕ) : ∀ i, OracleInterface
    ((modularPSpec (K := K) (ϑ := ϑ) β hRate γ).Message i) :=
  instOracleInterfaceMessageAppend (pSpec₁ := Packing.Computable.ringSwitchPSpec L κ ℓ')

instance (hRate : ℓ' + R < 2 ^ κ) (γ : ℕ) : ∀ i, SampleableType
    ((modularPSpec (K := K) (ϑ := ϑ) β hRate γ).Challenge i) :=
  instSampleableTypeChallengeAppend (pSpec₁ := Packing.Computable.ringSwitchPSpec L κ ℓ')

omit [Fintype L] [SampleableType L] in
/-- The opening receives the same packed polynomial as the interpretation of the
ring-switching prover's output table. -/
theorem tableWitnessEquiv_apply_eq {n : ℕ} (packed : (Fin n → Fin 2) → L) :
    tableWitnessEquiv packed = Packing.Computable.toMultilinear packed := by
  rw [tableWitnessEquiv_apply]
  apply (MvPolynomial.MLEEquiv (R := L) (σ := Fin n)).injective
  funext y
  exact (eval_multilinearOfTable packed y).trans (MvPolynomial.MLE_eval_zeroOne y packed).symm

omit [Fintype K] [DecidableEq K] [Fact (Fintype.card K = 2)]
  [Fintype L] [DecidableEq L] [SampleableType L] [NeZero κ]
  [Fact (LinearIndependent K β)] [Fact (β 0 = 1)] in
private theorem profileBasis_eq (b : Basis (Fin (2 ^ κ)) K L) (hb : (⇑b) = β) :
    (β ∘ finFunctionFinEquiv) = (⇑(biniusProfile κ L K b).basis) := by
  rw [← hb]
  change _ = (⇑(booleanHypercubeBasis κ L K b))
  rw [booleanHypercubeBasis, Basis.coe_reindex]
  rfl

omit [Fintype K] [DecidableEq K] [Fact (Fintype.card K = 2)]
  [Fintype L] [DecidableEq L] [SampleableType L] [NeZero κ] in
private theorem profileCoordinates_eq (b : Basis (Fin (2 ^ κ)) K L)
    (hc : coordinates = fun x u => b.repr x (finFunctionFinEquiv u)) :
    coordinates = fun x u => (biniusProfile κ L K b).basis.repr x u := by
  rw [hc]
  funext x u
  change _ = (booleanHypercubeBasis κ L K b).repr x u
  rw [booleanHypercubeBasis, Basis.repr_reindex_apply]
  rfl

omit [Fintype K] [DecidableEq K] [Fact (Fintype.card K = 2)] [Fintype L] [NeZero κ] [NeZero ℓ'] in
private theorem multiplierPolynomial_eq (P : RingSwitchingProfile K L κ)
    (h : ℓ = ℓ' + κ) (ctx : Packing.Computable.Context L ℓ κ) :
    multilinearOfTable (Packing.Computable.prefixMultiplierTable
      (fun x u => P.basis.repr x u) h ctx) = (TensorPrefix.multiplier P h).polynomial ctx := by
  apply (MvPolynomial.MLEEquiv (R := L) (σ := Fin ℓ')).injective
  funext y
  change (multilinearOfTable (Packing.Computable.prefixMultiplierTable
    (fun x u => P.basis.repr x u) h ctx)).val.eval (y : Fin ℓ' → L) = _
  rw [eval_multilinearOfTable]
  exact Packing.Computable.prefixMultiplierTable_eq P h ctx y

/-- Build the sum-check multiplier table for the prover and its matrix evaluator for the
verifier. The coordinate-map agreement is used only in the evaluator law. -/
@[no_expose]
def multiplier (h : ℓ = ℓ' + κ) (hCoordinates : CoordinatesAgree β coordinates) :
    Multiplier (Packing.Computable.Context L ℓ κ) L ℓ' where
  polynomial ctx := multilinearOfTable (Packing.Computable.prefixMultiplierTable coordinates h ctx)
  evaluate ctx :=
    Packing.Computable.prefixEvaluateMultiplier (β ∘ finFunctionFinEquiv) coordinates h ctx
  evaluate_eq ctx z := by
    obtain ⟨b, hb, hc⟩ := hCoordinates
    let P := biniusProfile κ L K b
    rw [profileBasis_eq β b hb, profileCoordinates_eq coordinates b hc,
      Packing.Computable.prefixEvaluateMultiplier_eq P h, multiplierPolynomial_eq P h]
    exact (TensorPrefix.multiplier P h).evaluate_eq ctx z

omit [Fintype K] [DecidableEq K] [Fact (Fintype.card K = 2)] [Fintype L] [NeZero κ] [NeZero ℓ']
  [Fact (LinearIndependent K β)] [Fact (β 0 = 1)] in
/-- The executable multiplier has the same polynomial and point evaluator as the tensor
multiplier. This preserves both the honest sum-check messages and the final verifier check. -/
theorem multiplier_eq (h : ℓ = ℓ' + κ) (hCoordinates : CoordinatesAgree β coordinates)
    (b : Basis (Fin (2 ^ κ)) K L) (hb : (⇑b) = β)
    (hc : coordinates = fun x u => b.repr x (finFunctionFinEquiv u)) :
    multiplier β coordinates h hCoordinates =
      TensorPrefix.multiplier (biniusProfile κ L K b) h := by
  let P := biniusProfile κ L K b
  have hp : (multiplier β coordinates h hCoordinates).polynomial =
      (TensorPrefix.multiplier P h).polynomial := by
    funext ctx
    change multilinearOfTable (Packing.Computable.prefixMultiplierTable coordinates h ctx) = _
    rw [profileCoordinates_eq coordinates b hc]
    exact multiplierPolynomial_eq P h ctx
  have he : (multiplier β coordinates h hCoordinates).evaluate =
      (TensorPrefix.multiplier P h).evaluate := by
    funext ctx
    change Packing.Computable.prefixEvaluateMultiplier (β ∘ finFunctionFinEquiv)
      coordinates h ctx = _
    rw [profileBasis_eq β b hb, profileCoordinates_eq coordinates b hc]
    exact Packing.Computable.prefixEvaluateMultiplier_eq P h ctx
  generalize multiplier β coordinates h hCoordinates = A at hp he ⊢
  generalize TensorPrefix.multiplier P h = B at hp he ⊢
  rcases A with ⟨p, e, _⟩
  rcases B with ⟨p', e', _⟩
  cases hp
  cases he
  rfl

/-- Execute the coordinate batching head and the shared Binary Basefold product opening. -/
def unrolledReduction (h : ℓ = ℓ' + κ) (hRate : ℓ' + R < 2 ^ κ) (γ : ℕ)
    (hCoordinates : CoordinatesAgree β coordinates) :=
  OracleReduction.append (Oₛ₃ := fun i : Empty => nomatch i)
    (Packing.Computable.headReduction (inputOracleFamily (K := K) (ϑ := ϑ) β hRate)
      (β ∘ finFunctionFinEquiv) coordinates h)
    (ProductClaim.openingReduction K β (multiplier β coordinates h hCoordinates)
      (ProductSumcheck.Statement.claim (m := ℓ')) tableWitnessEquiv γ
      (ϑ := ϑ) (h_rate := hRate))

/-- Execute the coordinate ring-switching reduction and the separate Binary Basefold
evaluation opening. -/
def modularReduction (h : ℓ = ℓ' + κ) (hRate : ℓ' + R < 2 ^ κ) (γ : ℕ) :=
  OracleReduction.append (Oₛ₃ := fun i : Empty => nomatch i)
    (Packing.Computable.ringSwitchReduction (inputOracleFamily (K := K) (ϑ := ϑ) β hRate)
      (β ∘ finFunctionFinEquiv) coordinates h)
    (Opening.openingReduction K β
      (Opening.contextualQuery (L := L) (ℓ := ℓ') (Packing.Computable.Context L ℓ κ))
      tableWitnessEquiv γ (ϑ := ϑ) (h_rate := hRate))

end Binius.FRIBinius.Executable
