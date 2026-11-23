/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.ProofSystem.Binius.FRIBinius.Prelude
public import ArkLib.ProofSystem.Binius.FRIBinius.Protocol
public import ArkLib.ProofSystem.Binius.FRIBinius.Executable.Witness
public import ArkLib.ProofSystem.RingSwitching.Packing.TensorPrefix.Computable

/-!
# Executable small-field Binius openings

The batching message carries column coordinates in place of an abstract tensor. The modular
prefix also sends sum-check polynomials as coefficient arrays. Both honest prefixes use Boolean
evaluation tables for their witnesses; the opening interprets the packed table as its multilinear
extension. The Binary Basefold suffix keeps the abstract protocol's message and challenge types.
The verifier evaluates the ring-switching multiplier by a matrix formula, without constructing
its Boolean table.
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

/-- The vectors `β` form a basis over `K`, and `coordinates x u` gives the coefficient in that
basis at Boolean index `u` in low-bit-first order. -/
def CoordinatesAgree : Prop :=
  ∃ b : Basis (Fin (2 ^ κ)) K L, (⇑b) = β ∧
    coordinates = fun x u => b.repr x (finFunctionFinEquiv u)

local instance [Finite K] : Fact (Nat.Prime (ringChar K)) :=
  ⟨CharP.prime_ringChar K⟩

/-- The unchanged family of Binary BaseFold input codeword oracles. -/
abbrev inputOracleFamily (hRate : ℓ' + R < 2 ^ κ) :=
  openingOracles K β (ϑ := ϑ) hRate

/-- The Binary BaseFold opening suffix, including its zero-message input adapter. -/
abbrev openingPSpec (hRate : ℓ' + R < 2 ^ κ) (γ : ℕ) :=
  openingWire K β (ϑ := ϑ) hRate γ

/-- The column-coordinate batching message and challenge followed by the Binary Basefold product
opening. -/
abbrev unrolledPSpec (hRate : ℓ' + R < 2 ^ κ) (γ : ℕ) :=
  TensorPrefix.Computable.headPSpec L κ ++ₚ openingPSpec (K := K) (ϑ := ϑ) β hRate γ

/-- The full coordinate ring-switching prefix, including its separate sum-check, followed by the
original Binary Basefold opening. -/
abbrev modularPSpec (hRate : ℓ' + R < 2 ^ κ) (γ : ℕ) :=
  TensorPrefix.Computable.ringSwitchPSpec L κ ℓ' ++ₚ openingPSpec (K := K) (ϑ := ϑ) β hRate γ

instance (hRate : ℓ' + R < 2 ^ κ) (γ : ℕ) : ∀ i, OracleInterface
    ((unrolledPSpec (K := K) (ϑ := ϑ) β hRate γ).Message i) :=
  instOracleInterfaceMessageAppend (pSpec₁ := TensorPrefix.Computable.headPSpec L κ)

instance (hRate : ℓ' + R < 2 ^ κ) (γ : ℕ) : ∀ i, SampleableType
    ((unrolledPSpec (K := K) (ϑ := ϑ) β hRate γ).Challenge i) :=
  instSampleableTypeChallengeAppend (pSpec₁ := TensorPrefix.Computable.headPSpec L κ)

instance (hRate : ℓ' + R < 2 ^ κ) (γ : ℕ) : ∀ i, OracleInterface
    ((modularPSpec (K := K) (ϑ := ϑ) β hRate γ).Message i) :=
  instOracleInterfaceMessageAppend (pSpec₁ := TensorPrefix.Computable.ringSwitchPSpec L κ ℓ')

instance (hRate : ℓ' + R < 2 ^ κ) (γ : ℕ) : ∀ i, SampleableType
    ((modularPSpec (K := K) (ϑ := ϑ) β hRate γ).Challenge i) :=
  instSampleableTypeChallengeAppend (pSpec₁ := TensorPrefix.Computable.ringSwitchPSpec L κ ℓ')

omit [Fintype L] [SampleableType L] in
/-- The opening receives the same packed polynomial as the interpretation of the
ring-switching prover's output table. -/
theorem tableWitnessEquiv_apply_eq {n : ℕ} (packed : (Fin n → Fin 2) → L) :
    tableWitnessEquiv packed = TensorPrefix.Computable.toMultilinear packed := by
  rw [tableWitnessEquiv_apply]
  apply (MvPolynomial.MLEEquiv (R := L) (σ := Fin n)).injective
  funext y
  exact (eval_multilinearOfTable packed y).trans (MvPolynomial.MLE_eval_zeroOne y packed).symm

omit [Fintype K] [DecidableEq K] [Fact (Fintype.card K = 2)]
  [Fintype L] [DecidableEq L] [SampleableType L] [NeZero κ]
  [Fact (LinearIndependent K β)] [Fact (β 0 = 1)] in
private theorem profileBasis_eq (b : Basis (Fin (2 ^ κ)) K L) (hb : (⇑b) = β) :
    (β ∘ finFunctionFinEquiv) = (⇑(biniusProfile κ L K b).basis) := by
  rw [← hb, biniusProfile_basis_eq]

omit [Fintype K] [DecidableEq K] [Fact (Fintype.card K = 2)]
  [Fintype L] [DecidableEq L] [SampleableType L] [NeZero κ] in
private theorem profileCoordinates_eq (b : Basis (Fin (2 ^ κ)) K L)
    (hc : coordinates = fun x u => b.repr x (finFunctionFinEquiv u)) :
    coordinates = fun x u => (biniusProfile κ L K b).basis.repr x u := by
  simpa only [biniusProfile_basis_repr_eq] using hc

omit [Fintype K] [DecidableEq K] [Fact (Fintype.card K = 2)] [Fintype L] [NeZero κ] [NeZero ℓ'] in
private theorem multiplierPolynomial_eq (P : RingSwitchingProfile K L κ)
    (h : ℓ = ℓ' + κ) (ctx : TensorPrefix.Computable.Context L ℓ κ) :
    multilinearOfTable (TensorPrefix.Computable.prefixMultiplierTable
      (fun x u => P.basis.repr x u) h ctx) = (TensorPrefix.multiplier P h).polynomial ctx := by
  apply (MvPolynomial.MLEEquiv (R := L) (σ := Fin ℓ')).injective
  funext y
  change (multilinearOfTable (TensorPrefix.Computable.prefixMultiplierTable
    (fun x u => P.basis.repr x u) h ctx)).val.eval (y : Fin ℓ' → L) = _
  rw [eval_multilinearOfTable]
  exact TensorPrefix.Computable.prefixMultiplierTable_eq P h ctx y

/-- Build the sum-check multiplier table for the prover and its matrix evaluator for the
verifier. The coordinate-map agreement is used only in the evaluator law. -/
@[no_expose]
def multiplier (h : ℓ = ℓ' + κ) (hCoordinates : CoordinatesAgree β coordinates) :
    Multiplier (TensorPrefix.Computable.Context L ℓ κ) L ℓ' where
  polynomial ctx :=
    multilinearOfTable (TensorPrefix.Computable.prefixMultiplierTable coordinates h ctx)
  evaluate ctx :=
    TensorPrefix.Computable.prefixEvaluateMultiplier (β ∘ finFunctionFinEquiv) coordinates h ctx
  evaluate_eq ctx z := by
    obtain ⟨b, hb, hc⟩ := hCoordinates
    let P := biniusProfile κ L K b
    rw [profileBasis_eq β b hb, profileCoordinates_eq coordinates b hc,
      TensorPrefix.Computable.prefixEvaluateMultiplier_eq P h, multiplierPolynomial_eq P h]
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
    change multilinearOfTable (TensorPrefix.Computable.prefixMultiplierTable coordinates h ctx) = _
    rw [profileCoordinates_eq coordinates b hc]
    exact multiplierPolynomial_eq P h ctx
  have he : (multiplier β coordinates h hCoordinates).evaluate =
      (TensorPrefix.multiplier P h).evaluate := by
    funext ctx
    change TensorPrefix.Computable.prefixEvaluateMultiplier (β ∘ finFunctionFinEquiv)
      coordinates h ctx = _
    rw [profileBasis_eq β b hb, profileCoordinates_eq coordinates b hc]
    exact TensorPrefix.Computable.prefixEvaluateMultiplier_eq P h ctx
  generalize multiplier β coordinates h hCoordinates = A at hp he ⊢
  generalize TensorPrefix.multiplier P h = B at hp he ⊢
  rcases A with ⟨p, e, _⟩
  rcases B with ⟨p', e', _⟩
  cases hp
  cases he
  rfl

/-- The evaluation claim and proximity to the packed encoding, stated on Boolean tables. -/
noncomputable def inputRelation (b : Basis (Fin (2 ^ κ)) K L)
    (hRate : ℓ' + R < 2 ^ κ) (h : ℓ = ℓ' + κ) :
    Set ((((Fin ℓ → L) × L) × (∀ j, inputOracleFamily (K := K) (ϑ := ϑ) (⇑b) hRate j)) ×
      ((Fin ℓ → Fin 2) → K)) :=
  tableWitnessRelation
    (TensorPrefix.relIn (biniusProfile κ L K b) h (binaryBasefoldInput κ L K b ℓ' R ϑ hRate))

/-- The evaluation claim and exact packed encoding, stated on Boolean tables. -/
noncomputable def strictInputRelation (b : Basis (Fin (2 ^ κ)) K L)
    (hRate : ℓ' + R < 2 ^ κ) (h : ℓ = ℓ' + κ) :
    Set ((((Fin ℓ → L) × L) × (∀ j, inputOracleFamily (K := K) (ϑ := ϑ) (⇑b) hRate j)) ×
      ((Fin ℓ → Fin 2) → K)) :=
  tableWitnessRelation (TensorPrefix.relIn (biniusProfile κ L K b) h
    (binaryBasefoldInput κ L K b ℓ' R ϑ hRate).strictView)

/-- Run the tensor batching head, then open its product claim with Binary Basefold.
The coordinate map must agree with the basis used for packing and encoding. -/
def unrolledReduction (h : ℓ = ℓ' + κ) (hRate : ℓ' + R < 2 ^ κ) (γ : ℕ)
    (hCoordinates : CoordinatesAgree β coordinates) :
    OracleProof []ₒ ((Fin ℓ → L) × L) (inputOracleFamily (K := K) (ϑ := ϑ) β hRate)
      ((Fin ℓ → Fin 2) → K) (unrolledPSpec (K := K) (ϑ := ϑ) β hRate γ) :=
  appendOpeningReduction K β (ϑ := ϑ) hRate
    (prefixReduction := TensorPrefix.Computable.headReduction
      (OStmt := inputOracleFamily (K := K) (ϑ := ϑ) β hRate)
      (basis := β ∘ finFunctionFinEquiv) (coordinates := coordinates) h)
    (multiplier := multiplier β coordinates h hCoordinates)
    (toProductClaim := ProductSumcheck.Statement.claim (m := ℓ'))
    (witnessEquiv := tableWitnessEquiv) γ

/-- Run tensor ring switching, then open the packed evaluation with Binary Basefold.
The coordinate map must agree with the basis used for packing and encoding.
Lean erases this proof when compiling the reduction. -/
def modularReduction (h : ℓ = ℓ' + κ) (hRate : ℓ' + R < 2 ^ κ) (γ : ℕ)
    (_hCoordinates : CoordinatesAgree β coordinates) :
    OracleProof []ₒ ((Fin ℓ → L) × L) (inputOracleFamily (K := K) (ϑ := ϑ) β hRate)
      ((Fin ℓ → Fin 2) → K) (modularPSpec (K := K) (ϑ := ϑ) β hRate γ) :=
  appendOpeningReduction K β (ϑ := ϑ) hRate
    (prefixReduction := TensorPrefix.Computable.ringSwitchReduction
      (OStmt := inputOracleFamily (K := K) (ϑ := ϑ) β hRate)
      (basis := β ∘ finFunctionFinEquiv) (coordinates := coordinates) h)
    (multiplier := evalMultiplier)
    (toProductClaim := Opening.toProductClaim ∘
      Opening.contextualQuery (L := L) (ℓ := ℓ') (TensorPrefix.Computable.Context L ℓ κ))
    (witnessEquiv := tableWitnessEquiv) γ

end Binius.FRIBinius.Executable
