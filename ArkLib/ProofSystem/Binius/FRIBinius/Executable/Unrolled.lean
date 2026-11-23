/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen
-/
module

public import ArkLib.ProofSystem.Binius.FRIBinius.Executable
public import ArkLib.ProofSystem.Binius.FRIBinius.Unrolled.General

/-!
# Verifier agreement for executable unrolled FRI-Binius

The batching prefix carries the tensor in basis coordinates. The Binary BaseFold suffix uses
the original message and challenge types. Decoding the prefix preserves the full verification
computation, including rejection.
-/

@[expose] public section

namespace Binius.FRIBinius.Executable

open AdditiveNTT Module OracleSpec ProtocolSpec RingSwitching RingSwitching.Packing
open BinaryBasefold

variable {κ ℓ ℓ' R ϑ : ℕ}
variable {K L : Type} [Field K] [Fintype K] [DecidableEq K] [Fact (Fintype.card K = 2)]
  [Field L] [Fintype L] [DecidableEq L] [SampleableType L] [Algebra K L]
variable [NeZero ℓ'] [NeZero R] [NeZero ϑ] [Fact (ϑ ∣ ℓ')]
variable (b : Basis (Fin (2 ^ κ)) K L) [Fact (b 0 = 1)]
variable (hRate : ℓ' + R < 2 ^ κ) (γ : ℕ)

local instance [Finite K] : Fact (Nat.Prime (ringChar K)) := ⟨CharP.prime_ringChar K⟩

omit [Fact (b 0 = 1)] in
/-- Decode the batching prefix and retain the original opening messages and challenges. -/
noncomputable def unrolledTranscriptMap :
    TranscriptMap (unrolledPSpec (K := K) (ϑ := ϑ) (⇑b) hRate γ)
      (Unrolled.pSpec κ K b (ϑ := ϑ) hRate γ) :=
  (TensorPrefix.Computable.headTranscriptMap (biniusProfile κ L K b)).append
    (TranscriptMap.refl (openingPSpec (K := K) (ϑ := ϑ) (⇑b) hRate γ))

omit [Fact (b 0 = 1)] in
/-- Decode the batching carrier and leave the Binary BaseFold suffix unchanged. -/
noncomputable def decodeUnrolledTranscript
    (tr : (unrolledPSpec (K := K) (ϑ := ϑ) (⇑b) hRate γ).FullTranscript) :
    (Unrolled.pSpec κ K b (ϑ := ϑ) hRate γ).FullTranscript :=
  (unrolledTranscriptMap (ϑ := ϑ) b hRate γ).decodeFull tr

omit [DecidableEq K] [Fact (Fintype.card K = 2)] [NeZero R] [Fact (b 0 = 1)] in
private theorem decodeUnrolledTranscript_eq
    (tr : (unrolledPSpec (K := K) (ϑ := ϑ) (⇑b) hRate γ).FullTranscript) :
    decodeUnrolledTranscript b hRate γ tr =
      TensorPrefix.Computable.decodeHeadTranscript (biniusProfile κ L K b) tr.fst ++ₜ tr.snd :=
  TranscriptMap.decodeFull_append
    (TensorPrefix.Computable.headTranscriptMap (biniusProfile κ L K b))
    (TranscriptMap.refl (openingPSpec (K := K) (ϑ := ϑ) (⇑b) hRate γ)) tr

/-- Unrolled FRI-Binius returns the same verifier result on every executable transcript
as the specification on the decoded transcript. The coordinates must agree with the
specified basis; no honest-prover or input-relation hypothesis is needed. -/
theorem unrolledReduction_verify_eq
    (coordinates : L → (Fin κ → Fin 2) → K)
    (hc : coordinates = fun x u => b.repr x (finFunctionFinEquiv u))
    (h : ℓ = ℓ' + κ) (stmt : (Fin ℓ → L) × L)
    (ost : ∀ j, inputOracleFamily (K := K) (ϑ := ϑ) (⇑b) hRate j)
    (tr : (unrolledPSpec (K := K) (ϑ := ϑ) (⇑b) hRate γ).FullTranscript) :
    (((unrolledReduction (ϑ := ϑ) (⇑b) coordinates h hRate γ ⟨b, rfl, hc⟩).verifier
      (Oₛₒ := fun i : Empty => nomatch i)).toVerifier
      (Oₛₒ := fun i : Empty => nomatch i)).verify
        (stmt, ost) tr =
      ((Unrolled.fullVerifier κ K b (ϑ := ϑ) hRate h γ).toVerifier
        (Oₛₒ := fun i : Empty => nomatch i)).verify
          (stmt, ost) (decodeUnrolledTranscript b hRate γ tr) := by
  let P := biniusProfile κ L K b
  let a := binaryBasefoldInput κ L K b ℓ' R ϑ hRate
  have hb : (⇑b ∘ finFunctionFinEquiv) = ⇑P.basis :=
    (biniusProfile_basis_eq κ L K b).symm
  have hcoords : coordinates = fun x u => P.basis.repr x u := by
    simpa only [P, biniusProfile_basis_repr_eq] using hc
  have hHead : (TensorPrefix.Computable.headVerifier (TensorPrefix.commitment a).OStmt
      (⇑b ∘ finFunctionFinEquiv) coordinates h).toVerifier.verify (stmt, ost) tr.fst =
      (TensorPrefix.headVerifier P h a).toVerifier.verify (stmt, ost)
        (TensorPrefix.Computable.decodeHeadTranscript P tr.fst) := by
    rw [hb, hcoords]
    exact TensorPrefix.Computable.headVerifier_verify_decodeHeadTranscript P h a stmt ost tr.fst
  rw [decodeUnrolledTranscript_eq]
  unfold unrolledReduction appendOpeningReduction OracleReduction.append
    Unrolled.fullVerifier appendOpeningVerifier
  conv_lhs => erw [OracleVerifier.append_toVerifier (Oₛ₃ := fun i : Empty => nomatch i)]
  conv_rhs => erw [OracleVerifier.append_toVerifier (Oₛ₃ := fun i : Empty => nomatch i)]
  simp only [Verifier.append, FullTranscript.append_fst, FullTranscript.append_snd]
  change (do
      let s ← (TensorPrefix.Computable.headVerifier (TensorPrefix.commitment a).OStmt
        (⇑b ∘ finFunctionFinEquiv) coordinates h).toVerifier.verify (stmt, ost) tr.fst
      ((ProductClaim.openingVerifier K b (multiplier (⇑b) coordinates h ⟨b, rfl, hc⟩)
        (ProductSumcheck.Statement.claim (m := ℓ')) γ (ϑ := ϑ) (h_rate := hRate)).toVerifier
        (Oₛₒ := fun i : Empty => nomatch i)).verify s tr.snd) = _
  rw [hHead, multiplier_eq (⇑b) coordinates h ⟨b, rfl, hc⟩ b rfl hc]
  rfl

end Binius.FRIBinius.Executable
