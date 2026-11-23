/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ArkLib Contributors
-/
module

public import ArkLib.ProofSystem.Binius.FRIBinius.Executable
public import ArkLib.ProofSystem.Binius.FRIBinius.RingSwitch

/-!
# Agreement of the executable modular FRI-Binius verifier

The original verifier reads a decoded ring-switching prefix. The Binary Basefold opening
verifies the same remaining transcript without conversion.
-/

@[expose] public section

namespace Binius.FRIBinius.Executable

open Module ProtocolSpec RingSwitching RingSwitching.Packing

variable {κ ℓ ℓ' R ϑ : ℕ}
variable {K L : Type} [Field K] [Fintype K] [DecidableEq K] [Fact (Fintype.card K = 2)]
  [Field L] [Fintype L] [DecidableEq L] [SampleableType L] [Algebra K L]
variable [NeZero ℓ'] [NeZero R] [NeZero ϑ] [Fact (ϑ ∣ ℓ')]
variable (b : Basis (Fin (2 ^ κ)) K L) [Fact (b 0 = 1)]

/-- The executable verifier has the same result as the modular specification on every
transcript, after decoding the ring-switching prefix and retaining the opening suffix. -/
theorem modularReduction_verify_eq (coordinates : L → (Fin κ → Fin 2) → K)
    (hc : coordinates = fun x u => b.repr x (finFunctionFinEquiv u))
    (h : ℓ = ℓ' + κ) (hRate : ℓ' + R < 2 ^ κ) (γ : ℕ)
    (stmt : (Fin ℓ → L) × L)
    (ost : ∀ j, inputOracleFamily (K := K) (ϑ := ϑ) (⇑b) hRate j)
    (tr : (modularPSpec (K := K) (ϑ := ϑ) (⇑b) hRate γ).FullTranscript) :
    (((modularReduction (ϑ := ϑ) (⇑b) coordinates h hRate γ).verifier
        (Oₛₒ := fun i : Empty => nomatch i)).toVerifier
        (Oₛₒ := fun i : Empty => nomatch i)).verify (stmt, ost) tr =
      ((Binius.FRIBinius.RingSwitch.fullVerifier κ K b hRate h γ (ϑ := ϑ)).toVerifier
        (Oₛₒ := fun i : Empty => nomatch i)).verify (stmt, ost)
          (Packing.Computable.decodeRingSwitchTranscript (biniusProfile κ L K b) tr.fst ++ₜ
            tr.snd) := by
  let P := biniusProfile κ L K b
  let a := Binius.FRIBinius.RingSwitch.inputInterface κ K b (ϑ := ϑ) hRate
  have hb : (⇑b ∘ finFunctionFinEquiv) = ⇑P.basis := by
    change _ = ⇑(booleanHypercubeBasis κ L K b)
    rw [booleanHypercubeBasis, Basis.coe_reindex]
    rfl
  have hCoordinates : coordinates = fun x u => P.basis.repr x u := by
    rw [hc]
    funext x u
    change _ = (booleanHypercubeBasis κ L K b).repr x u
    rw [booleanHypercubeBasis, Basis.repr_reindex_apply]
    rfl
  have hPrefix := Packing.Computable.ringSwitchReduction_verify_eq P h a
    (⇑b ∘ finFunctionFinEquiv) coordinates hb hCoordinates stmt ost tr.fst
  unfold modularReduction Binius.FRIBinius.RingSwitch.fullVerifier
  simp only [OracleReduction.append]
  conv_lhs => erw [OracleVerifier.append_toVerifier (Oₛ₃ := fun i : Empty => nomatch i)]
  conv_rhs => erw [OracleVerifier.append_toVerifier (Oₛ₃ := fun i : Empty => nomatch i)]
  simp only [Verifier.append, FullTranscript.append_fst, FullTranscript.append_snd]
  erw [hPrefix]
  rfl

end Binius.FRIBinius.Executable
