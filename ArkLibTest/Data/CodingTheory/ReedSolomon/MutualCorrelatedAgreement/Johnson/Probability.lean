/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.Johnson.Probability
import Mathlib.FieldTheory.Finite.GaloisField
/-!
# Johnson transfer in small positive characteristic

This acceptance client checks the all-characteristic ordinary transfer over a field of
characteristic two with eight evaluation points.
-/

open ReedSolomon ReedSolomon.HiddenDerivative Polynomial
namespace ArkLibTest.ReedSolomon

private instance : Fact (Nat.Prime 2) := ⟨by decide⟩

open Classical in
/-- Characteristic two is below both the block length and Johnson root-degree cap.
The full finite transfer still applies to the eight-element field. -/
example (domain : Fin 8 ↪ GaloisField 2 3) (f g : Fin 8 → GaloisField 2 3) :
    ∃ exceptional : Finset (GaloisField 2 3),
      (exceptional.card : ℝ) ≤ johnsonE0 8 1 4 (1 / 8) ∧
      ∀ z ∉ exceptional, ∀ P : (GaloisField 2 3)[X], P.degree < 2 →
        4 ≤ (polynomialAgreementSet domain (fun i ↦ f i + z * g i) P).card →
        HasExactCorrelatedPair domain f g (RingHom.id _) 2 z P := by
  have hs : √((1 : ℝ) / 8) ≤ 3 / 8 := by
    apply (Real.sqrt_le_iff).mpr
    norm_num
  apply exists_exceptional_johnsonMCA domain f g (by decide) (by decide)
    (by norm_num : (0 : ℝ) < 1 / 8) _ _ (by decide)
  · norm_num [johnsonAgreement, johnsonRhoMinus] at hs ⊢
    linarith
  · norm_num [johnsonAgreement, johnsonRhoMinus] at hs ⊢
    linarith

end ArkLibTest.ReedSolomon
