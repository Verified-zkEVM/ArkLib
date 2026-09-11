/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import
  ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.Squarefree.Sharp
import ArkLibExamples.ReedSolomon.LambdaVM.Parameters
import ArkLibExamples.ReedSolomon.ProveKit.Certificates
import ArkLibExamples.ReedSolomon.ZisK.Parameters
/-!
# Sharp squarefree curve certificate checks

Exact arithmetic checks for the retained application profiles.
-/

open ReedSolomon.CurveCertificate

namespace ArkLibTest.ReedSolomon.SharpCurveCertificate

/-- The refreshed ZisK integers are the exact ceilings of the sharp one-chart expression. -/
theorem zisk_sharp_envelopes_exact_ceil (i : Fin 8) :
    ArkLibExamples.ReedSolomon.ZisK.exceptionalCounts i - 1 <
        squarefreeSharpCurveEnvelope
          (ArkLibExamples.ReedSolomon.ZisK.profiles i)
          (ArkLibExamples.ReedSolomon.ZisK.splits i) ∧
      squarefreeSharpCurveEnvelope
          (ArkLibExamples.ReedSolomon.ZisK.profiles i)
          (ArkLibExamples.ReedSolomon.ZisK.splits i) ≤
        ArkLibExamples.ReedSolomon.ZisK.exceptionalCounts i := by
  fin_cases i <;> decide +kernel

/-- The refreshed LambdaVM integers are the exact ceilings of the sharp expression. -/
theorem lambdaVm_sharp_envelopes_exact_ceil (i : Fin 9) :
    ArkLibExamples.ReedSolomon.LambdaVM.CPU.exceptionalCounts i - 1 <
        squarefreeSharpCurveEnvelope
          (ArkLibExamples.ReedSolomon.LambdaVM.CPU.profiles i)
          (ArkLibExamples.ReedSolomon.LambdaVM.CPU.splits i) ∧
      squarefreeSharpCurveEnvelope
          (ArkLibExamples.ReedSolomon.LambdaVM.CPU.profiles i)
          (ArkLibExamples.ReedSolomon.LambdaVM.CPU.splits i) ≤
        ArkLibExamples.ReedSolomon.LambdaVM.CPU.exceptionalCounts i := by
  fin_cases i <;> decide +kernel

/-- Every retained ProveKit ceiling also dominates the sharper squarefree expression. -/
theorem proveKit_passportOuter_sharp_envelopes_le (i : Fin 6) :
    squarefreeSharpCurveEnvelope
        (ArkLibExamples.ReedSolomon.ProveKit.passportOuterProfiles i)
        (ArkLibExamples.ReedSolomon.ProveKit.passportOuterSplits i) ≤
      (ArkLibExamples.ReedSolomon.ProveKit.passportOuterWitness.row i).exceptionalCount := by
  fin_cases i <;> decide +kernel

theorem proveKit_passportInternal_sharp_envelopes_le (i : Fin 4) :
    squarefreeSharpCurveEnvelope
        (ArkLibExamples.ReedSolomon.ProveKit.passportInternalProfiles i)
        (ArkLibExamples.ReedSolomon.ProveKit.passportInternalSplits i) ≤
      (ArkLibExamples.ReedSolomon.ProveKit.passportInternalZk.row i).exceptionalCount := by
  fin_cases i <;> decide +kernel

theorem proveKit_goldilocksWitness_sharp_envelopes_le (i : Fin 4) :
    squarefreeSharpCurveEnvelope
        (ArkLibExamples.ReedSolomon.ProveKit.goldilocksWitnessProfiles i)
        (ArkLibExamples.ReedSolomon.ProveKit.goldilocksWitnessSplits i) ≤
      (ArkLibExamples.ReedSolomon.ProveKit.goldilocksLookupWitness.row i).exceptionalCount := by
  fin_cases i <;> decide +kernel

theorem proveKit_goldilocksBlind_sharp_envelope_le :
    squarefreeSharpCurveEnvelope
        ArkLibExamples.ReedSolomon.ProveKit.goldilocksBlindProfile
        ArkLibExamples.ReedSolomon.ProveKit.goldilocksBlindSplit ≤
      (ArkLibExamples.ReedSolomon.ProveKit.goldilocksLookupBlind.row 0).exceptionalCount := by
  decide +kernel

end ArkLibTest.ReedSolomon.SharpCurveCertificate
