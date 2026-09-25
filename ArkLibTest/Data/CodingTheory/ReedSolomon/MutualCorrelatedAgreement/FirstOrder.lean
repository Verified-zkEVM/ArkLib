import ArkLib.Data.CodingTheory.ReedSolomon.MutualCorrelatedAgreement.FirstOrder.HybridCurveTransfer

open ReedSolomon

example :
    hybridCurveAtDegree 4 1 1 3 2 2 1 ≤
      hybridCurveTail 4 1 1 1 2 3 2 + hybridCurveRegular 4 1 1 3 2 2 1 2 := by
  exact hybridCurveAtDegree_le_pair (by omega) (by omega) (by omega) (by omega)
