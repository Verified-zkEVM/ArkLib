import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.MathematicalUniform

open ReedSolomon.HiddenDerivative.RatePartition

example : 519 ≤ uniformDerivativeOrder (1 / 5 : ℝ) := by
  exact uniformDerivativeOrder_ge_519 (by norm_num) (by norm_num)
