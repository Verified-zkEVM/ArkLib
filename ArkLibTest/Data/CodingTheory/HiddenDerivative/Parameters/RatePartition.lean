import ArkLib.Data.CodingTheory.HiddenDerivative.Parameters.RatePartition.UniformEnvelope

open ReedSolomon.HiddenDerivative.RatePartition

example : Nonempty (UniformRatePartitionEnvelope (1 / 5 : ℝ)
    (50 * uniformMultiplicity (1 / 5)) (2 * uniformMultiplicity (1 / 5))
    (12 * uniformMultiplicity (1 / 5))) := by
  have hm : 0 < uniformMultiplicity (1 / 5 : ℝ) := by
    have h := add_two_le_uniformMultiplicity (1 / 5 : ℝ)
    omega
  apply exists_uniformRatePartitionEnvelope (δ := (1 / 5 : ℝ))
  · norm_num
  · norm_num
  · apply Nat.ceil_le.mpr
    rw [show (1 / 5 : ℝ) ^ 2 = 1 / 25 by norm_num]
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 1 / 25)]
    norm_num
    nlinarith
  · positivity
  · norm_num
    nlinarith
  · omega
