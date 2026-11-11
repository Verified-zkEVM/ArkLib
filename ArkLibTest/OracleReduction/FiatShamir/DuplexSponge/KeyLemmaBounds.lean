import ArkLib.OracleReduction.FiatShamir.DuplexSponge.Security.KeyLemma

/-!
# Regression tests for the CO25 Claim 5.24 and Eq. (5) bounds

The Claim 5.24 bound must be the closed form of the Eq. (56) sum
`∑_{j=t+1}^{t+1+L} (7j − 5) / |Σ|^c`, and `η★` must be the sum of the per-claim bounds.
At `t = L = 0` the sum has the single term `j = 1`, whose value is `2 / |Σ|^c`.
-/

open DuplexSpongeFS DuplexSpongeFS.KeyLemma

variable (U : Type) [SpongeUnit U] [Fintype U] [SpongeSize]

/-- At `t = L = 0`, the bound is the single Eq. (56) summand `2 / |Σ|^c`. -/
example : claim5_24Bound U 0 0 0 0 = 2 / ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C := by
  simp [claim5_24Bound]
  ring

/-- The `L = 1`, `t = 2` instance: the summands `j = 3, 4` give `16 + 23 = 39`. -/
example : claim5_24Bound U 1 1 0 1 = 39 / ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C := by
  rw [claim5_24Bound_eq_sum, ← Finset.sum_div]
  congr 1
  rw [show Finset.Icc (1 + 1 + 0 + 1) (1 + 1 + 0 + 1 + 1) = {3, 4} by decide]
  norm_num

/-- The bound is never negative. -/
example (tₕ tₚ tₚᵢ L : ℕ) : 0 ≤ claim5_24Bound U tₕ tₚ tₚᵢ L :=
  claim5_24Bound_nonneg U tₕ tₚ tₚᵢ L

/-- Eq. (5): the `η★` numerator ends in `− 6(L+1)`, so at `t = L = 0` its first term is
`(14 − 6) / (2|Σ|^c) = 4 / |Σ|^c` (Claim 5.21 contributes `2`, Claim 5.24 contributes `2`). -/
example {n : ℕ} {pSpec : ProtocolSpec n} (ε : CodecBias (pSpec := pSpec)) :
    ηStar (pSpec := pSpec) U 0 0 0 0 ε =
      4 / ((Fintype.card U : ℕ) : ℝ) ^ SpongeSize.C +
        (θStar 0 0 0 : ℝ) * iSup (fun i => (ε i : ℝ)) + ∑ i, (ε i : ℝ) := by
  simp [ηStar]
  ring
