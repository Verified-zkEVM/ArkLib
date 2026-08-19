/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.RingSwitch.Reduction
import ArkLib.ToMathlib.Polynomial.DivByXPowAddOne

/-!
# Centered coefficient bounds for the honest lift quotient

The honest prover of the HMZ25 lift (Hachi Figure 4) commits to the lifted witness `(z, ρ)`, where
`ρᵢ = (rowSumᵢ − rep yᵢ) /ₘ φ` (`Presentation.quotient`). The commitment's shortness regime
`liftShort` asks for `RhoShort ρBound ρ`, i.e. a centered coefficient bound on those quotients. This
file proves it, without developing any general theory of coefficient growth under polynomial
division.

**The mechanism.** For the power-of-two cyclotomic modulus `φ = X ^ d + 1`, dividing a polynomial of
degree `< 2d` by `φ` *selects* coefficients rather than combining them:
`(p /ₘ φ).coeff k = p.coeff (d + k)` (`Polynomial.coeff_divByMonic_X_pow_add_one`). The dividend
`rowSumᵢ − rep yᵢ` has degree `≤ 2d − 2`, so the quotient's coefficients are literally coefficients
of the row sum, and the bound reduces to a coefficient bound on `∑ⱼ rep(Mᵢⱼ)·rep(zⱼ)`.

**No wraparound condition is needed anywhere.** All bounds go through `valMinAbs_natAbs_le`: the
centered representative is minimal among integer representatives, so exhibiting *any* integer
representative bounds it. `valMinAbs_natAbs_mul_le` and `valMinAbs_natAbs_sum_le_card_mul`
(`NormBounds/Basic`) package that. Consequently no hypothesis of the form `… ≤ q/2` appears below.

## Main results

* `valMinAbs_natAbs_coeff_rep_le`: an `ℓ∞` bound on a ring element bounds every coefficient of its
  presentation representative (including the ones past `deg φ`, which vanish).
* `valMinAbs_natAbs_coeff_rowSum_le`: coefficient bound for the structured row sum,
  `μ · (m+1) · βM · βz` at index `m`.
* `valMinAbs_natAbs_coeff_quotient_le`: the quotient bound `μ · 2d · βM · βz` (assembled into
  `RhoShort` for the honest lifted witness by `rhoShort_honestLiftWitness` in
  `RingSwitch/Completeness`, where the honest witness is named).
* `Rq.lInftyNorm_le_half`, `rlinMatrixShort_half`, `rhoShort_half`: the *unconditional* fallback.
  Every element of `Rq Φ` has centered `ℓ∞` norm `≤ q/2`, so `RhoShort (q/2)` holds for **any**
  quotient family with no hypotheses at all. This is what makes the honest lift's `liftShort`
  obligation dischargeable for the Hachi chain, where the `R^lin` matrix contains the Ajtai key
  blocks `D`, `B`, `A` and the gadget powers `bᵉ` — none of them short, so `q/2` is the only honest
  `βM`. See `rhoShort_half`'s docstring for what that costs downstream.

## References

* [Huang, M.-Y. M., Mao, X., and Zhang, J., *Sublinear Proofs over Polynomial Rings*][HMZ25]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus
open RingSwitching RingSwitching.Lift

namespace ArkLib.Lattices.Ajtai.InnerOuter

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]

/-! ## The universal bound: every ring element is `q/2`-short -/

omit [IsCyclotomic Φ] in
/-- Every element of `Rq Φ` has centered `ℓ∞` norm at most `q/2`: each coefficient's centered
representative lies in `(−q/2, q/2]` (`ZMod.natAbs_valMinAbs_le`). Trivial, but it is the honest
`βM` for a matrix built from a uniformly random Ajtai key. -/
theorem Rq.lInftyNorm_le_half (a : Rq Φ) : Rq.lInftyNorm Φ a ≤ q / 2 :=
  Finset.sup_le fun _ _ => ZMod.natAbs_valMinAbs_le _

omit [IsCyclotomic Φ] in
/-- Vector form of `Rq.lInftyNorm_le_half`. -/
theorem vecLInftyNorm_le_half {cols : ℕ} (v : PolyVec (Rq Φ) cols) :
    vecLInftyNorm Φ v ≤ q / 2 :=
  Finset.sup_le fun i _ => Rq.lInftyNorm_le_half Φ (v i)

/-! ## Coefficient bounds for the structured row sum -/

set_option linter.unusedSectionVars false in
/-- An `ℓ∞` bound on a ring element bounds **every** coefficient of its presentation representative:
below `deg φ` by the definition of `Rq.lInftyNorm`, at or above it because representatives are
degree-reduced (`Rq.natDegree_val_toPoly_lt'`). -/
theorem valMinAbs_natAbs_coeff_rep_le (hd : 0 < Φ.φ.natDegree) {β : ℕ} {a : Rq Φ}
    (h : Rq.lInftyNorm Φ a ≤ β) (k : ℕ) :
    (((cyclotomicPresentation Φ).rep a).coeff k).valMinAbs.natAbs ≤ β := by
  by_cases hk : k < Φ.φ.natDegree
  · have hcoeff : ((cyclotomicPresentation Φ).rep a).coeff k = a.1.coeff k :=
      (CPolynomial.coeff_toPoly a.1 k).symm
    rw [hcoeff]
    exact Rq.valMinAbs_natAbs_coeff_le_of_lInftyNorm_le Φ h hk
  · have hzero : ((cyclotomicPresentation Φ).rep a).coeff k = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt
        (lt_of_lt_of_le (Rq.natDegree_val_toPoly_lt' Φ hd a) (by omega))
    rw [hzero, ZMod.valMinAbs_zero, Int.natAbs_zero]
    exact Nat.zero_le _

set_option linter.unusedSectionVars false in
/-- **Coefficient bound for the lifted row sum.** At index `m`, the centered representative of
`(∑ⱼ rep(Mᵢⱼ)·rep(zⱼ)).coeff m` is bounded by `μ · (m+1) · (βM · βz)`: the sum over `μ` columns of a
convolution of `m+1` products, each product bounded by `βM · βz`
(`valMinAbs_natAbs_mul_le`), each sum bounded by its cardinality times the term bound
(`valMinAbs_natAbs_sum_le_card_mul`). No wraparound hypothesis. -/
theorem valMinAbs_natAbs_coeff_rowSum_le (hd : 0 < Φ.φ.natDegree) {n μ βM βz : ℕ}
    (M : PolyMatrix (Rq Φ) n μ) (z : PolyVec (Rq Φ) μ)
    (hM : ∀ i j, Rq.lInftyNorm Φ (M i j) ≤ βM) (hz : ∀ j, Rq.lInftyNorm Φ (z j) ≤ βz)
    (i : Fin n) (m : ℕ) :
    (((cyclotomicPresentation Φ).rowSum M z i).coeff m).valMinAbs.natAbs
      ≤ μ * ((m + 1) * (βM * βz)) := by
  have hterm : ∀ j : Fin μ,
      ((((cyclotomicPresentation Φ).rep (M i j) *
          (cyclotomicPresentation Φ).rep (z j)).coeff m)).valMinAbs.natAbs
        ≤ (m + 1) * (βM * βz) := by
    intro j
    rw [Polynomial.coeff_mul]
    refine le_trans (valMinAbs_natAbs_sum_le_card_mul _ _ (β := βM * βz) (fun x _ => ?_)) ?_
    · exact le_trans (valMinAbs_natAbs_mul_le _ _)
        (Nat.mul_le_mul (valMinAbs_natAbs_coeff_rep_le Φ hd (hM i j) x.1)
          (valMinAbs_natAbs_coeff_rep_le Φ hd (hz j) x.2))
    · rw [Finset.Nat.card_antidiagonal]
  calc (((cyclotomicPresentation Φ).rowSum M z i).coeff m).valMinAbs.natAbs
      = ((∑ j : Fin μ, ((cyclotomicPresentation Φ).rep (M i j) *
            (cyclotomicPresentation Φ).rep (z j)).coeff m)).valMinAbs.natAbs := by
        rw [Presentation.rowSum, Polynomial.finsetSum_coeff]
    _ ≤ (Finset.univ : Finset (Fin μ)).card * ((m + 1) * (βM * βz)) :=
        valMinAbs_natAbs_sum_le_card_mul _ _ (fun j _ => hterm j)
    _ = μ * ((m + 1) * (βM * βz)) := by rw [Finset.card_univ, Fintype.card_fin]

/-! ## The quotient bound -/

set_option linter.unusedSectionVars false in
/-- **Centered coefficient bound for the honest lift quotient**, at the concrete power-of-two
modulus `φ = X ^ d + 1`.

Every quotient coefficient *is* a row-sum coefficient of index `≥ d`
(`Polynomial.coeff_divByMonic_X_pow_add_one`, valid because the dividend has degree `≤ 2d − 2`), and
`rep yᵢ` does not reach those indices. So the bound is the row-sum bound at index `< 2d`, i.e.
`μ · 2d · βM · βz` — division contributes **no growth at all**.

Hypotheses: the modulus shape `hφ`, positivity `hd`, and the two explicit coefficient bounds `hM`
(the `R^lin` matrix) and `hz` (the witness). No anti-wraparound condition. -/
theorem valMinAbs_natAbs_coeff_quotient_le {d : ℕ} (hφ : Φ.φ.toPoly = Polynomial.X ^ d + 1)
    (hd : 0 < d) {n μ βM βz : ℕ}
    (M : PolyMatrix (Rq Φ) n μ) (z : PolyVec (Rq Φ) μ) (y : PolyVec (Rq Φ) n)
    (hM : ∀ i j, Rq.lInftyNorm Φ (M i j) ≤ βM) (hz : ∀ j, Rq.lInftyNorm Φ (z j) ≤ βz)
    (i : Fin n) (k : ℕ) :
    (((cyclotomicPresentation Φ).quotient M z y i).coeff k).valMinAbs.natAbs
      ≤ μ * (2 * d * (βM * βz)) := by
  have hdegΦ : Φ.φ.natDegree = d := by
    rw [CPolynomial.natDegree_toPoly, hφ, ← Polynomial.C_1, Polynomial.natDegree_X_pow_add_C]
  haveI : Lift.IsPresentation (cyclotomicPresentation Φ) :=
    isPresentation_cyclotomic Φ (by omega)
  have hmod : (cyclotomicPresentation Φ).modulus = Polynomial.X ^ d + 1 := hφ
  -- The dividend and its degree.
  set p : Polynomial (ZMod q) :=
    (cyclotomicPresentation Φ).rowSum M z i - (cyclotomicPresentation Φ).rep (y i) with hp
  have hmd : (cyclotomicPresentation Φ).modulus.natDegree = d := by
    rw [hmod, ← Polynomial.C_1, Polynomial.natDegree_X_pow_add_C]
  have hrepdeg : ((cyclotomicPresentation Φ).rep (y i)).natDegree < d := by
    have h2 := Lift.IsPresentation.natDegree_rep_lt (P := cyclotomicPresentation Φ) (y i)
    rw [hmd] at h2
    exact h2
  have hpdeg : p.natDegree < 2 * d := by
    have h1 := (cyclotomicPresentation Φ).natDegree_rowSum_le M z i
    rw [hmd] at h1
    refine lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt (by omega) (by omega))
  -- Division selects the coefficient at `d + k`.
  have hquot : ((cyclotomicPresentation Φ).quotient M z y i).coeff k = p.coeff (d + k) := by
    rw [Presentation.quotient, ← hp, hmod]
    exact Polynomial.coeff_divByMonic_X_pow_add_one hd hpdeg k
  rw [hquot]
  by_cases hk : k < d
  · -- Inside the quotient's degree range: the row-sum bound, since `rep yᵢ` vanishes there.
    have hy : ((cyclotomicPresentation Φ).rep (y i)).coeff (d + k) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    have hpk : p.coeff (d + k) = ((cyclotomicPresentation Φ).rowSum M z i).coeff (d + k) := by
      rw [hp, Polynomial.coeff_sub, hy, sub_zero]
    rw [hpk]
    refine le_trans (valMinAbs_natAbs_coeff_rowSum_le Φ (by omega) M z hM hz i (d + k)) ?_
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
  · -- Past it: the coefficient vanishes.
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega), ZMod.valMinAbs_zero, Int.natAbs_zero]
    exact Nat.zero_le _

set_option linter.unusedSectionVars false in
/-- **The unconditional fallback: `RhoShort (q/2)` holds for every quotient family.** Centered
representatives live in `(−q/2, q/2]`, so this needs no hypotheses whatsoever.

It is the bound the Hachi chain actually uses, and that is a substantive statement about the
construction rather than laziness: `rlinStmt` assembles its matrix from the Ajtai key blocks `D`,
`B`, `A` and the gadget powers `bᵉ`, all of which are (or may be) uniform mod `q`, so the honest
`βM` of `rhoShort_honestQuotient` is `q/2` and the growth bound `μ · 2d · (q/2) · βz` exceeds `q/2`
— i.e. the honest quotient of a Hachi `R^lin` instance is *not* short, and no sharper claim is
available without assuming a short commitment key. Downstream consequence, documented at the
batching bridge: a zero-check range base `b` with `ρBound ≤ b − 1` must then satisfy `b − 1 ≥ q/2`,
so the single-`b` range table of `ZeroCheck/Constraints` cannot check the quotient half tightly. -/
theorem rhoShort_half {n : ℕ} (ρ : Fin n → Polynomial (ZMod q)) : RhoShort (q / 2) ρ :=
  fun _ _ => ZMod.natAbs_valMinAbs_le _

end ArkLib.Lattices.Ajtai.InnerOuter
