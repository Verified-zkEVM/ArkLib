/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/

import ArkLib.Data.CodingTheory.HiddenDerivative.Interpolation.WeightedSupport.Margin

/-!
# Acceptance cases for the strict surplus of the weighted support

The source's `finrank_weightedSupportLocalConstraint_lt_prescribed`, with its hypothesis
`H ≤ log d + 3 / 5`, and the source's `weightedSupport_margin_of_normalized_rank`, with
`48000 ≤ d`, derived from the general statements; and `prescribed_weightedSupport_margin` over
`ZMod 2` at `δ = 1 / 4`, `n = 4`, `D = 2`, where only the rate interval
`1 / 12 ≤ 1 / 2 ≤ 3 / 4` has to be checked.
-/

open ReedSolomon.HiddenDerivative
open ReedSolomon.HiddenDerivative.WeightedSupportParameters

/-- The source's `finrank_weightedSupportLocalConstraint_lt_prescribed`, whose hypothesis
`H ≤ log d + 3 / 5` is not needed. -/
example {F : Type*} [Field F] (g : ℝ) (d D : ℕ)
    (hg : 0 < g) (hd : 48000 ≤ d) (hD : 0 < D)
    (hHlower : let H : ℝ := harmonic (d - 1); 54 / 5 ≤ H)
    (_hHlog : let H : ℝ := harmonic (d - 1); H ≤ Real.log d + 3 / 5)
    (hgH : let H : ℝ := harmonic (d - 1); xi ≤ g * H)
    (hnormalized : let H : ℝ := harmonic (d - 1); (1 + theta * g) / (g * H) ≤ 1 / xi)
    (hgm :
      let H : ℝ := harmonic (d - 1)
      let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
      270 * d * H ≤ g * m)
    (center received : F) :
    let H : ℝ := harmonic (d - 1)
    let a := 1 + theta * g
    let m := Nat.ceil (100 * (d : ℝ) ^ 2 * H)
    let W := Nat.floor (a * d * m / H)
    let V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2
    (Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (d := d) (W := W)
        (L := (m : ℝ) * D * (1 + g)) m hD center received)) : ℝ) /
        (V * m ^ 3) <
      g * (448 / 625) * (101 / 100) * (37 / 20) *
        a ^ 2 / H ^ 2 * (d : ℝ) ^ (1 / a) / d :=
  finrank_weightedSupportLocalConstraint_lt_prescribed g d D hg hd hD hHlower hgH hnormalized hgm
    center received

/-- The source's `weightedSupport_margin_of_normalized_rank`, with `48000 ≤ d`. -/
example {F : Type*} [Field F]
    (δ : ℝ) (n D d m W : ℕ) (hδ : 0 < δ) (hδmax : δ ≤ 1 / 4)
    (hn : 0 < n) (hD : 0 < D) (hd : 48000 ≤ d) (hm : 0 < m) (hW : 0 < W)
    (hρlo : δ / 3 ≤ (D : ℝ) / n) (hρhi : (D : ℝ) / n ≤ 1 - δ)
    (hHlo : xi / δ ≤ harmonic (d - 1))
    (hlog : xi / δ ≤ Real.log d)
    (hmean : let g := rateGap δ ((D : ℝ) / n)
      W * (harmonic (d - 1) : ℝ) / d ≤ (1 + 3 * g / 8) * m)
    (hs : let g := rateGap δ ((D : ℝ) / n)
      W / ((d : ℝ) * (g * m)) ≤ 10 / 27)
    (hfloor : let g := rateGap δ ((D : ℝ) / n)
      (999 / 1000) * ((1 + theta * g) / (g * harmonic (d - 1))) ^ 2 ≤
        (W / ((d : ℝ) * (g * m))) ^ 2)
    (hrank : let g := rateGap δ ((D : ℝ) / n)
      let a := 1 + theta * g
      let H : ℝ := harmonic (d - 1)
      let V : ℝ := (W : ℝ) ^ (d - 1) / ((d - 1).factorial : ℝ) ^ 2
      (Module.finrank F (LinearMap.range
        (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
          (L := (m : ℝ) * D * (1 + g)) m hD 0 0)) : ℝ) / (V * m ^ 3) ≤
        g * (448 / 625) * (101 / 100) * (37 / 20) * a ^ 2 / H ^ 2 *
          (d : ℝ) ^ (1 / a) / d) :
    let g := rateGap δ ((D : ℝ) / n)
    (543 / 500 : ℝ) * n * Module.finrank F (LinearMap.range
      (weightedSupportLocalConstraint (R := F) (d := d) (W := W)
        (L := (m : ℝ) * D * (1 + g)) m hD 0 0)) <
      Module.finrank F (weightedSupportSpace F D d W ((m : ℝ) * D * (1 + g)) hD) :=
  weightedSupport_margin_of_normalized_rank δ n D d m W hδ hδmax hn hD (by omega) hm hW
    hρlo hρhi hHlo hlog hmean hs hfloor hrank

/-- The prescribed surplus over `ZMod 2` at `δ = 1 / 4`, `n = 4`, `D = 2`. -/
example :
    let δ : ℝ := 1 / 4
    let d := ⌈Real.exp (xi / δ)⌉₊
    let H : ℝ := harmonic (d - 1)
    let g := rateGap δ (((2 : ℕ) : ℝ) / (4 : ℕ))
    let m := ⌈100 * (d : ℝ) ^ 2 * H⌉₊
    let W := ⌊(1 + theta * g) * d * m / H⌋₊
    (543 / 500 : ℝ) * (4 : ℕ) * Module.finrank (ZMod 2) (LinearMap.range
      (weightedSupportLocalConstraint (R := ZMod 2) (d := d) (W := W)
        (L := (m : ℝ) * (2 : ℕ) * (1 + g)) m (show 0 < 2 by norm_num) 0 0)) <
      Module.finrank (ZMod 2)
        (weightedSupportSpace (ZMod 2) 2 d W ((m : ℝ) * (2 : ℕ) * (1 + g)) (by norm_num)) :=
  prescribed_weightedSupport_margin (1 / 4) 4 2 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
