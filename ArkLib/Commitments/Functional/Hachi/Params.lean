/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Pablo Martín Vinuelas
-/
import ArkLib.Commitments.Functional.Hachi.Concrete
import ArkLib.Commitments.Functional.Hachi.QuadEval.Soundness
import Mathlib.Tactic.NormNum.Prime

/-!
# The `ℓ = 30` Hachi parameters, with ArkLib's conservative `τ = 5`

The [NOZ26] Figure 9 parameter set — the one the Hachi paper benchmarks — **except for the
folded-witness digit count `τ`**, together with the arithmetic facts the correctness chain consumes
at it. Nothing here is baked into the generic algebra: every declaration is a *value* or a *fact
about values*, and the theorems of `Correctness.lean` / `Concrete.lean` stay parametric.

```
  q  = 4294967197      prime modulus (≡ 5 mod 8)                Figure 9
  b  = 16              decomposition base                       Figure 9
  δ  = 8               message / inner digit count = ⌈log_b q⌉   Figure 9
  r  = 10, m = 10      folding parameters                       Figure 9
  ω  = 16              ℓ₁ bound on a challenge                  Figure 9
  α  = 10, d = 2^α = 1024   ring dimension of R_q               Figure 9
  n_A = n_B = n_D = 1  commitment-matrix heights                Figure 9

  τ  = 5               folded-witness digit count   ← ArkLib's, NOT Figure 9's
```

**`τ` differs from the paper's.** Figure 9 lists `τ = 4` together with its own `‖z‖∞ ≤ 30583`.
What is proved here is the *naive* deterministic bound `‖z‖∞ ≤ 2ʳ·ω·⌊b/2⌋ = 131072` ([NOZ26] §4.4),
and `131072` does not fit four balanced base-`16` digits, whose capacity is exactly the paper's
`30583` (`balancedDigitCapacity_four_eq`). So `τ = 5` is the least digit count that bound admits
(`tau_minimal`); `τ = 4` requires the sharper `‖z‖∞` analysis behind Figure 9's `30583`, which is
not formalized here. Everything else in the table is Figure 9 verbatim.

## Why `τ = 5` is not a full-width decomposition

`16 ^ 5 = 1048576 < q` (`sixteen_pow_tau_lt_q`), so **no** `5`-digit base-`16` decomposition of
every residue of `ZMod q` exists: a `DigitDecomposition (16 : ZMod q) 5` is impossible. What makes
`τ = 5` correct is that the honest folded witness `z = Σᵢ cᵢ sᵢ` is *deterministically* short,

```
  ‖z‖∞ ≤ 2ʳ · ω · ⌊b/2⌋ = 2¹⁰ · 16 · 8 = 131072      (honestZBound)
```

and `5` balanced base-`16` digits represent every integer up to
`(b − 1 − ⌊b/2⌋)·S = 7·69905 = 489335`, `S = 1 + 16 + 16² + 16³ + 16⁴` (`digitOnesValue_eq`,
`balancedDigitCapacity_eq`). Since `131072 ≤ 489335`, the honest decomposition never fails
(`honestZBound_le_capacity`): `τ = 5` has zero honest decomposition-failure probability. This is
what `BoundedDigitDecomposition` (`Gadget/Core.lean`) is for.

## Main definitions

* `hachiQ`, `hachiB`, `hachiDelta`, `hachiTau`, `hachiR`, `hachiM`, `hachiOmega`, `hachiAlpha`,
  `hachiD`, `hachiN` — the values above.
* `honestZBound` — the deterministic `ℓ∞` bound on the folded witness `z`, `131072`.
* `tau_minimal` — `τ = 5` is the *least* digit count that bound admits.
* `params` — the `HonestRangeParams hachiQ` profile (`γ = 15`, `bZero = 16`), at the pinned point
  `HonestRangeParams.ofPinnedDigitBase` realizes, together with the correctness theorem's `τ`-side
  hypotheses (`params_hcap`, `params_hzb`, `hachiTau_pos`, `clog_pos`) discharged at it.
* `mu0`, `liftKeyWidth`, `sumcheckWidthAtProfile` — the `τ`-dependent dimensions: the `R^lin`
  column count `μ₀ = 57344`, the lift key's `57384` columns, and the sumcheck coverage bound `hμn`
  at `M = 25` (least such, `sumcheckWidthAtProfile_minimal`).
* `quadEvalLink_perfectCompleteness_atProfile{,_paperRelOut}` — `QuadEval`'s bounded-`z` perfect
  completeness at the profile, in the ball-relaxed and the paper-exact Eq.-(20) readings.
* `betaSq`, `packageAtProfile` — Lemma 8's extracted norm bound and escape-aware CWSS certificate at
  the same `τ`, with the two relations coupling them to the completeness side.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter.HachiParams

open ArkLib.Lattices.Ajtai ArkLib.Lattices.CyclotomicModulus

/-! ## The values -/

/-- The prime modulus `q = 4294967197` ([NOZ26] Figure 9). -/
def hachiQ : ℕ := 4294967197
/-- The decomposition base `b = 16`. -/
def hachiB : ℕ := 16
/-- The message / inner digit count `δ = ⌈log_b q⌉ = 8`. -/
def hachiDelta : ℕ := 8
/-- The folded-witness digit count `τ = 5`, independent of `δ` and not [NOZ26] Figure 9's `τ = 4`:
it is the least count the bound `‖z‖∞ ≤ 2ʳ·ω·⌊b/2⌋ = 131072` admits (`tau_minimal`). -/
def hachiTau : ℕ := 5
/-- The outer folding parameter `r = 10`. -/
def hachiR : ℕ := 10
/-- The inner folding parameter `m = 10`. -/
def hachiM : ℕ := 10
/-- The `ℓ₁` bound `ω = 16` on a challenge element. -/
def hachiOmega : ℕ := 16
/-- `α = 10`: the log of the ring dimension. -/
def hachiAlpha : ℕ := 10
/-- The ring dimension `d = 2^α = 1024` of `R_q`. -/
def hachiD : ℕ := 1024

/-- The commitment-matrix heights `n_A = n_B = n_D = 1`. -/
def hachiN : ℕ := 1

/-- The deterministic bound on the honest folded witness proved here:
`‖z‖∞ ≤ 2ʳ · ω · ⌊b/2⌋ = 131072` (`vecLInftyNorm_honestZ_le`). This is the `zBound` the bounded `z`
decomposition is sized for, and hence what fixes `τ = 5`; [NOZ26] Figure 9's sharper `30583` is not
formalized here. -/
def honestZBound : ℕ := 2 ^ hachiR * hachiOmega * (hachiB / 2)

/-! ## The modulus -/

instance : NeZero hachiQ := ⟨by norm_num [hachiQ]⟩

-- `norm_num`'s Pratt-certificate prime extension needs a deeper recursion budget than the
-- default at a 32-bit modulus; the elaboration itself is fast (a few seconds).
set_option maxRecDepth 20000 in
/-- **`q = 4294967197` is prime.** Proved, not assumed: `norm_num`'s prime extension produces a
Pratt certificate, so no `decide`/`native_decide` is involved. -/
theorem hachiQ_prime : Nat.Prime hachiQ := by norm_num [hachiQ]

instance : Fact (Nat.Prime hachiQ) := ⟨hachiQ_prime⟩

/-- `q ≡ 5 (mod 8)` — the Lyubashevsky–Seiler condition ([NOZ26] §2.1) and the soundness side's
`hq5`. -/
theorem hachiQ_mod_eight : hachiQ % 8 = 5 := by norm_num [hachiQ]

/-! ## `δ = 8` is the full width, and `τ = 5` is not -/

/-- `q ≤ 16 ^ 8`: eight base-`16` digits cover `ZMod q`. This is the `hqm` the message and inner
decompositions take. -/
theorem q_le_sixteen_pow_delta : hachiQ ≤ hachiB ^ hachiDelta := by
  norm_num [hachiB, hachiQ, hachiDelta]

/-- `⌈log₁₆ q⌉ = 8 = δ`. -/
theorem clog_eq_delta : Nat.clog hachiB hachiQ = hachiDelta := by
  have hb : 1 < hachiB := by norm_num [hachiB]
  have h1 : Nat.clog hachiB hachiQ ≤ 8 :=
    (Nat.clog_le_iff_le_pow hb).mpr (by norm_num [hachiB, hachiQ])
  have h2 : ¬ Nat.clog hachiB hachiQ ≤ 7 := fun h =>
    absurd ((Nat.clog_le_iff_le_pow hb).mp h) (by norm_num [hachiB, hachiQ])
  simp only [hachiDelta]
  omega

/-- **`16 ^ 5 < q`**: no full-width `5`-digit decomposition of `ZMod q` exists, which is why the
`z` side goes through `BoundedDigitDecomposition` rather than `DigitDecomposition`. -/
theorem sixteen_pow_tau_lt_q : hachiB ^ hachiTau < hachiQ := by
  norm_num [hachiB, hachiQ, hachiTau]

/-! ## The balanced capacity of `τ = 5` digits -/

/-- `S = 1 + 16 + 16² + 16³ + 16⁴ = 69905`. -/
theorem digitOnesValue_eq : digitOnesValue hachiB hachiTau = 69905 := by
  norm_num [digitOnesValue, hachiB, hachiTau, Finset.sum_range_succ]

/-- The balanced capacity of `5` base-`16` digits: `(16 - 1 - 8)·S = 7·69905 = 489335`. -/
theorem balancedDigitCapacity_eq : balancedDigitCapacity hachiB hachiTau = 489335 := by
  rw [balancedDigitCapacity, digitOnesValue_eq]
  norm_num [hachiB]

/-- `honestZBound = 131072`. -/
theorem honestZBound_eq : honestZBound = 131072 := by
  norm_num [honestZBound, hachiR, hachiOmega, hachiB]

/-- **`131072 ≤ 489335`**: the honest bound fits the balanced-`5`-digit interval, so the honest
decomposition never fails and `τ = 5` costs no correctness error. -/
theorem honestZBound_le_capacity : honestZBound ≤ balancedDigitCapacity hachiB hachiTau := by
  rw [honestZBound_eq, balancedDigitCapacity_eq]; norm_num

/-! ### `τ = 5` is minimal, not merely sufficient

Four digits have capacity `7·(1+16+16²+16³) = 30583 < 131072`, and capacity is monotone in the digit
count (`balancedDigitCapacity_mono`), so the failure propagates to every `t < 5`. The `30583` is
precisely the value [NOZ26] Figure 9 lists for the maximum `ℓ∞` norm of `z` alongside its `τ = 4`:
four digits are saturated on the nose by the paper's sharper bound, and need five under the naive
one proved here. -/

/-- `∑_{e<4} 16ᵉ = 4369`. -/
theorem digitOnesValue_four_eq : digitOnesValue hachiB 4 = 4369 := by
  norm_num [digitOnesValue, hachiB, Finset.sum_range_succ]

/-- `balancedDigitCapacity 16 4 = 30583` — which is exactly [NOZ26] Figure 9's `z` bound. -/
theorem balancedDigitCapacity_four_eq : balancedDigitCapacity hachiB 4 = 30583 := by
  rw [balancedDigitCapacity, digitOnesValue_four_eq]
  norm_num [hachiB]

/-- **Four digits are not enough** for the bound proved here: `131072 > 30583`. -/
theorem honestZBound_not_le_capacity_four :
    ¬ (honestZBound ≤ balancedDigitCapacity hachiB 4) := by
  rw [honestZBound_eq, balancedDigitCapacity_four_eq]
  norm_num

/-- **`τ = 5` is minimal.** No digit count below `5` has the capacity for the honest bound
`131072`: capacity is monotone in the digit count, and it already fails at `4`. -/
theorem tau_minimal {t : ℕ} (ht : t < hachiTau) :
    ¬ (honestZBound ≤ balancedDigitCapacity hachiB t) := by
  intro hle
  refine honestZBound_not_le_capacity_four (le_trans hle ?_)
  exact balancedDigitCapacity_mono hachiB (by simp only [hachiTau] at ht; omega)

/-! ## The honest range parameters -/

/-- `1 < b`. -/
theorem one_lt_hachiB : 1 < hachiB := by norm_num [hachiB]

/-- `b ≤ ⌊q/2⌋` — the anti-wraparound condition for balanced digits. -/
theorem hachiB_le_half : hachiB ≤ hachiQ / 2 := by norm_num [hachiB, hachiQ]

/-- **The profile's honest range parameters**: `b = 16`, `γ = 15`, `bZero = 16`, the pinned point
`HonestRangeParams.ofPinnedDigitBase` realizes (`γ = bZero − 1 = b − 1`, both `O(b)` and far below
`q/2` — see `HonestRangeParams.pinned_of_soundness_orientations`). -/
def params : HonestRangeParams hachiQ :=
  HonestRangeParams.ofPinnedDigitBase hachiB one_lt_hachiB hachiB_le_half

@[simp] theorem params_b : params.b = hachiB := rfl
@[simp] theorem params_gamma : params.γ = hachiB - 1 := rfl
@[simp] theorem params_bZero : params.bZero = hachiB := rfl

/-- The reverse range orientation the nested zero-check's honest seam needs, at the profile:
`bZero − 1 ≤ γ` holds with equality. -/
theorem params_hZeroγ : params.bZero - 1 ≤ params.γ := le_refl _

/-- `0 < bZero`. -/
theorem params_bZero_pos : 0 < params.bZero := by norm_num [params_bZero, hachiB]

/-! ## The correctness theorem's `τ`-side hypotheses, at the profile

`hachiNonrecursive_perfectCorrectness` / `hachiNonrecursiveConcrete_perfectCorrectness` take `hcap`,
`hzb` and `hτ` on the `τ` side; the message side's `hqm` is `Nat.le_pow_clog`. All are discharged
here at `τ = 5`, `zBound = 131072`. -/

/-- `hcap`: the honest bound fits the balanced capacity of `τ = 5` digits. -/
theorem params_hcap : honestZBound ≤ balancedDigitCapacity params.b hachiTau := by
  simp only [params_b]; exact honestZBound_le_capacity

/-- `hzb`: the honest folded-witness bound `2ʳ·ω·⌊b/2⌋` *is* the `zBound` chosen, so the
inequality holds with equality. -/
theorem params_hzb : 2 ^ hachiR * hachiOmega * (hachiB / 2) ≤ honestZBound := le_refl _

/-- `hτ`: `0 < τ`. -/
theorem hachiTau_pos : 0 < hachiTau := by norm_num [hachiTau]

/-- `hclog`: `0 < ⌈log_b q⌉` (it is `8`). -/
theorem clog_pos : 0 < Nat.clog params.b hachiQ := by
  simp only [params_b]; rw [clog_eq_delta]; norm_num [hachiDelta]

/-! ## The ring dimension -/

/-- The ring dimension is `d = 2^α = 1024`. -/
theorem ringDim_eq : 𝓜(hachiQ, hachiAlpha).φ.natDegree = hachiD := by
  rw [primePowTwoModulus_natDegree]
  norm_num [hachiAlpha, hachiD]

/-- `hd`: the ring dimension is positive. -/
theorem ringDim_pos : 0 < 𝓜(hachiQ, hachiAlpha).φ.natDegree := by
  rw [ringDim_eq]; norm_num [hachiD]

/-! ## Lemma 8's norm bound, at the same `τ`

Hachi Lemma 8's extracted norm bound (`QuadEval/Soundness.lean`) is
`βSq = quadEvalBetaSq γ b τ d m δ`, parametric in the same `zDigits` the correctness chain uses. -/

/-- The soundness-side `βSq` of Lemma 8 at the profile, at `τ = 5`. The degree slot is the ring's
own `natDegree` rather than the literal `hachiD`, so this value is *syntactically* the `βSq` field
of `quadEvalPackage` at the profile. -/
def betaSq : ℕ :=
  quadEvalBetaSq params.γ hachiB hachiTau (𝓜(hachiQ, hachiAlpha)).φ.natDegree hachiM hachiDelta

/-! ## The profile instantiated: both security directions, at one `τ`

* `quadEvalLink_perfectCompleteness_atProfile{,_paperRelOut}` — `QuadEval`'s bounded-`z` perfect
  completeness at the profile, in both readings: ArkLib's ball-relaxed `relOut` and the paper's
  exact Eq.-(20) box `paperRelOut`. Every hypothesis is discharged from the arithmetic above, and
  none of them is `q ≤ b ^ τ`, which is false here.
* `packageAtProfile` — Lemma 8's escape-aware CWSS certificate at the profile, with
  `packageAtProfile_relOut` and `relInMsgShort_atProfile_subset_packageAtProfile_relIn` identifying
  its relations with the completeness side's. Both statements are typed in `zDigits`, so the two
  security directions cannot be read at two different `τ`.
* `mu0` / `liftKeyWidth` / `sumcheckWidthAtProfile` — the `τ`-dependent dimensions: `μ₀ = 57344`,
  the lift key's `μ₀ + n₀·δ = 57384` columns, and the sumcheck coverage bound at `M = 25`. -/

section Instantiated

open ArkLib.Lattices.Ajtai.InnerOuter
open OracleComp OracleSpec ProtocolSpec CoordinateWise

variable {innerRows outerRows dRows : ℕ}
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-! ### Completeness, both readings -/

set_option linter.unusedSectionVars false in
/-- **Perfect completeness of Hachi's polynomial-evaluation link at this file's profile** — the
[NOZ26] Figure 9 `ℓ = 30` parameters (`q = 4294967197`, `b = 16`, `δ = 8`, `r = m = 10`, `ω = 16`,
`α = 10`) with ArkLib's conservative `τ = 5` — ball-relaxed reading, error `0`.

Every hypothesis is discharged from this file's arithmetic: the message side by
`q_le_sixteen_pow_delta`, the `z` side by `honestZBound_le_capacity` (capacity `489335 ≥ 131072`)
and `params_hzb`, the anti-wraparound by `hachiB_le_half`, the ring dimension by `ringDim_pos`. No
`q ≤ 16 ^ 5` appears anywhere; it is false (`sixteen_pow_tau_lt_q`). -/
theorem quadEvalLink_perfectCompleteness_atProfile
    [∀ i, SampleableType
      ((CoordinateWise.SingleRound.pSpec
          (CarrierCom 𝓜(hachiQ, hachiAlpha) dRows)
          (ShortChallenge 𝓜(hachiQ, hachiAlpha) hachiOmega) hachiR).Challenge i)]
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD 𝓜(hachiQ, hachiAlpha) innerRows (2 ^ hachiM) hachiDelta outerRows
      (2 ^ hachiR) hachiDelta dRows)
    {βSq κ : ℕ} :
    (quadEvalReduction (oSpec := oSpec) (zDigits := hachiTau) (ω := hachiOmega)
        𝓜(hachiQ, hachiAlpha) pp
        (balancedZmodDigitDecomposition hachiB hachiDelta one_lt_hachiB q_le_sixteen_pow_delta)
        (boundedBalancedZmodDigitDecomposition hachiB hachiTau honestZBound one_lt_hachiB
          honestZBound_le_capacity)).perfectCompleteness init impl
      (relInMsgShort 𝓜(hachiQ, hachiAlpha) pp (hachiB : ZMod hachiQ) βSq hachiB κ (hachiB / 2))
      (relOut (zDigits := hachiTau) 𝓜(hachiQ, hachiAlpha) pp (hachiB : ZMod hachiQ)
        hachiOmega hachiB) :=
  quadEvalReduction_perfectCompleteness_boundedBalancedDigits
    𝓜(hachiQ, hachiAlpha) init impl pp
    (powTwoCyclotomic_hasMulLInftyBound hachiAlpha)
    one_lt_hachiB q_le_sixteen_pow_delta honestZBound_le_capacity hachiB_le_half
    params_hzb
    (by norm_num [hachiDelta]) hachiTau_pos ringDim_pos

set_option linter.unusedSectionVars false in
/-- **Paper-exact perfect completeness at this file's profile** — the Figure 3 *verifier* verbatim
(Eq. (20)'s balanced-digit box `S₁₆ = [-8, 7]`, not the enclosing `ℓ∞` ball), at ArkLib's
conservative `τ = 5`, error `0`. "Paper-exact" here qualifies the verifier, not the digit count: the
`τ` is ours, Figure 9's is `4`.

Same discharge as the ball-relaxed reading, with the box range steps in place of the ball ones:
`boundedBalancedZmodDigit_valMinAbs_mem` puts the honest `ẑ` digits exactly in `S₁₆`, and does so
unconditionally, so the paper-exact reading costs nothing extra at these parameters. The input
relation is `relInBoxMsgShort` (see `relInBox` for why the input opening's own box shortness is part
of the relation). -/
theorem quadEvalLink_perfectCompleteness_atProfile_paperRelOut
    [∀ i, SampleableType
      ((CoordinateWise.SingleRound.pSpec
          (CarrierCom 𝓜(hachiQ, hachiAlpha) dRows)
          (ShortChallenge 𝓜(hachiQ, hachiAlpha) hachiOmega) hachiR).Challenge i)]
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD 𝓜(hachiQ, hachiAlpha) innerRows (2 ^ hachiM) hachiDelta outerRows
      (2 ^ hachiR) hachiDelta dRows)
    {βSq γ κ : ℕ} :
    (quadEvalReduction (oSpec := oSpec) (zDigits := hachiTau) (ω := hachiOmega)
        𝓜(hachiQ, hachiAlpha) pp
        (balancedZmodDigitDecomposition hachiB hachiDelta one_lt_hachiB q_le_sixteen_pow_delta)
        (boundedBalancedZmodDigitDecomposition hachiB hachiTau honestZBound one_lt_hachiB
          honestZBound_le_capacity)).perfectCompleteness init impl
      (relInBoxMsgShort 𝓜(hachiQ, hachiAlpha) pp (hachiB : ZMod hachiQ) βSq γ κ hachiB
        (hachiB / 2))
      (paperRelOut (zDigits := hachiTau) 𝓜(hachiQ, hachiAlpha) pp (hachiB : ZMod hachiQ)
        hachiOmega hachiB) :=
  quadEvalReduction_perfectCompleteness_boundedBalancedDigits_paperRelOut
    𝓜(hachiQ, hachiAlpha) init impl pp
    (powTwoCyclotomic_hasMulLInftyBound hachiAlpha)
    one_lt_hachiB q_le_sixteen_pow_delta honestZBound_le_capacity hachiB_le_half
    params_hzb
    (by norm_num [hachiDelta]) hachiTau_pos ringDim_pos

/-! ### Soundness at the same `τ`, and the coupling -/

/-- `(2ω)² < q` at the profile: `32² = 1024 < 4294967197` — the Lyubashevsky–Seiler slack
condition Lemma 8's extraction needs. -/
theorem sq_two_omega_lt_q : (2 * hachiOmega) ^ 2 < hachiQ := by
  norm_num [hachiOmega, hachiQ]

/-- **Hachi Lemma 8's escape-aware CWSS certificate at this file's profile**, at the same
`zDigits = τ = 5` the correctness chain uses and at the chain's own ball radius `γ = params.γ = 15`
(soundness is parametric in `γ`; the correctness chain pins it to `bZero − 1`). -/
def packageAtProfile
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD 𝓜(hachiQ, hachiAlpha) innerRows (2 ^ hachiM) hachiDelta outerRows
      (2 ^ hachiR) hachiDelta dRows) :=
  quadEvalPackage (zDigits := hachiTau) (b := hachiB) (ω := hachiOmega) (γ := params.γ)
    init impl hachiQ_mod_eight sq_two_omega_lt_q hachiTau_pos pp

set_option linter.unusedSectionVars false in
/-- **Coupling, output side.** The soundness certificate's output relation is the relation the
completeness theorems land in, at `γ = params.γ`. Holds by `rfl`; note it could not be *stated* at
two different `zDigits`, since `relOut`'s witnesses are `QuadEvalResponse … zDigits`. -/
theorem packageAtProfile_relOut
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD 𝓜(hachiQ, hachiAlpha) innerRows (2 ^ hachiM) hachiDelta outerRows
      (2 ^ hachiR) hachiDelta dRows) :
    (packageAtProfile (oSpec := oSpec) init impl pp).relOut
      = relOut (zDigits := hachiTau) 𝓜(hachiQ, hachiAlpha) pp (hachiB : ZMod hachiQ)
          hachiOmega params.γ :=
  rfl

set_option linter.unusedSectionVars false in
/-- **Coupling, input side.** The correctness-side input relation at the profile —
`relInMsgShort` at the certificate's own `βSq = betaSq` and `κ = 2ω` — lands inside the package's
`relIn`. So the `βSq` the extractor produces and the `βSq` the honest chain is stated at are the
same value, computed from the same `τ`. -/
theorem relInMsgShort_atProfile_subset_packageAtProfile_relIn
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD 𝓜(hachiQ, hachiAlpha) innerRows (2 ^ hachiM) hachiDelta outerRows
      (2 ^ hachiR) hachiDelta dRows) :
    relInMsgShort 𝓜(hachiQ, hachiAlpha) pp (hachiB : ZMod hachiQ) betaSq params.γ
        (2 * hachiOmega) (hachiB / 2)
      ⊆ (packageAtProfile (oSpec := oSpec) init impl pp).relIn :=
  relInMsgShort_subset_relIn 𝓜(hachiQ, hachiAlpha) pp (hachiB : ZMod hachiQ) betaSq params.γ
    (2 * hachiOmega) (hachiB / 2)

/-! ### The `τ`-dependent dimensions -/

/-- The `R^lin` column count `μ₀ = 2ʳ·δ + (2ʳ·(n_A·δ) + 2ᵐ·δ·τ)` at the profile, with the digit
counts written as `Nat.clog` the way the chain writes them, so that it unifies with the `μ₀` of
`Correctness.lean` / `Concrete.lean`. -/
abbrev mu0 : ℕ :=
  rlinCols hachiN (Nat.clog params.b hachiQ) (Nat.clog params.b hachiQ) hachiTau hachiM hachiR

/-- `μ₀ = 57344` at `τ = 5`. -/
theorem mu0_eq : mu0 = 57344 := by
  rw [mu0, params_b, clog_eq_delta]
  norm_num [rlinCols, hachiN, hachiDelta, hachiTau, hachiM, hachiR]

/-- The lift key's column count at the profile: `μ₀ + n₀·δ_{bZero}`, the width a whole lifted
witness needs once the quotient block is committed as its base-`bZero` digits. -/
abbrev liftKeyWidth : ℕ :=
  mu0 + rlinRows hachiN hachiN hachiN * rhoDigitCount hachiQ params.bZero

/-- `μ₀ + n₀·δ = 57344 + 5·8 = 57384`. -/
theorem liftKeyWidth_eq : liftKeyWidth = 57384 := by
  rw [liftKeyWidth, mu0_eq, rhoDigitCount, params_bZero, clog_eq_delta]
  norm_num [rlinRows, hachiN, hachiDelta]

/-- **The sumcheck coverage hypothesis is satisfiable at the profile**, at `M = 25`: the
digit-committed table is `57384` rows of `d = 1024` coefficients, i.e. `58761216 ≤ 2²⁶`. This is
the `hμn` of the correctness theorem, discharged. -/
theorem sumcheckWidthAtProfile :
    liftKeyWidth * 𝓜(hachiQ, hachiAlpha).φ.natDegree ≤ 2 ^ (25 + 1) := by
  rw [liftKeyWidth_eq, ringDim_eq]
  norm_num [hachiD]

/-- **And `M = 25` is the least such width**: at `M = 24` the cube has only `2²⁵ = 33554432`
points, below the table's `58761216`. -/
theorem sumcheckWidthAtProfile_minimal :
    ¬ (liftKeyWidth * 𝓜(hachiQ, hachiAlpha).φ.natDegree ≤ 2 ^ (24 + 1)) := by
  rw [liftKeyWidth_eq, ringDim_eq]
  norm_num [hachiD]

/-! ### The scheme-level hypotheses, collected

`hachiNonrecursiveConcrete_perfectCorrectness` is parametric in `τ`/`zBound`, and each of its
profile-side hypotheses is one of the facts above: `hcap` = `params_hcap`, `hzb` = `params_hzb`,
`hτ` = `hachiTau_pos`, `hclog` = `clog_pos`, `hd` = `ringDim_pos`, `hbZero` = `params_bZero_pos`,
`hZeroγ` = `params_hZeroγ`, `hμn` = `sumcheckWidthAtProfile` at `M = 25`. The substituted instance
is not written out as a declaration: its *type* alone carries `Nat.clog params.b 4294967197` inside
`Fin (2¹⁰)`-indexed matrices, a `μ₀ = 57344` column count and a 26-deep `ProtocolSpec` append tower,
which exhausts the elaborator's `isDefEq` budget. The `τ` agreement between the two security
directions is pinned one layer down instead, at `QuadEval`, where `τ` enters both. -/

end Instantiated

end ArkLib.Lattices.Ajtai.InnerOuter.HachiParams
