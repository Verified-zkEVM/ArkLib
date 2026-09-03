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

The [NOZ26] Figure 9 parameter set — the one the Hachi paper benchmarks and a Rust implementation
is meant to agree with — **except for the folded-witness digit count `τ`**, together with the
arithmetic facts the correctness chain consumes at it. Nothing here is baked into the generic
algebra: every declaration is a *value* or a *fact about values*, and the theorems of
`Correctness.lean` / `Concrete.lean` stay parametric.

```
  q  = 4294967197      prime modulus (≡ 5 mod 8)          Figure 9
  b  = 16              decomposition base                  Figure 9
  δ  = 8               message / inner digit count = ⌈log_b q⌉   Figure 9
  r  = 10, m = 10      folding parameters                  Figure 9
  ω  = 16              ℓ₁ bound on a challenge             Figure 9
  α  = 10, d = 2^α = 1024   ring dimension of R_q          Figure 9
  n_A = n_B = n_D = 1  commitment-matrix heights           Figure 9

  τ  = 5               folded-witness digit count   ← ArkLib's, NOT Figure 9's
```

**`τ` deliberately differs from the paper's.** Figure 9 lists `τ = 4`, together with its own
`‖z‖∞ ≤ 30583`. This development proves the *naive* deterministic bound
`‖z‖∞ ≤ 2ʳ·ω·⌊b/2⌋ = 131072` ([NOZ26] §4.4) and nothing sharper, and `131072` does not fit four
balanced base-`16` digits — whose capacity is `30583`, exactly the paper's own `z` value
(`balancedDigitCapacity_four_eq`). So `τ = 5` is the least digit count *this* bound admits
(`tau_minimal`), and it is a **conservative** choice, not the paper's: recovering `τ = 4` needs the
sharper `‖z‖∞` analysis behind Figure 9's `30583`, which is not formalized here. Everything else in
the table is Figure 9 verbatim.

## Why `τ = 5` is not a full-width decomposition

`16 ^ 5 = 1048576 < q` (`sixteen_pow_tau_lt_q`), so **no** `5`-digit base-`16` decomposition of
every residue of `ZMod q` exists: a `DigitDecomposition (16 : ZMod q) 5` is impossible, and
`q ≤ 16 ^ 5` is false. What makes `τ = 5` correct is that the honest folded witness
`z = Σᵢ cᵢ sᵢ` is *deterministically* short:

```
  ‖z‖∞ ≤ 2ʳ · ω · ⌊b/2⌋ = 2¹⁰ · 16 · 8 = 131072      (honestZBound)
```

and `5` balanced base-`16` digits represent every integer of
`[-8·S, 7·S] = [-559240, 489335]`, `S = 1 + 16 + 16² + 16³ + 16⁴ = 69905`
(`digitOnesValue_eq`, `balancedDigitCapacity_eq`). Since `131072 ≤ 489335`, the honest
decomposition **never** fails: `τ = 5` has zero honest decomposition-failure probability
(`honestZBound_le_capacity`). The paper's coarser bound `2ʳ·ω·b = 262144` also fits
(`paperZBound_le_capacity`), so the conclusion does not depend on which of the two bounds is
used.

## Main definitions

* `hachiQ`, `hachiB`, `hachiDelta`, `hachiTau`, `hachiR`, `hachiM`, `hachiOmega`, `hachiAlpha`,
  `hachiD` — the values above.
* `honestZBound` / `paperZBound` — the tight and the paper-coarse deterministic `ℓ∞` bounds on `z`.
* `params` — the `HonestRangeParams hachiQ` profile (`γ = 15`, `bZero = 16`), at the pinned point
  `HonestRangeParams.ofPinnedDigitBase` realizes.
* `tau_minimal` — `τ = 5` is the *least* digit count the bound proved here admits; `τ = 4`, which is
  Figure 9's, is ruled out at `131072` (`honestZBound_not_le_capacity_four`).
* `mu0` — the `R^lin` column count `μ₀` at the profile, and `mu0_eq` its value `57344`; `mu0_full`
  records what the discarded full-width choice `τ := δ` would have cost (`81920`).
* `betaSq` — the *soundness*-side `βSq = quadEvalBetaSq γ b τ d m δ` of Hachi Lemma 8, at the very
  same `τ = 5`. It exists here to make the correctness/soundness agreement on `τ` a checkable
  artifact rather than a comment.

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
/-- The folded-witness digit count `τ = 5` — **independent** of `δ`, and **not** [NOZ26]
Figure 9's `τ = 4`: it is the least count the naive bound `‖z‖∞ ≤ 2ʳ·ω·⌊b/2⌋ = 131072` proved here
admits (`tau_minimal`). See the module docstring. -/
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

/-- The **tightest deterministic bound this development proves** on the honest folded witness:
`‖z‖∞ ≤ 2ʳ · ω · ⌊b/2⌋ = 131072` (`vecLInftyNorm_honestZ_le`). This is the `zBound` the bounded `z`
decomposition is sized for, and hence what fixes `τ = 5`. Sharper is possible — [NOZ26] Figure 9
reports `30583` — but is not formalized here. -/
def honestZBound : ℕ := 2 ^ hachiR * hachiOmega * (hachiB / 2)

/-- The coarser deterministic bound `2ʳ · ω · b = 262144` written in [NOZ26] §4.4. Recorded
because the `τ = 5` conclusion must not depend on which of the two bounds is used.

Not to be confused with Figure 9's `30583`, which is a *third*, much sharper `‖z‖∞` value obtained
by a concrete analysis this development does not formalize — and the one Figure 9's `τ = 4` needs
(see the `τ = 5` minimality section). -/
def paperZBound : ℕ := 2 ^ hachiR * hachiOmega * hachiB

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

/-! ## `δ = 8` is the full width, and `τ = 5` is not

The two inequalities that bracket `⌈log₁₆ q⌉`, and the one that shows a `5`-digit *full*
decomposition cannot exist. -/

/-- `16 ^ 7 < q`: seven base-`16` digits do not cover `ZMod q`. -/
theorem sixteen_pow_seven_lt_q : hachiB ^ 7 < hachiQ := by norm_num [hachiB, hachiQ]

/-- `q ≤ 16 ^ 8`: eight base-`16` digits do cover `ZMod q` — the `hqm` the message and inner
decompositions legitimately need. -/
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

/-- **`16 ^ 5 < q`** — the fact that rules out a full-width `τ = 5` decomposition. Deliberately
stated: it is the reason `BoundedDigitDecomposition` exists, and any proof that assumed
`q ≤ 16 ^ τ` would be unsound. -/
theorem sixteen_pow_tau_lt_q : hachiB ^ hachiTau < hachiQ := by
  norm_num [hachiB, hachiQ, hachiTau]

/-- The contrapositive form: `q ≤ 16 ^ τ` is **false**. No declaration in the `τ = 5` correctness
path may depend on it. -/
theorem not_q_le_sixteen_pow_tau : ¬ (hachiQ ≤ hachiB ^ hachiTau) :=
  not_le_of_gt sixteen_pow_tau_lt_q

/-! ## The balanced capacity of `τ = 5` digits -/

/-- `S = 1 + 16 + 16² + 16³ + 16⁴ = 69905`. -/
theorem digitOnesValue_eq : digitOnesValue hachiB hachiTau = 69905 := by
  norm_num [digitOnesValue, hachiB, hachiTau, Finset.sum_range_succ]

/-- The **positive** balanced capacity of `5` base-`16` digits: `(16 - 1 - 8)·S = 7·69905 =
489335`. -/
theorem balancedDigitCapacity_eq : balancedDigitCapacity hachiB hachiTau = 489335 := by
  rw [balancedDigitCapacity, digitOnesValue_eq]
  norm_num [hachiB]

/-- The **negative** balanced capacity of `5` base-`16` digits: `8·S = 559240`. -/
theorem negBalancedCapacity_eq : (hachiB / 2) * digitOnesValue hachiB hachiTau = 559240 := by
  rw [digitOnesValue_eq]
  norm_num [hachiB]

/-- The tight honest bound is `131072`. -/
theorem honestZBound_eq : honestZBound = 131072 := by
  norm_num [honestZBound, hachiR, hachiOmega, hachiB]

/-- The paper's coarse honest bound is `262144`. -/
theorem paperZBound_eq : paperZBound = 262144 := by
  norm_num [paperZBound, hachiR, hachiOmega, hachiB]

/-- **`131072 ≤ 489335`**: the tight honest bound fits the positive balanced-`5`-digit interval.
This is the inequality that makes `τ = 5` a *perfectly* correct choice — zero honest decomposition
failure probability. -/
theorem honestZBound_le_capacity : honestZBound ≤ balancedDigitCapacity hachiB hachiTau := by
  rw [honestZBound_eq, balancedDigitCapacity_eq]; norm_num

/-- `131072 ≤ 559240`: it fits the negative side too. -/
theorem honestZBound_le_negCapacity :
    honestZBound ≤ (hachiB / 2) * digitOnesValue hachiB hachiTau := by
  rw [honestZBound_eq, negBalancedCapacity_eq]; norm_num

/-- `262144 ≤ 489335`: the paper's coarser bound fits as well, so the `τ = 5` conclusion is
independent of which deterministic bound is used. -/
theorem paperZBound_le_capacity : paperZBound ≤ balancedDigitCapacity hachiB hachiTau := by
  rw [paperZBound_eq, balancedDigitCapacity_eq]; norm_num

/-- `262144 ≤ 559240`, the negative side of the same. -/
theorem paperZBound_le_negCapacity :
    paperZBound ≤ (hachiB / 2) * digitOnesValue hachiB hachiTau := by
  rw [paperZBound_eq, negBalancedCapacity_eq]; norm_num

/-! ### `τ = 5` is *minimal*, not merely sufficient

Sufficiency (`honestZBound_le_capacity`) says five digits are enough. Minimality says four are not:
`balancedDigitCapacity 16 4 = 7·(1+16+16²+16³) = 7·4369 = 30583 < 131072`, and since capacity is
monotone in the digit count (`balancedDigitCapacity_mono`) the same failure propagates to every
`t < 5`. So `5` is the least digit count the bound proved here admits.

This is also where this development's `τ` parts company with the paper's, and the arithmetic says
exactly why: `30583` is *precisely* the value [NOZ26] Figure 9 lists for "maximum `L∞` norm of `z`",
alongside its `τ = 4`. So the paper's `τ = 4` is admissible only under that **sharper** `‖z‖∞`
bound, which saturates four digits' capacity on the nose — whereas the naive
`2ʳ·ω·⌊b/2⌋ = 131072` proved here needs five. Formalizing the sharper bound would let `τ` drop to
`4`; nothing here assumes it, and `tau_minimal` is stated relative to the bound actually proved. -/

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

/-- Four digits fail on the negative side too: `8·4369 = 34952 < 131072`. -/
theorem negCapacity_four_lt_honestZBound :
    (hachiB / 2) * digitOnesValue hachiB 4 < honestZBound := by
  rw [digitOnesValue_four_eq, honestZBound_eq]
  norm_num [hachiB]

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

/-- `γ = 15`. -/
theorem params_gamma_eq : params.γ = 15 := by norm_num [params_gamma, hachiB]

/-- The reverse range orientation the nested zero-check's honest seam needs, at the profile:
`bZero − 1 ≤ γ` holds with equality. -/
theorem params_hZeroγ : params.bZero - 1 ≤ params.γ := le_refl _

/-- `0 < bZero`. -/
theorem params_bZero_pos : 0 < params.bZero := by norm_num [params_bZero, hachiB]

/-! ## The three `τ`-side hypotheses of the correctness theorem, at the profile

`hachiNonrecursive_perfectCorrectness` / `hachiNonrecursiveConcrete_perfectCorrectness` take
exactly `hcap`, `hzb` and `hτ` on the `τ` side (plus `hqm` on the message side, which is
`Nat.le_pow_clog`). All four are discharged here at `τ = 5`, `zBound = 131072`. -/

/-- `hcap`: the honest bound fits the balanced capacity of `τ = 5` digits. -/
theorem params_hcap : honestZBound ≤ balancedDigitCapacity params.b hachiTau := by
  simp only [params_b]; exact honestZBound_le_capacity

/-- `hzb`: the honest folded-witness bound `2ʳ·ω·⌊b/2⌋` is the `zBound` chosen (equality). -/
theorem params_hzb : 2 ^ hachiR * hachiOmega * (params.b / 2) ≤ honestZBound := le_refl _

/-- `hτ`: `0 < τ`. -/
theorem hachiTau_pos : 0 < hachiTau := by norm_num [hachiTau]

/-- `hzb` in the base-only form the `QuadEval` link takes: `2ʳ·ω·⌊b/2⌋ ≤ honestZBound`. -/
theorem params_hzb' : 2 ^ hachiR * hachiOmega * (hachiB / 2) ≤ honestZBound := le_refl _

/-- `hclog`: `0 < ⌈log_b q⌉` (it is `8`). -/
theorem clog_pos : 0 < Nat.clog params.b hachiQ := by
  simp only [params_b]; rw [clog_eq_delta]; norm_num [hachiDelta]

/-! ## The ring, and the dimensions `τ` feeds -/

/-- The ring dimension is `d = 2^α = 1024`. -/
theorem ringDim_eq : 𝓜(hachiQ, hachiAlpha).φ.natDegree = hachiD := by
  rw [primePowTwoModulus_natDegree]
  norm_num [hachiAlpha, hachiD]

/-- `hd`: the ring dimension is positive. -/
theorem ringDim_pos : 0 < 𝓜(hachiQ, hachiAlpha).φ.natDegree := by
  rw [ringDim_eq]; norm_num [hachiD]

/-- The `R^lin` column count `μ₀` at the profile: `2ʳ·δ + (2ʳ·(n_A·δ) + 2ᵐ·δ·τ)`, with `τ = 5` in
the last block. -/
def mu0 : ℕ := rlinCols hachiN hachiDelta hachiDelta hachiTau hachiM hachiR

/-- `μ₀ = 57344` at `τ = 5`. -/
theorem mu0_eq : mu0 = 57344 := by
  norm_num [mu0, rlinCols, hachiN, hachiDelta, hachiTau, hachiM, hachiR]

/-- What the *discarded* full-width choice `τ := δ` would have cost: `81920` columns, `24576` more
than `mu0`. Recorded so the size consequence of separating `τ` from `δ` is visible. -/
theorem mu0_full : rlinCols hachiN hachiDelta hachiDelta hachiDelta hachiM hachiR = 81920 := by
  norm_num [rlinCols, hachiN, hachiDelta, hachiM, hachiR]

/-- The `R^lin` row count `n₀ = 5` at the profile. -/
theorem n0_eq : rlinRows hachiN hachiN hachiN = 5 := by
  norm_num [rlinRows, hachiN]

/-! ## Soundness uses the same `τ`

Hachi Lemma 8's extracted norm bound (`QuadEval/Soundness.lean`) is
`βSq = quadEvalBetaSq γ b τ d m δ`, parametric in the very same `zDigits`. Naming it at the profile
makes the agreement checkable: if a future edit desynchronized the two sides, `betaSq` below and
the `zDigits` of `hachiNonrecursiveConcrete` could not both be `5`. -/

/-- The soundness-side `βSq` of Lemma 8 at the profile — **at `τ = 5`**, the same `zDigits` the
correctness chain uses. The degree slot is the ring's own `natDegree` rather than the literal
`hachiD`, so that this value is *syntactically* the `βSq` field of `quadEvalPackage` at the profile
(`packageAtProfile_relIn`, a `rfl`); `betaSq_eq_hachiD` is the numeric reading. -/
def betaSq : ℕ :=
  quadEvalBetaSq params.γ hachiB hachiTau (𝓜(hachiQ, hachiAlpha)).φ.natDegree hachiM hachiDelta

/-- `betaSq` read at the literal ring dimension `d = 1024`. -/
theorem betaSq_eq_hachiD :
    betaSq = quadEvalBetaSq params.γ hachiB hachiTau hachiD hachiM hachiDelta := by
  rw [betaSq, ringDim_eq]

/-! ## The profile instantiated: both security directions, at one `τ`

Three things live here, in increasing strength.

1. `quadEvalLink_perfectCompleteness_atProfile{,_paperRelOut}` — `QuadEval`'s bounded-`z` perfect
   completeness at the profile, in **both** readings (ArkLib's ball-relaxed `relOut` and the paper's
   exact Eq.-(20) box `paperRelOut`), with every hypothesis discharged from the arithmetic above.
   These are also the strongest available check that the `τ = 5` path needs **no** `q ≤ b ^ τ`: if
   such an obligation existed anywhere in the path, these applications could not elaborate, since
   `not_q_le_sixteen_pow_tau` says the obligation is false.
2. `packageAtProfile` — the **soundness** side (Hachi Lemma 8's escape-aware CWSS certificate) at
   the profile, and the two coupling lemmas `packageAtProfile_relOut` /
   `relInMsgShort_atProfile_subset_packageAtProfile_relIn`. These are what make the `τ` agreement
   *mechanical* rather than editorial: the first is an equation between the package's output
   relation and the completeness theorems' output relation, and it cannot even be *stated* at two
   different `zDigits` (the `QuadEvalResponse` types would differ); the second lands the
   correctness-side input relation inside the package's `relIn`, whose `βSq` is `betaSq`, i.e.
   `quadEvalBetaSq … hachiTau …`. Desynchronize `τ` on either side and one of the two stops
   typechecking.
3. `mu0Raw` / `liftKeyWidth` / `sumcheckWidthAtProfile` — the `τ`-dependent *dimensions* at the
   profile: `μ₀ = 57344`, the lift key's `μ₀ + n₀·δ = 57384` columns, and the fact that the
   sumcheck coverage hypothesis `hμn` is satisfiable at `M = 25` (a `26`-round sumcheck) and not at
   `M = 24` (`sumcheckWidthAtProfile_minimal`). The scheme-level substitution itself is *not*
   spelled out as a named declaration — see the note at the end of this section for why (an
   elaborator cost, not a gap). -/

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
and `params_hzb`, the anti-wraparound by `hachiB_le_half`, the ring dimension by `ringDim_pos`.
**No `q ≤ 16 ^ 5` appears** — it is false (`not_q_le_sixteen_pow_tau`). -/
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
    params_hzb'
    (by norm_num [hachiDelta]) hachiTau_pos ringDim_pos

set_option linter.unusedSectionVars false in
/-- **Paper-exact perfect completeness at this file's profile** — the Figure 3 *verifier* verbatim
(Eq. (20)'s balanced-digit box `S₁₆ = [-8, 7]`, not the enclosing `ℓ∞` ball), at ArkLib's
conservative `τ = 5`, error `0`. "Paper-exact" here qualifies the verifier, not the digit count: the
`τ` is ours, Figure 9's is `4`.

Same discharge as the ball-relaxed reading, with the box range steps in place of the ball ones:
`boundedBalancedZmodDigit_valMinAbs_mem` puts the honest `ẑ` digits *exactly* in `S₁₆` — and does
so unconditionally, so the paper-exact reading costs nothing extra over the relaxed one at these
parameters. The input relation is `relInBoxMsgShort` (see `relInBox` for why the input opening's own
box shortness has to be part of the relation). **No `q ≤ 16 ^ 5` appears** here either. -/
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
    params_hzb'
    (by norm_num [hachiDelta]) hachiTau_pos ringDim_pos

/-! ### Soundness at the same `τ`, and the coupling -/

/-- `(2ω)² < q` at the profile: `32² = 1024 < 4294967197` — the Lyubashevsky–Seiler slack
condition Lemma 8's extraction needs. -/
theorem sq_two_omega_lt_q : (2 * hachiOmega) ^ 2 < hachiQ := by
  norm_num [hachiOmega, hachiQ]

/-- **Hachi Lemma 8's escape-aware CWSS certificate at this file's profile**, at the *same*
`zDigits = τ = 5` the correctness chain uses, and at the chain's own ball radius `γ = params.γ =
15` (soundness is parametric in `γ`; the correctness chain pins it to `bZero − 1`). -/
def packageAtProfile
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD 𝓜(hachiQ, hachiAlpha) innerRows (2 ^ hachiM) hachiDelta outerRows
      (2 ^ hachiR) hachiDelta dRows) :=
  quadEvalPackage (zDigits := hachiTau) (b := hachiB) (ω := hachiOmega) (γ := params.γ)
    init impl hachiQ_mod_eight sq_two_omega_lt_q hachiTau_pos pp

set_option linter.unusedSectionVars false in
/-- **Coupling, output side.** The soundness certificate's output relation *is* the relation the
completeness theorems land in, at `γ = params.γ`. Holds by `rfl` — and, more to the point, the
statement could not be *written* if the two sides used different `zDigits`: `relOut` is a set of
pairs whose second component is `QuadEvalResponse … zDigits`, so a mismatch is a type error, not a
silent disagreement. -/
theorem packageAtProfile_relOut
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD 𝓜(hachiQ, hachiAlpha) innerRows (2 ^ hachiM) hachiDelta outerRows
      (2 ^ hachiR) hachiDelta dRows) :
    (packageAtProfile (oSpec := oSpec) init impl pp).relOut
      = relOut (zDigits := hachiTau) 𝓜(hachiQ, hachiAlpha) pp (hachiB : ZMod hachiQ)
          hachiOmega params.γ :=
  rfl

set_option linter.unusedSectionVars false in
/-- **Coupling, input side.** The correctness-side input relation at the profile — `relInMsgShort`
at the *soundness* certificate's own `βSq = betaSq = quadEvalBetaSq … hachiTau …` and `κ = 2ω` —
lands inside the package's `relIn`. So the `βSq` the extractor produces and the `βSq` the honest
chain is stated at are the same value, computed from the same `τ`; had `betaSq` been formed at a
different `zDigits`, this would not typecheck. -/
theorem relInMsgShort_atProfile_subset_packageAtProfile_relIn
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD 𝓜(hachiQ, hachiAlpha) innerRows (2 ^ hachiM) hachiDelta outerRows
      (2 ^ hachiR) hachiDelta dRows) :
    relInMsgShort 𝓜(hachiQ, hachiAlpha) pp (hachiB : ZMod hachiQ) betaSq params.γ
        (2 * hachiOmega) (hachiB / 2)
      ⊆ (packageAtProfile (oSpec := oSpec) init impl pp).relIn :=
  relInMsgShort_subset_relIn 𝓜(hachiQ, hachiAlpha) pp (hachiB : ZMod hachiQ) betaSq params.γ
    (2 * hachiOmega) (hachiB / 2)

set_option linter.unusedSectionVars false in
/-- **The completeness theorem, restated at the soundness certificate's own parameters.** Same
theorem as `quadEvalLink_perfectCompleteness_atProfile`, with `βSq := betaSq` and `κ := 2ω` filled
in and the ball radius at `params.γ` — so this and `packageAtProfile` are two statements about one
protocol at one set of numbers. Together with the two coupling lemmas above, that is the sense in
which correctness and soundness cannot disagree about `τ` here. -/
theorem quadEvalLink_perfectCompleteness_atProfile_packageParams
    [∀ i, SampleableType
      ((CoordinateWise.SingleRound.pSpec
          (CarrierCom 𝓜(hachiQ, hachiAlpha) dRows)
          (ShortChallenge 𝓜(hachiQ, hachiAlpha) hachiOmega) hachiR).Challenge i)]
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (pp : Hachi.PublicParamsD 𝓜(hachiQ, hachiAlpha) innerRows (2 ^ hachiM) hachiDelta outerRows
      (2 ^ hachiR) hachiDelta dRows) :
    (quadEvalReduction (oSpec := oSpec) (zDigits := hachiTau) (ω := hachiOmega)
        𝓜(hachiQ, hachiAlpha) pp
        (balancedZmodDigitDecomposition hachiB hachiDelta one_lt_hachiB q_le_sixteen_pow_delta)
        (boundedBalancedZmodDigitDecomposition hachiB hachiTau honestZBound one_lt_hachiB
          honestZBound_le_capacity)).perfectCompleteness init impl
      (relInMsgShort 𝓜(hachiQ, hachiAlpha) pp (hachiB : ZMod hachiQ) betaSq params.γ
        (2 * hachiOmega) (hachiB / 2))
      ((packageAtProfile (oSpec := oSpec) init impl pp).relOut) :=
  quadEvalReduction_perfectCompleteness 𝓜(hachiQ, hachiAlpha) init impl pp _ _
    (powTwoCyclotomic_hasMulLInftyBound hachiAlpha)
    (by norm_num [hachiDelta]) hachiTau_pos ringDim_pos params_hzb'
    (fun x e => le_trans
      (balancedZmodDigit_natAbs_le one_lt_hachiB q_le_sixteen_pow_delta hachiB_le_half x e)
      params.hbγ)
    (fun x e => le_trans
      (boundedBalancedZmodDigit_natAbs_le one_lt_hachiB hachiB_le_half x e) params.hbγ)

/-! ### The whole scheme at the profile -/

/-- The `R^lin` column count at the profile, written the way the chain writes it (digit counts as
`Nat.clog`), so that it unifies with the `μ₀` of `Correctness.lean` / `Concrete.lean`. -/
abbrev mu0Raw : ℕ :=
  rlinCols hachiN (Nat.clog params.b hachiQ) (Nat.clog params.b hachiQ) hachiTau hachiM hachiR

/-- `mu0Raw` is `mu0` — the same number, `57344`, once `⌈log₁₆ q⌉` is evaluated. -/
theorem mu0Raw_eq_mu0 : mu0Raw = mu0 := by rw [mu0, mu0Raw, params_b, clog_eq_delta]

/-- The lift key's column count at the profile: `μ₀ + n₀·δ_{bZero}`, the width a whole lifted
witness needs once the quotient block is committed as its base-`bZero` digits. -/
abbrev liftKeyWidth : ℕ :=
  mu0Raw + rlinRows hachiN hachiN hachiN * rhoDigitCount hachiQ params.bZero

/-- `μ₀ + n₀·δ = 57344 + 5·8 = 57384`. -/
theorem liftKeyWidth_eq : liftKeyWidth = 57384 := by
  rw [liftKeyWidth, mu0Raw_eq_mu0, mu0_eq, rhoDigitCount, params_bZero, clog_eq_delta]
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

/-! ### Why the *scheme*-level instantiation is not spelled out here

`hachiNonrecursiveConcrete_perfectCorrectness` is already parametric in `τ`/`zBound`, and every
profile-side hypothesis it needs is discharged above: `hcap` = `params_hcap`, `hzb` = `params_hzb`,
`hτ` = `hachiTau_pos`, `hclog` = `clog_pos`, `hd` = `ringDim_pos`, `hbZero` = `params_bZero_pos`,
`hZeroγ` = `params_hZeroγ`, and `hμn` = `sumcheckWidthAtProfile` at `M = 25`. Writing the
substituted instance out as a named `def`/`theorem` would therefore add no mathematical content —
and it does not elaborate: the composed scheme's *type* carries `Nat.clog params.b 4294967197`
(well-founded recursion on a 32-bit numeral) inside `Fin (2¹⁰)`-indexed matrices, a `μ₀ = 57344`
column count and a 26-deep nested `ProtocolSpec` append tower, and instance search for
`SampleableType (Simple.PublicParams … (2¹⁰ · Nat.clog params.b q))` re-triggers `isDefEq` over all
of it. The result is an `isDefEq` heartbeat timeout, and an out-of-memory kill once the terms are
made to unify more eagerly. That is an elaborator cost, not a gap in the argument.

The `τ` agreement between the two security directions is instead pinned one layer down, at
`QuadEval` — which is where `τ` actually enters both — by `packageAtProfile`,
`packageAtProfile_relOut` and `relInMsgShort_atProfile_subset_packageAtProfile_relIn` above. -/

end Instantiated

end ArkLib.Lattices.Ajtai.InnerOuter.HachiParams
