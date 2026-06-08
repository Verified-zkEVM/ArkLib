import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeRadiusOneExact
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeResolutionWitness
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeCollapse
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeListClosedForm
import ArkLib.Data.CodingTheory.ProximityGap.GrandChallengeDecision
import Mathlib.NumberTheory.LucasLehmer

/-!
# The §1 Grand Challenge prize resolution: a single judge-facing file (issue #120)

This file assembles the formal resolution of the ABF26 §1 Grand-Challenge **predicates as
formalized in this repository** into one apex deliverable, and exhibits a concrete instance
that discharges every numeric hypothesis with no remaining `sorry`/`admit`/`native_decide`.

**Scope honesty (Finding F6):** the formal `mcaPrize` / `grandMCAChallenge` predicates here
collapse to radius-one counting (`GrandChallengeCollapse.lean`). Proving them is **not**
the same as resolving the external million-dollar MCA conjecture from the paper's `\ignore{}`
block (`mcaConjecture`). This file proves the **in-repo formal prize**, not open research math.

**Axiom honesty:** the pinned apex theorems in this file depend only on
`{propext, Classical.choice, Quot.sound}` when checked in isolation. Downstream capacity
routes may consume allowlisted paper axioms via `CapacityBoundsProofs` (`*_from_paper_axiom`);
those are separate from this file's `#print axioms` block.

## Deliverables

* `prizeResolution_mca_of_numeric` — the cleanest single packaging theorem: for any
  `(ι, F, domain)` satisfying the four explicit numeric inequalities per prize rate, the formal
  MCA prize **holds** *and* every prize-rate Grand MCA Challenge carries a full
  `GrandMCAResolution` witness (with maximal threshold `δ* = 1`).
* `prizeResolution_mca_M521` — **THE CONCRETE INSTANCE.** Taking `ι := Fin 16` (so the four
  prize-rate degrees are `⌊16·2^{-(j+1)}⌋ = 8, 4, 2, 1`) and `F := ZMod (2^521 − 1)` (the
  Mersenne prime `M₅₂₁`, certified in-kernel via the Lucas–Lehmer test), all numeric
  hypotheses are discharged and the formal MCA prize holds with explicit `δ*=1` witnesses. The
  worst binomial is `C(16,9) = 11440`; the field size `M₅₂₁ > 2^142 > 11440·2^128` clears both
  the exact-value separation `C(C(16,9),2) < q` and the budget `C(16,9)/q ≤ 2^{−128}`.
* `prizeResolution_ld` — the list-side resolution: for every domain with `2 ≤ n` and every
  `m ≥ 1`, the formal list-decoding prize is **false** (`not_listDecodingPrize`), the closed
  form `q^{k·m} ≤ ε*·q` explains why, and **no** `GrandListResolution` exists at the prize
  parameters (`isEmpty_grandListResolution_prize`).

## Anti-vacuity audit (per issue #121)

* `prizeResolution_mca_of_numeric`: its four numeric hypotheses are **non-vacuous** — the
  concrete instance `prizeResolution_mca_M521` is a literal witness that they are
  simultaneously satisfiable.
* `prizeResolution_mca_M521`: vacuity is impossible — it is a closed theorem with no
  hypotheses, asserting an unconditional `mcaPrize`.
* `prizeResolution_ld` / `isEmpty_grandListResolution_prize`: vacuity is impossible — these are
  *negations* (`¬ prize`, `IsEmpty`), so they carry no dischargeable hypotheses that could be
  silently false; the `2 ≤ n`, `1 ≤ m` side-conditions are exactly the regime where the prize
  rates are well-defined.

## References

- [ABF26] Arnon, Boneh, Fenzi. *Open Problems in List Decoding and Correlated Agreement*.
-/

set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.unusedSectionVars false
set_option maxRecDepth 8192

open scoped NNReal ENNReal

namespace ProximityGap

open NNReal Code Polynomial ReedSolomon GrandChallenges

/-! ## 1. The packaging theorem (positive MCA deliverable) -/

/-- **Packaged MCA prize resolution from the four numeric inequalities.**

For any evaluation domain `domain : ι ↪ F`, suppose at every prize rate
`ρⱼ ∈ {1/2, 1/4, 1/8, 1/16}` (degree `kⱼ := ⌊ρⱼ·n⌋`):

* `hk j` : `kⱼ + 1 ≤ n` (so the exact radius-one value applies);
* `hq j` : `C(C(n, kⱼ+1), 2) < |F|` (the large-field separation of
  `epsMCA_one_eq_choose_div`);
* `hbound j` : `C(n, kⱼ+1) / |F| ≤ ε* = 2^{−128}` (the §1 budget).

Then the formal MCA prize **holds**, and moreover *every* prize-rate Grand MCA Challenge
carries the full witness data the §1 challenge asks for: a `GrandMCAResolution` with maximal
threshold `δ* = 1`.  This is the single cleanest deliverable bundling the decision
(`mcaPrize_of_large_field`) with the witnesses (`mcaPrize_resolutions_of_large_field`). -/
theorem prizeResolution_mca_of_numeric
    {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
    {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (domain : ι ↪ F)
    (hk : ∀ j : Fin 4,
      ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1 ≤ Fintype.card ι)
    (hq : ∀ j : Fin 4,
      (Nat.choose (Fintype.card ι) (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1)).choose 2
        < Fintype.card F)
    (hbound : ∀ j : Fin 4,
      (Nat.choose (Fintype.card ι) (⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ + 1) : ENNReal)
        / (Fintype.card F : ENNReal) ≤ (epsStar : ENNReal)) :
    GrandChallenges.mcaPrize domain ∧
      ∀ j : Fin 4,
        Nonempty (GrandMCAResolution
          (ReedSolomon.code domain ⌊prizeRates j * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
          epsStar) :=
  ⟨mcaPrize_of_large_field domain hbound,
   fun j => ⟨mcaPrize_resolutions_of_large_field domain hk hq hbound j⟩⟩

/-! ## 2. The concrete instance: `ι = Fin 16`, `F = ZMod (2^521 − 1)` -/

section Concrete

/-- The Mersenne prime `M₅₂₁ = 2^521 − 1`, certified by the in-kernel Lucas–Lehmer test
(`decide`-based kernel reduction, **not** `native_decide`). -/
theorem mersenne521_prime : (mersenne 521).Prime :=
  lucas_lehmer_sufficiency _ (by simp) (by norm_num)

noncomputable instance : Fact (mersenne 521).Prime := ⟨mersenne521_prime⟩

/-- The prize field `𝔽 := ZMod M₅₂₁`, a field of `2^521 − 1` elements. -/
abbrev PrizeField : Type := ZMod (mersenne 521)

theorem card_prizeField : Fintype.card PrizeField = mersenne 521 := ZMod.card _

theorem sixteen_le_mersenne521 : (16 : ℕ) ≤ mersenne 521 := by
  unfold mersenne
  have h : (2 : ℕ) ^ 5 ≤ 2 ^ 521 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  omega

/-- The evaluation domain `Fin 16 ↪ ZMod M₅₂₁`, `i ↦ (i : ZMod M₅₂₁)`; injective since the
sixteen indices are `< 16 ≤ M₅₂₁`. -/
noncomputable def prizeDomain : Fin 16 ↪ PrizeField where
  toFun i := (i.val : PrizeField)
  inj' := by
    intro a b hab
    simp only at hab
    have hlt_a : a.val < mersenne 521 := lt_of_lt_of_le a.isLt sixteen_le_mersenne521
    have hlt_b : b.val < mersenne 521 := lt_of_lt_of_le b.isLt sixteen_le_mersenne521
    have hval : a.val = b.val := by
      have ha := ZMod.val_natCast_of_lt hlt_a
      have hb := ZMod.val_natCast_of_lt hlt_b
      rw [← ha, ← hb, hab]
    exact Fin.ext hval

/-! ### Numeric discharge for `n = 16`, `q = M₅₂₁`. -/

theorem card_fin16 : Fintype.card (Fin 16) = 16 := by simp

/-- `2^142 ≤ M₅₂₁`. -/
theorem pow142_le_mersenne521 : (2 : ℕ) ^ 142 ≤ mersenne 521 := by
  unfold mersenne
  have h : (2 : ℕ) ^ 143 ≤ 2 ^ 521 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
  have h2 : (2 : ℕ) ^ 142 * 2 = 2 ^ 143 := by ring
  omega

/-- At `n = 16`, every prize-rate degree `kⱼ` satisfies `kⱼ + 1 ≤ 16`
(`kⱼ + 1 ∈ {9, 5, 3, 2}`). -/
theorem prizeFloor_fin16_add_one_le (j : Fin 4) :
    ⌊prizeRates j * ((16 : ℕ) : ℝ≥0)⌋₊ + 1 ≤ 16 := by
  fin_cases j <;>
  · set k := ⌊prizeRates _ * ((16 : ℕ) : ℝ≥0)⌋₊ with hk
    clear_value k
    norm_num [prizeRates] at hk
    omega

/-- The prize binomial `C(16, kⱼ+1)` at any rate is at most `C(16,9) = 11440 < 2^14`. -/
theorem prizeChoose_fin16_le (j : Fin 4) :
    Nat.choose 16 (⌊prizeRates j * ((16 : ℕ) : ℝ≥0)⌋₊ + 1) ≤ 11440 := by
  fin_cases j <;>
  · set k := ⌊prizeRates _ * ((16 : ℕ) : ℝ≥0)⌋₊ with hk
    clear_value k
    norm_num [prizeRates] at hk
    rw [hk]; decide

/-- The exact-value separation hypothesis `C(C(16, kⱼ+1), 2) < q` at every prize rate. -/
theorem prizeChoose2_lt_mersenne521 (j : Fin 4) :
    (Nat.choose 16 (⌊prizeRates j * ((16 : ℕ) : ℝ≥0)⌋₊ + 1)).choose 2 < mersenne 521 := by
  have hle : Nat.choose 16 (⌊prizeRates j * ((16 : ℕ) : ℝ≥0)⌋₊ + 1) ≤ 11440 :=
    prizeChoose_fin16_le j
  calc (Nat.choose 16 (⌊prizeRates j * ((16 : ℕ) : ℝ≥0)⌋₊ + 1)).choose 2
      ≤ (Nat.choose 16 (⌊prizeRates j * ((16 : ℕ) : ℝ≥0)⌋₊ + 1)) ^ 2 :=
        Nat.choose_le_pow _ 2
    _ ≤ 11440 ^ 2 := by gcongr
    _ < 2 ^ 142 := by norm_num
    _ ≤ mersenne 521 := pow142_le_mersenne521

/-- The §1 budget `C(16, kⱼ+1) · 2^128 ≤ q` at every prize rate. -/
theorem prizeChoose_mul_le_mersenne521 (j : Fin 4) :
    Nat.choose 16 (⌊prizeRates j * ((16 : ℕ) : ℝ≥0)⌋₊ + 1) * 2 ^ 128 ≤ mersenne 521 := by
  calc Nat.choose 16 (⌊prizeRates j * ((16 : ℕ) : ℝ≥0)⌋₊ + 1) * 2 ^ 128
      ≤ 11440 * 2 ^ 128 := by gcongr; exact prizeChoose_fin16_le j
    _ ≤ 2 ^ 14 * 2 ^ 128 := by gcongr; norm_num
    _ = 2 ^ 142 := by ring
    _ ≤ mersenne 521 := pow142_le_mersenne521

/-! ### The generic ENNReal budget bridge. -/

/-- `(epsStar : ENNReal) = 1 / 2^128`. -/
theorem epsStar_enn : (epsStar : ENNReal) = (1 : ENNReal) / (2 : ENNReal) ^ (128 : ℕ) := by
  unfold epsStar
  rw [ENNReal.coe_div (by positivity)]
  push_cast
  ring

/-- The §1 budget in `ENNReal`: `c/q ≤ ε* = 1/2^128` whenever `c·2^128 ≤ q`. -/
theorem choose_div_le_epsStar_of_le {c q : ℕ} (h : c * 2 ^ 128 ≤ q) :
    (c : ENNReal) / (q : ENNReal) ≤ (epsStar : ENNReal) := by
  rw [epsStar_enn]
  refine ENNReal.div_le_of_le_mul ?_
  rw [one_div, ← ENNReal.div_eq_inv_mul]
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by positivity)) (Or.inl (by simp))]
  calc (c : ENNReal) * (2 : ENNReal) ^ (128 : ℕ)
      = ((c * 2 ^ 128 : ℕ) : ENNReal) := by push_cast; ring
    _ ≤ (q : ENNReal) := by exact_mod_cast h

/-! ### THE CONCRETE INSTANCE. -/

/-- **THE CONCRETE PRIZE INSTANCE (unconditional).**

For `ι := Fin 16` and `F := ZMod (2^521 − 1)` with the natural evaluation domain `prizeDomain`,
the formal §1 MCA prize **holds**, and every prize-rate Grand MCA Challenge carries a full
`GrandMCAResolution` witness with maximal threshold `δ* = 1`.

This is the genuinely new content: a *closed* theorem (no hypotheses) instantiating
`prizeResolution_mca_of_numeric`. All numeric inputs are discharged in-kernel:
* the prime `2^521 − 1` via Lucas–Lehmer (`mersenne521_prime`);
* the field card `|F| = 2^521 − 1` (`card_prizeField`);
* the degrees `kⱼ = 8,4,2,1` and binomials `C(16,kⱼ+1) ≤ C(16,9) = 11440`
  (`prizeChoose_fin16_le`);
* the separation `C(C(16,kⱼ+1),2) < q` and budget `C(16,kⱼ+1)·2^128 ≤ q` from `q > 2^142`. -/
theorem prizeResolution_mca_M521 :
    GrandChallenges.mcaPrize prizeDomain ∧
      ∀ j : Fin 4,
        Nonempty (GrandMCAResolution
          (ReedSolomon.code prizeDomain
            ⌊prizeRates j * (Fintype.card (Fin 16) : ℝ≥0)⌋₊ : Set (Fin 16 → PrizeField))
          epsStar) := by
  have hcardι : Fintype.card (Fin 16) = 16 := card_fin16
  have hcardF : Fintype.card PrizeField = mersenne 521 := card_prizeField
  refine prizeResolution_mca_of_numeric prizeDomain ?_ ?_ ?_
  · -- hk : kⱼ + 1 ≤ n
    intro j
    rw [hcardι]
    exact prizeFloor_fin16_add_one_le j
  · -- hq : C(C(n, kⱼ+1), 2) < q
    intro j
    rw [hcardι, hcardF]
    exact prizeChoose2_lt_mersenne521 j
  · -- hbound : C(n, kⱼ+1)/q ≤ ε*
    intro j
    rw [hcardι, hcardF]
    exact choose_div_le_epsStar_of_le (prizeChoose_mul_le_mersenne521 j)

end Concrete

/-! ## 3. The list-side resolution (negative deliverable) -/

section ListSide

variable {ι : Type} [Fintype ι] [Nonempty ι] [DecidableEq ι]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **No `GrandListResolution` exists at the prize parameters.**

At any prize rate `ρ = 1/2` (degree `k = ⌊n/2⌋ ≥ 1`), positive interleaving `m ≥ 1`, threshold
`ε* = 2^{−128} < 1` and `2 ≤ n`, the type `GrandListResolution (RS[F,domain,k]^⋈m) m ε*` is
**empty**: any inhabitant would, via `grandListDecodingChallenge_of_resolution`, prove the
Grand List Decoding Challenge, which `not_grandListDecodingChallengeRS_of_pos` refutes (the
radius-one collapse makes the list the whole interleaved code, of size `> ε*·|F|`). -/
theorem isEmpty_grandListResolution_prize (domain : ι ↪ F) {m : ℕ} (hm : 0 < m)
    (hι : 2 ≤ Fintype.card ι) :
    IsEmpty (GrandListResolution
      (ReedSolomon.code domain ⌊prizeRates 0 * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
      m epsStar) := by
  constructor
  intro R
  -- k = ⌊n/2⌋ ≥ 1
  have hrate : prizeRates 0 = 1 / 2 := by unfold prizeRates; norm_num
  set k := ⌊prizeRates 0 * (Fintype.card ι : ℝ≥0)⌋₊ with hk_def
  have hk : 0 < k := by
    rw [hk_def, hrate]
    refine lt_of_lt_of_le Nat.zero_lt_one (Nat.le_floor ?_)
    rw [Nat.cast_one]
    calc (1 : ℝ≥0) = (1 / 2) * 2 := by norm_num
      _ ≤ (1 / 2) * (Fintype.card ι : ℝ≥0) := by gcongr; exact_mod_cast hι
  have hε : epsStar < 1 := by
    unfold epsStar
    rw [div_lt_one (by positivity)]
    exact one_lt_pow₀ one_lt_two (by norm_num)
  -- a resolution proves the challenge, which is refuted
  exact not_grandListDecodingChallengeRS_of_pos domain hk hm hε
    (grandListDecodingChallenge_of_resolution R)

/-- **The list-side prize resolution.**

For every evaluation domain with `2 ≤ n` and every interleaving `m ≥ 1`:

1. the formal §1 list-decoding prize predicate is **false** (`not_listDecodingPrize`);
2. for `k ≤ n` the underlying challenge has the **closed form**
   `q^{k·m} ≤ ε*·q` (`grandListDecodingChallengeRS_iff_pow_le`), which is the precise reason
   the prize fails (LHS `≥ q²`, RHS `< q`);
3. **no** `GrandListResolution` exists at the prize parameters
   (`isEmpty_grandListResolution_prize`).

Vacuity is impossible: this is a conjunction of negations and an `IsEmpty`. -/
theorem prizeResolution_ld (domain : ι ↪ F) {m : ℕ} (hm : 0 < m)
    (hι : 2 ≤ Fintype.card ι) :
    ¬ GrandChallenges.listDecodingPrize domain m ∧
      (∀ k : ℕ, k ≤ Fintype.card ι →
        (GrandChallenges.grandListDecodingChallengeRS domain k m epsStar ↔
          ((Fintype.card F : ENNReal) ^ (k * m)) ≤
            ((epsStar : ENNReal) * (Fintype.card F : ENNReal)))) ∧
      IsEmpty (GrandListResolution
        (ReedSolomon.code domain ⌊prizeRates 0 * (Fintype.card ι : ℝ≥0)⌋₊ : Set (ι → F))
        m epsStar) :=
  ⟨not_listDecodingPrize domain hm hι,
   fun _k hk => grandListDecodingChallengeRS_iff_pow_le domain hk m epsStar,
   isEmpty_grandListResolution_prize domain hm hι⟩

end ListSide

end ProximityGap

/-! ## Standing apex audit (Issue #121 recommendation — build-confirmed 2026-06-07)

`#print axioms` regression guard for the apex prize theorems, plus the permanent non-vacuity
record. Verified via `lake env lean` against the built oleans: each apex theorem depends on exactly
`[propext, Classical.choice, Quot.sound]` — no `sorryAx`, no `native_decide` (`Lean.ofReduceBool`
is absent, so the Mersenne-521 Lucas–Lehmer primality is genuinely in-kernel `decide`), no custom
axiom.

**NON-VACUITY RECORD (the F4/F6 distinction — do not misread as a genuine-threshold result):**

* `prizeResolution_ld` (list side) is a *negative* deliverable —
  `¬ listDecodingPrize ∧ … ∧ IsEmpty (GrandListResolution …)`. A conjunction of negations and an
  `IsEmpty` cannot be vacuously inflated. Genuinely non-vacuous.

* `prizeResolution_mca_M521` (MCA side) is honest and kernel-clean, but the `GrandMCAResolution`
  it produces sets `δStar := 1`, so the structure's `maximal` clause
  (`∀ δ, δStar < δ → δ ≤ 1 → ε_mca > ε*`) is **vacuously true** (`1 < δ ≤ 1` is empty). The only
  genuine content is the radius-one bound `ε_mca(C, 1) = C(n, k+1)/|F| ≤ ε*`. This resolves the
  *formal/collapsed* Grand-MCA encoding (the documented F6 collapse, `GrandChallengeCollapse.lean`),
  NOT the genuine ABF26 MCA decoding threshold (the actual prize question). -/
#print axioms ProximityGap.prizeResolution_mca_M521
#print axioms ProximityGap.prizeResolution_ld
#print axioms ProximityGap.mersenne521_prime
