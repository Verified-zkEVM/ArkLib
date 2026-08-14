# MCA formalization dedup — historical design record

**Status: LANDED.** PR #692 unified the generator and module-alphabet MCA layers; PR #741 moved
the ABF26 API onto that canonical definition. Sections 1–5 below preserve the reasoning that led
to the design. They describe the tree *before* those PRs and are not current implementation
instructions.

The current architecture has one MCA event and one numeric value:

- `CoreDefinitions.IsMCA` is generator-parametric and accepts `ModuleCode ι F A` for an arbitrary
  `F`-module alphabet `A`.
- `CoreDefinitions.mcaError G C : ℝ → ENNReal` is the primitive worst-case value, and
  `IsMCAGenerator` is definitionally its pointwise bound on radii in `I`.
- `ProximityGap.epsMca` is only transparent notation for
  `mcaError (AffineLineGenerator F) C`; there is no separate `mcaEvent`/`epsMCA` definition.
- `Errors.lean` supplies affine-line comparisons, while `MCAGenerator.lean` and
  `TensorGenerator.lean` supply generator transport. The Grand Challenges API consumes
  `mcaError` directly.

For the maintained API, use
[`proximity-error-conventions.md`](../../wiki/proximity-error-conventions.md). The execution
history and source-fidelity decisions remain in
[`mca-unification-bootstrap.md`](mca-unification-bootstrap.md).

---

## 1. Historical situation — two MCA formalizations, no bridge

Before #692 and #741, ArkLib had two formalizations of "mutual correlated agreement," from two
papers, that overlapped but neither generalized the other:

- **`epsMCA` / `mcaEvent`** — ABF26 Def 4.3. `ArkLib/Data/CodingTheory/ProximityGap/Errors.lean`
  (`mcaEvent` ~L233, `epsMCA` ~L251). Numeric `ENNReal`-valued worst-case error; line family
  (`Fin 2`, `u₀ + γ·u₁`); alphabet is an arbitrary `F`-module `A`; `δ : ℝ≥0`.
  `epsMCA C δ := ⨆ u : WordStack A (Fin 2) ι, Pr_{γ ← $ᵖ F}[mcaEvent C δ (u 0) (u 1) γ]`.
- **`IsMCA` / `IsMCAGenerator`** — BCGM25 Def 3.14.
  `ArkLib/Data/CodingTheory/ProximityGap/ProximityGenerators.lean` (`IsMCA` L88,
  `IsMCAGenerator` L98). `Prop`-valued predicate; arbitrary generator `G : S → Fˡ`;
  alphabet `F` only; `γ : I` (unitInterval); error function `ε_mca : I → I`.
  `IsMCAGenerator G ε LC := ∀ U γ, Pr_{x ← $ᵖ S}[IsMCA G LC x U γ] ≤ ENNReal.ofReal (ε γ)`.
  Preservation lemmas in `MCAGenerator.lean` (`pseudoinverseGen` L59,
  `isMCA_projectedGenerator_of_isMCA` L89, `generatorSubset` L110) — BCGM25 Lem 4.1/4.2.

There was **no bridging lemma**. The design policy was already that the generator framework should
be canonical and that ArkLib should not grow a parallel polynomial-generator notion.
(Supporting defs: `projectedWord`/`projectedCode` `LinearCode.lean` L260/L267;
`pairJointAgreesOn` `Errors.lean` ~L192.)

## 2. Historical overlap — verified clause by clause

The pre-unification overlap was a single point in a two-axis space: alphabet `A = F`, code
`C = ↑LC` linear,
generator `G = lineGenerator` (`ℓ = Fin 2`, `G(x) = (1,x)` so `vecMul (G x) U = U 0 + x·U 1`),
sample `x = γ ← F`, `δ ↔ γ` across `ℝ≥0 ↔ I`. There `mcaEvent` and `IsMCA lineGen` are the
**same event**:

| clause | mcaEvent | IsMCA lineGen | match |
|---|---|---|---|
| combination | `u₀ + γ·u₁` | `vecMul (1,γ) U = U 0 + γ·U 1` | ✓ (`U = (u₀,u₁)`) |
| closeness | `∃ w∈C, ∀i∈S, w i = line i` | `line\|[T] ∈ (↑LC)\|[T]` (`= ∃ c∈↑LC, ∀i∈T, c i = line i`) | ✓ |
| non-agreement | `¬ pairJointAgreesOn C S u₀ u₁` | `∃ j, (U j)\|[T] ∉ (↑LC)\|[T]` | ✓ — `pairJointAgreesOn` factors (pair independent) into "`u₀` close ∧ `u₁` close", so its negation = "some `Uⱼ` not close" |
| size | `(S.card:ℝ≥0) ≥ (1−δ)·n` | `(T.card:ℝ) ≥ n·(1−γ)` | ✓ mod `ℝ≥0↔ℝ`, `mul_comm`, `δ↔γ` on `[0,1]` |

Hence the then-targeted equalities were:
- **value:** `epsMCA (↑LC) δ = ⨆_{U : Fin 2 → (ι→F)} Pr_{x←F}[IsMCA lineGen (↑LC) x U δ]`;
- **predicate:** `IsMCAGenerator lineGen ε (↑LC) ⟺ ∀ δ, epsMCA (↑LC) δ ≤ ε δ`.

## 3. Why the old definitions did not subsume each other

1. **`epsMCA` only — general `F`-module alphabet `A ≠ F`.** Used by `ConstrainedCode`.
   The source-audited `linear_mcaError_le_onePointFiveJohnson` is no longer an example:
   it now uses the cited theorem's field alphabet. `IsMCA` is `F`-valued (`vecMul`,
   `LinearCode ι F`) → cannot express general module alphabets.
   *Essential, not mechanical.*
2. **`IsMCA` only — general generator `G ≠ line`** (any `ℓ`, polynomial/tensor/MDS generators —
   the BCGM25 preservation theory). `epsMCA` is frozen at the `Fin 2` line → cannot express it.
3. **Representational.** `epsMCA` = `ENNReal` value; `IsMCAGenerator` = `Prop` bound
   (`value ≤ ε`). The generator framework has *no value form* yet. *(Minor/mechanical: `IsMCA`
   uses `LinearCode` but only `↑LC : Set`; `γ : I` vs `δ : ℝ≥0`.)*

**Historical two-axis map:** overlap was `(alphabet = F) × (generator = line)`. `epsMCA`
extended the *alphabet* axis; `IsMCA` extended the *generator* axis; neither contained the other.

## 4. Historical options — Option B landed

Do not execute either option below. They are retained to explain why the unified representation
was selected; the current declarations are summarized at the top of this page.

### Option A — Bridge (not chosen)

A proposed `ProximityGap/MCABridge.lean` would have imported `Errors` and
`ProximityGenerators` while touching neither. Its proposed helpers had verified clean
characterizations:

1. `def lineGenerator (γ : F) : Generator F (Fin 2) F := ![1, γ]` (not in tree yet).
2. `vecMul (lineGenerator γ) U = U 0 + γ • U 1` (`Matrix.vecMul` + `Fin.sum_univ_two`).
3. `v\|[T] ∈ C\|[T] ↔ ∃ c ∈ C, ∀ i ∈ T, c i = v i` (from `projectedCode` def; restriction-eq is
   pointwise-on-`T`).
4. `(∃ j, (U j)\|[T] ∉ C\|[T]) ↔ ¬ pairJointAgreesOn C T (U 0) (U 1)` (pairJointAgreesOn factors).
5. size-clause reconciliation `I ↔ ℝ≥0` (fiddly but mechanical; `δ ↔ γ` on `[0,1]`).
6. assemble → event iff → `iSup_congr`/`propext` → the value equality in §2.
This would have made "`epsMCA` is the special case of `IsMCA` at `(F, line)`" a theorem while
retaining two definitions.

### Option B — Unify (landed in #692 and #741)

The selected design generalized `IsMCA` to module alphabets, added the generator-parametric
`mcaError`, defined `IsMCAGenerator` as its bound, and made `epsMca` the affine-line abbreviation.
The radius of `IsMCA` and `mcaError` is now `ℝ`; the paper-facing bound still quantifies over `I`.
This removes the duplicate event and makes the former bridge definitional.

## 5. Historical PR #618 reconciliation

At planning time, PR #618 (`Katy/challenge`) defined a **third** `ε_mca` on
`IsMCA`/`lineGenerator` —
`ArkLib/Data/CodingTheory/ProximityPrize.lean`. It duplicated the ABF26 challenge quantity then
expressed by `grandMCAChallenge` on `epsMCA`. The landing requirement was to reconcile it onto a
canonical value rather than retain a third definition; the `mcaError`/`epsMca` architecture above
is that resolution.

## 6. Historical follow-up ledger

This 2026-07-09 audit ledger is retained for provenance, not as current API guidance. Check the
tree and the conventions page before acting on an item.

- **A1** `epsMCA_eq_of_floor_eq` (`GrandChallenges.lean` ~L113) is over-specialized to `A := F`
  and mislocated → generalize over `A`, move beside `epsMCA_mono` in `Errors.lean`.
- **A2** No `Lambda_eq_of_floor_eq` (`ListDecodability.lean`, only `Lambda_mono`) → add it, then
  port `le_of_lt_next` / `sublevel_iff` / `kStar_unique` / `paper_criterion` to
  `GrandListResolution` (list side is asymmetric with MCA side).
- **C1** `epsCA_le_epsMCA` (`Errors.lean` ~L404) requires `Submodule` but proof uses only set
  membership → relax to `C : Set`; ripples to `MCAUpperWitness.ofEpsCAGt`.
- **C2** `epsCA_eq_of_floor_eq` only covers `δ_int`; docstring claims both → add `δ_fld` companion.
- **C3** drop admittedly-unneeded hyps in the former catalogue drafts; current semantic APIs are
  `linear_epsCa_le_onePointFiveJohnson` and `rs_epsCa_le_of_no_radius_level_crossing`.
- **B2-cheap** rename `IsMCA`'s `γ : I → δ` (collides with `mcaEvent`'s random scalar `γ : F`).
- fragility (defensive, if touching): `poly_gen_is_zero_evading`, `minSeedCard_le`,
  `isMCA_projectedGenerator_of_isMCA`, `rs_epsCa_le_of_no_radius_level_crossing`;
  `Basic.lean` var shadowing.

At the time of the audit, every `sorry` in the files under discussion was a labeled external
admit rather than an in-tree proof gap.

## 7. Historical cross-references

Memory: `delta-grid-quantization.md`. Branch `feat/abf26-plan` (#505). BCGM25 = eprint 2025/2051.
`CapacityBounds.lean` ~L644 policy note. (Line numbers approximate — anchor on decl names.)
