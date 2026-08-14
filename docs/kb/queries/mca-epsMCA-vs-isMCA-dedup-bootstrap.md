# MCA formalization dedup: `epsMCA` (ABF26) vs `IsMCA` (BCGM25)

**Status: SUPERSEDED for execution (2026-08-03) — analysis still current.**
The trigger fired: Katy's generator framework landed on `main` via **#596** (2026-08-03).
**Option B (§4) is now ACTIVE** and is being executed on branch `feat/mca-unification`; see
[`mca-unification-bootstrap.md`](mca-unification-bootstrap.md) for the step plan.

Two things changed since this doc was written:
- **Option B is no longer optional.** It is the only *faithful* fix for BCGM25 Lemma 4.4's tight
  `ε + ε′`, which PR #610's Theorems 8.2/9.2 depend on and which is currently an unjustified
  `sorry`. The paper's proof needs MCA for the ℓ-fold interleaving `C^ℓ`, and ArkLib's `IsMCA`
  cannot express it. (BCGM25 Def 3.2/3.3 + Remark 3.4 confirm Σ is a general F-vector space, so
  this is an ArkLib limitation, not a paper gap.)
- **#505 no longer gates it.** The unification lands on `main`'s side; #505 bridges afterwards
  (§4 Option B's `epsMCA := mcaError lineGenerator …`).

§2's clause-by-clause coincidence has since been **compiled** (`scratchpad/unify.lean`), not just
argued. §1, §3, §5–§7 below remain the reference; do not re-derive them.

Also still to fold in: PR #618 (see §5).

---

## 1. The situation — two MCA formalizations, no bridge

ArkLib has two formalizations of "mutual correlated agreement," from two papers, that
overlap but neither generalizes the other:

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

There is **no bridging lemma**. Existing policy note: `CapacityBounds.lean` ~L644–650 says the
generator framework is canonical and "do not grow a parallel polynomial-generator notion."
(Supporting defs: `projectedWord`/`projectedCode` `LinearCode.lean` L260/L267;
`pairJointAgreesOn` `Errors.lean` ~L192.)

## 2. Where they coincide — verified clause by clause

**Overlap = a single point in a 2-axis space**: alphabet `A = F`, code `C = ↑LC` linear,
generator `G = lineGenerator` (`ℓ = Fin 2`, `G(x) = (1,x)` so `vecMul (G x) U = U 0 + x·U 1`),
sample `x = γ ← F`, `δ ↔ γ` across `ℝ≥0 ↔ I`. There `mcaEvent` and `IsMCA lineGen` are the
**same event**:

| clause | mcaEvent | IsMCA lineGen | match |
|---|---|---|---|
| combination | `u₀ + γ·u₁` | `vecMul (1,γ) U = U 0 + γ·U 1` | ✓ (`U = (u₀,u₁)`) |
| closeness | `∃ w∈C, ∀i∈S, w i = line i` | `line\|[T] ∈ (↑LC)\|[T]` (`= ∃ c∈↑LC, ∀i∈T, c i = line i`) | ✓ |
| non-agreement | `¬ pairJointAgreesOn C S u₀ u₁` | `∃ j, (U j)\|[T] ∉ (↑LC)\|[T]` | ✓ — `pairJointAgreesOn` factors (pair independent) into "`u₀` close ∧ `u₁` close", so its negation = "some `Uⱼ` not close" |
| size | `(S.card:ℝ≥0) ≥ (1−δ)·n` | `(T.card:ℝ) ≥ n·(1−γ)` | ✓ mod `ℝ≥0↔ℝ`, `mul_comm`, `δ↔γ` on `[0,1]` |

Hence the target equalities:
- **value:** `epsMCA (↑LC) δ = ⨆_{U : Fin 2 → (ι→F)} Pr_{x←F}[IsMCA lineGen (↑LC) x U δ]`;
- **predicate:** `IsMCAGenerator lineGen ε (↑LC) ⟺ ∀ δ, epsMCA (↑LC) δ ≤ ε δ`.

## 3. Where they do NOT coincide (three disjoint regions)

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

**2-axis map:** overlap is `(alphabet = F) × (generator = line)`. `epsMCA` extends the
*alphabet* axis; `IsMCA` extends the *generator* axis; neither contains the other.

## 4. Two options

### Option A — Bridge (low-risk, additive; the near-term move)
New file `ProximityGap/MCABridge.lean` (imports `Errors` + `ProximityGenerators`; touches
neither). Helper lemmas, all with verified clean characterizations:
1. `def lineGenerator (γ : F) : Generator F (Fin 2) F := ![1, γ]` (not in tree yet).
2. `vecMul (lineGenerator γ) U = U 0 + γ • U 1` (`Matrix.vecMul` + `Fin.sum_univ_two`).
3. `v\|[T] ∈ C\|[T] ↔ ∃ c ∈ C, ∀ i ∈ T, c i = v i` (from `projectedCode` def; restriction-eq is
   pointwise-on-`T`).
4. `(∃ j, (U j)\|[T] ∉ C\|[T]) ↔ ¬ pairJointAgreesOn C T (U 0) (U 1)` (pairJointAgreesOn factors).
5. size-clause reconciliation `I ↔ ℝ≥0` (fiddly but mechanical; `δ ↔ γ` on `[0,1]`).
6. assemble → event iff → `iSup_congr`/`propext` → the value equality in §2.
Result: "epsMCA is the special case of IsMCA at (F, line)" becomes a **theorem**; kills drift;
canonical target for #618. Does **not** foreclose Option B (it's a prerequisite/safety-net).

### Option B — Unify (the principled endpoint; a real project)
One minimal general def, general on **both** axes:
`mcaError {A : F-module} (G : Generator S ℓ F) (C : Set (ι → A)) (δ : ℝ≥0) : ENNReal
   := ⨆ U, Pr_{x←S}[IsMCA' G C x U δ]`, with `epsMCA := mcaError lineGenerator …` and
`IsMCAGenerator` the `bounded-by` predicate over it. Cost, in order of difficulty:
- **(real) generalize BCGM25 `IsMCA` alphabet `F → F`-module `A`** — `vecMul` → module
  linear-combination, `projectedCode` over `Set (ι → A)`. Extends #489's framework.
- **(new) add the `ENNReal` value form** (`IsMCAGenerator` is only a predicate today).
- **(mechanical) retype `γ : I → ℝ≥0`** — verified cheap: in `IsMCA`, `γ` is an opaque scalar
  in the real inequality `n·(1−γ)`; the three preservation lemmas carry it through untouched
  (`intro U γ` … pass along), so ~5-site swap, no I-lattice structure used.
- re-derive `epsMCA`'s numeric API on the new base; update ~15 call sites; **coordinate with
  #489 owners** (their file).

**Recommendation:** A now (once PRs land) → derisks + proves coincidence; B as a scoped,
coordinated follow-up if the team wants true minimality. Redefinition in B makes A's lemma
`rfl`, so if B is committed-to, A's standalone lemma can be skipped.

## 5. PR #618 reconciliation
PR #618 (`Katy/challenge`) defines a **third** `ε_mca` on `IsMCA`/`lineGenerator` —
`ArkLib/Data/CodingTheory/ProximityPrize.lean`. It duplicates the ABF26 challenge quantity
that `grandMCAChallenge` (on `epsMCA`) already expresses. Reconcile onto the canonical form
(A's `epsMCA`, or B's `mcaError`) rather than landing a parallel error.

## 6. Decision-independent quick wins (do anytime; not blocked on §4)
From the 2026-07-09 ProximityGap audit — polish/symmetry/hygiene on already-committed code:
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

Sound status: every `sorry` in these files is a labeled external admit — **no in-tree gaps**.

## 7. Cross-refs
Memory: `delta-grid-quantization.md`. Branch `feat/abf26-plan` (#505). BCGM25 = eprint 2025/2051.
`CapacityBounds.lean` ~L644 policy note. (Line numbers approximate — anchor on decl names.)
