# Proximity Error Conventions

Companion to [`coding-theory-conventions.md`](coding-theory-conventions.md) (code carriers,
notation, numeric types) and [`probability-conventions.md`](probability-conventions.md) (the
`Probability` namespace).

ArkLib formalises four proximity-style error notions — proximity gap, correlated agreement, mutual
correlated agreement, and weighted correlated agreement. Historically each arrived with its own
shape, its own family of random combinations, and its own numeric conventions. This page fixes one
shape for all of them, so that helper lemmas are written once rather than per notion × per family.

**Status.** The shape below is fully realised for MCA, in
`ArkLib/Data/CodingTheory/ProximityGap/ProximityGenerators.lean`. The `ε_pg` / `ε_ca` layer
(`ProximityGap/Errors.lean`) currently lives on `feat/abf26-plan` (PR #505) and is not yet on
`main`; declarations below marked **(#505)** are on that branch only. Migrating them onto this
shape is the open work.

## The shape

```lean
-- 1. one event predicate per notion, generator-parametric and alphabet-general
def IsMCA (G : Generator S ℓ F) (MC : ModuleCode ι F A) (x : S) (U : ℓ → (ι → A)) (δ : ℝ) : Prop

-- 2. the VALUE is the primitive, and is TOTAL in the radius
noncomputable def mcaError (G : Generator S ℓ F) (MC : ModuleCode ι F A) : ℝ → ENNReal :=
  fun δ => ⨆ U, Pr_{let x ←$ᵖ S}[IsMCA G MC x U δ]

-- 3. the predicate is DERIVED, never parallel — and is where `[0,1]` belongs
def IsMCAGenerator (G : Generator S ℓ F) (ε_mca : I → ℝ≥0) (MC : ModuleCode ι F A) : Prop :=
  ∀ U, ∀ δ : I, Pr_{let x ←$ᵖ S}[IsMCA G MC x U (δ : ℝ)] ≤ ↑(ε_mca δ)
-- tied to the value by `isMCAGenerator_iff_mcaError_le`
```

Five rules, each with a reason that has bitten us:

1. **The value is the primitive; the predicate is derived.** A value can be *assigned* to a code
   family, not merely bounded — which is what the Grand Challenge and prize statements need. The
   reverse arrangement (predicate primitive, value alongside, tied by an `iff`) lets the two drift.
   Same call as `Lambda` / `listDecodable`. Use `def`, not `abbrev`: `simp` will unfold an `abbrev`
   whose body is a `≤` via `ge_iff_le`.

   The payoff is concrete. Stated at the value, the [BCGM25] transport lemmas lose `ε_mca` from
   their statements entirely — `mcaError_generatorByRightMul_le` (Lemma 4.1),
   `mcaError_projectedGenerator_le` (Cor 4.2) — and each is one application of a single shared
   skeleton, `mcaError_le_of_event_implies`. Their `IsMCAGenerator` forms (`pseudoinverseGen`,
   `generatorSubset`) then follow in one line each. The only mathematical content left per lemma
   is its event implication.

2. **No guarded `if … then 0 else Pr […]`.** An `x`-independent guard belongs *inside* the
   probability as a conjunct — which is also how the papers print it. The two forms are equal, and
   the unguarded one is the one a generic API can be written against.

   **But a shared shape is not a shared API.** The guard-turned-conjunct is *anti*-monotone in the
   distance, sitting in the same event as a monotone conjunct, so a guarded error is generally not
   monotone. `epsPG` and `epsCA'` are both pinned to `0` at `δ ≥ 1` while being nonzero below it,
   so `epsPG_mono` and `epsCA'_mono` are **false theorems**, not open ones — see the regression
   pins `epsPG_eq_zero_of_one_le` / `epsCA'_eq_zero_of_one_le` **(#505)**. Monotonicity holds for
   `epsMCA` (guard-free, `epsMCA_mono`) and for `epsCA` in `δ_fld` only (`epsCA_mono_δ_fld`); it is
   *antitone* in `δ_int` (`epsCA_antitone_δ_int`). This matches the sources: BCGM25 Lemma 3.16
   states monotonicity for **MCA only**. Threshold-style statements (`ε ≤ ε*` below a radius,
   `> ε*` above) are therefore MCA-specific; do not transplant them to CA'/PG, where they are
   uninhabitable.

3. **The family is a `Generator` argument, never a new definition.** Affine lines, affine spaces,
   curves, multilinear/tensor combinations and polynomial generators are all `G : S → F^ℓ`. A
   definition per family multiplies every helper lemma by six. Family-dependent error multipliers
   (`k · ε`, `ϑ · ε`) belong in the *theorem*, not in what the notion means.

4. **Codes are `ModuleCode ι F A`, not `Set (ι → A)`.** Both source papers require it: BCGM25
   Def 3.14 says `F`-linear, and ABF26 Def 2.7 defines "F-additive" as *"C is an F-linear subspace
   of Σⁿ"*. `Set` is looser than the mathematics. Alphabets stay general (`A`, not `F`) — this is
   forced, not cosmetic: the interleaving `C^⋈ℓ` has alphabet `Σ^ℓ`
   (`InterleavedWord A κ ι = Matrix ι κ A`, i.e. literally `ι → (κ → A)`), so a field-alphabet
   definition cannot even state BCGM25 Lemma 4.4's hypothesis.

   If someone objects that the flat re-indexing `(κ × ι) → A` keeps the alphabet at `F` and so
   removes the need: it does, and it is the **wrong notion**. Flat indexing measures per-*symbol*
   Hamming distance, whereas interleaved MCA needs the agreement set to be a set of *columns*
   (`T : Finset ι`) — one bad row spoils a column. The module alphabet is what keeps the index type
   equal to the column index. This is the argument that survives the objection; the typing argument
   alone does not.

5. **Radius `δ : ℝ` on the value, `[0,1]` on the bound, compared with `↑` not
   `ENNReal.ofReal`.** See below.

## Numeric conventions

| Slot | Type | Why not the alternatives |
|---|---|---|
| distance `δ` — **argument to the value** (`IsMCA`, `mcaError`) | `ℝ` | Same call as `Code.Lambda`, and for the same reason: this is an argument, and narrowing it only relocates a membership obligation to every call site. The size clause `|T| ≥ n·(1 − δ)` is *total and honest* at every real — no `T` can meet it below `0`, and it is vacuous at and above `1` — so nothing is asserted outside `[0,1]` that the endpoints do not already assert. `I` costs a membership proof wherever a radius is computed (`1 − √ρ − η`, `k/n`); `ℝ≥0` drags truncated subtraction into the size clause and still cannot express a negative radius. |
| distance `δ` — **quantifier on the bound** (`IsMCAGenerator`) | `I` | This is where the sources put `[0,1]`, so this is where it goes: BCGM25 Def 3.14 quantifies `γ ∈ [0,1]` and types `ϵMCA : [0,1] → [0,1]`. Closed, not `Ioo 0 1`: Lemma 3.18 gives `ϵMCA(0) = ϵZE`, Remark 3.15 saturates `ϵMCA(γ) = 1` above some `γ₀ < 1`, and both ABF26 Grand Challenges quantify `δ* ∈ [0,1]`. |
| error **value** | `ENNReal` | It is a supremum of probabilities. Bounded (`mcaError_le_one`, `mcaError_ne_top`), so it crosses back to `ℝ≥0` freely. |
| error **bound** | `ℝ≥0` | `I` **cannot express the transport lemmas at all** — it has no `Add` and no ℕ-`SMul`, so `ε + ε′` (BCGM25 L4.4), `ε + ℓ·ε′`, `k · ε` (L10.1) are unstatable. `ℝ` admits negative bounds, which `ENNReal.ofReal` silently maps to `0`, turning the bound into `Pr = 0`. `ENNReal` allows a meaningless `⊤`. |
| comparison | `Pr ≤ ↑(ε δ)` | `ENNReal.ofReal (p : ℝ) = (p : ENNReal)` for `p : ℝ≥0`, so `ofReal` is a redundant round-trip through `ℝ`; using `↑` lets `norm_cast` discharge the arithmetic instead of hand-rolled `ofReal_add` / `ofReal_mul` / `ofReal_natCast` rewrites. |

**Beware a citation trap here.** ABF26 **contradicts itself** on the radius domain in the ε-error
slot, exactly as it does in the `Λ` slot: §1.2 and both Grand Challenge statements write
`δ ∈ [0,1]`, while Definition 4.1, Definition 4.3, Fact 4.5 and Lemmas 4.6/4.7 all write
`δ ∈ (0,1)`. So `(0,1)` is *not* "the `Λ` slot only" — do not cite ABF26 as settling this either
way. What settles the closed reading on the bound is BCGM25 Def 3.14 together with ABF26's own
Grand Challenge quantifier; what settles totality on the value is that the sources contradict
themselves, so faithfulness cannot decide it and Lean's ergonomics should.

**The radius convention is now single.** `Code.Lambda`, `IsMCA` and `mcaError` all take `δ : ℝ`.
The earlier reading — that `Λ`'s `ℝ` was an outlier to be pulled toward `I` — is wrong and is
recorded as such in `coding-theory-conventions.md` ("Why the radius is `ℝ` while the bound is
`ℝ≥0`"): `I` carries no `Sub`, so `1 − √ρ − η` cannot even be *formed* in it without a membership
proof at every call site, and both ways of narrowing are worse than leaving it alone. That argument
applies verbatim to the ε-error radius; the only thing `[0,1]` genuinely constrains is the *bound*,
and that is where it now sits.

Two things this buys, both checked rather than asserted:

- **The abf26 bridge is unconditional.** `epsMCA C δ = mcaError (AffineLineGenerator F) MC (δ : ℝ)`
  holds for **every** `δ : ℝ≥0` with no side condition. Under `δ : I` it required
  `(δn : ℝ) = (δi : ℝ)` supplied at each call site. Above `1` the two size clauses differ
  syntactically — `ℝ≥0`'s truncated `1 − δ` is `0`, `ℝ`'s is negative — but both are then vacuously
  true, so the equivalence survives on the whole domain.
- **`gridPt` stays total.** It can remain `ℕ → ℝ≥0` (or `ℕ → ℝ`) and compose with `mcaError`
  directly, exactly as `GrandChallenges`' `Lambda (C^⋈ m) (gridPt k : ℝ)` already does. The former
  note here — that `gridPt : ℕ → I` "cannot be made total" because `gridPt_le_one` needs
  `k ≤ Fintype.card ι` — described a constraint that only existed because the value took `I`. It is
  gone, not tracked.

## Naming

Follows `coding-theory-conventions.md`. The quantity tokens are `epsPG`, `epsCA`, `epsMCA`,
`epsWCA`; ε-error material lives in `ProximityGap.*`. A bound for a specific code family reads
`<codeFamily>_<quantity>_<regime>` — `rs_epsMCA_johnson_range_bchks25`,
`subspaceDesign_epsMCA_gg25`.

**The generator-framework value is `CoreDefinitions.mcaError`, not `epsMCA`, and must stay that way
for now.** `ProximityGap.epsMCA` **(#505)** is a *different function* — `(C : Set (ι → A)) → ℝ≥0 →
ENNReal`, with the affine line hard-wired — and the two are related, not equal:
`epsMCA C δ = mcaError (AffineLineGenerator F) MC (δ : ℝ)` at `C = ↑MC`, for every `δ : ℝ≥0`.
Renaming `mcaError` to `epsMCA` before that bridge has retired the abf26 definition would both
collide on merge and make the bridge unstatable. Unify the names when the duplicate is deleted, not
before.

## The helper-lemma API

Writing these against the shape above means writing them once per *notion*, not once per family.
But a notion is **not** required to carry all of them — monotonicity in particular is
notion-specific and two of the four cases are false (rule 2). Check that before attempting one.

- `eps?_mono` in `δ` — **`epsMCA` only**; `epsCA` is monotone in `δ_fld` and *antitone* in `δ_int`;
  **false** for `epsPG` and `epsCA'`. Done for MCA: `mcaError_mono` (BCGM25 Lemma 3.16)
- `eps?_ne_top`, `eps?_le_one` — done for MCA: `mcaError_le_one`, `mcaError_ne_top`
- `eps?_eq_of_floor_eq` — the `1/n` step-function fact (challenge radii are integer grid points).
  Done for MCA: `mcaError_eq_of_floor_eq`, on the primitive `size_clause_iff_floor`
- `isXGenerator_iff_eps?_le` — definitional under rule 1 (`isMCAGenerator_iff_mcaError_le`)
- `eps?_le_iff_threshold` — `eps? ≤ ↑t ↔ ∀ U, Pr > t → jointAgreement`, at an **arbitrary threshold
  `t`, not at `ε`**: the families do not share one. Affine lines and affine spaces use `> ε`, but
  curves use `> k · ε` and multilinear uses `> ϑ · ε`, so a bridge stated at `ε` silently covers
  only two of the five. Each family supplies its own `t` at the call site, per rule 3. Subsumes any
  threshold-implication phrasing, so no such phrasing needs to be a definition
- `epsPG ≤ epsCA ≤ epsMCA` (ABF26 Fact 4.5)
- `epsMCA = epsCA` below the unique-decoding radius (ABF26 Lemma 4.6)
- `eps?(C^⋈k) ≤ k · eps?(C)` (ABF26 Lemma 4.7 / BCGM25 Lemma 10.1)
- generator transport: pseudoinverse (BCGM25 L4.1), subset (Cor 4.2), tensor (L4.4), reindex — all
  via `mcaError_le_of_event_implies`
- `δᵣ(MC^⋈κ) = δᵣ(MC)` — discharges interleaved hypotheses; **not yet proved in-tree**, so
  arguments that rely on it (e.g. the "free at BCGM25 Theorem 8.2" reading in
  `TensorGenerator.lean`) currently have no in-tree witness

## Known exceptions

- **Weighted CA** may not fit rule 3. Its measure `μ` replaces cardinality counting, so the size
  clause `|T| ≥ (1-δ)·n` changes shape rather than instantiating. Treat as a separate family until
  someone checks. `BCIKS20/WeightedAgreement.lean` also still carries `sorry`s.
- **Absolute-distance variants.** `DG25/Basic.lean` states its notions over `ℕ`-valued `Δ₀` rather
  than relative distance. This is faithful to a source — BCGM25 Def 3.21 types CA on integer pairs
  `{(e,t) : 1 ≤ t < e ≤ n} → [0,1]` even though Def 3.14 types MCA on `[0,1]` — so BCGM25 does not
  unify the numeric axis either, and any single convention deviates from it for one of the two
  notions. Leaving this axis plural is the current recommendation.
- **`IsZeroEvadingGenerator`** is already `sSup`-shaped (so it agrees with rule 1) but is a
  different notion, and its bound is typed `ε_ze : I` rather than `I → ℝ≥0` — it has no error
  arithmetic to compose, so the rule-5 argument does not bite. It does fit rule 2's normal form
  (`sSup {y | ∃ v ≠ 0, y = Pr[…]}` is `⨆ v, if v = 0 then 0 else Pr[…]`, with a sample-independent
  guard) and inherits rule 2's caveat about guarded sups and monotonicity.
- **`δ_ε_proximityGap`** (`ProximityGap/Basic.lean`) is stated with `Xor`, which is **stronger than
  ABF26**, whose `ε_pg` is a threshold *implication*: *"for every `L ∈ F` such that
  `p(L) > εpg(C, δ)`, `L` is `δ`-close to `C`"*. The `Xor` additionally asserts the branches are
  exclusive, which fails outright at `ε ≥ 1`. It has consumers (`DivergenceOfSets.lean`,
  `BCIKS20/ReedSolomonGap.lean`), so fixing it is its own change, not a drive-by.
- **Threshold-style statements** (`ε ≤ ε*` below a radius, `> ε*` above — `grandMCAChallenge`)
  depend on monotonicity and are therefore **MCA-specific**. A CA'/PG analogue would be
  uninhabitable.
