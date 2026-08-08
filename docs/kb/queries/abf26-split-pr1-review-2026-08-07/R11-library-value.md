# R11 — library value / consumer / generality review of PR #701

Scope: does this PR leave ArkLib better off as a *general library*, or is it a private
staging area for ABF26? Diff `4f386913..ffa0733a`. All probes under
`(session-local probe) R11-*.lean`, all compiled with `lake env lean` (no repo modification).

Verdict up front: **the PR contains real, reusable library work — but it is not yet wired
into the library.** 9 of the 11 new modules are import-leaves that nothing in the tree
imports or uses; several headline bridges have zero crossers even though a *one-line*
crossing compiles; and the new coding-theory modules regress the surrounding `Type*`
convention and carry unnecessary instance arguments. None of this is unsound. It is
"progresses the library" that is in question, and on the evidence below the answer today
is **partially** — with 3 MEDIUM fixes that are cheap and would flip it.

---

## Section 1 — Consumer analysis (module level)

Measured with `git grep -l "import ArkLib.<M>$"` over `ArkLib/**` excluding the generated
`ArkLib.lean` aggregator, plus a per-declaration usage sweep.

| New module | LoC | Importers in tree | Any decl used outside the module? |
|---|---|---|---|
| `Data/CodingTheory/Basic/Entropy.lean` | 67 | **0** | **no** |
| `Data/CodingTheory/Erasure.lean` | 146 | **0** | **no** |
| `Data/CodingTheory/ExtensionCodes.lean` | 373 | **0** | **no** |
| `Data/CodingTheory/HammingBallVolume.lean` | 211 | **0** | **no** |
| `Data/CodingTheory/JohnsonBound/Family.lean` | 859 | **0** | **no** |
| `Data/CodingTheory/ReedSolomon/Interleaved.lean` | 128 | **0** | **no** |
| `Data/CodingTheory/ReedSolomon/Multiplicity.lean` | 136 | **0** | **no** |
| `Data/CodingTheory/SubspaceDesign.lean` | 763 | **0** | **no** |
| `Data/Probability/Combinatorial.lean` | 352 | **0** | **no** |
| `Data/CodingTheory/ReedSolomon/Folded.lean` | 499 | 1 (`SubspaceDesign.lean`) | yes (only `SubspaceDesign`) |
| `Data/Polynomial/FoldedWronskian.lean` | 406 | 1 (`SubspaceDesign.lean`) | yes (only `SubspaceDesign`) |

So the ~3 900 lines of new Lean form **one connected component**
(`SubspaceDesign → {Folded, FoldedWronskian}`) plus **eight isolated islands**. Nothing
pre-existing in the tree reaches any of it.

Class-(c) new *public* declarations (zero uses anywhere, including inside the PR).
Headline theorems are expected to be here; the ones I flag are marked ⚠.

- **Erasure**: `SupportsErasureCorrection`, `additive_code_supports_erasure_correction_grs12` ⚠
- **Entropy**: `qEntropy`, `qEntropy_zero`, `qEntropy_eq_qaryEntropy_div_log` ⚠ (whole module)
- **HammingBallVolume**: `hammingBallVolume`, `hammingBallVolume_zero_radius`,
  `hammingBallVolume_eq_ncard_hammingBall`
- **Multiplicity**: `umEvalOnPoints`, `umCode`, `mem_umCode_one_iff_mem_rsCode` (whole module)
- **ExtensionCodes**: everything, incl. `IsSystematic` (unused *even inside its own file*) ⚠,
  `lambda_extensionCode_eq_lambda_interleaved`, `extensionCode_iff_coord_in_base`,
  `extensionCode_psi_smul_mem`, `ψ_injective`
- **JohnsonBound/Family**: `Jcap`, `Jcap_zero`, `Jcap_one` ⚠ (see finding R11-3),
  `mds_johnson_lambda_le` ⚠ (see R11-2), `johnson_bound_alphabet_free`
- **SubspaceDesign**: `IsSubspaceDesign`, `subspaceDesign_tau_lower`,
  `frs_is_subspaceDesign_gk16`, `ker_proj_eq_vanish_at`
- **Folded / Interleaved**: `dim_frsCode`, `minDist_frsCode`, `frsCode_one_map_eq_rsCode`,
  `mem_frsCode_iff_flipped`, `dim_irsCode_of_dvd`
- **ListDecodability**: `Lambda_le_iff_listDecodable` ⚠ (the STIR bridge — R11-2), `Lambda_ne_top`
- **RelativeDistance**: `minDist_div_card_eq_minRelHammingDistCode` ⚠ (100-line bridge, no crosser)
- **LinearCode**: `IsMDS_iff_rate_distance'` ⚠ (ρ-idiom restatement, no crosser)
- **Fin/Basic**: `induction_three`, `induction_three'` (fine — completes the existing
  `induction_one/two` family, one-line `rfl`, `@[simp]`)
- **Probability/Instances** (new decls): `Pr_map_eq`, `prob_dotProduct_eq_zero_le`,
  `prob_polynomial_identity_le`, `prob_uniform_le_inv_of_card_le_one`,
  `prob_uniform_pi_mem_finset_le`, `MvPolynomial.totalDegree_le_of_degreeOf_lt` ⚠ — the last
  one's docstring says *"lives here while `prob_polynomial_identity_le` is the only
  consumer"*, but `prob_polynomial_identity_le` itself has zero consumers, so the stated
  justification for its placement is already void.
- **Probability/Combinatorial**: `exists_large_image_of_pairwise_collision_bound`

Judgement on the six modules the brief singled out:

- `HammingBallVolume.lean` — **legitimate.** `card_filter_hammingDist_eq` (the sphere count
  `C(n,i)(q−1)^i`) is a genuinely missing, genuinely general fact, and
  `hammingBallVolume_eq_ncard_hammingBall` correctly bridges to the *pre-existing*
  `ListDecodable.hammingBall`. Keep.
- `Data/Probability/Combinatorial.lean` — **legitimate.** `numCollsOrdered`,
  `sum_fiber_sq_eq`, `cauchy_schwarz_fiber` and Claim B.1 are stated in paper-independent
  form over arbitrary finite `S, T`. Keep. (Minor: the three helpers contain no probability
  and would sit better in a combinatorics file.)
- `Basic/Entropy.lean` — **should not ship as a module** (finding R11-6).
- `Erasure.lean` — **thin** (finding R11-7).
- `ReedSolomon/Multiplicity.lean` — **borderline placeholder.** 136 lines, 2 definitions and
  one `s = 1` sanity lemma. No dimension, no distance, no list-size theory, no consumer.
  It is a correct and standard definition, so not a defect — but it carries no theory and
  its only justification in the audit doc is "ABF26 D A.7". This is the clearest example of
  a module staged for a future split.
- `ExtensionCodes.lean` — **mixed** (findings R11-4 and R11-5).

---

## Findings

### [MEDIUM] The two headline bridges have no crosser, and a one-line crossing that would give the library its first proven Reed-Solomon list-size bound compiles today
- **Where**: `ArkLib/Data/CodingTheory/JohnsonBound/Family.lean:600` (`mds_johnson_lambda_le`),
  `ArkLib/Data/CodingTheory/ListDecodability.lean:102` (`Lambda_le_iff_listDecodable`)
- **What's wrong**: The PR's own docstrings advertise integration —
  *"List-size bounds proved for `Lambda` … transfer to `listDecodable` consumers through this
  equivalence"* (`ListDecodability.lean:99-101`) — but no such transfer is performed, and
  `Lambda_le_iff_listDecodable` has **zero** uses. Meanwhile `ReedSolomon.isMDS_code`
  (`ArkLib/Data/CodingTheory/ReedSolomon.lean:497`, pre-existing, proven) and
  `ReedSolomon.minDist_of_le` (`:398`, pre-existing, proven) already sit in the tree, so
  ABF26 C3.3 instantiates at Reed-Solomon **in one line**, and the STIR-shaped
  `listDecodable` form follows in two.
- **Evidence** (both compile clean, no `sorry`):
  - `(session-local probe) R11-rs-johnson.lean` —
    `theorem rs_johnson_lambda_le … := mds_johnson_lambda_le (ReedSolomon.code α n) η hη ReedSolomon.isMDS_code`
  - `(session-local probe) R11-stir-bridge.lean` —
    `theorem johnson_listDecodable … := Lambda_le_iff_listDecodable.mp ((Lambda_mono hδ).trans (johnson_bound_lambda_le_ell C ℓ hℓ hrad))`,
    which is exactly the shape of `Stir/MainThm.lean:72` `CodeParams.h_listDecode` and
    `Stir/OutOfDomSmpl.lean:55,65` `h_decodable` — hypotheses those files currently *assume*
    and no in-tree lemma can supply.
- **Refutation attempt**: I checked whether the RS instantiation is blocked by a universe or
  instance mismatch (`mds_johnson_lambda_le` is `Type 0`-only, `isMDS_code` is also
  `{ι : Type}` with `[Inhabited ι] [NeZero n]`) — they line up, and the probe compiles. I also
  checked whether STIR's `listDecodable C δ (l : ℝ≥0)` differs from `listDecodable C δ (ℓ : ℝ)`
  in a blocking way — it does not, both are `ℝ`-valued after coercion.
- **Suggested fix**: Add the two corollaries above (≈8 lines total). That single change turns
  `JohnsonBound/Family.lean` from an isolated island into the first in-tree supplier of the
  list-decodability hypotheses the STIR/WHIR development has been assuming since it landed —
  and it is exactly what "progresses the library beyond ABF26" means here.

### [MEDIUM] `Jcap` is a definition with no theory, no consumer, and an existing in-tree lemma about the very same expression that it does not touch
- **Where**: `ArkLib/Data/CodingTheory/JohnsonBound/Family.lean:88` (`Jcap`)
- **Source**: pre-existing `JohnsonBound.sqrt_le_J` at
  `ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean:64`:
  `lemma sqrt_le_J … : 1 - √(1 - δ) ≤ J q δ`, i.e. literally `Jcap δ ≤ J q δ`.
- **What's wrong**: `Jcap δ := 1 - √(1 - δ)` is added next to `sqrt_le_J`, whose statement
  *is* `Jcap`; the PR neither restates `sqrt_le_J` in terms of `Jcap` nor proves anything
  about `Jcap` beyond `Jcap 0 = 0` / `Jcap 1 = 1`. `Jcap` has zero uses anywhere.
  Worse, the two docstrings now *contradict each other* in the same directory:
  `sqrt_le_J` calls `1 - √(1-δ)` "the binary Johnson bound", while `Jcap`'s docstring says
  *"It is **not** the binary Johnson bound: `J_2(δ) = ½(1 - √(1 - 2δ)) ≠ 1 - √(1 - δ)`."*
  The PR identifies an error in an existing docstring and leaves it in place.
- **Evidence**: `grep -rn "\bJcap\b" ArkLib/` → only the definition + its two `@[simp]`
  lemmas + docstrings in `Family.lean`. `sed -n '63,65p' JohnsonBound/Basic.lean` for the quote.
- **Refutation attempt**: I looked for a `Jcap`-based statement elsewhere in the PR (e.g. as
  the `η → 0` limit in `mds_johnson_lambda_le`) — `mds_johnson_lambda_le` writes
  `1 - Real.sqrt ρ - η` literally and never mentions `Jcap`. So even the PR's own
  capacity-shaped theorem declines to use it.
- **Suggested fix**: either drop `Jcap` until it has a theorem, or restate `sqrt_le_J` as
  `Jcap δ ≤ J q δ` and fix its docstring — one line each, and it wires the new name in.

### [MEDIUM] Three new "paper-named" declarations are `rfl`-identical to Mathlib API, against a convention the PR's own audit doc states
- **Where**: `ArkLib/Data/CodingTheory/ExtensionCodes.lean:82` (`ψ`), `:89` (`φ`), `:95` (`coord`)
- **Source**: Mathlib `algebraMap`, `Basis.equivFun`, `Basis.coord`.
- **What's wrong**: all three are definitionally the Mathlib item. The PR's own
  `docs/kb/audits/…correlated-agreement.md` D2.7 row states *"ArkLib convention avoids
  alias-style wrappers for items already realised by existing types"*, and the recorded owner
  feedback is "no paper-shape `alias` wrappers". The downstream consequences are visible in
  the same file: `ψ_injective` is `FaithfulSMul.algebraMap_injective` verbatim (and has zero
  uses), and `coord_add` / `coord_psi_smul` restate `LinearMap.map_add` / `map_smul` for a
  map that already *is* a `LinearMap`.
- **Evidence**: `(session-local probe) R11-coord-dup.lean` compiles clean, proving all three by `rfl`:
  ```
  example … : P.coord j = P.basis.coord j := rfl
  example … : P.φ       = P.basis.equivFun := rfl
  example … : P.ψ       = algebraMap B F  := rfl
  ```
- **Refutation attempt**: I checked whether the aliases buy notation or better unfolding — `φ`
  is a plain `noncomputable def` (not `@[reducible]`) and `coord` is a `∘ₗ`-composition, so
  they *hinder* `simp` relative to `Basis.coord`'s existing `@[simp]` API rather than help it.
- **Suggested fix**: delete `ψ`/`φ`/`coord`/`ψ_injective`/`coord_add`/`coord_psi_smul` and use
  `algebraMap`, `P.basis.equivFun`, `P.basis.coord` directly (the docstrings can keep the
  paper's names). `ExtensionFieldPresentation` itself (the `⟨e, Basis (Fin e) B F⟩` record)
  is a defensible bundling — keep that.

### [MEDIUM] Unnecessary instance arguments baked into new *definitions*, with the linters that catch them disabled file-wide
- **Where**: `ReedSolomon/Folded.lean:106` (`frsCode`), `ReedSolomon/Interleaved.lean:59`
  (`irsCode`), `ExtensionCodes.lean:135` (`extensionCode`); suppressions at
  `Folded.lean:48`, `Interleaved.lean:33-35`, `ExtensionCodes.lean:51-52`,
  `HammingBallVolume.lean:31-32`, `Family.lean:55-56`, `SubspaceDesign.lean:50-52`.
- **What's wrong**: `frsCode` demands `[DecidableEq ι] [DecidableEq F]`; `irsCode` demands
  `[Fintype ι] [DecidableEq ι] [DecidableEq F]`; `extensionCode` demands `[Fintype ι]`. None
  of these are needed. Because they sit on the *definitions*, every downstream statement
  inherits them and every future caller must supply them. Compare the sibling they mirror:
  pre-existing `ReedSolomon.code` requires only `[Semiring F]`.
  `linter.unusedDecidableInType` / `unusedFintypeInType` exist precisely to catch this and are
  turned off at the top of 5 of the new files (6 + 5 new `set_option` lines in the diff).
- **Evidence**: `(session-local probe) R11-inst2.lean` and `R11-inst3.lean` compile clean; each
  defines the weakened version and then proves `weakened = PR version` by `rfl`.
- **Refutation attempt**: I first suspected `HammingBallVolume.card_filter_hammingDist_eq`'s
  `[DecidableEq ι]` was also spurious — **it is not** (`Fintype (ι → F)` needs it), so I
  dropped that from the finding. I also confirmed the linter suppressions have in-tree
  precedent (`ReedSolomon.lean`, `AffineSpaces.lean`, `FoldingPolynomial.lean`), so the
  suppression itself is not novel — the *consequence* here is.
- **Suggested fix**: drop the three sets of instances; re-enable the two linters in the new
  files (the `unusedSectionVars` suppression in `Interleaved.lean`/`SubspaceDesign.lean` is
  the only one that looks genuinely needed).

### [MEDIUM] Universe regression: the new coding-theory layer is `Type 0`-only while the layer it extends is `Type*`
- **Where**: `JohnsonBound/Family.lean` (`johnson_bound_lambda_le_ell`, `mds_johnson_lambda_le`,
  `Jqℓ` call sites), `HammingBallVolume.lean`, `ExtensionCodes.lean`,
  `ReedSolomon/Folded.lean`, `ReedSolomon/Interleaved.lean`,
  `Basic/LinearCode.lean:667,707` (`IsMDS_iff_rate_distance`, `…'`).
- **What's wrong**: `#check @` with `pp.universes` shows these have **no universe
  parameters**, while the declarations they are *about* do:
  ```
  @Lambda.{u_1, u_2}                     -- added by this PR, polymorphic
  @johnson_bound_lambda_le_ell           -- theorem ABOUT Lambda, Type 0 only
  @ReedSolomon.code.{u_1, u_2}           -- pre-existing, polymorphic
  @ReedSolomon.Folded.frsCode            -- its new sibling, Type 0 only
  @ReedSolomon.Interleaved.irsCode       -- Type 0 only
  @Code.interleavedCodeSet.{u_1,u_2,u_3} -- pre-existing, polymorphic in κ
  @LinearCode.singleton_bound_module.{u_1,u_2,u_3}  -- added by this PR, polymorphic
  @LinearCode.IsMDS_iff_rate_distance    -- added by this PR, same file, Type 0 only
  ```
  Counts of `: Type}` vs `: Type*}` binders — existing files: `Basic/Distance.lean` 0/26,
  `Basic/RelativeDistance.lean` 0/23, `InterleavedCode.lean` 0/46, `ReedSolomon.lean` 4/16.
  New files: `ExtensionCodes.lean` 18/0, `Folded.lean` 21/0, `Family.lean` 8/0,
  `Interleaved.lean` 6/0, `HammingBallVolume.lean` 4/0. The PR is internally inconsistent —
  `singleton_bound_module` and `Multiplicity.lean` got `Type*` right; the neighbours did not.
- **Evidence**: `(session-local probe) R11-universe.lean` output (quoted above);
  `(session-local probe) R11-rs.lean`.
- **Refutation attempt**: I checked whether the `JohnsonBound/` directory's own convention is
  `Type` (it is — `JohnsonBound/Basic.lean` uses `{F : Type}` + `Fin n`), which excuses
  `Family.lean` in isolation. It does **not** excuse `Folded.lean`/`Interleaved.lean`, whose
  parent `ReedSolomon.lean` is polymorphic, nor `IsMDS_iff_rate_distance` sitting directly
  below a `Type*` sibling in the same file.
- **Suggested fix**: `Type` → `Type*` in the five new coding-theory files. On the sample I
  tried this is mechanical.

### [MEDIUM] `Basic/Entropy.lean` should not be a module: it is a rescale of a fully-developed Mathlib notion, has no theory, no consumer, and no connection to codes
- **Where**: `ArkLib/Data/CodingTheory/Basic/Entropy.lean` (67 lines, 3 declarations)
- **Source**: Mathlib `Real.qaryEntropy` (`Mathlib.Analysis.SpecialFunctions.BinaryEntropy`),
  which already ships `qaryEntropy_zero`, `qaryEntropy_one`, `qaryEntropy_two`,
  `qaryEntropy_continuous`, `strictConcaveOn_qaryEntropy`, sign lemmas, …
- **What's wrong**: the PR itself proves `qEntropy q x = Real.qaryEntropy q x / Real.log q`
  (`qEntropy_eq_qaryEntropy_div_log`), i.e. the new definition is Mathlib's up to a constant
  factor. It re-derives none of the Mathlib API, so any future consumer needing continuity or
  concavity must round-trip through the bridge anyway. The module contains no `ArkLib` import
  at all and never mentions a code — it is a pure real-analysis file placed in
  `Data/CodingTheory/Basic/`, whose 67 lines make it the smallest module in the directory.
- **Evidence**: `lean_loogle "Real.qaryEntropy"` (8 hits listing the Mathlib API);
  `head -10 ArkLib/Data/CodingTheory/Basic/Entropy.lean` shows only Mathlib imports;
  `git grep -l "import ArkLib.Data.CodingTheory.Basic.Entropy"` → empty.
- **Refutation attempt**: I checked whether base-`q` entropy exists in Mathlib under another
  name (it does not — Mathlib's is natural-log), so `qEntropy` is not a literal duplicate.
  That is why this is MEDIUM and not HIGH. But the right home for a `logb`-based entropy is
  Mathlib (`ToMathlib/Analysis/`), not a coding-theory `Basic/` module with zero code content.
- **Suggested fix**: fold the definition into whichever module first needs it, or move it to
  `ArkLib/ToMathlib/` as an upstreaming candidate.

### [LOW→MEDIUM] `Erasure.lean` ships a predicate whose only theorem is that every code satisfies it, and whose stated generic use case does not exist in the tree
- **Where**: `ArkLib/Data/CodingTheory/Erasure.lean:66`, `:125`
- **What's wrong**: `additive_code_supports_erasure_correction_grs12` proves
  `∀ C, SupportsErasureCorrection C` for an *arbitrary* set `C`; the docstring correctly and
  honestly admits *"this theorem does NOT capture the cited [GRS12] content"* (the content is
  the `O((sn)³)` algorithm, out of ArkLib's cost-free model). What is left is: a predicate
  with no consumer, a theorem that is a classical-choice existence statement, and a module
  docstring justifying its `Data/CodingTheory/` home by *"any reduction whose extractor
  erasure-decodes its oracles consumes the same shape"* — no such reduction exists in the tree.
  The one piece of durable value is `eq_of_consistent_with_erased` (a clean Hamming pigeonhole).
- **Evidence**: `git grep "SupportsErasureCorrection" ArkLib/` → 4 hits, all inside
  `Erasure.lean`; module has 0 importers.
- **Refutation attempt**: I checked whether any `OracleReduction`/`ProofSystem` extractor does
  erasure decoding today (`grep -ri erasure ArkLib/OracleReduction ArkLib/ProofSystem`) — none.
- **Suggested fix**: keep `eq_of_consistent_with_erased` (promote it into `Basic/Distance.lean`
  next to `disagreementCols`, which it uses); hold `SupportsErasureCorrection` and its
  existence theorem until the §6 split brings the consumer.

### [LOW] Two provably-unnecessary hypotheses on the headline `L2.21` theorem — a transcription of the paper's "for every δ ∈ (0,1)" that the proof never uses
- **Where**: `ArkLib/Data/CodingTheory/ExtensionCodes.lean:316`
  (`lambda_extensionCode_eq_lambda_interleaved`, hypotheses `_hδ_pos : 0 < δ`, `_hδ_lt : δ < 1`)
- **Evidence**: `lean_minimal_hypotheses` on the theorem reports both binders
  `"status": "removable"` (all other binders `load-bearing`). Confirmed by inspection:
  neither name occurs anywhere in the proof body.
- **Refutation attempt**: I re-ran the same tool on `subspaceDesign_tau_lower` (all
  load-bearing) and hand-checked `johnson_bound_lambda_le_ell` (`_hℓ_ge` used at :515,
  `_h_radicand` at :513) and `mds_johnson_lambda_le` (`_hη_pos` at :758,:775, `_h_mds` at
  :615) — so this is a one-off, not a pattern.
- **Suggested fix**: drop them (the lemma is true for every real `δ`, which is strictly more
  useful; the paper's range can stay in the docstring). While there: the `_h`-underscore
  prefix is used on load-bearing hypotheses elsewhere in `Family.lean`, which reads as
  "unused" to a Lean audience — rename the load-bearing ones.

### [LOW] `docs/wiki/coding-theory-conventions.md` documents API that does not exist, and misstates one that does
- **Where**: `docs/wiki/coding-theory-conventions.md` (new, 186 lines)
- **What's wrong** (all verified by `grep -rn … --include=*.lean ArkLib/`, 0 hits each):
  - Names documented but absent from the tree: `epsCA`, `epsMCA`, `epsPG`,
    `restrictedRelHammingDist` (+ its `Δ[T]` notation), `LineDecodable`, `IsFAdditive`.
    Every example in the "Theorem naming" table (`linear_epsCA_1_5_johnson_bgks20`,
    `rs_epsMCA_johnson_range_bchks25`, `rs_epsCA_breakdown_cs25`,
    `linear_lambda_ge_elias_volume_eli57`, `rs_lambda_high_rate_jh01`) is fictional.
  - The "File and namespace layout" section lists `IsMDS` as a `CodingTheory.*` item; it is
    `LinearCode.IsMDS`.
  - The "Tagged sorry comments" section defines a convention with **zero** instances in the
    tree (the PR is sorry-free), and asserts that
    `hammingBallVolume_eq_ncard_hammingBall` has a "partial proof … decompos[ing] into
    `card_filter_hammingDist_eq` and a small Set/Finset conversion" — it is fully proven.
  - `docs/kb/audits/…correlated-agreement.md` lists Lean targets
    `existing + scoped notation "RS[" F ", " L ", " k "]"` and `existing + scoped notation
    "_^≡_"`; neither notation exists, and the conventions doc in the *same PR* explicitly
    rules the `RS[...]` family out ("Per design decision (polish-plan D2)").
- **Refutation attempt**: the page is honest that "several examples below are drawn from"
  the next split, so this is not dishonesty — it is a maintenance liability: a *permanent
  wiki page* pinned to unreleased code, which is exactly the "private staging area" signal.
- **Suggested fix**: cut the page down to what is in the tree; move the forward-looking
  half into `docs/kb/` (where speculative planning belongs) until the split lands.

### [LOW] Placement: generic, reusable lemmas are `private`, or in the wrong namespace/file
- `Polynomial.pow_dvd_det_of_forall_mem_col_dvd` (`Data/Polynomial/FoldedWronskian.lean:103`)
  — a pure `Matrix`/`CommRing` determinant-divisibility lemma, with no Mathlib equivalent
  (`lean_loogle "?d ^ _ ∣ Matrix.det ?M"` → 0 hits), living in `namespace Polynomial` inside
  a Wronskian file. `ArkLib/Data/Matrix/Basic.lean` exists. Nobody looking for this will find it.
- `Polynomial.X_pow_card_sub_one_sub_C_irreducible` (`:181`) — a standalone finite-field
  Kummer-irreducibility theorem (the docstring notes Mathlib's criterion does not cover the
  even exponent `q−1`) with nothing to do with Wronskians. Prime `ToMathlib/` material.
- `SubspaceDesign.lean` locks three fully general, Mathlib-shaped facts behind `private`:
  `sum_rootMultiplicity_le_natDegree` (`:276`), `finrank_eq_of_map_eq` (`:298`),
  `exists_adapted_basis` (`:312` — "any finite-dimensional `M` has a `Fin σ`-basis whose first
  `dim N` vectors lie in `N`"; no Mathlib equivalent surfaced by `lean_leansearch`).
- `foldedWronskian_of_linearComb` (`:338`) and `pow_dvd_foldedWronskian` (`:362`) are theorems
  *about* `Polynomial.foldedWronskian` but live `private` in `namespace CodingTheory` inside
  `Data/CodingTheory/SubspaceDesign.lean`, not in `Data/Polynomial/FoldedWronskian.lean`.
- **Suggested fix**: move the two matrix/field-theory items out of `FoldedWronskian.lean`;
  make the three generic lemmas public (in `ToMathlib/` or the relevant `Data/` file); move
  the two `foldedWronskian_*` lemmas into `FoldedWronskian.lean`.

### [LOW] `irsCode` bakes ABF26's `k/s` rounding convention into a general-sounding definition
- **Where**: `ReedSolomon/Interleaved.lean:59`
- `irsCode domain k s := (ReedSolomon.code domain (k / s)) ^⋈ (Fin s)` — `Nat` truncated
  division. Its own docstring concedes downstream theorems "should add an explicit `s ∣ k`
  hypothesis at the use site", and `dim_irsCode_of_dvd` exists solely to undo the truncation.
  A general caller wanting the `s`-interleave of `RS[k']` must write `irsCode domain (s*k') s`.
  The body is a one-line application of the existing `^⋈` operator, so the wrapper's only
  content is the rounding convention. Consider taking the *inner* degree as the parameter.

---

## Section 4 — Architecture / import graph

- **Granularity.** `Basic/Entropy.lean` (67 lines) is over-fragmented (see R11-6);
  `HammingBallVolume.lean` (211 lines) is fine as its own module — it has one real theorem
  and a clean dependency on `ListDecodability`.
- **`Data/Polynomial/FoldedWronskian.lean`** — the Wronskian core is correctly placed; the
  matrix lemma and the field-theory irreducibility theorem are not (see the LOW placement
  finding). Net: right directory, wrong contents for 2 of its 6 public declarations.
- **New top-level namespaces.** `namespace CodingTheory` is **entirely new** — all 6
  occurrences in the tree are PR files. `ArkLib/Data/CodingTheory/` previously used
  `Code`, `ListDecodable`, `LinearCode`, `ReedSolomon`, `JohnsonBound`, `ProximityGap`. The
  PR adds a 7th that shadows the directory name and overlaps `Code`; e.g.
  `CodingTheory.hammingBallVolume` and `ListDecodable.hammingBall` are the same concept in
  two namespaces, and `CodingTheory.qEntropy` is not about codes at all. Meanwhile the PR's
  *own* new declarations do not follow it (`Lambda` → `ListDecodable`,
  `IsMDS_iff_rate_distance` → `LinearCode`, `singleton_bound_module` → `LinearCode`),
  and the conventions doc misdescribes `IsMDS` as `CodingTheory.*`.
  `namespace Probability` (Instances + Combinatorial) is, by contrast, **a genuine
  improvement**: it de-pollutes the root namespace, is documented in a new wiki page, and
  the two affected consumers (`ProximityGap/AffineGenerator.lean`,
  `OracleReduction/Security/RbrGame.lean`) were updated. One nit: `Notation.lean`'s new
  `Pr_decide_eq_tsum_indicator` goes to `ProbabilityTheory` instead, and the two fixed
  consumers use a *file-level* `open Probability` where the new wiki page says to open
  "locally near the use site".
- **Import graph.** New Mathlib edges are all into new leaf modules except one:
  `Mathlib.FieldTheory.Finiteness` → `Basic/LinearCode.lean` (15 direct importers). That file
  already imports `Mathlib.LinearAlgebra.FreeModule.PID` / `RingTheory.PicardGroup` /
  `RingTheory.RegularLocalRing.Defs`, so the added weight is negligible. **No cycle risk**:
  the entire new subtree is a DAG of leaves. Full list of new `import` lines is in the report
  workspace (`git diff … | grep '^+import'`, 26 lines, 5 of them intra-ArkLib).

---

## Clean bill — checked and found genuinely OK

- **Hypothesis weakening on pre-existing declarations (the best library work in the PR).**
  `johnson_bound`, `johnson_bound_alphabet_free`, `johnson_condition_weak_implies_strong`,
  `min_dist_le_d`, `e_ball_le_radius`, `JohnsonBound.johnson_bound_lemma` all lose
  `[Field F]`. This is a *real generalisation of an existing ArkLib development*, not a fork:
  the field-based `lin_shift_*` recentering is replaced by the new coordinatewise `remap`
  transport, so the Johnson bound now applies over arbitrary finite alphabets. Exactly the
  "generalise the original instead of forking it" behaviour the owner asks for.
- **`disagreementCols`** (`Basic/Distance.lean:149`) — a genuine base primitive; the PR
  refactored two existing proofs in the same file onto it and documented the relationship to
  the four protocol-specific `disagreementSet`s. Well-judged, including the naming choice.
- **`singleton_bound_module`** — universe-polymorphic, module-alphabet generalisation of
  `singleton_bound_linear`, and it is actually *used* (by `subspaceDesign_tau_lower`).
- **`lambda_extensionCode_eq_lambda_interleaved`** uses the pre-existing
  `Code.interleavedCodeSet` rather than a new interleave — correct reuse.
- **`ReedSolomon/Folded.lean`'s "Not the FRI fold" section** — explicitly disambiguates
  GR08 alphabet-enlarging folding from the FRI/STIR split-and-fold in
  `ProximityGap/Folding.lean`, `SplitFold.lean`, `FoldingPolynomial.lean`. This is exactly the
  kind of cross-development orientation a library needs and no paper would contain.
- **`minRelHammingDistCode` `Set.Finite.toFinset` refactor** — removes a `Fintype.ofFinite`
  diamond and adds the three missing characterisation lemmas (`_mem`, `_le`, `_of_empty`).
  Real hygiene improvement to a pre-existing definition.
- **`Data/Probability/Combinatorial.lean`** — Claim B.1 and its two helpers are stated in
  fully paper-independent form (arbitrary finite `S`, `T`, arbitrary `PMF`); reusable as-is.
- **`prob_schwartz_zippel_mv_polynomial` generalisation** — the old `d := n` form is preserved
  as a one-line wrapper over the new `_of_totalDegree_le`; no consumer break.
- **`Fin.induction_three` / `induction_three'`** — completes an existing family whose earlier
  members are used by `Sumcheck/Spec/SingleRound.lean`. Cheap and correct.
- **No import cycle, no heavy edge into a hot module, no consumer breakage** (build green;
  the two files needing `open Probability` were updated in the PR).
- **`ExtensionFieldPresentation` as a record** — bundling `⟨e, Basis (Fin e) B F⟩` on top of
  `[Algebra B F]` is a reasonable, non-duplicative abstraction (my complaint is only about
  the three `rfl` aliases hanging off it).
- **`lean_minimal_hypotheses`** run on `subspaceDesign_tau_lower` (all 5 explicit binders
  load-bearing) and hand-audit of `johnson_bound_lambda_le_ell` / `mds_johnson_lambda_le`
  (all explicit binders used) — only the one L2.21 case is defective.
