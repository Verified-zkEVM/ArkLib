# R5 — `ReedSolomon/{Folded,Interleaved,Multiplicity}.lean` (ABF26 §2.4 / App. A.2)

Reviewer: R5 (`R5-rs-families`). Repo `@ffa0733a`. Read-only; all probes in
`(session-local probe) R5-*.lean` (+ `R5-mindist-bruteforce.py`), all compiled with
`lake env lean` against this commit.

**Headline: no CRITICAL, no HIGH. The three modules are mathematically correct,
faithful to ABF26 (and to GR08 for the folded case), non-vacuous (compiled witnesses at
two concrete parameter sets, including ABF26's own smooth-domain shape), `sorry`-free and
axiom-clean.** The `minDist_frsCode` formula was independently re-derived by exhaustive
brute force at 22 parameter points and matches everywhere. Findings are 3 × MEDIUM
(two missed generalizations/reuses, one audit-doc honesty gap) and 6 × LOW.

---

## Verification of the PR's central claim (`Admissible` strengthening) — CONFIRMED, and
## stronger than the PR says

Not a defect; recorded because it is the load-bearing claim of the whole cluster.

- **ABF26 Def 2.14 (verbatim, `(pdftotext of ~/abf26-refs/) ABF26.txt:457`)**:
  > "Let `L ⊆ F` and `s ∈ N`. We say that `ω ∈ F` is `(L, s)`-admissible if for every
  > `α, β ∈ (L choose 2)` it holds that `α · ω^i ≠ β` for every `0 ≤ i < s`."

  (the extracted glyph `L2` with the tall paren is `\binom{L}{2}`, i.e. **distinct**
  unordered pairs — so `α ≠ β` is assumed, and nothing constrains `α` against itself.)
- **(e) The claimed paper defect is REAL.** Compiled:
  `R5-admissible-witness.lean → paper_admits_one` proves that the literal Def 2.14 is
  satisfied by `ω = 1` for **every** `L` and **every** `s`.
- **(b) What Lean adds** (`Folded.lean:79-80`): the second conjunct
  `∀ α ∈ L, ∀ i, 0 < i → i < s → α * ω^i ≠ α`. Together with the first conjunct this is
  *exactly* injectivity of `(α,i) ↦ α·ω^i` on `L × Fin s` (given `ω ≠ 0`), which is
  exactly GR08's setup (GR08 Def 2.1: evaluation points `1, γ, …, γ^{n−1}` all distinct,
  folded domain `{γ^{jm}}`, fold by `×γ^i` — `(pdftotext of ~/abf26-refs/) GuruswamiR08.txt:391-403`).
  So the folding is `ω^j · x`, **not** `x^{q^j}`, and no coset/orbit-union structure is
  baked into the Lean domain (correctly: ABF26 does not require it either; smoothness is
  a separate Def 2.12).
- **(c) Hypothesis position only.** `grep -rn Admissible --include=*.lean .`: 4 hypothesis
  occurrences in `Folded.lean` (139/181/211/243), 1 hypothesis in
  `SubspaceDesign.lean:488`, and one `have hadm` at `SubspaceDesign.lean:550` that
  *derives* admissibility on `image domain ⊆ L` **from** the strengthened hypothesis on
  `L` (antitone restriction). No declaration anywhere concludes `Admissible`. ✔
- **(d) Satisfiable — two compiled witnesses**, `R5-admissible-witness.lean`:
  - `adm_witness : Admissible (univ.map dom5) 2 (2 : ZMod 11)` (L = order-5 subgroup
    `{1,3,9,5,4}`, ω = 2 a generator, 10 = |F*| folded points — the tight GR08 regime);
  - `adm_smooth : Admissible (univ.map dom17) 4 (3 : ZMod 17)` — **ABF26's own smooth
    regime** (Def 2.12: `L` = the order-4 = 2² subgroup `{1,4,16,13}`, `s = 4` a power of
    two, `ω = 3` a generator; `L, ωL, ω²L, ω³L` are the 4 distinct cosets covering all 16
    nonzero elements).
  Both feed non-degenerate instantiations of `dim_frsCode` (=3, =7, =8) and
  `minDist_frsCode` (=4, =2, =3, all `< |ι|`). **No vacuity.**
- **The strengthening is not merely defensible — it is NECESSARY.**
  `R5-mindist-bruteforce.py` (exhaustive over all `(ZMod 11)^k`, `L` = the QR subgroup,
  `s = 2`, **`ω = 1`** — a value the paper's literal Def 2.14 permits):

  ```
  k=1 true_minDist=5 Lean_formula=5 OK
  k=2 true_minDist=4 Lean_formula=5 MISMATCH
  k=3 true_minDist=3 Lean_formula=4 MISMATCH
  k=4 true_minDist=2 Lean_formula=4 MISMATCH
  k=5 true_minDist=1 Lean_formula=3 MISMATCH
  ```
  i.e. under the paper's literal Def 2.14 the ABF26/GR08 folded-RS distance claim
  (and hence `minDist_frsCode`) is **false**. This should be added to the paper-review
  ledger: it is a genuine ABF26 defect, not a Lean convenience.

---

### [MEDIUM] `dim_irsCode` is an RS-specific instance of a general interleaved-code dimension lemma that `InterleavedCode.lean` does not have

- **Where**: `ArkLib/Data/CodingTheory/ReedSolomon/Interleaved.lean:70`
  (`ReedSolomon.Interleaved.dim_irsCode`)
- **Source / duplication target**: `ArkLib/Data/CodingTheory/InterleavedCode.lean`
  (803 lines) contains **no** `finrank` / `Module.rank` / `dim` lemma at all
  (`grep -n "finrank\|Module.rank\|dim" …` → 0 hits). The general fact
  `finrank F (MC ^⋈ κ) = |κ| · finrank F MC` belongs there.
- **What's wrong**: the *reuse* claim in the PR is true — `irsCode` really is
  `(ReedSolomon.code domain (k/s)) ^⋈ (Fin s)`, no fork (verified: `^⋈` resolves to
  `ModuleCode.moduleInterleavedCode`, `InterleavedCode.lean:149`, whose carrier is
  `interleavedCodeSet`, matching ABF26 Def 2.9 row-wise, `ABF26.txt:399-403`). But the
  *proof* of `dim_irsCode` (lines 74-115) is entirely RS-free until the last line: it
  builds `encoder : (Fin s → ↥RS) →ₗ[F] (ι → Fin s → F)`, shows injectivity and
  `range = irsCode`, then applies `finrank_pi_fintype`. Only `exact dim_eq_deg_of_le …`
  is RS-specific. The general lemma is what the repo needed.
- **Evidence**: `(session-local probe) R5-interleaved-general.lean` **compiles clean**. It proves
  `R5Probe.finrank_interleavedCode : finrank F ↥(MC ^⋈ κ) = Fintype.card κ * finrank F ↥MC`
  for an arbitrary `ModuleCode ι F A` **by literally the same script**, and then derives
  `dim_irsCode'` in *two lines*:
  ```
  rw [Interleaved.irsCode, finrank_interleavedCode, Fintype.card_fin]
  exact congrArg _ (ReedSolomon.dim_eq_deg_of_le h_rs_full)
  ```
  The general version also **drops the `[Nonempty ι]` binder** that ArkLib's
  `dim_irsCode` / `dim_irsCode_of_dvd` carry (probe's final `example` witnesses this).
- **Refutation attempt**: I looked for an existing general lemma under
  `ArkLib/Data/CodingTheory/**` and Mathlib (`Submodule.finrank_pi`, `finrank_pi_fintype`)
  — the pi-type lemma exists but the `interleavedCodeSet`-as-submodule bridge does not, so
  the lemma really is absent, and adding the RS-only version is the missed generalization.
  I also checked whether `A = Fin s → F` makes the general statement harder (extra
  `Module.Finite F ↥MC` instance argument needed) — it does add one instance binder, which
  is automatically discharged in the RS instantiation.
- **Suggested fix**: move the proof to `InterleavedCode.lean` as
  `ModuleCode.finrank_interleavedCode`, keep `dim_irsCode` as the 2-line corollary, drop
  `[Nonempty ι]`.

---

### [MEDIUM] `frsCode` *is* the plain RS code on the enlarged folded domain (GR08's own characterisation); the bridge is not stated, so `dim_frsCode` re-derives by hand what `ReedSolomon.dim_eq_deg_of_le` already gives

- **Where**: `ArkLib/Data/CodingTheory/ReedSolomon/Folded.lean:181` and `:211`
  (`frsEvalOnPoints_domRestrict_injective`, `dim_frsCode`)
- **Source**: GR08 Definition 2.1 (`(pdftotext of ~/abf26-refs/) GuruswamiR08.txt:399`):
  > "the codewords of `FRS_{F,γ,m,k}` are in one-one correspondence with those of the RS
  > code `C` and are obtained by bundling together consecutive `m`-tuple of symbols in
  > codewords of `C`."

  ArkLib pre-existing: `ReedSolomon.dim_eq_deg_of_le` (`ReedSolomon.lean:236`).
- **What's wrong**: `frsCode domain k s ω` is exactly the curry-image of
  `ReedSolomon.code (foldedDomain) k` where `foldedDomain : ι × Fin s ↪ F` is
  `(x,j) ↦ domain x · ω^j` (the embedding whose injectivity
  `admissible_foldedPoints_injective` already supplies). Once that bridge is stated, the
  30-line `frsEvalOnPoints_domRestrict_injective` + `dim_frsCode` pair collapses to a
  4-line transport of the existing RS dimension lemma. Not a *fork* (nothing is
  redefined), but a missed reuse of main's post-#663 generalized API — and it is the
  paper's/GR08's own way of saying what an FRS code is, so the bridge has independent
  value (it would also give rate, `s=1` collapse, and future list-decoding transport
  for free).
- **Evidence**: `(session-local probe) R5-frs-is-rs-on-folded-domain.lean` **compiles clean**:
  - `R5Probe.frsCode_eq_map_rsCode : frsCode domain k s ω = (ReedSolomon.code (foldedDomain …) k).map (LinearEquiv.curry F F ι (Fin s)).toLinearMap` (≈15 lines);
  - `R5Probe.dim_frsCode'` — same conclusion as `dim_frsCode`, 4 lines, **and it does not
    need the `[NeZero k]` instance that ArkLib's `dim_frsCode` carries** (see LOW below).
- **Refutation attempt**: I checked whether the block metric blocks the reuse — it does
  for `minDist_frsCode` (block-Hamming ≠ symbol-Hamming, so `ReedSolomon.minDist_of_le`
  genuinely cannot be transported and re-proving it is correct), but **not** for the
  dimension/injectivity half, which is metric-free. I also checked that
  `LinearEquiv.curry` exists in Mathlib (`Mathlib/Algebra/Module/Equiv/Basic.lean:464`).
- **Suggested fix**: add `frsCode_eq_map_rsCode` (or an `frsCode ≃ₗ RS-on-folded-domain`
  form) to `Folded.lean`; derive `dim_frsCode` from it and drop `[NeZero k]`.

---

### [MEDIUM] The faithfulness audit records `Admissible` as a plain transcription of Def 2.14, with no mention of the deliberate strengthening

- **Where**: `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md:43`
  ```
  | `D2.14` | `(L,s)`-admissible field element | present | […Folded.lean] |
    `ReedSolomon.Folded.Admissible` | Required by D2.15. |
  ```
- **What's wrong**: this table is the PR's faithfulness ledger — "present" there reads as
  "faithfully transcribed". The Lean docstring is scrupulous about the deviation
  (`Folded.lean:64-76`), but the audit row is silent, so a reader consulting the ledger
  (the intended entry point per `docs/wiki/README.md`) will not learn that every ArkLib
  theorem quantified over `Admissible` is **strictly weaker** than the corresponding
  ABF26 statement. Given that the deviation is *provably necessary* (see the brute-force
  table above), it deserves a ledger row, not only a docstring paragraph.
- **Evidence**: quoted row above; contrast `Folded.lean:64-71` ("Deviation from the
  paper's literal text … This is a deliberate strengthening, not a verbatim
  transcription.").
- **Refutation attempt**: I searched the whole audit file and `docs/wiki/*` for any other
  mention of the strengthening (`grep -rn "strengthen\|intra-orbit\|ω = 1\|omega = 1" docs/`)
  — none.
- **Suggested fix**: add to the D2.14 row: "**Strengthened**: Lean adds an intra-orbit
  clause `α·ω^i ≠ α (0<i<s)`; the paper's literal Def 2.14 admits `ω = 1`, under which
  the FRS distance claim is false (counterexample: `ZMod 11`, `L` = QR subgroup, `s = 2`,
  `k = 2` → true `d = 4`, formula `5`). Hypothesis position only ⇒ all downstream
  theorems are weaker than ABF26's, never stronger."

---

### [LOW] Superfluous instance/hypothesis binders: `[NeZero k]` on `dim_frsCode` and `frsEvalOnPoints_domRestrict_injective`, `[Nonempty ι]` on `dim_irsCode`/`dim_irsCode_of_dvd`

- **Where**: `Folded.lean:182`, `Folded.lean:213`; `Interleaved.lean:70`, `:120`.
- **Evidence**: `R5-frs-is-rs-on-folded-domain.lean → dim_frsCode'` proves the same
  conclusion with no `[NeZero k]`; `R5-interleaved-general.lean → dim_irsCode'` proves the
  same conclusion with no `[Nonempty ι]`. Both compile.
- **Note (not a defect)**: `[NeZero k]` on `minDist_frsCode` **is** load-bearing — at
  `k = 0` the code is `⊥`, `minWtCodewords = sInf ∅ = 0`, while the RHS is `|ι| ≠ 0`.
  Likewise `hk : k ≤ s * |ι|` is genuinely tight: `(session-local probe) R5-tightness.lean`
  compiles `encoder_not_injective_at_k_eq_11`, exhibiting nonzero `X^10 − 1 ∈ degreeLT 11`
  killed by the encoder at `k = s·|ι| + 1 = 11`.
- **Suggested fix**: drop the three superfluous binders.

---

### [LOW] `Admissible`'s second conjunct is written in an order that defeats `Nat.decidableBallLT`, so concrete admissibility cannot be discharged by `decide`

- **Where**: `Folded.lean:80` — `∀ α ∈ L, ∀ i : ℕ, 0 < i → i < s → α * ω ^ i ≠ α`.
- **Evidence**: `decide` on `Admissible (univ.map dom5) 2 2` fails with
  `failed to synthesize Decidable (… ∧ ∀ α ∈ …, ∀ (i : ℕ), 0 < i → i < 2 → …)` (first two
  iterations of `R5-admissible-witness.lean`); the *first* conjunct, written `∀ i < s, …`,
  **is** decidable and `by decide` closes it. The witness had to be hand-massaged
  (`intro …; interval_cases i; revert; decide`).
- **Suggested fix**: reorder to `∀ α ∈ L, ∀ i < s, 0 < i → α * ω ^ i ≠ α` (definitionally
  the same predicate) so users get `by decide` on concrete parameters. Optionally add a
  `Decidable` instance / `Fintype`-based reformulation.

---

### [LOW] "MDS" in the `minDist_frsCode` docstring is exact only when `s ∣ k`, under ABF26's own definition of MDS

- **Where**: `Folded.lean:230` ("the folded code is MDS in the block (per-fold) Hamming
  metric").
- **Source**: ABF26 Lemma 2.6 (`ABF26.txt:366-372`): "We say that a code `C` is maximum
  distance separable (MDS) if `ρ(C) = 1 − δmin(C) + 1/n`", with `ρ(C) = log_{|Σ|}|C| / n`
  (Def 2.5). For FRS, `Σ = F^s`, `|C| = |F|^k`, so `ρ = k/(sn)` and ABF26-MDS would force
  `d = n − k/s + 1`; the truth (and the Lean statement) is `d = n − ⌈k/s⌉ + 1`, equal only
  when `s ∣ k`. (The code *does* meet the **integer** Singleton bound
  `d ≤ n − ⌈log_{|Σ|}|C|⌉ + 1` exactly, so the claim is defensible under that reading —
  hence LOW, not MEDIUM.)
- **Suggested fix**: say "meets the integer Singleton bound `n − ⌈k/s⌉ + 1`; MDS in
  ABF26's sense exactly when `s ∣ k`."

---

### [LOW] Stale audit sentence: `dim_frsCode`'s "`h_encoder_inj` awaited"

- **Where**: `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md:44`
  — "…(`Admissible ∧ ω≠0 ∧ k ≤ s·|ι| ⇒` encoder injective — the `Admissible → injective`
  bridge `dim_frsCode`'s `h_encoder_inj` awaited)…".
- **What's wrong**: `dim_frsCode` exists and is proved in this PR (`Folded.lean:211`) and
  has **no** `h_encoder_inj` parameter; it takes `hadm`/`hω`/`hk` directly. The row also
  omits `dim_frsCode` from its list of proved bridges.
- **Suggested fix**: replace with "`dim_frsCode` (`finrank = k`, proved)".

---

### [LOW] `SubspaceDesign.lean`'s "Deferred" note says multiplicity codes "require a separate `D_ux` operation" — this PR defines them

- **Where**: `ArkLib/Data/CodingTheory/SubspaceDesign.lean:37-38`:
  "Univariate multiplicity codes `UM[F, L, k, s]` are referenced in T2.18 but require a
  separate `D_ux` (derivative-of-x) operation; tracked under ABF26-D2.19 / DA.7."
- **What's wrong**: the same PR ships `ReedSolomon.Multiplicity.umCode` /
  `umEvalOnPoints` (built on iterated `Polynomial.derivative`), so the definition is no
  longer missing. What is actually deferred is the *GK16 multiplicity-Wronskian proof*,
  not the `D_ux` definition. Minor internal inconsistency between two files in one PR.
- **Suggested fix**: reword to "the multiplicity half of T2.18 is deferred: the code is
  defined (`ReedSolomon.Multiplicity.umCode`) but the GK16 multiplicity-Wronskian argument
  is not formalised."

---

### [LOW] Module-docstring "Main lemmas" lists are incomplete

- `Folded.lean:21-28` omits `minDist_frsCode` — the file's headline theorem (250 of its
  499 lines) — and `admissible_foldedPoints_injective`.
- `Interleaved.lean:22-25` omits `dim_irsCode_of_dvd`.
- `Folded.lean:25` describes `dim_frsCode` as holding "under FRS encoder injectivity",
  but the actual hypotheses are `Admissible ∧ ω ≠ 0 ∧ k ≤ s·|ι|`.

---

## Clean bill (checked, genuinely OK)

**Faithfulness — clause by clause**

- **ABF26 Def 2.13** (`ABF26.txt:445`, `IRS[F,L,k,s] := (RS[F,L,k/s])^{≡s}`) vs
  `Interleaved.irsCode`: **faithful**. `^⋈` = `ModuleCode.moduleInterleavedCode`
  (`InterleavedCode.lean:149`) whose carrier is `interleavedCodeSet`
  (`{V | ∀ k, V.transpose k ∈ C}`) = ABF26 Def 2.9's "each row is a codeword of `C`"
  (`ABF26.txt:399-403`). **No fork**: `irsCode` re-derives nothing; it is literally
  `(ReedSolomon.code domain (k/s)) ^⋈ (Fin s)`. The `k/s` Nat-truncation deviation is
  explicitly documented (`Interleaved.lean:52-58`) and `dim_irsCode_of_dvd` supplies the
  paper-shaped `s ∣ k` version.
- **ABF26 Def 2.14** (`ABF26.txt:457`) vs `Folded.Admissible`: strengthened, see above;
  the strengthening is documented, hypothesis-position-only, satisfiable, and necessary.
- **ABF26 Def 2.15 [GR08]** (`ABF26.txt:464`) vs `Folded.frsCode`: **faithful**. Fold is
  `f̂(x·ω^j)`, `0 ≤ j < s`, degree bound `< k` unchanged, alphabet `F^s`, carrier
  `Submodule F (ι → Fin s → F)`. Matches GR08 Def 2.1 (`GuruswamiR08.txt:399`) with
  GR08's `γ ↦ ω`, `m ↦ s`, and GR08's folded domain `{γ^{jm}}` ↦ ArkLib's `domain`.
  The fold is `ω^j·x`, **not** `x^{q^j}` (that is the Frobenius/AG variant — not what
  either source uses). No coset/orbit-union structure is required of `domain` by either
  source; smoothness (ABF26 Def 2.12) is orthogonal.
  ABF26's remark "`FRS[F,L,k,1,ω] = RS[F,L,k]`" is discharged by
  `mem_frsCode_one_iff_mem_rsCode` and `frsCode_one_map_eq_rsCode` (correct: for `s ≤ 1`
  `Admissible` is unconditionally true, and both lemmas are `Admissible`-free).
- **ABF26 Def A.6 / A.7** (`ABF26.txt:2227-2250`) vs `Multiplicity.umEvalOnPoints` /
  `umCode`: **faithful**. *Crucially, ABF26 A.6 uses the ORDINARY formal derivative*
  (`f̂'(X) = ∑_{i=1}^{k-1} (a_i·i)·X^{i-1}`, iterated recursively), **not** the Hasse
  derivative, with the global side condition `char(F) ≥ k`. So `Polynomial.derivative^[j]`
  is the *correct* transcription and there is **no** small-characteristic correctness bug
  and **no** Mathlib `hasseDeriv` duplication. The `char(F) ≥ k` condition is documented
  (`Multiplicity.lean:33-40`) and deliberately not baked into the definition; the
  justification given ("`(a_i·i)` do not vanish below degree `k`") is exactly the paper's.
  No pre-existing multiplicity code anywhere in `ArkLib/` or Mathlib
  (`grep -rn "hasseDeriv\|multiplicityCode\|derivative^\["` → only the unrelated bivariate
  `GuruswamiSudan.hasseDerivEvalAt`).
- **Rate convention**: `Folded.lean:209` "`ρ = k/(s·n)`" is correct under ABF26 Def 2.5
  (`ρ = log_{|Σ|}|C| / n` with `Σ = F^s`), and is consistent with `SubspaceDesign.lean`'s
  `τ(r) = k/(n(s−r+1)) = sρ/(s−r+1)` = ABF26 T2.18.

**Mathematics — independently re-derived**

- `dim_frsCode` (`= k`): correct. Injectivity needs exactly `k − 1 < s·|ι|`, i.e.
  `k ≤ s·|ι|` — tight (probe `R5-tightness.lean`). Compiled non-vacuous instances at
  `(ZMod 11, n=5, s=2, k∈{3,7})` and `(ZMod 17, n=4, s=4, k=8)`.
- `minDist_frsCode` (`= |ι| − ⌊(k−1)/s⌋`): **correct, and equal to `n − ⌈k/s⌉ + 1`** for
  `k ≥ 1` (checked both branches `s ∣ k` and `s ∤ k`). Independently confirmed by
  exhaustive brute force over all message polynomials at **22 parameter points**
  (`R5-mindist-bruteforce.py`): `(q,n,s,ω) = (11,5,2,2) k=1..6`, `(7,2,3,3) k=1..6`,
  `(5,2,2,2) k=1..4`, `(13,3,2,5) k=1..6` — **every one matches**, including the
  `s ∤ k` cases that a `⌈k/s⌉`-vs-`⌊(k−1)/s⌋` slip would break.
  The metric is genuinely the block metric (`Code.minDist` over `Set (ι → (Fin s → F))`,
  `Distance.lean:217` + `LinearCode.dist_eq_minWtCodewords`).
- Both directions of the `minDist` proof read correctly: lower bound = `s·#zeroFolds ≤
  deg p ≤ k−1` via `Finset.card_le_card_of_injOn` on `admissible_foldedPoints_injective`;
  upper bound = explicit `∏_{(x,j) ∈ T×Fin s} (X − domain x·ω^j)` of degree
  `s·⌊(k−1)/s⌋ ≤ k−1 < k`. No `Nat`-subtraction trap: `hdiv_lt : (k−1)/s < |ι|` is
  established from `hk` + `NeZero k` before any subtraction is used.
- `admissible_foldedPoints_injective`: proof is real; the ordered-exponent `key` lemma
  uses both conjuncts, both at exponent `n − m` with `n − m ≤ n < s` correctly checked.
  `Admissible ∧ ω ≠ 0 ⟺ injectivity` (I verified the converse direction on paper too);
  the separate `ω ≠ 0` side condition is necessary and is documented (`Folded.lean:73-76`).
- `frsEvalOnPoints_domRestrict_injective`: real proof via
  `Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero`; hypotheses exactly what is
  needed (modulo the superfluous `[NeZero k]` above).
- `mem_frsCode_iff`, `mem_frsCode_iff_flipped`, `mem_frsCode_one_iff_mem_rsCode`,
  `frsCode_one_map_eq_rsCode`, `Multiplicity.mem_umCode_one_iff_mem_rsCode`: all correct,
  no `simp`-cheats, no degenerate instantiation.
- No `sorry` in any of the three files. `#print axioms` on all 9 non-`def` results:
  `[propext, Classical.choice, Quot.sound]` only (`(session-local probe) R5-axioms.lean`).

**Naming / placement / no-overlap (scope item 7) — claim VERIFIED TRUE**

- `ProximityGap/Folding.lean`'s "folded RS-code" really is a *plain RS code on a shrunken
  domain*: `foldWord_mem_code_of_mem_code` / `iteratedFoldWord_mem_code_of_mem_code` land
  in `ReedSolomon.code (domain.subdomain k) (d / 2^k)` (lines 387-397, 449-460). The
  domain shrinks and the degree bound drops — the opposite of GR08 folding, where the
  degree bound is unchanged and the alphabet grows. `Data/Polynomial/SplitFold.splitNth`
  and `Data/Polynomial/FoldingPolynomial.polyFold` (`f ↦ (foldingPolynomial (X^k) f).eval
  (C r)`) are FRI split-and-fold, also unrelated. `ProximityGap/Folding/Multilinear.lean`
  likewise. **No overlap; the `Folded.lean:30-39` "Not the FRI fold" disambiguation
  paragraph is accurate.**
- `ReedSolomon.lean` (764 lines, untouched): contains no folded/interleaved/multiplicity
  material, so nothing is duplicated. The new code correctly consumes main's post-#663
  API — `ReedSolomon.dim_eq_deg_of_le` (`Interleaved.lean:115`) and
  `ReedSolomon.natDegree_lt_of_mem_degreeLT` (`Folded.lean:200,417`).
  `ReedSolomon.minDist_of_le` is *correctly* not reused (different metric).
- Namespacing (`ReedSolomon.Folded.*`, `ReedSolomon.Interleaved.*`,
  `ReedSolomon.Multiplicity.*`) matches `docs/wiki/coding-theory-conventions.md:170-181`;
  the `set_option linter.unused*` suppressions match 10 other pre-existing
  `ArkLib/Data/**` files, so they are idiomatic here (though the underlying unused
  `[DecidableEq F]`/`[DecidableEq ι]`/`[Fintype ι]` binders on `Admissible`,
  `frsCode`, `frsEvalOnPoints` could simply be deleted).
- All three modules are correctly registered in the generated `ArkLib.lean` (lines
  116/117/119).

**Not defects, but worth the reviewer's note**

- `umCode`, `irsCode`, `dim_irsCode`, `dim_irsCode_of_dvd`, `dim_frsCode`,
  `minDist_frsCode` currently have **zero in-repo consumers**; only `frsCode`,
  `mem_frsCode_iff`, `frsEvalOnPoints` and `frsEvalOnPoints_domRestrict_injective` are
  used (all by `SubspaceDesign.lean`). Acceptable for a split-out library PR.
