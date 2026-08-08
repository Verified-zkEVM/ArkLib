# R8 — NO-DUPLICATION / MISSED-GENERALIZATION axis (PR #701 @ `ffa0733a` vs `origin/main`)

Scope: every declaration the PR adds (110 new decls across 22 `.lean` files, inventory in
`R8-new-decls.txt`), compared semantically against `origin/main`'s
`ArkLib/Data/{CodingTheory,Polynomial,Probability,Fin,MvPolynomial}/**`, `ArkLib/ToMathlib/**`,
and Mathlib.

All findings below are backed by a **compiled probe**. Probes live in `(session-local probe) `:
`R8-dup1.lean`, `R8-dup2.lean`, `R8-dup3.lean`, `R8-dup4.lean` — all four compile clean with
`lake env lean` (no `sorry`, no errors).

## Verdict summary

| # | Severity | Class | One-liner |
|---|---|---|---|
| D1 | HIGH | DUPLICATE | `JohnsonBound.Jqℓ` is the pre-existing `JohnsonBound.J` at a rescaled radius |
| D2 | HIGH | DUPLICATE | `JohnsonBound.remap`/`remap_injective`/`remap_hammingDist` are Mathlib's `Equiv.piCongrRight` / `Equiv.injective` / `hammingDist_comp` — which the *same PR* uses correctly in `ExtensionCodes.lean` |
| D3 | MEDIUM | GENERALIZE | `dim_irsCode`'s proof is 100% RS-independent; the general `finrank (MC ^⋈ κ) = |κ| · finrank MC` belongs in `InterleavedCode.lean` |
| D4 | MEDIUM | GENERALIZE | `Folded.mem_frsCode_one_iff_mem_rsCode` and `Multiplicity.mem_umCode_one_iff_mem_rsCode` are the same lemma written twice |
| D5 | MEDIUM | GENERALIZE | `eq_of_consistent_with_erased` is the `Option`-clothed case of a projection-injectivity lemma that belongs next to the pre-existing `LinearCode.projectedWord` |
| D6 | MEDIUM | GENERALIZE | `Code.disagreementCols` and the pre-existing `Matrix.neqCols` are the same primitive; no bridge is stated |
| D7 | MEDIUM | PLACEMENT | 8 Mathlib-generic declarations sit outside `ArkLib/ToMathlib/`, one of them self-admittedly |
| D8 | MEDIUM | NAMESPACE | PR introduces a *new* top-level `CodingTheory` namespace that has no precedent on `main`, and a *second* probability namespace `Probability` next to the existing `ProbabilityTheory` in the same directory |
| D9 | LOW | DUPLICATE | `JohnsonBound.Jcap` re-names an expression already spelled out in `JohnsonBound.sqrt_le_J`; zero consumers |
| D10 | LOW | GENERALIZE | `qEntropy` restates the three `logb` terms instead of being *defined* as `Real.qaryEntropy q x / Real.log q`; zero consumers |
| D11 | LOW | GENERALIZE | `singleton_bound_module` subsumes `singleton_bound_linear` over finite fields but the latter is not restated as a corollary |
| D12 | LOW | STYLE | `ExtensionFieldPresentation` adds nothing over Mathlib's `Basis (Fin e) B F` |
| D13 | LOW | SCOPE | `Fin.induction_three`/`induction_three'`: two new `@[simp]` `rfl` lemmas with zero consumers, unrelated to the PR's subject |
| D14 | LOW | COHERENCE | The PR now carries **three** different Hamming-distance transport idioms added/used in three files |

Counts: **2 HIGH, 5 MEDIUM, 7 LOW.** No CRITICAL on this axis.

---

### [HIGH] D1 — `JohnsonBound.Jqℓ` is the pre-existing `JohnsonBound.J` at a rescaled radius

- **Where**: `ArkLib/Data/CodingTheory/JohnsonBound/Family.lean:73` (`JohnsonBound.Jqℓ`)
- **Existing**: `ArkLib/Data/CodingTheory/JohnsonBound/Basic.lean:52` (`JohnsonBound.J`)
  (and its *already-duplicated* twin `ArkLib/Data/CodingTheory/JohnsonBound/Lemmas.lean:15`,
  `JohnsonBound.J'`, whose body is character-for-character identical to `J`'s — pre-existing,
  not this PR's doing).
- **What's wrong**: the two definitions are

  ```
  J   q δ     = (1/frac)     * (1 - √(1 - frac * δ))            -- frac := q/(q-1)
  Jqℓ q ℓ δ   = (1 - 1/q)    * (1 - √(1 - frac * lFac * δ))     -- lFac := (ℓ-1)/ℓ
  ```

  `1 - 1/q = (q-1)/q = 1/frac`, so `Jqℓ q ℓ δ = J q (((ℓ-1)/ℓ) * δ)` for every `q ≠ 0`.
  The list parameter is a pure reparametrisation of the radius, not new content. The PR's
  module docstring only claims `Jqℓ q ℓ δ → J q δ` as `ℓ → ∞`; it does not notice the exact
  identity, and no bridge lemma exists in the file. Every `Jqℓ` fact then has to be re-proved
  from scratch (and `johnson_card_le_ell` does re-derive `hradius_eq`,
  `hfrac_radius`, … at `Family.lean:160-190`, all of which are `J`-facts).
- **Evidence** (`(session-local probe) R8-dup1.lean`, compiles):
  ```lean
  theorem Jql_eq_J (q ℓ δ : ℚ) (hq : q ≠ 0) :
      JohnsonBound.Jqℓ q ℓ δ = JohnsonBound.J q (((ℓ - 1) / ℓ) * δ) := by
    unfold JohnsonBound.Jqℓ JohnsonBound.J
    simp only
    congr 2
    · push_cast; field_simp
    · push_cast; congr 1; ring
  ```
- **Refutation attempt**: I checked whether the coefficients genuinely differ. They do differ
  at `q = 0` only (`1 - 1/0 = 1` vs `1/(0/(0-1)) = 0`), which is outside any coding-theory
  regime and is not guarded anywhere in the file. I also checked whether `Jqℓ` puts `lFac`
  outside the square root in some branch — it does not; it is inside, exactly as a radius
  rescale. So the reduction is exact wherever it matters.
- **Suggested fix**: either (a) delete `Jqℓ` and write `J q ((ℓ-1)/ℓ * δ)` at the two use
  sites, or (b) keep it as `def Jqℓ q ℓ δ := J q (((ℓ-1)/ℓ) * δ)` and add
  `Jqℓ_eq_J` as an `@[simp]` unfolding, so the existing `J` API (`sqrt_le_J`,
  `johnson_e_div_ne_J`, …) is reachable. Separately, `J'` should be `deprecated alias J`.

---

### [HIGH] D2 — `JohnsonBound.remap` and its three lemmas are Mathlib, restated

- **Where**: `ArkLib/Data/CodingTheory/JohnsonBound/Expectations.lean:146` (`remap`),
  `:150` (`remap_injective`), `:158` (`remap_hammingDist`)
- **Existing**: Mathlib `Equiv.piCongrRight`, `Equiv.injective`, and
  `hammingDist_comp` (`.lake/packages/mathlib/Mathlib/InformationTheory/Hamming.lean:120`):
  ```
  theorem hammingDist_comp (f : ∀ i, γ i → β i) {x y : ∀ i, γ i} (hf : ∀ i, Injective (f i)) :
      hammingDist (fun i => f i (x i)) (fun i => f i (y i)) = hammingDist x y
  ```
- **What's wrong**: `remap σ x = fun i => σ i (x i)` **is** `Equiv.piCongrRight σ x` — the two
  are `rfl`-equal. `remap_hammingDist` is a direct instance of `hammingDist_comp`.
  This is the sharpest instance of the mandate's near-miss class, because the *same PR*
  already uses both Mathlib lemmas correctly in another file:
  `ArkLib/Data/CodingTheory/ExtensionCodes.lean:323` writes
  `set Ψ := Equiv.piCongrRight (fun _ => P.φ.toEquiv)` and `:328` writes
  `hammingDist_comp (fun (_ : ι) => (P.φ : F → (Fin P.e → B))) (fun _ => hφinj)`.
  So the PR knows the Mathlib idiom and reimplements it 200 lines away.
- **Evidence** (`(session-local probe) R8-dup1.lean`, compiles):
  ```lean
  example (σ : Fin n → (F ≃ G)) (x : Fin n → F) :
      JohnsonBound.remap σ x = Equiv.piCongrRight σ x := rfl
  example (σ : Fin n → (F ≃ G)) (x y : Fin n → F) :
      hammingDist (JohnsonBound.remap σ x) (JohnsonBound.remap σ y) = hammingDist x y :=
    hammingDist_comp (fun i => (σ i : F → G)) (fun i => (σ i).injective)
  example (σ : Fin n → (F ≃ G)) : Function.Injective (JohnsonBound.remap σ) :=
    (Equiv.piCongrRight σ).injective
  ```
- **Refutation attempt**: I checked whether `remap`'s `Fin n`-indexed, non-dependent shape
  buys anything over `Equiv.piCongrRight`'s dependent one — it does not; the probe is `rfl`.
  I also checked whether the `remap_e` / `remap_d` / `remap_image_card` lemmas (which *are*
  new content, about `JohnsonBound.e`/`d`) need the standalone name: they can be stated over
  `Equiv.piCongrRight σ` verbatim. And I confirmed `remap` is genuinely consumed
  (`JohnsonBound/Lemmas.lean:434-441`), so this is not a dead-code complaint — the consumers
  should just use the Mathlib equiv.
- **Suggested fix**: delete `remap`, `remap_injective`, `remap_hammingDist`; keep
  `remap_e`/`remap_d`/`remap_image_card` restated over `Equiv.piCongrRight σ`, proving the
  distance step with `hammingDist_comp`.

---

### [MEDIUM] D3 — `dim_irsCode` hides a general `InterleavedCode` lemma

- **Where**: `ArkLib/Data/CodingTheory/ReedSolomon/Interleaved.lean:70` (`dim_irsCode`)
- **Existing**: `ArkLib/Data/CodingTheory/InterleavedCode.lean` — the whole `^⋈` layer, which
  has **no** `finrank` lemma at all (`grep -nE "finrank" InterleavedCode.lean` → 0 hits).
- **What's wrong**: the 40-line proof at `Interleaved.lean:75-115` builds an injective
  `(Fin s → ↥RS) →ₗ[F] (ι → Fin s → F)`, identifies its range with the interleave, and applies
  `Module.finrank_pi_fintype`. Not one step of that uses Reed–Solomon; the only RS-specific
  line is the last (`ReedSolomon.dim_eq_deg_of_le`). The general statement
  `finrank F (MC ^⋈ κ) = Fintype.card κ * finrank F MC` is exactly the missing
  `InterleavedCode` lemma, and it is what any other interleaved code family (e.g. the
  `interleavedCodeSet` consumers in `ProximityGap/DG25`, `MCAGenerator`) will need next.
- **Evidence** (`(session-local probe) R8-dup2.lean`, compiles): the general lemma
  `finrank_moduleInterleavedCode` is proved by transcribing the PR's own proof with `RS`
  replaced by an abstract `MC : ModuleCode ι F A` (plus `[Module.Finite F ↥MC]`), and then
  ```lean
  example … : Module.finrank F (ReedSolomon.Interleaved.irsCode domain k s) = s * (k / s) := by
    rw [ReedSolomon.Interleaved.irsCode, finrank_moduleInterleavedCode, Fintype.card_fin]
    exact congrArg (s * ·) (ReedSolomon.dim_eq_deg_of_le (n := k/s) (α := domain) h_rs_full)
  ```
  i.e. the PR's 45-line lemma collapses to two lines.
- **Refutation attempt**: I tried to find an RS-specific ingredient in the proof (e.g. a
  `domain` injectivity use, a degree argument). There is none; only the closing rewrite. I
  also checked the general lemma needs a finiteness side-condition the RS case gets for free
  (`[Module.Finite F ↥MC]`), which is the only added hypothesis — and it is discharged
  automatically at `A = F`, `ι` finite.
- **Suggested fix**: move the general lemma into `InterleavedCode.lean` (e.g.
  `ModuleCode.finrank_moduleInterleavedCode`), make `dim_irsCode` a corollary, and reuse the
  general one for `frsCode`/`umCode` interleaves later.

---

### [MEDIUM] D4 — the two `s = 1` collapse lemmas are one lemma written twice

- **Where**: `ArkLib/Data/CodingTheory/ReedSolomon/Folded.lean:453`
  (`mem_frsCode_one_iff_mem_rsCode`) and
  `ArkLib/Data/CodingTheory/ReedSolomon/Multiplicity.lean:114`
  (`Multiplicity.mem_umCode_one_iff_mem_rsCode`)
- **What's wrong**: both codes are `(Polynomial.degreeLT F k).map enc` for an encoder into
  `ι → Fin s → F`, and both collapse lemmas have the *same* proof skeleton
  (`rintro ⟨p, hp, …⟩` / `funext` / `Subsingleton.elim` / `simpa`). A single generic lemma
  parameterised by the encoder covers both, and will also cover the next member of the family
  (the module docstrings of `Folded.lean` and `Multiplicity.lean` both promise more).
  Beyond the collapse lemma, the whole `evalOnPoints`/`code` ↔ `frsEvalOnPoints`/`frsCode` ↔
  `umEvalOnPoints`/`umCode` triple is three copies of one construction; the `dim_*` lemmas
  (`ReedSolomon.dim_eq_deg_of_le` at `ReedSolomon.lean:236` and `dim_frsCode` at
  `Folded.lean:211`) likewise repeat the same
  `h_range` → `LinearMap.finrank_range_of_inj` → `Polynomial.finrank_degreeLT_n` chain verbatim.
- **Evidence** (`(session-local probe) R8-dup3.lean`, compiles):
  ```lean
  theorem mem_map_one_iff_mem_rsCode (domain : ι ↪ F) (k : ℕ) (enc : F[X] →ₗ[F] (ι → Fin 1 → F))
      (henc : ∀ p i, enc p i 0 = p.eval (domain i)) (f : ι → Fin 1 → F) :
      f ∈ (Polynomial.degreeLT F k).map enc ↔ (fun i ↦ f i 0) ∈ ReedSolomon.code domain k
  ```
  followed by both PR lemmas derived from it in one line each.
- **Refutation attempt**: I checked whether the `Field`/`CommRing` typeclass split the PR
  invokes (`Multiplicity.lean:110-113` explains a `Polynomial`-`Semiring` instance clash)
  forces two lemmas. It does not: the generic lemma is stated at `[Field F]` and both
  instances typecheck against it, including the `umCode` one whose file otherwise runs at
  `[CommRing F]`.
- **Suggested fix**: put `mem_map_one_iff_mem_rsCode` (and a
  `finrank_map_degreeLT_of_inj` companion) in `ReedSolomon.lean`, derive all three families
  from them.

---

### [MEDIUM] D5 — `eq_of_consistent_with_erased` should be a `projectedWord` injectivity lemma

- **Where**: `ArkLib/Data/CodingTheory/Erasure.lean:83` (`eq_of_consistent_with_erased`)
- **Existing**: `ArkLib/Data/CodingTheory/Basic/LinearCode.lean:259` (`projectedWord`),
  `:264` (`projectedCode`), `:271` (`projectedCodeSubmod`) — the established ArkLib
  vocabulary for "restrict a word to a coordinate subset", actively consumed by
  `ProximityGap/AffineGenerator.lean` and `ProximityGap/MCAGenerator.lean`.
- **What's wrong**: the mathematical content of the lemma (and of the whole
  `SupportsErasureCorrection` file) is *"projection to a coordinate set whose complement is
  smaller than `minDist` is injective on the code"*. The PR states it only in `Option`-encoded
  form, so it is invisible to the `projectedCode` users who need exactly the same fact, and
  the erasure file re-derives the disagreement-set pigeonhole in-place.
- **Evidence** (`(session-local probe) R8-dup4.lean`, compiles): the general lemma
  ```lean
  theorem projectedWord_inj_of_compl_card_lt_minDist
      (hu : u ∈ C) (hv : v ∈ C) (hproj : projectedWord u T = projectedWord v T)
      (hcard : Tᶜ.card < Code.minDist C) : u = v
  ```
  is proved by the PR's own three lines, and the PR's `eq_of_consistent_with_erased` is then
  derived from it by instantiating `T := {i | f i ≠ none}`.
- **Refutation attempt**: I checked whether `Option`-valued partial words carry information
  the `Finset`-indexed projection loses (e.g. "erasure locations known to the decoder"). They
  do not for *this* lemma: the two hypotheses `hfu`/`hfv` only say the words agree on the
  non-`none` set. The `Option` encoding is still the right interface for
  `SupportsErasureCorrection` itself (the decoder input); only the uniqueness core generalizes.
- **Suggested fix**: state the general lemma in `Basic/LinearCode.lean` next to
  `projectedCode`, and make `eq_of_consistent_with_erased` a one-line corollary.

---

### [MEDIUM] D6 — `Code.disagreementCols` vs the pre-existing `Matrix.neqCols`

- **Where**: `ArkLib/Data/CodingTheory/Basic/Distance.lean:149` (`Code.disagreementCols`)
- **Existing**: `ArkLib/Data/CodingTheory/Prelims.lean:50`
  (`Matrix.neqCols U V = {j | ∃ i, V i j ≠ U i j}`)
- **What's wrong**: `neqCols` is exactly `disagreementCols` applied to the transposes —
  the matrix/interleaved instance of the same primitive. The PR's docstring for
  `disagreementCols` carefully enumerates the *other* paper-shape variants
  (`Binius/BinaryBasefold/Prelude.lean:1042`, `Stir/Quotienting.lean:52`,
  `Basic/BlockRelDistance.lean:42`, `ProximityGap/DG25/MainResults.lean:57`) and explains why
  they stay specialised — but it misses `Matrix.neqCols`, the one that really *is* the same
  function, and no bridge lemma is stated.
- **Evidence** (`(session-local probe) R8-dup3.lean`, compiles):
  ```lean
  example (U V : Matrix ι ι' F) :
      Matrix.neqCols U V = Code.disagreementCols (Matrix.transpose U) (Matrix.transpose V)
  ```
- **Refutation attempt**: I checked the four other `disagreementSet`s named in the docstring.
  All four genuinely carry extra structure (block fibers, `Ans`-tables, interleaved 4-tuples),
  so the PR's "intentional specialisations" claim holds for them — this finding is *only*
  about `Matrix.neqCols`, which the docstring omits.
- **Suggested fix**: add `Matrix.neqCols_eq_disagreementCols_transpose` (one `ext`), or
  redefine `neqCols` in terms of `disagreementCols`.

---

### [MEDIUM] D7 — Mathlib-generic declarations outside `ArkLib/ToMathlib/`

`AGENTS.md`: *"`ArkLib/ToMathlib/` — local extensions intended for upstreaming."*
The following new declarations mention no coding-theory, no ABF26 and no ArkLib concept:

| New decl | Where | Should live in |
|---|---|---|
| `Polynomial.pow_dvd_det_of_forall_mem_col_dvd` | `Data/Polynomial/FoldedWronskian.lean:103` | `ToMathlib/` — and it is a **`Matrix`** lemma over an arbitrary `CommRing`, wrongly placed in namespace `Polynomial` (its statement contains no polynomial) |
| `Polynomial.natDegree_comp_C_mul_X_le` | `FoldedWronskian.lean:66` | `ToMathlib/Polynomial/` (a `NatDegreeOfSum.lean` sibling already exists) |
| `expand_card_pow`, `aeval_pow_card_pow`, `pow_card_pow_eq` | `FoldedWronskian.lean:137,147,154` | `ToMathlib/` — pure finite-field Frobenius |
| `X_pow_card_sub_one_sub_C_irreducible` | `FoldedWronskian.lean:181` | `ToMathlib/` — a genuine Kummer-criterion gap in Mathlib (see "rejected" §R7); prime upstreaming candidate |
| `sum_rootMultiplicity_le_natDegree` | `CodingTheory/SubspaceDesign.lean:276` | `ToMathlib/Polynomial/` (verified absent from Mathlib by `loogle`) |
| `finrank_eq_of_map_eq`, `exists_adapted_basis` | `SubspaceDesign.lean:298,312` | `ToMathlib/` — pure linear algebra, currently `private` inside a coding-theory file |
| `MvPolynomial.totalDegree_le_of_degreeOf_lt` | `Data/Probability/Instances.lean` | `ToMathlib/MvPolynomial/`. **Self-admitted**: its own docstring says *"(Mathlib-extension candidate; … Would belong in `Mathlib/Algebra/MvPolynomial/Degrees.lean`)"* — yet it is declared `_root_` inside a *probability* file. |

Sub-finding: `finrank_eq_of_map_eq`'s **first** call site
(`SubspaceDesign.lean:380`, with `f := B.subtype`) is already Mathlib:
`Submodule.finrank_map_subtype_eq` (`Mathlib/LinearAlgebra/Dimension/Finrank.lean:132`).
Compiled in `(session-local probe) R8-dup4.lean`. The other two call sites (`:628`, `:679`, with a
general encoder injective only on `B`) do need the local lemma, so it is not wholly
redundant — but it should be `ToMathlib` material, not private coding-theory scaffolding.

---

### [MEDIUM] D8 — namespace fragmentation

**(a) A brand-new top-level `CodingTheory` namespace.** `git grep "namespace CodingTheory" origin/main -- ArkLib/` returns **nothing**. The tree's coding-theory decls live in
`Code` (Distance, LinearCode), `LinearCode`, `ListDecodable`, `JohnsonBound`, `ReedSolomon`,
`InterleavedCode`, `BlockRelDistance`, `CoreResults`, `DivergenceOfSets`, `ProximityGap`,
`Matrix`, or root. The PR adds `CodingTheory` as a *third* convention across six files
(`Basic/Entropy.lean`, `HammingBallVolume.lean`, `Erasure.lean`, `ExtensionCodes.lean`,
`SubspaceDesign.lean`, and the second half of `JohnsonBound/Family.lean`).

Concrete symptoms:
- `JohnsonBound/Family.lean` contains **two** namespaces: `JohnsonBound` (lines 57–96) and
  `CodingTheory` (98–859), in one 859-line file.
- `hammingBall` is `ListDecodable.hammingBall`; its volume counterpart is
  `CodingTheory.hammingBallVolume`; the bridging theorem
  `hammingBallVolume_eq_ncard_hammingBall` therefore crosses namespaces for no reason.
- `docs/wiki/coding-theory-conventions.md` (added by this PR) codifies the new layout and
  asserts *"`CodingTheory.*` for non-RS-specific definitions and predicates (`qEntropy`,
  `IsSubspaceDesign`, **`IsMDS`**, …)"* — but `IsMDS` is `LinearCode.IsMDS`
  (`Basic/LinearCode.lean:296`) and `grep "CodingTheory.IsMDS"` returns nothing. The wiki
  documents a policy the tree does not follow.

**(b) A second probability namespace.** `Data/Probability/Instances.lean` and
`Data/Probability/Combinatorial.lean` are put in `namespace Probability`, while the sibling
`Data/Probability/Notation.lean` (also edited by this PR, line 37) stays in
`namespace ProbabilityTheory` — where the PR adds `Pr_decide_eq_tsum_indicator`, whose own
docstring calls it a *"Specialisation of `Probability.prob_tsum_form_singleton`"*. So the
PR splits a two-lemma chain across two namespaces in the same directory. (Mathlib has no
`namespace Probability`, so there is no *clash*, but there is now no single home either.)

- **Suggested fix**: pick one. Either fold the new material into the existing `Code` /
  `ListDecodable` / `LinearCode` namespaces, or land a separate namespace-normalisation PR
  that moves the *existing* tree too — but not a third parallel convention. For probability,
  put `Pr_decide_eq_tsum_indicator` in `Probability` with the lemma it specialises.

---

### [LOW] D9 — `Jcap` renames an expression already present in the same directory

`JohnsonBound.Jcap δ := 1 - √(1 - δ)` (`Family.lean:88`) is literally the left-hand side of
the pre-existing `JohnsonBound.sqrt_le_J` (`Basic.lean:64`,
`1 - √(1 - δ) ≤ J q δ`). Verified `rfl` in `R8-dup1.lean`. `Jcap` has **zero** consumers in
the tree (only its own two `@[simp]` lemmas `Jcap_zero`/`Jcap_one`). Either restate
`sqrt_le_J` as `Jcap δ ≤ J q δ` — which is genuinely the paper's `J(δ) ≤ J_q(δ)` — or drop
`Jcap` until it has a consumer.

### [LOW] D10 — `qEntropy` should be defined through Mathlib's `qaryEntropy`

`CodingTheory.qEntropy` (`Basic/Entropy.lean:46`) spells out
`x·logb q (q-1) - x·logb q x - (1-x)·logb q (1-x)`. Mathlib has
`Real.qaryEntropy q p = p * log (q-1) + binEntropy p` (natural log), and the PR itself proves
`qEntropy q x = Real.qaryEntropy q x / Real.log q` (`:60`). Defining `qEntropy` *as* that
quotient would make the bridge `rfl` and inherit Mathlib's `binEntropy`/`qaryEntropy` API
(continuity, monotonicity, `strictMonoOn`) for free. Confirmed Mathlib has no base-`q`
variant, so the definition itself is not a duplicate. `qEntropy` currently has **zero**
consumers in the tree.

### [LOW] D11 — two Singleton bounds for linear codes, no link

`LinearCode.singleton_bound_module` (`Basic/LinearCode.lean:631`) is, at `A := F`
(`finrank F F = 1`), the statement `finrank ≤ card ι - (dist - 1)`, which implies the `dist`
form of the pre-existing `singleton_bound_linear` (`:589`, `finrank ≤ card ι - dist + 1`) and
is strictly stronger at `dist = 0`. The docstring claims the specialisation but the code does
not realise it: `singleton_bound_linear` keeps its 40-line independent proof. Mitigating: the
module version needs `[Finite F] [Finite A]`, the linear one only
`[CommRing F] [StrongRankCondition F]`, so neither strictly subsumes the other — hence LOW.
Suggested: add `singleton_bound_linear_of_finite` deriving the finite-field case from
`singleton_bound_module`, or at least a cross-reference.

### [LOW] D12 — `ExtensionFieldPresentation` adds nothing over `Basis`

`ExtensionCodes.lean:71`: `structure ExtensionFieldPresentation B F where e : ℕ;
basis : Basis (Fin e) B F`. Its own docstring calls it *"a thin structure on top of Mathlib's
existing `Algebra`/`Basis` machinery"*. Every consumer could take `(e : ℕ)
(b : Basis (Fin e) B F)` directly, or `[FiniteDimensional B F]` + `Module.finBasis`. Note
`ArkLib/ProofSystem/RingSwitching/Packing/Profile.lean:88` already carries a
`RingSwitchingProfile` with `basis : Basis (Fin κ → Fin 2) B L` — a *fatter* structure with
laws, so not a duplicate, but a reminder that ArkLib already has one basis-presentation
bundle and is now getting a second. Not a blocker; flagged for naming/API review.

### [LOW] D13 — `Fin.induction_three` / `induction_three'`: zero consumers, out of scope

`Data/Fin/Basic.lean:100,106`. Two `@[simp]` `rfl` lemmas continuing the existing
`induction_two`/`induction_two'` pattern. Neither is referenced anywhere in the tree
(`grep -rn induction_three ArkLib/` → the definitions only), and neither is used by anything
this PR adds. `induction_three'` differs from `induction_three` only in the numeral
representation of `3 : Fin 4` vs `last 3`. They are also derivable by three unfoldings of
`Fin.induction`'s successor equation. Consistent with the local family, so LOW — but they are
`Fin`-plumbing landing in a coding-theory data PR.

### [LOW] D14 — three Hamming-distance transport idioms in one PR

The PR simultaneously introduces/uses:
1. `JohnsonBound.remap_hammingDist` (`Expectations.lean:158`) — per-coordinate equivs,
2. `CodingTheory.reidx_hammingDist` (`Family.lean:107`) — precomposition by an index equiv,
3. Mathlib's `hammingDist_comp` (used at `ExtensionCodes.lean:328`).

(1) is (3) (finding D2). (2) is genuinely different (index reindexing, absent from Mathlib's
`InformationTheory/Hamming.lean`) and is worth keeping — but it should sit next to
`hammingDist` API in `Basic/Distance.lean` or `ToMathlib/`, not inside a Johnson-bound file,
and it should be stated for a general `Equiv ι ι'` rather than `ι ≃ Fin (card ι)`.

---

## Near-misses I CONSIDERED and REJECTED

| Candidate | Existing sibling | Why rejected |
|---|---|---|
| `Folded.frsCode` vs `ProximityGap/Folding.lean` (`foldWord`, `iteratedFoldWord`), `Polynomial/SplitFold.lean`, `Polynomial/FoldingPolynomial.lean` | — | Genuinely different constructions: GR08 alphabet-enlarging fold (degree bound unchanged, code in `ι → Fin s → F`) vs FRI split-and-fold (domain shrinks, plain RS code on the squared subdomain). The PR pre-empts this exact confusion in a dedicated "Not the FRI fold" docstring section (`Folded.lean:30-39`). Verified by reading `Folding.lean:64-293`. |
| `ListDecodable.Lambda` vs `listDecodable` / `closeCodewordsRel` | `ListDecodability.lean:42,53` | **Exemplary handling.** The PR explicitly declines to add a paper alias for `Λ(C,δ,f)` ("we do *not* introduce a paper-named alias for it") and adds the bridge `Lambda_le_iff_listDecodable`. `Lambda` (the sup over `f`) has no pre-existing counterpart — `grep "iSup.*ncard" origin/main` → 0 hits. |
| `hammingBallVolume` vs `ListDecodable.hammingBall` | `ListDecodability.lean:27` | Different objects (ℕ-valued closed-form vs a `Set`); bridged by `hammingBallVolume_eq_ncard_hammingBall`. No Mathlib ball-cardinality lemma exists (`loogle` on `card (filter (hammingDist _ · ≤ _))` → empty). Only complaint is the namespace split (D8). |
| `prob_schwartz_zippel_mv_polynomial_of_totalDegree_le` vs `prob_schwartz_zippel_mv_polynomial` | `Probability/Instances.lean` | **Exemplary handling** — the PR *generalized the original in place* and kept the old statement as a one-line corollary. This is the pattern the other findings should follow. |
| `Polynomial.foldedWronskian` vs Mathlib `Polynomial.wronskian` | `Mathlib/RingTheory/Polynomial/Wronskian.lean` | Mathlib's is `a * b' - a' * b` for two polynomials (Mason–Stothers); GK16's is a `σ × σ` determinant of `ω`-twists. Unrelated. No Wronskian anywhere in `origin/main` ArkLib. |
| `X_pow_card_sub_one_sub_C_irreducible` vs Mathlib Kummer criteria | `Mathlib/FieldTheory/KummerExtension.lean:114,146`, `KummerPolynomial.lean:98` | Mathlib covers only `n` odd / `n` prime / `n` a prime power. Here `n = q - 1` is even for odd `q` and generally composite. The PR's stated justification is accurate. |
| `pow_dvd_det_of_forall_mem_col_dvd`, `sum_rootMultiplicity_le_natDegree` | Mathlib | Verified absent (`loogle "?d ^ _ ∣ Matrix.det ?M"` and `loogle "Finset.sum _ (fun a => Polynomial.rootMultiplicity a _) ≤ _"` both empty). Genuinely new — but misplaced (D7). |
| `exists_adapted_basis` | Mathlib | No Mathlib lemma gives a basis whose first `finrank N` vectors lie in `N`; the PR builds it from `Submodule.exists_isCompl` + `Basis.prod` + `prodEquivOfIsCompl`, which is the right route. Misplaced (D7), not duplicated. |
| `numCollsOrdered`, `cauchy_schwarz_fiber`, `sum_fiber_sq_eq` | Mathlib | `cauchy_schwarz_fiber` *reuses* Mathlib's `sq_sum_le_card_mul_sum_sq` rather than reproving Cauchy–Schwarz; `sum_fiber_sq_eq` is a fiber-counting identity with no Mathlib analogue. Correct reuse. |
| `minRelHammingDistCode_{mem,le,of_empty}` | Mathlib `Finset.min'_mem` / `min'_le` | Thin, idiomatic universal-property wrappers that hide the `Set.Finite.toFinset` plumbing — exactly what such a def should ship. `possibleRelHammingDists` already reuses the generic `Code.possibleDists`. |
| `extensionCode` vs `Code.interleavedCodeSet` | `InterleavedCode.lean:135` | Defining `extensionCode` as the transport of `interleavedCodeSet` would make ABF26 L2.21 (`lambda_extensionCode_eq_lambda_interleaved`) vacuous. Keeping an independent definition and *proving* the isometry is the right call. |
| `IsSubspaceDesign` | — | Nothing comparable on `main`; `grep -i subspacedesign origin/main` → 0 hits. |
| `SupportsErasureCorrection` | — | No erasure material on `main` (`grep -in erasure origin/main -- ArkLib/` → 0 hits). Only its uniqueness core generalizes (D5). |
| `umCode` vs `GuruswamiSudan/Basic.lean` multiplicity machinery | `GuruswamiSudan/Basic.lean:593-733` | GS's "multiplicity" is root multiplicity of an interpolating bivariate `Q`; `umCode` is the derivative-packing code. Different notions despite the shared word. |
| `Admissible` vs `ReedSolomon.Smooth` / `CosetFftDomain` | `ReedSolomon.lean:700`, `Data/Domain/CosetFftDomain/` | `Smooth`/coset-domain classes are about multiplicative-subgroup structure of the *domain*; `Admissible` is an injectivity condition on the `(α, i) ↦ α ω^i` map. Overlapping in spirit, disjoint in statement. Not actionable now. |

---

## Clean bill (what I checked and found non-duplicative)

- **Inventory**: all 110 new declarations enumerated mechanically per file by diffing HEAD vs
  `origin/main` decl lists (`./R8-new-decls.txt`). No file skipped.
- **Baseline**: 1977 `origin/main` declarations under
  `ArkLib/Data/{CodingTheory,Polynomial,Probability,Fin,MvPolynomial}` and `ArkLib/ToMathlib`
  enumerated and scanned; the ~200 definitions/instances read in full.
- **Mathlib checks run**: `Real.qaryEntropy`/`binEntropy`; `Polynomial.wronskian`;
  Kummer irreducibility criteria; `hammingDist_comp` and the whole
  `InformationTheory/Hamming.lean` API; `Submodule.finrank_map_subtype_eq`,
  `LinearMap.finrank_range_of_inj`, `Submodule.equivMapOfInjective`, `LinearEquiv.finrank_map_eq`;
  `Equiv.piCongrRight`; `sq_sum_le_card_mul_sum_sq`; `MvPolynomial.schwartz_zippel_totalDegree`;
  `Matrix.det_updateCol_smul`, `Matrix.exists_vecMul_eq_zero_iff`; loogle queries for
  det-divisibility, summed root multiplicities, and Hamming-ball cardinality.
- **Genuinely new, correctly placed, no ArkLib/Mathlib precedent**: `IsSubspaceDesign`,
  `subspaceDesign_tau_lower`, `frs_is_subspaceDesign_gk16`, `foldedWronskian` + its degree
  bound + `foldedWronskian_ne_zero_of_linearIndependent`, `frsCode`/`Admissible`/`minDist_frsCode`,
  `umCode`, `extensionCode` + `lambda_extensionCode_eq_lambda_interleaved`,
  `SupportsErasureCorrection`, `Lambda` and its eight lemmas, `hammingBallVolume` +
  `card_filter_hammingDist_eq`, `johnson_bound_lambda_le_ell`, `mds_johnson_lambda_le`,
  `plotkin_card_le_ell`, `exists_large_image_of_pairwise_collision_bound` and its two helpers,
  `prob_dotProduct_eq_zero_le`, `prob_uniform_pi_mem_finset_{eq,le}`, `Pr_map_eq`,
  `prob_polynomial_identity_le`, `minDist_div_card_eq_minRelHammingDistCode`,
  `IsMDS_iff_rate_distance{,'}`, `singleton_bound_module`.
- **Reuse done right** (worth crediting): the Schwartz–Zippel generalisation-in-place;
  the `Lambda`/`listDecodable` bridge instead of a paper alias; `extensionCode` deriving
  `ψ`/`φ` from `algebraMap`/`Basis.equivFun` rather than re-implementing them; the FRI-fold
  disambiguation docstring; `cauchy_schwarz_fiber` calling Mathlib's Chebyshev;
  `disagreementCols` being pushed into the two pre-existing proofs in `Distance.lean` rather
  than added alongside them; the de-fielding of `johnson_bound` (removing spurious `[Field F]`).
- **`ArkLib.lean`** import additions match the new files exactly (11 added, all present).

## Probe files (all compile, `lake env lean`, no `sorry`)

- `(session-local probe) R8-dup1.lean` — D1, D2, D9
- `(session-local probe) R8-dup2.lean` — D3
- `(session-local probe) R8-dup3.lean` — D4, D6
- `(session-local probe) R8-dup4.lean` — D5, D7 (the `finrank_map_subtype_eq` sub-finding)
