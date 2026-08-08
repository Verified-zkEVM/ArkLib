# R7 — `ArkLib/Data/CodingTheory/ExtensionCodes.lean` (ABF26 §2.6: D2.19 / D2.20 / L2.21)

Repo `/home/alh/ArkLib-split-pr1` @ `ffa0733a`. All probes under
`(session-local probe) r7-*.lean`, compiled with `lake env lean` (no repo rebuild).

**Headline: no CRITICAL and no HIGH findings.** `lambda_extensionCode_eq_lambda_interleaved`
is a *correct, faithful, genuinely proven, non-vacuous* formalization of ABF26 Lemma 2.21 /
[BCFW25, Lemma D.3], axiom-clean, with a compiled concrete nondegenerate instance.
Everything below is MEDIUM/LOW: duplication, a missed (compiled) generalization, coverage
gaps, and doc/convention issues.

Counts: **0 CRITICAL, 0 HIGH, 3 MEDIUM, 5 LOW.**

---

### [MEDIUM] `ExtensionFieldPresentation.coord` is a redefinition of Mathlib's `Module.Basis.coord`; three more lemmas are Mathlib restatements

- **Where**: `ArkLib/Data/CodingTheory/ExtensionCodes.lean:97` (`ExtensionFieldPresentation.coord`),
  `:87` (`ψ_injective`), `:107` (`coord_add`), `:114` (`coord_psi_smul`)
- **Source**: Mathlib `Module.Basis.coord`
  (`.lake/packages/mathlib/Mathlib/LinearAlgebra/Basis/Defs.lean:665`,
  `def coord : M →ₗ[R] R := Finsupp.lapply i ∘ₗ ↑b.repr`) — already imported transitively
  (the file imports `Mathlib.LinearAlgebra.Basis.Defs` explicitly).
- **What's wrong**: the module docstring (line 26) and the D2.19 docstring (lines 68–70) claim
  "no parallel implementation" / "derived (not duplicated)". That is true of `ψ`
  (`algebraMap`) and `φ` (`Basis.equivFun`), but **not** of `coord`, which re-derives
  `Module.Basis.coord` as `LinearMap.proj j ∘ₗ basis.equivFun`. The three companion lemmas are
  also pure restatements: `coord_add` = `map_add`, `coord_psi_smul` = `map_smul` +
  `Algebra.smul_def`, `ψ_injective` = `FaithfulSMul.algebraMap_injective` (the last is literally
  its own proof term).
- **Evidence**: `(session-local probe) r7-dup.lean` compiles clean and proves
  `P.coord j = P.basis.coord j`, `P.φ = P.basis.equivFun` (`rfl`),
  `P.coord j (x+y) = … := map_add _ _ _`, and `Function.Injective P.ψ :=
  FaithfulSMul.algebraMap_injective B F`.
- **Refutation attempt**: I checked whether `coord` needs the `Fintype (Fin e)`-specific
  `equivFun` form (e.g. for `Basis.sum_equivFun` in `extensionCode_smul_mem`). It does not —
  `Basis.coord` is definitionally the same function, and the `sum_equivFun` step is unaffected.
  I also checked that `Basis.coord` is reachable from the current import set (it is; the
  earlier "unknown identifier" was only because `Basis = Module.Basis` needs `open Module`).
- **Suggested fix**: `def coord P j := P.basis.coord j` (or drop `coord` and use
  `P.basis.coord` at call sites); delete `coord_add`, `coord_psi_smul`, `ψ_injective` or
  demote them to `simp`-normal-form bridges; drop the "no parallel implementation" claim
  from the docstring and from the audit-doc `D2.19` row.

---

### [MEDIUM] Missed generalization: `extensionCode` is the `F`-span of the base code — basis-free, hence presentation-independent

- **Where**: `ArkLib/Data/CodingTheory/ExtensionCodes.lean:134` (`extensionCode`),
  `:202` (`extensionCode_smul_mem`, 58 lines), `:271` (`extensionCodeSubmodule`)
- **Source**: Mathlib `Submodule.span` / `Submodule.subset_span` / `Submodule.sum_mem`
- **What's wrong**: for a `B`-submodule `C_B`, `extensionCodeSubmodule P C_B` is *exactly*
  `Submodule.span F ((fun c i ↦ algebraMap B F (c i)) '' C_B)`. That characterization mentions
  neither `e`, nor the basis, nor `φ` — so the entire `ExtensionFieldPresentation` apparatus is
  unnecessary for D2.20, and in particular `extensionCode P C_B` **does not depend on `P`**.
  Consequences: (i) the 58-line basis-expansion proof of `extensionCode_smul_mem` (the "F-scalar
  closure the structural refactor delivers") is a one-liner from `Submodule.span`;
  (ii) `extensionCodeSubmodule` could be defined as the span and the three closure laws come free.
- **Evidence**: `(session-local probe) r7-span.lean` compiles clean, proving
  `extensionCode_eq_span : extensionCodeSubmodule P C_B = Submodule.span F (gen C_B)` and the
  corollary `extensionCode_presentation_independent :
  extensionCode P C_B = extensionCode P' C_B` for *any two* presentations `P P'`.
  `#print axioms` on both: `[propext, Classical.choice, Quot.sound]`.
- **Refutation attempt**: I tried to break the ⊇ direction by looking for a presentation whose
  `coord j 1 = 0` for some `j` (which would make the generator argument degenerate) — it is
  harmless, the generator lands in `(coord j 1) • c ∈ C_B` regardless. I also checked the ⊆
  direction needs `C_B` to be a submodule (it does — the span statement is only for the
  `Submodule` form; the raw `Set` form genuinely needs the closure hypotheses). So the finding
  is scoped to the `Submodule` form, where it is exact.
- **Suggested fix**: keep `extensionCode` (the `Set` form) as the paper-shaped definition, but
  add `extensionCode_eq_span` as the bridge and reprove `extensionCode_smul_mem` /
  `extensionCodeSubmodule` through it. At minimum record presentation-independence — it is the
  mathematically informative fact here and it is currently invisible.

---

### [MEDIUM] D2.20's encoder-level content is not formalized; `IsSystematic` is dead code with zero consumers

- **Where**: `ArkLib/Data/CodingTheory/ExtensionCodes.lean:102` (`IsSystematic`),
  `:142` (`extensionCode_iff_coord_in_base`), whole module
- **Source**: ABF26 D2.20 / [BCFW25] D.2, verbatim: *"If the extension field presentation is
  systematic, then `C_F(ψ(v)) = ψ(C_B(v))` for any `v ∈ B^k`."* BCFW25 §D.2 uses exactly this
  ("This is sound since, by virtue of the presentation being systematic,
  `C_F(ψ(v)) = ψ(C_B(v))` for every `v ∈ B^k`").
- **What's wrong**: `IsSystematic` is defined and then never used — no lemma in the file
  mentions it, and `grep -rn "IsSystematic"` over the whole repo returns only its own
  definition. The paper's *only* consequence of systematicity is not stated. It is in fact not
  even *expressible* in the current shape: ABF26 D2.20 defines `C_F` as an **encoder**
  `F^k → F^n`, whereas ArkLib formalizes only the image (`Set (ι → F)`), so a statement about
  `C_F` applied to a specific message has no Lean counterpart. The whole module also has zero
  in-repo consumers (only the generated `ArkLib.lean` import at line 71).
  Related nit: the lemma at `:142` is labelled **"Bridge to paper's encoder-image view"** but
  is `rfl` — it restates the definition and says nothing about any encoder.
- **Evidence**: `grep -rn "IsSystematic\|extensionCode\|ExtensionFieldPresentation" --include=*.lean .`
  → only `ExtensionCodes.lean` itself. `git log` shows the file was introduced by `a64ca0ec`
  with no downstream use.
- **Refutation attempt**: I checked whether the *membership* form ("`ψ ∘ c ∈ extensionCode` for
  `c ∈ C_B`") would be a reasonable stand-in for the paper's consequence. It would not be a
  faithful stand-in, because that membership holds **without** the systematic hypothesis (it
  follows from `span_le_ext` in `(session-local probe) r7-span.lean`: `coord j (ψ x) = x · coord j 1`,
  so `ψ ∘ c = (coord j 1) • c ∈ C_B` for every presentation). So systematicity really only
  buys the encoder-level statement, which cannot currently be written down.
- **Suggested fix**: either (a) drop `IsSystematic` until D2.20 grows an encoder, or (b) add an
  encoder-level `extensionEncode` (`(Fin k → F) → (ι → F)` from a base encoder) and state
  `IsSystematic → extensionEncode (ψ ∘ v) = ψ ∘ baseEncode v`. Also retitle the `rfl` lemma at
  `:142` (it is not a bridge to an encoder view), and note the encoder gap in the `D2.20` row of
  `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md`.

---

### [LOW] Headline theorem carries 8 redundant hypotheses; two Mathlib linters are disabled file-scope, hiding 5 of them

- **Where**: `ArkLib/Data/CodingTheory/ExtensionCodes.lean:50-51` (`set_option
  linter.unusedFintypeInType false`, `set_option linter.unusedDecidableInType false`),
  `:311-316` (`lambda_extensionCode_eq_lambda_interleaved`)
- **What's wrong**: `[Nonempty ι] [DecidableEq ι] [Fintype B] [DecidableEq B] [Fintype F]
  [DecidableEq F]` and both `_hδ_pos : 0 < δ`, `_hδ_lt : δ < 1` are all unused (the last two
  are honestly underscore-named). `Lambda` / `closeCodewordsRel` / `relHammingBall` are declared
  under `open Classical in` and take **no** `DecidableEq`/`Nonempty` instances at all
  (checked via `#check`), so those binders cannot be load-bearing. The two file-scope
  `set_option … false` at lines 50–51 (bare, not `… in`) are what keep the Mathlib linters
  quiet about 5 of them. Separately, `[Fintype ι]` is unused in the *definitions*
  `extensionCode` and `extensionCodeSubmodule`.
- **Evidence**:
  - `(session-local probe) r7-minhyp.lean` — the **verbatim** shipped proof reproves the theorem with
    all six instance binders and both `δ` hypotheses removed; compiles clean. It also derives
    the `δ = 0` instance, so the theorem is true outside the paper's `(0,1)` window
    (this answers scope item 3(d): the missing restriction is *not* a soundness problem).
  - `(session-local probe) r7-linter.lean` — re-declares the shipped statement under
    `set_option linter.mathlibStandardSet true` without the suppressions; the linters fire:
    `does not use … [DecidableEq ι] (#4) • [DecidableEq B] (#9) • [DecidableEq F] (#12)` and
    `… [Fintype B] (#8) • [Fintype F] (#11)`.
- **Refutation attempt**: I checked whether `[Fintype B]`/`[Fintype F]` are needed to keep
  `Lambda ≠ ⊤` (i.e. to make the equality meaningful rather than `⊤ = ⊤`). They are not needed
  for the *statement*, and finiteness is available separately via `Lambda_ne_top`; I verified
  `⊤ = ⊤` is not what is being proved by exhibiting a finite nondegenerate instance (next
  finding). I also confirmed the repo has precedent for these suppressions (5 other
  `ArkLib/Data/CodingTheory` files), which is why this is LOW rather than MEDIUM — but note
  `ReedSolomon.lean:664` and `Subdomain.lean:426` use the scoped `… in -- false alarm` form,
  which is the honest shape.
- **Suggested fix**: drop the six instance binders (keep `[Fintype ι]` where `Lambda` needs it),
  keep the `δ` hypotheses only if you want paper-shape fidelity (say so in the docstring), and
  delete the two file-scope linter suppressions.

---

### [LOW] Citation keys `[BuenzCFW25]` and `[DiamondP23]` do not exist in `blueprint/src/references.bib`; `DiamondP23` also misnames a paper the repo already keys twice

- **Where**: `ArkLib/Data/CodingTheory/ExtensionCodes.lean:37,44` (`[BuenzCFW25]`),
  `:47` (`[DiamondP23, Theorem 3.2]`), `:42` (`[ABF26]`)
- **Source**: `docs/wiki/blueprint-and-citations.md:25-28` — "Cite papers in Lean docstrings by
  citation key … Add the matching BibTeX entry to `blueprint/src/references.bib`."
- **What's wrong**: `references.bib` contains none of `ABF26`, `BuenzCFW25`, `DiamondP23`
  (the full key list is `LFKN92 BBS24 IOPs BCS16 spartan … DP23 DP24 DP25 …`). Consequently
  `scripts/kb/extract_lean_citations.py` produces a citation map in which `ExtensionCodes.lean`
  appears **not at all** — its three citations are silently dropped. Additionally, the paper the
  docstring calls `[DiamondP23]` is Diamond–Posen *"Succinct Arguments over Towers of Binary
  Fields"*, which ABF26 (line 552 of the text extraction) and BCFW25 both cite as `[DP25]` and
  which `references.bib` already carries **twice** (`DP23`, the 2023 ePrint, and `DP25`, the
  EUROCRYPT'25 version) — so the docstring invents a third, nonexistent spelling.
- **Evidence**:
  `grep -n "^@.*{" blueprint/src/references.bib` (no `ABF26`/`BuenzCFW25`/`DiamondP23`);
  `python3 scripts/kb/extract_lean_citations.py` → "152 files, 30 cited keys", with no
  `ExtensionCodes` entry; `(pdftotext of ~/abf26-refs/) ABF26.txt:552` `(see e.g. [DP25, Thm 3.2])`;
  `SCRATCH/refs2/BuenzCFW25.txt:3696` `[DP25, Thm 3.2]`.
- **Refutation attempt**: I checked `docs/kb/papers/` for a `BuenzCFW25.md` / `ABF26.md`
  fallback — neither exists. I also checked whether the missing `ABF26` key is a PR-wide issue
  rather than a defect of this file: it is (`grep -rl "\[ABF26" --include=*.lean ArkLib/` → 8
  files, all new in this PR; `origin/main` → 0), so I report `ABF26` only as context and score
  the file on `BuenzCFW25`/`DiamondP23`.
- **Suggested fix**: add `ABF26` and `BuenzCFW25` (= Bünz–Chiesa–Fenzi–Wang) to
  `references.bib` + `docs/kb/papers/`, and change `[DiamondP23]` to the existing `[DP25]`.

---

### [LOW] Universe-monomorphic at `Type 0` while every surrounding CodingTheory definition is `Type*`

- **Where**: `ExtensionCodes.lean:71` (`structure ExtensionFieldPresentation (B F : Type)`),
  `:134` (`def extensionCode {ι : Type}`), `:271`, `:292`, `:311` (same)
- **Source**: `ListDecodability.lean` `Lambda {ι : Type*} {F : Type*}`;
  `InterleavedCode.lean` `interleavedCodeSet {A κ ι : Type*}`.
- **What's wrong**: nothing forces the restriction — it just makes the module unusable at any
  index/alphabet type outside `Type 0`, unlike everything it builds on.
- **Evidence**: `(session-local probe) r7-univ.lean` compiles a `Type*`-polymorphic clone of the
  structure, of `coord` (as `basis.coord`), and of `extensionCode` (also without `[Fintype ι]`).
- **Refutation attempt**: I looked for a universe constraint forced by `Basis (Fin e) B F`
  or by `Equiv.piCongrRight` in the L2.21 proof — both are universe-polymorphic.
- **Suggested fix**: `Type*` throughout; drop `[Fintype ι]` from the two definitions.

---

### [LOW] Docstring overstatements

- **Where**: `ExtensionCodes.lean:27-28` and `:122-124`
- **What's wrong**: the module docstring calls `extensionCode` "the extension code
  `C_F : F^k → F^n`", and D2.20's docstring repeats "The *extension code* `C_F : F^k → F^n`".
  `extensionCode` is a `Set (ι → F)`, not a map; the `k` never appears anywhere in the module.
  (Cf. the MEDIUM above: this is the same encoder-vs-image gap, stated as if closed.)
- **Evidence**: `#check @extensionCode` →
  `… → ExtensionFieldPresentation B F → Set (ι → B) → Set (ι → F)`.
- **Suggested fix**: say "the image of the extension code" / "the extension code as a set of
  words", as the D2.9/D2.20 sibling modules do.

---

### [LOW] `docs/wiki/coding-theory-conventions.md` carrier table not updated for `extensionCodeSubmodule`

- **Where**: `docs/wiki/coding-theory-conventions.md:134-135`
- **What's wrong**: the "Linear code carrier" row lists `ReedSolomon.code`,
  `Interleaved.irsCode`, `Folded.frsCode` but not `extensionCodeSubmodule`, while the
  "Non-linear code carrier" row lists `extensionCode`. Since the PR's own docstring advertises
  "`extensionCode P C_B` as a full `F`-`Submodule`" and D2.20 in the paper says *linear code*,
  a reader of the conventions table would conclude ArkLib only has the non-linear form.
- **Suggested fix**: add `extensionCodeSubmodule` to the linear-carrier row.

---

### [LOW] `Code.interleavedCodeSet` used raw instead of the `C ^⋈ κ` notation

- **Where**: `ExtensionCodes.lean:318`, `:335`, `:342`, `:362`
- **What's wrong**: `InterleavedCode.lean:300` defines `notation:20 C "^⋈" κ` and
  `:356 interleavedCode_eq_interleavedCodeSet` proves the two are `rfl`-equal. The paper's
  `C_B^e` reads more directly as `C_B ^⋈ (Fin P.e)`. Cosmetic only — the underlying object is
  the right one, so this is **not** a duplication.
- **Suggested fix**: use the notation in the statement (keep the raw form in the proof).

---

## Clean bill

Everything below I actively tried to break and could not.

**D2.19 faithfulness (scope item 1)** — the Lean structure captures all five paper components:
`B`,`F` as `[Field B] [Field F]`; `ψ` as `algebraMap B F` with `ψ_injective` discharged by
`FaithfulSMul.algebraMap_injective`; `e` as a field; `φ` as `basis.equivFun`, a genuine
`B`-linear **iso** `F ≃ₗ[B] (Fin e → B)`; `IsSystematic` as `∀ x, φ(ψ x) = (x,0,…,0)` — verified
the `if i.val = 0 then x else 0` spelling is the paper's `(x, 0, …, 0)`.
- **`e` is tied to `finrank`, not free**: `(session-local probe) r7-inst.lean` proves
  `P.e = Module.finrank B F` for every `P` (from `Module.finrank_eq_card_basis P.basis`).
  So the structure admits no `e ≠ dim_B F` nonsense. Also `e = 0` is unreachable
  (`Basis (Fin 0) B F` would make the field `F` subsingleton), so the `by_cases P.e = 0` branch
  in `extensionCode_smul_mem:247` is dead but harmless.
- **Does wrapping `Algebra` lose presentations the paper allows?** Marginally and harmlessly:
  a given `[Algebra B F]` instance pins one `ψ`, so a *conjugate* embedding (e.g. the nontrivial
  `F4 ↪ F16`) needs a different instance rather than a different `P`. Every paper tuple
  `(B,F,e,ψ,φ)` is still representable by choosing the `Algebra` structure induced by `ψ`.
  The docstring is honest about this ("`[Algebra B F]` provides the embedding `ψ`").
  Not scored as a finding.

**D2.20 faithfulness (scope item 2)** — `extensionCode P C_B = {v | ∀ j, (fun i ↦ φ_j (v i)) ∈ C_B}`
is exactly the image of the paper's encoder `C_F(v) = φ⁻¹(C_B(φ_1 v),…,C_B(φ_e v))`: as `v`
ranges over `F^k`, `(φ_1 v,…,φ_e v)` ranges over all of `(B^k)^e`, so the image is
`{w : φ_j(w) ∈ C_B ∀ j}`, applied coordinatewise in `ι` in the right order. Verified `φ` is
applied to the *word* and the membership test is per-row.
- **F-linearity IS proven**, contrary to the worry in my brief: `extensionCode_smul_mem`
  (F-scalar closure), `extensionCode_add_mem`, and the packaged
  `extensionCodeSubmodule : Submodule F (ι → F)` with `coe_extensionCodeSubmodule` as the
  carrier bridge. The `smul_mem'` field really is F-scalar (`c : F`), not B-scalar — checked.
  The conventions-doc "Non-linear code carrier" row is an incomplete listing, not a claim that
  linearity is missing (scored LOW above).
- `extensionCode_smul_mem`'s proof is real: `Basis.sum_equivFun` expansion, `mul_smul_comm`,
  `map_sum`, then `Finset.sum_induction` with `0 ∈ C_B` derived from `hsmul 0`. No cheats;
  `hadd`/`hsmul` are both load-bearing.

**L2.21 (scope item 3) — the headline, fully validated**
- (a) **Both sides use the same `Λ`.** LHS and RHS are both `ListDecodable.Lambda`, i.e.
  `⨆ f, (closeCodewordsRel C f δ).ncard` — the **sup over centers**, matching the paper's
  `|Λ(C,δ)| = max_f |Λ(C,δ,f)|`. There is *no* pointwise/sup mismatch. The sup on the RHS
  correctly ranges over `g : ι → (Fin e → B)` (all interleaved words), matching BCFW25's
  `(f_i)_{i∈[e]}`. `δ ∈ (0,1)` is present as explicit (unused) hypotheses — see the LOW above;
  the statement is *true* at `δ = 0` and `δ ≥ 1` (compiled), so nothing is missing.
- (b) **It is a genuine blockwise isometry.** `Ψ = Equiv.piCongrRight (fun _ ↦ φ)` and
  `hammingDist_comp` (Mathlib, requires injectivity per coordinate — supplied by `φ.injective`)
  gives `Δ₀(Ψ x, Ψ y) = Δ₀(x, y)` *exactly*. Normalisation matches: `Code.relHammingDist u v =
  Δ₀(u,v) / Fintype.card ι` on **both** sides, with the same `ι` — i.e. both are normalized by
  the block length `n`, never by `n·e`. This is exactly BCFW25's `|S| ≥ (1-δ)·n, S ⊆ [n]`.
  The alphabet-cardinality worry in my brief does not materialize because relative distance
  here is alphabet-agnostic.
  The membership transport `hmem` is defeq (`exact h j`), correct because
  `(Ψ v).transpose j = fun i ↦ φ(v i) j = fun i ↦ coord j (v i)`.
  `Set.ncard_image_of_injective` + `Equiv.iSup_comp` + `iSup_congr` finish the sup transport —
  no `simp` doing hidden work, no `decide`.
- (c) **Non-vacuity: compiled concrete instance.** `(session-local probe) r7-nondeg.lean` builds
  `P4 : ExtensionFieldPresentation (ZMod 2) (GaloisField 2 2)` with `P4.e = 2`
  (`GaloisField.finrank`), takes `C_B` = the length-2 repetition code over `𝔽₂`, and proves:
  `extensionCode P4 Crep = {v | v 0 = v 1}` (nonempty, and `≠ Set.univ`);
  `lambda_lower : (2 : ℕ∞) ≤ Lambda (extensionCode P4 Crep) (1/2)`;
  `headline_concrete` = the shipped theorem instantiated at `δ = 1/2`;
  `rhs_nondeg : (2 : ℕ∞) ≤ Lambda (interleavedCodeSet Crep) (1/2)`;
  `lhs_ne_top`. So both sides are `≥ 2` and finite — the equality is not `0 = 0` or `⊤ = ⊤`.
  `#print axioms headline_concrete` / `rhs_nondeg` → `[propext, Classical.choice, Quot.sound]`.
- (d) covered under (a).

**Duplication verdict (scope item 4)** — **this file does NOT fork ArkLib's interleaving
machinery.** It consumes `Code.interleavedCodeSet` (`InterleavedCode.lean:135`) directly, which
is the same object as `C ^⋈ κ` (`interleavedCode_eq_interleavedCodeSet:356`, `rfl`), and it
correctly does **not** touch `relHammingBallInterleavedCode` / `Λᵢ` (a `WordStack`-indexed
notion, wrong shape here). No extension-code / base-change construction pre-exists anywhere in
`ArkLib/` (`grep -rn "extension" ArkLib/Data/CodingTheory ArkLib/ToMathlib` → only
multilinear-extension hits). `RingSwitching/Packing/Prelude.lean`'s `RingSwitchingProfile` is a
tensor-algebra decomposition profile, not the same object. The two real duplication/
generalization items are the MEDIUMs above (`Basis.coord`; the `Submodule.span` route). I also
checked `Submodule.restrictScalars` (wrong direction: restricts an `F`-module to `B`) and
`LinearMap.baseChange`/`Algebra.TensorProduct` (would need `C_B ⊗[B] F ↪ (ι → F)` plus
flatness bookkeeping) — the `Submodule.span` route is strictly simpler and is what I verified.

**Auxiliary lemmas (scope item 5)** — `extensionCode_iff_coord_in_base` (`rfl`),
`extensionCode_add_mem`, `extensionCode_psi_smul_mem`, `extensionCode_smul_mem`,
`extensionCodeSubmodule`, `coe_extensionCodeSubmodule` (`rfl`): each independently correct,
none false, none vacuous. `coord_add` / `coord_psi_smul` / `ψ_injective` are correct but are
Mathlib restatements (MEDIUM #1).

**Axioms (scope item 6)** — `(session-local probe) r7-sig.lean`: all 14 public declarations in the
file, including `lambda_extensionCode_eq_lambda_interleaved`, report exactly
`[propext, Classical.choice, Quot.sound]`. No `sorryAx`, no custom axioms.

**Doc honesty of the audit rows** — `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md`
rows `D2.19` / `D2.20` / `L2.21` are accurate about what is proven (including explicitly
recording that `δ_min(C_F) = δ_min(C_B)` from DP25 is **not** formalised — confirmed, the PR
does not claim it anywhere in Lean). The only inaccuracy is the "no parallel implementation"
phrase in the `D2.19` row (MEDIUM #1).
