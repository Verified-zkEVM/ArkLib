# R3 — distance & list primitives (PR #701)

Scope: `Basic/Distance.lean` (+70), `Basic/RelativeDistance.lean` (+100),
`Basic/Entropy.lean` (new), `HammingBallVolume.lean` (new), `ListDecodability.lean` (+90),
`Erasure.lean` (new).

Probes (all compiled with `lake env lean`, repo unmodified):

- `(session-local probe) r3-entropy.lean` — clean
- `(session-local probe) r3-reldist.lean` — clean (except two deliberate "old-def friction" cases)
- `(session-local probe) r3-vol-lambda.lean` — clean
- `(session-local probe) r3-erasure.lean` — clean
- `(session-local probe) r3-mindist.lean` — clean
- `(session-local probe) r3-hbv-nolint.lean` — linter experiment

**No CRITICAL, no HIGH.** Everything in this bucket is mathematically true, faithful to
ABF26, sorry-free and axiom-clean (`[propext, Classical.choice, Quot.sound]` everywhere I
checked). The findings below are 4 MEDIUM (three doc/claim, one type-convention trap) and
7 LOW.

---

### [MEDIUM] Wiki added by this PR still describes `hammingBallVolume_eq_ncard_hammingBall` as a *partial* proof with sub-sorries; it is fully proven

- **Where**: `docs/wiki/coding-theory-conventions.md:160-166` (section "Tagged sorry comments");
  the theorem is `ArkLib/Data/CodingTheory/HammingBallVolume.lean:164`.
- **Source**: the wiki text reads

  > exceptions are sub-sorries inside bridge lemmas (e.g. **the partial proof of**
  > `hammingBallVolume_eq_ncard_hammingBall` decomposes into `card_filter_hammingDist_eq`
  > and a small Set/Finset conversion). These are tracked in the local working notes instead.

- **What's wrong**: there are **no** sorries anywhere in the six files of this bucket
  (`grep -rn sorry` → exit 1), and both `hammingBallVolume_eq_ncard_hammingBall` and
  `card_filter_hammingDist_eq` are axiom-clean. A reviewer reading the newly-added wiki page
  would conclude the flagship bridge lemma is admitted. The paragraph is also the *only*
  instance the "Tagged sorry comments" section names, so it is the wiki's sole worked example
  and it is wrong.
- **Evidence**: `(session-local probe) r3-vol-lambda.lean` prints
  `'CodingTheory.hammingBallVolume_eq_ncard_hammingBall' depends on axioms: [propext, Classical.choice, Quot.sound]`
  and `'CodingTheory.card_filter_hammingDist_eq' depends on axioms: [propext, Classical.choice, Quot.sound]`.
- **Refutation attempt**: checked the whole PR diff for added `sorry` tokens
  (`git diff origin/main...HEAD | grep '^+.*sorry'`) — 13 hits, all inside docstrings/markdown,
  none a Lean `sorry` in this bucket.
- **Suggested fix**: delete the parenthetical, or replace with a live example (there is none in
  this split — say so).

---

### [MEDIUM] `SupportsErasureCorrection` is a tautology, but its docstring claims clause (ii) makes it "non-vacuous"

- **Where**: `ArkLib/Data/CodingTheory/Erasure.lean:66` (`SupportsErasureCorrection`),
  docstring lines 52-56; theorem at line 125.
- **Source**: ABF26 Definition 6.4 —

  > A code `C ⊆ Σⁿ` supports erasure correction **with correction time ecor_C** if there exists
  > a deterministic algorithm `E_C` … • if `|f⁻¹(⊥)| < δmin(C)·n` and there exists a codeword
  > `u ∈ C` such that `f(i) = u(i)` for all `i ∈ [n] \ f⁻¹(⊥)`, then `E_C(f) = u` …
  > • otherwise `E_C(f) = ⊥`. **Moreover, `E_C` performs at most `ecor_C` field operations.**

- **What's wrong**: the docstring at the *definition* says

  > Clause (ii) — easy to miss in a quick port from the paper — is what makes the predicate
  > **non-vacuous**: without it, `E := fun _ ↦ some <arbitrary>` satisfies the recovery clause
  > for any `f` whose preconditions fail, hollowing the definition out.

  Clause (ii) pins the *witness* `E`, but it does not make the predicate informative about `C`:
  `additive_code_supports_erasure_correction_grs12` proves `SupportsErasureCorrection C` for an
  **arbitrary** `C : Set (ι → F)`, so `∀ C, SupportsErasureCorrection C` is definitionally
  `True`. Dropping the `ecor` parameter (which is what carries the paper's whole content)
  necessarily makes the predicate a tautology; the *theorem*'s docstring says this honestly
  ("Scope caveat — this theorem does NOT capture the cited [GRS12] content"), the *definition*'s
  docstring contradicts it.
  Concretely: for any code with `|C| ≤ 1`, `Code.minDist C = sInf ∅ = 0`, so the **only** legal
  corrector is `fun _ ↦ none` — the predicate holds for a code whose corrector fails even on a
  fully-unerased exact codeword.
- **Evidence**: `(session-local probe) r3-erasure.lean`, all compiling:
  - `example : (∀ (C : Set (Fin 5 → Fin 2)), SupportsErasureCorrection C) ↔ True := ⟨fun _ => trivial, fun _ C => additive_code_supports_erasure_correction_grs12 C⟩`
  - `SupportsErasureCorrection (∅ : Set (Fin 5 → Fin 2))`, `… Set.univ`, `… {![0,0,0,0,0], ![1,1,0,0,0]}` all discharged by the same term.
  - a compiled `example` showing that for the singleton code `{c}`, any witness `E` satisfies
    `E (fun i => some (c i)) = none`.
- **Refutation attempt**: I checked whether clause (ii) could make the predicate *false* for
  some `C` (over-strong): no — `eq_of_consistent_with_erased` rules out the only possible
  conflict (two distinct codewords both matching a lightly-erased `f`), so the classical
  corrector always works. I also checked the guard `#erasures < Code.minDist C` against
  [GRS12] Proposition 1.4.2(4) ("C can correct d − 1 erasures" ⟺ minimum distance `d`,
  `(pdftotext of ~/abf26-refs/) GuruswamiRS12.txt:929`) — the guard is exactly right. So the *definition* is
  faithful; only the docstring claim is wrong.
- **Suggested fix**: change the definition docstring to say clause (ii) pins the *corrector*
  (making `E` unique) but that, without the `ecor` cost parameter, the predicate itself holds
  for every code — and cross-reference the theorem's scope caveat. Same paragraph is repeated
  in `docs/kb/audits/…:111`, which is accurate as written and can stay.

---

### [MEDIUM] `Lambda_le_iff_listDecodable` covers only `ℓ : ℕ`, but every in-tree `listDecodable` consumer uses `ℓ : ℝ≥0` — the docstring's "transfer" claim does not hold through the stated lemma

- **Where**: `ArkLib/Data/CodingTheory/ListDecodability.lean:102` (`Lambda_le_iff_listDecodable`),
  docstring lines 96-101.
- **Source**: the docstring claims

  > List-size bounds proved for `Lambda` (e.g. the Johnson family bounds in
  > `JohnsonBound/Family.lean`) **transfer to `listDecodable` consumers through this
  > equivalence**, and conversely.

- **What's wrong**: the lemma is `Lambda C δ ≤ (ℓ : ℕ∞) ↔ listDecodable C δ (ℓ : ℝ)` with
  `{ℓ : ℕ}`. But `listDecodable`'s own docstring (lines 47-52, pre-existing) explains that `ℓ`
  is real *precisely* "to accommodate the statement of the Johnson Bound Theorem", and all
  actual consumers instantiate it at `ℝ≥0`:
  - `ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean:52,62` — `{δ l : ℝ≥0}`, `listDecodable C δ l`
  - `ArkLib/ProofSystem/Stir/MainThm.lean:63,72` — `Distances.l : Fin (M+1) → ℝ≥0`
  And the Johnson bound this PR adds produces a real bound, not a `ℕ` one:
  `JohnsonBound/Family.lean:604` — `(Lambda C (1 - √ρ - η) : ENNReal) ≤ ENNReal.ofReal (1/(2*η*ρ))`.
  So the advertised transfer route is not available: a consumer must redo the
  `ℕ∞ → ENNReal → ℝ` reasoning by hand.
- **Evidence**: grep hits above; `johnson_bound_lambda_le_ell` (`Family.lean:408`) is the only
  `ℕ`-valued Lambda bound, and it is not what STIR consumes.
- **Refutation attempt**: I checked whether the ℕ form still suffices *in principle*
  (take `ℓ := ⌊r⌋₊`) — it does, since `Lambda` is integer-valued, but that derivation needs
  `ENat`/`ENNReal` plumbing that the lemma does not provide, so the "through this equivalence"
  wording overstates what is available.
- **Suggested fix**: add the real-valued form
  `lemma Lambda_le_ofReal_iff_listDecodable {ℓ : ℝ} (hℓ : 0 ≤ ℓ) : (Lambda C δ : ENNReal) ≤ ENNReal.ofReal ℓ ↔ listDecodable C δ ℓ`
  (or `Lambda C δ ≤ ⌊ℓ⌋₊ ↔ listDecodable C δ ℓ`), or soften the docstring.

---

### [MEDIUM] `Lambda` silently evaluates to `0` (not `⊤`) when the list is infinite

- **Where**: `ArkLib/Data/CodingTheory/ListDecodability.lean:93` (`Lambda`).
- **Source**: ABF26 Definition 2.8 — `|Λ(C, δ)| := max_f |Λ(C, δ, f)|`.
- **What's wrong**: `Lambda C δ := ⨆ f, ((closeCodewordsRel C f δ).ncard : ℕ∞)` uses
  `Set.ncard`, which is `0` on infinite sets. The definition carries **no** `[Finite F]`
  instance and no docstring caveat, while its codomain `ℕ∞` invites the reading "⊤ when the
  list is infinite". Over an infinite alphabet the value is therefore not just unknown but
  actively wrong, and `Lambda_le_iff_listDecodable` propagates it into a false-looking
  list-decodability claim. `Lambda_ne_top`'s docstring compounds this: it says the danger is
  `ENat.toNat` collapsing at `⊤`, whereas the real collapse channel here is `ncard → 0`.
- **Evidence**: `(session-local probe) r3-vol-lambda.lean`, compiled:
  ```
  lemma lambda_univ_Q : Lambda (Set.univ : Code (Fin 1) ℚ) 1 = 0        -- proven
  example : listDecodable (Set.univ : Code (Fin 1) ℚ) 1 ((0:ℕ) : ℝ)     -- proven
  ```
  i.e. "the full space `ℚ^1` has at most 0 codewords within relative distance 1 of any word",
  while in truth every one of the infinitely many words is in the list.
- **Refutation attempt**: I checked whether this is exploitable in-tree. It is not — every
  current `Lambda` consumer carries `[Fintype α]`/`[Fintype F]`
  (`johnson_bound_lambda_le_ell` Family.lean:398-402, `mds_johnson_lambda_le` Family.lean:600-603,
  `lambda_extensionCode_eq_lambda_interleaved` ExtensionCodes.lean:312-315), and the flaw is
  inherited from the pre-existing `listDecodable`/`ncard` convention rather than introduced.
  That is why this is MEDIUM and not HIGH.
- **Suggested fix**: either add `[Finite F]` to `Lambda` (matching `Lambda_mono`/`Lambda_le_card`),
  or use `Set.encard`/an `⊤`-on-infinite definition, or at minimum add the caveat to the
  docstring next to the existing quantisation note.

---

### [LOW] New "Type conventions" block in `Distance.lean` mistypes the computable variants

- **Where**: `ArkLib/Data/CodingTheory/Basic/Distance.lean:48` — "Computable variants: `ℚ≥0` —
  `δᵣ'`, `Δ₀'`, …".
- **What's wrong**: `notation "Δ₀'(" u ", " C ")" => distFromCode' C u` (Distance.lean:890) and
  `distFromCode' … : ℕ∞` (Distance.lean:887); `notation "‖" C "‖₀'" => dist' C`
  (Distance.lean:690) and `dist' … : ℕ∞` (Distance.lean:686). Only `δᵣ'`
  (`relDistFromCode' : ℚ≥0`, RelativeDistance.lean:715) is `ℚ≥0`.
- **Evidence**: the grep hits above.
- **Suggested fix**: split the row: `δᵣ' : ℚ≥0`; `Δ₀'`, `‖C‖₀' : ℕ∞`.

---

### [LOW] `docs/wiki/coding-theory-conventions.md` mistypes `Code.dist` / `‖C‖₀` as `ℕ∞`

- **Where**: `docs/wiki/coding-theory-conventions.md:123` — "| Min distance of a code (absolute)
  | `ℕ` (`Code.minDist`) / `ℕ∞` (`dist`, `‖C‖₀`) |".
- **What's wrong**: `Code.dist (C : Set (n → R)) : ℕ` (Distance.lean:167) and
  `‖C‖₀` is notation for `dist C` (Distance.lean:182), so both are `ℕ`; `dist_eq_minDist`
  (Distance.lean:249) proves them equal. The `ℕ∞` form is `distFromCode`
  (`Δ₀(u, C)`), which is already a separate row. The block the PR adds inside `Distance.lean`
  itself (line 46) gets this right — only the wiki is wrong.
- **Suggested fix**: change the row to `ℕ` (`Code.minDist`, `Code.dist`, `‖C‖₀`).

---

### [LOW] `disagreementCols` docstring overclaims usage and cites a non-existent file

- **Where**: `ArkLib/Data/CodingTheory/Basic/Distance.lean:130-148`.
- **What's wrong**: two claims.
  1. "This is the canonical primitive for 'coordinates where two words disagree', **used
     throughout the coding-theory development**." In fact it has exactly one consumer outside
     its own file (`Erasure.lean:91,93,102`) plus two rewrites inside `Distance.lean` itself.
     Every other pointwise-disagreement site in the repo still inlines the filter
     (`SubspaceDesign.lean:169,217,218,230,252`, `BCIKS20/AffineSpaces.lean:1857,1877`,
     `Binius/BinaryBasefold/Prelude.lean:1323`, `MDSCode.lean:146`,
     `ReedSolomon/Folded.lean:353`).
  2. It lists `Whir/BlockRelDistance.lean` among the specialised siblings. There is **no**
     `Whir` directory or file in the repo (`find ArkLib -ipath "*hir*" -name "*.lean"` → empty);
     the file meant is `ArkLib/Data/CodingTheory/Basic/BlockRelDistance.lean`.
- **Evidence**: greps above.
- **Suggested fix**: soften to "intended as the canonical primitive"; fix the path. (Optionally
  migrate the inline filters in the same PR so the claim becomes true.)

---

### [LOW] The `Set.Finite.toFinset` refactor is defeq-preserving, but there is no "diamond", and the lemmas it enables have zero consumers

- **Where**: `ArkLib/Data/CodingTheory/Basic/RelativeDistance.lean:565-576` (docstring +
  `minRelHammingDistCode`), and `:589-673` (`minRelHammingDistCode_of_empty/_mem/_le`,
  `minDist_div_card_eq_minRelHammingDistCode`).
- **What's wrong**: two sub-points, both benign.
  1. The docstring says the refactor "avoids a `Fintype.ofFinite` **diamond**". There is no
     diamond: `Set.Finite.fintype h = h.nonempty_fintype.some` and
     `Fintype.ofFinite ↥s = (nonempty_fintype ↥s).some` differ only by a *proof* argument, and
     Lean's definitional proof irrelevance makes them defeq. The genuine friction is
     *syntactic*: the `Set.Finite.*` API lemmas (`Set.Finite.mem_toFinset`,
     `Set.Finite.toFinset_nonempty`) do not fire against the `Set.toFinset` spelling, and
     `assumption` fails across the two forms. Worth fixing; just not a diamond.
  2. `minRelHammingDistCode_of_empty`, `_mem`, `_le` and
     `minDist_div_card_eq_minRelHammingDistCode` have **zero** consumers repo-wide (the first
     three are used only by the fourth, which is used nowhere), so the docstring's "downstream
     proofs that need to manipulate `Finset.min'` of this set" is forward-looking.
- **Evidence**:
  - `(session-local probe) r3-reldist.lean`: `example (C) : minRelHammingDistCodeOld C = minRelHammingDistCode C := by rfl` **compiles**, where `minRelHammingDistCodeOld` is the verbatim `origin/main` body. Semantics preserved exactly.
  - The same file's `Probe2` section reproduces the friction: proving `_mem` against the old
    body needs a re-introduced `haveI`, and then `assumption`/`rwa` fails on
    `(possibleRelHammingDists C).toFinset.min' ⋯ ∈ possibleRelHammingDists C`
    vs the syntactically-different instance.
  - `grep -rn "minRelHammingDistCode" ArkLib/ | grep -v Basic/RelativeDistance.lean` → empty.
- **Refutation attempt**: I tried to find a downstream `rw`/`simp` that the old spelling would
  break — none exists, because nothing downstream uses `minRelHammingDistCode` at all.
- **Suggested fix**: reword "diamond" → "instance-spelling mismatch that keeps the
  `Set.Finite.*` simp lemmas from firing".

---

### [LOW] `set_option linter.unusedFintypeInType false` in `HammingBallVolume.lean` is unnecessary; the `unusedDecidableInType` suppression is file-scoped when it need not be

- **Where**: `ArkLib/Data/CodingTheory/HammingBallVolume.lean:31-32`.
- **Evidence**: `(session-local probe) r3-hbv-nolint.lean` is the file with both `set_option`s stripped.
  Under `lake env lean -DautoImplicit=false -Dlinter.mathlibStandardSet=true` the *only* warning
  is
  ```
  warning: `hammingBallVolume_eq_ncard_hammingBall` does not use the following hypotheses in its type:
    • [DecidableEq ι] (#3)   • [DecidableEq F] (#6)
  ```
  i.e. `unusedFintypeInType` never fires, and `unusedDecidableInType` fires on exactly one
  declaration.
- **Note (informational, not a defect)**: the reason `[DecidableEq ι]`/`[DecidableEq F]` are
  unused *in the type* is that `ListDecodable.hammingBall` is defined under `open Classical in`,
  so it bakes in `Classical.propDecidable` rather than the ambient instance. That is why the
  proof needs `convert hx using 2` twice. The theorem is still correct — I validated it
  numerically (see clean bill).
- **Suggested fix**: drop the `unusedFintypeInType` line; move the `unusedDecidableInType`
  suppression to an attribute/`set_option … in` immediately above the one theorem.

---

### [LOW] `Entropy.lean` module header states the domain as `(0, 1)`; ABF26 D2.2 says `[0, 1]`

- **Where**: `ArkLib/Data/CodingTheory/Basic/Entropy.lean:13`.
- **Source**: ABF26 D2.2 (`(pdftotext of ~/abf26-refs/) ABF26.txt:320`) — "the q-entropy function is the function
  `H_q : [0, 1] → R`".
- **What's wrong**: cosmetic; the Lean definition is total and the *definition* docstring
  correctly discusses `x = 0` and `x = 1`. Only the module header disagrees with the paper.

---

### [LOW] Missed reuse: `qEntropy` could be *defined* as `Real.qaryEntropy q x / Real.log q`

- **Where**: `ArkLib/Data/CodingTheory/Basic/Entropy.lean:46`.
- **What's wrong**: the file already proves `qEntropy q x = Real.qaryEntropy q x / Real.log q`
  unconditionally. Taking that as the *definition* would make the bridge `rfl` and let the file
  inherit Mathlib's `qaryEntropy` API (`qaryEntropy_pos`, monotonicity, continuity,
  `qaryEntropy_two`) for free with a single `div_pos`. As written, none of that API is reachable
  without going through the bridge each time. Not a duplication (Mathlib has no base-`q`
  normalisation — `grep logb Mathlib/Analysis/SpecialFunctions/BinaryEntropy.lean` → empty), so
  the definition is justified; only the *spelling* leaves value on the table.
- **Suggested fix**: consider `noncomputable def qEntropy (q : ℕ) (x : ℝ) : ℝ := Real.qaryEntropy q x / Real.log q`
  with the current formula as a `lemma qEntropy_eq`.

---

### [LOW] `Lambda_ne_top` docstring references downstream `.toNat` uses that do not exist

- **Where**: `ArkLib/Data/CodingTheory/ListDecodability.lean:144-147` — "This is what makes the
  downstream `(Lambda C δ).toNat` occurrences (e.g. in the ABF26 §6 soundness error terms)
  faithful".
- **What's wrong**: `grep -rn "Lambda.*toNat" ArkLib/` finds nothing outside this docstring;
  `Lambda_ne_top` itself has zero consumers. Fine as forward-looking intent, but it is phrased
  in the present tense.

---

## Clean bill

Verified correct / faithful / non-duplicative:

**ABF26 D2.2 → `CodingTheory.qEntropy` (Entropy.lean:46).**
Paper (`ABF26.txt:320-324`): `H_q(x) = x·log_q(q−1) − x log_q(x) − (1−x)·log_q(1−x)`.
Lean is a term-for-term match, including the `(q:ℝ) − 1` (which agrees with Mathlib's
`((q:ℤ) − 1 : ℝ)` for all `q : ℕ`). Numerically validated in `r3-entropy.lean`:
`qEntropy 2 (1/2) = 1` and `qEntropy 3 (2/3) = 1` — both proved, i.e. the base-`q` (not
natural-log) normalisation is right and it is *not* Mathlib's `qaryEntropy`.
`qEntropy_zero`, `qEntropy q 1 = logb q (q−1)`, and the degenerate `q ∈ {0,1} ⇒ 0` behaviour
all proved. `qEntropy_eq_qaryEntropy_div_log` is TRUE and genuinely unconditional (I compiled
the `q = 0` instance, where both sides are `0/0 = 0`); axiom-clean.

**ABF26 D2.4 → `hammingBallVolume` (HammingBallVolume.lean:51).**
Paper (`ABF26.txt:344-350`): `Vol_q(δ,n) = Σ_{i=0}^{⌊δ·n⌋} C(n,i)·(q−1)^i`.
`Finset.range (⌊δ*n⌋₊ + 1)` is exactly `i = 0 … ⌊δn⌋`; `Nat.floor` agrees with `⌊·⌋` on the
paper's domain `δ ∈ (0,1)`, `n ≥ 0`. Concrete values proved: `Vol_2(1/2,4) = 11`,
`Vol_3(2/5,5) = 51`. The `q = 0`/`δ ≤ 0` total-extension caveats in the docstring are accurate
(`hammingBallVolume 0 (1/2) 4 = 1` proved). No Mathlib duplicate (no Hamming-ball cardinality
lemma exists there).

**`hammingBallVolume_eq_ncard_hammingBall` + `card_filter_hammingDist_eq`.**
Both fully proven, no sorry, axioms `[propext, Classical.choice, Quot.sound]`. Validated at a
concrete non-degenerate instance: `|B(y,1)| = 3` in `Bool^{Fin 2}` for *any* centre `y`
(compiled in `r3-vol-lambda.lean`), so the "independent of the centre" claim is exercised.
The bijection proof in `card_filter_hammingDist_eq` is a real counting argument, not a
`decide`/`simp` cheat.

**ABF26 D2.8 → `Lambda` (ListDecodability.lean:93) — the anti-duplication item.**
Paper (`ABF26.txt:384-392`): `Λ(C,δ,f) := {g ∈ C | Δ(f,g) ≤ δ}`, `|Λ(C,δ)| := max_f |Λ(C,δ,f)|`.
The claim "reformulation, not a fork" **holds up**:
- the point list is *not* re-defined — `Lambda` is literally `⨆ f, ((closeCodewordsRel C f δ).ncard : ℕ∞)`
  over the pre-existing `closeCodewordsRel` (ListDecodability.lean:42), and no `Lambda_at` alias
  was added;
- the sup is over **all** centres `f : ι → F`, matching the paper's `max_f`;
- `Lambda_le_iff_listDecodable` is a genuine `↔` (both sides unfold to `∀ f, ncard ≤ ℓ` in `ℕ`),
  not a one-directional bridge;
- `Lambda` has real consumers already (`JohnsonBound/Family.lean:408,604,783`,
  `ExtensionCodes.lean:317`), so it is not speculative;
- I searched for a pre-existing sup-form list size (`grep -rn "Lambda\|listSize\|maxList\|⨆.*ncard"`)
  — nothing before this PR;
- edge cases behave: `Lambda ∅ δ = 0` (proved), `Lambda_mono`, `Lambda_le_ncard`,
  `Lambda_le_card`, `Lambda_ne_top` all correctly gated on `[Finite F]`/`C.Finite`.
The two residual complaints are the MEDIUMs above (real-`ℓ` bridge gap; infinite-alphabet
`ncard = 0`), neither of which is a duplication.

**ABF26 D6.4 → `SupportsErasureCorrection`; L6.5 → `additive_code_supports_erasure_correction_grs12`.**
Clause-by-clause faithful to `ABF26.txt:1323-1333`, including the direction of the guard:
`|f⁻¹(⊥)| < δmin(C)·n` is rendered as `#{i | f i = none} < Code.minDist C`, which is right
because `δmin(C) = minDist(C)/n`. `∀ i, f i = some (u i) ∨ f i = none` is exactly
"`f(i) = u(i)` for all `i ∈ [n] \ f⁻¹(⊥)`". Clause (ii) matches "otherwise `E_C(f) = ⊥`".
Cross-checked the [GRS12] citation: Guruswami–Rudra–Sudan *Essential Coding Theory*
Proposition 1.4.2(4), "C can correct `d − 1` erasures" ⟺ min distance `d`
(`GuruswamiRS12.txt:929`, with the converse argued at `:1054`) — the `< minDist` guard is the
right threshold, and the polynomial-time half (Exercise 5.3 / Gaussian elimination) is
explicitly and correctly declared out of scope.
`eq_of_consistent_with_erased` is a real pigeonhole (disagreement set ⊆ erasure set ⇒
`Δ₀(u,v) < minDist`), no cheat; both declarations axiom-clean.

**`disagreementCols` + `hammingDist_eq_disagreementCols_card` (Distance.lean:149,159).**
Genuinely new as a *named* primitive: no Mathlib equivalent (Mathlib inlines
`hammingDist x y = #{i | x i ≠ y i}`, `InformationTheory/Hamming.lean:41`), and every existing
ArkLib `disagreementSet` is a specialisation with extra structure
(`Stir/Quotienting.lean:52` — polynomial-evaluation over a subset;
`Binius/BinaryBasefold/Prelude.lean:1042,1051` — folded/fiberwise;
`DG25/MainResults.lean:57` — interleaved pairs; `Basic/BlockRelDistance.lean:42` — block-fibers).
Both new declarations are `rfl`-true against the Mathlib unfolding (compiled in
`r3-mindist.lean`), so `hammingDist_eq_disagreementCols_card` is sound and the `@[simp]`
`mem_disagreementCols` is safe. The three `closeToWord_iff_exists_possibleDisagreeCols` proof
rewrites are cosmetic and preserve the statement.

**`minDist_div_card_eq_minRelHammingDistCode` (RelativeDistance.lean:623).**
Statement is true and correctly typed (`(minDist C : ℚ)/n = (δᵣ C : ℚ)`, `[Nonempty ι]` so
`n > 0`). The proof is a genuine `le_antisymm` through the image identification
`possibleRelHammingDists C = (·/n) '' S_nat`, with the `C` subsingleton branch handled
explicitly. Axiom-clean. Instantiated at a non-degenerate code `C = {00, 11} ⊆ (Fin 2 → Fin 2)`
in `r3-mindist.lean`: `0 < (δᵣ C : ℚ)` proved through the bridge, so it is not a `0 = 0`
degeneracy.

**Semantics of the `minRelHammingDistCode` refactor.** Preserved *definitionally* — the
verbatim `origin/main` body and the new body are `rfl`-equal (compiled). Nothing downstream can
have changed meaning.

**No sorries, no non-standard axioms** in any of the six files (`grep -rn sorry` → exit 1;
`#print axioms` on `qEntropy_eq_qaryEntropy_div_log`, `hammingBallVolume_eq_ncard_hammingBall`,
`card_filter_hammingDist_eq`, `additive_code_supports_erasure_correction_grs12`,
`eq_of_consistent_with_erased`, `minDist_div_card_eq_minRelHammingDistCode`,
`Code.disagreementCols`, `Code.hammingDist_eq_disagreementCols_card` → all
`[propext, Classical.choice, Quot.sound]` or less).

**Audit doc** `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md`
rows `D2.2` (:31), `D2.4` (:33), `D2.8` (:37), `D6.4` (:111), `L6.5` (:112) are accurate,
including the explicit "only existence is formalized" caveat on L6.5. (Contrast the wiki
finding above.)
