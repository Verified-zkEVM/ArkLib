# R2 — `ArkLib/Data/Probability/Combinatorial.lean` (ABF26 Claim B.1)

Reviewer: R2 (`R2-combinatorial`). Commit `ffa0733a`.
Probes: `(session-local probe) R2-{a,b,c,d,e,f}.lean` (all compiled with `lake env lean`).

**Headline: no CRITICAL, no HIGH.** The theorem is a clause-exact formalization of ABF26
Claim B.1, it is genuinely proven (axiom-clean), it is **not vacuous** (compiled concrete
instance with a strictly-informative conclusion), the Cauchy–Schwarz step points the right
way, both helper lemmas are independently true (brute-forced by `decide` over all
`Fin 4 → Fin 3`), and I found **no Mathlib or ArkLib duplication**. Findings below are
2 MEDIUM (both documentation/citation) and 6 LOW.

---

## Clause-by-clause faithfulness (mandate item 1) — PASS

ABF26 Appendix B (`(pdftotext of ~/abf26-refs/) ABF26.txt:2278`), verbatim:

> **Claim B.1.** Let S, T be finite sets and let Φ be a distribution on functions from S to T
> such that for any distinct x, y ∈ S,
>   Pr_{ϕ←Φ}[ϕ(x) = ϕ(y)] ≤ ϵ .
> Then there exists some ϕ in the support of Φ such that
>   |ϕ(S)| ≥ |S| / (1 + (|S| − 1) · ϵ).

| Paper clause | Lean (`Combinatorial.lean:195-201`) | Verdict |
|---|---|---|
| `S` finite set | `{S : Type} [Fintype S]` | match |
| `T` finite set | `{T : Type} [DecidableEq T]` | **strictly more general** (finiteness of `T` not needed); harmless |
| `Φ` distribution on `S → T` | `Φ : PMF (S → T)` | match |
| `ϵ` | `ε : ENNReal` | more general (paper implicitly `ϵ ∈ [0,1]`); statement stays true, incl. `ε = ⊤` |
| `∀ distinct x,y` | `∀ x y : S, x ≠ y → …` | match (ordered vs unordered is immaterial, event is symmetric) |
| `Pr_{ϕ←Φ}[ϕ(x)=ϕ(y)] ≤ ϵ` | `Pr_{ let φ ← Φ }[(decide (φ x = φ y) : Prop)] ≤ ε` | match; `decide`-form is propositionally identical (probe `R2-d.lean`, closed by `simp only [decide_eq_true_eq]`) |
| `∃ ϕ ∈ supp Φ` | `∃ φ ∈ Φ.support` | match |
| `\|ϕ(S)\|` | `(Finset.univ.image φ).card` | match |
| `≥ \|S\| / (1 + (\|S\|−1)·ϵ)` | `≥ (Fintype.card S : ENNReal) / (1 + ((Fintype.card S : ENNReal) - 1) * ε)` | match |

Pretty-printed elaborated statement (probe `R2-a.lean`, `pp.numericTypes`) confirms the
`- 1` is **ENNReal** truncated subtraction, not `Nat`:
`↑(Fintype.card S) / (1 + (↑(Fintype.card S) - (1:ℝ≥0∞)) * ε)`.
For `N ≥ 1` this is exact; for `N = 0` both sides collapse to the (correct, trivial) `0 ≥ 0`.
No drift in either direction. **No truncated-subtraction rescue anywhere in the bound.**

The internal `((N * (N - 1) : ℕ) : ENNReal)` (Step B) *is* `Nat`-subtraction, but it is
justified by the proved `hP_card : P.card = N * (N - 1)` (`Finset.offDiag_card`), i.e. it is
the true off-diagonal count, and `h_NC_cast` transfers it to ENNReal via
`ENNReal.natCast_sub`. Correct for all `N`, including `N = 0`.

Paper's proof route (Jensen on `|S|²/(2|C_ϕ|+|S|)`) vs Lean's (contradiction + strict
averaging) differ, and the docstring says so honestly ("contradiction-form, avoids Jensen").
The two `|C_ϕ|`-normalisations line up: `numCollsOrdered = 2·|C_ϕ|`, paper's
`E[|C_ϕ|] ≤ C(|S|,2)·ϵ` ⇔ Lean's `h_lin : E[numCollsOrdered] ≤ N(N−1)ε`. Verified by
`#eval`: `numCollsOrdered (const : Fin 3 → Fin 2) = 6 = 2·C(3,2)`, `numCollsOrdered id = 0`,
`numCollsOrdered (mod 2 : Fin 4 → Fin 2) = 4`.

## Vacuity (mandate item 2) — PASS, compiled non-degenerate instance

`(session-local probe) R2-b.lean` (compiles clean, no `sorry`):

- `S = T = Fin 2`, `Phi := PMF.uniformOfFintype (Fin 2 → Fin 2)`, `ε = 1/2`.
- `hPhi` : the hypothesis `Pr_{φ ← Phi}[decide (φ x = φ y)] ≤ 1/2` is **proved** for all
  `x ≠ y` (so the hypotheses are jointly satisfiable at a *non-zero* ε with a genuine
  mixture distribution, not just at the degenerate `ε = 0`).
- `rhs_gt_one` : the RHS `2 / (1 + (2−1)·(1/2)) = 4/3 > 1` is **proved**.
- `concrete_two` : instantiating the theorem yields `∃ φ ∈ Phi.support, 2 ≤ #(image φ univ)`,
  i.e. it *forces an injective φ in the support*. Strictly informative conclusion.

Degenerate corners checked and all behave correctly rather than hiding a bug:
`ε ≥ 1` ⇒ RHS `= 1` (matches paper, trivially true); `ε = ⊤` with `N ≥ 2` ⇒ denominator `⊤`,
RHS `= 0` (uninformative, as it should be); `S` empty ⇒ RHS `= 0`. The denominator is
`1 + …  ≥ 1`, so **no division-by-zero collapse is possible** and the RHS is never `⊤`
spuriously.

## Proof correctness / CS direction (mandate items 3, 4) — PASS

- `sq_sum_le_card_mul_sum_sq : (∑ f)^2 ≤ #s * ∑ f^2` is used with `s = image φ`,
  `f = fiber card`, giving `N² ≤ |image φ| · (N + numCollsOrdered φ)`, i.e.
  `|image φ| ≥ N²/(N+C)`. **Right direction** — the inequality is the one that lower-bounds
  the image, not the one that upper-bounds it. No `max 0` / `Nat`-sub rescue.
- Both helpers brute-forced over **all 81 maps `Fin 4 → Fin 3`** by `decide`
  (`R2-a.lean`), both statements hold; no counterexample exists at these sizes:
  - `sum_fiber_sq_eq : ∑_{μ ∈ image} |fiber μ|² = |S| + numCollsOrdered φ` — verified.
  - `cauchy_schwarz_fiber : |S|² ≤ |image φ| · (|S| + numCollsOrdered φ)` — verified.
- `#print axioms` (`R2-c.lean`): all three of
  `exists_large_image_of_pairwise_collision_bound`, `cauchy_schwarz_fiber`,
  `sum_fiber_sq_eq` depend only on `[propext, Classical.choice, Quot.sound]`.
  **No `sorryAx`, no non-standard axiom.**
- `hΦ` is load-bearing (used at line 253 to bound each of the `N(N−1)` indicator terms);
  removing it makes the statement false (take `Φ = pure (const c)`, `ε = 0`).
- `Pr_decide_eq_tsum_indicator` (the only new dependency, `Notation.lean` +11) is an
  *equality*, so no directionality risk; it is proved, and its LHS is literally the
  `Pr_{…}[…]` macro expansion.
- The file compiles with **zero warnings** (`lake env lean ArkLib/Data/Probability/Combinatorial.lean`)
  and `python3 scripts/lint-style.py` on it exits 0.

## Duplication (mandate item 5) — none found

- Mathlib: no `∑ fiber²` identity exists. `leansearch`/`loogle` return only
  `Finset.addEnergy_eq_sum_sq'` (additive-combinatorics-specific, `s + t` fibers, not
  general `f`-fibers) and the `Mathlib.Combinatorics.Pigeonhole` family
  (`Fintype.exists_le_card_fiber_of_mul_le_card` etc.), which bound a *single* fiber, not
  the image. `Finset.exists_ne_map_eq_of_card_image_lt` is the pigeonhole converse, not this.
  `Mathlib.Probability.BirthdayProblem` is about injectivity probability of a *uniform* map
  and does not subsume this.
- `sq_sum_le_card_mul_sum_sq` (Mathlib Chebyshev) **is** reused rather than reproven — good.
- `Finset.card_eq_sum_card_image`, `Finset.card_eq_sum_card_fiberwise`, `Finset.offDiag_card`
  are all reused — good.
- ArkLib: `grep -rniI "collision\|colliding\|birthday" ArkLib/` finds only
  FiatShamir/DuplexSponge hash-collision events, RingSwitching commitment collisions, and
  `Stir/OutOfDomSmpl.listDecodingCollisionProbability` — all semantically unrelated.
  No pre-existing image-size / fiber-square lemma anywhere in `ArkLib/`.

---

# Findings

### [MEDIUM] Docstring attributes "two applications of Claim B.1" to ABF26 Lemma 6.12; the paper applies it exactly once
- **Where**: `ArkLib/Data/Probability/Instances.lean:705-712` (section docstring
  `## Linear-form collision bounds (ABF26 §6.4.1 / Claim B.1 inputs)`), which is the only
  place in the tree that names a consumer of
  `Probability.exists_large_image_of_pairwise_collision_bound`.
- **Source**: `(pdftotext of ~/abf26-refs/) ABF26.txt`. `grep -n "Claim B" ABF26.txt` returns exactly two
  hits: line 1972 (`"and thus by Claim B.1 it holds that there exists a v ∈ Fk such that"`)
  and line 2278 (the statement itself). The *second* counting step in Lemma 6.12 — choosing
  `µ1 ∈ F \ B` so that `ψ : Sv → Γ_{µ1,µ2}` is injective — is a plain pigeonhole:
  > "Since |B| ≤ (|Sv| choose 2) ≤ |Λ(C^≡2,δ)| < |F| … it must be that there exists
  > µ1 ∈ F \ B, and then ψ is injective."
  That is *not* an application of Claim B.1.
- **What's wrong**: the docstring says the two new lemmas feed "the two applications of
  Claim B.1 … in the proof of ABF26 Lemma 6.12", asserting something about the source that
  the source does not do. Beyond the misattribution there is a forward-looking risk: if the
  planned Lean route really does replace the `µ1 ∉ B` pigeonhole by a *second* invocation
  of B.1 (which is what `prob_uniform_le_inv_of_card_le_one`, described as "the second
  B.1's affine bound", suggests), the resulting bound will be **weaker than Lemma 6.12 as
  printed** — B.1 yields `|ψ(Sv)| ≥ |Sv|/(1+(|Sv|−1)/|F|)`, not the injectivity
  `|Γ| ≥ |Sv|` the paper's bound needs.
- **Evidence**: exact PDF quotes above; `grep -c "Claim B" (pdftotext of ~/abf26-refs/) ABF26.txt` = 2.
- **Refutation attempt**: I read the whole of Lemma 6.12 (`ABF26.txt:1950-2020`) and
  Lemma 6.13 looking for a second B.1 use, and grepped the full text for "B.1". There is
  none. I also considered that "two applications" might mean "two applications in the
  forthcoming ArkLib proof" — but the sentence explicitly says "in the proof of ABF26
  Lemma 6.12".
- **Suggested fix**: reword to "the pairwise-collision inputs for ABF26 Lemma 6.12: the one
  application of Claim B.1 (`prob_dotProduct_eq_zero_le`) and the pigeonhole step for
  choosing `µ1` (`prob_uniform_le_inv_of_card_le_one`)". If the plan really is a second B.1
  call, say so and note the resulting bound differs from the paper's.

### [MEDIUM] Citation key `[ABF26]` has no BibTeX entry, contrary to CONTRIBUTING's Citation Standards
- **Where**: `ArkLib/Data/Probability/Combinatorial.lean:18-22` (module `## References`), and
  `:159` (`**Claim B.1 of [ABF26]**`).
- **Source**: `CONTRIBUTING.md:228` — "**Add BibTeX entries**: All academic papers must have
  entries in `blueprint/src/references.bib`. When adding a new paper, add the BibTeX entry,
  use the citation key in your Lean file, and list it in the References section."
- **What's wrong**: `grep -c "ABF26" blueprint/src/references.bib` → `0`. The reference
  line is otherwise correctly formatted and the author/title match the paper
  (`ABF26.txt:1-5`: "Open Problems in List Decoding and Correlated Agreement", Gal Arnon,
  Dan Boneh, Giacomo Fenzi), so this is purely the missing bib entry.
- **Evidence**: `grep -c "ABF26" blueprint/src/references.bib` = 0; the only `ABF26` hits
  outside `ArkLib/*.lean` are in `docs/`.
- **Refutation attempt**: checked for alternate spellings (`abf26`, `Arnon.*Boneh`) in
  `references.bib` — the three `Arnon` entries there are all ACFY (Arnon–Chiesa–Fenzi–Yogev),
  a different paper. Also confirmed this is not pre-existing on `main`:
  `git grep -l ABF26 origin/main -- 'ArkLib/*.lean'` is empty.
- **Scope note**: branch-wide — 16 files on this branch cite `[ABF26]`. Fix once in the bib.
- **Suggested fix**: add the `@misc{ABF26, …}` entry to `blueprint/src/references.bib`.

### [LOW] Conclusion is stated with `≥`, which CONTRIBUTING explicitly tells us to avoid
- **Where**: `Combinatorial.lean:200` (`exists_large_image_of_pairwise_collision_bound`).
- **Source**: `CONTRIBUTING.md:140` — "> **Note**: In adherence with mathlib, we standardize
  on `≤` (`le`) and `<` (`lt`). Avoid `≥` (`ge`) and `>` (`gt`) in theorem statements unless
  necessary for argument ordering."
- **What's wrong**: `((image φ univ).card : ENNReal) ≥ N / (1 + (N-1)*ε)`. Nothing here needs
  argument ordering. Practical cost: consumers must `rw [ge_iff_le]` before `gcongr`/`calc`/
  `le_trans` — I hit this in probe `R2-b.lean`.
- **Evidence**: probe `R2-b.lean` (`concrete_two` needs `le_trans hcard h1` to work around it).
- **Suggested fix**: state as `N / (1 + (N-1) * ε) ≤ (#(image φ univ) : ENNReal)`.

### [LOW] Broken doc reference: `Finset.sq_sum_le_card_mul_sum_sq` does not exist
- **Where**: `Combinatorial.lean:118` (docstring of `cauchy_schwarz_fiber`).
- **What's wrong**: the lemma lives in the **root** namespace
  (`Mathlib/Algebra/Order/Chebyshev.lean:137`, no enclosing `namespace Finset` in that file);
  the proof at line 133 correctly calls it unqualified, only the docstring is wrong.
- **Evidence**: probe `R2-e.lean` → `error: Unknown constant 'Finset.sq_sum_le_card_mul_sum_sq'`;
  `grep -n "^namespace" Mathlib/Algebra/Order/Chebyshev.lean` shows no `Finset` namespace.
- **Suggested fix**: drop the `Finset.` prefix (line 178 of the same file already gets it right).

### [LOW] Module docstring claims the module is "used elsewhere in ArkLib"; nothing consumes it
- **Where**: `Combinatorial.lean:14` — "Stand-alone probabilistic-combinatorics statements
  used elsewhere in ArkLib."
- **What's wrong**: the only importer is the generated `ArkLib.lean:209`. No `.lean` file
  references `exists_large_image_of_pairwise_collision_bound` except a *docstring* in
  `Instances.lean:708`. The intended consumer (ABF26 Lemma 6.12) is explicitly recorded as
  **missing**: `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md:118`
  — "| Lemma 6.12 list-decoding lower-bound attack | missing | none |".
- **Evidence**: `grep -rn "exists_large_image_of_pairwise_collision_bound" --include=*.lean .`
  → 2 hits, both docstrings.
- **Refutation attempt**: this is *not* a "speculative/dead code" flag — it is on a stated
  roadmap (`Instances.lean:709` "formalised in a later split of the ABF26 development", plus
  audit row `:137` "Claim B.1 … present … Proven sorry-free", which is accurate). So the
  finding is only that the docstring's present tense is false today.
- **Suggested fix**: "…statements intended for the ABF26 §6.4.1 development (Lemma 6.12),
  which lands in a later split."

### [LOW] Missed generalization: the `CollidingPairs` section is pure `Finset` combinatorics, needlessly pinned to `Type` + `Fintype` + `namespace Probability`
- **Where**: `Combinatorial.lean:33-157` (`numCollsOrdered`, `sum_fiber_sq_eq`,
  `cauchy_schwarz_fiber`); `variable {S T : Type} [Fintype S] …` at line 35.
- **What's wrong**: three things at once.
  (a) Nothing in this section mentions probability; it lives in
  `ArkLib/Data/Probability/` under `namespace Probability`. `ArkLib/ToMathlib/Finset/` and
  `ArkLib/Data/Finset/` both exist and are the natural homes.
  (b) `Type` instead of `Type*` — `CONTRIBUTING.md:102` uses `Type*` as the convention. The
  restriction to `Type 0` is *justified* for the main theorem (the `Pr_{…}` do-notation needs
  a single universe — documented in `Notation.lean:24-26`) but not for these three.
  (c) `Fintype S` + `Finset.univ` instead of an arbitrary `s : Finset S`.
- **Evidence**: probe `R2-f.lean` — the `Type*` + arbitrary-`Finset` restatements of
  `numCollsOrdered` and `sum_fiber_sq_eq` elaborate without error.
- **Refutation attempt**: I checked whether the main theorem forces `Fintype S` on the
  helpers — it does not; `cauchy_schwarz_fiber` is applied at `Finset.univ` only, so the
  general form specialises for free. I also checked `ArkLib/ToMathlib/Finset/Basic.lean`;
  it is a `Finset ℕ` grab-bag, so the case for moving there is real but not overwhelming.
- **Suggested fix**: generalise to `{S T : Type*}` + `(s : Finset S)` and relocate to
  `ArkLib/ToMathlib/Finset/`, leaving only the PMF theorem in `Data/Probability/`.

### [LOW] Naming does not follow ArkLib/Mathlib statement-derived conventions
- **Where**: `Combinatorial.lean:42` (`numCollsOrdered`), `:50` (`sum_fiber_sq_eq`),
  `:122` (`cauchy_schwarz_fiber`).
- **Source**: `CONTRIBUTING.md:78` "Theorem Naming Logic" + `:114` "Symbol Naming Dictionary".
- **What's wrong**: `sum_fiber_sq_eq` has an `_eq` with no RHS descriptor;
  `cauchy_schwarz_fiber` names the *technique*, not the statement (Mathlib names the same
  inequality `sq_sum_le_card_mul_sum_sq`); `numCollsOrdered` abbreviates "collisions" to
  "Colls". The main theorem name is fine.
- **Suggested fix**: e.g. `numOrderedCollisions`,
  `sum_sq_card_fiber_eq_card_add_numOrderedCollisions`,
  `sq_card_le_card_image_mul_card_add_numOrderedCollisions`.

### [LOW] Hypothesis uses the `decide`-coercion form, unlike every other `Pr_` lemma in the tree
- **Where**: `Combinatorial.lean:199` —
  `Pr_{ let φ ← Φ }[(decide (φ x = φ y) : Prop)] ≤ ε`.
- **What's wrong**: the sibling lemmas added by this same PR state events as plain `Prop`s
  (`Instances.lean:194` `Pr_{ let v ←$ᵖ (Fin k → F) }[ (∑ j, d j * v j = 0) ]`;
  `Instances.lean:173` `Pr_map_eq … [ Q b ]`). A consumer chaining
  `prob_dotProduct_eq_zero_le` into B.1 must insert a bridge step. This is *not* a soundness
  or strength issue.
- **Evidence / refutation attempt**: I tried to make this a real defect and failed — probe
  `R2-d.lean` proves
  `Pr_{let φ ← Φ}[(decide (φ x = φ y) : Prop)] = Pr_{let φ ← Φ}[φ x = φ y]`
  by the one-liner `simp only [decide_eq_true_eq]`. So it is friction only. Demoted to LOW.
- **Suggested fix**: state the hypothesis as `Pr_{ let φ ← Φ }[φ x = φ y] ≤ ε` and do the
  `decide` bridge internally after `classical` (`[DecidableEq T]` is already required by the
  conclusion, so nothing is lost).

---

## Clean bill

Checked and found genuinely OK:

1. **Statement vs source, clause by clause** — probability space, sampled object, event,
   quantifier over distinct pairs, `∃ φ ∈ support`, image cardinality, and the exact bound
   `|S|/(1+(|S|−1)ε)`. Table above. No weakening, no over-claiming. Generalization
   (drops `T` finite, allows `ε : ENNReal`) is safe and in the harmless direction.
2. **Non-vacuity** — compiled instance `R2-b.lean`: `Fin 2 → Fin 2`, uniform `Φ`, `ε = 1/2`
   (a genuine mixture, not `ε = 0`), RHS `= 4/3 > 1`, conclusion forces an injective `φ` in
   the support. All hypotheses discharged, no `sorry`.
3. **Degenerate corners** — `S = ∅`, `|S| = 1`, `ε ≥ 1`, `ε = ⊤` all give the correct
   (trivial-but-true) reading; denominator `≥ 1` always, so no `x/0` collapse.
4. **ENNReal truncated subtraction** — `(↑N - 1 : ENNReal)` verified by
   `set_option pp.numericTypes`; exact for `N ≥ 1`, harmless at `N = 0`. Internal
   `Nat`-subtraction `N*(N-1)` is backed by the proved `Finset.offDiag_card` count.
5. **Cauchy–Schwarz direction** — `(∑f)² ≤ #s · ∑f²` used to *lower*-bound the image;
   correct, and not rescued by any `max 0` / `Nat`-sub.
6. **Helper lemmas independently true** — `sum_fiber_sq_eq` and `cauchy_schwarz_fiber`
   brute-forced by `decide` over all 81 maps `Fin 4 → Fin 3` (`R2-a.lean`); plus `#eval`
   sanity of `numCollsOrdered` (6 / 0 / 4 on three witnesses) confirming it counts *ordered*
   pairs, i.e. `= 2·|C_φ|` as the docstring claims.
7. **Axiom hygiene** — all three declarations: `[propext, Classical.choice, Quot.sound]`.
   No `sorryAx`, no custom axiom (`R2-c.lean`).
8. **New dependency** `ProbabilityTheory.Pr_decide_eq_tsum_indicator` (`Notation.lean` +11) —
   an equality, correctly stated as the standard indicator tsum; no directional risk.
9. **Load-bearing hypotheses** — `hΦ` is used; the theorem is false without it.
10. **No duplication** — Mathlib (`leansearch`, `loogle`, grep over
    `Mathlib/Algebra/BigOperators`, `Mathlib/Combinatorics/Pigeonhole`,
    `Mathlib/Combinatorics/Additive/Energy`, `Mathlib/Probability/BirthdayProblem`) and
    ArkLib (`grep -rniI "collision\|colliding\|birthday" ArkLib/`) both come up empty for
    this statement. Mathlib's `sq_sum_le_card_mul_sum_sq`, `card_eq_sum_card_image`,
    `card_eq_sum_card_fiberwise`, `offDiag_card` are correctly *reused*, not reproven.
11. **Build hygiene** — `lake env lean ArkLib/Data/Probability/Combinatorial.lean` emits
    zero warnings (relevant: the `ArkLib/Data` zero-warning gate);
    `python3 scripts/lint-style.py` on the file exits 0; 352 lines, well under the 1500 cap.
12. **Audit-doc honesty** — `docs/kb/audits/open-problems-list-decoding-and-correlated-agreement.md:137`
    describes Claim B.1 as "present … Proven sorry-free" with an accurate route description,
    and correctly marks Lemma 6.12 itself as "missing" at `:118`. Both accurate.
13. **Proof-sketch docstring** (`:170-194`) — I re-read Steps A/B/C against the tactic script;
    every named lemma (`sq_sum_le_card_mul_sum_sq`, `Summable.tsum_finsetSum`,
    `Pr_decide_eq_tsum_indicator`, `mul_lt_of_lt_div`, `ENNReal.tsum_lt_tsum`) is actually
    used where claimed, and the `N² < N²` contradiction is described accurately.
