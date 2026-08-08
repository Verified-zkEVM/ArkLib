# R1 — `R1-probability` cluster report (PR #701)

Scope: `ArkLib/Data/Probability/Instances.lean`, `.../Notation.lean`, the six `open Probability`
consumers, `ArkLib/Data/Fin/Basic.lean`, `ArkLib/Data/MvPolynomial/EvenAndOdd.lean`.

Headline: **no CRITICAL and no HIGH findings.** The "zero statement drift" claim survives an
exhaustive byte-level check; every new bound is axiom-clean, correct, and non-vacuous (compiled
nondegenerate instances below). What is wrong is *documentation* (one claim about ABF26's proof
that the paper does not support) and *duplication/dead-code hygiene*.

Probes live in `(session-local probe) r1-*.lean`
(SCRATCH = `/tmp/claude-1000/-home-alh-ArkLib-split-pr1/40c8de3b-f989-4146-89bb-f72dc3e52889/scratchpad`).

---

### [MEDIUM] Module docstring attributes to ABF26 Lemma 6.12 a *second* application of Claim B.1 that its proof does not contain — and the route it sketches would be lossy

- **Where**: `ArkLib/Data/Probability/Instances.lean:702-715` (section docstring
  `## Linear-form collision bounds (ABF26 §6.4.1 / Claim B.1 inputs)`), and the docstring of
  `Probability.prob_uniform_le_inv_of_card_le_one` at `:797` ("the second Claim-B.1 application in
  ABF26 Lemma 6.12").
- **Source**: ABF26, proof of Lemma 6.12 (`(pdftotext of ~/abf26-refs/) ABF26.txt:1955-2031`). The string
  "Claim B.1" occurs exactly once in the whole proof, at line 1972: *"and thus by Claim B.1 it holds
  that there exists a v ∈ F^k such that |S_v| ≥ |S| / (1 + (|S|−1)·1/|F|)"*. The `μ₁` step is a
  **pigeonhole**, not a B.1 application: *"Since |B| ≤ (|S_v| choose 2) ≤ |Λ(C^≡2,δ)| < |F| … it must
  be that there exists µ1 ∈ F \ B, and then ψ is injective."* (`:2029-2031`).
- **What's wrong**: two problems.
  (a) Factual: the docstring says "the two applications of Claim B.1 … in the proof of ABF26
      Lemma 6.12". There is one.
  (b) Substantive, forward-looking: the paper's `μ₁` step needs **full injectivity** of
      `ψ : S_v → Γ_{µ1,µ2}`, giving `|Γ| ≥ |S_v|`. Claim B.1 can only deliver
      `|ψ(S_v)| ≥ |S_v| / (1 + (|S_v|−1)/|F|)`. Chaining two B.1 applications therefore yields
      roughly `|S| / (1 + 2(|S|−1)/|F|)`, strictly weaker than Lemma 6.12's advertised
      `|Λ| / (|F| + |Λ| − 1)`. A future split that follows this docstring's plan will not reproduce
      the stated bound.
- **Evidence**: PDF quotes above; `grep -n "B\.1" (pdftotext of ~/abf26-refs/) ABF26.txt` → lines 63 (TOC), 1972,
  2277, 2278 only.
- **Refutation attempt**: I read the entire Lemma 6.12 proof (`:1955-2031`) and the whole of
  Appendix B (`:2277+`) looking for a second B.1 invocation, and considered the reading that "the
  two applications" refers to ArkLib's future proof rather than the paper's. Even under that
  reading (b) stands: B.1's conclusion is strictly weaker than the injectivity the bound needs.
  The *mathematical* content of the two lemmas is faithful — `prob_dotProduct_eq_zero_le` really is
  the paper's `Pr_v[ϕ_v(F1) = ϕ_v(F2)] ≤ 1/|F|` input (`:1970`), and "the affine collision equation
  in `µ1` has at most one solution" really is the paper's
  `µ1 = (µ2(a1−b1) + a1b2 − b1a2)/(b2−a2)` uniqueness (`:2020-2024`). Only the *framing* is wrong.
- **Suggested fix**: say "the pairwise-collision input to the single Claim-B.1 application (ABF26
  Lemma 6.12, p. 35)" and, for `prob_uniform_le_inv_of_card_le_one`, "the uniqueness input to the
  pigeonhole choice of `µ1` (ABF26 Lemma 6.12, p. 36)". Consider restating the second as a
  *counting* lemma (`(univ.filter P).card ≤ 1 → ∃ r, ¬ P r` given `1 < |F|`), which is what the
  paper's argument actually needs.

---

### [MEDIUM] ArkLib already has a strictly more general probabilistic Schwartz–Zippel; the PR generalises the weaker copy without referencing it

- **Where**: new `Probability.prob_schwartz_zippel_mv_polynomial_of_totalDegree_le`
  (`ArkLib/Data/Probability/Instances.lean:550`) and its wrapper
  `Probability.prob_polynomial_identity_le` (`:636`).
- **Source (existing ArkLib decl)**: `prob_eval_zero_le_div` at
  `ArkLib/Data/MvPolynomial/SchwartzZippelCounting.lean:126`:
  ```
  Pr_{let x ←$ᵖ (∀ i, ↥(S i))}[MvPolynomial.eval (fun i => (↑(x i) : F)) f = 0] ≤ (d : ℝ≥0∞) / m
  ```
  under `f ≠ 0`, `f.totalDegree ≤ d`, `0 < m`, `∀ i, m ≤ (S i).toFinset.card`. Taking
  `S i = Set.univ`, `m = |F|` is exactly the new lemma's conclusion. Supporting counting lemmas
  `schwartz_zippel_counting` (`:27`) and `MvPolynomial.card_zeros_le_of_totalDegree_le_fin` (`:151`)
  are in the same file.
- **What's wrong**: after this PR ArkLib carries **two independent probabilistic Schwartz–Zippel
  APIs**, in two modules and two namespaces (root `prob_eval_zero_le_div` vs
  `Probability.prob_schwartz_zippel_mv_polynomial_of_totalDegree_le`), with no cross-reference in
  either direction. The PR touched exactly this lemma and added a docstring paragraph about *where
  helpers should live*, so the omission is visible. (Not literally a duplicate: the sampling types
  differ, `∀ i, ↥(S i)` vs `Fin n → R`, and typeclasses differ `[Field F]` vs
  `[CommRing R] [IsDomain R] [Fintype R]` — equivalent for finite carriers.)
- **Evidence**: `grep -rn "prob_eval_zero_le_div" ArkLib/` → declared at
  `SchwartzZippelCounting.lean:126`, used once at
  `ArkLib/Data/CodingTheory/ProximityGap/ProximityGenerators.lean:230`. Neither file mentions
  `Data/Probability/Instances.lean` and vice versa.
- **Refutation attempt**: I checked whether the new lemma is genuinely unobtainable from the old
  one — it is not *directly* obtainable (`Fin n → R` is not `∀ i, ↥(Set.univ : Set R)`), so this is
  a missed-consolidation finding rather than a strict duplicate. I also checked Mathlib
  (`Mathlib/Algebra/MvPolynomial/SchwartzZippel.lean`): it has
  `schwartz_zippel_sup_sum`/`schwartz_zippel_sum_degreeOf`/`schwartz_zippel_totalDegree`, all
  counting-form in `ℚ≥0`, none in `Pr_` form — so the ArkLib-side probability wrapper is legitimate;
  the problem is having two of them.
- **Suggested fix**: at minimum cross-reference the two modules. Better: state one
  `Probability.prob_schwartz_zippel_*` over `∀ i, ↥(S i)` (or add a `Set.univ` transport lemma) and
  derive both. Note also that `MvPolynomial.schwartz_zippel_sum_degreeOf`
  (Mathlib `SchwartzZippel.lean:179`) gives `≤ ∑ i, degreeOf i / #(S i)`, which is **tighter** than
  routing ABF26 L2.1 through `totalDegree ≤ m·(d−1)`; the paper's bound is the loose one, so the
  current statement is faithful, but the tighter route is one line and worth a remark.

---

### [MEDIUM] `ProbabilityTheory.Pr_decide_eq_tsum_indicator` is documented as a "specialisation" of `prob_tsum_form_singleton` but is a from-scratch re-proof that cannot use it

- **Where**: `ArkLib/Data/Probability/Notation.lean:80-90`.
- **Source**: `Probability.prob_tsum_form_singleton`, `ArkLib/Data/Probability/Instances.lean:49`.
- **What's wrong**: the docstring says *"Specialisation of `Probability.prob_tsum_form_singleton`
  (in `ArkLib.Data.Probability.Instances`)"*. It cannot be: `Instances.lean` **imports**
  `Notation.lean` (`Instances.lean:8`), so the dependency runs the other way. The lemma duplicates
  the `simp only [Bind.bind, Pure.pure, PMF.bind, PMF.pure, DFunLike.coe, …]` unfolding of
  `prob_tsum_form_singleton`. The reason it lives in `Notation.lean` is that its only consumer,
  `ArkLib/Data/Probability/Combinatorial.lean:254`, imports only `Notation.lean` (see
  `Combinatorial.lean:7-9`) — i.e. the placement is an import-avoidance workaround, not a
  specialisation.
- **Evidence**: compiled probe `(session-local probe) r1-dup.lean` (exit 0) shows the lemma is derivable in
  two lines once `Instances` is in scope:
  ```lean
  rw [Probability.prob_tsum_form_singleton p (fun a => (decide (P a) : Prop))]; simp
  ```
- **Refutation attempt**: I checked whether `Combinatorial.lean` could simply import `Instances.lean`
  — it can (no cycle; `Instances` imports `Notation`, `Combinatorial` imports `Notation`), at the
  cost of pulling in `CompPoly.*` and `Mathlib.Algebra.MvPolynomial.SchwartzZippel`. So the
  workaround has a real cost-basis; only the docstring wording and the duplicated proof are
  defects. I also confirmed the lemma statement itself is correct (`decide (P a) : Prop` unfolds to
  `decide (P a) = true ↔ P a`).
- **Suggested fix**: move `prob_tsum_form_singleton` down into `Notation.lean` and derive both
  there; or keep the placement and reword to "re-proved here to keep `Combinatorial.lean`
  independent of `Instances.lean`; see `Probability.prob_tsum_form_singleton` for the same fact".

---

### [LOW] `Fin.induction_three` / `induction_three'` are dead code

- **Where**: `ArkLib/Data/Fin/Basic.lean:99-108`.
- **Evidence**: `grep -rn "induction_three" ArkLib/ --include=*.lean` → only the two declarations.
  (By contrast `Fin.induction_two` has one live use at
  `ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:551`, and `induction_one`/`induction_one'`/
  `induction_two'` are already dead on `main`.)
- **What's checked and OK**: both are correct (`rfl`), axiom set `[propext]` only
  (`(session-local probe) r1-axioms.lean`), they match the existing `induction_one`/`induction_two` pair
  shape exactly (`@[simp]`, `last k` + numeral variant), and they are **not** in Mathlib — Mathlib
  only has the generic `Fin.induction_zero` / `Fin.induction_succ` (verified by `#check`,
  `(session-local probe) r1-fin.lean`), which do not fire on `last 3` / `(3 : Fin 4)`.
- **Suggested fix**: drop them until the PR that needs them, or land them with their consumer.

---

### [LOW] Every new probability declaration in this PR has zero consumers in the repo

- **Where**: `Instances.lean` — `prob_schwartz_zippel_mv_polynomial_of_totalDegree_le` (:550),
  `MvPolynomial.totalDegree_le_of_degreeOf_lt` (:605), `prob_polynomial_identity_le` (:636),
  `Pr_map_eq` (:724), `prob_dotProduct_eq_zero_le` (:745), `prob_uniform_le_inv_of_card_le_one`
  (:799), `prob_uniform_pi_mem_finset_eq` (:817), `prob_uniform_pi_mem_finset_le` (:835).
  Also `ArkLib/Data/Probability/Combinatorial.lean` is imported by nothing except the generated
  `ArkLib.lean:209`.
- **Evidence**: per-name `grep -rl` sweep over `ArkLib/` (recorded in the transcript) returns no
  hits outside `Instances.lean` itself. The pre-existing `prob_schwartz_zippel_mv_polynomial`,
  `Pr_congr`, `Pr_or_le`, `Pr_exists_le`, `Pr_seq_le_of_forall_le`, `prob_tsum_form_doubleton`,
  `prob_split_uniform_sampling_of_equiv_prod` are likewise consumer-free.
- **What's wrong**: nothing is *false*, but nothing exercises these statements either, so the
  shapes (especially the `≤` vs `=` and cast choices below) are unvalidated by any real use. This
  is inherent to a split PR; recording it so a later split is required to actually consume them.
- **Suggested fix**: none required; flag for the reviewer of the follow-up split to confirm the
  shapes survive contact with the Lemma 6.12 proof.

---

### [LOW] `prob_dotProduct_eq_zero_le` proves an equality but is stated as `≤`

- **Where**: `ArkLib/Data/Probability/Instances.lean:745-795`.
- **Evidence**: the proof ends `refine le_of_eq ?_` (`:793`) — the kernel-cardinality argument gives
  `Pr = 1/|F|` exactly (for `d ≠ 0`), and the `≤` is discarded strength.
- **Suggested fix**: state `… = (Fintype.card F : ENNReal)⁻¹` and add a `.le` corollary, matching
  the `prob_uniform_pi_mem_finset_eq` / `_le` pair five lines below.

---

### [LOW] Cast inconsistency inside the new block

- **Where**: `prob_polynomial_identity_le` (`:636`) elaborates its RHS as
  `(↑(↑(m * (d - 1)) : NNReal) : ENNReal) / (↑(↑(Fintype.card R) : NNReal) : ENNReal)` (verified with
  `pp.coercions.types`, `(session-local probe) r1-coe.lean`), inheriting the legacy `ℝ≥0` double coercion
  from `prob_schwartz_zippel_mv_polynomial`, while its four new siblings
  (`prob_dotProduct_eq_zero_le`, `prob_uniform_le_inv_of_card_le_one`,
  `prob_uniform_pi_mem_finset_eq/le`) use plain `ENNReal` casts.
- **Suggested fix**: use `(m * (d - 1) : ENNReal) / (Fintype.card R : ENNReal)` for the new lemma
  (the legacy one must keep its shape for the zero-drift guarantee).

---

### [LOW] `prob_polynomial_identity_le` docstring's `d = 0` analysis is wrong in its first clause

- **Where**: `ArkLib/Data/Probability/Instances.lean:628-632`: *"The `d = 0` case is vacuous —
  `h_indiv_deg : ∀ i, P.degreeOf i < 0` is unsatisfiable in `ℕ`"*.
- **What's wrong**: for `m = 0` the hypothesis `∀ i : Fin 0, …` is vacuously **satisfiable**, so the
  blanket "unsatisfiable" is false; the next clause patches it ("if `m = 0`, the bound is `0` and
  `Pr` is also `0`") but the two clauses read as alternatives rather than as a case split.
- **Refutation attempt**: I checked the mathematics is fine in both branches — `m = 0, d = 0` gives
  `Fin 0 → R` a singleton, `P` a nonzero constant, `Pr = 0 ≤ 0 = 0*(0-1)/|R|`. So this is purely a
  wording defect, not a soundness one.
- **Suggested fix**: "for `m ≥ 1` and `d = 0` the hypothesis is unsatisfiable; for `m = 0` both
  sides are `0`."

---

### [LOW] Namespace consolidation is scoped narrowly; the stated rationale is only partly achieved

- **Where**: `docs/wiki/probability-conventions.md` (new): *"Do not add new root-level `prob_*` or
  `Pr_*` helper names for generic finite-probability facts … keeps the root namespace from
  accumulating ad hoc helper names."*
- **What's wrong**: generic finite-probability helpers remain at root level elsewhere in
  `ArkLib/Data`: `pmf_prob_le_one` and `prob_eval_zero_le_div`
  (`ArkLib/Data/MvPolynomial/SchwartzZippelCounting.lean:118,126`),
  `Pr_uniform_eq_one_imp_forall` / `Pr_uniform_equiv`
  (`ArkLib/Data/CodingTheory/DivergenceOfSets.lean:83,107`),
  `prob_uniform_congr_equiv` / `prob_uniform_shift_invariant`
  (`ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineSpaces.lean:133,157`). Within the
  `Data/Probability/` subtree itself the new `Notation.lean` lemma goes into Mathlib's
  `ProbabilityTheory` namespace rather than `Probability`.
- **Refutation attempt**: the wiki page *does* scope its rule to "this subtree", and *does*
  explicitly sanction `namespace ProbabilityTheory` for `Notation.lean`, so the PR is
  self-consistent. Demoted to LOW for that reason. The residue is that a ~25-name public API break
  buys a partial cleanup.
- **Suggested fix**: either widen the sweep (moving `pmf_prob_le_one` etc.) in a follow-up, or add
  one sentence to the wiki page listing the known root-level stragglers so the next contributor
  knows they are backlog, not counter-examples.

---

### [LOW] Two micro-nits

- `prob_uniform_pi_mem_finset_le` (`:835`) is `le_of_eq` of the `_eq` version six lines above;
  `.le` at the call site would do.
- `prob_dotProduct_eq_zero_le` names `dotProduct` but spells `∑ j, d j * v j` instead of Mathlib's
  `d ⬝ᵥ v`, which ArkLib does use elsewhere
  (`ArkLib/Data/CodingTheory/ProximityGap/ProximityGenerators.lean:224`).
- Related, a genuinely shared helper is available: `proj_lincomb_ker_card_le`
  (`ArkLib/Data/CodingTheory/ProximityGap/AffineGenerator.lean:76-110`) already runs the
  "kernel of a nonzero linear map has ≤ `|F|^(s-1)` elements" argument via `finrank`;
  `prob_dotProduct_eq_zero_le` re-derives it via `Submodule.card_eq_card_quotient_mul_card`.

---

## Clean bill

Everything below was actively attacked and found genuinely OK.

**1. Zero statement drift across the namespace migration — CLAIM HOLDS.**
Method: `git show origin/main:ArkLib/Data/Probability/Instances.lean` vs HEAD, diffed after
stripping `^namespace Probability$` / `^end Probability$` and `_root_.`. The *only* residual
differences are the Schwartz–Zippel hunk and one sed artifact (`_root_.map_bind`, unchanged in
both). No hypothesis, bound, coercion, binder explicitness, or instance argument changed on any of
the ~25 migrated declarations (`prob_tsum_form_singleton`, `prob_tsum_form_split_first`,
`prob_tsum_form_doubleton`, `prob_uniform_eq_card_filter_div_card`,
`prob_uniform_singleton_finFun_eq`, `prob_split_uniform_sampling_of_prod`,
`do_two_uniform_sampling_eq_uniform_prod`, `prob_uniform_eq_ofReal`,
`prob_split_uniform_sampling_of_equiv_prod`, `prob_split_last_uniform_sampling_of_finFun`,
`prob_marginalization_first_of_prod`, `Pr_le_Pr_of_implies`, `Pr_multi_let_equiv_single_let`,
`Pr_add_split_by_complement`, `prob_const_and_prop_eq_ite`, `Pr_congr`, `Pr_or_le`, `Pr_exists_le`,
`Pr_seq_le_of_forall_le`).
`Fintype.card_fun_fin_one_eq` and `PMF.map_uniformOfFintype_of_fiber_const` keep their **full
names** via `_root_.` — no downstream break there.

**2. The `d := n` specialisation claim.** The retained `prob_schwartz_zippel_mv_polynomial`
signature is byte-identical to `origin/main`'s (binders, `{n : ℕ}`, `h_deg : P.totalDegree ≤ n`,
RHS `(n : ℝ≥0) / (Fintype.card R : ℝ≥0)`), and its proof is now
`prob_schwartz_zippel_mv_polynomial_of_totalDegree_le P h_nonzero h_deg`. No off-by-one; the
generalisation is `n ↦ d` in the bound and the hypothesis simultaneously. `d = 0` /
zero-polynomial edge: `P ≠ 0` with `totalDegree ≤ 0` forces a nonzero constant, `Pr = 0 ≤ 0`.

**3. ABF26 Lemma 2.1 faithfulness — EXACT.** Paper (`(pdftotext of ~/abf26-refs/) ABF26.txt:272-283`): *"Let
p̂ ∈ F^<d[X1,…,Xm] be a non-zero polynomial. Then Pr_{v←F^m}[p̂(v) = 0] ≤ m·(d−1)/|F|"*, with
`F^<d` defined as *"the set of all m-variate polynomials over F of individual degree at most d−1"*.
Lean: `(∀ i, P.degreeOf i < d)` (= individual degree ≤ d−1), bound `(m * (d - 1))/|R|`. Same
quantity, same direction. `[CommRing R] [IsDomain R] [Fintype R]` is equivalent to the paper's
finite field. The supporting `MvPolynomial.totalDegree_le_of_degreeOf_lt` is correct
(`sup_{s ∈ support} ∑ i s i ≤ ∑_{i : Fin m} degreeOf i ≤ m(d−1)`) and is **not** in Mathlib
(loogle `MvPolynomial.totalDegree _ ≤ _ * _` returns only `totalDegree_pow`;
`Mathlib/Algebra/MvPolynomial/Degrees.lean` has only the converse `degreeOf_le_totalDegree:562`).

**4. Vacuity sweep — all new ENNReal bounds are non-vacuous, with compiled witnesses.**
`(session-local probe) r1-nonvacuous.lean` compiles clean and contains:
- a satisfying instance of `prob_polynomial_identity_le` (`R = ZMod 5`, `m = 1`, `d = 2`,
  `P = X 0`), together with a proof that its RHS is `< 1`;
- a satisfying instance of `prob_dotProduct_eq_zero_le` (`d = ![1,0] ≠ 0` over `ZMod 5`), together
  with `(Fintype.card (ZMod 5) : ENNReal)⁻¹ < 1`.
Hand-checked degenerate corners: `prob_uniform_pi_mem_finset_eq` at `t = 0` (both sides `1`),
`A = ∅` (both sides `0`), `A = univ` (both sides `1` — an equality, so not vacuity);
`prob_dotProduct_eq_zero_le` at `k = 0` (`d ≠ 0` unsatisfiable, so no false claim);
`prob_uniform_le_inv_of_card_le_one` with `filter P = ∅` (`0 ≤ 1/|F|`). No `⊤` RHS anywhere: every
denominator is a `Fintype.card` of an inhabited type. No `Nat`-subtraction cheat:
`m * (d - 1)` truncation only bites at `d = 0`, handled above.

**5. Axiom hygiene.** `(session-local probe) r1-axioms.lean`: all of
`prob_schwartz_zippel_mv_polynomial_of_totalDegree_le`, `prob_schwartz_zippel_mv_polynomial`,
`MvPolynomial.totalDegree_le_of_degreeOf_lt`, `prob_polynomial_identity_le`, `Pr_map_eq`,
`prob_dotProduct_eq_zero_le`, `prob_uniform_le_inv_of_card_le_one`,
`prob_uniform_pi_mem_finset_eq`, `prob_uniform_pi_mem_finset_le`,
`ProbabilityTheory.Pr_decide_eq_tsum_indicator`, `Fintype.card_fun_fin_one_eq`,
`PMF.map_uniformOfFintype_of_fiber_const` = `[propext, Classical.choice, Quot.sound]`;
`Fin.induction_three`/`induction_three'` = `[propext]`. **No `sorryAx` anywhere.**

**6. `Fin.sumCases` docstring is accurate.** `#print axioms Fin.sumCases` → `[propext, sorryAx,
Quot.sound]`, matching "WIP (admitted)". `grep -rn "sumCases" ArkLib/` finds **zero** uses outside
its own definition and the commented recursion sketch, so "No declaration in the ABF26 surface
depends on it" is true — and in fact stronger (nothing in the repo depends on it). Compiling
`ArkLib/Data/Fin/Basic.lean` emits exactly one warning, the pre-existing
`:323:4: declaration uses 'sorry'`, which `scripts/validate.sh:20` explicitly exempts
("fail on non-`sorry` warnings under ArkLib/Data/").

**7. No namespace clash, and the migration cannot silently change resolution.**
`grep -rn "^namespace Probability" .lake/packages/mathlib/Mathlib/` → **no Mathlib `Probability`
namespace** (Mathlib uses `ProbabilityTheory`); no Mathlib declaration is named `Probability.*`.
I also ran a per-name clash sweep of all 20+ short names now exported by `namespace Probability`
against `ArkLib/`, `Mathlib/`, and `VCVio` — zero collisions, so `open Probability` cannot cause an
ambiguity or a silent re-resolution in any consumer. Same check for `Combinatorial.lean`'s four
names (`numCollsOrdered`, `sum_fiber_sq_eq`, `cauchy_schwarz_fiber`,
`exists_large_image_of_pairwise_collision_bound`) — no collisions, and no consumer even imports
that module.

**8. The six `open Probability` additions are minimal, sufficient, and correctly placed.**
For each file I confirmed at least one use of a now-namespaced name, all occurring *after* the
`open` line and inside the same namespace block:
`AffineGenerator.lean` (open :251; uses :283,291 `prob_uniform_eq_ofReal`);
`MCAGenerator.lean` (:30; :79,115 `Pr_le_Pr_of_implies`);
`BCIKS20/AffineSpaces.lean` (:22; :137,138,201,228,418,419,522,524,734,772,2180);
`BCIKS20/ReedSolomonGap.lean` (:18; :70,123,212,213);
`OracleReduction/Security/RbrGame.lean` (:68; :146);
`DG25/MainResults.lean` (:21; :174,829,1088-1367).
A repo-wide sweep for the migrated names finds **no seventh file** that would have needed the
`open` — the fix is exactly complete. No consumer's proof body was touched.

**9. `ArkLib/Data/MvPolynomial/EvenAndOdd.lean` is exactly what it claims.**
`Finset.prod_eq_mul_prod_diff_singleton → prod_eq_mul_prod_sdiff_singleton`: the old name is a
Mathlib **deprecated alias** (`Mathlib/Algebra/BigOperators/Group/Finset/Piecewise.lean:201-202`,
`@[deprecated (since := "2026-06-03")]`) for the identical statement at `:193`. Pure
deprecation-warning fix, zero semantic change.

**10. Build/lint hygiene of the two probability files.** `lake env lean` on
`ArkLib/Data/Probability/Instances.lean` and `.../Notation.lean` produces **no output** — no
warnings, no deprecations, no unused-simp-arg hits. `Instances.lean` is 843 lines, well under the
1500-line cap.

**11. Correctness of the remaining new statements (hand-verified, all proven so also
machine-verified):** `Pr_map_eq` is the standard change-of-variables for `PMF.map`;
`prob_uniform_pi_mem_finset_eq` is exact (`|piFinset (fun _ ↦ A)| = |A|^t` out of `|ι|^t`);
`prob_uniform_le_inv_of_card_le_one` is `|filter P| ≤ 1 ⟹ |filter P|/|F| ≤ 1/|F|`;
`prob_dotProduct_eq_zero_le` is rank–nullity on a surjective linear form. None of these exists in
Mathlib (leansearch "probability that a nonzero linear functional vanishes at a uniformly random
point of a finite vector space" returns only `Module.Dual.range_eq_top_of_ne_zero` and unrelated
`uniformOn` lemmas) or elsewhere in ArkLib.
