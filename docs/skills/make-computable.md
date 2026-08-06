# /make-computable

Use this workflow when the task is to turn `noncomputable` definitions into executable ones —
algebraic operations, decoders, encoders, extractors, provers and verifiers, or any definition
someone wants to `#eval`. It triages every marker, distinguishes the ones that are symptoms from
the ones that are the disease, fixes the tractable ones, and reports the rest with the real blocker
named.

This is a general skill, not a subsystem guide. It assumes ArkLib's Lean 4 codebase and
`./scripts/validate.sh` as the routine build check. It is the computability counterpart of
[`discharge-lemmas.md`](discharge-lemmas.md); the triage-then-place-then-prove spine is the same,
but the ratings, the placement rules, and the definition of "done" are different.

## Goal

Turn a pile of `noncomputable` markers into:

- a rated, triaged inventory that separates the three *kinds* of noncomputability,
- executable definitions for everything rated below 7,
- correctness lemmas showing the executable version agrees with what it replaced,
- a **runtime** demonstration that the new code actually runs,
- and a clear statement of what remains noncomputable and why.

Favor reusing verified executable algorithms already in Mathlib or the dependency packages
(CompPoly especially) over writing a new algorithm and proving it from scratch.

## The Three Kinds

Classify every marker before touching anything. Most of the triage value is here, and the kinds
have wildly different costs.

| Kind | Signature | What to do |
| --- | --- | --- |
| **Sorried** | body is `sorry`; `noncomputable` is forced because `sorryAx` is noncomputable | **Skip.** Making it computable *is* writing the missing algorithm. That is formalization work under [`discharge-lemmas.md`](discharge-lemmas.md), not a computability task. Record it and move on. |
| **Leaf** | a real implementation that names `Ring.inverse`, `Exists.choose`, `Classical.arbitrary`, `Classical.ofNonempty`, `open Classical in`, or a `Decidable` instance that is missing | **Fix.** Usually 1–5. This is the bulk of real work. |
| **Architectural** | the definition has no data to compute *from* — it inverts an arbitrary `Set`, chooses a witness for an `∃` over a non-`Fintype`, or the input type genuinely lacks the information | **Defer.** Almost always 8–10. Name the missing information and what API change would supply it. |

The architectural kind is the one people misjudge. A `Classical.choice` inside a definition is not
automatically a syntactic accident: check whether the function's *input type* even contains enough
information to compute the answer. If it does not, no local edit will help.

## TODO List

Work through these in order. Do not skip triage because a marker looks mechanical.

### 1. Inventory and classify

- Collect every marker in scope: `grep -rn "noncomputable" path/to/scope`, plus
  `grep -rn "open Classical\|Classical\.\|\.choose" path/to/scope` — a definition can be
  noncomputable-in-effect without carrying the keyword, and a file-wide `noncomputable section`
  hides markers from the first grep.
- **Check for a file-wide `noncomputable section`.** In Lean 4 it needs no matching `end`, so it
  silently covers the rest of the file. Any `Decidable` instance you add inside one is born
  noncomputable and useless. Look at the section boundaries before you edit.
- For each marker, read the body and decide its **kind** from the table above. Read the goal and
  the input types, not the prose.

### 2. Rate each gap

| Rating | Meaning | Typical signs |
| --- | --- | --- |
| 1–2 | 1–2 minutes | missing `Decidable` instance that `unfold X; infer_instance` supplies; dropping a now-redundant marker |
| 3–5 | up to ~an hour | `Exists.choose` → `Fin.find`; threading a `[DecidableEq]` constraint; rewiring a handful of proof sites |
| 6 | half a day | a new executable algorithm plus its agreement lemma, where the algorithm exists upstream but the bridge lemma does not |
| 7–10 | a day or longer | new algorithm *and* new upstream theory; or an architectural gap requiring an API redesign |

**Only tackle gaps rated below 7.** Rate 7+ as deferred with the blocker named. Skip every
**Sorried** gap regardless of how its eventual body would look.

Record the rating and a one-line justification per gap. This table is the first deliverable.

### 3. Probe before you estimate blast radius

Before committing to a plan, write a throwaway file in the scratchpad that imports the real module
and re-declares the definition the way you intend to fix it. Compile it with
`lake env lean scratch.lean`.

This is cheap and it repeatedly beats reasoning:

- It tells you exactly which instance is missing, rather than which one you guessed.
- It tells you whether the surrounding arithmetic is *already* computable. Often the only blocker
  is one named function and everything around it is fine.
- It corrects blast-radius estimates. A constraint that looks like it must thread through dozens of
  call sites usually discharges by synthesis at every one, because the type is concrete there.

Do this before step 4, not after.

### 4. Decide the best home

Follow [`../wiki/repo-map.md`](../wiki/repo-map.md) routing, with two computability-specific rules:

- A new **executable algorithm** on an existing structure is reusable math: it belongs in
  `ArkLib/Data/` (or `ArkLib/ToMathlib/`) next to the structure, never in the consumer file that
  happens to need it first.
- A **`Decidable` instance belongs next to the predicate it decides**, not next to the search that
  consumes it. If a `noncomputable section` is in the way, move the section boundary rather than
  the instance — and leave a comment saying why the block must stay computable.

Create a new file only when several related declarations share a topic and pull in imports the host
file should not carry. Give it the Apache header and module docstring per
[`../../CONTRIBUTING.md`](../../CONTRIBUTING.md), and `git add` it so validation sees it.

### 5. Replace, then prove agreement

- Prefer a **total** definition with no unit test or case split in the body, matching the totality
  of whatever it replaces. Off the good inputs it may return junk; say so in the docstring.
- State correctness **only where it is meaningful** — under the side condition callers already
  carry (invertibility, well-formedness, membership, a degree or norm bound). Do not prove the junk
  branch unless a call site needs it; that direction is often most of the work for none of the
  benefit.
- Always prove the **agreement lemma** `side condition → new = old` against whatever you replaced.
  It may have no call site. Keep it anyway: it is the certificate that the swap was
  semantics-preserving, and without it a reviewer cannot tell.
- Keep the `[Decidable…]` hypotheses out of `Prop`-valued statements. If the statement does not
  mention the instance, drop the binder and use `classical` in the proof — the
  `unusedDecidableInType` linter will otherwise flag it.
- Build after each replacement (`lake env lean File.lean`). Do not batch.

### 6. Verify at runtime, not just at the type level

Lean accepting a `def` without `noncomputable` means code was generated, but it does not mean the
code is *correct*. Finish with `#eval` on a small concrete instance in the scratchpad:

- Choose parameters where the interesting case actually fires. For a ring inverse, pick a modulus
  that makes the quotient **not** a field, so the unit test is genuinely exercised.
- Check a value you computed by hand, not just that it terminates.
- Exercise each branch of a case split.

`#print axioms` is **not** a computability test. It reports `Classical.choice` for perfectly
computable definitions whose erased `Prop` fields have classical proofs. Ignore it here.

If a `decide` in the probe gets stuck on kernel reduction, that is a probe problem, not a code
problem — the compiler path is what matters. `native_decide` is acceptable in a throwaway
scratchpad probe; it is forbidden in repo code.

### 7. Clean up

- Delete or correct every comment and docstring that claimed the definition needed classical
  choice. These are load-bearing for the next reader and go stale silently.
- Where a marker remains, say in the module docstring *which* declaration still carries it and
  why — a reader should not have to re-derive the architectural blocker.
- Run [`fix-lean-warnings.md`](fix-lean-warnings.md) over the changed files.
- If you added a file under `ArkLib/`, run `./scripts/update-lib.sh` and `git add` the result —
  `check-imports.sh` compares against the index, so an unstaged regeneration still fails.
- Confirm `./scripts/validate.sh` passes (`--lint` too). Changes under `ArkLib/Data/` must clear
  the zero-warning gate.

### 8. Summarize and improve this skill

Report:

- the rating table from step 2, with the **kind** column,
- for each gap: chosen home, and status (executable / deferred / skipped-because-sorried),
- for deferred gaps: the blocker, named concretely enough to plan against,
- any rating you revised mid-flight, and any blast-radius estimate that turned out wrong,
- the runtime evidence,
- and per the Maintenance Rule in [`README.md`](README.md), how this skill should change.

## Persistence Rule

Only consider the task complete when:

1. Every marker in scope has a kind and a rating.
2. Every gap rated below 7 whose kind is **Leaf** is executable, or you have re-rated it honestly
   and said why.
3. Every remaining marker is either **Sorried** (skipped by policy), **Architectural**, or rated 7+,
   and is documented as such in the file where it lives.
4. There is runtime `#eval` evidence that the new code computes correct values.
5. `./scripts/validate.sh` passes and every changed file is warning-free.
6. You have delivered the summary and any suggested skill improvements.

## Known Pitfalls

- **A `sorry` body makes a definition noncomputable.** Do not read those markers as computability
  debt; they are proof debt wearing a disguise.
- **`noncomputable section` has no matching `end`.** It covers the rest of the file. Instances
  added inside are silently poisoned.
- **`Exists.choose` is always noncomputable, even over a `Fintype` with decidable predicates.**
  Use `Fin.find (p) (h : ∃ k, p k)`, whose `Fin.find_spec h : p (Fin.find p h)` has the same shape
  as `Exists.choose_spec`, so the consuming proofs usually survive verbatim. Pass `h` explicitly —
  the predicate is implicit and often will not unify from `_`.
- **`Nonempty` is not enough.** Junk fallbacks need `Inhabited` (or `default`). Changing the binder
  is part of the fix, and `Fin (n+1)` supplies it automatically.
- **A `def` returning `Type` is opaque to instance search.** A subtype defined by `def` (not
  `abbrev`) will not inherit `DecidableEq` from its carrier; declare the instance explicitly.
- **Do not invent an algorithm before searching the dependency packages.** CompPoly ships verified
  division, `xgcd`/`normXgcd` with Bézout and gcd correctness, and normalization bridges to
  Mathlib. Reusing them turns a multi-day job into a half-day one.
- **Computability is not a stronger theorem.** Unless the surrounding definitions bound complexity,
  making something executable buys `#eval`-ability and testability, not a better result. (Concrete
  case: ArkLib's `Extractor.TreeBased` is a plain function type with no complexity bound, so a
  computable extractor is no stronger a security statement than a classical one.) Say so rather
  than overselling.
