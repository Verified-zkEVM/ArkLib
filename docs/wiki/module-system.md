# The Lean Module System and ArkLib

Lean's module system splits each source file into a public scope, visible to importers, and a
private scope that is not normally visible outside the module. A file opts in by starting with
`module`, then uses `public import`, `import all`, `meta import`, `public section` and `@[expose]`
to say what crosses the boundary. The upstream reference is
[Source Files and Modules](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/).

**Every file under `ArkLib/` is a module, including the generated root `ArkLib.lean`** (issue #795).
`ArkLibTest/` is deliberately classic, and so are the `lean_exe` roots under `scripts/`.

If you are writing or fixing a file today, go to [the canonical file shape](#the-canonical-file-shape)
and [when a build breaks](#when-a-build-breaks), which lists every error the port actually produced
and its fix. The rest of the page records what the boundary buys, how it is enforced, and the
handful of places where ArkLib had to give ground.

## What is enforced, and by what

| Rule | Enforced by |
| --- | --- |
| A `module` file may only import `module` files | Lean, at header elaboration (`cannot import non-`module` X from `module``) |
| Every file under `ArkLib/` is a module | the generated root `ArkLib.lean` is a module and `public import`s all 464 files, so a classic file fails the build the moment it is added |
| The `ArkLib` library uses the module system | `requiresModuleSystem = true` on the `ArkLib` `lean_lib` in `lakefile.toml` |
| `ArkLibTest/` may stay classic | `allowNonModules = true` on the `ArkLibTest` `lean_lib` |
| The header's shape | `lake exe lint-style` (see below) |

There is no separate migration checker to run: `lake build` is the gate.

## What adoption is worth, measured

Measured on 2026-09-09 against a 36-file downward-closed subset of the
`ArkLib/Data/CodingTheory/ListDecodability` closure, editing one proof in
`ArkLib/Data/Fin/Basic.lean`, which 17 files in that set transitively import.

| Tree | Proof edit | Modules rebuilt | Wall time |
| --- | --- | --- | --- |
| classic Lean | in place, no line shift | 18 | 39.5 s |
| module system | in place, no line shift | **1** | **2.6 s** |
| module system | inserts a line | 18 | 34.3 s |

Olean split for those same 36 ported modules:

| Part | Size |
| --- | --- |
| `.olean` (exported, what an importer loads) | 3.43 MB |
| `.olean.private` (proofs and unexposed bodies) | 19.66 MB |

**Only 14.9% of the bytes are what an importer loads.** ArkLib is far more proof-heavy than
mathlib, whose corresponding split is about 34% exported, so the memory benefit here is larger than
upstream's headline figure.

**The caveat that matters.** The rebuild win only materialises when an edit does not shift the
source positions of later declarations. Declaration ranges are exported metadata, so inserting or
deleting a line invalidates every downstream module exactly as today — the third row above. Editing
a tactic in place, or editing the last declaration in a file, gets the full benefit. Adoption is
therefore a large win on some edits and a no-op on others; it is never worse than the status quo.

## The canonical file shape

Fixed by `lake exe lint-style`, whose header policy requires the span between the copyright block
and the first `/-!` to contain nothing but a module header. The copyright block stays first and the
section goes *after* the docstring:

```lean
/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Name, Name
-/
module

public import ArkLib.Data.Foo
public import Mathlib.Bar

/-!
# Module docstring
-/

@[expose] public section
```

No closing `end` is needed; an unclosed outermost `public section` is expected. Two cases differ:

- **Imports-only re-export files** get `module` and `public import` and **no section**. Adding one
  would cost them the copyright, docstring and file-length exemptions they rely on. Three files are
  of this shape: `ArkLib/Data/CodingTheory/{GuruswamiSudan,PolishchukSpielman}.lean` and
  `ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Prelude.lean`.
- **Metaprograms** — delaborators, unexpanders, elaborators and their helpers — are marked `meta`
  on the declaration (`meta def fooUnexpander : Lean.PrettyPrinter.Unexpander`). ArkLib has ten,
  in `ArkLib/Data/Fin/Tuple/Notation.lean`, `ArkLib/Data/Classes/Slice.lean` and
  `ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Escape.lean`. `macro`, `elab`,
  `notation` and `syntax` commands are already meta and need no annotation.

### Why `@[expose] public section`, and never a per-declaration `@[expose]`

`linter.privateModule`, part of the `mathlibStandardSet` this repository enables, is inert on
classic files and fires the moment a file gains `module` if all its declarations are private. The
warning budget in `scripts/validate.sh` treats that as a hard failure, and `set_option linter.*` is
forbidden repository-wide, so a public section in every non-imports-only file is mandatory.

`@[expose]` then keeps definition bodies unfoldable, which is what preserves the repository's `rfl`,
`decide`, `simp` and `unfold` proofs. Theorem proofs stay private regardless, and that alone is
where the measured win above comes from.

A per-declaration `@[expose]` *inside* a blanket exposed section is a warning
(`Redundant [expose] attribute`, `@[expose] has no effect ...`), and therefore a CI failure. Tighten
exposure only after the blanket section is removed.

## Working in a module file

### What each piece of the header does

| Written | Effect |
| --- | --- |
| `public import M` | `M`'s public scope enters *this* file's public scope, and importers of this file see it too. The default choice. |
| `import M` | `M` is available here but not re-exported. Use when `M` is needed only inside proofs. |
| `public meta import M` | As `public import`, and available to metaprograms. Only for `Lean.*` and `Qq`. |
| `import all M` | Loads `M`'s private scope: private names, **and the bodies `M` did not expose**. `M` must be the module that *declares* what you need — an umbrella that merely re-exports it does nothing. It may not be combined with `public` on one line. |
| `@[expose] public section` | Everything below is public and its definition bodies stay unfoldable. Theorem proofs stay private regardless, which is where the build win comes from. |

`import all` is what makes a proof that unfolds an unexposed upstream definition keep working, and
it is the reason the port needed no upstream changes. ArkLib uses it 24 times across 16 files,
against `CompPoly.Univariate.*`, `Mathlib.Algebra.Polynomial.Basic`,
`Mathlib.Analysis.SpecialFunctions.BinaryEntropy` and `Init.Data.Vector.FinRange`. Each site
carries a one-line comment saying which definition it is unfolding, because the line looks
redundant next to the `public import` of the same tree and is easy to "clean up" by mistake.

### When a build breaks

Every row below is an error seen while porting real ArkLib files.

| Error | Cause | Fix |
| --- | --- | --- |
| ``cannot import non-`module` X from `module` `` | a dependency is still classic | make it a module; everything under `ArkLib/` must be one |
| `Unknown constant X` / `unknown identifier X` | the name arrived transitively before, and is not in your public scope now | add the explicit `public import` for the module that declares it. If it is imported privately, Lean names it: ``A public declaration `X` exists but is imported privately; consider adding `public import M`.`` |
| `Note: The following definitions were not unfolded because their definition is not exposed` alongside a failing `change`, `rfl`, `decide` or `simp` | the definition's body is not exposed | if it is ours, check the import is `public`. If it belongs to a dependency, add `import all M` naming the module that **declares** it — not an umbrella that re-exports it. Failing that, rewrite the proof against the public API |
| `Invalid rewrite argument: ... is a value of type ...` from `rw [SomeDef]` | same cause: you cannot unfold an unexposed definition by name | `import all` its defining module, or use the dependency's `_def`/API lemma |
| ``A private declaration `X` ... would need to be public to access here`` | a `private` declaration is named in a public signature | drop the `private`, or make the referring declaration `private` too. Lean names the declaration, so this is mechanical |
| `tactic execution is stuck, goal contains metavariables` | a `by` block in an exposed *definition* is delayed until the surrounding type is solved, and it never is | hoist it: bind the proof with `have h : T := by …` before the term that needs it, and pass `h`. Only if the definition's inferred type itself embeds the proof is [`backward.proofsInPublic`](#backwardproofsinpublic) warranted |
| `Unknown constant _private.….foo._proof_3` | a proof inside a non-exposed definition was abstracted into a private auxiliary theorem that the public signature then mentions | same fix, same last resort |
| `Invalid match expression: The type of pattern variable … contains metavariables` | the same delayed-`by`, seen through a `match` | same fix |
| ``may not access declaration `X` imported as `meta` `` | metaprogram code outside a meta scope | mark the declaration `meta` |
| ``cannot use `all` with `public import` `` | `public import all M` | split into `public import M` and `import all M` on separate lines |
| `Redundant [expose] attribute` / `@[expose] has no effect` | a per-declaration `@[expose]` inside the blanket section | delete it. Warnings are CI failures here |

### `backward.proofsInPublic`

Three files set `set_option backward.proofsInPublic true`, all in the Binius tree:

- `ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean`
- `ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean`
- `ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean`

They hold composed verifier and reduction bundles written as `def foo := <let-chain>` with no type
ascription, whose *inferred* type embeds the inline `Fin` bounds proofs from their bodies. That
shape has no good outcome under the default: exposed, every `by` is delayed until the still-unknown
result type is solved and none ever is; not exposed, each proof is abstracted into a private
auxiliary theorem that the public signature may not mention. The option restores the classic
elaboration those definitions were written against, and each site carries a comment saying so.

This is a compatibility flag, not a suppression — it silences no diagnostic and the zero-warning
budget still applies to these files. Do not reach for it before trying the hoist above, and never
reach for `backward.privateInPublic`, which logs a warning at every access site.

Writing these definitions with explicit result types would retire the option; that is a
Binius-authors change, not a mechanical one.

### Why `ArkLibTest/` stays classic

A classic file imports at `.private` level and sees everything, including proof bodies. That matters
because `ArkLibTest/` holds around 40 `#guard_msgs` assertions wrapped around `#print axioms`, and
`#print axioms` walks proof bodies, which are private to a module importer. Migrating the test tree
would change that output and break every one of those guards. mathlib leaves `Archive` classic for
the same reason. `allowNonModules = true` on the `ArkLibTest` library records the decision.

`scripts/AxiomSweep.lean` is unaffected for the same reason: it calls `importModules` at the default
`.private` level, and at that level `importAll` is forced true for every module transitively, so the
census still sees every proof body.

## What the port changed, beyond headers

Of 464 files, all but a few needed nothing but the header rewrite. The exceptions:

- **70 `private` markers dropped**, where a private declaration was named by a public signature.
  Lean names the declaration in its own error, so this was mechanical.
- **Missing imports made explicit.** `ArkLib/Data/Fin/Basic.lean` failed with
  `Unknown constant List.le_sum_of_mem`, a `to_additive`-generated mathlib lemma it had only ever
  received transitively; `ArkLib/Data/CodingTheory/ListDecodability/Bounds/KKH26.lean` needed
  `Mathlib.RingTheory.MvPolynomial.Symmetric.Defs` and `Mathlib.RingTheory.Polynomial.Vieta`. The
  module system turns implicit transitive dependencies into declared ones, which is a real bug class
  it finds for free.
- **A handful of proofs rewritten** where a delayed `by` could not survive in an exposed position:
  term proofs in place of `by simp` (`ArkLib/OracleReduction/Execution.lean`,
  `ArkLib/ProofSystem/Component/RandomQuery.lean`), a hoisted arity lemma
  (`Prover.append_state_arity` in
  `ArkLib/OracleReduction/Composition/Sequential/Append/Basic.lean`), and hoisted `have`s in
  `ArkLib/ProofSystem/Binius/BinaryBasefold/Prelude.lean`.

## Where the remaining win is

The port preserves classic semantics everywhere: every file is blanket-exposed, and every import is
`public`. That is the conservative end of the design space, and it leaves value on the table.

- Demote `public import` to `import` where a dependency is used only inside proofs.
- Remove the blanket `@[expose]` file by file, marking only the definitions whose bodies downstream
  proofs actually unfold.
- Mark internals `private`.

All three are manual: mathlib's `shake` no longer works under the module system. Each is a
per-file change that can land independently, and each shrinks the exported olean further.

## Out of scope

The `set_option backward.isDefEq.respectTransparency false` sites are Lean v4.33's reducibility
change, not module-system exposure. They are real debt, but the port would not retire them.
