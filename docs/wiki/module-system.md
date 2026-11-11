# The Lean Module System and ArkLib

Lean's module system splits each source file into a public scope, visible to importers, and a
private scope that is not normally visible outside the module. A file opts in by starting with
`module`, then uses `public import`, `import all`, `meta import`, `public section` and `@[expose]`
to say what crosses the boundary. The upstream reference is
[Source Files and Modules](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/).

**Every file under `ArkLib/` is a module, including the generated root `ArkLib.lean`** (issue #795).
`ArkLibTest/` is deliberately classic, and so are the `lean_exe` roots under `scripts/`.

If you are writing or fixing a file today, go to [the canonical file shape](#the-canonical-file-shape)
and [when a build breaks](#when-a-build-breaks), which lists the errors the module system produces
in practice and their fixes. The rest of the page records what the boundary buys, how it is
enforced, and the handful of places where ArkLib had to give ground.

## What is enforced, and by what

| Rule | Enforced by |
| --- | --- |
| A `module` file may only import `module` files | Lean, at header elaboration (`cannot import non-`module` X from `module``) |
| Every file under `ArkLib/` is a module | the generated root `ArkLib.lean` is a module and `public import`s every file, so a classic file fails the build the moment it is added |
| The `ArkLib` library uses the module system | `requiresModuleSystem = true` on the `ArkLib` `lean_lib` in `lakefile.toml` |
| `ArkLibTest/` may stay classic | `allowNonModules = true` on the `ArkLibTest` `lean_lib` |
| The header's shape | `lake exe lint-style` (see below) |

There is no separate migration checker to run: `lake build` is the gate.

## What the module system buys

Theorem proofs are private to their module. Ordinary module imports load the public artifact
without private proof bodies. Imports using `import all`, and classic clients, can load private
information. Because ArkLib is proof-heavy, the exported part is a small fraction of the build
output, which keeps the memory of ordinary importers low.

A proof-only edit that leaves the public artifact unchanged need not rebuild dependents that
consume only that artifact. Declaration ranges are exported metadata, so inserting or deleting a
line invalidates every downstream module as it would without the module system. Editing a tactic
in place, or editing the last declaration in a file, gets the full benefit.

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
  would cost them the copyright, docstring and file-length exemptions they rely on. List the
  current ones with
  `git ls-files 'ArkLib/*.lean' | xargs grep -L 'public section'`.
- **Metaprograms** (delaborators, unexpanders, elaborators and their helpers) are marked `meta`
  on the declaration (`meta def fooUnexpander : Lean.PrettyPrinter.Unexpander`);
  `ArkLib/Data/Fin/Tuple/Notation.lean` and `ArkLib/Data/Classes/Slice.lean` have examples.
  `macro`, `elab`, `notation` and `syntax` commands are already meta and need no annotation.

### Why `@[expose] public section`, and never a per-declaration `@[expose]`

`linter.privateModule`, part of the `mathlibStandardSet` this repository enables, is inert on
classic files and fires the moment a file gains `module` if all its declarations are private. The
warning budget in `scripts/validate.sh` treats that as a hard failure, and `set_option linter.*` is
forbidden repository-wide, so a public section in every non-imports-only file is mandatory.

`@[expose]` then keeps definition bodies unfoldable, which is what preserves the repository's `rfl`,
`decide`, `simp` and `unfold` proofs. Theorem proofs stay private regardless, and that alone is
where the rebuild win above comes from.

A per-declaration `@[expose]` *inside* a blanket exposed section is a warning
(`Redundant [expose] attribute`, `@[expose] has no effect ...`), and therefore a CI failure. Tighten
exposure only after the blanket section is removed.

### Public producers with private constructors

A public data type may retain a private constructor when its supported producers must control
how fields are paired. Under the blanket exposed section, mark each producer whose implementation
uses that constructor with `@[no_expose]`. The producer remains public, but its implementation is
not exported. Do the same for private implementation helpers used by these producers.

Prove public equations and erasure laws in the defining module. A downstream proof that must
unfold an unexposed producer can add `import all` for that exact defining module, alongside its
ordinary public import. This grants proof-time access; it does not make the constructor public or
turn constructor privacy into a reachability or provenance theorem. The logged interaction
executors demonstrate this pattern while their classic acceptance clients still check computation.

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
it is the reason the port needed no upstream changes. Most uses target `CompPoly.Univariate.*`;
`git grep -n '^import all' -- ArkLib` lists them all. When adding `import all`, include a short
comment naming the definition whose private body is needed, so the import is not mistaken for a
redundant public import.

### When a build breaks

Every row below is an error seen in real ArkLib files.

| Error | Cause | Fix |
| --- | --- | --- |
| ``cannot import non-`module` X from `module` `` | a dependency is still classic | make it a module; everything under `ArkLib/` must be one |
| `Unknown constant X` / `unknown identifier X` | the name arrived transitively before, and is not in your public scope now | add the explicit `public import` for the module that declares it. If it is imported privately, Lean names it: ``A public declaration `X` exists but is imported privately; consider adding `public import M`.`` |
| `Note: The following definitions were not unfolded because their definition is not exposed` alongside a failing `change`, `rfl`, `decide` or `simp` | the definition's body is not exposed | if it is ours, check the import is `public`. If it belongs to a dependency, add `import all M` naming the module that **declares** it — not an umbrella that re-exports it. Failing that, rewrite the proof against the public API |
| `Invalid rewrite argument: ... is a value of type ...` from `rw [SomeDef]` | same cause: you cannot unfold an unexposed definition by name | `import all` its defining module, or use the dependency's `_def`/API lemma |
| ``A private declaration `X` ... would need to be public to access here`` | a `private` declaration is named in a public signature | drop the `private`, or make the referring declaration `private` too. Lean names the declaration, so this is mechanical |
| `tactic execution is stuck, goal contains metavariables` | a `by` block in an exposed *definition* is delayed until the surrounding type is solved, and it never is | hoist it: bind the proof with `have h : T := by …` before the term that needs it, and pass `h`, or give the definition an explicit result type (see [inferred types that embed proofs](#inferred-types-that-embed-proofs)) |
| `Unknown constant _private.….foo._proof_3` | a proof inside a non-exposed definition was abstracted into a private auxiliary theorem that the public signature then mentions | same fix |
| `Invalid match expression: The type of pattern variable … contains metavariables` | the same delayed-`by`, seen through a `match` | same fix |
| ``may not access declaration `X` imported as `meta` `` | metaprogram code outside a meta scope | mark the declaration `meta` |
| ``cannot use `all` with `public import` `` | `public import all M` | split into `public import M` and `import all M` on separate lines |
| `Redundant [expose] attribute` / `@[expose] has no effect` | a per-declaration `@[expose]` inside the blanket section | delete it. Warnings are CI failures here |

### Inferred types that embed proofs

A composed verifier or reduction written as `def foo := <let-chain>` without a type ascription
can have an *inferred* type that embeds the inline `Fin` bounds proofs from its body. That
shape has no good outcome: exposed, every `by` is delayed until the still-unknown result type is
solved and none ever is; not exposed, each proof is abstracted into a private auxiliary theorem
that the public signature may not mention. Give such definitions explicit result types and name
the index equalities they need, as Binary Basefold's composed bundles do. No ArkLib file needs
the compatibility option `backward.proofsInPublic`; try both fixes before reaching for it, and
never use `backward.privateInPublic`, which logs a warning at every access site.

### Why `ArkLibTest/` stays classic

A classic file imports at `.private` level and sees everything, including proof bodies. That matters
because `ArkLibTest/` holds many `#guard_msgs` assertions wrapped around `#print axioms`, and
`#print axioms` walks proof bodies, which are private to a module importer. Migrating the test tree
would change that output and break every one of those guards. mathlib leaves `Archive` classic for
the same reason. `allowNonModules = true` on the `ArkLibTest` library records the decision.

`scripts/AxiomSweep.lean` is unaffected for the same reason: it calls `importModules` at the default
`.private` level, and at that level `importAll` is forced true for every module transitively, so the
census still sees every proof body.

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
