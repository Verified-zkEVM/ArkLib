# The Lean Module System and ArkLib

Lean's module system splits each source file into a public scope, visible to importers, and a
private scope that is not. It is opt-in per file: a file joins by starting with `module`, and then
uses `public import`, `import all`, `meta import`, `public section` and `@[expose]` to say what
crosses the boundary. The upstream reference is
[Source Files and Modules](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/).

This page records where ArkLib stands relative to it, what that costs, and what a migration would
have to solve. It is not a migration plan.

## Where ArkLib stands

**ArkLib is not a module package. Its dependencies are.** No file under `ArkLib/` carries a
`module` header, uses `public import`, or is annotated `@[expose]`. Mathlib, VCVio, CompPoly,
PolyFun, cslib and Batteries are all essentially fully ported. ArkLib is the only classic-Lean
layer in its own stack.

To check the current state:

```bash
# ArkLib
grep -rl '^module$' ArkLib/ | wc -l          # module files
find ArkLib -name '*.lean' | wc -l           # total

# any dependency
grep -rl '^module' .lake/packages/mathlib --include='*.lean' | wc -l
```

Lake records the verdict per module in `.lake/build/ir/**/**.setup.json` as `"isModule"`. It is
detected from the header; there is no lakefile option to set.

The only module-system files in the repository are the axiom-sweep fixtures under
`scripts/ArkLibAxiomSweepTestFixtures/`, and only because they were adapted from module-native
upstreams.

## Why nothing is broken today

Non-module files may import modules; they ignore the module-system annotations on what they
import. Lean v4.33 added a Lake package option, `requiresModuleSystem`, that makes Lake warn when
a file without a `module` header imports the package, with `allowNonModules` to opt back out. No
ArkLib dependency sets it. That option is the thing to watch: the day mathlib or VCVio turns it
on, ArkLib starts emitting warnings on every build.

## What non-adoption costs

Upstream states two benefits, both of which ArkLib currently forgoes:

- Build times. "Changes to files that affect only non-exported information (e.g. proofs,
  comments, and docstrings) will not trigger rebuilds outside of these files." A proof-only edit
  in ArkLib today rebuilds everything downstream of it.
- Memory. "Excluding private information such as proofs from importing can improve Lean's memory
  use both while building and editing a project. Porting mathlib4 to the module system has shown
  savings close to 50%."

There is also a design benefit ArkLib already wants but cannot enforce. Both
[`../../ArkLib/ToVCVio/README.md`](../../ArkLib/ToVCVio/README.md) and
[`repo-map.md`](repo-map.md) already ask contributors not to reach through a dependency's module
boundary — "Do not use `import all` to recover a dependency implementation detail", "Expose a body
only when dependent elaboration genuinely needs its definitional reduction". Under the module
system those are checked by the compiler instead of by review.

## What a migration has to solve

These are the ArkLib-specific obstacles, beyond the ordinary per-file work.

1. **The generated root emits plain `import`.** `scripts/update-lib.sh` builds `ArkLib.lean` by
   piping `git ls-files` through `sed 's/^/import /'`. A module-system root re-exports nothing
   unless it emits `module` and `public import`, so the emitter changes before any file does.
   `scripts/check-imports.sh` gates the result, so the two move together.
2. **The `ArkLib` library has no `globs`.** `lakefile.toml` declares `[[lean_lib]] name =
   "ArkLib"` and nothing else, so Lake defaults the library's module set to `ArkLib.lean` plus its
   transitive imports. Under the module system, whether an import is `public` changes what that
   closure means for downstream consumers, so the library boundary is better stated explicitly
   than inferred.
3. **The fixture quarantine hand-rolls what `import all` is for.** The
   `ArkLibAxiomSweepTestFixtures` library uses `roots = []` with a `.+` glob to keep deliberately
   tainted fixtures out of workspace-wide tooling. Upstream's mechanism for code that tests must
   reach but consumers must not is `import all` within a package.
4. **The axiom sweep encodes the classic privacy model.** `scripts/AxiomSweep.lean` enumerates
   `env.header.moduleData` from `importModules` and filters with `privateToUserName?` /
   `isInternalDetail`. Module-system `private`, and bodies that are public but unexposed, change
   what that census can see. The sweep needs re-auditing as part of any migration, not after it.

## The upstream porting recipe

Quoted from the reference manual, for whoever picks this up:

> 1. Prefix all files with `module`. 2. Make all existing imports `public` unless they will be
> used only in proofs. Add `import all` when errors that mention references to private data occur.
> Add `public meta import` when errors mention "must be `meta`". 3. Prefix the remainder of the
> file with `@[expose] public section` or `public section`.

and afterwards, "removing uses of `public` and `@[expose]` will help avoid unnecessary rebuilds".

Note that step 1 is all-or-nothing per import edge — a module may only import modules — so the
port cannot advance one leaf directory at a time from the top. It can be measured on a subtree
whose imports are already satisfied, which is the cheapest way to get a real number for the
rebuild and memory win before committing.

## What is not a module-system problem

`set_option backward.isDefEq.respectTransparency false in` appears at several sites in ArkLib.
That flag is Lean v4.33's reducibility change (`backward.isDefEq.respectTransparency.types` on by
default), not module-system exposure. It is real debt — `backward.*` options are removed upstream
after a few releases — but adopting the module system would not retire it. Each site carries a
comment naming the tactic that fails without it; `git grep backward.isDefEq.respectTransparency`
lists them.
