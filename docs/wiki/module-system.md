# The Lean Module System and ArkLib

Lean's module system splits each source file into a public scope, visible to importers, and a
private scope that is not normally visible outside the module. A file opts in by starting with
`module`, then uses `public import`, `import all`, `meta import`, `public section` and `@[expose]`
to say what crosses the boundary. The upstream reference is
[Source Files and Modules](https://lean-lang.org/doc/reference/latest/Source-Files-and-Modules/).

This page records where ArkLib stands relative to it, what that costs, and what a migration would
have to solve. It is not a migration plan.

## Where ArkLib stands

**ArkLib's library sources do not use the module system yet. Most source files in its pinned
dependencies do.** No file under `ArkLib/` carries a `module` header, uses `public import`, or is
annotated `@[expose]`. PolyFun and CompPoly are essentially fully ported; mathlib, VCVio, cslib
and Batteries still contain a mixture of module-system and classic Lean files. ArkLib is the only
library layer in the stack whose sources are entirely classic Lean.

To check the current state:

```bash
# ArkLib's tracked library sources
git grep -l '^module$' -- 'ArkLib/**/*.lean' | wc -l
git ls-files 'ArkLib/**/*.lean' | wc -l

# A pinned dependency, after `lake exe cache get`
git -C .lake/packages/VCVio grep -l '^module$' -- '*.lean' | wc -l
git -C .lake/packages/VCVio ls-files '*.lean' | wc -l
```

Lake records the verdict per module in `.lake/build/ir/**/**.setup.json` as `"isModule"`. It is
detected from the header; there is no lakefile option to set.

The only module-system files in the repository are the executable axiom-sweep fixtures under
`scripts/AxiomSweepTestFixtures/`. Their test harness was ported from module-system users PolyFun
and VCVio, and the fixtures retain that harness's module-system layout.

## Why nothing is broken today

Non-module files may import modules; they ignore the module-system annotations on what they
import. ArkLib's pinned Lean 4.32.2 toolchain predates two Lake options added in Lean 4.33:
`requiresModuleSystem`, which lets a package or library warn non-module importers, and
`allowNonModules`, which lets an importer acknowledge and suppress that warning. When ArkLib next
updates Lean, check these options in every pinned dependency before treating the migration as
optional. If a dependency enables `requiresModuleSystem`, ArkLib's classic files that import it
will warn until ArkLib migrates or explicitly opts out.

## What non-adoption costs

Upstream states two benefits, both of which ArkLib currently forgoes:

- Build times. "Changes to files that affect only non-exported information (e.g. proofs,
  comments, and docstrings) will not trigger rebuilds outside of these files." A proof-only edit
  in ArkLib today rebuilds everything downstream of it.
- Memory. "Excluding private information such as proofs from importing can improve Lean's memory
  use both while building and editing a project. Porting mathlib4 to the module system has shown
  savings close to 50%."

There is also a design benefit: the compiler checks which declarations and bodies form a public
API. ArkLib currently relies on ordinary imports, naming, and review to maintain those boundaries.
A migration would make the intended boundary explicit in each source file.

## What a migration has to solve

These are the ArkLib-specific decisions and prerequisites beyond the ordinary per-file work.

1. **The generated root emits plain `import`.** `scripts/update-lib.sh` builds `ArkLib.lean` by
   piping `git ls-files` through `sed 's/^/import /'`. A module-system root re-exports nothing
   unless it emits `module` and `public import`, so the emitter changes before any file does.
   `scripts/check-imports.sh` gates the result, so the two move together.
2. **The `ArkLib` library has no explicit `globs`.** `lakefile.toml` declares `[[lean_lib]] name =
   "ArkLib"` and nothing else. Lake therefore starts from the default `ArkLib` root and recursively
   builds its local imports. This does not block a migration, but the migration should decide
   whether an explicit `ArkLib.+` glob better states the intended library membership.
3. **The fixture library has a separate quarantine requirement.** `AxiomSweepTestFixtures` uses
   `roots = []` with a `.+` glob so its deliberately tainted modules are available to the explicit
   test target but excluded from workspace-root import discovery. This Lake target configuration
   is separate from `import all`, which controls access to a module's private scope. Preserve the
   quarantine during migration; use `import all` only if a test must inspect private declarations.
4. **The axiom sweep encodes the classic privacy model.** `scripts/AxiomSweep.lean` enumerates
   `env.header.moduleData` from `importModules` and filters with `privateToUserName?` /
   `isInternalDetail`. Module-system `private`, and bodies that are public but unexposed, change
   what that census can see. The sweep needs re-auditing as part of any migration, not after it.

## Follow the upstream porting recipe

Follow the porting recipe in the reference manual linked above. Start with permissive public
imports and sections, make the package compile, and then reduce visibility and exposure to
recover the module system's rebuild and memory benefits.

Note that step 1 is all-or-nothing per import edge — a module may only import modules — so the
port cannot advance one directory at a time from the top of the import graph. It can be measured
on a subtree whose imports are already satisfied, which is the cheapest way to get a real number
for the rebuild and memory win before committing.
