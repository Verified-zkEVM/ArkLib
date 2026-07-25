# ArkLib additions to VCV-io

This directory mirrors VCV-io's module structure (`OracleComp/`, `EvalDist/`, `ToMathlib/`, ...) and
holds two kinds of thing:

1. **Additions the pinned VCVio predates** — `simulateQ` / `OracleComp` / distribution lemmas ArkLib
   needs before they exist upstream.
2. **ArkLib-specific glue** that mentions ArkLib definitions and therefore does not belong upstream at
   all. `OracleComp/RbrGame.lean` is the current example: it mentions `ProtocolSpec` and is the one
   file here that imports `ArkLib/OracleReduction/`.

## Working rule

Prefer landing general statements **upstream in VCV-io**, under the same name and the mirrored path.
At the next VCVio bump, delete the local copy and let references resolve upstream. Anything in
category 1 is temporary by construction; anything in category 2 stays.

Two things to know when doing that cleanup:

- **Upstream versions are often more general** (`ProbComp` → generic monad, `StateT σ ProbComp` →
  lawful target, `Type` → `Type*`). They still unify at ArkLib's instantiations, but the extra
  generality can change how arguments elaborate, so expect call sites to need named arguments rather
  than positional ones.
- **A green build does not prove the absence of duplicates.** Lean only reports
  `… has already been declared` when both copies are in scope *together*. A local lemma and its
  upstream twin can sit at root scope in different modules indefinitely without ever colliding, if no
  module imports both. When deduplicating, check names against VCVio's sources directly rather than
  relying on the compiler to object.

## Compatibility shells

When a file's entire contents go upstream, it is reduced to an import-only shell rather than deleted,
so downstream modules keep resolving. Currently in that state:

- `EvalDist/Defs/Support.lean`
- `EvalDist/Instances/OptionT.lean`
- `OracleComp/EvalDist.lean`
- `OracleComp/Coercions/SubSpec.lean`
- `OracleComp/SimSemantics/SimulateQ.lean`

Each can be removed once its importers point upstream directly. See each file's module docstring for
what moved and where.
