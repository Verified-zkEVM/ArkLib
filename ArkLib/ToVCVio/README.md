# ArkLib additions to VCV-io

This directory mirrors VCV-io's module structure (`OracleComp/`, `EvalDist/`, `ToMathlib/`, ...) and
holds **additions the pinned VCVio predates** — `simulateQ` / `OracleComp` / distribution lemmas
ArkLib needs before they exist upstream, each destined to move up and be deleted here — together
with compatibility shells that preserve old ArkLib import paths after such additions move upstream.

**Invariant: nothing in this directory imports ArkLib outside `ToVCVio` itself.** That is what makes
a file here upstreamable by construction — it can be moved to VCVio unchanged. A lemma that needs
`ArkLib/OracleReduction/`, `ArkLib/Data/`, or any other ArkLib layer does not belong here, however
generic its content; it belongs beside its consumers in ArkLib core.

Note the second clause: content that is *morally* generic but *depends* on ArkLib still fails the
invariant. `ArkLib/OracleReduction/Security/RbrGame.lean` is the illustrative case — its mixture
bounds need nothing about protocols beyond "a sub-oracle answered by a uniform sample", but they are
stated over `ProtocolSpec`, so they sit in core with a note that generalising that one ingredient
would let them move up. Upstream them by generalising first, then moving; not by parking them here.

## Working rule

Prefer landing general statements **upstream in VCV-io**, under the same name and the mirrored path.
At the next VCVio bump, delete the local declaration and let references resolve upstream. Keep an
import-only compatibility shell only while downstream modules still use the old ArkLib path.

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
