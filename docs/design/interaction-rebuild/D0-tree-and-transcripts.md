# D0. One protocol tree, a lens signature, and two transcript types

**Status:** Proposed: awaiting maintainer approval.
**Implemented by:** PolyFun PR P (signature vocabulary and transcript ledger).

## Decision

A protocol is a single tree `s : FreeM P PUnit` over a source polynomial `P`. Its positions
`a : P.A` say what kind of event happens next; its branches `P.B a` say which continuation the
event selects. A *signature* is a lens from `P` into the role polynomial, which assigns every
position an owner and a move type, and maps each move to the branch it selects:

```lean
-- intended, not existing
def rolePoly.{u} : PFunctor.{u+1, u} := ⟨Role × Type u, fun r => r.2⟩

variable (l : Lens P rolePoly.{u})
def owner (l) (a : P.A) : Role   := (l.toFunA a).1      -- sender or receiver
def Move  (l) (a : P.A) : Type u := (l.toFunA a).2      -- what is exchanged at `a`
-- the branch map is the lens's backward map: l.toFunB a : Move l a → P.B a
```

Two transcript types are attached to a tree, both of which already exist in PolyFun:

- `Path s` (`PFunctor/Free/Path.lean:93`) records the branch chosen at each node: the *shape
  path*. It is what a suffix tree may depend on.
- `PathAlong l s` (`PFunctor/Free/Path.lean:178`) records every move, including moves whose
  branch map is constant. At a node `a` it is a move `x : Move l a` followed by a path through
  the branch `l.toFunB a x`.
- `projectPathAlong l s : PathAlong l s → Path s` (`Path.lean:329`) forgets each move to the
  branch it selects.

Appending trees uses `FreeM.append s₁ s₂` (`Path.lean:657`) with a suffix family
`s₂ : Path s₁ → FreeM P β`. A suffix participant after a full prefix transcript `tr₁` lives on
`s₂ (projectPathAlong l s₁ tr₁)`. The existing appended-transcript API (`PathAlong.LiftAppend`,
`append`, `split`, `packAppend`, `unpackAppend` and their round trips, `Path.lean:1123–1300`)
already indexes the suffix this way.

P adds the following laws and definitions; none exist yet.

```lean
-- intended, not existing
theorem projectPathAlong_id (s : FreeM P α) (p : PathAlong (Lens.id P) s) :
    projectPathAlong (Lens.id P) s p = p
-- product transport for separately lifted statement and witness outputs
def PathAlong.liftAppendProd ...; def PathAlong.liftAppendProdMk ...
theorem PathAlong.liftAppendProd_packAppend ...
-- replication ledger for `FreeM.replicate` (PFunctor/Free/Replicate.lean:33)
def PathAlong.replicateCons ...; def PathAlong.replicateUncons ...
def PathAlong.replicateJoin ...; def PathAlong.replicateSplit ...
-- zero and successor equations and both inverse laws for each pair
```

P also adds `PathAlong.MoveMap` and `PathAlong.mapMoves`, a map of transcripts between two lenses
over the same polynomial functor along a branch-respecting move map; record D3 uses it for the
verifier view.

At the identity lens, `PathAlong (Lens.id P) s` and `Path s` are equal as types after
unfolding. `projectPathAlong (Lens.id P) s` is a structural recursion on `s` and is therefore
not definitionally the identity when `s` is a variable. The two append APIs are kept separate
(as the comment at `Path.lean:1107–1115` already explains), and `projectPathAlong_id` is the
only bridge between them. No proof identifies them by `rfl`.

Lens vocabulary used in later records: every lens factors as a vertical lens followed by a
cartesian lens (`factorVert`, `factorCart` in `PFunctor/Lens/Factorization.lean:115,120`). In
the canonical factorization the vertical leg is the identity on positions and the cartesian leg
is the identity on directions. A general vertical lens is bijective on positions
(`IsVertical`, `Factorization.lean:65`); a general cartesian lens has bijective backward maps at
every position. It is not true that every cartesian lens merely renames positions.

## Why

The legacy layer fixes the shape in advance. `ProtocolSpec n` (`ProtocolSpec/Basic.lean:31`) is
a length and a sequence of directions and types, so a prover message cannot select what comes
next, and every protocol whose round structure depends on a public message must be padded.

The current interaction layer has message-dependent shape, but executes oracle protocols by
converting between two tree types. `Oracle/TypeTree.lean` defines `runtimeLens` (line 122),
`toTypeTree` (line 151) and the path conversion `toTypeTreePath` (line 183): a protocol is
authored as one tree and run as another, and every statement about a run must be transported
back across the conversion. Ownership is carried by a separate role decoration (record D2).

One tree with a lens signature removes both problems. The tree is the only thing that is run.
The lens says who moves and what is sent, and `PathAlong` versus `Path` separates what was sent
from what the shape may depend on. Whether a move can select the continuation is decided by the
lens's backward map, so record D1 can make challenges and oracle payloads shape-irrelevant by
typing.

## Alternatives considered

- **Extend `ProtocolSpec`.** A fixed-length index cannot express a message that selects the
  remaining protocol without padding or encoding, and composition must reindex `Fin` sums.
- **Keep the `TypeTree` source and a role decoration.** This is the current interaction layer.
  It allows any move, including a challenge, to select shape (record D1), and it duplicates
  ownership outside the tree (record D2).
- **Use a lens as a conversion between two tree types.** This is today's `runtimeLens` and
  `toTypeTree`. It is excluded: a lens here is a signature over one tree, never a change of
  representation during execution.
- **Identify `Path` and `PathAlong (Lens.id P)` by definitional unfolding.** This fails for
  variable trees because `projectPathAlong` is stuck there; it would reintroduce the equality
  transports that the separate append families avoid.

## Consequences

- There is one execution tree. No execution step converts it to a `TypeTree` or any other tree.
- Clients write suffix families over `Path s₁` and participant data over `PathAlong l s₁`.
  Moving between the two is always `projectPathAlong`, and at the identity lens
  `projectPathAlong_id`.
- The general polynomial universes stay independent of the role polynomial's universe (record
  D2).

**Implementation.** P commit 1 adds `Move`, `owner`, the role polynomial and an `ofRoles`
constructor. P commit 2 adds `projectPathAlong_id` and the product and replication ledger with
their inverse and constructor laws.

**Acceptance tests (in P).**

- A fully branching example at the identity lens, using `projectPathAlong_id`.
- A message/challenge signature where different challenges give the same shape path but
  different `PathAlong` transcripts and different dependent outputs.
- A message that selects genuinely different suffix trees.
- Append/split and product-transport round trips; replication at zero and several rounds.
- An ordinary-import client in `PolyFunTest/ModuleAPI/` at the universes of record D2.

## Open points

None. The record fixes vocabulary that later records use.
