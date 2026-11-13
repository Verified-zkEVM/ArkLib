# D1. Plain and oracle signatures, and the shape restriction

**Status:** Proposed: awaiting maintainer approval.
**Implemented by:** ArkLib PR A (commit 2 for plain signatures, commit 3 for oracle signatures).

## Decision

ArkLib uses two source polynomials, authored separately. A *plain* protocol has two kinds of
position; an *oracle* protocol has a third.

| Position | Owner | Move type | Branch type | Branch map |
|---|---|---|---|---|
| `message X` | sender (prover) | `X` | `X` | identity |
| `challenge C` | receiver (verifier) | `C` | `PUnit` | constant |
| `oracle X` (oracle protocols only) | sender (prover) | `X` | `PUnit` | constant |

```lean
-- intended, not existing
inductive PlainPos : Type (u+1)
  | message   (X : Type u)
  | challenge (C : Type u)

def PlainPoly : PFunctor.{u+1, u} :=
  ⟨PlainPos, fun | .message X => X | .challenge _ => PUnit⟩

def plainSig : Lens PlainPoly rolePoly.{u} where
  toFunA | .message X => (.sender, X) | .challenge C => (.receiver, C)
  toFunB | .message _ => id           | .challenge _ => fun _ => ⟨⟩

inductive OraclePos : Type (u+1)
  | message (X : Type u) | challenge (C : Type u) | oracle (X : Type u) -- interface: see open point

def oracleSig : Lens OraclePoly rolePoly.{u}   -- as above; `oracle X ↦ (.sender, X)`, branch `PUnit`
```

The *shape restriction* follows from the branch types. A challenge or an oracle payload has a
`PUnit` branch, so it is recorded in `PathAlong` but not in `Path`. A suffix family has type
`s₂ : Path s₁ → FreeM P PUnit`, and a participant after a transcript `tr₁` sees
`s₂ (projectPathAlong l s₁ tr₁)` (record D0). Hence:

```lean
-- intended, not existing
-- Two full transcripts that differ only in challenges and oracle payloads have the same shape
-- path, and therefore the same suffix tree.
theorem projectPathAlong_eq_of_publicMessages_eq
    (tr tr' : PathAlong plainSig s) (h : publicMessages tr = publicMessages tr') :
    projectPathAlong plainSig s tr = projectPathAlong plainSig s tr'
```

(For a plain protocol the shape path *is* the list of public messages, so the theorem is close
to a restatement; it is listed as an acceptance client, not as new theory.)

The restriction holds across composition: the suffix of an appended reduction is indexed by the
prefix's shape path and the composed reduction's input statement, never by a challenge, an
oracle payload, or a value that the prefix verifier obtained by an oracle query (record D6).
A challenge or oracle payload may still change strategy state, outputs, and relations; such data
is carried in `PathAlong`-indexed state (record D3), not in the shape.

"Public" or "hashed" is not a reason to allow shape dependence. Challenges are public and are
still erased from the shape path.

## Why

The current interaction layer lets any move select the remaining protocol. The test
`ArkLibTest/Interaction/CompositionExecution.lean` states this as its purpose: "A public
challenge selects the suffix tree" (line 11). Its prefix is a single receiver node (line 22), and
`suffixTree` returns different trees on the two challenge values (lines 30–32). Under the
commitment that challenges never change shape, an ArkLib protocol of this form must be
unwritable.

Making the restriction a typing fact rather than a hypothesis matters downstream. Fiat–Shamir
replaces challenges by hash outputs and must not change which tree is run; round-by-round errors
are indexed by challenge nodes (record D7), which is meaningful only if the set of challenge
nodes does not depend on challenge values; and the oracle family of a run must be determined by
public data (record D6).

## Alternatives considered

- **Challenge branches of type `C`, with a separate shape-independence hypothesis.** Every
  suffix selector and every security definition would carry a proof obligation that typing
  discharges for free under the chosen branch types.
- **Allowing shape dependence on any public or hashed value.** Rejected: challenges are public,
  and allowing them reintroduces the problem above.
- **One signature for both layers, or a plain-to-oracle inclusion used at run time.** The
  inclusion of plain positions into oracle positions is mathematically a lens with identity
  backward maps that commutes with the two signatures. Executing a plain protocol through it
  (`mapLens`) is a runtime tree conversion, which is excluded. A direct structural inclusion with
  a transcript equivalence is a possible later convenience; the first milestone authors plain
  and oracle trees separately and does not need it. Transcripts over different tree types are
  never promised to be the same Lean type.

## Consequences

- An ArkLib protocol in which a challenge selects the suffix does not typecheck. The current
  test's generic assertions (both output pairs and the ordered effect traces) move to PolyFun
  over a fully branching receiver signature, where they are valid generic theory (PolyFun PR P).
  ArkLib gets new tests showing that challenges preserve shape while affecting state and
  outputs. PR D records this relocation in its migration list.
- A protocol whose structure depends on a verifier-sampled parameter (for example a random prime)
  uses a fixed-width carrier and a decoder, not a shape-changing challenge.
- Oracle payloads cannot be read by the shape, so an oracle message cannot be hashed to choose
  the continuation; this matches the rule that oracle protocols reach non-interactive arguments
  through BCS.

**Acceptance tests (in A).** Challenges and oracle payloads do not choose shape; a public
message can; recorded challenges still affect dependent outputs.

## Open points

- **Open: where an oracle position's `OracleInterface` lives.** Either the position carries it
  (`oracle X I`), or it lives in non-ownership metadata `Γ` beside the tree. The current
  interaction layer uses a decoration. The choice affects record D6's definition of `oracles`
  but not the shape restriction.
- **Open: a direct plain-to-oracle inclusion convenience.** Deferred until a maintainer decides
  whether a structural inclusion that is never used as a runtime representation change is
  permitted. No first-milestone PR depends on it.
