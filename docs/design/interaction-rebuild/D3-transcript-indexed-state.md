# D3. Transcript-indexed state, shape-indexed trees, and the verifier view

**Status:** Proposed: awaiting maintainer approval.
**Implemented by:** PolyFun PR P (output families over `PathAlong`; the generic transcript map
`PathAlong.mapMoves`) and ArkLib PR A (commits 2–3, the verifier view and its use by the decision).

## Decision

Three observations of a run are kept separate. Each piece of data is indexed by exactly one of
them.

| Observation | Type | Contains | Indexes |
|---|---|---|---|
| Shape path | `p : Path s` | Public messages (the branches taken) | Suffix trees, the oracle family `oracles s p` (record D6) |
| Verifier view | `(p : Path s) × View s p` | Public messages and challenges as values; oracle positions as `PUnit` markers | The verifier's decision, the output oracle map |
| Full transcript | `PathAlong l s` | Every move, including oracle payloads | Party outputs, strategy state, bookkeeping claims, state functions and extractors |

**Outputs and state are indexed by the full transcript; trees by the shape path.** A party's
output family is `OutputP : PathAlong l s → Type u` (and `OutputC` for the counterpart), so an
output may depend on challenges and on oracle payloads. A suffix tree is `s₂ : Path s₁ → FreeM P
PUnit` (record D0), so it cannot. Challenge-dependent state (for example Sumcheck's running
target) is carried in the strategy and its outputs, never in the shape.

**The generic transcript map belongs to PolyFun.** PolyFun PR P adds a map of transcripts
between two lenses over the same polynomial functor, along a move map that respects branches
(module `PolyFun/PFunctor/Free/Path/MapMoves.lean`):

```lean
-- intended, not existing (PolyFun PR P)
structure PathAlong.MoveMap (l : Lens P Q) (l' : Lens P R) where
  map    : (a : P.A) → Q.B (l.toFunA a) → R.B (l'.toFunA a)
  branch : ∀ a d, l'.toFunB a (map a d) = l.toFunB a d
def PathAlong.mapMoves (g : MoveMap l l') : (s : FreeM P α) → PathAlong l s → PathAlong l' s
theorem projectPathAlong_mapMoves (g s tr) :
    projectPathAlong l' s (PathAlong.mapMoves g s tr) = projectPathAlong l s tr
theorem PathAlong.mapMoves_id : mapMoves (MoveMap.id l) s tr = tr
```

**The verifier view is the fibre of the view transcript over the shape path.** ArkLib defines a
view signature that agrees with `oracleSig` except that it erases the payload type of oracle
positions, the move map that performs the erasure, and the view as a fibre:

```lean
-- intended, not existing (ArkLib PR A)
def viewSig : Lens OraclePoly rolePoly.{u} where
  toFunA | .message X => (.sender, X) | .challenge C => (.receiver, C)
         | .oracle _  => (.sender, PUnit)
  toFunB | .message _ => id | .challenge _ => fun _ => ⟨⟩ | .oracle _ => fun _ => ⟨⟩

-- identity on message and challenge moves, `fun _ => ⟨⟩` on oracle moves
def eraseOracle : PathAlong.MoveMap oracleSig viewSig

def View (s : FreeM OraclePoly PUnit) (p : Path s) : Type u :=
  {v : PathAlong viewSig s // projectPathAlong viewSig s v = p}

def toView (s) (tr : PathAlong oracleSig s) : View s (projectPathAlong oracleSig s tr) :=
  ⟨PathAlong.mapMoves eraseOracle s tr, projectPathAlong_mapMoves eraseOracle s tr⟩
```

The decision is typed against the shape path and the view over it:

```lean
-- intended, not existing
decide : StmtIn → (p : Path s) → View s p →
  OptionT (OracleComp (oSpec + [OStmtIn]ₒ + oracles s p)) StmtOut
-- in a run: decide stmt (projectPathAlong oracleSig s tr) (toView s tr)
```

The call needs no cast: the oracle family is indexed by `p`, which is the run's shape path
itself, and the fibre carries the equation `projectPathAlong viewSig s v = p` as a proof rather
than in a type index. The decision reads public messages and challenges as values from `v` (or
`p`) and reaches oracle payloads only by queries to `oracles s p`, answered from the same run
(record D4).

For a plain signature every move is public: the view signature is `plainSig`, the move map is
the identity (`mapMoves_id`), and the fibre over `p` holds the full transcripts with shape path
`p`, so the plain view carries every move.

**Who may read the full transcript.** A claim may be indexed by the full transcript for
bookkeeping. Round-by-round state functions and extractors read the full transcript, including
prefix oracle payloads, as data (record D7). This is not query access and does not weaken the
view: the security statements quantify over them separately from the verifier.

## Why

The legacy layer enforces a view by giving the oracle verifier only the challenges:
`OracleVerifier.verify : StmtIn → pSpec.Challenges → OptionT (OracleComp (oSpec + ([OStmtIn]ₒ +
[pSpec.Message]ₒ))) StmtOut` (`OracleReduction/Basic.lean:337`). Every message is an oracle
message, so a public message must be given a trivial oracle interface and queried. The bundled
`toVerifier` (`Basic.lean:484`) instead reads the messages in the clear; the bundled security
interface uses it, so the two observations are distinguished only by which function is called.

The interaction layer has public messages that are read as values (they may select shape) and
oracle messages that must not be. A decision typed against the full `PathAlong` would receive
oracle payloads as values, and "the decision does not read them" would be a convention rather
than a typing fact.

The view is a fibre over `Path s` because the decision's oracle family is indexed by the path.
If the view were a free-standing transcript `v` with a separate projection law, the decision would
be typed at `oracles s (projectPathAlong viewSig s v)`, and running it on the view of `tr` would
require identifying `OracleComp (… + oracles s (projectPathAlong viewSig s (mapMoves … tr)))` with
`OracleComp (… + oracles s (projectPathAlong oracleSig s tr))` along a propositional equation.
That is a cast in the index type of `OracleComp`, and every statement about the decision
(simulation, query logs, the composition and legacy equivalence laws) would have to commute past
it. Passing `p` explicitly and keeping the equation inside the fibre indexes the decision and the
oracle implementation of record D6 by the same `p`.

## Alternatives considered

- **Decision on the full `PathAlong`, with a no-payload convention.** Not enforced, and the
  acceptance test "the decision reaches oracle messages only by queries" would have nothing to
  check.
- **Decision on the full `PathAlong`, plus a law that it depends only on the view** (`decide stmt
  tr = decide stmt tr'` whenever the two transcripts have the same view). This is a proof
  obligation on every verifier, and it leaves the same acceptance test with nothing to check.
- **A free-standing view transcript `PathAlong viewSig s`, with the projection law outside the
  type.** Introduces the `OracleComp` index casts described above.
- **Decision on the shape path plus a separate list of challenges** (the legacy form, adapted).
  Challenges sit at tree nodes whose existence depends on earlier public messages, so "the list of
  challenges" is itself a dependent type over the shape path; the fibre `View s p` supplies it.
- **A second tree for the verifier, converted from the protocol tree.** Excluded: no lens is used
  as a conversion between tree types.
- **Indexing state by the shape path.** Loses challenge dependence, which Sumcheck's running
  target needs.

## Consequences

- P's output families, composition and packing operate on `PathAlong` (records D0 and D5). No
  output is indexed by `Path` except through `projectPathAlong`. P also adds `PathAlong.MoveMap`,
  `mapMoves`, `projectPathAlong_mapMoves` and `mapMoves_id`.
- A provides `viewSig`, `eraseOracle`, `View`, `toView`, and the decision and output oracle map
  (record D6) typed against `(p, View s p)`. Composition splits views along `Path.append` (record D5).
- Exported oracle claims depend on the statement, the view and the input and message oracles,
  never on raw payloads.

**Acceptance tests.** In A: a decision written against `View` that therefore cannot read an
oracle payload as a value; a recorded challenge changes a dependent output without changing the
shape path; `toView` on a mixed message/oracle/challenge tree, and a run that calls the decision on
`toView` with no cast. In P: `mapMoves_id` and `projectPathAlong_mapMoves`.

## Open points

None.
