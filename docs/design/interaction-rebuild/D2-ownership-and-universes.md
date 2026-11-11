# D2. Ownership from the signature, the universe ledger, and role-free metadata

**Status:** Proposed: awaiting maintainer approval.
**Implemented by:** PolyFun PR P (commit 1, signature vocabulary; commit 5, swap) and ArkLib PR A
(commit 2, ArkLib signatures).

## Decision

**Ownership is read from the signature.** The owner of a position is the first component of the
lens's forward map, `owner l a := (l.toFunA a).1` (record D0). There is no separate role
decoration in the new API, and no second role field anywhere that could disagree with the lens.
The paired syntax of record D4 receives the position `pos` (as generic `SyntaxOver.Node` already
does, `Interaction/Basic/Syntax.lean:78`) and computes each participant's perspective from
`owner l pos`:

```lean
-- intended, not existing
def perspective (l : Lens P rolePoly) (pos : P.A) : Participant → Ownership.Perspective :=
  TwoParty.perspective (owner l pos)       -- existing `perspective`, TwoParty/Syntax.lean:45
```

**Swapping ownership is a lens.** Exchanging the two roles is post-composition with the role-swap
lens on `rolePoly`, which is the identity on move types and on branches:

```lean
-- intended, not existing
def roleSwap : Lens rolePoly rolePoly := ⟨fun r => (r.1.swap, r.2), fun _ => id⟩
def Lens.swapOwners (l : Lens P rolePoly) : Lens P rolePoly := roleSwap ∘ₗ l
theorem swapOwners_swapOwners (l) : l.swapOwners.swapOwners = l
theorem owner_swapOwners (l a) : owner l.swapOwners a = (owner l a).swap
theorem PathAlong_swapOwners (l s) : PathAlong l.swapOwners s = PathAlong l s   -- same moves
```

The exchange of the paired participants and of the run under swap belongs to record D4, because
swapping changes which party moves first at each boundary.

**Non-ownership metadata stays in `Γ`.** Data that is not ownership (for example oracle
interfaces, if record D1's open point puts them there) may remain in the generic context `Γ` of
`SyntaxOver`. `Γ` never contains a role.

**Universe ledger.**

| Object | Universe | Reason |
|---|---|---|
| Source polynomial `P` | `PFunctor.{uA, uB}`, independent | Positions may contain types |
| Role polynomial `rolePoly.{u}` | `PFunctor.{u+1, u}` | `Role × Type u : Type (u+1)`; moves lie in `Type u` |
| Move types, participant outputs | `Type u` | Values exchanged and returned |
| Ambient monad `m` | `Type u → Type u` | Runs on moves and outputs only |
| `Participant.{u}` | `Type u` | Matches the monad's universe |
| `PUnit.{u+1}` (challenge and oracle branches) | `Type u` | So constant branches fit `P.B a : Type u` |
| ArkLib positions `PlainPos`, `OraclePos` | `Type (u+1)` | A position names a type |
| Run outputs: output statements `StmtOut p`, output oracle data `B p j`, prover outputs | `Type u` | Returned by the runner `m : Type u → Type u` |
| Oracle responses (ambient, input, path and output oracles) | `Type u` | Answered in the runner's monad |
| Ambient oracle index `ι` of a verifier | independent | Only queried, never returned |
| Ambient oracle index `ι` of a prover, reduction or run | `Type u` | `OracleComp ambient` must be `Type u → Type u` |
| Input oracle index `I` | independent | Simulated away before the verdict |
| Output oracle index `J p` of an oracle verifier | independent; `Type u` in a run | A run returns `∀ j, B p j` |
| Input statement and input witness | independent | Arguments of the decision and the prover, never returned |
| Input oracle data `A i` and its query type | `Type u` | Shares one oracle family with the path's payloads |

ArkLib's polynomials therefore live in `PFunctor.{u+1, u}`, like `rolePoly`. The ambient monad is
not enlarged because a position contains a type: positions are never values of the monad.

Every component that is not a run output takes its own universe as far as the definitions allow,
and only run outputs and oracle responses are tied to `u`. Two non-output components remain tied.
The ambient index of a prover is in `Type u` because `OracleComp ambient : Type u → Type (max uι
u)` is the prover's monad and the runner needs `Type u → Type u`. The input oracle data and its
query type are in `Type u` because the decision queries the inputs and the path's payloads through
one family `sumFamily inputs (pathFamily s p)`, which has one realization universe and one
interface universe, and the path's payloads are in `Type u`. The test
`ArkLibTest/Interaction/Core/UniverseCanary.lean` instantiates the independent universes.

## Why

The current PolyFun two-party syntax takes roles from its context rather than from the lens:
`SyntaxOver.TwoParty.paired` (`Interaction/TwoParty/Syntax.lean:65`) is a `SyntaxOver` with
`Γ := fun _ : P.A => Role`, and its node cases (lines 69–72) match on that decorated role. The
two-party API around it carries a `RoleDecoration` (`TwoParty/Decoration.lean:224`) for every tree,
so every client threads a second tree-shaped object, every append must append decorations, and
swap must map them (`RoleDecoration.swap`, `Decoration.lean:228`; `RoleDecoration.swap_append`,
`Swap.lean:55`). Who moves at a node is recorded only in that second object, not in the tree or
in the lens that says what the move is.

With ownership in the lens, a signature cannot assign a challenge to the prover by accident, and
append and swap need no decoration bookkeeping.

The universe ledger addresses the opposite risk. The current interaction layer's oracle positions
already live one universe up (`Oracle/TypeTree.lean`, `Position`, around line 38). If the move
universe were tied to the position universe, the monad would have to be `Type (u+1) → Type (u+1)`
and every participant output would be pushed up a universe, only because a position names a type.
Separating the universes keeps the runner at `m : Type u → Type u`.

## Alternatives considered

- **Keep a `RoleDecoration` beside the lens.** This is the duplicate role field that the decision
  removes. It needs a coherence condition between decoration and lens, and every operation must
  maintain it.
- **One universe for positions, moves and the monad.** Simpler to state, but it forces the monad
  into `Type (u+1)` for ArkLib and breaks ordinary-import clients at the usual universes.
- **Swap by rewriting the source tree.** There is nothing to rewrite: the tree carries no roles.
  Swap as a lens leaves the tree and transcripts unchanged.

## Consequences

- Clients never write role decorations. The PolyFun cleanup PR (P-clean) deletes
  `TwoParty/Decoration.lean` once no ArkLib client uses it. A failed cutover is detected by any
  remaining use of `RoleDecoration` in new production or test code.
- The existing `Role` type is shared. The new participant type does not depend on the old
  role-decoration modules.
- Generic `SyntaxOver`, `Ownership` and `MonadDecoration` keep their independent universe
  parameters; the common runner fixes them as in the ledger.

**Acceptance tests.** P includes an ordinary-import client in `PolyFunTest/ModuleAPI/` that
instantiates the ledger at `P : PFunctor.{u+1, u}` with `m := OracleComp spec` and
`Participant.{u}`, plus `swapOwners_swapOwners` and an ownership-swap example. A's signature
clients check `owner` on every ArkLib position kind.

## Open points

None beyond record D1's placement of oracle interfaces, which decides whether `Γ` is empty for
ArkLib signatures.
