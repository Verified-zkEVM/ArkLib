# D2. Ownership from the signature, the universe policy, and role-free metadata

**Status:** Proposed: awaiting maintainer approval. The universe policy replaced the earlier
universe ledger on 2026-11-25; the code still follows the ledger until the
[migration](#migration) lands.
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
theorem Transcript_swapOwners (l s) : Transcript l.swapOwners s = Transcript l s   -- same moves
```

The exchange of the paired participants and of the run under swap belongs to record D4, because
swapping changes which party moves first at each boundary.

**Non-ownership metadata stays in `Γ`.** Data that is not ownership (for example oracle
interfaces, if record D1's open point puts them there) may remain in the generic context `Γ` of
`SyntaxOver`. `Γ` never contains a role.

### Universe policy

**Rule.** Every universe parameter of an ArkLib declaration occurs in the type of one of its
arguments. A universe that only the result type, a structure field or a `Prop` body mentions is
not allowed.

| Object | Universe | Parameter |
|---|---|---|
| Data: moves, messages, challenges, oracle payloads, query and response types, oracle indices, statements, input, intermediate and output witnesses, transcripts, logs, costs, experiment state | `Type` | none |
| Descriptions of data: positions (`PlainPos`, `OraclePos`), protocols (`Protocol`, `OracleProtocol`), `OracleInterface X`, oracle families and bundles, problem bundles (`Problem`, `ClaimFamily`, `ConstraintSystem`) | `Type 1` | none; forced, because a description names a type |
| Adversaries and extractors: `AdversaryModel.Adv`, `ExtractionInterface.Ext` | `Type w` | one; the model argument determines it |
| Generic polynomial machinery: declarations over an arbitrary `P : PFunctor` | PolyFun's universes | determined by `P` |
| Upstream libraries (Mathlib, VCVio, PolyFun) | their own | ArkLib instantiates them at `Type` |

The runner is `m : Type → Type`, and positions are never its values, so the description universe
`Type 1` never meets the monad. Each upstream constant whose universes no argument determines
(for example `[]ₒ`) gets one ArkLib alias at `Type`.

[`universe-policy.md`](../interaction-layer/universe-policy.md) gives the measurements, the
Lean experiments, the options compared, and the workarounds for what the policy rules out.

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

**Why the universe rule.** Universe polymorphism costs nothing when an argument determines each
universe: Mathlib's `Probability` folder is written with `Type*` and has 0.2 explicit universe
annotations per thousand lines. ArkLib's core has 61. A scan of the core's 1,247 declarations
finds 56 whose universes no argument determines, and those 56 are the vocabulary every client
uses. They cause three failures, each reproduced in Lean in the companion document:

- A constant without arguments (`Protocol`, `OracleProtocol`, `[]ₒ`) gets fresh universes at each
  use, so every use needs a pin. A pin on the constant and a pin on its lemma can also name the
  universes in different orders.
- A universe that only a `Prop` mentions (the intermediate witness universe `uK` of
  `rbrKnowledgeSoundness`) elaborates separately in a hypothesis and in a goal, so
  `h : rbrKnowledgeSoundness … ⊢ rbrKnowledgeSoundness …` fails without a pin or a `.lift` lemma.
- Independent universes that meet the runner either fail to unify (`u =?= max u v`) or elaborate
  at a universe that Lean invents.

The independence also does not survive composition: every intermediate statement is a run output,
so only the first statement of a chain has its own universe.

**Why data in `Type` and not one polymorphic data universe `u`.** At `u = 0` the two are the same.
A larger `u` buys only data that is itself large, such as a move that is a type or a statement
that bundles types. No client has such data, and each case has a workaround (send a code or a
size, make the bundle a parameter, or send it as data). A larger `u` does not serve the quantum
provers of record D9 either. Their messages are small and only the prover is large, so they need
a separate adversary universe, which the policy keeps. Moving from `Type` to one universe `u` later
is mechanical, because all data shares one universe.

**Why positions stay apart from moves.** If the move universe were tied to the position universe,
the monad would have to be `Type 1 → Type 1` and every participant output would move up a
universe, only because a position names a type.

## Alternatives considered

- **Keep a `RoleDecoration` beside the lens.** This is the duplicate role field that the decision
  removes. It needs a coherence condition between decoration and lens, and every operation must
  maintain it.
- **Swap by rewriting the source tree.** There is nothing to rewrite: the tree carries no roles.
  Swap as a lens leaves the tree and transcripts unchanged.
- **One universe for positions, moves and the monad.** It forces the monad into `Type 1` and
  every participant output with it.
- **Independent universes for each component (the earlier ledger).** It has all three failures
  above, needs 15 adapter declarations that only change universes, and gives generality no client
  uses.
- **Everything in `Type`, including adversaries and generic code.** It blocks the quantum provers
  of record D9 and stops generic tree code from moving to PolyFun.

## Consequences

- Clients never write role decorations. The PolyFun cleanup PR (P-clean) deletes
  `TwoParty/Decoration.lean` once no ArkLib client uses it. A failed cutover is detected by any
  remaining use of `RoleDecoration` in new production or test code.
- The existing `Role` type is shared. The new participant type does not depend on the old
  role-decoration modules.
- Generic `SyntaxOver`, `Ownership` and `MonadDecoration` keep PolyFun's universe parameters.
  ArkLib's signatures, protocols, runs and security definitions fix them as in the policy.

**Acceptance tests.** P includes an ordinary-import client in `PolyFunTest/ModuleAPI/` that
instantiates the generic API at `P : PFunctor.{u+1, u}` with `m := OracleComp spec` and
`Participant.{u}`, plus `swapOwners_swapOwners` and an ownership-swap example. A's signature
clients check `owner` on every ArkLib position kind.

## Migration

The code follows the earlier ledger until these steps land. Each is one PR or part of one.

1. This record and [implementation note 18](IMPLEMENTATION-NOTES.md#18-run-outputs-are-tied-to-the-monad-universe).
2. `Relation/`: `OracleInterface` and `Relation` at `Type`.
3. Signatures and protocols: drop `u` and `q`; leaves become `Unit`.
4. Oracle bundles, families, routing, sent oracles and reassociation; delete the universe
   adapters (`liftQueries`, `lowerQueries`, `liftResponse`, `liftInputs`, `liftOutputs`).
5. Execution, reductions, oracle verifiers, composition and stage chains.
6. Security definitions: drop the statement and witness universes and both `.lift` lemmas; keep
   the adversary universe.
7. Tests and clients: replace `UniverseCanary.lean` with a policy test (generic code at a large
   polynomial, an `AdversaryModel` with `Adv : Type 1`), drop client pins, add the `[]ₒ` alias,
   and update the port tables and disposition records that describe universes.
8. CI: a linter that checks the rule on `Interaction/` and `Relation/`, allowing only the
   adversary universe and the generic files.

## Open points

- Whether the quantum layer needs a core theorem to accept prover outputs in `Type 1`. If it does,
  the prover argument determines that universe, so the rule permits it.
- Which files count as generic, and when they move to PolyFun.
- Whether VCVio adds a `Type` alias for `[]ₒ` upstream.
- Record D1's placement of oracle interfaces, which decides whether `Γ` is empty for ArkLib
  signatures.
