# D10. Protocol specifications and the round-iteration proof kit

**Status:** Proposed: awaiting maintainer approval.
**Implemented by:** a post-milestone track, in the stages listed under "Order of work". Stage 0 is
the two prototypes under `docs/design/interaction-layer/prototypes/`: `ProtocolSpecs.lean` (the
specification layer) and `RoundIteration.lean` (the proof kit's first item).

Lean blocks below that name a prototype declaration exist in those files and compile against the
stack tip. Blocks marked "intended, not existing" specify later work, as in the other records.

## Decision

**One description per protocol.** An author writes an interactive oracle reduction once, as a
value of a description type whose terms read like a paper's protocol figure: named prover
messages (plain or oracle) with their honest formulas, named challenges, named verifier checks
written next to the round whose moves they read, local definitions, rounds and stages. The
interaction layer's objects are definitions computed from that value. Nothing else is written by
hand for the protocol's construction.

```lean
-- prototype: ProtocolSpecs.lean (abridged)
inductive Desc (M : Type → Type) (W T : Type) : OracleProtocol → List Item → Type 1 where
  | done (out : T) : Desc M W T (.pure ⟨⟩) []
  | message (label : String) (X : Type) (name : String) (honest : W → X) (display : Display)
      {t : X → OracleProtocol} {ks : List Item} (rest : (x : X) → Desc M W T (t x) ks) :
      Desc M W T (.liftBind (.message X) t) (.step label .message name display :: ks)
  | oracle (label : String) (X : Type) (I : OracleInterface X) (name : String)
      (honest : W → X) (display : Display) {t : OracleProtocol} {ks : List Item}
      (rest : Oracle M X I → Desc M W T t ks) :
      Desc M W T (.liftBind (.oracle X I) fun _ => t) (.step label .oracle name display :: ks)
  | challenge … | check (label) (c : M Bool) … | compute … | mark (item : Item) …
```

The description is in continuation-passing style. Its two indices are the protocol tree `t` and
the skeleton `ks`. A continuation receives a challenge value, an oracle handle or a local value,
but it cannot change either index. This is record D1's rule that challenges and oracle payloads
do not select shape, enforced by the type. A plain message's continuation may change the tree, as
D1 allows.

**Shallow elaboration, deep skeleton.** The description elaborates to the existing core objects,
and proofs work on those objects exactly as they do on hand-written ones.

| Output | Definition | Core object |
|---|---|---|
| Protocol tree | `Spec.tree` (the index `t`) | `OracleProtocol` |
| Honest prover | `Spec.prover`: run the description at `M = Id`, sending `honest w` and answering its own oracle queries | `Focal oracleSig m t Out` |
| Verifier decision | `Spec.decision`: run the description at `M = OracleComp (oracleMessageSpec t p)`, reaching every check, deciding at the leaf | `OracleComp … (Option T)` |
| Verifier | `Spec.verifier` | `OracleVerifier` |
| Accessors | `tr.msg "g" i`, `v.msg "r" i`: the move labeled `"g"` in its `i`-th occurrence | projections of `Transcript`, `View` |
| Skeleton | `Spec.skeleton` (the index `ks`), exported to JSON and LaTeX | new: `List Item` |

The skeleton is computable even when the description uses noncomputable Mathlib polynomials,
because it is read from the type. Tools read the skeleton; proofs never do.

**Checks are written in place and decided at the leaf.** A `check` line sits in its round, but the
verifier runs every check in order and returns its decision once, after the interaction. This
keeps record D4's passive verifier and the fixed premise that nothing rejects early. The verifier
reaches an oracle message only through an `Oracle` handle, whose single operation is `query`.

**Labels and display text live in the skeleton index.** Record D2 places non-ownership metadata
outside the tree. The skeleton index carries each step's label, kind, printed type and optional
`tex` and `doc` strings, beside the tree rather than on it. Accessors compute positions from the
same index (`movePos`), so the skeleton and the accessors agree by construction.

**Rounds count up and carry round-indexed state.** `rounds name n init body next` runs `body i`
for `i = 0, …, n - 1`, with state `State i → State (i + 1)` and a per-round error string. The
tree recursion counts rounds remaining internally (`roundsGo`), so the generated tree is the
existing one (for sum-check, `Sumcheck.protocol R d n`) with no cast in any statement. This
settles record D5's open point on dependent iteration state for the case the ported protocols
need: the state type may depend on the round index, and the iteration is a dependent fold that
the description owns, not `FreeM.replicate`.

**Stages declare their boundary claims.** `stage name input output body next` groups steps and
records the claim the stage consumes and the claim it produces, each with the point where it is
stated. The skeleton's claim edges come from these declarations. A composed protocol is a
description whose stages are other descriptions; Spartan's outer and inner stages both reuse the
sum-check description.

**A proof kit consumes the same round structure.** The iteration theorem builds round-by-round
soundness of an n-round iteration from a one-round obligation. The obligation mentions no spine,
cursor or partial transcript.

```lean
-- prototype: RoundIteration.lean (abridged)
def RoundSound (chal : ∀ i, ProbComp (rs i).Chal) (step : Step rs S)
    (good : ∀ i, S i → Prop) (ε : Fin n → ℝ≥0∞) : Prop :=
  ∀ (i : Fin n) (st : S i.castSucc) (msg : (rs i).Msg), ¬ good i.castSucc st →
    Pr{let c ← chal i}[∃ st', step i st msg c = some st' ∧ good i.succ st'] ≤ ε i

theorem Rounds.rbrSoundness (w : Rounds rs 0 n (Nat.zero_add n) s) … (hround : ∀ x, RoundSound chal step (good x) ε) :
    Interaction.rbrSoundness oracleSig s admissible language accepts draw (fun c => ε (w.roundOf c))
```

`Rounds rs j k h t` is a witness that the tree `t` is the iteration of the round family `rs`, so a
protocol keeps its own tree. Soundness with error `∑ i, ε i` follows through the existing
`OracleVerifier.soundness_of_rbrSoundness`. The sum-check round argument is stated once, as
`claimReduction_le`, on top of ArkLib's `prob_agreement_of_sum_ne`.

**Statements read like the paper.** A statement front end fixes the execution parameters of the
common case: no ambient oracle unless the protocol uses one, uniform challenges, the relations
from the specification's input and output claims, and acceptance as the decision returning
`true`.

```lean
-- intended, not existing
theorem sumcheck_sound : (sumcheck n d D).Sound (error := n * d / Fintype.card R)
theorem sumcheck_rbr   : (sumcheck n d D).RBRSound (error := fun _ ↦ d / Fintype.card R)
```

`Sound` and `RBRSound` unfold to `OracleVerifier.soundness` and `rbrSoundness`. The general forms
stay available.

**One skeleton schema.** The exporter writes `arklib-protocol-skeleton/0` JSON (steps with id,
label, owner, kind, block, round, stage, printed type, `tex` and `doc`; stages with their input
and output claims; claim edges `{from, to, label, point}`; per-round errors) and a `cryptocode`
figure. The Binary Jolt Book's book-graph reads the same schema.

## Why

**Readability.** The current interaction layer gets the protocol shape right but scatters the
figure. In sum-check, the verifier's check (`intervalCheck`, `Interval.lean:99`) sits inside a
claim state with a proof field `round_add`, the decision is a fold over paths and views
(`Interpreted.lean:41`), the honest message is in `IndexedDomain.lean`, the prover fold in
`IntervalCompleteness.lean` and `Protocol.lean`, and moves are reached by position (`tr.2.1`,
`⟨.inr ⟨⟨⟩, .inl ⟨⟩⟩, rfl⟩` at `SingleRound.lean:85`). A reader assembles one round from 12 files
and 2,351 lines. The prototype's sum-check description is 19 lines in protocol order:

```lean
-- prototype: ProtocolSpecs.lean (round body; `sumcheck` wraps it in `rounds`)
  oracle "g" (R⦃≤ d⦄[X]) (fun w => Sumcheck.projectedRoundPolynomial D ⟨i, hi⟩ st.challenges (poly w))
    (tex := "g_i(X) = \\sum_{x \\in D^{n-i-1}} p(r_{<i}, X, x)") fun g =>
  check "sum" (do
      let vs ← (List.finRange k).mapM fun a => g.query (D a)
      pure (decide (vs.sum = st.target)))
    (tex := "\\sum_{a \\in D} g_i(a) = c_i") <|
  challenge "r" R (tex := "r_i \\gets \\mathbb{F}") fun r =>
  compute "c" R (g.query r) (tex := "c_{i+1} = g_i(r_i)") fun c =>
  next ⟨c, Fin.snoc st.challenges r⟩
```

**Modularity.** Protocol-specific mathematics is 8–45% of each security proof today. In
sum-check's new-layer proof the rest is hand recursion over `Cursor.Spine` (`foldPrefix` and about
eight companion lemmas in `Indexed.lean`). The kit does that recursion once. Through it,
`indexedVerifier_soundness_viaKit` proves exactly the statement of
`Sumcheck.indexedVerifier_soundness` in 124 lines instead of 317. The sum-check round argument,
proved four times today (`Indexed.lean:117`, `Spec/SingleRound.lean:560`, RingSwitching
`RoundSecurity.lean:54`, Binius `Steps/Fold.lean:850-890`), becomes one lemma.

**The two belong together.** Rounds, stages, round-local checks and boundary claims make a
specification readable, and the generic theorems induct over the same structure. A round's
checks give the candidate state function, its declared error is the obligation's `ε i`, and a
stage is a link in a composition chain.

**Stage-0 evidence.** For every `n`, the sum-check description yields ArkLib's tree
(`sumcheck_tree`, `rfl`), its honest prover (`sumcheck_prover`, equal to `intervalProver`), and
its verifier decision on every transcript (`sumcheck_decide`, against `indexedVerifier`), with
`sumcheck_outputMap` by `rfl`. Every theorem in both prototypes depends only on `propext`,
`Classical.choice` and `Quot.sound`.

## Alternatives considered

- **A deep embedding with a denotation.** It would make the projection to prover and verifier a
  real theorem, but it would put a denotation between every proof and the protocol. Proofs would
  stop working on the core objects.
- **Custom syntax first** (a `protocol … where` block, as in the old `Choreo.lean` on
  `origin/quang/core-rebuild`). Custom syntax gives worse error messages and must be maintained
  against the core. `Choreo.lean`'s notation is what tied it to the old `Spec`/`RoleDecoration`
  API. Notation comes after the combinators stabilize, and stays optional.
- **Early rejection at a check.** It would change record D4 and the fixed premise that nothing
  rejects early. Placement next to the round is presentation; the decision stays at the leaf.
- **Labels stored only in the exported skeleton.** Accessors and the figure could then disagree.
  Keeping labels in the type index makes them one source.
- **Constant-state `FreeM.replicate` with round index and history as strategy state** (record D5's
  current plan). Sum-check's claim state has a challenge vector whose length is the round index,
  so the state type depends on the round. A constant state would need a bounded history with a
  length invariant in every protocol.

## Consequences

- A ported protocol has a specification of a screen or two, and its figure, claim-flow graph and
  timeline are generated, not retyped.
- Each protocol needs one agreement proof per hand-written form it replaces, by induction on the
  rounds (`prove_roundsGo`, `decision_roundsGo`), until the hand-written form is deleted.
- A protocol's soundness proof becomes its one-round obligation plus the round's algebra, as
  long as its rounds fit the kit's round shape (see the open points).
- Record D5's iteration section changes: dependent round state is owned by the description and
  the `Rounds` witness, not by `FreeM.replicate`.

**Acceptance tests** for each stage that turns the prototypes into library code:

- Tree agreement by `rfl` with every hand-written tree a specification replaces.
- Honest-prover and decision agreement theorems for every `n`, as in the prototype.
- Accessor examples `tr.msg label i` that reduce by `rfl` at a concrete size.
- The exporter's JSON parses and its TeX compiles with `cryptocode`.
- A soundness theorem through the kit whose statement equals the hand-written one, checked by
  elaborating the original statement's type against the new proof.
- No `cast`, `Fin.cast` or `Fin.vsum` in any specification.

## Order of work

| Stage | Content | Exit |
|---|---|---|
| 0 | This record and the two prototypes | The maintainer approves this record |
| 1 | Iteration combinator, iteration theorem, claim-reduction lemma, run lemma for passive verifiers, in `ArkLib/Interaction/`; sum-check soundness re-proved through them | The new proof is a small fraction of `Indexed.lean`, and the legacy-equivalence theorems still hold |
| 2 | Specification layer for sum-check: labels, accessors, skeleton, statement front end, exporter | Sum-check's specification fits on one screen, and its generated figure matches a paper figure line for line |
| 3 | Oracle-verifier and `StageChain` composition theorems, single-round helpers, the missing implications, completeness composition, a component library on #1578's lifts; Spartan ported as a specification of stages | Spartan's total error comes from the chain theorem with no manual sum |
| 4 | FRI, then BinaryBasefold and RingSwitching, then WHIR | No `cast` or `Fin.vsum` in each specification, and each proof reuses the kit |
| 5 | Symbolic sum-check ("claims as data") and batching with placement; the Binary Jolt Book's first slice rendered from the skeleton | `spartan.outer` renders from the exported skeleton |

Fiat–Shamir and BCS on the new layer run in parallel from stage 1. They need stage 3's composition
theorems only for the end-to-end statement.

## Open points

- **Open: display text is not checked.** Each step's `tex` is a string written beside its Lean
  term. Options: generate it from the term with a delaborator, or test it on sample values. Until
  then a reviewer checks the two by reading.
- **Open: input oracles.** A description cannot yet query the input oracle bundle. The FRI example
  therefore sends `f_0` as a message, and Spartan's final check reads the witness oracle the prover
  sent.
- **Open: round shape.** `rounds` requires the same tree shape every round, so the toy FRI keeps
  one domain instead of halving it. The kit's `Round` is exactly one oracle message followed by one
  challenge; plain messages, several moves per round and a final message after the last challenge
  are not covered, which blocks a FRI instance of the kit.
- **Open: proof ergonomics.** Proofs about descriptions need `set_option smartUnfolding false`.
  `simp` leaves `if "g" = "g" then …` stuck inside accessor result types, and dot notation
  `(sumcheckSpec R d 3 D).Tr` fails because a `Spec` is a function type, so proofs write
  `Spec.Tr (…)`.
- **Open: label scope.** Labels are global: in Spartan, `tr.msg "g" 2` is the inner stage's first
  round polynomial. Labels need stage-scoped paths such as `spartan.outer.round[1].g`.
- **Open: dependent shapes in figures.** Protocols whose later shape depends on an earlier plain
  message are allowed by the core and by `Desc.message`, but the skeleton is one list and cannot
  show a branch. Sum-check and FRI do not need it, so it can follow stage 2.
- **Open: where the symbolic sum-check layer lives.** This record proposes ArkLib, as a generic
  layer that Spartan, GKR, Jolt and Binary Jolt instantiate, with Binary Jolt's `SymbolicSumcheck`
  as the reference shape.
- **Open: elaboration cost at scale.** Nobody has measured elaboration time for the prototype's
  `rfl` checks or for generated accessors on deep trees, such as a full Spartan. In #1599 a
  projection elaborated slowly enough that the `LoggedExecution` test used a `match` instead.
