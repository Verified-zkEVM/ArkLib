# D10. Protocol specifications and the round-iteration proof kit

**Status:** Proposed: awaiting maintainer approval.
**Implemented by:** a post-milestone track, in the stages listed under "Order of work". Stage 0 is
the prototype library `ArkLibPrototypes` under `docs/design/interaction-layer/prototypes/Specs/`.

The prototype is a nondefault Lake library (`lake build ArkLibPrototypes`). It is outside the
production import graph, its files are classic so that `#print axioms` sees proof bodies, and it
builds against `main`. It has no `sorry`, `admit`, `native_decide` or `smartUnfolding` option,
and every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. Lean blocks below
that name a declaration exist in it. Blocks marked "intended, not existing" specify later work.

The first version of the prototype (two standalone files) left eight open points. Review judged
them to be limitations, not open questions. The second version fixes each of them. The section
"Limitations of the first prototype and how this record resolves them" gives the decision, the
reason and the evidence for each.

## Decision

**One description per protocol.** An author writes an interactive oracle reduction once, as a
value of a description type whose terms read like a paper's protocol figure: named prover
messages (plain or oracle) with their honest values, named challenges, reads of input oracles,
verifier checks and local values written as formulas next to the round whose moves they read,
rounds, stages with their input and output claims, and branches on a prover message. The
interaction layer's objects are computed from that value.

```lean
-- prototype: Specs/Examples/Sumcheck.lean
noncomputable def sumcheckRound (n : ℕ) (D : Fin k → R) (poly : W → R⦃≤ d⦄[X Fin n])
    {t : OracleProtocol} {ks : Skel} (i : ℕ) (hi : i < n) (st : Claim R i)
    (next : Claim R (i + 1) → Desc In W T t ks) :=
  oracle (ix "g" i) (R⦃≤ d⦄[X]) R "\\mathsf{proj}"
    (fun w => Sumcheck.projectedRoundPolynomial D ⟨i, hi⟩ st.rs (poly w)) fun g =>
  check "sum" ⟪g, st.c⟫ (fun g c => (∑∈ a ∈ Dom.ofFn "D" D, ask g a) =' .var c) <|
  challenge (ix "r" i) R fun r =>
  compute (ix "c" (i + 1)) R ⟪g, r⟫ (fun g r => ask g r) fun c =>
  next ⟨c, Fin.snoc st.rs r.val⟩

noncomputable def sumcheckSpec (d n : ℕ) (D : Fin k → R) :=
  Spec.mk (In := Sumcheck.polynomialFamily R n d) (W := R⦃≤ d⦄[X Fin n])
    (T := Sumcheck.RoundStatement R n (Fin.last n)) fun stmt =>
  input "p" (Fin n → R) R "R_{\\le d}[X_{1..n}]" (fun x => ⟨(), x⟩) (fun _ => rfl) fun p =>
  stage "sumcheck" ⟪p, (⟨stmt.target⟩ : Val (ix "c" 0) R)⟫
    (fun p c => (∑∈ x ∈ (Dom.ofFn "D" D).pow n "n", ask p x) =' .var c)
    (fun st : Claim R n => ⟪p, (⟨st.rs⟩ : Val "r" (Fin n → R)), st.c⟫)
    (fun p r c => ask p r =' .var c)
    (fun next => sumcheck n D id ⟨⟨stmt.target⟩, stmt.challenges⟩ next
      (tree := fun _ r => Sumcheck.protocol R d r))
    fun st => done ⟨st.c.val, st.rs⟩
```

The description `Desc In W T t ks` is in continuation-passing style. `In` is the input oracle
bundle, `W` the witness and `T` the output. Its two indices are the protocol tree `t` and the
skeleton `ks`. A continuation receives a challenge value, an oracle handle or a local value, but
cannot change either index. This is record D1's rule that challenges and oracle payloads do not
select shape, enforced by the type. A plain message may select the shape (`branch`), as D1 allows.

**Shallow elaboration, deep skeleton.** The description elaborates to the existing core objects,
and proofs work on those objects exactly as they do on hand-written ones.

| Output | Definition | Core object |
|---|---|---|
| Protocol tree | `s.tree` (the index `t`) | `OracleProtocol` |
| Honest prover | `Spec.prover`: send the honest values, answer oracle queries from them and from the input data | `Focal oracleSig m t Out` |
| Verifier | `Spec.verifier`: evaluate every check in order, decide at the leaf, query input and message oracles through `pathBundle` | `OracleVerifier` |
| Pure verdict | `Spec.verdict`: the same walk with the oracle data supplied | `Option T` |
| Accessors | `tr⟦outer, sumcheck, 0, g⟧`, `tr⟦m = 2, sumcheck, 1, r⟧` | projections of `Transcript`, `View` |
| Claims | `Spec.inClaim`, `Spec.outClaim`, `Spec.inputProblem`, `Spec.outputProblem` | ArkLib `Problem`s |
| Skeleton | `s.skeleton` (the index `ks`), exported to JSON and LaTeX | new: `Skel` |

**Formulas, not strings.** Checks, local values and stage claims are terms of a small typed
formula language `Fml v o β` in parametric higher-order abstract syntax (`Specs/Formula.lean`):
variables, literals, ring operations, decided equality, conjunction, finite sums and products with
a binder, oracle queries, coordinate access, and named opaque functions. The verifier evaluates
the term (`Fml.evalM`), the figure prints it (`Fml.tex`), and the skeleton and the JSON carry its
erased syntax (`Syn`). Every name a formula prints is the name in the type of the handle it reads,
so a printed variable is the move it denotes.

**Checks are written in place and decided at the leaf.** This keeps record D4's passive verifier
and the premise that nothing rejects early.

**Rounds count up, carry round-indexed state, and may change shape.** `rounds` runs `body i` for
`i = 0, …, n - 1` with state `State i → State (i + 1)` and an optional tree family, so round
`i`'s tree may depend on `i` (FRI's domain halves). The generated tree is the existing one:
`sumcheck_tree` holds by `rfl` against `Sumcheck.protocol R d n`. This settles record D5's open
point on dependent iteration state: `rounds` and the kit certificate own the state, not
`FreeM.replicate`.

**Stages declare their claims as formulas, and security statements are about those claims.**
`stage name inArgs inClaim outArgs outClaim body next` records the claim the stage consumes and
the claim it produces. `Spec.inputProblem` and `Spec.outputProblem` are the languages those
formulas denote, and the statement front end states soundness and completeness on them.

**A statement front end.** `Spec.Sound`, `Spec.RBRSound`, `Spec.RBRKnowledgeSound` and
`Spec.Complete` (`Specs/Security.lean`) are definitions over `Interaction.Security` applied to the
derived prover and verifier, each with an `iff` lemma proved by `Iff.rfl`. The stage contracts
`ClaimSound`, `ClaimRBRSound`, `ClaimComplete` and `StageContract` state them on the spec's own
claims.

**A proof kit consumes the same round structure.** A kit round is a block of zero or more prover
messages, plain or oracle, with types that may depend on the round, followed by one challenge. An
iteration has a prefix block and a suffix block. The iteration theorem builds round-by-round
soundness from a one-round obligation that mentions no spine, cursor or partial transcript, and
soundness with error `∑ i, ε i` follows.

```lean
-- prototype: Specs/Kit/Iteration.lean
def RoundSound (chal : ∀ i, ProbComp (rs i).Chal) (step : Step rs S)
    (good : ∀ i, S i → Prop) (ε : Fin n → ℝ≥0∞) : Prop :=
  ∀ (i : Fin n) (st : S i.castSucc) (vals : (rs i).msgs.Values), ¬ good i.castSucc st →
    Pr{let c ← chal i}[∃ st', step i st vals c = some st' ∧ good i.succ st'] ≤ ε i
```

**A bridge connects the two.** `Specs/Bridge/Rounds.lean` proves, for any `rounds` block whose
round bodies have the kit's shape, that the spec's verdict factors through the kit's iteration
verdict, and concludes `Spec.Sound` from per-round `RoundSound` (`sound_of_kit`,
`rbrSound_of_kit`). A protocol written in the spec layer thus gets its soundness from the kit
without a hand-written verifier.

**One skeleton schema.** The exporter writes `arklib-protocol-skeleton/1` JSON and a `cryptocode`
figure. The JSON has nested stages, rounds and branch cases. Each step carries its label, kind,
owner, display name, printed type, formula syntax tree and stage claims, and any annotation text
carries `"checked": false`. The figure comes in two forms: folded (one round per block, with the
round variable `i`) and expanded. The Binary Jolt Book's book-graph reads the same schema.

## What the prototype proves

| Claim | Declaration | File |
|---|---|---|
| Sum-check's tree is ArkLib's, for every `n`, by `rfl` | `sumcheck_tree` | `Examples/Sumcheck.lean` |
| Its honest prover is `intervalProver` | `sumcheck_prover` | same |
| Its verdict is `indexedVerdict`, and its verifier agrees with `indexedVerifier` on every transcript | `sumcheck_verdict`, `sumcheck_decide`, `sumcheck_outputMap` | same |
| The decision of any spec equals its pure verdict | `Spec.decide_eq_verdict` | `Run.lean` |
| Any spec accepts the honest transcript when its checks hold on the honest run | `Spec.verdict_isSome` | `Run.lean` |
| Sum-check soundness through the generalized kit, with exactly the statement of `Sumcheck.indexedVerifier_soundness` | `indexedVerifier_soundness_viaKit`, checked with `type_of%` | `Kit/Sumcheck.lean` |
| Round-by-round soundness of FRI's commit phase, whose domain halves each round, from ArkLib's folding lemmas, with no undischarged hypothesis | `commitPhase_rbrSoundness`, `commitPhase_rbrSoundness_johnson` | `Kit/Fri.lean` |
| Soundness of a round with two messages (an oracle and a plain message) | `twoVerifier_soundness` | `Kit/TwoMessage.lean` |
| Soundness of the verifier that `sumcheckSpec` derives, error `n·d/|R|`, through the bridge and not through `indexedVerifier` | `sumcheckSpec_sound` | `Bridge/Sumcheck.lean` |
| The same verifier agrees with the kit's iteration verifier | `sumcheckSpec_agrees` | `Bridge/Sumcheck.lean` |
| Soundness and round-by-round soundness on the claims the figure shows: `Σ_{x ∈ D^n} p(x) = c` in, `p(r) = c_n` out | `sumcheckSpec_claimSound`, `sumcheckSpec_claimRBRSound` | `Claims.lean` |
| Completeness on those claims: a true input claim makes every check pass and the output claim true | `sumcheckSpec_claimComplete`, `sumcheckSpec_contract` | `Claims.lean` |
| Spartan (input oracles `Ã`, `B̃`, `C̃`, two stages reusing sum-check), FRI (halving domain, input oracle `f₀`) and a branching protocol: trees by `rfl`, accessors by label path, honest acceptance | `spartan_tree`, `fri_tree`, `branching_tree`, `*_verdict_isSome` | `Examples/*.lean` |

## Limitations of the first prototype and how this record resolves them

Each item names the first prototype's limitation, the decision, why, the alternatives rejected,
and the evidence in the second prototype.

### 1. Display text was not checked

**Decision.** Checks, local values and stage claims are formulas with three readings:
evaluation, TeX and erased syntax. No check, local value or claim carries hand-written display
text. The remaining free text is *annotation*: the printed type of a message, the name of an
opaque honest function such as `\mathsf{proj}`, a round's error, and a literal's printed form. The
figure prints annotation in gray, and the JSON marks it `"checked": false`.

**Why.** A reviewer who trusts two small interpreters (one case per constructor) trusts every
figure, instead of comparing each string with its term. PHOAS keeps the syntax printable and
inspectable, lets authors write binders as Lean lambdas, and needs no universe of types. A formula
is parametric in its variable carrier, so it cannot behave differently when printed and when
evaluated.

**Rejected.** A value paired with a string at each node cannot print a binder's body without a
value. A deep embedding with named variables and a dynamic environment needs a type universe that
covers `R⦃≤ d⦄[X]`, `Fin N → R` and the rest. Proving the TeX correct has no meaning, since TeX
has no semantics in Lean.

**Evidence.** `Fml.tex_eq` proves that printing a formula and printing its erased syntax agree.
`Fml.erase_toFO` proves that the erased syntax is the erasure of the typed first-order form.
`#guard` tests fix the printed text of every example's checks. The generated sum-check check is
`\sum_{a \in D} g_{i}(a) = c_{i}`.

**Gap.** That the exported tree evaluates like the formula (`FO.eval (toFO φ) = some (Fml.eval φ)`)
is tested on the examples' formulas, not proved in general. A general proof relates a PHOAS term
at two carriers and needs parametricity, which Lean cannot prove internally.

### 2. Input oracles could not be queried

**Decision.** A spec declares its input bundle `In`, and `input` gives the description a named
handle on an input oracle. The verifier routes input queries to the input part of `pathBundle`
and message queries to the message part, as `pathLift` does. The honest prover answers input
queries from the input data.

**Why.** `OracleVerifier.decide` already has query access to the inputs. Ignoring them forced FRI
to resend `f₀` and kept Spartan from reading its index oracles.

**Evidence.** Sum-check reads `p`, FRI reads `f₀`, and Spartan reads `Ã`, `B̃`, `C̃` as input
oracles. `Spec.decide_eq_verdict` covers the routing for every spec.

### 3. Round shape had to be uniform, and the kit's round was one oracle plus one challenge

**Decision.** `rounds` takes a tree family, so round `i`'s tree may depend on `i`. The kit's round
is a block of messages followed by a challenge, with prefix and suffix blocks.

**Why.** Real protocols change message types per round. Every interactive proof the kit targets
alternates prover blocks and single challenges, and two consecutive challenges are one challenge
of the product type. One challenge per round therefore costs no generality for round-by-round
soundness.

**Evidence.** The FRI spec sends round `i`'s word on a domain of size `2^(k-i)`. The kit's FRI
commit phase has per-round message types and an empty block in round 0. `Kit/TwoMessage.lean` has
two messages per round and a plain suffix message.

### 4. Proof ergonomics

**Decision.** `Spec` is a structure, so `(branchingSpec R d D).Tr` works. The smart constructor
`Spec.mk` infers the tree and the skeleton. Accessors compute positions at elaboration time, so a
goal never contains a stuck label comparison. Tree agreement uses the tree family of `rounds`,
whose obligations hold by `rfl`. The final-state cast stays inside `roundsGo`.

**Why.** Computing positions while elaborating removes the stuck `if "g" = "g"` terms. Passing
the target tree family lines up the definitional unfolding with ArkLib's recursion, so neither
`smartUnfolding false` nor a cast is needed.

**Evidence.** No file sets `smartUnfolding`. `sumcheck_tree`, `spartan_tree`, `fri_tree` and
`branching_tree` hold by `rfl`.

**Gaps.** `simp` and `rw` do not see through the `Curry` encoding of formula arguments, so proofs
about a formula's value use small `rfl` lemmas at the exact hole list (`eval_round_value`,
`eval_round_check`) or `change`. Proofs step through the interpreters with
`erw [Desc.verdict.eq_N]`. Simp lemmas generated per constructor would fix both. This is stage 2
work.

### 5. Labels were global

**Decision.** Labels are paths of stage names, block names, round numbers and the label. A branch
component `m = v` enters case `v`. Inside a branch the accessor returns an `Option`, because the
transcript type after the branch message depends on the message. When moves in one context share
a base, the label adds the subscript: `tr⟦outer, v_B⟧`, `tr⟦"\\alpha_2"⟧`. With the base alone the
accessor reads the first such move.

**Why the subscript form.** Spartan's row values `v_A`, `v_B`, `v_C` and FRI's last folding
challenge share a base with other moves in their context, so a base alone cannot reach all of
them. Matching the subscript reuses the name the figure prints instead of adding a second label to
each move.

**Evidence.** In Spartan, `tr⟦outer, sumcheck, 0, g⟧` and `tr⟦inner, sumcheck, 0, g⟧` are
different moves, and `tr⟦outer, v_B⟧` and `tr⟦inner, "\\rho_C"⟧` read the second and third
moves of their kind, by `rfl`. In the branching example `tr⟦m = 2, sumcheck, 1, r⟧` is `some` on a transcript
whose message is 2 and `none` on one whose message is 1, both by `rfl`.

### 6. Figures could not show dependent shapes

**Decision.** The skeleton is a tree with stage, round and branch nodes. `branch` records one
sub-skeleton per case of a finite message type, and `branchOpaque` marks a shape-selecting message
of infinite type.

**Evidence.** In `Examples/Branching.lean` the prover sends `m : Fin 4` and an `m`-variable
sum-check follows. The JSON and the figures show the four cases.

### 7. Where the symbolic sum-check layer lives

**Decision.** In the spec layer. Claims are formulas with a denotation. Sum-check's stage claims
are `Σ_{x ∈ D^n} p(x) = c` and `p(r) = c_n`, and the soundness and completeness statements are
about the languages those formulas denote. Spartan's two stages share one named claim value, so
the outer stage's output claim and the inner stage's input claim are one term.

**Why.** With string claims, the claim-flow figure had no meaning Lean knew. With formula claims,
the figure's edges and the security statements come from one object, which is what "claims as
data" asks for.

**Evidence.** `sumcheckSpec_claimSound`, `sumcheckSpec_claimRBRSound`,
`sumcheckSpec_claimComplete`, `sumcheckSpec_contract`.

**Gap.** Stage contracts read the first stage's input claim and the last stage's output claim.
Contracts for the inner stages of a multi-stage spec, and their composition along a `StageChain`,
are stage 3 work.

### 8. Elaboration cost was unmeasured

**Decision.** `bench.sh` measures it and writes `out/bench.md`. Single runs on an Apple M4 with
24 GB and Lean 4.36.0:

| case | size | wall time |
|---|---|---|
| sum-check: tree by `rfl`, accessors | n = 8 / 32 / 128 | 2.21 s / 2.22 s / 2.30 s |
| sum-check: skeleton export | n = 8 / 128 | 2.21 s / 2.21 s |
| Spartan: tree, accessors, export | m = n = 4 / 8 | 2.29 s / 2.28 s |
| FRI: tree, accessors, export | k = 4 / 32 | 2.23 s / 2.36 s |

About 1 s of each row is importing the library. Cost does not grow with the protocol's size: the
tree agreement is `rfl` for every size, and the skeleton is computed without enumerating any
domain, because a domain stores its elements behind a function. One limit remains: the accessor at
round 127 of a 128-round sum-check exceeds Lean's default `maxRecDepth` of 512, and the bench file
raises the limit for that definition.

### Further gaps found while fixing the limitations

- **The two prototypes were disconnected.** The bridge (`sound_of_kit`) and its sum-check
  instance connect them.
- **Each protocol needed its own induction for agreement.** `Spec.decide_eq_verdict` and
  `Spec.verdict_isSome` hold for every spec. A protocol still compares the pure verdict with a
  hand-written verifier when one exists, by a round induction (`verdict_roundsGo`).

## What stays open

- **Soundness of the Spartan and FRI specs.** The kit proves FRI's commit phase, but the FRI spec
  groups a round as challenge then word, while the kit groups it as words then challenge. Relating
  them is a regrouping lemma. Spartan needs per-stage contracts and their composition.
- **FRI's commit-phase output language.** It is "the input is close or some fold fails", the bad
  event the query phase needs. Linking it to ArkLib's `FoldTrace.Safe` and `Fri.query_soundness`
  needs cast lemmas between the two ways of indexing subdomains.
- **Probabilistic completeness.** Completeness is proved in its deterministic form, and ArkLib's
  `completeness` in the classical model is not instantiated.
- **The general evaluation theorem for exported syntax** (item 1) and **simp support for formula
  arguments** (item 4).

## Why

**Readability.** Today's sum-check spreads one round over 12 files and 2,351 lines under
`ArkLib/ProofSystem/Sumcheck/`: the tree, the claim with a proof field, the honest message, the
prover fold and the verifier fold. Proofs reach moves by position (`tr.2.1`). The spec's round is
six lines in protocol order, and the whole specification with its claims is 11 more. Its figure,
claim-flow graph and timeline are generated from those lines.

**Modularity.** Protocol-specific mathematics is 8–45% of each security proof today. The rest is
recursion over `Cursor.Spine` (`foldPrefix` and about eight companion lemmas in `Indexed.lean`).
The kit does that recursion once, and sum-check's soundness through it is 118 lines instead of
317. The sum-check round argument, proved four times today (`Indexed.lean:117`,
`Spec/SingleRound.lean:560`, RingSwitching `RoundSecurity.lean:54`, Binius
`Steps/Fold.lean:850-890`), becomes one lemma in `Kit/ClaimReduction.lean`.

**The two belong together.** Rounds, stages, round-local checks and claims make a spec readable,
and the generic theorems induct over the same structure. The bridge shows this: the spec's rounds
are the kit's rounds, the round's check is the kit's step, and the stage claims are the soundness
statement's languages.

## Alternatives considered

- **A deep embedding of whole protocols with a denotation.** It would put a denotation between
  every proof and the protocol, and proofs would stop working on the core objects. The formula
  language is deep only where display and evaluation must agree.
- **Custom syntax first** (a `protocol … where` block, as in the old `Choreo.lean`). It gives worse
  error messages and must be maintained against the core. Notation comes after the combinators
  stabilize and stays optional.
- **Early rejection at a check.** It would change record D4. Placing a check next to its round is
  presentation, and the decision stays at the leaf.
- **Labels only in the exported skeleton.** Accessors and figures could then disagree. Labels in
  the type index are one source.
- **Constant-state `FreeM.replicate`** (record D5's plan). Sum-check's state has a challenge vector
  whose length is the round index, so the state type depends on the round.

## Consequences

- A ported protocol has a specification of a screen or two, and its figures, claim-flow graph and
  timeline are generated.
- A protocol whose rounds fit the kit's shape gets soundness on the claims its figure shows from a
  one-round obligation plus the round's algebra, through the bridge.
- Each hand-written form a spec replaces needs one agreement proof until the hand-written form is
  deleted.
- Record D5's iteration section changes: `rounds` and the kit certificate own dependent round
  state.
- Authors write formula arguments with `⟪…⟫` and formulas with `='`, `∑∈` and `ask`. This is the
  cost of generated display text.

**Acceptance tests** for each stage that moves the prototype into `ArkLib/`:

- Tree agreement by `rfl` with every hand-written tree a spec replaces.
- Honest-prover and verdict agreement for every size.
- Accessor tests by label path, including inside branches.
- No hand-written display text on checks, local values or claims; `#guard` tests on the printed
  text; the JSON parses and the TeX compiles with `cryptocode`.
- A soundness theorem through the kit whose statement equals the hand-written one (checked with
  `type_of%`), and a soundness theorem on the spec's own claims.
- No `cast`, `Fin.cast` or `Fin.vsum` in any spec, and no `smartUnfolding` option anywhere.
- The bench table at the protocol's realistic sizes.

## Order of work

| Stage | Content | Exit |
|---|---|---|
| 0 | This record and the prototype library | The maintainer approves this record |
| 1 | The kit (blocks, iteration theorem, passive iteration verifier, claim reduction) in `ArkLib/Interaction/`; sum-check soundness re-proved through it | The new proof replaces the spine recursion in `Indexed.lean`, and the legacy-equivalence theorems still hold |
| 2 | The formula language and the spec layer (descriptions, interpreters, generic lemmas, accessors, statement front end, exporter) for sum-check, with simp support for formula arguments | Sum-check's spec fits on one screen, its figure matches a paper figure line for line, and its soundness on its own claims goes through the bridge |
| 3 | Stage contracts for inner stages and their composition along `StageChain`; oracle-verifier composition theorems; Spartan ported as a spec of stages | Spartan's total error comes from the chain theorem with no manual sum |
| 4 | FRI (with the regrouping lemma and the link to `Fri.query_soundness`), then BinaryBasefold and RingSwitching, then WHIR | No `cast` or `Fin.vsum` in each spec, and each proof reuses the kit |
| 5 | Batching with placement; the Binary Jolt Book's first slice rendered from the skeleton | `spartan.outer` renders from the exported skeleton |

Fiat–Shamir and BCS on the new layer run in parallel from stage 1. They need stage 3's composition
theorems only for the end-to-end statement.
