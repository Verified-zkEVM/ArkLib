# Context lifting in the interaction layer

The legacy layer lifts a reduction into a larger context with `liftContext`
(`ArkLib/OracleReduction/LiftContext/`). The interaction layer now has the same operation in
`ArkLib/Interaction/LiftContext.lean` and `ArkLib/Interaction/Oracle/LiftContext.lean`. This
note records which legacy notions get a counterpart, how they fit the core's types, and which
legacy pieces are retired.

The core's design principles stay as they are:

- **Passive verifiers.** A lifted verifier still decides once, from the completed public
  transcript. Lifting changes only what the decision receives and what it returns.
- **Bundle queries happen only in the decision.** A lifted oracle verifier routes the inner
  decision's bundle queries through an `OracleMap`. Nothing else queries a bundle.
- **No new axioms or classes.** Lens conditions are ordinary `Prop`-valued structures, passed
  as explicit arguments.

## Lenses

| Legacy notion | Core counterpart | Shape |
|---|---|---|
| `Statement.Lens` | `StatementLens s OuterIn InnerIn OuterOut InnerOut` | `proj : OuterIn → InnerIn` and `lift : OuterIn → (p : Path s) → InnerOut p → OuterOut p` |
| `Witness.Lens` | `WitnessLens l s OuterIn OuterWit InnerWit OuterOut InnerOut` | `proj : OuterIn → OuterWit → InnerWit` and `lift : OuterIn → OuterWit → (tr : Transcript l s) → InnerOut tr → OuterOut tr` |
| `Context.Lens` | `ContextLens` | a statement lens and a witness lens |
| `OracleStatement.ExecutableLens` | `OracleStatementLens` | a statement lens, `projOracle : OuterIn → OracleMap outerInputs innerInputs`, and `liftOracle : OuterIn → (p : Path s) → OracleMap (outerInputs.sum (outputs p)) (outerOutputs p)` |
| `Witness.InvLens`, `Extractor.Lens` | `ExtractorLens` | a statement lens, `witOutProj` from outer to inner output witnesses, and `witInLift` from inner to outer input witnesses |

Three differences from the legacy shapes follow from the core's types.

1. **The statement lift is indexed by the shape path.** Core output statements have type
   `StmtOut p`, which may depend on the public shape path `p` of the run. The lift therefore
   takes the path. A verifier with one output type uses a constant family and ignores `p`.
2. **The witness lens acts on the prover's output family.** A core prover returns
   `Out tr`, a type indexed by the completed transcript, instead of a pair of output statement
   and witness. The witness lens maps `InnerOut tr` to `OuterOut tr`. A legacy context lens
   gives a core witness lens whose output family is the constant pair type
   (`ContextLens.ofLegacy`).
3. **Oracle lenses go through `OracleMap`.** The legacy executable lens has a materialization
   function and a query simulation for each direction, together with laws that they agree. An
   `OracleMap` is exactly such a pair with its law, so the core lens stores two oracle maps.
   The input map routes the inner decision's input queries to outer input queries. The output
   map builds the outer output oracles from the outer inputs and the inner outputs. Both maps
   see only the outer input statement, so they cannot depend on the inner decision's result.

### Alternatives considered

- **Bundled structures or pairs of functions.** The core already bundles `OracleMap`,
  `Verifier` and `OracleVerifier` as structures with named fields. The lenses follow that
  style. PolyFun's `PFunctor.Lens` is a pair of functions too, but its fiber map is indexed by
  positions, which does not match a lift that also takes the shape path. A named structure
  also keeps error messages readable.
- **Oracle lenses as a materialization and a simulation without a law.** This repeats the
  legacy split and would need a separate agreement proof at every use. `OracleMap` carries the
  law, and `OracleMap.withAmbient` already turns a map into a query router for decisions, as
  in oracle composition. The oracle lens reuses both.
- **Output oracle maps that read the inner output statement.** The core's `outputMap` sees
  the input statement, the path and the view, not the decision's result, because a decision
  may query ambient oracles that a pure map cannot. The lifted output map keeps this
  restriction. A lift that needs the inner output statement must recompute it from public
  data, as `OracleVerifier.OutputCompatibility` does for composition.
- **Classes for lens conditions.** Legacy uses the classes `Context.Lens.IsComplete`,
  `Statement.Lens.IsSound` and `Extractor.Lens.IsKnowledgeSound`. The core uses no class for a
  security property, so the conditions are structures passed explicitly. This also lets one
  lens carry different conditions for different problems without instance search.

## Lifting

- `Verifier.liftContext lens V` decides with `V` on `lens.proj stmt` and maps an accepted
  inner statement through `lens.lift stmt p`. It makes no other query.
- `Prover.liftContext proj wit P stmt w` runs `P (proj stmt) (wit.proj stmt w)` and maps its
  output through `wit.lift stmt w tr`. It takes only the statement projection, not a whole
  statement lens, because the prover never sees output statements. It is a `Strategy.mapOutput`, so every node slot is the inner
  prover's slot.
- `Reduction.liftContext` pairs the two.
- `OracleVerifier.liftContext lens V` runs the inner decision with its bundle queries routed
  through `(lens.projOracle stmt).par (OracleMap.id messages)` and maps an accepted inner
  statement through `lens.lift`. Its output map is `lens.liftOracle stmt p` after the fan-out
  of the outer inputs and the routed inner output map. `OracleMap.pair` is the new fan-out
  combinator.

### Run laws

The lifted run against any prover is a post-map of the inner run on the projected input:

```lean
(V.liftContext lens).run stmt prover =
  (fun obs => ⟨obs.1, obs.2.1, obs.2.2.map (lens.lift stmt obs.1.path)⟩) <$>
    V.run (lens.proj stmt) prover
```

This is `Verifier.liftContext_run`. The reduction law `Reduction.liftContext_runOutcome` also
maps the prover output through the witness lens. It follows from `Verifier.run_mapOutput`:
running a verifier against a prover with a mapped output maps the prover output of the outcome.
That lemma rests on `run_mapOutput_focal`, the same fact for `TwoParty.Lens.run` on a focal
strategy.

The oracle laws `OracleVerifier.liftContext_run` and `OracleVerifier.run_mapOutput` have the same
form, with the input data projected through `lens.projOracle` and the output data built by
`lens.liftOracle`. Their proofs use `OracleMap.simulate_withAmbient`.

These laws hold for every prover, not only for lifted ones. A soundness adversary against the
lifted verifier is therefore already an adversary against the inner verifier on the projected
statement. Legacy needs `frozen` provers to state this, because a legacy verifier receives its
statement through the prover's run. The core needs no counterpart.

## Lens conditions and transfers

Each condition is guarded by a compatibility predicate `compat stmt p t`: the inner decision
on the projected statement can return `t` at path `p` for some view. For a plain verifier this
is `Verifier.Compatible`. For an oracle verifier it is `OracleVerifier.Compatible`, which also
fixes the inner output data to the inner output map's value. The conditions take `compat` as a
parameter, so the plain and oracle transfers share them.

| Condition | Fields | Transfers |
|---|---|---|
| `StatementLens.IsSound` | `proj_sound`: an admissible false outer input projects to an admissible false inner input. `lift_sound`: on such an input, a compatible inner output whose lift is in the outer output language is in the inner output language. | soundness, round-by-round soundness |
| `ContextLens.IsComplete` | `proj_complete`: a valid outer input pair projects to a valid inner input pair. `lift_complete`: a compatible honest inner outcome lifts to an honest outer outcome. | completeness at the same error, so perfect completeness |
| `ExtractorLens.IsKnowledgeSound` | `proj_admissible`, `lift_knowledgeSound`: a valid inner input witness lifts to a valid outer one. `proj_knowledgeSound`: a compatible accepted outer output witness projects to a valid inner one, or every inner input witness lifts to a valid outer one. | round-by-round knowledge soundness |

The round-by-round transfers are first proved for the generic predicates
`Interaction.rbrSoundness` and `Interaction.rbrKnowledgeSoundness`, given a statement map and an
implication between the leaf acceptance predicates. The plain and oracle forms then supply that
implication from `validAcceptance_iff_support` and the lens condition.

- The lifted state function is true on an outer statement that is outside the admissible false
  region, and otherwise is the inner state function at the projected statement.
- The lifted knowledge state carries the completed transcript and the outer output witness
  beside the inner intermediate witness. Its predicate is the inner predicate, or the shortcut
  that every inner input witness lifts to a valid outer one. Root extraction applies
  `witInLift` to the inner root extraction. This raises the witness universe to
  `max uO uK`.

Both round-by-round transfers keep the inner draw and the inner error unchanged.

## Retired legacy pieces

- **`frozen` provers and their run lemmas.** The run laws above hold for every prover.
- **Classes for lens conditions.** Replaced by explicit structures.
- **`OracleStatement.Lens` as a `PFunctor.Lens` on materialized data.** The executable form
  with `OracleMap`s is the only oracle lens. Its materialized statement lens on
  `S × inputs.Data` is derived (`OracleStatementLens.toStatementLens`) and is what the oracle
  security statements use.
- **`Inhabited` assumptions** on inner output statements and witnesses. Legacy needs defaults
  because a legacy run can fail before the output exists. A core outcome always carries an
  `Option` verdict, so no default is needed.

## Legacy correspondence

`ArkLib/Interaction/Legacy/LiftContext.lean` relates the two layers for plain reductions.
`StatementLens.ofLegacy` and `ContextLens.ofLegacy` turn legacy lenses into core lenses with
constant output families. Then:

- `Legacy.embedVerifier_liftContext`: embedding a legacy verifier lifted along a legacy
  statement lens gives the core lift of the embedded verifier.
- `Legacy.embedProver_liftContext`: embedding a legacy prover lifted along a legacy context lens
  gives the core lift of the embedded prover. The proof goes round by round
  (`Legacy.roundSlot_liftContext`, `Legacy.embedFrom_liftContext`).
- `Legacy.embedReduction_liftContext`: the same for reductions.

All three are equalities of the embedded objects, so lifting then embedding equals embedding
then lifting on every run.

## Not covered

- **Straight-line knowledge soundness.** The core's `Security/Knowledge.lean` has its own
  extraction interface. A transfer needs an extractor lens on that interface and is left for a
  follow-up.
- **Oracle correspondence with legacy.** The oracle bridge in
  `Interaction/Legacy/OracleReduction.lean` embeds oracle verifiers on the oracle tree with
  its own output-oracle representations. Relating `OracleVerifier.liftContext` to legacy
  `OracleVerifier.liftContext` needs an `OracleMap` from a legacy `ExecutableLens`, built with
  `OracleMap.ofLegacySimulation`, and a commuting lemma for the embedded decision's query
  routing. It is left for a follow-up.
- **Output index families outside universe `u`.** `OracleVerifier.Output` requires the output
  oracle index family `J : Path s → Type u`, so `OracleStatementLens` fixes both output index
  families in universe `u`. Generalizing this is a change to the core's oracle verifier, not to
  the lens.
