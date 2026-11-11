# Source and resource port dispositions

This inventory accounts for all 74 assertions in the six frozen files ported by this branch.
Each row links its frozen assertion by line. A retained contract links the exact interaction-layer
client; parent-owned clients are identified below. Added checks supplement these rows.

**Retained** means the mathematical contract holds after the stated representation change.
**Partial** preserves only the listed dimensions and does not close the original contract.
**Retired** identifies a removed mechanism whose original contract has no corresponding API.
These statuses do not count a narrower test as equivalent to the frozen assertion.

## SourceExample

| Frozen test | Contract | Disposition |
| --- | --- | --- |
| S1a [32][fs1a] | Dependent answers give 9 | Retained: [test][ns1a] |
| S1b [33][fs1b] | Dependent answers give 12 | Retained: [test][ns1b] |
| S2 [46][fs2] | Negation and finite wraparound | Retained: [test][ns2] |
| S3 [54][fs3] | Hidden tags are unobservable | Retained: [test][ns3] |
| S4 [58][fs4] | Tagged data really differs | Retained: [test][ns4] |
| S5a [87][fs5a] | Shift after doubling | Retained: [test][ns5a] |
| S5b [88][fs5b] | Double after shifting | Retained: [test][ns5b] |
| S6a [91][fs6a] | Right injection reads right data | Retained: [test][ns6a] |
| S6b [94][fs6b] | Left injection reads left data | Retained: [test][ns6b] |
| S7 [98][fs7] | Constant renaming answers 5 | Retained: [test][ns7] |
| S8 [101][fs8] | Tensor answer is a pair | Retained: [test][ns8] |
| S9 [105][fs9] | Indexed function selection | Retained: [test][ns9] |
| S10 [113][fs10] | Independent sum universes | Retained: [test][ns10] |
| S11 [116][fs11] | Independent tensor universes | Retained: [test][ns11] |
| S12 [119][fs12] | Response-only universe lift | Retained: [test][ns12] |
| S13 [123][fs13] | Invertible heterogeneous routes | Retained: [test][ns13] |
| S14 [127][fs14] | Unwrap response universe 2 | Retained: [test][ns14] |
| S15 [131][fs15] | Rewrap response universe 2 | Retained: [test][ns15] |

## ResourceExample

| Frozen test | Contract | Disposition |
| --- | --- | --- |
| R1 [54][fr1] | Inhabited sparse guarantee | Retired: property-symbol language removed |
| R2 [56][fr2] | Empty sparse guarantee language | Retired: property-symbol language removed |
| R3 [66][fr3] | Disjoint named contexts | Retired: no separate names or name disjointness |
| R4 [91][fr4] | Distinct carriers answer (3,4) | Retained: [test][nr4] |
| R5 [93][fr5] | A context overlaps itself | Retired: named-context union is no longer an API |
| R6 [105][fr6] | Both aliases answer (2,2) | Retained: [test][nr6] |
| R7 [108][fr7] | Both aliases have one name | Name field retired; retained sharing: [test][nr7] |
| R8 [109][fr8] | Alias indices are distinct | Retained: [test][nr8] |
| R9 [112][fr9] | Aliased value is below 3 | Retained numerical guarantee: [test][nr9] |
| R10 [117][fr10] | Zero fails bound zero | Retained numerical false property: [test][nr10] |
| R11 [122][fr11] | Universal bound zero fails | Retained numerical contradiction: [test][nr11] |
| R12 [130][fr12] | Different indices have equal answers | Retained: [test][nr12] |
| R13 [133][fr13] | The two names differ | Retained as distinct family indices: [test][nr13] |
| R14 [134][fr14] | The two owners differ | Retired: resource owner metadata removed |
| R15 [137][fr15] | No name-preserving inclusion | Retired: no name-preserving reindex API |
| R16 [166][fr16] | Renaming transports carrier data | Retained: [test][nr16] |
| R17 [175][fr17] | Renamed program answers (4,3) | Retained: [test][nr17] |
| R18 [179][fr18] | Empty context needs no data | Retained: [test][nr18] |
| R19 [184][fr19] | Sum interpretation answers (3,4) | Retained: [test][nr19] |
| R20 [198][fr20] | Shared view answers (3,2) | Retained: [test][nr20] |
| R21 [227][fr21] | Dependent query and response carriers | Retained: [test][nr21] |
| R22a [253][fr22a] | Evaluate the refined polynomial at 3 | Retained: [test][nr22a] |
| R22b [257][fr22b] | Evaluate the refined polynomial at 7 | Retained: [test][nr22b] |
| R23 [261][fr23] | Actual degree is below 2 | Retained carrier guarantee: [test][nr23] |
| R24 [265][fr24] | Degree < 0 is false | Retained numerical false property: [test][nr24] |
| R25 [269][fr25] | The symbol 0 is not promised | Retired: reified promise membership removed |
| R26 [278][fr26] | Context universes | Partial: [test][nr26]; response universe unresolved |
| R27 [284][fr27] | View universe contract | Partial: [test][nr27]; response universe unresolved |

## RunSourcesExample

| Frozen test | Contract | Disposition |
| --- | --- | --- |
| RS1 [49][frs1] | All three slots answer (7,11,19) | Retained: [test][nrs1] |
| RS2 [53][frs2] | Private coordinates do not affect answers | Retained: [test][nrs2] |
| RS3 [60][frs3] | An impossible send has no payload | Retained: [test][nrs3] |
| RS4 [129][frs4] | Append keeps both suffix shapes | Shapes: [test][nrs4]; conversion retired |
| RS5 [143][frs5] | Append preserves node ownership | Retained via signature: [test][nrs5] |
| RS6a [153][frs6a] | The prefix choice is receiver-owned | Retained via signature: [test][nrs6a] |
| RS6b [157][frs6b] | Each suffix root is sender-owned | Retained via signature: [test][nrs6b] |
| RS7 [162][frs7] | Concrete split/append round trip | Retained: [test][nrs7] |
| RS8 [169][frs8] | Splitting commutes with projection | Retained: [test][nrs8] |
| RS9 [200][frs9] | Component handlers answer both branches | Retained: [test][nrs9] |
| RS10 [209][frs10] | Combined handler gives the same answers | Retained: [test][nrs10] |
| RS11 [221][frs11] | Hidden coordinates remain unobservable | Retained: [test][nrs11] |

## SourceRoutingExample

| Frozen test | Contract | Disposition |
| --- | --- | --- |
| SR1 [140][fsr1] | Composed result and ambient order | Partial passive replacement: [test][nsr1] |
| SR2 [162][fsr2] | Exactly two raw queries; answer 18 | Retained: [test][nsr2] |
| SR3 [167][fsr3] | The routing theorem accepts the client | Retained API acceptance: [test][nsr3] |
| SR4 [174][fsr4] | Routing theorem trust dependencies | Retained: [test][nsr4] |

## TerminalRun/Examples

| Frozen test | Contract | Disposition |
| --- | --- | --- |
| TR1 [57][ftr1] | Effects survive failure | Partial: [test][ntr1]; fault outcome retired |
| TR2 [60][ftr2] | Private output/query survive | Partial: [test][ntr2]; fault outcome retired |
| TR3a [66][ftr3a] | Fault label 17 survives closing | Retired: no fault-label outcome |
| TR3b [68][ftr3b] | Fault label 23 survives closing | Retired: no fault-label outcome |
| TR4 [71][ftr4] | Rejection keeps the query answering 19 | Retained rejection/log: [test][ntr4] |
| TR5a [77][ftr5a] | First run closes to 18 | Retained: [test][ntr5a] |
| TR5b [82][ftr5b] | Second run closes to 32 | Retained: [test][ntr5b] |
| TR6 [86][ftr6] | Erasure trust | Logging-erasure trust replacement: [test][ntr6] |
| TR7 [87][ftr7] | Closure trust | Runner closure trust replacement: [test][ntr7] |

## Virtual

| Frozen test | Contract | Disposition |
| --- | --- | --- |
| V1 [32][fv1] | Toy simulation for every pure handler | Retained: [test][nv1] |
| V2 [62][fv2] | Substitution answers 135 | Retained: [test][nv2] |
| V3 [66][fv3] | Reindexing does not identify data | Retained: [test][nv3] |

## Representation changes and retired mechanisms

Resource indices replace separate oracle names. A sum of families creates distinct slots directly;
it does not take the named-context `Disjoint` certificate tested by R3 and R5. Reindexing may be
non-injective and requires no preservation of external names, so the exclusion in R15 no longer
applies. Owner/origin metadata is absent, so R14's owner inequality has no resource-level object.
R7 retains query and data sharing, rather than claiming equality of a removed `name` field.
R13's concrete inequality is the same `false ≠ true` on the two retained family indices.

The sparse property-symbol languages in R1/R2, and promised-symbol membership in R25, are removed.
Carrier refinements express actual bounds. R9 keeps the bound for every aliased realization;
R10/R11 keep the false numerical bound and its universally quantified contradiction. R23/R24
keep the true and false degree facts about the same polynomial. These numerical clients do not
reintroduce a property-symbol language or claim tests of its removed membership operations.

RS4 retains the exact one-send/two-send shape equality; conversion to a separate runtime tree is
removed. RS5/RS6 test a genuinely receiver-selected suffix with PolyFun's general `rolePoly`,
using `Node.position_appendEquiv`. They retain receiver ownership of the root and sender ownership
of either suffix root. Separate role decorations and their conversion casts are removed. The
interaction core's oracle signature still erases challenge answers from shape; the general
signature clients do not claim an oracle-protocol receiver can select its next shape.

The SR1 replacement is the parent-owned `RoutingTests` client, also used by SR3/SR4. Its result is
`(secret + 23 + 50, some ((20, 23), 23), [1, 20, 50, 10, 30, 40, 60])`, rather than the frozen
`(secret + 23 + 50, some (23, 23), [1, 10, 20, 30, 40, 50, 60])`. Decisions run after the prover,
and the suffix challenge is sampled rather than computed from an export. This is a partial
passive replacement. The active verifier's receive-time effects and export-dependent challenge
are retired mechanisms; this row does not claim the original execution equality.

TR1/TR2/TR4 and TR6 link parent-owned `LoggedExecutionTests`. TR1/TR2 preserve private output,
query history `[9, 0, 1, 2]` and the sent-resource answer 11, while faults become rejection.
TR3a/TR3b's distinct fault labels are retired; `Option` decisions do not distinguish them.
TR4 retains rejection and the sent-resource answer 19. A source-only log is represented by the
resource entries of the decision log, which also records ambient queries in order. TR6's separate
terminal wrapper is gone; its replacement checks the logging-erasure declarations. TR7's
`closed_of_ofOption` wrapper is gone; the new guard checks `OracleVerifier.run`, whose accepted
result already materializes output data. These are trust-policy replacements, not claims that
the old wrapper theorems still exist.

V1 now quantifies over every pure input handler, as the frozen test does. `Resources.ofSpec`
uses arbitrary handlers as backing data, and `OracleMap.ofQuery` supplies the simulated output
behavior. The [parent legacy client][legacy] tests legacy materialized
inputs under `simOracle2`; it is useful additional coverage but only a narrower specialization,
and is not counted as the arbitrary-handler V1 replacement.

## Universe contracts

**SourceExample S10.** `Resources.sum` takes query universes `u`, `u'`, shared response universe
`v`, and data universes `w`, `w'`. Its result is
`Resources.{v, max u u', max w w'}`. Further tests assert the exact disjoint index carrier,
product data carrier and componentwise answer handler. No universe is tied beyond the frozen
sum's shared response universe.

**SourceExample S11.** `Resources.tensor` pairs the queries, responses and backing data. The
query universes `u`, `u'`, response universes `v`, `v'` and data universes `w`, `w'` remain
independent. Its result is `Resources.{max v v', max u u', max w w'}`. The tests also check the
exact product query and backing-data carriers.

**SourceExample S12.** `Resources.liftResponse` raises responses from `v` to `max v v'` with
`ULift`, preserving query universe `u`, data universe `w`, and both original carriers. This is
the response-lifting contract itself.

**SourceExample S13.** `ResourceEquiv.liftResponse` gives coherent raw maps between the original
resource and its lifted responses. Both composites are identity resource maps, including their
query, response and backing-data maps. The general pullback round-trip laws apply to arbitrary
pure answers. The universe canary retains independent `u`, `v`, `v'` and `w`; additional checks
assert that both directions preserve each backing datum.

**SourceExample S14 and S15.** Both concrete checks use universe instantiation `{0, 0, 0, 2}`
and close by `rfl`. Unwrapping the lifted answer gives `5`; rewrapping the original answer has
`.down = 5`. The natural-number family retains its original backing data, and its query
`⟨true, ()⟩` selects the frozen example's index `true`.

**ResourceExample R26, partial.** Names, context indices and queries keep independent universes
`i`, `s`
and `q`. The selected resources have queries in `max s q` and data in `max s a`. Tests check the
exact dependent query carrier and interpretation of arbitrary context data. The frozen response
universe `e` stays equal to realization universe `a` because of the unresolved interface dependency
in entry 18.

**ResourceExample R27, partial.** Every view map from universe `h` to context universe `s` is
allowed.
View queries have universe `max h q`; the input data stays indexed by the original context in
universe `max s a`. `OracleMap.embedding` selects that data, and a universally quantified answer
equality checks the selected index. Universes `i`, `s`, `h` and `q` stay independent. Only `e = a`
remains tied, for the same interface dependency.

## Interface restriction

[Implementation note 18](../interaction-rebuild/IMPLEMENTATION-NOTES.md)
records that `OracleInterface` ties realization data and responses through `ReaderM`. This is the
unresolved dimension of the partial resource canaries. The logged-runner restriction does not
apply to these tests. The source sum, tensor, lifting and raw-routing canaries retain all their
frozen universe instantiations.

The concrete owner change for R26/R27 is to separate realization universe `a` and response
universe `e` in `ArkLib/OracleReduction/OracleInterface.lean`. Its `toOC` must use a reader on
`Type e`, such as `(α : Type e) → Message → α`, instead of the pinned `ReaderM Message` tied to
`a`. `OracleFamily` in `ArkLib/Relation/Basic.lean`, and then `Resources.ofFamily`, must expose
that separate response parameter. Until those owner changes land, R26/R27 remain partial.

## Unresolved cost universes

[`OracleMap.withAmbient_worstCaseCost`][cost] has independent backing-data universes `dX`, `dY`.
Its ambient index, both resource-query indices, response/result types and cost carrier `ω` remain
in `Type`. This is an unresolved restriction of the pinned VCVio cost API, separate from
`OracleInterface` and from the runner's requirement that returned values match its monad universe.
Query indices and costs are not forced to universe zero by protocol semantics.

The owner changes belong in VCVio, pinned here at `fc54dd3d7691d6f5db7dc829e321a727f095bc2d`:

- Generalize `VCVio/OracleComp/QueryTracking/CostModel.lean`: the variables at line 64, `CostModel`
  at line 87, `costDist`, and `WorstCaseCostBound` at line 218. Query-index, response/result and
  cost universes must be explicit, with any necessary relation stated instead of fixing zero.
- Generalize the corresponding cost-writer helpers and their simulation/support laws.
- Generalize `CostModel/Simulation.lean`'s variables at line 33 and
  `WorstCaseCostBound.simulateQ` to those universes.
- Then generalize this branch's wrapper using the upstream theorem; no separate cost semantics
  or local proof of the upstream simulation law is needed.

[cost]: ../../../ArkLib/Interaction/Core/Oracle/Cost.lean#L42

## Definition-site fixture transparency

All 27 retained attributes set the transparency of declarations introduced by this branch.
There are no added local/global `attribute [...]` commands changing another declaration, and no
`respectTransparency` options. No declaration in the parent or a dependency is modified.

The eight `@[reducible]` interface fixtures expose their query and dependent response carriers
while elaborating explicitly typed queries. The thirteen `@[instance_reducible]` family fixtures
expose selected interfaces while resolving query, answer and arithmetic instances. The six
`@[instance_reducible]` protocol fixtures expose constructor shapes for transcript, payload,
challenge and view types. These are definition-site choices, like `abbrev`, under the corrected
review rule. The `functions` and `polynomials` families use ordinary definition transparency;
their previous attributes were unnecessary. The exact retained declarations are:

| File under `Core/Oracle/` | Attribute | Declarations |
| --- | --- | --- |
| `SourceExample` | `reducible` | `taggedInterface`, `pairInterface` |
| `SourceExample` | `instance_reducible` | `dependent`, `tagged`, `numbers` |
| `ResourceExample` | `reducible` | `countInterface`, `mixedInterface`, `evaluation` |
| `ResourceExample` | `instance_reducible` | `model`, `mixedModel` |
| `RunSourcesExample` | `reducible` | `interface` |
| `RunSourcesExample` | `instance_reducible` | `inputs`, `tree`, `impossible` |
| `RunSourcesExample` | `instance_reducible` | `firstTree`, `secondTree` |
| `SourceRoutingExample` | `reducible` | `firstInterface` |
| `SourceRoutingExample` | `instance_reducible` | `inputs`, `firstProtocol`, `exported` |
| `TerminalRun/Examples` | `reducible` | `firstInterface` |
| `TerminalRun/Examples` | `instance_reducible` | `inputs`, `output`, `protocol` |
| `Virtual` | `instance_reducible` | `scalarFamily`, `source`, `suffix` |

## Assertion links

[fs1a]: ../../../ArkLibTest/Interaction/Oracle/SourceExample.lean#L32
[ns1a]: ../../../ArkLibTest/Interaction/Core/Oracle/SourceExample.lean#L47
[fs1b]: ../../../ArkLibTest/Interaction/Oracle/SourceExample.lean#L33
[ns1b]: ../../../ArkLibTest/Interaction/Core/Oracle/SourceExample.lean#L48
[fs2]: ../../../ArkLibTest/Interaction/Oracle/SourceExample.lean#L46
[ns2]: ../../../ArkLibTest/Interaction/Core/Oracle/SourceExample.lean#L68
[fs3]: ../../../ArkLibTest/Interaction/Oracle/SourceExample.lean#L54
[ns3]: ../../../ArkLibTest/Interaction/Core/Oracle/SourceExample.lean#L91
[fs4]: ../../../ArkLibTest/Interaction/Oracle/SourceExample.lean#L58
[ns4]: ../../../ArkLibTest/Interaction/Core/Oracle/SourceExample.lean#L97
[fs5a]: ../../../ArkLibTest/Interaction/Oracle/SourceExample.lean#L87
[ns5a]: ../../../ArkLibTest/Interaction/Core/Oracle/SourceExample.lean#L138
[fs5b]: ../../../ArkLibTest/Interaction/Oracle/SourceExample.lean#L88
[ns5b]: ../../../ArkLibTest/Interaction/Core/Oracle/SourceExample.lean#L140
[fs6a]: ../../../ArkLibTest/Interaction/Oracle/SourceExample.lean#L91
[ns6a]: ../../../ArkLibTest/Interaction/Core/Oracle/SourceExample.lean#L152
[fs6b]: ../../../ArkLibTest/Interaction/Oracle/SourceExample.lean#L94
[ns6b]: ../../../ArkLibTest/Interaction/Core/Oracle/SourceExample.lean#L156
[fs7]: ../../../ArkLibTest/Interaction/Oracle/SourceExample.lean#L98
[ns7]: ../../../ArkLibTest/Interaction/Core/Oracle/SourceExample.lean#L163
[fs8]: ../../../ArkLibTest/Interaction/Oracle/SourceExample.lean#L101
[ns8]: ../../../ArkLibTest/Interaction/Core/Oracle/SourceExample.lean#L188
[fs9]: ../../../ArkLibTest/Interaction/Oracle/SourceExample.lean#L105
[ns9]: ../../../ArkLibTest/Interaction/Core/Oracle/SourceExample.lean#L197
[fs10]: ../../../ArkLibTest/Interaction/Oracle/SourceExample.lean#L113
[ns10]: ../../../ArkLibTest/Interaction/Core/Oracle/SourceExample.lean#L205
[fs11]: ../../../ArkLibTest/Interaction/Oracle/SourceExample.lean#L116
[ns11]: ../../../ArkLibTest/Interaction/Core/Oracle/SourceExample.lean#L222
[fs12]: ../../../ArkLibTest/Interaction/Oracle/SourceExample.lean#L119
[ns12]: ../../../ArkLibTest/Interaction/Core/Oracle/SourceExample.lean#L235
[fs13]: ../../../ArkLibTest/Interaction/Oracle/SourceExample.lean#L123
[ns13]: ../../../ArkLibTest/Interaction/Core/Oracle/SourceExample.lean#L240
[fs14]: ../../../ArkLibTest/Interaction/Oracle/SourceExample.lean#L127
[ns14]: ../../../ArkLibTest/Interaction/Core/Oracle/SourceExample.lean#L253
[fs15]: ../../../ArkLibTest/Interaction/Oracle/SourceExample.lean#L131
[ns15]: ../../../ArkLibTest/Interaction/Core/Oracle/SourceExample.lean#L259
[fr1]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L54
[fr2]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L56
[fr3]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L66
[fr4]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L91
[nr4]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L70
[fr5]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L93
[fr6]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L105
[nr6]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L83
[fr7]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L108
[nr7]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L88
[fr8]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L109
[nr8]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L93
[fr9]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L112
[nr9]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L231
[fr10]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L117
[nr10]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L236
[fr11]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L122
[nr11]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L239
[fr12]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L130
[nr12]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L247
[fr13]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L133
[nr13]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L251
[fr14]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L134
[fr15]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L137
[fr16]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L166
[nr16]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L106
[fr17]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L175
[nr17]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L117
[fr18]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L179
[nr18]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L126
[fr19]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L184
[nr19]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L134
[fr20]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L198
[nr20]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L161
[fr21]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L227
[nr21]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L188
[fr22a]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L253
[nr22a]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L209
[fr22b]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L257
[nr22b]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L215
[fr23]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L261
[nr23]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L227
[fr24]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L265
[nr24]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L255
[fr25]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L269
[fr26]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L278
[nr26]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L265
[fr27]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L284
[nr27]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L282
[frs1]: ../../../ArkLibTest/Interaction/Oracle/RunSourcesExample.lean#L49
[nrs1]: ../../../ArkLibTest/Interaction/Core/Oracle/RunSourcesExample.lean#L61
[frs2]: ../../../ArkLibTest/Interaction/Oracle/RunSourcesExample.lean#L53
[nrs2]: ../../../ArkLibTest/Interaction/Core/Oracle/RunSourcesExample.lean#L68
[frs3]: ../../../ArkLibTest/Interaction/Oracle/RunSourcesExample.lean#L60
[nrs3]: ../../../ArkLibTest/Interaction/Core/Oracle/RunSourcesExample.lean#L86
[frs4]: ../../../ArkLibTest/Interaction/Oracle/RunSourcesExample.lean#L129
[nrs4]: ../../../ArkLibTest/Interaction/Core/Oracle/RunSourcesExample.lean#L132
[frs5]: ../../../ArkLibTest/Interaction/Oracle/RunSourcesExample.lean#L143
[nrs5]: ../../../ArkLibTest/Interaction/Core/Oracle/RunSourcesExample.lean#L278
[frs6a]: ../../../ArkLibTest/Interaction/Oracle/RunSourcesExample.lean#L153
[nrs6a]: ../../../ArkLibTest/Interaction/Core/Oracle/RunSourcesExample.lean#L293
[frs6b]: ../../../ArkLibTest/Interaction/Oracle/RunSourcesExample.lean#L157
[nrs6b]: ../../../ArkLibTest/Interaction/Core/Oracle/RunSourcesExample.lean#L297
[frs7]: ../../../ArkLibTest/Interaction/Oracle/RunSourcesExample.lean#L162
[nrs7]: ../../../ArkLibTest/Interaction/Core/Oracle/RunSourcesExample.lean#L144
[frs8]: ../../../ArkLibTest/Interaction/Oracle/RunSourcesExample.lean#L169
[nrs8]: ../../../ArkLibTest/Interaction/Core/Oracle/RunSourcesExample.lean#L153
[frs9]: ../../../ArkLibTest/Interaction/Oracle/RunSourcesExample.lean#L200
[nrs9]: ../../../ArkLibTest/Interaction/Core/Oracle/RunSourcesExample.lean#L192
[frs10]: ../../../ArkLibTest/Interaction/Oracle/RunSourcesExample.lean#L209
[nrs10]: ../../../ArkLibTest/Interaction/Core/Oracle/RunSourcesExample.lean#L230
[frs11]: ../../../ArkLibTest/Interaction/Oracle/RunSourcesExample.lean#L221
[nrs11]: ../../../ArkLibTest/Interaction/Core/Oracle/RunSourcesExample.lean#L248
[fsr1]: ../../../ArkLibTest/Interaction/Oracle/SourceRoutingExample.lean#L140
[nsr1]: ../../../ArkLibTest/Interaction/Core/Oracle/Routing.lean#L161
[fsr2]: ../../../ArkLibTest/Interaction/Oracle/SourceRoutingExample.lean#L162
[nsr2]: ../../../ArkLibTest/Interaction/Core/Oracle/SourceRoutingExample.lean#L73
[fsr3]: ../../../ArkLibTest/Interaction/Oracle/SourceRoutingExample.lean#L167
[nsr3]: ../../../ArkLibTest/Interaction/Core/Oracle/Routing.lean#L178
[fsr4]: ../../../ArkLibTest/Interaction/Oracle/SourceRoutingExample.lean#L174
[nsr4]: ../../../ArkLibTest/Interaction/Core/Oracle/Routing.lean#L215
[ftr1]: ../../../ArkLibTest/Interaction/Oracle/TerminalRun/Examples.lean#L57
[ntr1]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L178
[ftr2]: ../../../ArkLibTest/Interaction/Oracle/TerminalRun/Examples.lean#L60
[ntr2]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L178
[ftr3a]: ../../../ArkLibTest/Interaction/Oracle/TerminalRun/Examples.lean#L66
[ftr3b]: ../../../ArkLibTest/Interaction/Oracle/TerminalRun/Examples.lean#L68
[ftr4]: ../../../ArkLibTest/Interaction/Oracle/TerminalRun/Examples.lean#L71
[ntr4]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L166
[ftr5a]: ../../../ArkLibTest/Interaction/Oracle/TerminalRun/Examples.lean#L77
[ntr5a]: ../../../ArkLibTest/Interaction/Core/Oracle/TerminalRun/Examples.lean#L93
[ftr5b]: ../../../ArkLibTest/Interaction/Oracle/TerminalRun/Examples.lean#L82
[ntr5b]: ../../../ArkLibTest/Interaction/Core/Oracle/TerminalRun/Examples.lean#L95
[ftr6]: ../../../ArkLibTest/Interaction/Oracle/TerminalRun/Examples.lean#L86
[ntr6]: ../../../ArkLibTest/Interaction/Core/Oracle/LoggedExecution.lean#L662
[ftr7]: ../../../ArkLibTest/Interaction/Oracle/TerminalRun/Examples.lean#L87
[ntr7]: ../../../ArkLibTest/Interaction/Core/Oracle/TerminalRun/Examples.lean#L109
[fv1]: ../../../ArkLibTest/Interaction/Oracle/Virtual.lean#L32
[nv1]: ../../../ArkLibTest/Interaction/Core/Oracle/Virtual.lean#L37
[fv2]: ../../../ArkLibTest/Interaction/Oracle/Virtual.lean#L62
[nv2]: ../../../ArkLibTest/Interaction/Core/Oracle/Virtual.lean#L90
[fv3]: ../../../ArkLibTest/Interaction/Oracle/Virtual.lean#L66
[nv3]: ../../../ArkLibTest/Interaction/Core/Oracle/Virtual.lean#L98

[legacy]: ../../../ArkLibTest/Interaction/Core/Legacy/OracleReduction.lean#L107
