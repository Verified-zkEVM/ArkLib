# Source and resource port table

This port table accounts for all 74 assertions in six old-layer test files. Each row links its
old-layer assertion by line. This branch ports four of the files. The logged-execution and routing
tests port the 13 assertions of `SourceRoutingExample` and `TerminalRun/Examples`. For those rows,
this table links the full entry in the
[logged-execution port table](port-logged-execution.md). A ported row links the exact Core client. Added checks supplement these rows.

The two approved premises are:

- **P1 (passive verifier):** verifiers send public-coin challenges only, and resource queries
  happen in the final decision. A challenge cannot be computed from an input or from a previously
  sent oracle.
- **P2 (fixed shape):** neither a challenge nor an oracle message selects the protocol's subtree.

Each row has one of four statuses:

- **ported:** the new tests check the same mathematical observation, after any representation
  change that the row or the sections below state.
- **excluded by P1** (or **P2**): the row states exactly which assertion P1 (or P2) excludes.
- **removed:** the row names a mechanism that no longer exists.
- **open:** the row names an interface that the parent branch is missing.

A row marked **ported in the logged-execution table** takes its status and exact target from the
linked section of that table. The logged-execution table splits SR1 into three entries. It ports
one and excludes two by P1. A narrower test never counts as a port of an old-layer assertion.

This table has 66 ported rows, 12 of them ported in the logged-execution table, and 7 removed
rows. SR1 is the split row described above. No other row is excluded, and no row is open.

## SourceExample

| Old-layer test | Contract | Status and evidence |
| --- | --- | --- |
| S1a [32][fs1a] | Dependent answers give 9 | ported: [test][ns1a] |
| S1b [33][fs1b] | Dependent answers give 12 | ported: [test][ns1b] |
| S2 [46][fs2] | Negation and finite wraparound | ported: [test][ns2] |
| S3 [54][fs3] | Hidden tags are unobservable | ported: [test][ns3] |
| S4 [58][fs4] | Tagged data really differs | ported: [test][ns4] |
| S5a [87][fs5a] | Shift after doubling | ported: [test][ns5a] |
| S5b [88][fs5b] | Double after shifting | ported: [test][ns5b] |
| S6a [91][fs6a] | Right injection reads right data | ported: [test][ns6a] |
| S6b [94][fs6b] | Left injection reads left data | ported: [test][ns6b] |
| S7 [98][fs7] | Constant renaming answers 5 | ported: [test][ns7] |
| S8 [101][fs8] | Tensor answer is a pair | ported: [test][ns8] |
| S9 [105][fs9] | Indexed function selection | ported: [test][ns9] |
| S10 [113][fs10] | Independent sum universes | ported: [test][ns10] |
| S11 [116][fs11] | Independent tensor universes | ported: [test][ns11] |
| S12 [119][fs12] | Response-only universe lift | ported: [test][ns12] |
| S13 [123][fs13] | Invertible heterogeneous routes | ported: [test][ns13] |
| S14 [127][fs14] | Unwrap response universe 2 | ported: [test][ns14] |
| S15 [131][fs15] | Rewrap response universe 2 | ported: [test][ns15] |

## ResourceExample

| Old-layer test | Contract | Status and evidence |
| --- | --- | --- |
| R1 [54][fr1] | Inhabited sparse guarantee | removed: the property-symbol language no longer exists |
| R2 [56][fr2] | Empty sparse guarantee language | removed: the property-symbol language no longer exists |
| R3 [66][fr3] | Disjoint named contexts | removed: separate names and name disjointness no longer exist |
| R4 [91][fr4] | Distinct carriers answer (3,4) | ported: [test][nr4] |
| R5 [93][fr5] | A context overlaps itself | removed: named-context union is no longer an API |
| R6 [105][fr6] | Both aliases answer (2,2) | ported: [test][nr6] |
| R7 [108][fr7] | Both aliases have one name | ported as query and data sharing: [test][nr7]; the name field is removed |
| R8 [109][fr8] | Alias indices are distinct | ported: [test][nr8] |
| R9 [112][fr9] | Aliased value is below 3 | ported as a numerical guarantee: [test][nr9] |
| R10 [117][fr10] | Zero fails bound zero | ported as a false numerical property: [test][nr10] |
| R11 [122][fr11] | Universal bound zero fails | ported as a numerical contradiction: [test][nr11] |
| R12 [130][fr12] | Different indices have equal answers | ported: [test][nr12] |
| R13 [133][fr13] | The two names differ | ported as distinct family indices: [test][nr13] |
| R14 [134][fr14] | The two owners differ | removed: resource owner metadata no longer exists |
| R15 [137][fr15] | No name-preserving inclusion | removed: no name-preserving reindex API exists |
| R16 [166][fr16] | Renaming transports carrier data | ported: [test][nr16] |
| R17 [175][fr17] | Renamed program answers (4,3) | ported: [test][nr17] |
| R18 [179][fr18] | Empty context needs no data | ported: [test][nr18] |
| R19 [184][fr19] | Sum interpretation answers (3,4) | ported: [test][nr19] |
| R20 [198][fr20] | Shared view answers (3,2) | ported: [test][nr20] |
| R21 [227][fr21] | Dependent query and response carriers | ported: [test][nr21] |
| R22a [253][fr22a] | Evaluate the refined polynomial at 3 | ported: [test][nr22a] |
| R22b [257][fr22b] | Evaluate the refined polynomial at 7 | ported: [test][nr22b] |
| R23 [261][fr23] | Actual degree is below 2 | ported as a carrier guarantee: [test][nr23] |
| R24 [265][fr24] | Degree < 0 is false | ported as a false numerical property: [test][nr24] |
| R25 [269][fr25] | The symbol 0 is not promised | removed: reified promise membership no longer exists |
| R26 [278][fr26] | Context universes | ported: [namedResources][nr26] and [verifier inputs][resourceRuns] |
| R27 [284][fr27] | View universe contract | ported: [viewResources][nr27] and [verifier inputs][resourceRuns] |

## RunSourcesExample

| Old-layer test | Contract | Status and evidence |
| --- | --- | --- |
| RS1 [49][frs1] | All three oracles answer (7,11,19) | ported: [test][nrs1] |
| RS2 [53][frs2] | Private coordinates do not affect answers | ported: [test][nrs2] |
| RS3 [60][frs3] | An impossible send has no oracle message | ported: [test][nrs3] |
| RS4 [129][frs4] | Append keeps both suffix shapes | ported for the shapes: [test][nrs4]; the conversion is removed |
| RS5 [143][frs5] | Append preserves node ownership | ported through the signature: [test][nrs5] |
| RS6a [153][frs6a] | The prefix choice is receiver-owned | ported through the signature: [test][nrs6a] |
| RS6b [157][frs6b] | Each suffix root is sender-owned | ported through the signature: [test][nrs6b] |
| RS7 [162][frs7] | Concrete split/append round trip | ported: [test][nrs7] |
| RS8 [169][frs8] | Splitting commutes with projection | ported: [test][nrs8] |
| RS9 [200][frs9] | Component handlers answer both branches | ported: [test][nrs9] |
| RS10 [209][frs10] | Combined handler gives the same answers | ported: [test][nrs10] |
| RS11 [221][frs11] | Hidden coordinates remain unobservable | ported: [test][nrs11] |

## SourceRoutingExample

| Old-layer test | Contract | Status and evidence |
| --- | --- | --- |
| SR1 [140][fsr1] | Composed result and ambient order | split in the logged-execution table, one entry ported and two excluded by P1: [entries][lsr] |
| SR2 [162][fsr2] | Exactly two raw queries; answer 18 | ported in the logged-execution table: [entries][lsr] |
| SR3 [167][fsr3] | The routing theorem accepts the client | ported in the logged-execution table: [entry][lsr] |
| SR4 [174][fsr4] | Routing theorem trust dependencies | ported in the logged-execution table: [entry][lsr] |

## TerminalRun/Examples

| Old-layer test | Contract | Status and evidence |
| --- | --- | --- |
| TR1 [57][ftr1] | Effects survive a fault | ported in the logged-execution table: [entry][ltr] |
| TR2 [60][ftr2] | Private output/query survive a fault | ported in the logged-execution table: [entry][ltr] |
| TR3a [66][ftr3a] | Fault label 17 survives closing | ported in the logged-execution table: [entry][ltr] |
| TR3b [68][ftr3b] | Fault label 23 survives closing | ported in the logged-execution table: [entry][ltr] |
| TR4 [71][ftr4] | Rejection keeps the query answering 19 | ported in the logged-execution table: [entry][ltr] |
| TR5a [77][ftr5a] | First run closes to 18 | ported in the logged-execution table: [entry][ltr] |
| TR5b [82][ftr5b] | Second run closes to 32 | ported in the logged-execution table: [entry][ltr] |
| TR6 [86][ftr6] | Erasure trust | ported in the logged-execution table: [entry][ltr] |
| TR7 [87][ftr7] | Closure trust | ported in the logged-execution table: [entry][ltr] |

## Virtual

| Old-layer test | Contract | Status and evidence |
| --- | --- | --- |
| V1 [32][fv1] | Toy simulation for every pure handler | ported: [test][nv1] |
| V2 [62][fv2] | Substitution answers 135 | ported: [test][nv2] |
| V3 [66][fv3] | Reindexing does not identify data | ported: [test][nv3] |

## Representation changes and removed mechanisms

Resource indices replace separate oracle names. A sum of families creates distinct resource
indices directly. It does not take the named-context `Disjoint` certificate that R3 and R5 test.
Reindexing may be non-injective and need not preserve external names, so the exclusion in R15 no
longer applies. Owner and origin metadata is absent, so R14's owner inequality has no
resource-level object. R7 keeps query and data sharing and does not claim equality of a removed
`name` field. R13's concrete inequality is the same `false ≠ true` on the two ported family
indices.

The sparse property-symbol languages in R1/R2, and promised-symbol membership in R25, are removed.
Carrier refinements express actual bounds. R9 keeps the bound for every aliased realization.
R10/R11 keep the false numerical bound and its universally quantified contradiction. R23/R24 keep
the true and false degree facts about the same polynomial. These numerical clients do not
reintroduce a property-symbol language or claim tests of its removed membership operations.

RS4 keeps the exact one-send/two-send shape equality. The conversion to a separate runtime tree is
removed. RS5/RS6 test a suffix that the receiver really selects, with PolyFun's general `rolePoly`
and `Node.position_appendEquiv`. They keep receiver ownership of the root and sender ownership of
either suffix root. Separate role decorations and their conversion casts are removed. The Core
oracle signature still erases challenge answers from the shape. The general signature clients do
not claim that an oracle-protocol receiver can select its next shape.

The [logged-execution port][ltr] of `TerminalRun/Examples` interprets the final decision with
labelled failures. Fault labels 17 and 23 remain distinct outcomes, and each differs from
rejection. Each keeps the private output, the history `[9, 0, 1, 2]` and the sent-oracle answer.
No TR row is removed.

This branch adds a cost check to the routing tests' export map in
[`SourceRoutingExample`][nsrc]. The exported query's implementation has worst-case cost two at unit
cost per resource query. By `OracleMap.withAmbient_worstCaseCost`, an exported query charged two
units and routed through the map then costs at most two unit-cost resource queries. The cost check
supplements SR2 and does not discharge an old-layer row.

V1 quantifies over every pure input handler, as the old-layer test does. `Resources.ofSpec`
uses arbitrary handlers as backing data, and `OracleMap.ofQuery` supplies the simulated output
behavior. The [parent legacy client][legacy] tests legacy materialized inputs under `simOracle2`.
It adds useful coverage, but it is only a narrower specialization. This table does not count it as
the port of V1, which quantifies over arbitrary handlers.

## Universe contracts

**SourceExample S10.** `Resources.sum` takes query universes `u`, `u'`, shared response universe
`v`, and data universes `w`, `w'`. Its result is
`Resources.{v, max u u', max w w'}`. Further tests assert the exact disjoint index carrier,
product data carrier and componentwise answer handler. The port ties no universe beyond the
old-layer sum's shared response universe.

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
pure answers. The universe canary keeps independent `u`, `v`, `v'` and `w`. Additional checks
assert that both directions preserve each backing datum.

**SourceExample S14 and S15.** Both concrete checks use universe instantiation `{0, 0, 0, 2}`
and close by `rfl`. Unwrapping the lifted answer gives `5`; rewrapping the original answer has
`.down = 5`. The natural-number family keeps its original backing data, and its query
`⟨true, ()⟩` selects the old-layer example's index `true`.

**ResourceExample R26, ported.** `namedResources` has
`Resources.{e, max s q, max s a}` with query carrier `((x : Index) × Query (name x))` and
data carrier `((x : Index) → Realization (name x))`. Response universe `e` and realization
universe `a` are independent. This is the identity-view specialization of `viewResources`.

**ResourceExample R27, ported.** `viewResources` has
`Resources.{e, max h q, max s a}`. Its query carrier is
`((x : Visible) × Query (name (select x)))`; its data carrier remains the whole original
context `((x : Index) → Realization (name x))`. The view index universe `h` is independent
of context universe `s`, query universe `q`, realization universe `a` and response universe `e`.
The [shared client][resourceRuns] runs both resource forms as verifier inputs using the same
unencoded context data. `namedVerifier` specializes `viewVerifier` at the identity selection.
The definitions occur once in `ResourceExample.lean`, which `UniverseCanary.lean` imports.
Neither P1 nor P2 excludes any part of these contracts.

## Remaining interface restrictions

[Implementation note 18](../interaction-rebuild/IMPLEMENTATION-NOTES.md) states:
“Its input query index and oracle-node query type must remain in `Type`.” This applies to
`OracleVerifier.runWithLog`, whose returned full log records resource queries. It does not
restrict R26/R27, which use general `Resources` as inputs to `OracleVerifier.run`.
`Resources.ofFamily` keeps the shared `OracleInterface` specialization, with its `ReaderM`
coupling. That specialization no longer restricts general verifier inputs. The shared interface
is unchanged. The source sum, tensor, lifting and raw-routing canaries also keep all their
old-layer universe instantiations.

## Open cost universes

[`OracleMap.withAmbient_worstCaseCost`][cost] has independent backing-data universes `dX`, `dY`.
Its ambient index, both resource-query indices, response/result types and cost carrier `ω` remain
in `Type`. This is an open restriction of the pinned VCVio cost API. It is separate from
`OracleInterface` and from the runner's requirement that returned values match its monad universe.
Protocol semantics do not force query indices and costs to universe zero.

The required changes belong in VCVio, pinned here at `fc54dd3d7691d6f5db7dc829e321a727f095bc2d`:

- Generalize `VCVio/OracleComp/QueryTracking/CostModel.lean`: the variables at line 64, `CostModel`
  at line 87, `costDist`, and `WorstCaseCostBound` at line 218. Query-index, response/result and
  cost universes must be explicit, with any necessary relation stated instead of fixing zero.
- Generalize the corresponding cost-writer helpers and their simulation/support laws.
- Generalize `CostModel/Simulation.lean`'s variables at line 33 and
  `WorstCaseCostBound.simulateQ` to those universes.
- Then generalize this branch's wrapper using the upstream theorem. It needs no separate cost
  semantics and no local proof of the upstream simulation law.

[cost]: ../../../ArkLib/Interaction/Core/Oracle/Cost.lean#L42

## Definition-site fixture transparency

The six remaining `@[reducible]` attributes are on interface definitions that this branch
introduces. Each constructs an `OracleInterface` class value. Removing its attribute produces
Lean's class-definition reducibility warning. These attributes set the definitions' own
transparency. This branch adds no local or global `attribute [...]` command that changes another
declaration, and no `respectTransparency` option. It modifies no declaration in the parent or a
dependency.

The thirteen family and protocol definitions in these clients use ordinary definition
transparency and carry no `@[instance_reducible]` attribute. The `functions` and `polynomials`
families use ordinary definition transparency as well. The exact remaining attributes are:

| File under `Core/Oracle/` | Attribute | Declarations |
| --- | --- | --- |
| `SourceExample` | `reducible` | `taggedInterface`, `pairInterface` |
| `ResourceExample` | `reducible` | `countInterface`, `mixedInterface`, `evaluation` |
| `RunSourcesExample` | `reducible` | `interface` |

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
[nr4]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L73
[fr5]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L93
[fr6]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L105
[nr6]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L86
[fr7]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L108
[nr7]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L91
[fr8]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L109
[nr8]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L96
[fr9]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L112
[nr9]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L234
[fr10]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L117
[nr10]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L239
[fr11]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L122
[nr11]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L242
[fr12]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L130
[nr12]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L250
[fr13]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L133
[nr13]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L254
[fr14]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L134
[fr15]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L137
[fr16]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L166
[nr16]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L109
[fr17]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L175
[nr17]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L120
[fr18]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L179
[nr18]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L129
[fr19]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L184
[nr19]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L137
[fr20]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L198
[nr20]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L164
[fr21]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L227
[nr21]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L191
[fr22a]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L253
[nr22a]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L212
[fr22b]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L257
[nr22b]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L218
[fr23]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L261
[nr23]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L230
[fr24]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L265
[nr24]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L258
[fr25]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L269
[fr26]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L278
[nr26]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L279
[fr27]: ../../../ArkLibTest/Interaction/Oracle/ResourceExample.lean#L284
[nr27]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L270
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
[fsr2]: ../../../ArkLibTest/Interaction/Oracle/SourceRoutingExample.lean#L162
[fsr3]: ../../../ArkLibTest/Interaction/Oracle/SourceRoutingExample.lean#L167
[fsr4]: ../../../ArkLibTest/Interaction/Oracle/SourceRoutingExample.lean#L174
[lsr]: port-logged-execution.md#sourceroutingexamplelean
[nsrc]: ../../../ArkLibTest/Interaction/Core/Oracle/SourceRoutingExample.lean#L33
[ftr1]: ../../../ArkLibTest/Interaction/Oracle/TerminalRun/Examples.lean#L57
[ftr2]: ../../../ArkLibTest/Interaction/Oracle/TerminalRun/Examples.lean#L60
[ftr3a]: ../../../ArkLibTest/Interaction/Oracle/TerminalRun/Examples.lean#L66
[ftr3b]: ../../../ArkLibTest/Interaction/Oracle/TerminalRun/Examples.lean#L68
[ftr4]: ../../../ArkLibTest/Interaction/Oracle/TerminalRun/Examples.lean#L71
[ftr5a]: ../../../ArkLibTest/Interaction/Oracle/TerminalRun/Examples.lean#L77
[ftr5b]: ../../../ArkLibTest/Interaction/Oracle/TerminalRun/Examples.lean#L82
[ftr6]: ../../../ArkLibTest/Interaction/Oracle/TerminalRun/Examples.lean#L86
[ftr7]: ../../../ArkLibTest/Interaction/Oracle/TerminalRun/Examples.lean#L87
[ltr]: port-logged-execution.md#terminalrunexampleslean
[fv1]: ../../../ArkLibTest/Interaction/Oracle/Virtual.lean#L32
[nv1]: ../../../ArkLibTest/Interaction/Core/Oracle/Virtual.lean#L37
[fv2]: ../../../ArkLibTest/Interaction/Oracle/Virtual.lean#L62
[nv2]: ../../../ArkLibTest/Interaction/Core/Oracle/Virtual.lean#L90
[fv3]: ../../../ArkLibTest/Interaction/Oracle/Virtual.lean#L66
[nv3]: ../../../ArkLibTest/Interaction/Core/Oracle/Virtual.lean#L98

[legacy]: ../../../ArkLibTest/Interaction/Core/Legacy/OracleReduction.lean#L107

[resourceRuns]: ../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean#L330
