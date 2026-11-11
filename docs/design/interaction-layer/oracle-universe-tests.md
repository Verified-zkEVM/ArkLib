# Oracle universe test dispositions

These rows supersede the earlier retirement of the frozen source and resource universe canaries.
The frozen files remain unchanged. Tests use the interaction layer's `Resources`, `OracleFamily`
and `OracleMap` APIs.

The source counterpart is
[`Core/Oracle/SourceExample.lean`](../../../ArkLibTest/Interaction/Core/Oracle/SourceExample.lean),
and the resource counterpart is
[`ResourceExample.lean`](../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean).
Both contain a `Universes` section.

| Frozen row | Frozen lines | Contract | Disposition |
| --- | --- | --- | --- |
| SourceExample S10 | 113–114 | Disjoint sum | Restored at all frozen universes |
| SourceExample S11 | 116–117 | Tensor | Blocked: resource tensor API missing |
| SourceExample S12 | 119–120 | Response lifting | Blocked: resource lifting API missing |
| SourceExample S13 | 123–124 | Raw routing equivalence | Blocked: raw routing API missing |
| SourceExample S14 | 127–128 | Unwrap raised answer | Blocked: lifting and routing APIs missing |
| SourceExample S15 | 131–132 | Rewrap answer | Blocked: lifting and routing APIs missing |
| ResourceExample R26 | 278–282 | Context interface | Restored with entry 18's data/response tie |
| ResourceExample R27 | 284–288 | View interface | Restored with entry 18's data/response tie |

## Restored contracts

**SourceExample S10.** `Resources.sum` takes query universes `u`, `u'`, shared response universe
`v`, and data universes `w`, `w'`. Its result is
`Resources.{v, max u u', max w w'}`. Further tests assert the exact disjoint index carrier,
product data carrier and componentwise answer handler. No universe is tied beyond the frozen
sum's shared response universe.

**ResourceExample R26.** Names, context indices and queries keep independent universes `i`, `s`
and `q`. The selected resources have queries in `max s q` and data in `max s a`. Tests check the
exact dependent query carrier and interpretation of arbitrary context data. The frozen response
universe `e` stays equal to realization universe `a` because of the unresolved interface dependency
in entry 18.

**ResourceExample R27.** Every view map from universe `h` to context universe `s` is allowed.
View queries have universe `max h q`; the input data stays indexed by the original context in
universe `max s a`. `OracleMap.embedding` selects that data, and a universally quantified answer
equality checks the selected index. Universes `i`, `s`, `h` and `q` stay independent. Only `e = a`
remains tied, for the same interface dependency.

## Remaining dependencies

[Implementation note 18](../interaction-rebuild/IMPLEMENTATION-NOTES.md)
records that `OracleInterface` ties realization data and responses through `ReaderM`. This is the
only restriction used in the restored resource canaries. The logged-runner restriction does not
apply to these tests.

**SourceExample S11** requires a tensor with independent query universes `u`, `u'`, response
universes `v`, `v'` and data universes `w`, `w'`. The base has no resource tensor combining these
response universes. The concrete pair-interface example does not close this row.

**SourceExample S12** requires lifting responses from `v` to `max v v'` while preserving query
universe `u` and data universe `w`. The base has no resource response-lifting operation.

**SourceExample S13** requires reversible raw routing between response universes `v` and
`max v v'`, preserving the backing data. `OracleMap` has one shared response universe; the base
has no raw resource-routing equivalence. Instantiating both sides at the same response universe
would narrow the frozen pure-routing contract.

**SourceExample S14 and S15** require unwrapping and rewrapping an answer lifted from response
universe `0` to `2`, with the resulting scalar equal to `5`. They depend on response lifting and
both raw routes. No homogeneous replacement is counted.

These rows remain open dependencies, rather than accepted universe departures. They require an
owner-level API on the base and are not implemented as test-local substitutes.
