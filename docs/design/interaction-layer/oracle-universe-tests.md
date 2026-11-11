# Oracle universe test dispositions

These rows supersede the earlier retirement of the frozen source and resource universe canaries.
The frozen files remain unchanged. Tests use the interaction layer's `Resources`, `OracleFamily`
and `OracleMap` APIs, with tensor and response lifting in
[`ResourceOps.lean`](../../../ArkLib/Interaction/Core/Oracle/ResourceOps.lean).

The source counterpart is
[`Core/Oracle/SourceExample.lean`](../../../ArkLibTest/Interaction/Core/Oracle/SourceExample.lean),
and the resource counterpart is
[`ResourceExample.lean`](../../../ArkLibTest/Interaction/Core/Oracle/ResourceExample.lean).
Both contain a `Universes` section.

| Frozen row | Frozen lines | Contract | Disposition |
| --- | --- | --- | --- |
| SourceExample S10 | 113–114 | Disjoint sum | Restored at all frozen universes |
| SourceExample S11 | 116–117 | Tensor | Restored at all frozen universes |
| SourceExample S12 | 119–120 | Response lifting | Restored at all frozen universes |
| SourceExample S13 | 123–124 | Raw routing equivalence | Restored at all frozen universes |
| SourceExample S14 | 127–128 | Unwrap raised answer | Restored at response universes 0 and 2 |
| SourceExample S15 | 131–132 | Rewrap answer | Restored at response universes 0 and 2 |
| ResourceExample R26 | 278–282 | Context interface | Restored with entry 18's data/response tie |
| ResourceExample R27 | 284–288 | View interface | Restored with entry 18's data/response tie |

## Restored contracts

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

## Interface restriction

[Implementation note 18](../interaction-rebuild/IMPLEMENTATION-NOTES.md)
records that `OracleInterface` ties realization data and responses through `ReaderM`. This is the
only restriction used in the restored resource canaries. The logged-runner restriction does not
apply to these tests. The source sum, tensor, lifting and raw-routing canaries retain all their
frozen universe instantiations.
