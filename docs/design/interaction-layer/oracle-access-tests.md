# Independent-universe oracle access tests

The following dispositions replace the retired rows 17–18 for the frozen
`ArkLibTest/Interaction/Oracle/TypeTree/AccessExample.lean`. Their interaction layer
counterparts are the final two examples in
`ArkLibTest/Interaction/Core/Oracle/TypeTree/AccessExample.lean`.

| Frozen row | Interface | Initial and result | Disposition |
|---|---|---|---|
| 17 | `OracleInterface.{1, 0} Messages`, `Messages : Type 1` | `PFunctor.{0, 1}` | Restored |
| 18 | `OracleInterface.{0, 1} Messages`, `Messages : Type` | `PFunctor.{1, 0}` | Restored |

Each counterpart uses `Resources.sum` to extend the initial specification with the given
interface. Row 17 keeps queries in `Type 0` and responses in `Type 1`; row 18 keeps queries in
`Type 1` and responses in `Type 0`.

Both tests quantify over every initial polynomial and every interface at the frozen universe
instantiations. The prior data is an arbitrary query handler; the new data is the message itself.
The sum answers each query from its corresponding data. Neither test encodes or restricts the
message type, the query type, or the initial specification.

The data and response universes of `OracleInterface` remain equal, exactly as in the frozen
assertions. [Implementation note 18][universes]
explains this `ReaderM` restriction. No additional universe tie is needed for these two tests;
neither uses the full-log runner.

[universes]:
    ../interaction-rebuild/IMPLEMENTATION-NOTES.md#18-run-outputs-are-tied-to-the-monad-universe
