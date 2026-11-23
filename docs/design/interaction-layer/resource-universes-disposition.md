# Resource and oracle-node universe contracts

This inventory records the universe assertions reviewed as F3 and F4 for PR #1492. Frozen
sources are read at `9829e83ced`; the replacements import only the interaction Core APIs.
The acceptance client is `ArkLibTest/Interaction/Core/UniverseCanary.lean`.

| Frozen assertion | Status | Replacement and evidence |
| --- | --- | --- |
| R26: `Oracle/ResourceExample.lean:278`, whole named context with response universe `e` independent of realization universe `a` | equivalent | `namedResources` has `Resources.{e, max s q, max s a}` with exactly the named query and realization carriers. `namedVerifier` and its run consume that resource without encoding its data. |
| R27: `Oracle/ResourceExample.lean:285`, visible named context retaining the whole context's data | equivalent | `viewResources` has `Resources.{e, max h q, max s a}`. Only the query indices follow the visible selection; data remains the whole named realization family. |
| `Oracle/TypeTree/DecorationExample.lean:27`, independent oracle message and query universes | equivalent | `OraclePos.{u, q}`, `oracleSig`, `OracleProtocol.{u, q}`, path resources and append routing retain independent universes. `typeQueryProtocol` carries an actual `OracleInterface.{0, 1} Nat` node; `nodeQueryVerifier.run` queries its payload and returns `17` by `rfl`. |

These rows move from unresolved to equivalent. Neither approved premise P1 (passivity) nor P2
(shape independence) retires a universe contract. Implementation note 18 retains the separate
unresolved requirement for a parent logging interface that can return large resource-query logs
through a small computation monad.
