# Oracle-bundle and oracle-node universe contracts

This port table records the universe assertions reviewed as F3 and F4 for PR #1492. It reads the
old-layer sources at `9829e83ced`. The ports import only the interaction Core APIs.
The R26/R27 acceptance client is
[`BundleFamilies.lean`](../../../ArkLibTest/Interaction/Core/Oracle/BundleFamilies.lean),
imported by `ArkLibTest/Interaction/Core/UniverseCanary.lean`. The latter keeps the oracle-node
query canary.

| Old-layer assertion | Status | Port and evidence |
| --- | --- | --- |
| R26: `Oracle/ResourceExample.lean:278`, whole named context with response universe `e` independent of realization universe `a` | ported | `namedBundle` has `OracleBundle.{e, max s q, max s a}` with exactly the named query and realization carriers. `namedVerifier` specializes `viewVerifier` at the identity view; their shared run example consumes both bundles without encoding the data. |
| R27: `Oracle/ResourceExample.lean:285`, visible named context keeping the whole context's data | ported | `viewBundle` has `OracleBundle.{e, max h q, max s a}`. Only the query indices follow the visible selection; data remains the whole named realization family. `viewVerifier` and the shared run example consume it directly. |
| `Oracle/TypeTree/DecorationExample.lean:27`, independent oracle message and query universes | ported | `OraclePos.{u, q}`, `oracleSig`, `OracleProtocol.{u, q}`, path bundles and append routing keep independent universes. `typeQueryProtocol` carries an actual `OracleInterface.{0, 1} Nat` node; `nodeQueryVerifier.run` queries its oracle message and returns `17` by `rfl`. |

These rows move from open to ported. Neither approved premise, P1 (passive verifier) or P2 (fixed
shape), excludes a universe contract. Implementation note 18 keeps a separate open requirement:
the parent branch is missing a logging interface that can return large bundle-query logs
through a small computation monad.
