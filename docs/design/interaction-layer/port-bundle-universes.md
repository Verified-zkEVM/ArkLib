# Oracle-bundle and oracle-node universe contracts

This port table records the universe assertions reviewed as F3 and F4 for PR #1492. It reads the
old-layer sources at `9829e83ced`. The ports import only the interaction Core APIs.
The R26/R27 acceptance client is
[`BundleFamilies.lean`](../../../ArkLibTest/Interaction/Oracle/BundleFamilies.lean).
`ArkLibTest/Interaction/UniverseCanary.lean` keeps the separate oracle-node protocol canary.

| Old-layer assertion | Status | Port and evidence |
| --- | --- | --- |
| R26: `Oracle/ResourceExample.lean:278`, whole named context with response universe `e` independent of realization universe `a` | retired | The universe policy adopted in #1580 puts all bundle data in `Type`, and step 4 removed the independent bundle universes. `BundleFamilies.lean` still covers `namedBundle`, `namedVerifier` and their shared run in `Type`, with the exact named query and realization carriers. |
| R27: `Oracle/ResourceExample.lean:285`, visible named context keeping the whole context's data | retired | The universe policy adopted in #1580 puts all bundle data in `Type`, and step 4 removed the independent bundle universes. `BundleFamilies.lean` still covers `viewBundle`, `viewVerifier` and their shared run in `Type`. Only the query indices follow the visible selection, and the data remains the whole named realization family. |
| `Oracle/TypeTree/DecorationExample.lean:27`, independent oracle message and query universes | ported | `OraclePos.{u, q}`, `oracleSig`, `OracleProtocol.{u, q}` and the oracle-message families keep independent universes. `typeQueryProtocol` carries an actual `OracleInterface.{0, 1} Nat` node. Since step 3 of the D2 migration, the verifier APIs (`pathBundle` in a decision, `run` and append routing) pin the node-query universe at `0`, so the earlier `nodeQueryVerifier`, which ran a verifier against such a node, is removed. |

R26 and R27 retire because of the universe policy, not P1 (passive verifier) or P2 (fixed
shape). Step 4 also retired the full-log limit of implementation note 18, because every bundle
query index now lies in `Type`.
