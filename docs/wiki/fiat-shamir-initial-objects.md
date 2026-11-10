# Fiat–Shamir initial objects

## Separate initial object

`OracleReduction/FiatShamir/DuplexSponge/InitialObject.lean` defines a generic fixed-zero
runner for any injectively encoded, fixed-length initial object. The intended object is
`(session identifier, statement)`. The proof salt is a separate argument and is absorbed next.
The interactive protocol specification, challenge codecs and prover-message tuple are unchanged.
The session identifier is never inserted into a prover message.

`InitialObject/Execution.lean` proves that consecutive object and salt absorptions equal absorption
of their concatenated encodings, and that this setup encoding is injective. This is an execution
identity; it does not reclassify the object as a salt or a protocol message.

`rounds_eq_existing` proves equality with the existing round interpreter, retaining its final
state, cursors, transcript and queries. `initialize_pair` proves that product encoding is exactly
separate absorption of its two fields, followed by the salt. `InitialObject/QueryBounds.lean` reuses
existing operation and round bounds: setup costs at most `(objectSize + saltSize - 1) / rate`
permutation queries, followed by the unchanged protocol block bound.

All these definitions and theorems are generic over the alphabet, rate, capacity, object type,
encoding and protocol. Concrete suites belong in example clients under `ArkLibTest/`, outside
the core construction and proof.
Concrete implementation extraction, parsing and wire encodings remain separate obligations.

## Security boundary

The existing `DuplexSpongeFS.KeyLemma.discreteTVDist_dsfs_canonicalFS_le` remains proved and unchanged.
Its real experiment samples an independent uniform capacity-valued hash and a uniform
permutation. The new initial-object runner starts from a fixed public zero root instead.
Execution equality and injective encoding do not identify these two sampling laws.

Consequently this change establishes the initial-object model and operational/query bridges,
but does not yet prove the statistical-distance theorem for its fixed-zero experiment. That
requires a probability argument connecting fixed-root initialization to the existing hybrids,
including adversaries that query the permutation before selecting their session and statement.
No new admission or assumption stands in for this argument.

## Validation

Run `./scripts/validate.sh --axioms` after changes. Acceptance clients check the constructor
composition, query bound and standard axiom dependencies of the bridges and existing key lemma.
When updating the blueprint, also run `./scripts/validate.sh --site`.
