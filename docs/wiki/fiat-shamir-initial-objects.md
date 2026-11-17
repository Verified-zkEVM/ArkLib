# Fiat–Shamir initial objects

## Separate initial object

`NonInteractiveArgument/FiatShamir/DuplexSponge/InitialObject.lean` defines a generic fixed-zero
runner for any injectively encoded, fixed-length initial object. The intended object is
`(session identifier, statement)`. The proof salt is a separate argument and is absorbed next.
The interactive protocol specification, challenge codecs and prover-message tuple are unchanged.
The session identifier is never inserted into a prover message.

`InitialObject/Execution.lean` proves that consecutive object and salt absorptions equal one
absorption of their concatenated encodings. The object uses the fixed-size injective encoding
supplied by `HasSize`.

`rounds_eq_existing` proves equality with the existing round interpreter, retaining its final
state, cursors, transcript and queries. `initialize_pair` proves that product encoding is exactly
separate absorption of its two fields, followed by the salt. `DuplexSponge/QueryBounds.lean`
bounds permutation calls for individual absorb and squeeze operations.

All these definitions and theorems are generic over the alphabet, rate, capacity, object type,
encoding and protocol. Concrete suites belong in example clients under `ArkLibTest/`, outside
the core construction and proof.
Concrete implementation extraction, parsing and wire encodings remain separate obligations.

## Security boundary

The salted DSFS perfect-completeness theorem uses the ideal oracle distribution with an
independent uniform capacity-valued hash and a uniform permutation. The initial-object
runner starts from a fixed public zero state. Its execution equality identifies the round
computations from the same initialized state. Applying the DSFS statistical-distance argument
to fixed-zero initialization requires a separate probability comparison of the two experiments.

## Validation

Run `./scripts/validate.sh --axioms` after changing the execution laws. When updating the
blueprint, also run `./scripts/validate.sh --site`.
