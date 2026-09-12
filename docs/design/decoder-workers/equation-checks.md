# Worker D: certify equation bounds and checked construction

Read [shared instructions](README.md). Use the supplied checkpoint SHA and branch
`quang/decoder-m1-equation-checks`.

## Owned files

Create `HiddenDerivativeDecoder/EquationChecks.lean` and new corresponding tests.
If essential, you may edit `HiddenDerivativeDecoder/Input.lean` only; preserve existing
public names and types. Submit suggested changes to `Run.lean`, `Correctness.lean`,
`Explainer.lean`, or `Explainer/Support.lean` separately for coordinator integration.

## Deliverable

Prove that `SuppliedEquation.boundsPass` is equivalent to the intended concrete
nonzero/X-degree/jet-degree bounds (`WithinBounds`, with nonzeroness explicit as
appropriate to its definition). Verify finite-support iteration covers every monomial.

Prove that a valid support certificate's constructed equation passes that executable
check. Compose existing `construct_success` and `construct_explains`; do not assume
successful checking as a hypothesis. Include the precise structural hypotheses needed
for the interpolation dimension argument.

Audit `ValidInput`, `ValidOptions`, and dispatch guard arithmetic against the current
interfaces. Add checked predicates with reflection theorems for missing input/option
conditions when useful, without changing runtime dispatch order. Supplied characteristic
must be tied to ring characteristic in theorems. Determine and state the exact prime-field
hypotheses needed for any field-size interpretation. Do not claim that guard arithmetic
alone proves eventual symbolic decoding correctness or that all extension fields have
size equal to their characteristic.

## Acceptance

Compile principal reflection and checked-construction theorems. Test valid support,
empty/duplicate/short support, boundary degrees, zero equation, and early-dispatch cases.
Keep the symbolic backend's explicit unavailable result honest. No field enumeration,
new backend oracle, altered fallback range, or full decoder completion claim.
