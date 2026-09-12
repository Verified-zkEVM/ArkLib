# Taylor algebra, projection and one-center decoding checkpoint

Personal 4 remains the integration owner and owns G03–G05 and G10. These are bounded
implementation slices, not completed Taylor or zeroth-order decoder groups. The shared
`symbolicDecode` backend remains unavailable.

## Source and ownership

Every worker started at `24c3e183ecdac020973c1446400e42db3b62b2ed`, with unchanged
`lake-manifest.json` and `lean-toolchain`. The paper specification is pinned to
`04ca01fbce9609bcc5730c8f620da6dfa5c2bf8c`; later paper edits were not adopted.

| Work | Branch | Owned source and test module |
| --- | --- | --- |
| G03 geometry | Geometry and shifts workers | `FastTaylor/Geometry/{Projection,Matrix}`, `MvPolynomial/NonvanishingGrid` |
| G04 local arithmetic | `quang/decoder-taylor-local` | `MvPolynomial/BoxAlgebraNilpotence`, `Polynomial/ConfluentAlgebra/{MonicArithmetic,Structure,ParameterKernel,Inverse}` |
| G04/G05 generic operations | Shifts and geometry workers | `Polynomial/NewtonInverse`, `MvPolynomial/TaylorReconstruction/{AffineShift,UnivariateView}` |
| I0 chart and equation adapter | Core integration branch | `FastTaylor/ChartData`, `MvPolynomial/TaylorReconstruction/LocalEquation` |
| G10 center search | Core integration branch | `ListDecoding/ZerothOrderDecoder/{CenterSearch,BatchedCenter}` |

`FastTaylor` paths are under `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/`.
`ListDecoding` is under `ArkLib/Data/CodingTheory/ReedSolomon/`; generic paths are under
`ArkLib/Data/`. Each module has a matching `ArkLibTest/Data/` client. Workers are bounded
Astra low agents with private source worktrees and private dependency/build copies.

## Established boundaries

- Linear substitution computes matrix-coordinate polynomials, preserves polynomial semantics,
  does not increase total degree, and preserves the regular locus through a supplied matrix
  inverse. The explicit matrix constructor now selects the first nonzero pivot of a supplied direction
  and computes both inverse matrices. Constructing the direction and retained component remains open.
- The parameter ideal and the entire zero-constant-specialization kernel have nilpotence
  exponent `r*(N-1)+1` for positive precision. The bound applies to mixed products.
- Monic quotient arithmetic uses stored canonical representatives over a nontrivial commutative
  ring. Reduction, addition, multiplication and negation refine the semantic quotient.
  Executable coefficient specialization commutes with monic reduction. No field or squarefree
  constant-fiber hypothesis is imposed.
- Division-free sparse parameter shifts cancel exactly. A shifted box with `N>L` recovers
  every polynomial of total degree at most `L`. This is parameter reconstruction, not a claim
  that fast divide-and-conquer composition of the equation's X variable has been implemented.
- `FastTaylor.ChartData` fixes the stored payload and exactly `k` local Taylor numerators.
  The agreement consumer computes the paper's shifted residual and proves evaluation after
  any coefficient ring homomorphism. Full chart validity and coverage remain separate.
- `ZerothOrderDecoder.selectCenter` finds the first checked fiber. It rejects zero fibers,
  lost value-variable degree, and failed slope inverses. `runNormalized?` invokes ordinary
  quotient Newton and recovery at that center. Its exactness theorem proves successful exact
  output assuming a good center exists in the supplied prefix and the supplied equation
  vanishes on wanted messages. It does not assume regularity separately: the executed inverse
  check supplies it. The separate `BatchedCenter` entrypoint uses actual subproduct-tree evaluation to select the
  first nonzero obstruction value, then executes the regularity checks at that single center.
  It still requires an obstruction polynomial and its validity certificate.

## Additional integrated producers

- `ConfluentAlgebra/Structure` supplies the executable representative ring and coefficient maps.
  `ParameterKernel` proves that the whole specialization kernel in the quotient is nilpotent.
- `ConfluentAlgebra/Inverse` computes a constant-fiber Bézout coefficient, lifts stored constants,
  and executes `NewtonInverse` doubling. Success is equivalent to an inverse existing in the
  original quotient, including unit modulus. No approximate inverse is supplied by the caller.
- `NonvanishingGrid` executes Cartesian enumeration and first-nonzero search, with success from
  nonzeroness and the distinct-grid degree bound. It does not construct a sufficient field.
- `UnivariateView` converts exactly between flat last-variable and nested coefficient forms.
  `LocalEquation` shifts free parameters into the box, preserves supplied monicity, and recovers
  the exact constant fiber for positive precision, including repeated-root fibers.

## Acceptance evidence

The integration gate is `./scripts/validate.sh --axioms`, with
`LAKE_ARTIFACT_CACHE=false LAKE_NO_CACHE=true`. All fifteen runtime clients are registered in
`agreement-recovery-runtime`; compiling an unused test entrypoint is not acceptance.
The coordinator report records the completed gate result and immutable accepted commit.

Independent nonauthor review covered every production/test slice. The geometry worker reviewed
shifts; the shifts worker reviewed geometry, local algebra, chart payload and center search.
No mathematical correctness blocker was found. Review requested additional center-degree,
nonzero-center quadratic, nonreduced multiplication and failure/empty-output tests; those are
included in the checkpoint.

Executed acceptance cases distinguish surviving mixed parameter squares from vanishing cubes,
repeated-root monic fibers, inverse shifts in characteristic three at degree three, nonidentity
shears, quadratic local Taylor residuals, rejected centers followed by success, degree loss,
search exhaustion, and actual selected-center Newton/recovery. The latter has no fallback path.

## Next producer obligations

1. G03: computed regular-component reduction from Personal 1, homogeneous direction selection from the implemented grid search,
   weighted monic coefficient bounds, separant resultant and good confluent sample.
2. G04: algebraic/differential series Newton and fundamental matrices; scalar quotient inversion
   and its whole-kernel Newton correction are implemented.
3. G05: weighted monic reduction, denominator clearing, global coefficient reconstruction and
   all-regular-solution coverage, including ramified projection fibers.
4. G10: prescribed interpolation algorithm correspondence, Personal 1 global normalization,
   obstruction polynomial construction, and a sufficient constructed
   field/prefix from G07. A supplied normalized equation and good prefix remain conditional.
5. I0/I1: full geometry/local/global validity and coverage contracts, concrete producer
   composition, global dispatch and public unconditional exactness.

Personal 1 owns G01/G02/G06. G07/G08/G09 remain deferred in this coordinator's current scope.
These dependencies cannot be replaced by supplied producer assumptions in the final theorem.
