# Executable LogUp

For source navigation and import entry points, start with the
[code-local index](../../ArkLib/ProofSystem/Logup/README.md).

ArkLib implements complete interactive oracle arguments for field-valued weighted balance,
scalar indexed lookup, and typed tuple/bus indexed lookup. They use Haböck's grouped construction,
computable native Sumcheck, retained original sources and an executable terminal authentication
check. Honest provers operate on Boolean evaluation tables and coefficient arrays.

The [reference comparison](../kb/concepts/logup.md) records the inspected paper version and pinned
Plonky3, OpenVM, SP1 and Stwo sources. Those references explain the equations and design choices;
they do not establish Rust/Lean program equivalence. Fractional GKR, LogUp*, heterogeneous trace
packing, a STARK AIR compiler, polynomial commitments, Fiat–Shamir and zero knowledge are separate
protocol developments.

## Statements and witnesses

For finite messages `(key_i, weight_i)`, weighted balance means

```text
netWeight(k) = sum_{i : key_i = k} weight_i
Balanced    = forall k, netWeight(k) = 0
```

The weighted protocol tests balance **after** the explicit scalar map `f : B →+* E`. It does not
infer integer multiset equality or lookup membership from field balance alone. Generic fiber,
fraction and histogram algebra has no field-size, characteristic or finite-key assumption beyond
the operations used by each declaration.

A scalar lookup has `M` query columns and `P` declared physical table pieces, each with
`N = 2^n` rows. Its language is exactly

```text
forall queryColumn row, exists piece tableRow,
  query[queryColumn][row] = table[piece][tableRow]
```

`Logup.Lookup.ValidIndices` checks a supplied table position for every query. The honest prover
computes a natural histogram of those indices once, then casts and reshapes it into the actual
multiplicity message. Duplicate values and different valid witnesses are supported. Runtime
witnesses come from input data, not classical extraction from an existential proof.

Queries have weight `+1`; table rows have the negative retained multiplicity. Histogram balance
holds in every characteristic. The converse from field balance to membership needs positive
query counts to stay nonzero. `Logup.Lookup.Config` carries an explicit `p` and proof-only
`CharP B p` certificate; `create?` checks `M*N < p` and the grouping bounds. It does not search
for a characteristic at runtime, and it requires no table-row budget `P*N < p`.
An extension field enlarges the challenge space without repairing base-characteristic wraparound.

The [normalization bridge](../../ArkLib/Data/Vector/LookupNormalization.lean) proves equality of
per-key aggregates with the paper's normalized assignment when its table normalizers are nonzero.
The messages themselves can differ. Bounded count-cast recovery and `Vector.Perm` are separate
algebraic results in [Lookup.lean](../../ArkLib/Data/Vector/Lookup.lean) and
[Count.lean](../../ArkLib/ToMathlib/List/Count.lean). The lookup endpoint is an inclusion argument;
equal collection lengths alone do not turn it into a permutation argument.

## Grouped circuit

Let `T` be the number of terms per row: `T=M+P` for scalar and tuple lookups. The checked
[weighted configuration](../../ArkLib/ProofSystem/Logup/Interaction/Config.lean) accepts `T>0`
and `1≤ell≤T`. It stores the actual consecutive groups `I_k`, with `K=ceil(T/ell)`, exact ordered
coverage and lengths at most `ell`. Zero row variables and empty query or table collections are
allowed; a zero total collection is rejected.

[FractionPair](../../ArkLib/Data/Fraction.lean) folds unnormalized pairs using

```text
combine (a,b) (c,d) = (a*d + c*b, b*d)
unit                = (0,1)
```

Associativity, commutativity, regrouping and numerator scaling hold even at zero denominators.
Agreement with evaluated fractions separately requires nonzero denominators. The pairs have no
misleading field or semiring instance. [PartialFractions.lean](../../ArkLib/Data/Polynomial/PartialFractions.lean)
proves rational uniqueness, repeated-pole denominator clearing and the degree bound for

```text
P(X) = sum_a w_a * product_{b != a} (X - v_b),    degree P ≤ T*N-1.
```

For a scalar challenge `alpha`, set `d_i=alpha-v_i`. The grouped residual and batched polynomial are

```text
R_k(X) = h_k(X) * product_{i in I_k} d_i(X)
         - sum_{i in I_k} w_i(X) * product_{j in I_k, j != i} d_j(X)

Q(X)   = sum_k h_k(X) + eq(X,z) * sum_k lambda_k * R_k(X)
eq(x,z)= product_j ((1-x_j)*(1-z_j) + x_j*z_j).
```

[Algebra/Grouped.lean](../../ArkLib/ProofSystem/Logup/Algebra/Grouped.lean) proves the scalar circuit,
polynomial realization, Boolean sum and individual degree bound `degreeOf j Q≤ell+2` for arbitrary
multilinear value, weight and helper inputs. Its global clearing implication is division-free:

```text
(forall k u, R_k(u)=0) and (sum_{k,u} h_k(u)=0)  ==>  P(alpha)=0.
```

This includes poles. Soundness therefore charges roots of the fixed cleared numerator without a
separate pole event. Mathematical sparse-polynomial and rational-function views are individually
noncomputable proof objects; the scalar circuit and all protocol algorithms remain executable.

## Interaction and retained sources

For scalar lookup, the prover sends its BASE multiplicity oracle `mu` before `alpha`. For tuple
lookup, it sends `mu` before an additional fingerprint challenge `beta`; the compressed weighted
suffix follows. Weighted balance starts with fixed value and weight sources. Their common suffix is:

1. Draw `alpha : E` from the whole challenge field.
2. The prover sends `K` multilinear helper oracles. Honest Boolean entries are the **termwise**
   total-field sums `h_k(u)=sum_{i in I_k} w_i(u)/(alpha-v_i(u))`, including at poles.
3. Draw the joint `(z,lambda) : E^n × E^K`.
4. Run native Sumcheck on the zero-sum claim for `Q`, using degree `ell+2` coefficient messages.
5. Execute the returned final claim's oracle action against the retained original sources and
   actual helper message; compare its result with the claimed value.

[Interaction/Protocol.lean](../../ArkLib/ProofSystem/Logup/Interaction/Protocol.lean) selects the
actual computable native verifier and terminal action. [Interaction/Source.lean](../../ArkLib/ProofSystem/Logup/Interaction/Source.lean)
binds each value, weight and helper scalar once before `Logup.reconstruct`; its realization theorem
holds for every well-typed helper, with no honesty or off-pole premise. Queries build no sparse
polynomial and enumerate no Boolean rows in the reconstruction circuit.

The scalar and tuple source adapters retain the actual earlier `mu` and the later helper in their
distinct slots, even when interfaces have the same shape. Arbitrary original source views remain
explicit. [Interaction/Execution.lean](../../ArkLib/ProofSystem/Logup/Interaction/Execution.lean) and the scalar/
tuple execution owners prove the actual prefix binds and routed native suffix, preserving private
continuations, effects after public abort, path-dependent outputs and terminal authentication.
The native reduction still exposes a final claim for composition; the complete endpoint additionally
checks it. A returned unchecked claim is not acceptance.

`n=0` still sends the required helper, receives the joint challenge and performs final source
checking; it has no coefficient messages or private equality-cache initialization. At positive
`n`, a failed round sum returns `None` and no native challenge is drawn for that round. The prover's
`None` continuation still executes. Successful final rounds omit an unused private fold.

## Soundness and completeness

The three `uniformExecute_soundness` theorems quantify over arbitrary whole native prover
strategies, including dependent private outputs. They require genuine realization by the original
source and preserve the actual ordering of `mu`, `beta`, helpers and later challenges.
Weighted soundness tests balance after `f` in the finite challenge field. Scalar/tuple membership
soundness uses fields `B,E`, hence an injective field map, and the certified query-count budget.
For `q=|E|`, `D=T*N` and `s` distinct occurring typed keys, their bounds are:

| Complete endpoint | False initial statement | Acceptance probability at most |
| --- | --- | --- |
| [Weighted](../../ArkLib/ProofSystem/Logup/Security/Soundness.lean) | Nonzero mapped net weight at some value | `(D+n*(ell+3))/q` |
| [Scalar](../../ArkLib/ProofSystem/Logup/Lookup/Security.lean) | False membership in the declared table collection | `((M+P)*N+n*(ell+3))/q` |
| [Tuple/bus](../../ArkLib/ProofSystem/Logup/Lookup/Tuple/Security.lean) | False membership among original semantic keys | `((s-1)*W+(M+P)*N+n*(ell+3))/q` |

The weighted proof charges `(D-1)/q` for the fixed cleared numerator, `n/q` for one nonzero residual
selected before `z`, `1/q` for affine batching, and `n*(ell+2)/q` for native Sumcheck. It has no union
factor `K` on the residual event. Final authentication adds no soundness error. These are proved
upper bounds, which can exceed one for unsuitable parameters; they do not import the paper's
printed numerical ledger.

The honest helper algorithm uses total inversion, with no pole scan, retry or rejection sampler.
[Weighted completeness](../../ArkLib/ProofSystem/Logup/Security/Completeness.lean) proves acceptance
away from the actual mapped value support. Scalar completeness sharpens this to the distinct
**declared table** support, at most `P*N` values. Tuple completeness holds for every `beta`, including
fingerprint collisions, with the same coarse `P*N/q` failure bound and no compression-error term.
The completeness owners expose supported off-pole acceptance, uniform failure/success bounds and
exact total probability mass one, including public abort branches.

## Typed tuple and bus encoding

[TaggedTuple.lean](../../ArkLib/Data/Polynomial/TaggedTuple.lean) checks a finite schema with
injective BASE bus tags and one fixed payload width per bus, bounded by `W`. A key is the dependent
pair of its bus and exact-width payload. Its fingerprint is

```text
c_beta(bus,payload) = tag(bus)*beta^W + sum_{j < width(bus)} payload_j*beta^j.
```

Under an injective coefficient map, the formal polynomial encoding is injective. Evaluation at a
particular `beta` can collide, including across buses. [TaggedTupleProbability.lean](../../ArkLib/Data/Polynomial/TaggedTupleProbability.lean)
isolates one fixed key with nonzero net weight from the other `s-1` occurring keys, with error
at most `(s-1)*W/q`.
The original keys and arbitrary BASE `mu` are fixed before beta; honest histogram balance instead
transports for every beta. Plonky3/Stwo power-order translations have explicit equations; SP1's
multilinear hash is a different family and is not verified by this univariate fingerprint theorem.

[Lookup/Tuple/Provider.lean](../../ArkLib/ProofSystem/Logup/Lookup/Tuple/Provider.lean) checks common Boolean
row heights, exact payload shapes and declared physical-piece ownership. It stores original typed
keys and padded coefficient tables once. Structural provider validity is separate from lookup
membership. Several physical pieces may have the same bus owner; unused registered buses and
zero-width payloads retain their schema and container roles. `Schema.mk?`,
`ProviderLayout.create?` and `PreparedProvider.prepareRaw?` return `None` on malformed raw tags,
widths, column/row lengths or owners. Typed messages carry their shape and degree proofs.
Heterogeneous-height packing and caller constraints for enabled/signed counts remain separate adapters.

## Honest programs and defaults

Boolean tables use CompPoly's little-endian order: adjacent entries eliminate the least significant
remaining coordinate. [Prover/Helpers.lean](../../ArkLib/ProofSystem/Logup/Prover/Helpers.lean) prepares
`D_i(u)=alpha-f(V_i(u))`, mapped weights and termwise helpers. [Prover/State.lean](../../ArkLib/ProofSystem/Logup/Prover/State.lean)
retains D/weight/helper tables and lambda. After the joint challenge it caches equality weights
using the certified fast Boolean basis. Every nonterminal challenge folds all four table families
with `a+r*(b-a)`, preserving the exact formal head substitution without inversion.

[Prover/RoundCoefficients.lean](../../ArkLib/ProofSystem/Logup/Prover/RoundCoefficients.lean) turns adjacent
entries into affine coefficient arrays, evaluates the fraction circuit and streams each suffix
row directly into one padded accumulator. It normalizes once and packs a message of degree at
most `ell+2`. Its theorem identifies the formal native honest projection; equality of finite-field
point functions would be insufficient (`X^3` and `X` agree over `F₂` but have different coefficients).
No full multivariate expansion or interpolation-node inversion is used.

The public constructors are:

| Variant | Explicit-builder reference | Selected default |
| --- | --- | --- |
| Weighted | `Logup.Prover.Honest.honestWith` | [`Logup.Prover.Honest.prover`](../../ArkLib/ProofSystem/Logup/Prover/Default.lean) |
| Scalar | `Logup.Lookup.Honest.proverWith` | [`Logup.Lookup.Honest.prover`](../../ArkLib/ProofSystem/Logup/Lookup/Prover.lean) |
| Tuple/bus | `Logup.Lookup.Tuple.Honest.proverWith` | [`Logup.Lookup.Tuple.Honest.prover`](../../ArkLib/ProofSystem/Logup/Lookup/Tuple/Prover.lean) |

The selected defaults execute named arithmetic programs. Scalar histogram construction precedes
alpha; tuple histogram construction precedes beta, and the tuple default then eagerly constructs
both E cache matrices once with direct BASE coefficient reads and seeded Horner. Native coefficient
queries and public tuple queries select the same reusable seeded Horner core. A length-L message
uses L coefficient reads and `max(L-1,0)` multiplications/additions.

[Prover/Arithmetic/Control.lean](../../ArkLib/ProofSystem/Logup/Prover/Arithmetic/Control.lean) shares the
actual Unit, Cost and complete-Call control; [Prover/Arithmetic/Ledger.lean](../../ArkLib/ProofSystem/Logup/Prover/Arithmetic/Ledger.lean)
relates exact selected program arguments and messages along typed optional histories. Unit retains
no Call/Cost instrumentation. Whole-strategy equalities transfer correctness to the explicit-builder
reference. Resource bounds refer to the selected programs themselves, not a separate algorithm
with equal outputs.

## Separate resource metrics

Write `C` for the exact tuple compression profile and `D=(M+P)*N` for its value rows. The resource
owners distinguish the following metrics; none is a total machine-time bound.

| Metric | Delivered contract | Boundary |
| --- | --- | --- |
| Private arithmetic requests | [Weighted resource envelope](../../ArkLib/ProofSystem/Logup/Prover/Resources/Arithmetic.lean): each of nine instruction coordinates is at most `1012*N*T*ell`; their sum is at most `9108*N*T*ell`. | Includes selected prepare/helpers/start/native message/fold programs; excludes BASE/Nat work, embeddings, sampling, source handlers and allocation. |
| Scalar frontend | [Scalar resources](../../ArkLib/ProofSystem/Logup/Lookup/ArithmeticResources.lean): `M*N` histogram increment sites, `P*N` counters/casts, `P*N` BASE negation sites and `2*T*N` embedding sites. | Structural sites and dimensions; not Nat bit operations or opaque embedding work. |
| Tuple frontend | [Tuple resources](../../ArkLib/ProofSystem/Logup/Lookup/Tuple/ArithmeticResources.lean): exact compression prefix `C`, plus the same weighted request envelope; nine-kind cache total `D*(3W+3)+2*M*N+4*P*N`. | Direct reads/embeddings of `D*(W+1)` BASE coefficient cells and `P*N` BASE multiplicities; provider/histogram preparation remains separate. |
| Verifier-local arithmetic | [Native path usage](../../ArkLib/ProofSystem/Sumcheck/Interaction/Resources.lean), seeded Horner, shared sum/equality checks and [scalar reconstruction](../../ArkLib/ProofSystem/Logup/Algebra/ArithmeticReconstruction.lean). | Exact request recurrences for those selected local bodies; source/view/backend and sampling work remain separate. Reconstruction requests no inversion. |
| Logical and expanded source openings | [Source resources](../../ArkLib/ProofSystem/Logup/Interaction/Resources.lean): one Q query binds `2T+K` logical answers. Identity scalar sources expand it to `M+2P+K` raw openings; identity tuple coefficient sources to `(W+1)*(M+P)+P+K`. Native message queries are at most `3n`. | Arbitrary views use their actual fanout. The terminal Q action occurs after all rounds pass, including `n=0`, even if final authentication rejects; public abort skips it. |
| Dense source backend | Original `evalMle`/`eval₂Mle` recursively interpolate actual dense tables. | Count backend work separately from openings; the transparent runner is not thereby a succinct verifier. It does not silently select the private one-multiplication fold or fast equality cache. |
| Logical storage | [Prover/Resources/Storage.lean](../../ArkLib/ProofSystem/Logup/Prover/Resources/Storage.lean), [Prover/Resources/StorageBuffers.lean](../../ArkLib/ProofSystem/Logup/Prover/Resources/StorageBuffers.lean) and [Prover/Resources/StorageLedger.lean](../../ArkLib/ProofSystem/Logup/Prover/Resources/StorageLedger.lean): actual all-level fields, source/path messages, frontend/provider/cache data and named construction roles, with seven separate category envelopes. | Explicit original/view/embedding/raw allowances; logical cells and containers, not bytes, allocator peak, physical sharing, closure/stack layout or GC liveness. |

A full all-success history visits every positive private level, totaling `2N-2` table rows and
`nK` private lambda slots; early abort retains a prefix with no larger census.
Retaining all verifier target/challenge prefixes gives a triangular census bounded by `2N`.
Completed affine inputs use `4T+4K+2` coefficient cells; completed phase buffers and expanded builder roles have
distinct `96*(ell+4)` and `256*(ell+4)` bounds. The inventory inspects the actual array push loops,
`List.mapTR` reverse accumulators and certified heads/suffix/list-to-array builders separately.

### Actual source packets and ambient logs

In [Interaction/Resources.lean](../../ArkLib/ProofSystem/Logup/Interaction/Resources.lean),
`executeStrategiesLogged_eq_prefix_bind`, `scalar_executeStrategiesLogged_eq_sender_bind` and
`tuple_executeStrategiesLogged_eq_sender_beta_bind` preserve the complete actual path, dependent
private output, Bool and source-log order through the prefix and native suffix.
`qView_complete_log_eq_boundary` appends the actual Q boundary query to that same native message
log exactly when the bare native result is `Some claim`. `qView_final_log_length` gives the
complete source length: actual native `messageQueries`, plus the original view's actual fanouts
at that claim's returned challenges, plus K retained helpers.
The final Bool may be false: reaching authentication and passing it are different events. `None`
skips the Q query. These laws require no source-truth or honest-message premise.

The public source's synthetic query weights have M constant-one and P unary-negation sites.
Those negations are separate from `ArithmeticSpec.sub` requests in the already-bound scalar
reconstruction profile. Public tuple queries buffer W+1 E coefficient answers before seeded
Horner; the private eager cache instead reads BASE coefficients directly. Neither local profile
prices the dense MLE backend or an opaque original view.

[Interaction/SamplingResources.lean](../../ArkLib/ProofSystem/Logup/Interaction/SamplingResources.lean)
keeps arbitrary draw programs separate from uniform specialization. For every **supported complete**
phased run, `phased_verifier_queries` and its scalar/tuple variants count verifier-party ambient
queries as `ca+cj+cr*s`, with an additional `cb` for tuples. The constants are supported log lengths
of the actual alpha, joint, native-round and beta programs; `s` is the actual native path's
`roundSamples`. A scripted joint program need not draw every coordinate independently.
The `execute_world_eq`, `scalar_execute_world_eq` and `tuple_execute_world_eq` program equalities
connect the actual Bool endpoint and its full ordered ambient log to that same phased run.
They preserve arbitrary prover effects; there is no bound on malicious prover-private sampling.

For the selected uniform function/product programs, the joint draw is one public phase event but
uses `n+K` E sample blocks. Given a proved supported primitive-log length c for one selected E
sample, `uniform_phased_verifier_queries` and its scalar/tuple variants give
`c*(1+n+K+s)` verifier queries, or `c*(2+n+K+s)` for tuples. No generic `SampleableType` is assumed
to cost one or six. The pinned KoalaBear.Field and Ext6 sample programs provide c=1 and c=6.

[Interaction/HonestSamplingResources.lean](../../ArkLib/ProofSystem/Logup/Interaction/HonestSamplingResources.lean)
proves that actual weighted/scalar/tuple defaults make zero prover-party ambient queries, including
public abort responses and zero rounds, for any restricted verifier. The three variants of
`uniformExecute_default_queries` in SamplingResources combine this fact with the existing
phase partition. Each supported **actual named uniform endpoint** Bool/log pair retains a supported
concrete path with that exact Bool and ordered log, and the same formula now counts its **total**
primitive queries. There is no caller-supplied private-purity, valid-index or off-pole premise.
Ordinary-strategy equality transfers observable ambient logs here; it transfers no separate
arithmetic or storage cost.

When all native round checks pass, `s=n`: weighted/scalar uniform sampling has `1+K+2n` E blocks,
and tuple sampling adds beta, regardless of the final authentication Bool. The actual Ext6
`n=1,K=1` scalar/tuple fixtures attain 24/30 primitive BASE requests. Zero rounds still draw alpha
and the joint lambda vector, plus beta for tuples. Public round abort skips its unreached native
draw; a private ambient/runtime abort can prevent later stages entirely. The count theorems cover
supported complete results and assert neither losslessness nor a fixed count for such partial
runs. Uniform-oracle request counts do not price RNG internals, BASE/Nat preprocessing, field
instructions, source backends or memory.

## Owners and validation

| Owner | Responsibility |
| --- | --- |
| `Data/Fraction.lean`, `Data/Polynomial/PartialFractions.lean` | Executable pair algebra; rational and symbolic clearing proofs |
| `Data/Vector/`, `ToMathlib/List/Count.lean` | Indexed histograms, membership/count converses, normalization and bounded permutation recovery |
| `Data/Polynomial/TaggedTuple*.lean` | Checked semantic schemas, fingerprint equations and selected-key collision bounds |
| `ProofSystem/Logup/Algebra/` | Grouped circuit, degree/clearing/Boolean-sum proofs and shared scalar reconstruction |
| `ProofSystem/Logup/Interaction/`, `Security/` | Actual weighted source, native execution, arbitrary-prover soundness and source resources |
| `ProofSystem/Logup/Lookup/`, `Lookup/Tuple/` | Scalar/typed provider languages, retained multiplicities, complete endpoints, security, completeness and defaults |
| `ProofSystem/Logup/Prover/` | Helpers, private state, formal streamed messages, actual arithmetic control and resource/storage ledgers |
| `ToCompPoly/Multilinear/`, `ToCompPoly/Univariate/` | Reusable executable basis, affine/fold/formal-view bridges, raw arithmetic, seeded Horner and normalization |

`ArkLibTest/` includes ordinary generic callers, compiler-IR and standard-axiom guards, exact
finite-field cases, characteristic wraparound, repeated/unused rows, malformed shapes, source/
helper corruption, forged final claims, private effects on abort and nontrivial security bounds.
Concrete [scalar soundness fixtures](../../ArkLibTest/ProofSystem/Logup/Lookup/Security.lean)
instantiate `20/257<1`; the [tuple fixtures](../../ArkLibTest/ProofSystem/Logup/Lookup/Tuple/Security.lean)
instantiate `14/17<1` with false semantic membership. The [measured runtime fixtures](../../ArkLibTest/ProofSystem/Logup/Interaction/MeasuredRuntime.lean)
and `lake exe logup-runtime` exercise the actual complete defaults, including KoalaBear-to-Ext6,
scripted poles and named uniform IO samplers. Random checks use statements valid at every draw;
scripted exact values separately test failures and challenge ordering.

Run the [normal, docs and axiom gates](../wiki/quickstart.md) on the final coherent source/artifact
head. IR/native checks establish execution evidence; they do not replace kernel-checked semantic
proofs or review of the complete old-to-new source and acceptance-test delta.
