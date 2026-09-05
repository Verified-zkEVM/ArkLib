# BCPZZ26 statement and architecture audit

This page audits the Lean targets against `BCPZZ26` and records the parametric interfaces on which
the formalization should depend. It is a statement-fidelity ledger, not evidence that the paper's
main theorem is proved.

## Reviewed Sources

- `BCPZZ26`, ECCC TR26-164, public PDF dated 2026-09-04, SHA-256
  `b749151a7b5961e34760c735cf64067f0c3dea632030f2e69737b6caef7a3e70`.
- `Kop15`, final Theory of Computing article, Theorem 4.3.
- Published Lean corollary:
  `ReedSolomon.LowRateListDecoding.exists_decoderCertificate_of_low_rate`.
- Parametric Lean join:
  `ReedSolomon.HiddenDerivative.exists_decoderCertificate_of_contracts`.

## Architecture disposition

The published low-rate theorem remains a source-fidelity corollary. It is not the dependency
boundary for the interpolation, root-solver, or decoder trunks.

- `ReedSolomon.ListDecoding.DecoderCertificate` is generic and requires exact membership plus a
  uniform list bound.
- `ReedSolomon.ListDecoding.CandidateCertificate` allows ambient candidates and false positives;
  the final filter targets an independent `messageDim ≤ designDim` and checks actual agreement.
- `ReedSolomon.HiddenDerivative.Parameters` keeps `designDim`, `minAgreement`, `derivOrder`,
  `multiplicity`, and the three support caps free natural numbers.
- `ReedSolomon.HiddenDerivative.InterpolationContract` produces a valid equation for every received
  word and proves the differential identity for every sufficiently agreeing ambient polynomial.
- `ReedSolomon.HiddenDerivative.RootSolverContract` consumes the same equation validity and
  satisfaction predicates, exactly enumerates the ambient solutions, and exposes an arbitrary
  `listBound`.
- `ReedSolomon.HiddenDerivative.exists_decoderCertificate_of_contracts` is the stable join. It does
  not mention rates, the paper's named parameter choices, the constant `768`, a hitting-extension
  degree, or the bound `q^(4*d+6)`.

This separation ensures that improved interpolation geometry, multiplicity choices, root lifting,
or list-size estimates change a contract instance or parameter discharge rather than the decoder
theorem.

## Published theorem: clause-by-clause correspondence

| Source clause | Lean representation | Audit disposition |
| --- | --- | --- |
| `n ≥ k ≥ 1` | `hk : 0 < k`, `hkn : k ≤ n` | Exact over naturals. Positivity of `n` follows. |
| `ε, θ ∈ (0,1)` | `hε : ε ∈ Set.Ioo 0 1`, `hθ : θ ∈ Set.Ioo 0 1` | Exact; endpoints are excluded. |
| `d = ceil(ε^(-3/θ))` | `derivativeOrder ε θ` | Uses `Real.rpow` and `Nat.ceil`. Only the corollary fixes `d`. |
| `k > d` | `hdk : derivativeOrder ε θ < k` | Exact strict inequality. |
| `k/n ≤ (1-θ)ε` | `hrate : (k : ℝ) / n ≤ (1 - θ) * ε` | Exact real-valued rate. |
| condition (26) | `hεSmall : ε < smallEpsilonBound θ` | Exact base, exponent, denominator `768`, and strictness. |
| `q` prime | `[Fact q.Prime]` | Standard `ZMod q` field boundary. |
| `q ≥ max(n, 4ε^(1-9/θ)n/k)` | `hnq` and `hq` | Exact split of the maximum; second comparison is over reals. |
| distinct evaluation points | `domain : Fin n ↪ ZMod q` | Embedding enforces pairwise distinctness. |
| every received word | certificate exactness quantifies `Fin n → ZMod q` | Universal, not a fixed or existential word. |
| all polynomials of degree `< k` | `Polynomial.degreeLT (ZMod q) k` | Strict degree invariant, including zero. |
| agreement at least `εn` | `Nat.ceil (ε * n) ≤ Code.agree ...` | Exact integral form. |
| decoder output | membership iff agreement | Includes both soundness and completeness. |
| list length `q^O(ε^(-3/θ))` | `q^(4*d+6)` | Stronger explicit `BCPZZ26`/`Kop15` specialization. |
| radius `1-ε` consequence | `Code.IsListDecodable ... (1 - ε) ...` | Canonical ArkLib API. |
| runtime `q^O(ε^(-12/θ))` | not represented | Deliberate deferred scope; no current cost model. |

## Adversarial statement checks

- `messageDim` and `designDim` are independent, with the only decoder-side relation
  `messageDim ≤ designDim`; the interpolation proof cannot silently identify `k` with `K`.
- The root solver does not own the target message dimension. It solves at the ambient design
  dimension, and the decoder rejects candidates of excessive degree or insufficient agreement.
- The solver list bound is a parameter. The integration theorem does not hard-code Kopparty's
  quadratic hitting extension or `4*d+6` exponent.
- The degree bound is strict `< k`, not `≤ k`, and is carried by `Polynomial.degreeLT` rather than
  `natDegree`; this handles the zero polynomial without a special convention.
- The field-size hypothesis retains both independent parts. Although the embedding implies
  `n ≤ q`, keeping `hnq` in the corollary mirrors the source arithmetic.
- `Nonempty DecoderCertificate` is extensional existence, not executability or a complexity claim.

## Confirmed source repairs

### Ambient design dimension

Proposition 3.13 assumes `k/n ≤ (1-θ)ε`, but its proof uses
`k = floor ((1-θ)εn)`. The repair sets `K = floor ((1-θ)εn)`, proves `k ≤ K`, decodes degree
`< K`, and filters to degree `< k`. The generic contracts expose this repair directly.

### Exact lattice-growth constant

For `m=d^3`, `d≥3`, and the paper's `W`, the hidden term can be bounded by

```text
(d-1) * (m + binom d 2) / W ≤ 2/(2+θ) * log d + 5/4.
```

It suffices to prove

```text
θ(1-θ)/18 * log d ≥ log ((4+3θ)/θ) + 5/4.
```

The parameter-discharge theorem must prove that condition (20) supplies this margin. The core
contracts do not depend on `768`.

### Ceiling in the support cap

Lemma 3.2 uses the false inequality `ceil x ≤ x`. The repaired calculation uses

```text
m*A/(K-1) - |c| > θ*m/4 + θ^2*m/(1-θ) - 1
```

and discharges nonnegativity of the final two terms from the paper's hypotheses.

### Local-kernel hygiene

No structural defect was found in the local-kernel blocks, their cross-`r` independence, the error
rescaling, multiplicity accumulation, or the Hasse-derivative/Kopparty interface. Formal statements
must nevertheless expose `d≥3`, distinguish `rank Γ` from `rank Φ`, and restrict the unscaled
divisibility condition to `d*b < m`.

## Stronger theorem candidates

Keeping the natural parameters free suggests a fixed-rate, fixed-positive-gap theorem and improved
interpolation and root-list exponents. These are high-confidence candidates, not results currently
advertised by ArkLib. They require independent reconstruction or author confirmation. The present
interfaces are accepted only if such results can be added as new parameter discharges without an
API rewrite.

## Current trust boundary

Three guidepost theorems intentionally carry `sorryAx`:

- `CandidateCertificate.filteredDecoder_isExact`, the generic filtering correctness bridge;
- `CandidateCertificate.filteredDecoder_card_le`, the no-list-growth bridge; and
- `exists_decoderCertificate_of_low_rate`, the published source-fidelity corollary.

The parametric contracts and their composition into an ambient candidate certificate are proved.
`CandidateCertificate.toDecoderCertificate` and the central conditional decoder inherit the two
filtering guideposts. No downstream theorem may advertise the source result as formalized while
inheriting these `sorryAx` dependencies.
