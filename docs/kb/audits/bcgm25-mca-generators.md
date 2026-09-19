# BCGM25 MCA generators: paper-to-Lean map

Maps Bordage–Chiesa–Guan–Manzur, *All Polynomial Generators Preserve Distance with Mutual
Correlated Agreement* (`BCGM25`, https://eprint.iacr.org/2025/2051) onto ArkLib's
`ArkLib/Data/CodingTheory/ProximityGenerator/` layer, and records where the formalization
departs from the paper as printed.

Declaration docstrings in those files state what each declaration says; the correspondence to
paper items, and the argument for the departures, live here.

Checked against the ePrint version of 2025 held at `~/abf26-refs/BCGM25.pdf`. Paper items are cited
by number, so re-check them against the version in hand before relying on a row.

## Definitions

| Paper | Lean | Notes |
|---|---|---|
| Def 3.2 (`F`-linear code, `Σ` an `F`-vector space) | `ModuleCode ι F A` | The paper's alphabet generality is why the layer takes a module alphabet `A`, not `F` |
| Def 3.3 (`k`-interleaving) | `Code.ModuleCode.moduleInterleavedCode` | Row-wise; `Code.projectedCodeSubmod_moduleInterleavedCode_iff` projects it; `Code.minRelHammingDistCode_moduleInterleavedCode` shows it preserves `δᵣ` |
| Def 3.7 (projected code) | `LinearCode.projectedCodeSubmod` | |
| Def 3.10 (generator) | `CoreDefinitions.Generator` | |
| Def 3.11 (zero-evading) | `CoreDefinitions.IsZeroEvadingGenerator` | |
| Def 3.12 (MDS generator) | `CoreDefinitions.IsMDSGenerator` | |
| Def 3.14 (MCA event and error) | `CoreDefinitions.IsMCA`, `CoreDefinitions.mcaError`, `CoreDefinitions.IsMCAGenerator` | Event and value are separate; the predicate is the value's bound |
| Def 3.19 (polynomial generator) | `CoreDefinitions.IsPolynomialGenerator`, `CoreDefinitions.IsPolynomialGeneratorOf`, `CoreDefinitions.IsPolynomialGeneratorOfFull` | The `Of` forms carry the polynomial family as data; `Full` fixes each seed set to `F` |
| Def 4.3 (tensor generator) | `CoreDefinitions.TensorGenerator`, `CoreDefinitions.TensorGenerator_Explicit` | Agree under `tensorProductPiFunEquiv`; the `s`-fold iteration is `PolynomialGenIsMCA.tensorGeneratorPi` |
| Error of Thm 6.1 | `LinearTransformations.mdsMCAError` | Reads the code only through `n` and `δᵣ` (`mdsMCAError_congr`) |
| Def 8.1 (`ξ`, univariate-powers error) | `PolynomialGenIsMCA.powersMCAError` | `mdsMCAError` at output size `d + 1` (`mdsMCAError_eq_powersMCAError`, proved) |
| Def 9.1 (`ϵMCA,RS`, Reed–Solomon error) | `RSCode.reedSolomonMCAError` | Free `n` of the paper is `Fintype.card ι`; `[NeZero k]` excludes the `ρ = 0` degeneracy |

The paper types `ϵMCA : [0,1] → [0,1]`; ArkLib types the bound `I → ℝ≥0`. The codomain is widened
because `I` carries no `Add` and no ℕ-`SMul`, so the error arithmetic of Lemma 4.4 and Lemma 10.1
is unstatable in it. Bounds are therefore vacuous once they exceed `1`.

## Results

| Paper | Lean | Status |
|---|---|---|
| Lemma 3.16 (monotone in the distance) | `CoreDefinitions.mcaError_mono` | proved |
| Lemma 4.1 (right multiplication by a matrix with a left pseudoinverse) | `LinearTransformations.mcaError_generatorByRightMul_le`, `LinearTransformations.pseudoinverseGen` | proved |
| Cor 4.2 (projection onto a subset of outputs) | `LinearTransformations.mcaError_projectedGenerator_le`, `LinearTransformations.generatorSubset` | proved |
| Lemma 4.4 (tensor generator), printed statement | `LinearTransformations.isMCAGenerator_tensorGenerator_tight` | **sorried, open** — see below |
| Lemma 4.4, provable forms | `TensorMCA.isMCAGenerator_tensorGenerator_of_moduleInterleavedCode` (interleaved hypothesis, printed error), `TensorMCA.isMCAGenerator_tensorGenerator` (printed hypothesis, error scaled by `ℓ`) | proved |
| Lemma 4.4, `s`-fold iterations | `PolynomialGenIsMCA.isMCAGenerator_tensorGeneratorPi` (consumes the open form), `PolynomialGenIsMCA.isMCAGenerator_tensorGeneratorPi_tight` (δᵣ-anchored factor hypothesis, routed through the proved interleaved form) | the `tight` variant is sorry-free |
| Remark 3.20 (polynomial ⇒ zero-evading) | `PolynomialGenerator.poly_gen_is_zero_evading` | proved, total-degree variant |
| Lemma 3.22 (MCA implies CA) | — | not formalized; this is what licenses reading an `mcaError` bound as a correlated-agreement threshold statement |
| Lemma 7.1 (affine lines to affine spaces) | `AffineMCAMain.isMCAGenerator_affineSpaceGenerator_of_affineLineGenerator` | proved over module alphabets, at `ℓ ≥ 1` where the paper states `s ≥ 2`. At `ℓ = 1` the affine space generator *is* the affine line generator and the conclusion is immediate, since the scaled error `(1 - 1/|F|)⁻¹ · ϵMCA` only exceeds `ϵMCA`; the proof covers that case uniformly |
| Thm 6.1 (MCA for **MDS** generators) | `LinearTransformations.isMCAGenerator_of_isMDSGenerator` | **sorried**. Stated over module codes, matching the paper's `Σ`-generality; the error depends on the code only through `n` and `δᵣ`, which is what lets it discharge the interleaved hypotheses of the tight tensor induction. The restricted-seed univariate instance is `PolynomialGenIsMCA.isMCAGenerator_univariatePowersGeneratorOn` |
| Thm 8.2 (polynomial generators, arbitrary linear codes) | `PolynomialGenIsMCA.isMCAGenerator_of_isPolynomialGeneratorOf` | proved **assuming only Thm 6.1**: the tensor stage is the sorry-free `isMCAGenerator_tensorGeneratorPi_tight`, so the open Lemma 4.4 is not on its path. Strengthenings over the paper: no `ℓ ≥ 2` hypothesis, and the `d = 0` factor case (skipped by the paper's proof) is proved via the vacuous-event argument |
| Lemma 9.3 (`G_d` for Reed–Solomon) | `RSCode.isMCAGenerator_univariatePowersGenerator` | **sorried**; needs the Guruswami–Sudan machinery |
| Thm 9.2 (polynomial generators, Reed–Solomon up to Johnson) | `RSCode.isMCAGenerator_of_isPolynomialGeneratorOfFull` | proved assuming Lemma 9.3 **and** the open printed Lemma 4.4 — the latter dependence mirrors a gap in the paper's own proof, see below |
| Lemma 10.1 (`ϵMCA(C^k) ≤ k · ϵMCA(C)`) | — | not formalized |

## Lemma 4.4: the printed statement is open

Lemma 4.4 assumes both generators have MCA for `C` and concludes error `ϵMCA + ϵ′MCA`. Its proof
splits the tensor event by the law of total probability and bounds Equation (5), whose clauses are

- `∀ i ∈ [ℓ]`, `(Σ_j G′(x′)_j u_{(i,j)})|_T ∈ C|_T`, and
- `∃ k ∈ [ℓ] × [ℓ′]`, `u_k|_T ∉ C|_T`,

by "ϵ′MCA(γ), the MCA error of G′". A single application of `G′`'s MCA at a fixed family does not
give this. The bad index `k = (i₀, j₀)` is determined by the event and so depends on the outer seed
`x′`, which means the family fed to `G′` is not fixed. Two ways out:

1. Apply `G′`'s MCA to the `ℓ`-fold interleaving `C^ℓ ⊆ (Σ^ℓ)ⁿ` with the family
   `w_j := (u_{(1,j)}, …, u_{(ℓ,j)})`. The `∀ i` clause is exactly membership in the interleaved
   projected code, `w` does not depend on `x′`, and the printed error is reached.
   → `TensorMCA.isMCAGenerator_tensorGenerator_of_moduleInterleavedCode`, hypothesis at the interleaving.
2. Union-bound over the `ℓ` rows, paying a factor `ℓ`.
   → `TensorMCA.isMCAGenerator_tensorGenerator`, hypothesis as printed, error
   `ϵMCA + ℓ · ϵ′MCA`.

`TensorMCA.isMCAGenerator_of_moduleInterleavedCode` shows form 1's hypothesis is a strengthening of
form 2's, so the two do not subsume one another. The printed statement itself is in-tree as the
sorried `LinearTransformations.isMCAGenerator_tensorGenerator_tight`.

That the printed error is *unreachable* from the printed hypothesis is not claimed and is not
known — no separation at equal error is exhibited here or in the paper. What is established is that
the paper's own argument does not reach it.

Closing the gap needs `ϵMCA(C^ℓ) ≤ ϵMCA(C)`, that interleaving costs nothing. Lemma 10.1 gives only
the factor `k`, and `ABF26` states the improvement as open immediately after its Lemma 4.7
(`ε_mca(C^≡t, δ) ≤ t · ε_mca(C, δ)`): *"It is an open question whether this bound is tight or can be
improved."* So a proof of Lemma 4.4 at the printed hypothesis and the printed error, by this route,
would resolve a stated open problem.

### Where the two headline theorems stand relative to the open lemma

BCGM25 invokes Lemma 4.4 twice, with different outcomes in-tree.

- **Thm 8.2** (polynomial generators) does **not** need it. The base MCA comes from Thm 6.1,
  whose error reads the code only through `n` and `δᵣ` (`mdsMCAError_congr`), both preserved by
  interleaving (`Code.minRelHammingDistCode_moduleInterleavedCode`). The δᵣ-anchored induction
  `isMCAGenerator_tensorGeneratorPi_tight` therefore discharges every interleaved hypothesis
  through the proved form 1, and `isMCAGenerator_of_isPolynomialGeneratorOf` reaches the paper's
  exact error with Thm 6.1 as its only sorried input.
- **Thm 9.2** (Reed–Solomon, list-decoding regime) genuinely needs it. The base MCA comes from
  Lemma 9.3, which is Reed–Solomon-specific: its proof constructs the Guruswami–Sudan polynomial
  `Q(X, Y, Z)` of `BCIKS20` Thm 5.1 and factors `disc*_Y(Q)`. The interleaving `RS^ℓ ⊆ (F^ℓ)ⁿ`
  is not a Reed–Solomon code, so the interleaved hypothesis is not available at error `ϵ′MCA`,
  and `isMCAGenerator_of_isPolynomialGeneratorOfFull` consumes the open
  `isMCAGenerator_tensorGenerator_tight` (via `isMCAGenerator_tensorGeneratorPiUnivariate`).

## A separate gap in the source

The proof of Thm 9.2 writes "By Lemma 9.3, `G_d` has mutual correlated agreement for any linear
code `C` with error `ϵMCA,RS,d`", but Lemma 9.3 is stated only for `RS[F, D, k]`. The parallel
sentence in the proof of Thm 8.2 ("for any `F`-linear code `C`") *is* justified, by Thm 6.1; the
Thm 9.2 one is not justified by the lemma it cites. Thm 9.2's printed error therefore does not
follow from its printed proof, independently of anything in the formalization. Were Lemma 9.3 in
fact alphabet-general, the interleaved hypothesis would be dischargeable there too.
