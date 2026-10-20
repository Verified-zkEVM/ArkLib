# NOZ26 §3.1 trace head audit

Maps the generic `F_{q^k}`-to-`R_q` transformation of Nguyen–O'Rourke–Zhang, *Hachi: Efficient
Lattice-Based Multilinear Polynomial Commitments over Extension Fields* (`NOZ26`, §3.1, "Reducing to
multilinear evaluation over `R_q`") onto `ArkLib/Commitments/Functional/Hachi/TraceHead/`, and
records its security shape. Checked against the ePrint version of 30 January 2026.

Declaration docstrings state what each declaration says; the correspondence to the paper lives here.

## Correspondence

Notation: `d = 2^α`, `k = 2^κ`, `H = ⟨σ₋₁, σ_{4k+1}⟩`, `B = R_q^H` (`fixedSubring α (2^κ)`).

| Paper (§3.1) | Lean | Notes |
|---|---|---|
| `f` over `B` in `ℓ` variables, coefficients `f_{i‖j}` | `unpackCoefficients … (extractedPoly … w)` | The scalar polynomial is the coefficientwise decoding of the committed ring polynomial's weak opening |
| Split `i ∈ {0,1}^{ℓ−α+κ}` retained, `j ∈ {0,1}^{α−κ}` packed | `Statement.xl ++ xh` retained, `Statement.xp` packed | The packed variables are the final `α − κ`, as in Eq. (10) |
| `F_i := ψ((f_{i‖j})_j)` | `packCoefficients (coefficientEquiv …)` | `coefficientEquiv` is `ψ` (`psiLinearEquiv`) reindexed by `Fin (2^(α−κ))` |
| `v := ψ((x^j)_j)` | `packedMonomial α κ hk s.xp` | |
| Message `Y := Σ_i x^i · F_i` | `honestMessage` | The ring evaluation of `F` at the retained point |
| Check `Tr_H(Y·σ₋₁(v)) = (d/k)·y` | `check` | The unnormalized equation; `isUnit_traceScale` cancels `d/k` |
| Remaining claim `F(x_retained) = Y` over `R_q` | `output`, into `relPolyEval` | Same commitment and weak opening |
| Theorem 2 (`ψ` bijective, trace pairing) | `psi_bijective`, `traceH_psi_mul_conj`, `psiLinearEquiv` | `traceH_eval_eq_iff` is Theorem 2 applied to Eq. (10) |
| Lemma 6 (`‖ψ(a)‖∞ ≤ 2β`) | `cInfNorm_psi_le` | Not used by the trace head, whose relations bound the ring opening directly |

## Shared packing layer

The production head computes over CompPoly's `CMlPolynomial`. Its read-back identity
`unpackCoefficients_eval` is proved directly (`packCoefficients_eval` and `evalSplit_eq_eval`),
and the protocol's `observation` is a `CheckedObservation` written by hand. The packing is also
stated in the `MvPolynomial`-based coordinate layer of `ProofSystem/RingSwitching/Packing/`,
reached through CompPoly's `CMlPolynomial.equivMvPolynomialDeg1` and the monomial-side evaluation
bridge `CMlPolynomial.eval_eq_eval_toMvPolynomial` (`ToCompPoly/Multilinear/Basic.lean`).

- **Packing data.** `traceHeadData e = PackingData.ofBaseOpening (Basis.ofEquivFun e.symm)`:
  the packing basis is `ψ` (at `e = coefficientEquiv …`) and the opening algebra is the fixed
  subring `B` with its one-element basis. The retained point is `B`-valued, so there is one
  opening coordinate (`ιE = Unit`), and the shared transpose of a family of opening values is its
  image under `ψ` (`traceHeadData_transpose`, conformance test).
- **Layout.** `traceHeadLayout e` instantiates the `ScalarHead.ClaimLayout` contract. Its
  components are the monomial-coefficient rows of the final `α − κ` variables (`coefficientRows`,
  column `j` of `toMatrix`), transported to `MvPolynomial`, and its weights are the monomial basis
  at `xp`. Its `reconstruct` is Hachi's own proof, from `evalSplit_eq_eval` and the evaluation
  bridge. This is the faithful split: NOZ26 applies `ψ` to monomial coefficients. The
  Boolean-restriction `packedSuffixLayout` is a different split and is not used.
- **Packed polynomial.** `toMvPolynomialDeg1_packCoefficients`: under the equivalence,
  `packCoefficients e f` is the shared `(traceHeadData e).packedMLE ((traceHeadLayout
  e).components f)`, proved from `unpack_coeff` and `packedMLE_unpack`. In the conformance test,
  `toMvPolynomialDeg1_eq_packedMLE` states the same for the decoding of any ring polynomial, in
  particular the committed one.
- **Conformance theorem.** `traceHead_conforms`
  (`ArkLibTest/ProofSystem/RingSwitching/Conformance/Hachi.lean`) states the head's accepting
  condition through the shared layer: `check ∧ relPolyEval(output)` holds iff the weak opening is
  valid, the sent value `Y` is the single slice of the shared `packedMLE` of the layout's
  components of the decoded committed polynomial in the shared `sliceRel` at the retained point,
  and the claimed scalar is `∑ j, traceHeadLayout.weight j · ψ⁻¹(Y) j`. It is assembled from
  `output_mem_relPolyEval_iff_sliceRel`, `check_iff_layout_weight`, `eval_eq_iff_sliceRel` (through
  the shared `openingClaimRel_iff_sliceRel`) and `openingClaimRel_unpackCoefficients_iff` (through
  `packedMLE_eval_embedded`).
- **Exercised part.** Hachi §3.1 exercises only the packing, evaluation and opening part of the
  shared layer (one opening coordinate, no batching, multiplier or sumcheck), as in the paper, so
  its reuse is small at the proof level and real at the statement level. The
  `RingSwitchingProfile` layer does not apply (carrier `L` itself).

## Departures

- **No field hypothesis.** The paper works over `R_q^H ≅ F_{q^k}` (Lemma 5, `q ≡ 5 mod 8`). The
  trace head uses the fixed subring as a ring, assuming only `2 ≠ 0` in `ZMod q` and `2k ∣ d`;
  nothing in `TraceHead/` depends on `fixedSubring_isField`. Reading it as an `F_{q^k}` statement is
  Lemma 5.
- **Weak opening.** The relations carry Hachi's `VerifiedOpening` with the same `βSq`, `γ` and norm
  bound on both sides; `relScalarEvalMsgShort` adds the honest committer's message norm bound, and
  completeness and soundness hold for it as well.
- **Not covered.** §3.2 (base-field coefficients and partial evaluations) and §4.5's recursion
  handoff. `Recursion/TraceHandoff.lean` describes a trace guard of the same kind over the next
  ring; its `traceCheck` is still `sorry`.

## Paper erratum

Before the displayed equation that turns Eq. (10) into the check, p. 13 says "for every `x ∈ R_q^H`
we have `Tr_H(x) = x`". For `|H| > 1` this is false: an `H`-fixed `x` has `Tr_H(x) = |H|·x =
(d/k)·x`. The displayed equation, with its factor `d/k`, is correct, and so is the check. The Lean
proof derives the check from Theorem 2 (`traceH_psi_mul_conj`) and does not use the misstated step.

## Security shape

- **Completeness:** `traceHeadReduction_perfectCompleteness`, and
  `traceHeadReduction_perfectCompleteness_msgShort` at the message-bounded relations, from every
  initial state.
- **Soundness:** zero-challenge coordinate-wise special soundness
  `traceHeadVerifier_coordinateWiseSpecialSoundWith` from `relScalarEval` to `relPolyEval`, and the
  message-bounded variant, both instances of
  `traceHeadVerifier_coordinateWiseSpecialSoundWith_of_output`. The extractor returns the weak
  opening of the single leaf. The content is `mem_relScalarEval_of_output`: the shared
  `CheckedObservation.readback` applied to the trace check. `ψ`'s invertibility, which the paper
  calls crucial for knowledge soundness, enters through `coefficientEquiv`.
- **Escape:** the certificate is stated at the plain relations and carries no escape event. The
  verifier aborts on a failed check (`failure`), so rejection is absorbing. `traceHeadPackage`
  composes in front of `bridgePackage ▷ quadEvalPackage` with no adapter, and the composite starts
  at `relScalarEval` and ends at the evaluation step's output relation
  (`ArkLibTest/Commitments/Functional/Hachi/TraceHead/Composition.lean`). The composite carries the
  evaluation step's own escape event.
- **Non-vacuity:** `ArkLibTest/ProofSystem/RingSwitching/Conformance/Hachi.lean` states the
  accepting condition through the shared layer (`traceHead_conforms`) and the exact correspondence
  `check ∧ relPolyEval(output) ↔ relScalarEval ∧ Y = honestMessage` (`traceHead_accepts_iff`).
  At `q = 5`, `d = 2`, `k = 1`, through `traceHead_conforms`, it exhibits a nonconstant polynomial
  on the honest side and shows that, for a false claim, no sent ring value satisfies the
  shared-layer condition against the same weak opening. Its opening-relation fixtures accept
  exactly `ψ⁻¹` of the ring evaluation (`openingClaimRel_iff_honest`), reject the claimed values
  `0`, and accept the rows' constant coefficients `(1, 3)` of `1 + 2X + 3Y + 4XY` in order, so a row
  swap would be caught. `ArkLibTest/Commitments/Functional/Hachi/TraceHead/ProperSubring.lean`
  repeats the honest and false-claim instances at `d = 8`, `k = 2`, where the exponent of `σ₉` is
  not `1` modulo `2d`; its data are base-field numerals, so it does not compute `σ₉` on an element
  outside `ZMod q`. The check alone does not reject a false claim: for the claim `0`, the message
  `0` passes it (`zero_message_passes_check`). `RubberStamp.lean` shows that deleting the check
  breaks coordinate-wise special soundness with the head's own extractor `traceHeadExtractor`.
- **Axioms:** completeness, soundness and the committer coverage depend only on `propext`,
  `Classical.choice` and `Quot.sound`.
