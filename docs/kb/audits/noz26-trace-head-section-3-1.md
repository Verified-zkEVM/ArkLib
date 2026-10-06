# NOZ26 §3.1 trace head audit

Maps the generic `F_{q^k}`-to-`R_q` transformation of Nguyen–O'Rourke–Zhang, *Hachi: Efficient
Lattice-Based Multilinear Polynomial Commitments over Extension Fields* (`NOZ26`, §3.1, "Reducing
to multilinear evaluation over `R_q`") onto `ArkLib/Commitments/Functional/Hachi/TraceHead/`, and
records its security shape. Checked against the ePrint version of 30 January 2026.

Declaration docstrings state what each declaration says; the correspondence to the paper lives
here.

## Correspondence

Notation: `d = 2^α`, `k = 2^κ`, `H = ⟨σ₋₁, σ_{4k+1}⟩`, `B = R_q^H` (`fixedSubring α (2^κ)`).

| Paper (§3.1) | Lean | Notes |
|---|---|---|
| `f` over `B` in `ℓ` variables, coefficients `f_{i‖j}` | `unpackCoefficients … (extractedPoly … w)` | The scalar polynomial is the coefficientwise decoding of the committed ring polynomial's weak opening |
| Split `i ∈ {0,1}^{ℓ−α+κ}` retained, `j ∈ {0,1}^{α−κ}` packed | `Statement.xl ++ xh` retained, `Statement.xp` packed | The packed variables are the final `α − κ`, as in Eq. (10) |
| `F_i := ψ((f_{i‖j})_j)` | `packCoefficients (coefficientEquiv …)` | `coefficientEquiv` is `ψ` (`psiLinearEquiv`) reindexed by `Fin (2^(α−κ))` |
| `v := ψ((x^j)_j)` | `packedMonomial α κ hk s.xp` | |
| Message `Y := Σ_i x^i · F_i` | `honestMessage` | The ring evaluation of `F` at the retained point |
| Check `Tr_H(Y·σ₋₁(v)) = (d/k)·y` | `check` | Exactly the unnormalized equation; `isUnit_traceScale` cancels `d/k` |
| Remaining claim: `F(x_retained) = Y` over `R_q` | `output`, into `relPolyEval` | Same commitment and weak opening |
| Theorem 2 (`ψ` bijective, trace pairing) | `psi_bijective`, `traceH_psi_mul_conj`, `psiLinearEquiv` | `trace_eval_eq_iff` is Theorem 2 applied to Eq. (10) |

## Departures

- **No field hypothesis.** The paper works over `R_q^H ≅ F_{q^k}` (Lemma 5, `q ≡ 5 mod 8`). The trace
  head uses the fixed subring as a ring, assuming only `2 ≠ 0` in `ZMod q` and `2k ∣ d`; nothing in
  `TraceHead/` depends on `fixedSubring_isField`. Reading it as an `F_{q^k}` statement is Lemma 5.
- **Weak opening.** The relations carry Hachi's `VerifiedOpening` with the same `βSq`, `γ` and norm
  bound on both sides; `relInMsgShort` adds the honest committer's message norm bound and
  completeness holds for it as well.
- **Not covered.** §3.2 (base-field coefficients and partial evaluations) and §4.5's recursion
  handoff, whose trace guard (`Recursion/TraceHandoff.lean`) states the same check over the next
  ring and remains `sorry`.

## Security shape

- **Completeness:** `perfectCompleteness`, and `perfectCompleteness_msgShort` at the message-bounded
  relations, from every initial state.
- **Soundness:** zero-challenge coordinate-wise special soundness `coordinateWiseSpecialSoundWith`
  from `relIn` to `relPolyEval`. The extractor returns the weak opening of the single leaf; the
  content is `mem_relIn_of_output`, the shared `CheckedObservation.readback` applied to the trace
  check. `ψ`'s invertibility, which the paper calls crucial for knowledge soundness, enters through
  `coefficientEquiv`.
- **Escape:** the certificate is stated at the plain relations, with no `withEscape` widening, so the
  escape-vacuity pattern of the composed opening chain does not apply to it. The verifier aborts on a
  failed check (`failure`), so rejection is absorbing. A composition of `package` with an
  escape-carrying downstream package inherits that package's escape event.
- **Non-vacuity:** `ArkLibTest/ProofSystem/RingSwitching/Conformance/Hachi.lean` proves the exact
  correspondence `check ∧ relPolyEval(output) ↔ relIn ∧ Y = honestMessage` from the shared
  checked-observation laws. Over `q = 5`, `α = 1`, `κ = 0` it exhibits a nonconstant polynomial on
  the honest side and shows a false claim is rejected for every sent ring value.
- **Axioms:** completeness, soundness, the committer coverage and the packing data depend only on
  `propext`, `Classical.choice` and `Quot.sound`.
