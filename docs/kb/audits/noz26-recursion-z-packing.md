# NOZ26 §4.5 recursion: the `Z`-packing step

Records why ArkLib's Hachi development stops at one iteration closed by an end piece
(`hachiNonrecursive`) and does not formalize the recursive opening of Nguyen–O'Rourke–Zhang,
*Hachi: Efficient Lattice-Based Multilinear Polynomial Commitments over Extension Fields*
(`NOZ26`, §4.5, and the generic form in §3.2). Checked against the ePrint version of 30 January
2026.

## Where the recursion starts

One iteration of the opening (`Hachi/Composition.lean`, `iteration`) ends in the claim
`relWEvalClaim`: the lifted table `w̃`, with entries in `Z_q`, is committed by `t`, is short, and its
multilinear extension evaluates to `y′` at `a`. The point `a` has coordinates in the extension field
`F = F_{q^k}` with `k = 2^κ`. The recursion turns this claim into the input of the next
iteration's `QuadEval` over a smaller ring `R′`, in three steps:

1. **Partial evaluation (Eq. (24)).** Split `a = (a₀, a₁)` with `a₁ ∈ F^κ`. For each
   `i ∈ {0,1}^κ` let `pᵢ` be the evaluation at `a₀` of the slice `j ↦ w̃_{j‖i}`. Then
   `y′ = Σᵢ eq(i, a₁)·pᵢ`. The prover sends claimed values `yᵢ` for `i ≠ 0`, and the verifier
   derives `y₀` from `y′ = Σᵢ eq(i, a₁)·yᵢ`.
2. **`Z`-packing (Eqs. (25)–(26)).** With `1, Z, …, Z^{k−1}` a basis of `F` over `Z_q`, pack the
   slices into one `F`-valued table `ŵⱼ := Σᵢ w̃_{j‖i}·Z^i` and replace the `2^κ` claims by one:
   `Σⱼ ŵⱼ·eq(j, a₀) = Σᵢ yᵢ·Z^i`.
3. **Trace handoff (Eqs. (27)–(28)).** Map the `F`-valued table into `R′` with the bijection `ψ`
   of Theorem 2, send the packed evaluation `p ∈ R′`, check a trace equation, and continue with
   `QuadEval` over `R′` on the same commitment `t` read at the new ring dimension.

Steps 1 and 3 support extraction: from per-slice claims the input claim follows by multilinear
splitting, and the trace equation determines the packed value exactly. Step 2 does not.

## The gap

Extraction through step 2 needs the converse of the packing: the single packed claim should
determine every per-slice claim `pᵢ = yᵢ`. It would if the `pᵢ` and `yᵢ` were in `Z_q`, because
they are then the coordinates of `Σᵢ yᵢ·Z^i` in the basis `Z^i`. Since `a₀` has coordinates in `F`, however, the
partial evaluations are full `F`-elements, and the packed claim fixes only one `F`-linear
combination `Σᵢ Z^i·(pᵢ − yᵢ) = 0` of the `2^κ` defects. For `κ ≥ 1` this equation has nonzero
solutions.

**Counterexample (`κ = 1`).** Let `a = (a₀, a₁)` and let `p₀, p₁` be the true partial evaluations,
so the true value is `v = (1 − a₁)·p₀ + a₁·p₁`. A prover who wants to open to `v + Δ` picks `δ`
with `δ·((1 − a₁)·Z − a₁) = Δ`, which is possible whenever `a₁ ≠ Z/(1 + Z)`, and sends
`y₁ := p₁ − δ`. The verifier derives `y₀ = p₀ + Z·δ`. Then

- the derivation identity holds by construction, so step 1 accepts the claimed value `v + Δ`;
- the packed right-hand side is `y₀ + Z·y₁ = p₀ + Z·p₁`, the true packed evaluation, so steps 2
  and 3 and the next iteration prove a true statement with the honest witness.

The prover therefore opens `t` to an arbitrary value, except at one value of the sumcheck
challenge `a₁`. The formalization's relation-level statement of step 2's extraction
(`relHatEval ⊆` pull-back of `relPartialEval`) is false for the same reason.

We have not checked whether some other part of the paper's full argument constrains the `yᵢ`;
as written in §4.5 and §3.2, the packing step alone does not.

## Candidate repairs

Both change the protocol, which is why the recursion is not formalized until one is chosen:

- add a challenge that batches the peeled index before packing, so the slices are combined with
  verifier randomness rather than the fixed basis `Z^i`;
- replace the peeling with the generic §3.1 packing, which reads `F_{q^k}` coefficients directly
  (Figure 2, first row), at the cost of `κ` extra variables and a sparser reinterpretation of the
  commitment.

A recursive Hachi-style opening is also expected from the checkpoint extraction of Akita
(ePrint 2026/1983), tracked in ArkLib issue #1378.
