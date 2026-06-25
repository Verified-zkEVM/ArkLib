/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.Basis
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.Packing
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.TraceVanishing
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.TraceInnerProduct
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.Cardinality
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.Bijectivity
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.Factorization
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.Field
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.NormBound

/-!
# Hachi §3 in Lean: the Subfield Layer of `R_q` (Lemma 5, Theorem 2, Lemma 6)

Aggregator for the formalization of Hachi [NOZ26, §3] ("Evaluation Claims over Extension
Fields as Relations over `R_q`"), covering the subfield `R_q^H ⊆ R_q`, the packing map
`ψ : (R_q^H)^{d/k} → R_q`, the trace identity, and the norm bound. Throughout, `d = 2^α` is
the ring dimension of `R_q = Z_q[X]/(X^d + 1)` and `k = 2^κ` is the subfield degree.

## Correspondence with the paper

Prerequisites, from `CyclotomicRing/Galois/`:

* **`σ_i : X ↦ X^i`, `i ∈ Z×_{2d}`** (the Galois automorphisms, [NOZ26, §2.1]) —
  `galoisAut` (computable action), `galoisAutₛ` (semantic, on the quotient), `galoisRingHom`
  (bundled), in `Galois/Automorphism.lean`.
* **The generators `σ_{-1}`, `σ_{4k+1}` of `H`** — `conjExp`/`conjAut` (`σ_{-1}`, represented
  by the positive exponent `2^{α+1} − 1 ≡ −1 (mod 2d)`) and `genExp`/`genAut` (`σ_{4k+1}`),
  in `Galois/Group.lean`.
* **`H = ⟨σ_{-1}, σ_{4k+1}⟩` with `|H| = d/k`** — `Hexp` (the exponent set
  `{±(4k+1)^a mod 2d : a < d/2k}`), `Hexp_card`, `Hexp_odd_mem`, `Hexp_generator_smul`,
  in `Galois/Group.lean`.
* **`Tr_H(a) := Σ_{σ∈H} σ(a)`** — `traceH` (computable counterpart: `traceHComp`); that
  `Tr_H` lands in `R_q^H` (the paper's codomain) is `traceH_mem_fixed`, in `Galois/Trace.lean`.
* **`R_q^H := {x ∈ R_q : ∀ σ ∈ H, σ(x) = x}`** — `fixedSubring` (and `conjFixedSubring` for
  the single generator `σ_{-1}`), in `Galois/FixedSubring.lean`.

The Section 3 results:

* **Lemma 5, Eq. 7** (`|R_q^H| = q^k`, via the symmetric basis) — `vElt`
  (`X^{(d/2k)j} + σ_{-1}(X^{(d/2k)j})`, the Eq. 7 family up to the reindexing `j ↦ k − j`),
  `vElt_coeff` in `Subfield/Basis.lean`; `fixedBasisMap`, `card_fixedSubring_eq` in
  `Subfield/Cardinality.lean`.
* **Lemma 5** (`R_q^H` is a subfield `≅ F_{q^k}`) — `fixedSubring_isField`,
  `fixedSubringEquivGaloisField` in `Subfield/Field.lean`; the `q ≡ 5 (mod 8)` number theory
  (`orderOf_q_eq`, `neg_one_notMem_powers_q`, `cyclotomic_card_normalizedFactors`) in
  `Subfield/Factorization.lean`.
* **Theorem 2, Eq. 8** (the packing map `ψ`) — `packExp`, `psi` in `Subfield/Packing.lean`.
* **Theorem 2, Claim 1** (`⟨4k+1⟩ = {4k·α + 1 : α < d/2k}`, order `d/2k`) — `four_pow_injOn`
  in `Galois/Order.lean`, `Hexp_card` in `Galois/Group.lean`, `four_pow_i_reindex` in
  `Subfield/TraceVanishing.lean`.
* **Theorem 2, Claim 2** (`Tr_H(X^i) = 0` when `d/2k ∤ i`) — `traceH_Xpow_eq_zero` in
  `Subfield/TraceVanishing.lean`.
* **Theorem 2, Claim 3** (`Tr_H(X^{d/2}) = 0`) — `traceH_Xpow_half`, generalized to all odd
  multiples of `d/2` by `traceH_Xpow_neg_one_sq`, in `Subfield/TraceVanishing.lean`.
* **Theorem 2, trace formula** (`Tr_H(ψ(a)·σ_{-1}(ψ(b))) = (d/k)·⟨a,b⟩`) — `traceH_kernel`
  (the monomial kernel `(d/k)·[p = q]`) and `traceH_psi_mul_conj` in
  `Subfield/TraceInnerProduct.lean`.
* **Theorem 2, `ψ` is a bijection** — `psi_injective` in `Subfield/TraceInnerProduct.lean`,
  `psi_bijective` in `Subfield/Bijectivity.lean`.
* **Lemma 6** (`‖ψ(a)‖∞ ≤ 2β`) — `cInfNorm_psi_le` in `Subfield/NormBound.lean`.

## Deviations from the paper

* **`R_q^H` via generator equalizers.** The paper defines `R_q^H` as the elements fixed by
  *every* `σ ∈ H`; `fixedSubring` uses the equalizers of the two *generators* (equivalent,
  since fixedness is closed under composition — `galoisAut_fixed_of_mem` recovers the
  all-of-`H` direction). This yields a `Subring` directly from Mathlib's `RingHom.eqLocus`.
* **`H` as an explicit exponent set.** `H` is not formalized as a `Subgroup`; `Hexp`
  enumerates it extensionally as `{±(4k+1)^a mod 2d : a < d/2k}` (justified by Claim 1).
  The group facts used downstream are `Hexp_card` (`|H| = d/k`) and `Hexp_generator_smul`
  (translation invariance, which is what makes `Tr_H` land in `R_q^H`).
* **Claim 2 geometric sum.** `Σ_{j<d/2k}(X^{4ki})^j = 0` is closed via `X^{4ki} − 1` being a
  *unit* (`Xpow_sub_one_isUnit`, `geom_sum_eq_zero_of_isUnit`).
* **Claim 3 generalized.** `traceH_Xpow_neg_one_sq` proves `Tr_H(X^j) = 0` for *every* `j`
  with `X^{2j} = -1` (odd multiples of `d/2`), not just `j = d/2`: the packed kernel
  `traceH_kernel` pairs indices across the two halves of `Fin (d/k)`, where exponent
  differences `≡ ±d/2` arise; the paper handles the same cases as four separate double sums.
* **Exponents in `ℕ`.** Claim 2's `i ∈ ℤ` becomes `i : ℕ` (exponents are `2d`-periodic,
  `Xpow_periodic`), and `σ_{-1}` is represented by the positive exponent
  `conjExp = 2^{α+1} − 1`.
* **Hypotheses.** The paper's "`k ≥ 1` divides `d/2`" is `2 * k ∣ 2^α`; the explicit
  "`k` is a power of two" (`hk2pow`) is recorded although automatic for divisors of
  `2^{α-1}`. The blanket `q ≡ 5 (mod 8)` is demanded only where genuinely needed (the field
  structure, `Subfield/Field.lean` / `Subfield/Factorization.lean`); the trace formula,
  bijectivity, and cardinality need only `(2 : R) ≠ 0` (i.e. `q` odd) — slightly more
  general than the paper.
* **`ψ`-injectivity via the trace pairing.** The paper proves injectivity by the coefficient
  analysis of Eq. 9; the formal proof tests against basis vectors through the (already
  proven) trace formula and closes bijectivity by the cardinality match. Eq. 9's coefficient
  analysis instead underlies `vElt_coeff` and the Lemma 6 proof plan.

## Open items (`sorry`)

* `no_selfReciprocal_factor` (`Subfield/Field.lean`) — reversal swaps the two irreducible
  factors of `X^d + 1`. Everything downstream of it in the Lemma 5 chain is proven.
* `cInfNorm_psi_le` (`Subfield/NormBound.lean`) — Lemma 6; statement formalized, proof plan
  in its docstring.

## File map

* `Subfield/Basis.lean` — monomials `X^i`, the `X^d = -1` folding toolkit, the `Fintype`
  instance and `|R_q| = q^{2^α}`, and the symmetric basis `vElt` with its triangular
  coefficient formula (Eq. 7).
* `Subfield/Packing.lean` — the packing map `ψ` (Eq. 8) and its additivity.
* `Subfield/TraceVanishing.lean` — the trace-of-monomial vanishing identities (Claims 2, 3).
* `Subfield/TraceInnerProduct.lean` — the trace formula
  `Tr_H(ψ(a)·σ_{-1}(ψ(b))) = (d/k)·⟨a,b⟩` and the injectivity of `ψ`.
* `Subfield/Cardinality.lean` — `|R_q^H| = q^k` (Eq. 7) from the symmetric basis.
* `Subfield/Bijectivity.lean` — `ψ` is a bijection (Theorem 2).
* `Subfield/Factorization.lean` — `X^{2^α}+1 = Φ_{2^{α+1}}` has exactly two irreducible
  factors over `Z_q` for `q ≡ 5 (mod 8)`; `orderOf q = 2^{α-1}` and `−1 ∉ ⟨q⟩`.
* `Subfield/Field.lean` — `R_q^H` is a field isomorphic to `F_{q^k}` (Lemma 5).
* `Subfield/NormBound.lean` — the norm bound `‖ψ(a)‖∞ ≤ 2β` (Lemma 6).

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/
