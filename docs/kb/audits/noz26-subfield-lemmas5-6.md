# NOZ26 Lemmas 5–6: Subfield and Packing-Norm Audit

This page compares Hachi [NOZ26, §3, Lemmas 5–6] with the current ArkLib subfield
formalization. It was revalidated against the January 30, 2026 artifact and the working tree on
**30 July 2026**.

## Outcome

The formalization is coherent as a whole, but its proof status is asymmetric:

- **Lemma 5 is represented faithfully but is not unconditionally proved.** The fixed subring,
  its Eq. (7) coefficient structure, its cardinality `q^k`, and the assembly from the
  conjugation-fixed field to `R_q^H ≃ F_{q^k}` are present. The final field/isomorphism
  declarations depend on one explicit `sorry`, `no_selfReciprocal_factor`.
- **Lemma 6 is fully proved.** `cInfNorm_psi_le` has no `sorryAx` dependency and establishes the
  paper's `‖ψ(a)‖∞ ≤ 2β` with the same centered coefficient norm convention.
- Lemma 6 does **not** rely on the unfinished field upgrade in Lemma 5. It needs the proved
  fixed-subring support/cardinality layer and the packing map, so the current dependency graph
  is mathematically and formally sensible.

## Correspondence

| Paper item | Lean declaration(s) | Status | Notes |
|---|---|---|---|
| `R_q = Z_q[X]/(X^d+1)`, `d=2^α` | `powTwoCyclotomic`, `Rq` | proved | Same negacyclic ring and dimension convention. |
| `H = ⟨σ_{-1}, σ_{4k+1}⟩` | `conjAut`, `genAut`, `Hexp` | proved | `Hexp` is an explicit exponent `Finset`, not a bundled subgroup. |
| `R_q^H` | `fixedSubring α k` | proved | Defined by the equalizers of the two generators; fixedness under all of `H` is recovered separately. |
| Eq. (7), `k` free base-field coefficients | `vElt`, `fixedBasisMap`, `fixedSubring_coeff_eq_zero` | proved | Uses a symmetric basis, reindexed relative to the displayed paper formula. |
| `|R_q^H| = q^k` | `card_fixedSubring_eq` | proved, `sorryAx`-free | This cardinality result does not use the open field proof. |
| `R_q^H` is a field | `fixedSubring_isField` | conditional | Depends transitively on `no_selfReciprocal_factor`. |
| `R_q^H ≃ F_{q^k}` | `fixedSubringEquivGaloisField` | conditional | Adds the proved cardinality computation and finite-field uniqueness to the conditional field result. |
| Theorem 2 packing map `ψ` | `psi`, `psi_bijective` | proved, `sorryAx`-free | Included because Lemma 6 refers to this `ψ`. |
| Lemma 6, `‖ψ(a)‖∞ ≤ 2β` | `cInfNorm_psi_le` | proved, `sorryAx`-free | Each output coefficient receives contributions from at most two input coefficients. |

## Assumptions and notation

The paper assumes a prime `q ≡ 5 (mod 8)`, `d` a power of two, and `k ≥ 1` dividing `d/2`.
ArkLib writes `d = 2^α` and the subfield degree as `k = 2^κ`, with divisibility hypothesis
`2 * 2^κ ∣ 2^α`. This is not a restriction in the paper's setting: every positive divisor of
the power of two `2^{α-1}` is itself a power of two.

The final Lemma 5 field result uses `q % 8 = 5`. Lemma 6 is more general: its proof only assumes
`(2 : ZMod q) ≠ 0`, plus primality through the surrounding `ZMod q` setup and the same
divisibility condition. This weakening is compatible with the artifact because `q ≡ 5 (mod 8)`
implies odd characteristic.

ArkLib's norm is the maximum centered coefficient magnitude, using `ZMod.valMinAbs`, and its
vector norm is the maximum of that norm over entries. This matches the artifact's `mod± q`
coefficient convention and the vector `ℓ∞` norm used in Lemma 6.

## Why Lemma 6 is independent of the Lemma 5 gap

The proof of `cInfNorm_psi_le` follows the artifact's Eq. (9) observation in an explicit form:

1. `fixedSubring_coeff_eq_zero` confines each input entry to the Eq. (7) support positions.
2. `packExp_mod_eq` identifies which packed indices can contribute to an output coefficient.
3. `eq_or_eq_of_mod_eq` shows that there are at most two such indices, one from each half of
   Eq. (8).
4. The centered-representative triangle inequality bounds their signed sum by `2β`.

The support theorem is obtained from the proved cardinality and basis results. None of these
steps invokes `fixedSubring_isField` or `fixedSubringEquivGaloisField`.

## Remaining code-level work

Completing Lemma 5 requires proving `no_selfReciprocal_factor` in
[`Subfield/Field.lean`](../../../ArkLib/Data/Lattices/CyclotomicRing/Subfield/Field.lean). It must
show that reversal swaps, rather than preserves, the two irreducible factors of
`X^{2^α}+1` when `q ≡ 5 (mod 8)`. The file already proves the relevant order and
`−1 ∉ ⟨q⟩` facts and documents a root-orbit proof plan.

No code change is indicated for Lemma 6.

## Validation evidence

The imported subfield umbrella builds. A `#print axioms` audit reports:

- `fixedSubringEquivGaloisField`: includes `sorryAx`;
- `cInfNorm_psi_le`: only standard axioms (`propext`, `Classical.choice`, `Quot.sound`);
- `card_fixedSubring_eq` and `psi_bijective`: only those same standard axioms.
