# Ring Switching

This page is the KB landing page for the **ring-switching** technique and ArkLib's generic
formalization of it.

## Scope

Use this page when a question is about:

- what ring switching is and why a polynomial commitment scheme uses it;
- the `RingSwitchingProfile` abstraction and how a protocol family instantiates it;
- where Binius plugs in, and how Hachi (and other small-ring/large-ring PCS work) would;
- which security statements are generic vs. instance-specific.

## The idea

Ring switching reduces a multilinear evaluation claim `s = t(r)` over a **small** coefficient ring
`B` (a binary-tower field, `𝔽₂`, or a cyclotomic ring `R_q`) to an evaluation claim over a **large**
extension `L` and **without re-committing** over `L`. Field instances such as Binius pay only an
additive `O(1/|L|)` soundness cost; Hachi's cyclotomic-ring instance has a separate CWSS-style
soundness theorem because `R_q` is not a domain. This lets a PCS commit cheaply over a tiny ring
while running sum-check and the final opening over a carrier large enough for the intended
soundness argument.

With `ℓ = ℓ' + κ`, a small-field multilinear `t` in `ℓ` variables is *packed* into a large-field
multilinear `t'` in `ℓ'` variables (`packMLE`): each block of `2^κ` coefficients becomes one
`L`-element via a `B`-basis `β` of `L`. The interaction runs in a *pack/trace carrier* `A` where the
folded element `ŝ` lives; an eq̃/trace inner-product identity (DP24 §2.5) ties `ŝ`'s coordinates to
the original claim and the new sum-check target.

## ArkLib's abstraction

ArkLib formalizes ring switching **once**, generic over a `RingSwitchingProfile (B L) κ`:

- `basis`, carrier `A`, embeddings `φ₀`/`φ₁ : L →+* A`, coordinate maps `decomposeRows`/`Columns`,
- plus two **reconstruction laws** (`decomposeRows_spec`, `decomposeColumns_spec`) that tie the
  coordinate maps to `φ₀`/`φ₁`/`basis` and rule out law-free profiles.

Those laws are the algebraic profile boundary, not a complete soundness theorem by themselves.
The batching/sum-check proofs still have to connect the profile coordinates to `packMLE`,
`embedded_MLP_eval`, `compute_A_func`, and the instance's eq̃/trace identity.

The protocol is three phases (batching → sum-check → large-field IOPCS opening); see the blueprint
section *Ring Switching* (`blueprint/src/proof_systems/ring_switching.tex`) for the protocol and
security statements. The RBR knowledge error is `κ/|L| + Σ 2/|L| + 1/|L| + ε_IOPCS` (DP24 §3.1–3.2),
and soundness requires `[IsDomain L]` (Schwartz–Zippel).

## Instances

- **Binius** (`binaryTowerProfile`): `A = L ⊗_K L`, `φ₀ = ·⊗1`, `φ₁ = 1⊗·`, coordinates from the
  left/right `L`-module bases; the two laws are **proven** in ArkLib.
- **Hachi** ([`../papers/NOZ26.md`](../papers/NOZ26.md)): `L = R_q`, `A = R_q`, `φ₀ = id`,
  `φ₁ = σ₋₁`, `β = ψ` (Theorem 2). `R_q` is not a domain, so the Schwartz–Zippel soundness theorem
  does not apply — Hachi soundness is a separate (CWSS) argument.

## The Generic layer (`ProofSystem/RingSwitching/Generic/`)

A second-generation abstraction, intended to eventually subsume `RingSwitchingProfile` (which it
leaves untouched during migration). It generalizes from the tower case to **decoupled**
packing/opening algebras: the committed dense polynomial lives over a packing algebra `P`,
evaluation claims arrive over an opening algebra `E`, and `P`, `E` are *unrelated* free
`B`-algebras with chosen bases (`packBasis`, `openBasis`) — following Flock's Appendix B
(the Φ/matrix-branching-program formulation, [BRW26]) and the "Ring switching, generalized" note
([RSG]); DP24 tower switching is the special case `P = E = L`.

**The seven-step spine** every ring switch shares (docstrings cite these step numbers):
(1) pack the family `P_packed = ∑ᵢ Pᵢ·bᵢ^P`; (2) the fixed input claim `∀ i, αᵢ = P̂ᵢ(r)`;
(3) eq-decompose `A(y,u) = openBasis.repr (eq̃(r,y)) u` over `B`; (4) recombine the slices over
the packing basis; (5) batch the claims with random weights; (6) sum-check; (7) evaluate `B̂(r')`
(an efficiency refinement, off the soundness path).

**Safety pillars** (referenced as "pillar 1–4"): (1) every coordinate map / bridge is *derived
from a bundled `Basis`* (`Basis.repr`, `Basis.constr`) — an instance has no law-free lever;
(2) commitment binding flows through the PCS's own `commitsTo`, not a free hook; (3) packing
correctness is proven once, generically; (4) no free `Prop` in the relation chain — the input
relation is the fixed evaluation anchor of step (2). The carrier also structurally requires
`Nontrivial P`/`Nontrivial E` (an honest *empty* basis would otherwise admit a degenerate carrier
that collapses the anchor).

**Status (proven, sorry-free, axiom-clean):**

- [`Carrier.lean`](../../../ArkLib/ProofSystem/RingSwitching/Generic/Carrier.lean) —
  `RingSwitchCarrier` + derived `packedMLE`/`eqCoord`/`bridge`/`Bmult` and the linchpin
  `bridge_eqTilde` (`Φ(eq̃(r,y)) = ∑ᵤ A(y,u)·weight u`, Flock Claim 6's expansion); tower and
  decoupled instances.
- [`Packing.lean`](../../../ArkLib/ProofSystem/RingSwitching/Generic/Packing.lean) —
  `packedMLE_eval` (reassembly at base-embedded points — the only well-typed generic form, and
  sufficient: the papers use the family decomposition only at hypercube points) and
  `packMLE_eq_packedMLE_curry`, the *Binius-stability bridge* (label "R2"): DP24's rank-`2^κ`
  `packMLE` is the generic packing of the curried family.
- [`Batching.lean`](../../../ArkLib/ProofSystem/RingSwitching/Generic/Batching.lean) —
  `BatchingStrategy P W` (`[CommRing P]`-only vocabulary) with **proven** instances `gammaPowers`
  (γ-powers, any claim count, error `e/|P|`, [RSG]) and `eqFold` (eq-indicator folding over
  `{0,1}^κ`, error `κ/|P|`, [BRW26] App. B), both Schwartz–Zippel over `[IsDomain P] [Fintype P]`;
  `reindex` transports a strategy along `W' ≃ W`. Also the decoupled *field* carrier `𝔽₄ ≠ 𝔽₈`
  (label "R5": the `[IsDomain]`-gated layer exercised off-Binius).
- [`Recombine.lean`](../../../ArkLib/ProofSystem/RingSwitching/Generic/Recombine.lean) —
  `recombine_bijective`/`recombine_injective`: the packing-basis recombination `s ↦ ∑ᵢ sᵢ•bᵢ^P`
  is `packBasis.equivFun.symm`, hence bijective — Flock Remark 5's fix-side property ("naive
  recombination is complete but not sound") — plus `openingDecomposition_injective`, Remark 5's
  opening half (uniqueness of `B`-coordinates in `openBasis`). Both are one-liners over the
  reusable `Module.Basis.sum_smul_bijective`
  ([`ArkLib/Data/Module/Basis.lean`](../../../ArkLib/Data/Module/Basis.lean)).
- [`Relations.lean`](../../../ArkLib/ProofSystem/RingSwitching/Generic/Relations.lean) — the
  framework-fixed relation chain (pillar 4): the input anchor `openingClaimRel` (step 2, with a
  non-vacuity witness), the middle `sliceRel` (step 4) and `sumcheckClaimRel` (steps 5–6), and
  the chain-coherence proof `sumcheckClaim_of_slices` (batching honest slices *is* the sumcheck
  claim, via `bridge_eqTilde`). Plus the PCS interface (pillar 2): `PackedCommitment` whose
  `commitsTo` carries the **functionality law** plus a `Nonempty` well-formedness guard
  (`commitsTo_ne_top`: the `True` hook of the legacy `initialCompatibility` is *unstatable*),
  and `DenseMLPCS` — the `MLIOPCS`-shaped bundle whose completeness/RBR-knowledge fields are
  stated against the fixed anchored `evalRel`: the round-0 knowledge state function must track
  `commitsTo` bidirectionally and completeness must cover every `commitsTo`-satisfying input
  (a bogus-but-functional predicate survives locally and is caught at S6 composition
  completeness). The Binius codeword-consistency predicate is re-expressed in `commitsTo`
  orientation (`Binius.FRIBinius.biniusCommitsTo`, definitionally equal to the legacy hook).

**The honest fork**: field-like instances get the (future) generic Schwartz–Zippel soundness
theorem under `[IsDomain P]`; non-domain rings (Hachi `R_q`) can still *state* a carrier, a
`BatchingStrategy`, and a `DenseMLPCS` but are forced into a sibling theorem with their own
proven gap — the fork lives at the theorem, not the vocabulary.

**Not yet built**: the assembled `ringSwitch` reduction and its soundness statement (gated on
the upstream composition/sumcheck sorries), the Binius migration (the `biniusCommitsTo`
functionality proof — by unique decoding over the `witnessNovelCoeffs` cube-table encoding,
whose original diagonal-reading coercion bug was found at the S5 close-review and fixed in this
PR — and retirement of the legacy `initialCompatibility` hook), and the MBP-`B̂` efficiency
layer ([HJRRR25] §4).

## Core References

- [`../papers/DP24.md`](../papers/DP24.md) — origin of ring switching for binary towers.
- [`../papers/NOZ26.md`](../papers/NOZ26.md) — Hachi; the extension-field→cyclotomic-ring reduction.
- [BRW26] Bünz, Rothblum, Wang. "Flock: Fast Proving for Batch Boolean Computations." ePrint
  2026/1329 — Appendix B: the Φ/MBP formulation the Generic layer follows.
- [RSG] "Ring switching, generalized." Note, [leanEthereum/leanVM-b](https://github.com/leanEthereum/leanVM-b/blob/main/misc/ring-switching-generalized.pdf) — decoupled packing/opening fields,
  γ-power batching.
- [HJRRR25] Hemo, Jue, Rabinovich, Roh, Rothblum. "Jagged Polynomial Commitments (or: How to Stack
  Multilinears)." ePrint 2025/917 — §4: the MBP-MLE evaluation used by the future efficiency
  layer.

## Main ArkLib Touchpoints

- [`../../../ArkLib/ProofSystem/RingSwitching/Profile.lean`](../../../ArkLib/ProofSystem/RingSwitching/Profile.lean) — the abstraction.
- [`../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean`](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean) — `packMLE`, the Binius instance `binaryTowerProfile`, shared defs.
- [`../../../ArkLib/ProofSystem/RingSwitching/General.lean`](../../../ArkLib/ProofSystem/RingSwitching/General.lean) — full reduction + security theorems.
- [`../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean`](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean) — `biniusProfile`, the concrete instantiation.

## Notes

- The protocol skeleton and security *statements* are generic and final; the leaf
  completeness/soundness *proofs* are tracked as follow-up (see `M5_BOOTSTRAP.md` at repo root).
- Soundness reuse across instances is weaker than data-layer reuse: the `[IsDomain L]` theorems fit
  field instances (Binius) but not non-domain rings (Hachi `R_q`), whose soundness is a sibling
  theorem with a different error.
