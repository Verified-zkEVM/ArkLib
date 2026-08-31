# Ring Switching

This page is the KB landing page for the **ring-switching** technique. Ring switching is a
*family* of constructions, not one protocol — ArkLib formalizes two construction folders,
each with its own data layer: `Packing/` (`RingSwitchingProfile`, small→large packing)
and `Lift/` (`Lift.Presentation`, large quotient ring→field, the generic
HMZ25 switch); the taxonomy lives in the folder umbrella
`ArkLib/ProofSystem/RingSwitching/Basic.lean`. What the two constructions share sits at the folder
top level: the check-then-update round-shape verifiers (`RoundVerifiers.lean`) and the
embed-and-evaluate transport algebra (`Transport/Eval.lean` univariate, `Transport/Coeffs.lean`
degree-generic multivariate).

The folder names describe the algebraic operation, not merely the source and target types:

- **Packing** groups a basis-sized block of small-ring coefficients into the coordinates of
  one large-ring element. For rank `2^κ`, this turns `2^κ` coefficients—and therefore `κ`
  Boolean-variable positions—into one coefficient over the large ring.
- **Lift** replaces an equality in `S ≅ R[X]/(φ)`, which holds only modulo `φ`, by an exact
  equality in `R[X]` with an explicit quotient witness. Evaluating that lifted equality in a
  field is the subsequent verification step.

This distinction matters: both operations are called ring switching in the literature, but
they require different data layers and different security arguments.

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
additive `O(ℓ/|L|)` soundness cost (`O(1/|L|)` per challenge); Hachi's cyclotomic-ring instance has a separate CWSS-style
soundness theorem because `R_q` is not a domain. This lets a PCS commit cheaply over a tiny ring
while running sum-check and the final opening over a carrier large enough for the intended
soundness argument.

With `ℓ = ℓ' + κ`, a small-field multilinear `t` in `ℓ` variables is *packed* into a large-field
multilinear `t'` in `ℓ'` variables (`packMLE`): each block of `2^κ` coefficients becomes one
`L`-element via a `B`-basis `β` of `L`. The interaction runs in a *pack/trace carrier* `A` where the
folded element `ŝ` lives; an eq̃/trace inner-product identity (DP24 §2.5) ties `ŝ`'s coordinates to
the original claim and the new sum-check target.

## ArkLib's abstraction

ArkLib formalizes the packing *data layer* once, generic over a `RingSwitchingProfile (B L) κ`:

- `basis`, carrier `A`, embeddings `φ₀`/`φ₁ : L →+* A`, coordinate maps `decomposeRows`/`Columns`,
- plus two **reconstruction laws** (`decomposeRows_spec`, `decomposeColumns_spec`) that tie the
  coordinate maps to `φ₀`/`φ₁`/`basis` and rule out law-free profiles.

Those laws are the algebraic profile boundary, not a complete soundness theorem by themselves.
The batching/sum-check proofs still have to connect the profile coordinates to `packMLE`,
`embedded_MLP_eval`, `compute_A_func`, and the instance's eq̃/trace identity.

The *protocol* on top of the profile is per-construction. The DP24 packing protocol
(the protocol files of `ProofSystem/RingSwitching/Packing/`) is three phases (batching → sum-check → large-field IOPCS
opening); see the blueprint section *Ring Switching*
(`blueprint/src/proof_systems/ring_switching.tex`) for the protocol and security statements.
Its RBR knowledge error is `κ/|L| + Σ 2/|L| + 1/|L| + ε_IOPCS` (DP24 §3.1–3.2), and soundness
requires `[IsDomain L]` (Schwartz–Zippel).

## The three constructions

- **DP24 packing switch** (`ProofSystem/RingSwitching/Packing/`, instance
  `binaryTowerProfile`):
  small field → large field; `A = L ⊗_K L`, `φ₀ = ·⊗1`, `φ₁ = 1⊗·`, coordinates from the
  left/right `L`-module bases; the two profile laws are **proven** in ArkLib. Because the
  evaluation point is an arbitrary big-field point, the claim is relocated *interactively*
  (batching challenge + dedicated packing sum-check).
- **Hachi §3 packing head** ([`../papers/NOZ26.md`](../papers/NOZ26.md), planned): `L = R_q`,
  `A = R_q`, `φ₀ = id`, `φ₁ = σ₋₁`, `β = ψ` (Theorem 2). Same packing algebra, but the
  evaluation point is engineered to be subfield-valued, so the reduction is **deterministic**
  (one message + one trace check, no challenges, no sum-check). `R_q` is not a domain, so the
  Schwartz–Zippel soundness theorem does not apply — Hachi soundness is a separate (CWSS)
  argument.
- **HMZ25 `Lift` construction** ([`../papers/HMZ25.md`](../papers/HMZ25.md)): the
  *opposite* direction, `S ≅ R[X]/(φ)` → a field `F` — lift `M z = y` to `R[X]` and evaluate
  at a random `α`. **Formalized generically** in `ProofSystem/RingSwitching/Lift/`
  over any monic-modulus presentation (`Presentation`/`IsPresentation` — not
  cyclotomic-specific), with CWSS at `k = 2·deg φ` proven once from the presentation laws,
  on top of the committed-scalar shell
  (`OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean`).
  Hachi's link 4 (`Commitments/Functional/Hachi/RingSwitch/Reduction.lean`) is the proven
  cyclotomic instance (`cyclotomicPresentation`). It does **not** instantiate
  `RingSwitchingProfile`; what it shares with DP24 is the `pSpecScalar` wire shape and the
  top-level layer of `ProofSystem/RingSwitching/` (round-shape verifiers, embed-and-evaluate
  transport).

## Core References

- [`../papers/DP24.md`](../papers/DP24.md) — origin of ring switching for binary towers.
- [`../papers/NOZ26.md`](../papers/NOZ26.md) — Hachi; the extension-field→cyclotomic-ring reduction.

## Main ArkLib Touchpoints

- [`../../../ArkLib/ProofSystem/RingSwitching/Basic.lean`](../../../ArkLib/ProofSystem/RingSwitching/Basic.lean) — the family taxonomy umbrella.
- [`../../../ArkLib/ProofSystem/RingSwitching/RoundVerifiers.lean`](../../../ArkLib/ProofSystem/RingSwitching/RoundVerifiers.lean) — the shared check-then-update round verifiers.
- [`../../../ArkLib/ProofSystem/RingSwitching/Transport.lean`](../../../ArkLib/ProofSystem/RingSwitching/Transport.lean) — the shared claim-transport algebra (umbrella for `Transport/`).
- [`../../../ArkLib/ProofSystem/RingSwitching/Packing/Profile.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Profile.lean) — the packing abstraction.
- [`../../../ArkLib/ProofSystem/RingSwitching/Packing/Prelude.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/Prelude.lean) — `packMLE`, the Binius instance `binaryTowerProfile`, DP24 defs.
- [`../../../ArkLib/ProofSystem/RingSwitching/Packing/General.lean`](../../../ArkLib/ProofSystem/RingSwitching/Packing/General.lean) — the full DP24 reduction + security theorems.
- [`../../../ArkLib/ProofSystem/RingSwitching/Lift/Presentation.lean`](../../../ArkLib/ProofSystem/RingSwitching/Lift/Presentation.lean) — the quotient-presentation abstraction + lift algebra.
- [`../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean`](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean) — the generic `Lift` construction + CWSS.
- [`../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean`](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean) — the committed-scalar protocol seam.
- [`../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean`](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean) — `biniusProfile`, the concrete instantiation.

## Notes

- The DP24 protocol skeleton and security *statements* are profile-generic and final; the leaf
  completeness/soundness *proofs* are open (`sorry`) and tracked as follow-up.
- Soundness reuse across instances is weaker than data-layer reuse: the `[IsDomain L]` theorems fit
  field instances (Binius) but not non-domain rings (Hachi `R_q`), whose soundness is a sibling
  theorem with a different error.
