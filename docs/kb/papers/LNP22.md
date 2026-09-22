---
kind: paper
bibkey: LNP22
title: "Lattice-Based Zero-Knowledge Proofs and Applications: Shorter, Simpler, and More General"
year: "2022"
bib_source: blueprint/src/references.bib
source_metadata: ../sources/LNP22/metadata.yml
related_modules:
  - ArkLib/Data/Lattices/CyclotomicRing/Core.lean
  - ArkLib/Data/Lattices/CyclotomicRing/Galois/Automorphism.lean
  - ArkLib/Commitments/Functional/Hachi/Recursion/TraceHandoff.lean
status: seeded
---

# LNP22

## At A Glance

`LNP22` is Lyubashevsky–Nguyen–Plançon, *Lattice-Based Zero-Knowledge Proofs and Applications:
Shorter, Simpler, and More General* (CRYPTO 2022) — the reference framework for lattice
zero-knowledge proofs over power-of-two cyclotomic rings.

In ArkLib it is the background reference for the ambient ring setting of the lattice
developments, rather than the source of a specific formalized theorem. The protocols ArkLib
actually formalizes in that setting come from [`NOZ26`](NOZ26.md) (Hachi) and
[`NS24`](NS24.md) (Greyhound), both of which build on this framework.

## What ArkLib Uses From This Paper

- **The ring setting.** The power-of-two cyclotomic ring `R_q = Z_q[X]/(X^d + 1)`, its
  conductor conventions, and the Galois automorphisms `σ_i : X ↦ X^i` for odd `i` used to
  identify the finite-field extensions sitting inside `R_q`. This is the setting that
  `ArkLib/Data/Lattices/CyclotomicRing/` constructs, in a computable and a semantic layer with a
  soundness bridge between them.
- **Context for the proof machinery** that `NOZ26` and `NS24` instantiate: norm bounds,
  relaxed openings, and the Module-SIS hardness assumption that the commitments reduce to.

No theorem of this paper is stated or proved in ArkLib. Where a lattice statement is formalized,
it is cited to the paper that states it in the form ArkLib uses.

## Main ArkLib Touchpoints

- [`ArkLib/Data/Lattices/CyclotomicRing/Core.lean`](../../../ArkLib/Data/Lattices/CyclotomicRing/Core.lean)
  — the modulus data and the semantic quotient `R[X]/(φ)`.
- [`ArkLib/Data/Lattices/CyclotomicRing/Galois/Automorphism.lean`](../../../ArkLib/Data/Lattices/CyclotomicRing/Galois/Automorphism.lean)
  — the automorphisms `σ_i`, in computable and semantic form with the bridge between them.
- [`ArkLib/Commitments/Functional/Hachi/Recursion/TraceHandoff.lean`](../../../ArkLib/Commitments/Functional/Hachi/Recursion/TraceHandoff.lean)
  — trace/handoff step of the Hachi recursion, in the same ring setting.

## Known Divergences From ArkLib

- ArkLib's cyclotomic ring is built in two layers — a computable reduced-representative ring and a
  Mathlib quotient — connected by an explicit soundness bridge. The paper works with a single
  mathematical ring; the split is an implementation choice, not a change of object.

## Open Formalization Gaps

- The paper's own proof systems are not formalized. Only the ring layer they operate over is.

## Source Access

- Source metadata: [`../sources/LNP22/metadata.yml`](../sources/LNP22/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
