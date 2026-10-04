# Roadmap

**Updated October 3, 2026.** The current general-theory effort is the
[interaction framework](docs/design/05-roadmap.md). Its
[current-status page](docs/design/00-current-status.md) separates the supported source revision
from merged main, and the [migration page](roadmap/interaction-migration.md) states what remains
before replacing the legacy layer.

This page is the project-wide index. The [area roadmap folder](roadmap/README.md) provides
maintenance rules, a template, and populated interaction, Sumcheck/Spartan and Merkle pages. Detailed area plans belong in their owning pages rather than
in duplicated root checklists. The blueprint records mathematical exposition; roadmap pages record
implementation priorities and evidence. Update the affected area page in the same PR as a material
capability change, and distinguish **merged**, **proved in an open PR**, and **planned**.

| Area | Where things stand and next direction |
|---|---|
| Interaction theory and migration | Current focus. Native composition and Sumcheck foundations are merged; reviewed security extensions are in open PRs. See [migration gates](roadmap/interaction-migration.md) and the [implementation sequence](docs/design/05-roadmap.md). |
| [Merkle commitments](roadmap/commitments/merkle-trees.md) | Construction, extraction and random-oracle bounds belong to VCVio. ArkLib's open PRs connect them to native terminal protocols. General oracle elimination remains open. See [ownership and limits](roadmap/interaction-migration.md#merkle-ownership). |
| [Sumcheck and Spartan](roadmap/proof-systems/sumcheck-spartan.md) | [Sumcheck](ArkLib/ProofSystem/Sumcheck) has a native interaction client; [Spartan](ArkLib/ProofSystem/Spartan) still needs a native migration and corresponding security results. Efficient implementations need separate correspondence and cost proofs. |
| FRI, STIR, WHIR and coding theory | Existing developments under [ProofSystem](ArkLib/ProofSystem) and [CodingTheory](ArkLib/Data/CodingTheory). Native migration needs explicit oracle-view and execution correspondence. Existing codeword-folding results are not IVC folding schemes. |
| Binius and ring switching | Existing [Binius](ArkLib/ProofSystem/Binius) and [ring-switching](ArkLib/ProofSystem/RingSwitching) developments. Preserve the distinction between packing and quotient-ring lifting; see the [repository map](docs/wiki/repo-map.md). |
| KZG and functional commitments | [KZG](ArkLib/Commitments/Functional/KZG) contains correctness and binding developments with no local `sorry` at this snapshot. This does not assert unconditional security or certify every transitive dependency. Native interface integration remains a separate task. |
| Lattices and Hachi | Substantial developments in [lattices](ArkLib/Data/Lattices) and [commitments](ArkLib/Commitments), including Ajtai and Hachi. Consult the [repository map](docs/wiki/repo-map.md) and blueprint for construction-specific proof boundaries. |
| Computable polynomials and fields | Owned upstream by [CompPoly](https://github.com/Verified-zkEVM/CompPoly); ArkLib extensions live in [ToCompPoly](ArkLib/ToCompPoly). Do not recreate the obsolete local polynomial/field checklists. |

## Longer-term research targets

The Chiesa–Yogev pipeline is a required coverage direction, expressed in our interaction language
and with explicit correspondence to the literature. The
[textbook comparison](https://github.com/quangvdao/ArkLib/blob/e52099a7e612d5fdffb5eb6ed892d40a60b15172/docs/kb/audits/chiesa-yogev-interaction.md) and
[broader literature map](https://github.com/quangvdao/ArkLib/blob/e52099a7e612d5fdffb5eb6ed892d40a60b15172/docs/kb/audits/interaction-literature-map.md) record scope and unresolved
choices, including round-by-round knowledge, accumulation, Funky, and duplex-sponge Fiat–Shamir.

Further targets include general BCS/oracle elimination, zero knowledge, rewinding extraction,
the algebraic group model, mechanized adversary runtime, Plonk, Twist and Shout, IVC folding,
and foundational PCP results. This list does not claim these targets are implemented or scheduled.
Protocol definitions, security proofs, efficient algorithms, and legacy migration are separate
milestones, each requiring evidence.
