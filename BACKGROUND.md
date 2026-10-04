# References

ArkLib's development is informed by the following references:
- Original IOP paper [BCS16]
- Papers that introduce formalism for Polynomial IOPs (Plonk, Marlin, Dark, Lunar, etc.)
- [Linear-Size Constant-Query IOPs for Delegating Computation](https://eprint.iacr.org/2019/1230.pdf) (introduces IOR)
- Reductions of Knowledge (introduces interactive reductions of knowledge)
- Arc paper (re-introduces IOR)
- WHIR paper (introduces $$\mathcal{F}$$-IOP; though the notion has appeared in prior talks & conversations with Dan Boneh)
- Chiesa-Yogev textbook [Building Cryptographic Proofs from Hash Functions](https://snargsbook.org/)

The [textbook comparison](https://github.com/quangvdao/ArkLib/blob/e52099a7e612d5fdffb5eb6ed892d40a60b15172/docs/kb/audits/chiesa-yogev-interaction.md) and
[broader literature map](https://github.com/quangvdao/ArkLib/blob/e52099a7e612d5fdffb5eb6ed892d40a60b15172/docs/kb/audits/interaction-literature-map.md) compare these definitions
with ArkLib's interaction framework and record later work, source versions, and unresolved choices.
They are research notes, not a claim that every referenced result is formalized. For implemented
coverage and migration requirements, see the [roadmap](ROADMAP.md).
