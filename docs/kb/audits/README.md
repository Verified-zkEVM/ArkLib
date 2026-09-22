# Audit Pages

Audit pages are persistent comparison artifacts between an external source and ArkLib's current
formalization state.

Use this directory for:

- paper-to-ArkLib theorem matrices;
- gap analyses for a specific paper;
- source-version comparisons that affect formalization work.

The long-term goal is for deep paper audits to live here rather than in ad hoc branch notes.

An audit page states what it was checked against and stays present-tense about the tree. It is not
a review record: a verdict about one branch at one commit does not belong here.

Current audit pages:

- [`open-problems-list-decoding-and-correlated-agreement.md`](open-problems-list-decoding-and-correlated-agreement.md)
  - per-statement status matrix for [`ABF26`](../papers/ABF26.md), covering the coding-theory
    code families, Johnson bounds, subspace designs, and extension codes.
- [`bciks20-appendix-a-rational-functions.md`](bciks20-appendix-a-rational-functions.md)
  - Appendix A rational-function and Hensel-lifting status for [`BCIKS20`](../papers/BCIKS20.md).
- [`noz26-subfield-lemmas5-6.md`](noz26-subfield-lemmas5-6.md)
  - [`NOZ26`](../papers/NOZ26.md) §3 Lemmas 5–6: correspondence, assumptions, dependency split,
    and proof status.
- [`noz26-zero-check-lemma10.md`](noz26-zero-check-lemma10.md)
  - [`NOZ26`](../papers/NOZ26.md) Figure 5 / Lemma 10: correspondence, the nested-tree repair, and
    the weak-binding seam in the escape-threaded opening chain.
- [`bcgm25-mca-generators.md`](bcgm25-mca-generators.md)
  - [`BCGM25`](../papers/BCGM25.md) generator layer: definition and result correspondence, the two
    forms Lemma 4.4 is proved in and why, and a gap in the paper's Theorem 9.2 citation.
