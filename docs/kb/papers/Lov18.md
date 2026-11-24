---
kind: paper
bibkey: Lov18
title: "MDS matrices over small fields: A proof of the GM-MDS conjecture"
year: "2018"
bib_source: blueprint/src/references.bib
source_metadata: ../sources/Lov18/metadata.yml
status: seeded
related_modules:
  - ArkLib/ToMathlib/Combinatorics/SetFamily/GenericZeroPattern.lean
  - ArkLib/ToMathlib/RingTheory/Polynomial/GenericZeroPattern.lean
---

# Lov18

## At A Glance

`Lov18` is Lovett, *MDS matrices over small fields: A proof of the GM-MDS conjecture* (arXiv
1803.02523). It proves the algebraic GM-MDS conjecture of Dau–Song–Yuen: for sets `S_1, …, S_k ⊆ [n]`
of size `k − 1` satisfying the MDS condition `|I| + |⋂_{i∈I} S_i| ≤ k`, the polynomials
`∏_{j∈S_i} (x − a_j)` are linearly independent over `F(a_1, …, a_n)`.

## What ArkLib Uses From This Paper

Theorem 1.7 (p. 5): for multiplicity vectors `V ⊂ ℕ^n` with property `V*(k)` (Definitions 1.4, 1.6),
the polynomials `P(k, V)` are linearly independent over `F(a)`. Its proof (Section 2, Lemmas 2.1–2.6)
and the consequence Conjecture 1.3 (p. 3).

## Main ArkLib Touchpoints

- `Polynomial.linearIndependent_vanishingFamily` and
  `Polynomial.linearIndependent_vanishingFamily_fractionRing` (Theorem 1.7).
- `Polynomial.linearIndependent_prod_X_sub_C_of_isGenericZeroPattern` (Conjecture 1.3).
- `Polynomial.exists_embedding_linearIndependent_of_isGenericZeroPattern`: over an infinite field,
  distinct points and `m` linearly independent polynomials of degree `< m` realising a generic zero
  pattern.

## Known Divergences From ArkLib

Multiplicity vectors are multisets indexed by a finite type; the distinguished coordinate of
property (iii) is a chosen point `d`. All polynomials live in one ring `MvPolynomial ι F`: the
paper's passage to `n − 1` variables (Lemma 2.5) is the substitution `X d ↦ X j` in the same ring,
and the induction size counts the points that occur. Linear independence is stated over
`MvPolynomial ι F`, equivalent to independence over its fraction field. The proof works over any
field; the paper fixes a finite field.

## Open Formalization Gaps

Conjecture 1.1 / Theorem 1.2 (existence over finite fields with `|F| ≥ n + k − 1`) and Corollary 1.8
are not formalized. Conjecture 1.5 (linear independence under property `V(k)` alone) is open in the
source (p. 5).

## Version Notes

Theorem numbers and page numbers refer to arXiv v2 (20 March 2018). The paper also appeared in the
2018 IEEE 59th Annual Symposium on Foundations of Computer Science (FOCS 2018), pp. 194–199.

## Source Access

- Source metadata: [`../sources/Lov18/metadata.yml`](../sources/Lov18/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
