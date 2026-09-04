---
kind: paper
bibkey: Kop15
title: "List-Decoding Multiplicity Codes"
year: "2015"
bib_source: blueprint/src/references.bib
source_metadata: ../sources/Kop15/metadata.yml
status: seeded
related_concepts:
  - reed-solomon-proximity
related_modules:
  - ArkLib/ToMathlib/Polynomial/HasseTaylor/FiniteJet.lean
---

# Kop15

## At A Glance

`Kop15` is Swastik Kopparty, *List-Decoding Multiplicity Codes*, Theory of Computing
**11**(5) (2015), 149--182.  The journal article was received in 2013, revised in 2015,
and published on 29 May 2015; a prior version appeared as ECCC technical report TR12-044,
posted on 22 April 2012.

The paper's first main result gives capacity-achieving list decoding for univariate
multiplicity codes over prime fields.  Its root-finding engine turns the interpolation
polynomial into a differential equation and solves regular branches coefficient by
coefficient using a finite-field power-series argument described as a variation of
Hensel lifting.

ArkLib uses the regular-branch core as a standalone formalization component for the
all-rate Reed--Solomon theorem.  The source result is about multiplicity codes, but its
one-step lifting theorem is a general polynomial-differential-equation fact; that is the
reusable layer formalized here.

## What ArkLib Uses From This Paper

- **Definition 2.1 (Hasse derivatives).**  The source defines the `i`-th derivative as
  the coefficient of `Z^i` in `P(T + Z)`.  This is the same normalization as Mathlib's
  `Polynomial.hasseDeriv`, not the ordinary derivative divided later by a factorial.
  ArkLib packages evaluations of these derivatives as `Polynomial.hasseCoeffAt` and
  finite initial conditions as `Polynomial.hasseJet`.
- **Theorem 4.4 (one-step regular lift).**  Given residual vanishing modulo
  `(T - alpha)^k`, with `k >= 1`, changing `f` by
  `gamma * (T - alpha)^(k + r)` changes the first unresolved residual coefficient by
  `gamma * choose (k + r) r * separant`.  If the separant and this binomial coefficient
  are nonzero, exactly one `gamma` raises the residual order from `k` to `k + 1`.
- **Corollary 4.5 (iteration and counting).**  Starting from a fixed regular initial
  `r`-jet, the source iterates Theorem 4.4.  At indices where the binomial coefficient
  vanishes in the field it branches over every coefficient; otherwise the next
  coefficient is forced.

The ArkLib all-rate development uses the below-characteristic specialization:
if every coefficient degree under consideration is at most `D` and
`D < ringChar F`, then all relevant binomial coefficients are nonzero.  Consequently a
fixed regular initial jet extends to **at most one** degree-`D` solution.  This is a
specialization of the paper's branching count, not a stronger claim about arbitrary
characteristic.

## Main ArkLib Touchpoints

- [`ArkLib/ToMathlib/Polynomial/HasseTaylor/FiniteJet.lean`](../../../ArkLib/ToMathlib/Polynomial/HasseTaylor/FiniteJet.lean)
  — the characteristic-free finite Hasse-jet coordinates used for initial conditions and
  Taylor coefficients.
- The regular-lifting modules added by the R2 contribution — the exact paths and public
  theorem names will be recorded here when the independently reviewed integration commit
  is assembled.
- `ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/` — the downstream differential
  specialization, separant, and bounded-solution interfaces used by the all-rate proof.

## Assumption Ledger

- `D < ringChar F` is the characteristic guard for the unique-lifting specialization.
  A field-cardinality inequality is not a substitute outside prime fields.
- Bounds on the individual degrees of the differential-equation variables are used by
  derivative descent elsewhere in the root solver; they are not hypotheses of the
  regular one-step lift itself.
- The source's one-step proof needs `k >= 1`: only then are quadratic and higher Taylor
  terms divisible by `(T - alpha)^(k + 1)`.
- The most reusable algebraic helper can instead assume directly that
  `choose (k + r) r` is a unit or nonzero.  This preserves the exact source theorem and
  also supports characteristic zero; the below-characteristic result is a corollary.
- Regularity means that the partial derivative with respect to the highest derivative
  variable (the separant), evaluated at the initial jet, is nonzero.

## Version and Lineage Notes

- The BibTeX record and statement numbers refer to the final Theory of Computing article,
  DOI `10.4086/toc.2015.v011a005`.
- The earlier ECCC version is TR12-044.  It establishes the historical priority, but Lean
  docstrings should use the final journal numbering unless they explicitly compare versions.
- The all-rate Reed--Solomon manuscript reuses Kopparty's differential-equation engine in
  a different outer coding-theoretic argument.  ArkLib's contribution is the checked Lean
  reconstruction, generic interfaces around its algebraic steps, and the explicit
  below-characteristic uniqueness corollary needed downstream.
- Declaration names describe their mathematics rather than embedding paper numbers.
  Paper correspondence belongs in module and theorem documentation.

## Scope and Non-Claims

- This component does not by itself formalize Theorem 4.3, the singular recursive branch,
  the list-size count in general characteristic, or the root-finding runtime bound.
- It does not claim that every initial jet extends to a full solution.  The regular lift
  gives unique continuation when the current truncation satisfies the required residual
  congruence; the final uniqueness theorem compares actual solutions.
- No code is copied from Kopparty's article.  The mathematical proof lineage is cited;
  Lean proof engineering and supporting generic lemmas are ArkLib work.

## Source Access

- Journal landing page: <https://theoryofcomputing.org/articles/v011a005/>
- Journal PDF: <https://theoryofcomputing.org/articles/v011a005/v011a005.pdf>
- Earlier ECCC report: <https://eccc.weizmann.ac.il/report/2012/044/>
- Source metadata: [`../sources/Kop15/metadata.yml`](../sources/Kop15/metadata.yml)
- Public reference: [`blueprint/src/references.bib`](../../../blueprint/src/references.bib)
