---
kind: paper
bibkey: EthStark21
title: "ethSTARK Documentation"
year: 2021
bib_source: blueprint/src/references.bib
canonical_url: https://eprint.iacr.org/2021/582
source_metadata: ../sources/EthStark21/metadata.yml
status: curated
related_modules:
  - ArkLib/Data/Polynomial/CosetChunks.lean
---

# EthStark21

## At A Glance

This reference supplies STARK arithmetization context for the reusable coset-chunk algebra.
The detailed Lagrange-decomposition correspondence is recorded under [`HK24`](HK24.md).

## What ArkLib Uses From This Paper

The ethSTARK documentation provides STARK arithmetization and quotient-polynomial context for
[`CosetChunks.lean`](../../../ArkLib/Data/Polynomial/CosetChunks.lean). Its polynomial
decomposition and masking results use the Lagrange construction recorded in
[`HK24`](HK24.md), rather than constituting an implementation of the ethSTARK protocol.

## Main ArkLib Touchpoints

`Polynomial.CosetChunks.sum_chunkL_mul_chunkInterp` explains how polynomial chunk evaluations
can reconstruct an overall quotient evaluation. The reusable algebra is stated over an arbitrary
field with a suitable primitive root and a nonzero coset shift.

## Version and Scope

The bibliography follows the ePrint record, first published in 2021. Version 1.2 of the
documentation, dated July 2023, supplies the background context used here.

The chunk module does not formalize the ethSTARK prover, verifier, commitment layer, or security
theorems. The reference records protocol context, not a claim of implementation conformance.

## Source Access

- [ePrint paper and revision history](https://eprint.iacr.org/2021/582).
