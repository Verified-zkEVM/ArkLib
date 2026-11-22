/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.Sumcheck.Spec.General
public import CompPoly.Multilinear.Equiv
public import ArkLib.ProofSystem.Sumcheck.Impl.Projection

/-!
# Computable Sumcheck polynomials

`Representation` defines degree-bounded CompPoly coefficient arrays and Horner evaluation.
`Projection` constructs honest round messages directly from CompPoly multivariate polynomials
and proves their correspondence with the mathematical specification. It also supplies direct
computational evaluation of the original polynomial.

The native verifier is in `Sumcheck.Interaction.Computable`; the honest strategy and completeness
proofs are in `Sumcheck.Interaction.ComputableCompleteness`.

The general construction enumerates the remaining summation domain. Optimized multilinear
algorithms and their cost guarantees remain future work.
-/

@[expose] public section
