# Roadmap

We provide here a list of projects and extensions to ArkLib. Please note that this list is extensive and covers more than our immediate priorities. This list will be updated as items are taken off into immediate issues to be worked on.

## General Theory

### 1. The BCS & Fiat-Shamir Transform

### 2. Zero-Knowledge

### 3. Rewinding Knowledge Soundness

### 4. The Algebraic Group Model

### 5. Mechanized Adversary Runtime


## Proof Systems

### 1. FRI, STIR, WHIR

Note that this item is under active development.

### 2. Binary Tower Fields and Binius.

Note that this item is under active development.

### 3. Twist & Shout

### 4. Pairing DLog based commitment schemes

### 5. Plonk and its variants

### 6. Folding Schemes

## Miscellaneous

### 1. The PCP Theorem

It would be nice to use the theories in ArkLib to prove foundational results such as the PCP theorem. We imagine that it is within reach to formalize the original proofs (using sum-check, multivariate low-degree tests, and proof composition), and also the quasilinear-length PCP by Ben-Sasson & Sudan.

## Supporting Operations

The below are content for an older version of the roadmap. Some of these contents are being actively worked on (especially computable polynomials).

  - [ ] [Computable Univariate Polynomials](ArkLib/Data/UniPoly)
    - [x] Define `UniPoly` as the type of univariate polynomials with computable representations (interally as an `Array` of coefficients). Define operations on `UniPoly` as operations on the underlying `Array` of coefficients.
    - [x] Define an equivalence relation on `UniPoly` that says two `UniPoly`s are equivalent iff they are equal up to zero-padding. Show that this is an equivalence relation.
    - [ ] Show that operations on `UniPoly` descends to the quotient (i.e. are the same up to zero-padding). Show that the quotient is isomorphic as semirings to `Polynomial` in `Mathlib`. Show that the same functions (e.g. `eval`) on `UniPoly` are the same as those of `Polynomial`.
    - [ ] For more efficient evaluation, and use in univariate-based SNARKs, define the coefficient representation of `UniPoly` (on `2`-adic roots of unity), and show conversions between the coefficient and evaluation representations.
  - [ ] [Computable Multilinear Polynomials](ArkLib/Data/MlPoly)
    - [ ] Define `MlPoly` as the type of multilinear polynomials with computable representations (internally as an `Array` of coefficients). Define operations on `MlPoly` as operations on the underlying `Array` of coefficients.
    - [ ] Define alternative definition of `MlPoly` where the evaluations on the hypercube are stored instead of the coefficients. Define conversions between the two definitions, and show that they commute with basic operations.
      - [ ] Will need to expand `Mathlib`'s support for indexing by bits (i.e. further develop `BitVec`).
    - [ ] Define an equivalence relation on `MlPoly` that says two `MlPoly`s are equivalent iff they are equal up to zero-padding. Show that this is an equivalence relation. Show that operations on `MlPoly` descends to the quotient.
    - [ ] Define & prove a module isomorphism between the quotient of `MlPoly` by the equivalence relation and `MvPolynomial` whose individual degrees are restricted to be at most 1.
  - [ ] [Extensions to Multivariate Polynomials in `Mathlib`](ArkLib/Data/MvPolynomial)
    - [ ] [`Interpolation.lean`](ArkLib/Data/MvPolynomial/Interpolation.lean)
      - [ ] Develop the theory of interpolating multivariate polynomials given their values on a `n`-dimensional grid of points.
      - [ ] Specialize this theory to the case of multilinear polynomials (then merge with [`Multilinear.lean`](ArkLib/Data/MvPolynomial/Multilinear.lean)).
        - There is some subtlety here in the sense that general interpolation requires a field (for inverses of Lagrange coefficients), but multilinear interpolation/extension only requires a ring (since the coefficients are just `1`). We may need to develop multilinear theory for non-fields (for Binius).
  - [ ] [Coding Theory](ArkLib/Data/CodingTheory)
    - [ ] Define and develop basic results on linear codes.
    - [ ] Define basic codes such as Reed-Solomon.
    - [ ] Prove proximity gap and interleaved distance results (up to one-third of the unique decoding distance).
  - [ ] [Binary Tower Fields](ArkLib/Data/BinaryTowerField)
    - [ ] Define iterated quadratic extensions of the binary field (Wiedermann construction), and prove that the resulting ring is a field.
    - [ ] Define efficient representation of elements in a binary tower field (using `BitVec`), efficient operations on them (see Binius paper), and prove that the resulting structure is a field isomorphic to the definition above.
  - [ ] [Large Scalar Fields used in Curves](ArkLib/Data/ScalarPrimeField)
    - [ ] Low-priority for now.
    - [ ] Development on this should be done over at [`FFaCiL`](https://github.com/argumentcomputer/FFaCiL.lean/tree/main).
