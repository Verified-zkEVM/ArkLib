/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Basic
import ArkLib.Data.Lattices.CyclotomicRing.Vectors
import Mathlib.Data.ZMod.ValMinAbs

/-!
# Norms On The Cyclotomic Ring

Coefficient norms for elements of the computable cyclotomic ring
`CompPoly.CPolynomial R`, plus their lifts to `PolyVec`. These are the
`ℓ∞ / ℓ₁ / ℓ₂` quantities used to state the shortness constraints
(`‖z‖∞ ≤ β`) in lattice-based proof systems.

Norms are defined relative to a `CenteredCoeffView`, an integer-valued
representative map on coefficients. The canonical instance for `R = ZMod q`
is `zmodCenteredView`, which uses `ZMod.valMinAbs` to map each residue to the
balanced range `[-(q-1)/2, (q-1)/2]`, matching the `mod± q` convention used in
the literature.

## Main definitions

* `CenteredCoeffView R` — an integer representative map for coefficients.
* `zmodCenteredView q` — the balanced representative for `ZMod q`.
* `cInfNorm` / `l1Norm` / `l2NormSq` — the three coefficient norms of a
  `CPolynomial R` (centered `ℓ∞`, `ℓ₁`, squared `ℓ₂`), returned as `ℕ`.
* `PolyVec.cInfNorm` / `l1Norm` / `l2NormSq` — their vector lifts.
-/

open scoped BigOperators

namespace ArkLib.Lattices

open CompPoly

/-- A centered integer view of coefficients: an integer representative map used
to define norms generically over any coefficient type. The canonical instance
for `ZMod q` is `zmodCenteredView`. -/
structure CenteredCoeffView (R : Type*) where
  /-- The integer representative of a coefficient. -/
  repr : R → ℤ

/-- The balanced representative for `ZMod q`, sending each residue to its unique
representative in `[-(q-1)/2, (q-1)/2]` via `ZMod.valMinAbs`. -/
def zmodCenteredView (q : ℕ) [NeZero q] : CenteredCoeffView (ZMod q) where
  repr := ZMod.valMinAbs

namespace CenteredCoeffView

variable {R : Type*} [Zero R] (view : CenteredCoeffView R)

/-- The absolute value of the `i`-th coefficient's centered representative. -/
def absCoeff (p : CPolynomial R) (i : ℕ) : ℕ := (view.repr (p.coeff i)).natAbs

/-- Centered `ℓ∞` norm of a `CPolynomial`: the largest absolute centered
coefficient. -/
def cInfNorm (p : CPolynomial R) : ℕ :=
  (Finset.range p.size).sup (view.absCoeff p)

/-- `ℓ₁` norm of a `CPolynomial`: `Σᵢ |cᵢ|`. -/
def l1Norm (p : CPolynomial R) : ℕ :=
  ∑ i ∈ Finset.range p.size, view.absCoeff p i

/-- Squared `ℓ₂` norm of a `CPolynomial`: `Σᵢ |cᵢ|²`. -/
def l2NormSq (p : CPolynomial R) : ℕ :=
  ∑ i ∈ Finset.range p.size, view.absCoeff p i ^ 2

/-- Vector `ℓ∞` norm: the largest entrywise `ℓ∞` norm. -/
def vecCInfNorm {n : ℕ} (v : PolyVec (CPolynomial R) n) : ℕ :=
  (Finset.univ : Finset (Fin n)).sup fun i => view.cInfNorm (v i)

/-- Vector `ℓ₁` norm: the sum of entrywise `ℓ₁` norms. -/
def vecL1Norm {n : ℕ} (v : PolyVec (CPolynomial R) n) : ℕ :=
  ∑ i : Fin n, view.l1Norm (v i)

/-- Vector squared `ℓ₂` norm: the sum of entrywise squared `ℓ₂` norms. -/
def vecL2NormSq {n : ℕ} (v : PolyVec (CPolynomial R) n) : ℕ :=
  ∑ i : Fin n, view.l2NormSq (v i)

end CenteredCoeffView

end ArkLib.Lattices
