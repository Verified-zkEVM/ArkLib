/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.Module.Basis
import ArkLib.ProofSystem.RingSwitching.Generic.Carrier

/-!
# Generic Ring-Switching — Recombination Injectivity (S4; opening half @ S5)

Discharges design safe-core (iii), **Flock Remark 5** [BRW26]: naive recombination is complete
but *not sound* — soundness requires the packing-basis recombination `s ↦ ∑ᵢ sᵢ • bᵢ^P`
(`B`-coordinates into the packed algebra) to be injective. In the generic design this is not an
instance obligation: the map *is* `packBasis.equivFun.symm`, so injectivity — indeed bijectivity —
is inherited from the `Basis` being a bundled linear equivalence (the reusable statement is
`Module.Basis.sum_smul_bijective`, `ArkLib/Data/Module/Basis.lean`). A fake or lossy recombination
is unrepresentable (design safety pillar 1; see `docs/kb/concepts/ring-switching.md`, "The Generic
layer", for the spine-step and pillar vocabulary used here).

Remark 5's soundness argument uses **both bases**: the packing side (this recombination), and the
uniqueness of `B`-coordinates on the opening side — `openingDecomposition_injective` below — which
pins the eq-decomposition `A(y,u) = openBasis.repr (eq r y) u` as the *only* `B`-decomposition of
`eq(r,y)`.

Scope (design §2, pillar-1 clarification): the soundness-relevant injective map is the
**packing-basis** recombination (step 4). The bridge `Φ = openBasis.constr weight` (step 7) is a
batching *combiner* and is deliberately not injective for general weights — do not conflate the
two.

No domain/field hypotheses — pure `CommRing B` + `Basis` module theory — so the result is
exercised on both S1 carriers (tower and the non-domain decoupled toy) directly (INV-2).

## References

- [BRW26] Bünz, Rothblum, Wang. "Flock: Fast Proving for Batch Boolean Computations." Cryptology
  ePrint Archive, Report 2026/1329. Appendix B, Remark 5 and Eq. (8)
  (slice-wise recombination over the packing basis; injectivity in the base-field coefficients).
-/

noncomputable section

namespace RingSwitching.Generic

open Module

namespace RingSwitchCarrier

variable {B : Type} [CommRing B] (car : RingSwitchCarrier B)

/-- Recombination is a **bijection**: every packed value arises from a *unique* `B`-coordinate
tuple, because `s ↦ ∑ᵢ sᵢ • bᵢ^P` is exactly `packBasis.equivFun.symm`. The inverse direction is
how S5's anchor argument reads (packed value determines the coordinates). -/
theorem recombine_bijective :
    Function.Bijective (fun s : car.ιP → B => ∑ i, s i • car.packBasis i) :=
  car.packBasis.sum_smul_bijective

/-- **Recombination injectivity** (design step 4 / safe-core (iii); [BRW26] Remark 5). Distinct
`B`-coordinate tuples recombine to distinct packed values. This is the property whose *absence*
makes naive recombination unsound (Flock Remark 5); here it is free from the packing `Basis`. -/
theorem recombine_injective :
    Function.Injective (fun s : car.ιP → B => ∑ i, s i • car.packBasis i) :=
  car.recombine_bijective.injective

/-- **Opening-side uniqueness** ([BRW26] Remark 5, the other half). `B`-coordinates in the
*opening* basis are unique: `s ↦ ∑ᵤ sᵤ • bᵤ^E` is injective. The load-bearing soundness
application ([BRW26] p. 38, "by the uniqueness of the 𝔽₂-decomposition") is to the *claim
values*: a wrong claim over `E` forces a wrong slice `sᵤ` for at least one `u`. It equally pins
the eq-decomposition `A(y,u) = eqCoord r y u` as the only `B`-reassembly of `eq(r,y)`
(`Basis.sum_repr` gives existence; this gives uniqueness). The S5/S6 anchor argument reads the
sumcheck claim back through this map. -/
theorem openingDecomposition_injective :
    Function.Injective (fun s : car.ιE → B => ∑ u, s u • car.openBasis u) :=
  car.openBasis.sum_smul_injective

end RingSwitchCarrier

/-! ## Sanity / testable deliverables (S4 §5.3) -/

section Sanity

-- INV-2: exercised on the *tower* carrier at full generality — arbitrary field extension,
-- arbitrary finite rank…
example {K L : Type} [Field K] [Field L] [Algebra K L] {ι : Type} [Fintype ι]
    (β : Basis ι K L) :
    Function.Injective
      (fun s : (towerCarrier β).ιP → K => ∑ i, s i • (towerCarrier β).packBasis i) :=
  (towerCarrier β).recombine_injective

-- …with a fully concrete pin (no missing instances at a closed type; NB `Pi.basisFun` has the
-- wrong module structure for `towerCarrier`, `Basis.singleton` works)…
example : Function.Injective
    (fun s : (towerCarrier (Basis.singleton (Fin 1) (ZMod 2))).ιP → ZMod 2
      => ∑ i, s i • (towerCarrier (Basis.singleton (Fin 1) (ZMod 2))).packBasis i) :=
  (towerCarrier _).recombine_injective

-- …and on the *decoupled* `P ≠ E` carrier — a non-domain product ring, pinning that the result
-- is CommRing-only (no `[IsDomain]`/`Field` needed anywhere in this file).
example : Function.Injective
    (fun s : decoupledToyCarrier.ιP → ZMod 2 => ∑ i, s i • decoupledToyCarrier.packBasis i) :=
  decoupledToyCarrier.recombine_injective

-- Opening-side uniqueness on the decoupled carrier (`E` of a *different* rank than `P` — the
-- two halves of Remark 5 genuinely act on different modules here, unlike the tower case).
example : Function.Injective
    (fun s : decoupledToyCarrier.ιE → ZMod 2 => ∑ u, s u • decoupledToyCarrier.openBasis u) :=
  decoupledToyCarrier.openingDecomposition_injective

end Sanity

end RingSwitching.Generic

end
