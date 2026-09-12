/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Pi

/-!
# The packing profile — data layer of `Packing`

`RingSwitchingProfile` is the data a `Packing` ring switch needs before any protocol is
spoken, and nothing more:

* a **basis** exhibiting the large ring `L` as free of rank `2^κ` over the small ring `B` —
  what makes packing possible in the first place: blocks of `2^κ` small-ring coefficients
  become single `L`-elements, and back;
* a **carrier** `A` — the commutative ring in which the relocation checks are computed;
* **two ring homomorphisms** `φ₀, φ₁ : L →+* A` — one transports evaluation-point data,
  the other polynomial coefficients. The structure records their reconstruction laws
  below; injectivity or other compatibility properties must be proved for each instance;
* **coordinate maps** `decomposeRows`/`decomposeColumns : A → (Fin κ → Fin 2) → L` — the
  `2^κ` `L`-coordinates of a carrier element, one per basis index, with two
  **reconstruction laws** stating that every carrier element is recovered from its
  coordinates as a `φ₀`/`φ₁`-weighted sum over the embedded basis.

The reconstruction laws make each coordinate map injective, since reconstruction is a left
inverse. When the carrier is nontrivial, this excludes identically zero coordinate maps. These
are data-layer laws, not a soundness theorem: protocol proofs must still connect the coordinates
to `packMLE`, the honest folded element, and the instance's own algebraic identities.

## Design notes

* It is a `structure` passed **explicitly** (not a `class`): distinct profiles may share the
  same carriers `(B, L, κ)` (e.g. with different bases), so instance resolution would be
  ambiguous.
* It is stated over `CommRing` (not `Field`): carriers of interest include non-field rings.
  The `Field`-only steps (Schwartz–Zippel over `|L|`) stay at the soundness use-sites, not
  here.
* This file holds only the abstract structure, so the sibling `Prelude.lean` can import it
  and parameterize the interactive protocol over it; the tensor-product constructor
  `tensorProductProfile` lives in `Prelude.lean`, after the tensor-algebra definitions it is
  built from.

## Instantiations

| field | Binius ([DP24]) | Hachi §3 head ([NOZ26], planned) |
|---|---|---|
| `B`, `L` | small field `K`, tower field `L` | `R_q^H ≅ F_{q^k}`, `R_q` |
| `basis` | binary `K`-basis of `L`, rank `2^κ` | `ψ`; ArkLib `κ = log₂(d/k)` |
| `A` | tensor algebra `L ⊗[K] L` | `R_q` itself (`= L`) |
| `φ₀`, `φ₁` | `α ↦ α ⊗ 1`, `α ↦ 1 ⊗ α` | `id`, the automorphism `σ₋₁` |
| `decomposeRows`/`Columns` | `L`-coords of `ŝ` in `L ⊗_K L` | coords of `Y ∈ R_q` via `ψ` |

The implemented profile is `tensorProductProfile`; the Hachi column records a proposed adapter,
whose reconstruction and protocol identities remain to be proved. The tensor profile discharges
both reconstruction laws by `Basis.sum_repr` for the corresponding base-changed basis.
The `Lift` construction
(`../Lift/`) does not instantiate this profile at all — see the family umbrella
`ArkLib/ProofSystem/RingSwitching/Basic.lean` for the taxonomy.

See also: the KB concept page `docs/kb/concepts/ring-switching.md` and the blueprint section
`blueprint/src/proof_systems/ring_switching.tex` for the protocol, phases, and security
statements.

## References

* [Diamond, B. E., and Posen, J., *Polylogarithmic Proofs for Multilinears over
  Binary Towers*][DP24], §2.5.
* [NOZ26] Nguyen, N. K., O'Rourke, G., and Zhang, J. "Hachi: Efficient Lattice-Based Multilinear
  Polynomial Commitments over Extension Fields."
-/

@[expose] public section

namespace RingSwitching

open Module

/-- The packing-layer data a ring-switching reduction abstracts over. `L` is free of rank `2^κ`
over the small ring `B` (via `basis`); `A` is the carrier of the folded element `ŝ` sent by
batching. The two coordinate maps reconstruct with the basis in opposite embedded factors. -/
structure RingSwitchingProfile (B L : Type*) (κ : ℕ)
    [CommRing B] [CommRing L] [Algebra B L] where
  /-- rank-`2^κ` `B`-basis of `L`. -/
  basis : Basis (Fin κ → Fin 2) B L
  /-- Carrier of the folded element sent in the batching phase. -/
  A : Type*
  [commRingA : CommRing A]
  [algLA : Algebra L A]
  /-- Ring homomorphism for evaluation-point data; `α ↦ α ⊗ 1` in the tensor carrier. -/
  φ₀ : L →+* A
  /-- Ring homomorphism for polynomial coefficients; `α ↦ 1 ⊗ α` in the tensor carrier. -/
  φ₁ : L →+* A
  /-- Row coordinates, used to batch the honest folded element and the final equality tensor.
  For the tensor carrier these are `baseChangeRight` coordinates: the right-factor scalar
  action, distinct from `algLA`, combines them with basis vectors in the left factor. -/
  decomposeRows : A → (Fin κ → Fin 2) → L
  /-- Column coordinates, used to reconstruct the original evaluation claim. For the tensor
  carrier these are `basis.baseChange L` coordinates, using the left-factor scalar action. -/
  decomposeColumns : A → (Fin κ → Fin 2) → L
  /-- Recover a carrier element from row coordinates with the basis in the `φ₀` factor.
  For the tensor carrier this is `z = ∑ u, basis u ⊗ decomposeRows z u`. -/
  decomposeRows_spec : ∀ z : A, z = ∑ u, φ₀ (basis u) * φ₁ (decomposeRows z u)
  /-- Recover a carrier element from column coordinates with the basis in the `φ₁` factor.
  For the tensor carrier this is `z = ∑ v, decomposeColumns z v ⊗ basis v`. -/
  decomposeColumns_spec : ∀ z : A, z = ∑ v, φ₀ (decomposeColumns z v) * φ₁ (basis v)

attribute [instance] RingSwitchingProfile.commRingA RingSwitchingProfile.algLA

end RingSwitching
