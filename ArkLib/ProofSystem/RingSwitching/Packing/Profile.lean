/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi

/-!
# The packing profile — data layer of `Packing`

`RingSwitchingProfile` is the data a `Packing` ring switch needs before any protocol is
spoken, and nothing more:

* a **basis** exhibiting the large ring `L` as free of rank `2^κ` over the small ring `B` —
  what makes packing possible in the first place: blocks of `2^κ` small-ring coefficients
  become single `L`-elements, and back;
* a **carrier** `A` — the ring in which the relocation checks are computed. The carrier must
  hold the packed polynomial's values and the evaluation point *simultaneously and
  independently*, which is why it comes with
* **two embeddings** `φ₀, φ₁ : L →+* A` — one transports evaluation-point data, the other
  polynomial data, so that products `φ₀(x) · φ₁(y)` keep the two roles apart inside `A`
  (when the roles need no separation, the carrier may be `L` itself and the embeddings
  cheap maps like `id` or an automorphism);
* **coordinate maps** `decomposeRows`/`decomposeColumns : A → (Fin κ → Fin 2) → L` — the
  `2^κ` `L`-coordinates of a carrier element, one per basis index, with two
  **reconstruction laws** stating that every carrier element is recovered from its
  coordinates as a `φ₀`/`φ₁`-weighted sum over the embedded basis.

The reconstruction laws make the coordinates faithful (they rule out law-free profiles such
as `decomposeRows ≡ 0`), but they are the data-layer boundary, not a soundness theorem: the
protocol proofs still connect the coordinates to `packMLE`, the honest folded element, and
the instance's own identities, each instance from its own algebra.

## Design notes

* It is a `structure` passed **explicitly** (not a `class`): distinct profiles may share the
  same carriers `(B, L, κ)` (e.g. with different bases), so instance resolution would be
  ambiguous.
* It is stated over `CommRing` (not `Field`): carriers of interest include non-field rings.
  The `Field`-only steps (Schwartz–Zippel over `|L|`) stay at the soundness use-sites, not
  here.
* This file holds only the abstract structure, so the sibling `Prelude.lean` can import it
  and parameterize the interactive protocol over it; the binary-tower instance
  `binaryTowerProfile` lives in `Prelude.lean`, after the tensor-algebra definitions it is
  built from.

## Instantiations

| field | Binius ([DP24]) | Hachi §3 head ([NOZ26], planned) |
|---|---|---|
| `B`, `L` | small field `K`, tower field `L` | `R_q^H ≅ F_{q^k}`, `R_q` |
| `basis` | binary `K`-basis of `L`, rank `2^κ` | `ψ`; ArkLib `κ = log₂(d/k)` |
| `A` | tensor algebra `L ⊗[K] L` | `R_q` itself (`= L`) |
| `φ₀`, `φ₁` | `α ↦ α ⊗ 1`, `α ↦ 1 ⊗ α` | `id`, the automorphism `σ₋₁` |
| `decomposeRows`/`Columns` | `L`-coords of `ŝ` in `L ⊗_K L` | coords of `Y ∈ R_q` via `ψ` |

The only structural difference between the two — a genuine tensor carrier versus `A = L`
with an automorphism — is absorbed by making `A`, `φ₀`, and `φ₁` explicit fields. Binius
discharges the reconstruction laws by `Basis.sum_repr` for the base-changed bases; the Hachi
head will discharge them from its trace identity. The `Lift` construction
(`../Lift/`) does not instantiate this profile at all — see the family umbrella
`ArkLib/ProofSystem/RingSwitching/Basic.lean` for the taxonomy.

See also: the KB concept page `docs/kb/concepts/ring-switching.md` and the blueprint section
`blueprint/src/proof_systems/ring_switching.tex` for the protocol, phases, and security
statements.

## References

* [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over
  Binary Towers." Cryptology ePrint Archive (2024).
* [NOZ26] Nguyen, N. K., O'Rourke, G., and Zhang, J. "Hachi: Efficient Lattice-Based Multilinear
  Polynomial Commitments over Extension Fields."
-/

namespace RingSwitching

open Module

/-- The packing-layer data a ring-switching reduction abstracts over. `L` is free of rank `2^κ`
over the small ring `B` (via `basis`); `A` is the pack/trace carrier where the folded element `ŝ`
lives (and which the batching phase sends on the wire). See the module docstring for the Binius and
Hachi instantiations of each field. -/
structure RingSwitchingProfile (B L : Type*) (κ : ℕ)
    [CommRing B] [CommRing L] [Algebra B L] where
  /-- rank-`2^κ` `B`-basis of `L`. -/
  basis : Basis (Fin κ → Fin 2) B L
  /-- pack/trace carrier; Binius `L ⊗[K] L`, Hachi `R_q` (`= L`). The batching wire type. -/
  A : Type*
  [commRingA : CommRing A]
  [algLA : Algebra L A]
  /-- column embedding `L → A`; Binius `α ↦ α ⊗ 1`, Hachi `id`. -/
  φ₀ : L →+* A
  /-- row embedding `L → A`; Binius `α ↦ 1 ⊗ α`, Hachi the automorphism `σ₋₁`. -/
  φ₁ : L →+* A
  /-- The `2^κ` `L`-valued "row" coordinates of an `A`-element (Binius: `β.baseChange L`-coords of
  `ŝ ∈ L ⊗_K L`; used in step 5 / `compute_s0`). Protocol-level identities relating these
  coordinates to `packMLE`/`compute_A_func` are discharged by the batching proofs, not by this
  data field alone. -/
  decomposeRows : A → (Fin κ → Fin 2) → L
  /-- The `2^κ` `L`-valued "column" coordinates of an `A`-element (Binius:
  `baseChangeRight`-coords; used in step 2 / `performCheckOriginalEvaluation`). NOTE: in the
  Binius instance this uses the *right* `L`-module structure on `A`, distinct from `algLA`
  (the left/`φ₀` action). -/
  decomposeColumns : A → (Fin κ → Fin 2) → L
  /-- **Row reconstruction law** (the base coordinate identity from DP24 §2.5 / Hachi Theorem 2):
  every `A`-element is recovered from its row coordinates via the `φ₀`-image of those coordinates
  weighted by the `φ₁`-image of the basis. This is the algebraic law tying `decomposeRows` to
  `φ₀`/`φ₁`/`basis` and rules out law-free profiles (e.g. `decomposeRows ≡ 0`). For Binius
  (`A = L ⊗_K L`) it is `Basis.sum_repr` for `β.baseChange L`; for Hachi it is supplied by
  Theorem 2 together with the profile-specific trace/coordinate interpretation. -/
  decomposeRows_spec : ∀ z : A, z = ∑ u, φ₀ (decomposeRows z u) * φ₁ (basis u)
  /-- **Column reconstruction law**: the right/`φ₁`-action dual of `decomposeRows_spec`. -/
  decomposeColumns_spec : ∀ z : A, z = ∑ v, φ₁ (decomposeColumns z v) * φ₀ (basis v)

attribute [instance] RingSwitchingProfile.commRingA RingSwitchingProfile.algLA

end RingSwitching
