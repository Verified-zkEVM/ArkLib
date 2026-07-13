/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Prelude
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.Pi

/-!
# Generic Ring-Switching — Definitional Layer (S1)

The shrunk carrier for a *generic, field-decoupled* ring switch, plus the derived definitions that
every ring-switch reduction shares. Design background — the seven-step spine, the safety pillars
cited below, and the layer's status — is in `docs/kb/concepts/ring-switching.md` ("The Generic
layer").

Unlike the DP24 `RingSwitchingProfile`, this carrier supplies **only** algebra + `Basis` witnesses:
the packing algebra `P` and the opening algebra `E` are *unrelated* `B`-algebras (the generalization
of Diamond–Posen / Flock App. B / the "Ring switching, generalized" note [RSG]). Everything else
— the eq-decomposition, the bridge `Φ`, the packed polynomial — is *derived* from the two bases, so
an instance has no lever to supply a law-free coordinate map (design safety pillar 1: `Basis` is the
safe primitive).

DP24/Binius is the special case `P = E = L`, `B = K` (`towerCarrier`); the decoupled case is
witnessed by `decoupledToyCarrier` (`P ≠ E`), which keeps the anti-overfit invariant INV-2 live from
the first session.

This module is **definitional only** — no security proofs. Packing correctness (`packedMLE_eval`,
and the `packMLE = packedMLE ∘ curry` bridge that keeps the Binius path stable) is S2.

## References

- [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over
  Binary Towers." Cryptology ePrint Archive (2024).
- [BRW26] Bünz, Rothblum, Wang. "Flock: Fast Proving for Batch Boolean Computations." Cryptology
  ePrint Archive, Report 2026/1329. Appendix B (the Φ/matrix-branching-program formulation of
  the ring switch).
- [RSG] "Ring switching, generalized." Note, leanEthereum/leanVM-b repository (decoupled
  packing/opening fields, γ-power batching).
-/

noncomputable section

namespace RingSwitching.Generic

open Module MvPolynomial Sumcheck.Structured

/-- The packing-layer data a *generic* ring-switch abstracts over. `P` is the packing algebra
(where the committed dense polynomial lives), `E` the opening algebra (where evaluation claims
arrive); both are free `B`-modules via `packBasis`/`openBasis`, and — crucially — they are
**unrelated** to each other. Compare `RingSwitchingProfile`, which bakes in a single tower field and
supplies coordinate maps + embeddings by hand; here those are all derived from the two bases.
Carriers live in `Type` 0 (`MultilinearPoly` is `Type`-bound, forcing `P`/`E` : `Type`). -/
structure RingSwitchCarrier (B : Type) [CommRing B] where
  /-- Packing algebra (dense-committed polynomial's coefficient ring). -/
  P : Type
  /-- Opening algebra (evaluation-claim field/ring). -/
  E : Type
  /-- Packing basis index; `|ιP|` = packing rank (arbitrary, need not be a power of two). -/
  ιP : Type
  /-- Index set of the opening basis (`|ιE|` = opening rank). -/
  ιE : Type
  [commP : CommRing P]
  [algP : Algebra B P]
  [commE : CommRing E]
  [algE : Algebra B E]
  -- Well-formedness: both algebras are nontrivial. A genuine ring-switch precondition, not a
  -- convenience — without it a degenerate carrier (e.g. `P = E = PUnit`, empty bases) is a
  -- *bona-fide* carrier (an empty `Basis` is honest, so "no fake basis" does not exclude it) on
  -- which the future opening anchor `∀ i, αᵢ = P̂ᵢ(r)` (which lives over `E`) collapses to `univ`.
  -- The planned `[IsDomain P]` fork guards only `P`; `Nontrivial E` is the symmetric guard needed.
  [ntP : Nontrivial P]
  [ntE : Nontrivial E]
  [ftP : Fintype ιP]
  [ftE : Fintype ιE]
  /-- `B`-basis of the packing algebra `P`. -/
  packBasis : Basis ιP B P
  /-- `B`-basis of the opening algebra `E`. -/
  openBasis : Basis ιE B E

attribute [instance] RingSwitchCarrier.commP RingSwitchCarrier.algP RingSwitchCarrier.commE
  RingSwitchCarrier.algE RingSwitchCarrier.ntP RingSwitchCarrier.ntE RingSwitchCarrier.ftP
  RingSwitchCarrier.ftE

namespace RingSwitchCarrier

variable {B : Type} [CommRing B] (car : RingSwitchCarrier B)

/-- Boolean hypercube point as a `0`/`1` point over the opening algebra `E`. -/
def boolToE {m : ℕ} (y : Fin m → Fin 2) : Fin m → car.E :=
  fun i => if y i = 1 then 1 else 0

/-- **Packing** (design step 1). Pack a family of `B`-valued multilinears into a single
`P`-valued multilinear: `P_packed(y) = ∑ᵢ (Pᵢ)(y) · packBasisᵢ`. This is the note's "pack across the
family" primitive — natively rank-agnostic (`ιP` arbitrary). DP24's variable-splitting `packMLE` is
the special case where the family is the currying of one polynomial's first `κ` variables (bridge
lemma is S2). -/
def packedMLE {m : ℕ} (Ps : car.ιP → MultilinearPoly B m) : MultilinearPoly car.P m :=
  ∑ i, car.packBasis i • componentWise_embed_MLE B m (algebraMap B car.P) (Ps i)

/-- **eq-decomposition** (design step 3). The `u`-th `B`-coordinate of `eq(r, y) ∈ E` in the opening
basis — the function `A(y,u)` of Flock App. B. This is *not* instance data: it is `openBasis.repr`,
so the reconstruction law `∑ᵤ A(y,u)·b_u^E = eq(r,y)` is `Basis.sum_repr`, free from mathlib. -/
def eqCoord {m : ℕ} (r : Fin m → car.E) (y : Fin m → Fin 2) (u : car.ιE) : B :=
  car.openBasis.repr (eqTilde r (car.boolToE y)) u

/-- **The bridge `Φ : E → P`** (design step 7 / batching). The unique `B`-linear map sending each
opening basis vector `b_u^E` to `weight u`. Derived via `Basis.constr`, so `B`-linearity and
`Φ(b_u^E) = weight u` are free — no instance freedom (design safety pillar 1). -/
def bridge (weight : car.ιE → car.P) : car.E →ₗ[B] car.P :=
  car.openBasis.constr B weight

/-- **The auxiliary multiplier `B(y) = Φ(eq(r, y))`** (design step 6), as a `P`-multilinear, given
the batching weights. The verifier evaluates its MLE at the sumcheck output point; efficient
evaluation (tensor / matrix-branching-program) is a later, off-soundness-path refinement (S9). -/
def Bmult {m : ℕ} (r : Fin m → car.E) (weight : car.ιE → car.P) : MultilinearPoly car.P m :=
  ⟨MvPolynomial.MLE (fun y : Fin m → Fin 2 => car.bridge weight (eqTilde r (car.boolToE y))),
    MLE_mem_restrictDegree _⟩

/-- **The linchpin identity** (design steps 3+5+6+7, unified): the bridge applied to `eq(r,y)`
expands over the opening basis as `Φ(eq(r,y)) = ∑ᵤ A(y,u)·weight(u)`, i.e. `B(y)` is the
`weight`-batched recombination of the eq-coordinates. Free from `Basis.constr` — no domain, no
instance freedom. This is the algebraic heart the batching/sumcheck soundness (S5/S6) pivots on;
proving it now locks the design's core claim (design safety pillars 1 & 3). -/
theorem bridge_eqTilde {m : ℕ} (r : Fin m → car.E) (y : Fin m → Fin 2)
    (weight : car.ιE → car.P) :
    car.bridge weight (eqTilde r (car.boolToE y)) = ∑ u, car.eqCoord r y u • weight u := by
  simp only [bridge, eqCoord, Basis.constr_apply_fintype, Basis.equivFun_apply]

end RingSwitchCarrier

/-! ## Instances (INV-2: two structurally distinct carriers) -/

/-- **Tower / Binius carrier**: `P = E = L`, `B = K`, both bases the single field basis `β` — the
DP24 special case (the shape `binaryTowerProfile` abstracts). -/
def towerCarrier {K L : Type} [Field K] [Field L] [Algebra K L]
    {ι : Type} [Fintype ι] (β : Basis ι K L) : RingSwitchCarrier K where
  P := L
  E := L
  ιP := ι
  ιE := ι
  packBasis := β
  openBasis := β

/-- **Decoupled toy carrier**: `P = Fin 2 → ZMod 2` (rank 2), `E = Fin 3 → ZMod 2` (rank 3) over
`B = ZMod 2`. `P ≠ E` with distinct ranks — a deliberately minimal witness that no definition
assumes `P = E` (INV-2). Not a domain (a product ring), which is fine here: S1 is definitional.
A `GaloisField` field pair is a later, more realistic instance (relevant once `[IsDomain]` enters
at S6). -/
def decoupledToyCarrier : RingSwitchCarrier (ZMod 2) where
  P := Fin 2 → ZMod 2
  E := Fin 3 → ZMod 2
  ιP := Fin 2
  ιE := Fin 3
  packBasis := Pi.basisFun (ZMod 2) (Fin 2)
  openBasis := Pi.basisFun (ZMod 2) (Fin 3)

/-! ## Sanity / testable deliverables (S1 §5.3) -/

section Sanity

-- Both carriers build (INV-2): tower `P = E` and decoupled `P ≠ E`.
example {K L ι : Type} [Field K] [Field L] [Algebra K L] [Fintype ι] (β : Basis ι K L) :
    RingSwitchCarrier K := towerCarrier β

example : RingSwitchCarrier (ZMod 2) := decoupledToyCarrier

-- The derived defs apply on the *decoupled* carrier (exercises the `P ≠ E` path).
-- Note the packing direction the types enforce: a family of `B`-valued (`ZMod 2`) multilinears
-- packs into a single `P`-valued one.
example (Ps : decoupledToyCarrier.ιP → MultilinearPoly (ZMod 2) 3) :
    MultilinearPoly decoupledToyCarrier.P 3 :=
  decoupledToyCarrier.packedMLE Ps

example (r : Fin 3 → decoupledToyCarrier.E) (y : Fin 3 → Fin 2) (u : decoupledToyCarrier.ιE) :
    ZMod 2 := decoupledToyCarrier.eqCoord r y u

example (w : decoupledToyCarrier.ιE → decoupledToyCarrier.P) :
    decoupledToyCarrier.E →ₗ[ZMod 2] decoupledToyCarrier.P :=
  decoupledToyCarrier.bridge w

example (r : Fin 3 → decoupledToyCarrier.E) (w : decoupledToyCarrier.ιE → decoupledToyCarrier.P) :
    MultilinearPoly decoupledToyCarrier.P 3 :=
  decoupledToyCarrier.Bmult r w

-- INV-2 (*semantic*, not just typecheck): the linchpin identity `bridge_eqTilde` holds on the
-- decoupled `P ≠ E` carrier — a value-level pin of `bridge` and `eqCoord` together.
example (r : Fin 3 → decoupledToyCarrier.E) (y : Fin 3 → Fin 2)
    (w : decoupledToyCarrier.ιE → decoupledToyCarrier.P) :
    decoupledToyCarrier.bridge w (eqTilde r (decoupledToyCarrier.boolToE y))
      = ∑ u, decoupledToyCarrier.eqCoord r y u • w u :=
  decoupledToyCarrier.bridge_eqTilde r y w

end Sanity

end RingSwitching.Generic

end
