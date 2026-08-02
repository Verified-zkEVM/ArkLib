/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Generic.Recombine
import ArkLib.ProofSystem.RingSwitching.Generic.Packing
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.Bijectivity

/-!
# The Hachi §3 packing head as a generic ring-switch carrier (INV-2, third instance)

Hachi's [NOZ26] §3 *packing head* — the `ψ` monomial packing of Theorem 2 — is an instance of
the generic `RingSwitchCarrier`, with

* `B = E = R_q^H`, the `H`-fixed subring of `R_q` (a field of size `q^{2^κ}`, the "extension
  field" Hachi's title refers to), where the subfield-valued evaluation claims live;
* `P = R_q`, the cyclotomic commitment ring — **not** a domain;
* `packBasis` = Hachi's `ψ`, bundled out of the *proven* `psi_bijective` (Theorem 2).

## Why this file exists

It discharges three standing obligations at once.

1. **INV-2 (anti-overfit), strongest form to date.** The two carriers shipped with S1/S3
   (`towerCarrier`, `decoupledFieldCarrier`) are both *field* packing algebras. This one has a
   **non-domain `P`**, so it exercises the generic layer exactly where the "honest fork" says
   the `[IsDomain P]`-gated soundness theorems must *not* reach — and the definitional and
   `Basis`-derived results (`recombine_bijective`, `openingDecomposition_injective`,
   `bridge_eqTilde`, `packedMLE_eval`) still apply verbatim, because none of them needs a
   domain. The `example`s below are that check, and they are the point of the file.

2. **"Usable by Hachi as well as Binius."** With this instance the generic carrier covers all
   four established *packing-family* ring switches: DP24/Binius (`towerCarrier`), the [RSG]
   decoupled note and Flock App. B (`decoupledFieldCarrier`), and Hachi §3 (here).

3. **The rank-1 opening basis.** `ιE = Unit`: Hachi engineers the evaluation point to be
   subfield-valued, so the opening algebra *is* the base and its basis is a singleton. That is
   precisely the degeneracy which makes the batching layer vacuous (one slice ⇒ nothing to
   batch), i.e. the structural reason [NOZ26] §3's relocation is deterministic where DP24's is
   interactive. NB this file establishes the *data layer* of that correspondence; that the
   assembled reduction collapses to one message and one check is a separate claim, not proven
   here.

## References

* [NOZ26] Nguyen, N. K., O'Rourke, G., and Zhang, J. "Hachi: Efficient Lattice-Based Multilinear
  Polynomial Commitments over Extension Fields." Cryptology ePrint Archive (2026). §3, Eq. 8,
  Theorem 2.
* [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over
  Binary Towers." Cryptology ePrint Archive (2024).
* [RSG] "Ring switching, generalized." Note, leanEthereum/leanVM-b.
-/

open ArkLib.Lattices.CyclotomicModulus Module MvPolynomial Sumcheck.Structured

noncomputable section

namespace RingSwitching.Generic

variable (q : ℕ) [Fact (Nat.Prime q)] [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)]

/-- `R_q` is nontrivial, via the coefficient equivalence `R_q ≃ (Fin (2^α) → R)`. (Missing from
the lattice layer; belongs upstream in `CyclotomicRing/`, kept local until then.) -/
instance instNontrivialRqPowTwo (α : ℕ) :
    Nontrivial (Rq (powTwoCyclotomic (R := ZMod q) α)) :=
  (Rq.powTwoCoeffEquiv (R := ZMod q) α).nontrivial

/-- Hachi's packing map `ψ` ([NOZ26] §3, Eq. 8) as an `R_q^H`-**linear** map. Additivity is the
shipped `psi_add`; the scalar law holds because `ψ a = ∑ⱼ aⱼ · X^{packExp j}` and the fixed-subring
action on `R_q` is multiplication by the coercion. -/
def psiLin (α κ : ℕ) :
    (Fin (2 ^ α / 2 ^ κ) → fixedSubring (R := ZMod q) α (2 ^ κ))
      →ₗ[fixedSubring (R := ZMod q) α (2 ^ κ)] Rq (powTwoCyclotomic (R := ZMod q) α) where
  toFun := psi α (2 ^ κ)
  map_add' := psi_add α (2 ^ κ)
  map_smul' := by
    intro c a
    change psi α (2 ^ κ) (c • a) = c • psi α (2 ^ κ) a
    unfold psi
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    change ((c * a j : fixedSubring (R := ZMod q) α (2 ^ κ)) :
        Rq (powTwoCyclotomic (R := ZMod q) α)) * _ = _
    rw [Subring.coe_mul, mul_assoc]
    rfl

/-- `ψ` bundled as a linear equivalence — this *is* [NOZ26] Theorem 2, restated as an iso of
`R_q^H`-modules rather than a bijection of sets. -/
def psiEquiv (α κ : ℕ) (h2 : (2 : ZMod q) ≠ 0) (hk : 2 * 2 ^ κ ∣ 2 ^ α) :
    (Fin (2 ^ α / 2 ^ κ) → fixedSubring (R := ZMod q) α (2 ^ κ))
      ≃ₗ[fixedSubring (R := ZMod q) α (2 ^ κ)] Rq (powTwoCyclotomic (R := ZMod q) α) :=
  LinearEquiv.ofBijective (psiLin q α κ) (psi_bijective q α κ h2 hk)

/-- **The Hachi packing basis**: `R_q` is free over the fixed subfield `R_q^H` on the packing
monomials `X^{packExp j}`. This is the `packBasis` the generic carrier asks for — note it is a
bundled `Basis`, so its coordinate map is `Basis.repr` and coordinate additivity is free
(safety pillar 1), rather than a raw function field carrying a reconstruction law. -/
def hachiPackBasis (α κ : ℕ) (h2 : (2 : ZMod q) ≠ 0) (hk : 2 * 2 ^ κ ∣ 2 ^ α) :
    Basis (Fin (2 ^ α / 2 ^ κ)) (fixedSubring (R := ZMod q) α (2 ^ κ))
      (Rq (powTwoCyclotomic (R := ZMod q) α)) :=
  Basis.ofEquivFun (psiEquiv q α κ h2 hk).symm

/-- **Hachi §3 packing carrier.** `P = R_q` is a non-domain packing algebra; the opening algebra
is the fixed subfield itself with a singleton basis (the subfield-valued evaluation point). -/
def hachiPackingCarrier (α κ : ℕ) (h2 : (2 : ZMod q) ≠ 0) (hk : 2 * 2 ^ κ ∣ 2 ^ α) :
    RingSwitchCarrier (fixedSubring (R := ZMod q) α (2 ^ κ)) where
  P := Rq (powTwoCyclotomic (R := ZMod q) α)
  E := fixedSubring (R := ZMod q) α (2 ^ κ)
  ιP := Fin (2 ^ α / 2 ^ κ)
  ιE := Unit
  packBasis := hachiPackBasis q α κ h2 hk
  openBasis := Basis.singleton Unit _

/-! ## INV-2 exercise: the generic results fire on a non-domain carrier

Each `example` below is the *generic* theorem applied to `hachiPackingCarrier`. None of them
mentions `[IsDomain P]` — that hypothesis appears only on the batching/soundness layer, which is
exactly the honest fork. -/

section Exercise

variable (α κ : ℕ) (h2 : (2 : ZMod q) ≠ 0) (hk : 2 * 2 ^ κ ∣ 2 ^ α)

/-- Recombination over `ψ` is bijective — Flock Remark 5, fix side. -/
example : Function.Bijective
    (fun s : (hachiPackingCarrier q α κ h2 hk).ιP → fixedSubring (R := ZMod q) α (2 ^ κ) =>
      ∑ i, s i • (hachiPackingCarrier q α κ h2 hk).packBasis i) :=
  RingSwitchCarrier.recombine_bijective _

/-- Opening coordinates are unique — Flock Remark 5, opening side. -/
example : Function.Injective
    (fun s : (hachiPackingCarrier q α κ h2 hk).ιE → fixedSubring (R := ZMod q) α (2 ^ κ) =>
      ∑ u, s u • (hachiPackingCarrier q α κ h2 hk).openBasis u) :=
  RingSwitchCarrier.openingDecomposition_injective _

/-- The linchpin identity `Φ(eq̃(r,y)) = ∑ᵤ A(y,u)·weight u`. -/
example {m : ℕ} (r : Fin m → (hachiPackingCarrier q α κ h2 hk).E) (y : Fin m → Fin 2)
    (weight : (hachiPackingCarrier q α κ h2 hk).ιE → (hachiPackingCarrier q α κ h2 hk).P) :
    (hachiPackingCarrier q α κ h2 hk).bridge weight
        (eqTilde r ((hachiPackingCarrier q α κ h2 hk).boolToE y))
      = ∑ u, (hachiPackingCarrier q α κ h2 hk).eqCoord r y u • weight u :=
  RingSwitchCarrier.bridge_eqTilde _ r y weight

/-- Generic packing correctness, at base-embedded points. -/
example {m : ℕ} (Ps : (hachiPackingCarrier q α κ h2 hk).ιP →
      MultilinearPoly (fixedSubring (R := ZMod q) α (2 ^ κ)) m)
    (pt : Fin m → fixedSubring (R := ZMod q) α (2 ^ κ)) :
    ((hachiPackingCarrier q α κ h2 hk).packedMLE Ps).val.eval
        (fun i => algebraMap _ (hachiPackingCarrier q α κ h2 hk).P (pt i))
      = ∑ i, algebraMap _ _ ((Ps i).val.eval pt) * (hachiPackingCarrier q α κ h2 hk).packBasis i :=
  RingSwitchCarrier.packedMLE_eval _ Ps pt

end Exercise

end RingSwitching.Generic

end
