/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.ProofSystem.RingSwitching.Generic.Carrier

/-!
# Generic Ring-Switching — Packing Correctness (S2)

Discharges the **embedded-point half** of design Hole B / safety pillar 3(i): the generic packing
correctness identity is proven once, generically, so no downstream instance re-touches it. See
`docs/kb/concepts/ring-switching.md` ("The Generic layer") for the safety pillars cited below.

Scope, stated honestly: (i) `packedMLE_eval` is the reassembly identity at **base-embedded points**
`algebraMap ∘ pt` — the only well-typed form, since each `Pᵢ` is a `B`-multilinear (there is no
`∑ Pᵢ·bᵢ` at a general `P`-point). (ii) full **polynomial** packing correctness (holding at every
point) is delivered *only for the tower/field case* by `packMLE_eq_packedMLE_curry`, via multilinear
uniqueness (needs `[IsDomain L]`). (iii) the round-trip for the **generic** `packedMLE` is now
delivered by the "Generic unpacking" section below (`unpack`, `packedMLE_unpack`,
`unpack_packedMLE` — coefficient-wise, `CommRing`-only; added at S6 for the extractor per design
review F2); the DP24-specific `unpackMLE ∘ packMLE = id` round-trip (rank-`2^κ` variable
merging, design Hole B's second half) remains a follow-up. A future session must still not assume
non-embedded-point reassembly from this file.

Two results (plus the unpacking section):

* `packedMLE_eval` — the semantic content of packing: evaluating the packed `P`-multilinear at (the
  image of) a base-ring point `pt` reassembles the base evaluations against the packing basis,
  `P̂_packed(pt) = ∑ᵢ (algebraMap (P̂ᵢ(pt))) · bᵢ^P`. A pure `Basis`/`MLE` fact — no domain
  hypothesis, no instance obligation.
* `packMLE_eq_packedMLE_curry` — the **Binius-stability bridge** (label "R2"): the DP24 rank-`2^κ`
  variable-splitting `packMLE` is exactly the generic `packedMLE` applied to the curried family of
  the input polynomial over the tower carrier. This keeps the proven Binius path stable while
  subsuming it under the generic definition.

## References

- [DP24] Diamond, Benjamin E., and Jim Posen. "Polylogarithmic Proofs for Multilinears over
  Binary Towers." Cryptology ePrint Archive (2024). Definition 2.2 (prefix variable-splitting).
- [RSG] "Ring switching, generalized." Note, leanEthereum/leanVM-b repository
  (arbitrary-rank family packing).
-/

noncomputable section

namespace RingSwitching.Generic

open Module MvPolynomial Sumcheck.Structured

namespace RingSwitchCarrier

variable {B : Type} [CommRing B] (car : RingSwitchCarrier B)

/-- The underlying `MvPolynomial` of the packed multilinear: the honest
`∑ᵢ bᵢ^P · map(algebraMap) Pᵢ` (safety pillar 1 — derived from the packing basis, no freedom). -/
theorem packedMLE_val {m : ℕ} (Ps : car.ιP → MultilinearPoly B m) :
    (car.packedMLE Ps).val
      = ∑ i, car.packBasis i • MvPolynomial.map (algebraMap B car.P) (Ps i).val := by
  rw [packedMLE, Submodule.coe_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Submodule.coe_smul]
  rfl

/-- **Packing correctness** (design step 1 / safety pillar 3, Hole B). Evaluating the packed
multilinear at (the image of) a base-ring point `pt` reassembles the base evaluations against the
packing basis:
`P̂_packed(algebraMap ∘ pt) = ∑ᵢ (algebraMap (P̂ᵢ(pt))) · bᵢ^P`.
A pure `Basis`/`MLE` fact — no domain hypothesis, no per-instance obligation. -/
theorem packedMLE_eval {m : ℕ} (Ps : car.ιP → MultilinearPoly B m) (pt : Fin m → B) :
    MvPolynomial.eval (fun i => algebraMap B car.P (pt i)) (car.packedMLE Ps).val
      = ∑ i, algebraMap B car.P ((Ps i).val.eval pt) * car.packBasis i := by
  have key : ∀ p : MvPolynomial (Fin m) B,
      MvPolynomial.eval (fun i => algebraMap B car.P (pt i))
          (MvPolynomial.map (algebraMap B car.P) p)
        = algebraMap B car.P (MvPolynomial.eval pt p) := by
    intro p
    induction p using MvPolynomial.induction_on with
    | C a => simp
    | add p q hp hq => simp [map_add, hp, hq]
    | mul_X p n hp => simp [map_mul, hp]
  rw [packedMLE_val, MvPolynomial.eval_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [MvPolynomial.smul_eval, key]
  ring

/-! ### Generic unpacking — the `packedMLE` round-trip (S6, design review F2)

The S6 extractor needs a *section* of `packedMLE`. The generic route is coefficient-wise: the
`i`-th unpacked component takes each packed coefficient to its `i`-th packing-basis
`B`-coordinate. This stays inside pure `Basis`/coefficient algebra — no evaluation detour, no
domain hypothesis — so both round-trip directions hold over any `CommRing` (unlike the
evaluation-interpolation route, which would need `[IsDomain P]`). -/

/-- **Generic unpacking**: the `i`-th component of the unpacked family has coefficients
`coeff d (unpack t' i) = packBasis.repr (coeff d t') i` (see `unpack_coeff`). This is the generic
section of `packedMLE` (design review F2); the DP24 rank-`2^κ` variable-*merging* `unpackMLE` is
a different, Binius-specific map (still a follow-up, see the header). -/
def unpack {m : ℕ} (t' : MultilinearPoly car.P m) : car.ιP → MultilinearPoly B m :=
  fun i =>
    ⟨∑ d ∈ t'.val.support, MvPolynomial.monomial d (car.packBasis.repr (t'.val.coeff d) i), by
      classical
      rw [MvPolynomial.mem_restrictDegree]
      intro s hs j
      have hsub : (∑ d ∈ t'.val.support,
            MvPolynomial.monomial d (car.packBasis.repr (t'.val.coeff d) i)).support
          ⊆ t'.val.support :=
        MvPolynomial.support_sum.trans (Finset.biUnion_subset.mpr fun d hd =>
          MvPolynomial.support_monomial_subset.trans (Finset.singleton_subset_iff.mpr hd))
      exact (MvPolynomial.mem_restrictDegree _ _ _).mp t'.property s (hsub hs) j⟩

/-- The defining coefficient law of `unpack`: coefficients of the `i`-th unpacked component are
the `i`-th packing-basis `B`-coordinates of the packed coefficients. -/
theorem unpack_coeff {m : ℕ} (t' : MultilinearPoly car.P m) (i : car.ιP) (d : Fin m →₀ ℕ) :
    (car.unpack t' i).val.coeff d = car.packBasis.repr (t'.val.coeff d) i := by
  classical
  simp only [unpack, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
  rw [Finset.sum_ite_eq' t'.val.support d]
  split_ifs with hd
  · rfl
  · rw [MvPolynomial.notMem_support_iff.mp hd]
    simp

/-- **Round-trip, packed side**: packing the unpacked family returns the packed polynomial —
`unpack` is a section of `packedMLE`. Pure coefficient algebra + `Basis.sum_repr`;
`CommRing`-only. -/
theorem packedMLE_unpack {m : ℕ} (t' : MultilinearPoly car.P m) :
    car.packedMLE (car.unpack t') = t' := by
  refine Subtype.ext (MvPolynomial.ext _ _ fun d => ?_)
  rw [packedMLE_val, MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, unpack_coeff, smul_eq_mul]
  calc ∑ i, car.packBasis i * algebraMap B car.P (car.packBasis.repr (t'.val.coeff d) i)
      = ∑ i, car.packBasis.repr (t'.val.coeff d) i • car.packBasis i :=
        Finset.sum_congr rfl fun i _ => by rw [Algebra.smul_def, mul_comm]
    _ = t'.val.coeff d := car.packBasis.sum_repr _

/-- **Round-trip, family side**: unpacking the packed family returns the family. Together with
`packedMLE_unpack` this makes `packedMLE` a bijection with explicit inverse `unpack`
(`CommRing`-only); the S6 completeness direction reads the honest claims through this law. -/
theorem unpack_packedMLE {m : ℕ} (Ps : car.ιP → MultilinearPoly B m) :
    car.unpack (car.packedMLE Ps) = Ps := by
  funext i
  refine Subtype.ext (MvPolynomial.ext _ _ fun d => ?_)
  rw [unpack_coeff]
  have hcoeff : (car.packedMLE Ps).val.coeff d
      = ∑ j, (Ps j).val.coeff d • car.packBasis j := by
    rw [packedMLE_val, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_smul, MvPolynomial.coeff_map, smul_eq_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [Algebra.smul_def, mul_comm]
  rw [hcoeff]
  exact congrFun (car.packBasis.repr_sum_self fun j => (Ps j).val.coeff d) i

/-- **`packedMLE` is surjective** (design review F2): every packed multilinear is the packing of
some `B`-family — witnessed constructively by `unpack`, no choice needed. -/
theorem packedMLE_surjective {m : ℕ} :
    Function.Surjective (car.packedMLE (m := m)) :=
  fun t' => ⟨car.unpack t', car.packedMLE_unpack t'⟩

/-- **Boolean read-back of `unpack`**: hypercube evaluations of the `i`-th unpacked component are
the `i`-th packing-basis coordinates of the packed evaluations. Derived from `packedMLE_eval`
through the round-trip (`CommRing`-only); this is the evaluation form the S6 Remark-5 read-back
lemma consumes. -/
theorem unpack_eval_zeroOne {m : ℕ} (t' : MultilinearPoly car.P m) (i : car.ιP)
    (y : Fin m → Fin 2) :
    (car.unpack t' i).val.eval (y : Fin m → B)
      = car.packBasis.repr (t'.val.eval (y : Fin m → car.P)) i := by
  have hpt : (y : Fin m → car.P) = fun j => algebraMap B car.P ((y : Fin m → B) j) :=
    funext fun j => (map_natCast (algebraMap B car.P) _).symm
  conv_rhs => rw [← car.packedMLE_unpack t', hpt, packedMLE_eval]
  simp_rw [← Algebra.smul_def]
  exact (congrFun (car.packBasis.repr_sum_self
    fun j => (car.unpack t' j).val.eval (y : Fin m → B)) i).symm

end RingSwitchCarrier

/-! ## The Binius-stability bridge (label "R2") -/

/-- The **curried family** of a length-`ℓ` multilinear over the first `κ` (Boolean) coordinates:
`curryFamily h_l t v` fixes the first `κ` variables to `v` and is the length-`ℓ'` multilinear whose
Boolean evaluations are `w ↦ t(v, w)` (with `ℓ = ℓ' + κ`). This is the honest currying that DP24's
`packMLE` packs across; `packMLE_eq_packedMLE_curry` identifies the two. Convention note: this
follows DP24 Def. 2.2 in packing the **prefix** coordinates; Flock App. B packs the *suffix*
(`r = (r_hi, r_lo)`) — a pure variable relabeling, and the generic `packedMLE` is
convention-free, so wiring Flock verbatim later needs only that relabeling, not a different
packing. -/
def curryFamily {κ ℓ ℓ' : ℕ} {K : Type} [CommRing K] (h_l : ℓ = ℓ' + κ)
    (t : MultilinearPoly K ℓ) : (Fin κ → Fin 2) → MultilinearPoly K ℓ' :=
  fun v => ⟨MvPolynomial.MLE (fun w : Fin ℓ' → Fin 2 =>
      MvPolynomial.eval (fun i : Fin ℓ =>
        ((if h : i.val < κ then v ⟨i.val, h⟩ else w ⟨i.val - κ, by omega⟩ : Fin 2) : K)) t.val),
    MLE_mem_restrictDegree _⟩

/-- **Binius-stability bridge** (label "R2"). The DP24 rank-`2^κ`
variable-splitting `packMLE` is exactly the generic `packedMLE` applied to the curried family, over
the tower carrier. So the proven Binius packing path is a *use* of the generic definition, not a
parallel one.

The `[Field K] [Field L]` hypotheses come from `towerCarrier` and the multilinear-uniqueness step
(`is_multilinear_eq_iff_eq_evals_zeroOne` needs `[IsDomain L]`); packing itself
(`packedMLE`/`packedMLE_eval`) needs only `CommRing`. -/
theorem packMLE_eq_packedMLE_curry {κ : ℕ} [NeZero κ] {K L : Type} [Field K] [Field L] [Algebra K L]
    {ℓ ℓ' : ℕ} (h_l : ℓ = ℓ' + κ) (β : Basis (Fin κ → Fin 2) K L) (t : MultilinearPoly K ℓ) :
    packMLE κ L K ℓ ℓ' h_l β t = (towerCarrier β).packedMLE (curryFamily h_l t) := by
  apply Subtype.ext
  rw [is_multilinear_eq_iff_eq_evals_zeroOne _ _
    (packMLE κ L K ℓ ℓ' h_l β t).property
    ((towerCarrier β).packedMLE (curryFamily h_l t)).property]
  funext w₀
  simp only [MvPolynomial.toEvalsZeroOne]
  rw [packMLE]
  simp only [MvPolynomial.MLE_eval_zeroOne, Basis.equivFun_symm_apply]
  -- The packed side, via generic packing correctness `packedMLE_eval` (proven above).
  -- `(towerCarrier β)` is not reducible, so we land the lemma into `L`/`β` via `exact` (defeq).
  have hpe : MvPolynomial.eval (fun i : Fin ℓ' => algebraMap K L ((w₀ i : ℕ) : K))
        ((towerCarrier β).packedMLE (curryFamily h_l t)).val
      = ∑ v : Fin κ → Fin 2, algebraMap K L ((curryFamily h_l t v).val.eval
          (fun i => ((w₀ i : ℕ) : K))) * β v :=
    RingSwitchCarrier.packedMLE_eval (towerCarrier β) (curryFamily h_l t)
      (fun i => ((w₀ i : ℕ) : K))
  conv_rhs => rw [show (fun i : Fin ℓ' => ((w₀ i : ℕ) : L))
      = (fun i => algebraMap K L ((w₀ i : ℕ) : K)) from by
        funext i; exact (map_natCast (algebraMap K L) _).symm]
  rw [hpe]
  simp only [curryFamily, MvPolynomial.MLE_eval_zeroOne, Algebra.smul_def]

/-! ## Sanity / testable deliverables (S2 §5.3) -/

section Sanity

-- INV-2: packing correctness `packedMLE_eval` instantiates on the *decoupled* (`P ≠ E`) carrier
-- with a genuine 2-element family (`ιP = Fin 2`), not just the tower carrier.
example (Ps : decoupledToyCarrier.ιP → MultilinearPoly (ZMod 2) 3) (pt : Fin 3 → ZMod 2) :
    MvPolynomial.eval (fun i => algebraMap (ZMod 2) decoupledToyCarrier.P (pt i))
        (decoupledToyCarrier.packedMLE Ps).val
      = ∑ i, algebraMap (ZMod 2) decoupledToyCarrier.P ((Ps i).val.eval pt)
          * decoupledToyCarrier.packBasis i :=
  decoupledToyCarrier.packedMLE_eval Ps pt

-- INV-2: the generic round-trip holds on the *decoupled* `P ≠ E` carrier — a non-domain product
-- ring, pinning that `unpack` and both round-trip directions are `CommRing`-only…
example (t' : MultilinearPoly decoupledToyCarrier.P 3) :
    decoupledToyCarrier.packedMLE (decoupledToyCarrier.unpack t') = t' :=
  decoupledToyCarrier.packedMLE_unpack t'

example (Ps : decoupledToyCarrier.ιP → MultilinearPoly (ZMod 2) 3) :
    decoupledToyCarrier.unpack (decoupledToyCarrier.packedMLE Ps) = Ps :=
  decoupledToyCarrier.unpack_packedMLE Ps

-- …and on the *tower* carrier at full generality (arbitrary field extension, arbitrary rank).
example {K L ι : Type} [Field K] [Field L] [Algebra K L] [Fintype ι] (β : Basis ι K L) (m : ℕ) :
    Function.Surjective ((towerCarrier β).packedMLE (m := m)) :=
  (towerCarrier β).packedMLE_surjective

end Sanity

end RingSwitching.Generic

end
