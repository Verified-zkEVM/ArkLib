/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.LinearCombination
import ArkLib.Data.Lattices.Vectors
import ArkLib.ProofSystem.RingSwitching.Transport.Eval

/-!
  # Quotient presentations — the data layer of `Lift`

  A ring `S` is *presented* as a quotient `R[X]/(φ)` when its elements carry canonical
  polynomial representatives below a monic modulus. That is all the `Lift`
  ring switch consumes — cyclotomic rings `R_q = Z_q[X]/(X^d + 1)` are one instance, not the
  definition. This file abstracts exactly that data, mirroring the
  `CyclotomicModulus`/`IsCyclotomic` split of the lattice layer:

  * `Presentation R S` — proof-free data: the monic modulus `φ : R[X]` and a canonical
    representative map `rep : S → R[X]`;
  * `IsPresentation P` — the laws: `φ` monic, representatives of degree `< deg φ`, `rep`
    injective, and `rep` additive/multiplicative *up to multiples of `φ`* (the coset laws).

  On top of the laws, this file proves the whole lift algebra of the switch. Here “lift” has
  its literal quotient-algebra meaning: replace equality modulo the modulus by an exact
  polynomial equality carrying an explicit quotient witness. The file supplies the
  equivalence between ring equations over `S` and polynomial identities over `R[X]` with an
  explicit quotient witness:

  `(M *ᵥ z) i = y i  in S    ↔    ∑ⱼ rep(Mᵢⱼ)·rep(zⱼ) = rep(yᵢ) + φ·ρᵢ  in R[X]`

  * the **exactness layer**: a modulus-multiple of degree below the monic modulus vanishes
    (`eq_zero_of_modulus_dvd_of_natDegree_lt`), so `rep` is additive *on the nose*
    (`rep_zero`, `rep_add`, `rep_neg`, `rep_sum`) — strictly stronger than the coset laws it
    is derived from;
  * `Presentation.rowSum` — the lifted left-hand side of a row — and its degree bound
    `≤ 2·deg φ − 2`;
  * `Presentation.mulVec_eq_of_rowSum_eq` / `Presentation.exists_rowSum_eq_of_mulVec_eq` —
    the two directions of the correspondence: lifted identities *descend* to `S`, and true
    row equations *lift* with an explicit quotient polynomial;
  * `Presentation.mulVec_eq_of_evalAt_rowSum` — the packaged per-row recovery engine: a
    lifted row identity that holds under `evalAt` at `2·deg φ` pairwise-distinct points of a
    field already descends to the row equation over `S`. (`evalAt` and the interpolation
    kernel it uses live one level up, in the family-shared
    `ArkLib/ProofSystem/RingSwitching/Transport/Eval.lean`.)

  No protocol imports: this is the algebra half; the committed-scalar protocol half lives in
  `Lift/Reduction.lean`.  Matrix–vector products are ArkLib's computable
  `ArkLib.Lattices.matVecMul`/`dot` (`Data/Lattices/Vectors.lean`), not Mathlib's
  `Matrix.mulVec`: instances such as `Rq Φ` have noncomputable ring instances, and the
  relations downstream are stated against the computable product.

  ## Instantiations

  The cyclotomic instance `cyclotomicPresentation` (with laws discharged from
  `Data/Lattices/CyclotomicRing/QuotientLift.lean`) realizes [NOZ26] Lemma 9's algebra —
  the [HMZ25] lift — over `Rq Φ`; see
  `Commitments/Functional/Hachi/RingSwitch/Reduction.lean`.

  ## References

  * [Huang, M.-Y. M., Mao, X., and Zhang, J., *Sublinear Proofs over Polynomial Rings*][HMZ25]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

open Polynomial ArkLib.Lattices

namespace RingSwitching.Lift

-- `evalAt`, `evalAt_apply`, and the interpolation kernel `eq_of_evalAt_eq` were lifted to the
-- family-shared `ArkLib/ProofSystem/RingSwitching/Transport/Eval.lean` (namespace `RingSwitching`);
-- unqualified references below resolve to them through the parent namespace.

/-! ## The presentation data and its laws -/

/-- Proof-free presentation data for a ring `S` as a quotient `R[X]/(φ)`: the modulus and a
canonical representative map. The laws live in `IsPresentation`, mirroring the
`CyclotomicModulus`/`IsCyclotomic` split, so that instances (e.g. Hachi's `Rq Φ`) can be
constructed without positivity or well-formedness side conditions. -/
structure Presentation (R S : Type*) [CommRing R] [CommRing S] where
  /-- The modulus polynomial presenting `S`, e.g. `X^d + 1`. -/
  modulus : Polynomial R
  /-- Canonical (degree-reduced) representative of a ring element. -/
  rep : S → Polynomial R

/-- The presentation laws: monic modulus, degree-reduced injective representatives, and the
coset laws (`rep` is additive and multiplicative up to multiples of the modulus). The two
coset laws are the base compatibility facts; everything else the switch needs — sums, dot
products, the quotient-witness correspondence — is derived below. -/
class IsPresentation {R S : Type*} [CommRing R] [CommRing S]
    (P : Presentation R S) : Prop where
  /-- The modulus is monic (so division with remainder applies). -/
  monic : P.modulus.Monic
  /-- Representatives are degree-reduced. In particular the modulus has positive degree. -/
  natDegree_rep_lt : ∀ s : S, (P.rep s).natDegree < P.modulus.natDegree
  /-- Distinct elements have distinct representatives. -/
  rep_injective : Function.Injective P.rep
  /-- Coset law for addition. -/
  modulus_dvd_rep_add : ∀ a b : S, P.modulus ∣ P.rep (a + b) - (P.rep a + P.rep b)
  /-- Coset law for multiplication. -/
  modulus_dvd_rep_mul : ∀ a b : S, P.modulus ∣ P.rep (a * b) - P.rep a * P.rep b

namespace Presentation

variable {R S : Type*} [CommRing R] [CommRing S] (P : Presentation R S) [IsPresentation P]

/-- The modulus has positive degree: even `0` has a representative of smaller degree. -/
theorem natDegree_modulus_pos : 0 < P.modulus.natDegree :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) (IsPresentation.natDegree_rep_lt (P := P) 0)

/-- The representative of `0` is a multiple of the modulus (in fact the coset laws force it). -/
theorem modulus_dvd_rep_zero : P.modulus ∣ P.rep 0 := by
  have h := IsPresentation.modulus_dvd_rep_add (P := P) 0 0
  rw [add_zero] at h
  have h' : P.rep 0 - (P.rep 0 + P.rep 0) = -P.rep 0 := by ring
  rw [h'] at h
  exact dvd_neg.mp h

/-- Coset law for finite sums, by induction from the addition law. -/
theorem modulus_dvd_rep_sum {ι : Type*} (t : Finset ι) (f : ι → S) :
    P.modulus ∣ P.rep (∑ j ∈ t, f j) - ∑ j ∈ t, P.rep (f j) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using P.modulus_dvd_rep_zero
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have h1 := IsPresentation.modulus_dvd_rep_add (P := P) (f a) (∑ j ∈ t, f j)
      have h2 := dvd_add h1 ih
      convert h2 using 1
      ring

/-- Two elements whose representatives differ by a multiple of the modulus are equal: the
difference has degree below the monic modulus, so divisibility forces it to vanish. -/
theorem eq_of_modulus_dvd {a b : S} (h : P.modulus ∣ P.rep a - P.rep b) : a = b := by
  have hz : P.rep a - P.rep b = 0 := by
    obtain ⟨c, hc⟩ := h
    rcases eq_or_ne c 0 with rfl | hc0
    · simpa using hc
    · exfalso
      have hne : P.modulus.leadingCoeff * c.leadingCoeff ≠ 0 := by
        rw [(IsPresentation.monic (P := P)).leadingCoeff, one_mul]
        exact Polynomial.leadingCoeff_ne_zero.mpr hc0
      have hdeg := Polynomial.natDegree_mul' hne
      have h1 := IsPresentation.natDegree_rep_lt (P := P) a
      have h2 := IsPresentation.natDegree_rep_lt (P := P) b
      have h3 : (P.rep a - P.rep b).natDegree < P.modulus.natDegree :=
        lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt h1 h2)
      rw [hc, hdeg] at h3
      omega
  exact IsPresentation.rep_injective (P := P) (sub_eq_zero.mp hz)

/-! ## The exactness layer: `rep` is additive on the nose

The coset laws only bound the additive defects up to modulus multiples, but each defect has
degree below the monic modulus, so it vanishes — `rep` is exactly additive. These are strictly
stronger than the shipped divisibility lemmas and come free to every instance. -/

/-- **Vanishing kernel**: a modulus-multiple of degree below the monic modulus is zero (a
nonzero multiple of a monic polynomial has at least the modulus degree). -/
theorem eq_zero_of_modulus_dvd_of_natDegree_lt {p : Polynomial R} (h : P.modulus ∣ p)
    (hdeg : p.natDegree < P.modulus.natDegree) : p = 0 := by
  obtain ⟨c, hc⟩ := h
  rcases eq_or_ne c 0 with rfl | hc0
  · simpa using hc
  · exfalso
    have hne : P.modulus.leadingCoeff * c.leadingCoeff ≠ 0 := by
      rw [(IsPresentation.monic (P := P)).leadingCoeff, one_mul]
      exact Polynomial.leadingCoeff_ne_zero.mpr hc0
    have hmul := Polynomial.natDegree_mul' hne
    rw [hc, hmul] at hdeg
    omega

/-- The representative of `0` is exactly `0`. -/
theorem rep_zero : P.rep (0 : S) = 0 :=
  P.eq_zero_of_modulus_dvd_of_natDegree_lt P.modulus_dvd_rep_zero
    (IsPresentation.natDegree_rep_lt (P := P) 0)

/-- `rep` is exactly additive: the coset defect has degree below the monic modulus. -/
theorem rep_add (a b : S) : P.rep (a + b) = P.rep a + P.rep b := by
  have hz : P.rep (a + b) - (P.rep a + P.rep b) = 0 := by
    refine P.eq_zero_of_modulus_dvd_of_natDegree_lt
      (IsPresentation.modulus_dvd_rep_add (P := P) a b) ?_
    have h1 := IsPresentation.natDegree_rep_lt (P := P) (a + b)
    have h2 := IsPresentation.natDegree_rep_lt (P := P) a
    have h3 := IsPresentation.natDegree_rep_lt (P := P) b
    have h4 := Polynomial.natDegree_add_le (P.rep a) (P.rep b)
    have h5 := Polynomial.natDegree_sub_le (P.rep (a + b)) (P.rep a + P.rep b)
    omega
  linear_combination hz

/-- `rep` commutes with negation exactly. -/
theorem rep_neg (a : S) : P.rep (-a) = -P.rep a := by
  have h := P.rep_add a (-a)
  rw [add_neg_cancel, P.rep_zero] at h
  linear_combination -h

/-- `rep` commutes with finite sums exactly — the exact form of `modulus_dvd_rep_sum`. -/
theorem rep_sum {ι : Type*} (t : Finset ι) (f : ι → S) :
    P.rep (∑ j ∈ t, f j) = ∑ j ∈ t, P.rep (f j) := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using P.rep_zero
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, P.rep_add, ih]

/-! ## The lifted rows and the quotient-witness correspondence -/

variable {n μ : ℕ}

/-- The `i`-th lifted row's left-hand side `∑ⱼ rep(Mᵢⱼ)·rep(zⱼ) ∈ R[X]`, on canonical
representatives (each factor has degree `< d`, so the row sum has degree `≤ 2d − 2`). -/
noncomputable def rowSum (M : PolyMatrix S n μ) (z : PolyVec S μ) (i : Fin n) :
    Polynomial R :=
  ∑ j, P.rep (M i j) * P.rep (z j)

/-- Structural degree bound of a lifted row: `deg (∑ⱼ rep(Mᵢⱼ)·rep(zⱼ)) ≤ 2d − 2`. -/
theorem natDegree_rowSum_le (M : PolyMatrix S n μ) (z : PolyVec S μ) (i : Fin n) :
    (P.rowSum M z i).natDegree ≤ 2 * P.modulus.natDegree - 2 := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)
  have h1 := IsPresentation.natDegree_rep_lt (P := P) (M i j)
  have h2 := IsPresentation.natDegree_rep_lt (P := P) (z j)
  have h3 := Polynomial.natDegree_mul_le (p := P.rep (M i j)) (q := P.rep (z j))
  omega

/-- The representative of a matrix-vector row agrees with the lifted row up to a multiple of
the modulus — the summed coset law. -/
theorem modulus_dvd_rep_mulVec_sub_rowSum (M : PolyMatrix S n μ) (z : PolyVec S μ)
    (i : Fin n) : P.modulus ∣ P.rep ((M *ᵥ z) i) - P.rowSum M z i := by
  have hmv : (M *ᵥ z) i = ∑ j, M i j * z j := by
    rw [matVecMul_apply, dot_eq_sum]
  have h1 := P.modulus_dvd_rep_sum Finset.univ (fun j => M i j * z j)
  have h2 : P.modulus ∣ (∑ j, P.rep (M i j * z j)) - ∑ j, P.rep (M i j) * P.rep (z j) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.dvd_sum (fun j _ => IsPresentation.modulus_dvd_rep_mul (P := P) (M i j) (z j))
  have h3 := dvd_add h1 h2
  rw [hmv, rowSum]
  convert h3 using 1
  ring

/-- **Quotient descent** (the `⇐` direction of the quotient-witness correspondence — the one
the extraction consumes): a per-row lift identity in `R[X]` descends to the row equation
over `S`. -/
theorem mulVec_eq_of_rowSum_eq {M : PolyMatrix S n μ} {z : PolyVec S μ}
    {y : PolyVec S n} {i : Fin n} {ρ : Polynomial R}
    (h : P.rowSum M z i = P.rep (y i) + P.modulus * ρ) :
    (M *ᵥ z) i = y i := by
  apply P.eq_of_modulus_dvd
  have h1 := P.modulus_dvd_rep_mulVec_sub_rowSum M z i
  have h2 : P.modulus ∣ P.rowSum M z i - P.rep (y i) := ⟨ρ, by rw [h]; ring⟩
  have h3 := dvd_add h1 h2
  convert h3 using 1
  ring

/-- **Quotient witness** (the `⇒`/honest direction): a row equation over `S` lifts to an
`R[X]` identity with an explicit quotient polynomial `ρ := (rowSum − rep yᵢ) /ₘ φ` of degree
`≤ d − 2`. -/
theorem exists_rowSum_eq_of_mulVec_eq {M : PolyMatrix S n μ} {z : PolyVec S μ}
    {y : PolyVec S n} {i : Fin n} (h : (M *ᵥ z) i = y i) :
    ∃ ρ : Polynomial R, ρ.natDegree ≤ P.modulus.natDegree - 2 ∧
      P.rowSum M z i = P.rep (y i) + P.modulus * ρ := by
  have hdvd : P.modulus ∣ P.rowSum M z i - P.rep (y i) := by
    have h1 := P.modulus_dvd_rep_mulVec_sub_rowSum M z i
    rw [h] at h1
    simpa [neg_sub] using dvd_neg.mpr h1
  refine ⟨(P.rowSum M z i - P.rep (y i)) /ₘ P.modulus, ?_, ?_⟩
  · rw [Polynomial.natDegree_divByMonic _ (IsPresentation.monic (P := P))]
    have h1 := P.natDegree_rowSum_le M z i
    have h2 := IsPresentation.natDegree_rep_lt (P := P) (y i)
    have h3 := Polynomial.natDegree_sub_le (P.rowSum M z i) (P.rep (y i))
    have h4 := P.natDegree_modulus_pos
    omega
  · have hmod : (P.rowSum M z i - P.rep (y i)) %ₘ P.modulus = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd (IsPresentation.monic (P := P))).mpr hdvd
    have hdiv := Polynomial.modByMonic_add_div (P.rowSum M z i - P.rep (y i)) P.modulus
    rw [hmod, zero_add] at hdiv
    linear_combination -hdiv

/-- **The per-row recovery engine**, over an arbitrary presentation: if a row's lifted
equation (with quotient `ρ` of degree `≤ d − 1`) holds under `evalAt` at `2d`
pairwise-distinct points of a field `F`, the row equation holds over `S`
([NOZ26] Lemma 9). The defect
polynomial has degree `< 2d`, so the `2d` roots kill it; the resulting `R[X]` identity
descends along the coset laws. The degree `d` is an explicit parameter tied to the modulus by
`hd`, so instances can state witnesses against their own degree expression.

The `2d` is **tight**, and it is the load-bearing constant of the whole lift: `P.rowSum M z i`
multiplies two degree-`< d` representatives, so `natDegree ≤ 2d − 2`, while
`P.rep (y i) + P.modulus * ρ` has `natDegree ≤ max (d − 1) (d + (d − 1)) = 2d − 1`. Both are
`< 2d`, so `2d` pairwise-distinct points force equality — matching [NOZ26] Lemma 9's "degree at
most `2d − 1`".

Note that `hA : Function.Injective A` with `A : Fin (2 * d) → F` implicitly requires
`2d ≤ ‖F‖`: over a carrier smaller than `2d` the hypothesis is unsatisfiable, so while the lemma
itself is proved unconditionally, no *application* to such an `F` can exist. This is benign in
context (the CWSS challenge tree could not exist either, and the paper's `(2d − 1)/|F_{q^k}|`
soundness error is only meaningful for `|F_{q^k}| > 2d`), but it is worth stating so that nobody
instantiates at a small carrier and believes something has been proved. -/
theorem mulVec_eq_of_evalAt_rowSum {F : Type*} [Field F] {φF : R →+* F}
    (hφF : Function.Injective φF) {d : ℕ} (hd : P.modulus.natDegree = d)
    {M : PolyMatrix S n μ} {z : PolyVec S μ} {y : PolyVec S n} {i : Fin n}
    {ρ : Polynomial R} (hρ : ρ.natDegree ≤ d - 1)
    {A : Fin (2 * d) → F} (hA : Function.Injective A)
    (h : ∀ j, evalAt φF (A j) (P.rowSum M z i)
          = evalAt φF (A j) (P.rep (y i))
            + evalAt φF (A j) P.modulus * evalAt φF (A j) ρ) :
    (M *ᵥ z) i = y i := by
  refine P.mulVec_eq_of_rowSum_eq (ρ := ρ) ?_
  refine eq_of_evalAt_eq hφF (N := 2 * d) ?_ ?_ hA ?_
  · have h1 := P.natDegree_rowSum_le M z i
    have h2 := P.natDegree_modulus_pos
    omega
  · have h1 := IsPresentation.natDegree_rep_lt (P := P) (y i)
    have h2 := Polynomial.natDegree_mul_le (p := P.modulus) (q := ρ)
    have h3 := Polynomial.natDegree_add_le (P.rep (y i)) (P.modulus * ρ)
    have h4 := P.natDegree_modulus_pos
    omega
  · intro j
    rw [map_add, map_mul]
    exact h j

end Presentation

end RingSwitching.Lift
