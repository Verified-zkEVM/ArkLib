/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ToMathlib.RingTheory.MvPolynomial.AffineHilbertAlgHom
public import Mathlib.RingTheory.Nullstellensatz

/-!
# Monomial maps

Let `S` be a set of exponent vectors on `τ`. The algebra map `MvPolynomial.monomialMap R S` from
the polynomial ring with one variable for each exponent in `S` to `MvPolynomial τ R` sends the
variable of `m` to the monomial of exponent `m`. It is surjective when every exponent
`Finsupp.single i 1` lies in `S`, since the variables `X i` are then among its coordinates. When
`0 ∈ S`, it sends a polynomial of total degree at most `N` into the span of the monomials whose
exponents are sums of `N` elements of `S`. A polynomial supported on `S` has the preimage
`MvPolynomial.monomialLift`, of total degree at most `1`.

On points, a point `x : τ → E` gives the point `MvPolynomial.monomialPoint S x` of values of the
monomials of `S` at `x`, and evaluation at it is evaluation at `x` after `monomialMap R S`. Over a
field `k`, when the exponents `Finsupp.single i 1` lie in `S`, the map `x ↦ monomialPoint S x` is
injective, a point `x` lies on the zero locus of an ideal `I` exactly when `monomialPoint S x` lies
on the zero locus of `I.comap (monomialMap k S)`, and every point of the zero locus of the kernel of
`monomialMap k S` is of the form `monomialPoint S x`. The ideal transport theorem packages the
prime and principal-open data induced by a surjective ring map, as used for these presentations.

## Main statements

* `MvPolynomial.monomialMap`, `MvPolynomial.monomialMap_surjective`: the monomial map and its
  surjectivity.
* `MvPolynomial.monomialMap_mem_restrictSupport_nsmul`: total degree `N` maps into the span of the
  monomials with exponents in `N • S`.
* `MvPolynomial.monomialLift`, `MvPolynomial.monomialMap_monomialLift`,
  `MvPolynomial.totalDegree_monomialLift_le_one`: the linear preimage.
* `MvPolynomial.monomialPoint`, `MvPolynomial.aeval_monomialPoint`: the point of monomial values.
* `MvPolynomial.monomialPoint_mem_zeroLocus_comap_iff`,
  `MvPolynomial.exists_monomialPoint_eq_of_mem_zeroLocus_ker`,
  `MvPolynomial.monomialPoint_injective`: zero loci under the monomial map.
* `Ideal.map_prime_principalOpenData_of_surjective`: transport of prime, principal-open, and cut
  membership data along a surjective ring map.
-/

@[expose] public section

noncomputable section

open scoped Pointwise

namespace MvPolynomial

variable {τ R : Type*}

section Map

variable [CommSemiring R]

variable (R) in
/-- The algebra map from the polynomial ring with one variable for each exponent of `S` that sends
the variable of `m` to the monomial of exponent `m`. -/
def monomialMap (S : Set (τ →₀ ℕ)) : MvPolynomial S R →ₐ[R] MvPolynomial τ R :=
  aeval fun m ↦ monomial m.1 1

/-- `monomialMap R S` sends the variable of `m` to the monomial of exponent `m`. -/
@[simp]
theorem monomialMap_X {S : Set (τ →₀ ℕ)} (m : S) : monomialMap R S (X m) = monomial m.1 1 :=
  aeval_X _ _

/-- `monomialMap R S` sends the variable of `Finsupp.single i 1` to `X i`. -/
theorem monomialMap_X_single {S : Set (τ →₀ ℕ)} {i : τ} (hi : Finsupp.single i 1 ∈ S) :
    monomialMap R S (X ⟨_, hi⟩) = X i := by
  rw [monomialMap_X, X]

/-- If every exponent `Finsupp.single i 1` lies in `S`, the variables `X i` are coordinates of
`monomialMap R S`, so it is surjective. -/
theorem monomialMap_surjective {S : Set (τ →₀ ℕ)} (hS : ∀ i, Finsupp.single i 1 ∈ S) :
    Function.Surjective (monomialMap R S) := by
  intro P
  induction P using MvPolynomial.induction_on with
  | C c => exact ⟨C c, by simp [monomialMap]⟩
  | add P Q hP hQ =>
    obtain ⟨P', rfl⟩ := hP
    obtain ⟨Q', rfl⟩ := hQ
    exact ⟨P' + Q', map_add _ _ _⟩
  | mul_X P i hP =>
    obtain ⟨P', rfl⟩ := hP
    exact ⟨P' * X ⟨_, hS i⟩, by rw [map_mul, monomialMap_X_single]⟩

/-- If `0 ∈ S`, `monomialMap R S` sends a polynomial of total degree at most `N` to a polynomial
whose exponents are sums of `N` elements of `S`. -/
theorem monomialMap_mem_restrictSupport_nsmul {S : Set (τ →₀ ℕ)} (h0 : 0 ∈ S)
    {P : MvPolynomial S R} {N : ℕ} (hP : P.totalDegree ≤ N) :
    monomialMap R S P ∈ restrictSupport R (N • S) := by
  have h := aeval_mem_of_forall_mul_mem (fun m : S ↦ (monomial m.1 1 : MvPolynomial τ R))
    (T := fun M ↦ restrictSupport R (M • S))
    (fun _ _ hMM' ↦ restrictSupport_mono R (Set.nsmul_right_monotone h0 hMM'))
    (by rw [zero_smul, restrictSupport_zero]; exact Submodule.one_le.mp le_rfl)
    (c := 1) (fun m M t ht ↦ by
      rw [succ_nsmul', restrictSupport_add]
      exact Submodule.mul_mem_mul ((monomial_mem_restrictSupport R).mpr (Or.inl m.2)) ht) hP
  rwa [one_mul] at h

/-- The preimage under `monomialMap R S` of a polynomial supported on `S` that replaces each
monomial by the variable of its exponent. -/
def monomialLift {S : Set (τ →₀ ℕ)} (P : MvPolynomial τ R) (hP : P ∈ restrictSupport R S) :
    MvPolynomial S R :=
  ∑ m : P.support, C (P.coeff m) * X ⟨m, hP m.2⟩

/-- `monomialLift` is a preimage under `monomialMap`. -/
theorem monomialMap_monomialLift {S : Set (τ →₀ ℕ)} (P : MvPolynomial τ R)
    (hP : P ∈ restrictSupport R S) :
    monomialMap R S (monomialLift P hP) = P := by
  classical
  simp only [monomialLift, map_sum, map_mul, monomialMap, aeval_C, aeval_X, algebraMap_eq,
    C_mul_monomial, mul_one]
  rw [Finset.sum_coe_sort P.support fun m ↦ monomial m (P.coeff m)]
  exact P.support_sum_monomial_coeff

/-- `monomialLift` is a linear polynomial. -/
theorem totalDegree_monomialLift_le_one {S : Set (τ →₀ ℕ)} (P : MvPolynomial τ R)
    (hP : P ∈ restrictSupport R S) :
    (monomialLift P hP).totalDegree ≤ 1 := by
  classical
  refine totalDegree_finsetSum_le fun m _ ↦ (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  exact (totalDegree_monomial_le _ _).trans_eq (Finsupp.degree_single _ _)

end Map

section Points

variable {E : Type*}

/-- The point with coordinate `x ^ m = ∏ i, x i ^ m i` at each exponent `m` of `S`. -/
def monomialPoint [CommMonoid E] (S : Set (τ →₀ ℕ)) (x : τ → E) : S → E :=
  fun m ↦ m.1.prod fun i e ↦ x i ^ e

/-- The coordinate of `monomialPoint S x` at `m` is the product of the powers `x i ^ m i`. -/
theorem monomialPoint_apply [CommMonoid E] (S : Set (τ →₀ ℕ)) (x : τ → E) (m : S) :
    monomialPoint S x m = m.1.prod fun i e ↦ x i ^ e :=
  rfl

/-- The coordinate of `monomialPoint S x` at `Finsupp.single i 1` is `x i`. -/
theorem monomialPoint_single [CommMonoid E] {S : Set (τ →₀ ℕ)} (x : τ → E) {i : τ}
    (hi : Finsupp.single i 1 ∈ S) : monomialPoint S x ⟨_, hi⟩ = x i := by
  simp [monomialPoint_apply]

/-- If every exponent `Finsupp.single i 1` lies in `S`, the map `x ↦ monomialPoint S x` is
injective. -/
theorem monomialPoint_injective [CommMonoid E] {S : Set (τ →₀ ℕ)}
    (hS : ∀ i, Finsupp.single i 1 ∈ S) :
    Function.Injective (monomialPoint (E := E) S) := fun x y hxy ↦ funext fun i ↦ by
  rw [← monomialPoint_single x (hS i), ← monomialPoint_single y (hS i), hxy]

/-- Evaluation at `monomialPoint S x` is evaluation at `x` after `monomialMap R S`. -/
theorem aeval_monomialPoint [CommSemiring R] [CommSemiring E] [Algebra R E] {S : Set (τ →₀ ℕ)}
    (x : τ → E) (P : MvPolynomial S R) :
    aeval (monomialPoint S x) P = aeval x (monomialMap R S P) := by
  have h : (aeval x).comp (monomialMap R S) = aeval (monomialPoint S x) :=
    algHom_ext fun m ↦ by simp [monomialPoint_apply, aeval_monomial]
  exact (DFunLike.congr_fun h P).symm

variable {k : Type*} [Field k] [Field E] [Algebra k E]

/-- If every exponent `Finsupp.single i 1` lies in `S`, the point `monomialPoint S x` lies on the
zero locus of `I.comap (monomialMap k S)` exactly when `x` lies on the zero locus of `I`. -/
theorem monomialPoint_mem_zeroLocus_comap_iff {S : Set (τ →₀ ℕ)}
    (hS : ∀ i, Finsupp.single i 1 ∈ S) (I : Ideal (MvPolynomial τ k)) (x : τ → E) :
    monomialPoint S x ∈ zeroLocus E (I.comap (monomialMap k S)) ↔ x ∈ zeroLocus E I := by
  simp only [mem_zeroLocus_iff, Ideal.mem_comap, aeval_monomialPoint]
  refine ⟨fun h p hp ↦ ?_, fun h P hP ↦ h _ hP⟩
  obtain ⟨P, rfl⟩ := monomialMap_surjective hS p
  exact h P hp

/-- If every exponent `Finsupp.single i 1` lies in `S`, every point of the zero locus of the kernel
of `monomialMap k S` is `monomialPoint S x` for the point `x` of its coordinates at the exponents
`Finsupp.single i 1`. -/
theorem exists_monomialPoint_eq_of_mem_zeroLocus_ker {S : Set (τ →₀ ℕ)}
    (hS : ∀ i, Finsupp.single i 1 ∈ S) {z : S → E}
    (hz : z ∈ zeroLocus E (RingHom.ker (monomialMap k S))) :
    ∃ x : τ → E, monomialPoint S x = z := by
  refine ⟨fun i ↦ z ⟨_, hS i⟩, funext fun m ↦ ?_⟩
  let P : MvPolynomial S k := m.1.prod fun i e ↦ X ⟨_, hS i⟩ ^ e
  have hP : monomialMap k S P = monomial m.1 1 := by
    simp only [P, Finsupp.prod, map_prod, map_pow, monomialMap_X_single, monomial_eq, C_1,
      one_mul]
  have hker : X m - P ∈ RingHom.ker (monomialMap k S) := by
    rw [RingHom.mem_ker, map_sub, monomialMap_X, hP, sub_self]
  have hzm := hz _ hker
  rw [map_sub, aeval_X, sub_eq_zero] at hzm
  rw [hzm, monomialPoint_apply]
  simp only [P, Finsupp.prod, map_prod, map_pow, aeval_X]

end Points

end MvPolynomial

namespace Ideal

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A surjective ring map transports a prime ideal and its principal-open cut data.

If `Q` contains the sum of the kernel and the principal ideal generated by `gl`, then its image is
prime, has comap `Q`, contains the image of `gl` and the images of the lifted high cuts, and avoids
the image of `sl` whenever `Q` avoids `sl`. -/
theorem map_prime_principalOpenData_of_surjective
    (φ : R →+* S) (hφ : Function.Surjective φ) (Q : Ideal R) (hQ : Q.IsPrime)
    {g s : S} {gl sl : R}
    (hprincipal : RingHom.ker φ ⊔ Ideal.span {gl} ≤ Q)
    (hgl : φ gl = g) (hsl : φ sl = s) (hslQ : sl ∉ Q)
    (highCuts : List S) (highCutsLift : ∀ f, f ∈ highCuts → R)
    (hhighMap : ∀ f hf, φ (highCutsLift f hf) = f)
    (hhighLift : ∀ f hf, highCutsLift f hf ∈ Q) :
    (Q.map φ).IsPrime ∧ (Q.map φ).comap φ = Q ∧ s ∉ Q.map φ ∧ g ∈ Q.map φ ∧
      (∀ f ∈ highCuts, f ∈ Q.map φ) := by
  have hkerQ : RingHom.ker φ ≤ Q := le_sup_left.trans hprincipal
  have hglQ : gl ∈ Q := hprincipal
    ((le_sup_right : Ideal.span {gl} ≤ RingHom.ker φ ⊔ Ideal.span {gl})
      (Ideal.subset_span (Set.mem_singleton _)))
  have hprime : (Q.map φ).IsPrime :=
    @Ideal.map_isPrime_of_surjective R S (R →+* S) _ _ _ _ φ hφ Q hQ hkerQ
  have hcomap : (Q.map φ).comap φ = Q := by
    rw [Ideal.comap_map_of_surjective φ hφ Q]
    apply sup_eq_left.mpr
    rw [← RingHom.ker_eq_comap_bot]
    exact hkerQ
  refine ⟨hprime, hcomap, ?_, ?_, ?_⟩
  · intro hs
    apply hslQ
    have hsl' : sl ∈ (Q.map φ).comap φ := by
      change φ sl ∈ Q.map φ
      rw [hsl]
      exact hs
    rwa [hcomap] at hsl'
  · rw [← hgl]
    exact Ideal.mem_map_of_mem φ hglQ
  · intro f hf
    rw [← hhighMap f hf]
    exact Ideal.mem_map_of_mem φ (hhighLift f hf)

end Ideal
