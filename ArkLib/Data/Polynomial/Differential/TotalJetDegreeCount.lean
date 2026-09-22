/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.BaseChange
public import ArkLib.Data.Polynomial.Differential.ChainWitness
public import ArkLib.ToMathlib.Combinatorics.Enumerative.DoubleCounting
public import ArkLib.ToMathlib.MvPolynomial.SchwartzZippel
public import Mathlib.FieldTheory.Finite.Extension

/-!
# Counting solutions by the total jet degree

Let `F` be a finite domain with `q` elements, `Q ≠ 0` a differential polynomial in
`X, Y₀, …, Y_d` satisfying the cast hypotheses at every jet, and `roots` a finite set of solutions
of `Q = 0` of degree at most `D`. Assume the binomial hypothesis
`((k + s).choose s : F) ≠ 0` for `0 < k`, `k + s ≤ D`, and `differentialWeightedDegree D Q - (D - d)
≤ H`. Then

  `#roots * (q - H) ≤ q * (jetTotalDegree Q * q ^ d)`.

The proof double counts pairs (solution, chain witness). Every solution has at least `q - H` chain
witnesses (`exists_chainWitness`). At a fixed point `a`, the chain-witnessed solutions have
distinct Hasse jets (`ChainWitness.eq_of_polynomialJet_eq`), and these jets are zeros of the
polynomial `jetFiberHom a Q` in `d + 1` variables, which is nonzero when there is a chain witness
at `a` and has total degree at most `jetTotalDegree Q`. The Schwartz–Zippel count
(`MvPolynomial.card_filter_eval_eq_zero_le`) bounds them by `jetTotalDegree Q * q ^ d`. The total
jet degree of `Q` enters once: there is no factor for the length of the singular chain or for the
individual jet degrees.

When `2 * H ≤ q` this gives at most `2 * jetTotalDegree Q * q ^ d` solutions of degree at most
`D`. Coefficient base change along an injective ring homomorphism `F →+* E` into a finite domain
turns this into a bound with `Nat.card E` in place of `q`, for `F` any commutative ring; with
`E = FiniteField.Extension F p e` the bound is `2 * jetTotalDegree Q * q ^ (e * d)`, under
`2 * H ≤ q ^ e`.

## Main statements

* `card_filter_chainWitness_le`: chain-witnessed solutions at one point.
* `card_mul_sub_le_jetTotalDegree_mul` and `BoundedSolution.natCard_mul_sub_le_jetTotalDegree_mul`:
  the division-free count, for a finite set of polynomials and for all bounded solutions.
* `BoundedSolution.natCard_le_two_mul_jetTotalDegree_mul`: the count when `2 * H ≤ q`.
* `BoundedSolution.natCard_le_two_mul_jetTotalDegree_mul_of_injective` and
  `BoundedSolution.natCard_le_two_mul_jetTotalDegree_mul_extension`: the count with witnesses in a
  larger finite domain.

## References

* [Dao, Q., Kominers, S. D., and Thaler, J., *Reed–Solomon Codes Beyond Johnson: Efficient
  Decoding and Smaller Cryptographic Proofs*][DKT26], Appendix A.3
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open Finset Polynomial

variable {F : Type*} {d : ℕ}

open Classical in
/-- **Chain witnesses at one point.** Over a finite domain with `q` elements, let `roots` be a
finite set of polynomials of degree at most `D`, and assume the binomial hypothesis
`((k + s).choose s : F) ≠ 0` for `0 < k`, `k + s ≤ D`. Then at most `jetTotalDegree Q * q ^ d`
elements of `roots` have `a` as a chain witness.

If `jetFiberHom a Q = 0` there are none (`ChainWitness.jetFiberHom_ne_zero`). Otherwise their Hasse
jets at `a` are distinct zeros of `jetFiberHom a Q`, a nonzero polynomial in `d + 1` variables of
total degree at most `jetTotalDegree Q`. -/
theorem card_filter_chainWitness_le [CommRing F] [IsDomain F] [Finite F]
    (Q : DifferentialPolynomial F d) {D : ℕ} (roots : Finset F[X])
    (hdegree : ∀ P ∈ roots, P.degree ≤ D)
    (hbinom : ∀ k s, 0 < k → k + s ≤ D → ((k + s).choose s : F) ≠ 0) (a : F) :
    #{P ∈ roots | ChainWitness Q P a} ≤ jetTotalDegree Q * Nat.card F ^ d := by
  have := Fintype.ofFinite F
  by_cases hzero : jetFiberHom a Q = 0
  · rw [filter_false_of_mem fun P _ h ↦ h.jetFiberHom_ne_zero hzero, card_empty]
    exact Nat.zero_le _
  calc
    #{P ∈ roots | ChainWitness Q P a}
        ≤ #{x ∈ Fintype.piFinset fun _ ↦ (univ : Finset F) |
            MvPolynomial.eval x (jetFiberHom a Q) = 0} := by
      refine card_le_card_of_injOn (polynomialJet a) (fun P hP ↦ ?_) fun P hP P' hP' h ↦ ?_
      · refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun _ ↦ mem_univ _, ?_⟩
        rw [eval_jetFiberHom]
        exact (mem_filter.mp hP).2.jetEvaluation_eq_zero
      · have hP := mem_filter.mp hP
        have hP' := mem_filter.mp hP'
        exact hP.2.eq_of_polynomialJet_eq hP'.2 (hdegree P hP.1) (hdegree P' hP'.1) hbinom h
    _ ≤ (jetFiberHom a Q).totalDegree * #(univ : Finset F) ^ d :=
      MvPolynomial.card_filter_eval_eq_zero_le hzero _
    _ ≤ jetTotalDegree Q * Nat.card F ^ d := by
      rw [card_univ, Fintype.card_eq_nat_card]
      exact Nat.mul_le_mul_right _ (totalDegree_jetFiberHom_le Q a)

/-- **Counting solutions by the total jet degree.** Let `F` be a finite domain with `q` elements,
`Q ≠ 0` satisfying the cast hypotheses at every jet, and `roots` a finite set of solutions of
`Q = 0` of degree at most `D`. If `((k + s).choose s : F) ≠ 0` for `0 < k`, `k + s ≤ D`, and
`differentialWeightedDegree D Q - (D - d) ≤ H`, then

  `#roots * (q - H) ≤ q * (jetTotalDegree Q * q ^ d)`.

Every solution has at most `H` points that are not chain witnesses (`exists_chainWitness`), and
every point is a chain witness for at most `jetTotalDegree Q * q ^ d` solutions
(`card_filter_chainWitness_le`). Truncated subtraction makes the statement true for every `H`.

`Q ≠ 0` is needed: over `ZMod 2` with `D = 0`, the zero equation has `2` solutions and total jet
degree `0`. The binomial hypothesis is needed: over `ZMod 2` with `D = 2` and `H = 0`, `y' = 0`
has the `4` solutions `c + c' X ^ 2`, and `4 * 2 > 2 * (1 * 2)`. The cast hypotheses are what
`exists_chainWitness` uses to produce chain witnesses (without them `Y₀ ^ 2 = 0` over `ZMod 2` has
the solution `0` and no chain witness); no example is recorded here in which the count itself
fails without them. -/
theorem card_mul_sub_le_jetTotalDegree_mul [CommRing F] [IsDomain F] [Finite F]
    {Q : DifferentialPolynomial F d} (hQ : Q ≠ 0) (hcast : ∀ j, JetDegreeCastsNeZero Q j)
    {D H : ℕ} (roots : Finset F[X])
    (hsolution : ∀ P ∈ roots, differentialSpecialization Q P = 0)
    (hdegree : ∀ P ∈ roots, P.degree ≤ D)
    (hbinom : ∀ k s, 0 < k → k + s ≤ D → ((k + s).choose s : F) ≠ 0)
    (hweight : differentialWeightedDegree D Q - (D - d) ≤ H) :
    #roots * (Nat.card F - H) ≤ Nat.card F * (jetTotalDegree Q * Nat.card F ^ d) := by
  classical
  have := Fintype.ofFinite F
  have hex : ∀ P ∈ roots, ∃ R : F[X], R ≠ 0 ∧ R.natDegree ≤ H ∧
      ∀ a, R.eval a ≠ 0 → ChainWitness Q P a := fun P hP ↦ by
    obtain ⟨R, hR, hdeg, hcover⟩ := exists_chainWitness hQ hcast (hsolution P hP)
      (natDegree_le_of_degree_le (hdegree P hP))
    exact ⟨R, hR, hdeg.trans hweight, hcover⟩
  choose! R hR hdeg hcover using hex
  have hfiber := card_filter_chainWitness_le Q roots hdegree hbinom
  simp only [Nat.card_eq_fintype_card, ← card_univ] at hfiber ⊢
  refine card_mul_sub_le_card_mul_of_card_bad_le (fun P a ↦ ChainWitness Q P a)
    (fun P ↦ (R P).roots.toFinset) (fun P hP ↦ ?_) (fun P hP a _ ha ↦ ?_) fun a _ ↦ ?_
  · exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (hdeg P hP))
  · exact hcover P hP a (by rwa [Multiset.mem_toFinset, mem_roots (hR P hP), IsRoot.def] at ha)
  · convert hfiber a using 2
    ext P
    simp [mem_bipartiteBelow]

/-- `card_mul_sub_le_jetTotalDegree_mul` for all solutions of degree at most `D`:
`Nat.card (BoundedSolution Q D) * (q - H) ≤ q * (jetTotalDegree Q * q ^ d)`. -/
theorem BoundedSolution.natCard_mul_sub_le_jetTotalDegree_mul [CommRing F] [IsDomain F]
    [Finite F] {Q : DifferentialPolynomial F d} (hQ : Q ≠ 0)
    (hcast : ∀ j, JetDegreeCastsNeZero Q j) {D H : ℕ}
    (hbinom : ∀ k s, 0 < k → k + s ≤ D → ((k + s).choose s : F) ≠ 0)
    (hweight : differentialWeightedDegree D Q - (D - d) ≤ H) :
    Nat.card (BoundedSolution Q D) * (Nat.card F - H) ≤
      Nat.card F * (jetTotalDegree Q * Nat.card F ^ d) := by
  classical
  have := Fintype.ofFinite (BoundedSolution Q D)
  have hpoly : Function.Injective (BoundedSolution.polynomial (Q := Q) (D := D)) :=
    fun P P' h ↦ Subtype.ext (Subtype.ext h)
  rw [Nat.card_eq_fintype_card, ← card_univ, ← card_map ⟨_, hpoly⟩]
  refine card_mul_sub_le_jetTotalDegree_mul hQ hcast _ (fun P hP ↦ ?_) (fun P hP ↦ ?_) hbinom
    hweight <;> obtain ⟨P, -, rfl⟩ := mem_map.mp hP
  · exact P.equation
  · exact P.degree_le

/-- **At most `2 * jetTotalDegree Q * q ^ d` solutions.** Under the hypotheses of
`BoundedSolution.natCard_mul_sub_le_jetTotalDegree_mul`, if `2 * H ≤ q` then `Q = 0` has at most
`2 * jetTotalDegree Q * q ^ d` solutions of degree at most `D`: at least half of the points are
chain witnesses for each solution. -/
theorem BoundedSolution.natCard_le_two_mul_jetTotalDegree_mul [CommRing F] [IsDomain F]
    [Finite F] {Q : DifferentialPolynomial F d} (hQ : Q ≠ 0)
    (hcast : ∀ j, JetDegreeCastsNeZero Q j) {D H : ℕ}
    (hbinom : ∀ k s, 0 < k → k + s ≤ D → ((k + s).choose s : F) ≠ 0)
    (hweight : differentialWeightedDegree D Q - (D - d) ≤ H) (hlarge : 2 * H ≤ Nat.card F) :
    Nat.card (BoundedSolution Q D) ≤ 2 * jetTotalDegree Q * Nat.card F ^ d := by
  have hcount := natCard_mul_sub_le_jetTotalDegree_mul hQ hcast hbinom hweight
  refine Nat.le_of_mul_le_mul_left ?_ (Nat.card_pos (α := F))
  calc
    Nat.card F * Nat.card (BoundedSolution Q D) ≤
        Nat.card (BoundedSolution Q D) * (2 * (Nat.card F - H)) := by
      rw [mul_comm]
      exact Nat.mul_le_mul_left _ (by omega)
    _ = 2 * (Nat.card (BoundedSolution Q D) * (Nat.card F - H)) := by ring
    _ ≤ 2 * (Nat.card F * (jetTotalDegree Q * Nat.card F ^ d)) := Nat.mul_le_mul_left 2 hcount
    _ = Nat.card F * (2 * jetTotalDegree Q * Nat.card F ^ d) := by ring

/-- **Witnesses in a larger domain.** Let `f : F →+* E` be an injective ring homomorphism into a
finite domain `E`. If `Q ≠ 0` satisfies the cast hypotheses, `((k + s).choose s : F) ≠ 0` for
`0 < k`, `k + s ≤ D`, `differentialWeightedDegree D Q - (D - d) ≤ H` and `2 * H ≤ Nat.card E`,
then `Q = 0` has at most `2 * jetTotalDegree Q * Nat.card E ^ d` solutions over `F` of degree at
most `D`.

The solutions over `F` inject into those of `Q.map f` over `E`
(`BoundedSolution.natCard_le_natCard_map`), and every hypothesis transfers along `f`. `F` itself
need not be finite or a domain. -/
theorem BoundedSolution.natCard_le_two_mul_jetTotalDegree_mul_of_injective {E : Type*}
    [CommRing F] [CommRing E] [IsDomain E] [Finite E] {f : F →+* E} (hf : Function.Injective f)
    {Q : DifferentialPolynomial F d} (hQ : Q ≠ 0) (hcast : ∀ j, JetDegreeCastsNeZero Q j)
    {D H : ℕ} (hbinom : ∀ k s, 0 < k → k + s ≤ D → ((k + s).choose s : F) ≠ 0)
    (hweight : differentialWeightedDegree D Q - (D - d) ≤ H) (hlarge : 2 * H ≤ Nat.card E) :
    Nat.card (BoundedSolution Q D) ≤ 2 * jetTotalDegree Q * Nat.card E ^ d := by
  have hQE : MvPolynomial.map f Q ≠ 0 := fun h ↦
    hQ (MvPolynomial.map_injective f hf (by rw [h, map_zero]))
  have hcastE (j : Fin (d + 1)) : JetDegreeCastsNeZero (MvPolynomial.map f Q) j :=
    (jetDegreeCastsNeZero_map_iff hf Q j).mpr (hcast j)
  have hbinomE : ∀ k s, 0 < k → k + s ≤ D → ((k + s).choose s : E) ≠ 0 := fun k s hk hks ↦ by
    rw [← map_natCast f]
    exact (map_ne_zero_iff f hf).mpr (hbinom k s hk hks)
  have hweightE : differentialWeightedDegree D (MvPolynomial.map f Q) - (D - d) ≤ H := by
    rwa [differentialWeightedDegree_map_eq f hf]
  calc
    Nat.card (BoundedSolution Q D) ≤ Nat.card (BoundedSolution (MvPolynomial.map f Q) D) :=
      natCard_le_natCard_map hf Q D
    _ ≤ 2 * jetTotalDegree (MvPolynomial.map f Q) * Nat.card E ^ d :=
      natCard_le_two_mul_jetTotalDegree_mul hQE hcastE hbinomE hweightE hlarge
    _ = 2 * jetTotalDegree Q * Nat.card E ^ d := by rw [jetTotalDegree_map_eq hf]

/-- **Witnesses in the extension of degree `e`.** Over a finite field `F` with `q` elements, under
the hypotheses of `BoundedSolution.natCard_le_two_mul_jetTotalDegree_mul` with `2 * H ≤ q ^ e` for
some `0 < e`, `Q = 0` has at most `2 * jetTotalDegree Q * q ^ (e * d)` solutions of degree at most
`D`. The witnesses are taken in `FiniteField.Extension F (ringChar F) e`, which has `q ^ e`
elements; the hypotheses stay those over `F`. -/
theorem BoundedSolution.natCard_le_two_mul_jetTotalDegree_mul_extension [Field F] [Finite F]
    {Q : DifferentialPolynomial F d} (hQ : Q ≠ 0) (hcast : ∀ j, JetDegreeCastsNeZero Q j)
    {D H : ℕ} (hbinom : ∀ k s, 0 < k → k + s ≤ D → ((k + s).choose s : F) ≠ 0)
    (hweight : differentialWeightedDegree D Q - (D - d) ≤ H) {e : ℕ} (he : 0 < e)
    (hlarge : 2 * H ≤ Nat.card F ^ e) :
    Nat.card (BoundedSolution Q D) ≤ 2 * jetTotalDegree Q * Nat.card F ^ (e * d) := by
  have : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  have : NeZero e := ⟨he.ne'⟩
  have hcard := FiniteField.natCard_extension F (ringChar F) e
  have h := natCard_le_two_mul_jetTotalDegree_mul_of_injective
    (algebraMap F (FiniteField.Extension F (ringChar F) e)).injective hQ hcast hbinom hweight
    (hcard ▸ hlarge)
  rwa [hcard, ← pow_mul] at h

end

end PolynomialDifferential
