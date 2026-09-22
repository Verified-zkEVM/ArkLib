/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.Data.Polynomial.Differential.RegularIteration
public import ArkLib.Data.Polynomial.Differential.RegularJetCount
public import ArkLib.ToMathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Counting polynomial solutions through regular witnesses

Let `Q(X, Y₀, ..., Y_d)` be a differential polynomial over a finite domain `F` with `q` elements,
and let `roots` be a finite set of polynomial solutions of `Q = 0`. A point `a` is a regular
witness for a solution `P` in the jet variable `Y_s` when the specialized separant
`(∂Q/∂Y_s)(X, P, D¹P, ...)` does not vanish at `a`. Then the Hasse jet of `P` at `a` is a regular
jet of `Q` at `a`, and there are at most `jetDegree Q s * q ^ d` of those
(`card_filter_isRegularJet_le`).

Suppose that every solution has at most `H` points that are not regular witnesses, and that at
each point distinct solutions with that point as a regular witness have distinct jets. Double
counting the pairs (solution, regular witness) gives

  `#roots * (q - H) ≤ q * (jetDegree Q s * q ^ d)`.

The jet-injectivity hypothesis holds for regular solutions: when `Y_s` is the highest active jet
variable of `Q`, solutions of degree at most `D` are determined by their jets at a regular witness
as soon as the binomial coefficients `(k + s choose s)` for `0 < k`, `k + s ≤ D` are nonzero in
`F` (`BoundedSolution.eq_of_polynomialJet_eq_of_isHighestActiveJet`). The degree of the
specialized separant bounds the number of exceptional points. The resulting count,
`card_mul_sub_le_of_isHighestActiveJet`, has only degree, binomial and separant-nonvanishing
hypotheses.

All counts use truncated subtraction, so no comparison between `H` and `q` is needed.

## Main statements

* `card_mul_sub_le_of_card_bad_le`: the count with arbitrary exceptional sets.
* `card_mul_sub_le_of_natDegree_separant_le`: the exceptional sets are the roots of the specialized
  separants.
* `natCast_choose_ne_zero_of_ringChar`: the binomial hypothesis from the characteristic guard
  `ringChar F = 0 ∨ D < ringChar F`, over a domain.
* `card_mul_sub_le_of_isHighestActiveJet` and
  `BoundedSolution.card_mul_sub_le_of_isHighestActiveJet`: the count of regular solutions, for a
  finite set of polynomials and for a finite set of bounded solutions.

## References

Ported from ArkLib revision a5aa2677fee4e3a79d6bb05136631cce4a08587d, files
`WitnessCounting.lean` and `RegularCounting.lean` in
`ArkLib/Data/CodingTheory/ReedSolomon/HiddenDerivative/RootFinding/FiniteField/`.

* `boundedSolution_counting_pow_le_of_bad` becomes `card_mul_sub_le_of_card_bad_le` and
  `boundedSolution_counting_pow_le` becomes `card_mul_sub_le_of_natDegree_separant_le`. The roots
  form a finite set of polynomials with a solution hypothesis instead of a finite set of
  `BoundedSolution Q D`, since the degree bound is not used; `[Field F]` becomes
  `[CommRing F] [IsDomain F]`; the degree budget `Δ ≥ jetDegree Q s` is replaced by
  `jetDegree Q s` itself; and the product is written as `#roots * (q - H)`. The predicate
  `IsRegularWitness s solution point` is written out as
  `(differentialSpecialization (separant Q s) P).eval point ≠ 0`, which is the same condition by
  `eval_differentialSpecialization`, so `IsRegularWitness`, `BoundedSolution.regularJetAt`,
  `separantBadPoints` and their lemmas are not ported; the canonical exceptional set is
  `(differentialSpecialization (separant Q s) P).roots.toFinset`.
* `regularBranch_counting_pow_le` becomes `BoundedSolution.card_mul_sub_le_of_isHighestActiveJet`,
  a corollary of `card_mul_sub_le_of_isHighestActiveJet`. The characteristic hypothesis
  `D < ringChar F` is replaced by the binomial hypothesis above, which also holds in
  characteristic zero; `natCast_choose_ne_zero_of_ringChar` recovers it from the source guard. The
  weighted-degree hypothesis `differentialWeightedDegree D Q ≤ H` is weakened to
  `differentialWeightedDegree D Q - (D - s) ≤ H`, the sharper separant degree bound of
  `natDegree_differentialSpecialization_separant_le_sub`.
* `polynomialJet_injOn_regularWitness` is inlined into `card_mul_sub_le_of_isHighestActiveJet`.

Deferred: the singular recursion that reduces every solution to a regular branch, and the root
counts over field extensions and by total jet degree that consume these theorems.
-/

@[expose] public section

namespace PolynomialDifferential

noncomputable section

open Finset Polynomial

variable {F : Type*} {d : ℕ}

/-- **Witness counting with arbitrary exceptional sets.** Let `F` be a finite domain with
`q = Nat.card F` elements and `roots` a finite set of solutions of `Q = 0`. Suppose that for each
solution `P` at most `H` points, collected in `bad P`, fail to be regular witnesses, where `a` is a
regular witness when the specialized separant in `Y_s` does not vanish at `a`. Suppose also that at
every point `a`, the Hasse jet at `a` is injective on the solutions having `a` as a regular witness.
Then `#roots * (q - H) ≤ q * (jetDegree Q s * q ^ d)`.

Each point is a regular witness for at most `jetDegree Q s * q ^ d` solutions, because their jets
are distinct regular jets of `Q` at that point; each solution has at least `q - H` regular
witnesses. The jet-injectivity hypothesis is what turns the count of regular jets into a count of
solutions; without it, many solutions may share a jet. -/
theorem card_mul_sub_le_of_card_bad_le [CommRing F] [IsDomain F] [Finite F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (roots : Finset F[X])
    (bad : F[X] → Finset F) (H : ℕ)
    (hsolution : ∀ P ∈ roots, differentialSpecialization Q P = 0)
    (hbad : ∀ P ∈ roots, (bad P).card ≤ H)
    (hcover : ∀ P ∈ roots, ∀ a, a ∉ bad P →
      (differentialSpecialization (separant Q s) P).eval a ≠ 0)
    (hinj : ∀ a, Set.InjOn (polynomialJet (d := d) a)
      {P | P ∈ roots ∧ (differentialSpecialization (separant Q s) P).eval a ≠ 0}) :
    roots.card * (Nat.card F - H) ≤ Nat.card F * (jetDegree Q s * Nat.card F ^ d) := by
  classical
  have := Fintype.ofFinite F
  rw [Nat.card_eq_fintype_card, ← card_univ]
  refine card_mul_sub_le_card_mul_of_card_bad_le
    (fun P a ↦ (differentialSpecialization (separant Q s) P).eval a ≠ 0) bad hbad
    (fun P hP a _ ha ↦ hcover P hP a ha) fun a _ ↦ ?_
  refine le_trans ?_ (card_filter_isRegularJet_le Q s a univ)
  refine card_le_card_of_injOn (polynomialJet a) (fun P hP ↦ ?_) fun P hP P' hP' h ↦ ?_
  · obtain ⟨hroot, hsep⟩ := mem_filter.mp hP
    refine mem_filter.mpr ⟨Fintype.mem_piFinset.mpr fun _ ↦ mem_univ _, ?_, ?_⟩
    · rw [← eval_differentialSpecialization, hsolution P hroot, eval_zero]
    · rwa [← eval_differentialSpecialization]
  · exact hinj a (mem_filter.mp hP) (mem_filter.mp hP') h

/-- **Witness counting with the separant's roots as exceptional sets.** If the specialized
separant in `Y_s` of every solution in `roots` is a nonzero polynomial of degree at most `H`, and
the Hasse jet at each point is injective on the solutions having that point as a regular witness,
then `#roots * (q - H) ≤ q * (jetDegree Q s * q ^ d)` with `q = Nat.card F`.

The nonvanishing hypothesis is needed: a solution whose specialized separant is zero has no
regular witness at all, while Mathlib's root multiset of the zero polynomial is empty, so the
empty exceptional set would not cover its points. -/
theorem card_mul_sub_le_of_natDegree_separant_le [CommRing F] [IsDomain F] [Finite F]
    (Q : DifferentialPolynomial F d) (s : Fin (d + 1)) (roots : Finset F[X]) (H : ℕ)
    (hsolution : ∀ P ∈ roots, differentialSpecialization Q P = 0)
    (hseparant : ∀ P ∈ roots, differentialSpecialization (separant Q s) P ≠ 0)
    (hdegree : ∀ P ∈ roots, (differentialSpecialization (separant Q s) P).natDegree ≤ H)
    (hinj : ∀ a, Set.InjOn (polynomialJet (d := d) a)
      {P | P ∈ roots ∧ (differentialSpecialization (separant Q s) P).eval a ≠ 0}) :
    roots.card * (Nat.card F - H) ≤ Nat.card F * (jetDegree Q s * Nat.card F ^ d) := by
  classical
  refine card_mul_sub_le_of_card_bad_le Q s roots
    (fun P ↦ (differentialSpecialization (separant Q s) P).roots.toFinset) H hsolution
    (fun P hP ↦ ?_) (fun P hP a ha ↦ ?_) hinj
  · exact (Multiset.toFinset_card_le _).trans ((card_roots' _).trans (hdegree P hP))
  · rwa [Multiset.mem_toFinset, mem_roots (hseparant P hP), IsRoot.def] at ha

/-- **Binomial coefficients below the characteristic.** Over a domain with
`ringChar F = 0 ∨ D < ringChar F`, the coefficients `(k + s choose s)` with `0 < k` and
`k + s ≤ D` are nonzero in `F`. This is the binomial hypothesis of
`card_mul_sub_le_of_isHighestActiveJet`. The disjunct `ringChar F = 0` covers characteristic zero.
The strict bound is needed: in characteristic `p`, `(p choose 1) = p` vanishes. -/
theorem natCast_choose_ne_zero_of_ringChar [CommRing F] [IsDomain F] {D s : ℕ}
    (hchar : ringChar F = 0 ∨ D < ringChar F) :
    ∀ k, 0 < k → k + s ≤ D → ((k + s).choose s : F) ≠ 0 := by
  intro k _ hk
  rcases hchar with hzero | hlt
  · exact natCast_ne_zero_of_ringChar_eq_zero_or_lt (Or.inl hzero)
      (Nat.choose_pos (Nat.le_add_left s k)) le_rfl
  · exact Polynomial.natCast_choose_ne_zero_of_lt_charP
      (CharP.char_prime_of_ne_zero F (by omega)) (by omega) (Nat.le_add_left s k)

/-- **Counting regular solutions.** Let `Y_s` be the highest active jet variable of `Q`, and let
`roots` be a finite set of solutions of `Q = 0` of degree at most `D` whose specialized separants
in `Y_s` are nonzero. If the binomial coefficients `(k + s choose s)` for `0 < k`, `k + s ≤ D` are
nonzero in `F` and `differentialWeightedDegree D Q - (D - s) ≤ H`, then

  `#roots * (q - H) ≤ q * (jetDegree Q s * q ^ d)`, where `q = Nat.card F`.

The weighted-degree hypothesis bounds the degree of every specialized separant by `H`. The
binomial and highest-active-jet hypotheses make a solution of degree at most `D` unique given its
jet at a regular witness (`BoundedSolution.eq_of_polynomialJet_eq_of_isHighestActiveJet`). The
binomial hypothesis cannot be dropped: over `ZMod 2`, the equation `y' = 0` with `D = 2` has the
three solutions `1`, `X ^ 2` and `1 + X ^ 2`, every other hypothesis holds with `H = 0`, and
`3 * 2 > 2 * (1 * 2)`; here `(2 choose 1) = 0`. Solutions with zero specialized separant are
handled by the singular recursion, not by this theorem. -/
theorem card_mul_sub_le_of_isHighestActiveJet [CommRing F] [IsDomain F] [Finite F]
    (Q : DifferentialPolynomial F d) {s : Fin (d + 1)} (hs : IsHighestActiveJet Q s)
    {D H : ℕ} (roots : Finset F[X])
    (hsolution : ∀ P ∈ roots, differentialSpecialization Q P = 0)
    (hdegree : ∀ P ∈ roots, P.degree ≤ D)
    (hbinom : ∀ k, 0 < k → k + s.val ≤ D → ((k + s.val).choose s.val : F) ≠ 0)
    (hweight : differentialWeightedDegree D Q - (D - s.val) ≤ H)
    (hseparant : ∀ P ∈ roots, differentialSpecialization (separant Q s) P ≠ 0) :
    roots.card * (Nat.card F - H) ≤ Nat.card F * (jetDegree Q s * Nat.card F ^ d) := by
  refine card_mul_sub_le_of_natDegree_separant_le Q s roots H hsolution hseparant
    (fun P hP ↦ ?_) fun a P hP P' hP' h ↦ ?_
  · exact (natDegree_differentialSpecialization_separant_le_sub Q s P
      (natDegree_le_of_degree_le (hdegree P hP))).trans hweight
  · refine eq_of_polynomialJet_eq_of_isHighestActiveJet Q hs a (hdegree P hP.1)
      (hdegree P' hP'.1) ((hsolution P hP.1).trans (hsolution P' hP'.1).symm) ?_ ?_
    · simpa only [restrictJet_polynomialJet] using congrArg (restrictJet s) h
    · intro k hk hkD
      apply IsLeftCancelMulZero.mul_left_cancel_of_ne_zero
      rw [← eval_differentialSpecialization]
      exact mul_ne_zero (hbinom k hk hkD) hP.2

/-- `card_mul_sub_le_of_isHighestActiveJet` for a finite set of bounded solutions of degree at
most `D`: with the same hypotheses on `Q`, the finite set `roots` of solutions with nonzero
specialized separant in `Y_s` satisfies `#roots * (q - H) ≤ q * (jetDegree Q s * q ^ d)`. -/
theorem BoundedSolution.card_mul_sub_le_of_isHighestActiveJet [CommRing F] [IsDomain F]
    [Finite F] (Q : DifferentialPolynomial F d) {s : Fin (d + 1)} (hs : IsHighestActiveJet Q s)
    {D H : ℕ} (roots : Finset (BoundedSolution Q D))
    (hbinom : ∀ k, 0 < k → k + s.val ≤ D → ((k + s.val).choose s.val : F) ≠ 0)
    (hweight : differentialWeightedDegree D Q - (D - s.val) ≤ H)
    (hseparant : ∀ P ∈ roots, differentialSpecialization (separant Q s) P.polynomial ≠ 0) :
    roots.card * (Nat.card F - H) ≤ Nat.card F * (jetDegree Q s * Nat.card F ^ d) := by
  have hpoly : Function.Injective (BoundedSolution.polynomial (Q := Q) (D := D)) :=
    fun P P' h ↦ Subtype.ext (Subtype.ext h)
  rw [← card_map ⟨_, hpoly⟩]
  refine PolynomialDifferential.card_mul_sub_le_of_isHighestActiveJet Q hs _ (fun P hP ↦ ?_)
    (fun P hP ↦ ?_) hbinom hweight fun P hP ↦ ?_ <;> obtain ⟨P, hmem, rfl⟩ := mem_map.mp hP
  · exact P.equation
  · exact P.degree_le
  · exact hseparant P hmem

end

end PolynomialDifferential
