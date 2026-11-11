/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: aryaethn
-/
module

public import ArkLib.Data.MvPolynomial.LinearMvExtension
public import ArkLib.Data.Polynomial.PointCollisionProbability

/-!
# BitZ: out-of-domain collisions

An out-of-domain (OOD) sample `ζ ∈ 𝔽` of Round 0 of [BGKLSW26, Construction 4.4] is the point
`(ζ, ζ², ζ⁴, …, ζ^{2^{r-1}})` with `r = log(ℓ/ν)`, at which the prover evaluates the multilinear
polynomials of the codewords in a list-decoding ball. Two distinct multilinear polynomials *collide*
at `ζ` if they agree there. Lemma B.2 bounds the probability that some pair in the list collides.

The substitution `Xᵢ ↦ X^{2^i}` is `LinearMvExtension.powAlgHom`: it sends a nonzero multilinear
polynomial in `r` variables to a nonzero univariate polynomial of degree at most `2^r - 1 = ℓ/ν - 1`
(`LinearMvExtension.powAlgHom_ne_zero`, `LinearMvExtension.natDegree_powAlgHom_le`), so two distinct
multilinear polynomials collide for at most that many values of `ζ`. A union bound over the pairs
of the list gives the count. This file instantiates the point-collision bounds of
`ArkLib/Data/Polynomial` with `powAlgHom`.

## Main statements

* `BitZ.card_collisionSet_le`: among a finite set `L` of multilinear polynomials in `r` variables,
  at most `C(|L|, 2) · (2^r - 1)` values of `ζ` make two distinct members collide.
* `BitZ.prob_not_injOn_eval_le`: for a set `L` of at most `L_δ` multilinear polynomials, a uniform
  `ζ` makes two distinct members collide with probability at most `C(L_δ, 2) · (2^r - 1) / |𝔽|`.
  This is [BGKLSW26, Lemma B.2] with `2^r = ℓ/ν` and `L` the list
  `{Pack̂_ν(g) : Δ(f, Enc_C ∘ Pack_ν(g)) < δ}`; it implies the error
  `κ_OOD ≤ L_δ² · (ℓ/ν - 1) / |𝔽|` of [BGKLSW26, Theorem B.1]. The step "`Enc_C ∘ Pack_ν` is
  injective, so `|L| ≤ L_δ`" is a statement about the code and is not part of this file.

Paper-specific correspondence and remaining formalization work are recorded in the
[BitZ KB](https://github.com/Verified-zkEVM/ArkLib/blob/main/docs/kb/papers/BGKLSW26.md).

## References

* [Bloemen, R., Garreta, A., Kostrzewa, M., Londhe, S., Soukhanov, L., and Wu, J.,
    *BitZ: proofs and commitments in arbitrary rings through binary fields*][BGKLSW26]
-/

@[expose] public section

open Finset Polynomial LinearMvExtension

namespace BitZ

section Counting

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {r : ℕ}

/-- The set of `ζ ∈ F` at which two distinct members of `L` agree at `(ζ, ζ², ζ⁴, …)`. -/
def collisionSet (L : Finset (MvPolynomial (Fin r) F)) : Finset F :=
  {ζ ∈ (univ : Finset F) | ∃ P ∈ L, ∃ Q ∈ L, P ≠ Q ∧
    MvPolynomial.eval (fun i : Fin r => ζ ^ (2 ^ (i : ℕ))) P =
      MvPolynomial.eval (fun i : Fin r => ζ ^ (2 ^ (i : ℕ))) Q}

/-- Among a finite set `L` of multilinear polynomials in `r` variables, the number of `ζ ∈ F` for
which two distinct members agree at `(ζ, ζ², ζ⁴, …, ζ^{2^{r-1}})` is at most
`C(|L|, 2) · (2^r - 1)`. -/
theorem card_collisionSet_le (L : Finset (MvPolynomial (Fin r) F))
    (hL : ∀ P ∈ L, P ∈ MvPolynomial.restrictDegree (Fin r) F 1) :
    #(collisionSet L) ≤ (#L).choose 2 * (2 ^ r - 1) := by
  classical
  set S : Finset (Unit → F[X]) := L.image fun P _ => powAlgHom P
  have hS : #S ≤ #L := card_image_le
  have h := Polynomial.card_le_of_not_injOn_evalTuple (ι := Unit) S (d := 2 ^ r - 1)
    (by
      intro f hf _
      obtain ⟨P, hP, rfl⟩ := mem_image.1 hf
      exact natDegree_powAlgHom_le (hL P hP))
    ((collisionSet L).image fun ζ _ => ζ)
    (by
      intro x hx hinj
      obtain ⟨ζ, hζ, rfl⟩ := mem_image.1 hx
      obtain ⟨-, P, hP, Q, hQ, hPQ, he⟩ := mem_filter.1 hζ
      have hPQ' : powAlgHom P ≠ powAlgHom Q := fun h =>
        hPQ (powAlgHom_injOn (hL P hP) (hL Q hQ) h)
      refine hPQ' (congrFun (hinj (mem_image_of_mem _ hP) (mem_image_of_mem _ hQ) ?_) ())
      funext _ _
      simp [eval_powAlgHom, he])
  rw [card_image_of_injective _ (fun a b h => congrFun h ())] at h
  simpa using h.trans (Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 hS))

end Counting

section Probability

open scoped ProbabilityTheory

variable {F : Type} [Field F] [Fintype F] [SampleableType F] {r : ℕ}

/-- For a set `L` of at most `L_δ` multilinear polynomials in `r` variables, a uniform `ζ ∈ F`
makes two distinct members of `L` agree at `(ζ, ζ², …, ζ^{2^{r-1}})` with probability at most
`C(L_δ, 2) · (2^r - 1) / |F|`. -/
theorem prob_not_injOn_eval_le {L : Set (MvPolynomial (Fin r) F)} {Lδ : ℕ}
    (hL : L ⊆ MvPolynomial.restrictDegree (Fin r) F 1) (hcard : L.encard ≤ Lδ) :
    Pr{let ζ ← $ᵗ F}[¬ Set.InjOn (MvPolynomial.eval fun i : Fin r => ζ ^ (2 ^ (i : ℕ))) L] ≤
      ENNReal.ofReal ((Lδ.choose 2 * (2 ^ r - 1) : ℕ) / (Fintype.card F : ℝ)) := by
  have h := Polynomial.prob_not_injOn_evalTuple_le_of_encard_le (ι := Unit) (κ := Unit)
    (pt := fun ζ _ => ζ) (fun _ _ h => congrFun h ()) (S := (fun P _ => powAlgHom P) '' L)
    (d := 2 ^ r - 1) ((Set.encard_image_le _ _).trans hcard)
    (by rintro _ ⟨P, hP, rfl⟩ _; exact natDegree_powAlgHom_le (hL hP))
  rw [Fintype.card_unit, pow_one] at h
  refine (prEvent_mono _ _ _ ?_).trans h
  intro ζ hζ hinj
  refine hζ fun P hP Q hQ he => ?_
  refine powAlgHom_injOn (hL hP) (hL hQ) (congrFun (hinj (Set.mem_image_of_mem _ hP)
    (Set.mem_image_of_mem _ hQ) ?_) ())
  funext _ _
  simp only [evalTuple_apply, eval_powAlgHom]
  exact he

end Probability

end BitZ
