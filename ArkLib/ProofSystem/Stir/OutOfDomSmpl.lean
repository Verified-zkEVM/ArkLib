/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mirco Richter, Poulami Das (Least Authority)
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.CodingTheory.ListDecodability
import ArkLib.Data.Probability.Notation
import Mathlib.Data.Fintype.Basic

open Finset ListDecodable NNReal Polynomial ProbabilityTheory ReedSolomon
namespace OutOfDomSmpl

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
         {ι : Type} [Fintype ι] [DecidableEq ι]

/-! Section 4.3 [ACFY24] -/

/--returns the domain complement `F \ φ(ι)`-/
def domainComplement (φ : ι ↪ F) : Finset F :=
  Finset.univ \ Finset.image φ.toFun Finset.univ

/-- Pr_{r₀, …, r_{s-1} ← (𝔽 \ φ(ι)) }
      [ ∃ distinct u, u′ ∈ List(C, f, δ) :
        ∀ i < s, u(r_i) = u′(r_i) ]
    here, List (C, f, δ) denotes the list of codewords of C δ-close to f,
    wrt the Relative Hamming distance. -/
noncomputable def listDecodingCollisionProbability
  (φ : ι ↪ F) (f : ι → F) (δ : ℝ) (s degree: ℕ) (Genfun : F → Fin s → F)
  (h_nonempty : Nonempty (domainComplement φ))  : ENNReal :=
  Pr_{let r ←$ᵖ (domainComplement φ)}[ ∃ (u u' : code φ degree),
                                    u.val ≠ u'.val ∧
                                    u.val ∈ relHammingBall (code φ degree) f δ ∧
                                    u'.val ∈ relHammingBall (code φ degree) f δ ∧
                                    ∀ i : Fin s,
                                    let uPoly := decodeLT u
                                    let uPoly' := decodeLT u'
                                    (uPoly : F[X]).eval (Genfun r i)
                                      = (uPoly' : F[X]).eval (Genfun r i)
                                    ]

/--Lemma 4.5.1-/
lemma out_of_dom_smpl_1
  {δ l : ℝ≥0} {s : ℕ} {f : ι → F} {degree : ℕ} {φ : ι ↪ F}
  (C : Set (ι → F)) (hC : C = code φ degree)
  (h_decodable : listDecodable C δ l)
  (h_nonempty : Nonempty (domainComplement φ))
  (Genfun : F → Fin s → F) :
  listDecodingCollisionProbability φ f δ s degree Genfun h_nonempty ≤
    ((l * (l-1) / 2)) * ((degree - 1) / (Fintype.card F - Fintype.card ι))^s
  := by sorry

/--Lemma 4.5.2-/
lemma out_of_dom_smpl_2
  {δ l : ℝ≥0} {s : ℕ} {f : ι → F} {degree : ℕ} {φ : ι ↪ F}
  (C : Set (ι → F)) (hC : C = code φ degree)
  (h_decodable : listDecodable C δ l)
  (h_nonempty : Nonempty (domainComplement φ))
  (Genfun : F → Fin s → F) :
  listDecodingCollisionProbability φ f δ s degree Genfun h_nonempty ≤
    ((l^2 / 2)) * (degree / (Fintype.card F - Fintype.card ι))^s
  := by sorry

end OutOfDomSmpl
