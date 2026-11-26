/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module

public import ArkLib.ProofSystem.ConstraintSystem.R1CS
public import ArkLib.Data.MvPolynomial.Split
public import Mathlib.Data.Nat.Log

/-!
# Spartan's R1CS layout

The assignment is the public prefix followed by a witness suffix of power-of-two length.
Integer indices use little-endian Boolean coordinates: the witness varies in the low coordinates,
while every high coordinate is one. This unequal-suffix layout is the Spartan API; equal halves
are its special case with one high coordinate. No distinguished constant-one variable is inserted.
Matrix multilinear extensions take the row point first and the column point second.

An arbitrary R1CS instance embeds by padding its public and witness blocks separately. This
preserves and reflects satisfaction, with witness recovery given by restriction to the original
witness coordinates. Polynomial views are noncomputable because the sparse `MvPolynomial`
representation requires a nonconstructive coefficient equality test over an arbitrary ring.
The finite tables, dimension selection, embeddings, and witness recovery are computable.
-/

@[expose] public section

namespace Spartan

/-- The base-two logarithms of the row, column, and witness dimensions. -/
structure PublicParams where
  ℓ_m : ℕ
  ℓ_n : ℕ
  ℓ_w : ℕ
  ℓ_w_le_ℓ_n : ℓ_w ≤ ℓ_n := by omega

namespace PublicParams

/-- The power-of-two R1CS dimensions represented by the parameters. -/
def toSizeR1CS (pp : PublicParams) : R1CS.Size where
  m := 2 ^ pp.ℓ_m
  n := 2 ^ pp.ℓ_n
  n_w := 2 ^ pp.ℓ_w
  n_w_le_n := Nat.pow_le_pow_of_le (by decide) pp.ℓ_w_le_ℓ_n

/-- Choose enough rows and equal-sized public and witness blocks for any R1CS dimensions. -/
def forSize (sz : R1CS.Size) : PublicParams where
  ℓ_m := Nat.clog 2 sz.m
  ℓ_n := Nat.clog 2 (max sz.n_x sz.n_w) + 1
  ℓ_w := Nat.clog 2 (max sz.n_x sz.n_w)
  ℓ_w_le_ℓ_n := Nat.le_succ _

/-- Dimension selection never truncates constraints, public inputs, or witness variables. -/
theorem forSize_bounds (sz : R1CS.Size) :
    sz.m ≤ (forSize sz).toSizeR1CS.m ∧
    sz.n_x ≤ (forSize sz).toSizeR1CS.n_x ∧
    sz.n_w ≤ (forSize sz).toSizeR1CS.n_w := by
  have hm := Nat.le_pow_clog (by decide : 1 < 2) sz.m
  have hc := Nat.le_pow_clog (by decide : 1 < 2) (max sz.n_x sz.n_w)
  change sz.m ≤ 2 ^ Nat.clog 2 sz.m ∧
    sz.n_x ≤ 2 ^ (Nat.clog 2 (max sz.n_x sz.n_w) + 1) -
      2 ^ Nat.clog 2 (max sz.n_x sz.n_w) ∧
    sz.n_w ≤ 2 ^ Nat.clog 2 (max sz.n_x sz.n_w)
  have hx := (le_max_left sz.n_x sz.n_w).trans hc
  have hw := (le_max_right sz.n_x sz.n_w).trans hc
  rw [pow_succ]
  constructor
  · exact hm
  constructor <;> omega

end PublicParams

open MvPolynomial

variable {R : Type*} [CommRing R] (pp : PublicParams)

/-- The multilinear extension of the concatenated public and witness assignment. -/
noncomputable def assignmentMLE (x : R1CS.Statement R pp.toSizeR1CS)
    (w : R1CS.Witness R pp.toSizeR1CS) : MvPolynomial (Fin pp.ℓ_n) R :=
  MLE' (R1CS.𝕫 x w)

/-- At every ring point, the public prefix contributes an equality-weighted sum, while the
witness suffix contributes its low-coordinate MLE times all high coordinates. -/
theorem assignment_mle_split (x : R1CS.Statement R pp.toSizeR1CS)
    (w : R1CS.Witness R pp.toSizeR1CS) (r : Fin pp.ℓ_n → R) :
    eval r (assignmentMLE pp x w) =
      (∑ j : Fin (2 ^ pp.ℓ_n - 2 ^ pp.ℓ_w),
        eqTilde (finFunctionFinEquiv.symm (Fin.castLE (Nat.sub_le _ _) j) :
          Fin pp.ℓ_n → R) r * x j) +
      (∏ i : Fin (pp.ℓ_n - pp.ℓ_w), r ⟨pp.ℓ_w + i.val, by omega⟩) *
        eval (fun i : Fin pp.ℓ_w => r (Fin.castLE pp.ℓ_w_le_ℓ_n i)) (MLE' w) := by
  rcases pp with ⟨s, t, k, h⟩
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  dsimp only [assignmentMLE, R1CS.𝕫, PublicParams.toSizeR1CS]
  change _ = _ + (∏ i : Fin (k + d - k), r ⟨k + i.val, by
    change k + i.val < k + d
    omega⟩) *
    eval (fun i : Fin k => r (Fin.castLE h i)) (MLE' w)
  have hprod : (∏ i : Fin (k + d - k), r ⟨k + i.val, by
      change k + i.val < k + d
      omega⟩) = ∏ i : Fin d, r (Fin.natAdd k i) := by
    exact Fintype.prod_equiv (finCongr (Nat.add_sub_cancel_left k d)) _ _ (fun _ => rfl)
  rw [hprod]
  exact MLE'_append_suffix_eval k d x w r

/-- Embed an arbitrary public input into the chosen Spartan public block. -/
def embedStatement (sz : R1CS.Size) (x : R1CS.Statement R sz) :
    R1CS.Statement R (PublicParams.forSize sz).toSizeR1CS :=
  R1CS.embedStatement R sz (PublicParams.forSize sz).toSizeR1CS x

/-- Embed an arbitrary matrix family into the chosen Spartan row and column layout. -/
def embedMatrices (sz : R1CS.Size) (matrices : ∀ idx, R1CS.OracleStatement R sz idx) :
    ∀ idx, R1CS.OracleStatement R (PublicParams.forSize sz).toSizeR1CS idx :=
  R1CS.embedMatrices R sz (PublicParams.forSize sz).toSizeR1CS matrices

/-- Embed an arbitrary witness into the chosen Spartan witness block. -/
def embedWitness (sz : R1CS.Size) (w : R1CS.Witness R sz) :
    R1CS.Witness R (PublicParams.forSize sz).toSizeR1CS :=
  R1CS.embedWitness R sz (PublicParams.forSize sz).toSizeR1CS w

/-- Restrict an enlarged Spartan witness to the original private coordinates. -/
def pullbackWitness (sz : R1CS.Size)
    (w : R1CS.Witness R (PublicParams.forSize sz).toSizeR1CS) : R1CS.Witness R sz :=
  R1CS.pullbackWitness R sz (PublicParams.forSize sz).toSizeR1CS
    (PublicParams.forSize_bounds sz).2.2 w

/-- Satisfaction in the embedded Spartan instance is equivalent to satisfaction by its
explicitly recovered original witness. -/
theorem embedding_relation_iff (sz : R1CS.Size) (x : R1CS.Statement R sz)
    (matrices : ∀ idx, R1CS.OracleStatement R sz idx)
    (w : R1CS.Witness R (PublicParams.forSize sz).toSizeR1CS) :
    R1CS.relation R (PublicParams.forSize sz).toSizeR1CS
      (embedStatement sz x) (embedMatrices sz matrices) w ↔
      R1CS.relation R sz x matrices (pullbackWitness sz w) :=
  R1CS.relation_embed_iff R sz (PublicParams.forSize sz).toSizeR1CS
    (PublicParams.forSize_bounds sz).1 (PublicParams.forSize_bounds sz).2.1
    (PublicParams.forSize_bounds sz).2.2 x matrices w

/-- Embedding and pulling back a witness recovers every original private coordinate. -/
@[simp]
theorem pullback_embedWitness (sz : R1CS.Size) (w : R1CS.Witness R sz) :
    pullbackWitness sz (embedWitness sz w) = w :=
  R1CS.pullbackWitness_embedWitness R sz (PublicParams.forSize sz).toSizeR1CS
    (PublicParams.forSize_bounds sz).2.2 w

/-- The embedded original witness satisfies precisely the original R1CS relation. -/
theorem embedding_preserves_relation (sz : R1CS.Size) (x : R1CS.Statement R sz)
    (matrices : ∀ idx, R1CS.OracleStatement R sz idx) (w : R1CS.Witness R sz) :
    R1CS.relation R (PublicParams.forSize sz).toSizeR1CS
      (embedStatement sz x) (embedMatrices sz matrices) (embedWitness sz w) ↔
      R1CS.relation R sz x matrices w := by
  rw [embedding_relation_iff, pullback_embedWitness]

end Spartan
