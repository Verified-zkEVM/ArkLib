/-
Coset averaging over a 1‑dimensional direction in a finite vector space.
This file provides lemma stubs used to bound the fraction of “good” points
in `rowSpan U` by averaging over cosets of a 1D subspace spanned by `v`.
-/

import ArkLib.Data.CodingTheory.InterleavedCode.Defs
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Tactic

noncomputable section

open Code
open scoped BigOperators

namespace ProximityToRS

variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
variable {κ ι : Type*} [Fintype κ] [Fintype ι] [DecidableEq ι]

-- Injectivity: α ↦ x + α•v along a nonzero direction.
omit [Fintype F] [DecidableEq ι] in
lemma coset_injective {v x : ι → F}
  (hv_ne : v ≠ 0) :
  Function.Injective (fun a : F => (fun j => x j + a * v j)) := by
  classical
  intro a b h
  -- Evaluate equality at a coordinate where v is nonzero.
  have hex : ∃ j : ι, v j ≠ 0 := by
    by_contra hnone
    push_neg at hnone
    apply hv_ne
    funext j; simp [hnone j]
  rcases hex with ⟨j₀, hvj₀⟩
  have hcoord := congrArg (fun (f : ι → F) => f j₀) h
  have hmul : a * v j₀ = b * v j₀ := by
    -- From x j₀ + a * v j₀ = x j₀ + b * v j₀
    have := hcoord
    -- cancel x j₀ on the left
    exact add_left_cancel this
  -- From equality, deduce (a - b) * v j₀ = 0, and use v j₀ ≠ 0.
  have h0 : (a - b) * v j₀ = 0 := by
    have : a * v j₀ - b * v j₀ = 0 := sub_eq_zero.mpr hmul
    simpa [sub_mul] using this
  have : a - b = 0 := (mul_eq_zero.mp h0).resolve_right hvj₀
  exact sub_eq_zero.mp this

-- Combinatorial core: double counting over cosets parallel to `v` inside `rowSpan U`.
-- It yields a cardinality inequality that underlies the uniform probability bound.
omit [DecidableEq F] [Fintype κ] [Fintype ι] [DecidableEq ι] in
lemma coset_averaging_card_bound
  {U : Matrix κ ι F} {v : ι → F} {M : ℕ}
  (P : (ι → F) → Prop) [DecidablePred P]
  (hv_span : v ∈ Matrix.rowSpan U)
  (hcoset : ∀ x ∈ Matrix.rowSpan U,
    Nat.card {a : F // P (fun j => x j + a * v j)} ≤ M)
  [Fintype (Matrix.rowSpan U)] :
  Nat.card {w : Matrix.rowSpan U // P ((w : ι → F))} * Nat.card F
    ≤ M * Nat.card (Matrix.rowSpan U) := by
  classical
  -- Regard v as an element of the row span and denote it by w.
  let w : Matrix.rowSpan U := ⟨v, hv_span⟩
  -- Define the set of pairs (x, a) with x ∈ rowSpan U and P(x + a•v).
  let Pairs := Σ x : Matrix.rowSpan U, {a : F // P ((x : ι → F) + a • v)}
  have hPairs_le_F : Fintype.card Pairs ≤ Fintype.card (Matrix.rowSpan U) * M := by
    -- card Σ x, {a // P(x + a•v)} = ∑_x card {a // ...} ≤ ∑_x M = |S| * M
    classical
    have hSigma_card :
        Fintype.card Pairs
          = ∑ x : Matrix.rowSpan U, Fintype.card {a : F // P ((x : ι → F) + a • v)} := by
      -- standard cardinality of sigma over a finite index type
      simp [Pairs]
    have hSum_le :
        (∑ x : Matrix.rowSpan U, Fintype.card {a : F // P ((x : ι → F) + a • v)})
          ≤ ∑ _x : Matrix.rowSpan U, M := by
      refine Finset.sum_le_sum ?_
      intro x hx
      -- Apply the coset hypothesis at x ∈ S
      have hxS : (x : ι → F) ∈ Matrix.rowSpan U := x.property
      have hx' := (hcoset (x := (x : ι → F)) hxS)
      -- normalize pointwise description of (x + a•v)
      simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hx'
    have hPairs_le_sum : Fintype.card Pairs ≤ ∑ _x : Matrix.rowSpan U, M := by
      simpa [hSigma_card] using hSum_le
    -- ∑_x M = |rowSpan U| * M
    simpa [Finset.card_univ, Finset.sum_const_nat] using hPairs_le_sum
  -- Build an injection from Good × F into Pairs, where Good := {y ∈ S | P y}.
  let Good := {y : Matrix.rowSpan U // P ((y : ι → F))}
  let ψ : Good × F → Pairs :=
    fun p =>
      let y : Matrix.rowSpan U := p.1.val
      let a : F := p.2
      -- Show that P holds at ((y - a•w) + a•v) = y
      have hP : P (((y - a • w : Matrix.rowSpan U) : ι → F) + a • v) := by
        -- coe (y - a•w) = (y : _) - a•v, so the sum simplifies to y
        have hsum : ((y - a • w : Matrix.rowSpan U) : ι → F) + a • v = (y : ι → F) := by
          -- Use linearity of coercion and sub_add_cancel
          -- In S: (y - a•w) + a•w = y
          have hS : (y - a • w : Matrix.rowSpan U) + a • w = y := sub_add_cancel y (a • w)
          -- Coerce to the ambient function space
          have hcoe := congrArg (fun (z : Matrix.rowSpan U) => (z : ι → F)) hS
          simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, w, Subtype.coe_mk] using hcoe
        -- use the fact that y is good under P
        have hyP : P ((y : ι → F)) := p.1.property
        -- Transport `hyP : P y` along the equality `hsum : ((y - a•w) + a•v) = y`.
        have hEq : P (((y - a • w : Matrix.rowSpan U) : ι → F) + a • v)
                    = P ((y : ι → F)) := congrArg P hsum
        exact (Eq.mp hEq.symm hyP)
      -- Pack into the sigma type
      ⟨y - a • w, ⟨a, hP⟩⟩
  have hψ_inj : Function.Injective ψ := by
    intro p q h
    -- Unpack components
    rcases p with ⟨⟨y, hy⟩, a⟩; rcases q with ⟨⟨y', hy'⟩, a'⟩
    -- Extract second component equality to get a = a'
    have haeq : a = a' := by
      -- Compare the second component value (the scalar) of ψ p and ψ q
      have h2 := congrArg (fun t : Pairs => t.2.1) h
      -- By definition, (ψ ⟨⟨y,hy⟩, a⟩).2.1 = a
      simpa [ψ] using h2
    -- With a = a', deduce y = y' from equality of first components
    have hy_eq : y = y' := by
      have hfirst := congrArg (fun t : Pairs => t.1) h
      have hfirst' : (y - a • w : Matrix.rowSpan U) = (y' - a' • w : Matrix.rowSpan U) := by
        simpa [ψ] using hfirst
      -- rewrite a' by a and cancel
      have hfirst'' : (y - a • w : Matrix.rowSpan U) = (y' - a • w : Matrix.rowSpan U) := by
        simpa [haeq]
        using hfirst'
      -- add a•w to both sides and cancel
      simpa using congrArg (fun z : Matrix.rowSpan U => z + a • w) hfirst''
    -- Conclude p = q
    cases haeq; cases hy_eq; rfl
  -- |Good| * |F| ≤ |Pairs|
  have hGood_mul_le_F : Fintype.card Good * Fintype.card F ≤ Fintype.card Pairs := by
    have hprod : Fintype.card (Good × F) = Fintype.card Good * Fintype.card F := by
      classical
      simpa using (Fintype.card_prod (α := Good) (β := F))
    simpa [hprod] using Fintype.card_le_of_injective (f := ψ) hψ_inj
  -- Chain inequalities
  have hPairs_le_nat : Nat.card Pairs ≤ M * Nat.card (Matrix.rowSpan U) := by
    simpa [mul_comm] using hPairs_le_F
  have hGood_mul_le_nat :
      Nat.card {w : Matrix.rowSpan U // P ((w : ι → F))} * Nat.card F
        ≤ Nat.card Pairs := by
    simpa using hGood_mul_le_F
  exact (hGood_mul_le_nat).trans (by simpa [mul_comm] using hPairs_le_nat)

-- Uniform fraction bound stub: if each coset contributes at most M good points,
-- then the uniform probability over rowSpan U of being good is ≤ M/|F|.
lemma uniform_fraction_bound
  {U : Matrix κ ι F} {v : ι → F} {M : ℕ}
  (P : (ι → F) → Prop) [DecidablePred P]
  (hv_span : v ∈ Matrix.rowSpan U)
  (hcoset : ∀ x ∈ Matrix.rowSpan U,
    Nat.card {a : F // P (fun j => x j + a * v j)} ≤ M)
  [Fintype (Matrix.rowSpan U)] :
  (PMF.uniformOfFintype (Matrix.rowSpan U)).toOuterMeasure { w | P (w : ι → F) }
    ≤ (M : ENNReal) / (Nat.card F) := by
  classical
  -- Compute the LHS as a simple cardinality ratio via mathlib
  let E' : Set (Matrix.rowSpan U) := { w | P (w : ι → F) }
  -- Cardinality double counting bound on Good × F versus pairs (x,a)
  have hcard :=
    coset_averaging_card_bound (U := U) (v := v) (M := M) P hv_span hcoset
  -- Rewrite the RHS bound in terms of ENNReal arithmetic
  have hF_ne : (Nat.card F : ENNReal) ≠ 0 := by simp
  have hS_ne : (Nat.card (Matrix.rowSpan U) : ENNReal) ≠ 0 := by simp
  have hcast :
      ((Nat.card {w : Matrix.rowSpan U // P ((w : ι → F))} : ℕ) : ENNReal)
        * (Nat.card F : ENNReal)
        ≤ (M : ENNReal) * (Nat.card (Matrix.rowSpan U) : ENNReal) := by
    exact_mod_cast hcard
  have hratio₀ : ((Nat.card {w : Matrix.rowSpan U // P ((w : ι → F))} : ENNReal)
            / (Nat.card (Matrix.rowSpan U) : ENNReal))
            ≤ (M : ENNReal) / (Nat.card F : ENNReal) := by
    -- Clear denominator on the RHS
    refine (ENNReal.le_div_iff_mul_le (h0 := Or.inl hF_ne) (ht := Or.inl (by simp))).2 ?_
    -- First, rewrite (a/#S) * #F as (a*#F)/#S in terms of Fintype.card
    have hmul_div_rewrite' :
        ((Fintype.card {w : Matrix.rowSpan U // P ((w : ι → F))} : ENNReal)
            / (Fintype.card (Matrix.rowSpan U) : ENNReal)) * (Fintype.card F : ENNReal)
          = (((Fintype.card {w : Matrix.rowSpan U // P ((w : ι → F))} : ENNReal)
                * (Fintype.card F : ENNReal))
              / (Fintype.card (Matrix.rowSpan U) : ENNReal)) := by
      simp [ENNReal.div_eq_inv_mul, mul_comm, mul_left_comm]
    -- Now absorb the denominator (#S) using the casted cardinal inequality
    have hdiv_le_nat :
        (((Nat.card {w : Matrix.rowSpan U // P ((w : ι → F))} : ENNReal)
            * (Nat.card F : ENNReal))
          / (Nat.card (Matrix.rowSpan U) : ENNReal)) ≤ (M : ENNReal) := by
      exact (ENNReal.div_le_iff_le_mul (hb0 := Or.inl hS_ne) (hbt := Or.inl (by simp))).2 hcast
    have hdiv_le :
        (((Fintype.card {w : Matrix.rowSpan U // P ((w : ι → F))} : ENNReal)
            * (Fintype.card F : ENNReal))
          / (Fintype.card (Matrix.rowSpan U) : ENNReal)) ≤ (M : ENNReal) := by
      simpa using hdiv_le_nat
    simpa [hmul_div_rewrite']
  -- Convert to a statement phrased using `Nat.card ↑E'`
  have hratio : ((Nat.card (↑E') : ENNReal)
            / (Nat.card (Matrix.rowSpan U) : ENNReal))
            ≤ (M : ENNReal) / (Nat.card F : ENNReal) := by
    simpa [E'] using hratio₀
  -- Conclude via the uniform cardinality formula
  calc
    (PMF.uniformOfFintype (Matrix.rowSpan U)).toOuterMeasure E'
        = (Nat.card (↑E') : ENNReal) / (Nat.card (Matrix.rowSpan U) : ENNReal) := by
          simpa using (PMF.toOuterMeasure_uniformOfFintype_apply
            (α := Matrix.rowSpan U) (s := E'))
    _ ≤ (M : ENNReal) / (Nat.card F : ENNReal) := hratio

end ProximityToRS
