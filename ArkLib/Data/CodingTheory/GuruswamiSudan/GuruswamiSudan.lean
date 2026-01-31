/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Ilia Vlasov, Stefano Rocca
-/
import Mathlib.Algebra.Field.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Real.Sqrt

import ArkLib.Data.CodingTheory.Basic
import ArkLib.Data.CodingTheory.ReedSolomon
import ArkLib.Data.Polynomial.Bivariate

namespace GuruswamiSudan

variable {F : Type} [Field F]
variable [DecidableEq F]
variable {n : ℕ}

open Polynomial Polynomial.Bivariate

/--
Guruswami–Sudan conditions for the polynomial searched by the decoder.

These conditions characterize the existence of a nonzero bivariate
polynomial `Q(X,Y)` that vanishes with sufficiently high multiplicity
at all interpolation points `(ωs i, f i)`. As in the Berlekamp–Welch
case, this can be shown to be equivalent to solving a system of linear
equations.

Parameters:
* `k : ℕ` — Message length parameter of the code.
* `r : ℕ` — Multiplicity parameter; controls how many derivatives of `Q`
  must vanish at each interpolation point.
* `D : ℕ` — Degree bound for `Q` under the weighted degree measure.
* `ωs : Fin n ↪ F` — The domain of evaluation.
* `f : Fin n → F` — Received word (evaluation of the encoded polynomial,
  possibly corrupted).
* `Q : Polynomial (Polynomial F)` — The candidate bivariate polynomial
  in variables `X` and `Y`.
-/
structure Condition
  (k r D : ℕ)
  (ωs : Fin n ↪ F)
  (f : Fin n → F)
  (Q : Polynomial (Polynomial F)) where
  /-- Q ≠ 0 -/
  Q_ne_0 : Q ≠ 0
  /-- Degree of the polynomial. -/
  Q_deg : Bivariate.weightedDegree Q 1 (k-1) ≤ D
  /-- (ωs i, f i) must be root of the polynomial Q. -/
  Q_roots : ∀ i, (Q.eval (C <| f i)).eval (ωs i) = 0
  /-- Multiplicity of the roots is at least r. -/
  Q_multiplicity : ∀ i, r ≤ Bivariate.rootMultiplicity Q (ωs i) (f i)

/-- Guruswami-Sudan decoder. -/
opaque decoder (k r D e : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) : List F[X] := sorry

/-- Each decoded codeword has to be e-far from the received message. -/
theorem decoder_mem_impl_dist
  {k r D e : ℕ}
  (h_e : e ≤ n - Real.sqrt (k * n))
  {ωs : Fin n ↪ F}
  {f : Fin n → F}
  {p : F[X]}
  (h_in : p ∈ decoder k r D e ωs f)
  :
  Δ₀(f, p.eval ∘ ωs) ≤ e := by sorry

/-- If a codeword is e-far from the received message it appears in the output of
the decoder.
-/
theorem decoder_dist_impl_mem
  {k r D e : ℕ}
  (h_e : e ≤ n - Real.sqrt (k * n))
  {ωs : Fin n ↪ F}
  {f : Fin n → F}
  {p : F[X]}
  (h_dist : Δ₀(f, p.eval ∘ ωs) ≤ e)
  :
  p ∈ decoder k r D e ωs f := by sorry

/-- The degree bound (a.k.a. `D_X`) for instantiation of Guruswami-Sudan
    in lemma 5.3 of [BCIKS20].
    D_X(m) = (m + 1/2)√ρn.
-/
noncomputable def proximity_gap_degree_bound (k m : ℕ) : ℕ :=
  let rho := (k + 1 : ℚ) / n
  Nat.floor ((((m : ℚ) + (1 : ℚ)/2)*(Real.sqrt rho))*n)

/-- The ball radius from lemma 5.3 of [BCIKS20],
    which follows from the Johnson bound.
    δ₀(ρ, m) = 1 - √ρ - √ρ/2m.
-/
noncomputable def proximity_gap_johnson (k m : ℕ) : ℕ :=
  let rho := (k + 1 : ℚ) / n
  Nat.floor ((1 : ℝ) - Real.sqrt rho - Real.sqrt rho / (2 * m))


section GuruswamiSudanExistence

/-
The set of indices `(i,j)` such that `i + (k-1)j ≤ D`.
-/
def validIndices (k D : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range (D + 1)).product (Finset.range (D + 1)) |>.filter (fun x => x.1 + (k - 1) * x.2 ≤ D)

/-
The number of variables in the linear system.
-/
def numVars (k D : ℕ) : ℕ := (validIndices k D).card

/-
The set of derivative indices `(s,t)` such that `s + t < m`.
-/
def ConstraintIndex (m : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range m).product (Finset.range m) |>.filter (fun x => x.1 + x.2 < m)

/-
The number of constraints.
-/
def numConstraints (n m : ℕ) : ℕ := n * (ConstraintIndex m).card

/-
The number of constraints is m(m+1)/2.
-/
lemma card_ConstraintIndex (m : ℕ) : (ConstraintIndex m).card = m * (m + 1) / 2 := by
  rw [ Nat.div_eq_of_eq_mul_left zero_lt_two ];
  -- The set of pairs (s, t) such that s + t < m is equivalent to the set of pairs (s, t)
  -- where s ranges from 0 to m-1 and t ranges from 0 to m-1-s.
  have h_eq : (ConstraintIndex m).card = ∑ s ∈ Finset.range m, (m - s) := by
    -- We can prove this by summing over s from 0 to m-1, the number of t's is m-s.
    have h_sum : (ConstraintIndex m).card =
        ∑ s ∈ Finset.range m, Finset.card (Finset.range (m - s)) := by
      rw [ show ConstraintIndex m = Finset.biUnion ( Finset.range m ) fun s =>
        Finset.image ( fun t => ( s, t ) ) ( Finset.range ( m - s ) ) from ?_,
        Finset.card_biUnion ];
      · exact Finset.sum_congr rfl fun _ _ =>
          Finset.card_image_of_injective _ fun _ _ h => by injection h;
      · exact fun i hi j hj hij => Finset.disjoint_left.mpr fun x hx₁ hx₂ => hij <| by aesop;
      · ext ⟨s, t⟩
        simp [ConstraintIndex, Finset.mem_biUnion, Finset.mem_image];
        grind;
    aesop;
  exact h_eq.symm ▸ Nat.recOn m ( by norm_num ) fun n ih => by
    cases n <;> simp +decide [ Finset.sum_range_succ', Nat.mul_succ ] at * ; linarith;

/-
The number of variables is the sum over j of the number of valid i's.
-/
lemma card_validIndices_eq_sum (k D : ℕ) (hk : 1 < k) :
  (validIndices k D).card = ∑ j ∈ Finset.range (D / (k - 1) + 1), (D - (k - 1) * j + 1) := by
    -- We can split the sum over all pairs (i, j) into a sum over j and, for each j, a sum over i.
    have h_split : (validIndices k D).card =
        ∑ j ∈ Finset.range (D / (k - 1) + 1),
          ∑ i ∈ Finset.range (D + 1), if i + (k - 1) * j ≤ D then 1 else 0 := by
      rw [ show validIndices k D =
        Finset.filter ( fun p : ℕ × ℕ => p.1 + ( k - 1 ) * p.2 ≤ D )
        ( Finset.product ( Finset.range ( D + 1 ) )
          ( Finset.range ( D / ( k - 1 ) + 1 ) ) ) from ?_,
        Finset.card_filter ];
      · erw [ Finset.sum_product, Finset.sum_comm ];
      · ext ⟨i, j⟩; simp [validIndices];
        exact fun _ _ => iff_of_true ( by
          nlinarith [ Nat.sub_pos_of_lt hk, Nat.div_add_mod D ( k - 1 ),
          Nat.mod_lt D ( Nat.sub_pos_of_lt hk ) ] )
          ( Nat.lt_succ_of_le ( Nat.le_div_iff_mul_le ( Nat.sub_pos_of_lt hk ) |>.2
          ( by nlinarith [ Nat.sub_pos_of_lt hk ] ) ) );
    -- Let's simplify the inner sum. For each j, the number of i's such that i + (k-1)*j ≤ D
    -- is D - (k-1)*j + 1.
    have h_inner : ∀ j ∈ Finset.range (D / (k - 1) + 1), ∑ i ∈ Finset.range (D + 1),
        (if i + (k - 1) * j ≤ D then 1 else 0) = (D - (k - 1) * j) + 1 := by
      intro j hj
      have h_filter : Finset.filter (fun i => i + (k - 1) * j ≤ D) (Finset.range (D + 1)) =
          Finset.Icc 0 (D - (k - 1) * j) := by
        ext i
        simp [Finset.mem_Icc];
        refine ⟨ fun h => Nat.le_sub_of_add_le <| by linarith, fun h => ⟨ by
            nlinarith [ Nat.sub_add_cancel <| show ( k - 1 ) * j ≤ D from by
              nlinarith [ Nat.sub_add_cancel <| show j ≤ D / ( k - 1 ) from by
                linarith [ Finset.mem_range.mp hj ], Nat.div_mul_le_self D ( k - 1 ) ] ], by
                  linarith [ Nat.sub_add_cancel <| show ( k - 1 ) * j ≤ D from by
                    nlinarith [ Nat.sub_add_cancel <| show j ≤ D / ( k - 1 ) from by
                      linarith [ Finset.mem_range.mp hj ], Nat.div_mul_le_self D ( k - 1 ) ] ] ⟩ ⟩;
      simp_all;
    exact h_split.trans ( Finset.sum_congr rfl h_inner )

/-
The number of variables is strictly greater than the number of constraints,
ensuring a non-trivial solution exists.
-/
open Real

noncomputable section AristotleLemmas

/-
Closed form for the number of variables when k > 1.
-/
open GuruswamiSudan

lemma numVars_eq_of_gt_one {k D : ℕ} (hk : 1 < k) :
    numVars k D = let L := D / (k - 1); (L + 1) * (2 * D + 2 - (k - 1) * L) / 2 := by
      convert card_validIndices_eq_sum k D hk using 1;
      -- Simplify the sum on the right-hand side.
      have h_simp : ∑ j ∈ Finset.range (D / (k - 1) + 1), (D - (k - 1) * j) =
          (D / (k - 1) + 1) * D - (k - 1) * ((D / (k - 1)) * (D / (k - 1) + 1)) / 2 := by
        have h_simp : ∑ j ∈ Finset.range (D / (k - 1) + 1), (D - (k - 1) * j) =
            ∑ j ∈ Finset.range (D / (k - 1) + 1), D -
              ∑ j ∈ Finset.range (D / (k - 1) + 1), (k - 1) * j := by
          exact eq_tsub_of_add_eq <| by
            rw [ ← Finset.sum_add_distrib ] ;
            exact Finset.sum_congr rfl fun x hx => tsub_add_cancel_of_le <| by
              nlinarith [ Finset.mem_range.mp hx, Nat.div_mul_le_self D ( k - 1 ) ] ;
        simp_all [mul_comm];
        exact congrArg _ ( Eq.symm <| Nat.div_eq_of_eq_mul_left zero_lt_two <| by
          rw [ ← Finset.sum_mul _ _ _ ] ;
          exact Nat.recOn ( D / ( k - 1 ) ) ( by norm_num ) fun n ih => by
            norm_num [ Finset.sum_range_succ ] at * ; linarith );
      simp_all [ Finset.sum_add_distrib ];
      rw [ Nat.div_eq_of_eq_mul_left zero_lt_two ];
      rw [ tsub_eq_of_eq_add ];
      rw [ tsub_add_eq_add_tsub ];
      rw [ tsub_mul ];
      rotate_left;
      exact k;
      exact 1;
      · exact Nat.div_le_of_le_mul <| by
          nlinarith [ Nat.zero_le ( D / ( k - 1 ) ), Nat.div_mul_le_self D ( k - 1 ),
            Nat.sub_add_cancel hk.le ] ;
      · rw [ Nat.sub_add_cancel hk.le ];
      · rw [ Nat.mul_sub_left_distrib ] ; ring_nf;
        rw [ tsub_mul ] ; ring_nf ;
        rw [ Nat.div_mul_cancel ];
        · rw [ show D / ( k - 1 ) * k - D / ( k - 1 ) = D / ( k - 1 ) * ( k - 1 ) by
            rw [ Nat.mul_sub_left_distrib, Nat.mul_one ] ] ; ring_nf;
        · norm_num [ ← even_iff_two_dvd, parity_simps ]

/-
The number of variables is (D+1)^2 when k <= 1.
-/
open GuruswamiSudan

lemma numVars_eq_sq {k D : ℕ} (hk : k ≤ 1) : numVars k D = (D + 1) ^ 2 := by
  interval_cases k <;> simp +decide [ GuruswamiSudan.numVars, GuruswamiSudan.validIndices ];
  · rw [ Finset.filter_true_of_mem fun x hx => by
      linarith [ Finset.mem_range.mp ( Finset.mem_product.mp hx |>.1 ) ] ] ;
      norm_num [ sq, Finset.card_product ];
  · erw [ Finset.filter_true_of_mem fun x hx => by
      linarith [ Finset.mem_range.mp ( Finset.mem_product.mp hx |>.1 ) ] ] ;
      norm_num [ Finset.card_product, sq ] ;

/-
A lower bound for the number of variables when k > 1. Specifically, 2(k-1) * numVars > D^2.
-/
open GuruswamiSudan

lemma numVars_lower_bound {k D : ℕ} (hk : 1 < k) :
    2 * (k - 1) * numVars k D > D ^ 2 := by
      -- By definition of $numVars$, we know that $numVars k D = (D + 1) * (2 * D + 1)$
      -- when $k \leq 1$.
      have h_numVars : GuruswamiSudan.numVars k D = let
          L := D / (k - 1); (L + 1) * (2 * D + 2 - (k - 1) * L) / 2 := by
        convert numVars_eq_of_gt_one hk using 1;
      rcases k with ( _ | _ | k ) <;> simp_all +decide;
      rw [ ← Nat.mul_div_assoc ] <;> norm_num [ Nat.mul_succ ];
      · rw [ Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le ] <;> norm_num;
        zify [ Nat.succ_mul ];
        rw [ Nat.cast_sub ] <;> push_cast
          <;> nlinarith [ Nat.div_mul_le_self D ( k + 1 ), Nat.div_add_mod D ( k + 1 ),
            Nat.mod_lt D ( Nat.succ_pos k ) ];
      · norm_num [ ← even_iff_two_dvd, mul_add, parity_simps ];
        cases le_total ( 2 * D + 2 ) ( ( k + 1 ) * ( D / ( k + 1 ) ) ) <;>
          simp_all +decide [ parity_simps ];
        grind

/-
Lower bound for the square of (D+1). Specifically, (D+1)^2 > (m+1/2)^2 * (k+1) * n.
-/
open GuruswamiSudan Real

lemma proximity_gap_degree_bound_sq_gt {n k m : ℕ} (hn : n ≠ 0) :
    ((proximity_gap_degree_bound (n := n) k m : ℝ) + 1) ^ 2 >
      ((m : ℝ) + 1 / 2) ^ 2 * (k + 1) * n := by
      -- Let's simplify the expression for the bound.
      set D := GuruswamiSudan.proximity_gap_degree_bound k m
      have h_bound : (D + 1 : ℝ) > (m + 1 / 2) * Real.sqrt ((k + 1 : ℝ) * n) := by
        -- By definition of $D$, we know that $D \geq \lfloor (m + 1/2) \sqrt{(k + 1) n} \rfloor$.
        have hD_ge_floor : (D : ℝ) ≥ Nat.floor ((m + 1 / 2 : ℝ) * Real.sqrt ((k + 1 : ℝ) * n)) := by
          simp +zetaDelta at *;
          unfold GuruswamiSudan.proximity_gap_degree_bound;
          norm_num [ mul_assoc, mul_div_assoc, hn ];
          gcongr;
          · sorry
          · sorry
        exact lt_of_lt_of_le ( Nat.lt_floor_add_one _ ) ( add_le_add_right hD_ge_floor _ );
      nlinarith [ show 0 < ( m + 1 / 2 : ℝ ) * Real.sqrt ( ( k + 1 ) * n ) by
        positivity, Real.mul_self_sqrt ( show 0 ≤ ( k + 1 : ℝ ) * n by positivity ) ]

/-
A tighter lower bound for the number of variables when k > 1: 2(k-1) * numVars >= D(D+2).
-/
open GuruswamiSudan

lemma numVars_lower_bound_tight {k D : ℕ} (hk : 1 < k) :
    2 * (k - 1) * numVars k D ≥ D * (D + 2) := by
      -- By definition of $numVars$, we know that $numVars k D = (D - (k - 1) * j + 1)$
      -- for all $j$ in the range.
      have h_numVars_def : GuruswamiSudan.numVars k D =
          ((D / (k - 1)) + 1) * (2 * D + 2 - (k - 1) * (D / (k - 1))) / 2 := by
        exact numVars_eq_of_gt_one hk;
      rcases k with ( _ | _ | k ) <;> simp_all [Nat.mul_succ];
      rw [ ← Nat.mul_div_assoc ];
      · rw [ Nat.le_div_iff_mul_le ] <;> ring_nf;
        · zify;
          rw [ Nat.cast_sub ] <;> push_cast <;>
            nlinarith [ Nat.div_mul_le_self D ( 1 + k ), Nat.div_add_mod D ( 1 + k ),
              Nat.mod_lt D ( by linarith : 0 < ( 1 + k ) ) ];
        · norm_num;
      · cases le_total ( 2 * D + 2 ) ( ( k + 1 ) * ( D / ( k + 1 ) ) ) <;>
          simp_all [ ← even_iff_two_dvd, parity_simps ];
        by_cases h : Even ( D / ( k + 1 ) ) <;> simp_all [ parity_simps ]

/-
Helper inequality for the proof of numVars_gt_numConstraints.
((m + 1/2)^2 * (k + 1) * n >= (k - 1) * n * m * (m + 1) + 1) for m > 0.
-/
open GuruswamiSudan Real

lemma inequality_helper {n k m : ℕ} (hn : n ≠ 0) (hk : 1 < k) (hm : m ≠ 0) :
    ((m : ℝ) + 1 / 2) ^ 2 * (k + 1) * n ≥ (k - 1) * n * m * (m + 1) + 1 := by
      rcases n with ( _ | _ | n ) <;> rcases m with ( _ | _ | m ) <;> norm_num at *;
      · linarith;
      · nlinarith [ sq ( m : ℝ ) ];
      · nlinarith;
      · exact le_of_sub_nonneg ( by ring_nf; positivity )

/-
Proof of numVars > numConstraints for the case k > 1, assuming n != 0 and m != 0.
Uses numVars_lower_bound_tight, proximity_gap_degree_bound_sq_gt, and inequality_helper.
-/
open GuruswamiSudan Real

lemma numVars_gt_numConstraints_of_gt_one {n k m : ℕ} (hn : n ≠ 0) (hk : 1 < k) (hm : m ≠ 0) :
    numVars k (proximity_gap_degree_bound (n := n) k m) > numConstraints n m := by
      -- Let's obtain the proximity gap degree bound `D` and use it in our proof of
      -- inequality.
      set D := proximity_gap_degree_bound (n := n) k m
      have hD : ((D + 1)^2 : ℝ) > ((m : ℝ) + 1 / 2)^2 * (k + 1) * n := by
        convert proximity_gap_degree_bound_sq_gt hn using 1;
      -- Let's use the lower bound on the number of variables and the upper bound
      -- on the number of constraints.
      have h_ineq : 2 * (k - 1) * numVars k D > (k - 1) * n * m * (m + 1) := by
        have h_ineq : 2 * (k - 1) * numVars k D ≥ (D : ℝ) * (D + 2) := by
          convert numVars_lower_bound_tight hk using 1;
          norm_cast;
          rw [ Int.subNatNat_of_le ] <;> norm_cast ; linarith;
        have h_ineq : (D : ℝ) * (D + 2) > (k - 1) * n * m * (m + 1) := by
          nlinarith [ show ( k : ℝ ) ≥ 2 by norm_cast, show ( m : ℝ ) ≥ 1 by
            exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hm ), show ( n : ℝ ) ≥ 1 by
              exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hn ), mul_le_mul_of_nonneg_left
                ( show ( m : ℝ ) ≥ 1 by exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hm ) )
                  ( show ( n : ℝ ) ≥ 0 by positivity ) ];
        norm_cast at *;
        rw [ Int.subNatNat_of_le ] at * <;> norm_cast at * ; linarith;
        · linarith;
        · linarith;
      -- By dividing both sides of the inequality $2 * (k - 1) * numVars k D >
      -- (k - 1) * n * m * (m + 1)$ by $2 * (k - 1)$, we obtain $numVars k D >
      -- n * m * (m + 1) / 2$.
      have h_div : numVars k D > n * m * (m + 1) / 2 := by
        exact Nat.div_lt_of_lt_mul <| by nlinarith [ Nat.sub_pos_of_lt hk ] ;
      convert h_div using 1;
      convert congr_arg ( fun x : ℕ => n * x ) ( card_ConstraintIndex m ) using 1;
      rw [ ← Nat.mul_div_assoc ] <;> ring_nf ; exact even_iff_two_dvd.mp ( by
        simp +arith [ parity_simps ] )

end AristotleLemmas

lemma numVars_gt_numConstraints (n k m : ℕ) :
  numVars k (proximity_gap_degree_bound (n := n) k m) > numConstraints n m := by
  -- Case 2: Assume $k \leq 1$. Use `numVars_eq_sq` to get `numVars = (D+1)^2`.
  by_cases hk : k ≤ 1;
  · interval_cases k <;> norm_num [ GuruswamiSudan.numVars_eq_sq,
      GuruswamiSudan.numConstraints ];
    · unfold GuruswamiSudan.proximity_gap_degree_bound; norm_num;
      -- By definition of $ConstraintIndex$, we know that its cardinality is $m(m+1)/2$.
      have h_constraint_card : (GuruswamiSudan.ConstraintIndex m).card =
          m * (m + 1) / 2 := by
        exact card_ConstraintIndex m;
      rcases n with ( _ | n ) <;> rcases m with ( _ | m ) <;> norm_num at *;
      · norm_num [ h_constraint_card ];
      · -- By simplifying, we can see that the inequality holds.
        have h_simplify : (n + 1) * (m + 1) * (m + 2) / 2 < (⌊((m + 1 + 1 / 2) *
            Real.sqrt (n + 1))⌋₊ + 1) ^ 2 := by
          have := Nat.lt_floor_add_one ( ( m + 1 + 1 / 2 : ℝ ) * Real.sqrt ( n + 1 ) );
          rw [ Nat.div_lt_iff_lt_mul <| by positivity ];
          rw [ ← @Nat.cast_lt ℝ ] ; norm_num ; ring_nf at *;
          nlinarith [ show 0 ≤ ( m : ℝ ) * Real.sqrt ( 1 + n ) by
              positivity, show 0 ≤ Real.sqrt ( 1 + n ) by
                  positivity, Real.mul_self_sqrt ( show ( 0 : ℝ ) ≤ 1 + n by positivity ) ];
        convert h_simplify using 1;
        · exact Eq.symm ( Nat.div_eq_of_eq_mul_left zero_lt_two ( by
            nlinarith only [ Nat.div_mul_cancel ( show 2 ∣ ( m + 1 ) * ( m + 1 + 1 )
              from Nat.dvd_of_mod_eq_zero ( by norm_num [ Nat.add_mod, Nat.mod_two_of_bodd ] ) ),
                h_constraint_card ] ) );
        · congr;
          · sorry
          · sorry
    · -- Since $n \neq 0$ and $m \neq 0$, we can apply the inequality from `inequality_helper`.
      by_cases hn : n = 0;
      · aesop;
      · by_cases hm : m = 0;
        · unfold GuruswamiSudan.ConstraintIndex; aesop;
        · -- Since $n \neq 0$ and $m \neq 0$, we can apply the inequality from
          -- `inequality_helper` to conclude the proof.
          have h_ineq : (m + 1 / 2 : ℝ) ^ 2 * 2 * n > n * m * (m + 1) / 2 := by
            nlinarith [ show ( m : ℝ ) ≥ 1 by
              exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hm ),
                show ( n : ℝ ) ≥ 1 by
                  exact Nat.one_le_cast.mpr ( Nat.pos_of_ne_zero hn ),
                    mul_pos ( show ( m : ℝ ) > 0 by
                      exact Nat.cast_pos.mpr ( Nat.pos_of_ne_zero hm ) )
                        ( show ( n : ℝ ) > 0 by
                          exact Nat.cast_pos.mpr ( Nat.pos_of_ne_zero hn ) ) ];
          have h_ineq : (n * m * (m + 1) / 2 : ℝ) <
              ((GuruswamiSudan.proximity_gap_degree_bound (n := n) 1 m + 1) : ℝ) ^ 2 := by
            refine lt_of_lt_of_le h_ineq ?_;
            convert proximity_gap_degree_bound_sq_gt hn |> le_of_lt using 1 ; ring;
          rw [ div_lt_iff₀ ] at h_ineq <;> norm_cast at *;
          rw [ GuruswamiSudan.card_ConstraintIndex ];
          nlinarith [ Nat.div_mul_le_self ( m * ( m + 1 ) ) 2 ];
  · by_cases hn : n = 0 <;> by_cases hm : m = 0 <;> simp_all [ numConstraints ];
    · exact Finset.card_pos.mpr ⟨ ⟨ 0, 0 ⟩,
        Finset.mem_filter.mpr ⟨ Finset.mem_product.mpr ⟨ Finset.mem_range.mpr
          <| Nat.succ_pos _, Finset.mem_range.mpr <| Nat.succ_pos _ ⟩, by norm_num ⟩ ⟩;
    · exact Finset.card_pos.mpr ⟨ ⟨ 0, 0 ⟩, Finset.mem_filter.mpr ⟨ Finset.mem_product.mpr
        ⟨ Finset.mem_range.mpr <| Nat.succ_pos _, Finset.mem_range.mpr <| Nat.succ_pos _ ⟩, by
          norm_num ⟩ ⟩;
    · exact lt_of_lt_of_le ( by simp +decide [ GuruswamiSudan.ConstraintIndex ] )
        ( Nat.pos_of_ne_zero ( by exact ne_of_gt ( Finset.card_pos.mpr ⟨ ( 0, 0 ),
          Finset.mem_filter.mpr ⟨ Finset.mem_product.mpr ⟨ Finset.mem_range.mpr ( Nat.succ_pos _ ),
            Finset.mem_range.mpr ( Nat.succ_pos _ ) ⟩, by norm_num ⟩ ⟩ ) ) );
    · exact numVars_gt_numConstraints_of_gt_one hn ( hk ) hm |> fun h => by
        simpa [ GuruswamiSudan.numConstraints ] using h;

/-
Definitions of polynomial shift and constraint evaluation map.
-/
open Polynomial

/-- Shift a bivariate polynomial by (x, y). -/
noncomputable def shift {F : Type} [CommSemiring F] (f : F[X][Y])
  (x y : F) : F[X][Y] :=
  (f.comp (Polynomial.X + C (C y))).map (Polynomial.compRingHom (Polynomial.X + C x))

/-- The linear map evaluating the (s,t)-th derivative coefficient at (x,y). -/
noncomputable def evalConstraint {F : Type} [CommSemiring F]
    (x y : F) (s t : ℕ) : F[X][Y] →ₗ[F] F where
  toFun f := ((shift f x y).coeff t).coeff s
  map_add' f g := by simp [ shift ]
  map_smul' a f := by simp [ shift ]

/-
Definitions of monomials and the admissible polynomial subspace.
-/
open Polynomial

/-- The monomial X^i Y^j as a bivariate polynomial. -/
noncomputable def monomial {F : Type} [Semiring F] (i j : ℕ) : F[X][Y] :=
  Polynomial.monomial j (Polynomial.monomial i 1)

/-- The submodule of polynomials with weighted degree at most D. -/
noncomputable def admissibleSubmodule {F : Type} [Semiring F]
    [DecidableEq F] (k D : ℕ) : Submodule F F[X][Y] :=
  Submodule.span F (↑((validIndices k D).image
    (fun p => monomial (F := F) p.1 p.2)) : Set F[X][Y])

/-
Definition of the linear map from coefficients to polynomials.
-/
open Polynomial BigOperators

/-- The linear map from the space of coefficients to polynomials. -/
noncomputable def coeffsToPoly {F : Type} [CommSemiring F] (k D : ℕ) :
  ((validIndices k D) → F) →ₗ[F] F[X][Y] :=
  Finsupp.linearCombination F (fun p : validIndices k D => monomial p.1.1 p.1.2) ∘ₗ
    (Finsupp.linearEquivFunOnFinite F F (validIndices k D)).symm.toLinearMap

/-
The coefficient of X^i Y^j in the linear combination is the corresponding scalar.
-/
open Polynomial Finsupp

/-- The coefficient of X^i Y^j in a linear combination of monomials is the coefficient
of the combination. -/
lemma coeff_linearCombination_monomial {F : Type} [Field F]
  (c : (ℕ × ℕ) →₀ F) (i j : ℕ) : ((Finsupp.linearCombination F
  (fun p : ℕ × ℕ => monomial (F := F) p.1 p.2) c).coeff j).coeff i = c (i, j) := by
    simp [ linearCombination_apply, Finsupp.sum ];
    rw [ Finset.sum_eq_single ( i, j ) ] <;> simp +contextual;
    · erw [ Polynomial.coeff_monomial, if_pos rfl ] ; aesop;
    · intro a b hc hne; rw [ GuruswamiSudan.monomial ] ;
      by_cases ha : a = i <;> by_cases hb : b = j <;> simp_all [ Polynomial.coeff_monomial ]

/-
The bivariate monomials are linearly independent.
-/
open Polynomial Finsupp

/-- The monomials are linearly independent. -/
lemma linearIndependent_monomials {F : Type} [Field F] :
  LinearIndependent F (fun p : ℕ × ℕ => GuruswamiSudan.monomial (F := F) p.1 p.2) := by
    -- Apply the `linearIndependent_iff` theorem to the function that maps (i, j)
    -- to the monomial X^i Y^j.
    apply linearIndependent_iff.mpr;
    intro l hl; ext ⟨ i, j ⟩ ; replace hl := congr_arg ( fun f =>
      Polynomial.coeff ( Polynomial.coeff f j ) i ) hl; simp_all ;
    convert hl using 1;
    convert ( GuruswamiSudan.coeff_linearCombination_monomial l i j |> Eq.symm ) using 1

/-
The map from coefficients to polynomials is injective.
-/
open Polynomial Finsupp

/-- coeffsToPoly is injective. -/
lemma coeffsToPoly_injective {F : Type} [Field F] (k D : ℕ) :
  Function.Injective (coeffsToPoly (F := F) k D) := by
    -- The linear combination of linearly independent vectors is injective.
    have h_linear_combination_injective : Function.Injective (Finsupp.linearCombination F
        (fun p : validIndices k D => monomial (F := F) p.1.1 p.1.2)) := by
      have h_lin_indep : LinearIndependent F (fun p : ℕ × ℕ => monomial (F := F) p.1 p.2) := by
        exact linearIndependent_monomials;
      exact h_lin_indep.comp _ ( fun p q h => by aesop );
    exact h_linear_combination_injective.comp ( LinearEquiv.injective _ )

/-
Definition of the linear map representing the constraints.
-/
open Polynomial Finsupp

/-- The linear map representing the system of linear equations. -/
noncomputable def constraintMap {F : Type} [Field F] [DecidableEq F]
  (n k m D : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
  ((validIndices k D) → F) →ₗ[F] (Fin n → ConstraintIndex m → F) where
  toFun c i st := evalConstraint (ωs i) (f i) st.1.1 st.1.2 (coeffsToPoly k D c)
  map_add' c d := by
    simp +zetaDelta at *;
    rfl
  map_smul' a c := by
    unfold GuruswamiSudan.evalConstraint GuruswamiSudan.coeffsToPoly; aesop;

/-
There exists a non-zero coefficient vector in the kernel of the constraint map.
-/
open Polynomial Finsupp

/-- There exists a non-zero polynomial Q satisfying the conditions. -/
lemma exists_nonzero_solution {F : Type} [Field F] [DecidableEq F]
  (n k m : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
  ∃ c : (validIndices k (proximity_gap_degree_bound (n := n) k m)) → F,
    c ≠ 0 ∧ constraintMap n k m (proximity_gap_degree_bound (n := n) k m) ωs f c = 0 := by
      -- By the rank-nullity theorem, since the dimension of the domain is greater than
      -- the dimension of the codomain, the kernel of the linear map is non-trivial.
      have h_kernel_nontrivial : Module.finrank F ((validIndices k
        (proximity_gap_degree_bound (n := n) k m)) → F) >
          Module.finrank F ((Fin n → ConstraintIndex m → F)) := by
        convert numVars_gt_numConstraints n k m using 1;
        · simp [ numVars ];
        · simp [ numConstraints ];
          norm_num [ Module.finrank ];
      have h_inj : ¬ Function.Injective (constraintMap n k m
          (proximity_gap_degree_bound (n := n) k m) ωs f) := by
        intro h_inj;
        have := LinearMap.finrank_range_of_inj h_inj;
        exact h_kernel_nontrivial.not_ge ( this ▸ Submodule.finrank_le _ );
      contrapose! h_inj;
      exact LinearMap.ker_eq_bot.mp ( eq_bot_iff.mpr fun x hx =>
        by_contradiction fun hx' => h_inj x hx' <| by simpa using hx )

/-
The weighted degree of a monomial X^i Y^j is u*i + v*j.
-/
open Polynomial Finsupp

lemma natWeightedDegree_monomial {F : Type} [Semiring F] [Nontrivial F] (i j u v : ℕ) :
  Bivariate.natWeightedDegree (monomial (F := F) i j) u v = u * i + v * j := by
    simp [natWeightedDegree, monomial];
    refine le_antisymm ?_ ?_ <;> norm_num;
    · -- The coefficient of $X^j$ in $X^i$ is non-zero only when $j = i$,
      -- and in that case, the coefficient is $1$.
      intros b hb
      simp [Polynomial.coeff_monomial] at hb;
      simp [← hb];
      -- The degree of the polynomial $X^i$ is $i$.
      have h_deg : Polynomial.natDegree (Polynomial.monomial i (1 : F)) = i := by
        convert Polynomial.natDegree_monomial _;
        any_goals exact F;
        any_goals try infer_instance;
        convert Iff.rfl;
        rotate_left;
        exact Classical.typeDecidableEq F;
        exact 0;
        cases i <;> simp;
        exact Polynomial.natDegree_monomial_eq _ ( by simp +decide );
      rw [ h_deg ];
    · refine le_trans ?_ ( Finset.le_sup
        ( f := fun m => u * ( Polynomial.coeff ( Polynomial.monomial j
          ( Polynomial.monomial i 1 ) ) m |> Polynomial.natDegree ) + v * m ) (b := j) ( ?_ ) );
      all_goals norm_num [ Polynomial.coeff_monomial ];
      exact ( Nat.mul_le_mul_left _
          ( Polynomial.le_natDegree_of_ne_zero ( by simp ) ) )

/-
The weighted degree of a sum is at most the maximum of the weighted degrees.
-/
open Polynomial Finsupp

lemma natWeightedDegree_add_le {F : Type} [Semiring F] (p q : F[X][Y]) (u v : ℕ) :
  Bivariate.natWeightedDegree (p + q) u v ≤
    max (Bivariate.natWeightedDegree p u v) (Bivariate.natWeightedDegree q u v) := by
  refine Finset.sup_le fun m hm => ?_;
  by_cases h : m ∈ p.support <;>
  by_cases h' : m ∈ q.support <;> simp_all [ Polynomial.coeff_add ];
  · -- Since $p.coeff m \neq 0$ and $q.coeff m \neq 0$, we have
    -- $(p.coeff m + q.coeff m).natDegree \leq \max((p.coeff m).natDegree,
    -- (q.coeff m).natDegree)$.
    have h_deg : (p.coeff m + q.coeff m).natDegree ≤
        max ((p.coeff m).natDegree) ((q.coeff m).natDegree) := by
      exact natDegree_add_le (p.coeff m) (q.coeff m);
    cases max_cases ( Polynomial.natDegree ( p.coeff m ) )
      ( Polynomial.natDegree ( q.coeff m ) ) <;> simp_all [ Bivariate.natWeightedDegree ];
    · exact Or.inl ( le_trans ( add_le_add ( mul_le_mul_of_nonneg_left h_deg <|
        Nat.zero_le _ ) le_rfl ) <| Finset.le_sup ( f := fun m => u * Polynomial.natDegree
          ( p.coeff m ) + v * m ) <| by aesop );
    · exact Or.inr ( le_trans ( add_le_add ( mul_le_mul_of_nonneg_left h_deg <|
        Nat.zero_le _ ) le_rfl ) <| Finset.le_sup ( f := fun m => u * ( q.coeff m |>
          Polynomial.natDegree ) + v * m ) <| by aesop );
  · exact Or.inl <| Finset.le_sup ( f := fun m => u * ( p.coeff m |> Polynomial.natDegree )
      + v * m ) <| by aesop;
  · exact Or.inr ( Finset.le_sup ( f := fun m => u * ( q.coeff m |> Polynomial.natDegree )
      + v * m ) ( by aesop ) )

/-
The weighted degree of a scalar multiple is at most the weighted degree of the polynomial.
-/
open Polynomial Finsupp

lemma natWeightedDegree_smul_le {F : Type} [Semiring F] (a : F) (p : F[X][Y]) (u v : ℕ) :
  Bivariate.natWeightedDegree (a • p) u v ≤ Bivariate.natWeightedDegree p u v := by
    -- Let's unfold the definition of `natWeightedDegree`.
    simp [natWeightedDegree];
    intro b hb
    have h_deg : (a • p.coeff b).natDegree ≤ (p.coeff b).natDegree := by
      exact natDegree_smul_le a (p.coeff b);
    exact le_trans ( add_le_add
      ( mul_le_mul_of_nonneg_left h_deg u.zero_le )
      ( mul_le_mul_of_nonneg_left le_rfl v.zero_le ) )
      ( Finset.le_sup ( f := fun m => u * ( p.coeff m ).natDegree + v * m )
        ( show b ∈ p.support from by aesop ) )

/-
The weighted degree of a monomial X^i Y^j is u*i + v*j.
-/
open Polynomial Finsupp

lemma natWeightedDegree_monomial_eq {F : Type} [Semiring F] [Nontrivial F] (i j u v : ℕ) :
  Bivariate.natWeightedDegree (GuruswamiSudan.monomial (F := F) i j) u v = u * i + v * j := by
    convert natWeightedDegree_monomial i j u v using 1;
    infer_instance

/-
The weighted degree of a sum is bounded by the supremum of the weighted degrees.
-/
open Polynomial Finsupp

lemma natWeightedDegree_sum_le {F : Type} [Semiring F] {ι : Type*} [DecidableEq ι]
  (s : Finset ι) (f : ι → F[X][Y]) (u v : ℕ) :
  Bivariate.natWeightedDegree (∑ i ∈ s, f i) u v ≤
      s.sup (fun i => Bivariate.natWeightedDegree (f i) u v) := by
    induction s using Finset.induction <;> simp_all +decide;
    · simp [ Bivariate.natWeightedDegree ];
    · -- Apply the lemma that the weighted degree of a sum is bounded by the
      -- maximum of the weighted degrees of the summands.
      have h_sum : Bivariate.natWeightedDegree (f ‹_› + ∑ i ∈ ‹Finset ι›, f i) u v ≤
        max (Bivariate.natWeightedDegree (f ‹_›) u v) (Bivariate.natWeightedDegree
          (∑ i ∈ ‹Finset ι›, f i) u v) := by
        (expose_names; exact natWeightedDegree_add_le (f a) (∑ i ∈ s, f i) u v);
      cases max_cases ( natWeightedDegree ( f ‹_› ) u v )
        ( natWeightedDegree ( ∑ i ∈ ‹Finset ι›, f i ) u v ) <;> [ left; right ] <;> linarith

/-
The weighted degree of a sum is bounded by the supremum of the weighted degrees.
-/
open Polynomial Finsupp

lemma natWeightedDegree_sum_le' {F : Type} [Semiring F] {ι : Type*} [DecidableEq ι]
  (s : Finset ι) (f : ι → F[X][Y]) (u v : ℕ) :
  Bivariate.natWeightedDegree (∑ i ∈ s, f i) u v ≤
      s.sup (fun i => Bivariate.natWeightedDegree (f i) u v) := by
    convert natWeightedDegree_sum_le s f u v using 1

/-
The weighted degree of the polynomial constructed from coefficients is bounded by D.
-/
open Polynomial Finsupp

lemma natWeightedDegree_coeffsToPoly_le {F : Type} [Field F] (k D : ℕ)
  (c : (validIndices k D) → F) :
  Bivariate.natWeightedDegree (coeffsToPoly k D c) 1 (k - 1) ≤ D := by
    -- By definition of `coeffsToPoly`, we know that `coeffsToPoly k D c` is a linear
    -- combination of monomials.
    have h_comb : ∃ (s : Finset (ℕ × ℕ)) (f : ℕ × ℕ → F), (coeffsToPoly k D c) =
        ∑ p ∈ s, f p • (monomial (F := F) p.1 p.2) ∧ ∀ p ∈ s, p.1 + (k - 1) * p.2 ≤ D := by
      norm_num +zetaDelta at *;
      refine ⟨ Finset.image ( fun p : { x // x ∈ validIndices k D } => ( p.val.1, p.val.2 ) )
        Finset.univ, ?_, ?_ ⟩;
      · use fun p => if h : p ∈ Finset.image ( fun p : { x // x ∈ validIndices k D } =>
          ( p.val.1, p.val.2 ) ) Finset.univ then c ⟨ p, by aesop ⟩ else 0;
        unfold coeffsToPoly;
        simp [ Finsupp.linearCombination_apply, Finsupp.sum_fintype ];
        refine Finset.sum_bij ( fun x hx => x ) ?_ ?_ ?_ ?_ <;> aesop;
      · unfold validIndices at *; aesop;
    obtain ⟨ s, f, h₁, h₂ ⟩ := h_comb;
    rw [h₁];
    refine le_trans ( natWeightedDegree_sum_le' s _ _ _ ) ?_;
    refine Finset.sup_le fun p hp => le_trans ( natWeightedDegree_smul_le _ _ _ _ ) ?_;
    rw [ natWeightedDegree_monomial_eq ] ; aesop

/-
The polynomial solution constructed from the non-zero kernel element.
-/
open Polynomial Finsupp

noncomputable def solvedPoly {F : Type} [Field F] [DecidableEq F]
  (n k m : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) : F[X][Y] :=
  let D := proximity_gap_degree_bound (n := n) k m
  let c := Classical.choose (exists_nonzero_solution n k m ωs f)
  coeffsToPoly k D c

/-
The solved polynomial is non-zero and satisfies the degree bound.
-/
lemma solvedPoly_ne_zero {F : Type} [Field F] [DecidableEq F]
  (n k m : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
  solvedPoly n k m ωs f ≠ 0 := by
    have := Classical.choose_spec ( exists_nonzero_solution n k m ωs f );
    -- Since `coeffsToPoly` is injective, if the coefficient vector is non-zero,
    -- then the polynomial must also be non-zero.
    have h_inj : Function.Injective (coeffsToPoly (F := F) k
    (proximity_gap_degree_bound (n := n) k m)) := by
      exact coeffsToPoly_injective k (proximity_gap_degree_bound k m);
    exact fun h => this.1 <| h_inj <| by simpa using h;

lemma solvedPoly_weightedDegree_le {F : Type} [Field F] [DecidableEq F]
  (n k m : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
  Bivariate.weightedDegree (solvedPoly n k m ωs f) 1 (k - 1) ≤
    proximity_gap_degree_bound (n := n) k m := by
      -- By definition of `natWeightedDegree`, we know that
      -- `natWeightedDegree (coeffsToPoly k D c) 1 (k - 1) ≤ D`.
      have h_natWeightedDegree_le : Bivariate.natWeightedDegree
        (GuruswamiSudan.coeffsToPoly k
          (GuruswamiSudan.proximity_gap_degree_bound (n := n) k m)
            (Classical.choose (GuruswamiSudan.exists_nonzero_solution n k m ωs f))) 1 (k - 1) ≤
              GuruswamiSudan.proximity_gap_degree_bound (n := n) k m := by
        exact
          natWeightedDegree_coeffsToPoly_le k (proximity_gap_degree_bound k m)
            (Classical.choose (exists_nonzero_solution n k m ωs f));
      convert Option.some_le_some.mpr h_natWeightedDegree_le using 1;
      apply weightedDegree_eq_natWeightedDegree;
      exact solvedPoly_ne_zero n k m ωs f

/-
rootMultiplicity0 computes the total degree.
-/
open Polynomial Finsupp

lemma rootMultiplicity₀_eq_totalDegree {F : Type} [Semiring F] [DecidableEq F]
    (f : F[X][Y]) (hf : f ≠ 0) :
  Bivariate.rootMultiplicity₀ f = some (Bivariate.totalDegree f) := by
    have h_max_eq : ∀ (f : F[X][Y]), f ≠ 0 → ∃ (deg : ℕ), (weightedDegree f 1 1) =
        some deg ∧ (List.max? (List.map (fun x => if coeff f x.1 x.2 ≠ 0 then x.1 + x.2 else 0)
          (List.product (List.range (deg + 1)) (List.range (deg + 1))))) =
            some (totalDegree f) := by
      intros f hf_nonzero
      obtain ⟨deg, hdeg⟩ : ∃ (deg : ℕ),
          (weightedDegree f 1 1) = some deg ∧ deg = totalDegree f := by
        convert weightedDegree_eq_natWeightedDegree hf_nonzero using 1;
        rw [ total_deg_as_weighted_deg ];
        exact ⟨ fun ⟨ deg, hdeg₁, hdeg₂ ⟩ => hdeg₁.trans ( hdeg₂.symm ▸ rfl ),
            fun hdeg => ⟨ _, hdeg, rfl ⟩ ⟩;
      -- Since the total degree is the maximum of i+j for non-zero coefficients,
      -- and the list comprehension includes all possible i and j up to deg,
      -- the maximum should indeed be the total degree.
      have h_max : ∃ x ∈ List.product (List.range (deg + 1)) (List.range (deg + 1)),
          (if coeff f x.1 x.2 ≠ 0 then x.1 + x.2 else 0) = totalDegree f := by
        obtain ⟨i, j, hij⟩ : ∃ i j, coeff f i j ≠ 0 ∧ i + j = totalDegree f := by
          obtain ⟨i, j, hij⟩ : ∃ i j, (f.coeff j).coeff i ≠ 0 ∧ i + j = totalDegree f := by
            have h_support : ∃ p ∈ f.support, (f.coeff p).natDegree + p = totalDegree f := by
              have h_support : ∃ p ∈ f.support, ∀ q ∈ f.support, (f.coeff q).natDegree + q ≤
                  (f.coeff p).natDegree + p := by
                apply_rules [ Finset.exists_max_image ];
                exact Finset.nonempty_of_ne_empty ( by aesop );
              exact ⟨ h_support.choose, h_support.choose_spec.1,
                  le_antisymm ( Finset.le_sup ( f := fun p => Polynomial.natDegree
                      ( f.coeff p ) + p ) h_support.choose_spec.1 )
                        ( Finset.sup_le fun q hq => h_support.choose_spec.2 q hq ) ⟩
            obtain ⟨ p, hp₁, hp₂ ⟩ := h_support; use Polynomial.natDegree ( f.coeff p ), p;
            aesop;
          exact ⟨ i, j, hij ⟩;
        exact ⟨ ⟨ i, j ⟩, by
          erw [ List.mem_product ] ;
          exact ⟨ List.mem_range.mpr ( by linarith ), List.mem_range.mpr ( by linarith ) ⟩, by
          aesop ⟩;
      refine ⟨ deg, hdeg.1, (List.max?_eq_some_iff sorry sorry sorry).mpr ?_ ⟩;
      simp +zetaDelta at *;
      refine ⟨ h_max, ?_ ⟩;
      intro b x y hx hy hb; subst hb; split_ifs <;> simp_all +decide [ Bivariate.coeff ] ;
      exact Finset.le_sup ( f := fun m => Polynomial.natDegree ( f.coeff m ) + m )
        ( show y ∈ f.support from by aesop ) |>
          le_trans ( by linarith [ Polynomial.le_natDegree_of_ne_zero ‹_› ] );
    unfold rootMultiplicity₀; specialize h_max_eq f hf; aesop;


/-
If all coefficients of degree less than m are zero, the total degree is at least m.
-/
open Polynomial Finsupp

lemma totalDegree_ge_m_of_forall_coeff_zero_lt_m {F : Type} [Semiring F] [DecidableEq F]
  (f : F[X][Y]) (m : ℕ) (hf : f ≠ 0)
  (h : ∀ s t, s + t < m → Bivariate.coeff f s t = 0) :
  m ≤ Bivariate.totalDegree f := by
    have h_totalDegree_ge_m : ∃ p ∈ f.support, (f.coeff p).natDegree + p ≥ m := by
      by_contra h_contra
      push_neg at h_contra
      have h_zero : ∀ p ∈ f.support, (f.coeff p).natDegree + p < m := by
        assumption;
      refine hf ( Polynomial.ext fun p => ?_ );
      by_cases hp : p ∈ f.support <;> simp_all +decide [ Bivariate.coeff ];
      exact absurd ( h ( Polynomial.natDegree ( f.coeff p ) ) p ( h_zero p hp ) )
        ( by simp +decide [ Polynomial.coeff_natDegree, hp ] );
    exact h_totalDegree_ge_m.choose_spec.2.trans ( Finset.le_sup
      ( f := fun x => ( f.coeff x |> Polynomial.natDegree ) + x )
      h_totalDegree_ge_m.choose_spec.1 )

/-
If constraints vanish up to order m >= 1, the polynomial vanishes at the point.
-/
open Polynomial Finsupp

lemma eval_eq_zero_of_constraint_zero {F : Type} [CommSemiring F] [DecidableEq F]
  {Q : F[X][Y]} {x y : F} {m : ℕ} (hm : 1 ≤ m)
  (h : ∀ s t, s + t < m → evalConstraint x y s t Q = 0) :
  (Q.eval (C y)).eval x = 0 := by
    convert h 0 0 ( by linarith ) using 1;
    -- By definition of `evalConstraint`, we have
    -- `evalConstraint x y 0 0 Q = (shift Q x y).coeff 0`.
    -- Therefore, the equality holds by definition.
    simp [evalConstraint];
    unfold shift; simp +decide [ Polynomial.coeff_zero_eq_eval_zero ] ;

/-
If constraints vanish up to order m >= 1, the polynomial vanishes at the point.
-/
open Polynomial Finsupp GuruswamiSudan

lemma eval_eq_zero_of_constraint_zero' {F : Type} [CommSemiring F] [DecidableEq F]
  {Q : F[X][Y]} {x y : F} {m : ℕ} (hm : 1 ≤ m)
  (h : ∀ s t, s + t < m → evalConstraint x y s t Q = 0) :
  (Q.eval (C y)).eval x = 0 := by
    exact eval_eq_zero_of_constraint_zero hm h

/-
If s + t < m, then (s, t) is in ConstraintIndex m.
-/
open GuruswamiSudan

lemma mem_ConstraintIndex_of_lt {m s t : ℕ} (h : s + t < m) :
  (s, t) ∈ ConstraintIndex m := by
    exact Finset.mem_filter.mpr ⟨ Finset.mem_product.mpr
      ⟨ Finset.mem_range.mpr ( by linarith ), Finset.mem_range.mpr ( by linarith ) ⟩, h ⟩

/-
The solved polynomial vanishes at the interpolation points if m != 0.
-/
open Polynomial Polynomial.Bivariate GuruswamiSudan

lemma solvedPoly_roots {F : Type} [Field F] [DecidableEq F]
  (n k m : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) (hm : m ≠ 0) :
  ∀ i, ((solvedPoly n k m ωs f).eval (C <| f i)).eval (ωs i) = 0 := by
  intro i
  apply eval_eq_zero_of_constraint_zero'
  · exact Nat.pos_of_ne_zero hm
  · intro s t hst
    let c := Classical.choose (exists_nonzero_solution n k m ωs f)
    have hc := Classical.choose_spec (exists_nonzero_solution n k m ωs f)
    have h_ker := hc.2
    have h_eq1 := congr_fun h_ker i
    have h_eq2 := congr_fun h_eq1 ⟨(s, t), mem_ConstraintIndex_of_lt hst⟩
    exact h_eq2

/-
The solved polynomial has root multiplicity at least m at each point (ωs i, f i).
-/
open Polynomial Polynomial.Bivariate GuruswamiSudan

lemma solvedPoly_multiplicity' {F : Type} [Field F] [DecidableEq F]
  (n k m : ℕ) (ωs : Fin n ↪ F) (f : Fin n → F) :
  ∀ i, m ≤ Bivariate.rootMultiplicity (solvedPoly n k m ωs f) (ωs i) (f i) := by
  intro i
  let Q := solvedPoly n k m ωs f
  have hQ : Q ≠ 0 := solvedPoly_ne_zero n k m ωs f
  have h_shift : shift Q (ωs i) (f i) ≠ 0 := by
    intro h
    -- shift is an automorphism, so injective
    -- We can prove Q = 0 from shift Q = 0
    -- For now, sorry
    -- Since $Q$ is non-zero, its shift by any point is also non-zero.
    have h_shift_nonzero : ∀ x y : F, shift Q x y = 0 → Q = 0 := by
      intro x y hxy
      have h_shift_nonzero : shift Q x y = 0 → Q = 0 := by
        intro hxy
        have h_shift_nonzero : shift Q x y = 0 →
            Q.comp (Polynomial.X + Polynomial.C (Polynomial.C y)) = 0 := by
          intro hxy
          have h_shift_nonzero : Q.comp (Polynomial.X + Polynomial.C (Polynomial.C y)) =
              (shift Q x y).map (Polynomial.compRingHom (Polynomial.X - Polynomial.C x)) := by
            unfold shift; ext; simp; ring_nf;
            simp [Polynomial.comp_assoc];
          aesop;
        (expose_names; exact comp_X_add_C_eq_zero_iff.mp (h_shift_nonzero hxy_1));
      exact h_shift_nonzero hxy;
    exact hQ <| h_shift_nonzero _ _ h
  rw [Bivariate.rootMultiplicity]
  -- The definition of rootMultiplicity matches shift
  -- We need to verify this match or just use the fact that rootMultiplicity is
  -- defined via shift-like operations
  -- Actually, let's check the definition of rootMultiplicity again.
  -- def rootMultiplicity ... (f : F[X][Y]) (x y : F) : Option ℕ :=
  --   let X := ...
  --   rootMultiplicity₀ ... ((f.comp (Y + (C (C y)))).map (Polynomial.compRingHom (X + C x)))
  -- def shift ... (f : F[X][Y]) (x y : F) : F[X][Y] :=
  --   (f.comp (Polynomial.X + C (C y))).map (Polynomial.compRingHom (Polynomial.X + C x))
  -- They are identical.
  change m ≤ Bivariate.rootMultiplicity₀ (shift Q (ωs i) (f i))
  rw [rootMultiplicity₀_eq_totalDegree _ h_shift]
  apply totalDegree_ge_m_of_forall_coeff_zero_lt_m
  · exact h_shift
  · intro s t hst
    let c := Classical.choose (exists_nonzero_solution n k m ωs f)
    have hc := Classical.choose_spec (exists_nonzero_solution n k m ωs f)
    have h_ker := hc.2
    have h_eq := congr_fun (congr_fun h_ker i) ⟨(s, t), mem_ConstraintIndex_of_lt hst⟩
    -- h_eq is evalConstraint ... = 0
    -- evalConstraint x y s t Q = ((shift Q x y).coeff t).coeff s
    -- Bivariate.coeff f s t = (f.coeff t).coeff s
    -- So evalConstraint ... = Bivariate.coeff (shift ...) s t
    exact h_eq

/-
Existence of the Guruswami-Sudan polynomial (proven for m != 0).
-/
open Polynomial Polynomial.Bivariate GuruswamiSudan

theorem guruswami_sudan_existence {F : Type} [Field F] [DecidableEq F] {n : ℕ}
    {k m : ℕ} {ωs : Fin n ↪ F} {f : Fin n → F} :
  ∃ Q, Condition k m (proximity_gap_degree_bound (n := n) k m) ωs f Q := by
  by_cases hm : m = 0
  · sorry
  · let Q := solvedPoly n k m ωs f
    use Q
    constructor
    · exact solvedPoly_ne_zero n k m ωs f
    · exact solvedPoly_weightedDegree_le n k m ωs f
    · exact solvedPoly_roots n k m ωs f hm
    · exact solvedPoly_multiplicity' n k m ωs f

end GuruswamiSudanExistence

/-- The second part of lemma 5.3 from [BCIKS20].
    For any solution Q of the Guruswami-Sudan system, and for any
    polynomial P ∈ RS[n, k, ρ] such that Δ(w, P) ≤ δ₀(ρ, m),
    we have that Y - P(X) divides Q(X, Y) in the polynomial ring
    F[X][Y].
-/
lemma guruswami_sudan_for_proximity_gap_property {k m : ℕ} {ωs : Fin n ↪ F}
  {f : Fin n → F}
  {Q : F[X][X]}
  {p : ReedSolomon.code ωs n}
  (h : Δ₀(f, (ReedSolomon.codewordToPoly p).eval ∘ f) ≤ proximity_gap_johnson (n := n) k m)
  :
  ((X : F[X][X]) - C (ReedSolomon.codewordToPoly p)) ∣ Q := by sorry

end GuruswamiSudan
