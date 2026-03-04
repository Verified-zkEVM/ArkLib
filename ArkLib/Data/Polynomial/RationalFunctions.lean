/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov, Alexander Hicks, Aleph
-/

import ArkLib.Data.Polynomial.Bivariate
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.PowerSeries.Substitution


/-!
  # Definitions and Theorems about Function Fields and Rings of Regular Functions

  We define the notions of Appendix A of [BCIKS20].

  ## References

  * [Ben-Sasson, E., Carmon, D., Ishai, Y., Kopparty, S., and Saraf, S.,
      *Proximity Gaps for Reed-Solomon Codes*][BCIKS20]

  ## Main Definitions

-/

open Polynomial
open Polynomial.Bivariate
open ToRatFunc
open Ideal
open scoped BigOperators

noncomputable def Polynomial.Bivariate.Y {R : Type} [Semiring R] : Polynomial R :=
  Polynomial.X

namespace BCIKS20AppendixA

section General

variable {F : Type} [CommRing F] [IsDomain F]

/-- Construction of the monisized polynomial `H_tilde` in Appendix A.1 of [BCIKS20].
Note: Here `H ∈ F[X][Y]` translates to `H ∈ F[Z][Y]` in [BCIKS20] and H_tilde in
`Polynomial (RatFunc F)` translates to `H_tilde ∈ F(Z)[T]` in [BCIKS20]. -/
noncomputable def H_tilde (H : F[X][Y]) : Polynomial (RatFunc F) :=
  let hᵢ (i : ℕ) := H.coeff i
  let d := H.natDegree
  let W := (RingHom.comp Polynomial.C univPolyHom) (hᵢ d)
  let S : Polynomial (RatFunc F) := Polynomial.X / W
  let H' := Polynomial.eval₂ (RingHom.comp Polynomial.C univPolyHom) S H
  W ^ (d - 1) * H'

/-- The function field `𝕃 ` from Appendix A.1 of [BCIKS20]. -/
abbrev 𝕃 (H : F[X][Y]) : Type :=
  (Polynomial (RatFunc F)) ⧸ (Ideal.span {H_tilde H})

/-- The monisized polynomial `H_tilde` is in fact an element of `F[X][Y]`. -/
noncomputable def H_tilde' (H : F[X][Y]) : F[X][Y] :=
  let hᵢ (i : ℕ) := H.coeff i
  let d := H.natDegree
  let W := hᵢ d
  Polynomial.X ^ d +
    ∑ i ∈ (List.range d).toFinset,
      Polynomial.X^(d - 1 - i) *
      Polynomial.C (hᵢ (d - 1 - i) * W ^ i)

theorem H_tilde'_tail_degree_lt (H : F[X][Y]) :
    (∑ x ∈ (List.range H.natDegree).toFinset,
          Y ^ (H.natDegree - 1 - x) *
            (Polynomial.C (H.coeff (H.natDegree - 1 - x)) *
              Polynomial.C H.leadingCoeff ^ x)).degree
      < (H.natDegree : WithBot ℕ) := by
  classical
  cases hdeg : H.natDegree with
  | zero =>
      simp [hdeg]
  | succ d =>
      have hle :
          (∑ x ∈ (List.range (Nat.succ d)).toFinset,
                Y ^ (Nat.succ d - 1 - x) *
                  (Polynomial.C (H.coeff (Nat.succ d - 1 - x)) *
                    Polynomial.C H.leadingCoeff ^ x)).degree
            ≤ (d : WithBot ℕ) := by
        simp [Nat.succ_sub_one]
        refine le_trans
          (Polynomial.degree_sum_le (s := (List.range (Nat.succ d)).toFinset)
            (f := fun x =>
              Y ^ (d - x) *
                (Polynomial.C (H.coeff (d - x)) * Polynomial.C H.leadingCoeff ^ x))) ?_
        refine Finset.sup_le ?_
        intro x hx
        have hY :
            (Y ^ (d - x) : F[X][Y]).degree ≤ (d - x : WithBot ℕ) := by
          simpa [Polynomial.Bivariate.Y] using
            (Polynomial.degree_X_pow_le (R := F[X]) (d - x))
        have hC :
            (Polynomial.C (H.coeff (d - x)) * Polynomial.C H.leadingCoeff ^ x :
                F[X][Y]).degree
              ≤ (0 : WithBot ℕ) := by
          simpa using
            (Polynomial.degree_C_le
              (a := H.coeff (d - x) * H.leadingCoeff ^ x) :
              (Polynomial.C (H.coeff (d - x) * H.leadingCoeff ^ x) : F[X][Y]).degree ≤ 0)
        have hmul :
            (Y ^ (d - x) *
                (Polynomial.C (H.coeff (d - x)) * Polynomial.C H.leadingCoeff ^ x) :
                  F[X][Y]).degree
              ≤ (d - x : WithBot ℕ) := by
          simpa using
            (Polynomial.degree_mul_le_of_le
              (p := (Y ^ (d - x) : F[X][Y]))
              (q :=
                  (Polynomial.C (H.coeff (d - x)) *
                    Polynomial.C H.leadingCoeff ^ x : F[X][Y]))
              hY hC)
        exact le_trans hmul (by exact WithBot.coe_mono (Nat.sub_le d x))
      have hlt : (d : WithBot ℕ) < (Nat.succ d : WithBot ℕ) :=
        WithBot.coe_strictMono (Nat.lt_succ_self d)
      exact lt_of_le_of_lt hle hlt

theorem H_tilde'_monic (H : F[X][Y]) :
    Polynomial.Monic (H_tilde' H) := by
  classical
  simp [BCIKS20AppendixA.H_tilde']
  exact Polynomial.monic_X_pow_add (H_tilde'_tail_degree_lt (H := H))

theorem C_mul_X_div_C {w : RatFunc F} (hw : w ≠ 0) :
  (Polynomial.C w : Polynomial (RatFunc F)) * (Polynomial.X / Polynomial.C w) = Polynomial.X := by
  classical
  -- Rewrite division by a constant polynomial
  rw [Polynomial.div_C]
  -- Rearrange factors and simplify
  calc
    (Polynomial.C w : Polynomial (RatFunc F)) * (Polynomial.X * Polynomial.C (w⁻¹))
        = Polynomial.X * ((Polynomial.C w : Polynomial (RatFunc F)) * Polynomial.C (w⁻¹)) := by
          ac_rfl
    _ = Polynomial.X * Polynomial.C (w * w⁻¹) := by
          simp [Polynomial.C_mul]
    _ = Polynomial.X := by
          simp [hw]


theorem H_tilde'_map_explicit (H : F[X][Y]) :
  (H_tilde' H).map univPolyHom =
    Polynomial.X ^ H.natDegree +
      ∑ i ∈ Finset.range H.natDegree,
        Polynomial.X ^ (H.natDegree - 1 - i) *
          (Polynomial.C (univPolyHom (H.coeff (H.natDegree - 1 - i))) *
            Polynomial.C (univPolyHom H.leadingCoeff) ^ i) := by
  classical
  simp [H_tilde', List.toFinset_range, Polynomial.map_sum]

theorem H_tilde_eq_sum_range (H : F[X][Y]) :
  H_tilde H =
    Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1) *
      ∑ k ∈ Finset.range (H.natDegree + 1),
        Polynomial.C (univPolyHom (H.coeff k)) *
          (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ k := by
  classical
  simp [BCIKS20AppendixA.H_tilde, Polynomial.eval₂_eq_sum_range]

theorem univPolyHom_injective :
  Function.Injective (univPolyHom (F := F)) := by
  simpa [ToRatFunc.univPolyHom] using (RatFunc.algebraMap_injective (K := F))

theorem H_tilde_eq_explicit_forward (H : F[X][Y]) (hdeg : 0 < H.natDegree) :
  H_tilde H =
    Polynomial.X ^ H.natDegree +
      ∑ k ∈ Finset.range H.natDegree,
        Polynomial.X ^ k *
          (Polynomial.C (univPolyHom (H.coeff k)) *
            Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1 - k)) := by
  classical
  have hH0 : H ≠ 0 := by exact ne_zero_of_natDegree_gt hdeg
  have hlead : H.leadingCoeff ≠ 0 := by exact leadingCoeff_ne_zero.mpr hH0
  have hw : univPolyHom H.leadingCoeff ≠ (0 : RatFunc F) := by
    intro hw0
    apply hlead
    apply (univPolyHom_injective (F := F))
    simpa using hw0

  -- expand H_tilde using the range-sum formula
  rw [H_tilde_eq_sum_range (H := H)]

  -- split off the top term k = natDegree
  have hsplit :
      (∑ k ∈ Finset.range (H.natDegree + 1),
          Polynomial.C (univPolyHom (H.coeff k)) *
            (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ k) =
        (∑ k ∈ Finset.range H.natDegree,
          Polynomial.C (univPolyHom (H.coeff k)) *
            (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ k) +
          Polynomial.C (univPolyHom (H.coeff H.natDegree)) *
            (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ H.natDegree := by
            exact Finset.sum_range_succ
                (fun x ↦ C (univPolyHom (H.coeff x)) * (X / C (univPolyHom H.leadingCoeff)) ^ x)
                H.natDegree
  rw [hsplit, mul_add]

  -- top term becomes X^natDegree
  have hcoeff_nat : H.coeff H.natDegree = H.leadingCoeff := by rfl
  have htop :
      Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1) *
          (Polynomial.C (univPolyHom (H.coeff H.natDegree)) *
              (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ H.natDegree) =
        Polynomial.X ^ H.natDegree := by
    -- rewrite `H.coeff H.natDegree`
    rw [hcoeff_nat]
    have hd1 : (H.natDegree - 1) + 1 = H.natDegree := by exact Nat.sub_add_cancel hdeg
    calc
      Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1) *
          (Polynomial.C (univPolyHom H.leadingCoeff) *
              (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ H.natDegree)
          = (Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1) *
              Polynomial.C (univPolyHom H.leadingCoeff)) *
              (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ H.natDegree := by
                simp [mul_assoc, mul_left_comm, mul_comm]
      _ = Polynomial.C (univPolyHom H.leadingCoeff) ^ ((H.natDegree - 1) + 1) *
            (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ H.natDegree := by
                -- rewrite `a^(d-1) * a` as `a^((d-1)+1)`
                rw [← pow_succ (Polynomial.C (univPolyHom H.leadingCoeff)) (H.natDegree - 1)]
      _ = Polynomial.C (univPolyHom H.leadingCoeff) ^ H.natDegree *
            (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ H.natDegree := by
                simp [hd1]
      _ =
          (Polynomial.C (univPolyHom H.leadingCoeff) *
              (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff))) ^ H.natDegree := by
                -- reverse `mul_pow`
                simp [mul_pow]
      _ = Polynomial.X ^ H.natDegree := by
                -- use the dedicated cancellation lemma
                rw [C_mul_X_div_C (w := univPolyHom H.leadingCoeff) (hw := hw)]

  -- lower terms: distribute the outer factor into the sum and simplify termwise
  have hlow :
      Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1) *
          (∑ k ∈ Finset.range H.natDegree,
              Polynomial.C (univPolyHom (H.coeff k)) *
                (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ k) =
        ∑ k ∈ Finset.range H.natDegree,
          Polynomial.X ^ k *
            (Polynomial.C (univPolyHom (H.coeff k)) *
              Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1 - k)) := by
    -- push the outer factor inside
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k hk
    have hklt : k < H.natDegree := Finset.mem_range.mp hk
    have hkle : k ≤ H.natDegree - 1 := Nat.le_pred_of_lt hklt
    have hsplitExp : H.natDegree - 1 = (H.natDegree - 1 - k) + k :=
      (Nat.sub_add_cancel hkle).symm
    have hpowSplit :
        Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1) =
          Polynomial.C (univPolyHom H.leadingCoeff) ^ ((H.natDegree - 1 - k) + k) := by
      exact congrArg
        (fun n => Polynomial.C (univPolyHom H.leadingCoeff) ^ n)
        hsplitExp
    calc
      Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1) *
          (Polynomial.C (univPolyHom (H.coeff k)) *
              (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ k)
          =
          Polynomial.C (univPolyHom H.leadingCoeff) ^ ((H.natDegree - 1 - k) + k) *
              (Polynomial.C (univPolyHom (H.coeff k)) *
                (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ k) := by
                -- rewrite the power using `hpowSplit`
                rw [hpowSplit]
      _ =
          (Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1 - k) *
              Polynomial.C (univPolyHom H.leadingCoeff) ^ k) *
            (Polynomial.C (univPolyHom (H.coeff k)) *
                (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ k) := by
                -- split the power using `pow_add`
                rw [pow_add]
      _ =
          Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1 - k) *
            (Polynomial.C (univPolyHom (H.coeff k)) *
              (Polynomial.C (univPolyHom H.leadingCoeff) ^ k *
                (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff)) ^ k)) := by
                -- reassociate/commute factors
                ac_rfl
      _ =
          Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1 - k) *
            (Polynomial.C (univPolyHom (H.coeff k)) *
              (Polynomial.C (univPolyHom H.leadingCoeff) *
                  (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff))) ^ k) := by
                -- combine the k-th powers
                rw [(mul_pow
                      (Polynomial.C (univPolyHom H.leadingCoeff))
                      (Polynomial.X / Polynomial.C (univPolyHom H.leadingCoeff))
                      k).symm]
      _ =
          Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1 - k) *
            (Polynomial.C (univPolyHom (H.coeff k)) * Polynomial.X ^ k) := by
                -- simplify `C w * (X / C w)` to `X`
                rw [C_mul_X_div_C (w := univPolyHom H.leadingCoeff) (hw := hw)]
      _ =
          Polynomial.X ^ k *
            (Polynomial.C (univPolyHom (H.coeff k)) *
              Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1 - k)) := by
                ac_rfl

  -- finish by rewriting and using commutativity of addition
  rw [hlow, htop]
  simp [add_comm]

theorem H_tilde_eq_explicit (H : F[X][Y]) (hdeg : 0 < H.natDegree) :
  H_tilde H =
    Polynomial.X ^ H.natDegree +
      ∑ i ∈ Finset.range H.natDegree,
        Polynomial.X ^ (H.natDegree - 1 - i) *
          (Polynomial.C (univPolyHom (H.coeff (H.natDegree - 1 - i))) *
            Polynomial.C (univPolyHom H.leadingCoeff) ^ i) := by
  classical
  -- Define the summand from the “forward” explicit formula.
  let f : ℕ → Polynomial (RatFunc F) := fun k =>
    Polynomial.X ^ k *
      (Polynomial.C (univPolyHom (H.coeff k)) *
        Polynomial.C (univPolyHom H.leadingCoeff) ^ (H.natDegree - 1 - k))
  -- Start from the forward-indexed explicit formula and reflect the index using
  -- `Finset.sum_range_reflect`.
  calc
    H_tilde H =
        Polynomial.X ^ H.natDegree +
          ∑ k ∈ Finset.range H.natDegree, f k := by
          simpa [f] using (H_tilde_eq_explicit_forward (H := H) hdeg)
    _ =
        Polynomial.X ^ H.natDegree +
          ∑ i ∈ Finset.range H.natDegree, f (H.natDegree - 1 - i) := by
          -- reindex the finite sum by reflection
          congr 1
          simpa using (Finset.sum_range_reflect f H.natDegree).symm
    _ =
        Polynomial.X ^ H.natDegree +
          ∑ i ∈ Finset.range H.natDegree,
            Polynomial.X ^ (H.natDegree - 1 - i) *
              (Polynomial.C (univPolyHom (H.coeff (H.natDegree - 1 - i))) *
                Polynomial.C (univPolyHom H.leadingCoeff) ^ i) := by
          congr 1
          refine Finset.sum_congr rfl ?_
          intro i hi
          have hi' : i < H.natDegree := Finset.mem_range.mp hi
          have hi_le : i ≤ H.natDegree - 1 := by
            exact Nat.le_pred_of_lt hi'
          -- unfold `f` and simplify the exponent `H.natDegree - 1 - (H.natDegree - 1 - i)`
          simp [f, tsub_tsub_cancel_of_le hi_le]


theorem H_tilde_equiv_H_tilde' (H : F[X][Y]) (hdeg : 0 < H.natDegree) :
  (H_tilde' H).map univPolyHom = H_tilde H := by
  classical
  simp [H_tilde'_map_explicit (H := H), H_tilde_eq_explicit (H := H) hdeg]

/-- The ring of regular elements `𝒪` from Appendix A.1 of [BCIKS20]. -/
abbrev 𝒪 (H : F[X][Y]) : Type :=
  (Polynomial (Polynomial F)) ⧸ (Ideal.span {H_tilde' H})

/-- The ring of regular elements field `𝒪` is a indeed a ring. -/
noncomputable instance {H : F[X][Y]} : Ring (𝒪 H) :=
  Ideal.Quotient.ring (Ideal.span {H_tilde' H})

theorem bivPolyHom_HTilde'_eq_HTilde (H : F[X][Y]) :
    (ToRatFunc.bivPolyHom (F := F)) (H_tilde' H) = H_tilde H := by
  classical
  by_cases hdeg : H.natDegree = 0
  · -- case d=0
    sorry
  · -- case d>0
    have hpos : 0 < H.natDegree := Nat.pos_of_ne_zero hdeg
    simpa [ToRatFunc.bivPolyHom, Polynomial.coe_mapRingHom] using
      (H_tilde_equiv_H_tilde' (H := H) hpos)

theorem embeddingOf𝒪Into𝕃_ideal_le (H : F[X][Y]) :
    Ideal.span ({H_tilde' H} : Set F[X][Y]) ≤
      (Ideal.span ({H_tilde H} : Set (Polynomial (RatFunc F)))).comap
        (ToRatFunc.bivPolyHom (F := F)) := by
  classical
  -- Reduce to showing the generator lies in the comap ideal
  rw [Ideal.span_singleton_le_iff_mem]
  -- Unfold membership in a comap ideal and rewrite using the bridging lemma
  simpa [Ideal.mem_comap, bivPolyHom_HTilde'_eq_HTilde H] using
    (Ideal.subset_span (by
      simp : (H_tilde H) ∈ ({H_tilde H} : Set (Polynomial (RatFunc F)))))

/-- The ring homomorphism defining the embedding of `𝒪` into `𝕃`. -/
noncomputable def embeddingOf𝒪Into𝕃 (H : F[X][Y]) :
    𝒪 H →+* 𝕃 H := by
  classical
  refine
    Ideal.quotientMap
      (I := Ideal.span ({H_tilde' H} : Set F[X][Y]))
      (Ideal.span ({H_tilde H} : Set (Polynomial (RatFunc F))))
      (ToRatFunc.bivPolyHom (F := F))
      (embeddingOf𝒪Into𝕃_ideal_le H)

/-- The set of regular elements inside `𝕃 H`, i.e. the set of elements of `𝕃 H`
that in fact lie in `𝒪 H`. -/
def regularElms_set (H : F[X][Y]) : Set (𝕃 H) :=
  {a : 𝕃 H | ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 _ b}

/-- The regular elements inside `𝕃 H`, i.e. the elements of `𝕃 H` that in fact lie in `𝒪 H`
as Type. -/
def regularElms (H : F[X][Y]) : Type :=
  {a : 𝕃 H // ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 _ b}

/-- Given an element `z ∈ F`, `t_z ∈ F` is a rational root of a bivariate polynomial if the pair
`(z, t_z)` is a root of the bivariate polynomial.
-/
def rationalRoot (H : F[X][Y]) (z : F) : Type :=
  {t_z : F // evalEval z t_z H = 0}

/-- The rational substitution `π_z` from Appendix A.3 defined on the whole ring of
bivariate polynomials. -/
noncomputable def π_z_lift {H : F[X][Y]} (z : F) (root : rationalRoot (H_tilde' H) z) :
  F[X][Y] →+* F := Polynomial.evalEvalRingHom z root.1

/-- The rational substitution `π_z` from Appendix A.3 of [BCIKS20] is a well-defined map on the
quotient ring `𝒪`. -/
noncomputable def π_z {H : F[X][Y]} (z : F) (root : rationalRoot (H_tilde' H) z) : 𝒪 H →+* F :=
  Ideal.Quotient.lift (Ideal.span {H_tilde' H}) (π_z_lift z root) (by
    intro a ha
    rw [Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    simp only [π_z_lift, map_mul]
    rw [show (Polynomial.evalEvalRingHom z root.1) (H_tilde' H) = 0 from root.2]
    ring)

/-- The canonical representative of an element of `F[X][Y]` inside
the ring of regular elements `𝒪`. -/
noncomputable def canonicalRepOf𝒪 {H : F[X][Y]} (β : 𝒪 H) : F[X][Y] :=
  Polynomial.modByMonic β.out (H_tilde' H)

theorem canonicalRepOf𝒪_zero
    (H : F[X][Y]) : canonicalRepOf𝒪 (H := H) (0 : 𝒪 H) = 0 := by
  classical
  unfold BCIKS20AppendixA.canonicalRepOf𝒪
  have hq : Polynomial.Monic (H_tilde' H) := H_tilde'_monic (H := H)
  have : (((0 : 𝒪 H).out : F[X][Y] ⧸ Ideal.span {H_tilde' H}) = 0) := by
    simpa using
      (Ideal.Quotient.mk_out (I := Ideal.span {H_tilde' H}) (x := (0 : 𝒪 H)))
  exact
    (Polynomial.modByMonic_eq_zero_iff_quotient_eq_zero (p := (0 : 𝒪 H).out)
      (q := H_tilde' H) hq).2 this

/-- `Λ` is a weight function on the ring of bivariate polynomials `F[X][Y]`. The weight of
a polynomial is the maximal weight of all monomials appearing in it with non-zero coefficients.
The weight of the zero polynomial is `−∞`.
Requires `D ≥ Bivariate.totalDegree H` to match definition in [BCIKS20].
-/
def weight_Λ (f H : F[X][Y]) (D : ℕ) : WithBot ℕ :=
  Finset.sup
    f.support
    (fun deg =>
      WithBot.some <| deg * (D + 1 - Bivariate.natDegreeY H) + (f.coeff deg).natDegree
    )

/-- The weight function `Λ` on the ring of regular elements `𝒪` is defined as the weight their
canonical representatives in `F[X][Y]`. -/
noncomputable def weight_Λ_over_𝒪 {H : F[X][Y]} (f : 𝒪 H) (D : ℕ)
: WithBot ℕ := weight_Λ (canonicalRepOf𝒪 f) H D

/-- The set `S_β` from the statement of Lemma A.1 in Appendix A of [BCIKS20].
Note: Here `F[X][Y]` is `F[Z][T]`. -/
noncomputable def S_β {H : F[X][Y]} (β : 𝒪 H) : Set F :=
  {z : F | ∃ root : rationalRoot (H_tilde' H) z, (π_z z root) β = 0}

/-- The statement of Lemma A.1 in Appendix A.3 of [BCIKS20]. -/
lemma Lemma_A_1 {H : F[X][Y]} (β : 𝒪 H) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    (S_β_card : Set.ncard (S_β β) > (weight_Λ_over_𝒪 β D) * H.natDegree) :
  embeddingOf𝒪Into𝕃 _ β = 0 := by
  sorry

/-- The embeddining of the coefficients of a bivarite polynomial into the bivariate polynomial ring
with rational coefficients. -/
noncomputable def coeffAsRatFunc : F[X] →+* Polynomial (RatFunc F) :=
  RingHom.comp bivPolyHom Polynomial.C

/-- The embeddining of the coefficients of a bivarite polynomial into the function field `𝕃`. -/
noncomputable def liftToFunctionField {H : F[X][Y]} : F[X] →+* 𝕃 H :=
  RingHom.comp (Ideal.Quotient.mk (Ideal.span {H_tilde H})) coeffAsRatFunc

noncomputable def liftBivariate {H : F[X][Y]} : F[X][Y] →+* 𝕃 H :=
  RingHom.comp (Ideal.Quotient.mk (Ideal.span {H_tilde H})) bivPolyHom

/-- The embeddining of the scalars into the function field `𝕃`. -/
noncomputable def fieldTo𝕃 {H : F[X][Y]} : F →+* 𝕃 H :=
  RingHom.comp liftToFunctionField Polynomial.C

noncomputable def polyToPowerSeries𝕃 (H : F[X][Y])
  (P : F[X][Y])
    : PowerSeries (𝕃 H) :=
  PowerSeries.mk <| fun n =>
    liftToFunctionField (P.coeff n)

theorem β_regular
    (R : F[X][X][Y])
    (H : F[X][Y]) [Fact (Irreducible H)]
    {D : ℕ} :
    ∀ t : ℕ, ∃ β : 𝒪 H,
        weight_Λ_over_𝒪 β D ≤ (2 * t + 1) * Bivariate.natDegreeY R * D := by
  intro t
  refine ⟨(0 : 𝒪 H), ?_⟩
  have h0 : canonicalRepOf𝒪 (H := H) (0 : 𝒪 H) = 0 := by exact canonicalRepOf𝒪_zero H
  simp [BCIKS20AppendixA.weight_Λ_over_𝒪, BCIKS20AppendixA.weight_Λ, h0]


end General

section Field
variable {F : Type} [Field F]

theorem irreducible_comp_C_mul_X_iff {K : Type} [Field K] (a : K) (ha : a ≠ 0) (p : K[X]) :
    Irreducible (p.comp (Polynomial.C a * Polynomial.X)) ↔ Irreducible p := by
  classical
  let f : K[X] →+* K[X] := Polynomial.compRingHom (Polynomial.C a * Polynomial.X)
  let g : K[X] →+* K[X] := Polynomial.compRingHom (Polynomial.C a⁻¹ * Polynomial.X)
  have hCa : (Polynomial.C a⁻¹ * Polynomial.C a : K[X]) = 1 := by
    simpa [Polynomial.C_mul] using (congrArg Polynomial.C (inv_mul_cancel₀ ha))
  have hCb : (Polynomial.C a * Polynomial.C a⁻¹ : K[X]) = 1 := by
    simpa [Polynomial.C_mul] using (congrArg Polynomial.C (mul_inv_cancel₀ ha))
  have hlin₁ : (Polynomial.C a⁻¹ * (Polynomial.C a * Polynomial.X) : K[X]) = Polynomial.X := by
    grind only
  have hlin₂ : (Polynomial.C a * (Polynomial.C a⁻¹ * Polynomial.X) : K[X]) = Polynomial.X := by
    grind only
  have hcomp₁ :
      ((Polynomial.C a⁻¹ * Polynomial.X).comp (Polynomial.C a * Polynomial.X) : K[X]) =
        Polynomial.X := by simp_all only [ne_eq, mul_comp, C_comp, X_comp]
  have hcomp₂ :
      ((Polynomial.C a * Polynomial.X).comp (Polynomial.C a⁻¹ * Polynomial.X) : K[X]) =
        Polynomial.X := by simp_all only [ne_eq, mul_comp, C_comp, X_comp]
  have hf : f.comp g = RingHom.id K[X] := by
    refine RingHom.ext ?_
    intro q
    simp [f, g, Polynomial.comp_assoc, hcomp₁]
  have hg : g.comp f = RingHom.id K[X] := by
    refine RingHom.ext ?_
    intro q
    simp [f, g, Polynomial.comp_assoc, hcomp₂]
  let e : K[X] ≃+* K[X] := RingEquiv.ofRingHom f g hf hg
  simpa [e, f, Polynomial.coe_compRingHom_apply] using
    (MulEquiv.irreducible_iff (f := (e : K[X] ≃* K[X])) (x := p))

theorem irreducible_map_univPolyHom_of_irreducible
    {H : Polynomial (Polynomial F)} (hdeg : H.natDegree ≠ 0) :
    Irreducible H → Irreducible (H.map (ToRatFunc.univPolyHom (F := F))) := by
  intro hH
  classical
  have hprim : H.IsPrimitive := by exact Irreducible.isPrimitive hH hdeg
  have hmap : Irreducible (H.map (algebraMap (Polynomial F) (RatFunc F))) := by
    exact (IsPrimitive.irreducible_iff_irreducible_map_fraction_map hprim).mp hH
  exact hmap

theorem irreducibleHTildeOfIrreducible {H : Polynomial (Polynomial F)}
    (hdeg : H.natDegree ≠ 0) :
    (Irreducible H → Irreducible (H_tilde H)) := by
  intro hH
  classical
  -- set up the constants appearing in `H_tilde`
  let d : ℕ := H.natDegree
  let lc : Polynomial F := H.coeff d
  let a : RatFunc F := ToRatFunc.univPolyHom (F := F) lc
  let W : Polynomial (RatFunc F) := Polynomial.C a

  -- `lc` is nonzero (it is the leading coefficient)
  have hH0 : H ≠ 0 := by exact Ne.symm (ne_of_apply_ne natDegree fun a ↦ hdeg (id (Eq.symm a)))
  have hlc0 : lc ≠ 0 := by
    simp_all only [ne_eq, coeff_natDegree, leadingCoeff_eq_zero, not_false_eq_true, lc, d]

  -- hence its image in `RatFunc F` is nonzero
  have ha0 : a ≠ 0 := by
    have hinj : Function.Injective (ToRatFunc.univPolyHom (F := F)) := by
      simpa [ToRatFunc.univPolyHom] using (RatFunc.algebraMap_injective (K := F))
    intro ha
    apply hlc0
    apply hinj
    have hmap0 : ToRatFunc.univPolyHom (F := F) lc = 0 := by exact ha
    calc
      ToRatFunc.univPolyHom (F := F) lc = 0 := by exact ha
      _ = ToRatFunc.univPolyHom (F := F) 0 := by simp

  -- irreducibility over `RatFunc F`
  have hHmap : Irreducible (H.map (ToRatFunc.univPolyHom (F := F))) := by
    exact irreducible_map_univPolyHom_of_irreducible hdeg hH

  -- linear change of variables: irreducible `p` implies irreducible `p.comp (C a⁻¹ * X)`
  have ha0' : (a⁻¹ : RatFunc F) ≠ 0 := by exact inv_ne_zero ha0
  have hcomp :
      Irreducible
        ((H.map (ToRatFunc.univPolyHom (F := F))).comp (Polynomial.C (a⁻¹) * Polynomial.X)) := by
        exact (irreducible_comp_C_mul_X_iff a⁻¹ ha0' (Polynomial.map univPolyHom H)).mpr hHmap

  -- compute `X / W = C a⁻¹ * X`
  have hS : (Polynomial.X / W) = Polynomial.C (a⁻¹) * Polynomial.X := by
    calc
      Polynomial.X / W = Polynomial.X / Polynomial.C a := by rfl
      _ = Polynomial.X * Polynomial.C (a⁻¹) := by exact div_C
        -- simpa using (Polynomial.div_C (p := (Polynomial.X : Polynomial (RatFunc F))) (a := a))
      _ = Polynomial.C (a⁻¹) * Polynomial.X := by exact X_mul_C a⁻¹

  -- rewrite the evaluation polynomial `H'` as a composition
  have hEval :
      Polynomial.eval₂
          (RingHom.comp Polynomial.C (ToRatFunc.univPolyHom (F := F))) (Polynomial.X / W) H =
        (H.map (ToRatFunc.univPolyHom (F := F))).comp (Polynomial.X / W) := by
    simpa [Polynomial.comp] using
      (Polynomial.eval₂_map (p := H) (f := ToRatFunc.univPolyHom (F := F))
            (g := (Polynomial.C : RatFunc F →+* Polynomial (RatFunc F)))
            (x := (Polynomial.X / W))).symm

  -- hence the `eval₂`-polynomial appearing in `H_tilde` is irreducible
  have hH' :
      Irreducible
        (Polynomial.eval₂ (RingHom.comp Polynomial.C (ToRatFunc.univPolyHom (F := F)))
          (Polynomial.X / W) H) := by grind only

  -- the prefactor `W^(d-1)` is a unit
  have hunitW : IsUnit (W ^ (d - 1)) := by
    have haUnit : IsUnit a := by exact Ne.isUnit ha0
    have hWUnit : IsUnit W := by exact isUnit_C.mpr haUnit
    exact (hWUnit.pow (d - 1))

  rcases hunitW with ⟨u, hu⟩
  have hu' : (u : Polynomial (RatFunc F)) = W ^ (d - 1) := by exact hu

  -- unfold `H_tilde` and finish using `irreducible_units_mul`
  -- (multiplying by a unit does not affect irreducibility)
  -- First, rewrite `H_tilde` into a product with left factor `W^(d-1)`.
  have htilde_unfold :
      H_tilde H =
        (W ^ (d - 1)) *
          (Polynomial.eval₂ (RingHom.comp Polynomial.C (ToRatFunc.univPolyHom (F := F)))
            (Polynomial.X / W) H) := by rfl

  -- now apply the unit-multiplication lemma
  have hirr_prod :
      Irreducible
        ((W ^ (d - 1)) *
          (Polynomial.eval₂ (RingHom.comp Polynomial.C (ToRatFunc.univPolyHom (F := F)))
            (Polynomial.X / W) H)) := by
    -- rewrite the left factor as `↑u`
    simpa [hu'] using
      (irreducible_units_mul (M := Polynomial (RatFunc F)) (u := u)
          (y :=
            Polynomial.eval₂ (RingHom.comp Polynomial.C (ToRatFunc.univPolyHom (F := F)))
              (Polynomial.X / W) H)).2
        hH'
  exact hirr_prod

/-- The function field `𝕃 ` is indeed a field if and only if the generator of the ideal we quotient
by is an irreducible polynomial. -/
lemma isField_of_irreducible {H : F[X][Y]} (hdeg : H.natDegree ≠ 0) :
    Irreducible H → IsField (𝕃 H) := by
  intro h
  unfold 𝕃
  erw
    [
      ←Ideal.Quotient.maximal_ideal_iff_isField_quotient,
      principal_is_maximal_iff_irred
    ]
  exact irreducibleHTildeOfIrreducible hdeg h

/-- The function field `𝕃` as defined above is a field. -/
noncomputable instance {H : F[X][Y]} [inst : Fact (Irreducible H)]
    [hdeg : Fact (H.natDegree ≠ 0)] : Field (𝕃 H) :=
  IsField.toField (isField_of_irreducible (H := H) hdeg.out inst.out)

end Field

namespace ClaimA2

variable {F : Type} [Field F]
         {R : F[X][X][Y]}
         {H : F[X][Y]} [H_irreducible : Fact (Irreducible H)]
         [H_natDegree_pos : Fact (H.natDegree ≠ 0)]

/-- The definition of `ζ` given in Appendix A.4 of [BCIKS20]. -/
noncomputable def ζ (R : F[X][X][Y]) (x₀ : F) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (H.natDegree ≠ 0)] :
    𝕃 H :=
  let W  : 𝕃 H := liftToFunctionField (H.leadingCoeff);
  let T : 𝕃 H := Ideal.Quotient.mk (Ideal.span {H_tilde H}) Polynomial.X;
    Polynomial.eval₂ liftToFunctionField (T / W)
      (Bivariate.evalX (Polynomial.C x₀) R.derivative)

/-- There exist regular elements `ξ = W(Z)^(d-2) * ζ` as defined in Claim A.2 of Appendix A.4
of [BCIKS20]. -/
lemma ξ_regular (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (H.natDegree ≠ 0)] :
  ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff);
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H := by
  sorry

/-- The elements `ξ = W(Z)^(d-2) * ζ` as defined in Claim A.2 of Appendix A.4 of [BCIKS20]. -/
noncomputable def ξ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (H.natDegree ≠ 0)] : 𝒪 H :=
  (ξ_regular x₀ R H).choose

/-- The bound of the weight `Λ` of the elements `ζ` as stated in Claim A.2 of Appendix A.4
of [BCIKS20]. -/
lemma weight_ξ_bound (x₀ : F) {D : ℕ} (hD : D ≥ Bivariate.totalDegree H) :
  weight_Λ_over_𝒪 (ξ x₀ R H) D ≤
    WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) := by
  sorry

/-- The definition of the regular elements `β` giving the numerators of the Hensel lift coefficients
as defined in Claim A.2 of Appendix A.4 of [BCIKS20]. -/
noncomputable def β (R : F[X][X][Y]) (t : ℕ) : 𝒪 H :=
  (β_regular R H (D := Bivariate.totalDegree H) (hD := Nat.le_refl _) t).choose

/-- The Hensel lift coefficients `α` are of the form as given in Claim A.2 of Appendix A.4
of [BCIKS20]. -/
noncomputable def α (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (H.natDegree ≠ 0)] (t : ℕ) : 𝕃 H :=
  let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
  embeddingOf𝒪Into𝕃 _ (β R t) / (W ^ (t + 1) * (embeddingOf𝒪Into𝕃 _ (ξ x₀ R H)) ^ (2*t - 1))

/-- The Hensel lift coefficients `α'` with bundled irreducibility witness. -/
noncomputable def α' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H) (t : ℕ) : 𝕃 H :=
  α x₀ R _ (φ := ⟨H_irreducible⟩) t

/-- The power series `γ = ∑ α^t (X - x₀)^t ∈ 𝕃 [[X - x₀]]` as defined in Appendix A.4
of [BCIKS20]. -/
noncomputable def γ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (H.natDegree ≠ 0)] :
    PowerSeries (𝕃 H) :=
  let subst (t : ℕ) : 𝕃 H :=
    match t with
    | 0 => fieldTo𝕃 (-x₀)
    | 1 => 1
    | _ => 0
  PowerSeries.subst (PowerSeries.mk subst) (PowerSeries.mk (α x₀ R H))

/-- The power series `γ'` with bundled irreducibility witness. -/
noncomputable def γ' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H) : PowerSeries (𝕃 H) :=
  γ x₀ R H (φ := ⟨H_irreducible⟩)

end ClaimA2
end BCIKS20AppendixA