/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Katerina Hristova, František Silváši, Julian Sutherland, Ilia Vlasov, Alexander Hicks, Aleph
-/

import ArkLib.Data.Polynomial.Bivariate
import ArkLib.Data.Polynomial.Prelims
import ArkLib.Data.Polynomial.RationalFunctionsInfrastructure
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.PowerSeries.Substitution
import Mathlib.FieldTheory.RatFunc.Defs


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

theorem bivPolyHom_HTilde'_eq_HTilde (H : F[X][Y]) (hdeg : 0 < H.natDegree) :
    (ToRatFunc.bivPolyHom (F := F)) (H_tilde' H) = H_tilde H := by
  classical
  simpa [ToRatFunc.bivPolyHom, Polynomial.coe_mapRingHom] using
    (H_tilde_equiv_H_tilde' (H := H) hdeg)

theorem embeddingOf𝒪Into𝕃_ideal_le (H : F[X][Y]) (hdeg : 0 < H.natDegree) :
    Ideal.span ({H_tilde' H} : Set F[X][Y]) ≤
      (Ideal.span ({H_tilde H} : Set (Polynomial (RatFunc F)))).comap
        (ToRatFunc.bivPolyHom (F := F)) := by
  classical
  -- Reduce to showing the generator lies in the comap ideal
  rw [Ideal.span_singleton_le_iff_mem]
  -- Unfold membership in a comap ideal and rewrite using the bridging lemma
  simpa [Ideal.mem_comap, bivPolyHom_HTilde'_eq_HTilde H hdeg] using
    (Ideal.subset_span (by
      simp : (H_tilde H) ∈ ({H_tilde H} : Set (Polynomial (RatFunc F)))))

/-- The ring homomorphism defining the embedding of `𝒪` into `𝕃`. -/
noncomputable def embeddingOf𝒪Into𝕃 (H : F[X][Y]) [Fact (0 < H.natDegree)] :
    𝒪 H →+* 𝕃 H := by
  classical
  refine
    Ideal.quotientMap
      (I := Ideal.span ({H_tilde' H} : Set F[X][Y]))
      (Ideal.span ({H_tilde H} : Set (Polynomial (RatFunc F))))
      (ToRatFunc.bivPolyHom (F := F))
      (embeddingOf𝒪Into𝕃_ideal_le H (hdeg := (Fact.out : 0 < H.natDegree)))

/-- The set of regular elements inside `𝕃 H`, i.e. the set of elements of `𝕃 H`
that in fact lie in `𝒪 H`. -/
def regularElms_set (H : F[X][Y]) [Fact (0 < H.natDegree)] : Set (𝕃 H) :=
  {a : 𝕃 H | ∃ b : 𝒪 H, a = embeddingOf𝒪Into𝕃 _ b}

/-- The regular elements inside `𝕃 H`, i.e. the elements of `𝕃 H` that in fact lie in `𝒪 H`
as Type. -/
def regularElms (H : F[X][Y]) [Fact (0 < H.natDegree)] : Type :=
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

/-- `π_z_lift` annihilates `H_tilde'`. -/
theorem pi_z_lift_H_tilde'_eq_zero {H : F[X][Y]} (z : F)
    (root : rationalRoot (H_tilde' H) z) :
    π_z_lift (H := H) z root (H_tilde' H) = 0 := by
  classical
  simpa [π_z_lift] using root.property

/-- The kernel of `π_z_lift` contains the span of `H_tilde'`. -/
theorem pi_z_lift_span_le_ker {H : F[X][Y]} (z : F)
    (root : rationalRoot (H_tilde' H) z) :
    Ideal.span {H_tilde' H} ≤ RingHom.ker (π_z_lift (H := H) z root) := by
  classical
  refine
    (Ideal.span_singleton_le_iff_mem (I := RingHom.ker (π_z_lift (H := H) z root))
          (x := H_tilde' H)).2 ?_
  exact (RingHom.mem_ker).2 (pi_z_lift_H_tilde'_eq_zero (H := H) z root)

/-- `π_z_lift` vanishes on the span of `H_tilde'`. -/
theorem pi_z_lift_vanishes_on_span {H : F[X][Y]} (z : F)
    (root : rationalRoot (H_tilde' H) z) :
    ∀ a, a ∈ Ideal.span {H_tilde' H} → π_z_lift (H := H) z root a = 0 := by
  intro a ha
  have hker : a ∈ RingHom.ker (π_z_lift (H := H) z root) :=
    (pi_z_lift_span_le_ker (H := H) z root) ha
  exact (RingHom.mem_ker (f := π_z_lift (H := H) z root)).1 hker

/-- The rational substitution map `𝒪 H →+* F` obtained by descending `π_z_lift`. -/
noncomputable def π_z {H : F[X][Y]} (z : F) (root : rationalRoot (H_tilde' H) z) :
    𝒪 H →+* F := by
  classical
  refine Ideal.Quotient.lift (Ideal.span {H_tilde' H}) (π_z_lift (H := H) z root) ?_
  intro a ha
  exact pi_z_lift_vanishes_on_span (H := H) z root a ha

/-- The canonical representative of an element of `F[X][Y]` inside
the ring of regular elements `𝒪`. -/
noncomputable def canonicalRepOf𝒪 {H : F[X][Y]} (β : 𝒪 H) : F[X][Y] :=
  Polynomial.modByMonic β.out (H_tilde' H)

lemma pi_z_apply_out {H : F[X][Y]} (z : F) (root : rationalRoot (H_tilde' H) z)
    (β : 𝒪 H) :
    (π_z z root) β = π_z_lift (H := H) z root β.out := by
  classical
  have hβ :
      (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) β.out : 𝒪 H) = β :=
    Ideal.Quotient.mk_out (I := Ideal.span {H_tilde' H}) (x := β)
  calc
    (π_z z root) β
        = (π_z z root) (Ideal.Quotient.mk (Ideal.span {H_tilde' H}) β.out) := by
            simpa [hβ]
    _ = π_z_lift (H := H) z root β.out := by
            simpa [π_z] using
              (Ideal.Quotient.lift_mk (I := Ideal.span {H_tilde' H})
                (f := π_z_lift (H := H) z root)
                (H := pi_z_lift_vanishes_on_span (H := H) z root)
                (a := β.out))

lemma canonicalRepOf𝒪_sub_out_mem_span {H : F[X][Y]} (β : 𝒪 H) :
    β.out - canonicalRepOf𝒪 (H := H) β ∈ Ideal.span {H_tilde' H} := by
  classical
  have hmonic : Polynomial.Monic (H_tilde' H) := H_tilde'_monic (H := H)
  have hmod :
      canonicalRepOf𝒪 (H := H) β =
        β.out - (H_tilde' H) * (β.out /ₘ (H_tilde' H)) := by
    simpa [canonicalRepOf𝒪] using
      (Polynomial.modByMonic_eq_sub_mul_div (p := β.out) (q := H_tilde' H) hmonic)
  have hdiff :
      β.out - canonicalRepOf𝒪 (H := H) β =
        (H_tilde' H) * (β.out /ₘ (H_tilde' H)) := by
    calc
      β.out - canonicalRepOf𝒪 (H := H) β
          = β.out - (β.out - (H_tilde' H) * (β.out /ₘ (H_tilde' H))) := by
              simp [hmod]
      _ = β.out - β.out + (H_tilde' H) * (β.out /ₘ (H_tilde' H)) := by
              simp [sub_eq_add_neg, add_assoc, add_left_comm, add_comm]
      _ = (H_tilde' H) * (β.out /ₘ (H_tilde' H)) := by simp
  -- conclude membership in the principal ideal
  have hmem : (H_tilde' H : F[X][Y]) ∈ Ideal.span {H_tilde' H} :=
    Ideal.subset_span (by simp)
  simpa [hdiff, mul_comm] using (Ideal.mul_mem_left (Ideal.span {H_tilde' H})
    (β.out /ₘ (H_tilde' H)) hmem)

lemma pi_z_apply_canonicalRep {H : F[X][Y]} (z : F) (root : rationalRoot (H_tilde' H) z)
    (β : 𝒪 H) :
    (π_z z root) β = evalEval z root.1 (canonicalRepOf𝒪 (H := H) β) := by
  classical
  have hsub :
      π_z_lift (H := H) z root (β.out - canonicalRepOf𝒪 (H := H) β) = 0 := by
    exact pi_z_lift_vanishes_on_span (H := H) z root _ (canonicalRepOf𝒪_sub_out_mem_span (H := H) β)
  have hsub' :
      π_z_lift (H := H) z root β.out -
          π_z_lift (H := H) z root (canonicalRepOf𝒪 (H := H) β) = 0 := by
    simpa [map_sub] using hsub
  have h1 :
      π_z_lift (H := H) z root β.out =
        π_z_lift (H := H) z root (canonicalRepOf𝒪 (H := H) β) :=
    sub_eq_zero.mp hsub'
  calc
    (π_z z root) β
        = π_z_lift (H := H) z root β.out := by
            simpa using (pi_z_apply_out (H := H) z root β)
    _ = π_z_lift (H := H) z root (canonicalRepOf𝒪 (H := H) β) := h1
    _ = evalEval z root.1 (canonicalRepOf𝒪 (H := H) β) := by rfl


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
noncomputable def S_β {H : F[X][Y]} [Fact (0 < H.natDegree)] (β : 𝒪 H) : Set F :=
  {z : F | ∃ root : rationalRoot (H_tilde' H) z, (π_z z root) β = 0}

lemma resultantY_eval_eq_zero_of_Sβ {H : F[X][Y]} [Fact (0 < H.natDegree)]
    (β : 𝒪 H) {z : F} (hz : z ∈ S_β (H := H) β) :
    (Polynomial.evalRingHom z) (resultantY (H_tilde' H) (canonicalRepOf𝒪 (H := H) β)) = 0 := by
  classical
  rcases hz with ⟨root, hroot⟩
  -- abbreviations for specializations
  set f : Polynomial F := specializeX (F := F) z (H_tilde' H)
  set g : Polynomial F := specializeX (F := F) z (canonicalRepOf𝒪 (H := H) β)
  -- `H_tilde'` is monic, hence its specialization is nonzero
  have hmonic : Polynomial.Monic (H_tilde' H) := H_tilde'_monic (H := H)
  have hmonic_spec : Polynomial.Monic f := by
    simpa [f, specializeX_apply] using
      (Monic.map (f := Polynomial.evalRingHom z) hmonic)
  have hspec_nonzero : f ≠ 0 := hmonic_spec.ne_zero
  -- common root in the specialization
  have hHroot : f.eval root.1 = 0 := by
    simpa [f, specializeX_apply, map_evalRingHom_eval] using root.property
  have hβroot : g.eval root.1 = 0 := by
    have hπ : (π_z z root) β = 0 := hroot
    have hπ' :
        evalEval z root.1 (canonicalRepOf𝒪 (H := H) β) = 0 := by
      simpa [pi_z_apply_canonicalRep (H := H) z root β] using hπ
    simpa [g, specializeX_apply, map_evalRingHom_eval] using hπ'
  -- natDegree of `H_tilde'`
  have hdeg_tilde : (H_tilde' H).natDegree = H.natDegree := by
    classical
    have htail :
        (∑ x ∈ (List.range H.natDegree).toFinset,
              Y ^ (H.natDegree - 1 - x) *
                (Polynomial.C (H.coeff (H.natDegree - 1 - x)) *
                  Polynomial.C H.leadingCoeff ^ x)).degree
          < (H.natDegree : WithBot ℕ) :=
      H_tilde'_tail_degree_lt (H := H)
    have hXdeg :
        (Polynomial.X ^ H.natDegree : F[X][Y]).degree = (H.natDegree : WithBot ℕ) := by
      simpa using (Polynomial.degree_X_pow (R := F[X]) H.natDegree)
    have hlt :
        (∑ x ∈ (List.range H.natDegree).toFinset,
              Y ^ (H.natDegree - 1 - x) *
                (Polynomial.C (H.coeff (H.natDegree - 1 - x)) *
                  Polynomial.C H.leadingCoeff ^ x)).degree
          < (Polynomial.X ^ H.natDegree : F[X][Y]).degree := by
      simpa [hXdeg] using htail
    have hdeg :
        (H_tilde' H).degree = (Polynomial.X ^ H.natDegree : F[X][Y]).degree := by
      simpa [H_tilde'] using (Polynomial.degree_add_eq_left_of_degree_lt hlt)
    have hnat :
        (H_tilde' H).natDegree =
          (Polynomial.X ^ H.natDegree : F[X][Y]).natDegree :=
      Polynomial.natDegree_eq_of_degree_eq hdeg
    simpa [Polynomial.natDegree_X_pow] using hnat
  have hdeg_f : f.natDegree = H.natDegree := by
    simpa [f, hdeg_tilde, specializeX_apply] using
      (Monic.natDegree_map (hmo := hmonic) (f := Polynomial.evalRingHom z))
  have hf_le : f.natDegree ≤ (H_tilde' H).natDegree := by
    simpa [hdeg_f, hdeg_tilde]
  have hg_le : g.natDegree ≤ (canonicalRepOf𝒪 (H := H) β).natDegree := by
    simpa [g, specializeX_apply] using
      (Polynomial.natDegree_map_le (f := Polynomial.evalRingHom z)
        (p := canonicalRepOf𝒪 (H := H) β))
  -- use the common root to show resultant is zero
  have hres :
      Polynomial.resultant f g (H_tilde' H).natDegree (canonicalRepOf𝒪 (H := H) β).natDegree = 0 := by
    by_cases hβ0 : g = 0
    · -- show determinant is zero via a zero column in the Sylvester matrix
      have hm_pos : 0 < (H_tilde' H).natDegree := by
        simpa [hdeg_tilde] using (Fact.out : 0 < H.natDegree)
      let m := (H_tilde' H).natDegree
      let n := (canonicalRepOf𝒪 (H := H) β).natDegree
      have hdet : (Polynomial.sylvester f 0 m n).det = 0 := by
        classical
        let j : Fin (n + m) := Fin.natAdd n ⟨0, hm_pos⟩
        have hcol : ∀ i, Polynomial.sylvester f 0 m n i j = 0 := by
          intro i
          classical
          dsimp [Polynomial.sylvester, Matrix.of_apply]
          have hnlt : ¬ (n < n) := by exact lt_irrefl _
          simp [Fin.addCases, hnlt, j]
        exact Matrix.det_eq_zero_of_column_eq_zero j hcol
      -- rewrite g to zero
      rw [hβ0]
      simpa [Polynomial.resultant, m, n] using hdet
    · exact
        resultant_eq_zero_of_common_root_eval'
          (f := f) (g := g) (t := root.1)
          (hf := hspec_nonzero) (hg := hβ0)
          (hft := hHroot) (hgt := hβroot) (hf_le := hf_le) (hg_le := hg_le)
  -- unfold and finish
  simpa [resultantY_eval, f, g] using hres

/- 
/-- The statement of Lemma A.1 in Appendix A.3 of [BCIKS20]. -/
lemma Lemma_A_1 {H : F[X][Y]} [Field F] [Fact (0 < H.natDegree)]
    [UniqueFactorizationMonoid F] [Fact (Irreducible (H_tilde' H))]
    (β : 𝒪 H) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    (S_β_card : Set.ncard (S_β β) > (weight_Λ_over_𝒪 β D) * H.natDegree) :
  embeddingOf𝒪Into𝕃 _ β = 0 := by
  classical
  -- abbreviations
  set g : F[X][Y] := canonicalRepOf𝒪 (H := H) β
  set A : ℕ := D + 1 - Bivariate.natDegreeY H
  -- compute the degree of `H_tilde'`
  have hdeg_tilde : (H_tilde' H).natDegree = H.natDegree := by
    classical
    have hlt :
        (∑ x ∈ (List.range H.natDegree).toFinset,
              Y ^ (H.natDegree - 1 - x) *
                (Polynomial.C (H.coeff (H.natDegree - 1 - x)) *
                  Polynomial.C H.leadingCoeff ^ x)).degree
          < (Polynomial.X ^ H.natDegree : F[X][Y]).degree := by
      have htail := H_tilde'_tail_degree_lt (H := H)
      simpa [Polynomial.Bivariate.Y, Polynomial.degree_X_pow] using htail
    have hdeg :
        (H_tilde' H).degree = (Polynomial.X ^ H.natDegree : F[X][Y]).degree := by
      simpa [H_tilde'] using (Polynomial.degree_add_eq_left_of_degree_lt hlt)
    have hnat :
        (H_tilde' H).natDegree =
          (Polynomial.X ^ H.natDegree : F[X][Y]).natDegree :=
      Polynomial.natDegree_eq_of_degree_eq hdeg
    simpa [Polynomial.natDegree_X_pow] using hnat
  -- case split on `weight_Λ`
  cases hW : weight_Λ_over_𝒪 β D with
  | bot =>
      -- if the weight is ⊥, the canonical representative is zero
      have hsupp : g.support = ∅ := by
        classical
        have hsup :
            g.support.sup (fun deg =>
              (WithBot.some <| deg * A + (g.coeff deg).natDegree)) = (⊥ : WithBot ℕ) := by
          simpa [weight_Λ_over_𝒪, weight_Λ, g, A] using hW
        have hforall :
            ∀ s ∈ g.support,
              (WithBot.some <| s * A + (g.coeff s).natDegree) = (⊥ : WithBot ℕ) := by
          simpa using (Finset.sup_eq_bot_iff (f := fun deg =>
            (WithBot.some <| deg * A + (g.coeff deg).natDegree)) (S := g.support)).1 hsup
        by_contra hne
        obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        have hneq :
            (⊥ : WithBot ℕ) ≠ (WithBot.some <| s * A + (g.coeff s).natDegree) := by
          exact WithBot.bot_ne_coe
        exact (hneq (hforall s hs).symm).elim
      have hg0 : g = 0 := by
        simpa [g] using (Polynomial.support_eq_empty.mp hsupp)
      have hmem : β.out ∈ Ideal.span ({H_tilde' H} : Set F[X][Y]) := by
        simpa [g, hg0] using (canonicalRepOf𝒪_sub_out_mem_span (H := H) β)
      have hβ0 :
          (Ideal.Quotient.mk (Ideal.span ({H_tilde' H} : Set F[X][Y])) β.out : 𝒪 H) = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem).2 hmem
      have hβ0' : (β : 𝒪 H) = 0 := by
        simpa using (by
          simpa using (hβ0.trans (Ideal.Quotient.mk_out
            (I := Ideal.span ({H_tilde' H} : Set F[X][Y])) (x := β)).symm))
      simpa [hβ0'] 
  | coe B =>
      -- `g` is nonzero in this case
      have hg0 : g ≠ 0 := by
        intro hg0
        have : (weight_Λ_over_𝒪 β D) = (⊥ : WithBot ℕ) := by
          simp [weight_Λ_over_𝒪, weight_Λ, g, hg0]
        simpa [hW] using this
      -- `H_tilde'` is prime in a UFD
      have hprime : Prime (H_tilde' H) := by
        simpa using
          (UniqueFactorizationMonoid.irreducible_iff_prime (α := F[X][Y])).1
            (Fact.out : Irreducible (H_tilde' H))
      -- degree bound for the resultant
      have hcoeff_bound :
          ∀ k, (g.coeff k).natDegree ≤ B - A * k := by
        intro k
        by_cases hk : k ∈ g.support
        · have hsup :
              (WithBot.some (k * A + (g.coeff k).natDegree)) ≤
                weight_Λ_over_𝒪 β D := by
              simpa [weight_Λ_over_𝒪, weight_Λ, g, A] using
                (Finset.le_sup (s := g.support)
                  (f := fun deg =>
                    (WithBot.some <| deg * A + (g.coeff deg).natDegree)) hk)
          have hsup' :
              (WithBot.some (k * A + (g.coeff k).natDegree)) ≤ (WithBot.some B) := by
            simpa [hW] using hsup
          have hle : k * A + (g.coeff k).natDegree ≤ B := by
            exact (WithBot.coe_le_coe.1 hsup')
          have hle' : (g.coeff k).natDegree + A * k ≤ B := by
            simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hle
          have hAk : A * k ≤ B := (Nat.le_add_left _ _).trans hle'
          exact (Nat.le_sub_iff_add_le hAk).2 hle'
        · have hcoeff : g.coeff k = 0 := by
            exact (Polynomial.notMem_support_iff.mp hk)
          simpa [hcoeff] using (Nat.zero_le (B - A * k))
      have hB : A * g.natDegree ≤ B := by
        have hmem : g.natDegree ∈ g.support := by
          classical
          have hne : g.coeff g.natDegree ≠ 0 := by
            intro h0
            have hlead0 : g.leadingCoeff = 0 := by
              simpa [Polynomial.coeff_natDegree (p := g)] using h0
            exact (Polynomial.leadingCoeff_ne_zero.mpr hg0) hlead0
          exact Polynomial.mem_support_iff.mpr hne
        have hsup :
            (WithBot.some (g.natDegree * A + (g.coeff g.natDegree).natDegree)) ≤
              weight_Λ_over_𝒪 β D := by
          simpa [weight_Λ_over_𝒪, weight_Λ, g, A] using
            (Finset.le_sup (s := g.support)
              (f := fun deg =>
                (WithBot.some <| deg * A + (g.coeff deg).natDegree)) hmem)
        have hsup' :
            (WithBot.some (g.natDegree * A + (g.coeff g.natDegree).natDegree)) ≤
              (WithBot.some B) := by
          simpa [hW] using hsup
        have hle : g.natDegree * A + (g.coeff g.natDegree).natDegree ≤ B := by
          exact (WithBot.coe_le_coe.1 hsup')
        exact le_trans (Nat.le.intro (Nat.add_sub_cancel _ _)) (by
          have : g.natDegree * A ≤ g.natDegree * A + (g.coeff g.natDegree).natDegree :=
            Nat.le.intro (Nat.add_sub_cancel _ _)
          exact this.trans hle)
      have hcoeff_H :
          ∀ k, ((H_tilde' H).coeff k).natDegree ≤ A * ((H_tilde' H).natDegree - k) := by
        intro k
        -- split on the position of `k`
        by_cases hk : k = H.natDegree
        · subst hk
          simp [hdeg_tilde, A]
        · by_cases hklt : k < H.natDegree
          · -- compute the coefficient explicitly
            have hk' : k ≠ H.natDegree := hk
            have hcoeff :
                (H_tilde' H).coeff k =
                  H.coeff k * H.leadingCoeff ^ (H.natDegree - 1 - k) := by
              classical
              -- only one term contributes to the coefficient
              have hkmem : H.natDegree - 1 - k ∈ (List.range H.natDegree).toFinset := by
                have hklt' : H.natDegree - 1 - k < H.natDegree := by
                  have hpos : 0 < H.natDegree := (Fact.out : 0 < H.natDegree)
                  have hk_le : k ≤ H.natDegree - 1 := Nat.le_pred_of_lt hklt
                  exact lt_of_le_of_lt (Nat.sub_le _ _) (Nat.lt_of_lt_of_le hpos (Nat.succ_le_iff.mp hk_le))
                simpa [List.toFinset_range] using (Finset.mem_range.mpr hklt')
              have hsum :
                  (∑ i ∈ (List.range H.natDegree).toFinset,
                        Y ^ (H.natDegree - 1 - i) *
                          (Polynomial.C (H.coeff (H.natDegree - 1 - i)) *
                            Polynomial.C H.leadingCoeff ^ i)).coeff k =
                    H.coeff k * H.leadingCoeff ^ (H.natDegree - 1 - k) := by
                classical
                -- use `sum_eq_single` on the unique matching index
                refine (Finset.sum_eq_single (H.natDegree - 1 - k) ?_ ?_).trans ?_
                · intro i hi hne
                  have hcoeff' :
                      (Y ^ (H.natDegree - 1 - i) *
                          (Polynomial.C (H.coeff (H.natDegree - 1 - i)) *
                            Polynomial.C H.leadingCoeff ^ i) : F[X][Y]).coeff k = 0 := by
                    classical
                    have hne' : H.natDegree - 1 - i ≠ k := by
                      intro h
                      have : i = H.natDegree - 1 - k := by
                        exact Nat.sub_eq_iff_eq_add_of_le (Nat.le_pred_of_lt hklt) |>.1 (by simpa [h] using rfl)
                      exact hne this
                    simp [Polynomial.Bivariate.Y, Polynomial.coeff_X_pow, hne', mul_comm, mul_left_comm,
                      mul_assoc]
                  simpa [hcoeff'] 
                · intro hnot
                  exact (hnot hkmem).elim
                · classical
                  simp [Polynomial.Bivariate.Y, Polynomial.coeff_X_pow, hk, mul_comm, mul_left_comm,
                    mul_assoc, hkmem]
              -- combine with the leading term
              have hlead :
                  (Polynomial.X ^ H.natDegree : F[X][Y]).coeff k = 0 := by
                classical
                simp [Polynomial.coeff_X_pow, hk', Polynomial.Bivariate.Y]
              simpa [H_tilde', hlead, hsum]
            have hcoeff_Hk :
                (H.coeff k).natDegree ≤ D - k := by
              by_cases hk0 : H.coeff k = 0
              · simp [hk0]
              · have hk_support : k ∈ H.support := by
                  exact Polynomial.mem_support_iff.mpr hk0
                have hle :
                    (H.coeff k).natDegree + k ≤ Bivariate.totalDegree H := by
                  simpa [Bivariate.totalDegree] using
                    (Finset.le_sup (s := H.support)
                      (f := fun m => (H.coeff m).natDegree + m) hk_support)
                have hle' : (H.coeff k).natDegree + k ≤ D := le_trans hle hD
                have hkD : k ≤ D := (Nat.le_add_left _ _).trans hle'
                exact (Nat.le_sub_iff_add_le hkD).2 hle'
            have hlead_H :
                H.leadingCoeff.natDegree ≤ D - H.natDegree := by
              by_cases hH0 : H = 0
              · simp [hH0]
              · have hlead0 : H.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hH0
                have hle :
                    H.leadingCoeff.natDegree + H.natDegree ≤ Bivariate.totalDegree H := by
                  simpa [Bivariate.totalDegree] using
                    (Finset.le_sup (s := H.support)
                      (f := fun m => (H.coeff m).natDegree + m)
                      (Polynomial.mem_support_iff.mpr hlead0))
                have hle' : H.leadingCoeff.natDegree + H.natDegree ≤ D := le_trans hle hD
                have hdegD : H.natDegree ≤ D := (Nat.le_add_left _ _).trans hle'
                exact (Nat.le_sub_iff_add_le hdegD).2 hle'
            -- use degree bounds
            have hpow :
                (H.leadingCoeff ^ (H.natDegree - 1 - k)).natDegree ≤
                  (H.natDegree - 1 - k) * (D - H.natDegree) :=
              (Polynomial.natDegree_pow_le _ _).trans <| by
                simpa [Nat.mul_comm] using (Nat.mul_le_mul_left _ hlead_H)
            have hmul :
                (H.coeff k * H.leadingCoeff ^ (H.natDegree - 1 - k)).natDegree ≤
                  (D - k) + (H.natDegree - 1 - k) * (D - H.natDegree) := by
              exact (Polynomial.natDegree_mul_le).trans (by
                exact Nat.add_le_add hcoeff_Hk hpow)
            -- rewrite the arithmetic
            have harith :
                (D - k) + (H.natDegree - 1 - k) * (D - H.natDegree) =
                  (D + 1 - H.natDegree) * (H.natDegree - k) := by
              -- algebra in ℕ
              have hk' : k ≤ H.natDegree - 1 := Nat.le_pred_of_lt hklt
              have hk'' : H.natDegree - k = (H.natDegree - 1 - k) + 1 := by
                exact (Nat.succ_sub (Nat.le_pred_of_lt hklt)).symm
              calc
                (D - k) + (H.natDegree - 1 - k) * (D - H.natDegree) =
                    (D - H.natDegree) * (H.natDegree - 1 - k) + (D - k) := by
                      ac_rfl
                _ = (D - H.natDegree) * (H.natDegree - 1 - k) + ((D - H.natDegree) + (H.natDegree - k)) := by
                      -- expand `D - k` as `(D - H.natDegree) + (H.natDegree - k)`
                      have : D - k = (D - H.natDegree) + (H.natDegree - k) := by
                        exact (Nat.sub_eq_iff_eq_add_of_le (Nat.le_trans (Nat.le_of_lt hklt) (Nat.le_of_lt (Fact.out : 0 < H.natDegree)))).symm
                      simpa [this]
                _ = (D + 1 - H.natDegree) * (H.natDegree - k) := by
                      -- collect terms
                      have hk'' : H.natDegree - k = (H.natDegree - 1 - k) + 1 := by
                        exact (Nat.succ_sub (Nat.le_pred_of_lt hklt)).symm
                      -- use distributivity
                      calc
                        (D - H.natDegree) * (H.natDegree - 1 - k) +
                            ((D - H.natDegree) + (H.natDegree - k)) =
                          (D - H.natDegree) * (H.natDegree - 1 - k) +
                            (D - H.natDegree) + (H.natDegree - k) := by
                              ac_rfl
                        _ = (D - H.natDegree) * ((H.natDegree - 1 - k) + 1) +
                            (H.natDegree - k) := by
                              simp [Nat.mul_add]
                        _ = (D - H.natDegree + 1) * (H.natDegree - k) := by
                              simp [hk'', Nat.add_comm, Nat.add_left_comm, Nat.add_assoc, Nat.mul_add,
                                Nat.add_mul]
            -- finish
            have :
                ((H_tilde' H).coeff k).natDegree ≤ (D + 1 - H.natDegree) * (H.natDegree - k) := by
              simpa [hcoeff, A] using hmul.trans (by simpa [harith, A])
            simpa [A, hdeg_tilde] using this
          · -- k > H.natDegree: coefficient vanishes
            have hkgt : H.natDegree < k := lt_of_le_of_ne (Nat.le_of_lt_succ ?_) ?_
            have hcoeff : (H_tilde' H).coeff k = 0 := by
              exact Polynomial.coeff_eq_zero_of_natDegree_lt (by
                simpa [hdeg_tilde] using hkgt)
            simp [hcoeff, hdeg_tilde]
      -- resultant degree bound
      have hdeg_res :
          (resultantY (H_tilde' H) g).natDegree ≤ (H_tilde' H).natDegree * B := by
        exact natDegree_resultantY_le_weight (A := A) (B := B) (f := H_tilde' H) (g := g)
          (hB := hB) (hf := hcoeff_H) (hg := hcoeff_bound)
      -- roots count gives zero resultant
      have hcard' : (S_β (H := H) β).ncard > B * H.natDegree := by
        simpa [hW] using S_β_card
      have hfinite : (S_β (H := H) β).Finite := by
        exact Set.finite_of_ncard_pos (lt_trans (Nat.zero_lt_one) hcard')
      let s : Finset F := hfinite.toFinset
      have hs : ∀ z ∈ s,
          (resultantY (H_tilde' H) g).eval z = 0 := by
        intro z hz
        have hz' : z ∈ S_β (H := H) β := by
          simpa [Set.mem_toFinset] using hz
        have hres := resultantY_eval_eq_zero_of_Sβ (H := H) (β := β) hz'
        simpa using hres
      have hdeg_lt : (resultantY (H_tilde' H) g).natDegree < s.card := by
        -- convert the bound to a strict inequality using the cardinality assumption
        have hs_card : s.card = (S_β (H := H) β).ncard := by
          simpa [s, Set.ncard_eq_toFinset_card] using rfl
        have hdeg_le : (resultantY (H_tilde' H) g).natDegree ≤ B * H.natDegree := by
          simpa [hdeg_tilde] using hdeg_res
        have hlt : B * H.natDegree < (S_β (H := H) β).ncard := hcard'
        exact lt_of_le_of_lt hdeg_le (by simpa [hs_card] using hlt)
      have hres_zero :
          resultantY (H_tilde' H) g = 0 :=
        eq_zero_of_card_lt_roots (p := resultantY (H_tilde' H) g) (s := s) hs hdeg_lt
      -- contradiction with nonzero resultant
      -- show resultant is nonzero using irreducibility
      have hres_nonzero : resultantY (H_tilde' H) g ≠ 0 := by
        -- if `g` is constant, use the explicit formula; otherwise use the Bézout relation
        by_cases hgdeg : g.natDegree = 0
        · -- constant case
          have hgC : g = Polynomial.C (g.coeff 0) := by
            exact Polynomial.eq_C_of_natDegree_eq_zero hgdeg
          have hcoeff0 : g.coeff 0 ≠ 0 := by
            intro h0
            apply hg0
            simpa [hgC, h0] using rfl
          have hres' :
              resultantY (H_tilde' H) g = (g.coeff 0) ^ (H_tilde' H).natDegree := by
            rw [hgC, resultantY_def]
            simpa using
              (Polynomial.resultant_C_right (f := H_tilde' H) (a := g.coeff 0)
                (m := (H_tilde' H).natDegree))
          have : (g.coeff 0) ^ (H_tilde' H).natDegree ≠ (0 : F[X]) := by
            exact pow_ne_zero _ hcoeff0
          intro h0
          apply this
          simpa [hres'] using h0
        · intro hres
          have hgpos : 0 < g.natDegree := Nat.pos_of_ne_zero hgdeg
          have hfpos : 0 < (H_tilde' H).natDegree := by
            simpa [hdeg_tilde] using (Fact.out : 0 < H.natDegree)
          -- obtain the Bézout relation from `resultant = 0`
          rcases exists_bezout_of_resultant_eq_zero
              (f := H_tilde' H) (g := g) (hf := hfpos) (hg := hgpos)
              (hres := by simpa [resultantY] using hres) with
            ⟨p, q, hpdeg, hqdeg, hbez, hpq⟩
          have hmul : (H_tilde' H) ∣ g * p := by
            -- from `f * q + g * p = 0`
            have : g * p = -(H_tilde' H) * q := by
              have := congrArg (fun t => t - (H_tilde' H) * q) hbez
              simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
                mul_assoc] using this
            refine ?_
            exact ⟨-q, by simpa [this, mul_comm, mul_left_comm, mul_assoc]⟩
          have hdiv : (H_tilde' H) ∣ g ∨ (H_tilde' H) ∣ p := hprime.dvd_or_dvd hmul
          -- show neither can happen
          have hdeg_g : g.natDegree < (H_tilde' H).natDegree := by
            have hmonic : Polynomial.Monic (H_tilde' H) := H_tilde'_monic (H := H)
            have hne1 : (H_tilde' H) ≠ 1 := by
              intro h1
              have : (H_tilde' H).natDegree = 0 := by
                simpa [h1] using (Polynomial.natDegree_one (R := F[X]))
              exact (Nat.lt_asymm (by simpa [hdeg_tilde] using (Fact.out : 0 < H.natDegree)) this).elim
            simpa [g, canonicalRepOf𝒪, hdeg_tilde] using
              (Polynomial.natDegree_modByMonic_lt (p := β.out) (hmq := hmonic) (hq := hne1))
          have hnot_g : ¬ (H_tilde' H) ∣ g := by
            intro hdivg
            have hle : (H_tilde' H).natDegree ≤ g.natDegree :=
              Polynomial.natDegree_le_of_dvd hdivg hg0
            exact (not_lt_of_ge hle hdeg_g)
          have hnot_p : ¬ (H_tilde' H) ∣ p := by
            intro hdivp
            have hle : (H_tilde' H).natDegree ≤ p.natDegree := by
              have hp0 : p ≠ 0 := by
                intro hp0
                cases hpq with
                | inl hp => exact hp hp0
                | inr hq =>
                    have : q = 0 := by
                      simpa [hp0] using (eq_of_mul_eq_zero_left (by
                        simpa [hp0] using hbez))
                    exact hq this
              exact Polynomial.natDegree_le_of_dvd hdivp hp0
            exact (not_lt_of_ge hle hpdeg)
          cases hdiv with
          | inl hdivg => exact (hnot_g hdivg).elim
          | inr hdivp => exact (hnot_p hdivp).elim
      exact (hres_nonzero hres_zero).elim

-/
/-- The embeddining of the coefficients of a bivarite polynomial into the bivariate polynomial ring
with rational coefficients. -/
noncomputable def coeffAsRatFunc : F[X] →+* Polynomial (RatFunc F) :=
  RingHom.comp bivPolyHom Polynomial.C

lemma eval₂_coeffAsRatFunc_X (p : F[X][Y]) :
    Polynomial.eval₂ (coeffAsRatFunc (F := F)) Polynomial.X p = bivPolyHom p := by
  classical
  refine Polynomial.induction_on' p ?add ?mono
  · intro p q hp hq
    simp [hp, hq, Polynomial.eval₂_add]
  · intro n a
    simp [coeffAsRatFunc, bivPolyHom, Polynomial.eval₂_monomial, C_mul_X_pow_eq_monomial]

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

/-- The statement of Lemma A.1 in Appendix A.3 of [BCIKS20], in the field setting. -/
lemma Lemma_A_1 {H : F[X][Y]} [Fact (0 < H.natDegree)]
    [UniqueFactorizationMonoid F] [Fact (Irreducible (H_tilde' H))]
    (β : 𝒪 H) (D : ℕ) (hD : D ≥ Bivariate.totalDegree H)
    (hcoeff_H :
      ∀ k, ((H_tilde' H).coeff k).natDegree ≤
        (D + 1 - Bivariate.natDegreeY H) * ((H_tilde' H).natDegree - k))
    (S_β_card : Set.ncard (S_β (H := H) β) > (weight_Λ_over_𝒪 β D) * H.natDegree) :
  embeddingOf𝒪Into𝕃 _ β = 0 := by
  classical
  set g : F[X][Y] := canonicalRepOf𝒪 (H := H) β
  set A : ℕ := D + 1 - Bivariate.natDegreeY H
  have hdeg_tilde : (H_tilde' H).natDegree = H.natDegree := by
    classical
    have hlt :
        (∑ x ∈ (List.range H.natDegree).toFinset,
              Y ^ (H.natDegree - 1 - x) *
                (Polynomial.C (H.coeff (H.natDegree - 1 - x)) *
                  Polynomial.C H.leadingCoeff ^ x)).degree
          < (Polynomial.X ^ H.natDegree : F[X][Y]).degree := by
      have htail := H_tilde'_tail_degree_lt (H := H)
      simpa [Polynomial.Bivariate.Y, Polynomial.degree_X_pow] using htail
    have hdeg :
        (H_tilde' H).degree = (Polynomial.X ^ H.natDegree : F[X][Y]).degree := by
      simpa [H_tilde'] using (Polynomial.degree_add_eq_left_of_degree_lt hlt)
    have hnat :
        (H_tilde' H).natDegree =
          (Polynomial.X ^ H.natDegree : F[X][Y]).natDegree :=
      Polynomial.natDegree_eq_of_degree_eq hdeg
    simpa [Polynomial.natDegree_X_pow] using hnat
  cases hW : weight_Λ_over_𝒪 β D with
  | bot =>
      have hsupp : g.support = ∅ := by
        classical
        have hsup :
            g.support.sup (fun deg =>
              (WithBot.some <| deg * A + (g.coeff deg).natDegree)) = (⊥ : WithBot ℕ) := by
          simpa [weight_Λ_over_𝒪, weight_Λ, g, A] using hW
        have hforall :
            ∀ s ∈ g.support,
              (WithBot.some <| s * A + (g.coeff s).natDegree) = (⊥ : WithBot ℕ) := by
          simpa using (Finset.sup_eq_bot_iff (f := fun deg =>
            (WithBot.some <| deg * A + (g.coeff deg).natDegree)) (S := g.support)).1 hsup
        by_contra hne
        obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.mpr hne
        have hneq :
            (⊥ : WithBot ℕ) ≠ (WithBot.some <| s * A + (g.coeff s).natDegree) := by
          exact WithBot.bot_ne_coe
        exact (hneq (hforall s hs).symm).elim
      have hg0 : g = 0 := by
        simpa [g] using (Polynomial.support_eq_empty.mp hsupp)
      have hmem : β.out ∈ Ideal.span ({H_tilde' H} : Set F[X][Y]) := by
        simpa [g, hg0] using (canonicalRepOf𝒪_sub_out_mem_span (H := H) β)
      have hβ0 :
          (Ideal.Quotient.mk (Ideal.span ({H_tilde' H} : Set F[X][Y])) β.out : 𝒪 H) = 0 :=
        (Ideal.Quotient.eq_zero_iff_mem).2 hmem
      have hβ0' : (β : 𝒪 H) = 0 := by
        simpa [Ideal.Quotient.mk_out (I := Ideal.span ({H_tilde' H} : Set F[X][Y])) (x := β)] using
          hβ0
      simpa [hβ0']
  | coe B =>
      have hg0 : g ≠ 0 := by
        intro hg0
        have : (weight_Λ_over_𝒪 β D) = (⊥ : WithBot ℕ) := by
          simp [weight_Λ_over_𝒪, weight_Λ, g, hg0]
        simpa [hW] using this
      have hprime : Prime (H_tilde' H) := by
        simpa using
          (UniqueFactorizationMonoid.irreducible_iff_prime (α := F[X][Y])).1
            (Fact.out : Irreducible (H_tilde' H))
      have hcoeff_bound :
          ∀ k, (g.coeff k).natDegree ≤ B - A * k := by
        intro k
        by_cases hk : k ∈ g.support
        · have hsup :
              (WithBot.some (k * A + (g.coeff k).natDegree)) ≤
                weight_Λ_over_𝒪 β D := by
              simpa [weight_Λ_over_𝒪, weight_Λ, g, A] using
                (Finset.le_sup (s := g.support)
                  (f := fun deg =>
                    (WithBot.some <| deg * A + (g.coeff deg).natDegree)) hk)
          have hsup' :
              (WithBot.some (k * A + (g.coeff k).natDegree)) ≤ (WithBot.some B) := by
            simpa [hW] using hsup
          have hle : k * A + (g.coeff k).natDegree ≤ B := by
            exact (WithBot.coe_le_coe.1 hsup')
          have hle' : (g.coeff k).natDegree + A * k ≤ B := by
            simpa [Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hle
          have hAk : A * k ≤ B := (Nat.le_add_left _ _).trans hle'
          exact (Nat.le_sub_iff_add_le hAk).2 hle'
        · have hcoeff : g.coeff k = 0 := by
            exact (Polynomial.notMem_support_iff.mp hk)
          simpa [hcoeff] using (Nat.zero_le (B - A * k))
      have hB : A * g.natDegree ≤ B := by
        have hmem : g.natDegree ∈ g.support := by
          have hne : g.coeff g.natDegree ≠ 0 := by
            intro h0
            have hlead0 : g.leadingCoeff = 0 := by
              simpa [Polynomial.coeff_natDegree (p := g)] using h0
            exact (Polynomial.leadingCoeff_ne_zero.mpr hg0) hlead0
          exact Polynomial.mem_support_iff.mpr hne
        have hsup :
            (WithBot.some (g.natDegree * A + (g.coeff g.natDegree).natDegree)) ≤
              weight_Λ_over_𝒪 β D := by
          simpa [weight_Λ_over_𝒪, weight_Λ, g, A] using
            (Finset.le_sup (s := g.support)
              (f := fun deg =>
                (WithBot.some <| deg * A + (g.coeff deg).natDegree)) hmem)
        have hsup' :
            (WithBot.some (g.natDegree * A + (g.coeff g.natDegree).natDegree)) ≤
              (WithBot.some B) := by
          simpa [hW] using hsup
        have hle : g.natDegree * A + (g.coeff g.natDegree).natDegree ≤ B := by
          exact (WithBot.coe_le_coe.1 hsup')
        have h1 : g.natDegree * A ≤ g.natDegree * A + (g.coeff g.natDegree).natDegree :=
          Nat.le_add_right _ _
        have hle' : g.natDegree * A ≤ B := h1.trans hle
        simpa [Nat.mul_comm] using hle'
      have hdeg_res :
          (resultantY (H_tilde' H) g).natDegree ≤ (H_tilde' H).natDegree * B := by
        exact natDegree_resultantY_le_weight (A := A) (B := B) (f := H_tilde' H) (g := g)
          (hB := hB) (hf := hcoeff_H) (hg := hcoeff_bound)
      have hcard' : (S_β (H := H) β).ncard > B * H.natDegree := by
        have hcard' :
            ((S_β (H := H) β).ncard : WithBot ℕ) >
              (B : WithBot ℕ) * (H.natDegree : WithBot ℕ) := by
          simpa [hW] using S_β_card
        have hcard'' :
            ((S_β (H := H) β).ncard : WithBot ℕ) >
              (B * H.natDegree : ℕ) := by
          simpa using hcard'
        exact (WithBot.coe_lt_coe.1 hcard'')
      have hpos : 0 < (S_β (H := H) β).ncard :=
        lt_of_le_of_lt (Nat.zero_le _) hcard'
      have hfinite : (S_β (H := H) β).Finite :=
        Set.finite_of_ncard_pos hpos
      let s : Finset F := hfinite.toFinset
      have hs : ∀ z ∈ s,
          (resultantY (H_tilde' H) g).eval z = 0 := by
        intro z hz
        have hz' : z ∈ S_β (H := H) β := by
          simpa [s] using hz
        have hres := resultantY_eval_eq_zero_of_Sβ (H := H) (β := β) hz'
        simpa using hres
      have hdeg_le : (resultantY (H_tilde' H) g).natDegree ≤ B * H.natDegree := by
        simpa [hdeg_tilde, Nat.mul_comm] using hdeg_res
      have hdeg_lt : (resultantY (H_tilde' H) g).natDegree < s.card := by
        have hs_card :
            s.card = (S_β (H := H) β).ncard := by
          simpa [s] using
            (Set.ncard_eq_toFinset_card (s := S_β (H := H) β) (hs := hfinite)).symm
        have hlt : B * H.natDegree < (S_β (H := H) β).ncard := hcard'
        exact lt_of_le_of_lt hdeg_le (by simpa [hs_card] using hlt)
      have hres_zero :
          resultantY (H_tilde' H) g = 0 :=
        eq_zero_of_card_lt_roots (p := resultantY (H_tilde' H) g) (s := s) hs hdeg_lt
      have hres_nonzero : resultantY (H_tilde' H) g ≠ 0 := by
        by_cases hgdeg : g.natDegree = 0
        · have hgC : g = Polynomial.C (g.coeff 0) := by
            exact Polynomial.eq_C_of_natDegree_eq_zero hgdeg
          have hcoeff0 : g.coeff 0 ≠ 0 := by
            intro h0
            apply hg0
            calc
              g = Polynomial.C (g.coeff 0) := hgC
              _ = Polynomial.C 0 := by rw [h0]
              _ = 0 := by simp
          have hres' :
              resultantY (H_tilde' H) g = (g.coeff 0) ^ (H_tilde' H).natDegree := by
            rw [hgC, resultantY_def]
            simpa using
              (Polynomial.resultant_C_right (f := H_tilde' H) (a := g.coeff 0)
                (m := (H_tilde' H).natDegree))
          have : (g.coeff 0) ^ (H_tilde' H).natDegree ≠ (0 : F[X]) := by
            exact pow_ne_zero _ hcoeff0
          simpa [hres'] using this
        · intro hres
          have hgpos : 0 < g.natDegree := Nat.pos_of_ne_zero hgdeg
          have hfpos : 0 < (H_tilde' H).natDegree := by
            simpa [hdeg_tilde] using (Fact.out : 0 < H.natDegree)
          rcases exists_bezout_of_resultant_eq_zero
              (f := H_tilde' H) (g := g) (hf := hfpos) (hg := hgpos)
              (hres := by simpa [resultantY] using hres) with
            ⟨p, q, hpdeg, hqdeg, hbez, hpq⟩
          have hmul : (H_tilde' H) ∣ g * p := by
            have hgp : g * p = -(H_tilde' H * q) :=
              eq_neg_of_add_eq_zero_right hbez
            have : g * p = (H_tilde' H) * (-q) := by
              calc
                g * p = -(H_tilde' H * q) := hgp
                _ = (H_tilde' H) * (-q) := by
                  exact (mul_neg (H_tilde' H) q).symm
            exact ⟨-q, by simpa [this, mul_comm, mul_left_comm, mul_assoc]⟩
          have hdiv : (H_tilde' H) ∣ g ∨ (H_tilde' H) ∣ p := hprime.dvd_or_dvd hmul
          have hdeg_g : g.natDegree < (H_tilde' H).natDegree := by
            have hmonic : Polynomial.Monic (H_tilde' H) := H_tilde'_monic (H := H)
            have hne1 : (H_tilde' H) ≠ 1 := by
              intro h1
              have : (H_tilde' H).natDegree = 0 := by
                simpa [h1] using (Polynomial.natDegree_one (R := F[X]))
              have hpos : 0 < (H_tilde' H).natDegree := by
                simpa [hdeg_tilde] using (Fact.out : 0 < H.natDegree)
              exact (ne_of_gt hpos) this
            simpa [g, canonicalRepOf𝒪] using
              (Polynomial.natDegree_modByMonic_lt (p := β.out) (hmq := hmonic) (hq := hne1))
          have hnot_g : ¬ (H_tilde' H) ∣ g := by
            intro hdivg
            have hle : (H_tilde' H).natDegree ≤ g.natDegree :=
              Polynomial.natDegree_le_of_dvd hdivg hg0
            exact (not_lt_of_ge hle hdeg_g)
          have hnot_p : ¬ (H_tilde' H) ∣ p := by
            intro hdivp
            have hp0 : p ≠ 0 := by
              intro hp0
              have hq0 : q = 0 := by
                have : (H_tilde' H) * q = 0 := by
                  simpa [hp0] using hbez
                exact (mul_eq_zero.mp this).resolve_left hprime.ne_zero
              cases hpq with
              | inl hp => exact hp hp0
              | inr hq => exact hq hq0
            have hle : (H_tilde' H).natDegree ≤ p.natDegree :=
              Polynomial.natDegree_le_of_dvd hdivp hp0
            exact (not_lt_of_ge hle hpdeg)
          cases hdiv with
          | inl hdivg => exact (hnot_g hdivg).elim
          | inr hdivp => exact (hnot_p hdivp).elim
      exact (hres_nonzero hres_zero).elim
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

local instance (H : F[X][Y]) [Fact (H.natDegree ≠ 0)] : Fact (0 < H.natDegree) :=
  ⟨Nat.pos_of_ne_zero (Fact.out)⟩

/-- The definition of `ζ` given in Appendix A.4 of [BCIKS20]. -/
noncomputable def ζ (R : F[X][X][Y]) (x₀ : F) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (H.natDegree ≠ 0)] :
    𝕃 H :=
  let W  : 𝕃 H := liftToFunctionField (H.leadingCoeff);
  let T : 𝕃 H := Ideal.Quotient.mk (Ideal.span {H_tilde H}) Polynomial.X;
    Polynomial.eval₂ liftToFunctionField (T / W)
      (Bivariate.evalX (Polynomial.C x₀) R.derivative)

set_option maxHeartbeats 400000 in
/-- There exist regular elements `ξ = W(Z)^(d-2) * ζ` as defined in Claim A.2 of Appendix A.4
of [BCIKS20]. -/
lemma ξ_regular (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [H_irreducible : Fact (Irreducible H)] [H_natDegree_pos : Fact (H.natDegree ≠ 0)]
    (hdeg : (Bivariate.evalX (Polynomial.C x₀) R.derivative).natDegree ≤ R.natDegree - 2) :
  ∃ pre : 𝒪 H,
    let d := R.natDegree
    let W : 𝕃 H := liftToFunctionField (H.leadingCoeff);
    embeddingOf𝒪Into𝕃 _ pre = W ^ (d - 2) * ζ R x₀ H := by
  classical
  -- abbreviations
  set P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative
  set d : ℕ := R.natDegree
  set s : F[X] := H.leadingCoeff
  set W : 𝕃 H := liftToFunctionField (H := H) s
  set T : 𝕃 H := Ideal.Quotient.mk (Ideal.span {H_tilde H}) Polynomial.X
  set k : ℕ := d - 2 - P.natDegree
  -- helper: `W` is nonzero
  have hH0 : H ≠ 0 := by
    intro h
    simpa [h] using (Fact.out : H.natDegree ≠ 0)
  have hlead : s ≠ 0 := by
    simpa [s] using (Polynomial.leadingCoeff_ne_zero.mpr hH0)
  have hHtilde_ne0 : H_tilde H ≠ 0 := by
    -- `H_tilde` is monic, hence nonzero
    have hmonic : Polynomial.Monic (H_tilde H) := by
      -- `H_tilde` is the image of the monic `H_tilde'`
      have hmonic' : Polynomial.Monic (H_tilde' H) := H_tilde'_monic (H := H)
      -- mapping preserves monicity
      simpa [H_tilde_equiv_H_tilde' (H := H) (hdeg := (Fact.out : 0 < H.natDegree))] using
        (Polynomial.Monic.map (f := ToRatFunc.univPolyHom (F := F)) hmonic')
    exact hmonic.ne_zero
  have hW0 : (W : 𝕃 H) ≠ 0 := by
    intro hW0
    -- unwrap `liftToFunctionField`
    have hmem :
        coeffAsRatFunc (F := F) s ∈ Ideal.span ({H_tilde H} : Set (Polynomial (RatFunc F))) := by
      simpa [liftToFunctionField, W] using
        (Ideal.Quotient.eq_zero_iff_mem).1 hW0
    -- `coeffAsRatFunc s` is constant in `Y`
    rcases (Ideal.mem_span_singleton).1 hmem with ⟨q, hq⟩
    have hconst_ne0 :
        (coeffAsRatFunc (F := F) s) ≠ 0 := by
      intro hconst
      have hs :
          (ToRatFunc.univPolyHom (F := F) s) = 0 := by
        -- rewrite the constant polynomial
        have hC :
            (Polynomial.C (ToRatFunc.univPolyHom (F := F) s) :
                Polynomial (RatFunc F)) = 0 := by
          simpa [coeffAsRatFunc, ToRatFunc.bivPolyHom] using hconst
        simpa using (Polynomial.C_eq_zero.mp hC)
      have hinj :
          Function.Injective (ToRatFunc.univPolyHom (F := F)) := by
        simpa [ToRatFunc.univPolyHom] using (RatFunc.algebraMap_injective (K := F))
      have hs' :
          ToRatFunc.univPolyHom (F := F) s = ToRatFunc.univPolyHom (F := F) 0 := by
        simpa using hs
      exact hlead (hinj hs')
    -- degree argument
    have hdeg0 :
        (coeffAsRatFunc (F := F) s).natDegree = 0 := by
      simpa [coeffAsRatFunc, ToRatFunc.bivPolyHom] using
        (Polynomial.natDegree_C (by
          -- show the constant is nonzero
          simpa [coeffAsRatFunc] using hconst_ne0))
    have hdeg_pos : 0 < (H_tilde H).natDegree := by
      have hdeg_tilde' : (H_tilde' H).natDegree = H.natDegree := by
        classical
        have htail :
            (∑ x ∈ (List.range H.natDegree).toFinset,
                  Y ^ (H.natDegree - 1 - x) *
                    (Polynomial.C (H.coeff (H.natDegree - 1 - x)) *
                      Polynomial.C H.leadingCoeff ^ x)).degree
              < (H.natDegree : WithBot ℕ) :=
          H_tilde'_tail_degree_lt (H := H)
        have hXdeg :
            (Polynomial.X ^ H.natDegree : F[X][Y]).degree =
              (H.natDegree : WithBot ℕ) := by
          simpa using (Polynomial.degree_X_pow (R := F[X]) H.natDegree)
        have hlt :
            (∑ x ∈ (List.range H.natDegree).toFinset,
                  Y ^ (H.natDegree - 1 - x) *
                    (Polynomial.C (H.coeff (H.natDegree - 1 - x)) *
                      Polynomial.C H.leadingCoeff ^ x)).degree
              < (Polynomial.X ^ H.natDegree : F[X][Y]).degree := by
          simpa [hXdeg] using htail
        have hdeg :
            (H_tilde' H).degree = (Polynomial.X ^ H.natDegree : F[X][Y]).degree := by
          simpa [H_tilde'] using (Polynomial.degree_add_eq_left_of_degree_lt hlt)
        have hnat :
            (H_tilde' H).natDegree =
              (Polynomial.X ^ H.natDegree : F[X][Y]).natDegree :=
          Polynomial.natDegree_eq_of_degree_eq hdeg
        simpa [Polynomial.natDegree_X_pow] using hnat
      have hdeg_tilde :
          (H_tilde H).natDegree = H.natDegree := by
        -- `H_tilde` is the image of `H_tilde'`
        have hinj :
            Function.Injective (ToRatFunc.univPolyHom (F := F)) := by
          simpa [ToRatFunc.univPolyHom] using (RatFunc.algebraMap_injective (K := F))
        have hmap :
            (H_tilde H).natDegree = (H_tilde' H).natDegree := by
          simpa [H_tilde_equiv_H_tilde' (H := H) (hdeg := (Fact.out : 0 < H.natDegree))]
            using (Polynomial.natDegree_map_eq_of_injective (f := ToRatFunc.univPolyHom (F := F))
              (p := H_tilde' H) hinj)
        simpa [hdeg_tilde'] using hmap
      simpa [hdeg_tilde] using (Fact.out : 0 < H.natDegree)
    -- a constant cannot equal a nontrivial multiple of `H_tilde`
    by_cases hq0 : q = 0
    · have : (coeffAsRatFunc (F := F) s) = 0 := by simpa [hq0] using hq
      exact hconst_ne0 this
    · have hdeg_mul' :
          (H_tilde H * q).natDegree =
            (H_tilde H).natDegree + q.natDegree := by
          simpa using (Polynomial.natDegree_mul hHtilde_ne0 hq0)
      have hpos : 0 < (H_tilde H * q).natDegree := by
        have : 0 < (H_tilde H).natDegree + q.natDegree := by
          exact Nat.add_pos_left hdeg_pos _
        simpa [hdeg_mul'] using this
      have : 0 < (coeffAsRatFunc (F := F) s).natDegree := by
        simpa [hq] using hpos
      have hcontr : (0 : ℕ) < 0 := by simpa [hdeg0] using this
      exact (Nat.lt_irrefl _ hcontr).elim
  -- scale-roots identity
  have hscale :
      Polynomial.eval₂ liftToFunctionField (W * (T / W))
          (Polynomial.scaleRoots P s) =
        W ^ P.natDegree * Polynomial.eval₂ liftToFunctionField (T / W) P := by
    simpa [W, s] using
      (Polynomial.scaleRoots_eval₂_mul (p := P) (f := liftToFunctionField) (r := T / W) (s := s))
  have hscale' :
      Polynomial.eval₂ liftToFunctionField T (Polynomial.scaleRoots P s) =
        W ^ P.natDegree * ζ R x₀ H := by
    -- simplify `W * (T / W)` to `T`
    have hWT : W * (T / W) = T := by
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
        (mul_div_cancel_left₀ T hW0)
    -- rewrite and unfold `ζ`
    simpa [ζ, W, T, P, hWT] using hscale
  -- combine the extra power `k`
  have hk : P.natDegree + k = d - 2 := by
    unfold k
    exact Nat.add_sub_of_le hdeg
  refine ⟨Ideal.Quotient.mk (Ideal.span ({H_tilde' H} : Set F[X][Y]))
      (Polynomial.C (s ^ k) * Polynomial.scaleRoots P s), ?_⟩
  -- evaluate the embedding
  have hC :
      embeddingOf𝒪Into𝕃 (H := H)
          (Ideal.Quotient.mk (Ideal.span ({H_tilde' H} : Set F[X][Y]))
            (Polynomial.C (s ^ k))) =
        W ^ k := by
    simp [embeddingOf𝒪Into𝕃, Ideal.quotientMap_mk, liftToFunctionField, coeffAsRatFunc, W, s]
  have hS :
      embeddingOf𝒪Into𝕃 (H := H)
          (Ideal.Quotient.mk (Ideal.span ({H_tilde' H} : Set F[X][Y]))
            (Polynomial.scaleRoots P s)) =
        Polynomial.eval₂ liftToFunctionField T (Polynomial.scaleRoots P s) := by
    -- use hom_eval₂ with the coefficient embedding
    have hhom :=
      (hom_eval₂ (f := coeffAsRatFunc (F := F))
        (g := Ideal.Quotient.mk (Ideal.span {H_tilde H}))
        (p := Polynomial.scaleRoots P s) (x := Polynomial.X))
    have hbiv :
        Polynomial.eval₂ (coeffAsRatFunc (F := F)) Polynomial.X (Polynomial.scaleRoots P s) =
          bivPolyHom (Polynomial.scaleRoots P s) := by
      simpa using (eval₂_coeffAsRatFunc_X (F := F) (p := Polynomial.scaleRoots P s))
    -- unfold the embedding and rewrite via `hom_eval₂`
    simpa [embeddingOf𝒪Into𝕃, Ideal.quotientMap_mk, liftToFunctionField, T, hbiv] using hhom
  -- finish
  have hk' : k + P.natDegree = d - 2 := by
    simpa [Nat.add_comm] using hk
  calc
    embeddingOf𝒪Into𝕃 (H := H)
        (Ideal.Quotient.mk (Ideal.span ({H_tilde' H} : Set F[X][Y]))
          (Polynomial.C (s ^ k) * Polynomial.scaleRoots P s)) =
        (embeddingOf𝒪Into𝕃 (H := H)
            (Ideal.Quotient.mk (Ideal.span ({H_tilde' H} : Set F[X][Y]))
              (Polynomial.C (s ^ k)))) *
          (embeddingOf𝒪Into𝕃 (H := H)
            (Ideal.Quotient.mk (Ideal.span ({H_tilde' H} : Set F[X][Y]))
              (Polynomial.scaleRoots P s))) := by
        simp [embeddingOf𝒪Into𝕃, Ideal.quotientMap_mk, map_mul]
    _ = W ^ k * (Polynomial.eval₂ liftToFunctionField T (Polynomial.scaleRoots P s)) := by
        rw [hC, hS]
    _ = W ^ k * (W ^ P.natDegree * ζ R x₀ H) := by
        rw [hscale']
    _ = (W ^ k * W ^ P.natDegree) * ζ R x₀ H := by
        simp [mul_assoc]
    _ = W ^ (k + P.natDegree) * ζ R x₀ H := by
        simp [pow_add, mul_assoc, mul_left_comm, mul_comm]
    _ = W ^ (d - 2) * ζ R x₀ H := by
        simp [hk']

/-- The elements `ξ = W(Z)^(d-2) * ζ` as defined in Claim A.2 of Appendix A.4 of [BCIKS20]. -/
noncomputable def ξ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (H.natDegree ≠ 0)]
    (hdeg : (Bivariate.evalX (Polynomial.C x₀) R.derivative).natDegree ≤ R.natDegree - 2) :
    𝒪 H :=
  let P : F[X][Y] := Bivariate.evalX (Polynomial.C x₀) R.derivative
  let d : ℕ := R.natDegree
  let s : F[X] := H.leadingCoeff
  let k : ℕ := d - 2 - P.natDegree
  Ideal.Quotient.mk (Ideal.span ({H_tilde' H} : Set F[X][Y]))
    (Polynomial.C (s ^ k) * Polynomial.scaleRoots P s)

/-- The bound of the weight `Λ` of the elements `ζ` as stated in Claim A.2 of Appendix A.4
of [BCIKS20]. -/
lemma weight_ξ_bound (x₀ : F) {D : ℕ} (hD : D ≥ Bivariate.totalDegree H)
    (hdeg : (Bivariate.evalX (Polynomial.C x₀) R.derivative).natDegree ≤ R.natDegree - 2)
    (hdegY :
      (canonicalRepOf𝒪 (H := H) (ξ x₀ R H hdeg)).natDegree ≤ Bivariate.natDegreeY R - 1)
    (hcoeff :
      ∀ k,
        ((canonicalRepOf𝒪 (H := H) (ξ x₀ R H hdeg)).coeff k).natDegree ≤
          (D - Bivariate.natDegreeY H + 1) * ((Bivariate.natDegreeY R - 1) - k)) :
  weight_Λ_over_𝒪 (ξ x₀ R H hdeg) D ≤
    WithBot.some ((Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1)) := by
  classical
  -- abbreviations
  set A : ℕ := D + 1 - Bivariate.natDegreeY H
  have hA : A = D - Bivariate.natDegreeY H + 1 := by
    have hleY : Bivariate.natDegreeY H ≤ D := by
      -- totalDegree dominates natDegreeY
      have hdegY : Bivariate.natDegreeY H ≤ Bivariate.totalDegree H := by
        classical
        by_cases hH0 : H = 0
        · simp [Bivariate.natDegreeY, Bivariate.totalDegree, hH0]
        · have hne : H.coeff H.natDegree ≠ 0 := by
            intro h0
            have hlead0 : H.leadingCoeff = 0 := by
              simpa [Polynomial.coeff_natDegree (p := H)] using h0
            exact (Polynomial.leadingCoeff_ne_zero.mpr hH0) hlead0
          have hmem : H.natDegree ∈ H.support :=
            Polynomial.mem_support_iff.mpr hne
          have hsup :
              (H.coeff H.natDegree).natDegree + H.natDegree ≤ Bivariate.totalDegree H :=
            (Finset.le_sup (s := H.support)
              (f := fun m => (H.coeff m).natDegree + m) hmem)
          have hle : H.natDegree ≤ (H.coeff H.natDegree).natDegree + H.natDegree :=
            Nat.le_add_left _ _
          simpa [Bivariate.natDegreeY] using hle.trans hsup
      exact le_trans hdegY hD
    calc
      A = D + 1 - Bivariate.natDegreeY H := rfl
      _ = 1 + D - Bivariate.natDegreeY H := by ac_rfl
      _ = 1 + (D - Bivariate.natDegreeY H) := by
            simpa using (Nat.add_sub_assoc hleY 1)
      _ = D - Bivariate.natDegreeY H + 1 := by ac_rfl
  -- unpack the weight definition
  unfold weight_Λ_over_𝒪 weight_Λ
  refine Finset.sup_le ?_
  intro k hk
  have hkcoeff :
      ((canonicalRepOf𝒪 (H := H) (ξ x₀ R H hdeg)).coeff k).natDegree ≤
      A * ((Bivariate.natDegreeY R - 1) - k) := by
    simpa [hA, A, Nat.mul_comm] using hcoeff k
  have hk_le :
      k ≤ Bivariate.natDegreeY R - 1 := by
    have hne :
        (canonicalRepOf𝒪 (H := H) (ξ x₀ R H hdeg)).coeff k ≠ 0 := by
      exact Polynomial.mem_support_iff.mp hk
    have hknat :
        k ≤ (canonicalRepOf𝒪 (H := H) (ξ x₀ R H hdeg)).natDegree :=
      Polynomial.le_natDegree_of_ne_zero hne
    exact le_trans hknat hdegY
  -- combine the bounds
  have hsum :
      k * A + ((canonicalRepOf𝒪 (H := H) (ξ x₀ R H hdeg)).coeff k).natDegree ≤
        (Bivariate.natDegreeY R - 1) * A := by
    -- `a + b ≤ (a + c)` when `b ≤ c`
    have : k * A + ((canonicalRepOf𝒪 (H := H) (ξ x₀ R H hdeg)).coeff k).natDegree ≤
        k * A + A * ((Bivariate.natDegreeY R - 1) - k) := by
      exact Nat.add_le_add_left hkcoeff _
    have hmul :
        k * A + A * ((Bivariate.natDegreeY R - 1) - k) =
          (Bivariate.natDegreeY R - 1) * A := by
      have hsum' : k + ((Bivariate.natDegreeY R - 1) - k) = Bivariate.natDegreeY R - 1 :=
        Nat.add_sub_of_le hk_le
      calc
        k * A + A * ((Bivariate.natDegreeY R - 1) - k)
            = A * k + A * ((Bivariate.natDegreeY R - 1) - k) := by
                ac_rfl
        _ = A * (k + ((Bivariate.natDegreeY R - 1) - k)) := by
              simp [Nat.mul_add]
        _ = A * (Bivariate.natDegreeY R - 1) := by simp [hsum']
        _ = (Bivariate.natDegreeY R - 1) * A := by simp [Nat.mul_comm]
    simpa [hmul] using this
  have hsum' :
      k * A + ((canonicalRepOf𝒪 (H := H) (ξ x₀ R H hdeg)).coeff k).natDegree ≤
        (Bivariate.natDegreeY R - 1) * (D - Bivariate.natDegreeY H + 1) := by
    simpa [hA] using hsum
  exact (WithBot.coe_le_coe.2 hsum')

/-- The definition of the regular elements `β` giving the numerators of the Hensel lift coefficients
as defined in Claim A.2 of Appendix A.4 of [BCIKS20]. -/
noncomputable def β (R : F[X][X][Y]) (t : ℕ) : 𝒪 H :=
  (β_regular R H (D := Bivariate.totalDegree H) t).choose

/-- Closed-form expression for the coefficient `α_t` from Claim A.2 of Appendix A.4
of [BCIKS20]. -/
noncomputable def αClosedForm (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (H.natDegree ≠ 0)]
    (t : ℕ)
    (hdeg : (Bivariate.evalX (Polynomial.C x₀) R.derivative).natDegree ≤ R.natDegree - 2) :
    𝕃 H :=
  let W : 𝕃 H := liftToFunctionField (H.leadingCoeff)
  embeddingOf𝒪Into𝕃 _ (β R t) /
    (W ^ (t + 1) * (embeddingOf𝒪Into𝕃 _ (ξ x₀ R H hdeg)) ^ (2*t - 1))

/-- Recursive presentation of the Hensel-lift coefficients `α_t`.  This keeps the construction
coefficient-by-coefficient, while each step is identified with the closed form from Claim A.2. -/
noncomputable def α (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (H.natDegree ≠ 0)]
    (t : ℕ)
    (hdeg : (Bivariate.evalX (Polynomial.C x₀) R.derivative).natDegree ≤ R.natDegree - 2) :
    𝕃 H :=
  Nat.recOn t
    (αClosedForm x₀ R H 0 hdeg)
    (fun n _ => αClosedForm x₀ R H (n + 1) hdeg)

lemma α_eq_closedForm (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (H.natDegree ≠ 0)]
    (t : ℕ)
    (hdeg : (Bivariate.evalX (Polynomial.C x₀) R.derivative).natDegree ≤ R.natDegree - 2) :
    α x₀ R H t hdeg = αClosedForm x₀ R H t hdeg := by
  induction t with
  | zero =>
      simp [α, αClosedForm]
  | succ n ih =>
      simp [α, αClosedForm]

/-- The Hensel lift coefficients `α'` with bundled irreducibility witness. -/
noncomputable def α' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H) (t : ℕ)
    (hdeg : (Bivariate.evalX (Polynomial.C x₀) R.derivative).natDegree ≤ R.natDegree - 2) :
    𝕃 H :=
  α x₀ R _ (φ := ⟨H_irreducible⟩) t hdeg

/-- Truncated recursive Hensel-lift series in the local parameter (corresponding to `X - x₀`). -/
noncomputable def γTrunc (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (H.natDegree ≠ 0)]
    (hdeg : (Bivariate.evalX (Polynomial.C x₀) R.derivative).natDegree ≤ R.natDegree - 2) :
    ℕ → PowerSeries (𝕃 H)
  | 0 => 0
  | n + 1 =>
      γTrunc x₀ R H hdeg n + PowerSeries.monomial (𝕃 H) n (α x₀ R H n hdeg)

lemma coeff_γTrunc_eq_zero_of_le (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (H.natDegree ≠ 0)]
    (hdeg : (Bivariate.evalX (Polynomial.C x₀) R.derivative).natDegree ≤ R.natDegree - 2)
    (n m : ℕ) (hmn : m ≤ n) :
    PowerSeries.coeff (𝕃 H) n (γTrunc x₀ R H hdeg m) = 0 := by
  induction m with
  | zero =>
      simp [γTrunc]
  | succ m ih =>
      have hmle : m ≤ n := Nat.le_trans (Nat.le_succ m) hmn
      have hmne : n ≠ m := by
        exact Nat.ne_of_gt (lt_of_lt_of_le (Nat.lt_succ_self m) hmn)
      simp [γTrunc, ih hmle, PowerSeries.coeff_monomial, hmne]

lemma coeff_γTrunc_succ_self (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (H.natDegree ≠ 0)]
    (hdeg : (Bivariate.evalX (Polynomial.C x₀) R.derivative).natDegree ≤ R.natDegree - 2)
    (n : ℕ) :
    PowerSeries.coeff (𝕃 H) n (γTrunc x₀ R H hdeg (n + 1)) = α x₀ R H n hdeg := by
  simp [γTrunc, coeff_γTrunc_eq_zero_of_le]

/-- The (infinite) recursive Hensel-lift series obtained from the truncations `γTrunc`. -/
noncomputable def γ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (H.natDegree ≠ 0)]
    (hdeg : (Bivariate.evalX (Polynomial.C x₀) R.derivative).natDegree ≤ R.natDegree - 2) :
    PowerSeries (𝕃 H) :=
  PowerSeries.mk (fun n => PowerSeries.coeff (𝕃 H) n (γTrunc x₀ R H hdeg (n + 1)))

lemma coeff_γ (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (H.natDegree ≠ 0)]
    (hdeg : (Bivariate.evalX (Polynomial.C x₀) R.derivative).natDegree ≤ R.natDegree - 2)
    (n : ℕ) :
    PowerSeries.coeff (𝕃 H) n (γ x₀ R H hdeg) = α x₀ R H n hdeg := by
  simp [γ, coeff_γTrunc_succ_self]

lemma γ_eq_mk_alpha (x₀ : F) (R : F[X][X][Y]) (H : F[X][Y])
    [φ : Fact (Irreducible H)] [H_natDegree_pos : Fact (H.natDegree ≠ 0)]
    (hdeg : (Bivariate.evalX (Polynomial.C x₀) R.derivative).natDegree ≤ R.natDegree - 2) :
    γ x₀ R H hdeg = PowerSeries.mk (fun n => α x₀ R H n hdeg) := by
  ext n
  simp [coeff_γ (x₀ := x₀) (R := R) (H := H) (hdeg := hdeg) n]

/-- The power series `γ'` with bundled irreducibility witness. -/
noncomputable def γ' (x₀ : F) (R : F[X][X][Y]) (H_irreducible : Irreducible H)
    (hdeg : (Bivariate.evalX (Polynomial.C x₀) R.derivative).natDegree ≤ R.natDegree - 2) :
    PowerSeries (𝕃 H) :=
  γ x₀ R H (φ := ⟨H_irreducible⟩) hdeg

end ClaimA2
end BCIKS20AppendixA
