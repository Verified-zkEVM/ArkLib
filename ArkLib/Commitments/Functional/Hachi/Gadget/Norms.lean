/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.Gadget.Core
import ArkLib.Data.Lattices.CyclotomicRing.NormBounds

/-!
# Centered Norm Bounds for the Gadget Decomposition `G⁻¹` and Recomposition `G·ẑ`

Centered `ℓ₂²` and `ℓ∞` norm bounds for both directions of the base-`b` gadget algebra over
`ZMod q`: the gadget matrix `G` packs the powers `1, b, …, b^(digits-1)`, so `G⁻¹` rewrites a
vector over `Rq Φ` in base-`b` digits and `G` recombines it. "Centered" means every coefficient
is measured through its representative in `(-q/2, q/2]` — the shortness measure of the lattice
commitment.

**Part I — decomposition (honest case).** Shortness of the gadget inverse `gadgetDecompose`
when instantiated with the genuine base-`b` digit decomposition `zmodDigitDecomposition`. These
are the honest-case norm bounds the inner-outer Ajtai commitment needs for perfect correctness
(`InnerOuter.Correctness.perfectlyCorrect`). The single analytic input is `zmodDigit_natAbs_le`:
each base-`b` digit, as a centered residue, has absolute value `≤ b - 1` (under `b - 1 ≤ q/2`,
so the residue does not wrap). Everything else is bookkeeping over the gadget's coefficient
layout (`Rq.ofFinCoeff_coeff`).

**Part II — recomposition (adversarial case).** Multiplying by the gadget matrix (`gadgetMul`)
grows norms controllably for **any** `ℓ∞`-range-bounded input — in particular an adversarial
`ẑ` that merely passed the verifier's range check (Eq. (20) of [NOZ26]), not an honest digit
decomposition. The analytic input is `valMinAbs_natAbs_le`: the centered representative of a
residue is minimal among all its integer representatives, so wraparound of the `ZMod q` powers
`bᵘ` is immaterial. The resulting subtraction bound has exactly the `βSq = 4·B_z` shape that
the extractor's `VerifiedBlock.scaled_short` obligation consumes in Lemma 8
(`QuadEval.Soundness`).

This file bridges the gadget algebra (`Hachi.Gadget.Core`) and the centered norms
(`Data.Lattices.CyclotomicRing.NormBounds`). The Hachi-reduction-specific norm constants
`B_z` / `βSq` that these bounds feed live with Lemma 8 in `QuadEval.Soundness`, not here.

## Main results

* `gadgetDecompose_vecLInftyNorm_le_of_digit_le`: an arbitrary `DigitDecomposition` whose digits
  are centered-bounded by `γ` produces a decomposition with `‖·‖∞ ≤ γ` — the form honest-prover
  (completeness) proofs need, and the source of the concrete bound below.
* `gadgetDecompose_zmod_vecLInftyNorm_le` / `gadgetDecompose_zmod_vecL2NormSq_le`: the honest
  decomposition satisfies `‖·‖∞ ≤ b - 1` and `‖·‖₂² ≤ (rows·digits)·(deg φ)·(b-1)²`.
* `gadgetMul_zmod_vecLInftyNorm_le` / `gadgetMul_zmod_vecL2NormSq_le`: if `‖v‖∞ ≤ γ` then
  `‖G ·ᵥ v‖∞ ≤ (∑_{u<digits} bᵘ) · γ`, hence `‖G ·ᵥ v‖₂²` is within `zRecomposeL2SqBound`.
* `gadgetMul_zmod_sub_l2NormSq_le`: two range-checked recompositions differ in `ℓ₂²` by at most
  `subL2NormSqBound (zRecomposeL2SqBound …)` — the `4·B_z` bound Lemma 8 needs.
* `boundedBalancedZmodDigit_valMinAbs_mem` / `boundedBalancedZmodDigit_natAbs_le`: the
  **short-input** balanced digits (`Gadget/Core.lean`) land in the same box `S_b` / ball `⌊b/2⌋`,
  for every input and with no `q ≤ b ^ digits` hypothesis.
* `boundedGadgetDecompose_gadgetMul_eq_of_vecLInftyNorm_le`: the bounded gadget inverse round-trips
  under `G` on every `ℓ∞`-short input — the honest `z = J·ẑ` step at `τ` chosen from the honest
  bound on `z`.

## References

* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus

namespace ArkLib.Lattices.Ajtai

section ZModGadgetNorms

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]

omit [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- **Core digit bound.** Each base-`b` digit of `zmodDigitDecomposition`, viewed as a centered
residue, has absolute value at most `b - 1` — provided `b - 1 ≤ q/2`, so the digit (a natural
number `< b`) does not wrap to a negative centered representative. -/
theorem zmodDigit_natAbs_le {b digits : ℕ} (hb : 1 < b) (hq : q ≤ b ^ digits)
    (hbq : b - 1 ≤ q / 2) (c : ZMod q) (e : Fin digits) :
    ((zmodDigitDecomposition b digits hb hq).digit c e).valMinAbs.natAbs ≤ b - 1 := by
  simp only [zmodDigitDecomposition]
  set d := (Nat.digits b c.val).getD (e : ℕ) 0 with hd
  have hdb : d < b := by
    rcases lt_or_ge (e : ℕ) (Nat.digits b c.val).length with hlt | hge
    · rw [hd, List.getD_eq_getElem _ _ hlt]
      exact Nat.digits_lt_base hb (List.getElem_mem _)
    · rw [hd, List.getD_eq_default _ _ hge]; omega
  rw [ZMod.valMinAbs_natCast_of_le_half (by omega : d ≤ q / 2)]
  simp only [Int.natAbs_natCast]
  omega

omit [NeZero q] in
/-- The `k`-th coefficient (`k < deg φ`) of a `gadgetDecomposeFun` block is exactly the
corresponding digit of the corresponding input coefficient. All the range bookkeeping below is a
consequence of this one identity, and it holds at the level of the *bare* digit map, so the full
(`DigitDecomposition`) and bounded (`BoundedDigitDecomposition`) decompositions share it. -/
theorem gadgetDecomposeFun_coeff {rows digits : ℕ} (digit : ZMod q → Fin digits → ZMod q)
    (x : PolyVec (Rq Φ) rows) (j : Fin (rows * digits)) {k : ℕ} (hk : k < Φ.φ.natDegree) :
    (gadgetDecomposeFun Φ digit x j).1.coeff k =
      digit ((x (finProdFinEquiv.symm j).1).1.coeff k) (finProdFinEquiv.symm j).2 := by
  rw [show gadgetDecomposeFun Φ digit x j =
      Rq.ofFinCoeff Φ Φ.φ.natDegree (fun k =>
        digit ((x (finProdFinEquiv.symm j).1).1.coeff k) (finProdFinEquiv.symm j).2) from rfl,
    Rq.ofFinCoeff_coeff Φ _ (Rq.phi_natDegree_le_degree Φ) k, if_pos hk]

omit [NeZero q] in
/-- The `k`-th coefficient (`k < deg φ`) of a gadget-decomposition block is exactly the
corresponding digit of the corresponding input coefficient. -/
theorem gadgetDecompose_coeff {base : ZMod q} {rows digits : ℕ}
    (dd : DigitDecomposition base digits) (x : PolyVec (Rq Φ) rows) (j : Fin (rows * digits))
    {k : ℕ} (hk : k < Φ.φ.natDegree) :
    (gadgetDecompose Φ dd x j).1.coeff k =
      dd.digit ((x (finProdFinEquiv.symm j).1).1.coeff k) (finProdFinEquiv.symm j).2 :=
  gadgetDecomposeFun_coeff Φ dd.digit x j hk

omit [NeZero q] in
/-- The bounded counterpart of `gadgetDecompose_coeff`: same identity, over a
`BoundedDigitDecomposition`'s digit map. -/
theorem boundedGadgetDecompose_coeff {base : ZMod q} {rows digits bound : ℕ}
    (bdd : BoundedDigitDecomposition base digits bound) (x : PolyVec (Rq Φ) rows)
    (j : Fin (rows * digits)) {k : ℕ} (hk : k < Φ.φ.natDegree) :
    (bdd.gadgetDecompose Φ x j).1.coeff k =
      bdd.digit ((x (finProdFinEquiv.symm j).1).1.coeff k) (finProdFinEquiv.symm j).2 :=
  gadgetDecomposeFun_coeff Φ bdd.digit x j hk

omit [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- **Core balanced-digit bound.** Each digit of `balancedZmodDigitDecomposition`, as a centered
residue, lies in the two-sided box `[−⌊b/2⌋, ⌈b/2⌉−1]` — i.e. `[-(b/2), (b+1)/2 - 1]` in `Nat`
division. This is the paper's balanced-digit box `S_b` ([NOZ26] §2.1) on the nose, for both
parities of `b`, and it is a genuinely two-sided statement: unlike `zmodDigit_natAbs_le` it is not
a symmetric `ℓ∞` ball but the exact interval Eq. (20)'s range check tests.

The digit is `u − ⌊b/2⌋` for an unsigned base-`b` digit `u < b`, so as an *integer* it lies in
`[−⌊b/2⌋, b−1−⌊b/2⌋]`, and `b − 1 − b/2 = (b+1)/2 − 1` for both parities. The hypothesis
`b ≤ q/2` (slightly stronger than `zmodDigit_natAbs_le`'s `b − 1 ≤ q/2`) is the anti-wraparound
condition that makes that integer *be* the centered representative, via `ZMod.valMinAbs_spec`. -/
theorem balancedZmodDigit_valMinAbs_mem {b digits : ℕ} (hb : 1 < b) (hq : q ≤ b ^ digits)
    (hbq : b ≤ q / 2) (c : ZMod q) (e : Fin digits) :
    -((b / 2 : ℕ) : ℤ) ≤
        ((balancedZmodDigitDecomposition b digits hb hq).digit c e).valMinAbs ∧
      ((balancedZmodDigitDecomposition b digits hb hq).digit c e).valMinAbs
        ≤ (((b + 1) / 2 : ℕ) : ℤ) - 1 := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  simp only [balancedZmodDigitDecomposition, zmodDigitDecomposition]
  set u := (Nat.digits b (c + balancedShift b digits).val).getD (e : ℕ) 0 with hu
  -- The unsigned digit is `< b` (out-of-range positions are `0`).
  have hub : u < b := by
    rcases lt_or_ge (e : ℕ) (Nat.digits b (c + balancedShift b digits).val).length with hlt | hge
    · rw [hu, List.getD_eq_getElem _ _ hlt]
      exact Nat.digits_lt_base hb (List.getElem_mem _)
    · rw [hu, List.getD_eq_default _ _ hge]; omega
  -- `u − ⌊b/2⌋` is small enough not to wrap, so it *is* the centered representative.
  have hval : ((u : ZMod q) - ((b / 2 : ℕ) : ZMod q)).valMinAbs = (u : ℤ) - ((b / 2 : ℕ) : ℤ) := by
    refine (ZMod.valMinAbs_spec _ _).mpr ⟨?_, ?_⟩
    · -- `push_cast` would turn `((b / 2 : ℕ) : ℤ)` into an `ℤ`-division; rewrite the casts by hand.
      simp only [Int.cast_sub, Int.cast_natCast]
    · rw [Set.mem_Ioc]
      omega
  rw [hval]
  omega

omit [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- **Ball form of the balanced-digit bound**: every balanced digit has centered absolute value at
most `⌊b/2⌋` — the box `[−⌊b/2⌋, ⌈b/2⌉−1]` is contained in the symmetric ball of radius `⌊b/2⌋`
(check both parities: `(b+1)/2 − 1 ≤ b/2` always). This is the form the `ℓ∞`/`ℓ₂²` gadget bounds
consume, so the balanced decomposition is short in the ordinary sense too, at half the radius of the
unsigned one. -/
theorem balancedZmodDigit_natAbs_le {b digits : ℕ} (hb : 1 < b) (hq : q ≤ b ^ digits)
    (hbq : b ≤ q / 2) (c : ZMod q) (e : Fin digits) :
    ((balancedZmodDigitDecomposition b digits hb hq).digit c e).valMinAbs.natAbs ≤ b / 2 := by
  obtain ⟨hlo, hhi⟩ := balancedZmodDigit_valMinAbs_mem hb hq hbq c e
  omega

/-! ### The bounded balanced digits: same range, no `q ≤ b ^ digits`

`boundedBalancedZmodDigit` is the short-input decomposition Hachi's folded witness `z` uses
(`Gadget/Core.lean`). Its digits are `u − ⌊b/2⌋` for an ordinary base-`b` digit `u < b` of a
*nonnegative* integer, exactly as in the full-width balanced case — so the range statements are
identical, hold for **every** input (shortness buys the reconstruction law, not the range), and
crucially require no `q ≤ b ^ digits`. -/

omit [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- **The bounded balanced digits lie in the paper's box `S_b`** — `[−⌊b/2⌋, ⌈b/2⌉−1]` ([NOZ26]
§2.1), for every input and with no `q ≤ b ^ digits` hypothesis. Same mechanism as
`balancedZmodDigit_valMinAbs_mem`: the digit is `u − ⌊b/2⌋` for an unsigned base-`b` digit `u < b`,
and `b ≤ q/2` is the anti-wraparound condition making that integer *be* the centered
representative. -/
theorem boundedBalancedZmodDigit_valMinAbs_mem {b digits : ℕ} (hb : 1 < b) (hbq : b ≤ q / 2)
    (x : ZMod q) (e : Fin digits) :
    -((b / 2 : ℕ) : ℤ) ≤ (boundedBalancedZmodDigit b digits x e).valMinAbs ∧
      (boundedBalancedZmodDigit b digits x e).valMinAbs
        ≤ (((b + 1) / 2 : ℕ) : ℤ) - 1 := by
  have hq0 : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  simp only [boundedBalancedZmodDigit]
  set n : ℕ :=
    (x.valMinAbs + ((b / 2 : ℕ) : ℤ) * (digitOnesValue b digits : ℤ)).toNat with hn
  set u := (Nat.digits b n).getD (e : ℕ) 0 with hu
  have hub : u < b := by
    rcases lt_or_ge (e : ℕ) (Nat.digits b n).length with hlt | hge
    · rw [hu, List.getD_eq_getElem _ _ hlt]
      exact Nat.digits_lt_base hb (List.getElem_mem _)
    · rw [hu, List.getD_eq_default _ _ hge]; omega
  have hval : ((u : ZMod q) - ((b / 2 : ℕ) : ZMod q)).valMinAbs
      = (u : ℤ) - ((b / 2 : ℕ) : ℤ) := by
    refine (ZMod.valMinAbs_spec _ _).mpr ⟨?_, ?_⟩
    · simp only [Int.cast_sub, Int.cast_natCast]
    · rw [Set.mem_Ioc]
      omega
  rw [hval]
  omega

omit [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- **Ball form of the bounded balanced-digit bound**: every digit has centered absolute value at
most `⌊b/2⌋` — the form Eq. (20)'s relaxed `c6` ball check consumes. -/
theorem boundedBalancedZmodDigit_natAbs_le {b digits : ℕ} (hb : 1 < b) (hbq : b ≤ q / 2)
    (x : ZMod q) (e : Fin digits) :
    (boundedBalancedZmodDigit b digits x e).valMinAbs.natAbs ≤ b / 2 := by
  obtain ⟨hlo, hhi⟩ := boundedBalancedZmodDigit_valMinAbs_mem hb hbq x e
  omega

omit [NeZero q] in
/-- **The conditional gadget round-trip in `ℓ∞` form** `G · G⁻¹(x) = x`: the bounded gadget inverse
is inverted by `G` on every input within the decomposition's bound. This is the honest
`z = J · ẑ` reconstruction (Hachi Eq. (20) rows c4/c5) at a digit count `τ` set by the honest
shortness bound on `z` rather than by `q` — the whole point of the bounded abstraction. -/
theorem boundedGadgetDecompose_gadgetMul_eq_of_vecLInftyNorm_le {base : ZMod q}
    {digits bound rows : ℕ} (hd : 0 < digits) (h1 : 1 ≤ Φ.φ.natDegree)
    (bdd : BoundedDigitDecomposition base digits bound) (x : PolyVec (Rq Φ) rows)
    (hx : vecLInftyNorm Φ x ≤ bound) :
    gadgetMul Φ base (bdd.gadgetDecompose Φ x) = x :=
  boundedGadgetDecompose_gadgetMul_eq Φ hd h1 bdd x
    (fun i _k hk => Rq.valMinAbs_natAbs_coeff_le_of_vecLInftyNorm_le Φ hx i hk)

/-! ## `ℓ∞` bound -/

omit [NeZero q] in
/-- **`ℓ∞` shortness of `G⁻¹` from a digit bound, for a bare digit map.** Every block of the
decomposition inherits whatever centered bound `γ` the digit map satisfies, because
`gadgetDecomposeFun_coeff` identifies each coefficient of the output with a single digit of a
single input coefficient. Shared by the full and the bounded decomposition. -/
theorem gadgetDecomposeFun_lInftyNorm_le_of_digit_le {digits rows γ : ℕ}
    (digit : ZMod q → Fin digits → ZMod q)
    (hdd : ∀ (c : ZMod q) (e : Fin digits), (digit c e).valMinAbs.natAbs ≤ γ)
    (x : PolyVec (Rq Φ) rows) (j : Fin (rows * digits)) :
    Rq.lInftyNorm Φ (gadgetDecomposeFun Φ digit x j) ≤ γ := by
  unfold Rq.lInftyNorm
  refine Finset.sup_le (fun k hk => ?_)
  rw [gadgetDecomposeFun_coeff Φ _ x j (Finset.mem_range.mp hk)]
  exact hdd _ _

omit [NeZero q] in
/-- **`ℓ∞` shortness of `G⁻¹` from a digit bound, for an arbitrary `DigitDecomposition`.** The
form completeness proofs need, since they are stated for whichever decomposition the honest prover
was instantiated with. -/
theorem gadgetDecompose_lInftyNorm_le_of_digit_le {base : ZMod q} {digits rows γ : ℕ}
    (dd : DigitDecomposition base digits)
    (hdd : ∀ (c : ZMod q) (e : Fin digits), (dd.digit c e).valMinAbs.natAbs ≤ γ)
    (x : PolyVec (Rq Φ) rows) (j : Fin (rows * digits)) :
    Rq.lInftyNorm Φ (gadgetDecompose Φ dd x j) ≤ γ :=
  gadgetDecomposeFun_lInftyNorm_le_of_digit_le Φ dd.digit hdd x j

omit [NeZero q] in
/-- **Two-sided (box) form of the same bookkeeping**: if every digit of `dd` has its centered
representative in the interval `[lo, hi]`, so does every coefficient of the gadget decomposition.

The `ℓ∞` lemmas above give a symmetric ball; Hachi's exact Eq. (20) range check is the asymmetric
box `S_b`, so the honest side of `paperRelOut` needs this form. Same one-line mechanism
(`gadgetDecompose_coeff`): each output coefficient *is* a digit of an input coefficient. -/
theorem gadgetDecomposeFun_coeff_valMinAbs_mem_of_digit_mem {digits rows : ℕ}
    {lo hi : ℤ} (digit : ZMod q → Fin digits → ZMod q)
    (hdd : ∀ (c : ZMod q) (e : Fin digits),
      lo ≤ (digit c e).valMinAbs ∧ (digit c e).valMinAbs ≤ hi)
    (x : PolyVec (Rq Φ) rows) (j : Fin (rows * digits)) {k : ℕ} (hk : k < Φ.φ.natDegree) :
    lo ≤ ((gadgetDecomposeFun Φ digit x j).1.coeff k).valMinAbs ∧
      ((gadgetDecomposeFun Φ digit x j).1.coeff k).valMinAbs ≤ hi := by
  rw [gadgetDecomposeFun_coeff Φ _ x j hk]
  exact hdd _ _

omit [NeZero q] in
/-- Box form for a `DigitDecomposition`, from the bare-digit-map version above. -/
theorem gadgetDecompose_coeff_valMinAbs_mem_of_digit_mem {base : ZMod q} {digits rows : ℕ}
    {lo hi : ℤ} (dd : DigitDecomposition base digits)
    (hdd : ∀ (c : ZMod q) (e : Fin digits),
      lo ≤ (dd.digit c e).valMinAbs ∧ (dd.digit c e).valMinAbs ≤ hi)
    (x : PolyVec (Rq Φ) rows) (j : Fin (rows * digits)) {k : ℕ} (hk : k < Φ.φ.natDegree) :
    lo ≤ ((gadgetDecompose Φ dd x j).1.coeff k).valMinAbs ∧
      ((gadgetDecompose Φ dd x j).1.coeff k).valMinAbs ≤ hi :=
  gadgetDecomposeFun_coeff_valMinAbs_mem_of_digit_mem Φ dd.digit hdd x j hk

omit [NeZero q] in
/-- Box form for a `BoundedDigitDecomposition` — the paper-exact `S_b` range check on the honest
`ẑ` at a `τ` chosen from the honest bound rather than from `q`. Note it is **unconditional**: what
shortness of the input buys is the reconstruction law, never the digit range. -/
theorem boundedGadgetDecompose_coeff_valMinAbs_mem_of_digit_mem {base : ZMod q}
    {digits rows bound : ℕ} {lo hi : ℤ} (bdd : BoundedDigitDecomposition base digits bound)
    (hdd : ∀ (c : ZMod q) (e : Fin digits),
      lo ≤ (bdd.digit c e).valMinAbs ∧ (bdd.digit c e).valMinAbs ≤ hi)
    (x : PolyVec (Rq Φ) rows) (j : Fin (rows * digits)) {k : ℕ} (hk : k < Φ.φ.natDegree) :
    lo ≤ ((bdd.gadgetDecompose Φ x j).1.coeff k).valMinAbs ∧
      ((bdd.gadgetDecompose Φ x j).1.coeff k).valMinAbs ≤ hi :=
  gadgetDecomposeFun_coeff_valMinAbs_mem_of_digit_mem Φ bdd.digit hdd x j hk

omit [NeZero q] in
/-- Vector form of `gadgetDecomposeFun_lInftyNorm_le_of_digit_le`. -/
theorem gadgetDecomposeFun_vecLInftyNorm_le_of_digit_le {digits rows γ : ℕ}
    (digit : ZMod q → Fin digits → ZMod q)
    (hdd : ∀ (c : ZMod q) (e : Fin digits), (digit c e).valMinAbs.natAbs ≤ γ)
    (x : PolyVec (Rq Φ) rows) :
    vecLInftyNorm Φ (gadgetDecomposeFun Φ digit x) ≤ γ := by
  unfold vecLInftyNorm
  exact Finset.sup_le
    (fun j _ => gadgetDecomposeFun_lInftyNorm_le_of_digit_le Φ digit hdd x j)

omit [NeZero q] in
/-- Vector form of `gadgetDecompose_lInftyNorm_le_of_digit_le`: the whole gadget decomposition is
`ℓ∞`-bounded by the decomposition's digit bound. -/
theorem gadgetDecompose_vecLInftyNorm_le_of_digit_le {base : ZMod q} {digits rows γ : ℕ}
    (dd : DigitDecomposition base digits)
    (hdd : ∀ (c : ZMod q) (e : Fin digits), (dd.digit c e).valMinAbs.natAbs ≤ γ)
    (x : PolyVec (Rq Φ) rows) :
    vecLInftyNorm Φ (gadgetDecompose Φ dd x) ≤ γ :=
  gadgetDecomposeFun_vecLInftyNorm_le_of_digit_le Φ dd.digit hdd x

omit [NeZero q] in
/-- Vector `ℓ∞` bound for a `BoundedDigitDecomposition` — the `c6` range check on the honest `ẑ`
in the ball-relaxed reading. Unconditional in the input, like its box counterpart. -/
theorem boundedGadgetDecompose_vecLInftyNorm_le_of_digit_le {base : ZMod q}
    {digits rows bound γ : ℕ} (bdd : BoundedDigitDecomposition base digits bound)
    (hdd : ∀ (c : ZMod q) (e : Fin digits), (bdd.digit c e).valMinAbs.natAbs ≤ γ)
    (x : PolyVec (Rq Φ) rows) :
    vecLInftyNorm Φ (bdd.gadgetDecompose Φ x) ≤ γ :=
  gadgetDecomposeFun_vecLInftyNorm_le_of_digit_le Φ bdd.digit hdd x

/-- **`ℓ∞` shortness of `G⁻¹`.** The full gadget decomposition has centered `ℓ∞` norm `≤ b - 1`. -/
theorem gadgetDecompose_zmod_vecLInftyNorm_le {b digits rows : ℕ} (hb : 1 < b) (hq : q ≤ b ^ digits)
    (hbq : b - 1 ≤ q / 2) (x : PolyVec (Rq Φ) rows) :
    vecLInftyNorm Φ (gadgetDecompose Φ (zmodDigitDecomposition b digits hb hq) x) ≤ b - 1 :=
  gadgetDecompose_vecLInftyNorm_le_of_digit_le Φ _ (zmodDigit_natAbs_le hb hq hbq) x

/-! ## `ℓ₂²` bound -/

/-- Each gadget-decomposition block is `ℓ₂²`-short: its centered squared-`ℓ₂` norm is at most
`(deg φ)·(b-1)²` (each of the `deg φ` coefficients contributes at most `(b-1)²`). -/
theorem gadgetDecompose_zmod_l2NormSq_le {b digits rows : ℕ} (hb : 1 < b) (hq : q ≤ b ^ digits)
    (hbq : b - 1 ≤ q / 2) (x : PolyVec (Rq Φ) rows)
    (j : Fin (rows * digits)) :
    ‖gadgetDecompose Φ (zmodDigitDecomposition b digits hb hq) x j‖₂² ≤
      Φ.φ.natDegree * (b - 1) ^ 2 := by
  unfold Rq.l2NormSq
  calc ∑ k ∈ Finset.range Φ.φ.natDegree,
        ((gadgetDecompose Φ (zmodDigitDecomposition b digits hb hq) x j).1.coeff k).valMinAbs.natAbs
          ^ 2
      ≤ ∑ _k ∈ Finset.range Φ.φ.natDegree, (b - 1) ^ 2 := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [gadgetDecompose_coeff Φ _ x j (Finset.mem_range.mp hk)]
        exact Nat.pow_le_pow_left (zmodDigit_natAbs_le hb hq hbq _ _) 2
    _ = Φ.φ.natDegree * (b - 1) ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

/-- **`ℓ₂²` shortness of `G⁻¹`.** The full gadget decomposition has centered squared-`ℓ₂` norm at
most `(rows·digits)·(deg φ)·(b-1)²`. -/
theorem gadgetDecompose_zmod_vecL2NormSq_le {b digits rows : ℕ} (hb : 1 < b) (hq : q ≤ b ^ digits)
    (hbq : b - 1 ≤ q / 2) (x : PolyVec (Rq Φ) rows) :
    ‖gadgetDecompose Φ (zmodDigitDecomposition b digits hb hq) x‖₂² ≤
      rows * digits * (Φ.φ.natDegree * (b - 1) ^ 2) := by
  unfold vecL2NormSq
  calc ∑ i : Fin (rows * digits),
        Rq.l2NormSq Φ (gadgetDecompose Φ (zmodDigitDecomposition b digits hb hq) x i)
      ≤ ∑ _i : Fin (rows * digits), Φ.φ.natDegree * (b - 1) ^ 2 :=
        Finset.sum_le_sum (fun i _ => gadgetDecompose_zmod_l2NormSq_le Φ hb hq hbq x i)
    _ = rows * digits * (Φ.φ.natDegree * (b - 1) ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

omit [NeZero q] in
/-- **`ℓ₂²` shortness of one `G⁻¹` block from a digit bound, for an arbitrary
`DigitDecomposition`** — the `ℓ₂²` twin of `gadgetDecompose_lInftyNorm_le_of_digit_le`. -/
theorem gadgetDecompose_l2NormSq_le_of_digit_le {base : ZMod q} {digits rows γ : ℕ}
    (dd : DigitDecomposition base digits)
    (hdd : ∀ (c : ZMod q) (e : Fin digits), (dd.digit c e).valMinAbs.natAbs ≤ γ)
    (x : PolyVec (Rq Φ) rows) (j : Fin (rows * digits)) :
    ‖gadgetDecompose Φ dd x j‖₂² ≤ Φ.φ.natDegree * γ ^ 2 := by
  unfold Rq.l2NormSq
  calc ∑ k ∈ Finset.range Φ.φ.natDegree,
        ((gadgetDecompose Φ dd x j).1.coeff k).valMinAbs.natAbs ^ 2
      ≤ ∑ _k ∈ Finset.range Φ.φ.natDegree, γ ^ 2 := by
        refine Finset.sum_le_sum (fun k hk => ?_)
        rw [gadgetDecompose_coeff Φ _ x j (Finset.mem_range.mp hk)]
        exact Nat.pow_le_pow_left (hdd _ _) 2
    _ = Φ.φ.natDegree * γ ^ 2 := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]

omit [NeZero q] in
/-- Vector form of `gadgetDecompose_l2NormSq_le_of_digit_le`. -/
theorem gadgetDecompose_vecL2NormSq_le_of_digit_le {base : ZMod q} {digits rows γ : ℕ}
    (dd : DigitDecomposition base digits)
    (hdd : ∀ (c : ZMod q) (e : Fin digits), (dd.digit c e).valMinAbs.natAbs ≤ γ)
    (x : PolyVec (Rq Φ) rows) :
    ‖gadgetDecompose Φ dd x‖₂² ≤ rows * digits * (Φ.φ.natDegree * γ ^ 2) := by
  unfold vecL2NormSq
  calc ∑ i : Fin (rows * digits), Rq.l2NormSq Φ (gadgetDecompose Φ dd x i)
      ≤ ∑ _i : Fin (rows * digits), Φ.φ.natDegree * γ ^ 2 :=
        Finset.sum_le_sum (fun i _ => gadgetDecompose_l2NormSq_le_of_digit_le Φ dd hdd x i)
    _ = rows * digits * (Φ.φ.natDegree * γ ^ 2) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]

end ZModGadgetNorms

/-! # Part II — the recomposition direction `G·ẑ` -/

section ZModGadgetRecomposeNorms

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]

/-- **Core recomposition coefficient bound.** Each centered coefficient of an entry of the
gadget product `G_{b,rows} ·ᵥ v` is at most `(∑_{u<digits} bᵘ) · γ` whenever `‖v‖∞ ≤ γ`.

The wraparound of the `ZMod q` powers `bᵘ` is immaterial: the integer
`∑ₑ bᵉ·valMinAbs(vₑ.coeff k)` is an explicit representative of the output coefficient, and
the centered representative is minimal among all representatives (`valMinAbs_natAbs_le`).
Holds for **any** range-bounded `v` (in particular an adversarial `ẑ`), not just honest
digit decompositions. -/
theorem gadgetMul_zmod_coeff_natAbs_le {b rows digits : ℕ} (hd : 0 < digits)
    (h1 : 1 ≤ Φ.φ.natDegree) {γ : ℕ} (v : PolyVec (Rq Φ) (rows * digits))
    (hv : vecLInftyNorm Φ v ≤ γ) (i : Fin rows) {k : ℕ} (hk : k < Φ.φ.natDegree) :
    ((gadgetMul Φ (b : ZMod q) v i).1.coeff k).valMinAbs.natAbs
      ≤ (∑ u ∈ Finset.range digits, b ^ u) * γ := by
  -- the coefficient of the gadget product is the digit-weighted sum of block coefficients
  have hcoeff : (gadgetMul Φ (b : ZMod q) v i).1.coeff k
      = ∑ e : Fin digits, (b : ZMod q) ^ (e : ℕ) * (v (finProdFinEquiv (i, e))).1.coeff k := by
    rw [gadgetMul_apply Φ (b : ZMod q) hd v i, ← Rq.coeffHom_apply Φ k, map_sum]
    simp only [Rq.coeffHom_apply]
    exact Finset.sum_congr rfl fun e _ => Rq.constRq_mul_coeff Φ h1 _ _ k
  -- the explicit integer representative of that coefficient
  have hrep : ((∑ e : Fin digits,
        (b : ℤ) ^ (e : ℕ) * ((v (finProdFinEquiv (i, e))).1.coeff k).valMinAbs : ℤ) : ZMod q)
      = (gadgetMul Φ (b : ZMod q) v i).1.coeff k := by
    rw [hcoeff, Int.cast_sum]
    refine Finset.sum_congr rfl fun e _ => ?_
    rw [Int.cast_mul, Int.cast_pow, Int.cast_natCast, ZMod.coe_valMinAbs]
  -- entrywise range bound from the ℓ∞ hypothesis
  have hentry : ∀ e : Fin digits,
      ((v (finProdFinEquiv (i, e))).1.coeff k).valMinAbs.natAbs ≤ γ := fun e =>
    calc ((v (finProdFinEquiv (i, e))).1.coeff k).valMinAbs.natAbs
        ≤ Rq.lInftyNorm Φ (v (finProdFinEquiv (i, e))) :=
          Finset.le_sup (f := fun k => ((v (finProdFinEquiv (i, e))).1.coeff k).valMinAbs.natAbs)
            (Finset.mem_range.mpr hk)
      _ ≤ vecLInftyNorm Φ v :=
          Finset.le_sup (f := fun j => Rq.lInftyNorm Φ (v j)) (Finset.mem_univ _)
      _ ≤ γ := hv
  -- minimality of the centered representative + triangle over the integer representative
  calc ((gadgetMul Φ (b : ZMod q) v i).1.coeff k).valMinAbs.natAbs
      ≤ (∑ e : Fin digits,
          (b : ℤ) ^ (e : ℕ) * ((v (finProdFinEquiv (i, e))).1.coeff k).valMinAbs).natAbs :=
        valMinAbs_natAbs_le _ hrep
    _ ≤ ∑ e : Fin digits,
          ((b : ℤ) ^ (e : ℕ) * ((v (finProdFinEquiv (i, e))).1.coeff k).valMinAbs).natAbs :=
        Int.natAbs_sum_le _ _
    _ = ∑ e : Fin digits,
          b ^ (e : ℕ) * ((v (finProdFinEquiv (i, e))).1.coeff k).valMinAbs.natAbs := by
        refine Finset.sum_congr rfl fun e _ => ?_
        rw [Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_natCast]
    _ ≤ ∑ e : Fin digits, b ^ (e : ℕ) * γ :=
        Finset.sum_le_sum fun e _ => Nat.mul_le_mul_left _ (hentry e)
    _ = (∑ u ∈ Finset.range digits, b ^ u) * γ := by
        rw [← Finset.sum_mul, Fin.sum_univ_eq_sum_range (fun u => b ^ u) digits]

/-- Entrywise `ℓ∞` growth of the gadget recomposition: `‖(G·ᵥv)ᵢ‖∞ ≤ (∑_{u<digits} bᵘ)·γ`. -/
theorem gadgetMul_zmod_lInftyNorm_le {b rows digits : ℕ} (hd : 0 < digits)
    (h1 : 1 ≤ Φ.φ.natDegree) {γ : ℕ} (v : PolyVec (Rq Φ) (rows * digits))
    (hv : vecLInftyNorm Φ v ≤ γ) (i : Fin rows) :
    Rq.lInftyNorm Φ (gadgetMul Φ (b : ZMod q) v i)
      ≤ (∑ u ∈ Finset.range digits, b ^ u) * γ := by
  unfold Rq.lInftyNorm
  exact Finset.sup_le fun k hkmem =>
    gadgetMul_zmod_coeff_natAbs_le Φ hd h1 v hv i (Finset.mem_range.mp hkmem)

/-- **`ℓ∞` growth of the gadget recomposition.**
`‖G_{b,rows} ·ᵥ v‖∞ ≤ (∑_{u<digits} bᵘ) · γ` whenever `‖v‖∞ ≤ γ` — for **any**
range-bounded `v` (adversarial `ẑ` included). -/
theorem gadgetMul_zmod_vecLInftyNorm_le {b rows digits : ℕ} (hd : 0 < digits)
    (h1 : 1 ≤ Φ.φ.natDegree) {γ : ℕ} (v : PolyVec (Rq Φ) (rows * digits))
    (hv : vecLInftyNorm Φ v ≤ γ) :
    vecLInftyNorm Φ (gadgetMul Φ (b : ZMod q) v)
      ≤ (∑ u ∈ Finset.range digits, b ^ u) * γ := by
  unfold vecLInftyNorm
  exact Finset.sup_le fun i _ => gadgetMul_zmod_lInftyNorm_le Φ hd h1 v hv i

/-- **The `J`-recomposition `ℓ₂²` chain.** From the range check `‖ẑ‖∞ ≤ γ`
(Eq. (20)'s `ẑ ∈ S_b`, symmetric model), the recomposed `z = J·ẑ` satisfies
`‖z‖₂² ≤ zRecomposeL2SqBound γ b τ (deg φ) rows` — no primitive `‖z‖₂²` verifier check
is needed. -/
theorem gadgetMul_zmod_vecL2NormSq_le {b rows digits : ℕ} (hd : 0 < digits)
    (h1 : 1 ≤ Φ.φ.natDegree) {γ : ℕ} (v : PolyVec (Rq Φ) (rows * digits))
    (hv : vecLInftyNorm Φ v ≤ γ) :
    ‖gadgetMul Φ (b : ZMod q) v‖₂²
      ≤ zRecomposeL2SqBound γ b digits Φ.φ.natDegree rows := by
  calc vecL2NormSq Φ (gadgetMul Φ (b : ZMod q) v)
      ≤ rows * (Φ.φ.natDegree * (vecLInftyNorm Φ (gadgetMul Φ (b : ZMod q) v)) ^ 2) :=
        vecL2NormSq_le_card_mul_lInftyNorm_sq Φ _
    _ ≤ rows * (Φ.φ.natDegree * ((∑ u ∈ Finset.range digits, b ^ u) * γ) ^ 2) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left
          (gadgetMul_zmod_vecLInftyNorm_le Φ hd h1 v hv) 2))
    _ = zRecomposeL2SqBound γ b digits Φ.φ.natDegree rows := rfl

/-- End-to-end subtraction chain: two range-checked decompositions recompose to vectors whose
difference is `ℓ₂²`-bounded by `subL2NormSqBound (zRecomposeL2SqBound …) = 4·B_z` — exactly the
`βSq` needed for `VerifiedBlock.scaled_short` (`‖c̄ⱼ •ᵥ sⱼ‖₂² = ‖z_sib − z_cent‖₂² ≤ 4·B_z`). -/
theorem gadgetMul_zmod_sub_l2NormSq_le {b rows digits : ℕ} (hd : 0 < digits)
    (h1 : 1 ≤ Φ.φ.natDegree) {γ : ℕ} (v w : PolyVec (Rq Φ) (rows * digits))
    (hv : vecLInftyNorm Φ v ≤ γ) (hw : vecLInftyNorm Φ w ≤ γ) :
    ‖gadgetMul Φ (b : ZMod q) v - gadgetMul Φ (b : ZMod q) w‖₂²
      ≤ subL2NormSqBound (zRecomposeL2SqBound γ b digits Φ.φ.natDegree rows) :=
  sub_l2NormSq_le Φ _ _ (gadgetMul_zmod_vecL2NormSq_le Φ hd h1 v hv)
    (gadgetMul_zmod_vecL2NormSq_le Φ hd h1 w hw)

end ZModGadgetRecomposeNorms

end ArkLib.Lattices.Ajtai
