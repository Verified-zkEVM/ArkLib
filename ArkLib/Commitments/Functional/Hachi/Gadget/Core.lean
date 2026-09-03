/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.ModuleSIS
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Field.ZMod

/-!
# Ajtai Gadget Matrix Core

The base-`b` gadget matrix `G = I_rows ⊗ [1, b, b², …, b^(digits-1)]` over the cyclotomic
ring `Rq Φ`, mapping `rows * digits` ring elements to `rows` ring elements, used by the
inner-outer (Greyhound [NS24] / Hachi [NOZ26]) commitment. Gadget entries are *ring
constants* `C(bᵉ)` embedded into `Rq Φ`. `IsLawfulGadgetDecomposition` records when a
decomposition is inverted by gadget multiplication (`G · G⁻¹(x) = x`).

The norm-reducing inverse `G⁻¹` is the genuine **base-`b` digit decomposition** of the Hachi
paper ([NOZ26], §2.1): each coefficient of a ring element is written in base `b`, and digit `e`
of each coefficient is placed in the `bᵉ`-slot of its block. Trading one ring element for
`digits` elements with small digit coefficients is what keeps honest Ajtai openings short
(the norm bounds live in `Gadget.Norms`). The decomposition is captured abstractly by
`DigitDecomposition` (a per-coefficient digit map satisfying the base-`b` reconstruction law)
and realized concretely over `ZMod q` by `balancedZmodDigitDecomposition` — the paper's balanced
digits `⌈-b/2⌉ ≤ dᵢ ≤ ⌈b/2⌉ - 1`, built by shifting the unsigned digits of
`zmodDigitDecomposition`.

## Main definitions

* `gadgetMatrix`, `gadgetMul`: the gadget matrix `G` and multiplication by it.
* `IsLawfulGadgetDecomposition`: a decomposition is lawful when `G · G⁻¹(x) = x` for all `x`.
* `DigitDecomposition`: abstract base-`b` digit map on the coefficient ring, with the
  reconstruction law `∑ₑ bᵉ · digit c e = c`.
* `zmodDigitDecomposition`: the unsigned digits `[0, b − 1]` of the canonical representative over
  `ZMod q`, valid when `1 < b` and `q ≤ b ^ digits`. It is the building block the balanced digits
  are shifted from, not itself a Hachi gadget inverse.
* `balancedZmodDigitDecomposition`: **the Hachi gadget inverse `G⁻¹`** — the unsigned digits of the
  shifted coefficient `c + ⌊b/2⌋·(1 + b + ⋯)`, each less `⌊b/2⌋`, so every digit lies in the paper's
  box `S_b = [⌈-b/2⌉, ⌈b/2⌉ - 1]`.
* `BoundedDigitDecomposition`: the **short-input** counterpart — a total, executable digit map
  whose reconstruction law is guaranteed only for coefficients whose centered representative is
  within `bound`. This is what Hachi's folded witness `z = Σᵢ cᵢ sᵢ` needs: `z` is
  deterministically short in an honest run, so its digit count `τ` is set by that bound and *not*
  by `q` (see `boundedBalancedZmodDigitDecomposition`).
* `boundedBalancedZmodDigit` / `boundedBalancedZmodDigitDecomposition`: the executable balanced
  base-`b` decomposition of a short centered value, correct on the balanced interval
  `[-⌊b/2⌋·S, (b-1-⌊b/2⌋)·S]` with `S = ∑_{e<digits} bᵉ` — with **no** `q ≤ b ^ digits`
  requirement.
* `gadgetDecomposeFun`: the gadget inverse `G⁻¹` induced by a bare per-coefficient digit map;
  `gadgetDecompose` and `BoundedDigitDecomposition.gadgetDecompose` are its two instantiations.

## Main results

* `gadgetMul_apply`: row `i` of the gadget product is the base-weighted sum of the `digits`
  slots of block `i`.
* `gadgetDecomposeFun_gadgetMul_eq`: gadget multiplication inverts `gadgetDecomposeFun` as soon
  as the per-coefficient reconstruction law holds at the coefficients actually decomposed.
* `gadgetDecompose_lawful`: `gadgetDecompose` is a lawful gadget decomposition, so the
  inner-outer correctness theorem instantiates with this genuine base-`b` decomposition.
* `boundedGadgetDecompose_gadgetMul_eq`: the bounded gadget inverse is inverted by `G` on every
  `ℓ∞`-short input — the conditional round-trip the honest `ẑ = J⁻¹(z)` step uses at `τ = 5`.

## References

* [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
    Polynomial Commitments over Extension Fields*][NOZ26]
-/

open CompPoly ArkLib.Lattices ArkLib.Lattices.CyclotomicModulus

namespace ArkLib.Lattices.Ajtai

/-! ## Base-`b` reconstruction of `Nat.ofDigits` as a finite sum -/

/-- `Nat.ofDigits` as the finite sum of digit-weighted powers over the length of the list. -/
private theorem ofDigits_eq_sum_range {α : Type*} [CommSemiring α] (β : α) (L : List ℕ) :
    Nat.ofDigits β L = ∑ i ∈ Finset.range L.length, (L.getD i 0 : α) * β ^ i := by
  induction L with
  | nil => simp [Nat.ofDigits]
  | cons h t ih =>
    rw [show Nat.ofDigits β (h :: t) = (h : α) + β * Nat.ofDigits β t from rfl, ih,
        List.length_cons, Finset.sum_range_succ', Finset.mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

/-- `Nat.ofDigits` as a finite sum over any range `D` at least the list length (the extra
high-order digits are zero). -/
private theorem ofDigits_eq_sum_range_of_len_le {α : Type*} [CommSemiring α] (β : α) (L : List ℕ)
    {D : ℕ} (hLD : L.length ≤ D) :
    Nat.ofDigits β L = ∑ i ∈ Finset.range D, (L.getD i 0 : α) * β ^ i := by
  rw [ofDigits_eq_sum_range β L]
  apply Finset.sum_subset (fun x hx =>
    Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hx) hLD))
  intro i _ hi
  rw [Finset.mem_range, not_lt] at hi
  rw [List.getD_eq_default _ _ hi, Nat.cast_zero, zero_mul]

/-! ## Abstract digit decompositions of the coefficient ring -/

section Digit

variable {R : Type*} [CommSemiring R]

/-- A base-`base` digit decomposition of the coefficient ring `R`: for each coefficient `c`,
`digit c e` is the `e`-th base-`base` digit, and the `digits` digits reconstruct `c` via
`∑ₑ baseᵉ · digit c e = c`. This is the per-coefficient data behind the Hachi gadget inverse
`G⁻¹`. -/
structure DigitDecomposition (base : R) (digits : Nat) where
  /-- The `e`-th base-`base` digit of a coefficient. -/
  digit : R → Fin digits → R
  /-- The digits reconstruct the coefficient: `∑ₑ baseᵉ · digit c e = c`. -/
  reconstruct : ∀ c : R, ∑ e : Fin digits, base ^ (e : ℕ) * digit c e = c

end Digit

/-! ## The concrete base-`b` digit decomposition over `ZMod q` -/

section ZModDigit

variable {q : ℕ} [NeZero q]

/-- The naive **unsigned** base-`b` digit decomposition over `ZMod q`: digit `e` of a coefficient
`c` is the `e`-th base-`b` digit of its canonical representative `c.val`, in `[0, b − 1]`.
Reconstruction holds whenever `1 < b` and `q ≤ b ^ digits` (so every residue fits in `digits`
base-`b` digits).

Not itself a Hachi gadget inverse: [NOZ26] §2.1 writes digits in the balanced range
`⌈-b/2⌉ ≤ dᵢ ≤ ⌈b/2⌉ - 1`, which unsigned digits violate (at `b = 16`, `[0, 15]` against `[-8, 7]`).
The Hachi `G⁻¹` is `balancedZmodDigitDecomposition`, which shifts the input and re-centers each
digit of this one. -/
def zmodDigitDecomposition (b digits : ℕ) (hb : 1 < b) (hq : q ≤ b ^ digits) :
    DigitDecomposition (R := ZMod q) (b : ZMod q) digits where
  digit c e := ((Nat.digits b c.val).getD (e : ℕ) 0 : ZMod q)
  reconstruct c := by
    set L := Nat.digits b c.val with hL
    have hlen : L.length ≤ digits :=
      (Nat.digits_length_le_iff hb c.val).mpr (lt_of_lt_of_le (ZMod.val_lt c) hq)
    calc ∑ e : Fin digits, (b : ZMod q) ^ (e : ℕ) * ((L.getD (e : ℕ) 0 : ZMod q))
        = ∑ e : Fin digits, ((L.getD (e : ℕ) 0 : ZMod q)) * (b : ZMod q) ^ (e : ℕ) := by
          apply Finset.sum_congr rfl; intro e _; ring
      _ = ∑ i ∈ Finset.range digits, ((L.getD i 0 : ZMod q)) * (b : ZMod q) ^ i :=
          Fin.sum_univ_eq_sum_range (fun i => (L.getD i 0 : ZMod q) * (b : ZMod q) ^ i) digits
      _ = Nat.ofDigits (b : ZMod q) L := (ofDigits_eq_sum_range_of_len_le (b : ZMod q) L hlen).symm
      _ = ((Nat.ofDigits b L : ℕ) : ZMod q) := (Nat.coe_ofDigits (ZMod q) b L).symm
      _ = ((c.val : ℕ) : ZMod q) := by rw [hL, Nat.ofDigits_digits]
      _ = c := ZMod.natCast_zmod_val c

/-- The shift `⌊b/2⌋ · (1 + b + ⋯ + b^{digits-1})` that turns unsigned base-`b` digits into
**balanced** ones: subtracting `⌊b/2⌋` from each digit of `c + balancedShift` recovers `c`, because
the shift is exactly what the per-digit subtractions remove. -/
def balancedShift (b digits : ℕ) : ZMod q :=
  ((b / 2 : ℕ) : ZMod q) * ∑ e : Fin digits, (b : ZMod q) ^ (e : ℕ)

/-- **The balanced base-`b` digit decomposition over `ZMod q`**: digit `e` of `c` is the `e`-th
unsigned base-`b` digit of the shifted coefficient `c + balancedShift b digits`, less `⌊b/2⌋`.

Because the unsigned digits lie in `[0, b−1]`, the balanced digits lie in
`[−⌊b/2⌋, b−1−⌊b/2⌋] = [⌈−b/2⌉, ⌈b/2⌉−1]` — which is *exactly* the paper's balanced-digit box `S_b`
([NOZ26] §2.1), for both parities of `b`. That is what makes this the decomposition Hachi's exact
Eq. (20) range check accepts; the centered bounds are
`ArkLib.Lattices.Ajtai.balancedZmodDigit_valMinAbs_mem` (`Gadget/Norms.lean`), and the honest
prover's use of it is `QuadEval/Completeness.lean`.

Reconstruction is inherited from `zmodDigitDecomposition` at the shifted input: the digitwise
subtractions of `⌊b/2⌋` sum to exactly `balancedShift`, cancelling the shift. -/
def balancedZmodDigitDecomposition (b digits : ℕ) (hb : 1 < b) (hq : q ≤ b ^ digits) :
    DigitDecomposition (R := ZMod q) (b : ZMod q) digits where
  digit c e :=
    (zmodDigitDecomposition b digits hb hq).digit (c + balancedShift b digits) e
      - ((b / 2 : ℕ) : ZMod q)
  reconstruct c := by
    have hrec := (zmodDigitDecomposition b digits hb hq).reconstruct (c + balancedShift b digits)
    calc ∑ e : Fin digits, (b : ZMod q) ^ (e : ℕ) *
            ((zmodDigitDecomposition b digits hb hq).digit (c + balancedShift b digits) e
              - ((b / 2 : ℕ) : ZMod q))
        = (∑ e : Fin digits, (b : ZMod q) ^ (e : ℕ) *
              (zmodDigitDecomposition b digits hb hq).digit (c + balancedShift b digits) e)
            - ((b / 2 : ℕ) : ZMod q) * ∑ e : Fin digits, (b : ZMod q) ^ (e : ℕ) := by
          rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl fun e _ => by ring
      _ = (c + balancedShift b digits) - balancedShift b digits := by rw [hrec, balancedShift]
      _ = c := by ring

/-! ## Bounded (short-input) digit decompositions over `ZMod q`

`DigitDecomposition` demands the reconstruction law for **every** coefficient, which over
`ZMod q` forces `q ≤ base ^ digits` (see `zmodDigitDecomposition`). That is the right demand for
ordinary committed message coefficients, which are arbitrary residues. It is the *wrong* demand
for Hachi's folded witness `z = Σᵢ cᵢ sᵢ`: at the `ℓ = 30` parameters (`q = 4294967197`,
`b = 16`) with ArkLib's conservative `τ = 5` (`Params.lean`; [NOZ26] Figure 9 itself uses `τ = 4`,
under a sharper `‖z‖∞` bound than is formalized here) one has `16⁵ < q`, so no `5`-digit base-`16`
decomposition of every residue exists — and yet `τ = 5` is correct, because an honest `z` is
*deterministically short*
(`‖z‖∞ ≤ 2ʳ·ω·⌊b/2⌋`, [NOZ26] §4.4). The abstraction below separates the two notions rather than
weakening either. -/

section BoundedDigit

/-- A **bounded** base-`base` digit decomposition of `ZMod q`: a total, executable digit map whose
reconstruction law `∑ₑ baseᵉ · digit x e = x` is guaranteed exactly for the **short** inputs, those
whose centered representative satisfies `|x| ≤ bound`.

The digit map is a *field* of the structure, hence total and computable: the honest prover consumes
only `digit`, never a proof term, and only the correctness proof consumes
`reconstruct_of_bound`. That asymmetry is what keeps the honest path an executable specification
(the Rust-extraction target) while the reconstruction identity stays conditional on shortness. -/
structure BoundedDigitDecomposition (base : ZMod q) (digits bound : ℕ) where
  /-- The `e`-th base-`base` digit of a coefficient. Total and executable. -/
  digit : ZMod q → Fin digits → ZMod q
  /-- The digits reconstruct every **short** coefficient. -/
  reconstruct_of_bound : ∀ x : ZMod q, x.valMinAbs.natAbs ≤ bound →
    ∑ e : Fin digits, base ^ (e : ℕ) * digit x e = x

/-! ### The concrete bounded balanced base-`b` decomposition

`S := ∑_{e<digits} bᵉ` is the all-ones base-`b` value, so `digits` balanced digits in
`[-⌊b/2⌋, b-1-⌊b/2⌋]` represent exactly the integers of `[-⌊b/2⌋·S, (b-1-⌊b/2⌋)·S]`. The
construction shifts the centered representative by `⌊b/2⌋·S` into `[0, b^digits)`, decomposes that
nonnegative integer in ordinary base `b`, and subtracts `⌊b/2⌋` from every digit. -/

/-- `S = ∑_{e<digits} bᵉ`, the all-ones base-`b` value of length `digits`: the unit of balanced
capacity, since a constant balanced digit `a` represents `a · S`. -/
def digitOnesValue (b digits : ℕ) : ℕ := ∑ u ∈ Finset.range digits, b ^ u

/-- The **positive** balanced capacity of `digits` base-`b` digits: `(b-1-⌊b/2⌋) · S`, the largest
integer `digits` balanced digits represent. (The negative capacity `⌊b/2⌋ · S` is at least as
large, so this is also the radius of the largest symmetric interval represented — which is why the
`ℓ∞`-shaped honest bound is compared against it.) -/
def balancedDigitCapacity (b digits : ℕ) : ℕ := (b - 1 - b / 2) * digitOnesValue b digits

omit [NeZero q] in
/-- `S = ∑_{e<digits} bᵉ` is monotone in the digit count (the extra terms are nonnegative). -/
theorem digitOnesValue_mono (b : ℕ) {d d' : ℕ} (h : d ≤ d') :
    digitOnesValue b d ≤ digitOnesValue b d' :=
  Finset.sum_le_sum_of_subset (fun _ hx => Finset.mem_range.mpr
    (lt_of_lt_of_le (Finset.mem_range.mp hx) h))

omit [NeZero q] in
/-- **Balanced capacity is monotone in the digit count.** Fewer digits represent fewer integers, so
a capacity failure at some digit count propagates down — which is how minimality of a chosen `τ` is
established (see `HachiParams.tau_minimal`). -/
theorem balancedDigitCapacity_mono (b : ℕ) {d d' : ℕ} (h : d ≤ d') :
    balancedDigitCapacity b d ≤ balancedDigitCapacity b d' :=
  Nat.mul_le_mul_left _ (digitOnesValue_mono b h)

/-- The geometric identity `(b-1)·S + 1 = b ^ digits`: `digits` base-`b` digits in `[0, b)`
represent exactly `[0, b ^ digits)`. -/
theorem pred_mul_digitOnesValue_succ (b digits : ℕ) (hb : 1 ≤ b) :
    (b - 1) * digitOnesValue b digits + 1 = b ^ digits := by
  induction digits with
  | zero => simp [digitOnesValue]
  | succ n ih =>
    rw [digitOnesValue, Finset.sum_range_succ, ← digitOnesValue, Nat.mul_add, pow_succ]
    have hbn : 1 ≤ b ^ n := Nat.one_le_pow _ _ hb
    have : (b - 1) * b ^ n + b ^ n = b ^ n * b := by
      cases b with
      | zero => omega
      | succ c => simp only [Nat.succ_sub_one]; ring
    omega

/-- **The executable balanced base-`b` digit map for short centered values.** Digit `e` of `x` is
the `e`-th ordinary base-`b` digit of the shifted nonnegative integer
`(valMinAbs x + ⌊b/2⌋·S).toNat`, less `⌊b/2⌋`.

Total and computable at every `x`: `Int.toNat` clamps an out-of-range (too negative) shift to `0`
and out-of-range digit positions read as `0`, so the function always answers. Its digits always lie
in the balanced box `[-⌊b/2⌋, ⌈b/2⌉-1] = S_b` ([NOZ26] §2.1, see
`Gadget/Norms.lean`'s `boundedBalancedZmodDigit_valMinAbs_mem`); what shortness buys is the
*reconstruction* law (`boundedBalancedZmodDigit_reconstruct`), not the range. -/
def boundedBalancedZmodDigit (b digits : ℕ) (x : ZMod q) (e : Fin digits) : ZMod q :=
  (((Nat.digits b (x.valMinAbs + ((b / 2 : ℕ) : ℤ) * (digitOnesValue b digits : ℤ)).toNat).getD
      (e : ℕ) 0 : ℕ) : ZMod q) - ((b / 2 : ℕ) : ZMod q)

omit [NeZero q] in
/-- **Reconstruction of the bounded balanced digits, on short inputs.** If the centered
representative of `x` is within the balanced capacity `(b-1-⌊b/2⌋)·S`, the `digits` balanced digits
of `x` reconstruct it: `∑ₑ bᵉ · digit x e = x`.

**No `q ≤ b ^ digits` hypothesis appears**, and none could: the theorem is about the short
residues only. The shift lands in `[0, b ^ digits)` — nonnegativity from
`bound ≤ ⌊b/2⌋·S` (implied by the capacity bound) and the upper end from
`(b-1-⌊b/2⌋)·S + ⌊b/2⌋·S = (b-1)·S = b ^ digits - 1` — so the ordinary base-`b` digits of the
shift have length `≤ digits` and `Nat.ofDigits` recovers it; the digitwise `⌊b/2⌋` subtractions
then sum to exactly the shift and cancel. -/
theorem boundedBalancedZmodDigit_reconstruct {b digits bound : ℕ} (hb : 1 < b)
    (hcap : bound ≤ balancedDigitCapacity b digits) (x : ZMod q)
    (hx : x.valMinAbs.natAbs ≤ bound) :
    ∑ e : Fin digits, (b : ZMod q) ^ (e : ℕ) * boundedBalancedZmodDigit b digits x e = x := by
  set S : ℕ := digitOnesValue b digits with hSdef
  -- The two capacity endpoints, as `ℤ`-atoms `p` (negative side) and `rc` (positive side).
  set p : ℤ := ((b / 2 : ℕ) : ℤ) * (S : ℤ) with hpdef
  set rc : ℤ := ((b - 1 - b / 2 : ℕ) : ℤ) * (S : ℤ) with hrcdef
  have hhalf : b - 1 - b / 2 ≤ b / 2 := by omega
  have hcapNat : bound ≤ (b - 1 - b / 2) * S := by rw [hSdef]; exact hcap
  have hcapNegNat : bound ≤ (b / 2) * S := le_trans hcapNat (Nat.mul_le_mul hhalf (le_refl S))
  have hcapPos : (bound : ℤ) ≤ rc := by rw [hrcdef]; exact_mod_cast hcapNat
  have hcapNeg : (bound : ℤ) ≤ p := by rw [hpdef]; exact_mod_cast hcapNegNat
  have hgeom : rc + p + 1 = ((b ^ digits : ℕ) : ℤ) := by
    have hnat : (b - 1 - b / 2) * S + (b / 2) * S + 1 = b ^ digits := by
      rw [← Nat.add_mul, show (b - 1 - b / 2) + b / 2 = b - 1 from by omega, hSdef]
      exact pred_mul_digitOnesValue_succ b digits (le_of_lt hb)
    rw [hrcdef, hpdef]
    exact_mod_cast hnat
  -- The bracketing facts on the centered representative.
  have hlo : -(bound : ℤ) ≤ x.valMinAbs := by omega
  have hhi : x.valMinAbs ≤ (bound : ℤ) := by omega
  -- The shift is a nonnegative integer below `b ^ digits`.
  set sh : ℤ := x.valMinAbs + p with hshdef
  have hsh0 : 0 ≤ sh := by rw [hshdef]; linarith
  have hshhi : sh < ((b ^ digits : ℕ) : ℤ) := by rw [hshdef]; linarith
  set n : ℕ := sh.toNat with hndef
  have hn : (n : ℤ) = sh := Int.toNat_of_nonneg hsh0
  have hnlt : n < b ^ digits := by
    have : (n : ℤ) < ((b ^ digits : ℕ) : ℤ) := by rw [hn]; exact hshhi
    exact_mod_cast this
  set L : List ℕ := Nat.digits b n with hLdef
  have hlen : L.length ≤ digits := (Nat.digits_length_le_iff hb n).mpr hnlt
  -- The digit map, unfolded at this `x`.
  have hdig : ∀ e : Fin digits, boundedBalancedZmodDigit b digits x e
      = ((L.getD (e : ℕ) 0 : ℕ) : ZMod q) - ((b / 2 : ℕ) : ZMod q) := by
    intro e; rw [boundedBalancedZmodDigit, hLdef, hndef, hshdef, hpdef, hSdef]
  -- The two closed forms of the two halves of the sum.
  have hones : ∑ e : Fin digits, (b : ZMod q) ^ (e : ℕ) = ((S : ℕ) : ZMod q) := by
    rw [Fin.sum_univ_eq_sum_range (fun i => (b : ZMod q) ^ i) digits, hSdef, digitOnesValue]
    push_cast
    rfl
  have hunsigned : ∑ e : Fin digits, (b : ZMod q) ^ (e : ℕ) * ((L.getD (e : ℕ) 0 : ℕ) : ZMod q)
      = ((n : ℕ) : ZMod q) := by
    calc ∑ e : Fin digits, (b : ZMod q) ^ (e : ℕ) * ((L.getD (e : ℕ) 0 : ℕ) : ZMod q)
        = ∑ e : Fin digits, ((L.getD (e : ℕ) 0 : ℕ) : ZMod q) * (b : ZMod q) ^ (e : ℕ) := by
          exact Finset.sum_congr rfl fun e _ => by ring
      _ = ∑ i ∈ Finset.range digits, ((L.getD i 0 : ℕ) : ZMod q) * (b : ZMod q) ^ i :=
          Fin.sum_univ_eq_sum_range
            (fun i => ((L.getD i 0 : ℕ) : ZMod q) * (b : ZMod q) ^ i) digits
      _ = Nat.ofDigits (b : ZMod q) L :=
          (ofDigits_eq_sum_range_of_len_le (b : ZMod q) L hlen).symm
      _ = ((Nat.ofDigits b L : ℕ) : ZMod q) := (Nat.coe_ofDigits (ZMod q) b L).symm
      _ = ((n : ℕ) : ZMod q) := by rw [hLdef, Nat.ofDigits_digits]
  -- The shift cancels.
  have hcast : ((n : ℕ) : ZMod q) = x + ((b / 2 : ℕ) : ZMod q) * ((S : ℕ) : ZMod q) := by
    have hz : ((n : ℕ) : ℤ) = x.valMinAbs + ((b / 2 : ℕ) : ℤ) * (S : ℤ) := by
      rw [hn, hshdef, hpdef]
    calc ((n : ℕ) : ZMod q) = (((n : ℕ) : ℤ) : ZMod q) := (Int.cast_natCast n).symm
      _ = ((x.valMinAbs + ((b / 2 : ℕ) : ℤ) * (S : ℤ) : ℤ) : ZMod q) := by rw [hz]
      _ = x + ((b / 2 : ℕ) : ZMod q) * ((S : ℕ) : ZMod q) := by
          rw [Int.cast_add, Int.cast_mul, ZMod.coe_valMinAbs, Int.cast_natCast,
            Int.cast_natCast]
  calc ∑ e : Fin digits, (b : ZMod q) ^ (e : ℕ) * boundedBalancedZmodDigit b digits x e
      = ∑ e : Fin digits, (b : ZMod q) ^ (e : ℕ) *
          (((L.getD (e : ℕ) 0 : ℕ) : ZMod q) - ((b / 2 : ℕ) : ZMod q)) := by
        exact Finset.sum_congr rfl fun e _ => by rw [hdig e]
    _ = (∑ e : Fin digits, (b : ZMod q) ^ (e : ℕ) * ((L.getD (e : ℕ) 0 : ℕ) : ZMod q))
          - ((b / 2 : ℕ) : ZMod q) * ∑ e : Fin digits, (b : ZMod q) ^ (e : ℕ) := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun e _ => by ring
    _ = x := by rw [hunsigned, hones, hcast]; ring

/-- **The bounded balanced base-`b` digit decomposition over `ZMod q`.** The executable digit map
`boundedBalancedZmodDigit` packaged with its conditional reconstruction law, at any `bound` within
the balanced capacity of `digits` digits.

This is the `τ = 5` instance of `Params.lean` (ArkLib's conservative choice, not [NOZ26]
Figure 9's `τ = 4`): at `q = 4294967197`, `b = 16`, `digits = 5` the capacity is
`(16-1-8)·(1+16+256+4096+65536) = 7 · 69905 = 489335`, comfortably above the honest bound
`2¹⁰ · 16 · 8 = 131072` — and `q ≤ 16⁵` is nowhere assumed (it is false). -/
def boundedBalancedZmodDigitDecomposition (b digits bound : ℕ) (hb : 1 < b)
    (hcap : bound ≤ balancedDigitCapacity b digits) :
    BoundedDigitDecomposition (b : ZMod q) digits bound where
  digit := boundedBalancedZmodDigit b digits
  reconstruct_of_bound x hx := boundedBalancedZmodDigit_reconstruct hb hcap x hx

end BoundedDigit

end ZModDigit

/-! ## The gadget matrix over `Rq Φ` -/

variable {R : Type} [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]
  (Φ : CyclotomicModulus R) [IsCyclotomic Φ]

/-- Entry of the base-`base` gadget matrix `I_rows ⊗ [1, base, …, base^(digits-1)]`:
column `j` of row `i` is `base^(j % digits)` when `j / digits = i`, else `0`. -/
def gadgetEntry (base : R) {rows digits : Nat} (i : Fin rows) (j : Fin (rows * digits)) : Rq Φ :=
  if j.val / digits = i.val then Rq.constRq Φ (base ^ (j.val % digits)) else 0

/-- The base-`base` gadget matrix `I_rows ⊗ [1, base, …, base^(digits-1)]`. -/
def gadgetMatrix (base : R) (rows digits : Nat) : PolyMatrix (Rq Φ) rows (rows * digits) :=
  fun i j => gadgetEntry Φ base i j

/-- Apply the gadget matrix to a decomposed vector. -/
def gadgetMul (base : R) {rows digits : Nat} (v : PolyVec (Rq Φ) (rows * digits)) :
    PolyVec (Rq Φ) rows :=
  gadgetMatrix Φ base rows digits *ᵥ v

/-- A gadget decomposition is lawful when gadget multiplication reconstructs its input. -/
def IsLawfulGadgetDecomposition (base : R) {rows digits : Nat}
    (decompose : PolyVec (Rq Φ) rows → PolyVec (Rq Φ) (rows * digits)) : Prop :=
  ∀ x, gadgetMul Φ base (decompose x) = x

/-! ## The gadget product as a block digit-sum -/

omit [DecidableEq R] in
/-- The gadget entry at the flattened index `finProdFinEquiv (i', e)` is `constRq (base^e)`
on the diagonal block and `0` elsewhere. -/
theorem gadgetEntry_finProdFinEquiv (base : R) {rows digits : Nat} (hd : 0 < digits)
    (i i' : Fin rows) (e : Fin digits) :
    gadgetEntry Φ base i (finProdFinEquiv (i', e))
      = if i' = i then Rq.constRq Φ (base ^ (e : ℕ)) else 0 := by
  unfold gadgetEntry
  have hval : (finProdFinEquiv (i', e)).val = e.val + digits * i'.val := rfl
  have hdiv : (finProdFinEquiv (i', e)).val / digits = i'.val := by
    rw [hval, Nat.add_mul_div_left _ _ hd, Nat.div_eq_of_lt e.isLt, zero_add]
  have hmod : (finProdFinEquiv (i', e)).val % digits = e.val := by
    rw [hval, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt e.isLt]
  rw [hdiv, hmod]
  simp only [Fin.ext_iff]

omit [DecidableEq R] in
/-- The gadget product, evaluated at row `i`, is the base-weighted sum of the `digits`
slots of block `i`. -/
theorem gadgetMul_apply (base : R) {rows digits : Nat} (hd : 0 < digits)
    (v : PolyVec (Rq Φ) (rows * digits)) (i : Fin rows) :
    gadgetMul Φ base v i
      = ∑ e : Fin digits, Rq.constRq Φ (base ^ (e : ℕ)) * v (finProdFinEquiv (i, e)) := by
  rw [gadgetMul, matVecMul_apply, dot_eq_sum]
  simp only [gadgetMatrix]
  rw [← Equiv.sum_comp finProdFinEquiv (fun j => gadgetEntry Φ base i j * v j),
      Fintype.sum_prod_type]
  rw [Finset.sum_eq_single i]
  · apply Finset.sum_congr rfl
    intro e _
    rw [gadgetEntry_finProdFinEquiv Φ base hd i i e, if_pos rfl]
  · intro i' _ hne
    apply Finset.sum_eq_zero
    intro e _
    rw [gadgetEntry_finProdFinEquiv Φ base hd i i' e, if_neg hne, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ## The base-`b` gadget decomposition and its lawfulness

`gadgetDecompose dd` is the Hachi gadget inverse `G⁻¹` built from a `DigitDecomposition dd`:
block `i`'s slot `e` is the ring element whose `k`-th coefficient is the `e`-th base-`b`
digit of the `k`-th coefficient of `x i`. By the reconstruction law of `dd`, gadget
multiplication recovers `x` (`gadgetDecompose_lawful`), so the inner-outer correctness
theorem instantiates with this genuine binary decomposition. -/

variable {base : R}

/-- The base-`b` gadget decomposition (Hachi `G⁻¹`) induced by a **bare per-coefficient digit
map**: block `i`'s slot `e` is the ring element whose `k`-th coefficient is `digit` of the `k`-th
coefficient of `x i` at position `e`.

This is the shared computational core of the two decompositions the reduction uses:
`gadgetDecompose` (from a full `DigitDecomposition`, for arbitrary coefficients) and
`BoundedDigitDecomposition.gadgetDecompose` (from a bounded one, for short coefficients). Both are
`rfl`-equal to it, so the layout bookkeeping and the norm bounds are proved once. -/
def gadgetDecomposeFun {rows digits : Nat} (digit : R → Fin digits → R)
    (x : PolyVec (Rq Φ) rows) : PolyVec (Rq Φ) (rows * digits) :=
  fun j => Rq.ofFinCoeff Φ Φ.φ.natDegree
    (fun k => digit ((x (finProdFinEquiv.symm j).1).1.coeff k) (finProdFinEquiv.symm j).2)

/-- Value of `gadgetDecomposeFun` at the flattened index `finProdFinEquiv (i, e)`. -/
theorem gadgetDecomposeFun_apply {rows digits : Nat} (digit : R → Fin digits → R)
    (x : PolyVec (Rq Φ) rows) (i : Fin rows) (e : Fin digits) :
    gadgetDecomposeFun Φ digit x (finProdFinEquiv (i, e))
      = Rq.ofFinCoeff Φ Φ.φ.natDegree (fun k => digit ((x i).1.coeff k) e) := by
  unfold gadgetDecomposeFun
  simp only [Equiv.symm_apply_apply]

/-- **Gadget multiplication inverts `gadgetDecomposeFun`** whenever the per-coefficient
reconstruction law holds *at the coefficients actually decomposed*. Both round-trips in the
reduction are instances: unconditional for a `DigitDecomposition` (`gadgetDecompose_lawful`) and
conditional on shortness for a `BoundedDigitDecomposition`
(`boundedGadgetDecompose_gadgetMul_eq`). -/
theorem gadgetDecomposeFun_gadgetMul_eq {rows digits : Nat} (hd : 0 < digits)
    (h1 : 1 ≤ Φ.φ.natDegree) (digit : R → Fin digits → R) (x : PolyVec (Rq Φ) rows)
    (hrec : ∀ (i : Fin rows) (k : ℕ), k < Φ.φ.natDegree →
      ∑ e : Fin digits, base ^ (e : ℕ) * digit ((x i).1.coeff k) e = (x i).1.coeff k) :
    gadgetMul Φ base (gadgetDecomposeFun Φ digit x) = x := by
  funext i
  rw [gadgetMul_apply Φ base hd]
  simp_rw [gadgetDecomposeFun_apply Φ digit x i]
  apply Subtype.ext
  rw [CompPoly.CPolynomial.eq_iff_coeff]
  intro k
  have hsum : (∑ e : Fin digits,
        Rq.constRq Φ (base ^ (e : ℕ)) * Rq.ofFinCoeff Φ Φ.φ.natDegree
          (fun k' => digit ((x i).1.coeff k') e)).1.coeff k
      = ∑ e : Fin digits,
        (Rq.constRq Φ (base ^ (e : ℕ)) * Rq.ofFinCoeff Φ Φ.φ.natDegree
          (fun k' => digit ((x i).1.coeff k') e)).1.coeff k := by
    rw [← Rq.coeffHom_apply Φ k, map_sum]
    simp only [Rq.coeffHom_apply]
  have hterm : ∀ e : Fin digits,
      (Rq.constRq Φ (base ^ (e : ℕ)) * Rq.ofFinCoeff Φ Φ.φ.natDegree
          (fun k' => digit ((x i).1.coeff k') e)).1.coeff k
        = base ^ (e : ℕ) * (if k < Φ.φ.natDegree then digit ((x i).1.coeff k) e else 0) := by
    intro e
    rw [Rq.constRq_mul_coeff Φ h1, Rq.ofFinCoeff_coeff Φ _ (Rq.phi_natDegree_le_degree Φ)]
  rw [hsum]
  simp_rw [hterm]
  by_cases hk : k < Φ.φ.natDegree
  · simp only [if_pos hk]
    exact hrec i k hk
  · simp only [if_neg hk, mul_zero, Finset.sum_const_zero]
    exact (Rq.coeff_eq_zero_of_natDegree_le Φ (x i) (not_lt.mp hk)).symm

/-- The base-`b` gadget decomposition (Hachi `G⁻¹`) induced by a `DigitDecomposition`. -/
def gadgetDecompose {rows digits : Nat} (dd : DigitDecomposition base digits)
    (x : PolyVec (Rq Φ) rows) : PolyVec (Rq Φ) (rows * digits) :=
  gadgetDecomposeFun Φ dd.digit x

/-- The base-`b` gadget decomposition is a lawful gadget decomposition. -/
theorem gadgetDecompose_lawful {rows digits : Nat} (hd : 0 < digits) (h1 : 1 ≤ Φ.φ.natDegree)
    (dd : DigitDecomposition base digits) :
    IsLawfulGadgetDecomposition Φ base (gadgetDecompose Φ dd (rows := rows)) := fun x =>
  gadgetDecomposeFun_gadgetMul_eq Φ hd h1 dd.digit x
    (fun i k _ => dd.reconstruct ((x i).1.coeff k))

/-! ## The bounded gadget decomposition `J⁻¹` on short inputs

The `ZMod q` counterpart of the block above: the gadget inverse built from a
`BoundedDigitDecomposition`, whose round-trip `G · G⁻¹(x) = x` holds exactly when the coefficients
being decomposed are short. This is the honest `ẑ = J⁻¹(z)` step at `τ = 5`; the `ℓ∞`-shaped form of
the hypothesis is `boundedGadgetDecompose_gadgetMul_eq_of_vecLInftyNorm_le`
(`Gadget/Norms.lean`), where the centered norms live. -/

section BoundedGadget

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ] {base : ZMod q} {digits bound : ℕ}

/-- The gadget inverse `G⁻¹` induced by a `BoundedDigitDecomposition` — the same computation as
`gadgetDecompose`, over the bounded decomposition's (total, executable) digit map. -/
def BoundedDigitDecomposition.gadgetDecompose
    (bdd : BoundedDigitDecomposition base digits bound) {rows : Nat}
    (x : PolyVec (Rq Φ) rows) : PolyVec (Rq Φ) (rows * digits) :=
  gadgetDecomposeFun Φ bdd.digit x

omit [NeZero q] in
/-- **The conditional gadget round-trip** `G · G⁻¹(x) = x` for the bounded decomposition, from the
coefficientwise shortness of `x`. Every coefficient of the output *is* a digit of a coefficient of
the input (`gadgetDecomposeFun`), so `bdd.reconstruct_of_bound` at each short input coefficient is
all that is needed. -/
theorem boundedGadgetDecompose_gadgetMul_eq (hd : 0 < digits) (h1 : 1 ≤ Φ.φ.natDegree)
    (bdd : BoundedDigitDecomposition base digits bound) {rows : Nat}
    (x : PolyVec (Rq Φ) rows)
    (hx : ∀ (i : Fin rows) (k : ℕ), k < Φ.φ.natDegree →
      ((x i).1.coeff k).valMinAbs.natAbs ≤ bound) :
    gadgetMul Φ base (bdd.gadgetDecompose Φ x) = x :=
  gadgetDecomposeFun_gadgetMul_eq Φ hd h1 bdd.digit x
    (fun i k hk => bdd.reconstruct_of_bound ((x i).1.coeff k) (hx i k hk))

end BoundedGadget

end ArkLib.Lattices.Ajtai
