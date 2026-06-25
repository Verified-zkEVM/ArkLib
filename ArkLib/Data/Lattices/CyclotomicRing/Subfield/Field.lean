/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.Factorization
import ArkLib.Data.Lattices.CyclotomicRing.Subfield.Cardinality
import Mathlib.RingTheory.IntegralDomain
import Mathlib.Algebra.Polynomial.Reverse

/-!
# `R_q^H` is a Field Isomorphic to `F_{q^k}` (Hachi §3, Lemma 5)

This is the one piece of Hachi [NOZ26, §3] not yet covered by the rest of `Subfield/`: upgrading
the fixed subring `R_q^H` from "a `Subring` of cardinality `q^k`" (`card_fixedSubring_eq`) to "a
field isomorphic to `F_{q^k}`".

The route (blueprint `blueprint/src/lattices/hachi_subfield.tex`, Phases 4–5):

1. `X^{2^α}+1 = p₁·p₂` (coprime irreducibles, `exists_irreducible_factorization`), and `σ_{-1}`
   (`= X ↦ X⁻¹`) relates to polynomial reversal by `mk(reverse p) = σ_{-1}(mk p)·(mk X)^{deg p}`
   (`mk_reverse_eq_galoisAutₛ_mul`); with `p₁.reverse ~ p₂` (`no_selfReciprocal_factor`) this makes
   `σ_{-1}` swap the two factors.
2. Hence in `S = Z_q[X]/(X^{2^α}+1)` every nonzero `σ_{-1}`-fixed element is a unit
   (`galoisAutₛ_fixed_isUnit`): if `p₁ ∣ g` then `σ_{-1}`-fixedness forces `p₂ ∣ g` too, so
   `X^{2^α}+1 ∣ g` and the element is `0`. Transporting to `R_q` gives `conjFixedSubring_isField`.
3. `R_q^H ⊆ R_q^{σ_{-1}}` (`fixedSubring_le_conjFixedSubring`) is then a finite integral domain,
   hence a field (`fixedSubring_isField`).
4. A finite field of cardinality `q^k` (`card_fixedSubring_eq`) is `≃+* GaloisField q k`
   (`fixedSubringEquivGaloisField`).

## Status

The only remaining `sorry` is `no_selfReciprocal_factor` (the `−1 ∉ ⟨q⟩` root-orbit argument,
blueprint Lemma 4.5); its docstring carries a self-contained proof plan and an inventory of the
already-proven ingredients. It holds the entire number-theoretic content of the swap. Everything
else — the reverse identity, factor existence, the core unit lemma, and the whole assembly
(`conjFixedSubring_isField`, `fixedSubring_isField`, `fixedSubringEquivGaloisField`) — is proven.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi …*][NOZ26]
-/

open Polynomial

namespace ArkLib.Lattices.CyclotomicModulus

variable (q : ℕ) [Fact (Nat.Prime q)] [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)]

/-! ## Phase 4a: the `σ_{-1} ↔ reverse` correspondence -/

open Polynomial in
omit [NeZero q] in
/-- **The reverse identity.** In `S = Z_q[X]/(X^{2^α}+1)`, the conjugation `σ_{-1}` (here the
semantic automorphism `galoisAutₛ` of exponent `conjExp = 2^{α+1}-1`) and the polynomial reversal
are related by `mk(reverse p) = σ_{-1}(mk p) · (mk X)^{deg p}`.

This is the concrete handle behind "`σ_{-1}` swaps the two factors": since `(mk X)^{deg p}` is a
unit, `σ_{-1}` carries the principal ideal `(mk p)` onto `(mk (reverse p))`. The proof routes
through Mathlib's `Polynomial.eval₂_reverse_mul_pow` with the evaluation point `⅟(mk X) = (mk X)^c`
(as `(mk X)^{2^{α+1}} = 1`), avoiding any coefficient-sum manipulation. -/
theorem mk_reverse_eq_galoisAutₛ_mul (α : ℕ) (p : (ZMod q)[X]) :
    Ideal.Quotient.mk (powTwoCyclotomic (R := ZMod q) α).modIdeal p.reverse
      = galoisAutₛ α (conjExp α) (conjExp_odd α)
          (Ideal.Quotient.mk (powTwoCyclotomic (R := ZMod q) α).modIdeal p)
        * (Ideal.Quotient.mk (powTwoCyclotomic (R := ZMod q) α).modIdeal X) ^ p.natDegree := by
  set mk := Ideal.Quotient.mk (powTwoCyclotomic (R := ZMod q) α).modIdeal with hmkdef
  set x : (powTwoCyclotomic (R := ZMod q) α).CyclotomicRing := mk X with hxdef
  have hx2d : x ^ (2 ^ (α + 1)) = 1 := by rw [hxdef, ← map_pow]; exact mk_X_pow_conductor_eq_one α
  have hcx : x ^ (conjExp α) * x = 1 := by
    rw [← pow_succ, conjExp, Nat.sub_add_cancel Nat.one_le_two_pow, hx2d]
  letI invx : Invertible x := ⟨x ^ (conjExp α), hcx, by rw [mul_comm]; exact hcx⟩
  set i : ZMod q →+* (powTwoCyclotomic (R := ZMod q) α).CyclotomicRing := mk.comp C with hidef
  have heval_mk : ∀ r : (ZMod q)[X], eval₂ i x r = mk r := by
    have hext : (Polynomial.eval₂RingHom i x) = mk := by
      apply Polynomial.ringHom_ext
      · intro a
        simp only [Polynomial.coe_eval₂RingHom, eval₂_C, hidef, RingHom.comp_apply]
      · simp only [Polynomial.coe_eval₂RingHom, eval₂_X, hxdef]
    intro r; rw [← hext]; rfl
  have hxc : mk (X ^ (conjExp α)) = ⅟x := by rw [map_pow]; rfl
  have hsigma : galoisAutₛ α (conjExp α) (conjExp_odd α) (mk p) = eval₂ i (⅟x) p := by
    rw [galoisAutₛ_mk, Polynomial.aeval_def, Polynomial.algebraMap_eq, Polynomial.hom_eval₂,
      ← hidef, hxc]
  have hrev := Polynomial.eval₂_reverse_mul_pow i (⅟x) p
  rw [invOf_invOf, heval_mk, ← hsigma] at hrev
  rw [← hrev, mul_assoc, ← mul_pow, invOf_mul_self, one_pow, mul_one]

/-! ## Phase 4b: factorization into two coprime irreducibles -/

omit [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- **Factor existence.** For `q ≡ 5 (mod 8)`, `X^{2^α}+1` factors over `Z_q` as a product of two
coprime irreducible polynomials. Extracted from `cyclotomic_card_normalizedFactors` (the
two normalized factors), with coprimality from `Irreducible.coprime_iff_not_dvd`. -/
theorem exists_irreducible_factorization (hq5 : q % 8 = 5) {α : ℕ} (hα : 1 ≤ α) :
    ∃ p₁ p₂ : (ZMod q)[X], Irreducible p₁ ∧ Irreducible p₂ ∧ IsCoprime p₁ p₂ ∧
      (X ^ (2 ^ α) + 1 : (ZMod q)[X]) = p₁ * p₂ := by
  classical
  have hqcop : ¬ (q ∣ 2 ^ (α + 1)) := by
    intro h
    have hq2 : q ∣ 2 := Nat.Prime.dvd_of_dvd_pow Fact.out h
    have := Nat.le_of_dvd (by norm_num) hq2; omega
  haveI : NeZero ((2 ^ (α + 1) : ℕ) : ZMod q) :=
    ⟨by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hqcop⟩
  set f : (ZMod q)[X] := cyclotomic (2 ^ (α + 1)) (ZMod q) with hf
  have hfne : f ≠ 0 := cyclotomic_ne_zero _ _
  have hf_monic : f.Monic := cyclotomic.monic _ _
  have hsqf : Squarefree f := squarefree_cyclotomic _ _
  have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors hfne).mp hsqf
  have hcard : Multiset.card (UniqueFactorizationMonoid.normalizedFactors f) = 2 := by
    have h2 := cyclotomic_card_normalizedFactors q hq5 hα
    rw [← hf] at h2
    rwa [← Multiset.toFinset_card_of_nodup hnodup]
  obtain ⟨a, b, hab⟩ := Multiset.card_eq_two.mp hcard
  have ha_mem : a ∈ UniqueFactorizationMonoid.normalizedFactors f := by rw [hab]; simp
  have hb_mem : b ∈ UniqueFactorizationMonoid.normalizedFactors f := by rw [hab]; simp
  have ha_irr := UniqueFactorizationMonoid.irreducible_of_normalized_factor a ha_mem
  have hb_irr := UniqueFactorizationMonoid.irreducible_of_normalized_factor b hb_mem
  have ha_monic : a.Monic := by
    have h := UniqueFactorizationMonoid.normalize_normalized_factor a ha_mem
    rw [← h]; exact monic_normalize ha_irr.ne_zero
  have hb_monic : b.Monic := by
    have h := UniqueFactorizationMonoid.normalize_normalized_factor b hb_mem
    rw [← h]; exact monic_normalize hb_irr.ne_zero
  have hne : a ≠ b := by have := hnodup; rw [hab] at this; simpa using this
  have hprod : a * b = f := by
    have hassoc : Associated (a * b) f := by
      have := UniqueFactorizationMonoid.prod_normalizedFactors hfne
      rwa [hab, Multiset.prod_pair] at this
    calc a * b = normalize (a * b) := ((ha_monic.mul hb_monic).normalize_eq_self).symm
      _ = normalize f := normalize_eq_normalize_iff.mpr ⟨hassoc.dvd, hassoc.symm.dvd⟩
      _ = f := hf_monic.normalize_eq_self
  have hcop : IsCoprime a b := by
    rw [ha_irr.coprime_iff_not_dvd]
    intro hdvd
    have hassoc : Associated a b := ha_irr.associated_of_dvd hb_irr hdvd
    refine hne ?_
    calc a = normalize a := (ha_monic.normalize_eq_self).symm
      _ = normalize b := normalize_eq_normalize_iff.mpr ⟨hassoc.dvd, hassoc.symm.dvd⟩
      _ = b := hb_monic.normalize_eq_self
  exact ⟨a, b, ha_irr, hb_irr, hcop, by rw [Xpow_add_one_eq_cyclotomic q α, ← hf, ← hprod]⟩

/-! ## Phase 4: the swap -/

/-- **(Phase 4, blueprint Lemma 4.5, `lem:no_selfReciprocal` in
`blueprint/src/lattices/hachi_subfield.tex`)** For `q ≡ 5 (mod 8)`, reversal *swaps* the two
irreducible factors of `X^{2^α}+1`: if `X^{2^α}+1 = p₁ · p₂` with `p₁, p₂` irreducible, then
`p₁.reverse` is associated to `p₂` (and hence not to `p₁`).

**Status: `sorry` — open for contribution** (blueprint difficulty rating 8/10). This is the *only*
remaining gap in the `R_q^H ≃+* F_{q^k}` chain (Hachi [NOZ26, §3], Lemma 5): everything downstream
(`galoisAutₛ_fixed_isUnit`, `conjFixedSubring_isField`, `fixedSubring_isField`,
`fixedSubringEquivGaloisField`) is fully proven conditional on this lemma.

## Mathematical content

`X^{2^α}+1 = Φ_{2^{α+1}}` is self-reciprocal, so reversal permutes its two irreducible factors up
to associates; the claim is that this permutation is the *swap*, never the identity. All the
number theory of `q ≡ 5 (mod 8)` is concentrated here: the roots of `p₁` (in any splitting field,
e.g. `F_{q^{2^{α-1}}}`) are primitive `2^{α+1}`-th roots of unity forming a single Frobenius orbit
`{ζ^{q^i}}` — a coset of `⟨q⟩ ≤ (Z/2^{α+1})ˣ` in the exponent — while the roots of `p₁.reverse`
are their inverses. If `p₁.reverse ~ p₁`, the orbit is closed under `ζ ↦ ζ⁻¹`, so
`q^i ≡ −1 (mod 2^{α+1})` for some `i`, i.e. `−1 ∈ ⟨q⟩` — contradicting `neg_one_notMem_powers_q`.
This swap is exactly what makes `σ_{-1}` (`= X ↦ X⁻¹`) interchange the two CRT factors.

## Suggested proof outline

1. *Reversal permutes `{p₁, p₂}`.* From `p₁ ∣ X^{2^α}+1` get `p₁.reverse ∣ (X^{2^α}+1).reverse
   = X^{2^α}+1` (`Polynomial.reverse_mul_of_domain` plus computing the reverse of `X^{2^α}+1`).
   `p₁.reverse` is irreducible of the same degree, since `p₁.coeff 0 ≠ 0` (`0` is not a root of
   `X^{2^α}+1`); see the `Polynomial.reverse` / `natTrailingDegree` API. As `p₁, p₂` are the only
   irreducible factors of `X^{2^α}+1` (by `hf` and uniqueness of factorization), either
   `p₁.reverse ~ p₂` (done) or `p₁.reverse ~ p₁`.

2. *Set up a root without splitting fields.* Work in `K := AdjoinRoot p₁`, a field since `p₁` is
   irreducible. Let `ζ : K` be the image of `X`: then `ζ^{2^α} = -1` (from `hf`), so `ζ` has
   multiplicative order exactly `2^{α+1}` (as `(2 : ZMod q) ≠ 0` because `q` is odd).

3. *Roots of `p₁` in `K` are the Frobenius orbit `{ζ^{q^i} | i < 2^{α-1}}`.* The Frobenius
   `x ↦ x^q` fixes `Z_q` (`ZMod.pow_card`/`FiniteField.pow_card`), so each `ζ^{q^i}` is a root of
   `p₁`. They are pairwise distinct: `ζ^{q^i} = ζ^{q^j}` forces `q^i ≡ q^j (mod 2^{α+1})`, and
   `orderOf (q : ZMod (2^{α+1})) = 2^{α-1}` (`orderOf_q_eq`, proven in
   `Subfield/Factorization.lean`). Since `p₁.natDegree = 2^{α-1}`
   (`cyclotomic_card_normalizedFactors` gives two factors each of degree `2^{α-1}`; or directly
   from `hf` plus step 1's degree bookkeeping), a card count shows these are *all* roots of `p₁`
   in `K`.

4. *Derive the contradiction from `p₁.reverse ~ p₁`.* `ζ⁻¹` is a root of `p₁.reverse`
   (`Polynomial.eval₂_reverse_eq_zero_iff`, the same trick as `mk_reverse_eq_galoisAutₛ_mul`
   above, with `⅟ζ = ζ^{2^{α+1}-1}`). If `p₁.reverse ~ p₁` then `ζ⁻¹` is a root of `p₁`, so by
   step 3 `ζ⁻¹ = ζ^{q^i}` for some `i`; comparing exponents via `orderOf ζ = 2^{α+1}` (step 2)
   yields `(q : ZMod (2^{α+1}))^i = -1`, contradicting `neg_one_notMem_powers_q q hq5 hα`
   (proven in `Subfield/Factorization.lean`).

## Available ingredients (all proven)

- `neg_one_notMem_powers_q` (`Subfield/Factorization.lean`): no power of `q` is `-1` in
  `ZMod (2^{α+1})` — the number-theoretic core.
- `orderOf_q_eq` (`Subfield/Factorization.lean`): `orderOf (q : ZMod (2^{α+1})) = 2^{α-1}`.
- `cyclotomic_card_normalizedFactors` (`Subfield/Factorization.lean`): exactly two irreducible
  factors, and `Xpow_add_one_eq_cyclotomic` identifies `X^{2^α}+1` with `Φ_{2^{α+1}}`.
- `mk_reverse_eq_galoisAutₛ_mul` (above): a worked example of the `Invertible`-point
  `eval₂`-reverse technique (`Polynomial.eval₂_reverse_mul_pow`).
- Mathlib's `Polynomial.Reverse` file: `reverse_mul_of_domain`, `eval₂_reverse_eq_zero_iff`,
  `reverse_natDegree`-style lemmas. -/
theorem no_selfReciprocal_factor (hq5 : q % 8 = 5) {α : ℕ} (hα : 1 ≤ α)
    {p₁ p₂ : (ZMod q)[X]} (hp₁ : Irreducible p₁) (hp₂ : Irreducible p₂)
    (hf : (X ^ (2 ^ α) + 1 : (ZMod q)[X]) = p₁ * p₂) :
    Associated p₁.reverse p₂ := by
  sorry

open Polynomial in
/-- **Core unit lemma.** In `S = Z_q[X]/(X^{2^α}+1)`, every nonzero `σ_{-1}`-fixed element is a
unit. If `b = mk g` is not a unit then `g` shares a factor `p_i` with `X^{2^α}+1 = p₁p₂`; the
reverse identity plus the swap `p₁.reverse ~ p₂` force `g` to be divisible by *both* `p₁` and `p₂`,
hence by `X^{2^α}+1`, so `b = 0`. -/
theorem galoisAutₛ_fixed_isUnit (hq5 : q % 8 = 5) {α : ℕ} (hα : 1 ≤ α)
    {b : (powTwoCyclotomic (R := ZMod q) α).CyclotomicRing}
    (hbfix : galoisAutₛ α (conjExp α) (conjExp_odd α) b = b) (hb0 : b ≠ 0) :
    IsUnit b := by
  classical
  obtain ⟨p₁, p₂, hp₁, hp₂, hcop, hf⟩ := exists_irreducible_factorization q hq5 hα
  have hswap12 : Associated p₁.reverse p₂ := no_selfReciprocal_factor q hq5 hα hp₁ hp₂ hf
  have hswap21 : Associated p₂.reverse p₁ :=
    no_selfReciprocal_factor q hq5 hα hp₂ hp₁ (by rw [hf]; ring)
  set mk := Ideal.Quotient.mk (powTwoCyclotomic (R := ZMod q) α).modIdeal with hmkdef
  have hmk_zero : ∀ z : (ZMod q)[X], mk z = 0 ↔ (X ^ (2 ^ α) + 1 : (ZMod q)[X]) ∣ z := fun z => by
    rw [hmkdef, Ideal.Quotient.eq_zero_iff_mem, modIdeal, powTwoCyclotomic_toPoly,
      Ideal.mem_span_singleton]
  -- `mk X` is a unit (`(mk X)^{2^{α+1}} = 1`)
  have hmkX_unit : IsUnit (mk X) :=
    IsUnit.of_mul_eq_one ((mk X) ^ (conjExp α)) (by
      rw [mul_comm, ← pow_succ, conjExp, Nat.sub_add_cancel Nat.one_le_two_pow, ← map_pow,
        mk_X_pow_conductor_eq_one α])
  obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective b
  by_contra hbnu
  have hncop : ¬ IsCoprime g (X ^ (2 ^ α) + 1 : (ZMod q)[X]) := by
    rintro ⟨u, v, huv⟩
    refine hbnu (IsUnit.of_mul_eq_one (mk u) ?_)
    have := congrArg mk huv
    rwa [map_add, map_mul, map_mul, (hmk_zero _).mpr (dvd_refl _), mul_zero, add_zero, map_one,
      mul_comm] at this
  -- the key step: a factor `p` of `g` forces its "reverse partner" `p'` to divide `g` too
  have keystep : ∀ (p p' : (ZMod q)[X]), Associated p.reverse p' →
      p' ∣ (X ^ (2 ^ α) + 1 : (ZMod q)[X]) → p ∣ g → p' ∣ g := by
    intro p p' hpp' hp'f hpg
    have hd1 : mk p' ∣ mk p.reverse := map_dvd mk hpp'.symm.dvd
    rw [mk_reverse_eq_galoisAutₛ_mul q α p] at hd1
    have hd2 : mk p' ∣ galoisAutₛ α (conjExp α) (conjExp_odd α) (mk p) :=
      ((hmkX_unit.pow p.natDegree).dvd_mul_right).mp hd1
    have hd3 : galoisAutₛ α (conjExp α) (conjExp_odd α) (mk p) ∣ mk g := by
      obtain ⟨h, hh⟩ := hpg
      refine ⟨galoisAutₛ α (conjExp α) (conjExp_odd α) (mk h), ?_⟩
      rw [← map_mul, ← hbfix, hh, map_mul]
    obtain ⟨c, hc⟩ := hd2.trans hd3
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    have hz : (X ^ (2 ^ α) + 1 : (ZMod q)[X]) ∣ (g - p' * c') := by
      rw [← hmk_zero, map_sub, map_mul, ← hc, sub_self]
    have : p' ∣ (g - p' * c') := hp'f.trans hz
    simpa using dvd_add this (Dvd.intro c' rfl)
  rw [hf, IsCoprime.mul_right_iff, not_and_or] at hncop
  have hfg : (X ^ (2 ^ α) + 1 : (ZMod q)[X]) ∣ g := by
    rw [hf]
    rcases hncop with h1 | h2
    · have hp1g : p₁ ∣ g := by
        by_contra hnd
        exact h1 (isCoprime_comm.mp ((hp₁.coprime_iff_not_dvd).mpr hnd))
      exact hcop.mul_dvd hp1g (keystep p₁ p₂ hswap12 (hf ▸ dvd_mul_left p₂ p₁) hp1g)
    · have hp2g : p₂ ∣ g := by
        by_contra hnd
        exact h2 (isCoprime_comm.mp ((hp₂.coprime_iff_not_dvd).mpr hnd))
      exact hcop.mul_dvd (keystep p₂ p₁ hswap21 (hf ▸ dvd_mul_right p₁ p₂) hp2g) hp2g
  exact hb0 ((hmk_zero g).mpr hfg)

/-! ## Phase 5: assembling the field structure and the isomorphism -/

/-- **`R_q^{σ_{-1}}` is a field** (blueprint Theorem, Phase 5). For `q ≡ 5 (mod 8)`, every nonzero
`σ_{-1}`-fixed element is a unit: if `p₁ ∣ g` then the reverse identity plus the swap
`p₁.reverse ~ p₂` force `p₂ ∣ g` too, so `X^{2^α}+1 ∣ g` and the element vanishes.

Proven (modulo `no_selfReciprocal_factor`): transport to `S = Z_q[X]/(X^{2^α}+1)` via
`Rq.equivQuotient`, where `conjAut` becomes `galoisAutₛ` (`galoisAut_toQuotient`), and apply the
core unit lemma `galoisAutₛ_fixed_isUnit`. The inverse of a `σ_{-1}`-fixed unit is again fixed
(apply `σ_{-1}` to `a·a⁻¹ = 1` and cancel the unit). -/
theorem conjFixedSubring_isField (hq5 : q % 8 = 5) {α : ℕ} (hα : 1 ≤ α) :
    IsField (conjFixedSubring (R := ZMod q) α) := by
  haveI hntC : Nontrivial (powTwoCyclotomic (R := ZMod q) α).CyclotomicRing := by
    refine ⟨0, 1, fun h => ?_⟩
    rw [show (1 : (powTwoCyclotomic (R := ZMod q) α).CyclotomicRing)
          = Ideal.Quotient.mk _ 1 from (map_one _).symm, eq_comm,
        Ideal.Quotient.eq_zero_iff_mem, modIdeal, powTwoCyclotomic_toPoly,
        Ideal.mem_span_singleton] at h
    have hdeg := Polynomial.natDegree_le_of_dvd h one_ne_zero
    rw [Polynomial.natDegree_one, show (X ^ (2 ^ α) + 1 : (ZMod q)[X]) = X ^ (2 ^ α) + C 1 by
      rw [map_one], Polynomial.natDegree_X_pow_add_C] at hdeg
    exact absurd hdeg (Nat.not_le.mpr (by positivity))
  haveI : Nontrivial (Rq (powTwoCyclotomic (R := ZMod q) α)) := by
    refine ⟨0, 1, fun h => ?_⟩
    have h2 := congrArg (Rq.equivQuotient (powTwoCyclotomic (R := ZMod q) α)) h
    rw [map_zero, map_one] at h2
    exact zero_ne_one h2
  haveI : Nontrivial (conjFixedSubring (R := ZMod q) α) := inferInstance
  refine ⟨exists_pair_ne _, mul_comm, ?_⟩
  intro a ha
  set Ψ := Rq.equivQuotient (powTwoCyclotomic (R := ZMod q) α) with hΨ
  have haval_fix : conjAut α (a : Rq (powTwoCyclotomic (R := ZMod q) α)) = a :=
    (mem_conjFixedSubring_iff α _).mp a.property
  have haval0 : (a : Rq (powTwoCyclotomic (R := ZMod q) α)) ≠ 0 :=
    fun h => ha (Subtype.ext (by rw [h]; rfl))
  have hbfix : galoisAutₛ α (conjExp α) (conjExp_odd α) (Ψ a) = Ψ a := by
    have h1 := (galoisAut_toQuotient α (conjExp α) (conjExp_odd α)
      (a : Rq (powTwoCyclotomic (R := ZMod q) α))).symm
    have h2 : galoisAut (powTwoCyclotomic α) (conjExp α)
        (a : Rq (powTwoCyclotomic (R := ZMod q) α)) = a := by
      have h := haval_fix; rwa [conjAut, galoisRingHom_apply] at h
    rw [show Ψ (a : Rq (powTwoCyclotomic (R := ZMod q) α))
        = Rq.toQuotient _ a from rfl, h1, h2]
  have hb0 : Ψ (a : Rq (powTwoCyclotomic (R := ZMod q) α)) ≠ 0 := by
    rw [Ne, ← map_zero Ψ]; exact fun h => haval0 (Ψ.injective h)
  have hunitC := galoisAutₛ_fixed_isUnit q hq5 hα hbfix hb0
  have hunitRq : IsUnit (a : Rq (powTwoCyclotomic (R := ZMod q) α)) := by
    have := hunitC.map Ψ.symm
    rwa [Ψ.symm_apply_apply] at this
  obtain ⟨u, hu⟩ := hunitRq
  set c : Rq (powTwoCyclotomic (R := ZMod q) α) := ↑u⁻¹ with hcdef
  have hac : (a : Rq (powTwoCyclotomic (R := ZMod q) α)) * c = 1 := by
    rw [hcdef, ← hu]; exact u.mul_inv
  have hcfix : conjAut α c = c := by
    have h1 : conjAut α ((a : Rq (powTwoCyclotomic (R := ZMod q) α)) * c) = 1 := by
      rw [hac, map_one]
    rw [map_mul, haval_fix] at h1
    have h2 : (a : Rq (powTwoCyclotomic (R := ZMod q) α)) * conjAut α c
        = (a : Rq (powTwoCyclotomic (R := ZMod q) α)) * c := by rw [h1, hac]
    rw [← hu] at h2
    exact (Units.mul_right_inj u).mp h2
  exact ⟨⟨c, (mem_conjFixedSubring_iff α _).mpr hcfix⟩, Subtype.ext (by
    rw [MulMemClass.coe_mul, OneMemClass.coe_one]; exact hac)⟩

/-- **`R_q^H` is a field** (Hachi [NOZ26, §3, Lemma 5], field part). Since
`R_q^H ⊆ R_q^{σ_{-1}}` (`fixedSubring_le_conjFixedSubring`) and the latter is a field
(`conjFixedSubring_isField`), `R_q^H` is a finite integral domain, hence a field.

Proven modulo `conjFixedSubring_isField`: the inclusion `R_q^H ↪ R_q^{σ_{-1}}` is an injective
ring hom into a field, so `R_q^H` is an integral domain (`Function.Injective.isDomain`); being
finite (`fixedSubring.fintype`) it is therefore a field (`Finite.isField_of_domain`). -/
theorem fixedSubring_isField (hq5 : q % 8 = 5) {α κ : ℕ} (hα : 1 ≤ α) :
    IsField (fixedSubring (R := ZMod q) α (2 ^ κ)) := by
  have hconjF := conjFixedSubring_isField q hq5 hα
  have hle := fixedSubring_le_conjFixedSubring (R := ZMod q) α (2 ^ κ)
  -- Derive `Nontrivial`/`NoZeroDivisors` on `R_q^{σ_{-1}}` from the `IsField` *Prop* directly,
  -- avoiding the instance diamond that `IsField.toField` would create on the subring carrier.
  haveI : Nontrivial (conjFixedSubring (R := ZMod q) α) := ⟨hconjF.exists_pair_ne⟩
  haveI : NoZeroDivisors (conjFixedSubring (R := ZMod q) α) := by
    refine ⟨fun {a b} hab => ?_⟩
    by_cases ha : a = 0
    · exact Or.inl ha
    · obtain ⟨a', haa'⟩ := hconjF.mul_inv_cancel ha
      refine Or.inr ?_
      have h0 : a' * (a * b) = 0 := by rw [hab, mul_zero]
      rwa [← mul_assoc, mul_comm a' a, haa', one_mul] at h0
  -- Pull the domain structure back along the injective inclusion `R_q^H ↪ R_q^{σ_{-1}}`.
  haveI : Nontrivial (fixedSubring (R := ZMod q) α (2 ^ κ)) :=
    (Subring.inclusion hle).domain_nontrivial
  haveI : NoZeroDivisors (fixedSubring (R := ZMod q) α (2 ^ κ)) :=
    Function.Injective.noZeroDivisors (Subring.inclusion hle) (Subring.inclusion_injective hle)
      (Subring.inclusion hle).map_zero (fun x y => (Subring.inclusion hle).map_mul x y)
  haveI : IsDomain (fixedSubring (R := ZMod q) α (2 ^ κ)) := NoZeroDivisors.to_isDomain _
  exact Finite.isField_of_domain _

/-- **Hachi [NOZ26, §3, Lemma 5]: `R_q^H ≅ F_{q^k}`.** For `q ≡ 5 (mod 8)` and `2·2^κ ∣ 2^α`,
the fixed subring is ring-isomorphic to `GaloisField q (2^κ)` (`= F_{q^{2^κ}}`). Combines
`fixedSubring_isField` with `card_fixedSubring_eq` (`|R_q^H| = q^{2^κ}`) and the classification of
finite fields by cardinality.

Proven modulo `conjFixedSubring_isField` (via `fixedSubring_isField`): equip `R_q^H` with the
field structure from `fixedSubring_isField`, compute both cardinalities as `q^{2^κ}`
(`card_fixedSubring_eq` and `GaloisField.card`), and invoke the uniqueness of finite fields
(`FiniteField.ringEquivOfCardEq`). -/
theorem fixedSubringEquivGaloisField (hq5 : q % 8 = 5) {α κ : ℕ} (hα : 1 ≤ α)
    (hk : 2 * 2 ^ κ ∣ 2 ^ α) :
    Nonempty (fixedSubring (R := ZMod q) α (2 ^ κ) ≃+* GaloisField q (2 ^ κ)) := by
  have hq2 : ¬ (q ∣ 2) := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have h2 : (2 : ZMod q) ≠ 0 := by
    have h2' : ((2 : ℕ) : ZMod q) ≠ 0 := by rw [Ne, ZMod.natCast_eq_zero_iff]; exact hq2
    simpa using h2'
  letI : Field (fixedSubring (R := ZMod q) α (2 ^ κ)) := (fixedSubring_isField q hq5 hα).toField
  haveI : Fintype (GaloisField q (2 ^ κ)) := Fintype.ofFinite _
  have hcardK : Fintype.card (fixedSubring (R := ZMod q) α (2 ^ κ)) = q ^ 2 ^ κ := by
    rw [card_fixedSubring_eq q α κ h2 hk, ZMod.card q]
  have hcardG : Fintype.card (GaloisField q (2 ^ κ)) = q ^ 2 ^ κ := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card q (2 ^ κ) (by positivity)]
  exact ⟨FiniteField.ringEquivOfCardEq (hcardK.trans hcardG.symm)⟩

end ArkLib.Lattices.CyclotomicModulus
