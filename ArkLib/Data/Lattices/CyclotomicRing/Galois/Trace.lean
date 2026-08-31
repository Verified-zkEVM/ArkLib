/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Data.Lattices.CyclotomicRing.Galois.Group

/-!
# The Trace Map `Tr_H`

For a subgroup `H` of Galois automorphisms, the relative trace is `Tr_H(a) := Σ_{σ ∈ H} σ(a)`.
Hachi [NOZ26, §3] uses `Tr_H` (for `H = ⟨σ_{-1}, σ_{4k+1}⟩`) to express inner products over the
subfield `F_{q^k} ≅ R_q^H` as relations over `R_q` (Theorem 2).

Computably, the trace is the finite sum of the automorphism actions over the exponent set `Hexp`.
It is additive (proven here, from additivity of `galoisAut`). Its image lands in the fixed subring
`R_q^H` (`traceH_mem_fixed`); the diagonal value `(d/k)·id` driving Theorem 2 is established in
`Subfield/TraceVanishing.lean` and `Subfield/TraceInnerProduct.lean`.

## Main definitions

* `traceOver Φ S` — `Σ_{i ∈ S} σ_i`, the trace over an arbitrary exponent set.
* `traceH α k` — the trace `Tr_H` over `H = ⟨σ_{-1}, σ_{4k+1}⟩`.

## References

* [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi …*][NOZ26]
-/

open CompPoly Finset

namespace ArkLib.Lattices.CyclotomicModulus

variable {R : Type*} [Field R] [BEq R] [LawfulBEq R] [DecidableEq R]
variable (Φ : CyclotomicModulus R) [IsCyclotomic Φ]

/-- The **trace over an exponent set** `S`: `Σ_{i ∈ S} σ_i(a)`.

Noncomputable as stated, since `Finset.sum` routes through `Rq`'s (transported, noncomputable)
`CommRing`. The computable counterpart is `traceOverComp` (equal by `traceOverComp_eq`); the
underlying automorphism action `galoisAut` is itself computable. -/
noncomputable def traceOver (S : Finset ℕ) (a : Rq Φ) : Rq Φ := ∑ i ∈ S, galoisAut Φ i a

@[simp] theorem traceOver_zero (S : Finset ℕ) : traceOver Φ S 0 = 0 := by
  unfold traceOver
  simp only [galoisAut_zero, Finset.sum_const_zero]

/-- The trace is additive. -/
theorem traceOver_add (S : Finset ℕ) (a b : Rq Φ) :
    traceOver Φ S (a + b) = traceOver Φ S a + traceOver Φ S b := by
  unfold traceOver
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun i _ => galoisAut_add Φ i a b)

/-- The **computable trace** over an exponent set `S`. The monomial remap is summed at the
`CPolynomial` level — whose ring structure is computable, unlike `Rq`'s transported one — and
reduced once at the end. Equal to `traceOver` (`traceOverComp_eq`). -/
def traceOverComp (S : Finset ℕ) (a : Rq Φ) : Rq Φ :=
  Rq.mk Φ (∑ i ∈ S, ∑ k ∈ Finset.range Φ.φ.natDegree,
    CompPoly.CPolynomial.monomial (k * i) (a.1.coeff k))

/-- The computable trace agrees with `traceOver`. -/
theorem traceOverComp_eq (S : Finset ℕ) (a : Rq Φ) : traceOverComp Φ S a = traceOver Φ S a := by
  rw [traceOverComp, Rq.mk_sum]
  simp only [traceOver, galoisAut]

/-- The **trace map `Tr_H`** for `H = ⟨σ_{-1}, σ_{4k+1}⟩`. -/
noncomputable def traceH (α k : ℕ) (a : Rq (powTwoCyclotomic (R := R) α)) :
    Rq (powTwoCyclotomic (R := R) α) :=
  traceOver (powTwoCyclotomic α) (Hexp α k) a

/-- The **computable** trace map `Tr_H`, equal to `traceH` (`traceHComp_eq`). -/
def traceHComp (α k : ℕ) (a : Rq (powTwoCyclotomic (R := R) α)) :
    Rq (powTwoCyclotomic (R := R) α) :=
  traceOverComp (powTwoCyclotomic α) (Hexp α k) a

/-- The computable `Tr_H` agrees with `traceH`. -/
theorem traceHComp_eq (α k : ℕ) (a : Rq (powTwoCyclotomic (R := R) α)) :
    traceHComp α k a = traceH α k a :=
  traceOverComp_eq _ _ _

/-- If multiplication by `g` permutes `Hexp` (`Hexp_generator_smul`), then `σ_g` fixes `Tr_H`.
The per-term step uses `σ_g(σ_i a) = σ_{g·i} a = σ_{(g·i) mod 2^{α+1}} a` (composition +
exponent-periodicity, both proven); the sum then reindexes along the permutation. -/
theorem traceH_fixed_of_smul (α k g : ℕ) (hg : Odd g)
    (himg : (Hexp α k).image (fun i => (g * i) % 2 ^ (α + 1)) = Hexp α k)
    (a : Rq (powTwoCyclotomic (R := R) α)) :
    galoisRingHom α g hg (traceH α k a) = traceH α k a := by
  have hodd := Hexp_odd_mem α k
  have hinj : Set.InjOn (fun i => (g * i) % 2 ^ (α + 1)) (Hexp α k) :=
    Finset.injOn_of_card_image_eq (by rw [himg])
  unfold traceH traceOver
  rw [map_sum,
    Finset.sum_congr rfl fun i hi => by
      rw [galoisRingHom_apply, galoisAut_comp α g i hg (hodd i hi), galoisAut_periodic]]
  conv_rhs => rw [← himg]
  rw [Finset.sum_image fun x hx y hy h => hinj hx hy h]

/-- `Tr_H` is fixed by both generators of `H`, hence lands in the fixed subring `R_q^H`.

The hypotheses match `Hexp_card` (`k` a power of two dividing `d/2`): they are needed for `Hexp`
to genuinely enumerate the subgroup `H = ⟨σ_{-1}, σ_{4k+1}⟩`. Reduced to the permutation lemma
`Hexp_generator_smul` (the open group-theoretic core); the rest is fully proven. -/
theorem traceH_mem_fixed (α k : ℕ) (hk2pow : ∃ κ, k = 2 ^ κ) (hk : 2 * k ∣ 2 ^ α)
    (a : Rq (powTwoCyclotomic (R := R) α)) :
    conjAut α (traceH α k a) = traceH α k a ∧ genAut α k (traceH α k a) = traceH α k a :=
  ⟨traceH_fixed_of_smul α k (conjExp α) (conjExp_odd α)
      (Hexp_generator_smul α k (conjExp α) hk2pow hk (Or.inl rfl)) a,
    traceH_fixed_of_smul α k (genExp k) (genExp_odd k)
      (Hexp_generator_smul α k (genExp k) hk2pow hk (Or.inr rfl)) a⟩

end ArkLib.Lattices.CyclotomicModulus
