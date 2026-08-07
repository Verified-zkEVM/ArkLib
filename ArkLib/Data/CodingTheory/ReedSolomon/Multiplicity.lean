/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/

import ArkLib.Data.CodingTheory.ReedSolomon
import Mathlib.Algebra.Polynomial.Derivative

/-!
# Univariate multiplicity codes (ABF26 Definition A.7)

The univariate multiplicity code packs the evaluations of a polynomial
**and its first `s − 1` formal derivatives** at each domain point into
a length-`s` symbol, mirroring how folded Reed-Solomon codes pack
`s` consecutive evaluations on a multiplicative orbit. Originally
introduced in [GW13] and analysed in detail in [KSY14]; ABF26 §A.2
records the definition in the context of the toy-problem
parametrisations.

## Notation

For `f̂ ∈ F^{<k}[X]`, write `f̂^(j)` for the `j`-th formal derivative.
Then

  `UM[F, L, k, s] := { f : L → F^s | ∃ f̂ ∈ F^{<k}[X],`
  `                     ∀ x ∈ L, f(x) = (f̂^{(0)}(x), …, f̂^{(s-1)}(x)) }`.

For `s = 1`, this degenerates to the plain Reed-Solomon code
`RS[F, L, k]` (see `mem_umCode_one_iff_mem_rsCode`).

**Characteristic condition.** For `s ≥ 2`, the paper's A.7 requires
`char(F) ≥ k` so that the derivative-of-monomial coefficients
`(a_i · i)` do not vanish below degree `k` (without this, multiple
distinct polynomials of degree `< k` can fold to the same multiplicity
codeword, and the dimension claim collapses). The bare encoder
`umEvalOnPoints` is well-typed in any `CommRing F` — we keep the
hypothesis as a downstream caller's responsibility rather than baking
it into the definition, since the `s = 1` collapse lemma below works
unconditionally.

## Layout

* `umEvalOnPoints` — the encoder, as an `F`-linear map from polynomials
  to multiplicity codewords.
* `umCode` — the multiplicity code as an `F`-submodule of `ι → Fin s → F`.

Sanity lemmas:

* `mem_umCode_one_iff_mem_rsCode` — `UM[F, L, k, 1]` collapses to
  `RS[F, L, k]` (modulo the `Fin 1 → F` ≃ `F` reshaping).

## References

* [Arnon, G., Boneh, D., Fenzi, G., *Open Problems in List Decoding and
  Correlated Agreement*][ABF26] (§A.2, Definitions A.6, A.7).
* [GW13] Guruswami-Wang. *Linear-algebraic list decoding for
  variants of Reed-Solomon codes.*
* [KSY14] Kopparty-Saraf-Yekhanin. *High-rate codes with sublinear-time
  decoding.*
-/

namespace ReedSolomon

namespace Multiplicity

variable {ι : Type*} [Fintype ι]
variable {F : Type*} [CommRing F]

/-- The univariate multiplicity-code evaluation map: send a polynomial
`p` to the matrix `(p^{(j)}(domain x))_{x ∈ ι, j ∈ Fin s}` packaging the
first `s` formal derivatives of `p` evaluated on the domain.

`F`-linear by construction: each entry is `c ↦ (derivative^[j] c).eval (domain x)`,
and both `Polynomial.derivative` (iterated) and `Polynomial.eval ·` are
`F`-linear (the latter as a function of the polynomial).

Mirrors `ReedSolomon.evalOnPoints` (the `s = 1` case) and the FRS encoder
`ReedSolomon.Folded.frsEvalOnPoints`. -/
noncomputable def umEvalOnPoints (domain : ι ↪ F) (s : ℕ) :
    Polynomial F →ₗ[F] (ι → Fin s → F) where
  toFun p := fun x j ↦ (Polynomial.derivative^[j.val] p).eval (domain x)
  map_add' p q := by
    ext x j
    simp [Polynomial.eval_add]
  map_smul' c p := by
    ext x j
    simp [Polynomial.eval_smul]

/-- **ABF26 Definition A.7 [GW13, KSY14]** — the univariate multiplicity
code `UM[F, L, k, s]`.

Defined as the image of `Polynomial.degreeLT F k` under
`umEvalOnPoints`, exactly mirroring the structure of `ReedSolomon.code`
and `ReedSolomon.Folded.frsCode`. This makes `umCode` an
`F`-submodule of `ι → Fin s → F`. -/
noncomputable def umCode (domain : ι ↪ F) (k s : ℕ) :
    Submodule F (ι → Fin s → F) :=
  (Polynomial.degreeLT F k).map (umEvalOnPoints domain s)

end Multiplicity

/-- **Sanity check: `UM[F, L, k, 1]` ↔ `RS[F, L, k]`.** With `s = 1`,
the only fold index is `0 : Fin 1`, and `Polynomial.derivative^[0]` is
the identity, so each multiplicity codeword reduces to a plain RS
codeword. Stated as an iff between memberships (the LHS lives in
`ι → Fin 1 → F`, the RHS in `ι → F`, avoiding the cross-type equality
issue).

Stated outside the `Multiplicity` namespace's `[CommRing F]` section to
sidestep the `Polynomial`-Semiring instance clash between `CommRing.to…`
and `Field.to…`: when both are in scope, the `umCode`-side polynomial
type is incommensurate with the `ReedSolomon.code`-side one. -/
lemma Multiplicity.mem_umCode_one_iff_mem_rsCode
    {ι : Type*} {F : Type*} [Field F]
    (domain : ι ↪ F) (k : ℕ) (f : ι → Fin 1 → F) :
    f ∈ Multiplicity.umCode domain k 1 ↔
      (fun i ↦ f i 0) ∈ ReedSolomon.code domain k := by
  simp only [Multiplicity.umCode, Multiplicity.umEvalOnPoints,
    ReedSolomon.code, ReedSolomon.evalOnPoints,
    Submodule.mem_map, LinearMap.coe_mk, AddHom.coe_mk]
  constructor
  · rintro ⟨p, hp, hf⟩
    refine ⟨p, hp, ?_⟩
    funext i
    have := congrFun (congrFun hf i) (0 : Fin 1)
    simpa using this
  · rintro ⟨p, hp, hp_eval⟩
    refine ⟨p, hp, ?_⟩
    funext i j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    have := congrFun hp_eval i
    simpa using this

end ReedSolomon
