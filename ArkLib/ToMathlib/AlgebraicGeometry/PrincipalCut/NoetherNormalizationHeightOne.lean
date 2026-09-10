/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
module


public import ArkLib.ToMathlib.AlgebraicGeometry.PrincipalCut.Dimension
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.Finiteness.Quotient
public import Mathlib.RingTheory.Ideal.Quotient.PowTransition
public import Mathlib.RingTheory.Polynomial.IsIntegral

/-!
# Height-one primes under Noether normalization

For a finite injective normalization map from a polynomial ring into a finite-type domain, a
height-one prime contracts to a nonzero principal height-one prime.  The induced map on the two
prime quotients remains finite and injective.  This is the commutative-algebra seam needed to
compare their concrete Hilbert growth.
-/

@[expose] public section

noncomputable section

namespace AffineHilbert

variable {F A : Type*} [Field F] [CommRing A] [IsDomain A] [Algebra F A]

/-- The contraction and quotient data attached to a height-one prime under a polynomial
normalization map. -/
structure NormalizationHeightOneData {d : ℕ} (g : MvPolynomial (Fin d) F →ₐ[F] A)
    (Q : Ideal A) : Prop where
  contraction_isPrime : (Q.comap g).IsPrime
  contraction_ne_bot : Q.comap g ≠ ⊥
  contraction_height : (Q.comap g).height = 1
  contraction_isPrincipal : (Q.comap g).IsPrincipal
  quotientMap_injective : Function.Injective
    (Ideal.quotientMap (I := Q.comap g) Q g.toRingHom le_rfl)
  quotientMap_finite :
    (Ideal.quotientMap (I := Q.comap g) Q g.toRingHom le_rfl).Finite

/-- Regard a normalization map as a map from the coordinate quotient by the zero ideal. -/
def normalizationBotMap {d : ℕ} (g : MvPolynomial (Fin d) F →ₐ[F] A) :
    (MvPolynomial (Fin d) F ⧸ (⊥ : Ideal (MvPolynomial (Fin d) F))) →ₐ[F] A :=
  g.comp (AlgEquiv.quotientBot F (MvPolynomial (Fin d) F)).toAlgHom

omit [IsDomain A] in
/-- The coordinate-quotient form of an injective normalization remains injective. -/
theorem normalizationBotMap_injective {d : ℕ} {g : MvPolynomial (Fin d) F →ₐ[F] A}
    (hg : Function.Injective g) : Function.Injective (normalizationBotMap g) :=
  hg.comp (AlgEquiv.quotientBot F (MvPolynomial (Fin d) F)).injective

omit [IsDomain A] in
/-- The coordinate-quotient form of a finite normalization remains finite. -/
theorem normalizationBotMap_finite {d : ℕ} {g : MvPolynomial (Fin d) F →ₐ[F] A}
    (hg : g.toRingHom.Finite) : (normalizationBotMap g).toRingHom.Finite := by
  exact RingHom.Finite.comp hg (AlgEquiv.quotientBot F (MvPolynomial (Fin d) F)).toRingEquiv.finite

omit [IsDomain A] in
/-- Choose a nonzero proper principal generator for the contracted height-one prime. -/
theorem NormalizationHeightOneData.exists_contraction_generator
    {d : ℕ} {g : MvPolynomial (Fin d) F →ₐ[F] A} {Q : Ideal A}
    (h : NormalizationHeightOneData g Q) :
    ∃ a : MvPolynomial (Fin d) F,
      a ≠ 0 ∧ Ideal.span {a} ≠ ⊤ ∧ Q.comap g = Ideal.span {a} := by
  let _ : (Q.comap g).IsPrincipal := h.contraction_isPrincipal
  obtain ⟨a, ha⟩ := Submodule.IsPrincipal.principal (Q.comap g)
  have ha' : Q.comap g = Ideal.span {a} := ha.trans Ideal.submodule_span_eq
  refine ⟨a, ?_, ?_, ?_⟩
  · intro ha0
    apply h.contraction_ne_bot
    rw [ha', ha0]
    simp
  · rw [← ha']
    exact h.contraction_isPrime.ne_top
  · exact ha'

/-- Reindex the finite quotient map by a chosen principal generator of the contraction. -/
def normalizationPrincipalQuotientMap {d : ℕ}
    (g : MvPolynomial (Fin d) F →ₐ[F] A) (Q : Ideal A)
    (a : MvPolynomial (Fin d) F) (ha : Q.comap g = Ideal.span {a}) :
    (MvPolynomial (Fin d) F ⧸ Ideal.span {a}) →ₐ[F] (A ⧸ Q) :=
  (Ideal.quotientMapₐ Q g le_rfl).comp
    (Ideal.quotientEquivAlgOfEq F ha.symm).toAlgHom

omit [IsDomain A] in
/-- The principal-generator reindexing preserves injectivity of the quotient map. -/
theorem normalizationPrincipalQuotientMap_injective {d : ℕ}
    {g : MvPolynomial (Fin d) F →ₐ[F] A} {Q : Ideal A}
    (h : NormalizationHeightOneData g Q) {a : MvPolynomial (Fin d) F}
    (ha : Q.comap g = Ideal.span {a}) :
    Function.Injective (normalizationPrincipalQuotientMap g Q a ha) :=
  h.quotientMap_injective.comp (Ideal.quotientEquivAlgOfEq F ha.symm).injective

omit [IsDomain A] in
/-- The principal-generator reindexing preserves finiteness of the quotient map. -/
theorem normalizationPrincipalQuotientMap_finite {d : ℕ}
    {g : MvPolynomial (Fin d) F →ₐ[F] A} {Q : Ideal A}
    (h : NormalizationHeightOneData g Q) {a : MvPolynomial (Fin d) F}
    (ha : Q.comap g = Ideal.span {a}) :
    (normalizationPrincipalQuotientMap g Q a ha).toRingHom.Finite := by
  exact RingHom.Finite.comp h.quotientMap_finite
    (Ideal.quotientEquivAlgOfEq F ha.symm).toRingEquiv.finite

/-- Quotienting the parent coordinate ring by the image of a larger ideal recovers the larger
coordinate quotient. -/
def parentComponentQuotientEquiv
    {F σ : Type*} [Field F] {P J : Ideal (MvPolynomial σ F)} (hPJ : P ≤ J) :
    ((MvPolynomial σ F ⧸ P) ⧸ J.map (Ideal.Quotient.mk P)) ≃ₐ[F]
      (MvPolynomial σ F ⧸ J) :=
  (Ideal.quotientEquivAlgOfEq F (Ideal.Quotient.factor_ker hPJ).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective
      (f := Ideal.Quotient.factorₐ F hPJ) (Ideal.Quotient.factor_surjective hPJ))

/-- The direct coordinate-quotient map from a principal normalization hypersurface to a child
component quotient. -/
def normalizationChildMap
    {F σ : Type*} [Field F] {P J : Ideal (MvPolynomial σ F)} (hPJ : P ≤ J)
    {d : ℕ} (g : MvPolynomial (Fin d) F →ₐ[F] (MvPolynomial σ F ⧸ P))
    (a : MvPolynomial (Fin d) F)
    (ha : (J.map (Ideal.Quotient.mk P)).comap g = Ideal.span {a}) :
    (MvPolynomial (Fin d) F ⧸ Ideal.span {a}) →ₐ[F] (MvPolynomial σ F ⧸ J) :=
  (parentComponentQuotientEquiv hPJ).toAlgHom.comp
    (normalizationPrincipalQuotientMap g (J.map (Ideal.Quotient.mk P)) a ha)

/-- The direct child coordinate-quotient map is finite. -/
theorem normalizationChildMap_finite
    {F σ : Type*} [Field F] {P J : Ideal (MvPolynomial σ F)} {hPJ : P ≤ J}
    {d : ℕ} {g : MvPolynomial (Fin d) F →ₐ[F] (MvPolynomial σ F ⧸ P)}
    (h : NormalizationHeightOneData g (J.map (Ideal.Quotient.mk P)))
    {a : MvPolynomial (Fin d) F}
    (ha : (J.map (Ideal.Quotient.mk P)).comap g = Ideal.span {a}) :
    (normalizationChildMap hPJ g a ha).toRingHom.Finite := by
  convert! (parentComponentQuotientEquiv hPJ).toRingEquiv.finite.comp
    (normalizationPrincipalQuotientMap_finite h ha)

/-- The direct child coordinate-quotient map is injective. -/
theorem normalizationChildMap_injective
    {F σ : Type*} [Field F] {P J : Ideal (MvPolynomial σ F)} {hPJ : P ≤ J}
    {d : ℕ} {g : MvPolynomial (Fin d) F →ₐ[F] (MvPolynomial σ F ⧸ P)}
    (h : NormalizationHeightOneData g (J.map (Ideal.Quotient.mk P)))
    {a : MvPolynomial (Fin d) F}
    (ha : (J.map (Ideal.Quotient.mk P)).comap g = Ideal.span {a}) :
    Function.Injective (normalizationChildMap hPJ g a ha) :=
  (parentComponentQuotientEquiv hPJ).injective.comp
    (normalizationPrincipalQuotientMap_injective h ha)

/-- A height-one prime in a domain finite over a polynomial ring contracts to a nonzero principal
height-one prime, and the induced quotient extension is finite and injective. -/
theorem normalization_contraction_height_one
    {d : ℕ} (g : MvPolynomial (Fin d) F →ₐ[F] A)
    (hg_inj : Function.Injective g) (hg_fin : g.toRingHom.Finite)
    (Q : Ideal A) [Q.IsPrime] (hQ : Q.height = 1) :
    NormalizationHeightOneData g Q := by
  let B := MvPolynomial (Fin d) F
  let _ : Algebra B A := g.toRingHom.toAlgebra
  have halg : algebraMap B A = g.toRingHom := rfl
  let q : Ideal B := Q.comap (algebraMap B A)
  let _ : q.IsPrime := Ideal.comap_isPrime (algebraMap B A) Q
  let _ : Q.LiesOver q := ⟨rfl⟩
  let _ : Module.Finite B A := hg_fin
  let _ : Algebra.IsIntegral B A := ⟨hg_fin.to_isIntegral⟩
  let _ : IsIntegrallyClosed B := UniqueFactorizationMonoid.instIsIntegrallyClosed
  let _ : IsNoetherianRing A := IsNoetherianRing.of_finite B A
  let _ : FaithfulSMul B A :=
    (faithfulSMul_iff_algebraMap_injective B A).mpr (halg.symm ▸ hg_inj)
  have hQne : Q ≠ ⊥ := Ideal.ne_bot_of_height_eq_one hQ
  have hbotQ : (⊥ : Ideal A) < Q := bot_lt_iff_ne_bot.mpr hQne
  have hqpos : (⊥ : Ideal B) < q := by
    have hstrict := Ideal.IsIntegral.comap_lt_comap (R := B) hbotQ
    rw [Ideal.comap_bot_of_injective (algebraMap B A)
      (FaithfulSMul.algebraMap_injective B A)] at hstrict
    exact hstrict
  have hqne : q ≠ ⊥ := ne_of_gt hqpos
  have hqle : q.height ≤ 1 := by
    calc
      q.height ≤ q.height +
          (Q.map (Ideal.Quotient.mk (q.map (algebraMap B A)))).height := le_add_right le_rfl
      _ = Q.height := (Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown q Q).symm
      _ = 1 := hQ
  have hqheight : q.height = 1 := by
    apply le_antisymm hqle
    rw [Order.one_le_iff_ne_zero]
    exact fun hz ↦ hqne (Ideal.height_eq_zero_iff_eq_bot.mp hz)
  have hqprincipal : q.IsPrincipal :=
    UniqueFactorizationMonoid.isPrincipal_of_height_eq_one hqheight
  refine ⟨inferInstance, hqne, hqheight, hqprincipal, ?_, ?_⟩
  · exact Ideal.quotientMap_injective
  · change (algebraMap (B ⧸ q) (A ⧸ Q)).Finite
    rw [RingHom.finite_algebraMap]
    infer_instance

/-- Noether normalization supplies a finite injective polynomial subalgebra whose contraction of
a prescribed height-one prime is nonzero, principal, and height one.  The quotient extension is
again finite and injective. -/
theorem exists_normalization_contraction_height_one [Algebra.FiniteType F A]
    (Q : Ideal A) [Q.IsPrime] (hQ : Q.height = 1) :
    ∃ (d : ℕ) (g : MvPolynomial (Fin d) F →ₐ[F] A),
      Function.Injective g ∧ g.toRingHom.Finite ∧ NormalizationHeightOneData g Q := by
  obtain ⟨d, g, hg_inj, hg_fin⟩ := exists_finite_inj_algHom_of_fg F A
  exact ⟨d, g, hg_inj, hg_fin,
    normalization_contraction_height_one g hg_inj hg_fin Q hQ⟩

/-- Apply Noether normalization directly to a minimal component of a principal cut in an affine
prime quotient.  The component becomes a height-one prime in the quotient, and its contraction
to the normalization polynomial ring is a nonzero principal height-one prime with finite
injective quotient extension. -/
theorem principalCut_component_exists_normalization_contraction
    {F σ : Type*} [Field F] [Finite σ]
    {P J : Ideal (MvPolynomial σ F)} (hP : P.IsPrime) {f : MvPolynomial σ F}
    (hf : f ∉ P) (hJ : J ∈ (P ⊔ Ideal.span {f}).minimalPrimes) :
    let A := MvPolynomial σ F ⧸ P
    let Q := J.map (Ideal.Quotient.mk P)
    ∃ (d : ℕ) (g : MvPolynomial (Fin d) F →ₐ[F] A),
      Function.Injective g ∧ g.toRingHom.Finite ∧ NormalizationHeightOneData g Q := by
  let _ : P.IsPrime := hP
  let _ : J.IsPrime := hJ.isPrime
  let A := MvPolynomial σ F ⧸ P
  let Q : Ideal A := J.map (Ideal.Quotient.mk P)
  let _ : Q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
    rw [Ideal.mk_ker]
    exact le_sup_left.trans hJ.le)
  have hQ : Q.height = 1 :=
    Ideal.map_quotient_height_eq_one_of_mem_minimalPrimes_sup_span hP hf hJ
  exact exists_normalization_contraction_height_one Q hQ

/-- Coordinate-quotient form of normalization for a principal-cut component.  The parent map has
source `F[Fin d] / ⊥`; the child map has source a proper nonzero hypersurface quotient
`F[Fin d] / (a)` and target the original component quotient. -/
theorem principalCut_component_exists_coordinate_normalization
    {F σ : Type*} [Field F] [Finite σ]
    {P J : Ideal (MvPolynomial σ F)} (hP : P.IsPrime) {f : MvPolynomial σ F}
    (hf : f ∉ P) (hJ : J ∈ (P ⊔ Ideal.span {f}).minimalPrimes) :
    let A := MvPolynomial σ F ⧸ P
    let Q := J.map (Ideal.Quotient.mk P)
    let hPJ : P ≤ J := le_sup_left.trans hJ.le
    ∃ (d : ℕ) (g : MvPolynomial (Fin d) F →ₐ[F] A)
        (a : MvPolynomial (Fin d) F)
        (ha : Q.comap g = Ideal.span {a}),
      Function.Injective g ∧ g.toRingHom.Finite ∧
        a ≠ 0 ∧ Ideal.span {a} ≠ ⊤ ∧
        Function.Injective (normalizationBotMap g) ∧
        (normalizationBotMap g).toRingHom.Finite ∧
        Function.Injective (normalizationChildMap hPJ g a ha) ∧
        (normalizationChildMap hPJ g a ha).toRingHom.Finite ∧
        NormalizationHeightOneData g Q := by
  let _ : P.IsPrime := hP
  let _ : J.IsPrime := hJ.isPrime
  let A := MvPolynomial σ F ⧸ P
  let Q : Ideal A := J.map (Ideal.Quotient.mk P)
  let _ : Q.IsPrime := Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by
    rw [Ideal.mk_ker]
    exact le_sup_left.trans hJ.le)
  have hQ : Q.height = 1 :=
    Ideal.map_quotient_height_eq_one_of_mem_minimalPrimes_sup_span hP hf hJ
  obtain ⟨d, g, hg_inj, hg_fin, hdata⟩ :=
    exists_normalization_contraction_height_one (F := F) (A := A) Q hQ
  obtain ⟨a, ha0, haproper, ha⟩ := hdata.exists_contraction_generator
  refine ⟨d, g, a, ha, hg_inj, hg_fin, ha0, haproper,
    normalizationBotMap_injective hg_inj, normalizationBotMap_finite hg_fin,
    normalizationChildMap_injective hdata ha, normalizationChildMap_finite hdata ha, hdata⟩

end AffineHilbert
