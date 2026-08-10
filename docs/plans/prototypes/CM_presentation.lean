/-
PROTOTYPE: the computable presentation layer (Phase 6 of the plan).

Kills the one non-`sorry` computability blocker outside the extractor notion:
`cyclotomicPresentation` is `noncomputable` only because `Lift.Presentation` carries Mathlib
`Polynomial` data fields, and it is a *kept argument* of `Lift.package`, so `liftPackage`,
`openCore` and `openingChain` can never gain IR while it stands.

The rewrite is a data/laws split, NOT an adapter: `Presentation` keeps its name and fields but
carries **computable** polynomials (`CPolynomial`), and `IsPresentation` states the laws as the
**Mathlib semantics of that data** — via `toPoly` — exactly the `CyclotomicModulus`/`IsCyclotomic`
idiom the structure's own docstring says it mirrors (`IsCyclotomic.monic : Φ.φ.toPoly.Monic`).
`LiftedWitness.ρ` moves to `CPolynomial` the same way, which also removes the constructibility
barrier (no Mathlib `Polynomial` value is constructible at all — even `0` fails codegen on
`Polynomial.instZero`).

What is machine-checked here:
  A  the new `Presentation`/`IsPresentation` (computable data, `toPoly` laws);
  B  the ENTIRE proof engine of `Lift/Presentation.lean` transcribes mechanically —
     every occurrence of `P.modulus` becomes `P.modulus.toPoly` and `P.rep x` becomes
     `(P.rep x).toPoly`, and every proof survives verbatim (the proofs treat these as opaque
     `Polynomial` terms and never unfold the fields);
  C  the retyped `LiftedWitness` + `checkAt` + `relLin` + the full `recover` theorem
     ([NOZ26] Lemma 9's generic recovery) at the new structures;
  D  the cyclotomic instance: `cyclotomicPresentation := { modulus := Φ.φ, rep := fun a => a.1 }`
     is a plain `def` (pure projections), and `isPresentation_cyclotomic` is discharged from the
     SAME QuotientLift bridge lemmas as today — `val_toPoly_injective`,
     `modulus_dvd_toPoly_add_sub`, `modulus_dvd_toPoly_mul_sub` verbatim;
  E  the package-shaped IR gate, positive AND negative control: a `liftPackage`-shaped consumer
     retaining the presentation as an argument has IR at the new structure, and the same
     construction over a Mathlib-typed presentation has NO IR (today's failure, reproduced);
  F  runtime: a concrete modulus (`X² + 1` over `ZMod 17`), a concrete `Rq` element, and a
     concrete `LiftedWitness` all construct and `#eval` — the values that were previously
     unconstructible.
-/
import ArkLib.Data.Lattices.CyclotomicRing.QuotientLift
import ArkLib.Data.Lattices.Vectors
import ArkLib.ProofSystem.RingSwitching.Transport.Eval
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic.LinearCombination

open Polynomial ArkLib.Lattices CompPoly RingSwitching ArkLib.Lattices.CyclotomicModulus

namespace CMP

/-! ## Part A — the structures: computable data, `toPoly` laws -/

/-- Proof-free presentation data for a ring `S` as a quotient `R[X]/(φ)`, over **computable**
polynomials. Same name, same fields as today's `Lift.Presentation`; only the carrier changes
(`Polynomial R` → `CPolynomial R`). The laws live in `IsPresentation` and speak about the
`toPoly` semantics of these fields, mirroring `CyclotomicModulus`/`IsCyclotomic`. -/
structure Presentation (R S : Type*) [CommRing R] [CommRing S] where
  /-- The modulus polynomial presenting `S`, e.g. `X^d + 1`. -/
  modulus : CPolynomial R
  /-- Canonical (degree-reduced) representative of a ring element. -/
  rep : S → CPolynomial R

/-- The presentation laws, stated as the Mathlib semantics (`toPoly`) of the computable data —
the `IsCyclotomic` idiom. Note `rep_injective` is injectivity of the *semantic* representative
`s ↦ (P.rep s).toPoly`, which is what the engine consumes and what the cyclotomic instance's
`val_toPoly_injective` provides verbatim (it implies injectivity of `P.rep` itself). -/
class IsPresentation {R S : Type*} [CommRing R] [CommRing S]
    (P : Presentation R S) : Prop where
  /-- The modulus is monic (so division with remainder applies). -/
  monic : P.modulus.toPoly.Monic
  /-- Representatives are degree-reduced. In particular the modulus has positive degree. -/
  natDegree_rep_lt : ∀ s : S, (P.rep s).toPoly.natDegree < P.modulus.toPoly.natDegree
  /-- Distinct elements have distinct (semantic) representatives. -/
  rep_injective : Function.Injective (fun s : S => (P.rep s).toPoly)
  /-- Coset law for addition. -/
  modulus_dvd_rep_add : ∀ a b : S,
    P.modulus.toPoly ∣ (P.rep (a + b)).toPoly - ((P.rep a).toPoly + (P.rep b).toPoly)
  /-- Coset law for multiplication. -/
  modulus_dvd_rep_mul : ∀ a b : S,
    P.modulus.toPoly ∣ (P.rep (a * b)).toPoly - (P.rep a).toPoly * (P.rep b).toPoly

/-! ## Part B — the proof engine, transcribed mechanically

Every theorem below is `Lift/Presentation.lean`'s, under the rename `P.modulus ↦
P.modulus.toPoly`, `P.rep x ↦ (P.rep x).toPoly`. The proofs are verbatim. -/

namespace Presentation

variable {R S : Type*} [CommRing R] [CommRing S] (P : Presentation R S) [IsPresentation P]

/-- The modulus has positive degree: even `0` has a representative of smaller degree. -/
theorem natDegree_modulus_pos : 0 < P.modulus.toPoly.natDegree :=
  Nat.lt_of_le_of_lt (Nat.zero_le _) (IsPresentation.natDegree_rep_lt (P := P) 0)

/-- The representative of `0` is a multiple of the modulus. -/
theorem modulus_dvd_rep_zero : P.modulus.toPoly ∣ (P.rep 0).toPoly := by
  have h := IsPresentation.modulus_dvd_rep_add (P := P) 0 0
  rw [add_zero] at h
  have h' : (P.rep (0 : S)).toPoly - ((P.rep (0 : S)).toPoly + (P.rep (0 : S)).toPoly)
      = -(P.rep (0 : S)).toPoly := by ring
  rw [h'] at h
  exact dvd_neg.mp h

/-- Coset law for finite sums, by induction from the addition law. -/
theorem modulus_dvd_rep_sum {ι : Type*} (t : Finset ι) (f : ι → S) :
    P.modulus.toPoly ∣ (P.rep (∑ j ∈ t, f j)).toPoly - ∑ j ∈ t, (P.rep (f j)).toPoly := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using P.modulus_dvd_rep_zero
  | insert a t ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      have h1 := IsPresentation.modulus_dvd_rep_add (P := P) (f a) (∑ j ∈ t, f j)
      have h2 := dvd_add h1 ih
      convert h2 using 1
      ring

/-- Two elements whose representatives differ by a multiple of the modulus are equal. -/
theorem eq_of_modulus_dvd {a b : S}
    (h : P.modulus.toPoly ∣ (P.rep a).toPoly - (P.rep b).toPoly) : a = b := by
  have hz : (P.rep a).toPoly - (P.rep b).toPoly = 0 := by
    obtain ⟨c, hc⟩ := h
    rcases eq_or_ne c 0 with rfl | hc0
    · simpa using hc
    · exfalso
      have hne : P.modulus.toPoly.leadingCoeff * c.leadingCoeff ≠ 0 := by
        rw [(IsPresentation.monic (P := P)).leadingCoeff, one_mul]
        exact Polynomial.leadingCoeff_ne_zero.mpr hc0
      have hdeg := Polynomial.natDegree_mul' hne
      have h1 := IsPresentation.natDegree_rep_lt (P := P) a
      have h2 := IsPresentation.natDegree_rep_lt (P := P) b
      have h3 : ((P.rep a).toPoly - (P.rep b).toPoly).natDegree
          < P.modulus.toPoly.natDegree :=
        lt_of_le_of_lt (Polynomial.natDegree_sub_le _ _) (max_lt h1 h2)
      rw [hc, hdeg] at h3
      omega
  exact IsPresentation.rep_injective (P := P) (sub_eq_zero.mp hz)

/-- **Vanishing kernel**: a modulus-multiple of degree below the monic modulus is zero. -/
theorem eq_zero_of_modulus_dvd_of_natDegree_lt {p : Polynomial R} (h : P.modulus.toPoly ∣ p)
    (hdeg : p.natDegree < P.modulus.toPoly.natDegree) : p = 0 := by
  obtain ⟨c, hc⟩ := h
  rcases eq_or_ne c 0 with rfl | hc0
  · simpa using hc
  · exfalso
    have hne : P.modulus.toPoly.leadingCoeff * c.leadingCoeff ≠ 0 := by
      rw [(IsPresentation.monic (P := P)).leadingCoeff, one_mul]
      exact Polynomial.leadingCoeff_ne_zero.mpr hc0
    have hmul := Polynomial.natDegree_mul' hne
    rw [hc, hmul] at hdeg
    omega

/-- The representative of `0` is exactly `0`. -/
theorem rep_zero : (P.rep (0 : S)).toPoly = 0 :=
  P.eq_zero_of_modulus_dvd_of_natDegree_lt P.modulus_dvd_rep_zero
    (IsPresentation.natDegree_rep_lt (P := P) 0)

/-- `rep` is exactly additive: the coset defect has degree below the monic modulus. -/
theorem rep_add (a b : S) :
    (P.rep (a + b)).toPoly = (P.rep a).toPoly + (P.rep b).toPoly := by
  have hz : (P.rep (a + b)).toPoly - ((P.rep a).toPoly + (P.rep b).toPoly) = 0 := by
    refine P.eq_zero_of_modulus_dvd_of_natDegree_lt
      (IsPresentation.modulus_dvd_rep_add (P := P) a b) ?_
    have h1 := IsPresentation.natDegree_rep_lt (P := P) (a + b)
    have h2 := IsPresentation.natDegree_rep_lt (P := P) a
    have h3 := IsPresentation.natDegree_rep_lt (P := P) b
    have h4 := Polynomial.natDegree_add_le ((P.rep a).toPoly) ((P.rep b).toPoly)
    have h5 := Polynomial.natDegree_sub_le ((P.rep (a + b)).toPoly)
      ((P.rep a).toPoly + (P.rep b).toPoly)
    omega
  linear_combination hz

/-- `rep` commutes with negation exactly. -/
theorem rep_neg (a : S) : (P.rep (-a)).toPoly = -(P.rep a).toPoly := by
  have h := P.rep_add a (-a)
  rw [add_neg_cancel, P.rep_zero] at h
  linear_combination -h

/-- `rep` commutes with finite sums exactly. -/
theorem rep_sum {ι : Type*} (t : Finset ι) (f : ι → S) :
    (P.rep (∑ j ∈ t, f j)).toPoly = ∑ j ∈ t, (P.rep (f j)).toPoly := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using P.rep_zero
  | insert a t ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, P.rep_add, ih]

/-! ### The lifted rows and the quotient-witness correspondence -/

variable {n μ : ℕ}

/-- The `i`-th lifted row's left-hand side, on the semantics of canonical representatives.
Stays a `Polynomial R`-valued spec object (reachable only through `Prop`s), so it stays
`noncomputable` by design — the DATA is in the presentation, the algebra is Mathlib's. -/
noncomputable def rowSum (M : PolyMatrix S n μ) (z : PolyVec S μ) (i : Fin n) :
    Polynomial R :=
  ∑ j, (P.rep (M i j)).toPoly * (P.rep (z j)).toPoly

/-- Structural degree bound of a lifted row. -/
theorem natDegree_rowSum_le (M : PolyMatrix S n μ) (z : PolyVec S μ) (i : Fin n) :
    (P.rowSum M z i).natDegree ≤ 2 * P.modulus.toPoly.natDegree - 2 := by
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ (fun j _ => ?_)
  have h1 := IsPresentation.natDegree_rep_lt (P := P) (M i j)
  have h2 := IsPresentation.natDegree_rep_lt (P := P) (z j)
  have h3 := Polynomial.natDegree_mul_le
    (p := (P.rep (M i j)).toPoly) (q := (P.rep (z j)).toPoly)
  omega

/-- The representative of a matrix-vector row agrees with the lifted row up to a multiple of
the modulus — the summed coset law. -/
theorem modulus_dvd_rep_mulVec_sub_rowSum (M : PolyMatrix S n μ) (z : PolyVec S μ)
    (i : Fin n) :
    P.modulus.toPoly ∣ (P.rep ((M *ᵥ z) i)).toPoly - P.rowSum M z i := by
  have hmv : (M *ᵥ z) i = ∑ j, M i j * z j := by
    rw [matVecMul_apply, dot_eq_sum]
  have h1 := P.modulus_dvd_rep_sum Finset.univ (fun j => M i j * z j)
  have h2 : P.modulus.toPoly ∣ (∑ j, (P.rep (M i j * z j)).toPoly)
      - ∑ j, (P.rep (M i j)).toPoly * (P.rep (z j)).toPoly := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.dvd_sum (fun j _ => IsPresentation.modulus_dvd_rep_mul (P := P) (M i j) (z j))
  have h3 := dvd_add h1 h2
  rw [hmv, rowSum]
  convert h3 using 1
  ring

/-- **Quotient descent** (the direction the extraction consumes). -/
theorem mulVec_eq_of_rowSum_eq {M : PolyMatrix S n μ} {z : PolyVec S μ}
    {y : PolyVec S n} {i : Fin n} {ρ : Polynomial R}
    (h : P.rowSum M z i = (P.rep (y i)).toPoly + P.modulus.toPoly * ρ) :
    (M *ᵥ z) i = y i := by
  apply P.eq_of_modulus_dvd
  have h1 := P.modulus_dvd_rep_mulVec_sub_rowSum M z i
  have h2 : P.modulus.toPoly ∣ P.rowSum M z i - (P.rep (y i)).toPoly :=
    ⟨ρ, by rw [h]; ring⟩
  have h3 := dvd_add h1 h2
  convert h3 using 1
  ring

/-- **Quotient witness** (the honest direction), with an explicit quotient polynomial. -/
theorem exists_rowSum_eq_of_mulVec_eq {M : PolyMatrix S n μ} {z : PolyVec S μ}
    {y : PolyVec S n} {i : Fin n} (h : (M *ᵥ z) i = y i) :
    ∃ ρ : Polynomial R, ρ.natDegree ≤ P.modulus.toPoly.natDegree - 2 ∧
      P.rowSum M z i = (P.rep (y i)).toPoly + P.modulus.toPoly * ρ := by
  have hdvd : P.modulus.toPoly ∣ P.rowSum M z i - (P.rep (y i)).toPoly := by
    have h1 := P.modulus_dvd_rep_mulVec_sub_rowSum M z i
    rw [h] at h1
    simpa [neg_sub] using dvd_neg.mpr h1
  refine ⟨(P.rowSum M z i - (P.rep (y i)).toPoly) /ₘ P.modulus.toPoly, ?_, ?_⟩
  · rw [Polynomial.natDegree_divByMonic _ (IsPresentation.monic (P := P))]
    have h1 := P.natDegree_rowSum_le M z i
    have h2 := IsPresentation.natDegree_rep_lt (P := P) (y i)
    have h3 := Polynomial.natDegree_sub_le (P.rowSum M z i) ((P.rep (y i)).toPoly)
    have h4 := P.natDegree_modulus_pos
    omega
  · have hmod : (P.rowSum M z i - (P.rep (y i)).toPoly) %ₘ P.modulus.toPoly = 0 :=
      (Polynomial.modByMonic_eq_zero_iff_dvd (IsPresentation.monic (P := P))).mpr hdvd
    have hdiv := Polynomial.modByMonic_add_div
      (P.rowSum M z i - (P.rep (y i)).toPoly) P.modulus.toPoly
    rw [hmod, zero_add] at hdiv
    linear_combination -hdiv

/-- **The per-row recovery engine** ([NOZ26] Lemma 9), over an arbitrary presentation. -/
theorem mulVec_eq_of_evalAt_rowSum {F : Type*} [Field F] {φF : R →+* F}
    (hφF : Function.Injective φF) {d : ℕ} (hd : P.modulus.toPoly.natDegree = d)
    {M : PolyMatrix S n μ} {z : PolyVec S μ} {y : PolyVec S n} {i : Fin n}
    {ρ : Polynomial R} (hρ : ρ.natDegree ≤ d - 1)
    {A : Fin (2 * d) → F} (hA : Function.Injective A)
    (h : ∀ j, evalAt φF (A j) (P.rowSum M z i)
          = evalAt φF (A j) ((P.rep (y i)).toPoly)
            + evalAt φF (A j) (P.modulus.toPoly) * evalAt φF (A j) ρ) :
    (M *ᵥ z) i = y i := by
  refine P.mulVec_eq_of_rowSum_eq (ρ := ρ) ?_
  refine eq_of_evalAt_eq hφF (N := 2 * d) ?_ ?_ hA ?_
  · have h1 := P.natDegree_rowSum_le M z i
    have h2 := P.natDegree_modulus_pos
    omega
  · have h1 := IsPresentation.natDegree_rep_lt (P := P) (y i)
    have h2 := Polynomial.natDegree_mul_le (p := P.modulus.toPoly) (q := ρ)
    have h3 := Polynomial.natDegree_add_le ((P.rep (y i)).toPoly) (P.modulus.toPoly * ρ)
    have h4 := P.natDegree_modulus_pos
    omega
  · intro j
    rw [map_add, map_mul]
    exact h j

end Presentation

/-! ## Part C — the retyped `LiftedWitness`, `checkAt`, `relLin`, and `recover` -/

/-- The lifted witness, with **computable** quotient polynomials. Same fields as today's
`Lift.LiftedWitness`; only `ρ`'s carrier changes, and the degree bound speaks about its
`toPoly` semantics (uniform with the `IsPresentation` laws; `natDegree_toPoly` bridges to
the computable `CPolynomial.natDegree` wherever a decidable bound is preferred). -/
structure LiftedWitness (R : Type*) [Semiring R] (S : Type*) (d μ n : ℕ) where
  /-- The witness `z ∈ S^μ` of the linear relation. -/
  z : Fin μ → S
  /-- Per-row quotient polynomials, computable. -/
  ρ : Fin n → CPolynomial R
  /-- Degree bound on the quotients (semantic form). -/
  hρ : ∀ i, (ρ i).toPoly.natDegree ≤ d - 1

variable {R S : Type*} [CommRing R] [CommRing S] {F : Type*}
variable {Stmt : Type*} {d μ n : ℕ}

/-- The input linear relation (verbatim from `Lift/Reduction.lean`). -/
def relLin (getM : Stmt → PolyMatrix S n μ) (getY : Stmt → PolyVec S n)
    (zOk : Stmt → PolyVec S μ → Prop) : Set (Stmt × PolyVec S μ) :=
  {p | getM p.1 *ᵥ p.2 = getY p.1 ∧ zOk p.1 p.2}

section CheckAt

variable [CommSemiring F]

/-- The challenge-local predicate of the switch, at the computable structures. `Prop`-valued,
so the `toPoly` semantics inside costs nothing at runtime. -/
def checkAt (P : Presentation R S) (φF : R →+* F)
    (getM : Stmt → PolyMatrix S n μ) (getY : Stmt → PolyVec S n)
    (sideCond : Stmt → Prop)
    (s : Stmt) (a : F) (w : LiftedWitness R S d μ n) : Prop :=
  (∀ i, evalAt φF a (P.rowSum (getM s) w.z i) =
      evalAt φF a ((P.rep (getY s i)).toPoly) +
        evalAt φF a (P.modulus.toPoly) * evalAt φF a ((w.ρ i).toPoly)) ∧
    sideCond s

end CheckAt

variable [Field F]

/-- **The generic recovery theorem** at the computable structures — statement and proof
verbatim from `Lift/Reduction.lean` (modulo the `toPoly` spelling of `hd`). -/
theorem recover (P : Presentation R S) [IsPresentation P] {φF : R →+* F}
    (getM : Stmt → PolyMatrix S n μ) (getY : Stmt → PolyVec S n)
    (zOk : Stmt → PolyVec S μ → Prop) (sideCond : Stmt → Prop)
    {wShort : LiftedWitness R S d μ n → Prop}
    (hφF : Function.Injective φF)
    (hd : P.modulus.toPoly.natDegree = d)
    (short_zOk : ∀ (s : Stmt) (w : LiftedWitness R S d μ n),
      wShort w → sideCond s → zOk s w.z)
    (s : Stmt) (w : LiftedWitness R S d μ n) (fam : Fin (2 * d) → F)
    (hinj : Function.Injective fam)
    (hcheck : ∀ j, checkAt P φF getM getY sideCond s (fam j) w)
    (hshort : wShort w) : (s, w.z) ∈ relLin getM getY zOk := by
  have hpos : 0 < d := hd ▸ P.natDegree_modulus_pos
  have hside : sideCond s := (hcheck ⟨0, by omega⟩).2
  refine ⟨?_, short_zOk s w hshort hside⟩
  funext i
  exact P.mulVec_eq_of_evalAt_rowSum hφF hd (w.hρ i) hinj (fun j => (hcheck j).1 i)

end CMP

/-! ## Part D — the cyclotomic instance, computable, laws verbatim -/

namespace CMP

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]

/-- Hachi's presentation of `Rq Φ`, now a plain `def` of two projections — the
noncomputability was PURELY the `toPoly` bridge the old structure forced. -/
def cyclotomicPresentation : Presentation (ZMod q) (Rq Φ) where
  modulus := Φ.φ
  rep a := a.1

omit [NeZero q] in
/-- The presentation degree is the ring dimension — same statement as today
(the old `modulus` was literally `Φ.φ.toPoly`, so the proposition is unchanged). -/
theorem cyclotomicPresentation_modulus_natDegree :
    (cyclotomicPresentation Φ).modulus.toPoly.natDegree = Φ.φ.natDegree :=
  (CPolynomial.natDegree_toPoly Φ.φ).symm

omit [NeZero q] in
/-- The presentation laws for the cyclotomic instance — discharged from the SAME QuotientLift
bridge lemmas as today, verbatim. -/
theorem isPresentation_cyclotomic (hd : 0 < Φ.φ.natDegree) :
    IsPresentation (cyclotomicPresentation Φ) where
  monic := IsCyclotomic.monic
  natDegree_rep_lt s := by
    have h := Rq.natDegree_val_toPoly_lt' Φ hd s
    rwa [CPolynomial.natDegree_toPoly] at h
  rep_injective := val_toPoly_injective Φ
  modulus_dvd_rep_add := modulus_dvd_toPoly_add_sub Φ
  modulus_dvd_rep_mul := modulus_dvd_toPoly_mul_sub Φ

end CMP

/-! ## Part E — the package-shaped IR gate: positive and negative control

The blocker was never that `Lift.package` *computes* with the presentation — it doesn't
(post-plan, `P` is consumed only through `Prop`s). The blocker is that `P` is a **kept
argument**: Lean does not erase a `Type`-valued binder even when every use of it is erased.
So the gate is exactly that shape: a package-like consumer that RETAINS its presentation
argument and whose extractor ignores it. -/

namespace CMP

/-- A minimal stand-in for `EscapeCWSSPackage`: one erased field, one data field of the
post-plan extractor shape (consume a leaf witnessing, return an input witness). -/
structure PkgLike (Stmt Wit : Type*) where
  relOut : Set (Stmt × Wit)
  extractor : Stmt → (Fin 1 → Option Wit) → Option Wit

variable {R S : Type*} [CommRing R] [CommRing S] {d μ n : ℕ}

/-- The `Lift.package` shape at the NEW presentation: `P` is a retained argument (as in the
repo), the extractor forwards the leaf witness. Computable. -/
def packageLike (P : Presentation R S) (_hd : P.modulus.toPoly.natDegree = d) :
    PkgLike S (LiftedWitness R S d μ n) where
  relOut := ∅
  extractor := fun _ o => o 0

/-- Today's failure shape, for the negative control: the same presentation DATA but over
Mathlib `Polynomial` fields. -/
structure PresentationM (R S : Type*) [CommRing R] [CommRing S] where
  modulus : Polynomial R
  rep : S → Polynomial R

/-- The Mathlib-typed package-shaped consumer. -/
def packageLikeM (_P : PresentationM R S) : PkgLike S (Fin μ → S) where
  relOut := ∅
  extractor := fun _ o => o 0

section Instantiation

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]

/-- **The positive gate** — `liftPackage`'s exact shape at the computable presentation:
apply the package builder to `cyclotomicPresentation Φ`. This is the application that today
fails codegen; here it is a plain `def`. -/
def liftPackageLike {μ n : ℕ} :
    PkgLike (Rq Φ) (LiftedWitness (ZMod q) (Rq Φ) Φ.φ.natDegree μ n) :=
  packageLike (cyclotomicPresentation Φ) (cyclotomicPresentation_modulus_natDegree Φ)

/-- Today's `cyclotomicPresentation`, reproduced: Mathlib fields force `noncomputable`. -/
noncomputable def cyclotomicPresentationM : PresentationM (ZMod q) (Rq Φ) where
  modulus := Φ.φ.toPoly
  rep a := a.1.toPoly

/-- **The negative control** — the same package application at the Mathlib-typed
presentation is noncomputable (this is today's `liftPackage`, in miniature). The IR gate
below confirms it has NO IR while `liftPackageLike` has IR. -/
noncomputable def liftPackageLikeM {μ : ℕ} : PkgLike (Rq Φ) (Fin μ → Rq Φ) :=
  packageLikeM (cyclotomicPresentationM Φ)

end Instantiation

end CMP

/-! ## Part F — runtime: the previously-unconstructible values, constructed and `#eval`ed -/

namespace CMPDemo

open CMP

instance : Fact (Nat.Prime 17) := ⟨by decide⟩

/-- A concrete cyclotomic modulus: `X² + 1` over `ZMod 17` — the repo's own
`powTwoCyclotomic 1` (conductor 4), which ships its `IsCyclotomic` instance.
`abbrev` (the repo's `primePowTwoModulus` pattern) so that instance applies transparently. -/
abbrev Phi17 : CyclotomicModulus (ZMod 17) := powTwoCyclotomic 1

/-- The computable presentation at a concrete modulus. -/
def pres17 : Presentation (ZMod 17) (Rq Phi17) := cyclotomicPresentation Phi17

/-- A concrete `Rq` element, built by reduction — computable end to end. -/
def x17 : Rq Phi17 := Rq.mk Phi17 (CPolynomial.ofArray #[3, 5])

/-- A concrete lifted witness — the value that is UNCONSTRUCTIBLE at today's structures
(`Polynomial.instZero` has no IR, so not even the all-zero witness compiles). -/
def w17 : LiftedWitness (ZMod 17) (Rq Phi17) Phi17.φ.natDegree 1 1 where
  z := fun _ => x17
  ρ := fun _ => CPolynomial.C 2
  hρ := fun _ => by
    rw [← CPolynomial.natDegree_toPoly, CPolynomial.natDegree_C]
    exact Nat.zero_le _

-- The demos: modulus degree, representative coefficients, witness data — all runnable.
#eval pres17.modulus.natDegree                    -- 2
#eval (pres17.rep x17).coeff 0                    -- 3
#eval (pres17.rep x17).coeff 1                    -- 5
#eval (w17.ρ 0).coeff 0                           -- 2
#eval CPolynomial.eval (3 : ZMod 17) (w17.ρ 0)    -- 2
#eval (liftPackageLike Phi17 (μ := 1) (n := 1)).extractor x17 (fun _ => some w17)
        |>.map (fun w => (w.ρ 0).coeff 0)         -- some 2

-- Kernel-checked structure: `rep` is definitionally the canonical-representative projection,
-- and the package-shaped extractor definitionally forwards the leaf witness. (Computed VALUES
-- are checked by the `#eval`s above; kernel reduction of `Array`-backed arithmetic is not
-- available — `decide` sticks on `Array`/`USize` internals, a CompPoly limitation, not ours.)
example : pres17.rep x17 = x17.1 := rfl
example (o : Fin 1 → Option (LiftedWitness (ZMod 17) (Rq Phi17) Phi17.φ.natDegree 1 1)) :
    (liftPackageLike Phi17 (μ := 1) (n := 1)).extractor x17 o = o 0 := rfl

end CMPDemo

/-! ## Part G — audit: axioms + IR

Note the axiom prints below include `Classical.choice` even for the plain data definitions:
it enters through `Prop`-side instance arguments (`Rq`'s `CommRing` borrows its *laws* from the
noncomputable quotient bridge) and is erased at codegen — E25's calibration point. The IR gate,
not the axiom print, is the computability judge here; what the axiom prints DO certify is the
absence of `sorryAx`. -/

#print axioms CMP.cyclotomicPresentation
#print axioms CMP.isPresentation_cyclotomic
#print axioms CMP.recover
#print axioms CMPDemo.w17

open Lean in
run_cmd do
  let env ← Lean.getEnv
  for nm in [``CMP.cyclotomicPresentation, ``CMP.packageLike, ``CMP.liftPackageLike,
             ``CMPDemo.pres17, ``CMPDemo.x17, ``CMPDemo.w17] do
    match Lean.IR.findEnvDecl env nm with
    | some _ => Lean.logInfo m!"IR PRESENT: {nm}"
    | none   => Lean.logError m!"NO IR (noncomputable): {nm}"
  -- The negative control must have NO IR — that is the point.
  match Lean.IR.findEnvDecl env ``CMP.liftPackageLikeM with
  | some _ => Lean.logError m!"UNEXPECTED IR: {``CMP.liftPackageLikeM}"
  | none   => Lean.logInfo m!"NO IR AS EXPECTED (the negative control): {``CMP.liftPackageLikeM}"
