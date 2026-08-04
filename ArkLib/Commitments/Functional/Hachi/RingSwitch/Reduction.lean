/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.RingSwitch.Rlin
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.ScalarRound
import CompPoly.Univariate.ToPoly.Impl

/-!
  # HMZ25 lift — Hachi Figure 4 / Lemma 9 — skeleton (sumcheck-track milestone F4)

  The first interactive stage of Hachi's §4.3 sumcheck chain, following the ring-switching idea
  of Huang–Mao–Zhang [HMZ25]: `M z = y` over `Rq = Zq[X]/(X^d + 1)` holds **iff** there are
  quotient polynomials `rᵢ ∈ Zq[X]` of degree `≤ d − 2` with

  `∑ⱼ Mᵢⱼ(X)·zⱼ(X) = yᵢ(X) + (X^d + 1)·rᵢ(X)`  in `Zq[X]`, for every row `i`.

  ## Protocol (two rounds, `pSpecScalar`)

  * **Round 0 (P→V)** — the prover sends `t := Com(w̃)`, a binding commitment to the *lifted
    witness* `w̃` — the `R^lin` witness `z` together with the quotients `r` (Hachi Eq. (21); the
    gadget digits of `r` arrive with the F5 table encoding, `ZeroCheck/Constraints.lean`).
    Figure 4 draws `(z, r)` as the prover's last message, but in the composed scheme it is
    **never sent** — it is the output-relation witness (QuadEval precedent, design D6).
  * **Round 1 (V→P)** — the verifier samples `α ← F` (an extension field `F ⊇ Zq`, abstract per
    design G5) and both sides evaluate the lifted rows at `X := α`. The verifier itself is a pure
    statement-extending pass-through — the row checks at `α` constrain the never-sent witness,
    so they live in the output relation.

  ## Soundness shape (Lemma 9)

  Output relation `relLift`: an opening `w̃` of `t` whose lifted rows vanish at `α` and which is
  short. **CWSS at `k = 2d`** (`scalarStructure`, plain special soundness): each row's defect
  polynomial `∑ⱼ Mᵢⱼ·zⱼ − yᵢ − (X^d+1)·rᵢ` has degree `≤ 2d − 1`, so `2d` accepting branches at
  pairwise-distinct `α` either exhibit two openings of `t` with distinct tables — the weak-binding
  escape (`LiftCom.collision_mem`; [NOZ26] Remark 2 / Lemma 7), threaded through `K.esc` — or
  share one opening whose row defects have `2d` roots, hence vanish identically: `M z = y` over
  `Rq` plus the range bound, i.e. `relRlinE` membership.

  ## The abstract commitment `LiftCom` and the norm bookkeeping

  The commitment is abstract (design G2: the key is a *parameter*, not a statement field; Lemma 9
  needs only binding). The delicate point is that [NOZ26] carries **two unrelated** shortness
  notions, and they must not be identified:

  * the admissibility built into a *weak opening* (Lemma 7) — slack-relative
    (`‖cᵢ·sᵢ‖ ≤ β̄`, `‖cᵢ‖₁ ≤ ω̄`, `cᵢ ∈ Rq^×`), part of what "opening" *means* for an
    Ajtai-style scheme, and the precondition of its binding property (Remark 2);
  * `liftShort` — the *range* claim `‖z‖∞ ≤ bound`, `‖r‖∞ ≤ rBound` that Figure 4 checks and
    that the range identity `H₀ ≡ 0` proves.

  `LiftCom` therefore carries its own `Opening` type, with `table` reading off the Eq. (21)
  table; binding (`collision_mem`) is stated unconditionally on openings, so **no reduction
  above the commitment carries a norm hypothesis** — matching Lemmas 9–11, which say only "or
  break binding of the commitment scheme Com". `relLift` keeps `liftShort bound rBound` as
  Figure 4's own norm *claim* about the committed table, which the batching bridge then
  **derives** from `H₀ ≡ 0` (`ZeroCheck/Batch.lean`) rather than assuming; together with the
  public sanity conjunct `bound ≤ s.bound` it supplies the statement-level `R^lin` bound of the
  extraction target (assembled statements have `s.bound = γ = bound`, so completeness is
  unaffected). The concrete instantiation — the inner-outer commitment *without initial
  decomposition* ([NOZ26] §4.5), `Opening` the weak openings, collision discharged by
  `outputToModuleSIS_valid_of_verified` — and the commitment reinterpretation at the next ring
  dimension used by the recursion handoff (`Recursion/TraceHandoff.lean`) are Phase-G
  deliverables.

  **Sorried**: the CWSS theorem `lift_coordinateWiseSpecialSound` (Lemma 9's interpolation
  extraction; consumes the F3 quotient-lift algebra and the F4.1 scalar-round assembly).

  ## References

  * [Huang, M.-Y. M., Mao, X., and Zhang, J., *Sublinear Proofs over Polynomial Rings*][HMZ25]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open WeakBinding
open OracleComp OracleSpec ProtocolSpec CoordinateWise CoordinateWise.ScalarRound

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {n μ : ℕ} {E : Type}

/-- **The lifted witness** (Hachi Eq. (21), polynomial form): the `R^lin` witness `z` together
with the per-row quotient polynomials `rᵢ` of the `Zq[X]`-lift, with their structural degree
bound `deg rᵢ ≤ d − 2`. This is the committed data of Figure 4. -/
structure LiftedWitness (Φ : CyclotomicModulus (ZMod q)) (μ n : ℕ) where
  /-- The `R^lin` witness `z ∈ Rq^μ`. -/
  z : PolyVec (Rq Φ) μ
  /-- The per-row quotient polynomials `rᵢ ∈ Zq[X]`. -/
  r : Fin n → CPolynomial (ZMod q)
  /-- Structural degree bound: `deg rᵢ ≤ d − 2` (from `deg (∑ Mᵢⱼzⱼ − yᵢ) ≤ 2d − 2`). -/
  hr : ∀ i, (r i).natDegree ≤ Φ.φ.natDegree - 2

/-- `LiftedWitness` is inhabited (the all-zero witness). -/
instance : Nonempty (LiftedWitness Φ μ n) :=
  ⟨⟨fun _ => 0, fun _ => 0, fun _ => Nat.zero_le _⟩⟩

/-- Coefficient-range predicate on the quotient polynomials (the `r`-side of the Eq. (21) range
claims; the exact constant is pinned by the F5 digit decomposition). -/
def rShort (rBound : ℕ) (r : Fin n → CPolynomial (ZMod q)) : Prop :=
  ∀ i k, ((r i).coeff k).valMinAbs.natAbs ≤ rBound

/-- The **range** predicate of the lifted witness — Figure 4's norm check
`z ∈ Zq^{<d}[X] ∧ ‖z‖∞, ‖r‖∞ ≤ b − 1`, carried as the norm side of `relLift` and *derived* from
the range identity `H₀ ≡ 0` at the batching bridge (`hZero_eq_zero_imp_liftShort`).

This is **not** the admissibility notion that conditions the commitment's binding property: that
one is the slack-relative weak-opening data of [NOZ26] Lemma 7 and lives inside
`LiftCom.Opening`. Conflating the two would turn this derived claim into an assumption at every
seam above the commitment (see `LiftCom`). -/
def liftShort (bound rBound : ℕ) (w : LiftedWitness Φ μ n) : Prop :=
  vecLInftyNorm Φ w.z ≤ bound ∧ rShort rBound w.r

/-- **Abstract binding commitment** for the lifted witness (design G2: abstract in F4;
instantiated by the §4.5 inner-outer commitment without initial decomposition in Phase G).

`Opening` is the scheme's *opening type* — the object a knowledge extractor hands back — and
`table` reads off the Eq. (21) coefficient table `w̃ = (z, r)` that an opening determines. Keeping
the two apart is what keeps the norm bookkeeping straight, because [NOZ26] has **two unrelated**
shortness notions:

* the admissibility built into a *weak opening* (Lemma 7: `‖cᵢ·sᵢ‖ ≤ β̄`, `‖cᵢ‖₁ ≤ ω̄`,
  `cᵢ ∈ Rq^×`) — slack-relative, part of what "opening" *means* for an Ajtai-style scheme, and
  the precondition of its binding property (Remark 2);
* `liftShort` — the *range* claim `‖z‖∞ ≤ bound`, `‖r‖∞ ≤ rBound` that Figure 4 checks and that
  the range identity `H₀ ≡ 0` proves.

Identifying the two — as a shortness *parameter* on this structure would — forces every reduction
above the commitment to carry `liftShort` as a hypothesis, that is, to assume at the point seams
of Figure 5 exactly what the range check exists to prove (one evaluation `H₀(τ₀) = 0` cannot
recover it). Here the first notion is absorbed into `Opening`, so `collision_mem` is
unconditional and **no reduction above the commitment mentions a norm** — matching Lemmas 9–11,
which say only "or break binding of the commitment scheme `Com`" — while the second stays a
derived conclusion (`ZeroCheck/Batch.lean`).

`collision_mem` is binding in the paper's weak sense (Remark 2): two openings of one commitment
whose *tables* differ (Lemma 7's `sⱼ ≠ s'ⱼ`) are a valid escape — concretely a Module-SIS
solution via `outputToModuleSIS_valid_of_verified`, which is where the weak-opening admissibility
carried by `Opening` is consumed. -/
structure LiftCom (Φ : CyclotomicModulus (ZMod q)) (μ n : ℕ) (E : Type) where
  /-- The scheme's opening type ([NOZ26] Lemma 7's weak openings). -/
  Opening : Type
  /-- Openings exist — e.g. the honest opening of the zero witness. -/
  nonempty : Nonempty Opening
  /-- The Eq. (21) coefficient table `w̃ = (z, r)` an opening determines. -/
  table : Opening → LiftedWitness Φ μ n
  /-- The commitment space (the wire type of Figure 4's first message). -/
  TCom : Type
  /-- The (deterministic) commitment function. -/
  com : Opening → TCom
  /-- The escape set: valid cryptographic break artifacts (statement-independent, design G1). -/
  esc : Set E
  /-- The escape produced from a commitment collision. -/
  escOfCollision : Opening → Opening → E
  /-- Weak binding: two openings of one commitment with distinct tables are a valid escape. -/
  collision_mem : ∀ o o', table o ≠ table o' → com o = com o' → escOfCollision o o' ∈ esc

/-- Openings form a nonempty type — needed wherever an extractor must return a fallback value
outside the accepting case. -/
instance instNonemptyOpening (K : LiftCom Φ μ n E) : Nonempty K.Opening := K.nonempty

variable {F : Type} [Field F] (bound rBound : ℕ)

/-- The lift's output statement: the `R^lin` statement extended by the commitment `t` and the
evaluation challenge `α` (the statement-extending pass-through shape of `pSpecScalar`). -/
abbrev LiftStatement (Φ : CyclotomicModulus (ZMod q)) (TCom F : Type) (n μ : ℕ) : Type :=
  RlinStatement Φ n μ × TCom × F

/-- The computable `i`-th lifted row
`∑ⱼ Mᵢⱼ(X)·zⱼ(X) ∈ Zq[X]`, formed from the canonical `CPolynomial` representatives. -/
def cRowSum (s : RlinStatement Φ n μ) (z : PolyVec (Rq Φ) μ) (i : Fin n) :
    CPolynomial (ZMod q) :=
  ∑ j, (s.M i j).1 * (z j).1

/-- Computable evaluation of a `Zq[X]` polynomial at `a ∈ F` through the base-field embedding. -/
def cEvalAt (φF : ZMod q →+* F) (a : F) (p : CPolynomial (ZMod q)) : F :=
  p.eval₂ φF a

/-- Mathlib view of `cRowSum`, retained for degree and root-counting proofs. -/
noncomputable def rowSum (s : RlinStatement Φ n μ) (z : PolyVec (Rq Φ) μ) (i : Fin n) :
    Polynomial (ZMod q) :=
  (cRowSum Φ s z i).toPoly

omit [NeZero q] [IsCyclotomic Φ] in
/-- `rowSum` is the expected Mathlib sum of products of canonical representatives. -/
theorem rowSum_eq_sum_toPoly (s : RlinStatement Φ n μ) (z : PolyVec (Rq Φ) μ) (i : Fin n) :
    rowSum Φ s z i = ∑ j, (s.M i j).1.toPoly * (z j).1.toPoly := by
  unfold rowSum cRowSum
  rw [CPolynomial.toPoly_sum]
  exact Finset.sum_congr rfl fun j _ => CPolynomial.toPoly_mul _ _

/-- Mathlib evaluation homomorphism, retained as a specification-level view of `cEvalAt`. -/
noncomputable def evalAt (φF : ZMod q →+* F) (a : F) : Polynomial (ZMod q) →+* F :=
  Polynomial.eval₂RingHom φF a

omit [NeZero q] [IsCyclotomic Φ] in
/-- The computable and Mathlib row-sum evaluations agree. -/
theorem cEvalAt_cRowSum_eq_evalAt (φF : ZMod q →+* F) (a : F)
    (s : RlinStatement Φ n μ) (z : PolyVec (Rq Φ) μ) (i : Fin n) :
    cEvalAt φF a (cRowSum Φ s z i) = evalAt φF a (rowSum Φ s z i) := by
  exact CPolynomial.eval₂_toPoly φF a (cRowSum Φ s z i)

omit [NeZero q] [BEq (ZMod q)] [LawfulBEq (ZMod q)] in
/-- Evaluation of any computable polynomial agrees with evaluation of its Mathlib image. -/
theorem cEvalAt_eq_evalAt_toPoly (φF : ZMod q →+* F) (a : F)
    (p : CPolynomial (ZMod q)) :
    cEvalAt φF a p = evalAt φF a p.toPoly := by
  exact CPolynomial.eval₂_toPoly φF a p

/-- **The lift's output relation** (Hachi Figure 4 / Lemma 9 residual claims, at the fixed
challenge `α` of the transcript): `w̃ = (z, r)` opens `t`; every lifted row vanishes at `α`,
i.e. `∑ⱼ Mᵢⱼ(α)·zⱼ(α) = yᵢ(α) + (α^d + 1)·rᵢ(α)`; and the opened table is short. The range claims
are *witness-level* — proven downstream by the zero-check/sumcheck stages (`liftShort` is
**derived** from `H₀ ≡ 0` at the batching bridge, never assumed) and consumed upstream by Lemma
9's extraction. The final conjunct `bound ≤ s.bound` is the public sanity condition tying the
global norm parameter to the statement's declared `R^lin` bound (see the module docstring). -/
def relLift (K : LiftCom Φ μ n E) (φF : ZMod q →+* F) :
    Set (LiftStatement Φ K.TCom F n μ × K.Opening) :=
  {p |
    K.com p.2 = p.1.2.1 ∧
    (∀ i, cEvalAt φF p.1.2.2 (cRowSum Φ p.1.1 (K.table p.2).z i) =
          cEvalAt φF p.1.2.2 (p.1.1.yvec i).1 +
            cEvalAt φF p.1.2.2 Φ.φ * cEvalAt φF p.1.2.2 ((K.table p.2).r i)) ∧
    liftShort Φ bound rBound (K.table p.2) ∧
    bound ≤ p.1.1.bound}

/-- Escape-threaded lift relation — the seam consumed by the batching bridge
(`ZeroCheck/Batch.lean`). -/
def relLiftE (K : LiftCom Φ μ n E) (φF : ZMod q →+* F) :
    Set (LiftStatement Φ K.TCom F n μ × (K.Opening ⊕ E)) :=
  (relLift Φ bound rBound K φF).withEscape K.esc

section Protocol

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
variable (K : LiftCom Φ μ n E) (φF : ZMod q →+* F)

/-- The lift's verifier (Hachi Figure 4): a **pure pass-through** extending the statement by the
round-0 commitment `t` and the round-1 challenge `α`. All checks constrain the never-sent
witness and live in `relLift`. -/
def liftVerifier :
    Verifier oSpec (RlinStatement Φ n μ) (LiftStatement Φ K.TCom F n μ)
      (pSpecScalar K.TCom F) where
  verify := fun stmt tr => pure (stmt, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩)

/-- The honest prover skeleton (Hachi Figure 4; completeness is out of scope for Lemma 9): round
0 sends `t := Com(w̃)` for the honestly lifted witness, round 1 receives `α`, and the output
witness is `w̃` itself. The honest computations (quotient extraction `rᵢ := (∑ Mᵢⱼzⱼ − yᵢ) /ₘ φ`
and the commitment) are the parameters `computeW`/`computeT`, to be instantiated by the
completeness layer from the F3 quotient-lift algebra. -/
def liftProver (WitIn : Type)
    (computeW : RlinStatement Φ n μ → WitIn → K.Opening)
    (computeT : RlinStatement Φ n μ → WitIn → K.TCom) :
    Prover oSpec (RlinStatement Φ n μ) WitIn (LiftStatement Φ K.TCom F n μ)
      K.Opening (pSpecScalar K.TCom F) where
  PrvState
    | 0 => RlinStatement Φ n μ × WitIn
    | 1 => RlinStatement Φ n μ × WitIn
    | 2 => (RlinStatement Φ n μ × WitIn) × F
  input := id
  sendMessage
    | ⟨0, _⟩ => fun st => pure (computeT st.1 st.2, st)
    | ⟨1, h⟩ => nomatch h
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun st => pure fun c => (st, c)
  output := fun ⟨⟨stmt, wit⟩, c⟩ =>
    pure ((stmt, computeT stmt wit, c), computeW stmt wit)

variable [SampleableType F]

/-- **Hachi Lemma 9 (skeleton): CWSS of the HMZ25 lift at `k = 2d`.**

**Sorried (F4.4).** Extraction plan, case-faithful to the paper:
* if some branch's `relLiftE`-witness is an escape `.inr e`, pass it through;
* if two branches carry openings of the shared `t` with distinct tables, `K.collision_mem`
  yields the weak-binding escape — no norm hypothesis is needed, the admissibility that
  conditions binding is carried by `K.Opening` itself;
* otherwise all `2d` branches share one `w̃`; for each row `i` the defect polynomial
  `rowSum − yᵢ.rep − φ·rᵢ` (degree `≤ 2d − 2 < 2d` by `w̃.hr` and representative degree bounds)
  vanishes at the `2d` pairwise-distinct challenges (`scalarStructure`'s injective family), hence
  is zero (F3 interpolation kernel); the `Zq[X]`-identities descend to `M z = y` over `Rq` (F3
  quotient-witness lemma), and `liftShort` + `bound ≤ s.bound` give the `R^lin` norm conjunct —
  `.inl w̃.z` lands in `relRlinE`.

Assembled via `coordinateWiseSpecialSound_of_mkWitness_scalar` (F4.1); `2 ≤ 2d` from
`hd : 0 < d`. No field-size hypothesis is needed for CWSS itself (an injective `2d`-family in `F`
is the tree's obligation; only knowledge-error accounting, out of scope, needs `2d ≤ |F|`). -/
theorem lift_coordinateWiseSpecialSound
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hd : 0 < Φ.φ.natDegree) :
    (liftVerifier (oSpec := oSpec) Φ K).coordinateWiseSpecialSound init impl
      (scalarStructure (2 * Φ.φ.natDegree) (by omega))
      (relRlinE Φ (n := n) (μ := μ) K.esc)
      (relLiftE Φ bound rBound K φF) := by
  sorry

/-- **The HMZ25 lift as a `CWSSPackage`** (Hachi [NOZ26] Figure 4 / Lemma 9): the two-round
commit-then-challenge verifier with the plain-special-soundness structure at `k = 2d`, reducing
`relRlinE` to `relLiftE`. The certificate is the sorried `lift_coordinateWiseSpecialSound`. -/
def liftPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hd : 0 < Φ.φ.natDegree) :
    CWSSPackage init impl
      (RlinStatement Φ n μ) (PolyVec (Rq Φ) μ ⊕ E)
      (LiftStatement Φ K.TCom F n μ) (K.Opening ⊕ E)
      (pSpecScalar K.TCom F) where
  verifier := liftVerifier (oSpec := oSpec) Φ K
  struct := scalarStructure (2 * Φ.φ.natDegree) (by omega)
  relIn := relRlinE Φ (n := n) (μ := μ) K.esc
  relOut := relLiftE Φ bound rBound K φF
  isPure := ⟨fun stmt tr => (stmt, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩), fun _ _ => rfl⟩
  isCWSS := lift_coordinateWiseSpecialSound Φ bound rBound K φF init impl hd

end Protocol

end ArkLib.Lattices.Ajtai.InnerOuter
