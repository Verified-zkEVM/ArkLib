/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.RingSwitch.Rlin
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.ScalarRound

/-!
  # HMZ25 lift — Hachi Figure 4 / Lemma 9 — skeleton (sumcheck-track milestone F4)

  The first interactive stage of Hachi's §4.3 sumcheck chain, following the ring-switching idea
  of Huang–Mao–Zhang [HMZ25]: `M z = y` over `Rq = Zq[X]/(X^d + 1)` holds **iff** there are
  quotient polynomials `ρᵢ ∈ Zq[X]` of degree `≤ d − 2` with

  `∑ⱼ Mᵢⱼ(X)·zⱼ(X) = yᵢ(X) + (X^d + 1)·ρᵢ(X)`  in `Zq[X]`, for every row `i`.

  ## Protocol (two rounds, `pSpecScalar`)

  * **Round 0 (P→V)** — the prover sends `t := Com(w̃)`, a binding commitment to the *lifted
    witness* `w̃` — the `R^lin` witness `z` together with the quotients `ρ` (Hachi Eq. (21); the
    gadget digits of `ρ` arrive with the F5 table encoding, `ZeroCheck/Constraints.lean`).
    Figure 4 draws `(z, r)` as the prover's last message, but in the composed scheme it is
    **never sent** — it is the output-relation witness (QuadEval precedent, design D6).
  * **Round 1 (V→P)** — the verifier samples `α ← F` (an extension field `F ⊇ Zq`, abstract per
    design G5) and both sides evaluate the lifted rows at `X := α`. The verifier itself is a pure
    statement-extending pass-through — the row checks at `α` constrain the never-sent witness,
    so they live in the output relation.

  ## Soundness shape (Lemma 9)

  Output relation `relLift`: an opening `w̃` of `t` whose lifted rows vanish at `α` and which is
  short. **CWSS at `k = 2d`** (`scalarStructure`, plain special soundness): each row's defect
  polynomial `∑ⱼ Mᵢⱼ·zⱼ − yᵢ − (X^d+1)·ρᵢ` has degree `≤ 2d − 1`, so `2d` accepting branches at
  pairwise-distinct `α` either exhibit two distinct short openings of `t` — the weak-binding
  escape (`LiftCom.collision_mem`; [NOZ26] Remark 2 / Lemma 7), threaded through `K.esc` — or
  share one opening whose row defects have `2d` roots, hence vanish identically: `M z = y` over
  `Rq` plus the range bound, i.e. `relRlinE` membership.

  ## The abstract commitment `LiftCom` and the norm bookkeeping

  The commitment is abstract (design G2: the key is a *parameter*, not a statement field; Lemma 9
  needs only binding). Weak binding is **norm-conditioned**, so `LiftCom` is parameterized by a
  shortness predicate `Short` and its collision axiom requires both openings short; this chain
  instantiates `Short := liftShort bound ρBound` at the *global* norm parameters. `relLift`
  therefore carries (i) `liftShort bound ρBound w̃` — feeding both the collision axiom and, (ii)
  via the public sanity conjunct `bound ≤ s.bound`, the statement-level `R^lin` bound of the
  extraction target (assembled statements have `s.bound = γ = bound`, so completeness is
  unaffected). The concrete instantiation — the inner-outer commitment *without initial
  decomposition* ([NOZ26] §4.5), collision discharged by `outputToModuleSIS_valid_of_verified` —
  and the commitment reinterpretation at the next ring dimension used by the recursion handoff
  (`Recursion/TraceHandoff.lean`) are Phase-G deliverables.

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
with the per-row quotient polynomials `ρᵢ` of the `Zq[X]`-lift, with their structural degree
bound `deg ρᵢ ≤ d − 2`. This is the committed data of Figure 4. -/
structure LiftedWitness (Φ : CyclotomicModulus (ZMod q)) (μ n : ℕ) where
  /-- The `R^lin` witness `z ∈ Rq^μ`. -/
  z : PolyVec (Rq Φ) μ
  /-- The per-row quotient polynomials `ρᵢ ∈ Zq[X]`. -/
  ρ : Fin n → Polynomial (ZMod q)
  /-- Structural degree bound: `deg ρᵢ ≤ d − 2` (from `deg (∑ Mᵢⱼzⱼ − yᵢ) ≤ 2d − 2`). -/
  hρ : ∀ i, (ρ i).natDegree ≤ Φ.φ.natDegree - 2

/-- `LiftedWitness` is inhabited (the all-zero witness). -/
instance : Nonempty (LiftedWitness Φ μ n) :=
  ⟨⟨fun _ => 0, fun _ => 0, fun _ => by simp⟩⟩

/-- Coefficient-range predicate on the quotient polynomials (the `ρ`-side of the Eq. (21) range
claims; the exact constant is pinned by the F5 digit decomposition). -/
def RhoShort (ρBound : ℕ) (ρ : Fin n → Polynomial (ZMod q)) : Prop :=
  ∀ i k, ((ρ i).coeff k).valMinAbs.natAbs ≤ ρBound

/-- The combined shortness predicate of the lifted witness — the norm side of `relLift`, and the
`Short` parameter of the abstract commitment `LiftCom` (weak binding is norm-conditioned,
[NOZ26] Lemma 7). -/
def liftShort (bound ρBound : ℕ) (w : LiftedWitness Φ μ n) : Prop :=
  vecLInftyNorm Φ w.z ≤ bound ∧ RhoShort ρBound w.ρ

/-- **Abstract binding commitment** for the lifted witness (design G2: abstract in F4;
instantiated by the §4.5 inner-outer commitment without initial decomposition in Phase G).
`collision_mem` is the weak-binding axiom: two distinct *short* openings of the same commitment
yield a valid escape (concretely, a Module-SIS solution via [NOZ26] Lemma 7 /
`outputToModuleSIS_valid_of_verified`). The shortness conditioning is load-bearing: Ajtai-style
commitments are only binding on short openings. -/
structure LiftCom (W E : Type) (Short : W → Prop) where
  /-- The commitment space (the wire type of Figure 4's first message). -/
  TCom : Type
  /-- The (deterministic) commitment function. -/
  com : W → TCom
  /-- The escape set: valid cryptographic break artifacts (statement-independent, design G1). -/
  esc : Set E
  /-- The escape produced from a commitment collision. -/
  escOfCollision : W → W → E
  /-- Weak binding: a collision of two distinct short openings is a valid escape. -/
  collision_mem : ∀ w w', w ≠ w' → com w = com w' → Short w → Short w' →
    escOfCollision w w' ∈ esc

variable {F : Type} [Field F] (bound ρBound : ℕ)

/-- The lift's output statement: the `R^lin` statement extended by the commitment `t` and the
evaluation challenge `α` (the statement-extending pass-through shape of `pSpecScalar`). -/
abbrev LiftStatement (Φ : CyclotomicModulus (ZMod q)) (TCom F : Type) (n μ : ℕ) : Type :=
  RlinStatement Φ n μ × TCom × F

/-- The `i`-th lifted row's left-hand side `∑ⱼ Mᵢⱼ(X)·zⱼ(X) ∈ Zq[X]`, on canonical
representatives (`CPolynomial.toPoly` of the reduced forms; each factor has degree `< d`, so the
row sum has degree `≤ 2d − 2`). -/
noncomputable def rowSum (s : RlinStatement Φ n μ) (z : PolyVec (Rq Φ) μ) (i : Fin n) :
    Polynomial (ZMod q) :=
  ∑ j, (s.M i j).1.toPoly * (z j).1.toPoly

/-- Evaluation of a `Zq[X]`-polynomial at `a ∈ F` through the base-field embedding `φF`
(the `Rq → Zq[X] → F` bridge of milestone F3). -/
noncomputable def evalAt (φF : ZMod q →+* F) (a : F) : Polynomial (ZMod q) →+* F :=
  Polynomial.eval₂RingHom φF a

/-- **The lift's output relation** (Hachi Figure 4 / Lemma 9 residual claims, at the fixed
challenge `α` of the transcript): `w̃ = (z, ρ)` opens `t`; every lifted row vanishes at `α`,
i.e. `∑ⱼ Mᵢⱼ(α)·zⱼ(α) = yᵢ(α) + (α^d + 1)·ρᵢ(α)`; and `w̃` is short. The range claims are
*witness-level* — proven downstream by the zero-check/sumcheck stages and consumed upstream by
Lemma 9's extraction. The final conjunct `bound ≤ s.bound` is the public sanity condition tying
the global norm parameter to the statement's declared `R^lin` bound (see the module
docstring). -/
def relLift (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) :
    Set (LiftStatement Φ K.TCom F n μ × LiftedWitness Φ μ n) :=
  {p |
    K.com p.2 = p.1.2.1 ∧
    (∀ i, evalAt φF p.1.2.2 (rowSum Φ p.1.1 p.2.z i) =
          evalAt φF p.1.2.2 ((p.1.1.yvec i).1.toPoly) +
            evalAt φF p.1.2.2 Φ.φ.toPoly * evalAt φF p.1.2.2 (p.2.ρ i)) ∧
    liftShort Φ bound ρBound p.2 ∧
    bound ≤ p.1.1.bound}

/-- Escape-threaded lift relation — the seam consumed by the batching bridge
(`ZeroCheck/Batch.lean`). -/
def relLiftE (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
    (φF : ZMod q →+* F) :
    Set (LiftStatement Φ K.TCom F n μ × (LiftedWitness Φ μ n ⊕ E)) :=
  (relLift Φ bound ρBound K φF).withEscape K.esc

section Protocol

variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
variable (K : LiftCom (LiftedWitness Φ μ n) E (liftShort Φ bound ρBound))
  (φF : ZMod q →+* F)

/-- The lift's verifier (Hachi Figure 4): a **pure pass-through** extending the statement by the
round-0 commitment `t` and the round-1 challenge `α`. All checks constrain the never-sent
witness and live in `relLift`. -/
def liftVerifier :
    Verifier oSpec (RlinStatement Φ n μ) (LiftStatement Φ K.TCom F n μ)
      (pSpecScalar K.TCom F) where
  verify := fun stmt tr => pure (stmt, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩)

/-- The honest prover skeleton (Hachi Figure 4; completeness is out of scope for Lemma 9): round
0 sends `t := Com(w̃)` for the honestly lifted witness, round 1 receives `α`, and the output
witness is `w̃` itself. The honest computations (quotient extraction `ρᵢ := (∑ Mᵢⱼzⱼ − yᵢ) /ₘ φ`
and the commitment) are the parameters `computeW`/`computeT`, to be instantiated by the
completeness layer from the F3 quotient-lift algebra. -/
def liftProver (WitIn : Type)
    (computeW : RlinStatement Φ n μ → WitIn → LiftedWitness Φ μ n)
    (computeT : RlinStatement Φ n μ → WitIn → K.TCom) :
    Prover oSpec (RlinStatement Φ n μ) WitIn (LiftStatement Φ K.TCom F n μ)
      (LiftedWitness Φ μ n) (pSpecScalar K.TCom F) where
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
* if two branches carry distinct openings `w ≠ w'` of the shared `t`, both are short
  (`relLift`'s `liftShort` conjunct), so `K.collision_mem` yields the weak-binding escape;
* otherwise all `2d` branches share one `w̃`; for each row `i` the defect polynomial
  `rowSum − yᵢ.rep − φ·ρᵢ` (degree `≤ 2d − 2 < 2d` by `w̃.hρ` and representative degree bounds)
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
    (liftVerifier (oSpec := oSpec) Φ bound ρBound K).coordinateWiseSpecialSound init impl
      (scalarStructure (2 * Φ.φ.natDegree) (by omega))
      (relRlinE Φ (n := n) (μ := μ) K.esc)
      (relLiftE Φ bound ρBound K φF) := by
  sorry

/-- **The HMZ25 lift as a `CWSSPackage`** (Hachi [NOZ26] Figure 4 / Lemma 9): the two-round
commit-then-challenge verifier with the plain-special-soundness structure at `k = 2d`, reducing
`relRlinE` to `relLiftE`. The certificate is the sorried `lift_coordinateWiseSpecialSound`. -/
def liftPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hd : 0 < Φ.φ.natDegree) :
    CWSSPackage init impl
      (RlinStatement Φ n μ) (PolyVec (Rq Φ) μ ⊕ E)
      (LiftStatement Φ K.TCom F n μ) (LiftedWitness Φ μ n ⊕ E)
      (pSpecScalar K.TCom F) where
  verifier := liftVerifier (oSpec := oSpec) Φ bound ρBound K
  struct := scalarStructure (2 * Φ.φ.natDegree) (by omega)
  relIn := relRlinE Φ (n := n) (μ := μ) K.esc
  relOut := relLiftE Φ bound ρBound K φF
  isPure := ⟨fun stmt tr => (stmt, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩), fun _ _ => rfl⟩
  isCWSS := lift_coordinateWiseSpecialSound Φ bound ρBound K φF init impl hd

end Protocol

end ArkLib.Lattices.Ajtai.InnerOuter
