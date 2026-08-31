/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.Recursion.ZBatchBridge

/-!
  # Trace handoff — Hachi §4.5, Eqs. (27)–(28) — skeleton

  The recursion-closing adapter: convert the `Z`-packed `F`-claim of Eq. (26) into the **next
  iteration's `Rq`-quadratic statement**, re-entering the chain at the `QuadEval` seam
  (the paper: "this is exactly the type of statement supported natively by Greyhound").

  ## Protocol (one message, guarded)

  * **message (P→V)** — the packed evaluation `p ∈ R′_q` (`Rq Φ'`, the **next** ring, dimension
    `d′`), Eq. (27): `p := eᵀ(σ₋₁(ψ(f))ᵀ ⊗ I)ψ(ŵ)`, where `e`/`f` are the `eq`-tensor halves
    of the low point and `ψ` is the packing bijection of Theorem 2
    (`ArkLib/Data/Lattices/CyclotomicRing/Subfield/Packing.lean`, `psi`);
  * **check (guarded)** — the trace equation `Tr_H(p·…) = (d′/k)·value` (Theorem 2 /
    `traceH_psi_mul_conj`): it reads the packed claim `value`, which the pinned next-iteration
    statement type drops, so it must be a runtime guard — the same argument as the §3.1 head;
  * **output** — the next iteration's `QuadEvalStatement` over `Φ'`: bases `avec`/`bvec` are the
    `eq`-tensor packings of the low point (σ₋₁-twisted), the evaluation is `p`,
    and the outer commitment is the **reinterpretation** of `t` at ring dimension `d′`.

  ## No new commitment — reinterpretation of `t`

  §4.5 sends only `(yᵢ)ᵢ` and `p` (Eq. (28)): the next iteration's commitment **is** the lift
  commitment `t` from Figure 4, *re-read* at ring dimension `d′` — the `Z`-packing (Eq. (25))
  composed with `ψ` is a fixed `Zq`-linear bijection on coefficient tables, and the lift
  commitment's message-packing convention is chosen (`LiftCom` instantiation) to make
  `Com_{d}(w̃) = Com'_{d′}(ψ(ŵ))` a definitional re-indexing. This is what ties the next
  iteration's extracted openings back to `t` (`reinterpretCom` below abstracts the re-reading);
  norm growth under `ψ` is Lemma 6 (`‖ψ(a)‖∞ ≤ 2β`, `cInfNorm_psi_le`).

  ## Soundness shape

  Extraction (sorried): a next-iteration witness at the mapped statement is a weak opening of
  the reinterpreted `t` that is eval-consistent for the `eq`-tensor bases with value `p`
  (`QuadEval`'s plain `relIn` at `Φ'`). The package carries any ambient escape separately.
  Pulling the opening back through the
  `ψ`/`Z`-packing bijection yields an opening `w̃` of `t`; Theorem 2 turns the eval-consistency
  plus the **guard's** trace equation into `hatEval w̃ a₀ = value` — exactly `relHatEval`.
  (The extracted table entries are subfield-valued with small `Eq. (7)`-basis coordinates; the
  `Zq`-entry reading is recovered through the same bijection. The *semantic* content of this
  seam — unlike the `Z`-packing bridge before it — is pinned exactly by the trace: no slack.)

  **Sorried**: the encoding defs (`traceCheck`, `toNextQuadEvalStatement`) and the CWSS theorem.

  ## References

  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
  * [Lyubashevsky, V., Nguyen, N. K., and Plançon, M., *Lattice-Based Zero-Knowledge Proofs and
      Applications: Shorter, Simpler, and More General*][LNP22]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open OracleComp OracleSpec ProtocolSpec CoordinateWise

section Protocol

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
  (Φ' : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ']
variable {n μ : ℕ} {F : Type} [Field F] [BEq F] [LawfulBEq F]
variable (mLow κ : ℕ) (bound bDig : ℕ)
variable {innerRows' messageDigits' outerRows' innerDigits' dRows' m' r' : ℕ}
variable {ι : Type} {oSpec : OracleSpec ι} {σ : Type}

/-- The handoff wire format: one prover message carrying the packed evaluation `p ∈ R′_q`
(Eq. (27)) over the **next** ring `Φ'`. -/
@[reducible] def pSpecHandoff (Φ' : CyclotomicModulus (ZMod q)) : ProtocolSpec 1 :=
  ⟨!v[.P_to_V], !v[Rq Φ']⟩

instance : IsEmpty (pSpecHandoff Φ').ChallengeIdx := ⟨fun ⟨0, h⟩ => nomatch h⟩

instance : ∀ i, SampleableType ((pSpecHandoff Φ').Challenge i) := fun i => isEmptyElim i

/-- The trace check (Eq. (26)/(27) right-hand side, Theorem 2): `Tr_H` of `p` against the
`σ₋₁`-twisted packed `eq`-tail equals `(d′/k)·value`. **Sorried** — `traceHComp` at the
`fixedSubring` instantiation of `F` (decidable via the computable trace). -/
def traceCheck {TCom : Type} (φF : ZMod q →+* F)
    (stmt : HatEvalStatement TCom F mLow) (p : Rq Φ') : Bool :=
  sorry

/-- The next-iteration statement (Eq. (27) as a `QuadEval` claim over `Φ'`): the
**reinterpreted** commitment `reinterpretCom stmt.t`, the `eq`-tensor bases derived
from the low point (σ₋₁-twisted), and the evaluation `p`. (The next iteration's key
`pp'` is not statement data; it enters only the next iteration's relations.) **Sorried** —
the `e`/`f` packing (`psi` on the `eq`-tensor halves) and the split bookkeeping
`mLow = m' + r' + (α' − κ)`. -/
def toNextQuadEvalStatement {TCom : Type} (φF : ZMod q →+* F)
    (reinterpretCom : TCom → Commitment Φ' outerRows')
    (stmt : HatEvalStatement TCom F mLow) (p : Rq Φ') :
    QuadEvalStatement Φ' innerRows' (2 ^ m') messageDigits' outerRows' (2 ^ r') innerDigits'
      dRows' :=
  sorry

/-- The trace-handoff verifier (Hachi §4.5, Eqs. (27)–(28)): **guarded** on the trace check,
outputting the next iteration's `QuadEvalStatement` over `Φ'`. -/
def handoffVerifier {TCom : Type} (φF : ZMod q →+* F)
    (reinterpretCom : TCom → Commitment Φ' outerRows') :
    Verifier oSpec (HatEvalStatement TCom F mLow)
      (QuadEvalStatement Φ' innerRows' (2 ^ m') messageDigits' outerRows' (2 ^ r') innerDigits'
        dRows')
      (pSpecHandoff Φ') where
  verify := fun stmt tr =>
    if traceCheck Φ' mLow φF stmt (tr 0) then
      pure (toNextQuadEvalStatement Φ' mLow φF reinterpretCom stmt (tr 0))
    else failure

omit [NeZero q] [IsCyclotomic Φ] [IsCyclotomic Φ'] [BEq F] [LawfulBEq F] in
/-- **The trace-handoff verifier's guardedness as data** (`Verifier.GuardedForm`): the guard is
`traceCheck` and the verdict is `toNextQuadEvalStatement`, so `verify_eq` is `rfl`.

The package carries this instead of a `Verifier.IsGuarded` instance, because a composed chain must
*run* the left verdict at the seam to know which statement to extract the right factor at (and the
composed escape event must name it too); reading either off the `IsGuarded` existential would cost
`Classical.choice`. This is the chain's closing seam, so its verdict is the next iteration's
`QuadEvalStatement` over `Φ'`. -/
def handoffVerifierGuardedForm {TCom : Type} (φF : ZMod q →+* F)
    (reinterpretCom : TCom → Commitment Φ' outerRows') :
    (handoffVerifier (oSpec := oSpec) Φ' mLow
      (innerRows' := innerRows') (messageDigits' := messageDigits') (innerDigits' := innerDigits')
      (dRows' := dRows') (m' := m') (r' := r') φF reinterpretCom).GuardedForm where
  check := fun stmt tr => traceCheck Φ' mLow φF stmt (tr 0)
  out := fun stmt tr => toNextQuadEvalStatement Φ' mLow φF reinterpretCom stmt (tr 0)
  verify_eq := fun _ _ => rfl

omit [NeZero q] [IsCyclotomic Φ] [IsCyclotomic Φ'] [BEq F] [LawfulBEq F] in
/-- The trace-handoff verifier is guarded — definitionally, by `traceCheck`. -/
theorem handoffVerifier_isGuarded {TCom : Type} (φF : ZMod q →+* F)
    (reinterpretCom : TCom → Commitment Φ' outerRows') :
    (handoffVerifier (oSpec := oSpec) Φ' mLow
      (innerRows' := innerRows') (messageDigits' := messageDigits') (innerDigits' := innerDigits')
      (dRows' := dRows') (m' := m') (r' := r') φF reinterpretCom).IsGuarded :=
  ⟨fun stmt tr => traceCheck Φ' mLow φF stmt (tr 0),
   fun stmt tr => toNextQuadEvalStatement Φ' mLow φF reinterpretCom stmt (tr 0),
   fun _ _ => rfl⟩

/-- The honest trace-handoff prover skeleton: sends `p` (the parameter `computeP`, honestly
Eq. (27)'s `eᵀ(σ₋₁(ψ(f))ᵀ ⊗ I)ψ(ŵ)`), and carries the witness forward as the next iteration's
opening data (the parameter `computeWit` — the ψ-packed re-reading of `w̃`). -/
def handoffProver {TCom WitOut : Type} (φF : ZMod q →+* F)
    (reinterpretCom : TCom → Commitment Φ' outerRows')
    (computeP : HatEvalStatement TCom F mLow → LiftedWitness Φ μ n → Rq Φ')
    (computeWit : LiftedWitness Φ μ n → WitOut) :
    Prover oSpec (HatEvalStatement TCom F mLow) (LiftedWitness Φ μ n)
      (QuadEvalStatement Φ' innerRows' (2 ^ m') messageDigits' outerRows' (2 ^ r') innerDigits'
        dRows')
      WitOut (pSpecHandoff Φ') where
  PrvState
    | 0 => HatEvalStatement TCom F mLow × LiftedWitness Φ μ n
    | 1 => HatEvalStatement TCom F mLow × LiftedWitness Φ μ n
  input := id
  sendMessage
    | ⟨0, _⟩ => fun st => pure (computeP st.1 st.2, st)
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
  output := fun ⟨stmt, wit⟩ =>
    pure (toNextQuadEvalStatement Φ' mLow φF reinterpretCom stmt (computeP stmt wit),
      computeWit wit)

variable [SampleableType F]

/-- **The trace-handoff extraction algorithm.**

**Sorried** — this def is the extraction *algorithm* itself (the transcript-level pull-back of the
proof plan on `handoff_coordinateWiseSpecialSoundWith`).

No `noncomputable` marker: the gap here is the missing algorithm, not an architectural obstruction,
so the marker set stays a record of *computability* debt only. Until the `sorry` is filled the
generated code panics when run. -/
def handoffExtractor
    (zpow : Fin (2 ^ κ) → F)
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    (φF : ZMod q →+* F)
    (reinterpretCom : K.TCom → Commitment Φ' outerRows') :
    Extractor.TreeBased (HatEvalStatement K.TCom F mLow) (LiftedWitness Φ μ n)
      (QuadEvalWitness Φ' innerRows' (2 ^ m') messageDigits' (2 ^ r') innerDigits')
      (pSpecHandoff Φ')
      (CWSSStructure.toShape (CWSSStructure.ofIsEmpty
        (pSpec := pSpecHandoff Φ'))).arity :=
  sorry

/-- **CWSS of the trace handoff — closing the recursion loop, at the named
`handoffExtractor`** (the named form is deliberate — see `Verifier.treeSpecialSoundWith`;
closing this gap means filling the extractor and this specification about it).

**Sorried.** Proof plan: no challenge round, so CWSS collapses to a transcript-level pull-back
(the probability-phrased no-challenge bridge tolerates the guard): acceptance forces
`traceCheck = true`; a next-iteration `relIn` witness at the mapped statement is a weak opening
of `reinterpretCom t` that is eval-consistent for the `eq`-tensor bases with value `p`. Pull the
opening back through the commitment reinterpretation and the `ψ`/`Z`-packing
bijection (`psi_bijective`) to an opening `w̃` of `t`; Theorem 2 (`traceH_psi_mul_conj`) turns
eval-consistency plus the guard's trace equation into `hatEval w̃ a₀ = value` — `relHatEval`
membership. Norm bookkeeping through `ψ` is Lemma 6 (`cInfNorm_psi_le`); the
reinterpretation identity `Com_d(w̃) = Com'_{d′}(ψ(ŵ))` is an obligation of the concrete
`LiftCom` instantiation ([NOZ26] §4.5).

## The `Short` obligation this seam does not discharge — do not paper over it

Since `LiftCom` is indexed by `liftShort Φ bound bDig`, every relation on this side of the
chain carries that predicate, and the pull-back above must **produce** it for the witness it
returns. **At this theorem's free parameters, that is not merely unproven but false**:
`base' βSq' γ' κ'` are unconstrained, so nothing ties the next iteration's norm regime to this
one's. Two things are missing, and neither is a proof-engineering detail:

1. a hypothesis linking `γ'` to `γ`/`bDig` through the `ψ`-packing, so the two regimes are
   comparable at all;
2. an **inverse**-`ψ` norm lemma. `cInfNorm_psi_le` bounds `‖ψ(a)‖∞` from `‖a‖∞` — the wrong
   direction for pulling an opening back — and `psi_bijective` gives no norm bound whatsoever.

Do **not** cite `QuadEval/Reduction.lean`'s `relOut` norm conjuncts as discharging this: those sit
at the leftmost seam, upstream of `liftPackage`, and say nothing about the reinterpreted
commitment. This `sorry` is therefore load-bearing in a way the neighbouring ones are not — it
stands for a gap in the *design*, not just in the formalization. -/
theorem handoff_coordinateWiseSpecialSoundWith
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (zpow : Fin (2 ^ κ) → F)
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    (φF : ZMod q →+* F)
    (pp' : Hachi.PublicParamsD Φ' innerRows' (2 ^ m') messageDigits' outerRows' (2 ^ r')
      innerDigits' dRows')
    (reinterpretCom : K.TCom → Commitment Φ' outerRows')
    (base' : ZMod q) (βSq' γ' κ' : ℕ) :
    Verifier.coordinateWiseSpecialSoundWith init impl
      CWSSStructure.ofIsEmpty
      (relHatEval Φ mLow κ bound bDig zpow K φF)
      (relIn Φ' pp' base' βSq' γ' κ')
      (handoffVerifier (oSpec := oSpec) Φ' mLow φF reinterpretCom)
      (handoffExtractor Φ Φ' mLow κ bound bDig zpow K φF reinterpretCom) := by
  sorry

/-- **The trace handoff as a guarded `GCWSSPackage`** (Hachi §4.5, Eqs. (27)–(28)): the
guarded one-message verifier with the empty challenge structure, reducing the `Z`-packed claim
`relHatEval` to the **next iteration's** `QuadEval` input relation `relIn` over `Φ'` — the recursion
loop's closing seam (the next iteration re-enters at `quadEvalPackage Φ'`, bypassing the
polynomial-level bridge: the bases are `eq`-tensor packings, not monomial bases of a point).

The handoff *re-reads* the existing commitment through `ψ` rather than introducing a new one, hence
carries no escape event. -/
def handoffPackage (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (zpow : Fin (2 ^ κ) → F)
    (K : LiftCom (LiftedWitness Φ μ n) (liftShort Φ bound bDig))
    (φF : ZMod q →+* F)
    (pp' : Hachi.PublicParamsD Φ' innerRows' (2 ^ m') messageDigits' outerRows' (2 ^ r')
      innerDigits' dRows')
    (reinterpretCom : K.TCom → Commitment Φ' outerRows')
    (base' : ZMod q) (βSq' γ' κ' : ℕ) :
    GCWSSPackage init impl
      (HatEvalStatement K.TCom F mLow) (LiftedWitness Φ μ n)
      (QuadEvalStatement Φ' innerRows' (2 ^ m') messageDigits' outerRows' (2 ^ r') innerDigits'
        dRows')
      (QuadEvalWitness Φ' innerRows' (2 ^ m') messageDigits' (2 ^ r') innerDigits')
      (pSpecHandoff Φ') where
  verifier := handoffVerifier (oSpec := oSpec) Φ' mLow φF reinterpretCom
  struct := CWSSStructure.ofIsEmpty
  relIn := relHatEval Φ mLow κ bound bDig zpow K φF
  relOut := relIn Φ' pp' base' βSq' γ' κ'
  isGuarded := handoffVerifierGuardedForm Φ' mLow φF reinterpretCom
  extractor := handoffExtractor Φ Φ' mLow κ bound bDig zpow K φF reinterpretCom
  isCWSS := handoff_coordinateWiseSpecialSoundWith Φ Φ' mLow κ bound bDig init impl zpow K
    φF pp' reinterpretCom base' βSq' γ' κ'

end Protocol

end ArkLib.Lattices.Ajtai.InnerOuter
