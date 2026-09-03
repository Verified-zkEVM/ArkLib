/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.QuadEval.Gadgets
import ArkLib.Commitments.Functional.Hachi.InnerOuter.Security
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.SingleRound

/-!
  # Hachi polynomial-evaluation reduction (`QuadEval`) — statement, relations, protocol
    (Hachi §4.2, Figure 3)

  Hachi's polynomial-evaluation reduction proves `f(x) = y` by rewriting the evaluation as the
  quadratic form `bᵀ M a` (Eq. (12): `a`/`b` are the split evaluation bases, `M` the committed
  coefficient matrix) and folding the `2ʳ` carrier blocks under the verifier's challenge vector
  — hence the name `QuadEval`. The *carrier* `w = M a` collects the per-block partial
  evaluations (so `y = bᵀ w`); `ŵ` denotes its gadget decomposition `G⁻¹(w)`. It is Hachi's
  multilinear / inner-outer lift of Greyhound's [NS24, §3.1] polynomial-evaluation protocol.

  This file carries the reduction's *data*: the statement/response/witness types
  (`QuadEvalStatement`, `QuadEvalResponse`, `QuadEvalWitness`), the short-challenge space
  (`ShortChallenge`, shortness carried by the subtype), the relations (`derivedMsgMatrix`,
  `evalConsistency` = Eq. (15), `relOut` = Eq. (20) + the `S_b` range checks, `relIn` = weak
  opening, `dShort`). The commitment key `(A, B, D)` is the *parameter* `pp` of the relations and
  of the Module-SIS **break vocabulary** (`QuadEvalSISBreak` / `quadEvalSISSet`), never statement
  data — breaks are checkable against the fixed key alone, which ties them to the actual key rather
  than an adversary-chosen matrix. The reduction's escape *event* over that vocabulary,
  `quadEvalEscLocal`, lives in `QuadEval/Soundness.lean`. The file closes with the protocol (the
  two-round
  `pSpec ⟨!v[.P_to_V, .V_to_P], !v[CarrierCom, Fin 2ʳ → C]⟩` of `CoordinateWise.SingleRound`,
  the pure pass-through `verifier`, and the honest `prover`). Round 0 (P→V) sends the
  short commitment `v = D ŵ`; round 1 (V→P) is the challenge vector; the triple `(ŵ, t̂, ẑ)` is
  the **output witness** (`QuadEvalResponse`, never sent — §4.3 proves knowledge of it instead),
  so the verifier is a pure pass-through.

  **Hachi Lemma 8** — coordinate-wise special soundness of this reduction (from `2ʳ+1` accepting
  transcripts with challenge vectors in `SS(C, 2ʳ, 2)`), and its subtract-and-divide extractor —
  lives in the companion `QuadEval/Soundness.lean`.

  The file sits inside `namespace ArkLib.Lattices.Ajtai.InnerOuter` (required: that namespace
  activates the scoped `PolyVec`/`*ᵥ`/`•ᵥ`/`dot`/`splitForm`), with `open WeakBinding` (so
  `VerifiedOpening`/`outerShort` resolve). Never `open ArkLib.Lattices` here (the `⬝ᵥ` token is
  ambiguous between `Matrix.dotProduct` and `ArkLib.Lattices.dot`); spell `dot _ _`.

  ## References

  * [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open WeakBinding
open OracleComp OracleSpec ProtocolSpec CoordinateWise CoordinateWise.SingleRound

/-! ## Generic definitions (any coefficient field `R`) -/

section Defs

variable {R : Type} [Field R] [BEq R] [LawfulBEq R] (Φ : CyclotomicModulus R) [IsCyclotomic Φ]
variable {innerRows messageRows messageDigits outerRows blocks innerDigits dRows zDigits : Nat}

/-- The **carrier commitment** space (`CarrierCom` = carrier commitment): the short commitment
`v = D ŵ` lives in the `D`-row space. -/
abbrev CarrierCom (Φ : CyclotomicModulus R) (dRows : Nat) := Simple.Commitment Φ dRows

/-- Input statement of Hachi's polynomial-evaluation reduction (Hachi §4.2, Figure 3): the outer
commitment `u`, the two evaluation basis vectors `a ∈ Rq^{2^m}` (`avec`) and `b ∈ Rq^{2^r}`
(`bvec`) of Eq. (12), and the claimed evaluation `y = u_eval`.

The public parameters `(A, B, D)` are **not** statement data: the commitment key is fixed once
for the whole reduction (honestly, sampled by `keygen`) and enters the relations as the
parameter `pp`. Keeping the key out of the adversary-chosen statement is what ties the parallel
Module-SIS break vocabulary (`quadEvalSISSet`) to the *actual* key — a statement-carried key would
let breaks be validated against an adversary-chosen matrix.

The dimension parameters (`messageRows`, `blocks`, …) are left generic on the structure (the
full profile of the reduction instance, shared with the key's `PublicParamsD` type); the
relations and protocol below specialize `messageRows := 2^m` and `blocks := 2^r` (the paper's
Figure 3 shape), matching the genericity of the other reduction structures. -/
structure QuadEvalStatement (Φ : CyclotomicModulus R)
    (innerRows messageRows messageDigits outerRows blocks innerDigits dRows : Nat) where
  /-- The outer commitment `u`. -/
  u : Commitment Φ outerRows
  /-- The inner evaluation basis `aᵀ = (x_{r+1}^{j₁} ⋯ x_l^{j_m})_j ∈ Rq^{2^m}` (Eq. 12). -/
  avec : PolyVec (Rq Φ) messageRows
  /-- The outer evaluation basis `bᵀ = (x_1^{i₁} ⋯ x_r^{i_r})_i ∈ Rq^{2^r}` (Eq. 12). -/
  bvec : PolyVec (Rq Φ) blocks
  /-- The claimed evaluation `y = u_eval = f(x)`. -/
  y : Rq Φ

/-- The reduction's output witness `(ŵ, t̂, ẑ)` of Hachi Eq. (20) — Figure 3's final "message",
never sent in the composed protocol (§4.3 proves knowledge of it instead). Block-major layouts
(`finProdFinEquiv`, block = outer index). -/
structure QuadEvalResponse (Φ : CyclotomicModulus R)
    (innerRows messageRows messageDigits blocks innerDigits zDigits : Nat) where
  /-- `ŵ := G⁻¹_{2^r}(w)`, the decomposed carrier (block-major, `blocks · messageDigits`). -/
  carrierDec : PolyVec (Rq Φ) (blocks * messageDigits)
  /-- `t̂ = (t̂ᵢ)ᵢ`, the per-block inner decompositions. -/
  innerDec : PolyVec (PolyVec (Rq Φ) (innerRows * innerDigits)) blocks
  /-- `ẑ := J⁻¹(z)`, the decomposed masked opening (`τ = zDigits` digits). -/
  zDec : PolyVec (Rq Φ) ((messageRows * messageDigits) * zDigits)

/-- `QuadEvalResponse` is inhabited (the all-zero triple). -/
instance : Nonempty
    (QuadEvalResponse Φ innerRows messageRows messageDigits blocks innerDigits zDigits) :=
  ⟨⟨fun _ => 0, fun _ _ => 0, fun _ => 0⟩⟩

/-- The input-side witness of `QuadEval`: a genuine weak opening for `u`.

Module-SIS breakages found by Hachi Lemma 8 are deliberately not constructors of this type: they are
reported by the escape event `quadEvalEscLocal` (`QuadEval/Soundness.lean`), a predicate on the
observable `(statement, transcript tree)`. -/
abbrev QuadEvalWitness (Φ : CyclotomicModulus R)
    (innerRows messageRows messageDigits blocks innerDigits : Nat) :=
  Opening Φ innerRows messageRows messageDigits blocks innerDigits

/-- `QuadEvalWitness` is inhabited by the all-zero opening. The value need not satisfy `relIn`;
the instance is used only as the total fallback of generic extractors outside accepting trees. -/
instance : Nonempty (QuadEvalWitness Φ innerRows messageRows messageDigits blocks innerDigits) :=
  ⟨{ message := fun _ _ => 0, innerDecomp := fun _ _ => 0, challenge := fun _ => 0 }⟩

/-- A concrete Module-SIS break produced by the three-case extractor of Hachi Lemma 8: a candidate
kernel vector for the outer commitment matrix `B` or the carrier commitment matrix `D`. The break
carries only the solution; validity (`quadEvalSISSet`) is checked against the *fixed* commitment key
`pp` — a parameter of the reduction, not statement data — so it is a break of the actual key.
(Carrying the matrix inside the break instead would let it be validated against an arbitrary — e.g.
zero — matrix, making the set free.) -/
inductive QuadEvalSISBreak (Φ : CyclotomicModulus R)
    (innerRows messageDigits outerRows blocks innerDigits dRows : Nat) where
  /-- A short nonzero kernel vector for the outer commitment matrix `B`. -/
  | msisB (solution : ModuleSIS.Solution Φ (blocks * (innerRows * innerDigits)))
  /-- A short nonzero kernel vector for the carrier commitment matrix `D`. -/
  | msisD (solution : ModuleSIS.Solution Φ (blocks * messageDigits))

end Defs

/-! ## The challenge space (over `ZMod q`, where the norms live) -/

section ShortChallenge

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]

/-- **The reduction's challenge space, carried by the type** (Hachi §4.2): the paper's
`C ⊆ {c ∈ Rq : ‖c‖₁ ≤ ω}` is rendered as the subtype of `ℓ₁`-short ring elements. The
verifier's relation `relOut` therefore needs NO challenge-norm checks (faithful to Eq. (20),
which never checks the challenge); extraction recovers `‖cᵢ‖₁ ≤ ω` from the subtype property. -/
def ShortChallenge (Φ : CyclotomicModulus (ZMod q)) (ω : ℕ) : Type :=
  {c : Rq Φ // Rq.l1Norm Φ c ≤ ω}

/-- The challenge space has decidable equality (inherited from `Rq Φ`, whose representatives are
canonical). This is the alphabet-side hypothesis of the star-center search
(`CoordinateWise.SingleRound.central`/`sib`), so it is what keeps extraction executable; `Type` is
opaque to instance search through a plain `def`, hence the explicit instance. -/
instance (Φ : CyclotomicModulus (ZMod q)) (ω : ℕ) : DecidableEq (ShortChallenge Φ ω) :=
  Subtype.instDecidableEq

variable {Φ : CyclotomicModulus (ZMod q)} [IsCyclotomic Φ] {ω : ℕ}

namespace ShortChallenge

/-- The underlying ring element `c ∈ Rq` of a short challenge (Hachi §4.2's challenge `cᵢ`). -/
def val (c : ShortChallenge Φ ω) : Rq Φ := Subtype.val c

omit [NeZero q] [IsCyclotomic Φ] in
/-- The subtype bound: every challenge is `ℓ₁`-short. -/
theorem l1Norm_le (c : ShortChallenge Φ ω) : ‖c.val‖₁ ≤ ω := Subtype.prop c

/-- Coordinate difference of two short challenges is `ℓ₁`-bounded by `2ω` — the extractor's
`hshort` for the slack `c̄ⱼ = c_{j,j} - c_{0,j}` (Hachi Lemma 8), for free from the subtype. -/
theorem l1Norm_val_sub_le (c c' : ShortChallenge Φ ω) : ‖c.val - c'.val‖₁ ≤ 2 * ω :=
  calc ‖c.val - c'.val‖₁ ≤ ‖c.val‖₁ + ‖c'.val‖₁ := Rq.l1Norm_sub_le Φ c.val c'.val
    _ ≤ ω + ω := Nat.add_le_add c.l1Norm_le c'.l1Norm_le
    _ = 2 * ω := (Nat.two_mul ω).symm

omit [NeZero q] [IsCyclotomic Φ] in
/-- `≠` on the subtype transfers to `≠` on the underlying ring elements — the extractor's
nonzero-slack input (`CoordEq` gives subtype-`≠` at the differing coordinate). -/
theorem val_ne_of_ne {c c' : ShortChallenge Φ ω} (h : c ≠ c') : c.val ≠ c'.val :=
  fun hval => h (Subtype.ext hval)

end ShortChallenge

end ShortChallenge

/-! ## Eval consistency (Eq. 15) and the relations -/

section ZModDefs

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {innerRows messageRows messageDigits outerRows blocks innerDigits dRows zDigits
  zBound m r : Nat}

/-- The matrix `M` of Hachi Eq. (15): row `i` = derived message block `G_{2^m} · sᵢ`; rows are
indexed by the outer basis `b`, columns by the inner basis `a`. -/
def derivedMsgMatrix (base : ZMod q)
    (o : Opening Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :
    PolyMatrix (Rq Φ) (2 ^ r) (2 ^ m) := fun i k => derivedMessage Φ base o.toDecomp i k

/-- Eq. (15): the derived messages of the weak opening evaluate to `y` under the split
bilinear form (`splitForm`, argument order `b a` load-bearing). -/
def evalConsistency (base : ZMod q) (a : PolyVec (Rq Φ) (2 ^ m)) (b : PolyVec (Rq Φ) (2 ^ r))
    (y : Rq Φ) (o : Opening Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) : Prop :=
  splitForm (derivedMsgMatrix Φ base o) b a = y

/-- Shortness predicate for the extracted `D`-kernel witness (Hachi Lemma 8, case (B)): the
`D`-matrix analogue of `outerShort`, at `subLInftyNormBound γ = 2·γ`. -/
def dShort (γ : ℕ) : ModuleSIS.Solution Φ (blocks * messageDigits) → Bool :=
  fun z => decide (vecLInftyNorm Φ z ≤ subLInftyNormBound γ)

/-- The set of **valid** Module-SIS breaks that `QuadEval`'s extraction may exhibit, **relative to
the fixed commitment key `pp`**: solutions are checked against `pp`'s `B` matrix (a divergent inner
decomposition) or its `D` matrix (a divergent carrier decomposition). Checkability against the key
alone — never against statement data — is what makes this a genuine hardness target: an element is a
Module-SIS break of the *actual* key ([NOZ26] Remark 2 / Lemma 7).

This set is the target of the reduction's escape event `quadEvalEscLocal`
(`QuadEval/Soundness.lean`), which fires on `(stmt, tree)` exactly when the tree's own
`relOut`-responses make `buildWitness` return one of its elements. -/
def quadEvalSISSet
    (pp : Hachi.PublicParamsD Φ innerRows messageRows messageDigits outerRows blocks innerDigits
      dRows) (γ : ℕ) :
    Set (QuadEvalSISBreak Φ innerRows messageDigits outerRows blocks innerDigits dRows) :=
  { e | match e with
    | .msisB solution =>
        ModuleSIS.relation Φ (outerShort Φ γ) pp.outerMatrix solution = true
    | .msisD solution =>
        ModuleSIS.relation Φ (dShort Φ γ) pp.dMatrix solution = true }

/-- **`relOut` — Hachi Eq. (20) (rows c1–c5 verbatim) plus a symmetric-`ℓ∞`-ball model of the
`S_b` range checks (c6)** on `((stmt, v, c), (ŵ, t̂, ẑ))`, with `z := J ẑ`:

* c1: `D ŵ = v`
* c2: `B (flatten t̂) = u`
* c3: `bᵀ (G_{2^r} ŵ) = y` (row 3 of Eq. (20), `u_eval`)
* c4: `(cᵀ ⊗ G₁) ŵ = aᵀ G_{2^m} J ẑ` (row 4; challenges coerced from the subtype)
* c5: `(cᵀ ⊗ G_{n_A}) t̂ = A J ẑ` (row 5)
* c6: the `S_b` range checks, as symmetric `ℓ∞` balls `≤ γ`.

**`S_b` modeling (a deliberate generalization).** Eq. (20) checks `(ŵ, t̂, ẑ) ∈ S_b^…`, whose
elements have centered coefficients in `[⌈-b/2⌉, ⌈b/2⌉-1]`; c6 instead uses the symmetric ball
`‖·‖∞ ≤ γ`, so `relOut` is *not* pointwise identical to Eq. (20) — it is the strictly weaker
(larger) relation obtained by replacing the `S_b` box with its enclosing `ℓ∞` ball. For any
`γ ≥ ⌊b/2⌋` the paper's `S_b` box is **contained** in c6's ball, hence `{Eq. (20)-valid
transcripts} ⊆ relOut`: every honest/paper-accepted transcript is `relOut`-valid, so the CWSS
theorem below covers the paper's verifier. This box→ball containment is formalized faithfully just
below: the paper's exact `S_b` output relation is `paperRelOut` (built from the box `InSb`, Hachi
[NOZ26] §2.1), and the inclusion is `paperRelOut_subset_relOut`. This generalized `relOut` is the
reduction's intended output relation and the one downstream Hachi code should cite. No
challenge-norm checks appear (the challenge
TYPE carries `‖cᵢ‖₁ ≤ ω`), and no `‖z‖₂²` check appears (`‖z‖∞ ≤ …` is derived downstream from
c6's `‖ẑ‖∞ ≤ γ` via the `J`-recomposition norm lemma, `Gadget/Norms.lean`) — both exactly as in the
paper. `pp` is the fixed commitment key `(A, B, D)` the c1/c2/c5 rows check against. -/
def relOut
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (ω γ : ℕ) :
    Set ((QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows ×
          CarrierCom Φ dRows × (Fin (2 ^ r) → ShortChallenge Φ ω)) ×
         QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits) :=
  { p | match p with
    | ((stmt, v, chals), resp) =>
      let c : PolyVec (Rq Φ) (2 ^ r) := fun i => (chals i).val
      let z : PolyVec (Rq Φ) ((2 ^ m) * messageDigits) :=
        Hachi.jMatrix Φ base ((2 ^ m) * messageDigits) zDigits *ᵥ resp.zDec
      -- c1: `D ŵ = v`
      Simple.commit Φ pp.dMatrix resp.carrierDec = v ∧
      -- c2: `B (flatten t̂) = u`
      Simple.commit Φ pp.outerMatrix (PolyVec.flattenBlocks resp.innerDec) = stmt.u ∧
      -- c3: `bᵀ (G_{2^r} ŵ) = y`
      dot stmt.bvec (gadgetMatrix Φ base (2 ^ r) messageDigits *ᵥ resp.carrierDec) = stmt.y ∧
      -- c4: `(cᵀ ⊗ G₁) ŵ = aᵀ (G_{2^m} z)`
      Hachi.tensorG1 Φ base messageDigits c resp.carrierDec =
        dot stmt.avec (gadgetMatrix Φ base (2 ^ m) messageDigits *ᵥ z) ∧
      -- c5: `(cᵀ ⊗ G_{n_A}) t̂ = A z`
      Hachi.tensorG Φ base innerRows innerDigits c resp.innerDec =
        pp.innerMatrix *ᵥ z ∧
      -- c6: the `S_b` range checks (as `ℓ∞` balls)
      vecLInftyNorm Φ resp.carrierDec ≤ γ ∧
      vecLInftyNorm Φ (PolyVec.flattenBlocks resp.innerDec) ≤ γ ∧
      vecLInftyNorm Φ resp.zDec ≤ γ }

/-! ### The paper's exact `S_b` range check and the `paperRelOut ⊆ relOut` containment

`relOut` relaxes Eq. (20)'s `S_b` box (Hachi [NOZ26] §2.1) to a symmetric `ℓ∞` ball. Here we
formalize that box faithfully (`InSb`) and prove that the paper's exact output relation
`paperRelOut` is contained in `relOut`, so the Lemma 8 CWSS theorem covers the paper's verifier. -/

/-- **The paper's balanced-digit box `S_β`** (Hachi [NOZ26] §2.1, p. 9): a ring element lies in
`S_β` when every centered coefficient (its `ZMod.valMinAbs` representative) is in the box
`[⌈-β/2⌉, ⌈β/2⌉-1]`. In `ℕ`/`ℤ` arithmetic these endpoints are `⌈-β/2⌉ = -(β/2)` and
`⌈β/2⌉-1 = (β+1)/2 - 1` (both `/` are `Nat` division). This is exactly the set the Figure 3
verifier checks in Eq. (20) (`(ŵ, t̂, ẑ) ∈ S_b`). -/
def InSb (β : ℕ) (a : Rq Φ) : Prop :=
  ∀ k, k < Φ.φ.natDegree →
    -((β / 2 : ℕ) : ℤ) ≤ (a.1.coeff k).valMinAbs ∧
      (a.1.coeff k).valMinAbs ≤ (((β + 1) / 2 : ℕ) : ℤ) - 1

/-- Vector version of `InSb`: every entry lies in the box `S_β`. -/
def vecInSb (β : ℕ) {cols : ℕ} (z : PolyVec (Rq Φ) cols) : Prop := ∀ i, InSb Φ β (z i)

omit [NeZero q] [IsCyclotomic Φ] in
/-- **Box ⊆ ball.** An `S_β` ring element has centered `ℓ∞` norm `≤ γ` for any `γ ≥ ⌊β/2⌋`: the box
`[⌈-β/2⌉, ⌈β/2⌉-1]` has maximum centered magnitude `⌊β/2⌋ = β/2` (for both parities of `β`). -/
theorem lInftyNorm_le_of_InSb {β γ : ℕ} (hγ : β / 2 ≤ γ) {a : Rq Φ} (h : InSb Φ β a) :
    Rq.lInftyNorm Φ a ≤ γ := by
  unfold Rq.lInftyNorm
  refine Finset.sup_le fun k hk => ?_
  obtain ⟨hlo, hhi⟩ := h k (Finset.mem_range.mp hk)
  omega

omit [NeZero q] [IsCyclotomic Φ] in
/-- Vector box ⊆ ball: `vecInSb β z → vecLInftyNorm z ≤ γ` for any `γ ≥ ⌊β/2⌋`. -/
theorem vecLInftyNorm_le_of_vecInSb {β γ cols : ℕ} (hγ : β / 2 ≤ γ)
    {z : PolyVec (Rq Φ) cols} (h : vecInSb Φ β z) : vecLInftyNorm Φ z ≤ γ := by
  unfold vecLInftyNorm
  exact Finset.sup_le fun i _ => lInftyNorm_le_of_InSb Φ hγ (h i)

omit [NeZero q] [IsCyclotomic Φ] in
/-- Box membership passes through block flattening: `flattenBlocks` only re-indexes, so the
flattened vector lies in `S_β` as soon as every block does. (The `ℓ∞` analogue is
`vecLInftyNorm_flattenBlocks_le`.) -/
theorem vecInSb_flattenBlocks {β blocks width : ℕ}
    (xs : PolyVec (PolyVec (Rq Φ) width) blocks) (h : ∀ i, vecInSb Φ β (xs i)) :
    vecInSb Φ β (PolyVec.flattenBlocks xs) :=
  fun j => h (finProdFinEquiv.symm j).1 (finProdFinEquiv.symm j).2

/-- **`paperRelOut` — the Figure 3 / Eq. (20) verifier verbatim.** Identical to `relOut` except the
c6 range checks are the paper's exact `S_b` box membership (`vecInSb`, Hachi [NOZ26] §2.1) instead
of the symmetric `ℓ∞` ball. This is the relation the Hachi verifier actually checks; rows c1–c5
mirror `relOut` verbatim (only c6 differs). -/
def paperRelOut
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (ω b : ℕ) :
    Set ((QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows ×
          CarrierCom Φ dRows × (Fin (2 ^ r) → ShortChallenge Φ ω)) ×
         QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits) :=
  { p | match p with
    | ((stmt, v, chals), resp) =>
      let c : PolyVec (Rq Φ) (2 ^ r) := fun i => (chals i).val
      let z : PolyVec (Rq Φ) ((2 ^ m) * messageDigits) :=
        Hachi.jMatrix Φ base ((2 ^ m) * messageDigits) zDigits *ᵥ resp.zDec
      -- c1–c5: the linear system, identical to `relOut`
      Simple.commit Φ pp.dMatrix resp.carrierDec = v ∧
      Simple.commit Φ pp.outerMatrix (PolyVec.flattenBlocks resp.innerDec) = stmt.u ∧
      dot stmt.bvec (gadgetMatrix Φ base (2 ^ r) messageDigits *ᵥ resp.carrierDec) = stmt.y ∧
      Hachi.tensorG1 Φ base messageDigits c resp.carrierDec =
        dot stmt.avec (gadgetMatrix Φ base (2 ^ m) messageDigits *ᵥ z) ∧
      Hachi.tensorG Φ base innerRows innerDigits c resp.innerDec =
        pp.innerMatrix *ᵥ z ∧
      -- c6: the paper's exact `S_b` box (Eq. (20)'s `(ŵ, t̂, ẑ) ∈ S_b`)
      vecInSb Φ b resp.carrierDec ∧
      vecInSb Φ b (PolyVec.flattenBlocks resp.innerDec) ∧
      vecInSb Φ b resp.zDec }

omit [NeZero q] in
/-- **`paperRelOut ⊆ relOut`** — the paper-to-code containment (the reviewer's `paper_relOut ⊆
relOut`). Every transcript the Figure 3 verifier accepts (Eq. (20), `(ŵ, t̂, ẑ) ∈ S_b`) is accepted
by ArkLib's generalized `relOut` at any range `γ ≥ ⌊b/2⌋`: rows c1–c5 pass through verbatim, and
each `S_b` box check (`vecInSb b`) implies the ball check `vecLInftyNorm ≤ γ` via
`vecLInftyNorm_le_of_vecInSb`. In particular at the paper's own `γ := b` (`b ≥ ⌊b/2⌋`) this shows
the Lemma 8 CWSS theorem (`quadEval_coordinateWiseSpecialSoundWithEscape`) covers the paper's
verifier. -/
theorem paperRelOut_subset_relOut
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (ω : ℕ) {b γ : ℕ} (hγ : b / 2 ≤ γ) :
    paperRelOut (zDigits := zDigits) Φ pp base ω b
      ⊆ relOut (zDigits := zDigits) Φ pp base ω γ := by
  rintro ⟨⟨stmt, v, chals⟩, resp⟩ ⟨h1, h2, h3, h4, h5, hb1, hb2, hb3⟩
  exact ⟨h1, h2, h3, h4, h5,
    vecLInftyNorm_le_of_vecInSb Φ hγ hb1,
    vecLInftyNorm_le_of_vecInSb Φ hγ hb2,
    vecLInftyNorm_le_of_vecInSb Φ hγ hb3⟩

/-- **`relIn` — the ordinary input relation of `QuadEval`**: a weak `VerifiedOpening` for `u` under
the fixed key `pp` that is also eval-consistent (Eq. 15). Module-SIS outcomes are not witnesses of
this relation; they are reported by the escape event `quadEvalEscLocal`
(`QuadEval/Soundness.lean`). -/
def relIn
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (βSq γ κ : ℕ) :
    Set (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows ×
         QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :=
  { p | VerifiedOpening Φ base βSq γ κ pp.toPublicParams p.1.u p.2 ∧
      evalConsistency Φ base p.1.avec p.1.bvec p.1.y p.2 }

/-- **`relIn` with the honest committer's message decomposition pinned `ℓ∞`-short** — the
correctness-side input relation of the bounded-`z` reading.

The extra conjunct is exactly what the honest-`z` bound needs and nothing more. It is a genuine
strengthening (a `relIn` member need not have short message blocks), so it belongs in the relation,
where the layer that *chose* the committer's decomposition establishes it: for the balanced
committer it is `gadgetDecompose_vecLInftyNorm_le_of_digit_le` at
`balancedZmodDigit_natAbs_le`, giving `msgBound = ⌊b/2⌋`. `relInMsgShort_subset_relIn` is the
forgetful inclusion, so nothing downstream of `relOut` — in particular no soundness statement —
sees the strengthening. -/
def relInMsgShort
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (βSq γ κ msgBound : ℕ) :
    Set (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows ×
         QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :=
  { p | p ∈ relIn Φ pp base βSq γ κ ∧
      ∀ i, vecLInftyNorm Φ (p.2.message i) ≤ msgBound }

omit [NeZero q] in
/-- **The forgetful inclusion `relInMsgShort ⊆ relIn`.** The strengthening is correctness-only: it
never reaches a soundness statement, and any consumer of `relIn` accepts a `relInMsgShort`
member. -/
theorem relInMsgShort_subset_relIn
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows) (base : ZMod q) (βSq γ κ msgBound : ℕ) :
    relInMsgShort Φ pp base βSq γ κ msgBound ⊆ relIn Φ pp base βSq γ κ :=
  fun _ h => h.1

/-! ## The protocol: pure pass-through verifier and honest prover -/

section Protocol

variable {ι : Type} {oSpec : OracleSpec ι} {ω : ℕ}

/-- The reduction's verifier (Hachi §4.2, Figure 3) is a **pure pass-through**: it re-emits the
statement, the round-0 carrier commitment `v`, and the round-1 challenge vector. The Eq.-(20)
checks live in `relOut` (the `(ŵ, t̂, ẑ)` triple is never sent — §4.3 proves knowledge of it),
so there is no runtime `guard`. -/
def verifier :
    Verifier oSpec
      (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
      (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows ×
        CarrierCom Φ dRows × (Fin (2 ^ r) → ShortChallenge Φ ω))
      (pSpec (CarrierCom Φ dRows) (ShortChallenge Φ ω) r) where
  verify := fun stmt tr => pure (stmt, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩)

/-- **The pass-through verifier's purity as data** (`Verifier.PureForm`): the verdict is the
pass-through triple itself, so `verify_eq` is `rfl`.

The `QuadEval` package carries this instead of a `Verifier.IsPure` instance, because a composed
chain must *run* the left verdict at the seam to know which statement to extract the right factor
at, and reading that function off the `IsPure` existential would cost `Classical.choice`. -/
def verifierPureForm : (verifier (oSpec := oSpec) (ω := ω) Φ
    (innerRows := innerRows) (messageDigits := messageDigits) (outerRows := outerRows)
    (innerDigits := innerDigits) (dRows := dRows) (m := m) (r := r)).PureForm where
  verify := fun stmt tr => (stmt, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩)
  verify_eq := fun _ _ => rfl

/-- The honest prover (Hachi §4.2, Figure 3; completeness is out of scope for Lemma 8): round 0
sends the carrier commitment `v`, round 1 receives the challenge vector, and the output witness
is the `QuadEvalResponse` `(ŵ, t̂, ẑ)` of Eq. (20). The honest computations (`v = D ŵ` with
`ŵ = G⁻¹(w)`, `ẑ = J⁻¹(Σᵢ cᵢ sᵢ)`, …) are the parameters `computeV` / `computeResp`, to be
instantiated by the completeness layer from the `QuadEval/Gadgets` carrier/decomposition
definitions. -/
def prover (WitIn : Type)
    (computeV :
      QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows →
      WitIn → CarrierCom Φ dRows)
    (computeResp :
      QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows →
      WitIn → (Fin (2 ^ r) → ShortChallenge Φ ω) →
      QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits) :
    Prover oSpec
      (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
      WitIn
      (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows ×
        CarrierCom Φ dRows × (Fin (2 ^ r) → ShortChallenge Φ ω))
      (QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits)
      (pSpec (CarrierCom Φ dRows) (ShortChallenge Φ ω) r) where
  PrvState
    | 0 =>
      QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows
        × WitIn
    | 1 =>
      QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows
        × WitIn
    | 2 =>
      (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows
          × WitIn) × (Fin (2 ^ r) → ShortChallenge Φ ω)
  input := id
  sendMessage
    | ⟨0, _⟩ => fun st => pure (computeV st.1 st.2, st)
    | ⟨1, h⟩ => nomatch h
  receiveChallenge
    | ⟨0, h⟩ => nomatch h
    | ⟨1, _⟩ => fun st => pure fun c => (st, c)
  output := fun ⟨⟨stmt, wit⟩, c⟩ =>
    pure ((stmt, computeV stmt wit, c), computeResp stmt wit c)

/-! ### The honest computations, and the protocol object

`prover` above is parametric in the two honest computations. Here they are instantiated with the
concrete gadget algebra of `QuadEval/Gadgets.lean`, giving the actual Figure-3 prover; pairing
that with `verifier` gives the **protocol** `quadEvalReduction` — the
computable object an honest execution runs, and the one perfect completeness is stated about
(`QuadEval/Completeness.lean`). The Lemma-8 certificate `quadEvalPackage`
(`QuadEval/Soundness.lean`) is a statement about the *same* verifier; that they cannot drift apart
is recorded there by `quadEvalPackage_verifier_eq_quadEvalReduction_verifier`. -/

/-- **The honest round-0 message** `v = D ŵ` (Hachi Eq. (16), Figure 3): the short commitment under
`D` of the carrier decomposition `ŵ = G⁻¹(w)`, where the carrier `wᵢ = aᵀ G sᵢ` is assembled from
the statement's inner evaluation basis `a` and the witness's message blocks `sᵢ`. -/
def honestComputeV
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    {base : ZMod q} (ddCarrier : DigitDecomposition base messageDigits)
    (stmt : QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (wit : QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :
    CarrierCom Φ dRows :=
  Hachi.carrierCommit Φ pp.dMatrix ddCarrier stmt.avec wit.message

/-- **The honest masked opening** `z = Σᵢ cᵢ sᵢ` (Hachi Eq. (19)): the challenge-weighted fold of
the witness's message blocks. It is never sent; the prover hands on its decomposition
`ẑ = J⁻¹(z)`, and the verifier's Eq.-(20) rows c4/c5 reconstruct `z = J ẑ`. -/
def honestZ (wit : QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
    (c : Fin (2 ^ r) → ShortChallenge Φ ω) : PolyVec (Rq Φ) ((2 ^ m) * messageDigits) :=
  ∑ i : Fin (2 ^ r), (c i).val •ᵥ wit.message i

/-- **The honest output witness** `(ŵ, t̂, ẑ)` of Hachi Eq. (20): the carrier decomposition
`ŵ = G⁻¹(w)` committed in round 0, the witness's own inner decompositions `t̂`, and the
decomposition `ẑ = J⁻¹(z)` of the masked opening `z = Σᵢ cᵢ sᵢ`.

The `z` step uses a **`BoundedDigitDecomposition`** (`Gadget/Core.lean`), *not* a full-width one:
`z` is deterministically short in an honest run, so the digit count `τ = zDigits` is sized from
that bound and may be far below `⌈log_b q⌉` (at the `ℓ = 30` parameters with ArkLib's
conservative `τ = 5`, `Params.lean`, that is `τ = 5 < δ = 8`, and `q ≤ 16⁵` is false). The digit
map is total, so this remains a plain computable function — only the
round-trip `z = J ẑ` needs shortness, and that is discharged in the completeness layer. The carrier
step keeps the ordinary full-width `DigitDecomposition`, since carrier coefficients are arbitrary
residues. -/
def honestComputeResp {base : ZMod q} (ddCarrier : DigitDecomposition base messageDigits)
    (ddZ : BoundedDigitDecomposition base zDigits zBound)
    (stmt : QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (wit : QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
    (c : Fin (2 ^ r) → ShortChallenge Φ ω) :
    QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits where
  carrierDec := Hachi.carrierDecomp Φ ddCarrier stmt.avec wit.message
  innerDec := wit.innerDecomp
  zDec := Hachi.zDecompBounded Φ ddZ (honestZ Φ wit c)

/-- **The `QuadEval` protocol** (Hachi §4.2, Figure 3): the honest prover paired with the
pass-through verifier.

Deliberately computable — this is what an honest execution runs, what perfect completeness is
stated about (`QuadEval/Completeness.lean`), and what the extraction rail consumes. The digit
decompositions `ddCarrier` (for `G⁻¹`, `messageDigits` digits) and `ddZ` (for `J⁻¹`, `zDigits`
digits) must share the gadget base `base`, since the verifier's Eq.-(20) rows recompose both with
the same `base`. They differ in kind: `ddCarrier` is a full-width `DigitDecomposition` (carrier
coefficients are arbitrary residues), while `ddZ` is a `BoundedDigitDecomposition` at the honest
shortness bound on `z`, which is what decouples `τ` from `δ = ⌈log_b q⌉`. -/
def quadEvalReduction
    (pp : Hachi.PublicParamsD Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    {base : ZMod q} (ddCarrier : DigitDecomposition base messageDigits)
    (ddZ : BoundedDigitDecomposition base zDigits zBound) :
    Reduction oSpec
      (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
      (QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
      (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows ×
        CarrierCom Φ dRows × (Fin (2 ^ r) → ShortChallenge Φ ω))
      (QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits)
      (pSpec (CarrierCom Φ dRows) (ShortChallenge Φ ω) r) where
  prover := InnerOuter.prover Φ
    (QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
    (honestComputeV Φ pp ddCarrier) (honestComputeResp Φ ddCarrier ddZ)
  verifier := InnerOuter.verifier Φ

end Protocol

end ZModDefs

end ArkLib.Lattices.Ajtai.InnerOuter
