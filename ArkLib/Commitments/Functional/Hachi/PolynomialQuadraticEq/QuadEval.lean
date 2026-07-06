/-
Copyright (c) 2024-2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tobias Rothmann
-/
import ArkLib.Commitments.Functional.Hachi.PolynomialQuadraticEq.QuadEvalGadgets
import ArkLib.Commitments.Functional.Hachi.InnerOuter.Security
import ArkLib.OracleReduction.Security.CoordinateWiseSpecialSoundness.SingleRound

/-!
  # Hachi polynomial-evaluation reduction (QuadEval) — coordinate-wise special soundness
    (Hachi Lemma 8)

  Hachi's polynomial-evaluation reduction proves `f(x) = y` by rewriting the evaluation as the
  quadratic form `bᵀ M a` and folding the `2ʳ` carrier blocks under the verifier's challenge
  vector — hence the name `QuadEval`. It is Hachi's multilinear / inner-outer lift of Greyhound's
  [NS24, §3.1] polynomial-evaluation protocol.

  **Lemma 8** (Hachi [NOZ26] §4.2, Figure 3, p. 17–18): this reduction is coordinate-wise special
  sound. From `2ʳ+1` accepting transcripts with challenge vectors in `SS(C, 2ʳ, 2)`, the tree
  extractor either reconstructs a valid weak `InnerOuter.Opening` by subtract-and-divide, or
  outputs a Module-SIS solution for `B` or `D`.

  The reduction is modeled as the two-round
  `pSpec ⟨!v[.P_to_V, .V_to_P], !v[CarrierCom, Fin 2ʳ → C]⟩`: round 0 (P→V) sends the short
  commitment `v = D ŵ`; round 1 (V→P) is the challenge vector. The triple `(ŵ, t̂, ẑ)` is the
  **output witness** (`QuadEvalResponse`, never sent — §4.3 proves knowledge of it instead), so the
  verifier is a pure pass-through (`IsPure` by `rfl`) and the extractor sources per-branch triples
  from `relOut.language`.

  This module holds:
  * the reduction's definitions and relations (`CarrierCom`, `QuadEvalStatement`,
    `QuadEvalResponse`, `QuadEvalWitness`, `ShortChallenge`, `derivedMsgMatrix`/`evalConsistency`,
    `dShort`, `relOut`, `relIn`);
  * the two-transcript MSIS lemmas (`msisB_of_two_valid`, `msisD_of_two_valid`) and the
    subtract-and-divide core (`inner_eq_of_chain`);
  * the pure `verifier` + `instIsPure` and the `prover` skeleton;
  * the extractor data (`extractedOpening`, `buildWitness`) and the extraction lemmas
    (`verifiedOpening_of_star` = Sublemma 1, `evalConsistency_of_relOut_star` = Sublemma 2 — both
    internal steps of Hachi Lemma 8's case (C), not paper lemmas — and `buildWitness_mem_relIn`),
    and the top-level theorem `quadEval_coordinateWiseSpecialSound(')`.

  This module implements milestones **M3–M7** of
  `Commitments/Functional/Hachi/LEMMA8_FOLDBLOCK_PLAN.md` (§9.5). It sits inside
  `namespace ArkLib.Lattices.Ajtai.InnerOuter` (required: that namespace activates the scoped
  `PolyVec`/`*ᵥ`/`•ᵥ`/`dot`/`splitForm`), with `open WeakBinding` (so `VerifiedOpening`/`outerShort`
  resolve). Never `open ArkLib.Lattices` here (the `⬝ᵥ` token is ambiguous between
  `Matrix.dotProduct` and `ArkLib.Lattices.dot`); spell `dot _ _`.

  ## References

  * [Nguyen, N. K., and Seiler, G., *Greyhound: Fast Polynomial Commitments from Lattices*][NS24]
  * [Nguyen, N. K., O'Rourke, G., and Zhang, J., *Hachi: Efficient Lattice-Based Multilinear
      Polynomial Commitments over Extension Fields*][NOZ26]
-/

-- ================= PolynomialQuadraticEq/QuadEval.lean — definitions layer =================
namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open WeakBinding
open OracleComp OracleSpec ProtocolSpec CoordinateWise.SingleRound

/-! ## Generic definitions (any coefficient field `R`, mimicking `Scheme.lean`'s `Defs`) -/

section Defs

variable {R : Type} [Field R] [BEq R] [LawfulBEq R] (Φ : CyclotomicModulus R) [IsCyclotomic Φ]
variable {innerRows messageRows messageDigits outerRows blocks innerDigits dRows zDigits : Nat}

/-- The carrier commitment space: `v = D ŵ` lives in the `D`-row space. -/
abbrev CarrierCom (Φ : CyclotomicModulus R) (dRows : Nat) := Simple.Commitment Φ dRows

/-- Input statement of Hachi's polynomial-evaluation reduction (Hachi §4.2, Figure 3): the public
parameters `(A, B, D)`, the outer commitment `u`, the two evaluation basis vectors
`a ∈ Rq^{2^m}` (`avec`) and `b ∈ Rq^{2^r}` (`bvec`) of Eq. (12), and the claimed evaluation
`y = u_eval`. -/
structure QuadEvalStatement (Φ : CyclotomicModulus R)
    (innerRows messageRows messageDigits outerRows blocks innerDigits dRows : Nat) where
  /-- Public matrices `(A, B, D)`. -/
  pp : Hachi.PublicParamsD Φ innerRows messageRows messageDigits outerRows blocks innerDigits dRows
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

instance : Nonempty
    (QuadEvalResponse Φ innerRows messageRows messageDigits blocks innerDigits zDigits) :=
  ⟨⟨fun _ => 0, fun _ _ => 0, fun _ => 0⟩⟩

/-- The extracted (input-side) witness of Hachi Lemma 8: either a weak `Opening` for `u`, or a
Module-SIS solution for the outer matrix `B`, or one for the short-commitment matrix `D`. -/
inductive QuadEvalWitness (Φ : CyclotomicModulus R)
    (innerRows messageRows messageDigits blocks innerDigits : Nat) where
  /-- A weak opening `(sᵢ, t̂ᵢ, c̄ᵢ)ᵢ` for the outer commitment `u`. -/
  | opening (o : Opening Φ innerRows messageRows messageDigits blocks innerDigits)
  /-- A Module-SIS solution for the outer matrix `B`. -/
  | msisB (z : ModuleSIS.Solution Φ (blocks * (innerRows * innerDigits)))
  /-- A Module-SIS solution for the short-commitment matrix `D`. -/
  | msisD (z : ModuleSIS.Solution Φ (blocks * messageDigits))

instance : Nonempty (QuadEvalWitness Φ innerRows messageRows messageDigits blocks innerDigits) :=
  ⟨.msisB (fun _ => 0)⟩

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

omit [NeZero q] [IsCyclotomic Φ] in
/-- `val` is injective (distinct Hachi §4.2 challenges have distinct underlying ring elements). -/
theorem val_injective : Function.Injective (val : ShortChallenge Φ ω → Rq Φ) :=
  fun _ _ h => Subtype.ext h

end ShortChallenge

end ShortChallenge

/-! ## Eval consistency (Eq. 15) — probe-compiled §9.3 block, kept verbatim -/

section ZModDefs

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {innerRows messageRows messageDigits outerRows blocks innerDigits dRows zDigits
  m r : Nat}

/-- The matrix `M` of Hachi Eq. (15): row `i` = derived message block `G_{2^m} · sᵢ`; rows are
indexed by the outer basis `b`, columns by the inner basis `a`. -/
def derivedMsgMatrix (base : ZMod q)
    (o : Opening Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :
    PolyMatrix (Rq Φ) (2 ^ r) (2 ^ m) := fun i k => derivedMessage Φ base o.toDecomp i k

omit [NeZero q] in
/-- Row `i` of the Hachi Eq. (15) matrix `M` is the derived message block (definitional). -/
@[simp] theorem derivedMsgMatrix_apply {base : ZMod q}
    (o : Opening Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) (i : Fin (2 ^ r)) :
    derivedMsgMatrix Φ base o i = derivedMessage Φ base o.toDecomp i := rfl

/-- Eq. (15): the derived messages of the weak opening evaluate to `y` under the split
bilinear form (`splitForm`, argument order `b a` load-bearing). -/
def evalConsistency (base : ZMod q) (a : PolyVec (Rq Φ) (2 ^ m)) (b : PolyVec (Rq Φ) (2 ^ r))
    (y : Rq Φ) (o : Opening Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) : Prop :=
  splitForm (derivedMsgMatrix Φ base o) b a = y

omit [NeZero q] in
/-- The Hachi Eq. (15) quadratic form `bᵀ M a` expands to the block sum
`∑ᵢ bᵢ · ⟨a, G_{2^m} sᵢ⟩` (the per-block reading used by `evalConsistency_of_star`). -/
theorem splitForm_derivedMsgMatrix_eq_sum (base : ZMod q) (a : PolyVec (Rq Φ) (2 ^ m))
    (b : PolyVec (Rq Φ) (2 ^ r))
    (o : Opening Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :
    splitForm (derivedMsgMatrix Φ base o) b a =
      ∑ i, b i * dot a (derivedMessage Φ base o.toDecomp i) := by
  rw [splitForm, dot_eq_sum]; refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [matVecMul_apply, derivedMsgMatrix_apply, dot_comm]

omit [NeZero q] in
/-- **Sublemma 2 of the extraction** (an internal step of Hachi Lemma 8, case (C), establishing
Eq. (15)): from c3 (`dot b w = y`) and the c4-subtractions
(`wⱼ = dot a (derivedMessage o j)`), the extracted opening is eval-consistent. -/
theorem evalConsistency_of_star (base : ZMod q) (a : PolyVec (Rq Φ) (2 ^ m))
    (b : PolyVec (Rq Φ) (2 ^ r)) (y : Rq Φ)
    (o : Opening Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits)
    (w : PolyVec (Rq Φ) (2 ^ r)) (c3 : dot b w = y)
    (c4 : ∀ j, w j = dot a (derivedMessage Φ base o.toDecomp j)) :
    evalConsistency Φ base a b y o := by
  unfold evalConsistency; rw [splitForm_derivedMsgMatrix_eq_sum, ← c3, dot_eq_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_); rw [c4 j]

/-! ## `dShort` and the output/input relations -/

/-- Shortness predicate for the extracted `D`-kernel witness (Hachi Lemma 8, case (B)): the
`D`-matrix analogue of `outerShort`, at `subLInftyNormBound γ = 2·γ`. -/
def dShort (γ : ℕ) : ModuleSIS.Solution Φ (blocks * messageDigits) → Bool :=
  fun z => decide (vecLInftyNorm Φ z ≤ subLInftyNormBound γ)

/-- **`relOut` — exactly Hachi Eq. (20) plus the `S_b` range checks** on
`((stmt, v, c), (ŵ, t̂, ẑ))`, with `z := J ẑ`:

* c1: `D ŵ = v`
* c2: `B (flatten t̂) = u`
* c3: `bᵀ (G_{2^r} ŵ) = y` (row 3 of Eq. (20), `u_eval`)
* c4: `(cᵀ ⊗ G₁) ŵ = aᵀ G_{2^m} J ẑ` (row 4; challenges coerced from the subtype)
* c5: `(cᵀ ⊗ G_{n_A}) t̂ = A J ẑ` (row 5)
* c6: the `S_b` range checks, as symmetric `ℓ∞` balls `≤ γ`.

**`S_b` modeling**: Eq. (20) checks `(ŵ, t̂, ẑ) ∈ S_b^…`, whose elements have centered
coefficients in `[⌈-b/2⌉, ⌈b/2⌉-1]`; c6 uses the symmetric ball `‖·‖∞ ≤ γ`, which with `γ ≥
⌈b/2⌉` **contains** the paper's box — so every Eq.-(20)-valid transcript is `relOut`-valid and
the CWSS theorem covers the paper's verifier. No challenge-norm checks appear (the challenge
TYPE carries `‖cᵢ‖₁ ≤ ω`), and no `‖z‖₂²` check appears (`‖z‖∞ ≤ …` is derived downstream from
c6's `‖ẑ‖∞ ≤ γ` via the `J`-recomposition norm lemma, `GadgetNorms.lean`) — both exactly as in the
paper. -/
def relOut (base : ZMod q) (ω γ : ℕ) :
    Set ((QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows ×
          CarrierCom Φ dRows × (Fin (2 ^ r) → ShortChallenge Φ ω)) ×
         QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits) :=
  { p | match p with
    | ((stmt, v, chals), resp) =>
      let c : PolyVec (Rq Φ) (2 ^ r) := fun i => (chals i).val
      let z : PolyVec (Rq Φ) ((2 ^ m) * messageDigits) :=
        Hachi.jMatrix Φ base ((2 ^ m) * messageDigits) zDigits *ᵥ resp.zDec
      -- c1: `D ŵ = v`
      Simple.commit Φ stmt.pp.dMatrix resp.carrierDec = v ∧
      -- c2: `B (flatten t̂) = u`
      Simple.commit Φ stmt.pp.outerMatrix (PolyVec.flattenBlocks resp.innerDec) = stmt.u ∧
      -- c3: `bᵀ (G_{2^r} ŵ) = y`
      dot stmt.bvec (gadgetMatrix Φ base (2 ^ r) messageDigits *ᵥ resp.carrierDec) = stmt.y ∧
      -- c4: `(cᵀ ⊗ G₁) ŵ = aᵀ (G_{2^m} z)`
      Hachi.tensorG1 Φ base messageDigits c resp.carrierDec =
        dot stmt.avec (gadgetMatrix Φ base (2 ^ m) messageDigits *ᵥ z) ∧
      -- c5: `(cᵀ ⊗ G_{n_A}) t̂ = A z`
      Hachi.tensorG Φ base innerRows innerDigits c resp.innerDec =
        stmt.pp.innerMatrix *ᵥ z ∧
      -- c6: the `S_b` range checks (as `ℓ∞` balls)
      vecLInftyNorm Φ resp.carrierDec ≤ γ ∧
      vecLInftyNorm Φ (PolyVec.flattenBlocks resp.innerDec) ≤ γ ∧
      vecLInftyNorm Φ resp.zDec ≤ γ }

/-- **`relIn` — Hachi Lemma 8's extraction disjunction**: a weak `VerifiedOpening` for `u` that is
also eval-consistent (Eq. 15), or a Module-SIS solution for `B`, or one for `D`. The `.opening`
disjunct is the interface into `outputToModuleSIS_valid_of_verified` for the downstream
cross-run knowledge-soundness step. -/
def relIn (base : ZMod q) (βSq γ κ : ℕ) :
    Set (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows ×
         QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits) :=
  { p | match p with
    | (stmt, .opening o) =>
        VerifiedOpening Φ base βSq γ κ stmt.pp.toPublicParams stmt.u o ∧
        evalConsistency Φ base stmt.avec stmt.bvec stmt.y o
    | (stmt, .msisB z) =>
        ModuleSIS.relation Φ (outerShort Φ γ) stmt.pp.outerMatrix z = true
    | (stmt, .msisD z) =>
        ModuleSIS.relation Φ (dShort Φ γ) stmt.pp.dMatrix z = true }

/-! ## The two-transcript MSIS extraction lemmas (Hachi Lemma 8, cases (A)/(B)) -/

/-- **Hachi Lemma 8, case (A)**: two Eq.-(20)-valid responses (c2 + c6 facts) with different inner
decompositions yield a `B`-kernel Module-SIS solution. Clone of
`outer_relation_of_verified`'s tail. -/
theorem msisB_of_two_valid {γ : ℕ}
    {B : Simple.PublicParams Φ outerRows (blocks * (innerRows * innerDigits))}
    {u : Commitment Φ outerRows}
    {resp₁ resp₂ :
      QuadEvalResponse Φ innerRows messageRows messageDigits blocks innerDigits zDigits}
    (hu₁ : Simple.commit Φ B (PolyVec.flattenBlocks resp₁.innerDec) = u)
    (hu₂ : Simple.commit Φ B (PolyVec.flattenBlocks resp₂.innerDec) = u)
    (hγ₁ : vecLInftyNorm Φ (PolyVec.flattenBlocks resp₁.innerDec) ≤ γ)
    (hγ₂ : vecLInftyNorm Φ (PolyVec.flattenBlocks resp₂.innerDec) ≤ γ)
    (hne : PolyVec.flattenBlocks resp₁.innerDec ≠ PolyVec.flattenBlocks resp₂.innerDec) :
    ModuleSIS.relation Φ (outerShort Φ γ) B
      (PolyVec.flattenBlocks resp₁.innerDec - PolyVec.flattenBlocks resp₂.innerDec) = true := by
  have hne0 : PolyVec.flattenBlocks resp₁.innerDec - PolyVec.flattenBlocks resp₂.innerDec ≠ 0 :=
    sub_ne_zero.mpr hne
  have hshort : vecLInftyNorm Φ
      (PolyVec.flattenBlocks resp₁.innerDec - PolyVec.flattenBlocks resp₂.innerDec) ≤
        subLInftyNormBound γ :=
    sub_lInftyNorm_le Φ _ _ hγ₁ hγ₂
  have heq : B *ᵥ PolyVec.flattenBlocks resp₁.innerDec =
      B *ᵥ PolyVec.flattenBlocks resp₂.innerDec := by
    simpa [Simple.commit] using hu₁.trans hu₂.symm
  have hker : B *ᵥ
      (PolyVec.flattenBlocks resp₁.innerDec - PolyVec.flattenBlocks resp₂.innerDec) = 0 := by
    rw [matVecMul_sub]; exact sub_eq_zero.mpr heq
  simp [ModuleSIS.relation, outerShort, hne0, hshort, hker]

/-- **Hachi Lemma 8, case (B)**: two Eq.-(20)-valid responses (c1 + c6 facts, shared `v`) with
different carrier decompositions yield a `D`-kernel Module-SIS solution. -/
theorem msisD_of_two_valid {γ : ℕ}
    {D : Simple.PublicParams Φ dRows (blocks * messageDigits)}
    {v : CarrierCom Φ dRows}
    {resp₁ resp₂ :
      QuadEvalResponse Φ innerRows messageRows messageDigits blocks innerDigits zDigits}
    (hv₁ : Simple.commit Φ D resp₁.carrierDec = v)
    (hv₂ : Simple.commit Φ D resp₂.carrierDec = v)
    (hγ₁ : vecLInftyNorm Φ resp₁.carrierDec ≤ γ)
    (hγ₂ : vecLInftyNorm Φ resp₂.carrierDec ≤ γ)
    (hne : resp₁.carrierDec ≠ resp₂.carrierDec) :
    ModuleSIS.relation Φ (dShort Φ γ) D (resp₁.carrierDec - resp₂.carrierDec) = true := by
  have hne0 : resp₁.carrierDec - resp₂.carrierDec ≠ 0 := sub_ne_zero.mpr hne
  have hshort : vecLInftyNorm Φ (resp₁.carrierDec - resp₂.carrierDec) ≤ subLInftyNormBound γ :=
    sub_lInftyNorm_le Φ _ _ hγ₁ hγ₂
  have heq : D *ᵥ resp₁.carrierDec = D *ᵥ resp₂.carrierDec := by
    simpa [Simple.commit] using hv₁.trans hv₂.symm
  have hker : D *ᵥ (resp₁.carrierDec - resp₂.carrierDec) = 0 := by
    rw [matVecMul_sub]; exact sub_eq_zero.mpr heq
  simp [ModuleSIS.relation, dShort, hne0, hshort, hker]

/-! ## The subtract-and-divide core step (`inner_eq` via `Ring.inverse`) -/

omit [NeZero q] in
/-- The c5-side unit-cancellation of the subtract-and-divide extraction (Hachi Lemma 8, case (C)):
from the c5-subtract chain `c̄ᵢ •ᵥ (G_{n_A} t̂ᵢ) = A *ᵥ Δz` and `IsUnit c̄ᵢ`, the extracted
message block
`sᵢ := Ring.inverse c̄ᵢ •ᵥ Δz` satisfies the weak-opening inner gadget relation
(`VerifiedBlock.inner_eq`). Total at the definition site — no `IsUnit` needed to *define* `sᵢ`. -/
theorem inner_eq_of_chain {base : ZMod q} {cols : Nat}
    (A : Simple.PublicParams Φ innerRows cols)
    (that : Simple.Message Φ (innerRows * innerDigits)) (zdiff : PolyVec (Rq Φ) cols)
    (c : Rq Φ) (hc : IsUnit c)
    (hchain : c •ᵥ Simple.commit Φ (gadgetMatrix Φ base innerRows innerDigits) that =
      A *ᵥ zdiff) :
    Simple.commit Φ (gadgetMatrix Φ base innerRows innerDigits) that
      = Simple.commit Φ A (Ring.inverse c •ᵥ zdiff) := by
  have hAs : Simple.commit Φ A (Ring.inverse c •ᵥ zdiff) = Ring.inverse c •ᵥ (A *ᵥ zdiff) := by
    simp only [Simple.commit]; rw [matVecMul_scalarVecMul]
  rw [hAs, ← hchain]; funext i
  simp only [scalarVecMul_apply, ← mul_assoc, Ring.inverse_mul_cancel c hc, one_mul]

/-! ## The protocol: pure verifier, `IsPure`, prover skeleton -/

section Protocol

variable {ι : Type} {oSpec : OracleSpec ι} {ω : ℕ}

/-- The reduction's verifier (Hachi §4.2, Figure 3) is a **pure pass-through**: it re-emits the
statement, the round-0 carrier commitment `v`, and the round-1 challenge vector. The Eq.-(20)
checks live in `relOut` (the `(ŵ, t̂, ẑ)` triple is never sent — §4.3 proves knowledge of it), so
there is no runtime `guard` and the verifier is `IsPure`. -/
def verifier :
    Verifier oSpec
      (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
      (QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows ×
        CarrierCom Φ dRows × (Fin (2 ^ r) → ShortChallenge Φ ω))
      (pSpec (CarrierCom Φ dRows) (ShortChallenge Φ ω) r) where
  verify := fun stmt tr => pure (stmt, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩)

omit [NeZero q] [IsCyclotomic Φ] in
/-- The `hpure` shape consumed by `branch_relOut_language` (`SingleRound.lean`). -/
theorem verifier_verify_pure
    (stmt : QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (tr : (pSpec (CarrierCom Φ dRows) (ShortChallenge Φ ω) r).FullTranscript) :
    (verifier (oSpec := oSpec) (ω := ω) Φ).verify stmt tr =
      pure (stmt, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩) := rfl

/-- The Hachi Figure 3 verifier is pure: its output is a total function of `(stmt, tr)`. -/
instance instIsPure : (verifier (oSpec := oSpec) (ω := ω) Φ
    (innerRows := innerRows) (messageDigits := messageDigits) (outerRows := outerRows)
    (innerDigits := innerDigits) (dRows := dRows) (m := m) (r := r)).IsPure :=
  ⟨fun stmt tr => (stmt, tr.messages ⟨0, rfl⟩, tr.challenges ⟨1, rfl⟩), fun _ _ => rfl⟩

/-- Prover skeleton (Hachi §4.2, Figure 3; completeness is out of scope for Lemma 8): round 0 sends
the carrier commitment `v` (cf. `SendClaim.oracleProver`), round 1 receives the challenge vector
(cf. `SendChallenge.oracleProver`), and the output witness is the `QuadEvalResponse` `(ŵ, t̂, ẑ)`
of Eq. (20). The honest computations (`v = D ŵ` with `ŵ = G⁻¹(w)`, `ẑ = J⁻¹(Σᵢ cᵢ sᵢ)`, …) are the
parameters `computeV` / `computeResp`, to be instantiated by the completeness layer from the
`QuadEvalGadgets` carrier/decomposition definitions (§9.3). -/
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

end Protocol

end ZModDefs

end ArkLib.Lattices.Ajtai.InnerOuter

-- ================= PolynomialQuadraticEq/QuadEval.lean — extraction assembly =================

section QuadEvalExtraction

namespace ArkLib.Lattices.Ajtai.InnerOuter

open CompPoly ArkLib.Lattices.CyclotomicModulus
open WeakBinding
open OracleComp OracleSpec ProtocolSpec CoordinateWise CoordinateWise.SingleRound

/-! ## The extracted opening and the witness assembler (generic `Φ`) -/

section BuildWitness

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)]
  (Φ : CyclotomicModulus (ZMod q)) [IsCyclotomic Φ]
variable {innerRows messageDigits outerRows innerDigits dRows zDigits m r ω : Nat}

/-- The subtract-and-divide weak opening extracted from a star of accepting branches
(Hachi Lemma 8, case (C)): per coordinate `j`, the message is
`sⱼ := c̄ⱼ⁻¹ •ᵥ (z^{(sib j)} − z^{(central)})` with `z^{(i)} := J ẑ^{(i)}`, the inner
decomposition is the shared central `t̂`, and the challenge is the slack
`c̄ⱼ := c_{sib j, j} − c_{central, j}`. Total — no `IsUnit`/star hypotheses at the definition
(`Ring.inverse` is total); correctness lives in `verifiedOpening_of_star`. -/
noncomputable def extractedOpening (base : ZMod q)
    (fam : Fin (2 ^ r + 1) → (Fin (2 ^ r) → ShortChallenge Φ ω))
    (resp : Fin (2 ^ r + 1) →
      QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits) :
    Opening Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits :=
  let z : Fin (2 ^ r + 1) → PolyVec (Rq Φ) ((2 ^ m) * messageDigits) := fun j =>
    Hachi.jMatrix Φ base ((2 ^ m) * messageDigits) zDigits *ᵥ (resp j).zDec
  { message := fun j =>
      Ring.inverse ((fam (sib fam j) j).val - (fam (central fam) j).val) •ᵥ
        (z (sib fam j) - z (central fam))
    innerDecomp := (resp (central fam)).innerDec
    challenge := fun j => (fam (sib fam j) j).val - (fam (central fam) j).val }

open Classical in
/-- The reduction's witness assembler (Hachi Lemma 8's three-case extraction) — the `mkWitness`
argument of the generic extractor `E`:

* some branch's (flattened) inner decomposition `t̂` differs from the central one → a
  `B`-kernel Module-SIS solution (the `msisB_of_two_valid` data);
* else some branch's carrier decomposition `ŵ` differs from the central one → a `D`-kernel
  Module-SIS solution (the `msisD_of_two_valid` data);
* else all branches share `t̂` and `ŵ`, and the star's subtract-and-divide yields the weak
  opening `extractedOpening`.

("Two branches differ" is equivalent to "some branch differs from the central one": if two
branches disagree, at least one of them disagrees with the central branch.) Fully defined —
the classical `dite`s always produce a term; that each case lands in `relIn` is
`buildWitness_mem_relIn`. -/
noncomputable def buildWitness (base : ZMod q)
    (_stmt :
      QuadEvalStatement Φ innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits dRows)
    (_v : CarrierCom Φ dRows)
    (fam : Fin (2 ^ r + 1) → (Fin (2 ^ r) → ShortChallenge Φ ω))
    (resp : Fin (2 ^ r + 1) →
      QuadEvalResponse Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits) :
    QuadEvalWitness Φ innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits :=
  if hB : ∃ j, PolyVec.flattenBlocks (resp j).innerDec
      ≠ PolyVec.flattenBlocks (resp (central fam)).innerDec then
    .msisB (PolyVec.flattenBlocks (resp hB.choose).innerDec -
      PolyVec.flattenBlocks (resp (central fam)).innerDec)
  else if hD : ∃ j, (resp j).carrierDec ≠ (resp (central fam)).carrierDec then
    .msisD ((resp hD.choose).carrierDec - (resp (central fam)).carrierDec)
  else
    .opening (extractedOpening Φ base fam resp)

omit [NeZero q] [IsCyclotomic Φ] in
/-- Coordinate difference transfers from the `ShortChallenge` subtype to the underlying ring
vectors — the bridge from `sib_coordEq` (subtype-level `CoordEq`) to the ring-level
coordinate-isolation lemmas `tensorG_coordDiff`/`tensorG1_coordDiff` (`QuadEvalGadgets.lean`). -/
theorem ShortChallenge.coordEq_val {ℓ : ℕ} {i : Fin ℓ} {x y : Fin ℓ → ShortChallenge Φ ω}
    (h : CoordEq i x y) :
    CoordEq i (fun j => (x j).val) (fun j => (y j).val) :=
  ⟨ShortChallenge.val_ne_of_ne h.1, fun j hj => congrArg ShortChallenge.val (h.2 j hj)⟩

end BuildWitness

/-! ## The extraction lemmas and the top-level theorem (pinned to `𝓜(q, α)`)

Only here does the Lyubashevsky–Seiler invertibility enter (`isUnit_of_l1Norm_le` is pinned
to the power-of-two modulus), so — mirroring `InnerOuter/Security.lean` — the statements are
pinned to `𝓜(q, α)` and carry the [LS18] hypotheses `q ≡ 5 (mod 8)`, `(2ω)² < q`. -/

section Pinned

variable {q : ℕ} [NeZero q] [Fact (Nat.Prime q)] [BEq (ZMod q)] [LawfulBEq (ZMod q)] {α : ℕ}
variable {innerRows messageDigits outerRows innerDigits dRows zDigits m r : Nat}

/-- **Sublemma 1 (an internal step of Hachi Lemma 8, case (C), weak-opening part).** At a
star-shaped family of `2^r + 1` `relOut`-accepting branches sharing the carrier commitment `v`
and (cases (A)/(B) excluded) sharing `t̂` and `ŵ`, the subtract-and-divide `extractedOpening` is a
`VerifiedOpening` at

* `βSq := quadEvalBetaSq γ b zDigits (deg φ) m messageDigits = 4·B_z`, the `GadgetNorms`-derived
  `J`-recomposition bound (`deg φ = 2^α`; no primitive `‖z‖₂²` verifier check anywhere);
* `γ' := γ` — **not** `2γ`: `outer_short` constrains the extracted opening's `innerDecomp`,
  which is the CENTRAL branch's `t̂` verbatim, and relOut c6 bounds it by `γ` directly (the
  `2γ` slack of `subLInftyNormBound` is only for the *difference* witnesses of cases (A)/(B));
* `κ := 2ω`, the slack bound for `c̄ⱼ = c_{sib j, j} − c_{central, j}` from two `‖·‖₁ ≤ ω`
  subtype challenges (`ShortChallenge.l1Norm_val_sub_le`). -/
theorem verifiedOpening_of_star (hq5 : q % 8 = 5) {b ω γ : ℕ} (hκ : (2 * ω) ^ 2 < q)
    (hτ : 0 < zDigits)
    (stmt : QuadEvalStatement 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (v : CarrierCom 𝓜(q, α) dRows)
    (fam : Fin (2 ^ r + 1) → (Fin (2 ^ r) → ShortChallenge 𝓜(q, α) ω))
    (resp : Fin (2 ^ r + 1) →
      QuadEvalResponse 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits)
    (hrel : ∀ j, ((stmt, v, fam j), resp j) ∈ relOut 𝓜(q, α) ((b : ZMod q)) ω γ)
    (hstar : ∃ e, StarAt fam e)
    (ht : ∀ j, (resp j).innerDec = (resp (central fam)).innerDec)
    (_hw : ∀ j, (resp j).carrierDec = (resp (central fam)).carrierDec) :
    VerifiedOpening 𝓜(q, α) ((b : ZMod q))
      (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω)
      stmt.pp.toPublicParams stmt.u
      (extractedOpening 𝓜(q, α) ((b : ZMod q)) fam resp) := by
  -- PROOF PLAN (rank 7). Notation: e := central fam, sibᵢ := sib fam i,
  --   c̄ᵢ := (fam sibᵢ i).val − (fam e i).val, zⱼ := jMatrix 𝓜 b _ zDigits *ᵥ (resp j).zDec,
  --   Δzᵢ := z sibᵢ − z e. Destructure each hrel j by plain
  --   `obtain ⟨c1, c2, c3, c4, c5, c6w, c6t, c6z⟩ := hrel j` (smoke test above: the match
  --   iota-reduces on the literal tuple).
  -- * outer_eq   := c2 of the central branch (relOut c2 is verbatim
  --   `Simple.commit 𝓜 B (flattenBlocks t̂) = stmt.u`).
  -- * outer_short := c6t of the central branch — the γ (NOT 2γ) bound; the extracted
  --   `innerDecomp` IS `(resp e).innerDec`, syntactically.
  -- * block i, fieldwise:
  --   - hne : c̄ᵢ ≠ 0 — from sib_coordEq fam hstar i : CoordEq i (fam e) (fam sibᵢ) (SingleRound),
  --     sib_coordEq_ne + ShortChallenge.val_ne_of_ne + sub_ne_zero_of_ne.
  --   - hpos := Rq.l1Norm_pos_of_ne_zero 𝓜(q,α) hne (NormBounds/Basic.lean).
  --   - challenge_short := ShortChallenge.l1Norm_val_sub_le _ _ : ‖c̄ᵢ‖₁ ≤ 2ω (via
  --     Rq.l1Norm_sub_le).
  --   - unit := isUnit_of_l1Norm_le α hq5 hpos challenge_short hκ (LS18, 𝓜-pinned; κ = 2ω).
  --   - scaled_short : challenge i •ᵥ message i = c̄ᵢ •ᵥ (Ring.inverse c̄ᵢ •ᵥ Δzᵢ) = Δzᵢ
  --     (scalarVecMul associativity + Ring.mul_inverse_cancel with unit); then
  --     ‖Δzᵢ‖₂² ≤ subL2NormSqBound (quadEvalZL2SqBound γ b zDigits (deg φ) m messageDigits)
  --       = quadEvalBetaSq … (rfl)
  --     by gadgetMul_zmod_sub_l2NormSq_le 𝓜 hτ h1 (resp sibᵢ).zDec (resp e).zDec c6z c6z
  --     (GadgetNorms.lean; `jMatrix … *ᵥ ·` is `gadgetMul` by rfl), with
  --     h1 : 1 ≤ (𝓜(q,α)).φ.natDegree from hachiModulus_natDegree ▸ Nat.one_le_two_pow.
  --   - inner_eq : the c5-subtract chain. Rewrite c5 of branch sibᵢ along ht sibᵢ to the
  --     shared t̂ := (resp e).innerDec; subtract c5 of the central branch:
  --     tensorG_sub_challenge + matVecMul_sub give
  --       tensorG 𝓜 b innerRows innerDigits (c_sib − c_e) t̂ = A *ᵥ Δzᵢ;
  --     coordinate-isolate with tensorG_coordDiff at
  --       ShortChallenge.coordEq_val (coordEq_symm (sib_coordEq fam hstar i))
  --     to get c̄ᵢ •ᵥ (gadgetMatrix 𝓜 b innerRows innerDigits *ᵥ t̂ i) = A *ᵥ Δzᵢ; close by
  --     inner_eq_of_chain 𝓜 stmt.pp.innerMatrix (t̂ i) Δzᵢ c̄ᵢ unit (above)
  --     (`Simple.commit 𝓜 (gadgetMatrix …)` is `gadgetMatrix … *ᵥ ·` by rfl).
  -- outer_eq / outer_short := c2 / c6t of the central branch.
  obtain ⟨-, hc2e, -, -, -, -, hc6te, -⟩ := hrel (central fam)
  refine ⟨hc2e, hc6te, fun i => ?_⟩
  -- Block `i`: the extracted challenge `c̄ᵢ := c_{sib i, i} − c_{e, i}` is nonzero, `2ω`-short,
  -- hence a unit (Lyubashevsky–Seiler).
  have hne : (fam (sib fam i) i).val - (fam (central fam) i).val ≠ 0 :=
    sub_ne_zero_of_ne (ShortChallenge.val_ne_of_ne (sib_coordEq_ne fam hstar i))
  have hshort : ‖(fam (sib fam i) i).val - (fam (central fam) i).val‖₁ ≤ 2 * ω :=
    ShortChallenge.l1Norm_val_sub_le _ _
  have hunit : IsUnit ((fam (sib fam i) i).val - (fam (central fam) i).val) :=
    isUnit_of_l1Norm_le α hq5 (Rq.l1Norm_pos_of_ne_zero 𝓜(q, α) hne) hshort hκ
  refine ⟨hunit, hshort, ?_, ?_⟩
  · -- scaled_short : `c̄ᵢ •ᵥ (c̄ᵢ⁻¹ •ᵥ Δzᵢ) = Δzᵢ = J ẑ^{(sib i)} − J ẑ^{(e)}`, then the
    -- `J`-recomposition ℓ₂² bound from the two branches' c6z (`GadgetNorms.lean`).
    have h1 : 1 ≤ (𝓜(q, α)).φ.natDegree := by
      rw [hachiModulus_natDegree]; exact Nat.one_le_two_pow
    obtain ⟨-, -, -, -, -, -, -, hc6zs⟩ := hrel (sib fam i)
    obtain ⟨-, -, -, -, -, -, -, hc6ze⟩ := hrel (central fam)
    have hcancel : (extractedOpening 𝓜(q, α) ((b : ZMod q)) fam resp).challenge i •ᵥ
        (extractedOpening 𝓜(q, α) ((b : ZMod q)) fam resp).message i
        = Hachi.jMatrix 𝓜(q, α) ((b : ZMod q)) ((2 ^ m) * messageDigits) zDigits *ᵥ
            (resp (sib fam i)).zDec
          - Hachi.jMatrix 𝓜(q, α) ((b : ZMod q)) ((2 ^ m) * messageDigits) zDigits *ᵥ
            (resp (central fam)).zDec := by
      simp only [extractedOpening]
      funext k
      simp only [scalarVecMul_apply, ← mul_assoc, Ring.mul_inverse_cancel _ hunit, one_mul]
    rw [hcancel]
    exact gadgetMul_zmod_sub_l2NormSq_le 𝓜(q, α) hτ h1
      (resp (sib fam i)).zDec (resp (central fam)).zDec hc6zs hc6ze
  · -- inner_eq : the c5-subtract chain, shared `t̂ := (resp e).innerDec`, coordinate-isolated
    -- and unit-divided.
    have hcoord : CoordEq i (fun k => (fam (sib fam i) k).val)
        (fun k => (fam (central fam) k).val) :=
      ShortChallenge.coordEq_val 𝓜(q, α) (coordEq_symm (sib_coordEq fam hstar i))
    obtain ⟨-, -, -, -, hc5s, -, -, -⟩ := hrel (sib fam i)
    obtain ⟨-, -, -, -, hc5e, -, -, -⟩ := hrel (central fam)
    rw [ht (sib fam i)] at hc5s
    have hchain : ((fam (sib fam i) i).val - (fam (central fam) i).val) •ᵥ
        (gadgetMatrix 𝓜(q, α) ((b : ZMod q)) innerRows innerDigits *ᵥ
          (resp (central fam)).innerDec i)
        = stmt.pp.innerMatrix *ᵥ
          (Hachi.jMatrix 𝓜(q, α) ((b : ZMod q)) ((2 ^ m) * messageDigits) zDigits *ᵥ
              (resp (sib fam i)).zDec
           - Hachi.jMatrix 𝓜(q, α) ((b : ZMod q)) ((2 ^ m) * messageDigits) zDigits *ᵥ
              (resp (central fam)).zDec) := by
      rw [matVecMul_sub, ← hc5s, ← hc5e, ← Hachi.tensorG_sub_challenge,
        Hachi.tensorG_coordDiff 𝓜(q, α) ((b : ZMod q)) innerRows innerDigits hcoord]
    simp only [extractedOpening]
    exact inner_eq_of_chain 𝓜(q, α) stmt.pp.innerMatrix
      ((resp (central fam)).innerDec i) _
      ((fam (sib fam i) i).val - (fam (central fam) i).val) hunit hchain

/-- **Sublemma 2 wiring (Eq. (15) for the extracted opening).** The shared-`ŵ` c3 row plus the
coordinate-isolated, unit-divided c4 rows give eval-consistency of `extractedOpening`. The
core computation `evalConsistency_of_star` is PROVED above (Part 4 / A4); this statement
discharges its `w`/`c3`/`c4` hypotheses from the star. -/
theorem evalConsistency_of_relOut_star (hq5 : q % 8 = 5) {b ω γ : ℕ} (hκ : (2 * ω) ^ 2 < q)
    (stmt : QuadEvalStatement 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (v : CarrierCom 𝓜(q, α) dRows)
    (fam : Fin (2 ^ r + 1) → (Fin (2 ^ r) → ShortChallenge 𝓜(q, α) ω))
    (resp : Fin (2 ^ r + 1) →
      QuadEvalResponse 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits)
    (hrel : ∀ j, ((stmt, v, fam j), resp j) ∈ relOut 𝓜(q, α) ((b : ZMod q)) ω γ)
    (hstar : ∃ e, StarAt fam e)
    (hw : ∀ j, (resp j).carrierDec = (resp (central fam)).carrierDec) :
    evalConsistency 𝓜(q, α) ((b : ZMod q)) stmt.avec stmt.bvec stmt.y
      (extractedOpening 𝓜(q, α) ((b : ZMod q)) fam resp) := by
  -- Apply `evalConsistency_of_star` at the shared recomposed carrier
  -- `w := G_{2^r} *ᵥ (resp (central fam)).carrierDec`.
  refine evalConsistency_of_star 𝓜(q, α) ((b : ZMod q)) stmt.avec stmt.bvec stmt.y
    (extractedOpening 𝓜(q, α) ((b : ZMod q)) fam resp)
    (gadgetMatrix 𝓜(q, α) ((b : ZMod q)) (2 ^ r) messageDigits *ᵥ (resp (central fam)).carrierDec)
    ?_ ?_
  · -- c3: verbatim c3 row of the central branch.
    obtain ⟨-, -, hc3, -, -, -, -, -⟩ := hrel (central fam)
    exact hc3
  · -- c4 j: the coordinate-isolated, unit-divided c4-subtract chain.
    intro j
    obtain ⟨-, -, -, hc4s, -, -, -, -⟩ := hrel (sib fam j)
    obtain ⟨-, -, -, hc4e, -, -, -, -⟩ := hrel (central fam)
    -- Move the sibling's c4 onto the shared carrier `ŵ := (resp (central fam)).carrierDec`.
    rw [hw (sib fam j)] at hc4s
    -- The difference challenge `c̄ⱼ = c_{sib j, j} − c_{central, j}` differs from `0`, hence is a
    -- unit (Lyubashevsky–Seiler, `‖c̄ⱼ‖₁ ≤ 2ω < √q`).
    have hne : (fam (sib fam j) j).val - (fam (central fam) j).val ≠ 0 :=
      sub_ne_zero_of_ne (ShortChallenge.val_ne_of_ne (sib_coordEq_ne fam hstar j))
    have hunit : IsUnit ((fam (sib fam j) j).val - (fam (central fam) j).val) :=
      isUnit_of_l1Norm_le α hq5 (Rq.l1Norm_pos_of_ne_zero 𝓜(q, α) hne)
        (ShortChallenge.l1Norm_val_sub_le _ _) hκ
    -- Subtract-and-isolate: the two branches' c4 rows, sharing `ŵ`, give `c̄ⱼ · wⱼ = aᵀ G Δzⱼ`.
    have hcoord : CoordEq j (fun i => (fam (sib fam j) i).val)
        (fun i => (fam (central fam) i).val) :=
      ShortChallenge.coordEq_val 𝓜(q, α) (coordEq_symm (sib_coordEq fam hstar j))
    have hchain : dot stmt.avec (gadgetMatrix 𝓜(q, α) ((b : ZMod q)) (2 ^ m) messageDigits *ᵥ
          ((Hachi.jMatrix 𝓜(q, α) ((b : ZMod q)) ((2 ^ m) * messageDigits) zDigits *ᵥ
              (resp (sib fam j)).zDec)
           - (Hachi.jMatrix 𝓜(q, α) ((b : ZMod q)) ((2 ^ m) * messageDigits) zDigits *ᵥ
              (resp (central fam)).zDec)))
        = ((fam (sib fam j) j).val - (fam (central fam) j).val) *
            (gadgetMatrix 𝓜(q, α) ((b : ZMod q)) (2 ^ r) messageDigits *ᵥ
              (resp (central fam)).carrierDec) j := by
      rw [matVecMul_sub, dot_sub, ← hc4s, ← hc4e, ← Hachi.tensorG1_sub_challenge,
        Hachi.tensorG1_coordDiff 𝓜(q, α) ((b : ZMod q)) messageDigits hcoord]
    -- Divide by `c̄ⱼ`: the extracted message `sⱼ := c̄ⱼ⁻¹ •ᵥ Δzⱼ` recovers `wⱼ` under `aᵀ G`.
    change (gadgetMatrix 𝓜(q, α) ((b : ZMod q)) (2 ^ r) messageDigits *ᵥ
          (resp (central fam)).carrierDec) j
        = dot stmt.avec (gadgetMatrix 𝓜(q, α) ((b : ZMod q)) (2 ^ m) messageDigits *ᵥ
            (Ring.inverse ((fam (sib fam j) j).val - (fam (central fam) j).val) •ᵥ
              ((Hachi.jMatrix 𝓜(q, α) ((b : ZMod q)) ((2 ^ m) * messageDigits) zDigits *ᵥ
                  (resp (sib fam j)).zDec)
               - (Hachi.jMatrix 𝓜(q, α) ((b : ZMod q)) ((2 ^ m) * messageDigits) zDigits *ᵥ
                  (resp (central fam)).zDec))))
    rw [matVecMul_scalarVecMul, dot_scalarVecMul, hchain, ← mul_assoc,
      Ring.inverse_mul_cancel _ hunit, one_mul]

/-- **The witness assembler is correct** — the `hmk` input to the generic assembly
`coordinateWiseSpecialSound_of_mkWitness` (`SingleRound.lean`): at every star-shaped family of
`relOut`-accepting branches, `buildWitness` lands in `relIn`. This is the ONLY remaining
mathematical obligation of the top-level theorem (see
`quadEval_coordinateWiseSpecialSound'`). -/
theorem buildWitness_mem_relIn (hq5 : q % 8 = 5) {b ω γ : ℕ} (hκ : (2 * ω) ^ 2 < q)
    (hτ : 0 < zDigits)
    (stmt : QuadEvalStatement 𝓜(q, α) innerRows (2 ^ m) messageDigits outerRows (2 ^ r) innerDigits
      dRows)
    (v : CarrierCom 𝓜(q, α) dRows)
    (fam : Fin (2 ^ r + 1) → (Fin (2 ^ r) → ShortChallenge 𝓜(q, α) ω))
    (resp : Fin (2 ^ r + 1) →
      QuadEvalResponse 𝓜(q, α) innerRows (2 ^ m) messageDigits (2 ^ r) innerDigits zDigits)
    (hrel : ∀ j, ((stmt, v, fam j), resp j) ∈ relOut 𝓜(q, α) ((b : ZMod q)) ω γ)
    (hstar : ∃ e, StarAt fam e) :
    (stmt, buildWitness 𝓜(q, α) ((b : ZMod q)) stmt v fam resp) ∈
      relIn 𝓜(q, α) ((b : ZMod q))
        (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω) := by
  -- PROOF PLAN (rank 6) — Hachi Lemma 8's three-case split. `unfold buildWitness` and split
  -- the two classical `dite`s (`rw [dif_pos hB]` / `rw [dif_neg hB, dif_pos hD]` / both neg).
  -- 1. Case hB (∃ j, flattenBlocks (resp j).innerDec ≠ flattenBlocks (resp e).innerDec):
  --    relIn membership at the literal `.msisB _` iota-reduces to the bare MSIS disjunct
  --    (smoke test above); close with msisB_of_two_valid (PROVED above) at
  --    B := stmt.pp.outerMatrix,
  --    hu₁/hu₂ := c2 of branches hB.choose / e (both equal stmt.u), hγ₁/hγ₂ := their c6t,
  --    hne := hB.choose_spec.
  -- 2. Case hD (¬hB, ∃ j, (resp j).carrierDec ≠ (resp e).carrierDec): close with
  --    msisD_of_two_valid (PROVED above) at D := stmt.pp.dMatrix, hv₁/hv₂ := c1 of branches
  --    hD.choose / e — both commit to the SHARED round-0 message `v` (the tree sharing of `v`
  --    across branches is exactly what fires this case), hγ₁/hγ₂ := their c6w,
  --    hne := hD.choose_spec.
  -- 3. Case ¬hB ∧ ¬hD: push_neg gives ∀-equalities; hw is direct; ht at family level via
  --    PolyVec.block_eq_of_flattenBlocks_eq (Vectors.lean:59) + funext from the flattened
  --    equality. relIn membership at the literal `.opening _` iota-reduces to
  --    `VerifiedOpening … ∧ evalConsistency …` (smoke test above); close with
  --    ⟨verifiedOpening_of_star hq5 hκ hτ … hrel hstar ht hw,
  --      evalConsistency_of_relOut_star hq5 hκ … hrel hstar hw⟩.
  unfold buildWitness
  by_cases hB : ∃ j, PolyVec.flattenBlocks (resp j).innerDec
      ≠ PolyVec.flattenBlocks (resp (central fam)).innerDec
  · -- Case (A): some branch's inner decomposition differs → `B`-kernel MSIS solution.
    rw [dif_pos hB]
    obtain ⟨-, hu₁, -, -, -, -, hγ₁, -⟩ := hrel hB.choose
    obtain ⟨-, hu₂, -, -, -, -, hγ₂, -⟩ := hrel (central fam)
    exact msisB_of_two_valid 𝓜(q, α) hu₁ hu₂ hγ₁ hγ₂ hB.choose_spec
  · by_cases hD : ∃ j, (resp j).carrierDec ≠ (resp (central fam)).carrierDec
    · -- Case (B): shared `t̂` but some carrier decomposition differs → `D`-kernel MSIS solution
      -- (the shared round-0 message `v` is what makes both branches commit to the same `v`).
      rw [dif_neg hB, dif_pos hD]
      obtain ⟨hv₁, -, -, -, -, hγ₁, -, -⟩ := hrel hD.choose
      obtain ⟨hv₂, -, -, -, -, hγ₂, -, -⟩ := hrel (central fam)
      exact msisD_of_two_valid 𝓜(q, α) hv₁ hv₂ hγ₁ hγ₂ hD.choose_spec
    · -- Case (C): shared `t̂` and `ŵ` → the subtract-and-divide weak opening (Sublemmas 1 & 2).
      rw [dif_neg hB, dif_neg hD]
      push Not at hB hD
      have ht : ∀ j, (resp j).innerDec = (resp (central fam)).innerDec :=
        fun j => funext fun i => PolyVec.block_eq_of_flattenBlocks_eq (hB j) i
      exact ⟨verifiedOpening_of_star hq5 hκ hτ stmt v fam resp hrel hstar ht hD,
        evalConsistency_of_relOut_star hq5 hκ stmt v fam resp hrel hstar hD⟩

/-- **Hachi Lemma 8 (CWSS of Hachi's polynomial-evaluation reduction, Figure 3; originally
Greyhound's [NS24, §3.1] folding protocol), top-level statement.**
The reduction's verifier is coordinate-wise special sound for the `(ℓ, k) = (2^r, 2)`
structure, with `relOut` = Eq. (20) + the `S_b` range checks and `relIn` = weak opening
(eval-consistent) ∨ MSIS(B) ∨ MSIS(D), at the derived constants
`βSq = quadEvalBetaSq γ b zDigits (deg φ) m messageDigits` and `κ = 2ω`.

The first proof step below is the load-bearing WitIn/WitOut wiring whose absence
invalidated v1 of this plan: the generic extractor `E` at `WitOut := QuadEvalResponse`
(relOut's witness) and `WitIn := QuadEvalWitness` (relIn's witness), assembled by `buildWitness` —
verified here to
elaborate. -/
theorem quadEval_coordinateWiseSpecialSound {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits) :
    (verifier (oSpec := oSpec) (ω := ω) 𝓜(q, α) (innerRows := innerRows)
        (messageDigits := messageDigits) (outerRows := outerRows)
        (innerDigits := innerDigits) (dRows := dRows) (m := m)
        (r := r)).coordinateWiseSpecialSound init impl
      (foldStructure (CarrierCom := CarrierCom 𝓜(q, α) dRows)
        (C := ShortChallenge 𝓜(q, α) ω) (r := r))
      (relIn 𝓜(q, α) ((b : ZMod q))
        (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω))
      (relOut (zDigits := zDigits) 𝓜(q, α) ((b : ZMod q)) ω γ) := by
  -- THE WIRING STEP (v1's blocker, now verified to typecheck):
  refine ⟨E (relOut (zDigits := zDigits) 𝓜(q, α) ((b : ZMod q)) ω γ)
    (buildWitness 𝓜(q, α) ((b : ZMod q))), ?_⟩
  -- The direct route mirrors the generic assembly `coordinateWiseSpecialSound_of_mkWitness`
  -- (`SingleRound.lean`), documenting the tree mechanics inline: shape-recover the tree, fire
  -- each branch's `relOut.language` guard, obtain the star center, then close with the sole
  -- math lemma `buildWitness_mem_relIn`.
  classical
  intro stmtIn tree hStruct hAcc
  -- 1. shape recovery: every accepting tree of `pSpec` is `tree2 v challenges`.
  obtain ⟨v, challenges, rfl⟩ := tree_shape tree
  have harity := (foldStructure_arity (CarrierCom := CarrierCom 𝓜(q, α) dRows)
    (C := ShortChallenge 𝓜(q, α) ω) (r := r)).symm
  -- 2. per-branch language membership (the extractor's guards fire on accepting trees).
  have hmem : ∀ j : Fin (2 ^ r + 1),
      ∃ w, ((stmtIn, v, challenges (Fin.cast harity j)), w) ∈
        relOut (zDigits := zDigits) 𝓜(q, α) ((b : ZMod q)) ω γ := by
    intro j
    have h := branch_relOut_language init impl _ (fun _ _ => rfl)
      (relOut (zDigits := zDigits) 𝓜(q, α) ((b : ZMod q)) ω γ) stmtIn v challenges hAcc
      (Fin.cast harity j)
    exact (Set.mem_language_iff _ _).1 h
  -- 3. the sibling family is special sound, hence has a star center.
  have hfam := (nodeOk_iff_family challenges).1 hStruct.1
  have hstar : ∃ e, StarAt
      (fun j : Fin (2 ^ r + 1) => challenges (Fin.cast harity j)) e :=
    exists_starAt (le_refl 2) (by omega) _ hfam
  -- 4. each chosen response satisfies `relOut` — `E` computes definitionally on `tree2`.
  have hbranch : ∀ j : Fin (2 ^ r + 1),
      ((stmtIn, v, challenges (Fin.cast harity j)),
        if h : ∃ w, ((stmtIn, v, challenges (Fin.cast harity j)), w) ∈
            relOut (zDigits := zDigits) 𝓜(q, α) ((b : ZMod q)) ω γ
          then h.choose else Classical.ofNonempty) ∈
        relOut (zDigits := zDigits) 𝓜(q, α) ((b : ZMod q)) ω γ := by
    intro j
    rw [dif_pos (hmem j)]
    exact (hmem j).choose_spec
  -- 5. close with the sole math lemma.
  exact buildWitness_mem_relIn hq5 hκ hτ stmtIn v _ _ hbranch hstar

/-- The same statement, proved in ONE LINE through A1's generic assembly
`coordinateWiseSpecialSound_of_mkWitness`: every tree/extractor/guard obligation is discharged
generically, and the whole of Hachi Lemma 8 reduces to the single math lemma
`buildWitness_mem_relIn`. Kept alongside `quadEval_coordinateWiseSpecialSound` so BOTH proof
routes' wiring is probe-verified. -/
theorem quadEval_coordinateWiseSpecialSound' {ι : Type} {oSpec : OracleSpec ι} {σ : Type}
    (init : ProbComp σ) (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hq5 : q % 8 = 5) {b ω γ : ℕ} (hκ : (2 * ω) ^ 2 < q) (hτ : 0 < zDigits) :
    (verifier (oSpec := oSpec) (ω := ω) 𝓜(q, α) (innerRows := innerRows)
        (messageDigits := messageDigits) (outerRows := outerRows)
        (innerDigits := innerDigits) (dRows := dRows) (m := m)
        (r := r)).coordinateWiseSpecialSound init impl
      (foldStructure (CarrierCom := CarrierCom 𝓜(q, α) dRows)
        (C := ShortChallenge 𝓜(q, α) ω) (r := r))
      (relIn 𝓜(q, α) ((b : ZMod q))
        (quadEvalBetaSq γ b zDigits ((𝓜(q, α)).φ.natDegree) m messageDigits) γ (2 * ω))
      (relOut (zDigits := zDigits) 𝓜(q, α) ((b : ZMod q)) ω γ) :=
  coordinateWiseSpecialSound_of_mkWitness init impl _ (fun _ _ => rfl) _ _
    (buildWitness 𝓜(q, α) ((b : ZMod q)))
    (fun stmtIn v fam resp hbranch hstar =>
      buildWitness_mem_relIn hq5 hκ hτ stmtIn v fam resp hbranch hstar)

-- NOTE (oracleVerifier wrapper): deliberately NOT included. An
-- `OracleVerifier.coordinateWiseSpecialSound` wrapper needs (i) an actual `OracleVerifier`
-- for the reduction, whose round-0 message `v : CarrierCom 𝓜(q,α) dRows` requires an
-- `OracleInterface (Simple.Commitment 𝓜(q,α) dRows)` instance that does not exist in the repo
-- (a query-model design decision), and (ii) the repo's oracle-level append theorem is itself
-- still sorried — so the plain-`Verifier` statement above is the
-- right interface for Lemma 8 now; the oracle wrapper is future work at the composition step.

end Pinned

end ArkLib.Lattices.Ajtai.InnerOuter

end QuadEvalExtraction
