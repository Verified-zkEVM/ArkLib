/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import Specs.Examples.Branching
import ArkLib.ProofSystem.Spartan.Algebra.Realization

/-!
# Spartan as a specification

This module writes Spartan for the constraint system `(A z) ∘ (B z) = C z` as two named stages,
`outer` and `inner`. Each stage runs the loop `sumcheck` of `Specs.Examples.Sumcheck`.

* `spartanSpec R m n`: the matrices `Ã`, `B̃`, `C̃` (with `2^m` rows and `2^n` columns) are input
  oracles that answer a point `(r_x, r_y)` with the multilinear extension (`matrixEval`). The
  prover sends the assignment `z̃` as an oracle that answers with its multilinear extension
  (`tableEval`). The verifier samples `τ`.
  * The stage `outer` consumes the claim
    `Σ_{x ∈ {0,1}^m} eq(τ, x) · ((Ãz̃)(x) · (B̃z̃)(x) − (C̃z̃)(x)) = 0`. It runs `m` rounds of
    degree 3 on ArkLib's `firstVirtual`, the prover sends the row values `v_A`, `v_B`, `v_C`, and
    the check `outer` tests `eq(τ, r_x) · (v_A v_B − v_C) = c_m`. It produces the evaluation
    claims `(Ãz̃)(r_x) = v_A`, `(B̃z̃)(r_x) = v_B` and `(C̃z̃)(r_x) = v_C`.
  * The stage `inner` consumes these claims. The verifier samples `ρ_A`, `ρ_B`, `ρ_C`, computes
    `c_0 = ρ_A v_A + ρ_B v_B + ρ_C v_C` and runs `n` rounds of degree 2 on ArkLib's
    `secondVirtual`. The check `final` queries `Ã`, `B̃`, `C̃` at `(r_x, r_y)` and `z̃` at `r_y`.
* `spartan_tree`: the tree is the oracle `z̃`, the challenge `τ`, `m` sum-check rounds of degree
  3, three messages, three challenges and `n` sum-check rounds of degree 2. Lean proves it by
  `rfl`.
* `spartan_verdict_isSome`: if the input oracles hold the matrices of the witness and the witness
  satisfies `(A z) ∘ (B z) = C z`, the verdict accepts every honest transcript. The proof applies
  `Spec.verdict_isSome`, `sumcheck_complete` for both stages and ArkLib's identities
  (`firstVirtual_cubeSum_eq_residualMLE`, `firstVirtual_eval`, `secondVirtual_cubeSum_eq`,
  `secondVirtual_eval`).
* The tests read the round-0 `g` of each stage by its label path, check the labels and the
  expanded TeX of the checks, and check that the two stages share the row claims.

What is not proved: soundness, and any link between the stage claims and the checks. The verdict
never evaluates a stage claim, so the claims are documentation that Lean only type-checks.

## Design choices

* The honest prover reads the matrices from the witness (`Witness.mats`), and the theorem assumes
  that the input oracles hold the same matrices (`hdata`). *Why:* an honest function sees only
  the witness, not the input data.
* A matrix query is the pair `(r_x, r_y)`, the row point first, as in ArkLib's `matrixEval`. The
  formula language has no pair constructor, so `pairF` writes the pair as `ι₁(r_x) + ι₂(r_y)` in
  the product group. This helper is the one gap in the formula API that this module works around.
* `eq(τ, x)` is the product binder over the coordinates (`eqF`), so the figure prints
  `\prod_{j \in [m]} (\tau_{j} \cdot r_{x,j} + (1 - \tau_{j}) \cdot (1 - r_{x,j}))`. *Why:* it is
  the definition of `eq` in the paper. The proof turns it into ArkLib's `eqWeight` with `prodM_id`
  and `Fin.prod_univ_def`.
* The row claims are one value, `rowClaims`, that both stages receive. *Why:* the output claim of
  `outer` and the input claim of `inner` are then the same formula by construction. A test checks
  that the two erased claims in the skeleton are equal.
* The row products `(M z̃)(x)` in the stage claims are sums over `{0,1}^n` of matrix and
  assignment queries (`rowF`), the definition of `M z` as a multilinear extension.
* Both stages reuse `sumcheck` with the block name `sumcheck`, and count their rounds with `m`
  and `n` (`countName`). The stage names scope the labels: `tr⟦outer, sumcheck, 0, g⟧` and
  `tr⟦inner, sumcheck, 0, g⟧` are different messages. The folded figure of `Specs.Export` keys a
  block by its stage path, so it shows one generic round of each stage, and it prints the outer
  target as `c_{m}` and the inner one as `c_{n}`.
-/

set_option linter.hashCommand false

namespace Specs
open Interaction PFunctor FreeM Interaction.TwoParty.Lens Interaction.Oracle OracleComp
  OracleSpec Polynomial MvPolynomial Matrix

namespace Spartan
open _root_.Spartan.Algebra _root_.Spartan.Realization

section Spartan

variable {R : Type} [CommRing R] [DecidableEq R] [TypeName R] {m n : ℕ}

/-- The default answer of a handle over a ring. -/
local instance : Inhabited R := ⟨0⟩

instance {α : Type} [TypeName α] {k : ℕ} : TypeName (Fin k → α) :=
  ⟨TypeName.name α ++ "^{" ++ toString k ++ "}"⟩

/-! ## Oracles -/

/-- A matrix with `2^m` rows and `2^n` columns. -/
def Mat (R : Type) (m n : ℕ) : Type := Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R

/-- A matrix answers a point `(r_x, r_y)` with its multilinear extension at that point, the row
point first, as ArkLib's Spartan does (`matrixEval`). -/
instance : OracleInterface (Mat R m n) where
  Query := (Fin m → R) × (Fin n → R)
  spec := fun _ => R
  answer M q := matrixEval M q.1 q.2

/-- A table of `2^n` values. -/
def Table (R : Type) (n : ℕ) : Type := Fin (2 ^ n) → R

/-- A table answers a point `r` with its multilinear extension at `r` (`tableEval`). -/
instance : OracleInterface (Table R n) where
  Query := Fin n → R
  spec := fun _ => R
  answer v r := tableEval v r

instance : TypeName (Table R n) := ⟨TypeName.name R ++ "^{2^{" ++ toString n ++ "}}"⟩

/-- The input oracles: the three matrices `A`, `B`, `C` of the constraint system. -/
abbrev SpartanIn (R : Type) [CommRing R] (m n : ℕ) : OracleBundle :=
  OracleBundle.ofIndexed (fun _ : R1CS.MatrixIdx => Mat R m n) fun _ => inferInstance

/-- The witness: the matrices, which the honest prover reads, and the assignment `z`. -/
structure Witness (R : Type) (m n : ℕ) where
  /-- The matrices `A`, `B`, `C`. -/
  mats : R1CS.MatrixIdx → Matrix (Fin (2 ^ m)) (Fin (2 ^ n)) R
  /-- The assignment. -/
  z : Fin (2 ^ n) → R

/-! ## Formula helpers -/

section Helpers
variable {v : Type → Type} {o : Type → Type → Type}

/-- The pair `(a, b)` as a formula. The formula language has no pair constructor, so the pair is
the sum `ι₁(a) + ι₂(b)` in the product group. -/
def pairF {α β : Type} [AddZeroClass α] [AddZeroClass β] (a : Fml v o α) (b : Fml v o β) :
    Fml v o (α × β) :=
  Fml.app "\\iota_1" (fun a => (a, 0)) a + Fml.app "\\iota_2" (fun b => (0, b)) b

/-- The domain `{0, 1}` in `R`. -/
def bits : Fin 2 → R := fun b => (b.val : R)

/-- The Boolean cube `{0,1}^k`, printed with the exponent `ktex`. -/
def cube (k : ℕ) (ktex : String) : Dom (Fin k → R) := (Dom.ofFn "\\{0,1\\}" bits).pow k ktex

/-- `eq(τ, x) = ∏_{j ∈ [k]} (τ_j x_j + (1 - τ_j)(1 - x_j))`, a product over the coordinates. The
index set prints as `ktex`. -/
def eqF {k : ℕ} (τ x : Fml v o (Fin k → R)) (ktex : String := "[" ++ toString k ++ "]") :
    Fml v o R :=
  ∏∈ j ∈ Dom.fin k ktex, Fml.index τ (.var j) * Fml.index x (.var j) +
    (1 - Fml.index τ (.var j)) * (1 - Fml.index x (.var j))

/-- `(M z)(x) = Σ_{y ∈ {0,1}^n} M(x, y) · z(y)`: the multilinear extension of `M z` at `x`. -/
def rowF (M : o ((Fin m → R) × (Fin n → R)) R) (z : o (Fin n → R) R)
    (x : Fml v o (Fin m → R)) : Fml v o R :=
  ∑∈ y ∈ cube n "n", Fml.query M (pairF x (Fml.var y)) * ask z y

/-- The value `(ρ_A Ã(r_x, r_y) + ρ_B B̃(r_x, r_y) + ρ_C C̃(r_x, r_y)) · z̃(r_y)` that the inner
sum-check reduces to. -/
def finalF (A B C : o ((Fin m → R) × (Fin n → R)) R) (z : o (Fin n → R) R)
    (rx : Fml v o (Fin m → R)) (ry : Fml v o (Fin n → R)) (ρa ρb ρc : Fml v o R) :
    Fml v o R :=
  (ρa * Fml.query A (pairF rx ry) + ρb * Fml.query B (pairF rx ry) +
    ρc * Fml.query C (pairF rx ry)) * Fml.query z ry

end Helpers

/-! ## Stage claims -/

/-- The name `r_x` of the outer sum-check point. -/
def rxN : Name := ⟨"r", .sym "x"⟩
/-- The name `r_y` of the inner sum-check point. -/
def ryN : Name := ⟨"r", .sym "y"⟩
/-- The name `v_s` of the claimed value of a row product. -/
def vN (s : String) : Name := ⟨"v", .sym s⟩
/-- The name `ρ_s` of a batching coefficient. -/
def ρN (s : String) : Name := ⟨"\\rho", .sym s⟩

/-- The output of the outer stage: the point `r_x` and the claimed values of `Az`, `Bz`, `Cz` at
`r_x`. -/
structure RowClaim (R : Type) (m : ℕ) where
  /-- The point `r_x`. -/
  rx : Val rxN (Fin m → R)
  /-- The claimed value of `Az` at `r_x`. -/
  vA : Val (vN "A") R
  /-- The claimed value of `Bz` at `r_x`. -/
  vB : Val (vN "B") R
  /-- The claimed value of `Cz` at `r_x`. -/
  vC : Val (vN "C") R

/-- The output of the inner stage: the batching coefficients and the final sum-check claim. -/
structure FinalClaim (R : Type) (n : ℕ) where
  /-- The coefficient of `A`. -/
  ρA : Val (ρN "A") R
  /-- The coefficient of `B`. -/
  ρB : Val (ρN "B") R
  /-- The coefficient of `C`. -/
  ρC : Val (ρN "C") R
  /-- The point `r_y` and the final claim of the inner sum-check. -/
  claim : Claim R n

/-- The holes of the row claims: the matrices, the assignment, the point `r_x` and the claimed
values. -/
abbrev RowHoles (R : Type) (m n : ℕ) : List Hole :=
  [.orc "\\tilde{A}" ((Fin m → R) × (Fin n → R)) R,
    .orc "\\tilde{B}" ((Fin m → R) × (Fin n → R)) R,
    .orc "\\tilde{C}" ((Fin m → R) × (Fin n → R)) R, .orc "\\tilde{z}" (Fin n → R) R,
    .val rxN (Fin m → R), .val (vN "A") R, .val (vN "B") R, .val (vN "C") R]

/-- The row claims `(Ãz̃)(r_x) = v_A`, `(B̃z̃)(r_x) = v_B` and `(C̃z̃)(r_x) = v_C`: the output claim
of the stage `outer` and the input claim of the stage `inner`. -/
def rowClaims {v : Type → Type} {o : Type → Type → Type} : Curry v o (RowHoles R m n) Bool :=
  fun A B C z rx a b c =>
    (rowF A z (Fml.var rx) =' Fml.var a) ∧' (rowF B z (Fml.var rx) =' Fml.var b) ∧'
      (rowF C z (Fml.var rx) =' Fml.var c)

/-! ## The specification -/

/-- The degree-3 polynomial of the outer sum-check, `eq(τ, X) · (Az(X) · Bz(X) - Cz(X))`. -/
noncomputable def outerPoly (τ : Fin m → R) (w : Witness R m n) : R⦃≤ 3⦄[X Fin m] :=
  ⟨firstVirtual w.mats w.z τ, (mem_restrictDegree _ _ _).2 fun _ hs i =>
    degreeOf_le_iff.1 (firstVirtual_degree_le_three w.mats w.z τ i) _ hs⟩

/-- The batching coefficients as a function on the matrix indices. -/
def ρFun (a b c : R) : R1CS.MatrixIdx → R
  | .A => a
  | .B => b
  | .C => c

/-- The degree-2 polynomial of the inner sum-check,
`(ρ_A A(r_x, Y) + ρ_B B(r_x, Y) + ρ_C C(r_x, Y)) · z(Y)`. -/
noncomputable def innerPoly (rx : Fin m → R) (ρ : R1CS.MatrixIdx → R) (w : Witness R m n) :
    R⦃≤ 2⦄[X Fin n] :=
  ⟨secondVirtual w.mats w.z rx ρ, (mem_restrictDegree _ _ _).2 fun _ hs i =>
    degreeOf_le_iff.1 (secondVirtual_degree_le_two w.mats w.z rx ρ i) _ hs⟩

variable (R) in
/-- Spartan for the constraint system `(A z) ∘ (B z) = C z`. -/
noncomputable def spartanSpec (m n : ℕ) :=
  Spec.mk (In := SpartanIn R m n) (W := Witness R m n) (T := Unit) fun _ : Unit =>
  input "\\tilde{A}" ((Fin m → R) × (Fin n → R)) R "\\mathbb{F}^{2^m \\times 2^n}"
    (fun q => ⟨.A, q⟩) (fun _ => rfl) fun A =>
  input "\\tilde{B}" ((Fin m → R) × (Fin n → R)) R "\\mathbb{F}^{2^m \\times 2^n}"
    (fun q => ⟨.B, q⟩) (fun _ => rfl) fun B =>
  input "\\tilde{C}" ((Fin m → R) × (Fin n → R)) R "\\mathbb{F}^{2^m \\times 2^n}"
    (fun q => ⟨.C, q⟩) (fun _ => rfl) fun C =>
  oracle "\\tilde{z}" (Table R n) R "\\mathsf{assignment}" (fun w => w.z) fun z =>
  challenge "\\tau" (Fin m → R) fun τ =>
  stage "outer" ⟪A, B, C, z, τ⟫
    (fun A B C z τ => (∑∈ x ∈ cube m "m",
      eqF (Fml.var τ) (Fml.var x) "[m]" *
        (rowF A z (Fml.var x) * rowF B z (Fml.var x) - rowF C z (Fml.var x))) =' 0)
    (fun e : RowClaim R m => ⟪A, B, C, z, e.rx, e.vA, e.vB, e.vC⟫) rowClaims
    (fun next =>
      sumcheck m bits (outerPoly τ.val) ⟨⟨0⟩, Fin.elim0⟩ (countName := "m") fun st =>
      message (vN "A") R "\\mathsf{row}_A" (fun w => rowEval (w.mats .A) w.z st.rs) fun a =>
      message (vN "B") R "\\mathsf{row}_B" (fun w => rowEval (w.mats .B) w.z st.rs) fun b =>
      message (vN "C") R "\\mathsf{row}_C" (fun w => rowEval (w.mats .C) w.z st.rs) fun c =>
      check "outer" ⟪τ, (⟨st.rs⟩ : Val rxN (Fin m → R)), a, b, c, st.c⟫
        (fun τ rx a b c e =>
          eqF (Fml.var τ) (Fml.var rx) "[m]" * (Fml.var a * Fml.var b - Fml.var c) =' Fml.var e) <|
      next ⟨⟨st.rs⟩, a, b, c⟩)
    fun e =>
  stage "inner" ⟪A, B, C, z, e.rx, e.vA, e.vB, e.vC⟫ rowClaims
    (fun f : FinalClaim R n =>
      ⟪A, B, C, z, e.rx, (⟨f.claim.rs⟩ : Val ryN (Fin n → R)), f.ρA, f.ρB, f.ρC, f.claim.c⟫)
    (fun A B C z rx ry ρa ρb ρc e =>
      finalF A B C z (Fml.var rx) (Fml.var ry) (Fml.var ρa) (Fml.var ρb) (Fml.var ρc) =' Fml.var e)
    (fun next =>
      challenge (ρN "A") R fun ρa =>
      challenge (ρN "B") R fun ρb =>
      challenge (ρN "C") R fun ρc =>
      compute (ix "c" 0) R ⟪ρa, e.vA, ρb, e.vB, ρc, e.vC⟫
        (fun ρa a ρb b ρc c =>
          Fml.var ρa * Fml.var a + Fml.var ρb * Fml.var b + Fml.var ρc * Fml.var c) fun c0 =>
      sumcheck n bits (innerPoly e.rx.val (ρFun ρa.val ρb.val ρc.val)) ⟨c0, Fin.elim0⟩
        (countName := "n") fun st => next ⟨ρa, ρb, ρc, st⟩)
    fun f =>
  check "final" ⟪A, B, C, z, e.rx, (⟨f.claim.rs⟩ : Val ryN (Fin n → R)), f.ρA, f.ρB, f.ρC,
      f.claim.c⟫
    (fun A B C z rx ry ρa ρb ρc e =>
      finalF A B C z (Fml.var rx) (Fml.var ry) (Fml.var ρa) (Fml.var ρb) (Fml.var ρc) ='
        Fml.var e) <|
  done ()

variable (R) in
/-- The expected tree: the oracle `z`, the challenge `τ`, the `m` outer sum-check rounds of degree
3, the three row values, the three batching challenges and the `n` inner sum-check rounds of
degree 2. -/
noncomputable abbrev spartanTree (m n : ℕ) : OracleProtocol :=
  .liftBind (.oracle (Table R n) inferInstance) fun _ =>
  .liftBind (.challenge (Fin m → R)) fun _ =>
  roundsTree (fun _ => roundTree R 3)
    (.liftBind (.message R) fun _ => .liftBind (.message R) fun _ =>
      .liftBind (.message R) fun _ => .liftBind (.challenge R) fun _ =>
      .liftBind (.challenge R) fun _ => .liftBind (.challenge R) fun _ =>
      roundsTree (fun _ => roundTree R 2) (.pure ⟨⟩) 0 n) 0 m

/-- The tree of the specification is the expected tree. -/
theorem spartan_tree (m n : ℕ) : (spartanSpec R m n).tree = spartanTree R m n := rfl

/-- **Honest acceptance.** If the input oracles hold the matrices of the witness and the witness
satisfies `(A z) ∘ (B z) = C z`, the verdict accepts every transcript of the honest prover. -/
theorem spartan_verdict_isSome (w : Witness R m n) (data : (SpartanIn R m n).Data)
    (tr : (spartanSpec R m n).Tr) (hdata : ∀ i, data i = w.mats i)
    (hR : (w.mats .A *ᵥ w.z) * (w.mats .B *ᵥ w.z) = w.mats .C *ᵥ w.z)
    (hh : ((spartanSpec R m n).desc ()).Honest w ((SpartanIn R m n).answer data) tr .empty 0) :
    ((spartanSpec R m n).verdict () data tr).isSome := by
  refine Spec.verdict_isSome _ () w data tr ?_ hh
  unfold spartanSpec
  erw [Desc.Complete.eq_7, Desc.Complete.eq_7, Desc.Complete.eq_7, Desc.Complete.eq_3,
    Desc.Complete.eq_4]
  intro τ
  erw [Desc.Complete.eq_9]
  refine sumcheck_complete bits (outerPoly τ) w _ _ _ _ _ (Frozen _ 4) Frozen.ext ?_ m 0 _ _
    _ _ (Frozen.refl _ _) ?_
  · intro st env ℓ hp hev
    erw [Desc.Complete.eq_2, Desc.Complete.eq_2, Desc.Complete.eq_2, Desc.Complete.eq_5]
    refine ⟨?_, ?_⟩
    · simp only [Closed.inst, ToArgs.toArgs_prod, ToArgs.toArgs_val, Args.append]
      change decide ((prodM (m := Id) (fun j : Fin m =>
          pure (τ j * st.rs j + (1 - τ j) * (1 - st.rs j))) (List.finRange m)).run *
        (rowEval (w.mats .A) w.z st.rs * rowEval (w.mats .B) w.z st.rs -
          rowEval (w.mats .C) w.z st.rs) = st.c.val) = true
      rw [prodM_id, Id.run_pure, ← Fin.prod_univ_def]
      change decide (eqWeight τ st.rs * (rowEval (w.mats .A) w.z st.rs *
        rowEval (w.mats .B) w.z st.rs - rowEval (w.mats .C) w.z st.rs) = st.c.val) = true
      refine decide_eq_true ?_
      rw [← hev, eqWeight_eq, rowEval_eq, rowEval_eq, rowEval_eq]
      exact (firstVirtual_eval w.mats w.z τ st.rs).symm
    · erw [Desc.Complete.eq_10, Desc.Complete.eq_9, Desc.Complete.eq_4]
      intro ρa
      erw [Desc.Complete.eq_4]
      intro ρb
      erw [Desc.Complete.eq_4]
      intro ρc
      erw [Desc.Complete.eq_6]
      refine sumcheck_complete bits (innerPoly st.rs (ρFun ρa ρb ρc)) w _ _ _ _ _ (Frozen _ 4)
        Frozen.ext ?_ n 0 _ _ _ _ hp ?_
      · intro st' env' ℓ' hp' hev'
        erw [Desc.Complete.eq_10, Desc.Complete.eq_5]
        refine ⟨?_, trivial⟩
        simp only [Closed.inst, ToArgs.toArgs_prod, ToArgs.toArgs_ohdl, ToArgs.toArgs_val,
          Args.append]
        change decide (((ρa * (env'.find (default : R) 0
            ((st.rs, (0 : Fin n → R)) + ((0 : Fin m → R), st'.rs))).run +
          ρb * (env'.find (default : R) 1
            ((st.rs, (0 : Fin n → R)) + ((0 : Fin m → R), st'.rs))).run +
          ρc * (env'.find (default : R) 2
            ((st.rs, (0 : Fin n → R)) + ((0 : Fin m → R), st'.rs))).run) *
          (env'.find (default : R) 3 st'.rs).run) = st'.c.val) = true
        rw [hp'.find (i := 0) (by norm_num), hp'.find (i := 1) (by norm_num),
          hp'.find (i := 2) (by norm_num), hp'.find (i := 3) (by norm_num)]
        simp only [Handlers.find_ext_ne, Handlers.find_ext_self, inputEntry, Desc.honestEntry,
          ne_eq, zero_ne_one, Nat.reduceAdd, Nat.reduceEqDiff, not_false_eq_true, cast_eq,
          Prod.mk_add_mk, add_zero, zero_add, Id.run_pure, Id.run_map]
        refine decide_eq_true ?_
        change (ρa * matrixEval (data .A) st.rs st'.rs + ρb * matrixEval (data .B) st.rs st'.rs +
          ρc * matrixEval (data .C) st.rs st'.rs) * tableEval w.z st'.rs = st'.c.val
        rw [hdata, hdata, hdata, matrixEval_eq, matrixEval_eq, matrixEval_eq, tableEval_eq, ← hev']
        exact (secondVirtual_eval w.mats w.z st.rs (ρFun ρa ρb ρc) st'.rs).symm
      · change Sumcheck.roundSum bits 0 Fin.elim0 (innerPoly st.rs (ρFun ρa ρb ρc) w).val =
          ρa * rowEval (w.mats .A) w.z st.rs + ρb * rowEval (w.mats .B) w.z st.rs +
            ρc * rowEval (w.mats .C) w.z st.rs
        rw [roundSum_zero, rowEval_eq, rowEval_eq, rowEval_eq]
        exact secondVirtual_cubeSum_eq w.mats w.z st.rs (ρFun ρa ρb ρc)
  · change Sumcheck.roundSum bits 0 Fin.elim0 (outerPoly τ w).val = 0
    rw [roundSum_zero]
    have h := firstVirtual_cubeSum_eq_residualMLE w.mats w.z τ
    rw [(residualMLE_zero_iff_matrix_relation w.mats w.z).2 hR, map_zero] at h
    exact h

section Tests

/-- The outer stage's round-0 `g` by its label path. -/
example (tr : (spartanSpec ℚ 2 2).Tr) : tr⟦outer, sumcheck, 0, g⟧ = tr.2.2.1 := rfl

/-- The inner stage's round-0 `g` by its label path: the labels of the two stages do not
collide. -/
example (tr : (spartanSpec ℚ 2 2).Tr) :
    tr⟦inner, sumcheck, 0, g⟧ = tr.2.2.2.2.2.2.2.2.2.2.2.2.1 := rfl

/-- The labels and the expanded TeX of the checks. -/
def checkTex (ks : Skel) : List (String × String) :=
  ks.checks.map fun (c : String × Syn) => (c.1, c.2.tex Mode.expanded)

/-! With `m = 2` and `n = 3`: two outer rounds, the outer check, three inner rounds and the final
check. -/
#guard (checkTex (spartanSpec ℚ 2 3).skeleton).map (·.1) ==
  ["sum", "sum", "outer", "sum", "sum", "sum", "final"]

#guard (checkTex (spartanSpec ℚ 2 3).skeleton).lookup "outer" == some
  "(\\prod_{j \\in [m]} (\\tau_{j} \\cdot r_{x,j} + (1 - \\tau_{j}) \\cdot (1 - r_{x,j}))) \\cdot \
  (v_{A} \\cdot v_{B} - v_{C}) = c_{2}"

/-- The stages of a skeleton without branches, each with its input and output claims. -/
def stageClaims : Skel → List (String × Syn × Syn)
  | .cons (.beginStage s φ ψ) rest => (s, φ, ψ) :: stageClaims rest
  | .cons _ rest => stageClaims rest
  | _ => []

/-! The two stages share the row claims: the output claim of `outer` is the input claim of
`inner`, as erased syntax. -/
#guard match stageClaims (spartanSpec ℚ 2 3).skeleton with
  | [("outer", _, out), ("inner", inp, _)] => out == inp
  | _ => false

#guard (checkTex (spartanSpec ℚ 2 3).skeleton).lookup "final" == some
  "(\\rho_{A} \\cdot \\tilde{A}(\\mathrm{\\iota_1}(r_{x}) + \\mathrm{\\iota_2}(r_{y})) + \
  \\rho_{B} \\cdot \\tilde{B}(\\mathrm{\\iota_1}(r_{x}) + \\mathrm{\\iota_2}(r_{y})) + \
  \\rho_{C} \\cdot \\tilde{C}(\\mathrm{\\iota_1}(r_{x}) + \\mathrm{\\iota_2}(r_{y}))) \\cdot \
  \\tilde{z}(r_{y}) = c_{3}"

end Tests

end Spartan

#print axioms outerPoly
#print axioms innerPoly
#print axioms spartan_tree
#print axioms spartan_verdict_isSome

end Spartan

end Specs
