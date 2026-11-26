/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quang Dao
-/
import VersoManual
import SpecSite.Data
import SpecSite.Meta.Blocks

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean
open SpecSite

#doc (Manual) "Spartan" =>
%%%
tag := "spartan"
%%%

Spartan proves that an assignment `z` satisfies the constraint system $`(A z) \circ (B z) = C z`,
where `A`, `B` and `C` are matrices with $`2^m` rows and $`2^n` columns. It reduces the constraint
system to two sum-checks. The specification is {name}`Specs.Spartan.spartanSpec`, in
`Specs/Examples/Spartan.lean`, with parameters the ring `R` and the sizes `m` and `n`. It is
written as two named stages, `outer` and `inner`, and each stage runs the loop
{name}`Specs.sumcheck` of the {ref "sumcheck"}[Sum-check page].

The protocol runs as follows:

* The matrices $`\tilde{A}`, $`\tilde{B}`, $`\tilde{C}` are input oracles. Each answers a point
  $`(r_x, r_y)` with its multilinear extension at that point. The prover sends the assignment
  $`\tilde{z}` as an oracle that answers with its multilinear extension, and the verifier samples
  $`\tau`.
* The stage `outer` consumes the claim
  $`\sum_{x \in \{0,1\}^m} \mathrm{eq}(\tau, x) \cdot ((\tilde{A}\tilde{z})(x) \cdot (\tilde{B}\tilde{z})(x) - (\tilde{C}\tilde{z})(x)) = 0`.
  It runs `m` sum-check rounds of degree 3 on ArkLib's `firstVirtual`. The prover then sends the row
  values $`v_A`, $`v_B`, $`v_C`, and the check `outer` tests
  $`\mathrm{eq}(\tau, r_x) \cdot (v_A v_B - v_C) = c_m`. The stage produces the evaluation claims
  $`(\tilde{A}\tilde{z})(r_x) = v_A`, $`(\tilde{B}\tilde{z})(r_x) = v_B` and
  $`(\tilde{C}\tilde{z})(r_x) = v_C`.
* The stage `inner` consumes these claims. The verifier samples $`\rho_A`, $`\rho_B`, $`\rho_C`,
  computes $`c_0 = \rho_A v_A + \rho_B v_B + \rho_C v_C`, and runs `n` sum-check rounds of degree 2
  on ArkLib's `secondVirtual`. The check `final` queries $`\tilde{A}`, $`\tilde{B}`, $`\tilde{C}`
  at $`(r_x, r_y)` and $`\tilde{z}` at $`r_y`.

# The oracles and the witness

A matrix answers a point $`(r_x, r_y)` with its multilinear extension, the row point first, as
ArkLib's Spartan does (`matrixEval`). A table of $`2^n` values answers a point with its multilinear
extension (`tableEval`). The input bundle holds the three matrices:

{decl Specs.Spartan.Mat Specs.Spartan.Table Specs.Spartan.SpartanIn}

The witness holds the matrices and the assignment. The honest prover reads the matrices from the
witness, because an honest function sees only the witness, not the input data. The completeness
theorem assumes that the input oracles hold the same matrices.

{decl Specs.Spartan.Witness}

# Formula helpers

The stage claims and the checks are built from a few formula helpers. Since the formula language has
no pair constructor, {name}`Specs.Spartan.pairF` writes a matrix query $`(r_x, r_y)` as
$`\iota_1(r_x) + \iota_2(r_y)` in the product group. This helper is the one gap in the formula API
that the module works around.

{decl Specs.Spartan.pairF Specs.Spartan.cube}

$`\mathrm{eq}(\tau, x)` is a product over the coordinates, the definition of `eq` in the paper. The
proof turns it into ArkLib's `eqWeight`.

{decl Specs.Spartan.eqF}

The row product $`(M \tilde{z})(x)` is a sum over $`\{0,1\}^n` of matrix and assignment queries,
the definition of $`M z` as a multilinear extension. {name}`Specs.Spartan.finalF` is the value that
the inner sum-check reduces to.

{decl Specs.Spartan.rowF Specs.Spartan.finalF}

# The stage claims

The names $`r_x`, $`r_y`, $`v_s` and $`\rho_s` have a fixed symbol as their subscript
({ref "names"}[Names and indices]):

{decl Specs.Spartan.rxN Specs.Spartan.ryN Specs.Spartan.vN Specs.Spartan.ρN}

The outer stage outputs the point $`r_x` and the claimed values of $`Az`, $`Bz`, $`Cz` at it. The
inner stage outputs the batching coefficients and the final claim of its sum-check, a
{name}`Specs.Claim`:

{decl Specs.Spartan.RowClaim Specs.Spartan.FinalClaim}

The row claims are one value, {name}`Specs.Spartan.rowClaims`, that both stages receive. The output
claim of `outer` and the input claim of `inner` are then the same formula by construction, and a
test checks that the two erased claims in the skeleton are equal.

{decl Specs.Spartan.RowHoles Specs.Spartan.rowClaims}

# The specification

The two sum-checks run on ArkLib's virtual polynomials, with degree 3 and 2:

{decl Specs.Spartan.outerPoly Specs.Spartan.innerPoly +statement}

The specification reads the three matrices, receives $`\tilde{z}`, samples $`\tau`, and runs the
two stages. Each stage's body calls {name}`Specs.sumcheck` with its own polynomial and count symbol
(`countName := "m"` and `countName := "n"`). The output of `outer` is a
{name}`Specs.Spartan.RowClaim`, which the stage `inner` receives as `e`.

{decl Specs.Spartan.spartanSpec}

The types of $`\tilde{z}` and $`\tau` print with the symbols `n` and `m` (`ty := …`), not their
values. Both stages name their loop `sumcheck`; the stage names scope the labels. Because each
stage's loop is one node with a generic round, the folded figure prints the outer target after the
loop as $`c_{m}` and the inner one as $`c_{n}`.

# The figure

{protocols SpecSite.spartan}

# Reaching moves

The stage names keep the labels of the two loops apart, and a subscript tells apart moves that share
a base ({ref "accessors"}[Transcript accessors]). The module's tests, at $`m = n = 2`:

```lean
example (tr : (Specs.Spartan.spartanSpec ℚ 2 2).Tr) :
    tr⟦outer, sumcheck, 0, g⟧ = tr.2.2.1 := rfl
example (tr : (Specs.Spartan.spartanSpec ℚ 2 2).Tr) :
    tr⟦inner, sumcheck, 0, g⟧ =
      tr.2.2.2.2.2.2.2.2.2.2.2.2.1 := rfl
example (tr : (Specs.Spartan.spartanSpec ℚ 2 2).Tr) :
    tr⟦outer, v_B⟧ = tr.2.2.2.2.2.2.2.1 := rfl
example (tr : (Specs.Spartan.spartanSpec ℚ 2 2).Tr) :
    tr⟦outer, v⟧ = tr⟦outer, v_A⟧ := rfl
example (tr : (Specs.Spartan.spartanSpec ℚ 2 2).Tr) :
    tr⟦inner, "\\rho_C"⟧ =
      tr.2.2.2.2.2.2.2.2.2.2.2.1 := rfl
```

With the base alone, `tr⟦outer, v⟧` reads the first row value, $`v_A`.

# What Lean proves

The tree is the oracle $`\tilde{z}`, the challenge $`\tau`, `m` sum-check rounds of degree 3, three
messages, three challenges and `n` sum-check rounds of degree 2:

{decl Specs.Spartan.spartanTree Specs.Spartan.spartan_tree}

The erased skeleton is the same for all `m` and `n`:

{decl Specs.Spartan.spartan_erase}

Honest acceptance: if the input oracles hold the matrices of the witness and the witness satisfies
$`(A z) \circ (B z) = C z`, the verdict accepts every honest transcript.

{decl Specs.Spartan.spartan_verdict_isSome +statement}

The proof applies {name}`Specs.Spec.verdict_isSome`, then {name}`Specs.sumcheck_complete` for both
stages, and ArkLib's identities `firstVirtual_cubeSum_eq_residualMLE`, `firstVirtual_eval`,
`secondVirtual_cubeSum_eq` and `secondVirtual_eval`. The oracle table invariant across each loop is
{name}`Specs.Frozen` from the {ref "branching"}[branching example].

{theorems Specs.Spartan.spartan_tree Specs.Spartan.spartan_erase Specs.Spartan.spartan_verdict_isSome}

The module's tests also check that the checks have the labels `sum`, `outer`, `sum` and `final`
in this order (the generic round check of each loop appears once), the folded TeX of the checks
`outer` and `final`, that the expanded figure at $`m = 2`, $`n = 3` unrolls five rounds in all and
prints the outer target as $`c_{2}` and the final one as $`c_{3}`, and that the output claim of
`outer` equals the input claim of `inner` as erased syntax.

Lean does not prove soundness, or any link between the stage claims and the checks. The verdict
never evaluates a stage claim. For Spartan the claims are therefore documentation that Lean only
type-checks. Soundness of the Spartan specification needs contracts for each stage and their
composition ({ref "limitations"}[limitation 7]).

# Design choices

* The honest prover reads the matrices from the witness (`Witness.mats`), and the theorem assumes
  that the input oracles hold the same matrices (`hdata`), because an honest function sees only the
  witness.
* A matrix query is the pair $`(r_x, r_y)`, the row point first, as in ArkLib's `matrixEval`.
  {name}`Specs.Spartan.pairF` writes the pair as a sum in the product group, since the formula
  language has no pair constructor.
* $`\mathrm{eq}(\tau, x)` is the product binder over the coordinates ({name}`Specs.Spartan.eqF`).
  That way the figure prints
  $`\prod_{j \in [m]} (\tau_{j} \cdot r_{x,j} + (1 - \tau_{j}) \cdot (1 - r_{x,j}))`, the
  definition in the paper. The proof turns it into ArkLib's `eqWeight` with
  {name}`Specs.prodM_id` and `Fin.prod_univ_def`.
* Since both stages receive one value of row claims, the output claim of `outer` and the input claim
  of `inner` are the same formula by construction.
* The row products in the stage claims are sums over $`\{0,1\}^n` of matrix and assignment queries
  ({name}`Specs.Spartan.rowF`).
* Both stages reuse {name}`Specs.sumcheck` with the block name `sumcheck` and count their rounds
  with `m` and `n`. Because the stage names scope the labels, `tr⟦outer, sumcheck, 0, g⟧` and
  `tr⟦inner, sumcheck, 0, g⟧` are different messages.
* The types of $`\tilde{z}` and $`\tau` print with the symbols `n` and `m`, so that
  {name}`Specs.Spartan.spartan_erase` holds.
