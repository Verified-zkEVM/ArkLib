# ArkLib dedup-candidate report

Generated from `docs/kb/_generated/declarations.json`. **Eyeball, do not auto-rewrite.** The point is to surface name collisions and doc-string overlap that *might* indicate an opportunity to consolidate.

## Stats

- `ArkLib` — 240 files, 4348 declarations

## Same short-name across multiple files (125 groups)

Each group lists declarations sharing a short name across ≥2 files. Most are legitimate (overloaded interface, paper-shape vs general form), but the list is the right anchor to look for duplicates.

### `oracleVerifier` (10 declarations, 9 files)

- `def Binius.RingSwitching.BatchingPhase.oracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:138](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L138) — (no docstring)
- `def CheckClaim.oracleVerifier` [ArkLib/ProofSystem/Component/CheckClaim.lean:153](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L153) — The oracle verifier for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleVerifier` [ArkLib/ProofSystem/Component/DoNothing.lean:72](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L72) — The oracle verifier for the `DoNothing` oracle reduction.
- `def RandomQuery.oracleVerifier` [ArkLib/ProofSystem/Component/RandomQuery.lean:82](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L82) — The oracle verifier simply returns the challenge, and performs no checks.
- `def ReduceClaim.oracleVerifier` [ArkLib/ProofSystem/Component/ReduceClaim.lean:177](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L177) — The oracle verifier for the `ReduceClaim` oracle reduction.
- `def SendClaim.oracleVerifier` [ArkLib/ProofSystem/Component/SendClaim.lean:63](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L63) — The verifier checks that the relationship `rel oldStmt newStmt` holds. It has access to the original
- `def SendSingleWitness.oracleVerifier` [ArkLib/ProofSystem/Component/SendWitness.lean:212](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L212) — The oracle verifier for the `SendSingleWitness` oracle reduction. The verifier receives the input st
- `def Sumcheck.Spec.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:158](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L158) — The oracle verifier for the (full) sum-check protocol
- `def Sumcheck.Spec.SingleRound.Simple.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:426](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L426) — (no docstring)
- `def Sumcheck.Spec.SingleRound.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:848](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L848) — The oracle verifier for the `i`-th round of the sum-check protocol

### `reduction` (10 declarations, 9 files)

- `def KZG.CommitmentScheme.reduction` [ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean:115](../../../ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean#L115) — The reduction breaking ARSDH using a successful function-binding adversary. The reduction follows th
- `def CheckClaim.reduction` [ArkLib/ProofSystem/Component/CheckClaim.lean:55](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L55) — The reduction for the `CheckClaim` reduction.
- `def DoNothing.reduction` [ArkLib/ProofSystem/Component/DoNothing.lean:43](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L43) — The reduction for the `DoNothing` reduction. - Prover simply returns the statement and witness. - Ve
- `def NoInteraction.reduction` [ArkLib/ProofSystem/Component/NoInteraction.lean:62](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L62) — The no-interaction reduction can be specified by a tuple of functions: - `mapStmt : StmtIn → OracleC
- `def ReduceClaim.reduction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:56](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L56) — The reduction for the `ReduceClaim` reduction.
- `def SendWitness.reduction` [ArkLib/ProofSystem/Component/SendWitness.lean:58](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L58) — (no docstring)
- `def Fri.Spec.reduction` [ArkLib/ProofSystem/Fri/Spec/General.lean:98](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L98) — (no docstring)
- `def Sumcheck.Spec.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:168](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L168) — The sum-check protocol as a reduction
- `def Sumcheck.Spec.SingleRound.Simple.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:413](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L413) — The reduction for the simple description of a single round of sum-check
- `def Sumcheck.Spec.SingleRound.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:853](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L853) — The sum-check reduction for the `i`-th round of the sum-check protocol

### `oracleReduction` (10 declarations, 8 files)

- `def CheckClaim.oracleReduction` [ArkLib/ProofSystem/Component/CheckClaim.lean:161](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L161) — The oracle reduction for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleReduction` [ArkLib/ProofSystem/Component/DoNothing.lean:82](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L82) — The oracle reduction for the `DoNothing` oracle reduction. - Prover simply returns the (non-oracle a
- `def RandomQuery.oracleReduction` [ArkLib/ProofSystem/Component/RandomQuery.lean:100](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L100) — Combine the trivial prover and this verifier to form the `RandomQuery` oracle reduction: the input o
- `def ReduceClaim.oracleReduction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:183](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L183) — The oracle reduction for the `ReduceClaim` oracle reduction.
- `def SendClaim.oracleReduction` [ArkLib/ProofSystem/Component/SendClaim.lean:92](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L92) — Combine the prover and verifier into an oracle reduction. The input has no statement or witness, but
- `def SendSingleWitness.oracleReduction` [ArkLib/ProofSystem/Component/SendWitness.lean:225](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L225) — (no docstring)
- `def Sumcheck.Spec.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:180](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L180) — The sum-check protocol as an oracle reduction
- `def Sumcheck.Spec.SingleRound.Simpler.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:300](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L300) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:443](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L443) — (no docstring)
- `def Sumcheck.Spec.SingleRound.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:859](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L859) — The sum-check oracle reduction for the `i`-th round of the sum-check protocol

### `OracleStatement` (8 declarations, 8 files)

- `def BatchedFri.Spec.OracleStatement` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:40](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L40) — An oracle for each batched polynomial.
- `def Binius.BinaryBasefold.OracleStatement` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:547](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L547) — For the `i`-th round of the protocol, there will be oracle statements corresponding to all committed
- `def R1CS.OracleStatement` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:48](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L48) — (no docstring)
- `def Fri.Spec.OracleStatement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:86](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L86) — For the `i`-th round of the protocol, there will be `i + 1` oracle statements, one for the beginning
- `abbrev Spartan.Spec.OracleStatement` [ArkLib/ProofSystem/Spartan/Basic.lean:144](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L144) — This unfolds to `A, B, C : Matrix (Fin 2 ^ ℓ_m) (Fin 2 ^ ℓ_n) R`
- `def StirIOP.OracleStatement` [ArkLib/ProofSystem/Stir/MainThm.lean:81](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L81) — `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type
- `def Sumcheck.Spec.OracleStatement` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:135](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L135) — Oracle statement for sum-check, which is a multivariate polynomial over `n` variables of individual 
- `def WhirIOP.OracleStatement` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:146](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L146) — `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type

### `verifier` (9 declarations, 7 files)

- `def CheckClaim.verifier` [ArkLib/ProofSystem/Component/CheckClaim.lean:50](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L50) — The verifier for the `CheckClaim` reduction.
- `def DoNothing.verifier` [ArkLib/ProofSystem/Component/DoNothing.lean:34](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L34) — The verifier for the `DoNothing` reduction.
- `def NoInteraction.verifier` [ArkLib/ProofSystem/Component/NoInteraction.lean:53](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L53) — The verifier in a no-interaction reduction takes an empty transcript, and hence reduce to a function
- `def ReduceClaim.verifier` [ArkLib/ProofSystem/Component/ReduceClaim.lean:52](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L52) — The verifier for the `ReduceClaim` reduction.
- `def SendWitness.verifier` [ArkLib/ProofSystem/Component/SendWitness.lean:54](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L54) — (no docstring)
- `def Sumcheck.Spec.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:149](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L149) — The verifier for the (full) sum-check protocol
- `def Sumcheck.Spec.SingleRound.Simple.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:404](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L404) — The verifier for the simple description of a single round of sum-check
- `def Sumcheck.Spec.SingleRound.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:842](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L842) — The verifier for the `i`-th round of the sum-check protocol
- `def Sumcheck.Spec.SingleRound.Unfolded.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1090](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1090) — The (non-oracle) verifier of the sum-check protocol for the `i`-th round, where `i < n + 1`

### `oracleProver` (8 declarations, 7 files)

- `def Binius.RingSwitching.BatchingPhase.oracleProver` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:90](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L90) — (no docstring)
- `def CheckClaim.oracleProver` [ArkLib/ProofSystem/Component/CheckClaim.lean:140](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L140) — The oracle prover for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleProver` [ArkLib/ProofSystem/Component/DoNothing.lean:67](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L67) — The oracle prover for the `DoNothing` oracle reduction.
- `def RandomQuery.oracleProver` [ArkLib/ProofSystem/Component/RandomQuery.lean:62](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L62) — The prover is trivial: it has no messages to send.  It only receives the verifier's challenge `q`, a
- `def ReduceClaim.oracleProver` [ArkLib/ProofSystem/Component/ReduceClaim.lean:167](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L167) — The oracle prover for the `ReduceClaim` oracle reduction.
- `def SendClaim.oracleProver` [ArkLib/ProofSystem/Component/SendClaim.lean:36](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L36) — The prover takes in the old oracle statement as input, and sends it as the protocol message.
- `def SendWitness.oracleProver` [ArkLib/ProofSystem/Component/SendWitness.lean:108](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L108) — The oracle prover for the `SendWitness` oracle reduction. For each round `i : Fin (FinEnum.card ιw)`
- `def SendSingleWitness.oracleProver` [ArkLib/ProofSystem/Component/SendWitness.lean:196](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L196) — The oracle prover for the `SendSingleWitness` oracle reduction. The prover sends the witness `wit` t

### `pSpec` (8 declarations, 6 files)

- `def RandomQuery.pSpec` [ArkLib/ProofSystem/Component/RandomQuery.lean:53](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L53) — (no docstring)
- `def SendClaim.pSpec` [ArkLib/ProofSystem/Component/SendClaim.lean:31](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L31) — (no docstring)
- `def SendWitness.pSpec` [ArkLib/ProofSystem/Component/SendWitness.lean:39](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L39) — (no docstring)
- `def Fri.Spec.FoldPhase.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:290](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L290) — Each round of the FRI protocol begins with the verifier sending a random field element as the challe
- `def Fri.Spec.FinalFoldPhase.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:492](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L492) — The final folding round of the FRI protocol begins with the verifier sending a random field element 
- `def Fri.Spec.QueryRound.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:667](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L667) — (no docstring)
- `def Sumcheck.Spec.pSpec` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:125](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L125) — The protocol specification for the general sum-check protocol, which is the composition of the singl
- `def Sumcheck.Spec.SingleRound.pSpec` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:148](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L148) — The protocol specification for a single round of sum-check. Has the form `⟨!v[.P_to_V, .V_to_P], !v[

### `prover` (7 declarations, 6 files)

- `def CheckClaim.prover` [ArkLib/ProofSystem/Component/CheckClaim.lean:39](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L39) — The prover for the `CheckClaim` reduction.
- `def DoNothing.prover` [ArkLib/ProofSystem/Component/DoNothing.lean:30](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L30) — The prover for the `DoNothing` reduction.
- `def NoInteraction.prover` [ArkLib/ProofSystem/Component/NoInteraction.lean:43](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L43) — The prover in a no-interaction reduction can be specified by a tuple of functions: - `mapStmt : Stmt
- `def ReduceClaim.prover` [ArkLib/ProofSystem/Component/ReduceClaim.lean:44](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L44) — The prover for the `ReduceClaim` reduction.
- `def SendWitness.prover` [ArkLib/ProofSystem/Component/SendWitness.lean:44](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L44) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.prover` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:382](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L382) — The prover in the simple description of a single round of sum-check. Takes in input `target : R` and
- `def Sumcheck.Spec.SingleRound.Unfolded.prover` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1080](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1080) — The overall prover for the `i`-th round of the sum-check protocol, where `i < n`. This is only well-

### `relation` (7 declarations, 6 files)

- `def ArkLib.Lattices.ModuleSIS.relation` [ArkLib/Data/Lattices/ModuleSIS.lean:85](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L85) — The kernel-form Module-SIS relation for a fixed matrix `A`: `z` is nonzero, short, and lies in the k
- `def Lookup.relation` [ArkLib/ProofSystem/ConstraintSystem/Lookup.lean:25](../../../ArkLib/ProofSystem/ConstraintSystem/Lookup.lean#L25) — The lookup relation. Takes in a collection of values and a table, both containers for elements of ty
- `def MemoryChecking.ReadOnly.relation` [ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean:128](../../../ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean#L128) — The read-only memory checking relation. It takes a memory `mem` and a list of read operations `ops`.
- `def MemoryChecking.ReadWrite.relation` [ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean:161](../../../ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean#L161) — The read-write memory checking relation. It takes an initial memory `startMem`, a final memory `fina
- `def Plonk.relation` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:161](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L161) — To define a relation based on the constraint system, we extend it with: - A natural number `ℓ ≤ m` r
- `def R1CS.relation` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:61](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L61) — The R1CS relation: `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where `*` is understood to mean component-wise 
- `abbrev Spartan.Spec.relation` [ArkLib/ProofSystem/Spartan/Basic.lean:152](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L152) — This unfolds to `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where `𝕫 = 𝕩 ‖ 𝕨`

### `inputRelation` (8 declarations, 5 files)

- `def BatchedFri.Spec.inputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/General.lean:41](../../../ArkLib/ProofSystem/BatchedFri/Spec/General.lean#L41) — (no docstring)
- `def BatchedFri.Spec.BatchingRound.inputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:56](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L56) — (no docstring)
- `def Fri.Spec.inputRelation` [ArkLib/ProofSystem/Fri/Spec/General.lean:37](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L37) — (no docstring)
- `def Fri.Spec.FoldPhase.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:269](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L269) — (no docstring)
- `def Fri.Spec.FinalFoldPhase.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:469](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L469) — (no docstring)
- `def Fri.Spec.QueryRound.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:646](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L646) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simpler.inputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:242](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L242) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.inputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:367](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L367) — (no docstring)

### `oracleVerifier_rbrKnowledgeSoundness` (7 declarations, 5 files)

- `theorem DoNothing.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/DoNothing.lean:98](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L98) — The `DoNothing` oracle verifier is perfectly round-by-round knowledge sound.
- `theorem RandomQuery.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/RandomQuery.lean:247](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L247) — The `RandomQuery` oracle reduction is round-by-round knowledge sound. The key fact governing the sou
- `theorem ReduceClaim.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:242](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L242) — The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness. Note that s
- `theorem Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:218](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L218) — Round-by-round knowledge soundness with error `deg / \|R\|` per challenge for the (full) sum-check pro
- `theorem Sumcheck.Spec.SingleRound.Simpler.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:338](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L338) — (no docstring)
- `theorem Sumcheck.Spec.SingleRound.Simple.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:776](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L776) — Round-by-round knowledge soundness for the oracle verifier
- `theorem Sumcheck.Spec.SingleRound.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:975](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L975) — Round-by-round knowledge soundness theorem for single-round of sum-check, obtained by transporting t

### `Witness` (5 declarations, 5 files)

- `def BatchedFri.Spec.Witness` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:48](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L48) — The Batched FRI protocol has as witness for each batched polynomial that is supposed to correspond t
- `structure Binius.BinaryBasefold.Witness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:568](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L568) — The round witness for round `i` of `t ∈ L[≤ 2][X Fin ℓ]` and `Hᵢ(Xᵢ, ..., Xₗ₋₁) := h(r₀', ..., rᵢ₋₁'
- `def R1CS.Witness` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:51](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L51) — (no docstring)
- `def Fri.Spec.Witness` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:107](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L107) — The FRI protocol has as witness the polynomial that is supposed to correspond to the codeword in the
- `abbrev Spartan.Spec.Witness` [ArkLib/ProofSystem/Spartan/Basic.lean:148](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L148) — This unfolds to `𝕨 : Fin 2 ^ ℓ_w → R`

### `outputRelation` (7 declarations, 4 files)

- `def BatchedFri.Spec.BatchingRound.outputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:65](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L65) — (no docstring)
- `def Fri.Spec.outputRelation` [ArkLib/ProofSystem/Fri/Spec/General.lean:47](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L47) — (no docstring)
- `def Fri.Spec.FoldPhase.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:278](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L278) — (no docstring)
- `def Fri.Spec.FinalFoldPhase.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:481](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L481) — (no docstring)
- `def Fri.Spec.QueryRound.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:654](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L654) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simpler.outputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:271](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L271) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.outputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:370](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L370) — (no docstring)

### `Statement` (4 declarations, 4 files)

- `structure Binius.BinaryBasefold.Statement` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:524](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L524) — Statement per iterated sumcheck round
- `def R1CS.Statement` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:45](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L45) — (no docstring)
- `def Fri.Spec.Statement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:77](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L77) — For the `i`-th round of the protocol, the input statement is equal to the challenges sent from round
- `abbrev Spartan.Spec.Statement` [ArkLib/ProofSystem/Spartan/Basic.lean:140](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L140) — This unfolds to `𝕩 : Fin (2 ^ ℓ_n - 2 ^ ℓ_w) → R`

### `disagreementSet` (4 declarations, 4 files)

- `def disagreementSet` [ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean:56](../../../ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean#L56) — The set D = Δ^{2m}(U, V), columns where U₀≠V₀ or U₁≠V₁.
- `def Binius.BinaryBasefold.disagreementSet` [ArkLib/ProofSystem/Binius/BinaryBasefold/Prelude.lean:1171](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Prelude.lean#L1171) — Disagreement set Δ : The set of points where two functions disagree. For functions f^(i+ϑ) and g^(i+
- `def Quotienting.disagreementSet` [ArkLib/ProofSystem/Stir/Quotienting.lean:52](../../../ArkLib/ProofSystem/Stir/Quotienting.lean#L52) — We define the set disagreementSet(f,ι,S,Ans) as the set of all points x ∈ ι that lie in S such that 
- `def BlockRelDistance.disagreementSet` [ArkLib/ProofSystem/Whir/BlockRelDistance.lean:97](../../../ArkLib/ProofSystem/Whir/BlockRelDistance.lean#L97) — Let C be a smooth ReedSolomon code `C = RS[F, ι^(2ⁱ), φ', m]` and `f,g : ι^(2ⁱ) → F`, then the (i,k)

### `reduction_completeness` (4 declarations, 4 files)

- `theorem CheckClaim.reduction_completeness` [ArkLib/ProofSystem/Component/CheckClaim.lean:70](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L70) — The `CheckClaim` reduction satisfies perfect completeness with respect to the predicate as the input
- `theorem NoInteraction.reduction_completeness` [ArkLib/ProofSystem/Component/NoInteraction.lean:69](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L69) — (no docstring)
- `theorem ReduceClaim.reduction_completeness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:66](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L66) — The `ReduceClaim` reduction satisfies perfect completeness for any relation.
- `theorem SendWitness.reduction_completeness` [ArkLib/ProofSystem/Component/SendWitness.lean:73](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L73) — The `SendWitness` reduction satisfies perfect completeness.

### `ratchet` (5 declarations, 3 files)

- `def DomainSeparator.ratchet` [ArkLib/Data/Hash/DomainSep.lean:221](../../../ArkLib/Data/Hash/DomainSep.lean#L221) — Ratchet the state. Rust interface: ```rust pub fn ratchet(self) -> Self ```
- `def DuplexSponge.ratchet` [ArkLib/Data/Hash/DuplexSponge.lean:612](../../../ArkLib/Data/Hash/DuplexSponge.lean#L612) — ### Ratchet the sponge state for domain separation Algorithm (from Rust implementation): 1. Permute 
- `def HashStateWithInstructions.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:141](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L141) — Perform a ratchet operation. Rust interface: ```rust pub fn ratchet(&mut self) -> Result<(), DomainS
- `def FSVerifierState.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:258](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L258) — Signal the end of statement with ratcheting. Rust interface: ```rust pub fn ratchet(&mut self) -> Re
- `def FSProverState.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:371](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L371) — Ratchet the protocol state. Rust interface: ```rust pub fn ratchet(&mut self) -> Result<(), DomainSe

### `Adversary` (4 declarations, 3 files)

- `def AGM.Adversary` [ArkLib/AGM/Basic.lean:149](../../../ArkLib/AGM/Basic.lean#L149) — An adversary in the Algebraic Group Model (AGM) is defined as follows: - It is given knowledge of th
- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.Adversary` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean:92](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean#L92) — A weak-binding adversary outputs two weak openings for the same commitment.
- `abbrev ArkLib.Lattices.SIS.Adversary` [ArkLib/Data/Lattices/ModuleSIS.lean:57](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L57) — A search adversary for a SIS-style problem.
- `abbrev ArkLib.Lattices.ModuleSIS.Adversary` [ArkLib/Data/Lattices/ModuleSIS.lean:100](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L100) — A Module-SIS adversary.

### `StmtIn` (4 declarations, 3 files)

- `def RandomQuery.StmtIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:30](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L30) — (no docstring)
- `def Sumcheck.Spec.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:137](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L137) — The input statement for the (full) sum-check protocol, which contains only the target sum value
- `def Sumcheck.Spec.SingleRound.Simpler.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:239](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L239) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:356](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L356) — (no docstring)

### `reduction_perfectCompleteness` (4 declarations, 3 files)

- `theorem DoNothing.reduction_perfectCompleteness` [ArkLib/ProofSystem/Component/DoNothing.lean:51](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L51) — The `DoNothing` reduction satisfies perfect completeness for any relation.
- `theorem Sumcheck.Spec.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:208](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L208) — Perfect completeness for the (full) sum-check protocol
- `theorem Sumcheck.Spec.SingleRound.Simple.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:543](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L543) — Perfect completeness for the (non-oracle) reduction
- `theorem Sumcheck.Spec.SingleRound.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:944](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L944) — (no docstring)

### `toFinset` (4 declarations, 3 files)

- `def ReedSolomon.toFinset` [ArkLib/Data/CodingTheory/ReedSolomon.lean:92](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L92) — (no docstring)
- `def Domain.CosetFftDomainClass.toFinset` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:287](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L287) — The elements of a domain as a finset.
- `abbrev Domain.CosetFftDomain.toFinset` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:306](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L306) — The finset of elements of a concrete coset FFT domain.
- `abbrev Domain.FftDomain.toFinset` [ArkLib/Data/Domain/FftDomain/Defs.lean:150](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L150) — The finite set of field elements contained in an FFT domain.

### `verifier_rbrKnowledgeSoundness` (4 declarations, 3 files)

- `theorem DoNothing.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/DoNothing.lean:57](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L57) — The `DoNothing` verifier is perfectly round-by-round knowledge sound.
- `theorem ReduceClaim.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:148](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L148) — The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness. Note that s
- `theorem Sumcheck.Spec.SingleRound.Simple.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:770](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L770) — Round-by-round knowledge soundness for the verifier
- `theorem Sumcheck.Spec.SingleRound.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:952](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L952) — (no docstring)

### `Message` (3 declarations, 3 files)

- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.Message` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:122](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L122) — Messages: block vectors over the message row space.
- `abbrev ArkLib.Lattices.Ajtai.Simple.Message` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:32](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L32) — Messages: column vectors over `Rq Φ`.
- `def ProtocolSpec.Message` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:66](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L66) — The type of the `i`-th message in a protocol specification. This does not distinguish between messag

### `Opening` (3 declarations, 3 files)

- `structure Commitment.Opening` [ArkLib/Commitments/Functional/Basic.lean:59](../../../ArkLib/Commitments/Functional/Basic.lean#L59) — The opening protocol used to prove a claimed oracle response for committed data.
- `structure ArkLib.Lattices.Ajtai.InnerOuter.Opening` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:98](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L98) — A Hachi/Greyhound *weak opening* `(sᵢ, t̂ᵢ, cᵢ)ᵢ`: the decomposition data `(sᵢ, t̂ᵢ)` (`Decomp`) ext
- `abbrev ArkLib.Lattices.Ajtai.Simple.Opening` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:43](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L43) — The simple Ajtai commitment has no auxiliary opening data.

### `Params` (3 declarations, 3 files)

- `structure Poseidon2.Params` [ArkLib/Data/Hash/Poseidon2.lean:412](../../../ArkLib/Data/Hash/Poseidon2.lean#L412) — The parameters determining a Poseidon2 permutation (over the KoalaBear field)
- `structure StirIOP.Params` [ArkLib/ProofSystem/Stir/MainThm.lean:32](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L32) — **Per‑round protocol parameters:** For a fixed depth `M`, the reduction runs `M + 1` rounds. In roun
- `structure WhirIOP.Params` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:54](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L54) — ** Per‑round protocol parameters. ** For a fixed depth `M`, the reduction runs `M + 1` rounds. In ro

### `PublicParams` (3 declarations, 3 files)

- `structure ArkLib.Lattices.Ajtai.InnerOuter.PublicParams` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:77](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L77) — Public parameters: inner Ajtai matrix `A` and outer Ajtai matrix `B`.
- `abbrev ArkLib.Lattices.Ajtai.Simple.PublicParams` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:29](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L29) — Public parameters: the Ajtai matrix `A`.
- `structure Spartan.PublicParams` [ArkLib/ProofSystem/Spartan/Basic.lean:110](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L110) — The public parameters of the (padded) Spartan protocol. Consists of the number of bits of the R1CS d

### `absorb` (3 declarations, 3 files)

- `def DomainSeparator.absorb` [ArkLib/Data/Hash/DomainSep.lean:182](../../../ArkLib/Data/Hash/DomainSep.lean#L182) — Absorb `count` native elements. Rust interface: ```rust pub fn absorb(self, count: usize, label: &st
- `def DuplexSponge.absorb` [ArkLib/Data/Hash/DuplexSponge.lean:416](../../../ArkLib/Data/Hash/DuplexSponge.lean#L416) — ### Absorb a list of units into the sponge (paper version) Paper algorithm (process one element at a
- `def HashStateWithInstructions.absorb` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:105](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L105) — Perform secure absorption of elements into the sponge. Rust interface: ```rust pub fn absorb(&mut se

### `commit` (3 declarations, 3 files)

- `def KZG.commit` [ArkLib/Commitments/Functional/KZG/Basic.lean:55](../../../ArkLib/Commitments/Functional/KZG/Basic.lean#L55) — To commit to an `n + 1`-tuple of coefficients `coeffs` (corresponding to a polynomial of maximum deg
- `def ArkLib.Lattices.Ajtai.Simple.commit` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:38](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L38) — Deterministically commit by multiplying the public matrix by the message vector.
- `def SimpleRO.commit` [ArkLib/Commitments/Ordinary/SimpleRO.lean:41](../../../ArkLib/Commitments/Ordinary/SimpleRO.lean#L41) — Commit to message `v` under the random oracle `ro` and randomness `r` by hashing `(v, r)`.

### `commitmentScheme` (3 declarations, 3 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.commitmentScheme` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:200](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L200) — The inner-outer Ajtai commitment as a `CommitmentScheme`, verified with the Hachi/Greyhound weak ver
- `def ArkLib.Lattices.Ajtai.Simple.commitmentScheme` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:56](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L56) — The simple Ajtai commitment as a `CommitmentScheme`. An opening is accepted only when the message sa
- `def SimpleRO.commitmentScheme` [ArkLib/Commitments/Ordinary/SimpleRO.lean:51](../../../ArkLib/Commitments/Ordinary/SimpleRO.lean#L51) — The simple random-oracle commitment as an (ordinary) `CommitmentScheme`. Setup samples a uniformly r

### `coreInteractionOracleReduction` (3 declarations, 3 files)

- `def coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:619](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L619) — The final oracle reduction that composes sumcheckFold with finalSumcheckStep
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:623](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L623) — The final oracle reduction that composes sumcheckFold with finalSumcheckStep
- `def Binius.RingSwitching.SumcheckPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:578](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L578) — Large-field reduction: Sumcheck seqCompose, then append FinalSum

### `coreInteractionOracleVerifier` (3 declarations, 3 files)

- `def coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:604](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L604) — The final oracle verifier that composes sumcheckFold with finalSumcheckStep
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:605](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L605) — The final oracle verifier that composes sumcheckFold with finalSumcheckStep
- `def Binius.RingSwitching.SumcheckPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:569](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L569) — Large-field reduction verifier: Sumcheck seqCompose, then append FinalSum

### `finalSumcheckKStateProp` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKStateProp` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:968](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L968) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKStateProp` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:522](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L522) — (no docstring)
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckKStateProp` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:476](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L476) — (no docstring)

### `finalSumcheckKnowledgeStateFunction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1002](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1002) — The knowledge state function for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:564](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L564) — The knowledge state function for the final sumcheck step
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:506](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L506) — The knowledge state function for the final sumcheck step

### `finalSumcheckOracleReduction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:897](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L897) — The oracle reduction for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:445](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L445) — The oracle reduction for the final sumcheck step
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:424](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L424) — The oracle reduction for the final sumcheck step

### `finalSumcheckOracleReduction_perfectCompleteness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:911](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L911) — Perfect completeness for the final sumcheck step
- `theorem Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:461](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L461) — Perfect completeness for the final sumcheck step
- `theorem Binius.RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:438](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L438) — Perfect completeness for the final sumcheck step

### `finalSumcheckOracleVerifier_rbrKnowledgeSoundness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1022](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1022) — Round-by-round knowledge soundness for the final sumcheck step
- `theorem Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:585](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L585) — Round-by-round knowledge soundness for the final sumcheck step
- `theorem Binius.RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:525](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L525) — Round-by-round knowledge soundness for the final sumcheck step

### `finalSumcheckProver` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckProver` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:811](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L811) — The prover for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckProver` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:348](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L348) — The prover for the final sumcheck step
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckProver` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:349](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L349) — The prover for the final sumcheck step

### `finalSumcheckRbrExtractor` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:938](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L938) — The round-by-round extractor for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:490](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L490) — The round-by-round extractor for the final sumcheck step
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:456](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L456) — The round-by-round extractor for the final sumcheck step

### `finalSumcheckVerifier` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:853](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L853) — The verifier for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:392](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L392) — The verifier for the final sumcheck step
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:385](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L385) — The verifier for the final sumcheck step

### `fullOracleProof` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:96](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L96) — The full Binary Basefold protocol as a Proof
- `def Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:160](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L160) — The full Binary Basefold protocol as a Proof
- `def Binius.RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:81](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L81) — The full Binary Basefold protocol as a Proof

### `fullOracleReduction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:68](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L68) — The reduction for the full Binary Basefold protocol
- `def Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:131](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L131) — The reduction for the full Binary Basefold protocol
- `def Binius.RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:69](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L69) — The reduction for the full Binary Basefold protocol

### `fullOracleReduction_perfectCompleteness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:111](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L111) — Perfect completeness for the full Binary Basefold protocol (reduction)
- `theorem Binius.FRIBinius.FullFRIBinius.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:175](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L175) — Perfect completeness for the full Binary Basefold protocol (reduction)
- `theorem Binius.RingSwitching.FullRingSwitching.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:119](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L119) — (no docstring)

### `fullOracleVerifier` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:45](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L45) — The oracle verifier for the full Binary Basefold protocol
- `def Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:108](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L108) — The oracle verifier for the full Binary Basefold protocol
- `def Binius.RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:52](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L52) — The oracle verifier for the full Binary Basefold protocol

### `oracleReduction_completeness` (3 declarations, 3 files)

- `theorem RandomQuery.oracleReduction_completeness` [ArkLib/ProofSystem/Component/RandomQuery.lean:114](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L114) — The `RandomQuery` oracle reduction is perfectly complete.
- `theorem ReduceClaim.oracleReduction_completeness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:195](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L195) — The `ReduceClaim` oracle reduction satisfies perfect completeness for any relation.
- `theorem SendSingleWitness.oracleReduction_completeness` [ArkLib/ProofSystem/Component/SendWitness.lean:264](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L264) — The `SendSingleWitness` oracle reduction satisfies perfect completeness.

### `relOut` (3 declarations, 3 files)

- `def CheckClaim.relOut` [ArkLib/ProofSystem/Component/CheckClaim.lean:63](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L63) — (no docstring)
- `def RandomQuery.relOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:49](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L49) — The output relation states that if the verifier's single query was `q`, then `a` and `b` agree on th
- `def SendClaim.relOut` [ArkLib/ProofSystem/Component/SendClaim.lean:98](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L98) — (no docstring)

### `squeeze` (3 declarations, 3 files)

- `def DomainSeparator.squeeze` [ArkLib/Data/Hash/DomainSep.lean:207](../../../ArkLib/Data/Hash/DomainSep.lean#L207) — Squeeze `count` native elements. Rust interface: ```rust pub fn squeeze(self, count: usize, label: &
- `def DuplexSponge.squeeze` [ArkLib/Data/Hash/DuplexSponge.lean:512](../../../ArkLib/Data/Hash/DuplexSponge.lean#L512) — ### Squeeze out a vector of units from the sponge (paper version) We differ from the paper version i
- `def HashStateWithInstructions.squeeze` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:117](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L117) — Perform a secure squeeze operation. Rust interface: ```rust pub fn squeeze(&mut self, output: &mut [

### `cast_id` (9 declarations, 2 files)

- `theorem Prover.cast_id` [ArkLib/OracleReduction/Cast.lean:53](../../../ArkLib/OracleReduction/Cast.lean#L53) — (no docstring)
- `theorem OracleProver.cast_id` [ArkLib/OracleReduction/Cast.lean:77](../../../ArkLib/OracleReduction/Cast.lean#L77) — (no docstring)
- `theorem Verifier.cast_id` [ArkLib/OracleReduction/Cast.lean:99](../../../ArkLib/OracleReduction/Cast.lean#L99) — (no docstring)
- `theorem Reduction.cast_id` [ArkLib/OracleReduction/Cast.lean:173](../../../ArkLib/OracleReduction/Cast.lean#L173) — (no docstring)
- `theorem ProtocolSpec.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:36](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L36) — (no docstring)
- `theorem ProtocolSpec.MessageIdx.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:80](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L80) — (no docstring)
- `theorem ProtocolSpec.ChallengeIdx.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:124](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L124) — (no docstring)
- `theorem ProtocolSpec.Transcript.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:168](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L168) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:198](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L198) — (no docstring)

### `seqCompose` (8 declarations, 2 files)

- `def Prover.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:37](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L37) — Sequential composition of provers, defined via iteration of the composition (append) of two provers.
- `def Verifier.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:75](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L75) — Sequential composition of verifiers, defined via iteration of the composition (append) of two verifi
- `def Reduction.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:104](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L104) — Sequential composition of reductions, defined via sequential composition of provers and verifiers (o
- `def OracleProver.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:135](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L135) — Sequential composition of provers in oracle reductions, defined via sequential composition of prover
- `def OracleVerifier.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:182](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L182) — Sequential composition of oracle verifiers (in oracle reductions), defined via iteration of the comp
- `def OracleReduction.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:247](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L247) — Sequential composition of oracle reductions, defined via sequential composition of oracle provers an
- `def ProtocolSpec.seqCompose` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:276](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L276) — Sequential composition of a family of `ProtocolSpec`s, indexed by `i : Fin m`. Defined for definitio
- `def ProtocolSpec.FullTranscript.seqCompose` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:334](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L334) — Sequential composition of a family of `FullTranscript`s, indexed by `i : Fin m`. Defined for definit

### `seqCompose_zero` (7 declarations, 2 files)

- `lemma Prover.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:48](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L48) — (no docstring)
- `lemma Verifier.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:83](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L83) — (no docstring)
- `lemma Reduction.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:113](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L113) — (no docstring)
- `lemma OracleVerifier.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:196](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L196) — (no docstring)
- `lemma OracleReduction.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:263](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L263) — (no docstring)
- `theorem ProtocolSpec.seqCompose_zero` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:292](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L292) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.seqCompose_zero` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:339](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L339) — (no docstring)

### `completeness` (5 declarations, 2 files)

- `def Reduction.completeness` [ArkLib/OracleReduction/Security/Basic.lean:86](../../../ArkLib/OracleReduction/Security/Basic.lean#L86) — A reduction satisfies **completeness** with regards to: - an initialization function `init : ProbCom
- `def OracleReduction.completeness` [ArkLib/OracleReduction/Security/Basic.lean:384](../../../ArkLib/OracleReduction/Security/Basic.lean#L384) — Completeness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.completeness` [ArkLib/OracleReduction/Security/Basic.lean:438](../../../ArkLib/OracleReduction/Security/Basic.lean#L438) — (no docstring)
- `def OracleProof.completeness` [ArkLib/OracleReduction/Security/Basic.lean:467](../../../ArkLib/OracleReduction/Security/Basic.lean#L467) — Completeness of an oracle reduction is the same as for non-oracle reductions.
- `theorem SendClaim.completeness` [ArkLib/ProofSystem/Component/SendClaim.lean:110](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L110) — (no docstring)

### `concat` (5 declarations, 2 files)

- `def ProtocolSpec.MessagesUpTo.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:403](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L403) — Concatenate the `k`-th message to the end of the tuple of messages up to round `k`, assuming round `
- `def ProtocolSpec.ChallengesUpTo.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:462](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L462) — Concatenate the `k`-th challenge to the end of the tuple of challenges up to round `k`, assuming rou
- `abbrev ProtocolSpec.Transcript.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:515](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L515) — Concatenate a message to the end of a partial transcript. This is definitionally equivalent to `Fin.
- `abbrev ProtocolSpec.concat` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:31](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L31) — Concatenate a round with direction `dir` and type `Message` to the end of a `ProtocolSpec`
- `def ProtocolSpec.FullTranscript.concat` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:149](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L149) — Adding a message with a given direction and type to the end of a `Transcript`

### `knowledgeSoundness` (5 declarations, 2 files)

- `def Verifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:289](../../../ArkLib/OracleReduction/Security/Basic.lean#L289) — A reduction satisfies **(straightline) knowledge soundness** with error `knowledgeError ≥ 0` and wit
- `def OracleVerifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:413](../../../ArkLib/OracleReduction/Security/Basic.lean#L413) — Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:454](../../../ArkLib/OracleReduction/Security/Basic.lean#L454) — (no docstring)
- `def OracleProof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:492](../../../ArkLib/OracleReduction/Security/Basic.lean#L492) — Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Verifier.StateRestoration.knowledgeSoundness` [ArkLib/OracleReduction/Security/StateRestoration.lean:151](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L151) — State-restoration knowledge soundness (w/ straightline extractor). The state-restoration extractor r

### `new` (5 declarations, 2 files)

- `def DomainSeparator.Op.new` [ArkLib/Data/Hash/DomainSep.lean:138](../../../ArkLib/Data/Hash/DomainSep.lean#L138) — Construct a new `Op` from a character `id` and a count number `count : Option Nat`. Returns error if
- `def DomainSeparator.new` [ArkLib/Data/Hash/DomainSep.lean:159](../../../ArkLib/Data/Hash/DomainSep.lean#L159) — Create a new DomainSeparator with the domain separator. Rust interface: ```rust pub fn new(session_i
- `def HashStateWithInstructions.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:93](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L93) — Initialize a stateful hash object from a domain separator. Rust interface: ```rust pub fn new(domain
- `def FSVerifierState.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:183](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L183) — Create a new VerifierState from a domain separator and NARG string. Rust interface: ```rust pub fn n
- `def FSProverState.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:326](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L326) — Create a new `FSProverState` from a domain separator and RNG. Rust interface: ```rust pub fn new(dom

### `soundness` (5 declarations, 2 files)

- `def Verifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:242](../../../ArkLib/OracleReduction/Security/Basic.lean#L242) — A reduction satisfies **soundness** with error `soundnessError ≥ 0` and with respect to input langua
- `def OracleVerifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:405](../../../ArkLib/OracleReduction/Security/Basic.lean#L405) — Soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:448](../../../ArkLib/OracleReduction/Security/Basic.lean#L448) — (no docstring)
- `def OracleProof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:484](../../../ArkLib/OracleReduction/Security/Basic.lean#L484) — Soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Verifier.StateRestoration.soundness` [ArkLib/OracleReduction/Security/StateRestoration.lean:130](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L130) — State-restoration soundness

### `cast_eq_dcast₂` (4 declarations, 2 files)

- `theorem Verifier.cast_eq_dcast₂` [ArkLib/OracleReduction/Cast.lean:107](../../../ArkLib/OracleReduction/Cast.lean#L107) — (no docstring)
- `theorem ProtocolSpec.MessageIdx.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:92](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L92) — (no docstring)
- `theorem ProtocolSpec.ChallengeIdx.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:136](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L136) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:204](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L204) — (no docstring)

### `instDCast₂` (4 declarations, 2 files)

- `instance Prover.instDCast₂` [ArkLib/OracleReduction/Cast.lean:60](../../../ArkLib/OracleReduction/Cast.lean#L60) — (no docstring)
- `instance ProtocolSpec.MessageIdx.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:88](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L88) — (no docstring)
- `instance ProtocolSpec.ChallengeIdx.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:132](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L132) — (no docstring)
- `instance ProtocolSpec.FullTranscript.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:200](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L200) — (no docstring)

### `oracleReduction_perfectCompleteness` (4 declarations, 2 files)

- `theorem DoNothing.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Component/DoNothing.lean:92](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L92) — The `DoNothing` oracle reduction satisfies perfect completeness for any relation.
- `theorem Sumcheck.Spec.SingleRound.Simpler.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:312](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L312) — (no docstring)
- `theorem Sumcheck.Spec.SingleRound.Simple.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:762](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L762) — Perfect completeness for the oracle reduction
- `theorem Sumcheck.Spec.SingleRound.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:962](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L962) — Completeness theorem for single-round of sum-check, obtained by transporting the completeness proof 

### `subdomain` (4 declarations, 2 files)

- `def Domain.CosetFftDomainClass.subdomain` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:112](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L112) — Given a smooth coset FFT domain `ω` of log-order `n`, return its subdomain of log-order `n - i`. The
- `abbrev Domain.CosetFftDomain.subdomain` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:467](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L467) — Concrete notation for taking the `i`th subdomain of a smooth coset FFT domain.
- `def Domain.FftDomainClass.subdomain` [ArkLib/Data/Domain/FftDomain/Subdomain.lean:60](../../../ArkLib/Data/Domain/FftDomain/Subdomain.lean#L60) — The `i`th subdomain of a smooth FFT domain, obtained by taking the corresponding coset subdomain and
- `abbrev Domain.FftDomain.subdomain` [ArkLib/Data/Domain/FftDomain/Subdomain.lean:164](../../../ArkLib/Data/Domain/FftDomain/Subdomain.lean#L164) — Concrete notation for the `i`th subdomain of a smooth FFT domain.

### `OStmtIn` (3 declarations, 2 files)

- `def RandomQuery.OStmtIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:33](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L33) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simpler.OStmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:240](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L240) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.OStmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:362](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L362) — (no docstring)

### `OStmtOut` (3 declarations, 2 files)

- `def RandomQuery.OStmtOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:34](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L34) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simpler.OStmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:269](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L269) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.OStmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:365](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L365) — (no docstring)

### `StmtOut` (3 declarations, 2 files)

- `def RandomQuery.StmtOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:31](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L31) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simpler.StmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:268](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L268) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.StmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:359](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L359) — (no docstring)

### `advantage` (3 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.advantage` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean:409](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean#L409) — Weak-binding advantage.
- `def ArkLib.Lattices.SIS.advantage` [ArkLib/Data/Lattices/ModuleSIS.lean:66](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L66) — Search advantage for a SIS-style problem.
- `def ArkLib.Lattices.ModuleSIS.advantage` [ArkLib/Data/Lattices/ModuleSIS.lean:112](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L112) — The Module-SIS advantage.

### `correctness` (3 declarations, 2 files)

- `def Commitment.correctness` [ArkLib/Commitments/Functional/Basic.lean:88](../../../ArkLib/Commitments/Functional/Basic.lean#L88) — A commitment scheme satisfies **correctness** with error `correctnessError` if for all `data : Data`
- `theorem KZG.correctness` [ArkLib/Commitments/Functional/KZG/Correctness.lean:51](../../../ArkLib/Commitments/Functional/KZG/Correctness.lean#L51) — Algebraic correctness of one KZG opening for a coefficient vector.
- `theorem KZG.CommitmentScheme.correctness` [ArkLib/Commitments/Functional/KZG/Correctness.lean:161](../../../ArkLib/Commitments/Functional/KZG/Correctness.lean#L161) — The KZG scheme satisfies perfect correctness as defined in `CommitmentScheme`.

### `drop` (3 declarations, 2 files)

- `def Fin.drop` [ArkLib/Data/Fin/Tuple/Defs.lean:60](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L60) — Drop the first `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple.
- `def ProtocolSpec.drop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:117](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L117) — Drop the first `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.drop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:174](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L174) — (no docstring)

### `experiment` (3 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.experiment` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean:396](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean#L396) — The Hachi/Greyhound weak-binding experiment. ## Ordinary vs. weak binding *Ordinary (exact) binding*
- `def ArkLib.Lattices.SIS.experiment` [ArkLib/Data/Lattices/ModuleSIS.lean:60](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L60) — The SIS experiment: sample a challenge, run the adversary, check validity.
- `def ArkLib.Lattices.ModuleSIS.experiment` [ArkLib/Data/Lattices/ModuleSIS.lean:106](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L106) — The Module-SIS experiment.

### `extract` (3 declarations, 2 files)

- `def Fin.extract` [ArkLib/Data/Fin/Tuple/Defs.lean:73](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L73) — Extract a sub-tuple from a `Fin`-tuple, from index `start` to `stop - 1`.
- `def ProtocolSpec.extract` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:125](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L125) — Extract the slice of the rounds of a `ProtocolSpec n` from `start` to `stop - 1`.
- `abbrev ProtocolSpec.FullTranscript.extract` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:182](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L182) — (no docstring)

### `mem_toFinset_iff_mem` (3 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.mem_toFinset_iff_mem` [ArkLib/Data/Domain/CosetFftDomain/Mem.lean:90](../../../ArkLib/Data/Domain/CosetFftDomain/Mem.lean#L90) — Membership in the finset of elements is the same as membership in the coset FFT domain.
- `lemma Domain.CosetFftDomain.mem_toFinset_iff_mem` [ArkLib/Data/Domain/CosetFftDomain/Mem.lean:143](../../../ArkLib/Data/Domain/CosetFftDomain/Mem.lean#L143) — Membership in the finset of elements is the same as membership in the concrete coset FFT domain.
- `lemma Domain.FftDomain.mem_toFinset_iff_mem` [ArkLib/Data/Domain/FftDomain/Mem.lean:85](../../../ArkLib/Data/Domain/FftDomain/Mem.lean#L85) — Membership in the finset of elements is the same as membership in the FFT domain.

### `rdrop` (3 declarations, 2 files)

- `abbrev Fin.rdrop` [ArkLib/Data/Fin/Tuple/Defs.lean:68](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L68) — Drop the last `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple. This is defi
- `def ProtocolSpec.rdrop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:121](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L121) — Drop the last `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.rdrop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:178](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L178) — (no docstring)

### `rtake` (3 declarations, 2 files)

- `def Fin.rtake` [ArkLib/Data/Fin/Tuple/Defs.lean:55](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L55) — Take the last `m` elements of a finite vector
- `def ProtocolSpec.rtake` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:113](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L113) — Take the last `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.rtake` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:170](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L170) — Take the last `m ≤ n` rounds of a (full) transcript for a protocol specification `pSpec`

### `ChallengeIdx` (2 declarations, 2 files)

- `def ProtocolSpec.ChallengeIdx` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:54](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L54) — Subtype of `Fin n` for the indices corresponding to challenges in a protocol specification
- `def ProtocolSpec.VectorSpec.ChallengeIdx` [ArkLib/OracleReduction/VectorIOR.lean:54](../../../ArkLib/OracleReduction/VectorIOR.lean#L54) — The type of indices for challenges in a `VectorSpec`.

### `Commitment` (2 declarations, 2 files)

- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.Commitment` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:126](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L126) — Inner-outer commitments live in the outer row space.
- `abbrev ArkLib.Lattices.Ajtai.Simple.Commitment` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:35](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L35) — Commitments: row vectors over `Rq Φ`.

### `FinalSumcheckWit` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.FinalSumcheckWit` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:932](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L932) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.FinalSumcheckWit` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:484](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L484) — (no docstring)

### `GenMutualCorrParams` (2 declarations, 2 files)

- `class Fold.GenMutualCorrParams` [ArkLib/ProofSystem/Whir/Folding.lean:165](../../../ArkLib/ProofSystem/Whir/Folding.lean#L165) — The `GenMutualCorrParams` class captures the necessary parameters and assumptions to model a sequenc
- `class WhirIOP.GenMutualCorrParams` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:85](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L85) — `GenMutualCorrParams` binds together a set of smooth ReedSolomon codes `C_{i : M + 1, j : foldingPar

### `MessageIdx` (2 declarations, 2 files)

- `def ProtocolSpec.MessageIdx` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:49](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L49) — Subtype of `Fin n` for the indices corresponding to messages in a protocol specification
- `def ProtocolSpec.VectorSpec.MessageIdx` [ArkLib/OracleReduction/VectorIOR.lean:50](../../../ArkLib/OracleReduction/VectorIOR.lean#L50) — The type of indices for messages in a `VectorSpec`.

### `ParamConditions` (2 declarations, 2 files)

- `structure StirIOP.ParamConditions` [ArkLib/ProofSystem/Stir/MainThm.lean:52](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L52) — **Conditions that protocol parameters must satisfy.** - `h_deg` : initial degree `deg` is a power of
- `structure WhirIOP.ParamConditions` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:66](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L66) — ** Conditions that protocol parameters must satisfy. ** h_m : m = varCount₀ h_sumkLt : ∑ i : Fin (M 

### `append_left_injective` (2 declarations, 2 files)

- `theorem Fin.append_left_injective` [ArkLib/Data/Fin/Basic.lean:238](../../../ArkLib/Data/Fin/Basic.lean#L238) — (no docstring)
- `theorem ProtocolSpec.append_left_injective` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:55](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L55) — (no docstring)

### `append_right_injective` (2 declarations, 2 files)

- `theorem Fin.append_right_injective` [ArkLib/Data/Fin/Basic.lean:246](../../../ArkLib/Data/Fin/Basic.lean#L246) — (no docstring)
- `theorem ProtocolSpec.append_right_injective` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:65](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L65) — (no docstring)

### `batchingCoreReduction` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.batchingCoreReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:91](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L91) — (no docstring)
- `def Binius.RingSwitching.FullRingSwitching.batchingCoreReduction` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:59](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L59) — (no docstring)

### `batchingCoreVerifier` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.batchingCoreVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:77](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L77) — (no docstring)
- `def Binius.RingSwitching.FullRingSwitching.batchingCoreVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:43](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L43) — (no docstring)

### `binding` (2 declarations, 2 files)

- `def Commitment.binding` [ArkLib/Commitments/Functional/Basic.lean:170](../../../ArkLib/Commitments/Functional/Basic.lean#L170) — A commitment scheme satisfies **(evaluation) binding** with error `bindingError` if for all adversar
- `theorem KZG.CommitmentScheme.binding` [ArkLib/Commitments/Functional/KZG/Binding.lean:737](../../../ArkLib/Commitments/Functional/KZG/Binding.lean#L737) — The KZG scheme satisfies evaluation binding provided `t`-SDH holds.

### `coeffHom` (2 declarations, 2 files)

- `def ArkLib.Lattices.CyclotomicModulus.Rq.coeffHom` [ArkLib/Data/Lattices/CyclotomicRing/Rq.lean:175](../../../ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L175) — Reading off the `k`-th coefficient of the underlying polynomial, as an additive homomorphism `Rq Φ →
- `def CompPoly.CPolynomial.coeffHom` [ArkLib/ToCompPoly/Univariate/Basic.lean:282](../../../ArkLib/ToCompPoly/Univariate/Basic.lean#L282) — Extracting the `k`-th coefficient as an additive homomorphism.

### `coeffHom_apply` (2 declarations, 2 files)

- `theorem ArkLib.Lattices.CyclotomicModulus.Rq.coeffHom_apply` [ArkLib/Data/Lattices/CyclotomicRing/Rq.lean:180](../../../ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L180) — (no docstring)
- `theorem CompPoly.CPolynomial.coeffHom_apply` [ArkLib/ToCompPoly/Univariate/Basic.lean:288](../../../ArkLib/ToCompPoly/Univariate/Basic.lean#L288) — (no docstring)

### `coreInteractionOracleRbrKnowledgeError` (2 declarations, 2 files)

- `def coreInteractionOracleRbrKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:656](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L656) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:669](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L669) — (no docstring)

### `coreInteractionOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:638](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L638) — Perfect completeness for the core interaction oracle reduction
- `theorem Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:645](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L645) — Perfect completeness for the core interaction oracle reduction

### `coreInteractionOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:664](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L664) — Round-by-round knowledge soundness for the core interaction oracle verifier
- `theorem Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:678](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L678) — Round-by-round knowledge soundness for the core interaction oracle verifier

### `decoder` (2 declarations, 2 files)

- `def BerlekampWelch.decoder` [ArkLib/Data/CodingTheory/BerlekampWelch/BerlekampWelch.lean:52](../../../ArkLib/Data/CodingTheory/BerlekampWelch/BerlekampWelch.lean#L52) — Berlekamp-Welch decoder for Reed-Solomon codes. Given received codeword evaluations with potential e
- `def GuruswamiSudan.decoder` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:98](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L98) — Guruswami-Sudan decoder.  Returns all roots of the GS interpolation polynomial whose evaluation is w

### `domain_implies_char_ne_2` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:123](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L123) — The existence of a nontrivial smooth coset FFT domain rules out characteristic `2`.
- `lemma Domain.FftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/FftDomain/Ops.lean:161](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L161) — The existence of a nontrivial smooth FFT domain rules out characteristic `2`.

### `finalSumcheckKnowledgeError` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:927](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L927) — RBR knowledge error for the final sumcheck step
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:479](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L479) — RBR knowledge error for the final sumcheck step

### `foldOracleReduction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.foldOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:198](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L198) — The oracle reduction that is the `i`-th round of Binary Foldfold.
- `def Fri.Spec.FoldPhase.foldOracleReduction` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:413](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L413) — The oracle reduction that is the `i`-th round of the FRI protocol.

### `fullOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:151](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L151) — Round-by-round knowledge soundness for the full Binary Basefold oracle verifier
- `theorem Binius.RingSwitching.FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:145](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L145) — Round-by-round knowledge soundness for the full ring-switching oracle verifier

### `fullPspec` (2 declarations, 2 files)

- `def Binius.FRIBinius.FullFRIBinius.fullPspec` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:54](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L54) — (no docstring)
- `def Binius.RingSwitching.fullPspec` [ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean:51](../../../ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean#L51) — (no docstring)

### `fullRbrKnowledgeError` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullRbrKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:141](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L141) — Combined RBR knowledge soundness error for the full protocol
- `def Binius.RingSwitching.FullRingSwitching.fullRbrKnowledgeError` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:137](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L137) — (no docstring)

### `guruswami_sudan_for_proximity_gap_existence` (2 declarations, 2 files)

- `lemma GuruswamiSudan.guruswami_sudan_for_proximity_gap_existence` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:889](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L889) — Constructive witness extraction for the Guruswami–Sudan system. When the computable `hasWitnessC` ch
- `lemma ProximityGap.guruswami_sudan_for_proximity_gap_existence` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:37](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L37) — The first part of Lemma 5.3 from [BCIKS20]. Given `D_X` (`proximity_gap_degree_bound`) and `δ₀` (`pr

### `guruswami_sudan_for_proximity_gap_property` (2 declarations, 2 files)

- `lemma GuruswamiSudan.guruswami_sudan_for_proximity_gap_property` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:928](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L928) — Constructive witness property for the Guruswami–Sudan system. When `m > 0` and the codeword polynomi
- `lemma ProximityGap.guruswami_sudan_for_proximity_gap_property` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:49](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L49) — The second part of Lemma 5.3 from [BCIKS20]. For any solution `Q` of the Guruswami-Sudan system, and

### `hint` (2 declarations, 2 files)

- `def DomainSeparator.hint` [ArkLib/Data/Hash/DomainSep.lean:196](../../../ArkLib/Data/Hash/DomainSep.lean#L196) — Hint `count` native elements. Rust interface: ```rust pub fn hint(self, label: &str) -> Self ```
- `def HashStateWithInstructions.hint` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:129](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L129) — Process a hint operation. Rust interface: ```rust pub fn hint(&mut self) -> Result<(), DomainSeparat

### `injOn` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomain.injOn` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:276](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L276) — A concrete coset FFT domain is injective on every set.
- `lemma Domain.FftDomain.injOn` [ArkLib/Data/Domain/FftDomain/Defs.lean:138](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L138) — An FFT domain is injective on every set.

### `injective` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomain.injective` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:270](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L270) — A concrete coset FFT domain is injective as a function.
- `lemma Domain.FftDomain.injective` [ArkLib/Data/Domain/FftDomain/Defs.lean:133](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L133) — An FFT domain is injective as a function.

### `knowledgeStateFunction` (2 declarations, 2 files)

- `def RandomQuery.knowledgeStateFunction` [ArkLib/ProofSystem/Component/RandomQuery.lean:219](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L219) — The knowledge state function for the `RandomQuery` oracle reduction.
- `def ReduceClaim.knowledgeStateFunction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:134](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L134) — The knowledge state function for the `ReduceClaim` reduction.

### `leftpad` (2 declarations, 2 files)

- `def Fin.leftpad` [ArkLib/Data/Fin/Tuple/Defs.lean:96](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L96) — Pad a `Fin`-indexed vector on the left with an element `a`. This becomes truncation if `n < m`.
- `def Matrix.leftpad` [ArkLib/Data/Matrix/Basic.lean:25](../../../ArkLib/Data/Matrix/Basic.lean#L25) — (no docstring)

### `liftContext_completeness` (2 declarations, 2 files)

- `theorem OracleReduction.liftContext_completeness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:118](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L118) — (no docstring)
- `theorem Reduction.liftContext_completeness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:350](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L350) — Lifting the reduction preserves completeness, assuming the lens satisfies its completeness condition

### `liftContext_knowledgeSoundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:155](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L155) — (no docstring)
- `theorem Verifier.liftContext_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:440](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L440) — (no docstring)

### `liftContext_perfectCompleteness` (2 declarations, 2 files)

- `theorem OracleReduction.liftContext_perfectCompleteness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:125](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L125) — (no docstring)
- `theorem Reduction.liftContext_perfectCompleteness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:374](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L374) — (no docstring)

### `liftContext_rbr_knowledgeSoundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_rbr_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:186](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L186) — (no docstring)
- `theorem Verifier.liftContext_rbr_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:523](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L523) — (no docstring)

### `liftContext_rbr_soundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_rbr_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:172](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L172) — (no docstring)
- `theorem Verifier.liftContext_rbr_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:489](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L489) — (no docstring)

### `liftContext_soundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:142](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L142) — Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions
- `theorem Verifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:396](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L396) — Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions

### `masterKStateProp` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.masterKStateProp` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:982](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L982) — Before V's challenge of the `i-th` foldStep, we ignore the bad-folding-event of the `i-th` oracle if
- `def Binius.RingSwitching.masterKStateProp` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:413](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L413) — (no docstring)

### `minDist` (2 declarations, 2 files)

- `def Code.minDist` [ArkLib/Data/CodingTheory/Basic/Distance.lean:164](../../../ArkLib/Data/CodingTheory/Basic/Distance.lean#L164) — (no docstring)
- `theorem ReedSolomon.minDist` [ArkLib/Data/CodingTheory/ReedSolomon.lean:416](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L416) — The minimal code distance of an RS code of length `ι` and dimension `deg` is `ι - deg + 1`.

### `ofFinCoeff` (2 declarations, 2 files)

- `def ArkLib.Lattices.CyclotomicModulus.Rq.ofFinCoeff` [ArkLib/Data/Lattices/CyclotomicRing/Rq.lean:184](../../../ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L184) — The reduced representative with prescribed finite coefficients `Σ_{k<N} cₖ Xᵏ`, valid when `N` does 
- `def CompPoly.CPolynomial.ofFinCoeff` [ArkLib/ToCompPoly/Univariate/Basic.lean:291](../../../ArkLib/ToCompPoly/Univariate/Basic.lean#L291) — The polynomial with prescribed finite coefficient function: `Σ_{k<N} cₖ Xᵏ`.

### `pSpecCoreInteraction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.pSpecCoreInteraction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean:249](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean#L249) — (no docstring)
- `def Binius.RingSwitching.pSpecCoreInteraction` [ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean:45](../../../ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean#L45) — (no docstring)

### `pSpecFold` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.pSpecFold` [ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean:202](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean#L202) — (no docstring)
- `def Fri.Spec.pSpecFold` [ArkLib/ProofSystem/Fri/Spec/General.lean:57](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L57) — (no docstring)

### `perfectlyCorrect` (2 declarations, 2 files)

- `theorem ArkLib.Lattices.Ajtai.InnerOuter.perfectlyCorrect` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Correctness.lean:198](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Correctness.lean#L198) — **Unconditional perfect correctness with the concrete binary decomposition.** Both message and inner
- `theorem ArkLib.Lattices.Ajtai.Simple.perfectlyCorrect` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Correctness.lean:33](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Correctness.lean#L33) — Simple Ajtai commitments are correct on short messages: an honest commitment to a message accepted b

### `proximityCondition` (2 declarations, 2 files)

- `def MutualCorrAgreement.proximityCondition` [ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean:47](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean#L47) — For `parℓ` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → parℓ → 𝔽` and linea
- `def Generator.proximityCondition` [ArkLib/ProofSystem/Whir/ProximityGen.lean:42](../../../ArkLib/ProofSystem/Whir/ProximityGen.lean#L42) — For `l` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → parℓ → 𝔽ˡ` and linear 

### `queryCodeword` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.QueryPhase.queryCodeword` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:146](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L146) — Oracle query helper: query a committed codeword at a given domain point. Restricted to codeword indi
- `def Fri.Spec.QueryRound.queryCodeword` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:731](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L731) — (no docstring)

### `queryOracleReduction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.QueryPhase.queryOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:306](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L306) — The oracle reduction for the final query phase.
- `def Fri.Spec.QueryRound.queryOracleReduction` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:849](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L849) — (no docstring)

### `reduction_verifier_eq_verifier` (2 declarations, 2 files)

- `lemma Sumcheck.Spec.reduction_verifier_eq_verifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:193](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L193) — (no docstring)
- `lemma Sumcheck.Spec.SingleRound.reduction_verifier_eq_verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:866](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L866) — (no docstring)

### `relIn` (2 declarations, 2 files)

- `def CheckClaim.relIn` [ArkLib/ProofSystem/Component/CheckClaim.lean:60](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L60) — (no docstring)
- `def RandomQuery.relIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:41](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L41) — The input relation is that the two oracles are equal.

### `rightpad` (2 declarations, 2 files)

- `def Fin.rightpad` [ArkLib/Data/Fin/Tuple/Defs.lean:90](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L90) — Pad a `Fin`-indexed vector on the right with an element `a`. This becomes truncation if `n < m`.
- `def Matrix.rightpad` [ArkLib/Data/Matrix/Basic.lean:21](../../../ArkLib/Data/Matrix/Basic.lean#L21) — (no docstring)

### `run` (2 declarations, 2 files)

- `def AGM.Adversary.run` [ArkLib/AGM/Basic.lean:164](../../../ArkLib/AGM/Basic.lean#L164) — Running the adversary on a given table, returning the list of group elements it is supposed to outpu
- `def Prover.run` [ArkLib/OracleReduction/Execution.lean:153](../../../ArkLib/OracleReduction/Execution.lean#L153) — Run the prover in an interactive reduction. Returns the output statement and witness, and the transc

### `sumcheckFoldOracleReduction` (2 declarations, 2 files)

- `def sumcheckFoldOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:512](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L512) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:140](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L140) — (no docstring)

### `sumcheckFoldOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:560](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L560) — Perfect completeness for the core interaction oracle reduction
- `theorem Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:201](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L201) — (no docstring)

### `sumcheckFoldOracleVerifier` (2 declarations, 2 files)

- `def sumcheckFoldOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:346](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L346) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:134](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L134) — (no docstring)

### `sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:584](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L584) — Round-by-round knowledge soundness for the sumcheck fold oracle verifier
- `theorem Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:310](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L310) — (no docstring)

### `vecL2NormSq` (2 declarations, 2 files)

- `def ArkLib.Lattices.CyclotomicModulus.vecL2NormSq` [ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean:91](../../../ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean#L91) — Centered squared-`ℓ₂` norm of a vector: the sum of entrywise norms.
- `def ArkLib.Lattices.CenteredCoeffView.vecL2NormSq` [ArkLib/Data/Lattices/CyclotomicRing/Norms.lean:80](../../../ArkLib/Data/Lattices/CyclotomicRing/Norms.lean#L80) — Vector squared `ℓ₂` norm: the sum of entrywise squared `ℓ₂` norms.

### `verify` (2 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.Simple.verify` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:46](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L46) — Verify a simple Ajtai opening by checking the matrix product.
- `def SimpleRO.verify` [ArkLib/Commitments/Ordinary/SimpleRO.lean:44](../../../ArkLib/Commitments/Ordinary/SimpleRO.lean#L44) — Verify an opening `r` of the commitment `cm` to message `v` by recomputing the hash.

### `witnessStructuralInvariant` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:875](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L875) — This condition ensures that the witness polynomial `H` has the correct structure `eq(...) * t(...)`
- `def Binius.RingSwitching.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:406](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L406) — This condition ensures that the witness polynomial `H` has the correct structure `A(...) * t'(...)`

## Near-duplicate docstrings (Jaccard ≥ 0.85, 64 cross-file pairs)

Each pair has docstrings sharing a high fraction of (4+-letter) words, in different files. Most are unrelated coincidences in boilerplate; look for pairs where the *concept* matches.

- **1.00** `Binius.BinaryBasefold.CoreInteraction.commitKState` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:582](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L582) vs `Binius.RingSwitching.SumcheckPhase.iteratedSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:294](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L294)
    - a: Knowledge state function (KState) for single round
    - b: Knowledge state function (KState) for single round
- **1.00** `Binius.BinaryBasefold.CoreInteraction.commitOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:602](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L602) vs `Binius.RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:330](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L330)
    - a: RBR knowledge soundness for a single round oracle verifier
    - b: RBR knowledge soundness for a single round oracle verifier
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:927](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L927) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:479](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L479)
    - a: RBR knowledge error for the final sumcheck step
    - b: RBR knowledge error for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:927](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L927) vs `Binius.RingSwitching.SumcheckPhase.finalSumcheckRbrKnowledgeError` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:453](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L453)
    - a: RBR knowledge error for the final sumcheck step
    - b: RBR knowledge error for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1002](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1002) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:564](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L564)
    - a: The knowledge state function for the final sumcheck step
    - b: The knowledge state function for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1002](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1002) vs `Binius.RingSwitching.SumcheckPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:506](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L506)
    - a: The knowledge state function for the final sumcheck step
    - b: The knowledge state function for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:897](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L897) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:445](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L445)
    - a: The oracle reduction for the final sumcheck step
    - b: The oracle reduction for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:897](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L897) vs `Binius.RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:424](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L424)
    - a: The oracle reduction for the final sumcheck step
    - b: The oracle reduction for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:911](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L911) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:461](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L461)
    - a: Perfect completeness for the final sumcheck step
    - b: Perfect completeness for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:911](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L911) vs `Binius.RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:438](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L438)
    - a: Perfect completeness for the final sumcheck step
    - b: Perfect completeness for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1022](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1022) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:585](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L585)
    - a: Round-by-round knowledge soundness for the final sumcheck step
    - b: Round-by-round knowledge soundness for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:1022](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L1022) vs `Binius.RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:525](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L525)
    - a: Round-by-round knowledge soundness for the final sumcheck step
    - b: Round-by-round knowledge soundness for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:938](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L938) vs `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:490](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L490)
    - a: The round-by-round extractor for the final sumcheck step
    - b: The round-by-round extractor for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:938](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L938) vs `Binius.RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:456](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L456)
    - a: The round-by-round extractor for the final sumcheck step
    - b: The round-by-round extractor for the final sumcheck step
- **1.00** `Binius.BinaryBasefold.CoreInteraction.foldKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:342](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L342) vs `Binius.RingSwitching.SumcheckPhase.iteratedSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:294](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L294)
    - a: Knowledge state function (KState) for single round
    - b: Knowledge state function (KState) for single round
- **1.00** `Binius.BinaryBasefold.CoreInteraction.foldOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:373](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L373) vs `Binius.RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:330](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L330)
    - a: RBR knowledge soundness for a single round oracle verifier
    - b: RBR knowledge soundness for a single round oracle verifier
- **1.00** `Binius.BinaryBasefold.CoreInteraction.getFoldProverFinalOutput` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:67](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L67) vs `Binius.RingSwitching.SumcheckPhase.getIteratedSumcheckProverFinalOutput` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:75](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L75)
    - a: This is in fact usable immediately after the V->P challenge since all inputs are available at that t
    - b: This is in fact usable immediately after the V->P challenge since all inputs are available at that t
- **1.00** `Binius.BinaryBasefold.CoreInteraction.relayKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:742](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L742) vs `Binius.RingSwitching.SumcheckPhase.iteratedSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:294](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L294)
    - a: Knowledge state function (KState) for single round
    - b: Knowledge state function (KState) for single round
- **1.00** `Binius.BinaryBasefold.CoreInteraction.relayOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean:765](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps.lean#L765) vs `Binius.RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:330](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L330)
    - a: RBR knowledge soundness for a single round oracle verifier
    - b: RBR knowledge soundness for a single round oracle verifier
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:96](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L96) vs `Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:160](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L160)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:96](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L96) vs `Binius.RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:81](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L81)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:68](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L68) vs `Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:131](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L131)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:68](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L68) vs `Binius.RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:69](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L69)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:111](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L111) vs `Binius.FRIBinius.FullFRIBinius.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:175](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L175)
    - a: Perfect completeness for the full Binary Basefold protocol (reduction)
    - b: Perfect completeness for the full Binary Basefold protocol (reduction)
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:45](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L45) vs `Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:108](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L108)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:45](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L45) vs `Binius.RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:52](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L52)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.fixFirstVariablesOfMQP_degreeLE` [ArkLib/ProofSystem/Binius/BinaryBasefold/Prelude.lean:158](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Prelude.lean#L158) vs `Sumcheck.Spec.SingleRound.sumcheck_roundPoly_degreeLE` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:787](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L787)
    - a: Auxiliary lemma for proving that the polynomial sent by the honest prover is of degree at most `deg`
    - b: Auxiliary lemma for proving that the polynomial sent by the honest prover is of degree at most `deg`
- **1.00** `Binius.BinaryBasefold.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:875](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L875) vs `Binius.RingSwitching.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:406](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L406)
    - a: This condition ensures that the witness polynomial `H` has the correct structure `eq(...) * t(...)`
    - b: This condition ensures that the witness polynomial `H` has the correct structure `A(...) * t'(...)`
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:479](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L479) vs `Binius.RingSwitching.SumcheckPhase.finalSumcheckRbrKnowledgeError` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:453](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L453)
    - a: RBR knowledge error for the final sumcheck step
    - b: RBR knowledge error for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:564](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L564) vs `Binius.RingSwitching.SumcheckPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:506](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L506)
    - a: The knowledge state function for the final sumcheck step
    - b: The knowledge state function for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:445](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L445) vs `Binius.RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:424](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L424)
    - a: The oracle reduction for the final sumcheck step
    - b: The oracle reduction for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:461](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L461) vs `Binius.RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:438](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L438)
    - a: Perfect completeness for the final sumcheck step
    - b: Perfect completeness for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:585](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L585) vs `Binius.RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:525](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L525)
    - a: Round-by-round knowledge soundness for the final sumcheck step
    - b: Round-by-round knowledge soundness for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:490](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L490) vs `Binius.RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:456](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L456)
    - a: The round-by-round extractor for the final sumcheck step
    - b: The round-by-round extractor for the final sumcheck step
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:160](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L160) vs `Binius.RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:81](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L81)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:131](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L131) vs `Binius.RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:69](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L69)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:108](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L108) vs `Binius.RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:52](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L52)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Groups.exists_zmod_power_of_generator` [ArkLib/Commitments/Functional/KZG/Algebra.lean:105](../../../ArkLib/Commitments/Functional/KZG/Algebra.lean#L105) vs `KZG.CommitmentScheme.binding_exists_zmod_power_of_generator` [ArkLib/Commitments/Functional/KZG/Binding.lean:167](../../../ArkLib/Commitments/Functional/KZG/Binding.lean#L167)
    - a: Every element of a prime-order group is a `ZMod p` power of a nontrivial generator.
    - b: Every element of a prime-order group is a `ZMod p` power of a nontrivial generator.
- **1.00** `Groups.orderOf_eq_prime_of_ne_one` [ArkLib/Commitments/Functional/KZG/Algebra.lean:61](../../../ArkLib/Commitments/Functional/KZG/Algebra.lean#L61) vs `KZG.CommitmentScheme.binding_order_of_eq_prime_of_ne_one` [ArkLib/Commitments/Functional/KZG/Binding.lean:157](../../../ArkLib/Commitments/Functional/KZG/Binding.lean#L157)
    - a: A nontrivial element of a prime-order group has order `p`.
    - b: A nontrivial element of a prime-order group has order `p`.
- **1.00** `KZG.CommitmentScheme.map_binding_instance_drag` [ArkLib/Commitments/Functional/KZG/Binding.lean:639](../../../ArkLib/Commitments/Functional/KZG/Binding.lean#L639) vs `KZG.CommitmentScheme.map_instance_drag` [ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean:534](../../../ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean#L534)
    - a: Transition 3: dragging the map into the probability event.
    - b: Transition 3: dragging the map into the probability event
- **1.00** `OracleVerifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:142](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L142) vs `Verifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:396](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L396)
    - a: Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions
    - b: Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions
- **1.00** `Prover.processRoundFS` [ArkLib/OracleReduction/FiatShamir/Basic.lean:78](../../../ArkLib/OracleReduction/FiatShamir/Basic.lean#L78) vs `Prover.processRoundDSFS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:167](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L167)
    - a: Prover's function for processing the next round, given the current result of the previous round. Thi
    - b: Prover's function for processing the next round, given the current result of the previous round. Thi
- **1.00** `Prover.runToRound` [ArkLib/OracleReduction/Execution.lean:103](../../../ArkLib/OracleReduction/Execution.lean#L103) vs `Prover.runToRoundDSFS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:197](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L197)
    - a: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement 
    - b: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement 
- **1.00** `Prover.runToRound` [ArkLib/OracleReduction/Execution.lean:103](../../../ArkLib/OracleReduction/Execution.lean#L103) vs `Prover.runToRoundFS` [ArkLib/OracleReduction/FiatShamir/Basic.lean:100](../../../ArkLib/OracleReduction/FiatShamir/Basic.lean#L100)
    - a: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement 
    - b: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement 
- **1.00** `Prover.runToRoundFS` [ArkLib/OracleReduction/FiatShamir/Basic.lean:100](../../../ArkLib/OracleReduction/FiatShamir/Basic.lean#L100) vs `Prover.runToRoundDSFS` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:197](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L197)
    - a: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement 
    - b: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement 
- **1.00** `StirIOP.OracleStatement` [ArkLib/ProofSystem/Stir/MainThm.lean:81](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L81) vs `WhirIOP.OracleStatement` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:146](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L146)
    - a: `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type
    - b: `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type
- **1.00** `StirIOP.Params` [ArkLib/ProofSystem/Stir/MainThm.lean:32](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L32) vs `WhirIOP.Params` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:54](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L54)
    - a: **Per‑round protocol parameters:** For a fixed depth `M`, the reduction runs `M + 1` rounds. In roun
    - b: ** Per‑round protocol parameters. ** For a fixed depth `M`, the reduction runs `M + 1` rounds. In ro
- **1.00** `coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:619](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L619) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:623](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L623)
    - a: The final oracle reduction that composes sumcheckFold with finalSumcheckStep
    - b: The final oracle reduction that composes sumcheckFold with finalSumcheckStep
- **1.00** `coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:638](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L638) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:645](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L645)
    - a: Perfect completeness for the core interaction oracle reduction
    - b: Perfect completeness for the core interaction oracle reduction
- **1.00** `coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:604](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L604) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:605](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L605)
    - a: The final oracle verifier that composes sumcheckFold with finalSumcheckStep
    - b: The final oracle verifier that composes sumcheckFold with finalSumcheckStep
- **1.00** `coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:664](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L664) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:678](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L678)
    - a: Round-by-round knowledge soundness for the core interaction oracle verifier
    - b: Round-by-round knowledge soundness for the core interaction oracle verifier
- **1.00** `sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:560](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L560) vs `Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:645](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L645)
    - a: Perfect completeness for the core interaction oracle reduction
    - b: Perfect completeness for the core interaction oracle reduction
- **0.88** `OracleProof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:492](../../../ArkLib/OracleReduction/Security/Basic.lean#L492) vs `OracleProof.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:506](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L506)
    - a: Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.88** `OracleProof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:492](../../../ArkLib/OracleReduction/Security/Basic.lean#L492) vs `OracleVerifier.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:463](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L463)
    - a: Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.88** `OracleVerifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:413](../../../ArkLib/OracleReduction/Security/Basic.lean#L413) vs `OracleProof.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:506](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L506)
    - a: Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.88** `OracleVerifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:413](../../../ArkLib/OracleReduction/Security/Basic.lean#L413) vs `OracleVerifier.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:463](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L463)
    - a: Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.86** `Domain.CosetFftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:123](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L123) vs `Domain.FftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/FftDomain/Ops.lean:161](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L161)
    - a: The existence of a nontrivial smooth coset FFT domain rules out characteristic `2`.
    - b: The existence of a nontrivial smooth FFT domain rules out characteristic `2`.
- **0.86** `OracleProof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:484](../../../ArkLib/OracleReduction/Security/Basic.lean#L484) vs `OracleProof.rbrSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:498](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L498)
    - a: Soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.86** `OracleProof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:484](../../../ArkLib/OracleReduction/Security/Basic.lean#L484) vs `OracleVerifier.rbrSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:454](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L454)
    - a: Soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.86** `OracleVerifier.id_knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:632](../../../ArkLib/OracleReduction/Security/Basic.lean#L632) vs `Verifier.id_rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:583](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L583)
    - a: The identity / trivial verifier is perfectly knowledge sound.
    - b: The identity / trivial verifier is perfectly round-by-round knowledge sound.
- **0.86** `OracleVerifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:405](../../../ArkLib/OracleReduction/Security/Basic.lean#L405) vs `OracleProof.rbrSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:498](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L498)
    - a: Soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.86** `OracleVerifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:405](../../../ArkLib/OracleReduction/Security/Basic.lean#L405) vs `OracleVerifier.rbrSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:454](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L454)
    - a: Soundness of an oracle reduction is the same as for non-oracle reductions.
    - b: Round-by-round soundness of an oracle reduction is the same as for non-oracle reductions.
- **0.86** `Verifier.id_knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:569](../../../ArkLib/OracleReduction/Security/Basic.lean#L569) vs `Verifier.id_rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:583](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L583)
    - a: The identity / trivial verifier is perfectly knowledge sound.
    - b: The identity / trivial verifier is perfectly round-by-round knowledge sound.
- **0.86** `proximity_gap_degree_bound` [ArkLib/Data/CodingTheory/GuruswamiSudan/Basic.lean:28](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/Basic.lean#L28) vs `ProximityGap.D_X` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:31](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L31)
    - a: The degree bound (i.e. `D_X(m) = (m + 1/2) * √ρ * n`) for instantiation of Guruswami-Sudan in Lemma 
    - b: The degree bound (a.k.a. `D_X`) for instantiation of Guruswami-Sudan in Lemma 5.3 of [BCIKS20]. `D_X

