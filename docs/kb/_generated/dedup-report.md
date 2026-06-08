# ArkLib dedup-candidate report

Generated from `docs/kb/_generated/declarations.json`. **Eyeball, do not auto-rewrite.** The point is to surface name collisions and doc-string overlap that *might* indicate an opportunity to consolidate.

## Stats

- `ArkLib` — 788 files, 14544 declarations

## Same short-name across multiple files (509 groups)

Each group lists declarations sharing a short name across ≥2 files. Most are legitimate (overloaded interface, paper-shape vs general form), but the list is the right anchor to look for duplicates.

### `oracleVerifier` (12 declarations, 11 files)

- `def Binius.RingSwitching.BatchingPhase.oracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:365](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L365) — (no docstring)
- `def CheckClaim.oracleVerifier` [ArkLib/ProofSystem/Component/CheckClaim.lean:250](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L250) — The oracle verifier for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleVerifier` [ArkLib/ProofSystem/Component/DoNothing.lean:106](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L106) — The oracle verifier for the `DoNothing` oracle reduction.
- `def RandomQuery.oracleVerifier` [ArkLib/ProofSystem/Component/RandomQuery.lean:87](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L87) — The oracle verifier simply returns the challenge, and performs no checks.
- `def ReduceClaim.oracleVerifier` [ArkLib/ProofSystem/Component/ReduceClaim.lean:260](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L260) — The oracle verifier for the `ReduceClaim` oracle reduction.
- `def SendClaim.oracleVerifier` [ArkLib/ProofSystem/Component/SendClaim.lean:67](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L67) — The verifier checks that the relationship `rel oldStmt newStmt` holds. It has access to the original
- `def SendSingleWitness.oracleVerifier` [ArkLib/ProofSystem/Component/SendWitness.lean:352](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L352) — The oracle verifier for the `SendSingleWitness` oracle reduction. The verifier receives the input st
- `def RingSwitching.BatchingPhase.oracleVerifier` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:176](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L176) — (no docstring)
- `def Sumcheck.Spec.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:158](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L158) — The oracle verifier for the (full) sum-check protocol
- `def Sumcheck.Spec.SingleRound.Simple.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:702](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L702) — (no docstring)
- `def Sumcheck.Spec.SingleRound.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1353](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1353) — The oracle verifier for the `i`-th round of the sum-check protocol. Migrated to the new `OracleState
- `def ToyProblem.Spec.oracleVerifier` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:576](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L576) — Oracle verifier for Construction 6.2. Queries the prover's message `g` once and the two oracle codew

### `reduction` (12 declarations, 11 files)

- `def KZG.CommitmentScheme.reduction` [ArkLib/CommitmentScheme/KZG/FunctionBinding/Basic.lean:115](../../../ArkLib/CommitmentScheme/KZG/FunctionBinding/Basic.lean#L115) — The reduction breaking ARSDH using a successful function-binding adversary. The reduction follows th
- `def CheckClaim.reduction` [ArkLib/ProofSystem/Component/CheckClaim.lean:56](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L56) — The reduction for the `CheckClaim` reduction.
- `def DoNothing.reduction` [ArkLib/ProofSystem/Component/DoNothing.lean:44](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L44) — The reduction for the `DoNothing` reduction. - Prover simply returns the statement and witness. - Ve
- `def NoInteraction.reduction` [ArkLib/ProofSystem/Component/NoInteraction.lean:63](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L63) — The no-interaction reduction can be specified by a tuple of functions: - `mapStmt : StmtIn → OracleC
- `def ReduceClaim.reduction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:59](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L59) — The reduction for the `ReduceClaim` reduction.
- `def SendWitness.reduction` [ArkLib/ProofSystem/Component/SendWitness.lean:77](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L77) — (no docstring)
- `def Fri.Spec.reduction` [ArkLib/ProofSystem/Fri/Spec/General.lean:107](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L107) — (no docstring)
- `def Sumcheck.Spec.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:168](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L168) — The sum-check protocol as a reduction
- `def Sumcheck.Spec.SingleRound.Simple.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:642](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L642) — The reduction for the simple description of a single round of sum-check
- `def Sumcheck.Spec.SingleRound.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1372](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1372) — The sum-check reduction for the `i`-th round of the sum-check protocol
- `def ToyProblem.Spec.reduction` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:499](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L499) — Honest reduction for Construction 6.2: the package `{prover, verifier}` over the bundled-input `Redu
- `def ToyProblem.SimplifiedIOR.reduction` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:168](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L168) — Honest reduction for Construction 6.9.

### `pSpec` (12 declarations, 10 files)

- `def RandomQuery.pSpec` [ArkLib/ProofSystem/Component/RandomQuery.lean:55](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L55) — (no docstring)
- `def SendClaim.pSpec` [ArkLib/ProofSystem/Component/SendClaim.lean:32](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L32) — (no docstring)
- `def SendWitness.pSpec` [ArkLib/ProofSystem/Component/SendWitness.lean:53](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L53) — (no docstring)
- `def Fri.Spec.FoldPhase.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:340](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L340) — Each round of the FRI protocol begins with the verifier sending a random field element as the challe
- `def Fri.Spec.FinalFoldPhase.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:645](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L645) — The final folding round of the FRI protocol begins with the verifier sending a random field element
- `def Fri.Spec.QueryRound.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:956](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L956) — (no docstring)
- `def Logup.pSpec` [ArkLib/ProofSystem/Logup/Protocol.lean:80](../../../ArkLib/ProofSystem/Logup/Protocol.lean#L80) — Protocol 2 transcript shape: the outer LogUp messages followed by ArkLib's generic sumcheck.
- `def StirIOP.Round.pSpec` [ArkLib/ProofSystem/Stir/RoundProtocol.lean:60](../../../ArkLib/ProofSystem/Stir/RoundProtocol.lean#L60) — The protocol spec of one STIR fold round: the verifier first sends a folding challenge in `F` (`V_to
- `def Sumcheck.Spec.pSpec` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:125](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L125) — The protocol specification for the general sum-check protocol, which is the composition of the singl
- `def Sumcheck.Spec.SingleRound.pSpec` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:149](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L149) — The protocol specification for a single round of sum-check. Has the form `⟨!v[.P_to_V, .V_to_P], !v[
- `def ToyProblem.Spec.pSpec` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:132](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L132) — Protocol specification for Construction 6.2: three rounds, in the order V → P  (γ : F)            --
- `def ToyProblem.SimplifiedIOR.pSpec` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:108](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L108) — Protocol specification for Construction 6.9: a single `V → P` round sending the combination randomne

### `OracleStatement` (10 declarations, 10 files)

- `abbrev Interaction.OracleStatement` [ArkLib/Interaction/Oracle/Core.lean:100](../../../ArkLib/Interaction/Oracle/Core.lean#L100) — (no docstring)
- `def BatchedFri.Spec.OracleStatement` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:46](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L46) — An oracle for each batched polynomial.
- `def Binius.BinaryBasefold.OracleStatement` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:746](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L746) — For the `i`-th round of the protocol, there will be oracle statements corresponding to all committed
- `def R1CS.OracleStatement` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:150](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L150) — (no docstring)
- `def Fri.Spec.OracleStatement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:89](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L89) — For the `i`-th round of the protocol, there will be `i + 1` oracle statements, one for the beginning
- `abbrev Spartan.Spec.OracleStatement` [ArkLib/ProofSystem/Spartan/Basic.lean:60](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L60) — This unfolds to `A, B, C : Matrix (Fin 2 ^ ℓ_m) (Fin 2 ^ ℓ_n) R`
- `def StirIOP.OracleStatement` [ArkLib/ProofSystem/Stir/MainThm.lean:84](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L84) — `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type
- `def Sumcheck.Spec.OracleStatement` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:136](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L136) — Oracle statement for sum-check, which is a multivariate polynomial over `n` variables of individual
- `def ToyProblem.Spec.OracleStatement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:99](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L99) — Oracle statements of Construction 6.2: the two purported codewords `f₁, f₂ : ι → F`. The verifier on
- `def WhirIOP.OracleStatement` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:146](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L146) — `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type

### `oracleReduction` (11 declarations, 9 files)

- `def CheckClaim.oracleReduction` [ArkLib/ProofSystem/Component/CheckClaim.lean:258](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L258) — The oracle reduction for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleReduction` [ArkLib/ProofSystem/Component/DoNothing.lean:116](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L116) — The oracle reduction for the `DoNothing` oracle reduction. - Prover simply returns the (non-oracle a
- `def RandomQuery.oracleReduction` [ArkLib/ProofSystem/Component/RandomQuery.lean:105](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L105) — Combine the trivial prover and this verifier to form the `RandomQuery` oracle reduction: the input o
- `def ReduceClaim.oracleReduction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:277](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L277) — The oracle reduction for the `ReduceClaim` oracle reduction.
- `def SendClaim.oracleReduction` [ArkLib/ProofSystem/Component/SendClaim.lean:96](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L96) — Combine the prover and verifier into an oracle reduction. The input has no statement or witness, but
- `def SendSingleWitness.oracleReduction` [ArkLib/ProofSystem/Component/SendWitness.lean:365](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L365) — (no docstring)
- `def Sumcheck.Spec.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:180](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L180) — The sum-check protocol as an oracle reduction
- `def Sumcheck.Spec.SingleRound.Simpler.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:566](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L566) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:721](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L721) — (no docstring)
- `def Sumcheck.Spec.SingleRound.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1382](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1382) — The sum-check oracle reduction for the `i`-th round of the sum-check protocol. Migrated to the new `
- `def ToyProblem.Spec.oracleReduction` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:608](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L608) — Honest oracle reduction for Construction 6.2: the `OracleProver` / `OracleVerifier` pair packaged as

### `verifier` (11 declarations, 9 files)

- `def CheckClaim.verifier` [ArkLib/ProofSystem/Component/CheckClaim.lean:51](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L51) — The verifier for the `CheckClaim` reduction.
- `def DoNothing.verifier` [ArkLib/ProofSystem/Component/DoNothing.lean:35](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L35) — The verifier for the `DoNothing` reduction.
- `def NoInteraction.verifier` [ArkLib/ProofSystem/Component/NoInteraction.lean:54](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L54) — The verifier in a no-interaction reduction takes an empty transcript, and hence reduce to a function
- `def ReduceClaim.verifier` [ArkLib/ProofSystem/Component/ReduceClaim.lean:55](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L55) — The verifier for the `ReduceClaim` reduction.
- `def SendWitness.verifier` [ArkLib/ProofSystem/Component/SendWitness.lean:73](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L73) — (no docstring)
- `def Sumcheck.Spec.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:149](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L149) — The verifier for the (full) sum-check protocol
- `def Sumcheck.Spec.SingleRound.Simple.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:633](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L633) — The verifier for the simple description of a single round of sum-check
- `def Sumcheck.Spec.SingleRound.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1343](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1343) — The verifier for the `i`-th round of the sum-check protocol
- `def Sumcheck.Spec.SingleRound.Unfolded.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1891](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1891) — The (non-oracle) verifier of the sum-check protocol for the `i`-th round, where `i < n + 1`
- `def ToyProblem.Spec.verifier` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:485](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L485) — Honest verifier for Construction 6.2. Takes the bundled input `(stmt, oStmt) = ((v, μ₁, μ₂), (f₁, f₂
- `def ToyProblem.SimplifiedIOR.verifier` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:157](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L157) — Honest verifier for Construction 6.9. Reads `γ` from the transcript and produces the new statement `

### `oracleProver` (10 declarations, 9 files)

- `def Binius.RingSwitching.BatchingPhase.oracleProver` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:326](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L326) — (no docstring)
- `def CheckClaim.oracleProver` [ArkLib/ProofSystem/Component/CheckClaim.lean:237](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L237) — The oracle prover for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleProver` [ArkLib/ProofSystem/Component/DoNothing.lean:101](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L101) — The oracle prover for the `DoNothing` oracle reduction.
- `def RandomQuery.oracleProver` [ArkLib/ProofSystem/Component/RandomQuery.lean:67](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L67) — The prover is trivial: it has no messages to send.  It only receives the verifier's challenge `q`, a
- `def ReduceClaim.oracleProver` [ArkLib/ProofSystem/Component/ReduceClaim.lean:250](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L250) — The oracle prover for the `ReduceClaim` oracle reduction.
- `def SendClaim.oracleProver` [ArkLib/ProofSystem/Component/SendClaim.lean:40](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L40) — The prover takes in the old oracle statement as input, and sends it as the protocol message.
- `def SendWitness.oracleProver` [ArkLib/ProofSystem/Component/SendWitness.lean:268](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L268) — The oracle prover for the `SendWitness` oracle reduction. For each round `i : Fin (FinEnum.card ιw)`
- `def SendSingleWitness.oracleProver` [ArkLib/ProofSystem/Component/SendWitness.lean:336](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L336) — The oracle prover for the `SendSingleWitness` oracle reduction. The prover sends the witness `wit` t
- `def RingSwitching.BatchingPhase.oracleProver` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:128](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L128) — (no docstring)
- `def ToyProblem.Spec.oracleProver` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:528](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L528) — Same as `prover` but exposed at the `OracleProver` signature. The underlying `Prover` is identical (

### `prover` (9 declarations, 8 files)

- `def CheckClaim.prover` [ArkLib/ProofSystem/Component/CheckClaim.lean:40](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L40) — The prover for the `CheckClaim` reduction.
- `def DoNothing.prover` [ArkLib/ProofSystem/Component/DoNothing.lean:31](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L31) — The prover for the `DoNothing` reduction.
- `def NoInteraction.prover` [ArkLib/ProofSystem/Component/NoInteraction.lean:44](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L44) — The prover in a no-interaction reduction can be specified by a tuple of functions: - `mapStmt : Stmt
- `def ReduceClaim.prover` [ArkLib/ProofSystem/Component/ReduceClaim.lean:47](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L47) — The prover for the `ReduceClaim` reduction.
- `def SendWitness.prover` [ArkLib/ProofSystem/Component/SendWitness.lean:63](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L63) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.prover` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:611](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L611) — The prover in the simple description of a single round of sum-check. Takes in input `target : R` and
- `def Sumcheck.Spec.SingleRound.Unfolded.prover` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1881](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1881) — The overall prover for the `i`-th round of the sum-check protocol, where `i < n`. This is only well-
- `def ToyProblem.Spec.prover` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:441](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L441) — Honest prover for Construction 6.2. After receiving the combination randomness `γ`, the prover sends
- `def ToyProblem.SimplifiedIOR.prover` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:126](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L126) — Honest prover for Construction 6.9. After receiving `γ`, sets the new witness `M_new := M₀ + γ·M₁` a

### `relation` (9 declarations, 8 files)

- `def ArkLib.Lattices.ModuleSIS.relation` [ArkLib/Data/Lattices/ModuleSIS.lean:82](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L82) — The kernel-form Module-SIS relation for a fixed matrix `A`: `z` is nonzero, short, and lies in the k
- `def ConstraintSystem.relation` [ArkLib/ProofSystem/ConstraintSystem/Basic.lean:68](../../../ArkLib/ProofSystem/ConstraintSystem/Basic.lean#L68) — The underlying set-theoretic relation at a given index.
- `def Lookup.relation` [ArkLib/ProofSystem/ConstraintSystem/Lookup.lean:25](../../../ArkLib/ProofSystem/ConstraintSystem/Lookup.lean#L25) — The lookup relation. Takes in a collection of values and a table, both containers for elements of ty
- `def MemoryChecking.ReadOnly.relation` [ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean:128](../../../ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean#L128) — The read-only memory checking relation. It takes a memory `mem` and a list of read operations `ops`.
- `def MemoryChecking.ReadWrite.relation` [ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean:161](../../../ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean#L161) — The read-write memory checking relation. It takes an initial memory `startMem`, a final memory `fina
- `def Plonk.relation` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:193](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L193) — To define a relation based on the constraint system, we extend it with: - A natural number `ℓ ≤ m` r
- `def R1CS.relation` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:163](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L163) — The R1CS relation: `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where `*` is understood to mean component-wise
- `abbrev Spartan.Spec.relation` [ArkLib/ProofSystem/Spartan/Basic.lean:68](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L68) — This unfolds to `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where `𝕫 = 𝕩 ‖ 𝕨`
- `def ToyProblem.relation` [ArkLib/ProofSystem/ToyProblem/Definitions.lean:78](../../../ArkLib/ProofSystem/ToyProblem/Definitions.lean#L78) — **Definition 6.1 of [ABF26]** (toy problem relation `R_C^ℓ`). Given a base code `C ⊆ (ι → F)` (the p

### `inputRelation` (10 declarations, 7 files)

- `def BatchedFri.Spec.inputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/General.lean:67](../../../ArkLib/ProofSystem/BatchedFri/Spec/General.lean#L67) — (no docstring)
- `def BatchedFri.Spec.BatchingRound.inputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:69](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L69) — (no docstring)
- `def Fri.Spec.inputRelation` [ArkLib/ProofSystem/Fri/Spec/General.lean:46](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L46) — (no docstring)
- `def Fri.Spec.FoldPhase.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:275](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L275) — The FRI non-final folding round input relation, with proximity parameter `0 < δ`, for the `i`-th rou
- `def Fri.Spec.FinalFoldPhase.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:584](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L584) — Input relation for the final folding round, with proximity parameter `0 < δ`. The round-`k` codeword
- `def Fri.Spec.QueryRound.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:935](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L935) — (no docstring)
- `def Logup.inputRelation` [ArkLib/ProofSystem/Logup/Common.lean:264](../../../ArkLib/ProofSystem/Logup/Common.lean#L264) — Semantic input relation for Protocol 2: every lookup-column value occurs in the table range.
- `def Sumcheck.Spec.SingleRound.Simpler.inputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:338](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L338) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.inputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:596](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L596) — (no docstring)
- `def ToyProblem.Spec.inputRelation` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:187](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L187) — The IOR-shaped input relation derived from `ToyProblem.relation` (Definition 6.1). `((v, μ₁, μ₂), (f

### `outputRelation` (9 declarations, 6 files)

- `def BatchedFri.Spec.BatchingRound.outputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:85](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L85) — (no docstring)
- `def Fri.Spec.outputRelation` [ArkLib/ProofSystem/Fri/Spec/General.lean:56](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L56) — (no docstring)
- `def Fri.Spec.FoldPhase.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:303](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L303) — The FRI non-final folding round output relation, with proximity parameter `0 < δ`, for the `i`-th ro
- `def Fri.Spec.FinalFoldPhase.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:613](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L613) — Output relation for the final folding round. After the final round the prover sends a polynomial in
- `def Fri.Spec.QueryRound.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:943](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L943) — (no docstring)
- `def Logup.outputRelation` [ArkLib/ProofSystem/Logup/Common.lean:299](../../../ArkLib/ProofSystem/Logup/Common.lean#L299) — The full protocol has a trivial final relation: successful verification returns `Unit`.
- `def Sumcheck.Spec.SingleRound.Simpler.outputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:367](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L367) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.outputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:599](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L599) — (no docstring)
- `def ToyProblem.Spec.outputRelation` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:266](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L266) — The IOR-shaped *relaxed* output relation derived from `ToyProblem.relaxedRelation` (Definition 6.3).

### `Witness` (6 declarations, 6 files)

- `def BatchedFri.Spec.Witness` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:54](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L54) — The Batched FRI protocol has as witness for each batched polynomial that is supposed to correspond t
- `structure Binius.BinaryBasefold.Witness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:767](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L767) — The round witness for round `i` of `t ∈ L[≤ 2][X Fin ℓ]` and `Hᵢ(Xᵢ, ..., Xₗ₋₁) := h(r₀', ..., rᵢ₋₁'
- `def R1CS.Witness` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:153](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L153) — (no docstring)
- `def Fri.Spec.Witness` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:110](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L110) — The FRI protocol has as witness the polynomial that is supposed to correspond to the codeword in the
- `abbrev Spartan.Spec.Witness` [ArkLib/ProofSystem/Spartan/Basic.lean:64](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L64) — This unfolds to `𝕨 : Fin 2 ^ ℓ_w → R`
- `def ToyProblem.Spec.Witness` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:107](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L107) — Honest witness: the underlying messages `M₁, M₂ : Fin k → F` whose encodings are the oracle codeword

### `Statement` (5 declarations, 5 files)

- `def R1CS.Statement` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:147](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L147) — (no docstring)
- `def Fri.Spec.Statement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:80](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L80) — For the `i`-th round of the protocol, the input statement is equal to the challenges sent from round
- `abbrev Spartan.Spec.Statement` [ArkLib/ProofSystem/Spartan/Basic.lean:56](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L56) — This unfolds to `𝕩 : Fin (2 ^ ℓ_n - 2 ^ ℓ_w) → R`
- `structure Sumcheck.Structured.Statement` [ArkLib/ProofSystem/Sumcheck/Structured.lean:197](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L197) — Statement per iterated sumcheck round
- `def ToyProblem.Spec.Statement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:93](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L93) — Input (explicit) statement of Construction 6.2: the linear-constraint vector `v ∈ F^k` and the two c

### `oracleReduction_isHVZK` (5 declarations, 5 files)

- `theorem CheckClaim.oracleReduction_isHVZK` [ArkLib/ProofSystem/Component/CheckClaim.lean:292](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L292) — The `CheckClaim` oracle reduction has an explicit perfect-HVZK simulator for any input relation.
- `theorem DoNothing.oracleReduction_isHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:194](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L194) — The `DoNothing` oracle reduction has an explicit perfect-HVZK simulator for any oracle-input relatio
- `theorem RandomQuery.oracleReduction_isHVZK` [ArkLib/ProofSystem/Component/RandomQuery.lean:229](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L229) — `RandomQuery` has an explicit perfect-HVZK simulator as an oracle reduction.
- `theorem ReduceClaim.oracleReduction_isHVZK` [ArkLib/ProofSystem/Component/ReduceClaim.lean:423](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L423) — The plain `ReduceClaim` oracle reduction has an explicit perfect-HVZK simulator for any input relati
- `theorem SendClaim.oracleReduction_isHVZK` [ArkLib/ProofSystem/Component/SendClaim.lean:285](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L285) — `SendClaim` has an explicit perfect-HVZK simulator as an oracle reduction.

### `oracleReduction_isStatHVZK` (5 declarations, 5 files)

- `theorem CheckClaim.oracleReduction_isStatHVZK` [ArkLib/ProofSystem/Component/CheckClaim.lean:303](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L303) — The `CheckClaim` oracle reduction has statistical HVZK for any input relation and error budget.
- `theorem DoNothing.oracleReduction_isStatHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:202](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L202) — The `DoNothing` oracle reduction has statistical HVZK for any oracle-input relation and error budget
- `theorem RandomQuery.oracleReduction_isStatHVZK` [ArkLib/ProofSystem/Component/RandomQuery.lean:237](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L237) — `RandomQuery` has statistical HVZK at every error budget as an oracle reduction.
- `theorem ReduceClaim.oracleReduction_isStatHVZK` [ArkLib/ProofSystem/Component/ReduceClaim.lean:434](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L434) — The plain `ReduceClaim` oracle reduction has statistical HVZK for any input relation and error budge
- `theorem SendClaim.oracleReduction_isStatHVZK` [ArkLib/ProofSystem/Component/SendClaim.lean:295](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L295) — `SendClaim` has statistical HVZK at every error budget as an oracle reduction.

### `oracleReduction_perfectHVZK` (5 declarations, 5 files)

- `theorem CheckClaim.oracleReduction_perfectHVZK` [ArkLib/ProofSystem/Component/CheckClaim.lean:269](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L269) — The `CheckClaim` oracle reduction is perfectly HVZK for any input relation: it has no prover message
- `theorem DoNothing.oracleReduction_perfectHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:176](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L176) — The `DoNothing` oracle reduction is perfectly HVZK for any oracle-input relation.
- `theorem RandomQuery.oracleReduction_perfectHVZK` [ArkLib/ProofSystem/Component/RandomQuery.lean:210](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L210) — `RandomQuery` is perfectly HVZK as an oracle reduction: it has no private witness, and the single ve
- `theorem ReduceClaim.oracleReduction_perfectHVZK` [ArkLib/ProofSystem/Component/ReduceClaim.lean:400](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L400) — The plain `ReduceClaim` oracle reduction is perfectly HVZK for any input relation: it has no message
- `theorem SendClaim.oracleReduction_perfectHVZK` [ArkLib/ProofSystem/Component/SendClaim.lean:264](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L264) — `SendClaim` is perfectly HVZK as an oracle reduction for any input relation: the protocol has no pri

### `oracleReduction_statisticalHVZK` (5 declarations, 5 files)

- `theorem CheckClaim.oracleReduction_statisticalHVZK` [ArkLib/ProofSystem/Component/CheckClaim.lean:280](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L280) — Perfect HVZK implies statistical HVZK for the `CheckClaim` oracle reduction at every error budget.
- `theorem DoNothing.oracleReduction_statisticalHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:185](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L185) — The `DoNothing` oracle reduction is statistically HVZK for any oracle-input relation and error budge
- `theorem RandomQuery.oracleReduction_statisticalHVZK` [ArkLib/ProofSystem/Component/RandomQuery.lean:220](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L220) — Perfect HVZK implies statistical HVZK for `RandomQuery` at every error budget.
- `theorem ReduceClaim.oracleReduction_statisticalHVZK` [ArkLib/ProofSystem/Component/ReduceClaim.lean:412](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L412) — Perfect HVZK implies statistical HVZK for the plain `ReduceClaim` oracle reduction at every error bu
- `theorem SendClaim.oracleReduction_statisticalHVZK` [ArkLib/ProofSystem/Component/SendClaim.lean:275](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L275) — Perfect HVZK implies statistical HVZK for `SendClaim` at every error budget.

### `oracleReduction_toReduction_isHVZK` (5 declarations, 5 files)

- `theorem CheckClaim.oracleReduction_toReduction_isHVZK` [ArkLib/ProofSystem/Component/CheckClaim.lean:334](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L334) — The underlying non-oracle reduction of `CheckClaim.oracleReduction` has an explicit perfect-HVZK sim
- `theorem DoNothing.oracleReduction_toReduction_isHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:159](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L159) — The `DoNothing` oracle reduction, viewed as a plain reduction, has an explicit perfect-HVZK simulato
- `theorem RandomQuery.oracleReduction_toReduction_isHVZK` [ArkLib/ProofSystem/Component/RandomQuery.lean:264](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L264) — The underlying non-oracle reduction of `RandomQuery` has an explicit perfect-HVZK simulator.
- `theorem ReduceClaim.oracleReduction_toReduction_isHVZK` [ArkLib/ProofSystem/Component/ReduceClaim.lean:466](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L466) — The underlying non-oracle reduction of the plain `ReduceClaim` oracle reduction has an explicit perf
- `theorem SendClaim.oracleReduction_toReduction_isHVZK` [ArkLib/ProofSystem/Component/SendClaim.lean:324](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L324) — The underlying non-oracle reduction of `SendClaim` has an explicit perfect-HVZK simulator.

### `oracleReduction_toReduction_isStatHVZK` (5 declarations, 5 files)

- `theorem CheckClaim.oracleReduction_toReduction_isStatHVZK` [ArkLib/ProofSystem/Component/CheckClaim.lean:345](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L345) — The underlying non-oracle reduction of `CheckClaim.oracleReduction` has statistical HVZK for any inp
- `theorem DoNothing.oracleReduction_toReduction_isStatHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:167](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L167) — The `DoNothing` oracle reduction, viewed as a plain reduction, has statistical HVZK for any relation
- `theorem RandomQuery.oracleReduction_toReduction_isStatHVZK` [ArkLib/ProofSystem/Component/RandomQuery.lean:274](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L274) — The underlying non-oracle reduction of `RandomQuery` has statistical HVZK at every error budget.
- `theorem ReduceClaim.oracleReduction_toReduction_isStatHVZK` [ArkLib/ProofSystem/Component/ReduceClaim.lean:477](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L477) — The underlying non-oracle reduction of the plain `ReduceClaim` oracle reduction has statistical HVZK
- `theorem SendClaim.oracleReduction_toReduction_isStatHVZK` [ArkLib/ProofSystem/Component/SendClaim.lean:335](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L335) — The underlying non-oracle reduction of `SendClaim` has statistical HVZK at every error budget.

### `oracleReduction_toReduction_perfectHVZK` (5 declarations, 5 files)

- `theorem CheckClaim.oracleReduction_toReduction_perfectHVZK` [ArkLib/ProofSystem/Component/CheckClaim.lean:312](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L312) — The underlying non-oracle reduction of `CheckClaim.oracleReduction` is perfectly HVZK for any input
- `theorem DoNothing.oracleReduction_toReduction_perfectHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:139](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L139) — The `DoNothing` oracle reduction, viewed as a plain reduction, is perfectly HVZK for any relation. T
- `theorem RandomQuery.oracleReduction_toReduction_perfectHVZK` [ArkLib/ProofSystem/Component/RandomQuery.lean:244](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L244) — The underlying non-oracle reduction of `RandomQuery` is perfectly HVZK.
- `theorem ReduceClaim.oracleReduction_toReduction_perfectHVZK` [ArkLib/ProofSystem/Component/ReduceClaim.lean:444](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L444) — The underlying non-oracle reduction of the plain `ReduceClaim` oracle reduction is perfectly HVZK fo
- `theorem SendClaim.oracleReduction_toReduction_perfectHVZK` [ArkLib/ProofSystem/Component/SendClaim.lean:303](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L303) — The underlying non-oracle reduction of `SendClaim` is perfectly HVZK.

### `oracleReduction_toReduction_statisticalHVZK` (5 declarations, 5 files)

- `theorem CheckClaim.oracleReduction_toReduction_statisticalHVZK` [ArkLib/ProofSystem/Component/CheckClaim.lean:323](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L323) — The underlying non-oracle reduction of `CheckClaim.oracleReduction` is statistically HVZK for any in
- `theorem DoNothing.oracleReduction_toReduction_statisticalHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:148](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L148) — The `DoNothing` oracle reduction, viewed as a plain reduction, is statistically HVZK for any relatio
- `theorem RandomQuery.oracleReduction_toReduction_statisticalHVZK` [ArkLib/ProofSystem/Component/RandomQuery.lean:254](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L254) — The underlying non-oracle reduction of `RandomQuery` is statistically HVZK at every error budget.
- `theorem ReduceClaim.oracleReduction_toReduction_statisticalHVZK` [ArkLib/ProofSystem/Component/ReduceClaim.lean:455](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L455) — The underlying non-oracle reduction of the plain `ReduceClaim` oracle reduction is statistically HVZ
- `theorem SendClaim.oracleReduction_toReduction_statisticalHVZK` [ArkLib/ProofSystem/Component/SendClaim.lean:314](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L314) — The underlying non-oracle reduction of `SendClaim` is statistically HVZK at every error budget.

### `toFinset` (6 declarations, 4 files)

- `def ReedSolomon.toFinset` [ArkLib/Data/CodingTheory/ReedSolomon.lean:97](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L97) — (no docstring)
- `def ReedSolomon.FftDomain.toFinset` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:184](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L184) — (no docstring)
- `def ReedSolomon.CosetFftDomain.toFinset` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:552](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L552) — (no docstring)
- `def Domain.CosetFftDomainClass.toFinset` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:242](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L242) — (no docstring)
- `abbrev Domain.CosetFftDomain.toFinset` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:258](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L258) — (no docstring)
- `abbrev Domain.FftDomain.toFinset` [ArkLib/Data/Domain/FftDomain/Defs.lean:126](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L126) — (no docstring)

### `StmtIn` (5 declarations, 4 files)

- `def RandomQuery.StmtIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:32](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L32) — (no docstring)
- `structure Logup.StmtIn` [ArkLib/ProofSystem/Logup/Common.lean:233](../../../ArkLib/ProofSystem/Logup/Common.lean#L233) — Public parameter assumptions for Protocol 2. The paper fixes a finite field with characteristic larg
- `def Sumcheck.Spec.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:137](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L137) — The input statement for the (full) sum-check protocol, which contains only the target sum value
- `def Sumcheck.Spec.SingleRound.Simpler.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:335](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L335) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:585](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L585) — (no docstring)

### `coreInteractionOracleReduction` (4 declarations, 4 files)

- `def coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:1122](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L1122) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1653](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1653) — The final oracle reduction that composes sumcheckFold with finalSumcheckStep
- `def Binius.RingSwitching.SumcheckPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1721](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1721) — Large-field reduction: Sumcheck seqCompose, then append FinalSum
- `def RingSwitching.SumcheckPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1579](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1579) — Large-field reduction: Sumcheck seqCompose, then append FinalSum

### `coreInteractionOracleVerifier` (4 declarations, 4 files)

- `def coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:1106](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L1106) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1634](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1634) — The final oracle verifier that composes sumcheckFold with finalSumcheckStep
- `def Binius.RingSwitching.SumcheckPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1712](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1712) — Large-field reduction verifier: Sumcheck seqCompose, then append FinalSum
- `def RingSwitching.SumcheckPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1543](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1543) — Large-field reduction verifier: Sumcheck seqCompose, then append FinalSum

### `disagreementSet` (4 declarations, 4 files)

- `def disagreementSet` [ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean:63](../../../ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean#L63) — The set D = Δ^{2m}(U, V), columns where U₀≠V₀ or U₁≠V₁. Specialisation of the canonical `Code.disagr
- `def Binius.BinaryBasefold.disagreementSet` [ArkLib/ProofSystem/Binius/BinaryBasefold/Code.lean:136](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Code.lean#L136) — Disagreement set Δ : The set of points where two functions disagree. For functions f^(i) and g^(i),
- `def Quotienting.disagreementSet` [ArkLib/ProofSystem/Stir/Quotienting.lean:121](../../../ArkLib/ProofSystem/Stir/Quotienting.lean#L121) — We define the set disagreementSet(f,ι,S,Ans) as the set of all points x ∈ ι that lie in S such that
- `def BlockRelDistance.disagreementSet` [ArkLib/ProofSystem/Whir/BlockRelDistance.lean:104](../../../ArkLib/ProofSystem/Whir/BlockRelDistance.lean#L104) — Let C be a smooth ReedSolomon code `C = RS[F, ι^(2ⁱ), φ', m]` and `f,g : ι^(2ⁱ) → F`, then the (i,k)

### `finalSumcheckKStateProp` (4 declarations, 4 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKStateProp` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:1668](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L1668) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKStateProp` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1355](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1355) — (no docstring)
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckKStateProp` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1494](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1494) — KState for the final sumcheck step, in the same style as BBF `finalSumcheckKStateProp`: m=0: same as
- `def RingSwitching.SumcheckPhase.finalSumcheckKStateProp` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1307](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1307) — (no docstring)

### `finalSumcheckKnowledgeStateFunction` (4 declarations, 4 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:1698](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L1698) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1395](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1395) — The knowledge state function for the final sumcheck step
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1522](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1522) — The knowledge state function for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1345](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1345) — The knowledge state function for the final sumcheck step

### `finalSumcheckOracleReduction` (4 declarations, 4 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:126](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L126) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:665](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L665) — The oracle reduction for the final sumcheck step
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1265](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1265) — The oracle reduction for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1185](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1185) — The oracle reduction for the final sumcheck step

### `finalSumcheckOracleVerifier_rbrKnowledgeSoundness` (4 declarations, 4 files)

- `theorem Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:1892](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L1892) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1607](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1607) — Round-by-round knowledge soundness for the final sumcheck step
- `theorem Binius.RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1660](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1660) — Round-by-round knowledge soundness for the final sumcheck step
- `theorem RingSwitching.SumcheckPhase.finalSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1476](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1476) — Round-by-round knowledge soundness for the final sumcheck step

### `finalSumcheckProver` (4 declarations, 4 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckProver` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:66](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L66) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckProver` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:607](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L607) — The prover for the final sumcheck step
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckProver` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1207](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1207) — The prover for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckProver` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1088](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1088) — The prover for the final sumcheck step

### `finalSumcheckRbrExtractor` (4 declarations, 4 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:1626](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L1626) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1317](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1317) — The round-by-round extractor for the final sumcheck step
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1471](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1471) — The round-by-round extractor for the final sumcheck step. We do not collapse the witness away (unlik
- `def RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1287](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1287) — The round-by-round extractor for the final sumcheck step

### `finalSumcheckVerifier` (4 declarations, 4 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:100](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L100) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:641](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L641) — The verifier for the final sumcheck step
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1238](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1238) — The verifier for the final sumcheck step
- `def RingSwitching.SumcheckPhase.finalSumcheckVerifier` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1124](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1124) — The verifier for the final sumcheck step

### `fullOracleProof` (4 declarations, 4 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:102](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L102) — The full Binary Basefold protocol as a Proof
- `def Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:171](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L171) — The full Binary Basefold protocol as a Proof
- `def Binius.RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:86](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L86) — The full Binary Basefold protocol as a Proof
- `def RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/RingSwitching/General.lean:96](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L96) — The full Binary Basefold protocol as a Proof

### `fullOracleReduction` (4 declarations, 4 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:74](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L74) — The reduction for the full Binary Basefold protocol
- `def Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:140](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L140) — The reduction for the full Binary Basefold protocol
- `def Binius.RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:74](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L74) — The reduction for the full Binary Basefold protocol
- `def RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/RingSwitching/General.lean:84](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L84) — The reduction for the full Binary Basefold protocol

### `fullOracleVerifier` (4 declarations, 4 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:51](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L51) — The oracle verifier for the full Binary Basefold protocol
- `def Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:114](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L114) — The oracle verifier for the full Binary Basefold protocol
- `def Binius.RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:56](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L56) — The oracle verifier for the full Binary Basefold protocol
- `def RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/RingSwitching/General.lean:60](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L60) — The oracle verifier for the full Binary Basefold protocol

### `fullOracleVerifier_rbrKnowledgeSoundness` (4 declarations, 4 files)

- `theorem Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:149](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L149) — Round-by-round knowledge soundness for the full Binary Basefold oracle verifier
- `theorem Binius.FRIBinius.FullFRIBinius.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:237](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L237) — Round-by-round knowledge soundness for the full FRI-Binius oracle verifier.
- `theorem Binius.RingSwitching.FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:204](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L204) — Round-by-round knowledge soundness for the full ring-switching oracle verifier
- `theorem RingSwitching.FullRingSwitching.fullOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/General.lean:226](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L226) — Round-by-round knowledge soundness for the full ring-switching oracle verifier. `IsDomain K` (with t

### `fullRbrKnowledgeError` (4 declarations, 4 files)

- `def Binius.BinaryBasefold.FullBinaryBasefold.fullRbrKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:139](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L139) — Combined RBR knowledge soundness error for the full protocol
- `def Binius.FRIBinius.FullFRIBinius.fullRbrKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:227](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L227) — Combined RBR knowledge error for full FRI-Binius.
- `def Binius.RingSwitching.FullRingSwitching.fullRbrKnowledgeError` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:197](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L197) — (no docstring)
- `def RingSwitching.FullRingSwitching.fullRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/General.lean:210](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L210) — (no docstring)

### `honestTranscriptDist_oracleReduction_evalDist` (4 declarations, 4 files)

- `theorem RandomQuery.honestTranscriptDist_oracleReduction_evalDist` [ArkLib/ProofSystem/Component/RandomQuery.lean:201](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L201) — The honest transcript distribution for `RandomQuery` is definitionally the simulator distribution.
- `theorem ReduceClaim.honestTranscriptDist_oracleReduction_evalDist` [ArkLib/ProofSystem/Component/ReduceClaim.lean:372](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L372) — The honest transcript distribution for the plain `ReduceClaim` oracle reduction is the deterministic
- `theorem SendClaim.honestTranscriptDist_oracleReduction_evalDist` [ArkLib/ProofSystem/Component/SendClaim.lean:254](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L254) — The honest transcript distribution for `SendClaim` is exactly the simulator distribution, because th
- `theorem SendSingleWitness.honestTranscriptDist_oracleReduction_evalDist` [ArkLib/ProofSystem/Component/SendWitness.lean:417](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L417) — The honest transcript distribution for `SendSingleWitness` is the deterministic one-message transcri

### `honestTranscriptDist_reduction_evalDist` (4 declarations, 4 files)

- `theorem CheckClaim.honestTranscriptDist_reduction_evalDist` [ArkLib/ProofSystem/Component/CheckClaim.lean:121](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L121) — The honest transcript distribution for a valid `CheckClaim` statement is the deterministic empty tra
- `theorem NoInteraction.honestTranscriptDist_reduction_evalDist` [ArkLib/ProofSystem/Component/NoInteraction.lean:256](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L256) — The honest transcript distribution for a no-interaction reduction is the deterministic empty transcr
- `theorem ReduceClaim.honestTranscriptDist_reduction_evalDist` [ArkLib/ProofSystem/Component/ReduceClaim.lean:116](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L116) — The honest transcript distribution for `ReduceClaim` is the deterministic empty transcript. The mapp
- `theorem SendWitness.honestTranscriptDist_reduction_evalDist` [ArkLib/ProofSystem/Component/SendWitness.lean:108](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L108) — The honest transcript distribution for `SendWitness` is the deterministic one-message transcript con

### `oracleVerifier_rbrKnowledgeSoundness` (4 declarations, 4 files)

- `theorem DoNothing.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/DoNothing.lean:132](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L132) — The `DoNothing` oracle verifier is perfectly round-by-round knowledge sound.
- `theorem RandomQuery.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/RandomQuery.lean:383](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L383) — The `RandomQuery` oracle reduction is round-by-round knowledge sound. The key fact governing the sou
- `theorem ReduceClaim.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:537](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L537) — The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness. Note that s
- `theorem Sumcheck.Spec.SingleRound.Simple.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1216](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1216) — Round-by-round knowledge soundness for the oracle verifier

### `reduction_completeness` (4 declarations, 4 files)

- `theorem CheckClaim.reduction_completeness` [ArkLib/ProofSystem/Component/CheckClaim.lean:71](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L71) — The `CheckClaim` reduction satisfies perfect completeness with respect to the predicate as the input
- `theorem NoInteraction.reduction_completeness` [ArkLib/ProofSystem/Component/NoInteraction.lean:199](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L199) — Completeness of a no-interaction reduction. **Faithfulness of the hypothesis `hRel`.** `Reduction.ru
- `theorem ReduceClaim.reduction_completeness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:69](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L69) — The `ReduceClaim` reduction satisfies perfect completeness for any relation.
- `theorem SendWitness.reduction_completeness` [ArkLib/ProofSystem/Component/SendWitness.lean:173](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L173) — The `SendWitness` reduction satisfies perfect completeness.

### `reduction_isHVZK` (4 declarations, 4 files)

- `theorem CheckClaim.reduction_isHVZK` [ArkLib/ProofSystem/Component/CheckClaim.lean:156](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L156) — `CheckClaim` has an explicit perfect-HVZK simulator.
- `theorem DoNothing.reduction_isHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:79](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L79) — The `DoNothing` reduction has an explicit perfect-HVZK simulator for any relation.
- `theorem NoInteraction.reduction_isHVZK` [ArkLib/ProofSystem/Component/NoInteraction.lean:315](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L315) — A no-interaction reduction has an explicit perfect-HVZK simulator for any input relation.
- `theorem ReduceClaim.reduction_isHVZK` [ArkLib/ProofSystem/Component/ReduceClaim.lean:153](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L153) — `ReduceClaim` has an explicit perfect-HVZK simulator for any input relation.

### `reduction_isStatHVZK` (4 declarations, 4 files)

- `theorem CheckClaim.reduction_isStatHVZK` [ArkLib/ProofSystem/Component/CheckClaim.lean:161](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L161) — `CheckClaim` has statistical HVZK at every error budget.
- `theorem DoNothing.reduction_isStatHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:85](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L85) — The `DoNothing` reduction has statistical HVZK for any relation and error budget.
- `theorem NoInteraction.reduction_isStatHVZK` [ArkLib/ProofSystem/Component/NoInteraction.lean:321](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L321) — A no-interaction reduction has statistical HVZK for any input relation and error budget.
- `theorem ReduceClaim.reduction_isStatHVZK` [ArkLib/ProofSystem/Component/ReduceClaim.lean:159](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L159) — `ReduceClaim` has statistical HVZK for any input relation and error budget.

### `reduction_perfectHVZK` (4 declarations, 4 files)

- `theorem CheckClaim.reduction_perfectHVZK` [ArkLib/ProofSystem/Component/CheckClaim.lean:142](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L142) — `CheckClaim` is perfectly HVZK for the predicate relation. The simulator is the identity transcript
- `theorem DoNothing.reduction_perfectHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:64](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L64) — The `DoNothing` reduction is perfectly HVZK for any relation.
- `theorem NoInteraction.reduction_perfectHVZK` [ArkLib/ProofSystem/Component/NoInteraction.lean:300](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L300) — A no-interaction reduction is perfectly HVZK for any input relation: it has no messages or challenge
- `theorem ReduceClaim.reduction_perfectHVZK` [ArkLib/ProofSystem/Component/ReduceClaim.lean:138](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L138) — `ReduceClaim` is perfectly HVZK for any input relation: it has no messages or challenges, so the ide

### `reduction_statisticalHVZK` (4 declarations, 4 files)

- `theorem CheckClaim.reduction_statisticalHVZK` [ArkLib/ProofSystem/Component/CheckClaim.lean:150](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L150) — Perfect HVZK implies statistical HVZK at every error budget.
- `theorem DoNothing.reduction_statisticalHVZK` [ArkLib/ProofSystem/Component/DoNothing.lean:71](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L71) — The `DoNothing` reduction is statistically HVZK for any relation and error budget.
- `theorem NoInteraction.reduction_statisticalHVZK` [ArkLib/ProofSystem/Component/NoInteraction.lean:308](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L308) — Perfect HVZK implies statistical HVZK for a no-interaction reduction at every error budget.
- `theorem ReduceClaim.reduction_statisticalHVZK` [ArkLib/ProofSystem/Component/ReduceClaim.lean:146](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L146) — Perfect HVZK implies statistical HVZK for `ReduceClaim` at every error budget.

### `simulateQ_simOracle2_messageQuery` (4 declarations, 4 files)

- `lemma Binius.RingSwitching.simulateQ_simOracle2_messageQuery` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:953](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L953) — **`simOracle2` message-query collapse (`OracleComp` form).** Simulating, via `simOracle2 oSpec t₁ t₂
- `lemma RingSwitching.BatchingPhase.simulateQ_simOracle2_messageQuery` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:59](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L59) — Local message-query collapse for `OracleInterface.simOracle2`.
- `lemma RingSwitching.simulateQ_simOracle2_messageQuery` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1416](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1416) — **`simOracle2` message-query collapse (`OracleComp` form).** Simulating, via `simOracle2 oSpec t₁ t₂
- `lemma ToyProblem.Spec.simulateQ_simOracle2_messageQuery` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:718](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L718) — `simOracle2` message-query collapse (`OracleComp` form), RIGHT (message) family.

### `prizeRates_le_half` (4 declarations, 4 files)

- `lemma ProximityGap.prizeRates_le_half` [ArkLib/Data/CodingTheory/ProximityGap/GrandChallengeDecision.lean:141](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallengeDecision.lean#L141) — Every prize rate is `≤ 1/2`.
- `lemma ProximityGap.GrandChallengesLattice.prizeRates_le_half` [ArkLib/Data/CodingTheory/ProximityGap/GrandChallengeInteriorJ1.lean:551](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallengeInteriorJ1.lean#L551) — Every ABF26 prize rate is at most `1/2`.
- `lemma ProximityGap.prizeRates_le_half` [ArkLib/Data/CodingTheory/ProximityGap/GrandChallengeLDFourRate.lean:208](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallengeLDFourRate.lean#L208) — Every ABF26 prize rate is at most `1/2`.
- `lemma ProximityGap.prizeRates_le_half` [ArkLib/Data/CodingTheory/ProximityGap/MCASecondMoment.lean:363](../../../ArkLib/Data/CodingTheory/ProximityGap/MCASecondMoment.lean#L363) — Every prize rate is at most `1/2`.

### `completeness` (6 declarations, 3 files)

- `abbrev DuplexSpongeFS.NARG.completeness` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:59](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L59) — Paper-facing alias for CO25 Section 3.4 completeness.
- `def Reduction.completeness` [ArkLib/OracleReduction/Security/Basic.lean:175](../../../ArkLib/OracleReduction/Security/Basic.lean#L175) — A reduction satisfies **completeness** with regards to: - an initialization function `init : ProbCom
- `def OracleReduction.completeness` [ArkLib/OracleReduction/Security/Basic.lean:521](../../../ArkLib/OracleReduction/Security/Basic.lean#L521) — Completeness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.completeness` [ArkLib/OracleReduction/Security/Basic.lean:575](../../../ArkLib/OracleReduction/Security/Basic.lean#L575) — (no docstring)
- `def OracleProof.completeness` [ArkLib/OracleReduction/Security/Basic.lean:604](../../../ArkLib/OracleReduction/Security/Basic.lean#L604) — Completeness of an oracle reduction is the same as for non-oracle reductions.
- `theorem SendClaim.completeness` [ArkLib/ProofSystem/Component/SendClaim.lean:114](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L114) — (no docstring)

### `soundness` (6 declarations, 3 files)

- `abbrev DuplexSpongeFS.NARG.soundness` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:72](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L72) — Paper-facing alias for CO25 Section 3.4 soundness.
- `def Verifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:353](../../../ArkLib/OracleReduction/Security/Basic.lean#L353) — A reduction satisfies **soundness** with error `soundnessError ≥ 0` and with respect to input langua
- `def OracleVerifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:542](../../../ArkLib/OracleReduction/Security/Basic.lean#L542) — Soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:585](../../../ArkLib/OracleReduction/Security/Basic.lean#L585) — (no docstring)
- `def OracleProof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:621](../../../ArkLib/OracleReduction/Security/Basic.lean#L621) — Soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Verifier.StateRestoration.soundness` [ArkLib/OracleReduction/Security/StateRestoration.lean:127](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L127) — State-restoration soundness

### `subdomain` (6 declarations, 3 files)

- `def ReedSolomon.FftDomain.subdomain` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:806](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L806) — Given a smooth FFT domain `ω` of log-order `n` this function returns its subdomain of log-order `i`.
- `def ReedSolomon.CosetFftDomain.subdomain` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1371](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1371) — Given a smooth coset FFT domain `ω` of log-order `n` returns a subdomain of log-order `i`.
- `def Domain.CosetFftDomainClass.subdomain` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:88](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L88) — Given a smooth coset FFT domain `ω` of log-order `n` this function returns its subdomain of log-orde
- `abbrev Domain.CosetFftDomain.subdomain` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:449](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L449) — (no docstring)
- `def Domain.FftDomainClass.subdomain` [ArkLib/Data/Domain/FftDomain/Subdomain.lean:44](../../../ArkLib/Data/Domain/FftDomain/Subdomain.lean#L44) — (no docstring)
- `abbrev Domain.FftDomain.subdomain` [ArkLib/Data/Domain/FftDomain/Subdomain.lean:134](../../../ArkLib/Data/Domain/FftDomain/Subdomain.lean#L134) — (no docstring)

### `toList` (6 declarations, 3 files)

- `def ReedSolomon.FftDomain.toList` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:287](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L287) — Convert an FFT domain into a list of all its members with proofs the members belong to the FFT domai
- `def ReedSolomon.CosetFftDomain.toList` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:614](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L614) — (no docstring)
- `def Domain.CosetFftDomainClass.toList` [ArkLib/Data/Domain/CosetFftDomain/ToList.lean:37](../../../ArkLib/Data/Domain/CosetFftDomain/ToList.lean#L37) — (no docstring)
- `def Domain.CosetFftDomain.toList` [ArkLib/Data/Domain/CosetFftDomain/ToList.lean:52](../../../ArkLib/Data/Domain/CosetFftDomain/ToList.lean#L52) — Convert a coset FFT domain into a list of all its members with proofs the members belong to the FFT
- `def Domain.FftDomain.toList` [ArkLib/Data/Domain/CosetFftDomain/ToList.lean:63](../../../ArkLib/Data/Domain/CosetFftDomain/ToList.lean#L63) — Convert a FFT domain into a list of all its members with proofs the members belong to the FFT domain
- `def ProtocolSpec.EncodedMessagesBefore.toList` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:77](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L77) — Flatten to a sigma-list for consumers still expecting `List (Sigma ...)`.

### `ratchet` (5 declarations, 3 files)

- `def DomainSeparator.ratchet` [ArkLib/Data/Hash/DomainSep.lean:255](../../../ArkLib/Data/Hash/DomainSep.lean#L255) — Ratchet the state. Rust interface: ```rust pub fn ratchet(self) -> Self ```
- `def DuplexSponge.ratchet` [ArkLib/Data/Hash/DuplexSponge.lean:612](../../../ArkLib/Data/Hash/DuplexSponge.lean#L612) — ### Ratchet the sponge state for domain separation Algorithm (from Rust implementation): 1. Permute
- `def HashStateWithInstructions.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:217](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L217) — Perform a ratchet operation. Rust interface: ```rust pub fn ratchet(&mut self) -> Result<(), DomainS
- `def FSVerifierState.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:348](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L348) — Signal the end of statement with ratcheting. Rust interface: ```rust pub fn ratchet(&mut self) -> Re
- `def FSProverState.ratchet` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:459](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L459) — Ratchet the protocol state. Rust interface: ```rust pub fn ratchet(&mut self) -> Result<(), DomainSe

### `Adversary` (4 declarations, 3 files)

- `def AGM.Adversary` [ArkLib/AGM/Basic.lean:468](../../../ArkLib/AGM/Basic.lean#L468) — An adversary in the Algebraic Group Model (AGM) is defined as follows: - It is given knowledge of th
- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.Adversary` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean:92](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean#L92) — A weak-binding adversary outputs two weak openings for the same commitment.
- `abbrev ArkLib.Lattices.SIS.Adversary` [ArkLib/Data/Lattices/ModuleSIS.lean:53](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L53) — A search adversary for a SIS-style problem.
- `abbrev ArkLib.Lattices.ModuleSIS.Adversary` [ArkLib/Data/Lattices/ModuleSIS.lean:96](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L96) — A Module-SIS adversary.

### `OStmtIn` (4 declarations, 3 files)

- `def RandomQuery.OStmtIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:35](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L35) — (no docstring)
- `def Logup.OStmtIn` [ArkLib/ProofSystem/Logup/Common.lean:241](../../../ArkLib/ProofSystem/Logup/Common.lean#L241) — Input oracle statements: the table `t` and lookup columns `fᵢ`, as multilinear oracles.
- `def Sumcheck.Spec.SingleRound.Simpler.OStmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:336](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L336) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.OStmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:591](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L591) — (no docstring)

### `OStmtOut` (4 declarations, 3 files)

- `def RandomQuery.OStmtOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:36](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L36) — (no docstring)
- `def Logup.OStmtOut` [ArkLib/ProofSystem/Logup/Common.lean:290](../../../ArkLib/ProofSystem/Logup/Common.lean#L290) — Output oracle statements for the full LogUp protocol.
- `def Sumcheck.Spec.SingleRound.Simpler.OStmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:365](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L365) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.OStmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:594](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L594) — (no docstring)

### `StmtOut` (4 declarations, 3 files)

- `def RandomQuery.StmtOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:33](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L33) — (no docstring)
- `def Logup.StmtOut` [ArkLib/ProofSystem/Logup/Common.lean:280](../../../ArkLib/ProofSystem/Logup/Common.lean#L280) — The full LogUp protocol returns no additional public data on success.
- `def Sumcheck.Spec.SingleRound.Simpler.StmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:364](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L364) — (no docstring)
- `def Sumcheck.Spec.SingleRound.Simple.StmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:588](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L588) — (no docstring)

### `append` (4 declarations, 3 files)

- `def AGM.GroupRepresentation.append` [ArkLib/AGM/RepresentationLemmas.lean:164](../../../ArkLib/AGM/RepresentationLemmas.lean#L164) — **Representations compose multiplicatively.** Concatenating the bases and exponent vectors of two al
- `def Interaction.Oracle.Spec.append` [ArkLib/Interaction/Oracle/Spec.lean:216](../../../ArkLib/Interaction/Oracle/Spec.lean#L216) — (no docstring)
- `abbrev ProtocolSpec.append` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:49](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L49) — Appending two `ProtocolSpec`s
- `def ProtocolSpec.FullTranscript.append` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:160](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L160) — Appending two transcripts for two `ProtocolSpec`s

### `correctness` (4 declarations, 3 files)

- `def Commitment.correctness` [ArkLib/CommitmentScheme/Basic.lean:88](../../../ArkLib/CommitmentScheme/Basic.lean#L88) — A commitment scheme satisfies **correctness** with error `correctnessError` if for all `data : Data`
- `def CommitmentScheme.correctness` [ArkLib/CommitmentScheme/CommitmentScheme.lean:64](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L64) — A commitment scheme satisfies **correctness** with error `correctnessError` if, for every message, t
- `theorem KZG.correctness` [ArkLib/CommitmentScheme/KZG/Correctness.lean:51](../../../ArkLib/CommitmentScheme/KZG/Correctness.lean#L51) — Algebraic correctness of one KZG opening for a coefficient vector.
- `theorem KZG.CommitmentScheme.correctness` [ArkLib/CommitmentScheme/KZG/Correctness.lean:161](../../../ArkLib/CommitmentScheme/KZG/Correctness.lean#L161) — The KZG scheme satisfies perfect correctness as defined in `CommitmentScheme`.

### `drop` (4 declarations, 3 files)

- `def Fin.drop` [ArkLib/Data/Fin/Tuple/Defs.lean:60](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L60) — Drop the first `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple.
- `def ProtocolSpec.drop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:129](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L129) — Drop the first `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.drop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:186](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L186) — (no docstring)
- `def SumcheckDomain.drop` [ArkLib/ProofSystem/Sumcheck/Domain.lean:133](../../../ArkLib/ProofSystem/Sumcheck/Domain.lean#L133) — Drop the first `j` coordinates, leaving the domain on the remaining `k - j` coordinates: coordinate

### `injOn` (4 declarations, 3 files)

- `lemma ReedSolomon.FftDomain.injOn` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:345](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L345) — (no docstring)
- `lemma ReedSolomon.CosetFftDomain.injOn` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:646](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L646) — (no docstring)
- `lemma Domain.CosetFftDomain.injOn` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:233](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L233) — (no docstring)
- `lemma Domain.FftDomain.injOn` [ArkLib/Data/Domain/FftDomain/Defs.lean:116](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L116) — (no docstring)

### `injective` (4 declarations, 3 files)

- `lemma ReedSolomon.FftDomain.injective` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:340](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L340) — (no docstring)
- `lemma ReedSolomon.CosetFftDomain.injective` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:639](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L639) — (no docstring)
- `lemma Domain.CosetFftDomain.injective` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:228](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L228) — (no docstring)
- `lemma Domain.FftDomain.injective` [ArkLib/Data/Domain/FftDomain/Defs.lean:112](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L112) — (no docstring)

### `reduction_perfectCompleteness` (4 declarations, 3 files)

- `theorem DoNothing.reduction_perfectCompleteness` [ArkLib/ProofSystem/Component/DoNothing.lean:52](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L52) — The `DoNothing` reduction satisfies perfect completeness for any relation.
- `theorem Fri.Spec.Completeness.reduction_perfectCompleteness` [ArkLib/ProofSystem/Fri/Spec/Completeness.lean:111](../../../ArkLib/ProofSystem/Fri/Spec/Completeness.lean#L111) — **Brick D — composed FRI reduction perfect completeness.** The honest FRI protocol is perfectly comp
- `theorem Sumcheck.Spec.SingleRound.Simple.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:742](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L742) — Perfect completeness for the (non-oracle) reduction
- `theorem Sumcheck.Spec.SingleRound.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1780](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1780) — (no docstring)

### `Message` (3 declarations, 3 files)

- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.Message` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean:122](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean#L122) — Messages: block vectors over the message row space.
- `abbrev ArkLib.Lattices.Ajtai.Simple.Message` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:32](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L32) — Messages: column vectors over `Rq Φ`.
- `def ProtocolSpec.Message` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:78](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L78) — The type of the `i`-th message in a protocol specification. This does not distinguish between messag

### `Opening` (3 declarations, 3 files)

- `structure ArkLib.Lattices.Ajtai.InnerOuter.Opening` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean:98](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean#L98) — A Hachi/Greyhound *weak opening* `(sᵢ, t̂ᵢ, cᵢ)ᵢ`: the decomposition data `(sᵢ, t̂ᵢ)` (`Decomp`) ext
- `abbrev ArkLib.Lattices.Ajtai.Simple.Opening` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:43](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L43) — The simple Ajtai commitment has no auxiliary opening data.
- `structure Commitment.Opening` [ArkLib/CommitmentScheme/Basic.lean:59](../../../ArkLib/CommitmentScheme/Basic.lean#L59) — The opening protocol used to prove a claimed oracle response for committed data.

### `OutputStatement` (3 declarations, 3 files)

- `abbrev Sumcheck.Spec.OutputStatement` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:131](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L131) — (no docstring)
- `def ToyProblem.Spec.OutputStatement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:112](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L112) — Output statement: the IOR is a yes/no test — accept (return `()`) or short-circuit to `none` via `Op
- `def ToyProblem.SimplifiedIOR.OutputStatement` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:72](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L72) — Output statement for C6.9: the new `(v, μ_new)` pair. The constraint count drops from 2 to 1 (a sing

### `Params` (3 declarations, 3 files)

- `structure Poseidon2.Params` [ArkLib/Data/Hash/Poseidon2.lean:412](../../../ArkLib/Data/Hash/Poseidon2.lean#L412) — The parameters determining a Poseidon2 permutation (over the KoalaBear field)
- `structure StirIOP.Params` [ArkLib/ProofSystem/Stir/MainThm.lean:35](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L35) — **Per‑round protocol parameters:** For a fixed depth `M`, the reduction runs `M + 1` rounds. In roun
- `structure WhirIOP.Params` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:54](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L54) — ** Per‑round protocol parameters. ** For a fixed depth `M`, the reduction runs `M + 1` rounds. In ro

### `Prover` (4 declarations, 3 files)

- `abbrev Interaction.Oracle.Prover` [ArkLib/Interaction/Oracle/Core.lean:1140](../../../ArkLib/Interaction/Oracle/Core.lean#L1140) — (no docstring)
- `abbrev Interaction.Prover` [ArkLib/Interaction/Reduction.lean:115](../../../ArkLib/Interaction/Reduction.lean#L115) — (no docstring)
- `structure Prover` [ArkLib/OracleReduction/Basic.lean:168](../../../ArkLib/OracleReduction/Basic.lean#L168) — (no docstring)
- `structure Prover` [ArkLib/OracleReduction/Basic.lean:413](../../../ArkLib/OracleReduction/Basic.lean#L413) — The type of honest provers for an interactive reduction with `n` messages. This consists of: - `PrvS

### `PublicParams` (3 declarations, 3 files)

- `structure ArkLib.Lattices.Ajtai.InnerOuter.PublicParams` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean:77](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean#L77) — Public parameters: inner Ajtai matrix `A` and outer Ajtai matrix `B`.
- `abbrev ArkLib.Lattices.Ajtai.Simple.PublicParams` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:29](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L29) — Public parameters: the Ajtai matrix `A`.
- `structure Spartan.PublicParams` [ArkLib/ProofSystem/Spartan/Basic.lean:26](../../../ArkLib/ProofSystem/Spartan/Basic.lean#L26) — The public parameters of the (padded) Spartan protocol. Consists of the number of bits of the R1CS d

### `Reduction` (3 declarations, 3 files)

- `structure Interaction.Oracle.Reduction` [ArkLib/Interaction/Oracle/Core.lean:1217](../../../ArkLib/Interaction/Oracle/Core.lean#L1217) — (no docstring)
- `structure Interaction.Reduction` [ArkLib/Interaction/Reduction.lean:187](../../../ArkLib/Interaction/Reduction.lean#L187) — (no docstring)
- `structure Reduction` [ArkLib/OracleReduction/Basic.lean:698](../../../ArkLib/OracleReduction/Basic.lean#L698) — An **interactive reduction** for a given protocol specification `pSpec`, and relative to oracles def

### `StraightlineExtractor` (3 declarations, 3 files)

- `abbrev Commitment.StraightlineExtractor` [ArkLib/CommitmentScheme/Basic.lean:178](../../../ArkLib/CommitmentScheme/Basic.lean#L178) — A **straightline extractor** for a commitment scheme takes in the commitment, the log of queries mad
- `def CommitmentScheme.StraightlineExtractor` [ArkLib/CommitmentScheme/CommitmentScheme.lean:123](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L123) — A **straightline extractor** for a standard commitment scheme takes the commitment and the log of qu
- `abbrev DuplexSpongeFS.NARG.StraightlineExtractor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:86](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L86) — Paper-facing alias for the straightline extractor interface used in Section 3.4.

### `SumcheckWitness` (3 declarations, 3 files)

- `abbrev Binius.RingSwitching.SumcheckWitness` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:226](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L226) — (no docstring)
- `abbrev RingSwitching.SumcheckWitness` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:237](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L237) — (no docstring)
- `structure Sumcheck.Structured.SumcheckWitness` [ArkLib/ProofSystem/Sumcheck/Structured.lean:231](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L231) — Witness for the structured sumcheck at round `i`: - `t'` — the original multilinear polynomial (the

### `Verifier` (3 declarations, 3 files)

- `structure Interaction.Oracle.Verifier` [ArkLib/Interaction/Oracle/Core.lean:1180](../../../ArkLib/Interaction/Oracle/Core.lean#L1180) — (no docstring)
- `abbrev Interaction.Verifier` [ArkLib/Interaction/Reduction.lean:130](../../../ArkLib/Interaction/Reduction.lean#L130) — (no docstring)
- `structure Verifier` [ArkLib/OracleReduction/Basic.lean:438](../../../ArkLib/OracleReduction/Basic.lean#L438) — A verifier of an interactive protocol is a function that takes in the input statement and the transc

### `absorb` (3 declarations, 3 files)

- `def DomainSeparator.absorb` [ArkLib/Data/Hash/DomainSep.lean:216](../../../ArkLib/Data/Hash/DomainSep.lean#L216) — Absorb `count` native elements. Rust interface: ```rust pub fn absorb(self, count: usize, label: &st
- `def DuplexSponge.absorb` [ArkLib/Data/Hash/DuplexSponge.lean:416](../../../ArkLib/Data/Hash/DuplexSponge.lean#L416) — ### Absorb a list of units into the sponge (paper version) Paper algorithm (process one element at a
- `def HashStateWithInstructions.absorb` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:110](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L110) — Perform secure absorption of elements into the sponge. Rust interface: ```rust pub fn absorb(&mut se

### `badPolyAgreement` (3 declarations, 3 files)

- `def Issue19Scratch.badPolyAgreement` [ArkLib/ProofSystem/RingSwitching/BadPolyAgreementCount.lean:29](../../../ArkLib/ProofSystem/RingSwitching/BadPolyAgreementCount.lean#L29) — The bad event tolerated by the weakened sum-check KState at one round: the prover message `p` differ
- `def Issue29Ring.badPolyAgreement` [ArkLib/ProofSystem/RingSwitching/TraceTensorAlgebra.lean:40](../../../ArkLib/ProofSystem/RingSwitching/TraceTensorAlgebra.lean#L40) — **Named per-round residual = the weakened-KState bad event.** The prover message `p` differs from th
- `def KStateWeaken.badPolyAgreement` [ArkLib/ToMathlib/KStateWeaken.lean:70](../../../ArkLib/ToMathlib/KStateWeaken.lean#L70) — **Named per-round residual (weakened KState surface).** `badPolyAgreement r p q` is the bad event to

### `batchingCoreRbrKnowledgeError` (3 declarations, 3 files)

- `def Binius.FRIBinius.FullFRIBinius.batchingCoreRbrKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:217](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L217) — Combined RBR knowledge error for batching + core interaction.
- `def Binius.RingSwitching.FullRingSwitching.batchingCoreRbrKnowledgeError` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:191](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L191) — (no docstring)
- `def RingSwitching.FullRingSwitching.batchingCoreRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/General.lean:204](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L204) — (no docstring)

### `batchingCoreReduction` (3 declarations, 3 files)

- `def Binius.FRIBinius.FullFRIBinius.batchingCoreReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:95](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L95) — (no docstring)
- `def Binius.RingSwitching.FullRingSwitching.batchingCoreReduction` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:63](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L63) — (no docstring)
- `def RingSwitching.FullRingSwitching.batchingCoreReduction` [ArkLib/ProofSystem/RingSwitching/General.lean:66](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L66) — (no docstring)

### `batchingCoreVerifier` (3 declarations, 3 files)

- `def Binius.FRIBinius.FullFRIBinius.batchingCoreVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:77](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L77) — (no docstring)
- `def Binius.RingSwitching.FullRingSwitching.batchingCoreVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:46](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L46) — (no docstring)
- `def RingSwitching.FullRingSwitching.batchingCoreVerifier` [ArkLib/ProofSystem/RingSwitching/General.lean:42](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L42) — (no docstring)

### `binding` (3 declarations, 3 files)

- `def Commitment.binding` [ArkLib/CommitmentScheme/Basic.lean:170](../../../ArkLib/CommitmentScheme/Basic.lean#L170) — A commitment scheme satisfies **(evaluation) binding** with error `bindingError` if for all adversar
- `def CommitmentScheme.binding` [ArkLib/CommitmentScheme/CommitmentScheme.lean:104](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L104) — A commitment scheme satisfies **binding** with error `bindingError` if every adversary's probability
- `theorem KZG.CommitmentScheme.binding` [ArkLib/CommitmentScheme/KZG/Binding.lean:737](../../../ArkLib/CommitmentScheme/KZG/Binding.lean#L737) — The KZG scheme satisfies evaluation binding provided `t`-SDH holds.

### `card_filter_eval_eq_le_natDegree` (3 declarations, 3 files)

- `theorem Issue19Scratch.card_filter_eval_eq_le_natDegree` [ArkLib/ProofSystem/RingSwitching/BadPolyAgreementCount.lean:35](../../../ArkLib/ProofSystem/RingSwitching/BadPolyAgreementCount.lean#L35) — **Root-counting core.** For distinct `p q`, the challenges at which they agree number at most `natDe
- `theorem Issue29Ring.card_filter_eval_eq_le_natDegree` [ArkLib/ProofSystem/RingSwitching/TraceTensorAlgebra.lean:48](../../../ArkLib/ProofSystem/RingSwitching/TraceTensorAlgebra.lean#L48) — **Root-counting core (Schwartz–Zippel, finite-field form).** For two distinct polynomials, the set o
- `theorem KStateWeaken.card_filter_eval_eq_le_natDegree` [ArkLib/ToMathlib/KStateWeaken.lean:91](../../../ArkLib/ToMathlib/KStateWeaken.lean#L91) — **Root-counting core (CompPoly-free).** For two *distinct* polynomials, the set of challenges on whi

### `coeff_pow_sub_at` (3 declarations, 3 files)

- `theorem ProximityPrize.HenselExistence.coeff_pow_sub_at` [ArkLib/Data/Polynomial/HenselExistence.lean:88](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L88) — Local copy of `NewtonLinearization.coeff_pow_sub_at` (order-`t` Newton linearization).
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_pow_sub_at` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:93](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L93) — **LEMMA B (Newton power linearization).** Local copy of `NewtonLinearization.coeff_pow_sub_at`.
- `theorem ProximityPrize.NewtonLinearization.coeff_pow_sub_at` [ArkLib/Data/Polynomial/NewtonLinearization.lean:97](../../../ArkLib/Data/Polynomial/NewtonLinearization.lean#L97) — **Newton linearization at order `t`.** Under the below-`t` agreement hypothesis with `0 < t`, writin

### `coeff_pow_sub_below` (3 declarations, 3 files)

- `theorem ProximityPrize.HenselExistence.coeff_pow_sub_below` [ArkLib/Data/Polynomial/HenselExistence.lean:71](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L71) — Local copy of `NewtonLinearization.coeff_pow_sub_below` (truncation propagation).
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_pow_sub_below` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:75](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L75) — **LEMMA A (truncation propagation).** Agreement below order `t` propagates to every power. Local cop
- `theorem ProximityPrize.NewtonLinearization.coeff_pow_sub_below` [ArkLib/Data/Polynomial/NewtonLinearization.lean:61](../../../ArkLib/Data/Polynomial/NewtonLinearization.lean#L61) — **Truncation propagation.** If `γ₁ γ₂ : R⟦X⟧` agree at every coefficient `j < t`, then so do `γ₁^i`

### `commit` (3 declarations, 3 files)

- `def ArkLib.Lattices.Ajtai.Simple.commit` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:38](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L38) — Deterministically commit by multiplying the public matrix by the message vector.
- `def KZG.commit` [ArkLib/CommitmentScheme/KZG/Basic.lean:55](../../../ArkLib/CommitmentScheme/KZG/Basic.lean#L55) — To commit to an `n + 1`-tuple of coefficients `coeffs` (corresponding to a polynomial of maximum deg
- `def SimpleRO.commit` [ArkLib/CommitmentScheme/SimpleRO.lean:43](../../../ArkLib/CommitmentScheme/SimpleRO.lean#L43) — (no docstring)

### `commitmentScheme` (3 declarations, 3 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.commitmentScheme` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean:200](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean#L200) — The inner-outer Ajtai commitment as a `CommitmentScheme`, verified with the Hachi/Greyhound weak ver
- `def ArkLib.Lattices.Ajtai.Simple.commitmentScheme` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:56](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L56) — The simple Ajtai commitment as a `CommitmentScheme`. An opening is accepted only when the message sa
- `def SimpleRO.commitmentScheme` [ArkLib/CommitmentScheme/SimpleRO.lean:83](../../../ArkLib/CommitmentScheme/SimpleRO.lean#L83) — (no docstring)

### `epsMCA_le_one` (3 declarations, 3 files)

- `theorem ProximityGap.epsMCA_le_one` [ArkLib/Data/CodingTheory/ProximityGap/Errors.lean:316](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean#L316) — The MCA error is bounded by the total probability mass.
- `theorem ProximityGap.MCAGS.epsMCA_le_one` [ArkLib/Data/CodingTheory/ProximityGap/GrandChallenge141PrizeMath.lean:92](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallenge141PrizeMath.lean#L92) — **The abstract MCA error is a probability ceiling: `ε_mca ≤ 1`.** (Companion to `epsMCAgs_le_one`; t
- `theorem CodingTheory.Bridge.epsMCA_le_one` [ArkLib/ToMathlib/BridgeListDecodingCA.lean:77](../../../ArkLib/ToMathlib/BridgeListDecodingCA.lean#L77) — **`ε_mca ≤ 1`.** The mutual-correlated-agreement error is a supremum of PMF probabilities, hence at

### `finSumFinEquiv_symm_dite` (3 declarations, 3 files)

- `theorem RingSwitching.finSumFinEquiv_symm_dite` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1533](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1533) — Value-form of `finSumFinEquiv.symm`: classify the index by whether its value is `< m`.
- `theorem ScratchRS.finSumFinEquiv_symm_dite` [ArkLib/ProofSystem/RingSwitching/Scratch.lean:28](../../../ArkLib/ProofSystem/RingSwitching/Scratch.lean#L28) — (no docstring)
- `theorem finSumFinEquiv_symm_dite` [ArkLib/ToMathlib/FinSumMvPolyBricks.lean:24](../../../ArkLib/ToMathlib/FinSumMvPolyBricks.lean#L24) — Value-form classification of `finSumFinEquiv.symm`.

### `finalSumcheckKnowledgeError` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:318](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L318) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1306](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1306) — RBR knowledge error for the final sumcheck step
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1463](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1463) — RBR knowledge error for the final sumcheck step

### `finalSumcheckOracleReduction_perfectCompleteness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.CoreInteraction.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:141](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L141) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1126](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1126) — Perfect completeness for the final sumcheck step
- `theorem Binius.RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1279](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1279) — Perfect completeness for the final sumcheck step

### `finalSumcheckStepLogic` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.CoreInteraction.finalSumcheckStepLogic` [ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:899](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean#L899) — The Logic Instance for the final sumcheck step. This is a 1-message protocol where the prover sends
- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckStepLogic` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:574](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L574) — The logic instance for the FRI final sumcheck step.
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckStepLogic` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1000](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1000) — The Logic Instance for the final sumcheck step. This is a 1-message protocol where the prover sends

### `finalSumcheckStep_is_logic_complete` (3 declarations, 3 files)

- `lemma Binius.BinaryBasefold.CoreInteraction.finalSumcheckStep_is_logic_complete` [ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:1355](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean#L1355) — Final sumcheck step logic is strongly complete. **Key Proof Obligations:** 1. **Verifier Check**: Sh
- `lemma Binius.FRIBinius.CoreInteractionPhase.finalSumcheckStep_is_logic_complete` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1073](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1073) — Strong completeness of the FRI final sumcheck logic step.
- `lemma Binius.RingSwitching.SumcheckPhase.finalSumcheckStep_is_logic_complete` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1155](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1155) — Final sumcheck step logic is strongly complete. **Key Proof Obligations:** 1. **Verifier Check**: Sh

### `finalSumcheckStep_verifierCheck_passed` (3 declarations, 3 files)

- `lemma Binius.BinaryBasefold.CoreInteraction.finalSumcheckStep_verifierCheck_passed` [ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:1212](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean#L1212) — The verifier check passes in the final sumcheck step. **Proof structure:** 1. From `sumcheckConsiste
- `lemma Binius.FRIBinius.CoreInteractionPhase.finalSumcheckStep_verifierCheck_passed` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:988](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L988) — Verifier check passes in the FRI final sumcheck logic step.
- `lemma Binius.RingSwitching.SumcheckPhase.finalSumcheckStep_verifierCheck_passed` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1093](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1093) — **Main helper lemma**: The verifier check passes in the final sumcheck step. **Proof Structure** (fo

### `fullOracleReduction_perfectCompleteness` (3 declarations, 3 files)

- `theorem Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:117](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L117) — Perfect completeness for the full Binary Basefold protocol (reduction)
- `theorem Binius.FRIBinius.FullFRIBinius.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:191](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L191) — Perfect completeness for the full Binary Basefold protocol (reduction)
- `theorem Binius.RingSwitching.FullRingSwitching.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:147](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L147) — (no docstring)

### `fullPspec` (3 declarations, 3 files)

- `def Binius.FRIBinius.FullFRIBinius.fullPspec` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:54](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L54) — (no docstring)
- `def Binius.RingSwitching.fullPspec` [ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean:73](../../../ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean#L73) — (no docstring)
- `def RingSwitching.fullPspec` [ArkLib/ProofSystem/RingSwitching/Spec.lean:57](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L57) — (no docstring)

### `knowledgeStateFunction` (3 declarations, 3 files)

- `def CheckClaim.knowledgeStateFunction` [ArkLib/ProofSystem/Component/CheckClaim.lean:174](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L174) — The knowledge state function for the `CheckClaim` reduction. Since there is no challenge round, the
- `def RandomQuery.knowledgeStateFunction` [ArkLib/ProofSystem/Component/RandomQuery.lean:338](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L338) — The knowledge state function for the `RandomQuery` oracle reduction.
- `def ReduceClaim.knowledgeStateFunction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:192](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L192) — The knowledge state function for the `ReduceClaim` reduction.

### `masterKStateProp` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.masterKStateProp` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:1399](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L1399) — Before V's challenge of the `i-th` foldStep, we ignore the bad-folding-event of the `i-th` oracle if
- `def Binius.RingSwitching.masterKStateProp` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:430](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L430) — (no docstring)
- `def RingSwitching.masterKStateProp` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:446](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L446) — (no docstring)

### `oracleReduction_completeness` (3 declarations, 3 files)

- `theorem RandomQuery.oracleReduction_completeness` [ArkLib/ProofSystem/Component/RandomQuery.lean:119](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L119) — The `RandomQuery` oracle reduction is perfectly complete.
- `theorem ReduceClaim.oracleReduction_completeness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:293](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L293) — The `ReduceClaim` oracle reduction satisfies perfect completeness for any relation. Proof strategy m
- `theorem SendSingleWitness.oracleReduction_completeness` [ArkLib/ProofSystem/Component/SendWitness.lean:545](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L545) — The `SendSingleWitness` oracle reduction satisfies perfect completeness.

### `oracleReduction_perfectCompleteness` (3 declarations, 3 files)

- `theorem DoNothing.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Component/DoNothing.lean:126](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L126) — The `DoNothing` oracle reduction satisfies perfect completeness for any relation.
- `theorem Sumcheck.Spec.SingleRound.Simple.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1033](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1033) — Perfect completeness for the oracle reduction
- `theorem ToyProblem.Spec.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:945](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L945) — **Honest completeness for Construction 6.2** (protocol-level form). The honest oracle reduction is p

### `pSpecCoreInteraction` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.pSpecCoreInteraction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean:248](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean#L248) — (no docstring)
- `def Binius.RingSwitching.pSpecCoreInteraction` [ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean:67](../../../ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean#L67) — (no docstring)
- `def RingSwitching.pSpecCoreInteraction` [ArkLib/ProofSystem/RingSwitching/Spec.lean:50](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L50) — (no docstring)

### `pSpecSumcheckRound` (3 declarations, 3 files)

- `abbrev Binius.RingSwitching.pSpecSumcheckRound` [ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean:58](../../../ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean#L58) — (no docstring)
- `abbrev RingSwitching.pSpecSumcheckRound` [ArkLib/ProofSystem/RingSwitching/Spec.lean:41](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L41) — (no docstring)
- `def Sumcheck.Structured.pSpecSumcheckRound` [ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean:256](../../../ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L256) — Protocol spec for one round of the structured sumcheck: P sends a degree-≤`d` univariate `h_i(X) ∈ L

### `relOut` (3 declarations, 3 files)

- `def CheckClaim.relOut` [ArkLib/ProofSystem/Component/CheckClaim.lean:64](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L64) — (no docstring)
- `def RandomQuery.relOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:51](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L51) — The output relation states that if the verifier's single query was `q`, then `a` and `b` agree on th
- `def SendClaim.relOut` [ArkLib/ProofSystem/Component/SendClaim.lean:102](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L102) — (no docstring)

### `rename_finCongr_heq` (3 declarations, 3 files)

- `lemma RingSwitching.SumcheckPhase.rename_finCongr_heq` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:294](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L294) — Renaming a polynomial along the canonical index `finCongr` of a (propositional) dimension equality `
- `lemma Sumcheck.Structured.rename_finCongr_heq` [ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean:140](../../../ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L140) — Renaming a polynomial along the canonical index `finCongr` of a dimension equality is heterogeneousl
- `theorem MvPolynomial.rename_finCongr_heq` [ArkLib/ToMathlib/ExtractedIssueBricks.lean:46](../../../ArkLib/ToMathlib/ExtractedIssueBricks.lean#L46) — Renaming along the canonical `finCongr` of a dimension equality is heterogeneously equal to the orig

### `simulateQ_simOracle2_query` (3 declarations, 3 files)

- `lemma Binius.RingSwitching.simulateQ_simOracle2_query` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:975](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L975) — **`simOracle2` message-query collapse (`OptionT`-`query` form).** The same reduction as `simulateQ_s
- `lemma RingSwitching.BatchingPhase.simulateQ_simOracle2_query` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:77](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L77) — OptionT/query form of `simulateQ_simOracle2_messageQuery`.
- `lemma RingSwitching.simulateQ_simOracle2_query` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1438](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1438) — **`simOracle2` message-query collapse (`OptionT`-`query` form).** The same reduction as `simulateQ_s

### `squeeze` (3 declarations, 3 files)

- `def DomainSeparator.squeeze` [ArkLib/Data/Hash/DomainSep.lean:241](../../../ArkLib/Data/Hash/DomainSep.lean#L241) — Squeeze `count` native elements. Rust interface: ```rust pub fn squeeze(self, count: usize, label: &
- `def DuplexSponge.squeeze` [ArkLib/Data/Hash/DuplexSponge.lean:512](../../../ArkLib/Data/Hash/DuplexSponge.lean#L512) — ### Squeeze out a vector of units from the sponge (paper version) We differ from the paper version i
- `def HashStateWithInstructions.squeeze` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:149](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L149) — Perform a secure squeeze operation. Rust interface: ```rust pub fn squeeze(&mut self, output: &mut [

### `toVerifier` (3 declarations, 3 files)

- `def Interaction.OracleDecoration.OracleReduction.toVerifier` [ArkLib/Interaction/Oracle/Core.lean:1096](../../../ArkLib/Interaction/Oracle/Core.lean#L1096) — (no docstring)
- `def Interaction.PublicCoinVerifier.toVerifier` [ArkLib/Interaction/Reduction.lean:162](../../../ArkLib/Interaction/Reduction.lean#L162) — (no docstring)
- `def OracleVerifier.toVerifier` [ArkLib/OracleReduction/Basic.lean:553](../../../ArkLib/OracleReduction/Basic.lean#L553) — An oracle verifier can be seen as a (non-oracle) verifier by providing the oracle interface using it

### `transcriptSimulator` (3 declarations, 3 files)

- `def RandomQuery.transcriptSimulator` [ArkLib/ProofSystem/Component/RandomQuery.lean:192](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L192) — The simulator for `RandomQuery`: the protocol is witness-free, so the simulator can rerun the honest
- `def SendClaim.transcriptSimulator` [ArkLib/ProofSystem/Component/SendClaim.lean:246](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L246) — The simulator for `SendClaim`: the component has no private witness, so the simulator can run the ho
- `def SendWitness.transcriptSimulator` [ArkLib/ProofSystem/Component/SendWitness.lean:102](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L102) — The simulator for the `SendWitness` reduction when the relation's witness is determined by the input

### `verify` (3 declarations, 3 files)

- `def ArkLib.Lattices.Ajtai.Simple.verify` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:46](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L46) — Verify a simple Ajtai opening by checking the matrix product.
- `def SimpleRO.verify` [ArkLib/CommitmentScheme/SimpleRO.lean:50](../../../ArkLib/CommitmentScheme/SimpleRO.lean#L50) — (no docstring)
- `def OracleVerifier.Append.verify` [ArkLib/OracleReduction/Composition/Sequential/Append.lean:374](../../../ArkLib/OracleReduction/Composition/Sequential/Append.lean#L374) — The composite `verify`: run `V₁` (routed by `router₁`) to obtain the intermediate statement, then ru

### `witnessStructuralInvariant` (3 declarations, 3 files)

- `def Binius.BinaryBasefold.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:1154](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L1154) — This condition ensures that the witness polynomial `H` has the correct structure `eq(...) * t(...)`
- `def Binius.RingSwitching.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:423](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L423) — This condition ensures that the witness polynomial `H` has the correct structure `A(...) * t'(...)`
- `def RingSwitching.witnessStructuralInvariant` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:439](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L439) — This condition ensures that the witness polynomial `H` has the correct structure `A(...) * t'(...)`

### `TranscriptSimulator` (3 declarations, 3 files)

- `abbrev OracleReduction.TranscriptSimulator` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:38](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L38) — Transcript simulators for oracle reductions are simulators for the associated non-oracle reduction,
- `def Reduction.TranscriptSimulator` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:62](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L62) — A transcript simulator produces, from the input statement alone, a distribution over full transcript
- `abbrev OracleReduction.TranscriptSimulator` [ArkLib/ToMathlib/ZKDefC.lean:46](../../../ArkLib/ToMathlib/ZKDefC.lean#L46) — A simulator for an oracle reduction receives the bundled public statement, but not the private witne

### `id_isHVZK` (3 declarations, 3 files)

- `theorem OracleReduction.id_isHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:245](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L245) — The zero-round identity oracle reduction is HVZK for any oracle-input relation.
- `theorem Reduction.id_isHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:332](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L332) — The zero-round identity reduction is honest-verifier zero-knowledge for any relation.
- `theorem OracleReduction.id_isHVZK` [ArkLib/ToMathlib/ZKDefC.lean:118](../../../ArkLib/ToMathlib/ZKDefC.lean#L118) — The zero-round identity oracle reduction is honest-verifier zero-knowledge for any relation over bun

### `id_perfectHVZK` (3 declarations, 3 files)

- `theorem OracleReduction.id_perfectHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:217](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L217) — The zero-round identity oracle reduction is perfect HVZK for any oracle-input relation.
- `theorem Reduction.id_perfectHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:312](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L312) — The zero-round identity reduction satisfies perfect honest-verifier zero-knowledge for any input rel
- `theorem OracleReduction.id_perfectHVZK` [ArkLib/ToMathlib/ZKDefC.lean:105](../../../ArkLib/ToMathlib/ZKDefC.lean#L105) — The zero-round identity oracle reduction satisfies perfect honest-verifier zero-knowledge for any re

### `isHVZK` (3 declarations, 3 files)

- `def OracleReduction.isHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:62](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L62) — Existential perfect HVZK for an oracle reduction.
- `def Reduction.isHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:90](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L90) — A reduction is honest-verifier zero-knowledge for relation `rel` if some simulator achieves perfect
- `def OracleReduction.isHVZK` [ArkLib/ToMathlib/ZKDefC.lean:73](../../../ArkLib/ToMathlib/ZKDefC.lean#L73) — An oracle reduction is honest-verifier zero-knowledge if some simulator achieves perfect transcript-

### `perfectHVZK` (3 declarations, 3 files)

- `def OracleReduction.perfectHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:44](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L44) — Perfect HVZK for an oracle reduction, delegated through `OracleReduction.toReduction`.
- `def Reduction.perfectHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:69](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L69) — A reduction satisfies perfect honest-verifier zero-knowledge with respect to a simulator and relatio
- `def OracleReduction.perfectHVZK` [ArkLib/ToMathlib/ZKDefC.lean:50](../../../ArkLib/ToMathlib/ZKDefC.lean#L50) — Perfect honest-verifier zero-knowledge for oracle reductions.

### `statisticalHVZK` (3 declarations, 3 files)

- `def OracleReduction.statisticalHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:53](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L53) — Statistical HVZK for an oracle reduction, delegated through `OracleReduction.toReduction`.
- `def Reduction.statisticalHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:80](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L80) — A reduction satisfies statistical honest-verifier zero-knowledge with error `ε` if the simulator's t
- `def OracleReduction.statisticalHVZK` [ArkLib/ToMathlib/ZKDefC.lean:61](../../../ArkLib/ToMathlib/ZKDefC.lean#L61) — Statistical honest-verifier zero-knowledge for oracle reductions with error `ε`.

### `prizeRate_floor_add_one_le` (3 declarations, 3 files)

- `lemma ProximityGap.prizeRate_floor_add_one_le` [ArkLib/Data/CodingTheory/ProximityGap/GrandChallengeDecision.lean:149](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallengeDecision.lean#L149) — For `n ≥ 2`, every prize-rate degree satisfies `k_j + 1 ≤ n`.
- `lemma ProximityGap.prizeRate_floor_add_one_le` [ArkLib/Data/CodingTheory/ProximityGap/GrandChallengeLDFourRate.lean:218](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallengeLDFourRate.lean#L218) — If the evaluation domain has at least two points, each prize degree is strictly below the block leng
- `lemma ProximityGap.prizeRate_floor_add_one_le` [ArkLib/Data/CodingTheory/ProximityGap/MCASecondMoment.lean:371](../../../ArkLib/Data/CodingTheory/ProximityGap/MCASecondMoment.lean#L371) — For `n ≥ 2`, every prize-rate degree satisfies `k_j + 1 ≤ n`.

### `cast_id` (9 declarations, 2 files)

- `theorem Prover.cast_id` [ArkLib/OracleReduction/Cast.lean:53](../../../ArkLib/OracleReduction/Cast.lean#L53) — (no docstring)
- `theorem OracleProver.cast_id` [ArkLib/OracleReduction/Cast.lean:77](../../../ArkLib/OracleReduction/Cast.lean#L77) — (no docstring)
- `theorem Verifier.cast_id` [ArkLib/OracleReduction/Cast.lean:99](../../../ArkLib/OracleReduction/Cast.lean#L99) — (no docstring)
- `theorem Reduction.cast_id` [ArkLib/OracleReduction/Cast.lean:272](../../../ArkLib/OracleReduction/Cast.lean#L272) — (no docstring)
- `theorem ProtocolSpec.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:35](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L35) — (no docstring)
- `theorem ProtocolSpec.MessageIdx.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:79](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L79) — (no docstring)
- `theorem ProtocolSpec.ChallengeIdx.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:118](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L118) — (no docstring)
- `theorem ProtocolSpec.Transcript.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:162](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L162) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:188](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L188) — (no docstring)

### `seqCompose` (8 declarations, 2 files)

- `def Prover.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:37](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L37) — Sequential composition of provers, defined via iteration of the composition (append) of two provers.
- `def Verifier.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:75](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L75) — Sequential composition of verifiers, defined via iteration of the composition (append) of two verifi
- `def Reduction.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:104](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L104) — Sequential composition of reductions, defined via sequential composition of provers and verifiers (o
- `def OracleProver.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:135](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L135) — Sequential composition of provers in oracle reductions, defined via sequential composition of prover
- `def OracleVerifier.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:188](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L188) — Sequential composition of oracle verifiers (in oracle reductions), defined via iteration of the comp
- `def OracleReduction.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:310](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L310) — Sequential composition of oracle reductions, defined via sequential composition of oracle provers an
- `def ProtocolSpec.seqCompose` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:303](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L303) — Sequential composition of a family of `ProtocolSpec`s, indexed by `i : Fin m`. Defined for definitio
- `def ProtocolSpec.FullTranscript.seqCompose` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:361](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L361) — Sequential composition of a family of `FullTranscript`s, indexed by `i : Fin m`. Defined for definit

### `seqCompose_zero` (7 declarations, 2 files)

- `lemma Prover.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:48](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L48) — (no docstring)
- `lemma Verifier.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:83](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L83) — (no docstring)
- `lemma Reduction.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:113](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L113) — (no docstring)
- `lemma OracleVerifier.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:204](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L204) — (no docstring)
- `lemma OracleReduction.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:347](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L347) — (no docstring)
- `theorem ProtocolSpec.seqCompose_zero` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:319](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L319) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.seqCompose_zero` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:366](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L366) — (no docstring)

### `concat` (5 declarations, 2 files)

- `def ProtocolSpec.MessagesUpTo.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:416](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L416) — Concatenate the `k`-th message to the end of the tuple of messages up to round `k`, assuming round `
- `def ProtocolSpec.ChallengesUpTo.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:465](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L465) — Concatenate the `k`-th challenge to the end of the tuple of challenges up to round `k`, assuming rou
- `abbrev ProtocolSpec.Transcript.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:504](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L504) — Concatenate a message to the end of a partial transcript. This is definitionally equivalent to `Fin.
- `abbrev ProtocolSpec.concat` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:44](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L44) — Concatenate a round with direction `dir` and type `Message` to the end of a `ProtocolSpec`
- `def ProtocolSpec.FullTranscript.concat` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:168](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L168) — Adding a message with a given direction and type to the end of a `Transcript`

### `knowledgeSoundness` (5 declarations, 2 files)

- `def Verifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:415](../../../ArkLib/OracleReduction/Security/Basic.lean#L415) — A reduction satisfies **(straightline) knowledge soundness** with error `knowledgeError ≥ 0` and wit
- `def OracleVerifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:550](../../../ArkLib/OracleReduction/Security/Basic.lean#L550) — Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:591](../../../ArkLib/OracleReduction/Security/Basic.lean#L591) — (no docstring)
- `def OracleProof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:629](../../../ArkLib/OracleReduction/Security/Basic.lean#L629) — Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Verifier.StateRestoration.knowledgeSoundness` [ArkLib/OracleReduction/Security/StateRestoration.lean:195](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L195) — State-restoration knowledge soundness (w/ straightline extractor).

### `log` (5 declarations, 2 files)

- `def ReedSolomon.FftDomain.log` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:737](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L737) — Finds a preimage of `x` under the mapping `ω`.
- `def ReedSolomon.CosetFftDomain.log` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1332](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1332) — Finds a preimage of `x` under the mapping `ω`.
- `def Domain.CosetFftDomainClass.log` [ArkLib/Data/Domain/CosetFftDomain/Log.lean:45](../../../ArkLib/Data/Domain/CosetFftDomain/Log.lean#L45) — Finds a preimage of `x` under the mapping `ω`.
- `abbrev Domain.CosetFftDomain.log` [ArkLib/Data/Domain/CosetFftDomain/Log.lean:75](../../../ArkLib/Data/Domain/CosetFftDomain/Log.lean#L75) — (no docstring)
- `abbrev Domain.FftDomain.log` [ArkLib/Data/Domain/CosetFftDomain/Log.lean:82](../../../ArkLib/Data/Domain/CosetFftDomain/Log.lean#L82) — (no docstring)

### `new` (5 declarations, 2 files)

- `def DomainSeparator.Op.new` [ArkLib/Data/Hash/DomainSep.lean:138](../../../ArkLib/Data/Hash/DomainSep.lean#L138) — Construct a new `Op` from a character `id` and a count number `count : Option Nat`. Returns error if
- `def DomainSeparator.new` [ArkLib/Data/Hash/DomainSep.lean:193](../../../ArkLib/Data/Hash/DomainSep.lean#L193) — Create a new DomainSeparator with the domain separator. Rust interface: ```rust pub fn new(session_i
- `def HashStateWithInstructions.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:98](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L98) — Initialize a stateful hash object from a domain separator. Rust interface: ```rust pub fn new(domain
- `def FSVerifierState.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:275](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L275) — Create a new VerifierState from a domain separator and NARG string. Rust interface: ```rust pub fn n
- `def FSProverState.new` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:416](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L416) — Create a new `FSProverState` from a domain separator and RNG. Rust interface: ```rust pub fn new(dom

### `perfectCompleteness` (5 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.perfectCompleteness` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:66](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L66) — Paper-facing alias for CO25 Section 3.4 perfect completeness.
- `def Reduction.perfectCompleteness` [ArkLib/OracleReduction/Security/Basic.lean:184](../../../ArkLib/OracleReduction/Security/Basic.lean#L184) — A reduction satisfies **perfect completeness** if it satisfies completeness with error `0`.
- `def OracleReduction.perfectCompleteness` [ArkLib/OracleReduction/Security/Basic.lean:530](../../../ArkLib/OracleReduction/Security/Basic.lean#L530) — Perfect completeness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.perfectCompleteness` [ArkLib/OracleReduction/Security/Basic.lean:580](../../../ArkLib/OracleReduction/Security/Basic.lean#L580) — (no docstring)
- `def OracleProof.perfectCompleteness` [ArkLib/OracleReduction/Security/Basic.lean:613](../../../ArkLib/OracleReduction/Security/Basic.lean#L613) — Perfect completeness of an oracle reduction is the same as for non-oracle reductions.

### `cast_eq_dcast₂` (4 declarations, 2 files)

- `theorem Verifier.cast_eq_dcast₂` [ArkLib/OracleReduction/Cast.lean:107](../../../ArkLib/OracleReduction/Cast.lean#L107) — (no docstring)
- `theorem ProtocolSpec.MessageIdx.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:91](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L91) — (no docstring)
- `theorem ProtocolSpec.ChallengeIdx.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:130](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L130) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:194](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L194) — (no docstring)

### `instDCast₂` (4 declarations, 2 files)

- `instance Prover.instDCast₂` [ArkLib/OracleReduction/Cast.lean:60](../../../ArkLib/OracleReduction/Cast.lean#L60) — (no docstring)
- `instance ProtocolSpec.MessageIdx.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:87](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L87) — (no docstring)
- `instance ProtocolSpec.ChallengeIdx.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:126](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L126) — (no docstring)
- `instance ProtocolSpec.FullTranscript.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:190](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L190) — (no docstring)

### `accepts` (3 declarations, 2 files)

- `def Plonk.Gate.accepts` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:58](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L58) — A gate accepts an input vector `x` if its evaluation at `x` is zero.
- `def Plonk.ConstraintSystem.accepts` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:129](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L129) — A constraint system accepts an input vector `x` if all of its gates accept `x`.
- `def ToyProblem.Spec.accepts` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:176](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L176) — The §6.1 decision predicate, factored out so completeness proofs and the verifier object share the s

### `advantage` (3 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.advantage` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean:409](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean#L409) — Weak-binding advantage.
- `def ArkLib.Lattices.SIS.advantage` [ArkLib/Data/Lattices/ModuleSIS.lean:62](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L62) — Search advantage for a SIS-style problem.
- `def ArkLib.Lattices.ModuleSIS.advantage` [ArkLib/Data/Lattices/ModuleSIS.lean:106](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L106) — The Module-SIS advantage.

### `experiment` (3 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.experiment` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean:396](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Security.lean#L396) — The Hachi/Greyhound weak-binding experiment. ## Ordinary vs. weak binding *Ordinary (exact) binding*
- `def ArkLib.Lattices.SIS.experiment` [ArkLib/Data/Lattices/ModuleSIS.lean:56](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L56) — The SIS experiment: sample a challenge, run the adversary, check validity.
- `def ArkLib.Lattices.ModuleSIS.experiment` [ArkLib/Data/Lattices/ModuleSIS.lean:101](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L101) — The Module-SIS experiment.

### `extract` (3 declarations, 2 files)

- `def Fin.extract` [ArkLib/Data/Fin/Tuple/Defs.lean:73](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L73) — Extract a sub-tuple from a `Fin`-tuple, from index `start` to `stop - 1`.
- `def ProtocolSpec.extract` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:137](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L137) — Extract the slice of the rounds of a `ProtocolSpec n` from `start` to `stop - 1`.
- `abbrev ProtocolSpec.FullTranscript.extract` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:194](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L194) — (no docstring)

### `logAux` (3 declarations, 2 files)

- `def ReedSolomon.FftDomain.logAux` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:727](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L727) — (no docstring)
- `def ReedSolomon.CosetFftDomain.logAux` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1322](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1322) — (no docstring)
- `def Domain.CosetFftDomainClass.logAux` [ArkLib/Data/Domain/CosetFftDomain/Log.lean:35](../../../ArkLib/Data/Domain/CosetFftDomain/Log.lean#L35) — (no docstring)

### `log_left_inverse` (3 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.log_left_inverse` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:760](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L760) — (no docstring)
- `lemma ReedSolomon.CosetFftDomain.log_left_inverse` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1355](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1355) — (no docstring)
- `lemma Domain.CosetFftDomainClass.log_left_inverse` [ArkLib/Data/Domain/CosetFftDomain/Log.lean:67](../../../ArkLib/Data/Domain/CosetFftDomain/Log.lean#L67) — (no docstring)

### `log_right_inverse` (3 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.log_right_inverse` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:757](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L757) — (no docstring)
- `lemma ReedSolomon.CosetFftDomain.log_right_inverse` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1352](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1352) — (no docstring)
- `lemma Domain.CosetFftDomainClass.log_right_inverse` [ArkLib/Data/Domain/CosetFftDomain/Log.lean:64](../../../ArkLib/Data/Domain/CosetFftDomain/Log.lean#L64) — (no docstring)

### `log_right_inverse'` (3 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.log_right_inverse'` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:741](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L741) — (no docstring)
- `lemma ReedSolomon.CosetFftDomain.log_right_inverse'` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1336](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1336) — (no docstring)
- `lemma Domain.CosetFftDomainClass.log_right_inverse'` [ArkLib/Data/Domain/CosetFftDomain/Log.lean:48](../../../ArkLib/Data/Domain/CosetFftDomain/Log.lean#L48) — (no docstring)

### `mem_subdomain_of_eq_vals` (3 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.mem_subdomain_of_eq_vals` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:818](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L818) — (no docstring)
- `lemma ReedSolomon.CosetFftDomain.mem_subdomain_of_eq_vals` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1376](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1376) — (no docstring)
- `lemma Domain.CosetFftDomainClass.mem_subdomain_of_eq_vals` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:109](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L109) — (no docstring)

### `mem_toFinset_iff_mem` (3 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.mem_toFinset_iff_mem` [ArkLib/Data/Domain/CosetFftDomain/Mem.lean:71](../../../ArkLib/Data/Domain/CosetFftDomain/Mem.lean#L71) — (no docstring)
- `lemma Domain.CosetFftDomain.mem_toFinset_iff_mem` [ArkLib/Data/Domain/CosetFftDomain/Mem.lean:117](../../../ArkLib/Data/Domain/CosetFftDomain/Mem.lean#L117) — (no docstring)
- `lemma Domain.FftDomain.mem_toFinset_iff_mem` [ArkLib/Data/Domain/FftDomain/Mem.lean:69](../../../ArkLib/Data/Domain/FftDomain/Mem.lean#L69) — (no docstring)

### `neg_mem_domain_iff_mem` (3 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.neg_mem_domain_iff_mem` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:460](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L460) — (no docstring)
- `lemma ReedSolomon.CosetFftDomain.neg_mem_domain_iff_mem` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1308](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1308) — (no docstring)
- `lemma Domain.CosetFftDomainClass.neg_mem_domain_iff_mem` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:90](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L90) — (no docstring)

### `neg_mem_domain_of_mem` (3 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.neg_mem_domain_of_mem` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:452](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L452) — (no docstring)
- `lemma ReedSolomon.CosetFftDomain.neg_mem_domain_of_mem` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1297](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1297) — (no docstring)
- `theorem Domain.CosetFftDomainClass.neg_mem_domain_of_mem` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:83](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L83) — (no docstring)

### `rdrop` (3 declarations, 2 files)

- `abbrev Fin.rdrop` [ArkLib/Data/Fin/Tuple/Defs.lean:68](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L68) — Drop the last `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple. This is defi
- `def ProtocolSpec.rdrop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:133](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L133) — Drop the last `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.rdrop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:190](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L190) — (no docstring)

### `rtake` (3 declarations, 2 files)

- `def Fin.rtake` [ArkLib/Data/Fin/Tuple/Defs.lean:55](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L55) — Take the last `m` elements of a finite vector
- `def ProtocolSpec.rtake` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:125](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L125) — Take the last `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.rtake` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:182](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L182) — Take the last `m ≤ n` rounds of a (full) transcript for a protocol specification `pSpec`

### `toList_eq_finset_toList` (3 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.toList_eq_finset_toList` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:291](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L291) — (no docstring)
- `lemma ReedSolomon.CosetFftDomain.toList_eq_finset_toList` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:619](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L619) — (no docstring)
- `lemma Domain.CosetFftDomainClass.toList_eq_finset_toList` [ArkLib/Data/Domain/CosetFftDomain/ToList.lean:41](../../../ArkLib/Data/Domain/CosetFftDomain/ToList.lean#L41) — (no docstring)

### `toSubgroup` (3 declarations, 2 files)

- `def ReedSolomon.FftDomain.toSubgroup` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:296](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L296) — (no docstring)
- `def Domain.FftDomainClass.toSubgroup` [ArkLib/Data/Domain/FftDomain/ToSubgroup.lean:36](../../../ArkLib/Data/Domain/FftDomain/ToSubgroup.lean#L36) — (no docstring)
- `abbrev Domain.FftDomain.toSubgroup` [ArkLib/Data/Domain/FftDomain/ToSubgroup.lean:77](../../../ArkLib/Data/Domain/FftDomain/ToSubgroup.lean#L77) — (no docstring)

### `twoNthRoot` (3 declarations, 2 files)

- `def ReedSolomon.FftDomain.twoNthRoot` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1258](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1258) — Finds a `2 ^ n`th root of `x`.
- `def ReedSolomon.CosetFftDomain.twoNthRoot` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1909](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1909) — Finds a `2 ^ n`th root of `x`.
- `def Domain.CosetFftDomain.twoNthRoot` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:464](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L464) — Finds a `2 ^ n`th root of `x`.

### `twoNthRootAux` (3 declarations, 2 files)

- `def ReedSolomon.FftDomain.twoNthRootAux` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1246](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1246) — (no docstring)
- `def ReedSolomon.CosetFftDomain.twoNthRootAux` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1897](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1897) — (no docstring)
- `def Domain.CosetFftDomain.twoNthRootAux` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:452](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L452) — (no docstring)

### `twoNthRootAux_correct` (3 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.twoNthRootAux_correct` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1262](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1262) — (no docstring)
- `lemma ReedSolomon.CosetFftDomain.twoNthRootAux_correct` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1913](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1913) — (no docstring)
- `lemma Domain.CosetFftDomain.twoNthRootAux_correct` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:468](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L468) — (no docstring)

### `twoNthRoot_correct` (3 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.twoNthRoot_correct` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1274](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1274) — (no docstring)
- `lemma ReedSolomon.CosetFftDomain.twoNthRoot_correct` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1925](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1925) — (no docstring)
- `lemma Domain.CosetFftDomain.twoNthRoot_correct` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:482](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L482) — (no docstring)

### `AbstractOStmtIn` (2 declarations, 2 files)

- `structure Binius.RingSwitching.AbstractOStmtIn` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:241](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L241) — (no docstring)
- `structure RingSwitching.AbstractOStmtIn` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:252](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L252) — (no docstring)

### `AbstractOStmtIn.toRelInput` (2 declarations, 2 files)

- `def Binius.RingSwitching.AbstractOStmtIn.toRelInput` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:249](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L249) — (no docstring)
- `def RingSwitching.AbstractOStmtIn.toRelInput` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:260](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L260) — (no docstring)

### `BatchingStmtIn` (2 declarations, 2 files)

- `structure Binius.RingSwitching.BatchingStmtIn` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:216](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L216) — (no docstring)
- `structure RingSwitching.BatchingStmtIn` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:221](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L221) — (no docstring)

### `BatchingWitIn` (2 declarations, 2 files)

- `structure Binius.RingSwitching.BatchingWitIn` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:212](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L212) — (no docstring)
- `structure RingSwitching.BatchingWitIn` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:217](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L217) — (no docstring)

### `BindingAdversary` (2 declarations, 2 files)

- `structure Commitment.BindingAdversary` [ArkLib/CommitmentScheme/Basic.lean:116](../../../ArkLib/CommitmentScheme/Basic.lean#L116) — An adversary in the (evaluation) binding game returns a commitment `cm`, a query `q`, two purported
- `structure CommitmentScheme.BindingAdversary` [ArkLib/CommitmentScheme/CommitmentScheme.lean:89](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L89) — An adversary in the binding game returns a commitment and two purported openings to possibly differe

### `ChallengeIdx` (2 declarations, 2 files)

- `def ProtocolSpec.ChallengeIdx` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:66](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L66) — Subtype of `Fin n` for the indices corresponding to challenges in a protocol specification
- `def ProtocolSpec.VectorSpec.ChallengeIdx` [ArkLib/OracleReduction/VectorIOR.lean:54](../../../ArkLib/OracleReduction/VectorIOR.lean#L54) — The type of indices for challenges in a `VectorSpec`.

### `Codec` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.Codec` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:204](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L204) — Paper-facing alias for CO25 Definition 4.1 codecs.
- `class ProtocolSpec.Codec` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:99](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L99) — Codec class for CO25 Definition 4.1. `Codec pSpec U` is the generic-parameter carrier for everything

### `Commit` (2 declarations, 2 files)

- `structure Commitment.Commit` [ArkLib/CommitmentScheme/Basic.lean:53](../../../ArkLib/CommitmentScheme/Basic.lean#L53) — The commitment algorithm, parameterized by the committer key and the data to commit.
- `structure CommitmentScheme.Commit` [ArkLib/CommitmentScheme/CommitmentScheme.lean:38](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L38) — The commitment algorithm, returning both the commitment and its opening value.

### `Commitment` (2 declarations, 2 files)

- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.Commitment` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean:126](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Scheme.lean#L126) — Inner-outer commitments live in the outer row space.
- `abbrev ArkLib.Lattices.Ajtai.Simple.Commitment` [ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean:35](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Scheme.lean#L35) — Commitments: row vectors over `Rq Φ`.

### `ConstraintSystem` (2 declarations, 2 files)

- `structure ConstraintSystem` [ArkLib/ProofSystem/ConstraintSystem/Basic.lean:49](../../../ArkLib/ProofSystem/ConstraintSystem/Basic.lean#L49) — A **constraint system** packages a family of indexed relations into a single bundle. For each `i : I
- `def Plonk.ConstraintSystem` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:116](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L116) — A Plonk constraint system is a vector of `numGates` gates, each parametrized by the underlying ring

### `CosetFftDomain` (2 declarations, 2 files)

- `structure ReedSolomon.CosetFftDomain` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:507](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L507) — A coset FFT domain is a domain of the form `x · G` for an FFT domain `G`.
- `structure Domain.CosetFftDomain` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:37](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L37) — A coset FFT domain is a domain of the form `x · G` for an FFT domain `G`.

### `CurveCoeffPolys` (2 declarations, 2 files)

- `def ArkLib.BetaToCurveCoeffPolys.CurveCoeffPolys` [ArkLib/ToMathlib/BetaToCurveCoeffPolys.lean:100](../../../ArkLib/ToMathlib/BetaToCurveCoeffPolys.lean#L100) — Asserts that each coefficient of the decoded polynomial $P(z)$ at index $j < deg$ is interpolated by
- `def ArkLib.KeystoneCapstone.CurveCoeffPolys` [ArkLib/ToMathlib/KeystoneCapstone.lean:92](../../../ArkLib/ToMathlib/KeystoneCapstone.lean#L92) — (no docstring)

### `ExtractabilityAdversary` (2 declarations, 2 files)

- `abbrev Commitment.ExtractabilityAdversary` [ArkLib/CommitmentScheme/Basic.lean:183](../../../ArkLib/CommitmentScheme/Basic.lean#L183) — An adversary in the extractability game is an oracle computation that returns a commitment, a query,
- `structure CommitmentScheme.ExtractabilityAdversary` [ArkLib/CommitmentScheme/CommitmentScheme.lean:137](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L137) — An adversary in the extractability game returns a commitment, a claimed message/opening pair, and au

### `FftDomain` (2 declarations, 2 files)

- `structure ReedSolomon.FftDomain` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:142](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L142) — An FFT domain is an injective group homomorphism whose codomain is the multiplicative group of a fie
- `structure Domain.FftDomain` [ArkLib/Data/Domain/FftDomain/Defs.lean:34](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L34) — (no docstring)

### `FinalOracleStatement` (2 declarations, 2 files)

- `def Fri.Spec.FinalOracleStatement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:97](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L97) — (no docstring)
- `def Spartan.Spec.Bricks.FinalOracleStatement` [ArkLib/ToMathlib/SpartanBricks.lean:85](../../../ArkLib/ToMathlib/SpartanBricks.lean#L85) — The terminal oracle-statement family: unchanged from after the second sum-check (`bundled (v_A,v_B,v

### `FinalStatement` (2 declarations, 2 files)

- `def Fri.Spec.FinalStatement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:83](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L83) — (no docstring)
- `def Spartan.Spec.Bricks.FinalStatement` [ArkLib/ToMathlib/SpartanBricks.lean:80](../../../ArkLib/ToMathlib/SpartanBricks.lean#L80) — The terminal claim statement type: the full Spartan statement after the second sum-check (`(r_y, (r_

### `FinalSumcheckWit` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.FinalSumcheckWit` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean:1620](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/FinalSumcheck.lean#L1620) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.FinalSumcheckWit` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1311](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1311) — (no docstring)

### `GenMutualCorrParams` (2 declarations, 2 files)

- `class Fold.GenMutualCorrParams` [ArkLib/ProofSystem/Whir/Folding.lean:683](../../../ArkLib/ProofSystem/Whir/Folding.lean#L683) — The `GenMutualCorrParams` class captures the necessary parameters and assumptions to model a sequenc
- `class WhirIOP.GenMutualCorrParams` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:85](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L85) — `GenMutualCorrParams` binds together a set of smooth ReedSolomon codes `C_{i : M + 1, j : foldingPar

### `KeyGen` (2 declarations, 2 files)

- `structure Commitment.KeyGen` [ArkLib/CommitmentScheme/Basic.lean:49](../../../ArkLib/CommitmentScheme/Basic.lean#L49) — Key generation for a commitment scheme, producing a committer key and a verifier key.
- `structure CommitmentScheme.KeyGen` [ArkLib/CommitmentScheme/CommitmentScheme.lean:34](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L34) — The key-generation algorithm, returning separate keys for the committer and verifier.

### `MLE_eval_eq_sum_eqTilde` (2 declarations, 2 files)

- `theorem MvPolynomial.MLE_eval_eq_sum_eqTilde` [ArkLib/Data/MvPolynomial/Multilinear.lean:319](../../../ArkLib/Data/MvPolynomial/Multilinear.lean#L319) — **MLE evaluation as an eq-weighted sum over the hypercube.**  Evaluating the multilinear extension a
- `lemma RingSwitching.MLE_eval_eq_sum_eqTilde` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1014](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1014) — **MLE evaluation as an `eq̃`-weighted hypercube sum.** Evaluating the multilinear extension `MLE f`

### `MLIOPCS` (2 declarations, 2 files)

- `structure Binius.RingSwitching.MLIOPCS` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:255](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L255) — (no docstring)
- `structure RingSwitching.MLIOPCS` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:266](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L266) — (no docstring)

### `MLIOPCSStmt` (2 declarations, 2 files)

- `structure Binius.RingSwitching.MLIOPCSStmt` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:231](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L231) — (no docstring)
- `structure RingSwitching.MLIOPCSStmt` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:242](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L242) — (no docstring)

### `MLPEvalRelation` (2 declarations, 2 files)

- `def Binius.RingSwitching.MLPEvalRelation` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:236](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L236) — Standard input relation for MLIOPCS: polynomial evaluation at point equals claimed evaluation
- `def RingSwitching.MLPEvalRelation` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:247](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L247) — Standard input relation for MLIOPCS: polynomial evaluation at point equals claimed evaluation

### `MLPEvalStatement` (2 declarations, 2 files)

- `structure Binius.RingSwitching.MLPEvalStatement` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:203](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L203) — Initial input (input to the batching phase): a polynomial-evaluation claim `s = t(r)`.
- `structure RingSwitching.MLPEvalStatement` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:208](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L208) — Initial input (input to the Batching Phase): a polynomial-evaluation claim `s = t(r)`.

### `MessageIdx` (2 declarations, 2 files)

- `def ProtocolSpec.MessageIdx` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:61](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L61) — Subtype of `Fin n` for the indices corresponding to messages in a protocol specification
- `def ProtocolSpec.VectorSpec.MessageIdx` [ArkLib/OracleReduction/VectorIOR.lean:50](../../../ArkLib/OracleReduction/VectorIOR.lean#L50) — The type of indices for messages in a `VectorSpec`.

### `OStmt` (2 declarations, 2 files)

- `def StirIOP.Round.OStmt` [ArkLib/ProofSystem/Stir/RoundProtocol.lean:53](../../../ArkLib/ProofSystem/Stir/RoundProtocol.lean#L53) — The single-index oracle statement family for a STIR fold round: the prover holds one oracle function
- `def WhirIOP.Construction.OStmt` [ArkLib/ToMathlib/WhirBricksConstruction.lean:48](../../../ArkLib/ToMathlib/WhirBricksConstruction.lean#L48) — The single-index oracle statement family for the WHIR Vector IOPP: the prover holds one oracle funct

### `OracleProver` (2 declarations, 2 files)

- `abbrev Interaction.OracleDecoration.OracleProver` [ArkLib/Interaction/Oracle/Core.lean:898](../../../ArkLib/Interaction/Oracle/Core.lean#L898) — (no docstring)
- `def OracleProver` [ArkLib/OracleReduction/Basic.lean:446](../../../ArkLib/OracleReduction/Basic.lean#L446) — An **(oracle) prover** in an interactive **oracle** reduction is a prover in the non-oracle reductio

### `OracleReduction` (2 declarations, 2 files)

- `structure Interaction.OracleDecoration.OracleReduction` [ArkLib/Interaction/Oracle/Core.lean:928](../../../ArkLib/Interaction/Oracle/Core.lean#L928) — (no docstring)
- `structure OracleReduction` [ArkLib/OracleReduction/Basic.lean:706](../../../ArkLib/OracleReduction/Basic.lean#L706) — An **interactive oracle reduction** for a given protocol specification `pSpec`, and relative to orac

### `OracleVerifier` (3 declarations, 2 files)

- `structure Interaction.OracleVerifier` [ArkLib/Interaction/Oracle/Core.lean:1042](../../../ArkLib/Interaction/Oracle/Core.lean#L1042) — (no docstring)
- `structure OracleVerifier` [ArkLib/OracleReduction/Basic.lean:175](../../../ArkLib/OracleReduction/Basic.lean#L175) — (no docstring)
- `structure OracleVerifier` [ArkLib/OracleReduction/Basic.lean:466](../../../ArkLib/OracleReduction/Basic.lean#L466) — An **(oracle) verifier** of an interactive **oracle** reduction consists of: - an oracle computation

### `OutputOracleStatement` (2 declarations, 2 files)

- `def ToyProblem.Spec.OutputOracleStatement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:116](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L116) — Output oracle statement: the IOR has no output oracle component.
- `def ToyProblem.SimplifiedIOR.OutputOracleStatement` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:77](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L77) — Output oracle statement: the single combined codeword `f_new := f₁ + γ·f₂ : ι → F`.

### `OutputWitness` (2 declarations, 2 files)

- `def ToyProblem.Spec.OutputWitness` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:120](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L120) — Output witness: empty.
- `def ToyProblem.SimplifiedIOR.OutputWitness` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:81](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L81) — Output witness for C6.9: the combined message `M_new := M₁ + γ·M₂`.

### `ParamConditions` (2 declarations, 2 files)

- `structure StirIOP.ParamConditions` [ArkLib/ProofSystem/Stir/MainThm.lean:55](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L55) — **Conditions that protocol parameters must satisfy.** - `h_deg` : initial degree `deg` is a power of
- `structure WhirIOP.ParamConditions` [ArkLib/ProofSystem/Whir/RBRSoundness.lean:66](../../../ArkLib/ProofSystem/Whir/RBRSoundness.lean#L66) — ** Conditions that protocol parameters must satisfy. ** h_m : m = varCount₀ h_sumkLt : ∑ i : Fin (M

### `Proof` (2 declarations, 2 files)

- `abbrev Interaction.Proof` [ArkLib/Interaction/Reduction.lean:232](../../../ArkLib/Interaction/Reduction.lean#L232) — (no docstring)
- `def Proof` [ArkLib/OracleReduction/Basic.lean:730](../../../ArkLib/OracleReduction/Basic.lean#L730) — An **interactive proof (IP)** is an interactive reduction where the output statement is a boolean, t

### `PrvState` (2 declarations, 2 files)

- `def Binius.RingSwitching.BatchingPhase.PrvState` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:319](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L319) — The state maintained by the prover throughout the batching phase.
- `def RingSwitching.BatchingPhase.PrvState` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:121](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L121) — The state maintained by the prover throughout the batching phase.

### `RewindingExtractor` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.RewindingExtractor` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:155](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L155) — Paper-facing alias for the rewinding extractor interface from CO25 Definition 3.8.
- `def Extractor.RewindingExtractor` [ArkLib/ToMathlib/RewindingExtractor.lean:115](../../../ArkLib/ToMathlib/RewindingExtractor.lean#L115) — A **rewinding extractor** for the 2-special-sound case: given the recorded prefix and **two** comple

### `RingSwitchingBaseContext` (2 declarations, 2 files)

- `structure Binius.RingSwitching.RingSwitchingBaseContext` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:220](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L220) — (no docstring)
- `structure RingSwitching.RingSwitchingBaseContext` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:225](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L225) — (no docstring)

### `RingSwitching_SumcheckMultParam` (2 declarations, 2 files)

- `def Binius.RingSwitching.RingSwitching_SumcheckMultParam` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:381](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L381) — Ring-Switching multiplier parameter for sumcheck, using `A_MLE` as the multiplier.
- `def RingSwitching.RingSwitching_SumcheckMultParam` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:389](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L389) — Ring-Switching multiplier parameter for sumcheck, using `A_MLE` as the multiplier.

### `Scheme` (2 declarations, 2 files)

- `structure Commitment.Scheme` [ArkLib/CommitmentScheme/Basic.lean:64](../../../ArkLib/CommitmentScheme/Basic.lean#L64) — A commitment scheme with key generation, commitment, and opening algorithms.
- `structure CommitmentScheme.Scheme` [ArkLib/CommitmentScheme/CommitmentScheme.lean:46](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L46) — An ordinary commitment scheme.

### `SmoothCosetFftDomain` (2 declarations, 2 files)

- `abbrev ReedSolomon.SmoothCosetFftDomain` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:722](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L722) — A smooth coset FFT domain is a coset FFT domain whose underlying FFT domain is smooth.
- `abbrev Domain.SmoothCosetFftDomain` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:238](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L238) — (no docstring)

### `SmoothFftDomain` (2 declarations, 2 files)

- `abbrev ReedSolomon.SmoothFftDomain` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:413](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L413) — A smooth FFT domain is an FFT domain whose domain (i.e. LHS) is a finite additive cyclic group, whic
- `abbrev Domain.SmoothFftDomain` [ArkLib/Data/Domain/FftDomain/Defs.lean:121](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L121) — (no docstring)

### `SpongeState` (2 declarations, 2 files)

- `class SpongeState` [ArkLib/Data/Hash/DuplexSponge.lean:255](../../../ArkLib/Data/Hash/DuplexSponge.lean#L255) — Type class for the state of a cryptographic permutation used in the duplex sponge construction. Rust
- `abbrev DuplexSpongeFS.SpongeState` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:42](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L42) — Paper-facing alias for the canonical duplex-sponge state used in CO25 Section 3.3.

### `SumcheckMultiplierParam` (2 declarations, 2 files)

- `structure Sumcheck.Structured.SumcheckMultiplierParam` [ArkLib/ProofSystem/Sumcheck/Structured.lean:85](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L85) — Parameters describing how the round polynomial `H` is built from the witness `t`: `H = P · Q(t)`, wh
- `structure Sumcheck.Structured.Prismalinear.SumcheckMultiplierParam` [ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean:50](../../../ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean#L50) — Parameters describing how a *prismalinear* round polynomial `H = P · Q(t)` is built from the witness

### `TensorAlgebra` (2 declarations, 2 files)

- `abbrev Binius.RingSwitching.TensorAlgebra` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:63](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L63) — Tensor Algebra A = L ⊗_K L. Based on the spec, it's viewed as (2^κ)x(2^κ) arrays of K-elements. The
- `abbrev RingSwitching.TensorAlgebra` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:63](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L63) — Tensor Algebra A = L ⊗_K L. Based on the spec, it's viewed as (2^κ)x(2^κ) arrays of K-elements. The

### `Verifier.run` (2 declarations, 2 files)

- `def Interaction.Verifier.run` [ArkLib/Interaction/Reduction.lean:262](../../../ArkLib/Interaction/Reduction.lean#L262) — (no docstring)
- `def Verifier.run` [ArkLib/OracleReduction/Execution.lean:137](../../../ArkLib/OracleReduction/Execution.lean#L137) — Run the (non-oracle) verifier in an interactive reduction. It takes in the input statement and the t

### `WitIn` (2 declarations, 2 files)

- `def RandomQuery.WitIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:38](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L38) — (no docstring)
- `def Logup.WitIn` [ArkLib/ProofSystem/Logup/Common.lean:368](../../../ArkLib/ProofSystem/Logup/Common.lean#L368) — Protocol 2 has no private witness beyond the input oracles at this layer.

### `WitMLP` (2 declarations, 2 files)

- `structure Binius.RingSwitching.WitMLP` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:209](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L209) — (no docstring)
- `structure RingSwitching.WitMLP` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:214](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L214) — (no docstring)

### `aeval_eqPolynomial_zeroOne` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.aeval_eqPolynomial_zeroOne` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:683](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L683) — `aeval` of `eqPolynomial` at a Boolean coefficient vector lands in `L₀` as `eqTilde`.
- `lemma RingSwitching.aeval_eqPolynomial_zeroOne` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:775](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L775) — `aeval` of `eqPolynomial` at a Boolean coefficient vector lands in `L₀` as `eqTilde`.

### `aeval_eq_sum_eqTilde` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.aeval_eq_sum_eqTilde` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:700](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L700) — **MLE evaluation identity (through the algebra map).** For a multilinear `t` over `K₀`, its `L₀`-eva
- `lemma RingSwitching.aeval_eq_sum_eqTilde` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:792](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L792) — **MLE evaluation identity (through the algebra map).** For a multilinear `t` over `K₀`, its `L₀`-eva

### `agree` (2 declarations, 2 files)

- `def CodeGeometry.agree` [ArkLib/Data/CodingTheory/CodeGeometry.lean:38](../../../ArkLib/Data/CodingTheory/CodeGeometry.lean#L38) — (no docstring)
- `def ProximityGap.WeightedAgreement.agree` [ArkLib/Data/CodingTheory/ProximityGap/Basic.lean:179](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean#L179) — Relative `μ`-agreement between words `u` and `v`.

### `answer_instDefault` (2 declarations, 2 files)

- `lemma RingSwitching.BatchingPhase.answer_instDefault` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:54](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L54) — The default oracle interface (`OracleInterface.instDefault`, used by the ring-switching message orac
- `lemma ToyProblem.Spec.answer_instDefault` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:628](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L628) — `answer` of the default oracle interface is the identity (the message itself).

### `appendRight` (2 declarations, 2 files)

- `def Interaction.OracleDecoration.QueryHandle.appendRight` [ArkLib/Interaction/Oracle/Core.lean:202](../../../ArkLib/Interaction/Oracle/Core.lean#L202) — (no docstring)
- `def ProtocolSpec.Transcript.appendRight` [ArkLib/OracleReduction/ProtocolSpec/TranscriptRecompose.lean:56](../../../ArkLib/OracleReduction/ProtocolSpec/TranscriptRecompose.lean#L56) — Append a full `pSpec₁` transcript and a *partial* `pSpec₂` transcript into a partial transcript for

### `append_left_injective` (2 declarations, 2 files)

- `theorem Fin.append_left_injective` [ArkLib/Data/Fin/Basic.lean:262](../../../ArkLib/Data/Fin/Basic.lean#L262) — (no docstring)
- `theorem ProtocolSpec.append_left_injective` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:68](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L68) — (no docstring)

### `append_right_injective` (2 declarations, 2 files)

- `theorem Fin.append_right_injective` [ArkLib/Data/Fin/Basic.lean:270](../../../ArkLib/Data/Fin/Basic.lean#L270) — (no docstring)
- `theorem ProtocolSpec.append_right_injective` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:78](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L78) — (no docstring)

### `badBatchingEventProp` (2 declarations, 2 files)

- `def Binius.RingSwitching.BatchingPhase.badBatchingEventProp` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:1045](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L1045) — The "bad batching event": the prover's ŝ (`msg0`) disagrees with the honest ŝ (`s_bar`), but their `
- `def RingSwitching.BatchingPhase.badBatchingEventProp` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:659](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L659) — The "bad batching event": the prover's ŝ (`msg0`) disagrees with the honest ŝ (`s_bar`), but their `

### `badSumcheckEventProp` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.badSumcheckEventProp` [ArkLib/ProofSystem/Binius/BinaryBasefold/Relations.lean:496](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Relations.lean#L496) — (no docstring)
- `def RingSwitching.SumcheckPhase.badSumcheckEventProp` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:235](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L235) — **Named weakened-KState bad event for one ring-switching sumcheck round.** The prover's degree-`≤ 2`

### `batchingCore_perfectCompleteness` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.FullRingSwitching.batchingCore_perfectCompleteness` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:110](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L110) — (no docstring)
- `lemma RingSwitching.FullRingSwitching.batchingCore_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/General.lean:121](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L121) — (no docstring)

### `batchingInputRelation` (2 declarations, 2 files)

- `def Binius.RingSwitching.BatchingPhase.batchingInputRelation` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:97](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L97) — Input relation: the witness `t` and `t'` are consistent, and `t` satisfies the original claim.
- `def RingSwitching.BatchingPhase.batchingInputRelation` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:301](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L301) — Input relation: the witness `t` and `t'` are consistent, and `t` satisfies the original claim.

### `batchingInputRelationProp` (2 declarations, 2 files)

- `def Binius.RingSwitching.BatchingPhase.batchingInputRelationProp` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:85](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L85) — (no docstring)
- `def RingSwitching.BatchingPhase.batchingInputRelationProp` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:294](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L294) — (no docstring)

### `batchingKStateProp` (2 declarations, 2 files)

- `def Binius.RingSwitching.BatchingPhase.batchingKStateProp` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:434](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L434) — (no docstring)
- `def RingSwitching.BatchingPhase.batchingKStateProp` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:336](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L336) — (no docstring)

### `batchingKnowledgeStateFunction` (2 declarations, 2 files)

- `def Binius.RingSwitching.BatchingPhase.batchingKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:483](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L483) — Knowledge state function for the batching phase.
- `def RingSwitching.BatchingPhase.batchingKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:406](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L406) — Knowledge state function for the batching phase.

### `batchingMismatchPoly` (2 declarations, 2 files)

- `def Binius.RingSwitching.BatchingPhase.batchingMismatchPoly` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:854](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L854) — Mismatch polynomial from row-decomposition difference `msg0 - s_bar`.
- `def RingSwitching.BatchingPhase.batchingMismatchPoly` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:569](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L569) — Mismatch polynomial from row-decomposition difference `msg0 - s_bar`.

### `batchingMismatchPoly_nonzero_of_embed_ne` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.BatchingPhase.batchingMismatchPoly_nonzero_of_embed_ne` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:908](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L908) — If embedded evaluation mismatches `msg0`, the mismatch polynomial is nonzero.
- `lemma RingSwitching.BatchingPhase.batchingMismatchPoly_nonzero_of_embed_ne` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:611](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L611) — If embedded evaluation mismatches `msg0`, the mismatch polynomial is nonzero.

### `batchingMismatchPoly_totalDegree_le` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.BatchingPhase.batchingMismatchPoly_totalDegree_le` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:878](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L878) — Degree bound for mismatch polynomial: multilinear in `κ` vars, so total degree ≤ `κ`.
- `lemma RingSwitching.BatchingPhase.batchingMismatchPoly_totalDegree_le` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:583](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L583) — Degree bound for mismatch polynomial: multilinear in `κ` vars, so total degree ≤ `κ`.

### `batchingOracleReduction` (2 declarations, 2 files)

- `def Binius.RingSwitching.BatchingPhase.batchingOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:394](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L394) — The Oracle Reduction for the Batching Phase.
- `def RingSwitching.BatchingPhase.batchingOracleReduction` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:274](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L274) — The Oracle Reduction for the Batching Phase.

### `batchingOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem Binius.RingSwitching.BatchingPhase.batchingOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:1220](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L1220) — RBR knowledge soundness for the batching phase oracle verifier.
- `theorem RingSwitching.BatchingPhase.batchingOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:554](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L554) — RBR knowledge soundness for the batching phase oracle verifier. `IsDomain K` (alongside the existing

### `batchingRBRKnowledgeError` (2 declarations, 2 files)

- `def Binius.RingSwitching.BatchingPhase.batchingRBRKnowledgeError` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:432](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L432) — RBR knowledge soundness error for the batching phase. The only verifier randomness is `r''`. A colli
- `def RingSwitching.BatchingPhase.batchingRBRKnowledgeError` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:331](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L331) — RBR knowledge soundness error for the batching phase. The only verifier randomness is `r''`. A colli

### `batchingRbrExtractor` (2 declarations, 2 files)

- `def Binius.RingSwitching.BatchingPhase.batchingRbrExtractor` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:414](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L414) — RBR extractor for the batching phase.
- `def RingSwitching.BatchingPhase.batchingRbrExtractor` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:312](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L312) — RBR extractor for the batching phase.

### `batchingReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem Binius.RingSwitching.BatchingPhase.batchingReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:649](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L649) — Perfect completeness for the batching phase oracle reduction. This theorem proves that the honest pr
- `theorem RingSwitching.BatchingPhase.batchingReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:540](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L540) — Batching completeness from the explicit local algebraic residual.

### `batchingWitMid` (2 declarations, 2 files)

- `def Binius.RingSwitching.BatchingPhase.batchingWitMid` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:408](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L408) — Intermediate witness types for RBR knowledge soundness.
- `def RingSwitching.BatchingPhase.batchingWitMid` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:306](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L306) — Intermediate witness types for RBR knowledge soundness.

### `batching_compute_s0_sub_eq_eval_mismatch` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.BatchingPhase.batching_compute_s0_sub_eq_eval_mismatch` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:860](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L860) — The mismatch polynomial evaluates to the `compute_s0` difference.
- `lemma RingSwitching.BatchingPhase.batching_compute_s0_sub_eq_eval_mismatch` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:574](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L574) — The mismatch polynomial evaluates to the `compute_s0` difference.

### `batching_doom_escape_probability_bound` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.BatchingPhase.batching_doom_escape_probability_bound` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:1153](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L1153) — Per-transcript batching bound: for a fixed prover message `msg0`, the probability (over batching cha
- `lemma RingSwitching.BatchingPhase.batching_doom_escape_probability_bound` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:760](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L760) — (no docstring)

### `batching_rbrExtractionFailureEvent_imply_badBatchingEvent` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.BatchingPhase.batching_rbrExtractionFailureEvent_imply_badBatchingEvent` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:1092](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L1092) — Extraction failure implies a witness-dependent bad batching event. The extracted `witMid` also carri
- `lemma RingSwitching.BatchingPhase.batching_rbrExtractionFailureEvent_imply_badBatchingEvent` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:721](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L721) — Extraction failure implies a witness-dependent bad batching event.

### `binomial_separation` (2 declarations, 2 files)

- `theorem ProximityGap.MultiplicativeRigidity.binomial_separation` [ArkLib/Data/CodingTheory/ProximityGap/MultiplicativeRigidityFiber.lean:154](../../../ArkLib/Data/CodingTheory/ProximityGap/MultiplicativeRigidityFiber.lean#L154) — **Binomial separation.** If `0 < b < a ≤ k`, then two distinct monomials `c₁ * X ^ a` and `c₂ * X ^
- `theorem MultiplicativeRigidity.binomial_separation` [ArkLib/Data/CodingTheory/ProximityGap/MultiplicativeRigidityZMod.lean:170](../../../ArkLib/Data/CodingTheory/ProximityGap/MultiplicativeRigidityZMod.lean#L170) — **Binomial separation.** Packaging of coset rigidity in the form the dossier consumes: if `b < a < k

### `boolHypercubeEmb` (2 declarations, 2 files)

- `def Binius.RingSwitching.boolHypercubeEmb` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:889](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L889) — The Boolean hypercube embedding `(Fin k → Fin 2) ↪ (Fin k → L₀)` induced by a 2-element domain embed
- `def RingSwitching.boolHypercubeEmb` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1351](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1351) — The Boolean hypercube embedding `(Fin k → Fin 2) ↪ (Fin k → L₀)` induced by a 2-element domain embed

### `boolHypercube_sum_eq` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.boolHypercube_sum_eq` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:897](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L897) — **`𝓑`-domain hypercube sum reindexes to the Boolean hypercube.** For any `𝓑 : Fin 2 ↪ L₀`, summing `
- `lemma RingSwitching.boolHypercube_sum_eq` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1359](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1359) — **`𝓑`-domain hypercube sum reindexes to the Boolean hypercube.** For any `𝓑 : Fin 2 ↪ L₀`, summing `

### `boolHypercube_sum_pinned` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.boolHypercube_sum_pinned` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:917](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L917) — **Pinned-`𝓑` Boolean-domain sumcheck sum.** When `𝓑` is pinned to the Boolean embedding (`𝓑 c = if c
- `lemma RingSwitching.boolHypercube_sum_pinned` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1379](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1379) — **Pinned-`𝓑` Boolean-domain sumcheck sum.** When `𝓑` is pinned to the Boolean embedding (`𝓑 c = if c

### `c0_ne_c1` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.c0_ne_c1` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:39](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L39) — The three codewords are pairwise distinct.
- `theorem JohnsonBound.JqlRefutation.c0_ne_c1` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:79](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L79) — The three codewords are pairwise distinct.

### `c0_ne_c2` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.c0_ne_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:40](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L40) — (no docstring)
- `theorem JohnsonBound.JqlRefutation.c0_ne_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:80](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L80) — (no docstring)

### `c1_ne_c2` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.c1_ne_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:41](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L41) — (no docstring)
- `theorem JohnsonBound.JqlRefutation.c1_ne_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:81](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L81) — (no docstring)

### `card` (2 declarations, 2 files)

- `theorem Probability.SizeSubset.card` [ArkLib/Data/Probability/Combinatorial.lean:47](../../../ArkLib/Data/Probability/Combinatorial.lean#L47) — The number of size-`n` subsets of a finite type is `\|α\| choose n`.
- `theorem Probability.SizedSubset.card` [ArkLib/Data/Probability/UniformSubset.lean:43](../../../ArkLib/Data/Probability/UniformSubset.lean#L43) — (no docstring)

### `card_allQueriesIn` (2 declarations, 2 files)

- `theorem Issue14Scratch.card_allQueriesIn` [ArkLib/ProofSystem/BatchedFri/QueryRoundAnalysis.lean:31](../../../ArkLib/ProofSystem/BatchedFri/QueryRoundAnalysis.lean#L31) — (= `Fri.QueryRound.card_allQueriesIn`) The number of length-`t` query tuples landing entirely in `G`
- `theorem Fri.QueryRound.card_allQueriesIn` [ArkLib/ProofSystem/BatchedFri/Security.lean:352](../../../ArkLib/ProofSystem/BatchedFri/Security.lean#L352) — The number of length-`t` query tuples landing entirely in a set `G` is `\|G\| ^ t`. This counts the ac

### `card_filter_badPolyAgreement_degree_two_le` (2 declarations, 2 files)

- `theorem Issue19Scratch.card_filter_badPolyAgreement_degree_two_le` [ArkLib/ProofSystem/RingSwitching/BadPolyAgreementCount.lean:88](../../../ArkLib/ProofSystem/RingSwitching/BadPolyAgreementCount.lean#L88) — **Degree-2 specialization (ring-switching/Binius round polynomial, carrier `↥F⦃≤ 2⦄[X]`).** Mirrors
- `theorem KStateWeaken.card_filter_badPolyAgreement_degree_two_le` [ArkLib/ToMathlib/KStateWeaken.lean:144](../../../ArkLib/ToMathlib/KStateWeaken.lean#L144) — Degree-2 cardinality specialization for the exact bad-agreement event.

### `card_filter_badPolyAgreement_le` (2 declarations, 2 files)

- `theorem Issue19Scratch.card_filter_badPolyAgreement_le` [ArkLib/ProofSystem/RingSwitching/BadPolyAgreementCount.lean:57](../../../ArkLib/ProofSystem/RingSwitching/BadPolyAgreementCount.lean#L57) — **Schwartz–Zippel counting bound (general degree).** For any common degree budget `D`, the number of
- `theorem KStateWeaken.card_filter_badPolyAgreement_le` [ArkLib/ToMathlib/KStateWeaken.lean:137](../../../ArkLib/ToMathlib/KStateWeaken.lean#L137) — Cardinality bound for the exact bad-agreement event from a common degree bound.

### `card_filter_eval_zero_le` (2 declarations, 2 files)

- `theorem RingSwitching.card_filter_eval_zero_le` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1724](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1724) — **Root-set cardinality bound.** Over an integral domain `L`, the number of field elements at which a
- `theorem Polynomial.card_filter_eval_zero_le` [ArkLib/ToMathlib/ExtractedIssueBricks.lean:57](../../../ArkLib/ToMathlib/ExtractedIssueBricks.lean#L57) — **Root-set cardinality bound.** Over a finite integral domain `L`, a nonzero `p : L[X]` vanishes at

### `card_filter_forall_pi` (2 declarations, 2 files)

- `lemma OutOfDomSmpl.card_filter_forall_pi` [ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean:71](../../../ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean#L71) — Counting a coordinatewise event: the tuples satisfying `Q` in every coordinate form the `piFinset` o
- `theorem card_filter_forall_pi` [ArkLib/ToMathlib/CountingAgreementBricks.lean:32](../../../ArkLib/ToMathlib/CountingAgreementBricks.lean#L32) — Count of length-`s` tuples whose every coordinate satisfies `Q` equals `(#Q)^s`.

### `check_rows_sum_eq_aeval` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.check_rows_sum_eq_aeval` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:740](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L740) — **DP24 ring-switching capstone (sum form).** The verifier's row-decomposition check sum, applied to
- `lemma RingSwitching.check_rows_sum_eq_aeval` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1209](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1209) — **DP24 ring-switching capstone (sum form).** The verifier's row-decomposition check sum, applied to

### `coeffHom` (2 declarations, 2 files)

- `def ProximityPrize.BCIKS20.GammaGenuine.coeffHom` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/GammaGenuine.lean:87](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/GammaGenuine.lean#L87) — The per-`Y`-coefficient ring hom `F[X][Y] → (𝕃 H)⟦X⟧`: recenter the `X`-layer at `x₀` (`taylorAlgHom
- `def ArkLib.Lattices.CyclotomicModulus.Rq.coeffHom` [ArkLib/Data/Lattices/CyclotomicRing/Rq.lean:175](../../../ArkLib/Data/Lattices/CyclotomicRing/Rq.lean#L175) — Reading off the `k`-th coefficient of the underlying polynomial, as an additive homomorphism `Rq Φ →

### `coeff_S_eq_zero_of_lt` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_S_eq_zero_of_lt` [ArkLib/Data/Polynomial/HenselExistence.lean:202](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L202) — The `t`-th partial sum is supported on `[0, t]`: every coefficient above order `t` vanishes. (`S t`
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_S_eq_zero_of_lt` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:279](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L279) — `S t` is supported on `[0, t]`: every coefficient above order `t` vanishes.

### `coeff_S_stable` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_S_stable` [ArkLib/Data/Polynomial/HenselExistence.lean:213](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L213) — Coefficient stability: for `j ≤ t`, `coeff j (S t) = coeff j (S j)`. The diagonal value is reached a
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_S_stable` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:289](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L289) — Coefficient stability: for `j ≤ t`, `coeff j (S t) = coeff j (S j)`.

### `coeff_S_succ_of_le` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_S_succ_of_le` [ArkLib/Data/Polynomial/HenselExistence.lean:196](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L196) — Adding the order-`(t+1)` monomial leaves coefficients `≤ t` unchanged.
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_S_succ_of_le` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:274](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L274) — Adding the order-`(t+1)` monomial leaves coefficients `≤ t` unchanged.

### `coeff_aeval_eq_sum_range` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_aeval_eq_sum_range` [ArkLib/Data/Polynomial/HenselExistence.lean:64](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L64) — Local copy of `NewtonLinearization.coeff_aeval_eq_sum_range`: `coeff n (aeval γ P) = ∑_{i ≤ deg P} P
- `theorem ProximityPrize.NewtonLinearization.coeff_aeval_eq_sum_range` [ArkLib/Data/Polynomial/NewtonLinearization.lean:165](../../../ArkLib/Data/Polynomial/NewtonLinearization.lean#L165) — Local restatement of the `HasSubst`-free `aeval`-coefficient expansion (this is `ProximityPrize.coef

### `coeff_aeval_sub_at` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_aeval_sub_at` [ArkLib/Data/Polynomial/HenselExistence.lean:146](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L146) — Local copy of `NewtonLinearization.coeff_aeval_sub_at` (the `P'(c)`-linear response). For `P : R[X]`
- `theorem ProximityPrize.NewtonLinearization.coeff_aeval_sub_at` [ArkLib/Data/Polynomial/NewtonLinearization.lean:185](../../../ArkLib/Data/Polynomial/NewtonLinearization.lean#L185) — **Newton/Hensel linearization of the composed series (P2 form).** For a polynomial `P` over `R` and

### `coeff_γ` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_γ` [ArkLib/Data/Polynomial/HenselExistence.lean:226](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L226) — (no docstring)
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_γ` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:302](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L302) — (no docstring)

### `coeff_γ_eq_S` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.coeff_γ_eq_S` [ArkLib/Data/Polynomial/HenselExistence.lean:235](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L235) — `γ` agrees with the `t`-th partial sum below order `t + 1`.
- `theorem ProximityPrize.HenselSeriesCoeff.coeff_γ_eq_S` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:311](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L311) — `γ` agrees with the `t`-th partial sum below order `t + 1`.

### `coeffs` (2 declarations, 2 files)

- `def Polynomial.Bivariate.coeffs` [ArkLib/Data/Polynomial/Bivariate.lean:34](../../../ArkLib/Data/Polynomial/Bivariate.lean#L34) — The set of coefficients of a bivariate polynomial.
- `def UniPoly.coeffs` [ArkLib/Data/UniPoly/Basic.lean:41](../../../ArkLib/Data/UniPoly/Basic.lean#L41) — (no docstring)

### `componentWise_φ₁_embed_MLE` (2 declarations, 2 files)

- `def Binius.RingSwitching.componentWise_φ₁_embed_MLE` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:171](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L171) — **Component-wise `φ₁` embedding**. Takes a polynomial `t'` with coefficients in `L` and embeds it in
- `def RingSwitching.componentWise_φ₁_embed_MLE` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:193](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L193) — Binius-named alias: component-wise `φ₁` embedding into the tensor algebra `L ⊗[K] L`.

### `computeRoundPoly` (2 declarations, 2 files)

- `def Sumcheck.Structured.computeRoundPoly` [ArkLib/ProofSystem/Sumcheck/Structured.lean:130](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L130) — The general round polynomial `H = P · Q(t)`, where `P = param.multpoly ctx` is the public multilinea
- `def Sumcheck.Structured.Prismalinear.computeRoundPoly` [ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean:70](../../../ArkLib/ProofSystem/Sumcheck/Structured/Prismalinear.lean#L70) — The *prismalinear* round polynomial `H = P · Q(t)`, where `P = param.multpoly ctx` has per-variable

### `compute_A_MLE` (2 declarations, 2 files)

- `def Binius.RingSwitching.compute_A_MLE` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:370](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L370) — Step 4b: P writes `A(X_0, ..., X_{ℓ'-1})` for its multilinear extension of `A_func`.
- `def RingSwitching.compute_A_MLE` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:378](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L378) — Step 4b: P writes `A(X_0, ..., X_{ℓ'-1})` for its multilinear extension of `A_func`.

### `compute_A_func` (2 declarations, 2 files)

- `def Binius.RingSwitching.compute_A_func` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:353](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L353) — Step 4a: For each `w ∈ {0,1}^{ℓ'}`, P decompose `eq̃(r_κ, ..., r_{ℓ-1}, w_0, ..., w_{ℓ'-1})` `=: Σ_{
- `def RingSwitching.compute_A_func` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:361](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L361) — Step 4a: For each `w ∈ {0,1}^{ℓ'}`, P decompose `eq̃(r_κ, ..., r_{ℓ-1}, w_0, ..., w_{ℓ'-1})` `=: Σ_{

### `compute_final_eq_tensor` (2 declarations, 2 files)

- `def Binius.RingSwitching.compute_final_eq_tensor` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:401](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L401) — Compute the tensor `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁(r'_0), ..., φ₁(r'_{ℓ'-1}))`
- `def RingSwitching.compute_final_eq_tensor` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:410](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L410) — Compute the tensor `e := eq̃(φ₀(r_κ), ..., φ₀(r_{ℓ-1}), φ₁(r'_0), ..., φ₁(r'_{ℓ'-1}))`

### `compute_final_eq_value` (2 declarations, 2 files)

- `def Binius.RingSwitching.compute_final_eq_value` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:411](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L411) — Decompose the final eq tensor `e := Σ_{u ∈ {0,1}^κ} eq̃(u, r'') ⨂ e_u`, where e_u is the row compone
- `def RingSwitching.compute_final_eq_value` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:420](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L420) — Decompose the final eq tensor `e := Σ_{u ∈ {0,1}^κ} eq̃(u, r'') ⨂ e_u`, where e_u is the row compone

### `compute_s0` (2 declarations, 2 files)

- `def Binius.RingSwitching.compute_s0` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:394](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L394) — Step 5 (V): Compute `s₀ := Σ_{u ∈ {0,1}^κ} eqTilde(u, r'') ⋅ ŝ_u`, where ŝ_u is the row components o
- `def RingSwitching.compute_s0` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:403](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L403) — Step 5 (V): Compute `s₀ := Σ_{u ∈ {0,1}^κ} eqTilde(u, r'') ⋅ ŝ_u`, where ŝ_u is the row components o

### `constantCoeff_γ` (2 declarations, 2 files)

- `theorem ProximityPrize.HenselExistence.constantCoeff_γ` [ArkLib/Data/Polynomial/HenselExistence.lean:230](../../../ArkLib/Data/Polynomial/HenselExistence.lean#L230) — The constant coefficient of the Newton root is the prescribed root `c`.
- `theorem ProximityPrize.HenselSeriesCoeff.constantCoeff_γ` [ArkLib/Data/Polynomial/HenselSeriesCoeff.lean:306](../../../ArkLib/Data/Polynomial/HenselSeriesCoeff.lean#L306) — The constant coefficient of the Newton root is the prescribed root `c`.

### `coord` (2 declarations, 2 files)

- `def CodingTheory.ExtensionFieldPresentation.coord` [ArkLib/Data/CodingTheory/ExtensionCodes.lean:100](../../../ArkLib/Data/CodingTheory/ExtensionCodes.lean#L100) — The `j`-th coordinate `φᵢ : F →ₗ[B] B` of an extension-field presentation, as a `B`-linear map.
- `def MuTwoPowDerandRefutation.coord` [ArkLib/Data/CodingTheory/ProximityGap/MuTwoPowDerandRIMRank.lean:49](../../../ArkLib/Data/CodingTheory/ProximityGap/MuTwoPowDerandRIMRank.lean#L49) — The coordinate (in `Fin 8`) of the edge represented by each row of `rimMatrix`.

### `coreInteractionOracleRbrKnowledgeError` (2 declarations, 2 files)

- `def coreInteractionOracleRbrKnowledgeError` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:1172](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L1172) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleRbrKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1715](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1715) — (no docstring)

### `coreInteractionOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:1142](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L1142) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1675](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1675) — Perfect completeness for the core interaction oracle reduction

### `coreInteractionOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:1180](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L1180) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.coreInteractionOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1724](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1724) — Round-by-round knowledge soundness for the core interaction oracle verifier

### `coreInteractionRbrKnowledgeError` (2 declarations, 2 files)

- `def Binius.RingSwitching.SumcheckPhase.coreInteractionRbrKnowledgeError` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1776](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1776) — standard sumcheck error
- `def RingSwitching.SumcheckPhase.coreInteractionRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1640](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1640) — standard sumcheck error

### `coreInteraction_perfectCompleteness` (2 declarations, 2 files)

- `theorem Binius.RingSwitching.SumcheckPhase.coreInteraction_perfectCompleteness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1735](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1735) — Perfect completeness for large-field reduction (Sumcheck ++ FinalSum)
- `theorem RingSwitching.SumcheckPhase.coreInteraction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1606](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1606) — Perfect completeness for large-field reduction (Sumcheck ++ FinalSum), conditional on the explicit i

### `coreInteraction_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem Binius.RingSwitching.SumcheckPhase.coreInteraction_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1809](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1809) — RBR knowledge soundness for large-field reduction (Sumcheck ++ FinalSum)
- `theorem RingSwitching.SumcheckPhase.coreInteraction_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1651](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1651) — RBR knowledge soundness for large-field reduction (Sumcheck ++ FinalSum)

### `correlatedAgreement_affine_curves_of_lattice_data` (2 declarations, 2 files)

- `theorem ArkLib.BoundaryCardResidual.correlatedAgreement_affine_curves_of_lattice_data` [ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidual.lean:805](../../../ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidual.lean#L805) — [BCIKS20] Theorem 1.5 consuming concrete square-lattice data. This is the data-level counterpart of
- `theorem ArkLib.BoundaryDischarge.correlatedAgreement_affine_curves_of_lattice_data` [ArkLib/ToMathlib/BoundaryDischarge.lean:542](../../../ArkLib/ToMathlib/BoundaryDischarge.lean#L542) — The affine-curves keystone can consume the exact lattice branch through the smaller `BoundaryCardLat

### `correlatedAgreement_affine_curves_of_lattice_data_isSquare` (2 declarations, 2 files)

- `theorem ArkLib.BoundaryCardResidual.correlatedAgreement_affine_curves_of_lattice_data_isSquare` [ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidual.lean:921](../../../ArkLib/Data/CodingTheory/ProximityGap/BoundaryCardResidual.lean#L921) — Curve-facing square-endpoint adapter from concrete lattice data. This is the data-level counterpart
- `theorem ArkLib.BoundaryDischarge.correlatedAgreement_affine_curves_of_lattice_data_isSquare` [ArkLib/ToMathlib/BoundaryDischarge.lean:605](../../../ArkLib/ToMathlib/BoundaryDischarge.lean#L605) — Curve-facing square-endpoint adapter from `BoundaryCardLatticeData`.  This is the lattice-data count

### `decoder` (2 declarations, 2 files)

- `def BerlekampWelch.decoder` [ArkLib/Data/CodingTheory/BerlekampWelch/BerlekampWelch.lean:52](../../../ArkLib/Data/CodingTheory/BerlekampWelch/BerlekampWelch.lean#L52) — Berlekamp-Welch decoder for Reed-Solomon codes. Given received codeword evaluations with potential e
- `def GuruswamiSudan.decoder` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:113](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L113) — Specification-level Guruswami-Sudan decoder. This finite-field specification enumerates all degree-`

### `decompose_rows_packMLE` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.decompose_rows_packMLE` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:598](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L598) — **Row recovery of `t`-evaluations.** The row components of the prover's tensor `ŝ = embedded_MLP_eva
- `lemma RingSwitching.decompose_rows_packMLE` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1188](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1188) — **Row recovery of `t`-evaluations.** The row components of the prover's tensor `ŝ = embedded_MLP_eva

### `decompose_rows_sum` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.decompose_rows_sum` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:552](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L552) — `decompose_tensor_algebra_rows` is additive over finite sums of tensors.
- `lemma RingSwitching.decompose_rows_sum` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:670](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L670) — `decompose_tensor_algebra_rows` is additive over finite sums of tensors.

### `decompose_rows_φ₀φ₁` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.decompose_rows_φ₀φ₁` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:562](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L562) — Row decomposition of a separated tensor `φ₀(a) · φ₁(b) = a ⊗ b`: the `u`-th row component represents
- `lemma RingSwitching.decompose_rows_φ₀φ₁` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:680](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L680) — Row decomposition of a separated tensor `φ₀(a) · φ₁(b) = a ⊗ b`: the `u`-th row component represents

### `decompose_tensor_algebra_columns` (2 declarations, 2 files)

- `def Binius.RingSwitching.decompose_tensor_algebra_columns` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:100](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L100) — Decompose `ŝ` into column components `(ŝ =: Σ_{v ∈ {0,1}^κ} ŝ_v ⊗ β_v)`. This views `L ⊗ L` as a mod
- `def RingSwitching.decompose_tensor_algebra_columns` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:100](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L100) — Decompose `ŝ` into column components `(ŝ =: Σ_{v ∈ {0,1}^κ} ŝ_v ⊗ β_v)`. This views `L ⊗ L` as a mod

### `decompose_tensor_algebra_rows` (2 declarations, 2 files)

- `def Binius.RingSwitching.decompose_tensor_algebra_rows` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:92](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L92) — Decompose `ŝ` into row components `(ŝ =: Σ_{u ∈ {0,1}^κ} β_u ⊗ ŝ_u)`. This views `L ⊗ L` as a module
- `def RingSwitching.decompose_tensor_algebra_rows` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:92](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L92) — Decompose `ŝ` into row components `(ŝ =: Σ_{u ∈ {0,1}^κ} β_u ⊗ ŝ_u)`. This views `L ⊗ L` as a module

### `degree` (2 declarations, 2 files)

- `def UniPoly.degree` [ArkLib/Data/UniPoly/Basic.lean:66](../../../ArkLib/Data/UniPoly/Basic.lean#L66) — Return the degree of a `UniPoly`.
- `def StirIOP.degree` [ArkLib/ProofSystem/Stir/MainThm.lean:45](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L45) — **Degree after `i` folds:** The starting degree is `deg`; every fold divides it by `foldingParamⱼ (j

### `domain_implies_char_ne_2` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:98](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L98) — (no docstring)
- `lemma Domain.FftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/FftDomain/Ops.lean:134](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L134) — (no docstring)

### `domain_sub_eq_div_domain` (2 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.domain_sub_eq_div_domain` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:395](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L395) — (no docstring)
- `lemma Domain.FftDomainClass.domain_sub_eq_div_domain` [ArkLib/Data/Domain/FftDomain/Ops.lean:61](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L61) — (no docstring)

### `duplexSpongeTraceEntry` (2 declarations, 2 files)

- `abbrev OracleSpec.duplexSpongeTraceEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean:371](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Defs.lean#L371) — The type of a single entry in a duplex sponge query trace. Implicit-parameter companion to `DSTraceS
- `abbrev DuplexSpongeFS.DSTraceStorage.duplexSpongeTraceEntry` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceDataStructures.lean:48](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceDataStructures.lean#L48) — A single query-answer entry of a `DuplexSpongeTrace`, i.e. one element of the underlying `QueryLog`

### `embedded_MLP_eval` (2 declarations, 2 files)

- `def Binius.RingSwitching.embedded_MLP_eval` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:320](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L320) — Compute the tensor value ŝ := φ₁(t')(φ₀(r_κ), ..., φ₀(r_{ℓ-1}))
- `def RingSwitching.embedded_MLP_eval` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:329](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L329) — Compute the tensor value ŝ := φ₁(t')(φ₀(r_κ), ..., φ₀(r_{ℓ-1}))

### `embedded_MLP_eval_eq_sum` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.embedded_MLP_eval_eq_sum` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:523](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L523) — **DP24 packing expansion.** The prover's tensor `ŝ := φ₁(t')(φ₀(r_κ), …, φ₀(r_{ℓ-1}))` expands over
- `lemma RingSwitching.embedded_MLP_eval_eq_sum` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1152](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1152) — **DP24 packing expansion.** The prover's tensor `ŝ := φ₁(t')(φ₀(r_κ), …, φ₀(r_{ℓ-1}))` expands over

### `empty` (2 declarations, 2 files)

- `def DuplexSpongeFS.DSTraceStorage.ListBacked.empty` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceDataStructures.lean:530](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Security/TraceDataStructures.lean#L530) — (no docstring)
- `def ProtocolSpec.empty` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:55](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L55) — The empty protocol specification, with no messages or challenges, written as `!p[]`.

### `epsCA_le_one` (2 declarations, 2 files)

- `theorem ProximityGap.epsCA_le_one` [ArkLib/Data/CodingTheory/ProximityGap/Errors.lean:247](../../../ArkLib/Data/CodingTheory/ProximityGap/Errors.lean#L247) — The CA error is bounded by the total probability mass.
- `theorem CodingTheory.Bridge.epsCA_le_one` [ArkLib/ToMathlib/BridgeListDecodingCA.lean:65](../../../ArkLib/ToMathlib/BridgeListDecodingCA.lean#L65) — **`ε_ca ≤ 1`.** The correlated-agreement error is a supremum of values each of which is either `0` o

### `eqPoly_collapse` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.eqPoly_collapse` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:508](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L508) — The full `eqPolynomial` collapses through the mixed embedding to `φ₀` of its ordinary evaluation, by
- `lemma RingSwitching.eqPoly_collapse` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:657](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L657) — The full `eqPolynomial` collapses through the mixed embedding to `φ₀` of its ordinary evaluation, by

### `eqTilde_concat_split` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.eqTilde_concat_split` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:665](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L665) — `eqTilde` of concatenated Boolean / point data factors along the κ/ℓ' split: `eqTilde (concat fp fs)
- `lemma RingSwitching.eqTilde_concat_split` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:758](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L758) — `eqTilde` of concatenated Boolean / point data factors along the κ/ℓ' split: `eqTilde (concat fp fs)

### `eqTilde_prod` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.eqTilde_prod` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:616](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L616) — `eqTilde` written as a product over coordinates of the symmetric Boolean factor.
- `lemma RingSwitching.eqTilde_prod` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:710](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L710) — `eqTilde` written as a product over coordinates of the symmetric Boolean factor.

### `eq_iff_domains_eq` (2 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.eq_iff_domains_eq` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:150](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L150) — (no docstring)
- `lemma Domain.FftDomain.eq_iff_domains_eq` [ArkLib/Data/Domain/FftDomain/Defs.lean:41](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L41) — (no docstring)

### `eq_iff_generators_eq` (2 declarations, 2 files)

- `theorem ReedSolomon.FftDomain.eq_iff_generators_eq` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:497](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L497) — (no docstring)
- `theorem Domain.FftDomainClass.eq_iff_generators_eq` [ArkLib/Data/Domain/FftDomain/Ops.lean:128](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L128) — (no docstring)

### `eval` (2 declarations, 2 files)

- `def UniPoly.eval` [ArkLib/Data/UniPoly/Basic.lean:412](../../../ArkLib/Data/UniPoly/Basic.lean#L412) — Evaluates a `UniPoly` at a given value
- `def Plonk.Gate.eval` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:54](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L54) — Evaluate a gate on a given input vector.

### `eval_fft_domain_eq_eval_domain` (2 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.eval_fft_domain_eq_eval_domain` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:166](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L166) — (no docstring)
- `lemma Domain.FftDomain.eval_fft_domain_eq_eval_domain` [ArkLib/Data/Domain/FftDomain/Defs.lean:61](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L61) — (no docstring)

### `exists_coordinate_subset_with_many_nonbad_of_heavy_complement_card` (2 declarations, 2 files)

- `lemma ProximityGap.exists_coordinate_subset_with_many_nonbad_of_heavy_complement_card` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean:6685](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean#L6685) — Complement-to-incidence form of the heavy-coordinate argument.  If a coordinate is not heavy for the
- `lemma ArkLib.Claim511.exists_coordinate_subset_with_many_nonbad_of_heavy_complement_card` [ArkLib/ToMathlib/Claim511.lean:129](../../../ArkLib/ToMathlib/Claim511.lean#L129) — **Complement-to-incidence selection.** If at least `r` coordinates are *not* heavy (each bad for `<

### `exists_ne_zero_map_eq_zero` (2 declarations, 2 files)

- `theorem GSMultInterp.exists_ne_zero_map_eq_zero` [ArkLib/Data/CodingTheory/GuruswamiSudan/MultiplicityInterpolation.lean:215](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/MultiplicityInterpolation.lean#L215) — **Abstract underdetermined-system existence** (mirrors `BCKHS25.exists_ne_zero_map_eq_zero`): a line
- `theorem BCKHS25.exists_ne_zero_map_eq_zero` [ArkLib/Data/CodingTheory/ProximityGap/BCKHS25/Interpolation.lean:71](../../../ArkLib/Data/CodingTheory/ProximityGap/BCKHS25/Interpolation.lean#L71) — Abstract underdetermined-system existence: a linear map between finite-dimensional spaces with stric

### `exists_subset_card_eq_of_le_card` (2 declarations, 2 files)

- `lemma ProximityGap.exists_subset_card_eq_of_le_card` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean:6635](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean#L6635) — Select exactly `r` elements from a finite set once its cardinality is large enough.  This is the fin
- `lemma ArkLib.Claim511.exists_subset_card_eq_of_le_card` [ArkLib/ToMathlib/Claim511.lean:119](../../../ArkLib/ToMathlib/Claim511.lean#L119) — Select exactly `r` elements from a finite set once its cardinality is large enough.  Final selection

### `extractability` (2 declarations, 2 files)

- `def Commitment.extractability` [ArkLib/CommitmentScheme/Basic.lean:242](../../../ArkLib/CommitmentScheme/Basic.lean#L242) — A commitment scheme satisfies **extractability** with error `extractabilityError` if there exists a
- `def CommitmentScheme.extractability` [ArkLib/CommitmentScheme/CommitmentScheme.lean:159](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L159) — A commitment scheme satisfies **extractability** with error `extractabilityError` if there exists a

### `extractor` (2 declarations, 2 files)

- `def CheckClaim.extractor` [ArkLib/ProofSystem/Component/CheckClaim.lean:167](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L167) — The round-by-round extractor for the `CheckClaim` reduction. Trivial since the witness is `Unit`.
- `def ReduceClaim.extractor` [ArkLib/ProofSystem/Component/ReduceClaim.lean:166](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L166) — The round-by-round extractor for the `ReduceClaim` (oracle) reduction. Requires a mapping `mapWitInv

### `failureProbability` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.failureProbability` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:132](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L132) — Paper-facing alias for CO25 Definition 3.7 failure probability.
- `def Verifier.failureProbability` [ArkLib/OracleReduction/Security/Rewinding.lean:163](../../../ArkLib/OracleReduction/Security/Rewinding.lean#L163) — CO25 Definition 3.7, adapted to ArkLib's non-interactive verifier interface. The paper's size bound

### `failureProbabilityFamily` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.failureProbabilityFamily` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:142](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L142) — Paper-facing alias for CO25 Definition 3.7 with explicit security parameter `λ`.
- `def Verifier.failureProbabilityFamily` [ArkLib/OracleReduction/Security/Rewinding.lean:249](../../../ArkLib/OracleReduction/Security/Rewinding.lean#L249) — CO25 Definition 3.7 with the security parameter `λ` made explicit as an external index.

### `failureState` (2 declarations, 2 files)

- `def Binius.RingSwitching.BatchingPhase.failureState` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:71](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L71) — A dummy state returned by the verifier upon failure of Check 1.
- `def RingSwitching.BatchingPhase.failureState` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:106](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L106) — A dummy state returned by the verifier upon failure of Check 1.

### `fiatShamir_completeness_of_runEq` (2 declarations, 2 files)

- `theorem Reduction.fiatShamir_completeness_of_runEq` [ArkLib/OracleReduction/FiatShamir/Basic.lean:356](../../../ArkLib/OracleReduction/FiatShamir/Basic.lean#L356) — Basic Fiat-Shamir completeness follows from the named run-equality residual and completeness of the
- `theorem Issue116.fiatShamir_completeness_of_runEq` [ArkLib/OracleReduction/FiatShamir/CompletenessUnroll.lean:79](../../../ArkLib/OracleReduction/FiatShamir/CompletenessUnroll.lean#L79) — Forward direction packaged for downstream users: basic FS completeness from the run-equality residua

### `fiatShamir_completeness_unroll_of_runEq` (2 declarations, 2 files)

- `theorem Reduction.fiatShamir_completeness_unroll_of_runEq` [ArkLib/OracleReduction/FiatShamir/Basic.lean:319](../../../ArkLib/OracleReduction/FiatShamir/Basic.lean#L319) — The named run-equality residual is enough to unroll basic-Fiat-Shamir completeness to the explicit h
- `theorem Issue116.fiatShamir_completeness_unroll_of_runEq` [ArkLib/OracleReduction/FiatShamir/CompletenessUnroll.lean:65](../../../ArkLib/OracleReduction/FiatShamir/CompletenessUnroll.lean#L65) — Completeness of the transformed one-message basic Fiat-Shamir reduction is equivalent to the explici

### `finalSumcheckProverComputeMsg` (2 declarations, 2 files)

- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckProverComputeMsg` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:562](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L562) — Pure prover message computation for FRI final sumcheck step.
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckProverComputeMsg` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:986](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L986) — Pure prover message computation: computes s' from the witness.

### `finalSumcheckProverWitOut` (2 declarations, 2 files)

- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckProverWitOut` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:569](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L569) — Pure prover output witness for FRI final sumcheck step.
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckProverWitOut` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:993](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L993) — Pure prover output: computes the output witness given the transcript.

### `finalSumcheckVerifierCheck` (2 declarations, 2 files)

- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckVerifierCheck` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:536](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L536) — Pure verifier check for FRI final sumcheck step.
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckVerifierCheck` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:968](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L968) — Pure verifier check: validates that s_{ℓ'} = eq_tilde_eval * s'. 8. `V` sets `e := eq̃(φ₀(r_κ), ...,

### `finalSumcheckVerifierStmtOut` (2 declarations, 2 files)

- `def Binius.FRIBinius.CoreInteractionPhase.finalSumcheckVerifierStmtOut` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:547](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L547) — Pure verifier output for FRI final sumcheck step.
- `def Binius.RingSwitching.SumcheckPhase.finalSumcheckVerifierStmtOut` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:977](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L977) — Pure verifier output: computes the output statement given the transcript.

### `firstOracleWitnessConsistency_unique` (2 declarations, 2 files)

- `lemma Binius.BinaryBasefold.CoreInteraction.firstOracleWitnessConsistency_unique` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/Fold.lean:762](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/Fold.lean#L762) — (no docstring)
- `lemma Binius.RingSwitching.BBFSmallFieldIOPCS.firstOracleWitnessConsistency_unique` [ArkLib/ProofSystem/Binius/RingSwitching/BBFSmallFieldIOPCS.lean:172](../../../ArkLib/ProofSystem/Binius/RingSwitching/BBFSmallFieldIOPCS.lean#L172) — Uniqueness of the polynomial witness from first-oracle UDR-compatibility.

### `fixVars_eq_bind₁` (2 declarations, 2 files)

- `theorem RingSwitching.fixVars_eq_bind₁` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1547](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1547) — Characterization of `fixFirstVariablesOfMQP` as a `bind₁` partial substitution: it sends the survivi
- `theorem ScratchRS.fixVars_eq_bind₁` [ArkLib/ProofSystem/RingSwitching/Scratch.lean:35](../../../ArkLib/ProofSystem/RingSwitching/Scratch.lean#L35) — (no docstring)

### `fixVars_step` (2 declarations, 2 files)

- `theorem RingSwitching.fixVars_step` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1587](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1587) — **Round-transition for `fixFirstVariablesOfMQP` (cons form).** Fixing the last `v` variables of `pol
- `theorem ScratchRS.fixVars_step` [ArkLib/ProofSystem/RingSwitching/Scratch.lean:47](../../../ArkLib/ProofSystem/RingSwitching/Scratch.lean#L47) — (no docstring)

### `foldOracleReduction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.foldOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/Fold.lean:114](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/Fold.lean#L114) — (no docstring)
- `def Fri.Spec.FoldPhase.foldOracleReduction` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:518](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L518) — The oracle reduction that is the `i`-th round of the FRI protocol.

### `fullOracleVerifier_knowledgeSoundness` (2 declarations, 2 files)

- `theorem Binius.FRIBinius.FullFRIBinius.fullOracleVerifier_knowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:491](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L491) — Scalar KS for the full stack with error **`concreteFRIBiniusKnowledgeError`**, i.e. **DP24 §5.2 (43)
- `theorem Binius.RingSwitching.FullRingSwitching.fullOracleVerifier_knowledgeSoundness` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:503](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L503) — Scalar KS with error `fullRingSwitchingConcreteKnowledgeError κ L ℓ' ε_pcs` (Protocol 3.1 front + `ε

### `getBit_eq_testBit` (2 declarations, 2 files)

- `lemma Binius.BinaryBasefold.QueryPhase.getBit_eq_testBit` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:302](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L302) — (no docstring)
- `lemma Binius.BinaryBasefold.getBit_eq_testBit` [ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/Lift.lean:42](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/Lift.lean#L42) — (no docstring)

### `getEvaluationPointSuffix` (2 declarations, 2 files)

- `def Binius.RingSwitching.getEvaluationPointSuffix` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:377](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L377) — (no docstring)
- `def RingSwitching.getEvaluationPointSuffix` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:385](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L385) — (no docstring)

### `getSumcheckRoundPoly_eval_eq_sum_snoc` (2 declarations, 2 files)

- `theorem RingSwitching.SumcheckPhase.getSumcheckRoundPoly_eval_eq_sum_snoc` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:274](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L274) — **Target (b): `getSumcheckRoundPoly` value as a cube sum (LAST-variable/`snoc` form, defect-#20 repa
- `theorem Sumcheck.Structured.getSumcheckRoundPoly_eval_eq_sum_snoc` [ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean:117](../../../ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L117) — **Round-univariate evaluation as a survivor-cube sum (last-variable / `snoc` form).** Evaluating the

### `guruswami_sudan_for_proximity_gap_existence` (2 declarations, 2 files)

- `lemma GuruswamiSudan.guruswami_sudan_for_proximity_gap_existence` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:758](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L758) — Constructive witness extraction for the Guruswami–Sudan system. When the computable `hasWitnessC` ch
- `lemma ProximityGap.guruswami_sudan_for_proximity_gap_existence` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:201](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L201) — The first part of Lemma 5.3 from [BCIKS20]. Given `D_X` (`proximity_gap_degree_bound`) and `δ₀` (`pr

### `guruswami_sudan_for_proximity_gap_property` (2 declarations, 2 files)

- `lemma GuruswamiSudan.guruswami_sudan_for_proximity_gap_property` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:797](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L797) — Constructive witness property for the Guruswami–Sudan system. When `m > 0` and the codeword polynomi
- `lemma ProximityGap.guruswami_sudan_for_proximity_gap_property` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:213](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L213) — The second part of Lemma 5.3 from [BCIKS20]. For any solution `Q` of the Guruswami-Sudan system, and

### `ham_c0_c1` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.ham_c0_c1` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:44](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L44) — Pairwise Hamming distances.
- `theorem JohnsonBound.JqlRefutation.ham_c0_c1` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:84](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L84) — Pairwise Hamming distances.

### `ham_c0_c2` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.ham_c0_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:45](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L45) — (no docstring)
- `theorem JohnsonBound.JqlRefutation.ham_c0_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:85](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L85) — (no docstring)

### `ham_c1_c2` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.ham_c1_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:46](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L46) — (no docstring)
- `theorem JohnsonBound.JqlRefutation.ham_c1_c2` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:86](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L86) — (no docstring)

### `hasseCoeff` (2 declarations, 2 files)

- `def GSMultInterp.hasseCoeff` [ArkLib/Data/CodingTheory/GuruswamiSudan/MultiplicityInterpolation.lean:136](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/MultiplicityInterpolation.lean#L136) — The order-`(a, b)` *Hasse coefficient* of the bivariate polynomial `Q = ∑_{(s,t)∈monoIdx} c(s,t)·X^s
- `def ArkLib.GS.hasseCoeff` [ArkLib/Data/CodingTheory/ProximityGap/BivariateVanishing.lean:67](../../../ArkLib/Data/CodingTheory/ProximityGap/BivariateVanishing.lean#L67) — The bivariate Hasse–Taylor coefficient of bidegree `(i, j)` of `Q` at `(a, b)`: take the `j`-th oute

### `hasseDeriv_eval_eq_sum` (2 declarations, 2 files)

- `theorem Issue9Hensel.hasseDeriv_eval_eq_sum` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HasseEvalConnectives.lean:29](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HasseEvalConnectives.lean#L29) — (no docstring)
- `theorem Polynomial.hasseDeriv_eval_eq_sum` [ArkLib/ToMathlib/Polynomial/HasseDerivEval.lean:36](../../../ArkLib/ToMathlib/Polynomial/HasseDerivEval.lean#L36) — **Hasse-derivative evaluation identity (★).** The evaluation of the order-`k` Hasse derivative of `p

### `heavyCoords_card_mul_le` (2 declarations, 2 files)

- `lemma ProximityGap.heavyCoords_card_mul_le` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean:6643](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Agreement.lean#L6643) — Generic double-counting brick for Claim 5.11. If each `z ∈ S` has at most `m` bad coordinates, then
- `lemma ArkLib.Claim511.heavyCoords_card_mul_le` [ArkLib/ToMathlib/Claim511.lean:78](../../../ArkLib/ToMathlib/Claim511.lean#L78) — **Double-counting brick.** If each `z ∈ S` has at most `m` bad coordinates, then the coordinates tha

### `hint` (2 declarations, 2 files)

- `def DomainSeparator.hint` [ArkLib/Data/Hash/DomainSep.lean:230](../../../ArkLib/Data/Hash/DomainSep.lean#L230) — Hint `count` native elements. Rust interface: ```rust pub fn hint(self, label: &str) -> Self ```
- `def HashStateWithInstructions.hint` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean:192](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/State.lean#L192) — Process a hint operation. Rust interface: ```rust pub fn hint(&mut self) -> Result<(), DomainSeparat

### `honestTranscriptDist` (2 declarations, 2 files)

- `def Reduction.honestTranscriptDist` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:49](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L49) — The honest transcript distribution of a reduction on input `(stmtIn, witIn)`: run the reduction with
- `def OracleReduction.honestTranscriptDist` [ArkLib/ToMathlib/ZKDefC.lean:36](../../../ArkLib/ToMathlib/ZKDefC.lean#L36) — The honest transcript distribution of an oracle reduction, interpreted via `toReduction`.

### `hypercubeSplitEquiv` (2 declarations, 2 files)

- `def Binius.RingSwitching.hypercubeSplitEquiv` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:715](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L715) — The κ-then-ℓ' hypercube concatenation `concatBit v w i = v i` for `i < κ`, `= w (i - κ)` otherwise —
- `def RingSwitching.hypercubeSplitEquiv` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:807](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L807) — The κ-then-ℓ' hypercube concatenation `concatBit v w i = v i` for `i < κ`, `= w (i - κ)` otherwise —

### `idTranscriptSimulator` (2 declarations, 2 files)

- `def Reduction.idTranscriptSimulator` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:288](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L288) — The simulator for the zero-round identity reduction: ignore the statement and emit the unique empty
- `abbrev OracleReduction.idTranscriptSimulator` [ArkLib/ToMathlib/ZKDefC.lean:98](../../../ArkLib/ToMathlib/ZKDefC.lean#L98) — The simulator for the zero-round identity oracle reduction.

### `id_isStatHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.id_isStatHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:255](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L255) — The zero-round identity oracle reduction is statistical HVZK for any oracle-input relation and any e
- `theorem Reduction.id_isStatHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:341](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L341) — The zero-round identity reduction is statistically honest-verifier zero-knowledge for any relation a

### `id_statisticalHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.id_statisticalHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:231](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L231) — The zero-round identity oracle reduction is statistical HVZK for any oracle-input relation and any e
- `theorem Reduction.id_statisticalHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:323](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L323) — The zero-round identity reduction satisfies statistical honest-verifier zero-knowledge for any relat

### `instFintypeOracleSpecEmpty` (2 declarations, 2 files)

- `instance Binius.RingSwitching.instFintypeOracleSpecEmpty` [ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean:142](../../../ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean#L142) — (no docstring)
- `instance RingSwitching.instFintypeOracleSpecEmpty` [ArkLib/ProofSystem/RingSwitching/Spec.lean:129](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L129) — (no docstring)

### `instFintypePSpecSumcheckRoundChallenge` (2 declarations, 2 files)

- `instance Binius.RingSwitching.instFintypePSpecSumcheckRoundChallenge` [ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean:189](../../../ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean#L189) — (no docstring)
- `instance RingSwitching.instFintypePSpecSumcheckRoundChallenge` [ArkLib/ProofSystem/RingSwitching/Spec.lean:132](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L132) — (no docstring)

### `instInhabitedOracleSpecEmpty` (2 declarations, 2 files)

- `instance Binius.RingSwitching.instInhabitedOracleSpecEmpty` [ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean:139](../../../ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean#L139) — (no docstring)
- `instance RingSwitching.instInhabitedOracleSpecEmpty` [ArkLib/ProofSystem/RingSwitching/Spec.lean:126](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L126) — (no docstring)

### `instInhabitedPSpecSumcheckRoundChallenge` (2 declarations, 2 files)

- `instance Binius.RingSwitching.instInhabitedPSpecSumcheckRoundChallenge` [ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean:203](../../../ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean#L203) — (no docstring)
- `instance RingSwitching.instInhabitedPSpecSumcheckRoundChallenge` [ArkLib/ProofSystem/RingSwitching/Spec.lean:146](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L146) — (no docstring)

### `instOracleVerifierAppendCoherent` (2 declarations, 2 files)

- `instance RingSwitching.BatchingPhase.instOracleVerifierAppendCoherent` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:219](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L219) — The batching-phase oracle verifier passes every output oracle through to the unchanged input oracle
- `instance Sumcheck.Spec.SingleRound.instOracleVerifierAppendCoherent` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1360](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1360) — The `i`-th-round oracle verifier routes its (single) output oracle to the (unchanged) input oracle (

### `instOstmtMLIOPCS` (2 declarations, 2 files)

- `instance Binius.RingSwitching.instOstmtMLIOPCS` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:294](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L294) — (no docstring)
- `instance RingSwitching.instOstmtMLIOPCS` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:305](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L305) — (no docstring)

### `interpolate` (2 declarations, 2 files)

- `def ReedSolomon.interpolate` [ArkLib/Data/CodingTheory/ReedSolomon.lean:631](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L631) — The linear map that maps a codeword `f : ι → F` to a degree < \|ι\| polynomial p, such that `p(x) = f(
- `def UniPoly.Lagrange.interpolate` [ArkLib/Data/UniPoly/Basic.lean:1120](../../../ArkLib/Data/UniPoly/Basic.lean#L1120) — This function produces the polynomial which is of degree n and is equal to r i at ω^i for i = 0, 1,

### `isHVZK.congr_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.congr_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:397](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L397) — **OracleReduction `isHVZK` transfers along an equal honest distribution.**
- `theorem Reduction.isHVZK.congr_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:480](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L480) — **`isHVZK` transfers along an `evalDist`-equal honest distribution.**

### `isHVZK.congr_honestDist_symm` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.congr_honestDist_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:424](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L424) — **OracleReduction `isHVZK` honest-distribution congruence with opposite-order equality.**
- `theorem Reduction.isHVZK.congr_honestDist_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:506](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L506) — **`isHVZK` honest-distribution congruence with opposite-order equality.**

### `isHVZK.isStatHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.isStatHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:151](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L151) — Perfect HVZK existence for oracle reductions implies statistical HVZK existence.
- `theorem Reduction.isHVZK.isStatHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:198](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L198) — **Perfect HVZK implies statistical HVZK existence** at any error.

### `isHVZK.mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.mono_relation` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:118](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L118) — `isHVZK` for oracle reductions is antitone in the relation.
- `theorem Reduction.isHVZK.mono_relation` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:167](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L167) — **`isHVZK` is antitone in the relation.** HVZK for `rel` implies HVZK for any `rel' ⊆ rel` (the same

### `isHVZK.triangle_honestDist_symm_zero` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.triangle_honestDist_symm_zero` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:523](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L523) — **Existential symmetric-facing zero-error approximate honest-distribution transfer for exact HVZK at
- `theorem Reduction.isHVZK.triangle_honestDist_symm_zero` [ArkLib/ToMathlib/ZKTransferBricks.lean:597](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L597) — **Existential symmetric-facing zero-error approximate honest-distribution transfer for exact HVZK.**

### `isHVZK.triangle_honestDist_zero` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK.triangle_honestDist_zero` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:509](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L509) — **Existential zero-error approximate honest-distribution transfer for exact HVZK at the OracleReduct
- `theorem Reduction.isHVZK.triangle_honestDist_zero` [ArkLib/ToMathlib/ZKTransferBricks.lean:583](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L583) — **Existential zero-error approximate honest-distribution transfer for exact HVZK.**

### `isHVZK_iff_isStatHVZK_zero` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK_iff_isStatHVZK_zero` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:174](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L174) — Perfect HVZK existence for oracle reductions is equivalent to zero-error statistical HVZK existence.
- `theorem Reduction.isHVZK_iff_isStatHVZK_zero` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:218](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L218) — **Perfect HVZK existence is equivalent to zero-error statistical HVZK existence.**

### `isHVZK_of_const_eq_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK_of_const_eq_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:372](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L372) — **OracleReduction `isHVZK` from the symmetric-facing constant-simulator criterion.**
- `theorem Reduction.isHVZK_of_const_eq_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:455](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L455) — **`isHVZK` from the symmetric-facing constant-simulator criterion.**

### `isHVZK_of_honestDist_eq_const` (2 declarations, 2 files)

- `theorem OracleReduction.isHVZK_of_honestDist_eq_const` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:347](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L347) — **OracleReduction `isHVZK` from the constant-simulator criterion.**
- `theorem Reduction.isHVZK_of_honestDist_eq_const` [ArkLib/ToMathlib/ZKTransferBricks.lean:432](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L432) — **`isHVZK` from the constant-simulator criterion.**

### `isStatHVZK` (2 declarations, 2 files)

- `def OracleReduction.isStatHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:71](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L71) — Existential statistical HVZK for an oracle reduction.
- `def Reduction.isStatHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:98](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L98) — A reduction is *statistically* honest-verifier zero-knowledge with error `ε` if some simulator achie

### `isStatHVZK.congr_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.congr_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:410](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L410) — **OracleReduction `isStatHVZK` transfers along an equal honest distribution.**
- `theorem Reduction.isStatHVZK.congr_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:493](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L493) — **`isStatHVZK` transfers along an `evalDist`-equal honest distribution.**

### `isStatHVZK.congr_honestDist_symm` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.congr_honestDist_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:436](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L436) — **OracleReduction `isStatHVZK` honest-distribution congruence with opposite-order equality.**
- `theorem Reduction.isStatHVZK.congr_honestDist_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:518](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L518) — **`isStatHVZK` honest-distribution congruence with opposite-order equality.**

### `isStatHVZK.mono_error` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.mono_error` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:198](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L198) — `isStatHVZK` for oracle reductions is monotone in the error bound.
- `theorem Reduction.isStatHVZK.mono_error` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:240](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L240) — **`isStatHVZK` is monotone in the error.**

### `isStatHVZK.mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.mono_relation` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:187](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L187) — `isStatHVZK` for oracle reductions is antitone in the relation.
- `theorem Reduction.isStatHVZK.mono_relation` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:230](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L230) — **`isStatHVZK` is antitone in the relation.**

### `isStatHVZK.triangle_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.triangle_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:449](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L449) — **Existential approximate honest-distribution transfer at the OracleReduction API boundary.**
- `theorem Reduction.isStatHVZK.triangle_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:530](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L530) — **Existential approximate honest-distribution transfer for statistical HVZK.**

### `isStatHVZK.triangle_honestDist_symm` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.triangle_honestDist_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:464](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L464) — **Existential symmetric-facing approximate honest-distribution transfer at the OracleReduction API b
- `theorem Reduction.isStatHVZK.triangle_honestDist_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:543](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L543) — **Existential symmetric-facing approximate honest-distribution transfer.**

### `isStatHVZK.triangle_honestDist_symm_zero` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.triangle_honestDist_symm_zero` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:494](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L494) — **Existential symmetric-facing zero-error approximate honest-distribution transfer for statistical H
- `theorem Reduction.isStatHVZK.triangle_honestDist_symm_zero` [ArkLib/ToMathlib/ZKTransferBricks.lean:570](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L570) — **Existential symmetric-facing zero-error approximate honest-distribution transfer for statistical H

### `isStatHVZK.triangle_honestDist_zero` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK.triangle_honestDist_zero` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:479](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L479) — **Existential zero-error approximate honest-distribution transfer for statistical HVZK at the Oracle
- `theorem Reduction.isStatHVZK.triangle_honestDist_zero` [ArkLib/ToMathlib/ZKTransferBricks.lean:556](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L556) — **Existential zero-error approximate honest-distribution transfer for statistical HVZK.**

### `isStatHVZK_of_const_eq_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK_of_const_eq_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:384](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L384) — **OracleReduction `isStatHVZK` from the symmetric-facing constant-simulator criterion.**
- `theorem Reduction.isStatHVZK_of_const_eq_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:467](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L467) — **`isStatHVZK` from the symmetric-facing constant-simulator criterion.**

### `isStatHVZK_of_honestDist_eq_const` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK_of_honestDist_eq_const` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:359](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L359) — **OracleReduction `isStatHVZK` from the constant-simulator criterion.**
- `theorem Reduction.isStatHVZK_of_honestDist_eq_const` [ArkLib/ToMathlib/ZKTransferBricks.lean:443](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L443) — **`isStatHVZK` from the constant-simulator criterion.**

### `isStatHVZK_zero.isHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.isStatHVZK_zero.isHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:162](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L162) — Zero-error statistical HVZK existence for oracle reductions recovers perfect HVZK existence.
- `theorem Reduction.isStatHVZK_zero.isHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:208](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L208) — **Zero-error statistical HVZK existence is perfect HVZK existence.**

### `iteratedSumcheckKStateProp` (2 declarations, 2 files)

- `def Binius.RingSwitching.SumcheckPhase.iteratedSumcheckKStateProp` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:563](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L563) — KState for the iterated sumcheck step, matching the structure of Binary Basefold's `foldKStateProp`:
- `def RingSwitching.SumcheckPhase.iteratedSumcheckKStateProp` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:729](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L729) — This follows the KState of `foldKStateProp`

### `iteratedSumcheckKnowledgeStateFunction` (2 declarations, 2 files)

- `def Binius.RingSwitching.SumcheckPhase.iteratedSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:606](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L606) — Knowledge state function (KState) for single round
- `def RingSwitching.SumcheckPhase.iteratedSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:789](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L789) — Knowledge state function (KState) for single round

### `iteratedSumcheckOracleProver` (2 declarations, 2 files)

- `def Binius.RingSwitching.SumcheckPhase.iteratedSumcheckOracleProver` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:156](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L156) — The prover for the `i`-th round of Ring Switching.
- `def RingSwitching.SumcheckPhase.iteratedSumcheckOracleProver` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:136](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L136) — (no docstring)

### `iteratedSumcheckOracleReduction` (2 declarations, 2 files)

- `def Binius.RingSwitching.SumcheckPhase.iteratedSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:220](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L220) — The oracle reduction that is the `i`-th round of Ring Switching.
- `def RingSwitching.SumcheckPhase.iteratedSumcheckOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:161](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L161) — (no docstring)

### `iteratedSumcheckOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem Binius.RingSwitching.SumcheckPhase.iteratedSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:333](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L333) — (no docstring)
- `theorem RingSwitching.SumcheckPhase.iteratedSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:208](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L208) — Iterated-sumcheck round completeness from the explicit local algebraic residual.

### `iteratedSumcheckOracleVerifier` (2 declarations, 2 files)

- `def Binius.RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:191](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L191) — The oracle verifier for the `i`-th round of Ring Switching.
- `def RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:149](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L149) — (no docstring)

### `iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem Binius.RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:888](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L888) — RBR knowledge soundness for a single round oracle verifier
- `theorem RingSwitching.SumcheckPhase.iteratedSumcheckOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1065](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1065) — (no docstring)

### `iteratedSumcheckPrvState` (2 declarations, 2 files)

- `def Binius.RingSwitching.SumcheckPhase.iteratedSumcheckPrvState` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:146](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L146) — The state maintained by the prover throughout the sumcheck phase.
- `def RingSwitching.SumcheckPhase.iteratedSumcheckPrvState` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:123](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L123) — (no docstring)

### `iteratedSumcheckRbrExtractor` (2 declarations, 2 files)

- `def Binius.RingSwitching.SumcheckPhase.iteratedSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:535](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L535) — (no docstring)
- `def RingSwitching.SumcheckPhase.iteratedSumcheckRbrExtractor` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:546](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L546) — (no docstring)

### `iteratedSumcheckRoundKnowledgeError` (2 declarations, 2 files)

- `def Binius.RingSwitching.SumcheckPhase.iteratedSumcheckRoundKnowledgeError` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:524](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L524) — (no docstring)
- `def RingSwitching.SumcheckPhase.iteratedSumcheckRoundKnowledgeError` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1637](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1637) — Per-round knowledge error for the iterated sumcheck rounds.

### `iteratedSumcheckWitMid` (2 declarations, 2 files)

- `def Binius.RingSwitching.SumcheckPhase.iteratedSumcheckWitMid` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:529](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L529) — Witness type at each message index for the iterated sumcheck step (counterpart of BBF `foldWitMid`).
- `def RingSwitching.SumcheckPhase.iteratedSumcheckWitMid` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:540](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L540) — (no docstring)

### `iteratedSumcheck_doom_escape_probability_bound` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.SumcheckPhase.iteratedSumcheck_doom_escape_probability_bound` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:819](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L819) — Per-transcript bound: for prover message h_i, the probability (over verifier challenge y) that extra
- `lemma RingSwitching.SumcheckPhase.iteratedSumcheck_doom_escape_probability_bound` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1004](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1004) — **Schwartz-Zippel bound for the bad sumcheck extraction event.** Proof strategy (follows `foldStep_d

### `iteratedSumcheck_rbrExtractionFailureEvent_imply_badSumcheck` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.SumcheckPhase.iteratedSumcheck_rbrExtractionFailureEvent_imply_badSumcheck` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:732](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L732) — Extraction failure implies a witness-dependent bad sumcheck event (no folding here). The extracted `
- `lemma RingSwitching.SumcheckPhase.iteratedSumcheck_rbrExtractionFailureEvent_imply_badSumcheck` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:900](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L900) — Extraction failure implies a witness-dependent bad sumcheck event. The extracted `witMid` also carri

### `iterated_fold_to_const_strict` (2 declarations, 2 files)

- `lemma Binius.BinaryBasefold.CoreInteraction.iterated_fold_to_const_strict` [ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:969](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean#L969) — **Strict version**: When folding the last oracle to level `ℓ` (final sumcheck), the iterated fold of
- `lemma Binius.FRIBinius.CoreInteractionPhase.iterated_fold_to_const_strict` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:730](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L730) — Strict helper: folding the last oracle block in the final sumcheck step yields the constant function

### `knowledgeSoundness.mono_error` (2 declarations, 2 files)

- `theorem Verifier.knowledgeSoundness.mono_error` [ArkLib/OracleReduction/Security/Basic.lean:439](../../../ArkLib/OracleReduction/Security/Basic.lean#L439) — Straightline knowledge soundness is monotone in the allowed knowledge error.
- `theorem Verifier.StateRestoration.knowledgeSoundness.mono_error` [ArkLib/OracleReduction/Security/StateRestoration.lean:218](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L218) — State-restoration knowledge soundness is monotone in the allowed knowledge-soundness error.

### `knowledgeSoundness.mono_relations` (2 declarations, 2 files)

- `theorem Verifier.knowledgeSoundness.mono_relations` [ArkLib/OracleReduction/Security/Basic.lean:455](../../../ArkLib/OracleReduction/Security/Basic.lean#L455) — Straightline knowledge soundness is monotone in the input and output relations. If knowledge soundne
- `theorem Verifier.StateRestoration.knowledgeSoundness.mono_relations` [ArkLib/OracleReduction/Security/StateRestoration.lean:232](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L232) — State-restoration knowledge soundness is monotone under enlarging the valid input relation and shrin

### `lambda_le_ggr11_of_Lambda_top` (2 declarations, 2 files)

- `theorem InterleavedCode.GGR11.lambda_le_ggr11_of_Lambda_top` [ArkLib/ToMathlib/GGR11Interleaved.lean:404](../../../ArkLib/ToMathlib/GGR11Interleaved.lean#L404) — Generic end-to-end infinite-list regime: if the base list size is infinite and the Red budget is pos
- `theorem InterleavedCode.GGR11Reconnect.lambda_le_ggr11_of_Lambda_top` [ArkLib/ToMathlib/GGR11Reconnect.lean:134](../../../ArkLib/ToMathlib/GGR11Reconnect.lean#L134) — **Infinite-list regime, reconnected.** When the base list size is infinite and the GGR11 Red budget

### `lambda_le_ggr11_of_le_exp` (2 declarations, 2 files)

- `theorem InterleavedCode.GGR11.lambda_le_ggr11_of_le_exp` [ArkLib/ToMathlib/GGR11Interleaved.lean:394](../../../ArkLib/ToMathlib/GGR11Interleaved.lean#L394) — Generic end-to-end elementary regime: if the Red budget already dominates the interleaving factor, t
- `theorem InterleavedCode.GGR11Reconnect.lambda_le_ggr11_of_le_exp` [ArkLib/ToMathlib/GGR11Reconnect.lean:122](../../../ArkLib/ToMathlib/GGR11Reconnect.lean#L122) — **Elementary regime, reconnected.** When the GGR11 Red budget already dominates the interleaving fac

### `lambda_le_ggr11_of_perWordBound` (2 declarations, 2 files)

- `theorem InterleavedCode.GGR11.lambda_le_ggr11_of_perWordBound` [ArkLib/ToMathlib/GGR11Interleaved.lean:118](../../../ArkLib/ToMathlib/GGR11Interleaved.lean#L118) — **Reduction of the GGR11 interleaved list-size bound to its per-word form.** Given the per-received-
- `theorem InterleavedCode.GGR11Reconnect.lambda_le_ggr11_of_perWordBound` [ArkLib/ToMathlib/GGR11Reconnect.lean:110](../../../ArkLib/ToMathlib/GGR11Reconnect.lean#L110) — **Reconnect (per-word form).** The bare bound follows from the (coarser) per-received-word residual

### `lambda_le_ggr11_of_treeFrontier` (2 declarations, 2 files)

- `theorem InterleavedCode.GGR11.lambda_le_ggr11_of_treeFrontier` [ArkLib/ToMathlib/GGR11Interleaved.lean:291](../../../ArkLib/ToMathlib/GGR11Interleaved.lean#L291) — End-to-end GGR11 list-size bound from the granular named frontier.
- `theorem InterleavedCode.GGR11Reconnect.lambda_le_ggr11_of_treeFrontier` [ArkLib/ToMathlib/GGR11Reconnect.lean:100](../../../ArkLib/ToMathlib/GGR11Reconnect.lean#L100) — **Reconnect (named frontier form).** The bare bound follows from the granular per-received-word `GGR

### `lambda_le_ggr11_of_treeStructure` (2 declarations, 2 files)

- `theorem InterleavedCode.GGR11.lambda_le_ggr11_of_treeStructure` [ArkLib/ToMathlib/GGR11Interleaved.lean:283](../../../ArkLib/ToMathlib/GGR11Interleaved.lean#L283) — **End-to-end:** the GGR11 interleaved list-size bound from the refined tree-existence residual.
- `theorem InterleavedCode.GGR11Reconnect.lambda_le_ggr11_of_treeStructure` [ArkLib/ToMathlib/GGR11Reconnect.lean:90](../../../ArkLib/ToMathlib/GGR11Reconnect.lean#L90) — **Reconnect (tree-existence form).** The bare `InterleavedCode.lambda_le_ggr11` bound follows from t

### `leftpad` (2 declarations, 2 files)

- `def Fin.leftpad` [ArkLib/Data/Fin/Tuple/Defs.lean:96](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L96) — Pad a `Fin`-indexed vector on the left with an element `a`. This becomes truncation if `n < m`.
- `def Matrix.leftpad` [ArkLib/Data/Matrix/Basic.lean:25](../../../ArkLib/Data/Matrix/Basic.lean#L25) — (no docstring)

### `liftContext_completeness` (2 declarations, 2 files)

- `theorem OracleReduction.liftContext_completeness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:242](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L242) — STATEMENT REPAIR (2026-06-04): completeness lifting now additionally takes the verifier's oracle-rou
- `theorem Reduction.liftContext_completeness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:776](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L776) — Lifting the reduction preserves completeness, assuming the lens satisfies its completeness condition

### `liftContext_knowledgeSoundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:292](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L292) — (no docstring)
- `theorem Verifier.liftContext_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:928](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L928) — (no docstring)

### `liftContext_perfectCompleteness` (2 declarations, 2 files)

- `theorem OracleReduction.liftContext_perfectCompleteness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:252](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L252) — (no docstring)
- `theorem Reduction.liftContext_perfectCompleteness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:881](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L881) — (no docstring)

### `liftContext_rbr_knowledgeSoundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_rbr_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:351](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L351) — (no docstring)
- `theorem Verifier.liftContext_rbr_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:1674](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L1674) — (no docstring)

### `liftContext_rbr_soundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_rbr_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:312](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L312) — (no docstring)
- `theorem Verifier.liftContext_rbr_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:1425](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L1425) — (no docstring)

### `liftContext_soundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:276](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L276) — Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions. STA
- `theorem Verifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:902](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L902) — Lifting a verifier context preserves soundness, supplied as an explicit residual.

### `list_reduceOption_helper` (2 declarations, 2 files)

- `lemma ReedSolomon.Finset.list_reduceOption_helper` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:256](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L256) — (no docstring)
- `lemma Finset.list_reduceOption_helper` [ArkLib/ToMathlib/Finset/ToListWithProof.lean:43](../../../ArkLib/ToMathlib/Finset/ToListWithProof.lean#L43) — (no docstring)

### `map` (2 declarations, 2 files)

- `def AGM.GroupRepresentation.map` [ArkLib/AGM/Basic.lean:109](../../../ArkLib/AGM/Basic.lean#L109) — **Functoriality of representations under group homomorphisms.** A group hom `f : G →* H` transports
- `def Fin.map` [ArkLib/Data/Fin/Sigma.lean:499](../../../ArkLib/Data/Fin/Sigma.lean#L499) — (no docstring)

### `mapEquiv` (2 declarations, 2 files)

- `def Probability.SizeSubset.mapEquiv` [ArkLib/Data/Probability/Combinatorial.lean:92](../../../ArkLib/Data/Probability/Combinatorial.lean#L92) — Transport a size-`n` subset across an equivalence of ambient types.
- `def Probability.SizedSubset.mapEquiv` [ArkLib/Data/Probability/UniformSubset.lean:54](../../../ArkLib/Data/Probability/UniformSubset.lean#L54) — Map an `n`-element subset across an equivalence of ambient finite types.

### `mem_C_iff` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.mem_C_iff` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:49](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L49) — Membership in `C` is membership in the explicit three-element set.
- `theorem JohnsonBound.JqlRefutation.mem_C_iff` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:89](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L89) — Membership in `C` is membership in the explicit three-element set.

### `mem_subgroup_iff_mem_domain` (2 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.mem_subgroup_iff_mem_domain` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:324](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L324) — (no docstring)
- `lemma Domain.FftDomainClass.mem_subgroup_iff_mem_domain` [ArkLib/Data/Domain/FftDomain/ToSubgroup.lean:67](../../../ArkLib/Data/Domain/FftDomain/ToSubgroup.lean#L67) — (no docstring)

### `mem_subgroup_iff_mem_finset` (2 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.mem_subgroup_iff_mem_finset` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:318](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L318) — (no docstring)
- `lemma Domain.FftDomainClass.mem_subgroup_iff_mem_finset` [ArkLib/Data/Domain/FftDomain/ToSubgroup.lean:60](../../../ArkLib/Data/Domain/FftDomain/ToSubgroup.lean#L60) — (no docstring)

### `mem_support_simulateQ_id'_liftM_query` (2 declarations, 2 files)

- `lemma OptionT.mem_support_simulateQ_id'_liftM_query` [ArkLib/ToVCVio/Lemmas.lean:430](../../../ArkLib/ToVCVio/Lemmas.lean#L430) — **Generic**: any element of the range of a query is in the support of `simulateQ (fun t => liftM (qu
- `lemma mem_support_simulateQ_id'_liftM_query` [ArkLib/ToVCVio/Simulation.lean:217](../../../ArkLib/ToVCVio/Simulation.lean#L217) — (no docstring)

### `minDist_C` (2 declarations, 2 files)

- `theorem JohnsonBound.FamilyRefutation.minDist_C` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean:54](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutation.lean#L54) — Every distinct pair of codewords has Hamming distance `≥ 1`, and the pair `(c0, c1)` attains `1`. He
- `theorem JohnsonBound.JqlRefutation.minDist_C` [ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean:97](../../../ArkLib/Data/CodingTheory/JohnsonBound/FamilyRefutationComplete.lean#L97) — **`Code.minDist C = 1`.**  The defining set of distinct-pair distances is `{1, 2}` (`d(c0,c1) = d(c0

### `mk_eq_trunc_of_tail_zero` (2 declarations, 2 files)

- `theorem ArkLib.BetaToCurveCoeffPolys.mk_eq_trunc_of_tail_zero` [ArkLib/ToMathlib/BetaToCurveCoeffPolysOffcentre.lean:86](../../../ArkLib/ToMathlib/BetaToCurveCoeffPolysOffcentre.lean#L86) — A power series whose coefficients vanish from index `k` on **is** (the coercion of) its `k`-truncati
- `theorem PowerSeries.mk_eq_trunc_of_tail_zero` [ArkLib/ToMathlib/ExtractedIssueBricks.lean:77](../../../ArkLib/ToMathlib/ExtractedIssueBricks.lean#L77) — A power series whose coefficients vanish from index `k` on equals the coercion of its `k`-truncation

### `multilinearWeight` (2 declarations, 2 files)

- `def multilinearWeight` [ArkLib/Data/CodingTheory/Prelims.lean:23](../../../ArkLib/Data/CodingTheory/Prelims.lean#L23) — The tensor product weight `⊗_{i=0}^{ϑ-1}(1 - rᵢ, rᵢ)` for a specific index `i` given randomness `r`.
- `def Issue33Binius.multilinearWeight` [ArkLib/ProofSystem/Binius/BinaryBasefold/MultilinearWeightRecursion.lean:24](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/MultilinearWeightRecursion.lean#L24) — Tensor product weight `⊗_{j<ϑ}(1 - r_j, r_j)` at index `i` given challenges `r`. This is a verbatim

### `natDegree_taylor_lt` (2 declarations, 2 files)

- `theorem ArkLib.BetaToCurveCoeffPolys.natDegree_taylor_lt` [ArkLib/ToMathlib/BetaToCurveCoeffPolysOffcentre.lean:141](../../../ArkLib/ToMathlib/BetaToCurveCoeffPolysOffcentre.lean#L141) — Taylor shift preserves the strict degree bound of a coefficient profile.
- `theorem Polynomial.natDegree_taylor_lt` [ArkLib/ToMathlib/ExtractedIssueBricks.lean:67](../../../ArkLib/ToMathlib/ExtractedIssueBricks.lean#L67) — A strict degree bound transports through a Taylor shift.

### `neg_one_mem_domain` (2 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.neg_one_mem_domain` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:419](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L419) — (no docstring)
- `lemma Domain.FftDomainClass.neg_one_mem_domain` [ArkLib/Data/Domain/FftDomain/Ops.lean:82](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L82) — (no docstring)

### `one_le_Lambda_of_nonempty` (2 declarations, 2 files)

- `theorem CodingTheory.one_le_Lambda_of_nonempty` [ArkLib/Data/CodingTheory/ListSizeVolumeBound.lean:184](../../../ArkLib/Data/CodingTheory/ListSizeVolumeBound.lean#L184) — **List-size lower bound `1 ≤ \|Λ(C,δ)\|` for a nonempty code and `δ ≥ 0`.** Any codeword is `0`-close
- `lemma InterleavedCode.GGR11.one_le_Lambda_of_nonempty` [ArkLib/ToMathlib/GGR11TreeConstruction.lean:1247](../../../ArkLib/ToMathlib/GGR11TreeConstruction.lean#L1247) — With a nonempty code, a nonnegative radius, and finite lists, the maximised list size is at least on

### `oracleVerifier_toVerifier_run` (2 declarations, 2 files)

- `theorem ReduceClaim.oracleVerifier_toVerifier_run` [ArkLib/ProofSystem/Component/ReduceClaim.lean:267](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L267) — Running the (oracle) verifier of the `ReduceClaim` oracle reduction deterministically returns the ma
- `theorem SendSingleWitness.oracleVerifier_toVerifier_run` [ArkLib/ProofSystem/Component/SendWitness.lean:383](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L383) — (no docstring)

### `pSpecBatching` (2 declarations, 2 files)

- `def Binius.RingSwitching.pSpecBatching` [ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean:54](../../../ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean#L54) — (no docstring)
- `def RingSwitching.pSpecBatching` [ArkLib/ProofSystem/RingSwitching/Spec.lean:34](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L34) — (no docstring)

### `pSpecFinalSumcheck` (2 declarations, 2 files)

- `def Binius.RingSwitching.pSpecFinalSumcheck` [ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean:64](../../../ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean#L64) — (no docstring)
- `def RingSwitching.pSpecFinalSumcheck` [ArkLib/ProofSystem/RingSwitching/Spec.lean:47](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L47) — (no docstring)

### `pSpecFold` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.pSpecFold` [ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean:201](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean#L201) — (no docstring)
- `def Fri.Spec.pSpecFold` [ArkLib/ProofSystem/Fri/Spec/General.lean:66](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L66) — (no docstring)

### `pSpecLargeFieldReduction` (2 declarations, 2 files)

- `def Binius.RingSwitching.pSpecLargeFieldReduction` [ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean:70](../../../ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean#L70) — (no docstring)
- `def RingSwitching.pSpecLargeFieldReduction` [ArkLib/ProofSystem/RingSwitching/Spec.lean:53](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L53) — (no docstring)

### `pSpecSumcheckLoop` (2 declarations, 2 files)

- `def Binius.RingSwitching.pSpecSumcheckLoop` [ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean:61](../../../ArkLib/ProofSystem/Binius/RingSwitching/Spec.lean#L61) — (no docstring)
- `def RingSwitching.pSpecSumcheckLoop` [ArkLib/ProofSystem/RingSwitching/Spec.lean:45](../../../ArkLib/ProofSystem/RingSwitching/Spec.lean#L45) — (no docstring)

### `packMLE` (2 declarations, 2 files)

- `def Binius.RingSwitching.packMLE` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:114](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L114) — **Definition 2.1 (MLE packing)**. Packs a small-field multilinear `t` into a large-field multilinear
- `def RingSwitching.packMLE` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:114](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L114) — **Definition 2.1 (MLE packing)**. Packs a small-field multilinear `t` into a large-field multilinear

### `packMLE_repr_eval` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.packMLE_repr_eval` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:575](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L575) — The basis coordinate of a packed evaluation recovers the small-field coefficient: `β.repr (t'(w)) u
- `lemma RingSwitching.packMLE_repr_eval` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:693](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L693) — The basis coordinate of a packed evaluation recovers the small-field coefficient: `β.repr (t'(w)) u

### `perfectCorrectness` (2 declarations, 2 files)

- `def Commitment.perfectCorrectness` [ArkLib/CommitmentScheme/Basic.lean:109](../../../ArkLib/CommitmentScheme/Basic.lean#L109) — A commitment scheme satisfies **perfect correctness** if it satisfies correctness with no error.
- `def CommitmentScheme.perfectCorrectness` [ArkLib/CommitmentScheme/CommitmentScheme.lean:74](../../../ArkLib/CommitmentScheme/CommitmentScheme.lean#L74) — A commitment scheme satisfies **perfect correctness** if it satisfies correctness with no error.

### `perfectHVZK.congr_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.congr_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:33](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L33) — **OracleReduction perfect HVZK transfers along an equal honest distribution.**
- `theorem Reduction.perfectHVZK.congr_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:64](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L64) — **Perfect HVZK transfers along an `evalDist`-equal honest distribution.** If two reductions have the

### `perfectHVZK.congr_honestDist_symm` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.congr_honestDist_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:59](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L59) — **OracleReduction perfect HVZK honest-distribution congruence with opposite-order equality.**
- `theorem Reduction.perfectHVZK.congr_honestDist_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:96](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L96) — **Perfect HVZK honest-distribution congruence with opposite-order equality.**

### `perfectHVZK.isHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.isHVZK` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:130](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L130) — **A concrete OracleReduction perfect-HVZK simulator witnesses existential HVZK.**
- `theorem Reduction.perfectHVZK.isHVZK` [ArkLib/ToMathlib/ZKTransferBricks.lean:174](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L174) — **A concrete perfect-HVZK simulator witnesses existential HVZK.**

### `perfectHVZK.isHVZK_of_simulator_congr` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.isHVZK_of_simulator_congr` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:152](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L152) — **Package an OracleReduction perfect-HVZK proof after normalizing the simulator distribution.**
- `theorem Reduction.perfectHVZK.isHVZK_of_simulator_congr` [ArkLib/ToMathlib/ZKTransferBricks.lean:194](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L194) — **Package a perfect-HVZK proof after normalizing the simulator distribution.**

### `perfectHVZK.isHVZK_of_simulator_congr_symm` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.isHVZK_of_simulator_congr_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:176](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L176) — **Package an OracleReduction perfect-HVZK proof after simulator normalization in the opposite direct
- `theorem Reduction.perfectHVZK.isHVZK_of_simulator_congr_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:216](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L216) — **Package a perfect-HVZK proof after simulator normalization in the opposite direction.**

### `perfectHVZK.mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.mono_relation` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:107](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L107) — Perfect HVZK for oracle reductions is antitone in the relation.
- `theorem Reduction.perfectHVZK.mono_relation` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:156](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L156) — **Perfect HVZK is antitone in the relation.** A simulator that matches the honest transcript distrib

### `perfectHVZK.simulator_congr` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.simulator_congr` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:86](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L86) — **OracleReduction perfect HVZK is preserved under an equal simulator distribution.**
- `theorem Reduction.perfectHVZK.simulator_congr` [ArkLib/ToMathlib/ZKTransferBricks.lean:123](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L123) — **Perfect HVZK is preserved under an `evalDist`-equal simulator.** Swapping in a simulator that prod

### `perfectHVZK.simulator_congr_symm` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.simulator_congr_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:108](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L108) — **OracleReduction perfect HVZK simulator congruence with opposite-order equality.**
- `theorem Reduction.perfectHVZK.simulator_congr_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:152](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L152) — **Perfect HVZK simulator congruence with opposite-order equality.**

### `perfectHVZK.statisticalHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.statisticalHVZK` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:96](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L96) — Perfect HVZK for oracle reductions implies statistical HVZK with any error bound.
- `theorem Reduction.perfectHVZK.statisticalHVZK` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:137](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L137) — Perfect HVZK implies statistical HVZK with any error `ε`.

### `perfectHVZK.triangle_honestDist_symm_zero` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.triangle_honestDist_symm_zero` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:283](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L283) — Symmetric-facing zero-error approximate honest-distribution transfer for perfect HVZK at the OracleR
- `theorem Reduction.perfectHVZK.triangle_honestDist_symm_zero` [ArkLib/ToMathlib/ZKTransferBricks.lean:362](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L362) — Symmetric-facing zero-error approximate honest-distribution transfer for perfect HVZK.

### `perfectHVZK.triangle_honestDist_zero` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK.triangle_honestDist_zero` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:269](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L269) — **Zero-error approximate honest-distribution transfer for perfect HVZK at the OracleReduction API bo
- `theorem Reduction.perfectHVZK.triangle_honestDist_zero` [ArkLib/ToMathlib/ZKTransferBricks.lean:342](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L342) — **Zero-error approximate honest-distribution transfer for perfect HVZK.** If the honest-transcript b

### `perfectHVZK_iff_statisticalHVZK_zero` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK_iff_statisticalHVZK_zero` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:85](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L85) — Perfect HVZK for oracle reductions is exactly statistical HVZK with error `0`.
- `theorem Reduction.perfectHVZK_iff_statisticalHVZK_zero` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:109](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L109) — Perfect HVZK is exactly statistical HVZK with error `0`.

### `perfectHVZK_of_const_eq_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK_of_const_eq_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:321](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L321) — **Symmetric-facing OracleReduction constant-simulator criterion for perfect HVZK.**
- `theorem Reduction.perfectHVZK_of_const_eq_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:406](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L406) — **Symmetric-facing constant-simulator criterion for perfect HVZK.**

### `perfectHVZK_of_honestDist_eq_const` (2 declarations, 2 files)

- `theorem OracleReduction.perfectHVZK_of_honestDist_eq_const` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:296](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L296) — **OracleReduction constant-simulator criterion for perfect HVZK.**
- `theorem Reduction.perfectHVZK_of_honestDist_eq_const` [ArkLib/ToMathlib/ZKTransferBricks.lean:380](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L380) — **Constant-simulator criterion for perfect HVZK.** If the honest transcript distribution is `evalDis

### `perfectlyCorrect` (2 declarations, 2 files)

- `theorem ArkLib.Lattices.Ajtai.InnerOuter.perfectlyCorrect` [ArkLib/CommitmentScheme/Ajtai/InnerOuter/Correctness.lean:198](../../../ArkLib/CommitmentScheme/Ajtai/InnerOuter/Correctness.lean#L198) — **Unconditional perfect correctness with the concrete binary decomposition.** Both message and inner
- `theorem ArkLib.Lattices.Ajtai.Simple.perfectlyCorrect` [ArkLib/CommitmentScheme/Ajtai/Simple/Correctness.lean:33](../../../ArkLib/CommitmentScheme/Ajtai/Simple/Correctness.lean#L33) — Simple Ajtai commitments are correct on short messages: an honest commitment to a message accepted b

### `performCheckOriginalEvaluation` (2 declarations, 2 files)

- `def Binius.RingSwitching.performCheckOriginalEvaluation` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:339](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L339) — Step 2 (V): Check 1: s ?= Σ_{v ∈ {0,1}^κ} eqTilde(v, r_{0..κ-1}) ⋅ ŝ_v. Note (soundness fix): the de
- `def RingSwitching.performCheckOriginalEvaluation` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:348](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L348) — Step 2 (V): Check 1: s ?= Σ_{v ∈ {0,1}^κ} eqTilde(v, r_{0..κ-1}) ⋅ ŝ_v. Note (soundness fix): the de

### `performCheckOriginalEvaluation_packMLE_iff` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.performCheckOriginalEvaluation_packMLE_iff` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:805](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L805) — **DP24 ring-switching capstone (decision form).** The verifier's Step-2 check on the prover's honest
- `lemma RingSwitching.performCheckOriginalEvaluation_packMLE_iff` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:982](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L982) — **Generic DP24 ring-switching capstone (decision form)** over an abstract `P`. The verifier's Step-2

### `pow_eq_card_eq_zero_or_gcd` (2 declarations, 2 files)

- `theorem ProximityGap.MultiplicativeRigidity.pow_eq_card_eq_zero_or_gcd` [ArkLib/Data/CodingTheory/ProximityGap/MultiplicativeRigidityFiber.lean:63](../../../ArkLib/Data/CodingTheory/ProximityGap/MultiplicativeRigidityFiber.lean#L63) — **Lemma 1 (monomial agreement / coset rigidity).** In a finite cyclic commutative group `G` of order
- `theorem MultiplicativeRigidity.pow_eq_card_eq_zero_or_gcd` [ArkLib/Data/CodingTheory/ProximityGap/MultiplicativeRigidityZMod.lean:99](../../../ArkLib/Data/CodingTheory/ProximityGap/MultiplicativeRigidityZMod.lean#L99) — **Coset rigidity / monomial agreement (core).** In a finite cyclic group `G` of order `n = Fintype.c

### `probability_bound_badBatchingEventProp` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.BatchingPhase.probability_bound_badBatchingEventProp` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:1052](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L1052) — **Schwartz-Zippel bound for the bad batching event.** When `msg0 = s_bar`, the event never holds (fi
- `lemma RingSwitching.BatchingPhase.probability_bound_badBatchingEventProp` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:663](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L663) — **Schwartz-Zippel bound for the bad batching event.**

### `prod_concat_split` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.prod_concat_split` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:627](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L627) — A product over `Fin (ℓ' + κ₀)` of a function defined by the κ/ℓ'-dichotomy splits as the product of
- `lemma RingSwitching.prod_concat_split` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:721](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L721) — A product over `Fin (ℓ' + κ₀)` of a function defined by the κ/ℓ'-dichotomy splits as the product of

### `prop_4_23_singleRepetition_proximityCheck_bound` (2 declarations, 2 files)

- `theorem Binius.BinaryBasefold.QueryPhase.prop_4_23_singleRepetition_proximityCheck_bound` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:2690](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L2690) — **Single Repetition Proximity Check Bound (Proposition 4.24)** For a single repetition of the proxim
- `theorem Binius.BinaryBasefold.prop_4_23_singleRepetition_proximityCheck_bound` [ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/QueryPhaseSoundness.lean:1267](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/QueryPhaseSoundness.lean#L1267) — **Proposition 4.24** (Query-phase soundness, assuming no bad events). If any oracle is non-compliant

### `proximityCondition` (2 declarations, 2 files)

- `def MutualCorrAgreement.proximityCondition` [ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean:56](../../../ArkLib/ProofSystem/Whir/MutualCorrAgreement.lean#L56) — For `parℓ` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → parℓ → 𝔽` and linea
- `def Generator.proximityCondition` [ArkLib/ProofSystem/Whir/ProximityGen.lean:38](../../../ArkLib/ProofSystem/Whir/ProximityGen.lean#L38) — For `l` functions `fᵢ : ι → 𝔽`, distance `δ`, generator function `GenFun: 𝔽 → parℓ → 𝔽ˡ` and linear

### `queryCodeword` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.QueryPhase.queryCodeword` [ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/QueryPhasePrelims.lean:178](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/QueryPhasePrelims.lean#L178) — Oracle query helper: query a committed codeword at a given domain point. Restricted to codeword indi
- `def Fri.Spec.QueryRound.queryCodeword` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:1019](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L1019) — (no docstring)

### `queryOracleReduction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.QueryPhase.queryOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean:174](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase.lean#L174) — The oracle reduction for the final query phase.
- `def Fri.Spec.QueryRound.queryOracleReduction` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:1137](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L1137) — (no docstring)

### `reduction_verifier_eq_verifier` (2 declarations, 2 files)

- `lemma Sumcheck.Spec.reduction_verifier_eq_verifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:193](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L193) — (no docstring)
- `lemma Sumcheck.Spec.SingleRound.reduction_verifier_eq_verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1396](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1396) — (no docstring)

### `relIn` (2 declarations, 2 files)

- `def CheckClaim.relIn` [ArkLib/ProofSystem/Component/CheckClaim.lean:61](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L61) — (no docstring)
- `def RandomQuery.relIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:43](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L43) — The input relation is that the two oracles are equal.

### `rewindingKnowledgeSoundness` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.rewindingKnowledgeSoundness` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:159](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L159) — Paper-facing alias for CO25 Definition 3.8 rewinding knowledge soundness.
- `def Verifier.rewindingKnowledgeSoundness` [ArkLib/OracleReduction/Security/Rewinding.lean:211](../../../ArkLib/OracleReduction/Security/Rewinding.lean#L211) — CO25 Definition 3.8, adapted to ArkLib's non-interactive argument interface. ArkLib's `Prover.NARG`

### `rewindingKnowledgeSoundnessFamily` (2 declarations, 2 files)

- `abbrev DuplexSpongeFS.NARG.rewindingKnowledgeSoundnessFamily` [ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean:176](../../../ArkLib/OracleReduction/FiatShamir/DuplexSponge/Basic.lean#L176) — Paper-facing alias for CO25 Definition 3.8 with explicit security parameter `λ`.
- `def Verifier.rewindingKnowledgeSoundnessFamily` [ArkLib/OracleReduction/Security/Rewinding.lean:264](../../../ArkLib/OracleReduction/Security/Rewinding.lean#L264) — CO25 Definition 3.8 with the security parameter `λ` made explicit as an external index. This is a wr

### `rightpad` (2 declarations, 2 files)

- `def Fin.rightpad` [ArkLib/Data/Fin/Tuple/Defs.lean:90](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L90) — Pad a `Fin`-indexed vector on the right with an element `a`. This becomes truncation if `n < m`.
- `def Matrix.rightpad` [ArkLib/Data/Matrix/Basic.lean:21](../../../ArkLib/Data/Matrix/Basic.lean#L21) — (no docstring)

### `roundKnowledgeError` (2 declarations, 2 files)

- `abbrev RingSwitching.SumcheckPhase.roundKnowledgeError` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:229](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L229) — Repaired local bound for the current round-by-round proof. The sharp `2 / \|L\|` statement needs the u
- `def Sumcheck.Structured.roundKnowledgeError` [ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean:473](../../../ArkLib/ProofSystem/Sumcheck/Structured/SingleRound.lean#L473) — Round-by-round knowledge error for a single round of the structured sumcheck: the Schwartz–Zippel bo

### `rs_lambda_high_rate_jh01` (2 declarations, 2 files)

- `theorem CodingTheory.rs_lambda_high_rate_jh01` [ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean:2083](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean#L2083) — **ABF26 Theorem 3.14 [JH01 Thm 2], repaired list-size form.** Large-rate Reed-Solomon lower bound. F
- `theorem CodingTheory.ReedSolomon.rs_lambda_high_rate_jh01` [ArkLib/Data/CodingTheory/ListDecoding/JH01.lean:214](../../../ArkLib/Data/CodingTheory/ListDecoding/JH01.lean#L214) — ABF26 Theorem 3.14 / JH01 Theorem 2, in a repaired list-size form.  For every `j ≥ 2`, infinitely ma

### `run` (2 declarations, 2 files)

- `def AGM.Adversary.run` [ArkLib/AGM/Basic.lean:484](../../../ArkLib/AGM/Basic.lean#L484) — Running the adversary on a given table, returning the list of group elements it is supposed to outpu
- `def Prover.run` [ArkLib/OracleReduction/Execution.lean:97](../../../ArkLib/OracleReduction/Execution.lean#L97) — Run the prover in an interactive reduction. Returns the output statement and witness, and the transc

### `shiftSeries` (2 declarations, 2 files)

- `def ArkLib.Claim59Conditional.shiftSeries` [ArkLib/ToMathlib/Claim59Conditional.lean:53](../../../ArkLib/ToMathlib/Claim59Conditional.lean#L53) — The BCIKS shift series corresponding to the substitution $X \mapsto X - x_0$.
- `def ArkLib.SubstFieldCaveat.shiftSeries` [ArkLib/ToMathlib/SubstFieldCaveat.lean:75](../../../ArkLib/ToMathlib/SubstFieldCaveat.lean#L75) — The shift series corresponding to the substitution $X \mapsto X - x_0$.

### `simulateQ_optionT_failure'` (2 declarations, 2 files)

- `theorem Logup.simulateQ_optionT_failure'` [ArkLib/ProofSystem/Logup/Security/OuterRun.lean:52](../../../ArkLib/ProofSystem/Logup/Security/OuterRun.lean#L52) — `simulateQ` commutes with `OptionT` `failure`.
- `theorem RingSwitching.SumcheckPhase.simulateQ_optionT_failure'` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:83](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L83) — `simulateQ` commutes with `OptionT` `failure`, for an arbitrary lawful target monad `m` (so it appli

### `simulateQ_optionT_pure'` (2 declarations, 2 files)

- `theorem Logup.simulateQ_optionT_pure'` [ArkLib/ProofSystem/Logup/Security/OuterRun.lean:44](../../../ArkLib/ProofSystem/Logup/Security/OuterRun.lean#L44) — `simulateQ` commutes with `OptionT.pure`.
- `theorem RingSwitching.SumcheckPhase.simulateQ_optionT_pure'` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:72](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L72) — `simulateQ` commutes with `OptionT.pure` (no explicit empty-spec universes).

### `simulateQ_oracleVerify_eq` (2 declarations, 2 files)

- `lemma Sumcheck.Spec.SingleRound.Simple.simulateQ_oracleVerify_eq` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:965](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L965) — Closed form of the simulated oracle-verifier `verify`: the inner `simOracle2` simulation collapses t
- `theorem ToyProblem.Spec.simulateQ_oracleVerify_eq` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:788](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L788) — **Closed form of the compiled toy-problem oracle verifier.** Simulating `oracleVerifier.verify` agai

### `singleEq_collapse` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.singleEq_collapse` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:491](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L491) — A single `eqPolynomial` factor, evaluated through the mixed embedding `eval₂ φ₁ (φ₀ ∘ g)` at a Boole
- `lemma RingSwitching.singleEq_collapse` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:640](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L640) — A single `eqPolynomial` factor, evaluated through the mixed embedding `eval₂ φ₁ (φ₀ ∘ g)` at a Boole

### `size_of_smooth_coset_domain_eq_pow_of_2` (2 declarations, 2 files)

- `lemma ReedSolomon.CosetFftDomain.size_of_smooth_coset_domain_eq_pow_of_2` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1317](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1317) — (no docstring)
- `lemma Domain.size_of_smooth_coset_domain_eq_pow_of_2` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:515](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L515) — Compatibility form of the smooth-coset domain size: the `toFinset` of a `SmoothCosetFftDomain n F` h

### `soundness.mono_error` (2 declarations, 2 files)

- `theorem Verifier.soundness.mono_error` [ArkLib/OracleReduction/Security/Basic.lean:373](../../../ArkLib/OracleReduction/Security/Basic.lean#L373) — Verifier soundness is monotone in the allowed soundness error.
- `theorem Verifier.StateRestoration.soundness.mono_error` [ArkLib/OracleReduction/Security/StateRestoration.lean:143](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L143) — State-restoration soundness is monotone in the allowed soundness error.

### `soundness.mono_languages` (2 declarations, 2 files)

- `theorem Verifier.soundness.mono_languages` [ArkLib/OracleReduction/Security/Basic.lean:389](../../../ArkLib/OracleReduction/Security/Basic.lean#L389) — Verifier soundness is monotone in the input and output languages. If soundness holds for a smaller h
- `theorem Verifier.StateRestoration.soundness.mono_languages` [ArkLib/OracleReduction/Security/StateRestoration.lean:157](../../../ArkLib/OracleReduction/Security/StateRestoration.lean#L157) — State-restoration soundness is monotone under enlarging the honest input language and shrinking the

### `sq_root_mem_subdomain` (2 declarations, 2 files)

- `lemma ReedSolomon.CosetFftDomain.sq_root_mem_subdomain` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1586](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1586) — (no docstring)
- `lemma Domain.CosetFftDomainClass.sq_root_mem_subdomain` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:416](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L416) — (no docstring)

### `sq_sum_le_card_support_mul_sum_sq` (2 declarations, 2 files)

- `theorem Finset.sq_sum_le_card_support_mul_sum_sq` [ArkLib/ToMathlib/SqSumCardSupport.lean:20](../../../ArkLib/ToMathlib/SqSumCardSupport.lean#L20) — (no docstring)
- `theorem ArkLib.sq_sum_le_card_support_mul_sum_sq` [ArkLib/ToMathlib/SupportSqBound.lean:25](../../../ArkLib/ToMathlib/SupportSqBound.lean#L25) — **Cauchy-Schwarz support bound.** Over a finite type, `(∑ f)² ≤ \|support f\| · (∑ f²)`.

### `statisticalHVZK.congr_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.congr_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:46](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L46) — **OracleReduction statistical HVZK transfers along an equal honest distribution.**
- `theorem Reduction.statisticalHVZK.congr_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:80](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L80) — **Statistical HVZK transfers along an `evalDist`-equal honest distribution.** The same simulator and

### `statisticalHVZK.congr_honestDist_symm` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.congr_honestDist_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:73](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L73) — **OracleReduction statistical HVZK honest-distribution congruence with opposite-order equality.**
- `theorem Reduction.statisticalHVZK.congr_honestDist_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:109](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L109) — **Statistical HVZK honest-distribution congruence with opposite-order equality.**

### `statisticalHVZK.isStatHVZK` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.isStatHVZK` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:141](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L141) — **A concrete OracleReduction statistical-HVZK simulator witnesses existential statistical HVZK.**
- `theorem Reduction.statisticalHVZK.isStatHVZK` [ArkLib/ToMathlib/ZKTransferBricks.lean:184](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L184) — **A concrete statistical-HVZK simulator witnesses existential statistical HVZK.**

### `statisticalHVZK.isStatHVZK_of_simulator_congr` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.isStatHVZK_of_simulator_congr` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:164](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L164) — **Package an OracleReduction statistical-HVZK proof after normalizing the simulator distribution.**
- `theorem Reduction.statisticalHVZK.isStatHVZK_of_simulator_congr` [ArkLib/ToMathlib/ZKTransferBricks.lean:205](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L205) — **Package a statistical-HVZK proof after normalizing the simulator distribution.**

### `statisticalHVZK.isStatHVZK_of_simulator_congr_symm` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.isStatHVZK_of_simulator_congr_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:188](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L188) — **Package an OracleReduction statistical-HVZK proof after simulator normalization in the opposite di
- `theorem Reduction.statisticalHVZK.isStatHVZK_of_simulator_congr_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:227](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L227) — **Package a statistical-HVZK proof after simulator normalization in the opposite direction.**

### `statisticalHVZK.mono_error` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.mono_error` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:140](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L140) — Statistical HVZK for oracle reductions is monotone in the error bound.
- `theorem Reduction.statisticalHVZK.mono_error` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:188](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L188) — **Statistical HVZK is monotone in the error.** A simulator within total-variation distance `ε₁` is a

### `statisticalHVZK.mono_relation` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.mono_relation` [ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean:129](../../../ArkLib/OracleReduction/Security/OracleZeroKnowledge.lean#L129) — Statistical HVZK for oracle reductions is antitone in the relation.
- `theorem Reduction.statisticalHVZK.mono_relation` [ArkLib/OracleReduction/Security/ZeroKnowledge.lean:177](../../../ArkLib/OracleReduction/Security/ZeroKnowledge.lean#L177) — **Statistical HVZK is antitone in the relation.**

### `statisticalHVZK.simulator_congr` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.simulator_congr` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:97](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L97) — **OracleReduction statistical HVZK is preserved under an equal simulator distribution.**
- `theorem Reduction.statisticalHVZK.simulator_congr` [ArkLib/ToMathlib/ZKTransferBricks.lean:138](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L138) — **Statistical HVZK is preserved under an `evalDist`-equal simulator.** Swapping in a simulator that

### `statisticalHVZK.simulator_congr_symm` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.simulator_congr_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:119](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L119) — **OracleReduction statistical HVZK simulator congruence with opposite-order equality.**
- `theorem Reduction.statisticalHVZK.simulator_congr_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:163](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L163) — **Statistical HVZK simulator congruence with opposite-order equality.**

### `statisticalHVZK.simulator_triangle` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.simulator_triangle` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:199](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L199) — **Triangle composition of statistical HVZK at the OracleReduction API boundary.**
- `theorem Reduction.statisticalHVZK.simulator_triangle` [ArkLib/ToMathlib/ZKTransferBricks.lean:240](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L240) — **Triangle composition of statistical HVZK.** If `sim₁` is within `ε₁` of the honest distribution an

### `statisticalHVZK.triangle_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.triangle_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:213](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L213) — **Approximate honest-distribution transfer at the OracleReduction API boundary.**
- `theorem Reduction.statisticalHVZK.triangle_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:265](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L265) — **Approximate honest-distribution transfer for statistical HVZK.** If a simulator is statistical-HVZ

### `statisticalHVZK.triangle_honestDist_symm` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.triangle_honestDist_symm` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:227](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L227) — **Symmetric-facing approximate honest-distribution transfer at the OracleReduction API boundary.**
- `theorem Reduction.statisticalHVZK.triangle_honestDist_symm` [ArkLib/ToMathlib/ZKTransferBricks.lean:291](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L291) — **Symmetric-facing approximate honest-distribution transfer.** This is the same result as `statistic

### `statisticalHVZK.triangle_honestDist_symm_zero` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.triangle_honestDist_symm_zero` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:255](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L255) — Symmetric-facing zero-error approximate honest-distribution transfer for statistical HVZK at the Ora
- `theorem Reduction.statisticalHVZK.triangle_honestDist_symm_zero` [ArkLib/ToMathlib/ZKTransferBricks.lean:324](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L324) — Symmetric-facing zero-error approximate honest-distribution transfer for statistical HVZK.

### `statisticalHVZK.triangle_honestDist_zero` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK.triangle_honestDist_zero` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:241](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L241) — **Zero-error approximate honest-distribution transfer for statistical HVZK at the OracleReduction AP
- `theorem Reduction.statisticalHVZK.triangle_honestDist_zero` [ArkLib/ToMathlib/ZKTransferBricks.lean:308](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L308) — **Zero-error approximate honest-distribution transfer for statistical HVZK.** If the honest transcri

### `statisticalHVZK_of_const_eq_honestDist` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK_of_const_eq_honestDist` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:334](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L334) — **Symmetric-facing OracleReduction constant-simulator criterion for statistical HVZK.**
- `theorem Reduction.statisticalHVZK_of_const_eq_honestDist` [ArkLib/ToMathlib/ZKTransferBricks.lean:419](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L419) — **Symmetric-facing constant-simulator criterion for statistical HVZK.**

### `statisticalHVZK_of_honestDist_eq_const` (2 declarations, 2 files)

- `theorem OracleReduction.statisticalHVZK_of_honestDist_eq_const` [ArkLib/ToMathlib/OracleZKTransferBricks.lean:308](../../../ArkLib/ToMathlib/OracleZKTransferBricks.lean#L308) — **OracleReduction constant-simulator criterion for statistical HVZK.**
- `theorem Reduction.statisticalHVZK_of_honestDist_eq_const` [ArkLib/ToMathlib/ZKTransferBricks.lean:394](../../../ArkLib/ToMathlib/ZKTransferBricks.lean#L394) — **Statistical constant-simulator criterion.** If the honest transcript distribution is `evalDist`-eq

### `subdomainZeroEquiv` (2 declarations, 2 files)

- `def Domain.CosetFftDomainClass.subdomainZeroEquiv` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:133](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L133) — The zeroth subdomain has the same finite set of field points as the ambient domain.
- `def Fri.subdomainZeroEquiv` [ArkLib/ProofSystem/BatchedFri/Security.lean:1333](../../../ArkLib/ProofSystem/BatchedFri/Security.lean#L1333) — The round-zero Batched FRI subdomain is equivalent to the original evaluation domain.

### `subdomain_embed` (2 declarations, 2 files)

- `def ReedSolomon.FftDomain.subdomain_embed` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:774](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L774) — (no docstring)
- `def Domain.CosetFftDomainClass.subdomain_embed` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:44](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L44) — (no docstring)

### `subdomain_embed_add` (2 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.subdomain_embed_add` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:784](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L784) — (no docstring)
- `lemma Domain.CosetFftDomainClass.subdomain_embed_add` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:56](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L56) — (no docstring)

### `subdomain_embed_injective` (2 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.subdomain_embed_injective` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:798](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L798) — (no docstring)
- `lemma Domain.CosetFftDomainClass.subdomain_embed_injective` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:74](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L74) — (no docstring)

### `subdomain_embed_of_le` (2 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.subdomain_embed_of_le` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:873](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L873) — (no docstring)
- `lemma Domain.CosetFftDomainClass.subdomain_embed_of_le` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:276](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L276) — (no docstring)

### `subdomain_embed_zero` (2 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.subdomain_embed_zero` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:793](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L793) — (no docstring)
- `lemma Domain.CosetFftDomainClass.subdomain_embed_zero` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:69](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L69) — (no docstring)

### `sum_div_mul_prod_eq_sum_mul_prod_erase` (2 declarations, 2 files)

- `theorem Logup.sum_div_mul_prod_eq_sum_mul_prod_erase` [ArkLib/ProofSystem/Logup/Common.lean:755](../../../ArkLib/ProofSystem/Logup/Common.lean#L755) — (no docstring)
- `theorem Finset.sum_div_mul_prod_eq_sum_mul_prod_erase` [ArkLib/ToMathlib/ProtocolCountingBricks.lean:30](../../../ArkLib/ToMathlib/ProtocolCountingBricks.lean#L30) — **LogUp clear-denominators core.** `(∑ num/den)·(∏ den) = ∑ num·∏_{erase} den`.

### `sumcheckConsistencyProp` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.sumcheckConsistencyProp` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:1162](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L1162) — Sumcheck consistency: the claimed sumcheck target equals the sum of `H` over the boolean hypercube o
- `def Sumcheck.Structured.sumcheckConsistencyProp` [ArkLib/ProofSystem/Sumcheck/Structured.lean:212](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L212) — Sumcheck consistency: the claimed sum equals the actual polynomial evaluation sum over the evaluatio

### `sumcheckConsistency_at_last_simplifies` (2 declarations, 2 files)

- `lemma Binius.FRIBinius.CoreInteractionPhase.sumcheckConsistency_at_last_simplifies` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:682](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L682) — At `Fin.last ℓ'`, sumcheck consistency simplifies to a single evaluation.
- `lemma Binius.RingSwitching.SumcheckPhase.sumcheckConsistency_at_last_simplifies` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1042](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1042) — At `Fin.last ℓ'`, the sumcheck consistency sum is over 0 variables, simplifying to a single evaluati

### `sumcheckFoldOracleReduction` (2 declarations, 2 files)

- `def sumcheckFoldOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:815](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L815) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:154](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L154) — (no docstring)

### `sumcheckFoldOracleReduction_perfectCompleteness` (2 declarations, 2 files)

- `theorem sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:922](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L922) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:252](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L252) — (no docstring)

### `sumcheckFoldOracleVerifier` (2 declarations, 2 files)

- `def sumcheckFoldOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:531](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L531) — (no docstring)
- `def Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:147](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L147) — (no docstring)

### `sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean:1077](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/CoreInteractionPhase.lean#L1077) — (no docstring)
- `theorem Binius.FRIBinius.CoreInteractionPhase.sumcheckFoldOracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:440](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L440) — (no docstring)

### `sumcheckLoopOracleReduction` (2 declarations, 2 files)

- `def Binius.RingSwitching.SumcheckPhase.sumcheckLoopOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1691](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1691) — Composed oracle reduction for the SumcheckStep (seqCompose over ℓ')
- `def RingSwitching.SumcheckPhase.sumcheckLoopOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1516](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1516) — Composed oracle reduction for the SumcheckStep (seqCompose over ℓ')

### `sumcheckLoopOracleVerifier` (2 declarations, 2 files)

- `def Binius.RingSwitching.SumcheckPhase.sumcheckLoopOracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1682](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1682) — Composed oracle verifier for the SumcheckStep (seqCompose over ℓ')
- `def RingSwitching.SumcheckPhase.sumcheckLoopOracleVerifier` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1497](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1497) — Composed oracle verifier for the SumcheckStep (seqCompose over ℓ')

### `sumcheckRoundRelation` (2 declarations, 2 files)

- `def Binius.RingSwitching.sumcheckRoundRelation` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:447](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L447) — Input relation for single round: proper sumcheck statement
- `def RingSwitching.sumcheckRoundRelation` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:463](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L463) — Input relation for single round: proper sumcheck statement

### `sumcheckRoundRelationProp` (2 declarations, 2 files)

- `def Binius.RingSwitching.sumcheckRoundRelationProp` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:440](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L440) — (no docstring)
- `def RingSwitching.sumcheckRoundRelationProp` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:456](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L456) — (no docstring)

### `sumcheckSum_X0_eq` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.sumcheckSum_X0_eq` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:849](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L849) — **Sumcheck hypercube sum depends on the evaluation domain `𝓑`.** The single-variable sumcheck consis
- `lemma RingSwitching.sumcheckSum_X0_eq` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1311](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1311) — **Sumcheck hypercube sum depends on the evaluation domain `𝓑`.** The single-variable sumcheck consis

### `sumcheckTarget_domain_indep` (2 declarations, 2 files)

- `lemma Binius.RingSwitching.sumcheckTarget_domain_indep` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:868](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L868) — **No `𝓑`-free target satisfies sumcheck consistency for all domains `𝓑`.** If a single value `c` (in
- `lemma RingSwitching.sumcheckTarget_domain_indep` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1330](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1330) — **No `𝓑`-free target satisfies sumcheck consistency for all domains `𝓑`.** If a single value `c` (in

### `support_mk` (2 declarations, 2 files)

- `lemma ReduceClaim.support_mk` [ArkLib/ProofSystem/Component/ReduceClaim.lean:181](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L181) — (no docstring)
- `lemma OptionT.support_mk` [ArkLib/ToVCVio/Lemmas.lean:106](../../../ArkLib/ToVCVio/Lemmas.lean#L106) — (no docstring)

### `toListWithProof.` (2 declarations, 2 files)

- `def ReedSolomon.Finset.toListWithProof.` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:238](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L238) — A helper to convert a finset into a list whose elements are the members of the finset, i.e. come wit
- `def Finset.toListWithProof.` [ArkLib/ToMathlib/Finset/ToListWithProof.lean:25](../../../ArkLib/ToMathlib/Finset/ToListWithProof.lean#L25) — A helper to convert a finset into a list whose elements are the members of the finset, i.e. come wit

### `toListWithProof_empty.` (2 declarations, 2 files)

- `lemma ReedSolomon.Finset.toListWithProof_empty.` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:245](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L245) — (no docstring)
- `lemma Finset.toListWithProof_empty.` [ArkLib/ToMathlib/Finset/ToListWithProof.lean:32](../../../ArkLib/ToMathlib/Finset/ToListWithProof.lean#L32) — (no docstring)

### `toListWithProof_eq_toList.` (2 declarations, 2 files)

- `lemma ReedSolomon.Finset.toListWithProof_eq_toList.` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:272](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L272) — (no docstring)
- `lemma Finset.toListWithProof_eq_toList.` [ArkLib/ToMathlib/Finset/ToListWithProof.lean:59](../../../ArkLib/ToMathlib/Finset/ToListWithProof.lean#L59) — (no docstring)

### `toListWithProof_mem.` (2 declarations, 2 files)

- `lemma ReedSolomon.Finset.toListWithProof_mem.` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:249](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L249) — (no docstring)
- `lemma Finset.toListWithProof_mem.` [ArkLib/ToMathlib/Finset/ToListWithProof.lean:36](../../../ArkLib/ToMathlib/Finset/ToListWithProof.lean#L36) — (no docstring)

### `toMonadDecoration` (2 declarations, 2 files)

- `def Interaction.OracleDecoration.toMonadDecoration` [ArkLib/Interaction/Oracle/Core.lean:802](../../../ArkLib/Interaction/Oracle/Core.lean#L802) — (no docstring)
- `def Interaction.Oracle.Spec.toMonadDecoration` [ArkLib/Interaction/Oracle/Spec.lean:193](../../../ArkLib/Interaction/Oracle/Spec.lean#L193) — (no docstring)

### `toOracleSpec` (2 declarations, 2 files)

- `def Interaction.Oracle.Spec.toOracleSpec` [ArkLib/Interaction/Oracle/Spec.lean:158](../../../ArkLib/Interaction/Oracle/Spec.lean#L158) — (no docstring)
- `def OracleInterface.toOracleSpec` [ArkLib/OracleReduction/OracleInterface.lean:92](../../../ArkLib/OracleReduction/OracleInterface.lean#L92) — Converts an indexed type family of oracle interfaces into an oracle specification. Notation: `[v]ₒ`

### `twoNthRoot_correct_one` (2 declarations, 2 files)

- `lemma ReedSolomon.CosetFftDomain.twoNthRoot_correct_one` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:1940](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L1940) — (no docstring)
- `lemma Domain.CosetFftDomain.twoNthRoot_correct_one` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:497](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L497) — (no docstring)

### `umCode` (2 declarations, 2 files)

- `def ReedSolomon.Multiplicity.umCode` [ArkLib/Data/CodingTheory/ReedSolomon/Multiplicity.lean:97](../../../ArkLib/Data/CodingTheory/ReedSolomon/Multiplicity.lean#L97) — **ABF26 Definition A.7 [GW13, KSY14]** — the univariate multiplicity code `UM[F, L, k, s]`. Defined
- `def CodingTheory.umCode` [ArkLib/Data/CodingTheory/SubspaceDesign.lean:1105](../../../ArkLib/Data/CodingTheory/SubspaceDesign.lean#L1105) — **ABF26 DA.7 (Univariate Multiplicity codes)**. The UM code `UM[F, L, k, s]`: `UM[F, L, k, s] := { f

### `uniform` (2 declarations, 2 files)

- `def OracleReduction.OracleDistribution.uniform` [ArkLib/OracleReduction/Security/OracleDistribution.lean:119](../../../ArkLib/OracleReduction/Security/OracleDistribution.lean#L119) — Uniform full-table sampling. Requires `SampleableType` over the dependent product `OracleFamily spec
- `def SumcheckDomain.uniform` [ArkLib/ProofSystem/Sumcheck/Domain.lean:74](../../../ArkLib/ProofSystem/Sumcheck/Domain.lean#L74) — The *uniform* domain: the same `m`-point embedding `D₀` in every one of the `k` coordinates. Its `cu

### `unpackMLE` (2 declarations, 2 files)

- `def Binius.RingSwitching.unpackMLE` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:144](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L144) — **Unpacking a Packed Multilinear Polynomial**. Reverses the packing defined in `packMLE`. It reconst
- `def RingSwitching.unpackMLE` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:144](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L144) — **Unpacking a Packed Multilinear Polynomial**. Reverses the packing defined in `packMLE`. It reconst

### `val_eq_nsmul_one` (2 declarations, 2 files)

- `lemma ReedSolomon.FftDomain.val_eq_nsmul_one` [ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean:481](../../../ArkLib/Data/CodingTheory/ReedSolomon/FftDomain.lean#L481) — (no docstring)
- `lemma Domain.FftDomainClass.val_eq_nsmul_one` [ArkLib/Data/Domain/FftDomain/Ops.lean:113](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L113) — (no docstring)

### `vanishesToOrder` (2 declarations, 2 files)

- `def GSMultInterp.vanishesToOrder` [ArkLib/Data/CodingTheory/GuruswamiSudan/MultiplicityInterpolation.lean:153](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/MultiplicityInterpolation.lean#L153) — `Q` (given by coefficient vector `c`) **vanishes to order `m`** at `(x₀, y₀)`: every Hasse coefficie
- `def ArkLib.GS.vanishesToOrder` [ArkLib/Data/CodingTheory/ProximityGap/BivariateVanishing.lean:60](../../../ArkLib/Data/CodingTheory/ProximityGap/BivariateVanishing.lean#L60) — `Q : F[X][Y]` **vanishes to order `m` at `(a, b)`** when, for every `Y`-index `j`, the inner Taylor

### `vecL2NormSq` (2 declarations, 2 files)

- `def ArkLib.Lattices.CyclotomicModulus.vecL2NormSq` [ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean:91](../../../ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean#L91) — Centered squared-`ℓ₂` norm of a vector: the sum of entrywise norms.
- `def ArkLib.Lattices.CenteredCoeffView.vecL2NormSq` [ArkLib/Data/Lattices/CyclotomicRing/Norms.lean:80](../../../ArkLib/Data/Lattices/CyclotomicRing/Norms.lean#L80) — Vector squared `ℓ₂` norm: the sum of entrywise squared `ℓ₂` norms.

### `verifier_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem DoNothing.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/DoNothing.lean:58](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L58) — The `DoNothing` verifier is perfectly round-by-round knowledge sound.
- `theorem ReduceClaim.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:225](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L225) — The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness. Note that s

### `verifyOpening` (2 declarations, 2 files)

- `def KZG.verifyOpening` [ArkLib/CommitmentScheme/KZG/Basic.lean:69](../../../ArkLib/CommitmentScheme/KZG/Basic.lean#L69) — To verify a KZG opening `opening` for a commitment `commitment` at point `z` with claimed evaluation
- `def InductiveMerkleTree.verifyOpening` [ArkLib/CommitmentScheme/MerkleTree/Batch.lean:101](../../../ArkLib/CommitmentScheme/MerkleTree/Batch.lean#L101) — Verify one packaged opening against a claimed root, in `OracleComp (spec α)`.

### `weight_Λ_over_𝒪_add_le` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_add_le` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean:640](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean#L640) — `Λ_𝒪(a + b) ≤ max(Λ_𝒪 a, Λ_𝒪 b)`: sub-additivity over `𝒪 H`.
- `lemma ArkLib.weight_Λ_over_𝒪_add_le` [ArkLib/ToMathlib/WeightLambdaCalculus.lean:82](../../../ArkLib/ToMathlib/WeightLambdaCalculus.lean#L82) — Sub-additivity of the `𝒪`-weight under addition: `Λ(a + b) ≤ max (Λ a) (Λ b)`.

### `weight_Λ_over_𝒪_mul_le` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_mul_le` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean:625](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean#L625) — `Λ_𝒪(a · b) ≤ Λ_𝒪(a) + Λ_𝒪(b)`: sub-multiplicativity over `𝒪 H`.  Take the canonical representatives
- `lemma ArkLib.weight_Λ_over_𝒪_mul_le` [ArkLib/ToMathlib/WeightLambdaCalculus.lean:143](../../../ArkLib/ToMathlib/WeightLambdaCalculus.lean#L143) — Sub-multiplicativity of the `𝒪`-weight: `Λ(a · b) ≤ Λ a + Λ b`. This is the central inequality the A

### `weight_Λ_over_𝒪_neg` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_neg` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean:655](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean#L655) — `Λ_𝒪(-a) = Λ_𝒪(a)`: the `𝒪`-weight is negation-invariant (`mk (-ra) = -a`, `weight_Λ_neg`).
- `lemma ArkLib.weight_Λ_over_𝒪_neg` [ArkLib/ToMathlib/WeightLambdaCalculus.lean:99](../../../ArkLib/ToMathlib/WeightLambdaCalculus.lean#L99) — Sub-additivity of the `𝒪`-weight under negation: it is invariant.

### `weight_Λ_over_𝒪_pow_le` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_pow_le` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean:681](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean#L681) — `Λ_𝒪(a ^ k) ≤ k • Λ_𝒪(a)` (i.e. `≤ k · Λ_𝒪(a)` in `WithBot ℕ`): the power bound over `𝒪 H`, by induc
- `lemma ArkLib.weight_Λ_over_𝒪_pow_le` [ArkLib/ToMathlib/WeightLambdaCalculus.lean:158](../../../ArkLib/ToMathlib/WeightLambdaCalculus.lean#L158) — Sub-multiplicativity for powers: `Λ(a ^ n) ≤ n • Λ a` (with `0 • Λ a = 0`, matching `weight_Λ_over_𝒪

### `weight_Λ_over_𝒪_sum_le` (2 declarations, 2 files)

- `lemma BCIKS20.HenselNumerator.weight_Λ_over_𝒪_sum_le` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean:667](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/HenselNumerator.lean#L667) — `Λ_𝒪(∑ᵢ f i) ≤ sup of Λ_𝒪(f i)`: the `𝒪`-weight of a finite sum is bounded by the sup of the summand
- `lemma ArkLib.weight_Λ_over_𝒪_sum_le` [ArkLib/ToMathlib/WeightLambdaCalculus.lean:124](../../../ArkLib/ToMathlib/WeightLambdaCalculus.lean#L124) — The `𝒪`-weight of a finite sum is bounded by the `sup` of the summands' weights.

### `OracleInterface` (3 declarations, 2 files)

- `structure OracleInterface` [ArkLib/OracleReduction/Basic.lean:88](../../../ArkLib/OracleReduction/Basic.lean#L88) — (no docstring)
- `structure OracleInterface` [ArkLib/OracleReduction/Basic.lean:162](../../../ArkLib/OracleReduction/Basic.lean#L162) — (no docstring)
- `class OracleInterface` [ArkLib/OracleReduction/OracleInterface.lean:52](../../../ArkLib/OracleReduction/OracleInterface.lean#L52) — `OracleInterface` is a type class that provides an oracle interface for a type `Message`. It consist

### `choose_pow_le_qEntropy` (2 declarations, 2 files)

- `theorem CodingTheory.choose_pow_le_qEntropy` [ArkLib/Data/CodingTheory/EntropyVolumeUpper.lean:55](../../../ArkLib/Data/CodingTheory/EntropyVolumeUpper.lean#L55) — **Single-term q-ary entropy UPPER bound.**  For `2 ≤ q`, `0 < k`, `k < n`: `C(n,k) · (q-1)^k ≤ q^{n·
- `theorem CodingTheory.choose_pow_le_qEntropy` [ArkLib/Data/CodingTheory/EntropyVolumeUpperBound.lean:53](../../../ArkLib/Data/CodingTheory/EntropyVolumeUpperBound.lean#L53) — **Per-term `q`-ary entropy upper bound.** For `2 ≤ q`, `0 < k`, `k < n`, `C(n,k) · (q-1)^k ≤ q^{n ·

### `coeff_ehQ_eq_leading` (2 declarations, 2 files)

- `lemma MvPolynomial.coeff_ehQ_eq_leading` [ArkLib/ToMathlib/RestrictedSumset.lean:223](../../../ArkLib/ToMathlib/RestrictedSumset.lean#L223) — The coefficient of the top monomial `X₀^{n-1} X₁^{n-2}` in `ehQ C'` (with `\|C'\| = 2(n-2)`) equals it
- `lemma MvPolynomial.coeff_ehQ_eq_leading` [ArkLib/ToMathlib/RestrictedSumsetGeneral.lean:278](../../../ArkLib/ToMathlib/RestrictedSumsetGeneral.lean#L278) — `ehQ h Cset` differs from the leading part `vdmX h · y^{\|Cset\|}` by a polynomial of strictly smaller

### `coeff_zero_of_natDegree_lt` (2 declarations, 2 files)

- `lemma ProximityGap.coeff_zero_of_natDegree_lt` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean:694](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean#L694) — (no docstring)
- `lemma ProximityGap.coeff_zero_of_natDegree_lt` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean:31](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean#L31) — (no docstring)

### `decodeLT_ne_of_val_ne` (2 declarations, 2 files)

- `lemma OutOfDomSmpl.decodeLT_ne_of_val_ne` [ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean:87](../../../ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean#L87) — Distinct codewords decode to distinct polynomials: the decoded polynomial interpolates the codeword
- `lemma OutOfDomSmpl.decodeLT_ne_of_val_ne` [ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean:181](../../../ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean#L181) — Distinct smooth codewords decode to distinct univariate polynomials (the decoded polynomial interpol

### `ehQ` (2 declarations, 2 files)

- `def MvPolynomial.ehQ` [ArkLib/ToMathlib/RestrictedSumset.lean:218](../../../ArkLib/ToMathlib/RestrictedSumset.lean#L218) — **The Erdős–Heilbronn polynomial** for a padded sumset `C'`.
- `def MvPolynomial.ehQ` [ArkLib/ToMathlib/RestrictedSumsetGeneral.lean:273](../../../ArkLib/ToMathlib/RestrictedSumsetGeneral.lean#L273) — **The general Erdős–Heilbronn polynomial** for a padded sumset `C'`.

### `ehY` (2 declarations, 2 files)

- `def MvPolynomial.ehY` [ArkLib/ToMathlib/RestrictedSumset.lean:169](../../../ArkLib/ToMathlib/RestrictedSumset.lean#L169) — Abbreviation for the "diagonal" variable `y = X₀ + X₁`.
- `def MvPolynomial.ehY` [ArkLib/ToMathlib/RestrictedSumsetGeneral.lean:191](../../../ArkLib/ToMathlib/RestrictedSumsetGeneral.lean#L191) — The "diagonal" variable `y = ∑_k X k`.

### `epsCA_ge_one_sub_inv_of_allButOne` (2 declarations, 2 files)

- `theorem CodingTheory.Bridge.epsCA_ge_one_sub_inv_of_allButOne` [ArkLib/ToMathlib/BGKS20AllButOne.lean:96](../../../ArkLib/ToMathlib/BGKS20AllButOne.lean#L96) — **T5.4 endpoint from the "all but one scalar" producer.** Under the hypotheses of `nearCertainBadLin
- `theorem CodingTheory.Bridge.epsCA_ge_one_sub_inv_of_allButOne` [ArkLib/ToMathlib/NearCertainBadLineProof.lean:103](../../../ArkLib/ToMathlib/NearCertainBadLineProof.lean#L103) — **T5.4 endpoint from an all-but-one near-certain bad line.**

### `eval_ehQ_eq_zero` (2 declarations, 2 files)

- `lemma MvPolynomial.eval_ehQ_eq_zero` [ArkLib/ToMathlib/RestrictedSumset.lean:294](../../../ArkLib/ToMathlib/RestrictedSumset.lean#L294) — `ehQ Cset` vanishes at every point `s : Fin 2 → F` whose two coordinates either coincide, or sum to
- `lemma MvPolynomial.eval_ehQ_eq_zero` [ArkLib/ToMathlib/RestrictedSumsetGeneral.lean:335](../../../ArkLib/ToMathlib/RestrictedSumsetGeneral.lean#L335) — `ehQ h Cset` vanishes at every point `s : Fin h → F` whose coordinates are not all distinct, or whos

### `finset_card_ge_of_pred_natCast_le_ennreal_lt` (2 declarations, 2 files)

- `lemma ProximityGap.finset_card_ge_of_pred_natCast_le_ennreal_lt` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean:127](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean#L127) — (no docstring)
- `theorem ProximityGap.finset_card_ge_of_pred_natCast_le_ennreal_lt` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean:131](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean#L131) — Convert an ENNReal lower bound on a finite set cardinality into a natural number weak cardinality bo

### `finset_card_gt_of_natCast_le_ennreal_lt` (2 declarations, 2 files)

- `lemma ProximityGap.finset_card_gt_of_natCast_le_ennreal_lt` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean:120](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves.lean#L120) — (no docstring)
- `theorem ProximityGap.finset_card_gt_of_natCast_le_ennreal_lt` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean:120](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/Curves/Assembly.lean#L120) — Convert an ENNReal lower bound on a finite set cardinality into a natural number strict cardinality

### `frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_prop` (2 declarations, 2 files)

- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_prop` [ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean:2293](../../../ArkLib/Data/CodingTheory/ListDecoding/Bounds.lean#L2293) — Prop-level C3.5 endpoint from coordinate-fiber cap plus T2.18. This wraps the unfolded reduction `fr
- `theorem CodingTheory.frs_list_decoding_capacity_cz25_of_coordFiberCap_T218_prop` [ArkLib/Data/CodingTheory/ListDecoding/CZ25CapacityPropEndpoint.lean:64](../../../ArkLib/Data/CodingTheory/ListDecoding/CZ25CapacityPropEndpoint.lean#L64) — **ABF26 Corollary 3.5 [CZ25 Cor 2.21] — named-`Prop` endpoint from the coordinate-fiber cap.** Concl

### `mcaPrizeLatticeResolved_with_spec_of_GSMassFrontiers_and_adjacent_upperWitnesses` (2 declarations, 2 files)

- `theorem ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_of_GSMassFrontiers_and_adjacent_upperWitnesses` [ArkLib/Data/CodingTheory/ProximityGap/MCAGSLatticePrizeSpec.lean:281](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAGSLatticePrizeSpec.lean#L281) — Adjacent GS mass frontiers resolve the four-rate MCA prize at the lower-frontier lattice indices and
- `theorem ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_of_GSMassFrontiers_and_adjacent_upperWitnesses` [ArkLib/Data/CodingTheory/ProximityGap/MCAGSLatticeResolvedSpec.lean:38](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAGSLatticeResolvedSpec.lean#L38) — Faithful GS mass frontiers plus adjacent explicit upper witnesses resolve the four-rate MCA prize at

### `mcaPrizeLatticeResolved_with_spec_of_GSPivotFrontiers_and_adjacent_upperWitnesses` (2 declarations, 2 files)

- `theorem ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_of_GSPivotFrontiers_and_adjacent_upperWitnesses` [ArkLib/Data/CodingTheory/ProximityGap/MCAGSLatticePrizeSpec.lean:316](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAGSLatticePrizeSpec.lean#L316) — Adjacent GS pivot/list-size frontiers resolve the four-rate MCA prize at the lower-frontier lattice
- `theorem ProximityGap.GrandChallengesLattice.mcaPrizeLatticeResolved_with_spec_of_GSPivotFrontiers_and_adjacent_upperWitnesses` [ArkLib/Data/CodingTheory/ProximityGap/MCAGSLatticeResolvedSpec.lean:76](../../../ArkLib/Data/CodingTheory/ProximityGap/MCAGSLatticeResolvedSpec.lean#L76) — Faithful GS pivot/list-size frontiers plus adjacent explicit upper witnesses resolve the four-rate M

### `nearCertainBadLine_of_allButOne` (2 declarations, 2 files)

- `theorem CodingTheory.Bridge.nearCertainBadLine_of_allButOne` [ArkLib/ToMathlib/BGKS20AllButOne.lean:80](../../../ArkLib/ToMathlib/BGKS20AllButOne.lean#L80) — **"All but one scalar" producer (BGKS20 line-witness shape).** Given a stack `u` that is **not** joi
- `theorem CodingTheory.Bridge.nearCertainBadLine_of_allButOne` [ArkLib/ToMathlib/NearCertainBadLineProof.lean:84](../../../ArkLib/ToMathlib/NearCertainBadLineProof.lean#L84) — **All-but-one producer for `NearCertainBadLine`.** If a stack is not jointly close and every scalar

### `qEntropy_mul_log_eq_qaryEntropy` (2 declarations, 2 files)

- `theorem CodingTheory.qEntropy_mul_log_eq_qaryEntropy` [ArkLib/Data/CodingTheory/ProximityPrizeLeaves.lean:143](../../../ArkLib/Data/CodingTheory/ProximityPrizeLeaves.lean#L143) — **Base-change bridge for the `q`-ary entropy.** For `q ≥ 2`, ArkLib's `qEntropy` (defined with base-
- `theorem CodingTheory.qEntropy_mul_log_eq_qaryEntropy` [ArkLib/Data/CodingTheory/ProximityPrizeLeaves2.lean:84](../../../ArkLib/Data/CodingTheory/ProximityPrizeLeaves2.lean#L84) — **Base-change bridge for the `q`-ary entropy** (re-proven locally so that this file is self-containe

### `totalDegree_ehQ_le` (2 declarations, 2 files)

- `lemma MvPolynomial.totalDegree_ehQ_le` [ArkLib/ToMathlib/RestrictedSumset.lean:265](../../../ArkLib/ToMathlib/RestrictedSumset.lean#L265) — `ehQ Cset` has total degree at most `\|Cset\| + 1`.
- `lemma MvPolynomial.totalDegree_ehQ_le` [ArkLib/ToMathlib/RestrictedSumsetGeneral.lean:316](../../../ArkLib/ToMathlib/RestrictedSumsetGeneral.lean#L316) — `ehQ h Cset` has total degree at most `deg(vdmX) + \|Cset\|`.

### `totalDegree_prod_sub_pow_le` (2 declarations, 2 files)

- `lemma MvPolynomial.totalDegree_prod_sub_pow_le` [ArkLib/ToMathlib/RestrictedSumset.lean:183](../../../ArkLib/ToMathlib/RestrictedSumset.lean#L183) — **Leading-part difference bound.** The product `∏_{c ∈ s} (y - C c)` differs from `y^{\|s\|}` by a pol
- `lemma MvPolynomial.totalDegree_prod_sub_pow_le` [ArkLib/ToMathlib/RestrictedSumsetGeneral.lean:195](../../../ArkLib/ToMathlib/RestrictedSumsetGeneral.lean#L195) — **Leading-part difference bound.** The product `∏_{c ∈ s} (y - C c)` differs from `y^{\|s\|}` by a pol

### `uniform_event_mass` (2 declarations, 2 files)

- `lemma OutOfDomSmpl.uniform_event_mass` [ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean:55](../../../ArkLib/ProofSystem/Stir/OutOfDomSmpl.lean#L55) — The mass that the `Pr_{...}[...]` PMF encoding assigns to an event under uniform sampling is exactly
- `lemma OutOfDomSmpl.uniform_event_mass` [ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean:166](../../../ArkLib/ProofSystem/Whir/OutofDomainSmpl.lean#L166) — The mass that the `Pr_{...}[...]` PMF encoding assigns to an event under uniform sampling is exactly

### `with` (2 declarations, 2 files)

- `instance with` [ArkLib/Data/CodingTheory/ProximityGap/GrandChallengeLDAttainment.lean:32](../../../ArkLib/Data/CodingTheory/ProximityGap/GrandChallengeLDAttainment.lean#L32) — (no docstring)
- `theorem with` [ArkLib/Data/CodingTheory/ProximityGap/PermanentlyBlocked.lean:55](../../../ArkLib/Data/CodingTheory/ProximityGap/PermanentlyBlocked.lean#L55) — (no docstring)

## Near-duplicate docstrings (Jaccard ≥ 0.85, 149 cross-file pairs)

Each pair has docstrings sharing a high fraction of (4+-letter) words, in different files. Most are unrelated coincidences in boilerplate; look for pairs where the *concept* matches.

- **1.00** `Binius.BinaryBasefold.CoreInteraction.finalSumcheckStepLogic` [ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean:899](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/ReductionLogic.lean#L899) vs `Binius.RingSwitching.SumcheckPhase.finalSumcheckStepLogic` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1000](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1000)
    - a: The Logic Instance for the final sumcheck step. This is a 1-message protocol where the prover sends
    - b: The Logic Instance for the final sumcheck step. This is a 1-message protocol where the prover sends
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:102](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L102) vs `Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:171](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L171)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:102](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L102) vs `Binius.RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:86](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L86)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleProof` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:102](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L102) vs `RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/RingSwitching/General.lean:96](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L96)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:74](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L74) vs `Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:140](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L140)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:74](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L74) vs `Binius.RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:74](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L74)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:74](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L74) vs `RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/RingSwitching/General.lean:84](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L84)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:117](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L117) vs `Binius.FRIBinius.FullFRIBinius.fullOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:191](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L191)
    - a: Perfect completeness for the full Binary Basefold protocol (reduction)
    - b: Perfect completeness for the full Binary Basefold protocol (reduction)
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:51](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L51) vs `Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:114](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L114)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:51](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L51) vs `Binius.RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:56](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L56)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.FullBinaryBasefold.fullOracleVerifier` [ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean:51](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/General.lean#L51) vs `RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/RingSwitching/General.lean:60](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L60)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Binius.BinaryBasefold.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:1154](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L1154) vs `Binius.RingSwitching.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:423](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L423)
    - a: This condition ensures that the witness polynomial `H` has the correct structure `eq(...) * t(...)`
    - b: This condition ensures that the witness polynomial `H` has the correct structure `A(...) * t'(...)`
- **1.00** `Binius.BinaryBasefold.witnessStructuralInvariant` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:1154](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L1154) vs `RingSwitching.witnessStructuralInvariant` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:439](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L439)
    - a: This condition ensures that the witness polynomial `H` has the correct structure `eq(...) * t(...)`
    - b: This condition ensures that the witness polynomial `H` has the correct structure `A(...) * t'(...)`
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1306](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1306) vs `Binius.RingSwitching.SumcheckPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1463](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1463)
    - a: RBR knowledge error for the final sumcheck step
    - b: RBR knowledge error for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1306](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1306) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1284](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1284)
    - a: RBR knowledge error for the final sumcheck step
    - b: RBR knowledge error for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:665](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L665) vs `Binius.RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1265](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1265)
    - a: The oracle reduction for the final sumcheck step
    - b: The oracle reduction for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:665](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L665) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1185](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1185)
    - a: The oracle reduction for the final sumcheck step
    - b: The oracle reduction for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1126](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1126) vs `Binius.RingSwitching.SumcheckPhase.finalSumcheckOracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1279](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1279)
    - a: Perfect completeness for the final sumcheck step
    - b: Perfect completeness for the final sumcheck step
- **1.00** `Binius.FRIBinius.CoreInteractionPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean:1317](../../../ArkLib/ProofSystem/Binius/FRIBinius/CoreInteractionPhase.lean#L1317) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrExtractor` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1287](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1287)
    - a: The round-by-round extractor for the final sumcheck step
    - b: The round-by-round extractor for the final sumcheck step
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:171](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L171) vs `Binius.RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:86](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L86)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleProof` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:171](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L171) vs `RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/RingSwitching/General.lean:96](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L96)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:140](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L140) vs `Binius.RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:74](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L74)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleReduction` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:140](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L140) vs `RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/RingSwitching/General.lean:84](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L84)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:114](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L114) vs `Binius.RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:56](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L56)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Binius.FRIBinius.FullFRIBinius.fullOracleVerifier` [ArkLib/ProofSystem/Binius/FRIBinius/General.lean:114](../../../ArkLib/ProofSystem/Binius/FRIBinius/General.lean#L114) vs `RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/RingSwitching/General.lean:60](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L60)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Binius.RingSwitching.BatchingPhase.PrvState` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:319](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L319) vs `RingSwitching.BatchingPhase.PrvState` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:121](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L121)
    - a: The state maintained by the prover throughout the batching phase.
    - b: The state maintained by the prover throughout the batching phase.
- **1.00** `Binius.RingSwitching.BatchingPhase.batchingInputRelation` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:97](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L97) vs `RingSwitching.BatchingPhase.batchingInputRelation` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:301](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L301)
    - a: Input relation: the witness `t` and `t'` are consistent, and `t` satisfies the original claim.
    - b: Input relation: the witness `t` and `t'` are consistent, and `t` satisfies the original claim.
- **1.00** `Binius.RingSwitching.BatchingPhase.batchingKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:483](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L483) vs `RingSwitching.BatchingPhase.batchingKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:406](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L406)
    - a: Knowledge state function for the batching phase.
    - b: Knowledge state function for the batching phase.
- **1.00** `Binius.RingSwitching.BatchingPhase.batchingMismatchPoly` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:854](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L854) vs `RingSwitching.BatchingPhase.batchingMismatchPoly` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:569](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L569)
    - a: Mismatch polynomial from row-decomposition difference `msg0 - s_bar`.
    - b: Mismatch polynomial from row-decomposition difference `msg0 - s_bar`.
- **1.00** `Binius.RingSwitching.BatchingPhase.batchingMismatchPoly_nonzero_of_embed_ne` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:908](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L908) vs `RingSwitching.BatchingPhase.batchingMismatchPoly_nonzero_of_embed_ne` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:611](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L611)
    - a: If embedded evaluation mismatches `msg0`, the mismatch polynomial is nonzero.
    - b: If embedded evaluation mismatches `msg0`, the mismatch polynomial is nonzero.
- **1.00** `Binius.RingSwitching.BatchingPhase.batchingMismatchPoly_totalDegree_le` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:878](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L878) vs `RingSwitching.BatchingPhase.batchingMismatchPoly_totalDegree_le` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:583](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L583)
    - a: Degree bound for mismatch polynomial: multilinear in `κ` vars, so total degree ≤ `κ`.
    - b: Degree bound for mismatch polynomial: multilinear in `κ` vars, so total degree ≤ `κ`.
- **1.00** `Binius.RingSwitching.BatchingPhase.batchingWitMid` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:408](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L408) vs `RingSwitching.BatchingPhase.batchingWitMid` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:306](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L306)
    - a: Intermediate witness types for RBR knowledge soundness.
    - b: Intermediate witness types for RBR knowledge soundness.
- **1.00** `Binius.RingSwitching.BatchingPhase.batching_compute_s0_sub_eq_eval_mismatch` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:860](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L860) vs `RingSwitching.BatchingPhase.batching_compute_s0_sub_eq_eval_mismatch` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:574](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L574)
    - a: The mismatch polynomial evaluates to the `compute_s0` difference.
    - b: The mismatch polynomial evaluates to the `compute_s0` difference.
- **1.00** `Binius.RingSwitching.BatchingPhase.failureState` [ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean:71](../../../ArkLib/ProofSystem/Binius/RingSwitching/BatchingPhase.lean#L71) vs `RingSwitching.BatchingPhase.failureState` [ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean:106](../../../ArkLib/ProofSystem/RingSwitching/BatchingPhase.lean#L106)
    - a: A dummy state returned by the verifier upon failure of Check 1.
    - b: A dummy state returned by the verifier upon failure of Check 1.
- **1.00** `Binius.RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:86](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L86) vs `RingSwitching.FullRingSwitching.fullOracleProof` [ArkLib/ProofSystem/RingSwitching/General.lean:96](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L96)
    - a: The full Binary Basefold protocol as a Proof
    - b: The full Binary Basefold protocol as a Proof
- **1.00** `Binius.RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:74](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L74) vs `RingSwitching.FullRingSwitching.fullOracleReduction` [ArkLib/ProofSystem/RingSwitching/General.lean:84](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L84)
    - a: The reduction for the full Binary Basefold protocol
    - b: The reduction for the full Binary Basefold protocol
- **1.00** `Binius.RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/General.lean:56](../../../ArkLib/ProofSystem/Binius/RingSwitching/General.lean#L56) vs `RingSwitching.FullRingSwitching.fullOracleVerifier` [ArkLib/ProofSystem/RingSwitching/General.lean:60](../../../ArkLib/ProofSystem/RingSwitching/General.lean#L60)
    - a: The oracle verifier for the full Binary Basefold protocol
    - b: The oracle verifier for the full Binary Basefold protocol
- **1.00** `Binius.RingSwitching.MLPEvalRelation` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:236](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L236) vs `RingSwitching.MLPEvalRelation` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:247](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L247)
    - a: Standard input relation for MLIOPCS: polynomial evaluation at point equals claimed evaluation
    - b: Standard input relation for MLIOPCS: polynomial evaluation at point equals claimed evaluation
- **1.00** `Binius.RingSwitching.MLPEvalStatement` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:203](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L203) vs `RingSwitching.MLPEvalStatement` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:208](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L208)
    - a: Initial input (input to the batching phase): a polynomial-evaluation claim `s = t(r)`.
    - b: Initial input (input to the Batching Phase): a polynomial-evaluation claim `s = t(r)`.
- **1.00** `Binius.RingSwitching.RingSwitching_SumcheckMultParam` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:381](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L381) vs `RingSwitching.RingSwitching_SumcheckMultParam` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:389](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L389)
    - a: Ring-Switching multiplier parameter for sumcheck, using `A_MLE` as the multiplier.
    - b: Ring-Switching multiplier parameter for sumcheck, using `A_MLE` as the multiplier.
- **1.00** `Binius.RingSwitching.SumcheckPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1721](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1721) vs `RingSwitching.SumcheckPhase.coreInteractionOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1579](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1579)
    - a: Large-field reduction: Sumcheck seqCompose, then append FinalSum
    - b: Large-field reduction: Sumcheck seqCompose, then append FinalSum
- **1.00** `Binius.RingSwitching.SumcheckPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1712](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1712) vs `RingSwitching.SumcheckPhase.coreInteractionOracleVerifier` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1543](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1543)
    - a: Large-field reduction verifier: Sumcheck seqCompose, then append FinalSum
    - b: Large-field reduction verifier: Sumcheck seqCompose, then append FinalSum
- **1.00** `Binius.RingSwitching.SumcheckPhase.coreInteraction_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1809](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1809) vs `RingSwitching.SumcheckPhase.coreInteraction_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1651](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1651)
    - a: RBR knowledge soundness for large-field reduction (Sumcheck ++ FinalSum)
    - b: RBR knowledge soundness for large-field reduction (Sumcheck ++ FinalSum)
- **1.00** `Binius.RingSwitching.SumcheckPhase.finalSumcheckKnowledgeError` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1463](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1463) vs `RingSwitching.SumcheckPhase.finalSumcheckRbrKnowledgeError` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1284](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1284)
    - a: RBR knowledge error for the final sumcheck step
    - b: RBR knowledge error for the final sumcheck step
- **1.00** `Binius.RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1265](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1265) vs `RingSwitching.SumcheckPhase.finalSumcheckOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1185](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1185)
    - a: The oracle reduction for the final sumcheck step
    - b: The oracle reduction for the final sumcheck step
- **1.00** `Binius.RingSwitching.SumcheckPhase.iteratedSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:606](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L606) vs `RingSwitching.SumcheckPhase.iteratedSumcheckKnowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:789](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L789)
    - a: Knowledge state function (KState) for single round
    - b: Knowledge state function (KState) for single round
- **1.00** `Binius.RingSwitching.SumcheckPhase.sumcheckLoopOracleReduction` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1691](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1691) vs `RingSwitching.SumcheckPhase.sumcheckLoopOracleReduction` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1516](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1516)
    - a: Composed oracle reduction for the SumcheckStep (seqCompose over ℓ')
    - b: Composed oracle reduction for the SumcheckStep (seqCompose over ℓ')
- **1.00** `Binius.RingSwitching.SumcheckPhase.sumcheckLoopOracleVerifier` [ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean:1682](../../../ArkLib/ProofSystem/Binius/RingSwitching/SumcheckPhase.lean#L1682) vs `RingSwitching.SumcheckPhase.sumcheckLoopOracleVerifier` [ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean:1497](../../../ArkLib/ProofSystem/RingSwitching/SumcheckPhase.lean#L1497)
    - a: Composed oracle verifier for the SumcheckStep (seqCompose over ℓ')
    - b: Composed oracle verifier for the SumcheckStep (seqCompose over ℓ')
- **1.00** `Binius.RingSwitching.TensorAlgebra` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:63](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L63) vs `RingSwitching.TensorAlgebra` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:63](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L63)
    - a: Tensor Algebra A = L ⊗_K L. Based on the spec, it's viewed as (2^κ)x(2^κ) arrays of K-elements. The
    - b: Tensor Algebra A = L ⊗_K L. Based on the spec, it's viewed as (2^κ)x(2^κ) arrays of K-elements. The
- **1.00** `Binius.RingSwitching.aeval_eqPolynomial_zeroOne` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:683](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L683) vs `RingSwitching.aeval_eqPolynomial_zeroOne` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:775](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L775)
    - a: `aeval` of `eqPolynomial` at a Boolean coefficient vector lands in `L₀` as `eqTilde`.
    - b: `aeval` of `eqPolynomial` at a Boolean coefficient vector lands in `L₀` as `eqTilde`.
- **1.00** `Binius.RingSwitching.aeval_eq_sum_eqTilde` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:700](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L700) vs `RingSwitching.aeval_eq_sum_eqTilde` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:792](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L792)
    - a: **MLE evaluation identity (through the algebra map).** For a multilinear `t` over `K₀`, its `L₀`-eva
    - b: **MLE evaluation identity (through the algebra map).** For a multilinear `t` over `K₀`, its `L₀`-eva
- **1.00** `Binius.RingSwitching.boolHypercubeEmb` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:889](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L889) vs `RingSwitching.boolHypercubeEmb` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1351](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1351)
    - a: The Boolean hypercube embedding `(Fin k → Fin 2) ↪ (Fin k → L₀)` induced by a 2-element domain embed
    - b: The Boolean hypercube embedding `(Fin k → Fin 2) ↪ (Fin k → L₀)` induced by a 2-element domain embed
- **1.00** `Binius.RingSwitching.boolHypercube_sum_eq` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:897](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L897) vs `RingSwitching.boolHypercube_sum_eq` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1359](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1359)
    - a: **`𝓑`-domain hypercube sum reindexes to the Boolean hypercube.** For any `𝓑 : Fin 2 ↪ L₀`, summing `
    - b: **`𝓑`-domain hypercube sum reindexes to the Boolean hypercube.** For any `𝓑 : Fin 2 ↪ L₀`, summing `
- **1.00** `Binius.RingSwitching.boolHypercube_sum_pinned` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:917](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L917) vs `RingSwitching.boolHypercube_sum_pinned` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1379](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1379)
    - a: **Pinned-`𝓑` Boolean-domain sumcheck sum.** When `𝓑` is pinned to the Boolean embedding (`𝓑 c = if c
    - b: **Pinned-`𝓑` Boolean-domain sumcheck sum.** When `𝓑` is pinned to the Boolean embedding (`𝓑 c = if c
- **1.00** `Binius.RingSwitching.check_rows_sum_eq_aeval` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:740](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L740) vs `RingSwitching.check_rows_sum_eq_aeval` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1209](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1209)
    - a: **DP24 ring-switching capstone (sum form).** The verifier's row-decomposition check sum, applied to
    - b: **DP24 ring-switching capstone (sum form).** The verifier's row-decomposition check sum, applied to
- **1.00** `Binius.RingSwitching.componentWise_φ₁_embed_MLE` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:171](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L171) vs `RingSwitching.componentWise_embed_MLE` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:171](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L171)
    - a: **Component-wise `φ₁` embedding**. Takes a polynomial `t'` with coefficients in `L` and embeds it in
    - b: **Component-wise `φ₁` embedding**. Takes a polynomial `t'` with coefficients in `L` and embeds it in
- **1.00** `Binius.RingSwitching.compute_A_MLE` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:370](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L370) vs `RingSwitching.compute_A_MLE` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:378](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L378)
    - a: Step 4b: P writes `A(X_0, ..., X_{ℓ'-1})` for its multilinear extension of `A_func`.
    - b: Step 4b: P writes `A(X_0, ..., X_{ℓ'-1})` for its multilinear extension of `A_func`.
- **1.00** `Binius.RingSwitching.compute_A_func` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:353](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L353) vs `RingSwitching.compute_A_func` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:361](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L361)
    - a: Step 4a: For each `w ∈ {0,1}^{ℓ'}`, P decompose `eq̃(r_κ, ..., r_{ℓ-1}, w_0, ..., w_{ℓ'-1})` `=: Σ_{
    - b: Step 4a: For each `w ∈ {0,1}^{ℓ'}`, P decompose `eq̃(r_κ, ..., r_{ℓ-1}, w_0, ..., w_{ℓ'-1})` `=: Σ_{
- **1.00** `Binius.RingSwitching.compute_final_eq_value` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:411](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L411) vs `RingSwitching.compute_final_eq_value` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:420](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L420)
    - a: Decompose the final eq tensor `e := Σ_{u ∈ {0,1}^κ} eq̃(u, r'') ⨂ e_u`, where e_u is the row compone
    - b: Decompose the final eq tensor `e := Σ_{u ∈ {0,1}^κ} eq̃(u, r'') ⨂ e_u`, where e_u is the row compone
- **1.00** `Binius.RingSwitching.compute_s0` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:394](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L394) vs `RingSwitching.compute_s0` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:403](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L403)
    - a: Step 5 (V): Compute `s₀ := Σ_{u ∈ {0,1}^κ} eqTilde(u, r'') ⋅ ŝ_u`, where ŝ_u is the row components o
    - b: Step 5 (V): Compute `s₀ := Σ_{u ∈ {0,1}^κ} eqTilde(u, r'') ⋅ ŝ_u`, where ŝ_u is the row components o
- **1.00** `Binius.RingSwitching.decompose_rows_packMLE` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:598](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L598) vs `RingSwitching.decompose_rows_packMLE` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1188](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1188)
    - a: **Row recovery of `t`-evaluations.** The row components of the prover's tensor `ŝ = embedded_MLP_eva
    - b: **Row recovery of `t`-evaluations.** The row components of the prover's tensor `ŝ = embedded_MLP_eva
- **1.00** `Binius.RingSwitching.decompose_rows_sum` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:552](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L552) vs `RingSwitching.decompose_rows_sum` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:670](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L670)
    - a: `decompose_tensor_algebra_rows` is additive over finite sums of tensors.
    - b: `decompose_tensor_algebra_rows` is additive over finite sums of tensors.
- **1.00** `Binius.RingSwitching.decompose_rows_φ₀φ₁` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:562](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L562) vs `RingSwitching.decompose_rows_φ₀φ₁` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:680](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L680)
    - a: Row decomposition of a separated tensor `φ₀(a) · φ₁(b) = a ⊗ b`: the `u`-th row component represents
    - b: Row decomposition of a separated tensor `φ₀(a) · φ₁(b) = a ⊗ b`: the `u`-th row component represents
- **1.00** `Binius.RingSwitching.decompose_tensor_algebra_columns` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:100](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L100) vs `RingSwitching.decompose_tensor_algebra_columns` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:100](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L100)
    - a: Decompose `ŝ` into column components `(ŝ =: Σ_{v ∈ {0,1}^κ} ŝ_v ⊗ β_v)`. This views `L ⊗ L` as a mod
    - b: Decompose `ŝ` into column components `(ŝ =: Σ_{v ∈ {0,1}^κ} ŝ_v ⊗ β_v)`. This views `L ⊗ L` as a mod
- **1.00** `Binius.RingSwitching.decompose_tensor_algebra_rows` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:92](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L92) vs `RingSwitching.decompose_tensor_algebra_rows` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:92](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L92)
    - a: Decompose `ŝ` into row components `(ŝ =: Σ_{u ∈ {0,1}^κ} β_u ⊗ ŝ_u)`. This views `L ⊗ L` as a module
    - b: Decompose `ŝ` into row components `(ŝ =: Σ_{u ∈ {0,1}^κ} β_u ⊗ ŝ_u)`. This views `L ⊗ L` as a module
- **1.00** `Binius.RingSwitching.embedded_MLP_eval_eq_sum` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:523](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L523) vs `RingSwitching.embedded_MLP_eval_eq_sum` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1152](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1152)
    - a: **DP24 packing expansion.** The prover's tensor `ŝ := φ₁(t')(φ₀(r_κ), …, φ₀(r_{ℓ-1}))` expands over
    - b: **DP24 packing expansion.** The prover's tensor `ŝ := φ₁(t')(φ₀(r_κ), …, φ₀(r_{ℓ-1}))` expands over
- **1.00** `Binius.RingSwitching.eqPoly_collapse` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:508](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L508) vs `RingSwitching.eqPoly_collapse` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:657](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L657)
    - a: The full `eqPolynomial` collapses through the mixed embedding to `φ₀` of its ordinary evaluation, by
    - b: The full `eqPolynomial` collapses through the mixed embedding to `φ₀` of its ordinary evaluation, by
- **1.00** `Binius.RingSwitching.eqTilde_concat_split` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:665](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L665) vs `RingSwitching.eqTilde_concat_split` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:758](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L758)
    - a: `eqTilde` of concatenated Boolean / point data factors along the κ/ℓ' split: `eqTilde (concat fp fs)
    - b: `eqTilde` of concatenated Boolean / point data factors along the κ/ℓ' split: `eqTilde (concat fp fs)
- **1.00** `Binius.RingSwitching.eqTilde_prod` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:616](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L616) vs `RingSwitching.eqTilde_prod` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:710](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L710)
    - a: `eqTilde` written as a product over coordinates of the symmetric Boolean factor.
    - b: `eqTilde` written as a product over coordinates of the symmetric Boolean factor.
- **1.00** `Binius.RingSwitching.hypercubeSplitEquiv` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:715](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L715) vs `RingSwitching.hypercubeSplitEquiv` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:807](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L807)
    - a: The κ-then-ℓ' hypercube concatenation `concatBit v w i = v i` for `i < κ`, `= w (i - κ)` otherwise —
    - b: The κ-then-ℓ' hypercube concatenation `concatBit v w i = v i` for `i < κ`, `= w (i - κ)` otherwise —
- **1.00** `Binius.RingSwitching.packMLE` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:114](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L114) vs `RingSwitching.packMLE` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:114](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L114)
    - a: **Definition 2.1 (MLE packing)**. Packs a small-field multilinear `t` into a large-field multilinear
    - b: **Definition 2.1 (MLE packing)**. Packs a small-field multilinear `t` into a large-field multilinear
- **1.00** `Binius.RingSwitching.packMLE_repr_eval` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:575](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L575) vs `RingSwitching.packMLE_repr_eval` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:693](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L693)
    - a: The basis coordinate of a packed evaluation recovers the small-field coefficient: `β.repr (t'(w)) u
    - b: The basis coordinate of a packed evaluation recovers the small-field coefficient: `β.repr (t'(w)) u
- **1.00** `Binius.RingSwitching.performCheckOriginalEvaluation_packMLE_iff` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:805](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L805) vs `RingSwitching.performCheckOriginalEvaluation_packMLE_iff_binaryTower` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1266](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1266)
    - a: **DP24 ring-switching capstone (decision form).** The verifier's Step-2 check on the prover's honest
    - b: **DP24 ring-switching capstone (decision form).** The verifier's Step-2 check on the prover's honest
- **1.00** `Binius.RingSwitching.prod_concat_split` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:627](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L627) vs `RingSwitching.prod_concat_split` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:721](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L721)
    - a: A product over `Fin (ℓ' + κ₀)` of a function defined by the κ/ℓ'-dichotomy splits as the product of
    - b: A product over `Fin (ℓ' + κ₀)` of a function defined by the κ/ℓ'-dichotomy splits as the product of
- **1.00** `Binius.RingSwitching.simulateQ_simOracle2_messageQuery` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:953](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L953) vs `RingSwitching.simulateQ_simOracle2_messageQuery` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1416](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1416)
    - a: **`simOracle2` message-query collapse (`OracleComp` form).** Simulating, via `simOracle2 oSpec t₁ t₂
    - b: **`simOracle2` message-query collapse (`OracleComp` form).** Simulating, via `simOracle2 oSpec t₁ t₂
- **1.00** `Binius.RingSwitching.simulateQ_simOracle2_query` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:975](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L975) vs `RingSwitching.simulateQ_simOracle2_query` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1438](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1438)
    - a: **`simOracle2` message-query collapse (`OptionT`-`query` form).** The same reduction as `simulateQ_s
    - b: **`simOracle2` message-query collapse (`OptionT`-`query` form).** The same reduction as `simulateQ_s
- **1.00** `Binius.RingSwitching.singleEq_collapse` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:491](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L491) vs `RingSwitching.singleEq_collapse` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:640](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L640)
    - a: A single `eqPolynomial` factor, evaluated through the mixed embedding `eval₂ φ₁ (φ₀ ∘ g)` at a Boole
    - b: A single `eqPolynomial` factor, evaluated through the mixed embedding `eval₂ φ₁ (φ₀ ∘ g)` at a Boole
- **1.00** `Binius.RingSwitching.sumcheckRoundRelation` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:447](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L447) vs `RingSwitching.sumcheckRoundRelation` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:463](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L463)
    - a: Input relation for single round: proper sumcheck statement
    - b: Input relation for single round: proper sumcheck statement
- **1.00** `Binius.RingSwitching.sumcheckSum_X0_eq` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:849](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L849) vs `RingSwitching.sumcheckSum_X0_eq` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1311](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1311)
    - a: **Sumcheck hypercube sum depends on the evaluation domain `𝓑`.** The single-variable sumcheck consis
    - b: **Sumcheck hypercube sum depends on the evaluation domain `𝓑`.** The single-variable sumcheck consis
- **1.00** `Binius.RingSwitching.sumcheckTarget_domain_indep` [ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean:868](../../../ArkLib/ProofSystem/Binius/RingSwitching/Prelude.lean#L868) vs `RingSwitching.sumcheckTarget_domain_indep` [ArkLib/ProofSystem/RingSwitching/Prelude.lean:1330](../../../ArkLib/ProofSystem/RingSwitching/Prelude.lean#L1330)
    - a: **No `𝓑`-free target satisfies sumcheck consistency for all domains `𝓑`.** If a single value `c` (in
    - b: **No `𝓑`-free target satisfies sumcheck consistency for all domains `𝓑`.** If a single value `c` (in

