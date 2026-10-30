# ArkLib dedup-candidate report

Generated from `docs/kb/_generated/declarations.json`. **Eyeball, do not auto-rewrite.** The point is to surface name collisions and doc-string overlap that *might* indicate an opportunity to consolidate.

## Stats

- `ArkLib` — 1155 files, 16069 declarations

## Same short-name across multiple files (397 groups)

Each group lists declarations sharing a short name across ≥2 files. Most are legitimate (overloaded interface, paper-shape vs general form), but the list is the right anchor to look for duplicates.

### `pSpec` (32 declarations, 30 files)

- `def CoordinateWise.SingleRound.pSpec` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:57](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L57) — The two-round single-challenge-round protocol (instantiated by Hachi's `QuadEval` reduction): the pr
- `abbrev Binius.FRIBinius.RingSwitch.pSpec` [ArkLib/ProofSystem/Binius/FRIBinius/RingSwitch.lean:84](../../../ArkLib/ProofSystem/Binius/FRIBinius/RingSwitch.lean#L84) — The original carrier wire and product sumcheck followed by the opening wire.
- `def GeneratorBatch.pSpec` [ArkLib/ProofSystem/Component/GeneratorBatch.lean:36](../../../ArkLib/ProofSystem/Component/GeneratorBatch.lean#L36) — One verifier challenge, with no prover messages.
- `def QuotientZeroTest.pSpec` [ArkLib/ProofSystem/Component/QuotientZeroTest.lean:63](../../../ArkLib/ProofSystem/Component/QuotientZeroTest.lean#L63) — The quotient is fixed in the first round, before the uniform evaluation challenge.
- `abbrev RandomEvaluation.pSpec` [ArkLib/ProofSystem/Component/RandomEvaluation.lean:50](../../../ArkLib/ProofSystem/Component/RandomEvaluation.lean#L50) — One uniformly sampled point.
- `def RandomQuery.pSpec` [ArkLib/ProofSystem/Component/RandomQuery.lean:68](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L68) — One uniformly sampled query from `Q`.
- `def SendChallenge.pSpec` [ArkLib/ProofSystem/Component/SendChallenge.lean:53](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L53) — One `V_to_P` challenge round carrying the fold challenge vector `c : Fin ℓ → C`.
- `def SendClaim.pSpec` [ArkLib/ProofSystem/Component/SendClaim.lean:62](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L62) — One prover→verifier message carrying the claim of type `Message`.
- `def SendWitness.pSpec` [ArkLib/ProofSystem/Component/SendWitness.lean:64](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L64) — (no docstring)
- `def Fri.Spec.pSpec` [ArkLib/ProofSystem/Fri/Spec/General.lean:60](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L60) — The complete FRI schedule: folding commitments, final polynomial, and query vector.
- `def Fri.Spec.FoldPhase.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:246](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L246) — Each round of the FRI protocol begins with the verifier sending a random field element as the challe
- `def Fri.Spec.FinalFoldPhase.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:441](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L441) — One field challenge followed by a polynomial message.
- `def Fri.Spec.QueryRound.pSpec` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:676](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L676) — One verifier challenge containing `l` initial-domain query positions.
- `abbrev Plonk.Assembly.pSpec` [ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean:117](../../../ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean#L117) — The six-round polynomial oracle protocol.
- `def Plonk.Batch.pSpec` [ArkLib/ProofSystem/Plonk/Batch/Reduction.lean:46](../../../ArkLib/ProofSystem/Plonk/Batch/Reduction.lean#L46) — One verifier challenge, with no prover messages.
- `def Plonk.GrandProduct.pSpec` [ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean:31](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean#L31) — A single joint challenge followed by the accumulator polynomial.
- `abbrev Plonk.Quotient.pSpec` [ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean:41](../../../ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean#L41) — Quotient first, then one uniform evaluation challenge.
- `def Plonk.SendWitness.pSpec` [ArkLib/ProofSystem/Plonk/SendWitness.lean:33](../../../ArkLib/ProofSystem/Plonk/SendWitness.lean#L33) — One table of three degree-bounded wire polynomials.
- `def RingSwitching.Packing.Head.pSpec` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:66](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L66) — One component-value message followed by one batching challenge.
- `def RingSwitching.Packing.ProductSumcheck.Round.pSpec` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean:31](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean#L31) — One clear degree-two polynomial followed by a scalar challenge over C.
- `def RingSwitching.Packing.ProductSumcheck.pSpec` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/SeqCompose.lean:76](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/SeqCompose.lean#L76) — All scalar challenges followed by the final packed-value message.
- `def RingSwitching.Packing.ProductSumcheck.Terminal.pSpec` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean:31](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean#L31) — The packed C-evaluation is sent as one clear message.
- `def RingSwitching.Packing.RingSwitch.pSpec` [ArkLib/ProofSystem/RingSwitching/Packing/RingSwitch.lean:75](../../../ArkLib/ProofSystem/RingSwitching/Packing/RingSwitch.lean#L75) — The generic head followed by the scalar-round sequence and terminal opening message.
- `abbrev RingSwitching.Packing.TensorPrefix.pSpec` [ArkLib/ProofSystem/RingSwitching/Packing/TensorPrefix.lean:74](../../../ArkLib/ProofSystem/RingSwitching/Packing/TensorPrefix.lean#L74) — The unchanged carrier/challenge wire followed by the shared scalar rounds.
- `abbrev Spartan.Batching.pSpec` [ArkLib/ProofSystem/Spartan/Batching/Reduction.lean:30](../../../ArkLib/ProofSystem/Spartan/Batching/Reduction.lean#L30) — One challenge containing three independent coefficients.
- `abbrev Spartan.SendEvaluations.pSpec` [ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean:30](../../../ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean#L30) — One message containing the three row evaluations.
- `abbrev Spartan.pSpec` [ArkLib/ProofSystem/Spartan/Protocol.lean:152](../../../ArkLib/ProofSystem/Spartan/Protocol.lean#L152) — The complete transcript specification.
- `abbrev Spartan.WitnessAttachment.pSpec` [ArkLib/ProofSystem/Spartan/WitnessAttachment.lean:50](../../../ArkLib/ProofSystem/Spartan/WitnessAttachment.lean#L50) — One prover message containing the padded witness table.
- `def Sumcheck.Spec.pSpec` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:130](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L130) — The protocol specification for the general sum-check protocol, which is the composition of the singl
- `def Sumcheck.Spec.SingleRound.pSpec` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:155](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L155) — The protocol specification for a single round of sum-check. Has the form `⟨!v[.P_to_V, .V_to_P], !v[
- `def ToyProblem.Spec.pSpec` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:217](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L217) — Protocol specification for the toy protocol: three rounds, in the order V → P  (γ : F)            --
- `def ToyProblem.SimplifiedIOR.pSpec` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:164](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L164) — Protocol specification for the simplified IOR: a single `V → P` round sending the combination random

### `oracleReduction` (30 declarations, 28 files)

- `def CheckClaim.oracleReduction` [ArkLib/ProofSystem/Component/CheckClaim.lean:214](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L214) — The oracle reduction for the `CheckClaim` oracle reduction.
- `def DoNothing.oracleReduction` [ArkLib/ProofSystem/Component/DoNothing.lean:93](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L93) — The oracle reduction for the `DoNothing` oracle reduction. - Prover simply returns the (non-oracle a
- `def GeneratorBatch.oracleReduction` [ArkLib/ProofSystem/Component/GeneratorBatch.lean:150](../../../ArkLib/ProofSystem/Component/GeneratorBatch.lean#L150) — Generator batching as a one-challenge oracle reduction.
- `def QuotientZeroTest.oracleReduction` [ArkLib/ProofSystem/Component/QuotientZeroTest.lean:159](../../../ArkLib/ProofSystem/Component/QuotientZeroTest.lean#L159) — The finite-domain zero test as an oracle reduction.
- `abbrev RandomEvaluation.oracleReduction` [ArkLib/ProofSystem/Component/RandomEvaluation.lean:59](../../../ArkLib/ProofSystem/Component/RandomEvaluation.lean#L59) — The random-evaluation reduction.
- `def RandomQuery.oracleReduction` [ArkLib/ProofSystem/Component/RandomQuery.lean:102](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L102) — The random-query reduction, with no oracle queries and no checks.
- `def ReduceClaim.oracleReduction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:266](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L266) — The oracle reduction for the `ReduceClaim` oracle reduction.
- `def SendChallenge.oracleReduction` [ArkLib/ProofSystem/Component/SendChallenge.lean:106](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L106) — The oracle reduction for `SendChallenge`.
- `def SendClaim.oracleReduction` [ArkLib/ProofSystem/Component/SendClaim.lean:125](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L125) — The oracle reduction for `SendClaim`.
- `def SendSingleWitness.Adapter.oracleReduction` [ArkLib/ProofSystem/Component/SendWitness.lean:272](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L272) — The one-message oracle reduction induced by an adapter.
- `def SendSingleWitness.oracleReduction` [ArkLib/ProofSystem/Component/SendWitness.lean:437](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L437) — (no docstring)
- `def Plonk.Assembly.Circuit.oracleReduction` [ArkLib/ProofSystem/Plonk/Assembly/CircuitExtraction.lean:30](../../../ArkLib/ProofSystem/Plonk/Assembly/CircuitExtraction.lean#L30) — The polynomial protocol with public equality rows and cleared public constants.
- `def Plonk.Assembly.oracleReduction` [ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean:120](../../../ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean#L120) — The full Plonk reduction, retaining every earlier oracle through its terminal guard.
- `def Plonk.Batch.oracleReduction` [ArkLib/ProofSystem/Plonk/Batch/Reduction.lean:217](../../../ArkLib/ProofSystem/Plonk/Batch/Reduction.lean#L217) — Residual batching over the full retained Plonk context.
- `def Plonk.GrandProduct.oracleReduction` [ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean:196](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean#L196) — The joint-challenge Plonk permutation grand product oracle reduction.
- `def Plonk.Quotient.oracleReduction` [ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean:92](../../../ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean#L92) — The honest quotient prover and its terminal evaluation guard.
- `def Plonk.SendWitness.oracleReduction` [ArkLib/ProofSystem/Plonk/SendWitness.lean:96](../../../ArkLib/ProofSystem/Plonk/SendWitness.lean#L96) — The initial polynomial-table reveal reduction.
- `def Spartan.Batching.oracleReduction` [ArkLib/ProofSystem/Spartan/Batching/Reduction.lean:60](../../../ArkLib/ProofSystem/Spartan/Batching/Reduction.lean#L60) — The independent batching reduction.
- `def Spartan.SendEvaluations.oracleReduction` [ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean:66](../../../ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean#L66) — The guarded send-evaluations reduction.
- `def Spartan.oracleReduction` [ArkLib/ProofSystem/Spartan/Protocol.lean:163](../../../ArkLib/ProofSystem/Spartan/Protocol.lean#L163) — The seven-stage Spartan PIOP, including an executable honest prover.
- `def Spartan.FirstSumcheck.oracleReduction` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:204](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L204) — The first virtual sumcheck reduction with its executable honest prover.
- `def Spartan.SecondSumcheck.oracleReduction` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:226](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L226) — The second virtual sumcheck reduction with its executable honest prover.
- `def Spartan.WitnessAttachment.oracleReduction` [ArkLib/ProofSystem/Spartan/WitnessAttachment.lean:126](../../../ArkLib/ProofSystem/Spartan/WitnessAttachment.lean#L126) — The original-instance witness attachment reduction.
- `abbrev Spartan.ZeroCheck.oracleReduction` [ArkLib/ProofSystem/Spartan/ZeroCheck/Reduction.lean:34](../../../ArkLib/ProofSystem/Spartan/ZeroCheck/Reduction.lean#L34) — Spartan's first challenge, retaining the attached witness and all matrix oracles.
- `def Sumcheck.Spec.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:447](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L447) — The oracle sum-check reduction. Its semantic honest prover materializes polynomial projections; `Sum
- `def Sumcheck.Spec.SingleRound.Simple.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:302](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L302) — (no docstring)
- `def Sumcheck.Spec.SingleRound.oracleReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:971](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L971) — The sum-check oracle reduction for the `i`-th round of the sum-check protocol
- `def ToyProblem.Impl.IRS.oracleReduction` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:273](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L273) — Oracle-flavoured honest toy-problem reduction instantiated with the executable interleaved-RS encode
- `def ToyProblem.Spec.oracleReduction` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:530](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L530) — Honest oracle reduction for the toy protocol: the `OracleProver` / `OracleVerifier` pair packaged as
- `def ToyProblem.SimplifiedIOR.oracleReduction` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:313](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L313) — The simplified protocol as a genuine interactive oracle reduction.

### `knowledgeStateFunction` (24 declarations, 24 files)

- `def CheckClaim.knowledgeStateFunction` [ArkLib/ProofSystem/Component/CheckClaim.lean:111](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L111) — The knowledge state function for the `CheckClaim` reduction, mirroring the trivial-verifier template
- `def GeneratorBatch.knowledgeStateFunction` [ArkLib/ProofSystem/Component/GeneratorBatch.lean:165](../../../ArkLib/ProofSystem/Component/GeneratorBatch.lean#L165) — Knowledge means all inputs vanish before the challenge, and the batch vanishes afterwards.
- `def QuotientZeroTest.knowledgeStateFunction` [ArkLib/ProofSystem/Component/QuotientZeroTest.lean:175](../../../ArkLib/ProofSystem/Component/QuotientZeroTest.lean#L175) — Before the challenge, knowledge means the input vanishes on the domain; afterwards it means the samp
- `abbrev RandomEvaluation.knowledgeStateFunction` [ArkLib/ProofSystem/Component/RandomEvaluation.lean:96](../../../ArkLib/ProofSystem/Component/RandomEvaluation.lean#L96) — Before sampling, knowledge means `P = 0`; afterwards it means `P` vanishes at the point.
- `def RandomQuery.knowledgeStateFunction` [ArkLib/ProofSystem/Component/RandomQuery.lean:158](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L158) — Before the query, knowledge means the identity `f = g`; afterwards it means agreement at the sampled
- `def ReduceClaim.knowledgeStateFunction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:141](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L141) — The knowledge state function for the `ReduceClaim` reduction.
- `def SendSingleWitness.Adapter.knowledgeStateFunction` [ArkLib/ProofSystem/Component/SendWitness.lean:317](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L317) — Decoded relation membership is the knowledge predicate before and after the send.
- `def Plonk.Assembly.Circuit.knowledgeStateFunction` [ArkLib/ProofSystem/Plonk/Assembly/CircuitExtraction.lean:61](../../../ArkLib/ProofSystem/Plonk/Assembly/CircuitExtraction.lean#L61) — The composed knowledge states, with the original circuit relation at the empty prefix.
- `def Plonk.Assembly.knowledgeStateFunction` [ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean:195](../../../ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean#L195) — The named knowledge state of the full oracle verifier.
- `def Plonk.Batch.knowledgeStateFunction` [ArkLib/ProofSystem/Plonk/Batch/Reduction.lean:235](../../../ArkLib/ProofSystem/Plonk/Batch/Reduction.lean#L235) — Knowledge is vanishing of all three inputs before the challenge and the batch afterwards.
- `def Plonk.GrandProduct.knowledgeStateFunction` [ArkLib/ProofSystem/Plonk/GrandProduct/Security.lean:43](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Security.lean#L43) — The accumulator exists after the challenge and is fixed by the prover message.
- `def Plonk.Quotient.knowledgeStateFunction` [ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean:170](../../../ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean#L170) — The named fixed-prefix knowledge state is transported by the executable lens.
- `def Plonk.SendWitness.knowledgeStateFunction` [ArkLib/ProofSystem/Plonk/SendWitness.lean:123](../../../ArkLib/ProofSystem/Plonk/SendWitness.lean#L123) — The table relation is transferred from the witness to its revealed message.
- `def RingSwitching.Packing.Head.knowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:333](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L333) — Knowledge states retain the scalar guard, with the committed source at each round.
- `def RingSwitching.Packing.ProductSumcheck.Round.knowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/RoundSecurity.lean:86](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/RoundSecurity.lean#L86) — Knowledge states with message and output extraction obligations.
- `def RingSwitching.Packing.ProductSumcheck.Terminal.knowledgeStateFunction` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean:213](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean#L213) — The knowledge states retain the accepted product guard and exact same-commitment opening.
- `def Spartan.Batching.knowledgeStateFunction` [ArkLib/ProofSystem/Spartan/Batching/Reduction.lean:103](../../../ArkLib/ProofSystem/Spartan/Batching/Reduction.lean#L103) — Knowledge is truth of all row claims before sampling and of the batched claim afterwards.
- `def Spartan.SendEvaluations.knowledgeStateFunction` [ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean:110](../../../ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean#L110) — The input relation is the knowledge invariant both before and after the prover message.
- `def Spartan.knowledgeStateFunction` [ArkLib/ProofSystem/Spartan/Security.lean:163](../../../ArkLib/ProofSystem/Spartan/Security.lean#L163) — The composed knowledge invariant, retaining every earlier rejecting guard. The constituent guards an
- `def Spartan.FirstSumcheck.knowledgeStateFunction` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:385](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L385) — The inner semantic knowledge state transported through the virtual-polynomial lens. The underlying c
- `def Spartan.SecondSumcheck.knowledgeStateFunction` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:388](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L388) — The inner semantic knowledge state transported through the virtual-polynomial lens. The underlying c
- `def Spartan.Terminal.knowledgeStateFunction` [ArkLib/ProofSystem/Spartan/Terminal.lean:181](../../../ArkLib/ProofSystem/Spartan/Terminal.lean#L181) — A terminal knowledge state records the semantic terminal equation.
- `def Spartan.WitnessAttachment.knowledgeStateFunction` [ArkLib/ProofSystem/Spartan/WitnessAttachment.lean:185](../../../ArkLib/ProofSystem/Spartan/WitnessAttachment.lean#L185) — The final knowledge predicate uses the witness read from the single prover message.
- `def Spartan.ZeroCheck.knowledgeStateFunction` [ArkLib/ProofSystem/Spartan/ZeroCheck/Reduction.lean:80](../../../ArkLib/ProofSystem/Spartan/ZeroCheck/Reduction.lean#L80) — The first challenge's semantic knowledge predicate. Its polynomial view uses nonconstructive coeffic

### `verifier` (26 declarations, 23 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.verifier` [ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean:432](../../../ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean#L432) — The reduction's verifier (Hachi §4.2, Figure 3) is a **pure pass-through**: it re-emits the statemen
- `def CoordinateWise.CommittedScalar.verifier` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:137](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L137) — Pure statement-extending verifier shared by committed scalar phases.
- `def Binius.FRIBinius.RingSwitch.verifier` [ArkLib/ProofSystem/Binius/FRIBinius/RingSwitch.lean:56](../../../ArkLib/ProofSystem/Binius/FRIBinius/RingSwitch.lean#L56) — The frontend verifier is defined through the shared prefix protocol.
- `def CheckClaim.verifier` [ArkLib/ProofSystem/Component/CheckClaim.lean:72](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L72) — The verifier for the `CheckClaim` reduction.
- `def DoNothing.verifier` [ArkLib/ProofSystem/Component/DoNothing.lean:40](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L40) — The verifier for the `DoNothing` reduction.
- `def NoInteraction.verifier` [ArkLib/ProofSystem/Component/NoInteraction.lean:57](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L57) — The verifier in a no-interaction reduction takes an empty transcript, and hence reduces to a functio
- `def ReduceClaim.verifier` [ArkLib/ProofSystem/Component/ReduceClaim.lean:62](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L62) — The verifier for the `ReduceClaim` reduction.
- `def SendWitness.verifier` [ArkLib/ProofSystem/Component/SendWitness.lean:87](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L87) — (no docstring)
- `def RingSwitching.Lift.verifier` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:142](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L142) — The switch's pure statement-extending verifier, from the committed-scalar shell.
- `def RingSwitching.Packing.Head.verifier` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:164](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L164) — Reject a failed reconstruction and otherwise return the derived batched claim.
- `def RingSwitching.Packing.ProductSumcheck.Round.verifier` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean:83](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean#L83) — A failed Boolean sum check aborts; acceptance extends the original challenge prefix.
- `def RingSwitching.Packing.ProductSumcheck.verifier` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/SeqCompose.lean:87](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/SeqCompose.lean#L87) — The complete-tail verifier ends at the packed evaluation point and value.
- `def RingSwitching.Packing.ProductSumcheck.Terminal.verifier` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean:65](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean#L65) — A failed product check aborts the oracle verifier.
- `def RingSwitching.Packing.RingSwitch.verifier` [ArkLib/ProofSystem/RingSwitching/Packing/RingSwitch.lean:87](../../../ArkLib/ProofSystem/RingSwitching/Packing/RingSwitch.lean#L87) — The oracle verifier preserving the commitment through the final evaluation claim.
- `def RingSwitching.Packing.TensorPrefix.verifier` [ArkLib/ProofSystem/RingSwitching/Packing/TensorPrefix.lean:78](../../../ArkLib/ProofSystem/RingSwitching/Packing/TensorPrefix.lean#L78) — The verifier is an instance of the shared ring-switching verifier.
- `abbrev Sumcheck.Interaction.Computable.verifier` [ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean:39](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean#L39) — The shared verifier, with Horner evaluation as its oracle interface.
- `def Sumcheck.Interaction.MultivariateRound.verifier` [ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:69](../../../ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean#L69) — A fixed-challenge verifier with a multivariate input and output interface.
- `def Sumcheck.Interaction.Native.Core.verifier` [ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:98](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean#L98) — The verifier uses only declared answers. Its original-oracle view is exported, never queried to deci
- `def Sumcheck.Interaction.Native.verifier` [ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:348](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean#L348) — The mathematical specialization of the shared verifier.
- `def Sumcheck.Interaction.SingleRound.verifier` [ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:75](../../../ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean#L75) — The verifier receives no concrete polynomial; all polynomial use is through evaluation.
- `def Sumcheck.Spec.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:156](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L156) — The ordinary sum-check verifier materializes its polynomial oracles using mathematical evaluation, w
- `def Sumcheck.Spec.SingleRound.Simple.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:249](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L249) — The verifier for the simple description of a single round of sum-check
- `def Sumcheck.Spec.SingleRound.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:858](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L858) — The verifier for the `i`-th round of the sum-check protocol
- `def Sumcheck.Spec.SingleRound.Unfolded.verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1250](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1250) — The (non-oracle) verifier of the sum-check protocol for the `i`-th round, where `i < n + 1`
- `def ToyProblem.Spec.verifier` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:402](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L402) — Honest verifier for the toy protocol. Takes the bundled input `(stmt, oStmt) = ((v, μ₁, μ₂), (f₁, f₂
- `def ToyProblem.SimplifiedIOR.verifier` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:217](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L217) — Honest verifier for the simplified IOR. Reads `γ` from the transcript and produces the new statement

### `oracleVerifier` (25 declarations, 23 files)

- `def CheckClaim.oracleVerifier` [ArkLib/ProofSystem/Component/CheckClaim.lean:194](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L194) — (no docstring)
- `def DoNothing.oracleVerifier` [ArkLib/ProofSystem/Component/DoNothing.lean:83](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L83) — The oracle verifier for the `DoNothing` oracle reduction.
- `def GeneratorBatch.oracleVerifier` [ArkLib/ProofSystem/Component/GeneratorBatch.lean:118](../../../ArkLib/ProofSystem/Component/GeneratorBatch.lean#L118) — Forward the uniform challenge and expose the virtual batch without additional checks.
- `def QuotientZeroTest.oracleVerifier` [ArkLib/ProofSystem/Component/QuotientZeroTest.lean:91](../../../ArkLib/ProofSystem/Component/QuotientZeroTest.lean#L91) — Query the dividend and quotient, guard their evaluation identity, then return acceptance.
- `abbrev RandomEvaluation.oracleVerifier` [ArkLib/ProofSystem/Component/RandomEvaluation.lean:56](../../../ArkLib/ProofSystem/Component/RandomEvaluation.lean#L56) — The verifier forwards the point and retains every input oracle.
- `def RandomQuery.oracleVerifier` [ArkLib/ProofSystem/Component/RandomQuery.lean:85](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L85) — The verifier forwards its query and retains every input oracle.
- `def ReduceClaim.oracleVerifier` [ArkLib/ProofSystem/Component/ReduceClaim.lean:256](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L256) — The oracle verifier for the `ReduceClaim` oracle reduction.
- `def SendChallenge.oracleVerifier` [ArkLib/ProofSystem/Component/SendChallenge.lean:86](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L86) — (no docstring)
- `def SendClaim.oracleVerifier` [ArkLib/ProofSystem/Component/SendClaim.lean:117](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L117) — (no docstring)
- `def SendSingleWitness.Adapter.oracleVerifier` [ArkLib/ProofSystem/Component/SendWitness.lean:267](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L267) — The verifier never rejects and exposes the adapter's oracle representation.
- `def SendSingleWitness.oracleVerifier` [ArkLib/ProofSystem/Component/SendWitness.lean:414](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L414) — The oracle verifier for the `SendSingleWitness` oracle reduction. The verifier receives the input st
- `def Plonk.Batch.oracleVerifier` [ArkLib/ProofSystem/Plonk/Batch/Reduction.lean:169](../../../ArkLib/ProofSystem/Plonk/Batch/Reduction.lean#L169) — Forward the public context and expose the virtual batch.
- `def Plonk.GrandProduct.oracleVerifier` [ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean:159](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean#L159) — Forward the joint challenge and expose the derived residual oracles.
- `def Plonk.Quotient.oracleVerifier` [ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean:87](../../../ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean#L87) — The actual evaluation-only quotient verifier in the retained Plonk context.
- `def Plonk.SendWitness.oracleVerifier` [ArkLib/ProofSystem/Plonk/SendWitness.lean:72](../../../ArkLib/ProofSystem/Plonk/SendWitness.lean#L72) — Reveal the table through its evaluation-only interface.
- `def Spartan.Batching.oracleVerifier` [ArkLib/ProofSystem/Spartan/Batching/Reduction.lean:50](../../../ArkLib/ProofSystem/Spartan/Batching/Reduction.lean#L50) — The verifier forms the claimed sum and retains the original oracle family.
- `def Spartan.SendEvaluations.oracleVerifier` [ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean:44](../../../ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean#L44) — The verifier reads the three scalar claims and checks their weighted residual.
- `def Spartan.FirstSumcheck.oracleVerifier` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:98](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L98) — The first sumcheck oracle verifier, with its virtual input and retained context.
- `def Spartan.SecondSumcheck.oracleVerifier` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:154](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L154) — The second sumcheck verifier uses the virtual degree-two input and retained context.
- `def Spartan.WitnessAttachment.oracleVerifier` [ArkLib/ProofSystem/Spartan/WitnessAttachment.lean:121](../../../ArkLib/ProofSystem/Spartan/WitnessAttachment.lean#L121) — The verifier attaches the sent witness and forwards all matrix evaluations.
- `def Sumcheck.Spec.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:369](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L369) — The oracle verifier for the full sum-check protocol. It computes only with the sent messages.
- `def Sumcheck.Spec.SingleRound.Simple.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:281](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L281) — (no docstring)
- `def Sumcheck.Spec.SingleRound.oracleVerifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:879](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L879) — The oracle verifier for the `i`-th round of the sum-check protocol.
- `def ToyProblem.Spec.oracleVerifier` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:508](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L508) — Oracle verifier for the toy protocol. Queries the prover's message `g` once and the two oracle codew
- `def ToyProblem.SimplifiedIOR.oracleVerifier` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:302](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L302) — Oracle verifier for the simplified IOR. The explicit output is the combined linear claim; the output

### `reduction` (24 declarations, 23 files)

- `def KZG.CommitmentScheme.reduction` [ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean:124](../../../ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean#L124) — The reduction breaking ARSDH using a successful function-binding adversary. The reduction follows th
- `def CoordinateWise.CommittedScalar.reduction` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:312](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L312) — **The committed scalar phase as a protocol object**: the honest prover shell paired with the stateme
- `def Binius.FRIBinius.RingSwitch.reduction` [ArkLib/ProofSystem/Binius/FRIBinius/RingSwitch.lean:60](../../../ArkLib/ProofSystem/Binius/FRIBinius/RingSwitch.lean#L60) — The frontend reduction is defined through the shared prefix protocol.
- `def CheckClaim.reduction` [ArkLib/ProofSystem/Component/CheckClaim.lean:77](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L77) — The reduction for the `CheckClaim` reduction.
- `def DoNothing.reduction` [ArkLib/ProofSystem/Component/DoNothing.lean:49](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L49) — The reduction for the `DoNothing` reduction. - Prover simply returns the statement and witness. - Ve
- `def NoInteraction.reduction` [ArkLib/ProofSystem/Component/NoInteraction.lean:70](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L70) — The no-interaction reduction can be specified by a tuple of functions: - `mapStmt : StmtIn → StmtOut
- `def ReduceClaim.reduction` [ArkLib/ProofSystem/Component/ReduceClaim.lean:66](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L66) — The reduction for the `ReduceClaim` reduction.
- `def SendWitness.reduction` [ArkLib/ProofSystem/Component/SendWitness.lean:91](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L91) — (no docstring)
- `def Fri.Spec.reduction` [ArkLib/ProofSystem/Fri/Spec/General.lean:103](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L103) — The complete FRI reduction, including the final query checks.
- `def RingSwitching.Lift.reduction` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:258](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L258) — **The switch as a protocol object**: the honest prover at `honestWitness` paired with the statement-
- `def RingSwitching.Packing.Head.reduction` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:174](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L174) — The reusable scalar-claim reduction, parameterized by both algebras, the message encoding and the ba
- `def RingSwitching.Packing.OpeningAdapter.reduction` [ArkLib/ProofSystem/RingSwitching/Packing/OpeningAdapter.lean:125](../../../ArkLib/ProofSystem/RingSwitching/Packing/OpeningAdapter.lean#L125) — A general multilinear opening accepting contextual evaluation inputs.
- `def RingSwitching.Packing.ProductSumcheck.Round.reduction` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean:88](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean#L88) — The scalar-round reduction preserving the commitment oracle.
- `def RingSwitching.Packing.ProductSumcheck.reduction` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/SeqCompose.lean:94](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/SeqCompose.lean#L94) — The product-sumcheck tail preserving the commitment oracle and ending with an opening message.
- `def RingSwitching.Packing.ProductSumcheck.Terminal.reduction` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean:70](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean#L70) — The terminal reduction ends at the original commitment's evaluation relation over C.
- `def RingSwitching.Packing.RingSwitch.reduction` [ArkLib/ProofSystem/RingSwitching/Packing/RingSwitch.lean:93](../../../ArkLib/ProofSystem/RingSwitching/Packing/RingSwitch.lean#L93) — The prover packs the source and preserves the packed polynomial through the tail.
- `def RingSwitching.Packing.TensorPrefix.reduction` [ArkLib/ProofSystem/RingSwitching/Packing/TensorPrefix.lean:82](../../../ArkLib/ProofSystem/RingSwitching/Packing/TensorPrefix.lean#L82) — The prover and verifier are an instance of the shared reduction.
- `def Sumcheck.Interaction.MultivariateRound.reduction` [ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:78](../../../ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean#L78) — The message is private prover input; the verifier sees only its evaluation interface.
- `def Sumcheck.Spec.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:434](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L434) — The sum-check reduction with semantic polynomial projection in its honest prover. `Sumcheck.Impl.Com
- `def Sumcheck.Spec.SingleRound.Simple.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:268](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L268) — The reduction for the simple description of a single round of sum-check
- `def Sumcheck.Spec.SingleRound.reduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:952](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L952) — The sum-check reduction for the `i`-th round of the sum-check protocol
- `def ToyProblem.Impl.IRS.reduction` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:262](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L262) — The honest toy-problem reduction instantiated with the executable interleaved-RS encoder.
- `def ToyProblem.Spec.reduction` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:416](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L416) — Honest reduction for the toy protocol: the package `{prover, verifier}` over the bundled-input `Redu
- `def ToyProblem.SimplifiedIOR.reduction` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:228](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L228) — Honest reduction for the simplified IOR.

### `guardedForm` (23 declarations, 23 files)

- `def GeneratorBatch.guardedForm` [ArkLib/ProofSystem/Component/GeneratorBatch.lean:133](../../../ArkLib/ProofSystem/Component/GeneratorBatch.lean#L133) — The forwarding stage has an always-true guard.
- `def QuotientZeroTest.guardedForm` [ArkLib/ProofSystem/Component/QuotientZeroTest.lean:136](../../../ArkLib/ProofSystem/Component/QuotientZeroTest.lean#L136) — Named guard and output data for guarded composition and knowledge bridges.
- `abbrev RandomEvaluation.guardedForm` [ArkLib/ProofSystem/Component/RandomEvaluation.lean:62](../../../ArkLib/ProofSystem/Component/RandomEvaluation.lean#L62) — The verifier's always-true guard.
- `def RandomQuery.guardedForm` [ArkLib/ProofSystem/Component/RandomQuery.lean:111](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L111) — The verifier has the always-true guard and deterministic query-forwarding verdict.
- `def SendSingleWitness.Adapter.guardedForm` [ArkLib/ProofSystem/Component/SendWitness.lean:302](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L302) — The stage has a constantly true guard.
- `def Plonk.Assembly.guardedForm` [ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean:131](../../../ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean#L131) — The composed verifier retains the terminal quotient guard.
- `def Plonk.Batch.guardedForm` [ArkLib/ProofSystem/Plonk/Batch/Reduction.lean:189](../../../ArkLib/ProofSystem/Plonk/Batch/Reduction.lean#L189) — Batching forwards every transcript without a guard.
- `def Plonk.GrandProduct.guardedForm` [ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean:174](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean#L174) — The Plonk permutation grand product stage forwards without a runtime guard.
- `def Plonk.Quotient.guardedForm` [ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean:103](../../../ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean#L103) — The transported guard checks the same multiplication identity as the generic zero test.
- `def Plonk.SendWitness.guardedForm` [ArkLib/ProofSystem/Plonk/SendWitness.lean:84](../../../ArkLib/ProofSystem/Plonk/SendWitness.lean#L84) — Revealing a table never rejects.
- `def RingSwitching.Packing.Head.guardedForm` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:180](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L180) — The exact guard and accepted output of the verifier.
- `def RingSwitching.Packing.ProductSumcheck.Round.guardedForm` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean:94](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean#L94) — The round's exact guarded form supports state-aware composition.
- `def RingSwitching.Packing.ProductSumcheck.guardedForm` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/SeqCompose.lean:109](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/SeqCompose.lean#L109) — The complete tail preserves failure from every scalar round and the terminal check.
- `def RingSwitching.Packing.ProductSumcheck.Terminal.guardedForm` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean:76](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean#L76) — The deterministic guarded form required by checked sequential composition.
- `def RingSwitching.Packing.RingSwitch.guardedForm` [ArkLib/ProofSystem/RingSwitching/Packing/RingSwitch.lean:107](../../../ArkLib/ProofSystem/RingSwitching/Packing/RingSwitch.lean#L107) — Guarded form of the generic head followed by the tail.
- `def Spartan.Batching.guardedForm` [ArkLib/ProofSystem/Spartan/Batching/Reduction.lean:87](../../../ArkLib/ProofSystem/Spartan/Batching/Reduction.lean#L87) — Batching has an always-true guard.
- `def Spartan.SendEvaluations.guardedForm` [ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean:101](../../../ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean#L101) — The deterministic guard and output of the underlying verifier.
- `def Spartan.guardedForm` [ArkLib/ProofSystem/Spartan/Protocol.lean:171](../../../ArkLib/ProofSystem/Spartan/Protocol.lean#L171) — The conjunction of all component guards, with their retained-context outputs. Its semantic sumcheck
- `def Spartan.FirstSumcheck.guardedForm` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:116](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L116) — The lifted verifier retains every sumcheck rejection guard. The semantic guarded form mentions mathe
- `def Spartan.SecondSumcheck.guardedForm` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:177](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L177) — Every rejection guard of the inner sumcheck is retained by the lifted verifier. The semantic guarded
- `def Spartan.Terminal.guardedForm` [ArkLib/ProofSystem/Spartan/Terminal.lean:166](../../../ArkLib/ProofSystem/Spartan/Terminal.lean#L166) — Guarded form of the materialized terminal verifier.
- `def Spartan.WitnessAttachment.guardedForm` [ArkLib/ProofSystem/Spartan/WitnessAttachment.lean:152](../../../ArkLib/ProofSystem/Spartan/WitnessAttachment.lean#L152) — Attachment has no rejecting guard and records the actual sent witness table.
- `abbrev Spartan.ZeroCheck.guardedForm` [ArkLib/ProofSystem/Spartan/ZeroCheck/Reduction.lean:39](../../../ArkLib/ProofSystem/Spartan/ZeroCheck/Reduction.lean#L39) — The first challenge has an always-true guard.

### `oracleProver` (23 declarations, 21 files)

- `def CheckClaim.oracleProver` [ArkLib/ProofSystem/Component/CheckClaim.lean:164](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L164) — The oracle prover for the `CheckClaim` oracle reduction: it forwards the statement and all oracle st
- `def DoNothing.oracleProver` [ArkLib/ProofSystem/Component/DoNothing.lean:73](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L73) — The oracle prover for the `DoNothing` oracle reduction.
- `def GeneratorBatch.oracleProver` [ArkLib/ProofSystem/Component/GeneratorBatch.lean:139](../../../ArkLib/ProofSystem/Component/GeneratorBatch.lean#L139) — The honest prover records the received challenge and computes the output polynomial.
- `def QuotientZeroTest.oracleProver` [ArkLib/ProofSystem/Component/QuotientZeroTest.lean:144](../../../ArkLib/ProofSystem/Component/QuotientZeroTest.lean#L144) — The honest prover sends the computable monic quotient and has no output witness.
- `abbrev RandomEvaluation.oracleProver` [ArkLib/ProofSystem/Component/RandomEvaluation.lean:53](../../../ArkLib/ProofSystem/Component/RandomEvaluation.lean#L53) — The prover retains the context and receives the point.
- `def RandomQuery.oracleProver` [ArkLib/ProofSystem/Component/RandomQuery.lean:71](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L71) — The prover retains the context and receives the query.
- `def ReduceClaim.oracleProver` [ArkLib/ProofSystem/Component/ReduceClaim.lean:241](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L241) — The oracle prover for the `ReduceClaim` oracle reduction.
- `def SendChallenge.oracleProver` [ArkLib/ProofSystem/Component/SendChallenge.lean:58](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L58) — The oracle prover receives the challenge `c` and appends it to the statement (the oracle statements
- `def SendClaim.oracleProver` [ArkLib/ProofSystem/Component/SendClaim.lean:78](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L78) — The oracle prover for `SendClaim`: it computes the claim `f stmt oStmt` and sends it as the only ora
- `def SendWitness.oracleProver` [ArkLib/ProofSystem/Component/SendWitness.lean:173](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L173) — The oracle prover for the `SendWitness` oracle reduction. For each round `i : Fin (FinEnum.card ιw)`
- `def SendSingleWitness.Adapter.oracleProver` [ArkLib/ProofSystem/Component/SendWitness.lean:255](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L255) — Send the encoded witness and materialize the same output as the verifier.
- `def SendSingleWitness.oracleProver` [ArkLib/ProofSystem/Component/SendWitness.lean:397](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L397) — Send the witness unchanged and expose it alongside the input oracles.
- `def Plonk.Batch.oracleProver` [ArkLib/ProofSystem/Plonk/Batch/Reduction.lean:196](../../../ArkLib/ProofSystem/Plonk/Batch/Reduction.lean#L196) — The component prover carries the retained context and tightens its generated batch. The field seed i
- `def Plonk.GrandProduct.oracleProver` [ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean:180](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean#L180) — The honest prover interpolates ratio prefixes, including its total zero-factor fallback.
- `def Plonk.SendWitness.oracleProver` [ArkLib/ProofSystem/Plonk/SendWitness.lean:88](../../../ArkLib/ProofSystem/Plonk/SendWitness.lean#L88) — The honest prover sends its input table unchanged.
- `def Spartan.Batching.oracleProver` [ArkLib/ProofSystem/Spartan/Batching/Reduction.lean:36](../../../ArkLib/ProofSystem/Spartan/Batching/Reduction.lean#L36) — The prover receives the coefficients and computes the same public batched claim.
- `def Spartan.SendEvaluations.oracleProver` [ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean:55](../../../ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean#L55) — The honest prover computes the row evaluations from its retained input tables.
- `def Spartan.FirstSumcheck.oracleProver` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:177](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L177) — The honest prover computes every round message and output target.
- `def Spartan.SecondSumcheck.oracleProver` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:199](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L199) — The honest prover computes every round message and output target.
- `def Spartan.WitnessAttachment.oracleProver` [ArkLib/ProofSystem/Spartan/WitnessAttachment.lean:103](../../../ArkLib/ProofSystem/Spartan/WitnessAttachment.lean#L103) — The honest prover pads its actual witness and sends that table.
- `def Sumcheck.Impl.Computable.oracleProver` [ArkLib/ProofSystem/Sumcheck/Impl/OracleProver.lean:70](../../../ArkLib/ProofSystem/Sumcheck/Impl/OracleProver.lean#L70) — Honest round prover with executable message projection and output evaluation.
- `def ToyProblem.Spec.oracleProver` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:460](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L460) — Same as `prover` but exposed at the `OracleProver` signature. The underlying `Prover` is identical (
- `def ToyProblem.SimplifiedIOR.oracleProver` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:293](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L293) — Honest prover at the oracle-reduction signature.

### `relIn` (20 declarations, 20 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.relIn` [ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean:386](../../../ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean#L386) — **`relIn` — the ordinary input relation of `QuadEval`**: a weak `VerifiedOpening` for `u` under the
- `def CheckClaim.relIn` [ArkLib/ProofSystem/Component/CheckClaim.lean:82](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L82) — (no docstring)
- `def GeneratorBatch.relIn` [ArkLib/ProofSystem/Component/GeneratorBatch.lean:51](../../../ArkLib/ProofSystem/Component/GeneratorBatch.lean#L51) — The input relation requires each polynomial to vanish on the domain.
- `def QuotientZeroTest.relIn` [ArkLib/ProofSystem/Component/QuotientZeroTest.lean:82](../../../ArkLib/ProofSystem/Component/QuotientZeroTest.lean#L82) — The input relation has no private witness beyond the polynomial oracle.
- `abbrev RandomEvaluation.relIn` [ArkLib/ProofSystem/Component/RandomEvaluation.lean:70](../../../ArkLib/ProofSystem/Component/RandomEvaluation.lean#L70) — The input relation: `P = 0`.
- `def RandomQuery.relIn` [ArkLib/ProofSystem/Component/RandomQuery.lean:53](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L53) — The input relation: the two values are equal.
- `def Plonk.Assembly.Circuit.relIn` [ArkLib/ProofSystem/Plonk/Assembly/CircuitExtraction.lean:34](../../../ArkLib/ProofSystem/Plonk/Assembly/CircuitExtraction.lean#L34) — The original circuit relation, retaining its public input and private suffix.
- `def Plonk.Batch.relIn` [ArkLib/ProofSystem/Plonk/Batch/Reduction.lean:57](../../../ArkLib/ProofSystem/Plonk/Batch/Reduction.lean#L57) — The input relation is exactly the grand-product output relation.
- `def Plonk.GrandProduct.relIn` [ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean:73](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean#L73) — The initial claim includes the gate equation and copy constraints.
- `def Plonk.Quotient.relIn` [ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean:44](../../../ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean#L44) — The input is the vanishing claim on the retained batch polynomial.
- `def Plonk.SendWitness.relIn` [ArkLib/ProofSystem/Plonk/SendWitness.lean:48](../../../ArkLib/ProofSystem/Plonk/SendWitness.lean#L48) — The unrevealed table satisfies the gate and copy equations.
- `def RingSwitching.Packing.Head.relIn` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:91](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L91) — The input anchors the scalar claim to this commitment's packed source.
- `abbrev RingSwitching.Packing.TensorPrefix.relIn` [ArkLib/ProofSystem/RingSwitching/Packing/TensorPrefix.lean:67](../../../ArkLib/ProofSystem/RingSwitching/Packing/TensorPrefix.lean#L67) — The scalar relation on the original query and source polynomial.
- `def Spartan.Batching.relIn` [ArkLib/ProofSystem/Spartan/Batching/Reduction.lean:67](../../../ArkLib/ProofSystem/Spartan/Batching/Reduction.lean#L67) — All three input row claims are true.
- `def Spartan.SendEvaluations.relIn` [ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean:74](../../../ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean#L74) — The semantic first sumcheck terminal relation.
- `abbrev Spartan.FirstSumcheck.relIn` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:231](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L231) — The input relation is the zero-check output.
- `def Spartan.SecondSumcheck.relIn` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:233](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L233) — The input relation is the batched second sumcheck claim.
- `def Spartan.Terminal.relIn` [ArkLib/ProofSystem/Spartan/Terminal.lean:85](../../../ArkLib/ProofSystem/Spartan/Terminal.lean#L85) — The terminal input relation.
- `def Spartan.WitnessAttachment.relIn` [ArkLib/ProofSystem/Spartan/WitnessAttachment.lean:132](../../../ArkLib/ProofSystem/Spartan/WitnessAttachment.lean#L132) — The input relation is satisfiability by the original, unpadded witness.
- `def Spartan.ZeroCheck.relIn` [ArkLib/ProofSystem/Spartan/ZeroCheck/Relation.lean:41](../../../ArkLib/ProofSystem/Spartan/ZeroCheck/Relation.lean#L41) — The R1CS relation after witness attachment has a unique private witness.

### `rbrExtractor` (19 declarations, 19 files)

- `def GeneratorBatch.rbrExtractor` [ArkLib/ProofSystem/Component/GeneratorBatch.lean:155](../../../ArkLib/ProofSystem/Component/GeneratorBatch.lean#L155) — Extraction retains the unique witness; the oracle family is fixed in the statement.
- `def QuotientZeroTest.rbrExtractor` [ArkLib/ProofSystem/Component/QuotientZeroTest.lean:164](../../../ArkLib/ProofSystem/Component/QuotientZeroTest.lean#L164) — Each backward extraction step returns the unique input witness.
- `abbrev RandomEvaluation.rbrExtractor` [ArkLib/ProofSystem/Component/RandomEvaluation.lean:65](../../../ArkLib/ProofSystem/Component/RandomEvaluation.lean#L65) — The round-by-round extractor retains the unique witness.
- `def RandomQuery.rbrExtractor` [ArkLib/ProofSystem/Component/RandomQuery.lean:120](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L120) — The round-by-round extractor retains the unique witness.
- `def SendSingleWitness.Adapter.rbrExtractor` [ArkLib/ProofSystem/Component/SendWitness.lean:308](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L308) — Read the message from the transcript and decode only at the input boundary.
- `def Plonk.Assembly.Circuit.rbrExtractor` [ArkLib/ProofSystem/Plonk/Assembly/CircuitExtraction.lean:46](../../../ArkLib/ProofSystem/Plonk/Assembly/CircuitExtraction.lean#L46) — Composed backward extraction followed by the computable circuit decoder.
- `def Plonk.Assembly.rbrExtractor` [ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean:176](../../../ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean#L176) — The designated backward composition of the four stage extractors.
- `def Plonk.Batch.rbrExtractor` [ArkLib/ProofSystem/Plonk/Batch/Reduction.lean:222](../../../ArkLib/ProofSystem/Plonk/Batch/Reduction.lean#L222) — The component extractor acts on the projected residual family.
- `def Plonk.GrandProduct.rbrExtractor` [ArkLib/ProofSystem/Plonk/GrandProduct/Security.lean:33](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Security.lean#L33) — All witnesses are unique after the initial wire oracles have been revealed.
- `def Plonk.Quotient.rbrExtractor` [ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean:162](../../../ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean#L162) — The named extractor is the transported generic zero-test extractor.
- `def Plonk.SendWitness.rbrExtractor` [ArkLib/ProofSystem/Plonk/SendWitness.lean:104](../../../ArkLib/ProofSystem/Plonk/SendWitness.lean#L104) — Backward extraction reads the actual table message.
- `def Spartan.Batching.rbrExtractor` [ArkLib/ProofSystem/Spartan/Batching/Reduction.lean:93](../../../ArkLib/ProofSystem/Spartan/Batching/Reduction.lean#L93) — The backward extractor retains the unique witness.
- `def Spartan.rbrExtractor` [ArkLib/ProofSystem/Spartan/Security.lean:108](../../../ArkLib/ProofSystem/Spartan/Security.lean#L108) — The composed backward extractor. Noncomputability is confined to the semantic guards and chosen sumc
- `def Spartan.FirstSumcheck.rbrExtractor` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:376](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L376) — The chosen inner extractor lifted through the explicit virtual-polynomial lens. Its only noncomputab
- `def Spartan.SecondSumcheck.rbrExtractor` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:379](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L379) — The chosen inner extractor lifted through the explicit virtual-polynomial lens. Its only noncomputab
- `def Spartan.WitnessAttachment.rbrExtractor` [ArkLib/ProofSystem/Spartan/WitnessAttachment.lean:156](../../../ArkLib/ProofSystem/Spartan/WitnessAttachment.lean#L156) — Extraction reads the sent padded table and restricts it to the original coordinates.
- `abbrev Spartan.ZeroCheck.rbrExtractor` [ArkLib/ProofSystem/Spartan/ZeroCheck/Reduction.lean:44](../../../ArkLib/ProofSystem/Spartan/ZeroCheck/Reduction.lean#L44) — The backward extractor preserves the unique witness.
- `def ToyProblem.Impl.IRS.rbrExtractor` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:358](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L358) — Named executable round-by-round extractor for interleaved RS.
- `def ToyProblem.Spec.rbrExtractor` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:1202](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L1202) — The round-by-round extractor: round 0 extracts a relaxed-relation witness by choice, round 1 passes

### `relOut` (18 declarations, 18 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.relOut` [ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean:262](../../../ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean#L262) — **`relOut` — Hachi Eq. (20) (rows c1–c5 verbatim) plus a symmetric-`ℓ∞`-ball model of the `S_b` rang
- `def CheckClaim.relOut` [ArkLib/ProofSystem/Component/CheckClaim.lean:85](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L85) — (no docstring)
- `def GeneratorBatch.relOut` [ArkLib/ProofSystem/Component/GeneratorBatch.lean:55](../../../ArkLib/ProofSystem/Component/GeneratorBatch.lean#L55) — The output relation is the quotient zero test's relation on the batched oracle.
- `def QuotientZeroTest.relOut` [ArkLib/ProofSystem/Component/QuotientZeroTest.lean:86](../../../ArkLib/ProofSystem/Component/QuotientZeroTest.lean#L86) — All returned outputs are accepting; a failed equation aborts the verifier.
- `abbrev RandomEvaluation.relOut` [ArkLib/ProofSystem/Component/RandomEvaluation.lean:73](../../../ArkLib/ProofSystem/Component/RandomEvaluation.lean#L73) — The output relation: `P` vanishes at the sampled point.
- `def RandomQuery.relOut` [ArkLib/ProofSystem/Component/RandomQuery.lean:57](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L57) — The output relation: the two values give the same answer at the sampled query.
- `def Plonk.Batch.relOut` [ArkLib/ProofSystem/Plonk/Batch/Reduction.lean:60](../../../ArkLib/ProofSystem/Plonk/Batch/Reduction.lean#L60) — The output batch vanishes on the row domain.
- `def Plonk.GrandProduct.relOut` [ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean:77](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean#L77) — All three virtual residuals vanish on the row domain.
- `def Plonk.Quotient.relOut` [ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean:47](../../../ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean#L47) — An accepted output retains all earlier oracles, without further obligations.
- `def RingSwitching.Lift.relOut` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:134](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L134) — The anchored output relation of the switch, from the committed-scalar shell: commitment consistency,
- `abbrev RingSwitching.Packing.Head.relOut` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:103](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L103) — The output is the initial sumcheck relation on the same committed polynomial.
- `def Spartan.Batching.relOut` [ArkLib/ProofSystem/Spartan/Batching/Reduction.lean:72](../../../ArkLib/ProofSystem/Spartan/Batching/Reduction.lean#L72) — The second sumcheck's initial claim holds for the retained original tables.
- `def Spartan.SendEvaluations.relOut` [ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean:79](../../../ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean#L79) — The three claims refer to the same original oracle tables.
- `abbrev Spartan.FirstSumcheck.relOut` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:234](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L234) — The output relation is the first virtual polynomial's terminal evaluation.
- `def Spartan.SecondSumcheck.relOut` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:236](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L236) — The output relation is the terminal second-polynomial evaluation equation.
- `def Spartan.Terminal.relOut` [ArkLib/ProofSystem/Spartan/Terminal.lean:90](../../../ArkLib/ProofSystem/Spartan/Terminal.lean#L90) — The terminal output relation imposes no further check.
- `abbrev Spartan.WitnessAttachment.relOut` [ArkLib/ProofSystem/Spartan/WitnessAttachment.lean:136](../../../ArkLib/ProofSystem/Spartan/WitnessAttachment.lean#L136) — The output relation is exactly the next zero-check stage's input relation.
- `def Spartan.ZeroCheck.relOut` [ArkLib/ProofSystem/Spartan/ZeroCheck/Relation.lean:46](../../../ArkLib/ProofSystem/Spartan/ZeroCheck/Relation.lean#L46) — The first challenge establishes the initial zero-valued sumcheck claim.

### `prover` (16 declarations, 15 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.prover` [ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean:458](../../../ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean#L458) — The honest prover (Hachi §4.2, Figure 3; completeness is out of scope for Lemma 8): round 0 sends th
- `def CoordinateWise.CommittedScalar.prover` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:147](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L147) — Honest prover shell for a committed scalar phase. The commitment is derived from `computeW`; the API
- `def CheckClaim.prover` [ArkLib/ProofSystem/Component/CheckClaim.lean:57](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L57) — The prover for the `CheckClaim` reduction.
- `def DoNothing.prover` [ArkLib/ProofSystem/Component/DoNothing.lean:33](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L33) — The prover for the `DoNothing` reduction.
- `def NoInteraction.prover` [ArkLib/ProofSystem/Component/NoInteraction.lean:46](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L46) — The prover in a no-interaction reduction can be specified by a tuple of functions: - `mapStmt : Stmt
- `def ReduceClaim.prover` [ArkLib/ProofSystem/Component/ReduceClaim.lean:50](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L50) — The prover for the `ReduceClaim` reduction.
- `def SendWitness.prover` [ArkLib/ProofSystem/Component/SendWitness.lean:73](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L73) — (no docstring)
- `def RingSwitching.Lift.prover` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:148](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L148) — Honest prover shell. Its commitment is definitionally derived from the output opening.
- `def RingSwitching.Packing.Head.prover` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:160](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L160) — Send component values while retaining the same packed polynomial and oracle collection.
- `def RingSwitching.Packing.ProductSumcheck.Round.prover` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean:79](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean#L79) — Send the exact product-sum polynomial while retaining the packed witness and oracles.
- `def RingSwitching.Packing.ProductSumcheck.Terminal.prover` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean:61](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean#L61) — Send the packed evaluation with unchanged oracle values.
- `def Sumcheck.Interaction.SingleRound.prover` [ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:88](../../../ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean#L88) — An honest prover sends its input polynomial and retains the evaluated output statement.
- `def Sumcheck.Spec.SingleRound.Simple.prover` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:223](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L223) — The prover in the simple description of a single round of sum-check. Takes in input `target : R` and
- `def Sumcheck.Spec.SingleRound.Unfolded.prover` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1240](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1240) — The overall prover for the `i`-th round of the sum-check protocol, where `i < n`. This is only well-
- `def ToyProblem.Spec.prover` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:358](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L358) — Honest prover for the toy protocol. After receiving the combination randomness `γ`, the prover sends
- `def ToyProblem.SimplifiedIOR.prover` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:186](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L186) — Honest prover for the simplified IOR. After receiving `γ`, sets the new witness `M_new := M₀ + γ·M₁`

### `perfectCompleteness` (16 declarations, 13 files)

- `def Reduction.perfectCompleteness` [ArkLib/OracleReduction/Security/Basic.lean:101](../../../ArkLib/OracleReduction/Security/Basic.lean#L101) — A reduction satisfies **perfect completeness** if it satisfies completeness with error `0`.
- `def OracleReduction.perfectCompleteness` [ArkLib/OracleReduction/Security/Basic.lean:455](../../../ArkLib/OracleReduction/Security/Basic.lean#L455) — Perfect completeness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.perfectCompleteness` [ArkLib/OracleReduction/Security/Basic.lean:538](../../../ArkLib/OracleReduction/Security/Basic.lean#L538) — (no docstring)
- `def OracleProof.perfectCompleteness` [ArkLib/OracleReduction/Security/Basic.lean:571](../../../ArkLib/OracleReduction/Security/Basic.lean#L571) — Perfect completeness of an oracle reduction is the same as for non-oracle reductions.
- `theorem SendSingleWitness.Adapter.perfectCompleteness` [ArkLib/ProofSystem/Component/SendWitness.lean:342](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L342) — Honest relation transfer gives perfect completeness of the actual one-message run.
- `theorem RingSwitching.Packing.Head.perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:273](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L273) — Perfect completeness at every initial oracle state, for every challenge sampled by the phase.
- `theorem RingSwitching.Packing.OpeningAdapter.perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/Packing/OpeningAdapter.lean:131](../../../ArkLib/ProofSystem/RingSwitching/Packing/OpeningAdapter.lean#L131) — A complete general opening yields a complete contextual opening.
- `theorem RingSwitching.Packing.ProductSumcheck.Round.perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/RoundExecution.lean:86](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/RoundExecution.lean#L86) — Every challenge preserves completeness over a commutative ring, at every oracle state.
- `theorem RingSwitching.Packing.ProductSumcheck.perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/SeqCompose.lean:133](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/SeqCompose.lean#L133) — Perfect completeness of the complete tail on the same commitment opening relation.
- `theorem RingSwitching.Packing.ProductSumcheck.Terminal.perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean:171](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean#L171) — Perfect completeness for arbitrary initial state distributions, over commutative rings.
- `theorem RingSwitching.Packing.RingSwitch.perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/Packing/RingSwitch.lean:127](../../../ArkLib/ProofSystem/RingSwitching/Packing/RingSwitch.lean#L127) — Perfect completeness for a challenge-algebra evaluation on the same commitment, from every initial s
- `theorem RingSwitching.Packing.TensorPrefix.perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/Packing/TensorPrefix.lean:92](../../../ArkLib/ProofSystem/RingSwitching/Packing/TensorPrefix.lean#L92) — Every valid initial claim completes on the same commitment, at every oracle state.
- `theorem Spartan.perfectCompleteness` [ArkLib/ProofSystem/Spartan/Protocol.lean:182](../../../ArkLib/ProofSystem/Spartan/Protocol.lean#L182) — The actual honest prover is perfectly complete for the original R1CS relation.
- `theorem Spartan.FirstSumcheck.perfectCompleteness` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:325](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L325) — The honest first sumcheck is perfectly complete for the zero-check claim and first terminal evaluati
- `theorem Spartan.SecondSumcheck.perfectCompleteness` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:327](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L327) — The honest second sumcheck is perfectly complete for the retained batch and terminal claim.
- `theorem Spartan.WitnessAttachment.perfectCompleteness` [ArkLib/ProofSystem/Spartan/WitnessAttachment.lean:200](../../../ArkLib/ProofSystem/Spartan/WitnessAttachment.lean#L200) — Honest witness padding and attachment establish the zero-check input relation.

### `oracleVerifier_rbrKnowledgeSoundness` (13 declarations, 12 files)

- `theorem DoNothing.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/DoNothing.lean:109](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L109) — The `DoNothing` oracle verifier is perfectly round-by-round knowledge sound.
- `theorem GeneratorBatch.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/GeneratorBatch.lean:238](../../../ArkLib/ProofSystem/Component/GeneratorBatch.lean#L238) — Existential form of the named fixed-prefix knowledge certificate.
- `theorem QuotientZeroTest.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/QuotientZeroTest.lean:256](../../../ArkLib/ProofSystem/Component/QuotientZeroTest.lean#L256) — Existential form of the named fixed-prefix knowledge certificate.
- `theorem RandomEvaluation.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/RandomEvaluation.lean:144](../../../ArkLib/ProofSystem/Component/RandomEvaluation.lean#L144) — Fixed-prefix round-by-round knowledge soundness, with error `d / \|F\|`.
- `theorem RandomQuery.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/RandomQuery.lean:215](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L215) — Fixed-prefix round-by-round knowledge soundness with error `ε`.
- `theorem ReduceClaim.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:359](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L359) — The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness. Note that s
- `theorem Plonk.Batch.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Plonk/Batch/Reduction.lean:306](../../../ArkLib/ProofSystem/Plonk/Batch/Reduction.lean#L306) — Existential packaging of the named fixed-prefix certificate.
- `theorem Plonk.GrandProduct.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Plonk/GrandProduct/Security.lean:100](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Security.lean#L100) — Existential packaging of the named fixed-prefix certificate.
- `theorem Sumcheck.Spec.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:513](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L513) — Knowledge soundness with error `deg / \|R\|` at every challenge.
- `theorem Sumcheck.Spec.SingleRound.Simple.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:583](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L583) — Round-by-round knowledge soundness for the oracle verifier.
- `theorem Sumcheck.Spec.SingleRound.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1180](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1180) — Round-by-round knowledge soundness for the lifted oracle verifier.
- `theorem ToyProblem.Impl.IRS.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:933](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L933) — Existential RBR knowledge soundness, retained as a compatibility corollary of the exact-object theor
- `theorem ToyProblem.Spec.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:1364](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L1364) — Round-by-round knowledge soundness of the toy protocol in the alphabet-generic classical-extractor f

### `Statement` (11 declarations, 10 files)

- `structure ArkLib.Lattices.Hachi.TraceHead.Statement` [ArkLib/Commitments/Functional/Hachi/TraceHead/Protocol.lean:49](../../../ArkLib/Commitments/Functional/Hachi/TraceHead/Protocol.lean#L49) — A scalar query with retained variables split into low/high blocks, followed by the packed suffix.
- `abbrev CoordinateWise.CommittedScalar.Statement` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:125](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L125) — Output statement of a committed scalar phase: input statement, commitment, challenge.
- `def R1CS.Statement` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:49](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L49) — (no docstring)
- `def Fri.Spec.Statement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:71](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L71) — The folding challenges received before stage `i`.
- `structure RingSwitching.Packing.ProductSumcheck.Statement` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Basic.lean:62](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Basic.lean#L62) — Public context, previously sampled coordinates, and the remaining cube sum claim.
- `structure Spartan.Evaluation.Statement` [ArkLib/ProofSystem/Spartan/Context.lean:26](../../../ArkLib/ProofSystem/Spartan/Context.lean#L26) — The first sumcheck's terminal claim and retained public input.
- `structure Spartan.Batching.Statement` [ArkLib/ProofSystem/Spartan/Context.lean:40](../../../ArkLib/ProofSystem/Spartan/Context.lean#L40) — The independent coefficients, claimed sum, and retained row claims.
- `abbrev Spartan.Assembly.Statement` [ArkLib/ProofSystem/Spartan/Protocol.lean:40](../../../ArkLib/ProofSystem/Spartan/Protocol.lean#L40) — The public context at each boundary of the seven stages.
- `abbrev Spartan.FirstSumcheck.Statement` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:32](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L32) — The retained zero-check challenge and original public input.
- `structure Sumcheck.Structured.Statement` [ArkLib/ProofSystem/Sumcheck/Structured.lean:157](../../../ArkLib/ProofSystem/Sumcheck/Structured.lean#L157) — Statement per iterated sumcheck round
- `def ToyProblem.Spec.Statement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:175](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L175) — Input (explicit) statement of the toy protocol: the linear-constraint vector `v ∈ F^k` and the two c

### `oracleVerifier_rbrKnowledgeSoundnessWith` (10 declarations, 10 files)

- `theorem GeneratorBatch.oracleVerifier_rbrKnowledgeSoundnessWith` [ArkLib/ProofSystem/Component/GeneratorBatch.lean:225](../../../ArkLib/ProofSystem/Component/GeneratorBatch.lean#L225) — A zero-evading generator hides each fixed false family with probability at most `ε`.
- `theorem QuotientZeroTest.oracleVerifier_rbrKnowledgeSoundnessWith` [ArkLib/ProofSystem/Component/QuotientZeroTest.lean:228](../../../ArkLib/ProofSystem/Component/QuotientZeroTest.lean#L228) — At every fixed prefix, a false domain-vanishing claim passes with probability at most `d / \|F\|`. The
- `theorem RandomEvaluation.oracleVerifier_rbrKnowledgeSoundnessWith` [ArkLib/ProofSystem/Component/RandomEvaluation.lean:132](../../../ArkLib/ProofSystem/Component/RandomEvaluation.lean#L132) — Fixed-prefix knowledge soundness, with error `d / \|F\|` when every polynomial has total degree at mos
- `theorem RandomQuery.oracleVerifier_rbrKnowledgeSoundnessWith` [ArkLib/ProofSystem/Component/RandomQuery.lean:186](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L186) — Fixed-prefix knowledge soundness for the named extractor and knowledge state, with error `ε` when ev
- `theorem Plonk.Assembly.Circuit.oracleVerifier_rbrKnowledgeSoundnessWith` [ArkLib/ProofSystem/Plonk/Assembly/CircuitExtraction.lean:74](../../../ArkLib/ProofSystem/Plonk/Assembly/CircuitExtraction.lean#L74) — The circuit decoder preserves the composed named fixed-prefix certificate.
- `theorem Plonk.Assembly.oracleVerifier_rbrKnowledgeSoundnessWith` [ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean:216](../../../ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean#L216) — Named fixed-prefix knowledge security of the entire oracle reduction.
- `theorem Plonk.Batch.oracleVerifier_rbrKnowledgeSoundnessWith` [ArkLib/ProofSystem/Plonk/Batch/Reduction.lean:287](../../../ArkLib/ProofSystem/Plonk/Batch/Reduction.lean#L287) — Every fixed false residual family survives the uniform batch challenge with probability at most `2 /
- `theorem Plonk.GrandProduct.oracleVerifier_rbrKnowledgeSoundnessWith` [ArkLib/ProofSystem/Plonk/GrandProduct/Security.lean:69](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Security.lean#L69) — A single joint uniform challenge hides a false copy claim with probability at most `(3n - 1) / \|F\|`,
- `theorem Plonk.Quotient.oracleVerifier_rbrKnowledgeSoundnessWith` [ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean:182](../../../ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean#L182) — The quotient/evaluation/terminal stage has exactly `4(n - 1) / \|F\|` fixed-prefix error.
- `theorem Plonk.SendWitness.oracleVerifier_rbrKnowledgeSoundnessWith` [ArkLib/ProofSystem/Plonk/SendWitness.lean:129](../../../ArkLib/ProofSystem/Plonk/SendWitness.lean#L129) — The reveal has zero fixed-prefix knowledge error.

### `outputRelation` (12 declarations, 9 files)

- `def BatchedFri.Spec.BatchingRound.outputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:103](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L103) — The batching output relation is exactly the initial FRI relation at the same radius.
- `def Fri.Spec.outputRelation` [ArkLib/ProofSystem/Fri/Spec/General.lean:48](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L48) — The final polynomial's evaluations are within distance `δ` of the final witness.
- `def Fri.Spec.FoldPhase.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:233](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L233) — The latest oracle word after non-final folding round `i` is within relative Hamming distance `δ` of
- `def Fri.Spec.FinalFoldPhase.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:429](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L429) — Proximity of the transmitted final polynomial's evaluations to the final witness. The witness type e
- `def Fri.Spec.QueryRound.outputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:667](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L667) — (no docstring)
- `def Spartan.Batching.outputRelation` [ArkLib/ProofSystem/Spartan/Batching/Relation.lean:43](../../../ArkLib/ProofSystem/Spartan/Batching/Relation.lean#L43) — The second virtual polynomial's Boolean sum equals the public claimed sum.
- `def Spartan.Evaluation.outputRelation` [ArkLib/ProofSystem/Spartan/Evaluation/Relation.lean:44](../../../ArkLib/ProofSystem/Spartan/Evaluation/Relation.lean#L44) — Each sent value is the evaluation of its original row-product polynomial.
- `def Spartan.ZeroCheck.outputRelation` [ArkLib/ProofSystem/Spartan/ZeroCheck/Relation.lean:36](../../../ArkLib/ProofSystem/Spartan/ZeroCheck/Relation.lean#L36) — The residual interpolation vanishes at the retained challenge.
- `abbrev Sumcheck.Interaction.Computable.outputRelation` [ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean:31](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean#L31) — Truth compares the exported original behavior with the final claimed evaluation.
- `def Sumcheck.Interaction.Native.Core.outputRelation` [ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:137](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean#L137) — Truth at the final leaf is evaluation of the retained original behavior at the full prefix.
- `def Sumcheck.Interaction.Native.outputRelation` [ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:354](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean#L354) — Truth of the exported original-oracle evaluation claim.
- `def Sumcheck.Spec.SingleRound.Simple.outputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:211](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L211) — (no docstring)

### `oracleReduction_perfectCompleteness` (11 declarations, 9 files)

- `theorem DoNothing.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Component/DoNothing.lean:103](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L103) — The `DoNothing` oracle reduction satisfies perfect completeness for any relation.
- `theorem GeneratorBatch.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Component/GeneratorBatch.lean:177](../../../ArkLib/ProofSystem/Component/GeneratorBatch.lean#L177) — Perfect completeness for every ambient oracle implementation and initial state.
- `theorem QuotientZeroTest.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Component/QuotientZeroTest.lean:198](../../../ArkLib/ProofSystem/Component/QuotientZeroTest.lean#L198) — Perfect completeness for every ambient oracle implementation and initial state.
- `theorem Plonk.Batch.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Plonk/Batch/Reduction.lean:260](../../../ArkLib/ProofSystem/Plonk/Batch/Reduction.lean#L260) — Batching inherits perfect completeness from the component's honest run.
- `theorem Plonk.Quotient.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean:154](../../../ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean#L154) — Completeness of the actual lifted quotient prover and terminal guard.
- `theorem Plonk.SendWitness.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Plonk/SendWitness.lean:137](../../../ArkLib/ProofSystem/Plonk/SendWitness.lean#L137) — The actual honest reveal run preserves the input relation with probability one.
- `theorem Sumcheck.Spec.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:495](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L495) — Perfect completeness of the full oracle sum-check protocol.
- `theorem Sumcheck.Spec.SingleRound.Simple.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:489](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L489) — Perfect completeness for the oracle reduction
- `theorem Sumcheck.Spec.SingleRound.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1161](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1161) — Completeness theorem for single-round of sum-check, obtained by transporting the completeness proof
- `theorem ToyProblem.Spec.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/ToyProblem/Spec/Completeness.lean:117](../../../ArkLib/ProofSystem/ToyProblem/Spec/Completeness.lean#L117) — **Honest completeness of the three-round toy protocol** (protocol-level form). The honest oracle red
- `theorem ToyProblem.SimplifiedIOR.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/ToyProblem/Spec/Completeness.lean:332](../../../ArkLib/ProofSystem/ToyProblem/Spec/Completeness.lean#L332) — **Perfect completeness of the simplified IOR** (protocol-level form). For every verifier challenge,

### `rbrKnowledgeSoundnessWith` (10 declarations, 9 files)

- `def Verifier.rbrKnowledgeSoundnessWith` [ArkLib/OracleReduction/Security/RoundByRound.lean:509](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L509) — `rbrKnowledgeSoundness` for one exact intermediate-witness family, extractor, and knowledge state fu
- `def OracleVerifier.rbrKnowledgeSoundnessWith` [ArkLib/OracleReduction/Security/RoundByRound.lean:615](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L615) — Extractor-specific round-by-round knowledge soundness (`Verifier.rbrKnowledgeSoundnessWith`) of an o
- `theorem SendSingleWitness.Adapter.rbrKnowledgeSoundnessWith` [ArkLib/ProofSystem/Component/SendWitness.lean:333](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L333) — With no verifier challenges, the fixed-prefix knowledge error is zero.
- `theorem RingSwitching.Packing.Head.rbrKnowledgeSoundnessWith` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:470](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L470) — Functional compatibility implies round-by-round knowledge soundness for the concrete extractor and k
- `theorem RingSwitching.Packing.ProductSumcheck.Round.rbrKnowledgeSoundnessWith` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/RoundSecurity.lean:109](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/RoundSecurity.lean#L109) — Round-by-round knowledge soundness at every fixed transcript prefix, with the round extractor.
- `theorem RingSwitching.Packing.ProductSumcheck.Terminal.rbrKnowledgeSoundnessWith` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean:231](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean#L231) — Exact round-by-round knowledge soundness with no challenge error, including when m is zero.
- `theorem Spartan.rbrKnowledgeSoundnessWith` [ArkLib/ProofSystem/Spartan/Security.lean:179](../../../ArkLib/ProofSystem/Spartan/Security.lean#L179) — The seven-stage verifier has a named fixed-prefix knowledge certificate for the original R1CS relati
- `theorem Spartan.FirstSumcheck.rbrKnowledgeSoundnessWith` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:397](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L397) — Fixed-prefix knowledge soundness for the named lifted certificate, with error `3 / \|R\|` per challeng
- `theorem Spartan.SecondSumcheck.rbrKnowledgeSoundnessWith` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:407](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L407) — Fixed-prefix knowledge soundness for the named lifted certificate, with error `2 / \|R\|` per challeng
- `theorem Spartan.WitnessAttachment.rbrKnowledgeSoundnessWith` [ArkLib/ProofSystem/Spartan/WitnessAttachment.lean:192](../../../ArkLib/ProofSystem/Spartan/WitnessAttachment.lean#L192) — The named transcript-reading extractor has zero fixed-prefix knowledge error.

### `inputRelation` (10 declarations, 8 files)

- `abbrev BatchedFri.Spec.inputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/General.lean:60](../../../ArkLib/ProofSystem/BatchedFri/Spec/General.lean#L60) — The composite protocol starts with the batching round's correlated-agreement relation.
- `def BatchedFri.Spec.BatchingRound.inputRelation` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:96](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L96) — The words agree with their degree-bounded polynomial witnesses on one common set of relative size at
- `def Binius.BinaryBasefold.Opening.inputRelation` [ArkLib/ProofSystem/Binius/BinaryBasefold/Opening.lean:97](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Opening.lean#L97) — Evaluation and unique-radius compatibility with the supplied first oracle.
- `def Fri.Spec.inputRelation` [ArkLib/ProofSystem/Fri/Spec/General.lean:40](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L40) — The initial word is within relative Hamming distance `δ` of its polynomial witness.
- `def Fri.Spec.FoldPhase.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:223](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L223) — The latest oracle word before non-final folding round `i` is within relative Hamming distance `δ` of
- `def Fri.Spec.FinalFoldPhase.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:415](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L415) — Proximity of the last oracle word to the polynomial witness before the final fold.
- `def Fri.Spec.QueryRound.inputRelation` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:660](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L660) — (no docstring)
- `def Spartan.Evaluation.inputRelation` [ArkLib/ProofSystem/Spartan/Evaluation/Relation.lean:31](../../../ArkLib/ProofSystem/Spartan/Evaluation/Relation.lean#L31) — The first virtual polynomial has the claimed terminal value.
- `def Spartan.ZeroCheck.inputRelation` [ArkLib/ProofSystem/Spartan/ZeroCheck/Relation.lean:31](../../../ArkLib/ProofSystem/Spartan/ZeroCheck/Relation.lean#L31) — The public input and attached witness satisfy the retained R1CS matrices.
- `def Sumcheck.Spec.SingleRound.Simple.inputRelation` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:208](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L208) — (no docstring)

### `OracleStatement` (8 declarations, 8 files)

- `def BatchedFri.Spec.OracleStatement` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:52](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L52) — An oracle for each batched polynomial.
- `def Binius.BinaryBasefold.OracleStatement` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:72](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L72) — The committed codeword oracles available at state `i`, indexed by their frontier positions.
- `def R1CS.OracleStatement` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:52](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L52) — (no docstring)
- `def Fri.Spec.OracleStatement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:79](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L79) — The initial word and the `i` subsequent committed words, each on its folding domain.
- `def Spartan.Realization.OracleStatement` [ArkLib/ProofSystem/Spartan/Algebra/Realization.lean:110](../../../ArkLib/ProofSystem/Spartan/Algebra/Realization.lean#L110) — The retained matrix and witness table family.
- `def StirIOP.OracleStatement` [ArkLib/ProofSystem/Stir/MainThm.lean:140](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L140) — `OracleStatement` defines the oracle message type for a multi-indexed setting: given base input type
- `def Sumcheck.Spec.OracleStatement` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:142](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L142) — Oracle statement for sum-check, which is a multivariate polynomial over `n` variables of individual
- `def ToyProblem.Spec.OracleStatement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:181](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L181) — Oracle statements of the toy protocol: the two purported codewords `f₁, f₂ : ι → A`. The verifier on

### `rbrKnowledgeSoundness` (10 declarations, 7 files)

- `def Verifier.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:487](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L487) — **Round-by-round knowledge soundness** with respect to input relation `relIn`, output relation `relO
- `def OracleVerifier.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:605](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L605) — Round-by-round knowledge soundness (`Verifier.rbrKnowledgeSoundness`) of an oracle verifier: that of
- `def Proof.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:649](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L649) — Round-by-round knowledge soundness (`Verifier.rbrKnowledgeSoundness`) of a proof: the output relatio
- `def OracleProof.rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:682](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L682) — Round-by-round knowledge soundness (`Verifier.rbrKnowledgeSoundness`) of an oracle proof: that of it
- `theorem RingSwitching.Packing.OpeningAdapter.rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/Packing/OpeningAdapter.lean:147](../../../ArkLib/ProofSystem/RingSwitching/Packing/OpeningAdapter.lean#L147) — Security of a general opening transports to its contextual adapter.
- `theorem RingSwitching.Packing.ProductSumcheck.rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Knowledge.lean:72](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Knowledge.lean#L72) — Round-by-round knowledge soundness on the original commitment opening.
- `theorem RingSwitching.Packing.RingSwitch.rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/Packing/RingSwitch.lean:171](../../../ArkLib/ProofSystem/RingSwitching/Packing/RingSwitch.lean#L171) — The concrete reduction is round-by-round knowledge sound on the original opening.
- `theorem RingSwitching.Packing.TensorPrefix.rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/Packing/TensorPrefix.lean:236](../../../ArkLib/ProofSystem/RingSwitching/Packing/TensorPrefix.lean#L236) — The verifier inherits the shared round-by-round security proof.
- `theorem Spartan.FirstSumcheck.rbrKnowledgeSoundness` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:412](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L412) — The first virtual sumcheck has fixed-prefix knowledge error `3 / \|R\|` per challenge.
- `theorem Spartan.SecondSumcheck.rbrKnowledgeSoundness` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:422](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L422) — The second virtual sumcheck has fixed-prefix knowledge error `2 / \|R\|` per challenge.

### `append` (8 declarations, 7 files)

- `def Interaction.Oracle.Security.RoundExtractor.append` [ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean:33](../../../ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean#L33) — Join two extractors along the actual first path, keeping its terminal knowledge state as the suffix
- `def Interaction.Oracle.Security.KnowledgeCertificate.append` [ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean:342](../../../ArkLib/Interaction/Oracle/Security/KnowledgeComposition.lean#L342) — Compose certificates along a suffix whose root is the actual first terminal state.
- `abbrev ProtocolSpec.append` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:39](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L39) — Appending two `ProtocolSpec`s
- `def ProtocolSpec.FullTranscript.append` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:171](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L171) — Appending two transcripts for two `ProtocolSpec`s
- `def CWSSStructure.append` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Composition.lean:77](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Composition.lean#L77) — Binary append of coordinate-wise special-soundness structures. On left challenge rounds this is `D₁`
- `def CoordinateWise.GCWSSPackage.append` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Guarded.lean:513](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Guarded.lean#L513) — **Compose two guarded packages along a matching seam** — the guarded canonical `▷`. The seam verdict
- `def CoordinateWise.CWSSPackage.append` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Package.lean:105](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Package.lean#L105) — **Compose two packages along a matching seam** — the `▷` of pure packages. Every composed field is *
- `def ProtocolSpec.ChallengeTreeShape.append` [ArkLib/OracleReduction/Security/TranscriptTree/Composition.lean:117](../../../ArkLib/OracleReduction/Security/TranscriptTree/Composition.lean#L117) — Append two protocol-generic tree shapes along sequential protocol append.

### `oracleReduction_completeness` (7 declarations, 7 files)

- `theorem CheckClaim.oracleReduction_completeness` [ArkLib/ProofSystem/Component/CheckClaim.lean:259](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L259) — **Perfect completeness of the pure pass-through `CheckClaim` oracle reduction.** Because the verifie
- `theorem RandomEvaluation.oracleReduction_completeness` [ArkLib/ProofSystem/Component/RandomEvaluation.lean:89](../../../ArkLib/ProofSystem/Component/RandomEvaluation.lean#L89) — Perfect completeness: the zero polynomial vanishes everywhere.
- `theorem RandomQuery.oracleReduction_completeness` [ArkLib/ProofSystem/Component/RandomQuery.lean:134](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L134) — The random-query reduction is perfectly complete: equal values agree at every query.
- `theorem ReduceClaim.oracleReduction_completeness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:282](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L282) — The `ReduceClaim` oracle reduction satisfies perfect completeness for any relation. Proof strategy m
- `theorem SendSingleWitness.oracleReduction_completeness` [ArkLib/ProofSystem/Component/SendWitness.lean:494](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L494) — The `SendSingleWitness` oracle reduction satisfies perfect completeness.
- `theorem Plonk.Assembly.oracleReduction_completeness` [ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean:243](../../../ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean#L243) — The composed honest prover is complete with failure at most `3n / \|F\|`.
- `theorem Plonk.GrandProduct.oracleReduction_completeness` [ArkLib/ProofSystem/Plonk/GrandProduct/Completeness.lean:83](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Completeness.lean#L83) — The honest Plonk permutation grand product reduction is complete with error at most `3n / \|F\|`, for

### `oracleVerifier_toVerifier` (7 declarations, 7 files)

- `theorem GeneratorBatch.oracleVerifier_toVerifier` [ArkLib/ProofSystem/Component/GeneratorBatch.lean:124](../../../ArkLib/ProofSystem/Component/GeneratorBatch.lean#L124) — Materialization returns exactly the computable batch at the transcript challenge.
- `theorem QuotientZeroTest.oracleVerifier_toVerifier` [ArkLib/ProofSystem/Component/QuotientZeroTest.lean:112](../../../ArkLib/ProofSystem/Component/QuotientZeroTest.lean#L112) — Materialization performs exactly the pure check, with failure when the equation is false.
- `theorem Plonk.Assembly.oracleVerifier_toVerifier` [ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean:136](../../../ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean#L136) — Materialization of the composed verifier is exactly the scalar quotient identity.
- `theorem Plonk.Batch.oracleVerifier_toVerifier` [ArkLib/ProofSystem/Plonk/Batch/Reduction.lean:179](../../../ArkLib/ProofSystem/Plonk/Batch/Reduction.lean#L179) — Materialization gives the retained context with the challenge-weighted batch.
- `theorem Plonk.GrandProduct.oracleVerifier_toVerifier` [ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean:165](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean#L165) — Materialization retains the challenge, wires, accumulator and their exact residuals.
- `theorem Plonk.Quotient.oracleVerifier_toVerifier` [ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean:110](../../../ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean#L110) — Materialization checks the quotient identity and returns the exact retained input on success.
- `theorem Plonk.SendWitness.oracleVerifier_toVerifier` [ArkLib/ProofSystem/Plonk/SendWitness.lean:78](../../../ArkLib/ProofSystem/Plonk/SendWitness.lean#L78) — Materialization exposes exactly the received table.

### `output` (7 declarations, 7 files)

- `def ArkLib.Lattices.Hachi.TraceHead.output` [ArkLib/Commitments/Functional/Hachi/TraceHead/Protocol.lean:74](../../../ArkLib/Commitments/Functional/Hachi/TraceHead/Protocol.lean#L74) — The ring-level statement drops the suffix and forwards the sent value.
- `def GeneratorBatch.output` [ArkLib/ProofSystem/Component/GeneratorBatch.lean:65](../../../ArkLib/ProofSystem/Component/GeneratorBatch.lean#L65) — The materialized batched output, with no extra public data.
- `def SendSingleWitness.Adapter.output` [ArkLib/ProofSystem/Component/SendWitness.lean:250](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L250) — The statement and oracles exposed by a particular sent message.
- `def Plonk.Batch.output` [ArkLib/ProofSystem/Plonk/Batch/Reduction.lean:74](../../../ArkLib/ProofSystem/Plonk/Batch/Reduction.lean#L74) — Preserve the joint grand-product challenge alongside the retained output oracles.
- `def Plonk.GrandProduct.output` [ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean:69](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean#L69) — The verifier records the joint challenge alongside its output oracles.
- `def Spartan.FirstSumcheck.output` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:75](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L75) — The virtual input is internal; the output family consists of the retained original oracles.
- `def Spartan.SecondSumcheck.output` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:122](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L122) — The virtual input is internal; the output retains the original oracle family.

### `outputSimulation` (7 declarations, 7 files)

- `def BatchedFri.Spec.BatchingRound.outputSimulation` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:198](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L198) — Virtual implementation of the random-linear-combination codeword.  Every downstream coordinate query
- `def GeneratorBatch.outputSimulation` [ArkLib/ProofSystem/Component/GeneratorBatch.lean:104](../../../ArkLib/ProofSystem/Component/GeneratorBatch.lean#L104) — Evaluation-only simulation of the batched polynomial oracle.
- `def Plonk.Batch.outputSimulation` [ArkLib/ProofSystem/Plonk/Batch/Reduction.lean:159](../../../ArkLib/ProofSystem/Plonk/Batch/Reduction.lean#L159) — Evaluation-only implementation of the retained and batched output oracles.
- `def Plonk.GrandProduct.outputSimulation` [ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean:144](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean#L144) — Query-by-query implementation of the retained and virtual output oracles.
- `def Plonk.SendWitness.outputSimulation` [ArkLib/ProofSystem/Plonk/SendWitness.lean:54](../../../ArkLib/ProofSystem/Plonk/SendWitness.lean#L54) — Each output column query is one evaluation query to the table message.
- `def Spartan.WitnessAttachment.outputSimulation` [ArkLib/ProofSystem/Spartan/WitnessAttachment.lean:69](../../../ArkLib/ProofSystem/Spartan/WitnessAttachment.lean#L69) — Output matrix queries forward one scalar source query; witness queries use the sent table.
- `def ToyProblem.SimplifiedIOR.outputSimulation` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:271](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L271) — Virtual implementation of the combined C6.9 output oracle.

### `instIsPure` (8 declarations, 6 files)

- `instance CheckClaim.instIsPure` [ArkLib/ProofSystem/Component/CheckClaim.lean:237](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L237) — The `CheckClaim` oracle verifier is pure: its underlying verifier deterministically returns the comb
- `instance NoInteraction.instIsPure` [ArkLib/ProofSystem/Component/NoInteraction.lean:61](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L61) — The no-interaction verifier deterministically recomputes the output statement.
- `instance ReduceClaim.instIsPure` [ArkLib/ProofSystem/Component/ReduceClaim.lean:184](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L184) — The `ReduceClaim` verifier is pure: it deterministically returns `mapStmt stmt`. This discharges the
- `instance SendChallenge.instIsPure` [ArkLib/ProofSystem/Component/SendChallenge.lean:130](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L130) — The `SendChallenge` oracle verifier is pure: it deterministically appends the (transcript-read) chal
- `instance SendClaim.instIsPure` [ArkLib/ProofSystem/Component/SendClaim.lean:166](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L166) — The `SendClaim` oracle verifier is pure, discharging the deterministic-left hypothesis of the CWSS b
- `instance SendWitness.instIsPure` [ArkLib/ProofSystem/Component/SendWitness.lean:106](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L106) — The `SendWitness` verifier is pure: it deterministically returns `⟨stmt, transcript 0⟩`. This discha
- `instance SendSingleWitness.Adapter.instIsPure` [ArkLib/ProofSystem/Component/SendWitness.lean:298](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L298) — Every adapter verifier is deterministic.
- `instance SendSingleWitness.instIsPure` [ArkLib/ProofSystem/Component/SendWitness.lean:479](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L479) — The `SendSingleWitness` oracle verifier is pure: its underlying (non-oracle) verifier deterministica

### `instOutputIsPure` (8 declarations, 6 files)

- `instance CheckClaim.instOutputIsPure` [ArkLib/ProofSystem/Component/CheckClaim.lean:66](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L66) — The `CheckClaim` prover has pure output: it reads its statement off the state, with no oracle query.
- `instance DoNothing.instOutputIsPure` [ArkLib/ProofSystem/Component/DoNothing.lean:36](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L36) — The `DoNothing` prover has pure output: it is `Prover.id`, whose `output` is `pure`.
- `instance ReduceClaim.instOutputIsPure` [ArkLib/ProofSystem/Component/ReduceClaim.lean:59](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L59) — The `ReduceClaim` prover has pure output: it applies the two plain maps `mapStmt` / `mapWit`, with n
- `instance SendChallenge.instOutputIsPure` [ArkLib/ProofSystem/Component/SendChallenge.lean:71](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L71) — The `SendChallenge` oracle prover has pure output: it appends the received challenge to the statemen
- `instance SendClaim.instOutputIsPure` [ArkLib/ProofSystem/Component/SendClaim.lean:90](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L90) — The `SendClaim` oracle prover has pure output: it exposes the claim it already computed alongside th
- `instance SendWitness.instOutputIsPure` [ArkLib/ProofSystem/Component/SendWitness.lean:84](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L84) — The `SendWitness` prover has pure output: it pairs up the state it already holds, with no oracle que
- `instance SendSingleWitness.Adapter.instOutputIsPure` [ArkLib/ProofSystem/Component/SendWitness.lean:264](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L264) — Materialization needs no oracle query.
- `instance SendSingleWitness.instOutputIsPure` [ArkLib/ProofSystem/Component/SendWitness.lean:404](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L404) — The fixed-output sender has pure output.

### `reduction_perfectCompleteness` (7 declarations, 6 files)

- `theorem CoordinateWise.CommittedScalar.reduction_perfectCompleteness` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:437](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L437) — **Perfect completeness of a committed scalar phase**, at error exactly `0`. The two hypotheses are p
- `theorem DoNothing.reduction_perfectCompleteness` [ArkLib/ProofSystem/Component/DoNothing.lean:57](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L57) — The `DoNothing` reduction satisfies perfect completeness for any relation.
- `theorem RingSwitching.Lift.reduction_perfectCompleteness` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:312](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L312) — **Perfect completeness at the plain linear relation `relLin`.** The specialization of `reduction_per
- `theorem Spartan.SendEvaluations.reduction_perfectCompleteness` [ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean:138](../../../ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean#L138) — Honest row evaluations pass the scalar check and establish all three output claims.
- `theorem Sumcheck.Spec.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:484](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L484) — Perfect completeness for the (full) sum-check protocol
- `theorem Sumcheck.Spec.SingleRound.Simple.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:458](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L458) — Perfect completeness for the (non-oracle) reduction
- `theorem Sumcheck.Spec.SingleRound.reduction_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1135](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1135) — (no docstring)

### `relation` (7 declarations, 6 files)

- `def ArkLib.Lattices.ModuleSIS.relation` [ArkLib/Data/Lattices/ModuleSIS.lean:89](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L89) — The kernel-form Module-SIS relation for a fixed matrix `A`: `z` is nonzero, short, and lies in the k
- `def Lookup.relation` [ArkLib/ProofSystem/ConstraintSystem/Lookup.lean:28](../../../ArkLib/ProofSystem/ConstraintSystem/Lookup.lean#L28) — The lookup relation. Takes in a collection of values and a table, both containers for elements of ty
- `def MemoryChecking.ReadOnly.relation` [ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean:131](../../../ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean#L131) — The read-only memory checking relation. It takes a memory `mem` and a list of read operations `ops`.
- `def MemoryChecking.ReadWrite.relation` [ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean:164](../../../ArkLib/ProofSystem/ConstraintSystem/MemoryChecking.lean#L164) — The read-write memory checking relation. It takes an initial memory `startMem`, a final memory `fina
- `def Plonk.relation` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:214](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L214) — To define a relation based on the constraint system, we extend it with: - A natural number `ℓ ≤ m` r
- `def R1CS.relation` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:65](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L65) — The R1CS relation: `(A *ᵥ 𝕫) * (B *ᵥ 𝕫) = (C *ᵥ 𝕫)`, where `*` is understood to mean component-wise
- `def Spartan.Assembly.relation` [ArkLib/ProofSystem/Spartan/Protocol.lean:127](../../../ArkLib/ProofSystem/Spartan/Protocol.lean#L127) — Relations at the boundaries, starting with the original R1CS relation.

### `verifier_rbrKnowledgeSoundness` (7 declarations, 6 files)

- `theorem Binius.FRIBinius.RingSwitch.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/RingSwitch.lean:152](../../../ArkLib/ProofSystem/Binius/FRIBinius/RingSwitch.lean#L152) — The frontend is round-by-round knowledge sound for first-oracle compatibility.
- `theorem CheckClaim.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/CheckClaim.lean:148](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L148) — The `CheckClaim` reduction satisfies perfect round-by-round knowledge soundness.
- `theorem DoNothing.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/DoNothing.lean:63](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L63) — The `DoNothing` verifier is perfectly round-by-round knowledge sound.
- `theorem ReduceClaim.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:175](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L175) — The `ReduceClaim` oracle reduction satisfies perfect round-by-round knowledge soundness. Note that s
- `theorem Spartan.SendEvaluations.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean:131](../../../ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean#L131) — Sending and checking row evaluations has zero fixed-prefix knowledge error.
- `theorem Sumcheck.Spec.SingleRound.Simple.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:564](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L564) — At every fixed prefix, a false sum becomes valid with probability at most `deg / \|R\|`.
- `theorem Sumcheck.Spec.SingleRound.verifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:1146](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L1146) — Round-by-round knowledge soundness for the lifted round verifier.

### `OStmtIn` (6 declarations, 6 files)

- `abbrev GeneratorBatch.OStmtIn` [ArkLib/ProofSystem/Component/GeneratorBatch.lean:48](../../../ArkLib/ProofSystem/Component/GeneratorBatch.lean#L48) — The fixed family of input polynomial oracles.
- `abbrev QuotientZeroTest.OStmtIn` [ArkLib/ProofSystem/Component/QuotientZeroTest.lean:75](../../../ArkLib/ProofSystem/Component/QuotientZeroTest.lean#L75) — The sole input oracle is the degree-bounded dividend.
- `abbrev Plonk.Batch.OStmtIn` [ArkLib/ProofSystem/Plonk/Batch/Reduction.lean:34](../../../ArkLib/ProofSystem/Plonk/Batch/Reduction.lean#L34) — Batching retains the grand-product stage's oracle family.
- `abbrev Plonk.GrandProduct.OStmtIn` [ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean:43](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean#L43) — Three wire polynomials, fixed before the challenge.
- `abbrev Plonk.SendWitness.OStmtIn` [ArkLib/ProofSystem/Plonk/SendWitness.lean:28](../../../ArkLib/ProofSystem/Plonk/SendWitness.lean#L28) — There are no polynomial oracles before the witness table is sent.
- `def Sumcheck.Spec.SingleRound.Simple.OStmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:203](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L203) — (no docstring)

### `Witness` (6 declarations, 6 files)

- `def BatchedFri.Spec.Witness` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:60](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L60) — The Batched FRI protocol has as witness for each batched polynomial that is supposed to correspond t
- `structure Binius.BinaryBasefold.Witness` [ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean:114](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Basic.lean#L114) — A multilinear source, its degree-two partial sum-check polynomial, and its folded codeword at the cu
- `def R1CS.Witness` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:55](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L55) — (no docstring)
- `def Fri.Spec.Witness` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:106](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L106) — A computational polynomial witness with the degree bound of stage `i`.
- `abbrev Spartan.Assembly.Witness` [ArkLib/ProofSystem/Spartan/Protocol.lean:47](../../../ArkLib/ProofSystem/Spartan/Protocol.lean#L47) — Only the attachment input has a private witness.
- `def ToyProblem.Spec.Witness` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:189](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L189) — Honest witness: the underlying messages `M₁, M₂ : Fin k → F` whose encodings are the oracle codeword

### `check` (6 declarations, 6 files)

- `def ArkLib.Lattices.Hachi.TraceHead.check` [ArkLib/Commitments/Functional/Hachi/TraceHead/Protocol.lean:93](../../../ArkLib/Commitments/Functional/Hachi/TraceHead/Protocol.lean#L93) — The scaled trace equality checked in the quotient ring.
- `def QuotientZeroTest.check` [ArkLib/ProofSystem/Component/QuotientZeroTest.lean:105](../../../ArkLib/ProofSystem/Component/QuotientZeroTest.lean#L105) — The deterministic equation on a fully materialized transcript.
- `def RingSwitching.Packing.Head.check` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:82](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L82) — The message must reconstruct the claimed scalar value under the chosen layout.
- `def RingSwitching.Packing.ProductSumcheck.Round.check` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean:46](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean#L46) — The local sumcheck equation.
- `def RingSwitching.Packing.ProductSumcheck.Terminal.check` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean:40](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean#L40) — The only verifier equation, valid also when the multiplier is zero.
- `def Spartan.Evaluation.check` [ArkLib/ProofSystem/Spartan/Evaluation/Relation.lean:37](../../../ArkLib/ProofSystem/Spartan/Evaluation/Relation.lean#L37) — The scalar equation checked when the three values are sent.

### `materializeOutput` (6 declarations, 6 files)

- `def OracleVerifier.materializeOutput` [ArkLib/OracleReduction/Basic.lean:383](../../../ArkLib/OracleReduction/Basic.lean#L383) — Materialize the semantic output family, using a virtual simulation when present and the legacy embed
- `def OracleReduction.LogicStep.materializeOutput` [ArkLib/OracleReduction/LogicStep.lean:79](../../../ArkLib/OracleReduction/LogicStep.lean#L79) — Materialize the output oracles from their embedded or simulated representation.
- `theorem Spartan.Batching.materializeOutput` [ArkLib/ProofSystem/Spartan/Batching/Reduction.lean:77](../../../ArkLib/ProofSystem/Spartan/Batching/Reduction.lean#L77) — (no docstring)
- `theorem Spartan.SendEvaluations.materializeOutput` [ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean:84](../../../ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean#L84) — (no docstring)
- `theorem Spartan.Terminal.materializeOutput` [ArkLib/ProofSystem/Spartan/Terminal.lean:93](../../../ArkLib/ProofSystem/Spartan/Terminal.lean#L93) — Materialized oracle identities are preserved.
- `theorem Spartan.WitnessAttachment.materializeOutput` [ArkLib/ProofSystem/Spartan/WitnessAttachment.lean:139](../../../ArkLib/ProofSystem/Spartan/WitnessAttachment.lean#L139) — Materialization exposes precisely the embedded matrices and the table in the transcript.

### `oracleVerifier_materializeOutput` (6 declarations, 6 files)

- `theorem CheckClaim.oracleVerifier_materializeOutput` [ArkLib/ProofSystem/Component/CheckClaim.lean:200](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L200) — (no docstring)
- `theorem RandomQuery.oracleVerifier_materializeOutput` [ArkLib/ProofSystem/Component/RandomQuery.lean:94](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L94) — (no docstring)
- `theorem SendChallenge.oracleVerifier_materializeOutput` [ArkLib/ProofSystem/Component/SendChallenge.lean:92](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L92) — (no docstring)
- `theorem SendClaim.oracleVerifier_materializeOutput` [ArkLib/ProofSystem/Component/SendClaim.lean:135](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L135) — (no docstring)
- `theorem SendSingleWitness.oracleVerifier_materializeOutput` [ArkLib/ProofSystem/Component/SendWitness.lean:420](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L420) — (no docstring)
- `theorem Sumcheck.Spec.oracleVerifier_materializeOutput` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:415](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L415) — Sum-check retains its original input polynomial as its output oracle.

### `polynomial` (6 declarations, 6 files)

- `def ReedSolomon.HiddenDerivative.SourceColumn.polynomial` [ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/SourceColumn.lean:181](../../../ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/SourceColumn.lean#L181) — The source monomial of a column, with coefficient `1`.
- `def PermutationFingerprint.polynomial` [ArkLib/Data/Polynomial/PermutationFingerprint.lean:37](../../../ArkLib/Data/Polynomial/PermutationFingerprint.lean#L37) — The formal fingerprint in the two challenge variables. Mathlib's finitely supported polynomial arith
- `def Spartan.FirstSumcheck.polynomial` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:35](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L35) — The degree-three virtual polynomial, constructed from the retained tables.
- `def Spartan.SecondSumcheck.polynomial` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:33](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L33) — The second sumcheck's polynomial is computed from the retained tables and batch.
- `def Spartan.ZeroCheck.polynomial` [ArkLib/ProofSystem/Spartan/ZeroCheck/Relation.lean:26](../../../ArkLib/ProofSystem/Spartan/ZeroCheck/Relation.lean#L26) — The residual interpolation. Sparse polynomial materialization uses nonconstructive equality.
- `def Sumcheck.EnumerationState.polynomial` [ArkLib/ProofSystem/Sumcheck/Prover/Enumeration.lean:70](../../../ArkLib/ProofSystem/Sumcheck/Prover/Enumeration.lean#L70) — The original polynomial with the challenge prefix fixed, in the remaining variables.

### `knowledgeSoundness` (9 declarations, 5 files)

- `def Verifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:351](../../../ArkLib/OracleReduction/Security/Basic.lean#L351) — A reduction satisfies **(straightline) knowledge soundness** with error `knowledgeError ≥ 0` and wit
- `def OracleVerifier.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:486](../../../ArkLib/OracleReduction/Security/Basic.lean#L486) — Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:549](../../../ArkLib/OracleReduction/Security/Basic.lean#L549) — (no docstring)
- `def OracleProof.knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:589](../../../ArkLib/OracleReduction/Security/Basic.lean#L589) — Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- `theorem Verifier.knowledgeSoundnessWithResources.knowledgeSoundness` [ArkLib/OracleReduction/Security/Resources.lean:97](../../../ArkLib/OracleReduction/Security/Resources.lean#L97) — Forget the measured program and the extractor's identity.
- `theorem OracleVerifier.knowledgeSoundnessWithResources.knowledgeSoundness` [ArkLib/OracleReduction/Security/Resources.lean:154](../../../ArkLib/OracleReduction/Security/Resources.lean#L154) — Forget the measured program and the extractor's identity.
- `theorem RingSwitching.Packing.RingSwitch.knowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/Packing/RingSwitch.lean:242](../../../ArkLib/ProofSystem/RingSwitching/Packing/RingSwitch.lean#L242) — The whole reduction is knowledge sound with error `bat.error + 2m/\|C\|`.
- `theorem RingSwitching.Packing.TensorPrefix.knowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/Packing/TensorPrefix.lean:268](../../../ArkLib/ProofSystem/RingSwitching/Packing/TensorPrefix.lean#L268) — Prefix packing is knowledge sound with error `κ/\|L\| + 2ℓ'/\|L\|`.
- `theorem Spartan.knowledgeSoundness` [ArkLib/ProofSystem/Spartan/Security.lean:252](../../../ArkLib/ProofSystem/Spartan/Security.lean#L252) — Spartan is knowledge sound for the original R1CS relation with additive error `(4s + 2t + 1) / \|R\|`.

### `Message` (5 declarations, 5 files)

- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.Message` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:142](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L142) — Messages: block vectors over the message row space.
- `abbrev ArkLib.Lattices.Ajtai.Simple.Message` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:36](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L36) — Messages: column vectors over `Rq Φ`.
- `def ProtocolSpec.Message` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:69](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L69) — The type of the `i`-th message in a protocol specification. This does not distinguish between messag
- `abbrev Sumcheck.Impl.Representation.Message` [ArkLib/ProofSystem/Sumcheck/Impl/Representation.lean:26](../../../ArkLib/ProofSystem/Sumcheck/Impl/Representation.lean#L26) — A bounded computable univariate polynomial, including the zero polynomial.
- `abbrev Sumcheck.Interaction.SingleRound.Message` [ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:32](../../../ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean#L32) — A degree-bounded polynomial message.

### `extractor` (5 declarations, 5 files)

- `def ReduceClaim.extractor` [ArkLib/ProofSystem/Component/ReduceClaim.lean:132](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L132) — The round-by-round extractor for the `ReduceClaim` (oracle) reduction. Requires a mapping `mapWitInv
- `def RingSwitching.Packing.Head.extractor` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:310](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L310) — Read back the original source through both the packing and layout equivalences.
- `def RingSwitching.Packing.ProductSumcheck.Round.extractor` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/RoundSecurity.lean:77](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/RoundSecurity.lean#L77) — No witness replacement is needed at a sumcheck message or at the output.
- `def RingSwitching.Packing.ProductSumcheck.Terminal.extractor` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean:203](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean#L203) — The terminal extractor preserves the original packed polynomial.
- `def Spartan.Assembly.extractor` [ArkLib/ProofSystem/Spartan/Security.lean:52](../../../ArkLib/ProofSystem/Spartan/Security.lean#L52) — Each named stage extractor, including the attachment's restriction of the sent table. The sumcheck e

### `interpolate` (5 declarations, 5 files)

- `def ReedSolomon.interpolate` [ArkLib/Data/CodingTheory/ReedSolomon.lean:572](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L572) — The linear map that maps a codeword `f : ι → F` to a degree < \|ι\| polynomial p, such that `p(x) = f(
- `def Matrix.ReadOnce.interpolate` [ArkLib/Data/Matrix/ReadOnce.lean:51](../../../ArkLib/Data/Matrix/ReadOnce.lean#L51) — The affine interpolation of a two-branch matrix layer.
- `def Plonk.EvaluationDomain.interpolate` [ArkLib/ProofSystem/Plonk/Encoding/Basic.lean:34](../../../ArkLib/ProofSystem/Plonk/Encoding/Basic.lean#L34) — The unique interpolant of a column, using Mathlib's noncomputable polynomial arithmetic.
- `def Plonk.Computable.interpolate` [ArkLib/ProofSystem/Plonk/Encoding/Computable.lean:27](../../../ArkLib/ProofSystem/Plonk/Encoding/Computable.lean#L27) — Interpolate a row column using executable coefficient arrays.
- `def CompPoly.Arithmetic.interpolate` [ArkLib/ToCompPoly/Univariate/ArithmeticInterpolation.lean:78](../../../ArkLib/ToCompPoly/Univariate/ArithmeticInterpolation.lean#L78) — Interpolate explicit cached nodes and values in their finite index order.

### `oracleVerifier_toVerifier_run` (5 declarations, 5 files)

- `theorem CheckClaim.oracleVerifier_toVerifier_run` [ArkLib/ProofSystem/Component/CheckClaim.lean:223](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L223) — The pure pass-through oracle verifier's underlying non-oracle verifier returns the combined input st
- `theorem ReduceClaim.oracleVerifier_toVerifier_run` [ArkLib/ProofSystem/Component/ReduceClaim.lean:370](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L370) — The `ReduceClaim` oracle verifier's underlying non-oracle verifier deterministically returns the map
- `theorem SendChallenge.oracleVerifier_toVerifier_run` [ArkLib/ProofSystem/Component/SendChallenge.lean:119](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L119) — The pure verifier's underlying non-oracle verifier returns the statement together with the sampled c
- `theorem SendClaim.oracleVerifier_toVerifier_run` [ArkLib/ProofSystem/Component/SendClaim.lean:153](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L153) — The pure pass-through oracle verifier's underlying non-oracle verifier returns the statement togethe
- `theorem SendSingleWitness.oracleVerifier_toVerifier_run` [ArkLib/ProofSystem/Component/SendWitness.lean:468](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L468) — (no docstring)

### `outputEmbedding` (5 declarations, 5 files)

- `def CheckClaim.outputEmbedding` [ArkLib/ProofSystem/Component/CheckClaim.lean:183](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L183) — The oracle verifier for the `CheckClaim` oracle reduction is a **pure pass-through**: it returns the
- `def SendChallenge.outputEmbedding` [ArkLib/ProofSystem/Component/SendChallenge.lean:76](../../../ArkLib/ProofSystem/Component/SendChallenge.lean#L76) — The oracle verifier samples the challenge `c` (as the `V_to_P` round), reads it off the transcript,
- `def SendClaim.outputEmbedding` [ArkLib/ProofSystem/Component/SendClaim.lean:100](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L100) — (no docstring)
- `def SendSingleWitness.outputEmbedding` [ArkLib/ProofSystem/Component/SendWitness.lean:371](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L371) — (no docstring)
- `def Spartan.SendEvaluations.outputEmbedding` [ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean:37](../../../ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean#L37) — Retain exactly the original matrix and witness oracles.

### `rbrError` (5 declarations, 5 files)

- `def RingSwitching.Packing.Head.rbrError` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:445](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L445) — The single fresh challenge incurs exactly the strategy's separation bound.
- `def RingSwitching.Packing.ProductSumcheck.rbrError` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Knowledge.lean:54](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Knowledge.lean#L54) — The scalar challenges retain their component error; the terminal contributes none.
- `def RingSwitching.Packing.ProductSumcheck.Round.rbrError` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/RoundSecurity.lean:104](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/RoundSecurity.lean#L104) — The scalar challenge carries the degree-two collision bound.
- `def RingSwitching.Packing.RingSwitch.rbrError` [ArkLib/ProofSystem/RingSwitching/Packing/RingSwitch.lean:148](../../../ArkLib/ProofSystem/RingSwitching/Packing/RingSwitch.lean#L148) — The error function on appended challenge indices, with no terminal loss.
- `abbrev RingSwitching.Packing.TensorPrefix.rbrError` [ArkLib/ProofSystem/RingSwitching/Packing/TensorPrefix.lean:232](../../../ArkLib/ProofSystem/RingSwitching/Packing/TensorPrefix.lean#L232) — The shared strategy assigns the original batching loss to the carrier wire.

### `reduction_completeness` (5 declarations, 5 files)

- `theorem CheckClaim.reduction_completeness` [ArkLib/ProofSystem/Component/CheckClaim.lean:92](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L92) — The `CheckClaim` reduction satisfies perfect completeness with respect to the predicate as the input
- `theorem NoInteraction.reduction_completeness` [ArkLib/ProofSystem/Component/NoInteraction.lean:77](../../../ArkLib/ProofSystem/Component/NoInteraction.lean#L77) — (no docstring)
- `theorem ReduceClaim.reduction_completeness` [ArkLib/ProofSystem/Component/ReduceClaim.lean:124](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L124) — The `ReduceClaim` reduction satisfies perfect completeness for any relation. The `↔` form of `reduct
- `theorem SendWitness.reduction_completeness` [ArkLib/ProofSystem/Component/SendWitness.lean:112](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L112) — The `SendWitness` reduction satisfies perfect completeness.
- `theorem Fri.Spec.reduction_completeness` [ArkLib/ProofSystem/Fri/Spec/Completeness.lean:156](../../../ArkLib/ProofSystem/Fri/Spec/Completeness.lean#L156) — The complete reduction accepts noisy inputs with the clipped first-fold completeness error, and its

### `reindex` (6 declarations, 4 files)

- `def Interaction.Oracle.NamedContext.reindex` [ArkLib/Interaction/Oracle/Resource.lean:95](../../../ArkLib/Interaction/Oracle/Resource.lean#L95) — Reindex a named context along an injection.
- `def Interaction.Oracle.NamedContext.View.reindex` [ArkLib/Interaction/Oracle/Resource.lean:341](../../../ArkLib/Interaction/Oracle/Resource.lean#L341) — Reindex a view; a noninjective map introduces aliases.
- `def Interaction.Oracle.SourceCtx.reindex` [ArkLib/Interaction/Oracle/Source.lean:61](../../../ArkLib/Interaction/Oracle/Source.lean#L61) — Restrict or rename the query interface; noninjective maps explicitly expose aliases.
- `def Interaction.Oracle.OracleFamily.reindex` [ArkLib/Interaction/Oracle/Virtual.lean:60](../../../ArkLib/Interaction/Oracle/Virtual.lean#L60) — Pull back the indexed interface family along an arbitrary map. Repeated indices copy interface types
- `def Interaction.Oracle.VirtualOracle.reindex` [ArkLib/Interaction/Oracle/Virtual.lean:118](../../../ArkLib/Interaction/Oracle/Virtual.lean#L118) — Reindex output interfaces by reusing their query programs.
- `def RingSwitching.Packing.BatchingStrategy.reindex` [ArkLib/ProofSystem/RingSwitching/Packing/Batching.lean:129](../../../ArkLib/ProofSystem/RingSwitching/Packing/Batching.lean#L129) — Transport a batching strategy along an equivalence of claim indices.

### `FinalStatement` (5 declarations, 4 files)

- `def Fri.Spec.FinalStatement` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:75](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L75) — All folding challenges, retained as the statement for the query round.
- `structure Spartan.Realization.FinalStatement` [ArkLib/ProofSystem/Spartan/Context.lean:50](../../../ArkLib/ProofSystem/Spartan/Context.lean#L50) — The final sumcheck evaluation and all retained batching data.
- `abbrev Sumcheck.Interaction.Computable.FinalStatement` [ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean:29](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean#L29) — The terminal statement is the unchanged full-prefix evaluation claim.
- `abbrev Sumcheck.Interaction.Native.Core.FinalStatement` [ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:74](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean#L74) — The final claim has the full challenge vector and the claimed evaluation.
- `abbrev Sumcheck.Interaction.Native.FinalStatement` [ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:339](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean#L339) — Final interaction-layer Sumcheck statement.

### `oracleProver_run` (5 declarations, 4 files)

- `theorem SendSingleWitness.Adapter.oracleProver_run` [ArkLib/ProofSystem/Component/SendWitness.lean:276](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L276) — The honest transcript contains the encoded input witness.
- `theorem SendSingleWitness.oracleProver_run` [ArkLib/ProofSystem/Component/SendWitness.lean:445](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L445) — (no docstring)
- `theorem Plonk.Batch.oracleProver_run` [ArkLib/ProofSystem/Plonk/Batch/Reduction.lean:250](../../../ArkLib/ProofSystem/Plonk/Batch/Reduction.lean#L250) — The honest runs have the same challenge and corresponding retained outputs.
- `theorem Plonk.GrandProduct.oracleProver_run` [ArkLib/ProofSystem/Plonk/GrandProduct/Completeness.lean:50](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Completeness.lean#L50) — The actual honest prover run samples one joint challenge and sends its accumulator.
- `theorem Spartan.WitnessAttachment.oracleProver_run` [ArkLib/ProofSystem/Spartan/WitnessAttachment.lean:109](../../../ArkLib/ProofSystem/Spartan/WitnessAttachment.lean#L109) — The honest transcript contains precisely the embedded input witness.

### `protocol` (5 declarations, 4 files)

- `def Interaction.Oracle.Security.StateRestoration.protocol` [ArkLib/Interaction/Oracle/Security/StateRestoration.lean:50](../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L50) — The fixed presentation uses oracle-message and public-receiver nodes.
- `abbrev Sumcheck.Interaction.Computable.protocol` [ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean:34](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean#L34) — Protocol carrying actual computable degree-bounded messages.
- `def Sumcheck.Interaction.Native.Core.protocol` [ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:41](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean#L41) — Each failed sum check takes a terminal public abort branch.
- `def Sumcheck.Interaction.Native.protocol` [ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:333](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean#L333) — The mathematical message specialization of the shared protocol.
- `abbrev Sumcheck.Interaction.SingleRound.protocol` [ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:45](../../../ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean#L45) — A degree-refined send followed by a public verifier challenge.

### `restrict` (5 declarations, 4 files)

- `abbrev Interaction.Oracle.TypeTree.AccessDecoration.restrict` [ArkLib/Interaction/Oracle/Access.lean:311](../../../ArkLib/Interaction/Oracle/Access.lean#L311) — Restrict a presentation using PolyFun's canonical displayed restriction.
- `def Interaction.Oracle.Security.RoundExtractor.restrict` [ArkLib/Interaction/Oracle/Security/Knowledge.lean:92](../../../ArkLib/Interaction/Oracle/Security/Knowledge.lean#L92) — Restrict witness maps to the residual selected by the concrete prefix.
- `abbrev Interaction.Oracle.TypeTree.RoleDecoration.restrict` [ArkLib/Interaction/Oracle/TypeTree/Decoration.lean:82](../../../ArkLib/Interaction/Oracle/TypeTree/Decoration.lean#L82) — Restrict roles to the residual tree selected by a structural cursor.
- `abbrev Interaction.Oracle.TypeTree.OracleDecoration.restrict` [ArkLib/Interaction/Oracle/TypeTree/Decoration.lean:234](../../../ArkLib/Interaction/Oracle/TypeTree/Decoration.lean#L234) — Restrict oracle interfaces to the residual tree selected by a structural cursor.
- `def ProtocolSpec.Transcript.restrict` [ArkLib/OracleReduction/Security/BadEvents.lean:47](../../../ArkLib/OracleReduction/Security/BadEvents.lean#L47) — Restrict a partial transcript to an earlier cutoff in the same protocol.

### `run` (5 declarations, 4 files)

- `def Matrix.ReadOnce.run` [ArkLib/Data/Matrix/ReadOnce.lean:33](../../../ArkLib/Data/Matrix/ReadOnce.lean#L33) — Apply each matrix to the state, reading the layers from first to last.
- `def OracleComp.MeasuredProgram.run` [ArkLib/Data/OracleComp/MeasuredProgram.lean:74](../../../ArkLib/Data/OracleComp/MeasuredProgram.lean#L74) — The handlers' execution of the program on the view of `input`.
- `def Interaction.Oracle.ClosedStage.run` [ArkLib/Interaction/Oracle/Composition.lean:119](../../../ArkLib/Interaction/Oracle/Composition.lean#L119) — Execute using exactly the input claim's behavior, and close with the resources of that run. The conc
- `def Interaction.Oracle.OrderedExecution.run` [ArkLib/Interaction/Oracle/Composition.lean:145](../../../ArkLib/Interaction/Oracle/Composition.lean#L145) — Execute a finite family of actual oracle reductions across explicit dependent interfaces. Each accep
- `def Prover.run` [ArkLib/OracleReduction/Execution.lean:102](../../../ArkLib/OracleReduction/Execution.lean#L102) — Run the prover in an interactive reduction. Returns the output statement and witness, and the transc

### `OStmtOut` (4 declarations, 4 files)

- `abbrev QuotientZeroTest.OStmtOut` [ArkLib/ProofSystem/Component/QuotientZeroTest.lean:77](../../../ArkLib/ProofSystem/Component/QuotientZeroTest.lean#L77) — No polynomial oracles remain after the acceptance check.
- `abbrev Plonk.Batch.OStmtOut` [ArkLib/ProofSystem/Plonk/Batch/Reduction.lean:37](../../../ArkLib/ProofSystem/Plonk/Batch/Reduction.lean#L37) — Retained earlier oracles and the new degree-bounded batch.
- `abbrev Plonk.GrandProduct.OStmtOut` [ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean:46](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean#L46) — Retained wires, the accumulator, and the three derived residuals.
- `def Sumcheck.Spec.SingleRound.Simple.OStmtOut` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:206](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L206) — (no docstring)

### `WitMid` (4 declarations, 4 files)

- `abbrev Plonk.SendWitness.WitMid` [ArkLib/ProofSystem/Plonk/SendWitness.lean:101](../../../ArkLib/ProofSystem/Plonk/SendWitness.lean#L101) — Intermediate witnesses retain the table throughout the reveal.
- `def RingSwitching.Packing.Head.WitMid` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:304](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L304) — The source witness before the message and the packed polynomial thereafter.
- `abbrev RingSwitching.Packing.ProductSumcheck.Round.WitMid` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/RoundSecurity.lean:74](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/RoundSecurity.lean#L74) — The original packed polynomial is retained at all three prefixes.
- `abbrev RingSwitching.Packing.ProductSumcheck.Terminal.WitMid` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean:200](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean#L200) — The original packed polynomial is the witness at every terminal prefix.

### `commit` (4 declarations, 4 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.commit` [ArkLib/Commitments/Functional/Hachi/Commitment.lean:114](../../../ArkLib/Commitments/Functional/Hachi/Commitment.lean#L114) — **The honest Hachi commitment**, at the paper's balanced base-`b` digits. Reshape `p` into its `2^r
- `def KZG.commit` [ArkLib/Commitments/Functional/KZG/Basic.lean:58](../../../ArkLib/Commitments/Functional/KZG/Basic.lean#L58) — To commit to an `n + 1`-tuple of coefficients `coeffs` (corresponding to a polynomial of maximum deg
- `def ArkLib.Lattices.Ajtai.Simple.commit` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:42](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L42) — Deterministically commit by multiplying the public matrix by the message vector.
- `def SimpleRO.commit` [ArkLib/Commitments/Ordinary/SimpleRO.lean:50](../../../ArkLib/Commitments/Ordinary/SimpleRO.lean#L50) — Commit to message `v` under the random oracle `ro` and randomness `r` by hashing `(v, r)`.

### `comp_assoc` (4 declarations, 4 files)

- `theorem Interaction.Oracle.TypeTree.ExecutionPrefix.comp_assoc` [ArkLib/Interaction/Oracle/Prefix.lean:151](../../../ArkLib/Interaction/Oracle/Prefix.lean#L151) — Ordered concrete prefix composition is associative.
- `theorem Interaction.Oracle.NamedContext.Inclusion.comp_assoc` [ArkLib/Interaction/Oracle/Resource.lean:257](../../../ArkLib/Interaction/Oracle/Resource.lean#L257) — (no docstring)
- `theorem Interaction.Oracle.SourceHom.comp_assoc` [ArkLib/Interaction/Oracle/Source.lean:218](../../../ArkLib/Interaction/Oracle/Source.lean#L218) — (no docstring)
- `theorem ConstraintSystem.Hom.comp_assoc` [ArkLib/ProofSystem/ConstraintSystem/Basic.lean:161](../../../ArkLib/ProofSystem/ConstraintSystem/Basic.lean#L161) — (no docstring)

### `disagreementSet` (4 declarations, 4 files)

- `def BlockRelDistance.disagreementSet` [ArkLib/Data/CodingTheory/Basic/BlockRelDistance.lean:46](../../../ArkLib/Data/CodingTheory/Basic/BlockRelDistance.lean#L46) — Let C be a smooth ReedSolomon code `C = RS[F, ι^(2ⁱ), φ', m]` and `f,g : ι^(2ⁱ) → F`, then the (i,k)
- `def disagreementSet` [ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean:60](../../../ArkLib/Data/CodingTheory/ProximityGap/DG25/MainResults.lean#L60) — The set D = Δ^{2m}(U, V), columns where U₀≠V₀ or U₁≠V₁.
- `def Binius.BinaryBasefold.disagreementSet` [ArkLib/ProofSystem/Binius/BinaryBasefold/Code.lean:168](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Code.lean#L168) — Disagreement set Δ : The set of points where two functions disagree. For functions f^(i) and g^(i),
- `def Quotienting.disagreementSet` [ArkLib/ProofSystem/Stir/Quotienting.lean:172](../../../ArkLib/ProofSystem/Stir/Quotienting.lean#L172) — We define the set disagreementSet(f,ι,S,Ans) as the set of all points `x ∈ ι` whose evaluation point

### `eval` (4 declarations, 4 files)

- `def FiniteDomainQuotient.eval` [ArkLib/Data/Polynomial/FiniteDomainQuotient.lean:133](../../../ArkLib/Data/Polynomial/FiniteDomainQuotient.lean#L133) — Horner evaluation of a bounded polynomial.
- `def Interaction.Oracle.SourceCtx.eval` [ArkLib/Interaction/Oracle/Source.lean:122](../../../ArkLib/Interaction/Oracle/Source.lean#L122) — Interpret a program using precisely the answers of the supplied environment.
- `def Interaction.Oracle.VirtualOracle.eval` [ArkLib/Interaction/Oracle/Virtual.lean:86](../../../ArkLib/Interaction/Oracle/Virtual.lean#L86) — Evaluate each query using a deterministic source handler. Compiler inlining erases the realization i
- `def Plonk.Gate.eval` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:58](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L58) — Evaluate a gate on a given input vector.

### `instOutputIsPureOracle` (4 declarations, 4 files)

- `instance CheckClaim.instOutputIsPureOracle` [ArkLib/ProofSystem/Component/CheckClaim.lean:174](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L174) — The `CheckClaim` oracle prover has pure output: it forwards the statement and oracle statements with
- `instance DoNothing.instOutputIsPureOracle` [ArkLib/ProofSystem/Component/DoNothing.lean:78](../../../ArkLib/ProofSystem/Component/DoNothing.lean#L78) — The `DoNothing` oracle prover has pure output: it is `OracleProver.id`, which unfolds to `Prover.id`
- `instance ReduceClaim.instOutputIsPureOracle` [ArkLib/ProofSystem/Component/ReduceClaim.lean:252](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L252) — The `ReduceClaim` oracle prover has pure output: it applies the plain maps `mapStmt`, `mapOStmt`, an
- `instance SendWitness.instOutputIsPureOracle` [ArkLib/ProofSystem/Component/SendWitness.lean:186](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L186) — The `SendWitness` oracle prover has pure output: it exposes the witness alongside the input oracles,

### `instSampleableTypeChallenge` (4 declarations, 4 files)

- `instance BatchedFri.Spec.BatchingRound.instSampleableTypeChallenge` [ArkLib/ProofSystem/BatchedFri/Security.lean:169](../../../ArkLib/ProofSystem/BatchedFri/Security.lean#L169) — The sole challenge samples the generator seed uniformly.
- `instance Fri.Spec.QueryRound.instSampleableTypeChallenge` [ArkLib/ProofSystem/Fri/Spec/Completeness.lean:50](../../../ArkLib/ProofSystem/Fri/Spec/Completeness.lean#L50) — Uniform sampling of the complete vector of initial-domain queries, with replacement.
- `instance Fri.Spec.FinalFoldPhase.instSampleableTypeChallenge` [ArkLib/ProofSystem/Fri/Spec/HonestFinalFolding.lean:32](../../../ArkLib/ProofSystem/Fri/Spec/HonestFinalFolding.lean#L32) — Uniform sampling of the field challenge of the final fold.
- `instance Fri.Spec.FoldPhase.instSampleableTypeChallenge` [ArkLib/ProofSystem/Fri/Spec/HonestFolding.lean:52](../../../ArkLib/ProofSystem/Fri/Spec/HonestFolding.lean#L52) — Uniform sampling of the field challenge of a non-final fold.

### `multiplier` (4 declarations, 4 files)

- `def Binius.BinaryBasefold.multiplier` [ArkLib/ProofSystem/Binius/BinaryBasefold/Relations.lean:117](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Relations.lean#L117) — The Binary Basefold multiplier: `eq(r, X)` at the evaluation point `r` of the context, so that the s
- `def Plonk.CosetLabels.multiplier` [ArkLib/ProofSystem/Plonk/Encoding/Domain.lean:95](../../../ArkLib/ProofSystem/Plonk/Encoding/Domain.lean#L95) — The multiplier `1`, `k₁`, or `k₂` of a wire column.
- `def RingSwitching.Packing.Head.multiplier` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:97](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L97) — The multiplier polynomial and its read-once matrix evaluator.
- `def RingSwitching.Packing.PackingData.multiplier` [ArkLib/ProofSystem/RingSwitching/Packing/Polynomial.lean:141](../../../ArkLib/ProofSystem/RingSwitching/Packing/Polynomial.lean#L141) — The public multilinear multiplier, specified by its Boolean values in a B-algebra C.

### `oracleReduction_toReduction` (4 declarations, 4 files)

- `theorem Spartan.FirstSumcheck.oracleReduction_toReduction` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:237](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L237) — Materializing the implemented reduction gives the ordinary context lift of sumcheck.
- `theorem Spartan.SecondSumcheck.oracleReduction_toReduction` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:239](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L239) — Materializing the implemented reduction gives the ordinary context lift of sumcheck.
- `theorem Sumcheck.Spec.oracleReduction_toReduction` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:469](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L469) — Materializing the oracle protocol gives the ordinary sum-check reduction.
- `theorem Sumcheck.Spec.SingleRound.oracleReduction_toReduction` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:990](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L990) — Materializing the oracle round gives its ordinary context-lifted reduction.

### `oracleVerifier_coordinateWiseSpecialSoundWith` (4 declarations, 4 files)

- `theorem CheckClaim.oracleVerifier_coordinateWiseSpecialSoundWith` [ArkLib/ProofSystem/Component/CheckClaim.lean:285](../../../ArkLib/ProofSystem/Component/CheckClaim.lean#L285) — **Coordinate-wise special soundness of `CheckClaim`, named form.** The verifier is a pure pass-throu
- `theorem ReduceClaim.oracleVerifier_coordinateWiseSpecialSoundWith` [ArkLib/ProofSystem/Component/ReduceClaim.lean:400](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L400) — **Coordinate-wise special soundness of the `ReduceClaim` oracle reduction, named form.** As in the n
- `theorem SendClaim.oracleVerifier_coordinateWiseSpecialSoundWith` [ArkLib/ProofSystem/Component/SendClaim.lean:192](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L192) — **Coordinate-wise special soundness of `SendClaim`, named form.** The verifier is a pure pass-throug
- `theorem SendSingleWitness.oracleVerifier_coordinateWiseSpecialSoundWith` [ArkLib/ProofSystem/Component/SendWitness.lean:510](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L510) — **Coordinate-wise special soundness of `SendSingleWitness`, named form.** The oracle verifier has no

### `treeExtractor` (4 declarations, 4 files)

- `def CoordinateWise.CommittedScalar.treeExtractor` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:207](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L207) — The committed-scalar named extractor: `mkWitness` transported along `ScalarRound.treeExtractorScalar
- `def CoordinateWise.SingleRound.treeExtractor` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:432](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L432) — **The single-round tree extractor**, generic over separate witness types: read the shared message an
- `def ReduceClaim.treeExtractor` [ArkLib/ProofSystem/Component/ReduceClaim.lean:195](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L195) — **The `ReduceClaim` tree extractor**, witness-only: the zero-round tree has a single root-to-leaf pa
- `def RingSwitching.Lift.treeExtractor` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:226](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L226) — The switch's named extractor: the committed-scalar assembler, projecting the common opening to its `

### `verifier_run` (4 declarations, 4 files)

- `theorem SendSingleWitness.Adapter.verifier_run` [ArkLib/ProofSystem/Component/SendWitness.lean:287](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L287) — The materialized verifier returns the output determined by the actual message.
- `theorem Spartan.Batching.verifier_run` [ArkLib/ProofSystem/Spartan/Batching/Reduction.lean:82](../../../ArkLib/ProofSystem/Spartan/Batching/Reduction.lean#L82) — The underlying verifier always returns the computed batch and unchanged oracle tables.
- `theorem Spartan.SendEvaluations.verifier_run` [ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean:90](../../../ArkLib/ProofSystem/Spartan/Evaluation/Reduction.lean#L90) — The verifier accepts precisely when the sent values pass the scalar equation.
- `theorem Spartan.WitnessAttachment.verifier_run` [ArkLib/ProofSystem/Spartan/WitnessAttachment.lean:146](../../../ArkLib/ProofSystem/Spartan/WitnessAttachment.lean#L146) — The materialized verifier returns the embedded public input and attached sent table.

### `soundness` (6 declarations, 3 files)

- `def Verifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:266](../../../ArkLib/OracleReduction/Security/Basic.lean#L266) — A reduction satisfies **soundness** with error `soundnessError ≥ 0` and with respect to input langua
- `def OracleVerifier.soundness` [ArkLib/OracleReduction/Security/Basic.lean:467](../../../ArkLib/OracleReduction/Security/Basic.lean#L467) — Soundness of an oracle reduction is the same as for non-oracle reductions.
- `def Proof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:543](../../../ArkLib/OracleReduction/Security/Basic.lean#L543) — (no docstring)
- `def OracleProof.soundness` [ArkLib/OracleReduction/Security/Basic.lean:580](../../../ArkLib/OracleReduction/Security/Basic.lean#L580) — Soundness of an oracle reduction is the same as for non-oracle reductions.
- `theorem BatchedFri.Spec.BatchingRound.soundness` [ArkLib/ProofSystem/BatchedFri/Security.lean:296](../../../ArkLib/ProofSystem/BatchedFri/Security.lean#L296) — Ordinary soundness against any prover, with any bound on the generator-indexed CA error.
- `theorem Fri.Spec.soundness` [ArkLib/ProofSystem/Fri/Spec/Soundness.lean:81](../../../ArkLib/ProofSystem/Fri/Spec/Soundness.lean#L81) — Soundness of the specified FRI oracle reduction, with its existing input and output relations. In fa

### `knowledgeSoundnessWith` (5 declarations, 3 files)

- `def Verifier.knowledgeSoundnessWith` [ArkLib/OracleReduction/Security/Basic.lean:298](../../../ArkLib/OracleReduction/Security/Basic.lean#L298) — The straightline knowledge-soundness game for one specified extractor. Unlike `knowledgeSoundness`,
- `def OracleVerifier.knowledgeSoundnessWith` [ArkLib/OracleReduction/Security/Basic.lean:475](../../../ArkLib/OracleReduction/Security/Basic.lean#L475) — Knowledge soundness of an oracle reduction is the same as for non-oracle reductions.
- `theorem Verifier.knowledgeSoundnessWithResources.knowledgeSoundnessWith` [ArkLib/OracleReduction/Security/Resources.lean:90](../../../ArkLib/OracleReduction/Security/Resources.lean#L90) — Forget the measured program, keeping the game for the same named extractor.
- `theorem OracleVerifier.knowledgeSoundnessWithResources.knowledgeSoundnessWith` [ArkLib/OracleReduction/Security/Resources.lean:147](../../../ArkLib/OracleReduction/Security/Resources.lean#L147) — Forget the measured program, keeping the game for the same named extractor.
- `theorem Spartan.knowledgeSoundnessWith` [ArkLib/ProofSystem/Spartan/Security.lean:230](../../../ArkLib/ProofSystem/Spartan/Security.lean#L230) — Folding the specified composed extractor gives ordinary knowledge soundness with error `(4s + 2t + 1

### `coordinateWiseSpecialSoundWithEscape` (4 declarations, 3 files)

- `def Verifier.coordinateWiseSpecialSoundWithEscape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean:324](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean#L324) — **Escape-threaded CWSS, named form**: `Verifier.treeSpecialSoundWithEscape` at the CWSS shape `D.toS
- `def OracleVerifier.coordinateWiseSpecialSoundWithEscape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean:469](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean#L469) — Escape-threaded CWSS of an oracle reduction, **named form**: the non-oracle escape notion of the und
- `theorem CoordinateWise.CommittedScalar.coordinateWiseSpecialSoundWithEscape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:254](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L254) — **Generic escape-threaded CWSS certificate for committed scalar phases.** All protocol-independent e
- `theorem RingSwitching.Lift.coordinateWiseSpecialSoundWithEscape` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:237](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L237) — **CWSS of `Lift`**, escape-threaded, at plain `k = 2d` special soundness: on every structured accept

### `drop` (4 declarations, 3 files)

- `def Fin.drop` [ArkLib/Data/Fin/Tuple/Defs.lean:63](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L63) — Drop the first `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple.
- `def ProtocolSpec.drop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:121](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L121) — Drop the first `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.drop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:178](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L178) — (no docstring)
- `def SumcheckDomain.drop` [ArkLib/ProofSystem/Sumcheck/Domain.lean:121](../../../ArkLib/ProofSystem/Sumcheck/Domain.lean#L121) — Drop the first `j` coordinates, leaving the domain on the remaining `k - j` coordinates: coordinate

### `extract` (4 declarations, 3 files)

- `def Fin.extract` [ArkLib/Data/Fin/Tuple/Defs.lean:76](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L76) — Extract a sub-tuple from a `Fin`-tuple, from index `start` to `stop - 1`.
- `def ProtocolSpec.extract` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:129](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L129) — Extract the slice of the rounds of a `ProtocolSpec n` from `start` to `stop - 1`.
- `abbrev ProtocolSpec.FullTranscript.extract` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:186](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L186) — (no docstring)
- `def Fri.Spec.Extractor.extract` [ArkLib/ProofSystem/Fri/Spec/Extraction/Program.lean:78](../../../ArkLib/ProofSystem/Fri/Spec/Extraction/Program.lean#L78) — Extract from the retained prefix of a full transcript.

### `mono` (4 declarations, 3 files)

- `theorem Verifier.knowledgeSoundnessWithResources.mono` [ArkLib/OracleReduction/Security/Resources.lean:104](../../../ArkLib/OracleReduction/Security/Resources.lean#L104) — A resource certificate remains valid for any larger budget.
- `theorem OracleVerifier.knowledgeSoundnessWithResources.mono` [ArkLib/OracleReduction/Security/Resources.lean:161](../../../ArkLib/OracleReduction/Security/Resources.lean#L161) — A resource certificate remains valid for any larger budget.
- `theorem MvPolynomial.CoeffNatDegreeLE.mono` [ArkLib/ToMathlib/MvPolynomial/PolynomialCoefficients.lean:298](../../../ArkLib/ToMathlib/MvPolynomial/PolynomialCoefficients.lean#L298) — The degree bound can be increased.
- `theorem MvPolynomial.SupportWeightOffset.mono` [ArkLib/ToMathlib/MvPolynomial/SupportWeightOffset.lean:55](../../../ArkLib/ToMathlib/MvPolynomial/SupportWeightOffset.lean#L55) — The allowance can be increased.

### `toFinset` (4 declarations, 3 files)

- `def ReedSolomon.toFinset` [ArkLib/Data/CodingTheory/ReedSolomon.lean:118](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L118) — (no docstring)
- `def Domain.CosetFftDomainClass.toFinset` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:341](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L341) — The elements of a domain as a finset.
- `abbrev Domain.CosetFftDomain.toFinset` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:359](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L359) — The finset of elements of a concrete coset FFT domain.
- `abbrev Domain.FftDomain.toFinset` [ArkLib/Data/Domain/FftDomain/Defs.lean:168](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L168) — The finite set of field elements contained in an FFT domain.

### `Accepts` (3 declarations, 3 files)

- `def ReedSolomon.ListDecoding.Accepts` [ArkLib/Data/CodingTheory/ReedSolomon/ListSpecification.lean:45](../../../ArkLib/Data/CodingTheory/ReedSolomon/ListSpecification.lean#L45) — The Reed–Solomon acceptance predicate at an absolute agreement threshold.
- `def Fri.FoldTrace.Accepts` [ArkLib/ProofSystem/Fri/QuerySoundness.lean:93](../../../ArkLib/ProofSystem/Fri/QuerySoundness.lean#L93) — Acceptance of a fixed query vector, including the final code-membership check.
- `def ToyProblem.Spec.Accepts` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:250](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L250) — The decision predicate, factored out so completeness proofs and the verifier object share the same s

### `BadChallenge` (3 declarations, 3 files)

- `def AffineFactorBadChallenge.BadChallenge` [ArkLib/Data/Polynomial/AffineFactorBadChallenge.lean:25](../../../ArkLib/Data/Polynomial/AffineFactorBadChallenge.lean#L25) — A challenge is bad when one of the affine factors vanishes.
- `def Plonk.BadChallenge` [ArkLib/ProofSystem/Plonk/Accumulator/Basic.lean:165](../../../ArkLib/ProofSystem/Plonk/Accumulator/Basic.lean#L165) — The denominator has a zero column factor at some row.
- `def Plonk.GrandProduct.BadChallenge` [ArkLib/ProofSystem/Plonk/GrandProduct/Data.lean:234](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Data.lean#L234) — The explicit bad challenge set consists of zero denominator factors.

### `Opening` (3 declarations, 3 files)

- `structure Commitment.Opening` [ArkLib/Commitments/Functional/Basic.lean:62](../../../ArkLib/Commitments/Functional/Basic.lean#L62) — The opening protocol used to prove a claimed oracle response for committed data.
- `structure ArkLib.Lattices.Ajtai.InnerOuter.Opening` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:118](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L118) — A Hachi/Greyhound *weak opening* `(sᵢ, t̂ᵢ, cᵢ)ᵢ`: the decomposition data `(sᵢ, t̂ᵢ)` (`Decomp`) ext
- `abbrev ArkLib.Lattices.Ajtai.Simple.Opening` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:47](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L47) — The simple Ajtai commitment has no auxiliary opening data.

### `OutputStatement` (3 declarations, 3 files)

- `abbrev Sumcheck.Spec.OutputStatement` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:137](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L137) — (no docstring)
- `def ToyProblem.Spec.OutputStatement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:194](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L194) — Output statement: the IOR is a yes/no test — accept (return `()`) or short-circuit to `none` via `Op
- `def ToyProblem.SimplifiedIOR.OutputStatement` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:94](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L94) — Output statement for C6.9: the new `(v, μ_new)` pair. The constraint count drops from 2 to 1 (a sing

### `ProverState` (3 declarations, 3 files)

- `structure ProverState` [ArkLib/OracleReduction/Basic.lean:133](../../../ArkLib/OracleReduction/Basic.lean#L133) — The type signature for the prover's state at each round. For a protocol with `n` messages exchanged,
- `abbrev RingSwitching.Packing.Head.ProverState` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:157](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L157) — The honest state family at a fixed commitment oracle interface.
- `abbrev RingSwitching.Packing.ProductSumcheck.Round.ProverState` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean:76](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean#L76) — The honest state family at a fixed commitment oracle interface.

### `PublicParams` (3 declarations, 3 files)

- `structure ArkLib.Lattices.Ajtai.InnerOuter.PublicParams` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:97](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L97) — Public parameters: inner Ajtai matrix `A` and outer Ajtai matrix `B`.
- `abbrev ArkLib.Lattices.Ajtai.Simple.PublicParams` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:33](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L33) — Public parameters: the Ajtai matrix `A`.
- `structure Spartan.PublicParams` [ArkLib/ProofSystem/Spartan/Algebra/Layout.lean:33](../../../ArkLib/ProofSystem/Spartan/Algebra/Layout.lean#L33) — The base-two logarithms of the row, column, and witness dimensions.

### `Reduction` (3 declarations, 3 files)

- `structure Interaction.Oracle.Reduction` [ArkLib/Interaction/Oracle/Execution.lean:594](../../../ArkLib/Interaction/Oracle/Execution.lean#L594) — A small statement/witness wrapper around oracle strategies. The verifier is built from the public st
- `structure Interaction.Reduction` [ArkLib/Interaction/Reduction.lean:173](../../../ArkLib/Interaction/Reduction.lean#L173) — A plain dependent reduction pairs a prover and verifier for one typed interaction.
- `structure Reduction` [ArkLib/OracleReduction/Basic.lean:638](../../../ArkLib/OracleReduction/Basic.lean#L638) — An **interactive reduction** for a given protocol specification `pSpec`, and relative to oracles def

### `access` (3 declarations, 3 files)

- `def Interaction.Oracle.TypeTree.ExecutionPrefix.access` [ArkLib/Interaction/Oracle/Prefix.lean:318](../../../ArkLib/Interaction/Oracle/Prefix.lean#L318) — The canonical access signature at the stopping boundary.
- `abbrev Sumcheck.Interaction.MultivariateRound.access` [ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:35](../../../ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean#L35) — Input access extended by the actual univariate message.
- `abbrev Sumcheck.Interaction.SingleRound.access` [ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:50](../../../ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean#L50) — The two polynomial evaluation resources available after the send.

### `adapter` (3 declarations, 3 files)

- `def SendSingleWitness.adapter` [ArkLib/ProofSystem/Component/SendWitness.lean:388](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L388) — The fixed-output witness sender is the identity adapter.
- `def Plonk.SendWitness.adapter` [ArkLib/ProofSystem/Plonk/SendWitness.lean:63](../../../ArkLib/ProofSystem/Plonk/SendWitness.lean#L63) — The shared witness sender exposes the table through three evaluation-only oracles.
- `def Spartan.WitnessAttachment.adapter` [ArkLib/ProofSystem/Spartan/WitnessAttachment.lean:93](../../../ArkLib/ProofSystem/Spartan/WitnessAttachment.lean#L93) — Pad the honest witness, restrict extracted tables, and forward matrix queries.

### `batch` (3 declarations, 3 files)

- `abbrev GeneratorBatch.batch` [ArkLib/Data/Polynomial/GeneratorBatch.lean:160](../../../ArkLib/Data/Polynomial/GeneratorBatch.lean#L160) — Compute a weighted batch within the quotient zero test's polynomial budget.
- `def Plonk.Batch.batch` [ArkLib/ProofSystem/Plonk/Batch/Data.lean:35](../../../ArkLib/ProofSystem/Plonk/Batch/Data.lean#L35) — Repackage the component's actual batch with the exact inclusive residual budget.
- `def Spartan.Batching.batch` [ArkLib/ProofSystem/Spartan/Batching/Relation.lean:39](../../../ArkLib/ProofSystem/Spartan/Batching/Relation.lean#L39) — Form the second sumcheck statement from the sampled coefficients.

### `closed` (3 declarations, 3 files)

- `def Interaction.Oracle.CoreRun.closed` [ArkLib/Interaction/Oracle/CoreRun.lean:72](../../../ArkLib/Interaction/Oracle/CoreRun.lean#L72) — Close using only this run's input and sent messages. Compiler inlining keeps the output realization
- `def Interaction.Oracle.LoggedRun.closed` [ArkLib/Interaction/Oracle/LoggedRun.lean:61](../../../ArkLib/Interaction/Oracle/LoggedRun.lean#L61) — Closing uses the core's own resources; the trace is observational evidence, not a handler.
- `def Interaction.Oracle.TerminalRun.closed` [ArkLib/Interaction/Oracle/TerminalRun.lean:68](../../../ArkLib/Interaction/Oracle/TerminalRun.lean#L68) — Close accepted claims using this run's available context, preserving rejection and returned faults.

### `commitmentScheme` (3 declarations, 3 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.commitmentScheme` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:220](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L220) — The inner-outer Ajtai commitment as a `CommitmentScheme`, verified with the Hachi/Greyhound weak ver
- `def ArkLib.Lattices.Ajtai.Simple.commitmentScheme` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:60](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L60) — The simple Ajtai commitment as a `CommitmentScheme`. An opening is accepted only when the message sa
- `def SimpleRO.commitmentScheme` [ArkLib/Commitments/Ordinary/SimpleRO.lean:60](../../../ArkLib/Commitments/Ordinary/SimpleRO.lean#L60) — The simple random-oracle commitment as an (ordinary) `CommitmentScheme`. Setup samples a uniformly r

### `comp_id` (3 declarations, 3 files)

- `theorem Interaction.Oracle.NamedContext.Inclusion.comp_id` [ArkLib/Interaction/Oracle/Resource.lean:255](../../../ArkLib/Interaction/Oracle/Resource.lean#L255) — (no docstring)
- `theorem Interaction.Oracle.SourceHom.comp_id` [ArkLib/Interaction/Oracle/Source.lean:214](../../../ArkLib/Interaction/Oracle/Source.lean#L214) — (no docstring)
- `theorem ConstraintSystem.Hom.comp_id` [ArkLib/ProofSystem/ConstraintSystem/Basic.lean:159](../../../ArkLib/ProofSystem/ConstraintSystem/Basic.lean#L159) — (no docstring)

### `empty` (3 declarations, 3 files)

- `def Interaction.Oracle.NamedContext.empty` [ArkLib/Interaction/Oracle/Resource.lean:85](../../../ArkLib/Interaction/Oracle/Resource.lean#L85) — The empty named context.
- `def Interaction.Oracle.SourceCtx.empty` [ArkLib/Interaction/Oracle/Source.lean:56](../../../ArkLib/Interaction/Oracle/Source.lean#L56) — A source with no queries and no backing data.
- `def ProtocolSpec.empty` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:46](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L46) — The empty protocol specification, with no messages or challenges, written as `!p[]`.

### `escEvent` (3 declarations, 3 files)

- `def CoordinateWise.CommittedScalar.escEvent` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:193](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L193) — The tree-level escape event of a committed scalar phase: `escLocal` transported along `ScalarRound.e
- `def CoordinateWise.SingleRound.escEvent` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:450](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L450) — The tree-level escape event induced by a **local** (per-star) event `escLocal`: the tree's own messa
- `def RingSwitching.Lift.escEvent` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:213](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L213) — The switch's **escape event**: the committed-scalar collision event at this switch's output relation

### `guardedForm_check` (3 declarations, 3 files)

- `theorem RingSwitching.Packing.Head.guardedForm_check` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:188](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L188) — The guard is the scalar reconstruction check on the transmitted message.
- `theorem RingSwitching.Packing.ProductSumcheck.Round.guardedForm_check` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean:100](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean#L100) — The sumcheck guarded form checks the Boolean sum of the clear message.
- `theorem RingSwitching.Packing.ProductSumcheck.Terminal.guardedForm_check` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean:82](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean#L82) — The terminal guarded form checks the multiplier equation.

### `guardedForm_out` (3 declarations, 3 files)

- `theorem RingSwitching.Packing.Head.guardedForm_out` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:195](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L195) — The accepted output retains the input commitment oracle verbatim.
- `theorem RingSwitching.Packing.ProductSumcheck.Round.guardedForm_out` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean:107](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean#L107) — The sumcheck guarded form retains the input oracles and appends the scalar challenge.
- `theorem RingSwitching.Packing.ProductSumcheck.Terminal.guardedForm_out` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean:89](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean#L89) — The terminal guarded form forwards the evaluation and the input commitment oracles.

### `honestAccumulator` (3 declarations, 3 files)

- `def Plonk.honestAccumulator` [ArkLib/ProofSystem/Plonk/Accumulator/Basic.lean:124](../../../ArkLib/ProofSystem/Plonk/Accumulator/Basic.lean#L124) — Interpolate the ratio prefixes. Mathlib's polynomial interpolation is noncomputable.
- `def Plonk.Computable.honestAccumulator` [ArkLib/ProofSystem/Plonk/Accumulator/Computable.lean:51](../../../ArkLib/ProofSystem/Plonk/Accumulator/Computable.lean#L51) — Interpolate the executable prefix products of numerator-to-denominator ratios.
- `def Plonk.GrandProduct.honestAccumulator` [ArkLib/ProofSystem/Plonk/GrandProduct/Data.lean:196](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Data.lean#L196) — Compute the honest normalized accumulator by interpolating ratio prefixes.

### `id_comp` (3 declarations, 3 files)

- `theorem Interaction.Oracle.NamedContext.Inclusion.id_comp` [ArkLib/Interaction/Oracle/Resource.lean:252](../../../ArkLib/Interaction/Oracle/Resource.lean#L252) — (no docstring)
- `theorem Interaction.Oracle.SourceHom.id_comp` [ArkLib/Interaction/Oracle/Source.lean:209](../../../ArkLib/Interaction/Oracle/Source.lean#L209) — (no docstring)
- `theorem ConstraintSystem.Hom.id_comp` [ArkLib/ProofSystem/ConstraintSystem/Basic.lean:157](../../../ArkLib/ProofSystem/ConstraintSystem/Basic.lean#L157) — (no docstring)

### `injective` (3 declarations, 3 files)

- `lemma Domain.CosetFftDomain.injective` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:323](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L323) — A concrete coset FFT domain is injective as a function.
- `lemma Domain.FftDomain.injective` [ArkLib/Data/Domain/FftDomain/Defs.lean:152](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L152) — An FFT domain is injective as a function.
- `theorem Interaction.Oracle.NamedContext.Inclusion.injective` [ArkLib/Interaction/Oracle/Resource.lean:229](../../../ArkLib/Interaction/Oracle/Resource.lean#L229) — A name-preserving inclusion is injective.

### `intermediateWitness` (3 declarations, 3 files)

- `def Spartan.Assembly.intermediateWitness` [ArkLib/ProofSystem/Spartan/Security.lean:41](../../../ArkLib/ProofSystem/Spartan/Security.lean#L41) — The intermediate witness families of the seven certificates. The sumcheck families are selected from
- `def Spartan.FirstSumcheck.intermediateWitness` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:370](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L370) — The retained terminal witness paired with the chosen inner sumcheck witness family.
- `def Spartan.SecondSumcheck.intermediateWitness` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:373](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L373) — The retained terminal witness paired with the chosen inner sumcheck witness family.

### `map` (3 declarations, 3 files)

- `def Fin.map` [ArkLib/Data/Fin/Sigma.lean:500](../../../ArkLib/Data/Fin/Sigma.lean#L500) — (no docstring)
- `def PolynomialDifferential.JetPrefixPresentation.map` [ArkLib/Data/Polynomial/Differential/JetPrefixPresentation.lean:200](../../../ArkLib/Data/Polynomial/Differential/JetPrefixPresentation.lean#L200) — Mapping coefficients along `φ` maps a presentation of `Q` to a presentation of `Q.map φ`.
- `def Interaction.Oracle.Terminal.map` [ArkLib/Interaction/Oracle/Terminal.lean:39](../../../ArkLib/Interaction/Oracle/Terminal.lean#L39) — Transform accepted claims, preserving rejection and faults.

### `nextStatement` (3 declarations, 3 files)

- `def RingSwitching.Packing.Head.nextStatement` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:86](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L86) — The output is computed from the public transpose, without another prover message.
- `def RingSwitching.Packing.ProductSumcheck.Round.nextStatement` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean:50](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean#L50) — Append the sampled scalar and set the next target to the received polynomial's evaluation.
- `def RingSwitching.Packing.ProductSumcheck.Terminal.nextStatement` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean:44](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean#L44) — Preserve the complete challenge point and forward the packed evaluation itself.

### `observe` (3 declarations, 3 files)

- `def Interaction.Oracle.PhasedResult.observe` [ArkLib/Interaction/Oracle/PhasedExecution.lean:61](../../../ArkLib/Interaction/Oracle/PhasedExecution.lean#L61) — Forget the world segmentation while retaining all source-run observations.
- `def Interaction.Oracle.Terminal.observe` [ArkLib/Interaction/Oracle/TerminalMeasure.lean:31](../../../ArkLib/Interaction/Oracle/TerminalMeasure.lean#L31) — Observe terminal outcomes after explicitly assigning execution missing mass a named fault.
- `def RingSwitching.Packing.PackingData.observe` [ArkLib/ProofSystem/RingSwitching/Packing/FiniteObservation.lean:28](../../../ArkLib/ProofSystem/RingSwitching/Packing/FiniteObservation.lean#L28) — Observe each packing coordinate of a finite table using opening-algebra weights.

### `oracleProver_eq` (3 declarations, 3 files)

- `theorem Spartan.FirstSumcheck.oracleProver_eq` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:184](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L184) — The executable honest prover agrees with the lifted sumcheck specification.
- `theorem Spartan.SecondSumcheck.oracleProver_eq` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:206](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L206) — The executable honest prover is the specified prover lifted to the Spartan context.
- `theorem Sumcheck.Impl.Computable.oracleProver_eq` [ArkLib/ProofSystem/Sumcheck/Impl/OracleProver.lean:84](../../../ArkLib/ProofSystem/Sumcheck/Impl/OracleProver.lean#L84) — The executable honest round prover refines the existing oracle reduction exactly.

### `oracleVerifier_eq_liftContext` (3 declarations, 3 files)

- `theorem Spartan.FirstSumcheck.oracleVerifier_eq_liftContext` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:110](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L110) — The implemented verifier is exactly the executable virtual-polynomial context lift.
- `theorem Spartan.SecondSumcheck.oracleVerifier_eq_liftContext` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:166](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L166) — The executable verifier is exactly the named context lift of the general sumcheck.
- `theorem Sumcheck.Spec.SingleRound.oracleVerifier_eq_liftContext` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:893](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L893) — The message-only verifier agrees exactly with the virtual-polynomial context lift.

### `oracleVerifier_knowledgeSoundnessWith` (3 declarations, 3 files)

- `theorem QuotientZeroTest.oracleVerifier_knowledgeSoundnessWith` [ArkLib/ProofSystem/Component/QuotientZeroTest.lean:264](../../../ArkLib/ProofSystem/Component/QuotientZeroTest.lean#L264) — The guarded bridge gives ordinary knowledge soundness with the named backward-fold extractor. There
- `theorem Plonk.Assembly.Circuit.oracleVerifier_knowledgeSoundnessWith` [ArkLib/ProofSystem/Plonk/Assembly/CircuitExtraction.lean:93](../../../ArkLib/ProofSystem/Plonk/Assembly/CircuitExtraction.lean#L93) — The revealed-table decoder extracts the original circuit witness with error `(7(ℓ + n) - 3) / \|F\|`,
- `theorem Plonk.Assembly.oracleVerifier_knowledgeSoundnessWith` [ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean:310](../../../ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean#L310) — Ordinary knowledge security with the designated table extractor and exact total error.

### `outputRelation_iff` (3 declarations, 3 files)

- `theorem Plonk.GrandProduct.outputRelation_iff` [ArkLib/ProofSystem/Plonk/GrandProduct/Data.lean:240](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Data.lean#L240) — All residuals vanish precisely when gates vanish and the accumulator is normalized and satisfies the
- `theorem Spartan.FirstSumcheck.outputRelation_iff` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:142](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L142) — The final sumcheck relation is polynomial evaluation at its returned challenge vector.
- `theorem Spartan.SecondSumcheck.outputRelation_iff` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:99](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L99) — The final inner relation is the terminal evaluation equation for the retained batch.

### `proverContextLens` (3 declarations, 3 files)

- `def Spartan.FirstSumcheck.proverContextLens` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:163](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L163) — The prover projects the computed virtual polynomial and retains the original tables.
- `def Spartan.SecondSumcheck.proverContextLens` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:185](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L185) — The prover's context projection computes the polynomial from the original tables.
- `def Sumcheck.Impl.Computable.proverContextLens` [ArkLib/ProofSystem/Sumcheck/Impl/OracleProver.lean:47](../../../ArkLib/ProofSystem/Sumcheck/Impl/OracleProver.lean#L47) — Context projection uses the finite-support implementation of the honest message.

### `proverForOracles` (3 declarations, 3 files)

- `def RingSwitching.Packing.Head.proverForOracles` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:140](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L140) — The honest round algorithm depends only on the oracle family, independently of compatibility.
- `def RingSwitching.Packing.ProductSumcheck.Round.proverForOracles` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean:61](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean#L61) — The honest round algorithm depends only on the oracle family, independently of compatibility.
- `def RingSwitching.Packing.ProductSumcheck.Terminal.proverForOracles` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean:48](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean#L48) — The honest prover preserves the packed polynomial and commitment oracle.

### `prover_run` (3 declarations, 3 files)

- `theorem RingSwitching.Packing.Head.prover_run` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:240](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L240) — Exact honest execution of the two-round prover, before materializing its fresh challenge.
- `theorem RingSwitching.Packing.ProductSumcheck.Round.prover_run` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/RoundExecution.lean:29](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/RoundExecution.lean#L29) — The honest prover samples one challenge and records the round transcript.
- `theorem RingSwitching.Packing.ProductSumcheck.Terminal.prover_run` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean:139](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean#L139) — Honest execution sends the challenge-algebra evaluation and preserves the packed witness.

### `publicInputPolynomial` (3 declarations, 3 files)

- `def Plonk.Assembly.publicInputPolynomial` [ArkLib/ProofSystem/Plonk/Assembly/Data.lean:35](../../../ArkLib/ProofSystem/Plonk/Assembly/Data.lean#L35) — The public-input contribution encoded in executable coefficients.
- `def Plonk.publicInputPolynomial` [ArkLib/ProofSystem/Plonk/Encoding/Basic.lean:138](../../../ArkLib/ProofSystem/Plonk/Encoding/Basic.lean#L138) — The public-input polynomial is negative input on reserved rows and zero elsewhere. It uses Mathlib's
- `def Plonk.Computable.publicInputPolynomial` [ArkLib/ProofSystem/Plonk/Encoding/Computable.lean:68](../../../ArkLib/ProofSystem/Plonk/Encoding/Computable.lean#L68) — Encode the public-input contribution on the reserved rows.

### `queryInput` (3 declarations, 3 files)

- `def BatchedFri.Spec.BatchingRound.queryInput` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:131](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L131) — Query one batched input codeword in the verifier's full oracle context.
- `def GeneratorBatch.queryInput` [ArkLib/ProofSystem/Component/GeneratorBatch.lean:70](../../../ArkLib/ProofSystem/Component/GeneratorBatch.lean#L70) — Query one member of the fixed input family.
- `def ToyProblem.SimplifiedIOR.queryInput` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:250](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L250) — Query an input codeword at one coordinate in the full verifier oracle context.

### `quotient` (3 declarations, 3 files)

- `def Polynomial.Bivariate.quotient` [ArkLib/Data/Polynomial/Bivariate.lean:140](../../../ArkLib/Data/Polynomial/Bivariate.lean#L140) — The bivariate quotient polynomial.
- `def FiniteDomainQuotient.quotient` [ArkLib/Data/Polynomial/FiniteDomainQuotient.lean:149](../../../ArkLib/Data/Polynomial/FiniteDomainQuotient.lean#L149) — Monic division computes a quotient within the remaining degree budget.
- `def RingSwitching.Lift.Presentation.quotient` [ArkLib/ProofSystem/RingSwitching/Lift/Presentation.lean:297](../../../ArkLib/ProofSystem/RingSwitching/Lift/Presentation.lean#L297) — The **honest quotient** of row `i`: the explicit polynomial `ρ := (rowSum − rep yᵢ) /ₘ φ` that witne

### `reduction_run` (3 declarations, 3 files)

- `theorem Fri.Spec.reduction_run` [ArkLib/ProofSystem/Fri/Spec/VerifierExecution.lean:167](../../../ArkLib/ProofSystem/Fri/Spec/VerifierExecution.lean#L167) — Exact rejection semantics of the existing complete FRI reduction.
- `theorem RingSwitching.Packing.ProductSumcheck.Round.reduction_run` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/RoundExecution.lean:51](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/RoundExecution.lean#L51) — The whole reduction preserves the checked verdict and the original oracle collection.
- `theorem RingSwitching.Packing.ProductSumcheck.Terminal.reduction_run` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean:157](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean#L157) — Complete execution retains failure and the true forwarded value.

### `rel` (3 declarations, 3 files)

- `def CoordinateWise.CommittedScalar.rel` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:132](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L132) — The anchored output relation for a committed scalar phase. The framework fixes commitment consistenc
- `def Plonk.Assembly.rel` [ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean:98](../../../ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean#L98) — The exact gate/copy, residual, batch and accepting relations.
- `def RingSwitching.Packing.ProductSumcheck.rel` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Basic.lean:68](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Basic.lean#L68) — The exact residual-sum relation at a fixed challenge prefix.

### `simulateQ_queryInput` (3 declarations, 3 files)

- `theorem BatchedFri.Spec.BatchingRound.simulateQ_queryInput` [ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean:139](../../../ArkLib/ProofSystem/BatchedFri/Spec/SingleRound.lean#L139) — (no docstring)
- `theorem GeneratorBatch.simulateQ_queryInput` [ArkLib/ProofSystem/Component/GeneratorBatch.lean:78](../../../ArkLib/ProofSystem/Component/GeneratorBatch.lean#L78) — Input simulation evaluates the corresponding computable polynomial.
- `theorem ToyProblem.SimplifiedIOR.simulateQ_queryInput` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:259](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L259) — (no docstring)

### `transcript` (3 declarations, 3 files)

- `def ProtocolSpec.ChallengeTree.LeafPath.transcript` [ArkLib/OracleReduction/Security/TranscriptTree/Basic.lean:195](../../../ArkLib/OracleReduction/Security/TranscriptTree/Basic.lean#L195) — Read the full transcript selected by a leaf path, extending an already-accumulated prefix.
- `def SendSingleWitness.Adapter.transcript` [ArkLib/ProofSystem/Component/SendWitness.lean:247](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L247) — The full transcript consisting of one sent message.
- `def RingSwitching.Packing.ProductSumcheck.Terminal.transcript` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean:136](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean#L136) — The sole-message transcript.

### `transcriptExtractor` (3 declarations, 3 files)

- `def SendSingleWitness.transcriptExtractor` [ArkLib/ProofSystem/Component/SendWitness.lean:217](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L217) — Transcript extraction depends only on the decoder, without any oracle interface.
- `def Plonk.Assembly.Circuit.transcriptExtractor` [ArkLib/ProofSystem/Plonk/Assembly/CircuitExtraction.lean:38](../../../ArkLib/ProofSystem/Plonk/Assembly/CircuitExtraction.lean#L38) — Decode the exact polynomial table revealed at the start of the transcript.
- `def Plonk.Assembly.transcriptExtractor` [ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean:298](../../../ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean#L298) — The ordinary extractor returns the exact initially revealed table.

### `prEvent_eq_evalDist_map_unifSpec` (3 declarations, 3 files)

- `theorem Sumcheck.Interaction.SingleRound.prEvent_eq_evalDist_map_unifSpec` [ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:268](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean#L268) — `prEvent_eq_evalDist_map` at `OracleComp unifSpec`, stated so that the `Pr{...}` side uses the same
- `theorem Sumcheck.Interaction.MultivariateRound.prEvent_eq_evalDist_map_unifSpec` [ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateSoundness.lean:104](../../../ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateSoundness.lean#L104) — (no docstring)
- `theorem Sumcheck.Interaction.SingleRound.prEvent_eq_evalDist_map_unifSpec` [ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean:118](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Soundness.lean#L118) — `prEvent_eq_evalDist_map` at `OracleComp unifSpec`, stated so that the `Pr{...}` side uses the same

### `cast_id` (11 declarations, 2 files)

- `theorem Prover.cast_id` [ArkLib/OracleReduction/Cast.lean:63](../../../ArkLib/OracleReduction/Cast.lean#L63) — (no docstring)
- `theorem OracleProver.cast_id` [ArkLib/OracleReduction/Cast.lean:95](../../../ArkLib/OracleReduction/Cast.lean#L95) — (no docstring)
- `theorem Verifier.cast_id` [ArkLib/OracleReduction/Cast.lean:117](../../../ArkLib/OracleReduction/Cast.lean#L117) — (no docstring)
- `theorem OracleVerifier.cast_id` [ArkLib/OracleReduction/Cast.lean:164](../../../ArkLib/OracleReduction/Cast.lean#L164) — Casting an oracle verifier along reflexive equalities leaves it unchanged.
- `theorem Reduction.cast_id` [ArkLib/OracleReduction/Cast.lean:201](../../../ArkLib/OracleReduction/Cast.lean#L201) — (no docstring)
- `theorem OracleReduction.cast_id` [ArkLib/OracleReduction/Cast.lean:230](../../../ArkLib/OracleReduction/Cast.lean#L230) — Casting an oracle reduction along reflexive equalities leaves it unchanged.
- `theorem ProtocolSpec.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:39](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L39) — (no docstring)
- `theorem ProtocolSpec.MessageIdx.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:83](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L83) — (no docstring)
- `theorem ProtocolSpec.ChallengeIdx.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:121](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L121) — (no docstring)
- `theorem ProtocolSpec.Transcript.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:164](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L164) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.cast_id` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:207](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L207) — (no docstring)

### `seqCompose` (9 declarations, 2 files)

- `def Prover.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:47](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L47) — Sequential composition of provers, defined via iteration of the composition (append) of two provers.
- `def Verifier.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:115](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L115) — Sequential composition of verifiers, defined via iteration of the composition (append) of two verifi
- `def Extractor.RoundByRound.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:185](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L185) — Fold round-by-round extractors along the guarded outputs, with the identity at the end.
- `def Reduction.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:234](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L234) — Sequential composition of reductions, defined via sequential composition of provers and verifiers (o
- `def OracleProver.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:265](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L265) — Sequential composition of provers in oracle reductions, defined via sequential composition of prover
- `def OracleVerifier.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:312](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L312) — Sequential composition of oracle verifiers (in oracle reductions), defined via iteration of the comp
- `def OracleReduction.seqCompose` [ArkLib/OracleReduction/Composition/Sequential/General.lean:483](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L483) — Sequential composition of oracle reductions, defined via sequential composition of oracle provers an
- `def ProtocolSpec.seqCompose` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:362](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L362) — Sequential composition of a family of `ProtocolSpec`s, indexed by `i : Fin m`. Defined for definitio
- `def ProtocolSpec.FullTranscript.seqCompose` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:420](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L420) — Sequential composition of a family of `FullTranscript`s, indexed by `i : Fin m`. Defined for definit

### `lift` (7 declarations, 2 files)

- `def Statement.Lens.lift` [ArkLib/OracleReduction/LiftContext/Lens.lean:57](../../../ArkLib/OracleReduction/LiftContext/Lens.lean#L57) — Transport output statements from the inner context to the outer context, additionally relying on the
- `def OracleStatement.Lens.lift` [ArkLib/OracleReduction/LiftContext/Lens.lean:119](../../../ArkLib/OracleReduction/LiftContext/Lens.lean#L119) — Transport output statements from the inner context to the outer context, additionally relying on the
- `def Witness.Lens.lift` [ArkLib/OracleReduction/LiftContext/Lens.lean:235](../../../ArkLib/OracleReduction/LiftContext/Lens.lean#L235) — Transport output witness from the inner context to the outer context, additionally relying on the in
- `def Context.Lens.lift` [ArkLib/OracleReduction/LiftContext/Lens.lean:261](../../../ArkLib/OracleReduction/LiftContext/Lens.lean#L261) — Lifting of the context.
- `def OracleContext.Lens.lift` [ArkLib/OracleReduction/LiftContext/Lens.lean:299](../../../ArkLib/OracleReduction/LiftContext/Lens.lean#L299) — Lifting of the context.
- `def Witness.InvLens.lift` [ArkLib/OracleReduction/LiftContext/Lens.lean:384](../../../ArkLib/OracleReduction/LiftContext/Lens.lean#L384) — Lifting of the witness.
- `theorem ProtocolSpec.OrderedChallenges.lift` [ArkLib/OracleReduction/Security/ChallengePresampling.lean:70](../../../ArkLib/OracleReduction/Security/ChallengePresampling.lean#L70) — Lifting ambient queries adds no challenge calls.

### `seqCompose_zero` (7 declarations, 2 files)

- `lemma Prover.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:58](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L58) — (no docstring)
- `lemma Verifier.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:123](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L123) — (no docstring)
- `lemma Reduction.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:243](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L243) — (no docstring)
- `lemma OracleVerifier.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:326](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L326) — (no docstring)
- `lemma OracleReduction.seqCompose_zero` [ArkLib/OracleReduction/Composition/Sequential/General.lean:499](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L499) — (no docstring)
- `theorem ProtocolSpec.seqCompose_zero` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:378](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L378) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.seqCompose_zero` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:425](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L425) — (no docstring)

### `concat` (5 declarations, 2 files)

- `def ProtocolSpec.MessagesUpTo.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:409](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L409) — Concatenate the `k`-th message to the end of the tuple of messages up to round `k`, assuming round `
- `def ProtocolSpec.ChallengesUpTo.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:468](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L468) — Concatenate the `k`-th challenge to the end of the tuple of challenges up to round `k`, assuming rou
- `abbrev ProtocolSpec.Transcript.concat` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:513](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L513) — Concatenate a message to the end of a partial transcript. This is definitionally equivalent to `Fin.
- `abbrev ProtocolSpec.concat` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:34](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L34) — Concatenate a round with direction `dir` and type `Message` to the end of a `ProtocolSpec`
- `def ProtocolSpec.FullTranscript.concat` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:179](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L179) — Adding a message with a given direction and type to the end of a `Transcript`

### `cast_eq_dcast₂` (4 declarations, 2 files)

- `theorem Verifier.cast_eq_dcast₂` [ArkLib/OracleReduction/Cast.lean:125](../../../ArkLib/OracleReduction/Cast.lean#L125) — (no docstring)
- `theorem ProtocolSpec.MessageIdx.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:94](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L94) — (no docstring)
- `theorem ProtocolSpec.ChallengeIdx.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:132](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L132) — (no docstring)
- `theorem ProtocolSpec.FullTranscript.cast_eq_dcast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:213](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L213) — (no docstring)

### `instDCast₂` (4 declarations, 2 files)

- `instance Prover.instDCast₂` [ArkLib/OracleReduction/Cast.lean:77](../../../ArkLib/OracleReduction/Cast.lean#L77) — (no docstring)
- `instance ProtocolSpec.MessageIdx.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:90](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L90) — (no docstring)
- `instance ProtocolSpec.ChallengeIdx.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:128](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L128) — (no docstring)
- `instance ProtocolSpec.FullTranscript.instDCast₂` [ArkLib/OracleReduction/ProtocolSpec/Cast.lean:209](../../../ArkLib/OracleReduction/ProtocolSpec/Cast.lean#L209) — (no docstring)

### `subdomain` (4 declarations, 2 files)

- `def Domain.CosetFftDomainClass.subdomain` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:126](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L126) — Given a smooth coset FFT domain `ω` of log-order `n`, return its subdomain of log-order `n - i`. The
- `abbrev Domain.CosetFftDomain.subdomain` [ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean:539](../../../ArkLib/Data/Domain/CosetFftDomain/Subdomain.lean#L539) — Concrete notation for taking the `i`th subdomain of a smooth coset FFT domain.
- `def Domain.FftDomainClass.subdomain` [ArkLib/Data/Domain/FftDomain/Subdomain.lean:64](../../../ArkLib/Data/Domain/FftDomain/Subdomain.lean#L64) — The `i`th subdomain of a smooth FFT domain, obtained by taking the corresponding coset subdomain and
- `abbrev Domain.FftDomain.subdomain` [ArkLib/Data/Domain/FftDomain/Subdomain.lean:142](../../../ArkLib/Data/Domain/FftDomain/Subdomain.lean#L142) — Concrete notation for the `i`th subdomain of a smooth FFT domain.

### `Adversary` (3 declarations, 2 files)

- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.Adversary` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean:111](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean#L111) — A weak-binding adversary outputs two weak openings for the same commitment.
- `abbrev ArkLib.Lattices.SIS.Adversary` [ArkLib/Data/Lattices/ModuleSIS.lean:61](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L61) — A search adversary for a SIS-style problem.
- `abbrev ArkLib.Lattices.ModuleSIS.Adversary` [ArkLib/Data/Lattices/ModuleSIS.lean:104](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L104) — A Module-SIS adversary.

### `advantage` (3 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.advantage` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean:428](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean#L428) — Weak-binding advantage.
- `def ArkLib.Lattices.SIS.advantage` [ArkLib/Data/Lattices/ModuleSIS.lean:70](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L70) — Search advantage for a SIS-style problem.
- `def ArkLib.Lattices.ModuleSIS.advantage` [ArkLib/Data/Lattices/ModuleSIS.lean:116](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L116) — The Module-SIS advantage.

### `correctness` (3 declarations, 2 files)

- `def Commitment.correctness` [ArkLib/Commitments/Functional/Basic.lean:93](../../../ArkLib/Commitments/Functional/Basic.lean#L93) — A commitment scheme satisfies **correctness** with error `correctnessError` if for all `data : Data`
- `theorem KZG.correctness` [ArkLib/Commitments/Functional/KZG/Correctness.lean:59](../../../ArkLib/Commitments/Functional/KZG/Correctness.lean#L59) — Algebraic correctness of one KZG opening for a coefficient vector.
- `theorem KZG.CommitmentScheme.correctness` [ArkLib/Commitments/Functional/KZG/Correctness.lean:169](../../../ArkLib/Commitments/Functional/KZG/Correctness.lean#L169) — The KZG scheme satisfies perfect correctness as defined in `CommitmentScheme`.

### `execute` (3 declarations, 2 files)

- `abbrev Sumcheck.Interaction.Computable.execute` [ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean:42](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Computable.lean#L42) — Actual execution of any ordinary prover sending computable messages.
- `def Sumcheck.Interaction.Native.Core.execute` [ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:123](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean#L123) — Execute and close the full interaction, retaining its actual paired source handler.
- `def Sumcheck.Interaction.Native.execute` [ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:351](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean#L351) — Close execution of the mathematical specialization.

### `experiment` (3 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.WeakBinding.experiment` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean:415](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Security.lean#L415) — The Hachi/Greyhound weak-binding experiment. ## Ordinary vs. weak binding *Ordinary (exact) binding*
- `def ArkLib.Lattices.SIS.experiment` [ArkLib/Data/Lattices/ModuleSIS.lean:64](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L64) — The SIS experiment: sample a challenge, run the adversary, check validity.
- `def ArkLib.Lattices.ModuleSIS.experiment` [ArkLib/Data/Lattices/ModuleSIS.lean:110](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L110) — The Module-SIS experiment.

### `extend` (3 declarations, 2 files)

- `def Interaction.Oracle.Access.extend` [ArkLib/Interaction/Oracle/Access.lean:44](../../../ArkLib/Interaction/Oracle/Access.lean#L44) — Add a disjoint query slot for a newly sent oracle message. This is signature extension, not a claim
- `def ProtocolSpec.MessagesUpTo.extend` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:417](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L417) — Extend the tuple of messages up to round `k` to up to round `k + 1`, assuming round `k` is a challen
- `def ProtocolSpec.ChallengesUpTo.extend` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:476](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L476) — Extend the tuple of challenges up to round `k` to up to round `k + 1`, assuming round `k` is a messa

### `instIsEmptyChallengeIdx` (3 declarations, 2 files)

- `instance SendClaim.instIsEmptyChallengeIdx` [ArkLib/ProofSystem/Component/SendClaim.lean:70](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L70) — `SendClaim` is a single `P_to_V` message, so it has no challenge rounds. This makes its coordinate-w
- `instance SendWitness.instIsEmptyChallengeIdx` [ArkLib/ProofSystem/Component/SendWitness.lean:70](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L70) — The `SendWitness` protocol is a single `P_to_V` message, so it has no challenge rounds. This is what
- `instance SendSingleWitness.instIsEmptyChallengeIdx` [ArkLib/ProofSystem/Component/SendWitness.lean:213](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L213) — The `SendSingleWitness` protocol is a single `P_to_V` message, so it has no challenge rounds. This i

### `mem_toFinset_iff_mem` (3 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.mem_toFinset_iff_mem` [ArkLib/Data/Domain/CosetFftDomain/Mem.lean:85](../../../ArkLib/Data/Domain/CosetFftDomain/Mem.lean#L85) — Membership in the finset of elements is the same as membership in the coset FFT domain.
- `lemma Domain.CosetFftDomain.mem_toFinset_iff_mem` [ArkLib/Data/Domain/CosetFftDomain/Mem.lean:147](../../../ArkLib/Data/Domain/CosetFftDomain/Mem.lean#L147) — Membership in the finset of elements is the same as membership in the concrete coset FFT domain.
- `lemma Domain.FftDomain.mem_toFinset_iff_mem` [ArkLib/Data/Domain/FftDomain/Mem.lean:88](../../../ArkLib/Data/Domain/FftDomain/Mem.lean#L88) — Membership in the finset of elements is the same as membership in the FFT domain.

### `rdrop` (3 declarations, 2 files)

- `abbrev Fin.rdrop` [ArkLib/Data/Fin/Tuple/Defs.lean:71](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L71) — Drop the last `m` elements of an `n`-tuple where `m ≤ n`, returning an `(n - m)`-tuple. This is defi
- `def ProtocolSpec.rdrop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:125](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L125) — Drop the last `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.rdrop` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:182](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L182) — (no docstring)

### `restrict_comp` (3 declarations, 2 files)

- `theorem Interaction.Oracle.TypeTree.AccessDecoration.restrict_comp` [ArkLib/Interaction/Oracle/Access.lean:329](../../../ArkLib/Interaction/Oracle/Access.lean#L329) — Restriction composes without introducing another cursor representation.
- `theorem Interaction.Oracle.TypeTree.RoleDecoration.restrict_comp` [ArkLib/Interaction/Oracle/TypeTree/Decoration.lean:100](../../../ArkLib/Interaction/Oracle/TypeTree/Decoration.lean#L100) — (no docstring)
- `theorem Interaction.Oracle.TypeTree.OracleDecoration.restrict_comp` [ArkLib/Interaction/Oracle/TypeTree/Decoration.lean:252](../../../ArkLib/Interaction/Oracle/TypeTree/Decoration.lean#L252) — (no docstring)

### `restrict_down` (3 declarations, 2 files)

- `theorem Interaction.Oracle.TypeTree.AccessDecoration.restrict_down` [ArkLib/Interaction/Oracle/Access.lean:321](../../../ArkLib/Interaction/Oracle/Access.lean#L321) — (no docstring)
- `theorem Interaction.Oracle.TypeTree.RoleDecoration.restrict_down` [ArkLib/Interaction/Oracle/TypeTree/Decoration.lean:92](../../../ArkLib/Interaction/Oracle/TypeTree/Decoration.lean#L92) — (no docstring)
- `theorem Interaction.Oracle.TypeTree.OracleDecoration.restrict_down` [ArkLib/Interaction/Oracle/TypeTree/Decoration.lean:244](../../../ArkLib/Interaction/Oracle/TypeTree/Decoration.lean#L244) — (no docstring)

### `restrict_root` (3 declarations, 2 files)

- `theorem Interaction.Oracle.TypeTree.AccessDecoration.restrict_root` [ArkLib/Interaction/Oracle/Access.lean:316](../../../ArkLib/Interaction/Oracle/Access.lean#L316) — (no docstring)
- `theorem Interaction.Oracle.TypeTree.RoleDecoration.restrict_root` [ArkLib/Interaction/Oracle/TypeTree/Decoration.lean:87](../../../ArkLib/Interaction/Oracle/TypeTree/Decoration.lean#L87) — (no docstring)
- `theorem Interaction.Oracle.TypeTree.OracleDecoration.restrict_root` [ArkLib/Interaction/Oracle/TypeTree/Decoration.lean:239](../../../ArkLib/Interaction/Oracle/TypeTree/Decoration.lean#L239) — (no docstring)

### `rtake` (3 declarations, 2 files)

- `def Fin.rtake` [ArkLib/Data/Fin/Tuple/Defs.lean:58](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L58) — Take the last `m` elements of a finite vector
- `def ProtocolSpec.rtake` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:117](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L117) — Take the last `m ≤ n` rounds of a `ProtocolSpec n`
- `abbrev ProtocolSpec.FullTranscript.rtake` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:174](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L174) — Take the last `m ≤ n` rounds of a (full) transcript for a protocol specification `pSpec`

### `CandidateCertificate` (2 declarations, 2 files)

- `structure ReedSolomon.ListDecoding.CandidateCertificate` [ArkLib/Data/CodingTheory/ReedSolomon/ListSpecification.lean:75](../../../ArkLib/Data/CodingTheory/ReedSolomon/ListSpecification.lean#L75) — A certified ambient polynomial candidate generator. It may return false positives, but it contains e
- `structure Finset.CandidateCertificate` [ArkLib/Data/Finset/Enumeration.lean:48](../../../ArkLib/Data/Finset/Enumeration.lean#L48) — A finite ambient candidate generator containing every embedded accepted output.

### `Challenge` (2 declarations, 2 files)

- `def Interaction.Oracle.Security.StateRestoration.Key.Challenge` [ArkLib/Interaction/Oracle/Security/StateRestoration.lean:91](../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L91) — The answer type is the challenge alphabet of the key's round.
- `def ProtocolSpec.Challenge` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:77](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L77) — The type of the `i`-th challenge in a protocol specification

### `ChallengeIdx` (2 declarations, 2 files)

- `def ProtocolSpec.ChallengeIdx` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:57](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L57) — Subtype of `Fin n` for the indices corresponding to challenges in a protocol specification
- `def ProtocolSpec.VectorSpec.ChallengeIdx` [ArkLib/OracleReduction/VectorIOR.lean:57](../../../ArkLib/OracleReduction/VectorIOR.lean#L57) — The type of indices for challenges in a `VectorSpec`.

### `ChallengeSchedule` (2 declarations, 2 files)

- `def Interaction.Oracle.Security.RoundExtractor.ChallengeSchedule` [ArkLib/Interaction/Oracle/Security/Knowledge.lean:347](../../../ArkLib/Interaction/Oracle/Security/Knowledge.lean#L347) — Fresh-challenge programs and local errors at verifier nodes; prover choices and concrete oracle mess
- `def Interaction.Oracle.Security.ChallengeSchedule` [ArkLib/Interaction/Oracle/Security/RoundByRound.lean:111](../../../ArkLib/Interaction/Oracle/Security/RoundByRound.lean#L111) — All authored branches have at most `count` challenges; only verifier moves increase rank.

### `Commitment` (2 declarations, 2 files)

- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.Commitment` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean:146](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Scheme.lean#L146) — Inner-outer commitments live in the outer row space.
- `abbrev ArkLib.Lattices.Ajtai.Simple.Commitment` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:39](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L39) — Commitments: row vectors over `Rq Φ`.

### `ConstraintSystem` (2 declarations, 2 files)

- `structure ConstraintSystem` [ArkLib/ProofSystem/ConstraintSystem/Basic.lean:49](../../../ArkLib/ProofSystem/ConstraintSystem/Basic.lean#L49) — A promise-free problem with public contexts and claims split into clear and oracle data.
- `def Plonk.ConstraintSystem` [ArkLib/ProofSystem/ConstraintSystem/Plonk.lean:116](../../../ArkLib/ProofSystem/ConstraintSystem/Plonk.lean#L116) — A Plonk constraint system is a vector of `numGates` gates, each parametrized by the underlying ring

### `Context` (2 declarations, 2 files)

- `def Interaction.Oracle.Verifier.Context` [ArkLib/Interaction/Oracle/Execution.lean:49](../../../ArkLib/Interaction/Oracle/Execution.lean#L49) — Role, interface, and pre-move query signature at a structural node. The interface describes post-rec
- `abbrev Binius.FRIBinius.RingSwitch.Context` [ArkLib/ProofSystem/Binius/FRIBinius/RingSwitch.lean:48](../../../ArkLib/ProofSystem/Binius/FRIBinius/RingSwitch.lean#L48) — The source query and batching challenge retained until the opening frontier.

### `Generator` (2 declarations, 2 files)

- `abbrev CoreDefinitions.Generator` [ArkLib/Data/CodingTheory/ProximityGenerator/Basic.lean:66](../../../ArkLib/Data/CodingTheory/ProximityGenerator/Basic.lean#L66) — The type of generators, where a generator `G` over a field `F` with output size `ℓ` is a function th
- `structure Fri.Spec.Extractor.Generator` [ArkLib/ProofSystem/Fri/Spec/Extraction/Generator.lean:61](../../../ArkLib/ProofSystem/Fri/Spec/Extraction/Generator.lean#L61) — The two field values used to generate a smooth coset domain.

### `InnerCertificate` (2 declarations, 2 files)

- `structure Spartan.FirstSumcheck.InnerCertificate` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:345](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L345) — The data and bound furnished by the general sumcheck knowledge theorem.
- `structure Spartan.SecondSumcheck.InnerCertificate` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:348](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L348) — The data and bound furnished by the general sumcheck knowledge theorem.

### `Input` (2 declarations, 2 files)

- `abbrev Extractor.Straightline.Input` [ArkLib/OracleReduction/Security/Resources.lean:38](../../../ArkLib/OracleReduction/Security/Resources.lean#L38) — The inputs of a straightline extractor: the input statement, the output witness, the transcript, and
- `abbrev RingSwitching.Packing.Head.Input` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:60](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L60) — The original scalar evaluation query and claimed value.

### `InputStatement` (2 declarations, 2 files)

- `abbrev Spartan.Batching.InputStatement` [ArkLib/ProofSystem/Spartan/Context.lean:37](../../../ArkLib/ProofSystem/Spartan/Context.lean#L37) — The row claims and first sumcheck terminal statement, fixed before batching.
- `def Sumcheck.Spec.InputStatement` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:123](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L123) — The input statement for sum-check, which just consists of the target value for the sum

### `LiftedWitness` (2 declarations, 2 files)

- `abbrev ArkLib.Lattices.Ajtai.InnerOuter.LiftedWitness` [ArkLib/Commitments/Functional/Hachi/RingSwitch/Reduction.lean:140](../../../ArkLib/Commitments/Functional/Hachi/RingSwitch/Reduction.lean#L140) — Hachi Eq. (21)'s lifted witness: the `R^lin` witness `z ∈ Rq^μ` and one quotient polynomial per row
- `structure RingSwitching.Lift.LiftedWitness` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:84](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L84) — The lifted witness of `Lift`: the `S`-witness `z` of the linear relation and one **computable** quot

### `MeasuredProgram` (2 declarations, 2 files)

- `structure OracleComp.MeasuredProgram` [ArkLib/Data/OracleComp/MeasuredProgram.lean:53](../../../ArkLib/Data/OracleComp/MeasuredProgram.lean#L53) — A charged instruction program computing a function from `Input` to `Result`. The input is reduced to
- `abbrev Extractor.Straightline.MeasuredProgram` [ArkLib/OracleReduction/Security/Resources.lean:43](../../../ArkLib/OracleReduction/Security/Resources.lean#L43) — A measured program for a deterministic straightline extractor: a measured program on the extractor's

### `MessageIdx` (2 declarations, 2 files)

- `def ProtocolSpec.MessageIdx` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:52](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L52) — Subtype of `Fin n` for the indices corresponding to messages in a protocol specification
- `def ProtocolSpec.VectorSpec.MessageIdx` [ArkLib/OracleReduction/VectorIOR.lean:53](../../../ArkLib/OracleReduction/VectorIOR.lean#L53) — The type of indices for messages in a `VectorSpec`.

### `Messages` (2 declarations, 2 files)

- `def Interaction.Oracle.Security.StateRestoration.Messages` [ArkLib/Interaction/Oracle/Security/StateRestoration.lean:214](../../../ArkLib/Interaction/Oracle/Security/StateRestoration.lean#L214) — The complete prover-message and salt sequence returned by a restoration adversary.
- `def ProtocolSpec.Messages` [ArkLib/OracleReduction/ProtocolSpec/Basic.lean:85](../../../ArkLib/OracleReduction/ProtocolSpec/Basic.lean#L85) — The type of all messages in a protocol specification. Uncurried version of `Message`.

### `OracleState` (2 declarations, 2 files)

- `def RingSwitching.Packing.Head.OracleState` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:132](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L132) — The original source before the message, its packed polynomial afterwards, then the challenge.
- `def RingSwitching.Packing.ProductSumcheck.Round.OracleState` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean:54](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean#L54) — The first two states keep the original input and polynomial; the last also records c.

### `OutputOracleStatement` (2 declarations, 2 files)

- `def ToyProblem.Spec.OutputOracleStatement` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:198](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L198) — Output oracle statement: the IOR has no output oracle component.
- `def ToyProblem.SimplifiedIOR.OutputOracleStatement` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:99](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L99) — Output oracle statement: the single combined codeword `f_new := f₁ + γ • f₂ : ι → A`.

### `OutputWitness` (2 declarations, 2 files)

- `def ToyProblem.Spec.OutputWitness` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:205](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L205) — Output witness: empty.
- `def ToyProblem.SimplifiedIOR.OutputWitness` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:109](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L109) — Output witness for C6.9: the combined message `M_new := M₁ + γ·M₂`.

### `Params` (2 declarations, 2 files)

- `structure Poseidon2.Params` [ArkLib/Data/Hash/Poseidon2.lean:420](../../../ArkLib/Data/Hash/Poseidon2.lean#L420) — Parameters for the Poseidon2 round function over the KoalaBear field. The size and round-count condi
- `structure StirIOP.Params` [ArkLib/ProofSystem/Stir/MainThm.lean:82](../../../ArkLib/ProofSystem/Stir/MainThm.lean#L82) — **Per‑round protocol parameters:** For a fixed depth `M`, the reduction runs `M + 1` rounds. In roun

### `Poly` (2 declarations, 2 files)

- `abbrev FiniteDomainQuotient.Poly` [ArkLib/Data/Polynomial/FiniteDomainQuotient.lean:128](../../../ArkLib/Data/Polynomial/FiniteDomainQuotient.lean#L128) — A computable polynomial within an inclusive natural-degree budget.
- `abbrev GeneratorBatch.Poly` [ArkLib/Data/Polynomial/GeneratorBatch.lean:155](../../../ArkLib/Data/Polynomial/GeneratorBatch.lean#L155) — A computable polynomial within a strict natural-degree budget.

### `Problem` (2 declarations, 2 files)

- `structure ArkLib.Lattices.SIS.Problem` [ArkLib/Data/Lattices/ModuleSIS.lean:54](../../../ArkLib/Data/Lattices/ModuleSIS.lean#L54) — A generic SIS-style problem: public challenge data `Sample` (e.g. a matrix), a `Solution` type, and
- `structure Interaction.Oracle.Problem` [ArkLib/Interaction/Oracle/Claim.lean:176](../../../ArkLib/Interaction/Oracle/Claim.lean#L176) — A claim-dependent witness relation with an explicit admissibility boundary.

### `Prover` (2 declarations, 2 files)

- `abbrev Interaction.Prover` [ArkLib/Interaction/Reduction.lean:149](../../../ArkLib/Interaction/Reduction.lean#L149) — A prover performs monadic setup and returns the focal strategy for the selected input.
- `structure Prover` [ArkLib/OracleReduction/Basic.lean:223](../../../ArkLib/OracleReduction/Basic.lean#L223) — The type of honest provers for an interactive reduction with `n` messages. This consists of: - `PrvS

### `Reduction.execute` (2 declarations, 2 files)

- `def Interaction.Oracle.Reduction.execute` [ArkLib/Interaction/Oracle/Execution.lean:608](../../../ArkLib/Interaction/Oracle/Execution.lean#L608) — Execute the package with arbitrary pure input behavior. This is single-run semantics, not run-derive
- `def Interaction.Reduction.execute` [ArkLib/Interaction/Reduction.lean:186](../../../ArkLib/Interaction/Reduction.lean#L186) — Execute a reduction with PolyFun's canonical two-party runner.

### `Slot` (2 declarations, 2 files)

- `def CubicStaircase.Slot` [ArkLib/ToMathlib/Combinatorics/CubicStaircase.lean:57](../../../ArkLib/ToMathlib/Combinatorics/CubicStaircase.lean#L57) — A slot is a total degree `s < ⌈L⌉₊`, a first weight-`D` exponent `b₀ ≤ s`, and a weight-one exponent
- `def QuadraticStaircase.Slot` [ArkLib/ToMathlib/Combinatorics/QuadraticStaircase.lean:55](../../../ArkLib/ToMathlib/Combinatorics/QuadraticStaircase.lean#L55) — A slot is a weight-`D` exponent `u < ⌈L⌉₊` and a weight-one exponent `x < ⌈D * (L - u)⌉₊`.

### `Slot.exponents` (2 declarations, 2 files)

- `def CubicStaircase.Slot.exponents` [ArkLib/ToMathlib/Combinatorics/CubicStaircase.lean:73](../../../ArkLib/ToMathlib/Combinatorics/CubicStaircase.lean#L73) — The exponent triple `(x, b₀, s - b₀)` of a slot.
- `def QuadraticStaircase.Slot.exponents` [ArkLib/ToMathlib/Combinatorics/QuadraticStaircase.lean:70](../../../ArkLib/ToMathlib/Combinatorics/QuadraticStaircase.lean#L70) — The exponent pair `(x, u)` of a slot, weight-one exponent first.

### `Slot.exponents_injective` (2 declarations, 2 files)

- `theorem CubicStaircase.Slot.exponents_injective` [ArkLib/ToMathlib/Combinatorics/CubicStaircase.lean:77](../../../ArkLib/ToMathlib/Combinatorics/CubicStaircase.lean#L77) — Distinct slots have distinct exponent triples: `s` is recovered as `b₀ + b₁`.
- `theorem QuadraticStaircase.Slot.exponents_injective` [ArkLib/ToMathlib/Combinatorics/QuadraticStaircase.lean:74](../../../ArkLib/ToMathlib/Combinatorics/QuadraticStaircase.lean#L74) — Distinct slots have distinct exponent pairs.

### `Slot.weighted_degree_lt` (2 declarations, 2 files)

- `theorem CubicStaircase.Slot.weighted_degree_lt` [ArkLib/ToMathlib/Combinatorics/CubicStaircase.lean:90](../../../ArkLib/ToMathlib/Combinatorics/CubicStaircase.lean#L90) — The exponent triple `(x, b₀, b₁)` of a slot satisfies `x + D * (b₀ + b₁) < D * L`.
- `theorem QuadraticStaircase.Slot.weighted_degree_lt` [ArkLib/ToMathlib/Combinatorics/QuadraticStaircase.lean:82](../../../ArkLib/ToMathlib/Combinatorics/QuadraticStaircase.lean#L82) — The exponent pair `(x, u)` of a slot satisfies `x + D * u < D * L`.

### `StmtIn` (2 declarations, 2 files)

- `def Sumcheck.Spec.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:149](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L149) — The input statement for the (full) sum-check protocol, which contains only the target sum value
- `def Sumcheck.Spec.SingleRound.Simple.StmtIn` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:197](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L197) — (no docstring)

### `Vanishes` (2 declarations, 2 files)

- `def NestedEvaluationTree.Vanishes` [ArkLib/Data/MvPolynomial/NestedEvaluationTree.lean:81](../../../ArkLib/Data/MvPolynomial/NestedEvaluationTree.lean#L81) — An evaluation function vanishes at every leaf point of an evaluation tree. At a node, the selected c
- `def Plonk.EvaluationDomain.Vanishes` [ArkLib/ProofSystem/Plonk/Encoding/Basic.lean:57](../../../ArkLib/ProofSystem/Plonk/Encoding/Basic.lean#L57) — Vanishing at every node of the evaluation domain.

### `Verifier` (2 declarations, 2 files)

- `abbrev Interaction.Verifier` [ArkLib/Interaction/Reduction.lean:162](../../../ArkLib/Interaction/Reduction.lean#L162) — A verifier returns the counterpart strategy for the selected input and public statement.
- `structure Verifier` [ArkLib/OracleReduction/Basic.lean:248](../../../ArkLib/OracleReduction/Basic.lean#L248) — A verifier of an interactive protocol is a function that takes in the input statement and the transc

### `Verifier.append` (2 declarations, 2 files)

- `def Interaction.Oracle.Verifier.append` [ArkLib/Interaction/Oracle/Sequential.lean:609](../../../ArkLib/Interaction/Oracle/Sequential.lean#L609) — Compose a value fragment with completed verifiers. Only the suffix carries a terminal action; the fi
- `def Verifier.append` [ArkLib/OracleReduction/Composition/Sequential/Append/Basic.lean:236](../../../ArkLib/OracleReduction/Composition/Sequential/Append/Basic.lean#L236) — Run the first verifier on the transcript prefix, then pass its output statement to the second verifi

### `Verifier.run` (2 declarations, 2 files)

- `def Interaction.Verifier.run` [ArkLib/Interaction/Reduction.lean:215](../../../ArkLib/Interaction/Reduction.lean#L215) — Run a focal strategy against an input-indexed verifier.
- `def Verifier.run` [ArkLib/OracleReduction/Execution.lean:132](../../../ArkLib/OracleReduction/Execution.lean#L132) — Run the (non-oracle) verifier in an interactive reduction. It takes in the input statement and the t

### `Wit` (2 declarations, 2 files)

- `abbrev ConstraintSystem.Wit` [ArkLib/ProofSystem/ConstraintSystem/Basic.lean:67](../../../ArkLib/ProofSystem/ConstraintSystem/Basic.lean#L67) — The underlying problem's witness family, specialized to the split claim.
- `def Plonk.Assembly.Wit` [ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean:64](../../../ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean#L64) — Only the input has a private polynomial table.

### `accumulatorDenominator` (2 declarations, 2 files)

- `def Plonk.accumulatorDenominator` [ArkLib/ProofSystem/Plonk/Accumulator/Basic.lean:35](../../../ArkLib/ProofSystem/Plonk/Accumulator/Basic.lean#L35) — The denominator product, using Mathlib's noncomputable polynomial arithmetic.
- `def Plonk.Computable.accumulatorDenominator` [ArkLib/ProofSystem/Plonk/Accumulator/Computable.lean:32](../../../ArkLib/ProofSystem/Plonk/Accumulator/Computable.lean#L32) — Compute the denominator product from the wire and permutation polynomials.

### `accumulatorNumerator` (2 declarations, 2 files)

- `def Plonk.accumulatorNumerator` [ArkLib/ProofSystem/Plonk/Accumulator/Basic.lean:30](../../../ArkLib/ProofSystem/Plonk/Accumulator/Basic.lean#L30) — The numerator product, using Mathlib's noncomputable polynomial arithmetic.
- `def Plonk.Computable.accumulatorNumerator` [ArkLib/ProofSystem/Plonk/Accumulator/Computable.lean:27](../../../ArkLib/ProofSystem/Plonk/Accumulator/Computable.lean#L27) — Compute the numerator product from the three wire polynomials.

### `aeval_optionEquivRight_symm` (2 declarations, 2 files)

- `theorem ReedSolomon.aeval_optionEquivRight_symm` [ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/ComponentDimension.lean:364](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/ComponentDimension.lean#L364) — Evaluating a flattened source polynomial first evaluates its polynomial coefficients at the challeng
- `theorem MvPolynomial.aeval_optionEquivRight_symm` [ArkLib/ToMathlib/MvPolynomial/PolynomialCoefficients.lean:169](../../../ArkLib/ToMathlib/MvPolynomial/PolynomialCoefficients.lean#L169) — Evaluating the inverse flattened-variable equivalence first evaluates the distinguished polynomial v

### `afterChallenge` (2 declarations, 2 files)

- `def RingSwitching.Packing.Head.afterChallenge` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:327](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L327) — After the challenge, retain acceptance and the derived product-sumcheck relation.
- `def RingSwitching.Packing.ProductSumcheck.Round.afterChallenge` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/RoundSecurity.lean:39](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/RoundSecurity.lean#L39) — After sampling, the local guard and next residual-sum relation hold.

### `agree` (2 declarations, 2 files)

- `def Code.agree` [ArkLib/Data/CodingTheory/Basic/Distance.lean:175](../../../ArkLib/Data/CodingTheory/Basic/Distance.lean#L175) — The number of positions at which the two words `u` and `v` agree.
- `def ProximityGap.WeightedAgreement.agree` [ArkLib/Data/CodingTheory/ProximityGap/Basic.lean:190](../../../ArkLib/Data/CodingTheory/ProximityGap/Basic.lean#L190) — Relative `μ`-agreement between words `u` and `v`.

### `appendPrefix` (2 declarations, 2 files)

- `def Interaction.Oracle.Security.RoundExtractor.appendPrefix` [ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean:178](../../../ArkLib/Interaction/Oracle/Security/KnowledgeAppend.lean#L178) — Embed a concrete first-stage prefix through dependent append.
- `def Prover.appendPrefix` [ArkLib/OracleReduction/Composition/Sequential/Append/ProverSplit.lean:32](../../../ArkLib/OracleReduction/Composition/Sequential/Append/ProverSplit.lean#L32) — Restrict an arbitrary composite prover to its first protocol. Its output is a chosen function of the

### `append_completeness_of_guarded_verifiers` (2 declarations, 2 files)

- `theorem Reduction.append_completeness_of_guarded_verifiers` [ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean:153](../../../ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean#L153) — Sequential composition preserves completeness for guarded verifiers when the prover execution factor
- `theorem OracleReduction.append_completeness_of_guarded_verifiers` [ArkLib/OracleReduction/Composition/Sequential/OracleCompleteness.lean:39](../../../ArkLib/OracleReduction/Composition/Sequential/OracleCompleteness.lean#L39) — Oracle reductions with guarded ordinary verifiers compose with the sum of their errors when prover e

### `append_left_injective` (2 declarations, 2 files)

- `theorem Fin.append_left_injective` [ArkLib/Data/Fin/Basic.lean:249](../../../ArkLib/Data/Fin/Basic.lean#L249) — (no docstring)
- `theorem ProtocolSpec.append_left_injective` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:58](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L58) — (no docstring)

### `append_perfectCompleteness_of_guarded_verifiers` (2 declarations, 2 files)

- `theorem Reduction.append_perfectCompleteness_of_guarded_verifiers` [ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean:169](../../../ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean#L169) — Guarded verifiers compose perfectly when prover execution factors at the seam and the suffix is perf
- `theorem OracleReduction.append_perfectCompleteness_of_guarded_verifiers` [ArkLib/OracleReduction/Composition/Sequential/OracleCompleteness.lean:56](../../../ArkLib/OracleReduction/Composition/Sequential/OracleCompleteness.lean#L56) — Oracle reductions with guarded ordinary verifiers compose perfectly when prover execution factors at

### `append_right_injective` (2 declarations, 2 files)

- `theorem Fin.append_right_injective` [ArkLib/Data/Fin/Basic.lean:257](../../../ArkLib/Data/Fin/Basic.lean#L257) — (no docstring)
- `theorem ProtocolSpec.append_right_injective` [ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean:68](../../../ArkLib/OracleReduction/ProtocolSpec/SeqCompose.lean#L68) — (no docstring)

### `availableContext` (2 declarations, 2 files)

- `def Interaction.Oracle.TypeTree.ExecutionPrefix.availableContext` [ArkLib/Interaction/Oracle/Prefix.lean:380](../../../ArkLib/Interaction/Oracle/Prefix.lean#L380) — Input names and available tree-scoped oracle occurrences form disjoint name spaces.
- `def Interaction.Oracle.WorldPhase.availableContext` [ArkLib/Interaction/Oracle/WorldSegments.lean:183](../../../ArkLib/Interaction/Oracle/WorldSegments.lean#L183) — The available stable resource schema is determined by this action's concrete prefix.

### `bad_event_le` (2 declarations, 2 files)

- `theorem RingSwitching.Packing.Head.bad_event_le` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:416](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L416) — A fixed commitment fixes the candidate before the challenge; only a batching collision survives.
- `theorem RingSwitching.Packing.ProductSumcheck.Round.bad_event_le` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/RoundSecurity.lean:53](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/RoundSecurity.lean#L53) — Fixing the input oracle collection fixes the witness before the random challenge.

### `beforeChallenge` (2 declarations, 2 files)

- `def RingSwitching.Packing.Head.beforeChallenge` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:321](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L321) — Before the fresh challenge, the sent family must equal the committed component evaluations.
- `def RingSwitching.Packing.ProductSumcheck.Round.beforeChallenge` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/RoundSecurity.lean:34](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/RoundSecurity.lean#L34) — Before sampling, the received polynomial equals the residual polynomial of the committed witness.

### `bind` (2 declarations, 2 files)

- `def Interaction.Oracle.Terminal.bind` [ArkLib/Interaction/Oracle/Terminal.lean:45](../../../ArkLib/Interaction/Oracle/Terminal.lean#L45) — Continue only after acceptance. Rejection and faults short-circuit the continuation.
- `theorem ProtocolSpec.OrderedChallenges.bind` [ArkLib/OracleReduction/Security/ChallengePresampling.lean:45](../../../ArkLib/OracleReduction/Security/ChallengePresampling.lean#L45) — Ordered computations compose on adjacent intervals.

### `binding` (2 declarations, 2 files)

- `def Commitment.binding` [ArkLib/Commitments/Functional/Basic.lean:219](../../../ArkLib/Commitments/Functional/Basic.lean#L219) — A commitment scheme satisfies **(evaluation) binding** with error `bindingError` if for all adversar
- `theorem KZG.CommitmentScheme.binding` [ArkLib/Commitments/Functional/KZG/Binding.lean:786](../../../ArkLib/Commitments/Functional/KZG/Binding.lean#L786) — Each evaluation-binding adversary whose reduction belongs to `Adv` has advantage at most `tSdhError`

### `boundaryResidual` (2 declarations, 2 files)

- `def Plonk.Computable.boundaryResidual` [ArkLib/ProofSystem/Plonk/Accumulator/Computable.lean:73](../../../ArkLib/ProofSystem/Plonk/Accumulator/Computable.lean#L73) — Compute the boundary residual using the first-row Lagrange indicator.
- `def Plonk.boundaryResidual` [ArkLib/ProofSystem/Plonk/Accumulator/Residual.lean:30](../../../ArkLib/ProofSystem/Plonk/Accumulator/Residual.lean#L30) — The normalized boundary condition, using noncomputable Lagrange interpolation and polynomial arithme

### `branchPath` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.branchPath` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:224](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L224) — The root-to-leaf path through `tree2` selecting branch `j` of the challenge node.
- `def CoordinateWise.SingleRound.branchPath` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:193](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L193) — The root-to-leaf path through `tree2` selecting branch `j` of the challenge node. Defined separately

### `branchPathOf` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.branchPathOf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:297](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L297) — The root-to-leaf path of branch `j` of an **arbitrary** full scalar-round tree — the index at which
- `def CoordinateWise.SingleRound.branchPathOf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:268](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L268) — The root-to-leaf path of branch `j` of an **arbitrary** full single-round tree — the index at which

### `branchTr` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.branchTr` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:231](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L231) — The full transcript of branch `j` of the star tree: message `v`, challenge `challenges j`.
- `def CoordinateWise.SingleRound.branchTr` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:200](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L200) — The full transcript of branch `j` of the star tree: message `v`, challenge `challenges j`.

### `branch_challenge` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.branch_challenge` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:237](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L237) — Branch `j`'s transcript carries challenge `challenges j` at round 1.
- `theorem CoordinateWise.SingleRound.branch_challenge` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:206](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L206) — Branch `j`'s transcript carries challenge `challenges j` at round 1.

### `branch_mem` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.branch_mem` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:264](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L264) — Branch `j`'s transcript is one of the star tree's leaf transcripts.
- `theorem CoordinateWise.SingleRound.branch_mem` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:233](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L233) — Branch `j`'s transcript is one of the star tree's leaf transcripts.

### `branch_pre` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.branch_pre` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:249](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L249) — Branch `j`'s transcript carries the shared message `v` at round 0.
- `theorem CoordinateWise.SingleRound.branch_pre` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:218](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L218) — Branch `j`'s transcript carries the shared message `v` at round 0.

### `branch_relOut_language` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.branch_relOut_language` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:361](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L361) — Acceptance of the star tree specializes, per branch `j`, to membership of the branch's verifier outp
- `theorem CoordinateWise.SingleRound.branch_relOut_language` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:392](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L392) — Acceptance of the star tree specializes, per branch `j`, to membership of the branch's verifier outp

### `card_slot` (2 declarations, 2 files)

- `theorem CubicStaircase.card_slot` [ArkLib/ToMathlib/Combinatorics/CubicStaircase.lean:65](../../../ArkLib/ToMathlib/Combinatorics/CubicStaircase.lean#L65) — The number of slots is `count D L`.
- `theorem QuadraticStaircase.card_slot` [ArkLib/ToMathlib/Combinatorics/QuadraticStaircase.lean:63](../../../ArkLib/ToMathlib/Combinatorics/QuadraticStaircase.lean#L63) — The number of slots is `count D L`.

### `certifiedExtractorError` (2 declarations, 2 files)

- `def ToyProblem.Impl.IRS.certifiedExtractorError` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:684](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L684) — Full extractor-certified error: the spot-check failure probability combined sharply with the executa
- `def ToyProblem.certifiedExtractorError` [ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean:1351](../../../ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean#L1351) — The executable extractor's full fixed-radius certificate.  Unlike `winningSetUpperBound`, its combin

### `certifiedGammaError` (2 declarations, 2 files)

- `def ToyProblem.Impl.IRS.certifiedGammaError` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:662](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L662) — The certified combination-round error for the executable interleaved-RS extractor.  This is the fini
- `def ToyProblem.certifiedGammaError` [ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean:1264](../../../ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean#L1264) — The finite nonnegative-real reflection of the executable extractor's canonical affine-line MCA-plus-

### `chalPathAux` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.chalPathAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:285](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L285) — Index-generic round-1 branch path: descend into sibling `j` of the challenge node.
- `def CoordinateWise.SingleRound.chalPathAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:256](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L256) — Index-generic round-1 branch path: descend into sibling `j` of the challenge node.

### `chal_shape` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.chal_shape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:182](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L182) — Shape recovery, level 1: every subtree at round 1 is a `chalNode` over leaves.
- `theorem CoordinateWise.SingleRound.chal_shape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:147](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L147) — Shape recovery, level 1: every subtree at round 1 is a `chalNode` over leaves.

### `challengeError` (2 declarations, 2 files)

- `def Fri.Spec.challengeError` [ArkLib/ProofSystem/Fri/Spec/BadEvents.lean:128](../../../ArkLib/ProofSystem/Fri/Spec/BadEvents.lean#L128) — Per-challenge error: the folding MCA error, or `(1 - min θ δ)^l` for the query vector.
- `def Spartan.challengeError` [ArkLib/ProofSystem/Spartan/Security.lean:173](../../../ArkLib/ProofSystem/Spartan/Security.lean#L173) — The challenge schedule routes each challenge to its stage's error. Real-valued bounds are noncomputa

### `chalsAux` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.chalsAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:125](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L125) — Index-generic round-1 reader: peel the sibling-challenge family off a `chalNode` at any index `a` to
- `def CoordinateWise.SingleRound.chalsAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:90](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L90) — Index-generic round-1 reader: peel the sibling-challenge family off a `chalNode` at any index `a` to

### `check_and_mem_of_prEvent_pos` (2 declarations, 2 files)

- `theorem RingSwitching.Packing.ProductSumcheck.Round.check_and_mem_of_prEvent_pos` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/RoundExecution.lean:70](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/RoundExecution.lean#L70) — A positive-probability related output determines the accepted guard and next residual relation.
- `theorem RingSwitching.Packing.ProductSumcheck.Terminal.check_and_mem_of_prEvent_pos` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean:186](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean#L186) — A positive-probability related output determines the accepted product check and opening.

### `check_iff_layout_weight` (2 declarations, 2 files)

- `theorem ArkLib.Lattices.Hachi.TraceHead.check_iff_layout_weight` [ArkLib/Commitments/Functional/Hachi/TraceHead/Conformance.lean:116](../../../ArkLib/Commitments/Functional/Hachi/TraceHead/Conformance.lean#L116) — The trace check says that the claimed scalar is the layout-weighted sum of the `ψ`-coordinates of th
- `theorem RingSwitching.Packing.Conformance.check_iff_layout_weight` [ArkLib/ProofSystem/RingSwitching/Packing/Conformance.lean:74](../../../ArkLib/ProofSystem/RingSwitching/Packing/Conformance.lean#L74) — The column check says that the claim is the layout-weighted sum of the carrier's column family.

### `code` (2 declarations, 2 files)

- `def ReedSolomon.code` [ArkLib/Data/CodingTheory/ReedSolomon.lean:65](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L65) — The Reed-Solomon code for polynomials of degree less than `deg` and evaluation points `domain`.
- `def Binius.BinaryBasefold.code` [ArkLib/ProofSystem/Binius/BinaryBasefold/Code.lean:72](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Code.lean#L72) — The Reed–Solomon evaluation code on `S⁽ⁱ⁾` with degree bound `2 ^ (ℓ - i)`.

### `coe_certifiedGammaError` (2 declarations, 2 files)

- `theorem ToyProblem.Impl.IRS.coe_certifiedGammaError` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:669](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L669) — The certified combination-round error coerces back to its defining MCA-plus-list expression.
- `theorem ToyProblem.coe_certifiedGammaError` [ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean:1274](../../../ArkLib/ProofSystem/ToyProblem/SoundnessBounds.lean#L1274) — `certifiedGammaError` coerces to the exact MCA-plus-list certificate.

### `collect_branch_data` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.collect_branch_data` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:445](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L445) — **Extraction core, scalar round.** Validity at the pure verdicts yields the `k` per-branch responses
- `theorem CoordinateWise.SingleRound.collect_branch_data` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:473](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L473) — **Extraction core.** A leaf witnessing that is valid *at the verifier's verdicts* yields the per-bra

### `compatible_oracles` (2 declarations, 2 files)

- `theorem Spartan.FirstSumcheck.compatible_oracles` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:285](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L285) — (no docstring)
- `theorem Spartan.SecondSumcheck.compatible_oracles` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:287](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L287) — (no docstring)

### `completenessError` (2 declarations, 2 files)

- `def Fri.Spec.completenessError` [ArkLib/ProofSystem/Fri/Spec/QueryCompleteness.lean:107](../../../ArkLib/ProofSystem/Fri/Spec/QueryCompleteness.lean#L107) — The clipped completeness error for `l` queries with first-fold exponent `s 0`.
- `def Plonk.Assembly.completenessError` [ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean:239](../../../ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean#L239) — Completeness loss occurs only at the joint grand-product challenge. Real division is noncomputable.

### `constrainedCode` (2 declarations, 2 files)

- `def ReedSolomon.constrainedCode` [ArkLib/Data/CodingTheory/ReedSolomon/Constrained.lean:55](../../../ArkLib/Data/CodingTheory/ReedSolomon/Constrained.lean#L55) — Definition 4.5, WHIR[ACFY24] Constrained Reed-Solomon codes are smooth codes whose decoded `m`-varia
- `def ToyProblem.constrainedCode` [ArkLib/ProofSystem/ToyProblem/ConstrainedCode.lean:138](../../../ArkLib/ProofSystem/ToyProblem/ConstrainedCode.lean#L138) — **The constrained code** (scalar alphabet `A = F`). Adjoin the linear-constraint value `⟨m, v⟩ = ∑ j

### `contextInclusion` (2 declarations, 2 files)

- `def Interaction.Oracle.PhasedRun.contextInclusion` [ArkLib/Interaction/Oracle/PhasedRun.lean:79](../../../ArkLib/Interaction/Oracle/PhasedRun.lean#L79) — A boundary's available context embeds into the final context with unchanged stable names.
- `def Interaction.Oracle.TypeTree.ExecutionPrefix.contextInclusion` [ArkLib/Interaction/Oracle/Prefix.lean:403](../../../ArkLib/Interaction/Oracle/Prefix.lean#L403) — Structural extension includes previously available context indices without changing their names. It

### `contextLens_complete` (2 declarations, 2 files)

- `instance Spartan.FirstSumcheck.contextLens_complete` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:250](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L250) — Honest execution retains the materialized virtual polynomial when lifting completeness.
- `instance Spartan.SecondSumcheck.contextLens_complete` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:252](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L252) — Honest execution retains the materialized virtual polynomial when lifting completeness.

### `count` (2 declarations, 2 files)

- `def CubicStaircase.count` [ArkLib/ToMathlib/Combinatorics/CubicStaircase.lean:52](../../../ArkLib/ToMathlib/Combinatorics/CubicStaircase.lean#L52) — The number of natural triples `(x, b₀, b₁)` with `x + D * (b₀ + b₁) < D * L`, written as a sum over
- `def QuadraticStaircase.count` [ArkLib/ToMathlib/Combinatorics/QuadraticStaircase.lean:50](../../../ArkLib/ToMathlib/Combinatorics/QuadraticStaircase.lean#L50) — The number of natural pairs `(x, u)` with `x + D * u < D * L`, written as a sum over `u`: there are

### `decode_relation` (2 declarations, 2 files)

- `theorem Plonk.SendWitness.decode_relation` [ArkLib/ProofSystem/Plonk/SendWitness.lean:109](../../../ArkLib/ProofSystem/Plonk/SendWitness.lean#L109) — An accepted revealed table is the same witness for the input relation.
- `theorem Spartan.WitnessAttachment.decode_relation` [ArkLib/ProofSystem/Spartan/WitnessAttachment.lean:172](../../../ArkLib/ProofSystem/Spartan/WitnessAttachment.lean#L172) — A satisfying attached table decodes to an original satisfying witness.

### `decoder` (2 declarations, 2 files)

- `def BerlekampWelch.decoder` [ArkLib/Data/CodingTheory/BerlekampWelch/BerlekampWelch.lean:56](../../../ArkLib/Data/CodingTheory/BerlekampWelch/BerlekampWelch.lean#L56) — Berlekamp-Welch decoder for Reed-Solomon codes. Given received codeword evaluations with potential e
- `def GuruswamiSudan.decoder` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:114](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L114) — Guruswami-Sudan decoder.  Returns all roots of the GS interpolation polynomial whose evaluation is w

### `domain` (2 declarations, 2 files)

- `def Plonk.Quotient.domain` [ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean:33](../../../ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean#L33) — The row-domain vanishing polynomial is evaluated by powering.
- `def ToyProblem.Impl.FRS.domain` [ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean:116](../../../ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean#L116) — A neutral `2^16`-point folded-RS evaluation domain in Ext6, given by the geometric progression `j ↦

### `domain_implies_2_ne_0` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.domain_implies_2_ne_0` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:117](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L117) — (no docstring)
- `lemma Domain.FftDomainClass.domain_implies_2_ne_0` [ArkLib/Data/Domain/FftDomain/Ops.lean:189](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L189) — (no docstring)

### `domain_implies_char_ne_2` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:114](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L114) — The existence of a nontrivial smooth coset FFT domain rules out characteristic `2`.
- `lemma Domain.FftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/FftDomain/Ops.lean:164](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L164) — The existence of a nontrivial smooth FFT domain rules out characteristic `2`.

### `domain_implies_neg_x_ne_x_dep` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.domain_implies_neg_x_ne_x_dep` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:130](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L130) — (no docstring)
- `lemma Domain.FftDomainClass.domain_implies_neg_x_ne_x_dep` [ArkLib/Data/Domain/FftDomain/Ops.lean:205](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L205) — (no docstring)

### `domain_implies_x_ne_neg_x` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.domain_implies_x_ne_neg_x` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:120](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L120) — (no docstring)
- `lemma Domain.FftDomainClass.domain_implies_x_ne_neg_x` [ArkLib/Data/Domain/FftDomain/Ops.lean:193](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L193) — (no docstring)

### `domain_implies_x_ne_neg_x_dep` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.domain_implies_x_ne_neg_x_dep` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:124](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L124) — (no docstring)
- `lemma Domain.FftDomainClass.domain_implies_x_ne_neg_x_dep` [ArkLib/Data/Domain/FftDomain/Ops.lean:199](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L199) — (no docstring)

### `done` (2 declarations, 2 files)

- `def Interaction.Oracle.Protocol.done` [ArkLib/Interaction/Oracle/Protocol.lean:47](../../../ArkLib/Interaction/Oracle/Protocol.lean#L47) — Terminal decorated protocol.
- `def Interaction.Oracle.TypeTree.done` [ArkLib/Interaction/Oracle/TypeTree.lean:71](../../../ArkLib/Interaction/Oracle/TypeTree.lean#L71) — Terminal oracle interaction tree.

### `embedMatrices` (2 declarations, 2 files)

- `def R1CS.embedMatrices` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:103](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L103) — Enlarge each of the three constraint matrices using the same column layout.
- `def Spartan.embedMatrices` [ArkLib/ProofSystem/Spartan/Algebra/Layout.lean:114](../../../ArkLib/ProofSystem/Spartan/Algebra/Layout.lean#L114) — Embed an arbitrary matrix family into the chosen Spartan row and column layout.

### `embedStatement` (2 declarations, 2 files)

- `def R1CS.embedStatement` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:75](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L75) — Pad the public coordinates independently of the witness coordinates.
- `def Spartan.embedStatement` [ArkLib/ProofSystem/Spartan/Algebra/Layout.lean:109](../../../ArkLib/ProofSystem/Spartan/Algebra/Layout.lean#L109) — Embed an arbitrary public input into the chosen Spartan public block.

### `embedWitness` (2 declarations, 2 files)

- `def R1CS.embedWitness` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:79](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L79) — Pad the witness coordinates independently of the public coordinates.
- `def Spartan.embedWitness` [ArkLib/ProofSystem/Spartan/Algebra/Layout.lean:119](../../../ArkLib/ProofSystem/Spartan/Algebra/Layout.lean#L119) — Embed an arbitrary witness into the chosen Spartan witness block.

### `encode_relation` (2 declarations, 2 files)

- `theorem Plonk.SendWitness.encode_relation` [ArkLib/ProofSystem/Plonk/SendWitness.lean:115](../../../ArkLib/ProofSystem/Plonk/SendWitness.lean#L115) — Revealing an honest table preserves its gate and copy equations.
- `theorem Spartan.WitnessAttachment.encode_relation` [ArkLib/ProofSystem/Spartan/WitnessAttachment.lean:179](../../../ArkLib/ProofSystem/Spartan/WitnessAttachment.lean#L179) — Honest padding transfers the original relation to the attached output.

### `encoder` (2 declarations, 2 files)

- `def ToyProblem.Impl.FRS.encoder` [ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean:161](../../../ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean#L161) — The neutral `s = 32` folded encoder: the degree-`< 2^20` folded Reed–Solomon evaluation map on the `
- `def ToyProblem.Impl.IRS.encoder` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:116](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L116) — Executable `s`-interleaved Reed--Solomon encoder.  Its public alphabet is `Fin s → F`; interleaving

### `encoder_injective` (2 declarations, 2 files)

- `theorem ToyProblem.Impl.FRS.encoder_injective` [ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean:184](../../../ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean#L184) — **Injectivity of the folded encoder** (the "code as the injective map"). Mathematically this would f
- `theorem ToyProblem.Impl.IRS.encoder_injective` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:179](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L179) — Below scalar-row saturation, the executable interleaved encoder is injective.

### `encoder_range` (2 declarations, 2 files)

- `theorem ToyProblem.Impl.FRS.encoder_range` [ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean:198](../../../ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean#L198) — **The folded encoder's image is exactly the folded RS code** `FRS[domain, 2^20, 32, foldOmega]`. The
- `theorem ToyProblem.Impl.IRS.encoder_range` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:145](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L145) — The executable encoder has exactly the canonical interleaved Reed--Solomon code as its range.

### `eq_leaf` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.eq_leaf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:172](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L172) — Shape recovery, level 2: every subtree at the last round is a leaf.
- `theorem CoordinateWise.SingleRound.eq_leaf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:137](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L137) — Shape recovery, level 2: every subtree at the last round is a leaf.

### `error` (2 declarations, 2 files)

- `def Plonk.Assembly.error` [ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean:211](../../../ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean#L211) — Each global challenge inherits its component's fixed-prefix error, using real division.
- `def Spartan.Assembly.error` [ArkLib/ProofSystem/Spartan/Security.lean:79](../../../ArkLib/ProofSystem/Spartan/Security.lean#L79) — Per-challenge errors, with real division used only in the security statement.

### `eval_interpolate` (2 declarations, 2 files)

- `theorem Plonk.EvaluationDomain.eval_interpolate` [ArkLib/ProofSystem/Plonk/Encoding/Basic.lean:39](../../../ArkLib/ProofSystem/Plonk/Encoding/Basic.lean#L39) — (no docstring)
- `theorem Plonk.Computable.eval_interpolate` [ArkLib/ProofSystem/Plonk/Encoding/Computable.lean:44](../../../ArkLib/ProofSystem/Plonk/Encoding/Computable.lean#L44) — The executable interpolant takes the supplied value at every row.

### `executeCore_closed` (2 declarations, 2 files)

- `theorem Sumcheck.Interaction.SingleRound.executeCore_closed` [ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:126](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean#L126) — Programmatic perfect completeness through the new run-derived relation boundary.
- `theorem Sumcheck.Interaction.MultivariateRound.executeCore_closed` [ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:177](../../../ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean#L177) — The run-derived closed result of an accepting stage preserves its entire input interface.

### `executeCore_honest` (2 declarations, 2 files)

- `theorem Sumcheck.Interaction.SingleRound.executeCore_honest` [ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:95](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean#L95) — The actual executor produces the paired honest run, pointwise in the challenge.
- `theorem Sumcheck.Interaction.MultivariateRound.executeCore_honest` [ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:265](../../../ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean#L265) — Honest execution exports the original polynomial at the actual next statement.

### `execute_perfectCompleteness` (2 declarations, 2 files)

- `theorem Sumcheck.Interaction.Computable.execute_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Interaction/ComputableCompleteness.lean:116](../../../ArkLib/ProofSystem/Sumcheck/Interaction/ComputableCompleteness.lean#L116) — For any normalized challenge program, actual computational honest execution is perfectly complete fr
- `theorem Sumcheck.Interaction.Native.execute_perfectCompleteness` [ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolCompleteness.lean:110](../../../ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolCompleteness.lean#L110) — Actual honest execution has probability-one completeness for any `ProbComp` challenge. `ProbComp` us

### `execute_soundness` (2 declarations, 2 files)

- `theorem Sumcheck.Interaction.Computable.execute_soundness` [ArkLib/ProofSystem/Sumcheck/Interaction/ComputableSoundness.lean:31](../../../ArkLib/ProofSystem/Sumcheck/Interaction/ComputableSoundness.lean#L31) — From a false initial claim over a polynomial-realized original oracle, the probability that the actu
- `theorem Sumcheck.Interaction.Native.execute_soundness` [ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolSoundness.lean:201](../../../ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolSoundness.lean#L201) — Full interaction-layer Sumcheck is sound against every ordinary prover strategy. From a false initia

### `execute_support_completeness` (2 declarations, 2 files)

- `theorem Sumcheck.Interaction.Computable.execute_support_completeness` [ArkLib/ProofSystem/Sumcheck/Interaction/ComputableCompleteness.lean:95](../../../ArkLib/ProofSystem/Sumcheck/Interaction/ComputableCompleteness.lean#L95) — Every supported actual honest execution accepts a true retained-original evaluation claim.
- `theorem Sumcheck.Interaction.Native.execute_support_completeness` [ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolCompleteness.lean:52](../../../ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolCompleteness.lean#L52) — Every supported honest execution accepts a true original-oracle evaluation claim.

### `exists_frobeniusContraction_fractionRing` (2 declarations, 2 files)

- `theorem MvPolynomial.exists_frobeniusContraction_fractionRing` [ArkLib/Data/MvPolynomial/FrobeniusContraction.lean:156](../../../ArkLib/Data/MvPolynomial/FrobeniusContraction.lean#L156) — Over a unique factorization domain of characteristic `p`, the terminal polynomial `G` of `exists_irr
- `theorem Polynomial.exists_frobeniusContraction_fractionRing` [ArkLib/Data/Polynomial/FrobeniusContraction.lean:149](../../../ArkLib/Data/Polynomial/FrobeniusContraction.lean#L149) — Over a GCD domain of characteristic `p`, the terminal polynomial `G` of the Frobenius contraction of

### `exists_irreducible_frobeniusContraction` (2 declarations, 2 files)

- `theorem MvPolynomial.exists_irreducible_frobeniusContraction` [ArkLib/Data/MvPolynomial/FrobeniusContraction.lean:82](../../../ArkLib/Data/MvPolynomial/FrobeniusContraction.lean#L82) — In characteristic `p` without zero divisors, an irreducible polynomial `F` of positive degree in `no
- `theorem Polynomial.exists_irreducible_frobeniusContraction` [ArkLib/Data/Polynomial/FrobeniusContraction.lean:87](../../../ArkLib/Data/Polynomial/FrobeniusContraction.lean#L87) — If `P` is irreducible of positive degree, the terminal polynomial `G` of `exists_frobeniusContractio

### `exists_irreducible_frobeniusContraction_expChar` (2 declarations, 2 files)

- `theorem MvPolynomial.exists_irreducible_frobeniusContraction_expChar` [ArkLib/Data/MvPolynomial/FrobeniusContraction.lean:105](../../../ArkLib/Data/MvPolynomial/FrobeniusContraction.lean#L105) — In exponential characteristic `p` without zero divisors, an irreducible polynomial `F` of positive d
- `theorem Polynomial.exists_irreducible_frobeniusContraction_expChar` [ArkLib/Data/Polynomial/FrobeniusContraction.lean:125](../../../ArkLib/Data/Polynomial/FrobeniusContraction.lean#L125) — In exponential characteristic `p` without zero divisors, an irreducible positive-degree polynomial `

### `exists_separantChain` (2 declarations, 2 files)

- `theorem ReedSolomon.HiddenDerivative.SymbolicReceivedCurve.Certificate.exists_separantChain` [ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/CurveCertificate.lean:94](../../../ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/CurveCertificate.lean#L94) — A certificate equation has a separant chain when its jet degrees satisfy the characteristic bound.
- `theorem PolynomialDifferential.exists_separantChain` [ArkLib/Data/Polynomial/Differential/SeparantChain.lean:87](../../../ArkLib/Data/Polynomial/Differential/SeparantChain.lean#L87) — A nonzero equation over a commutative semiring without zero divisors has a separant chain when it sa

### `exists_weightedSupport_certificate_of_rate` (2 declarations, 2 files)

- `theorem ReedSolomon.HiddenDerivative.SymbolicReceivedCurve.exists_weightedSupport_certificate_of_rate` [ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/CurveSupportCertificate.lean:108](../../../ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/CurveSupportCertificate.lean#L108) — The prescribed rate interval constructs a polynomial-curve certificate.
- `theorem ReedSolomon.HiddenDerivative.exists_weightedSupport_certificate_of_rate` [ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/WeightedSupportCertificate.lean:73](../../../ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/WeightedSupportCertificate.lean#L73) — The prescribed rate interval constructs a certificate with challenge degree below `12 (2 m - 1)` and

### `finite_regularHighCutJets_card_le_dimensionSensitive_of_exponent` (2 declarations, 2 files)

- `theorem ReedSolomon.finite_regularHighCutJets_card_le_dimensionSensitive_of_exponent` [ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedIncidence.lean:275](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedIncidence.lean#L275) — A finite family of regular jets satisfying all high Taylor cuts and enough agreement cuts is bounded
- `theorem PolynomialDifferential.finite_regularHighCutJets_card_le_dimensionSensitive_of_exponent` [ArkLib/Data/Polynomial/Differential/TaylorChartIncidence.lean:374](../../../ArkLib/Data/Polynomial/Differential/TaylorChartIncidence.lean#L374) — A finite family of regular jets satisfying all high Taylor cuts and enough agreement cuts is bounded

### `firstVirtual` (2 declarations, 2 files)

- `def Spartan.Computable.firstVirtual` [ArkLib/ProofSystem/Spartan/Algebra/Computable.lean:92](../../../ArkLib/ProofSystem/Spartan/Algebra/Computable.lean#L92) — Construct the first virtual polynomial from equality weights and row products.
- `def Spartan.Algebra.firstVirtual` [ArkLib/ProofSystem/Spartan/Algebra/Identities.lean:57](../../../ArkLib/ProofSystem/Spartan/Algebra/Identities.lean#L57) — The first sumcheck polynomial `G_τ(X) = eq(τ,X) F(X)`.

### `firstVirtual_realizes` (2 declarations, 2 files)

- `theorem Spartan.Realization.firstVirtual_realizes` [ArkLib/ProofSystem/Spartan/Algebra/Realization.lean:72](../../../ArkLib/ProofSystem/Spartan/Algebra/Realization.lean#L72) — Executable evaluation agrees with the first virtual polynomial.
- `theorem Spartan.VirtualOracle.firstVirtual_realizes` [ArkLib/ProofSystem/Spartan/Sumcheck/VirtualOracle.lean:87](../../../ArkLib/ProofSystem/Spartan/Sumcheck/VirtualOracle.lean#L87) — The oracle-query implementation realizes the semantic first virtual polynomial.

### `flatten` (2 declarations, 2 files)

- `def Interaction.Oracle.WorldSegments.flatten` [ArkLib/Interaction/Oracle/WorldSegments.lean:80](../../../ArkLib/Interaction/Oracle/WorldSegments.lean#L80) — Flatten local actions in actual execution order.
- `def ToyProblem.Impl.IRS.flatten` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:88](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L88) — Join `s` rows of length `k / s` into a length-`k` scalar message.

### `foldExtractor_eq` (2 declarations, 2 files)

- `theorem Plonk.Assembly.Circuit.foldExtractor_eq` [ArkLib/ProofSystem/Plonk/Assembly/CircuitExtraction.lean:87](../../../ArkLib/ProofSystem/Plonk/Assembly/CircuitExtraction.lean#L87) — The ordinary circuit extractor is the backward fold of the named certificate.
- `theorem Plonk.Assembly.foldExtractor_eq` [ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean:305](../../../ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean#L305) — Folding the composed round-by-round extractor reads the initial table message.

### `foldOracleReduction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.CoreInteraction.foldOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/Fold/Protocol.lean:123](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Steps/Fold/Protocol.lean#L123) — The oracle reduction of the `i`-th fold step.
- `def Fri.Spec.FoldPhase.foldOracleReduction` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:398](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L398) — The oracle reduction that is the `i`-th round of the FRI protocol.

### `fromReindex` (2 declarations, 2 files)

- `def Interaction.Oracle.NamedContext.Inclusion.fromReindex` [ArkLib/Interaction/Oracle/Resource.lean:262](../../../ArkLib/Interaction/Oracle/Resource.lean#L262) — Include an injectively reindexed context in its original context.
- `def Interaction.Oracle.SourceHom.fromReindex` [ArkLib/Interaction/Oracle/Source.lean:222](../../../ArkLib/Interaction/Oracle/Source.lean#L222) — Canonical routing from a reindexed signature into the original source.

### `fullTranscript_branchPathOf` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.fullTranscript_branchPathOf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:312](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L312) — The branch path's transcript **is** the branch transcript — definitional on the star tree.
- `theorem CoordinateWise.SingleRound.fullTranscript_branchPathOf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:284](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L284) — The branch path's transcript **is** the branch transcript — definitional on the star tree, since the

### `gamma` (2 declarations, 2 files)

- `def RationalFunctions.HenselNumerators.gamma` [ArkLib/Data/Polynomial/RationalFunctions/HenselNumerators/Sequence.lean:351](../../../ArkLib/Data/Polynomial/RationalFunctions/HenselNumerators/Sequence.lean#L351) — The chosen power series `γ = ∑ α_t (X - x₀)^t`, induced by the selected regular numerator sequence f
- `def ToyProblem.Impl.FRS.gamma` [ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean:85](../../../ArkLib/ProofSystem/ToyProblem/Impl/FRS.lean#L85) — The shared high-order generator `γ` of `gamma_exists`.

### `gammaAgreementSet` (2 declarations, 2 files)

- `def ToyProblem.Impl.IRS.gammaAgreementSet` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:210](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L210) — Maximal column agreement set computed from the fresh challenge and the prover's post-challenge messa
- `def ToyProblem.Spec.gammaAgreementSet` [ArkLib/ProofSystem/ToyProblem/Spec/ErasureDecoder.lean:262](../../../ArkLib/ProofSystem/ToyProblem/Spec/ErasureDecoder.lean#L262) — The source-faithful maximal agreement set computed after `γ` and `g` are known.

### `gammaAgreementSet_card_of_gammaState` (2 declarations, 2 files)

- `theorem ToyProblem.Impl.IRS.gammaAgreementSet_card_of_gammaState` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:226](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L226) — A post-`γ` knowledge state makes the computed maximal interleaved agreement set large.
- `theorem ToyProblem.Spec.gammaAgreementSet_card_of_gammaState` [ArkLib/ProofSystem/ToyProblem/Spec/ErasureDecoder.lean:286](../../../ArkLib/ProofSystem/ToyProblem/Spec/ErasureDecoder.lean#L286) — A `GammaState` witness makes the computed maximal agreement set large.

### `gatePolynomial` (2 declarations, 2 files)

- `def Plonk.gatePolynomial` [ArkLib/ProofSystem/Plonk/Encoding/Basic.lean:171](../../../ArkLib/ProofSystem/Plonk/Encoding/Basic.lean#L171) — The gate residual, using Mathlib's noncomputable polynomial arithmetic.
- `def Plonk.Computable.gatePolynomial` [ArkLib/ProofSystem/Plonk/Encoding/Computable.lean:73](../../../ArkLib/ProofSystem/Plonk/Encoding/Computable.lean#L73) — Assemble the gate residual from executable polynomials.

### `guruswami_sudan_for_proximity_gap_existence` (2 declarations, 2 files)

- `lemma GuruswamiSudan.guruswami_sudan_for_proximity_gap_existence` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:896](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L896) — Constructive witness extraction for the Guruswami–Sudan system. When the computable `hasWitnessC` ch
- `lemma ProximityGap.guruswami_sudan_for_proximity_gap_existence` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:57](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L57) — The first part of BCIKS20 Lemma 5.3: for messages of degree at most `k`, a nonzero multiplicity-`m`

### `guruswami_sudan_for_proximity_gap_property` (2 declarations, 2 files)

- `lemma GuruswamiSudan.guruswami_sudan_for_proximity_gap_property` [ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean:935](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/GuruswamiSudan.lean#L935) — Constructive witness property for the Guruswami–Sudan system. When `m > 0` and the codeword polynomi
- `lemma ProximityGap.guruswami_sudan_for_proximity_gap_property` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:71](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L71) — The second part of BCIKS20 Lemma 5.3: for messages of degree at most `k`, weighted degree strictly b

### `harmonic_eq_sum_fin` (2 declarations, 2 files)

- `theorem ReedSolomon.HiddenDerivative.harmonic_eq_sum_fin` [ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/WeightedSupport/Moments.lean:67](../../../ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/WeightedSupport/Moments.lean#L67) — The harmonic number as a sum over `Fin n`.
- `theorem ReedSolomon.HiddenDerivative.RatePartition.harmonic_eq_sum_fin` [ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/RatePartition/Moment.lean:77](../../../ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/RatePartition/Moment.lean#L77) — The harmonic number as a sum over `Fin n`.

### `honestAccumulator_toPoly` (2 declarations, 2 files)

- `theorem Plonk.Computable.honestAccumulator_toPoly` [ArkLib/ProofSystem/Plonk/Accumulator/Computable.lean:59](../../../ArkLib/ProofSystem/Plonk/Accumulator/Computable.lean#L59) — Executable interpolation represents the honest mathematical accumulator.
- `theorem Plonk.GrandProduct.honestAccumulator_toPoly` [ArkLib/ProofSystem/Plonk/GrandProduct/Data.lean:214](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Data.lean#L214) — Honest coefficient-array interpolation agrees with the mathematical accumulator.

### `honestMessage` (2 declarations, 2 files)

- `def ArkLib.Lattices.Hachi.TraceHead.honestMessage` [ArkLib/Commitments/Functional/Hachi/TraceHead/Protocol.lean:133](../../../ArkLib/Commitments/Functional/Hachi/TraceHead/Protocol.lean#L133) — Evaluate the ring polynomial extracted from the weak opening at the retained point.
- `def RingSwitching.Packing.ProductSumcheck.Round.honestMessage` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean:42](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean#L42) — The honest message is the exact remaining product sum as a polynomial in the next variable.

### `honestProver` (2 declarations, 2 files)

- `def Sumcheck.Interaction.Computable.honestProver` [ArkLib/ProofSystem/Sumcheck/Interaction/ComputableCompleteness.lean:37](../../../ArkLib/ProofSystem/Sumcheck/Interaction/ComputableCompleteness.lean#L37) — Compute each honest round message from the original computational polynomial. Prior challenges are r
- `def Sumcheck.Interaction.Native.honestProver` [ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolCompleteness.lean:36](../../../ArkLib/ProofSystem/Sumcheck/Interaction/ProtocolCompleteness.lean#L36) — Honest messages use the actual public prefix; memory lives in ordinary continuations.

### `honestTranscript` (2 declarations, 2 files)

- `def ArkLib.Lattices.Hachi.TraceHead.honestTranscript` [ArkLib/Commitments/Functional/Hachi/TraceHead/Completeness.lean:35](../../../ArkLib/Commitments/Functional/Hachi/TraceHead/Completeness.lean#L35) — The honest transcript contains exactly the one ring evaluation sent by the prover.
- `def Plonk.GrandProduct.honestTranscript` [ArkLib/ProofSystem/Plonk/GrandProduct/Completeness.lean:33](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Completeness.lean#L33) — The honest transcript contains the joint challenge and its computed accumulator.

### `honest_check` (2 declarations, 2 files)

- `theorem QuotientZeroTest.honest_check` [ArkLib/ProofSystem/Component/QuotientZeroTest.lean:192](../../../ArkLib/ProofSystem/Component/QuotientZeroTest.lean#L192) — The honest quotient passes at every point, including points inside the domain.
- `theorem RingSwitching.Packing.CheckedObservation.honest_check` [ArkLib/ProofSystem/RingSwitching/Packing/CheckedObservation.lean:45](../../../ArkLib/ProofSystem/RingSwitching/Packing/CheckedObservation.lean#L45) — Every correct original claim passes the observation check on its honest message.

### `honest_outputRelation` (2 declarations, 2 files)

- `theorem Plonk.GrandProduct.honest_outputRelation` [ArkLib/ProofSystem/Plonk/GrandProduct/Data.lean:256](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Data.lean#L256) — Valid input columns yield vanishing honest residuals outside the explicit bad set.
- `theorem Sumcheck.Interaction.SingleRound.honest_outputRelation` [ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:157](../../../ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean#L157) — The typed honest terminal statement satisfies the existing single-round output relation.

### `hypercubePoint` (2 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.hypercubePoint` [ArkLib/Commitments/Functional/Hachi/ZeroCheck/Constraints.lean:856](../../../ArkLib/Commitments/Functional/Hachi/ZeroCheck/Constraints.lean#L856) — Assemble a point from a fixed prefix and a Boolean suffix.
- `def MvPolynomial.hypercubePoint` [ArkLib/Data/MvPolynomial/Hypercube.lean:34](../../../ArkLib/Data/MvPolynomial/Hypercube.lean#L34) — Assemble a full point from a fixed prefix and a Boolean suffix.

### `hypercubeSum` (2 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.hypercubeSum` [ArkLib/Commitments/Functional/Hachi/ZeroCheck/Constraints.lean:890](../../../ArkLib/Commitments/Functional/Hachi/ZeroCheck/Constraints.lean#L890) — Partial sum of `H` over the trailing cube coordinates: `hypercubeSum H i cs = ∑_{x ∈ {0,1}^{m₀ − i}}
- `def MvPolynomial.hypercubeSum` [ArkLib/Data/MvPolynomial/Hypercube.lean:38](../../../ArkLib/Data/MvPolynomial/Hypercube.lean#L38) — Sum a polynomial over Boolean completions of a fixed challenge prefix.

### `hypercubeSum_zero` (2 declarations, 2 files)

- `theorem ArkLib.Lattices.Ajtai.InnerOuter.hypercubeSum_zero` [ArkLib/Commitments/Functional/Hachi/ZeroCheck/Constraints.lean:1110](../../../ArkLib/Commitments/Functional/Hachi/ZeroCheck/Constraints.lean#L1110) — The full-cube sum, with the empty challenge prefix unfolded: `hypercubeSum … 0` ranges over every Bo
- `theorem MvPolynomial.hypercubeSum_zero` [ArkLib/Data/MvPolynomial/Hypercube.lean:43](../../../ArkLib/Data/MvPolynomial/Hypercube.lean#L43) — The initial sum is the ordinary Boolean sum.

### `injOn` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomain.injOn` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:328](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L328) — A concrete coset FFT domain is injective on every set.
- `lemma Domain.FftDomain.injOn` [ArkLib/Data/Domain/FftDomain/Defs.lean:156](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L156) — An FFT domain is injective on every set.

### `inl` (2 declarations, 2 files)

- `def Interaction.Oracle.NamedContext.Inclusion.inl` [ArkLib/Interaction/Oracle/Resource.lean:267](../../../ArkLib/Interaction/Oracle/Resource.lean#L267) — Include the left context in a disjoint union.
- `def Interaction.Oracle.SourceHom.inl` [ArkLib/Interaction/Oracle/Source.lean:236](../../../ArkLib/Interaction/Oracle/Source.lean#L236) — Left weakening ignores the additional right environment.

### `innerCertificate` (2 declarations, 2 files)

- `def Spartan.FirstSumcheck.innerCertificate` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:363](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L363) — Choose the witness family, extractor, and state supplied by the proved general sumcheck certificate.
- `def Spartan.SecondSumcheck.innerCertificate` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:366](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L366) — Choose the witness family, extractor, and state supplied by the proved general sumcheck certificate.

### `inputImpl` (2 declarations, 2 files)

- `def Sumcheck.Impl.Computable.inputImpl` [ArkLib/ProofSystem/Sumcheck/Impl/Projection.lean:240](../../../ArkLib/ProofSystem/Sumcheck/Impl/Projection.lean#L240) — Direct original-polynomial oracle behavior. Every answer evaluates the computational multivariate da
- `def Sumcheck.Interaction.SingleRound.inputImpl` [ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:93](../../../ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean#L93) — Honest input behavior induced by a degree-bounded polynomial.

### `inputRelation_iff` (2 declarations, 2 files)

- `theorem Spartan.FirstSumcheck.inputRelation_iff` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:125](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L125) — The projected initial sumcheck relation is exactly the zero-check claim.
- `theorem Spartan.SecondSumcheck.inputRelation_iff` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:84](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L84) — The projected initial relation is exactly the second virtual sum claimed by batching.

### `inr` (2 declarations, 2 files)

- `def Interaction.Oracle.NamedContext.Inclusion.inr` [ArkLib/Interaction/Oracle/Resource.lean:272](../../../ArkLib/Interaction/Oracle/Resource.lean#L272) — Include the right context in a disjoint union.
- `def Interaction.Oracle.SourceHom.inr` [ArkLib/Interaction/Oracle/Source.lean:243](../../../ArkLib/Interaction/Oracle/Source.lean#L243) — Right weakening ignores the additional left environment.

### `instChallengeSampleable` (2 declarations, 2 files)

- `instance Binius.BinaryBasefold.Opening.instChallengeSampleable` [ArkLib/ProofSystem/Binius/BinaryBasefold/Opening.lean:249](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Opening.lean#L249) — (no docstring)
- `instance RingSwitching.Packing.OpeningAdapter.instChallengeSampleable` [ArkLib/ProofSystem/RingSwitching/Packing/OpeningAdapter.lean:120](../../../ArkLib/ProofSystem/RingSwitching/Packing/OpeningAdapter.lean#L120) — Challenge samplers of the context projection followed by the opening.

### `instMessageInterface` (2 declarations, 2 files)

- `instance Binius.BinaryBasefold.Opening.instMessageInterface` [ArkLib/ProofSystem/Binius/BinaryBasefold/Opening.lean:244](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Opening.lean#L244) — (no docstring)
- `instance RingSwitching.Packing.OpeningAdapter.instMessageInterface` [ArkLib/ProofSystem/RingSwitching/Packing/OpeningAdapter.lean:115](../../../ArkLib/ProofSystem/RingSwitching/Packing/OpeningAdapter.lean#L115) — Message interfaces of the context projection followed by the opening.

### `instOracleInterfaceMessagePSpec` (2 declarations, 2 files)

- `instance Sumcheck.Spec.instOracleInterfaceMessagePSpec` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:134](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L134) — Every sent sum-check polynomial uses the univariate evaluation interface.
- `instance Sumcheck.Spec.SingleRound.instOracleInterfaceMessagePSpec` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:173](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L173) — (no docstring)

### `instOutputOracleInterface` (2 declarations, 2 files)

- `instance SendClaim.instOutputOracleInterface` [ArkLib/ProofSystem/Component/SendClaim.lean:64](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L64) — (no docstring)
- `instance SendSingleWitness.instOutputOracleInterface` [ArkLib/ProofSystem/Component/SendWitness.lean:203](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L203) — (no docstring)

### `instSampleableTypeChallengePSpec` (2 declarations, 2 files)

- `instance Fri.Spec.instSampleableTypeChallengePSpec` [ArkLib/ProofSystem/Fri/Spec/Completeness.lean:150](../../../ArkLib/ProofSystem/Fri/Spec/Completeness.lean#L150) — Uniform challenge sampling for the complete folding and query schedule.
- `instance Sumcheck.Spec.SingleRound.instSampleableTypeChallengePSpec` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:183](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L183) — (no docstring)

### `jetDegree` (2 declarations, 2 files)

- `def ReedSolomon.HiddenDerivative.FirstOrderFiniteRateParameters.jetDegree` [ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/FiniteRateParameters.lean:94](../../../ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/FiniteRateParameters.lean#L94) — The total jet-degree cap belonging to a finite rate parameter certificate.
- `def PolynomialDifferential.jetDegree` [ArkLib/Data/Polynomial/Differential/JetDegree.lean:57](../../../ArkLib/Data/Polynomial/Differential/JetDegree.lean#L57) — The individual degree in the formal Hasse variable `Y_j`.

### `knowledgeState` (2 declarations, 2 files)

- `def Interaction.Oracle.Security.RoundExtractor.knowledgeState` [ArkLib/Interaction/Oracle/Security/Knowledge.lean:153](../../../ArkLib/Interaction/Oracle/Security/Knowledge.lean#L153) — The knowledge state at an actual concrete execution prefix.
- `def Spartan.Assembly.knowledgeState` [ArkLib/ProofSystem/Spartan/Security.lean:66](../../../ArkLib/ProofSystem/Spartan/Security.lean#L66) — Stage knowledge predicates for the retained relations. Their semantic sumcheck views and chosen inne

### `lastPathAux` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.lastPathAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:278](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L278) — Index-generic: at the last round every tree is a leaf, so its only path is the empty one.
- `def CoordinateWise.SingleRound.lastPathAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:249](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L249) — Index-generic: at the last round every tree is a leaf, so its only path is the empty one.

### `leftpad` (2 declarations, 2 files)

- `def Fin.leftpad` [ArkLib/Data/Fin/Tuple/Defs.lean:99](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L99) — Pad a `Fin`-indexed vector on the left with an element `a`. This becomes truncation if `n < m`.
- `def Matrix.leftpad` [ArkLib/Data/Matrix/Basic.lean:28](../../../ArkLib/Data/Matrix/Basic.lean#L28) — (no docstring)

### `length` (2 declarations, 2 files)

- `def LinearCode.length` [ArkLib/Data/CodingTheory/Basic/LinearCode.lean:246](../../../ArkLib/Data/CodingTheory/Basic/LinearCode.lean#L246) — The length of a linear code.
- `abbrev Spartan.Assembly.length` [ArkLib/ProofSystem/Spartan/Protocol.lean:77](../../../ArkLib/ProofSystem/Spartan/Protocol.lean#L77) — The lengths of the attachment, challenge, sumcheck, claims, batch, sumcheck, and check.

### `lens` (2 declarations, 2 files)

- `def Spartan.FirstSumcheck.lens` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:49](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L49) — The first sumcheck projects the degree-three virtual polynomial and retains every oracle.
- `def Spartan.SecondSumcheck.lens` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:62](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L62) — The second sumcheck retains the batch and original oracle family at its output.

### `lensKnowledgeSound` (2 declarations, 2 files)

- `instance Plonk.Quotient.lensKnowledgeSound` [ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean:140](../../../ArkLib/ProofSystem/Plonk/Quotient/Reduction.lean#L140) — (no docstring)
- `instance Spartan.FirstSumcheck.lensKnowledgeSound` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:303](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L303) — The virtual-polynomial lens transports knowledge back to the retained Spartan context.

### `liftContext_completeness` (2 declarations, 2 files)

- `theorem OracleReduction.liftContext_completeness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:250](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L250) — (no docstring)
- `theorem Reduction.liftContext_completeness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:612](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L612) — Lifting the reduction preserves completeness, assuming the lens satisfies its completeness condition

### `liftContext_knowledgeSoundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:290](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L290) — Lift knowledge soundness, using a default inner witness if inner extraction fails.
- `theorem Verifier.liftContext_knowledgeSoundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:703](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L703) — Lifting preserves knowledge soundness. A default inner input witness lets the lifted extractor use t

### `liftContext_perfectCompleteness` (2 declarations, 2 files)

- `theorem OracleReduction.liftContext_perfectCompleteness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:258](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L258) — (no docstring)
- `theorem Reduction.liftContext_perfectCompleteness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:645](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L645) — (no docstring)

### `liftContext_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_rbrKnowledgeSoundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:390](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L390) — Lifting preserves the round-by-round knowledge soundness bound.
- `theorem Verifier.liftContext_rbrKnowledgeSoundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:824](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L824) — Context lifting preserves round-by-round knowledge soundness at every fixed prefix with the same err

### `liftContext_rbrKnowledgeSoundnessWith` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_rbrKnowledgeSoundnessWith` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:360](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L360) — Lifting preserves the named certificate and its error function.
- `theorem Verifier.liftContext_rbrKnowledgeSoundnessWith` [ArkLib/OracleReduction/LiftContext/Reduction.lean:796](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L796) — Context lifting preserves the named extractor and knowledge state at every fixed prefix, with the sa

### `liftContext_rbrSoundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_rbrSoundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:312](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L312) — Lifting preserves the round-by-round soundness bound.
- `theorem Verifier.liftContext_rbrSoundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:775](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L775) — Context lifting preserves round-by-round soundness at every fixed prefix with the same error.

### `liftContext_soundness` (2 declarations, 2 files)

- `theorem OracleVerifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:275](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L275) — Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions
- `theorem Verifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:668](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L668) — Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions

### `logView` (2 declarations, 2 files)

- `def Interaction.Oracle.PhasedResult.logView` [ArkLib/Interaction/Oracle/PhasedExecution.lean:69](../../../ArkLib/Interaction/Oracle/PhasedExecution.lean#L69) — Keep the complete chronological world log paired with the source-run observations.
- `def Interaction.Oracle.PhasedRun.logView` [ArkLib/Interaction/Oracle/PhasedRun.lean:53](../../../ArkLib/Interaction/Oracle/PhasedRun.lean#L53) — All paired source observations and the complete world log.

### `mapProgram` (2 declarations, 2 files)

- `def Interaction.Oracle.SourceHom.mapProgram` [ArkLib/Interaction/Oracle/Source.lean:342](../../../ArkLib/Interaction/Oracle/Source.lean#L342) — Route a program with the existing interpreter; no new virtual-oracle package is introduced.
- `def Fri.Spec.Extractor.mapProgram` [ArkLib/ProofSystem/Fri/Spec/Extraction/Traversal.lean:27](../../../ArkLib/ProofSystem/Fri/Spec/Extraction/Traversal.lean#L27) — Traverse an explicit list without executing its certified reference function.

### `mapSource` (2 declarations, 2 files)

- `def Interaction.Oracle.OpenClaim.mapSource` [ArkLib/Interaction/Oracle/Claim.lean:78](../../../ArkLib/Interaction/Oracle/Claim.lean#L78) — Route the source of a claim without altering its public statement.
- `def Interaction.Oracle.VirtualOracle.mapSource` [ArkLib/Interaction/Oracle/Virtual.lean:127](../../../ArkLib/Interaction/Oracle/Virtual.lean#L127) — Map the source along a coherent polynomial source morphism.

### `mem_gammaAgreementSet` (2 declarations, 2 files)

- `theorem ToyProblem.Impl.IRS.mem_gammaAgreementSet` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:217](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L217) — (no docstring)
- `theorem ToyProblem.Spec.mem_gammaAgreementSet` [ArkLib/ProofSystem/ToyProblem/Spec/ErasureDecoder.lean:268](../../../ArkLib/ProofSystem/ToyProblem/Spec/ErasureDecoder.lean#L268) — (no docstring)

### `mem_relIn_iff` (2 declarations, 2 files)

- `theorem Binius.FRIBinius.Conformance.mem_relIn_iff` [ArkLib/ProofSystem/Binius/FRIBinius/Conformance.lean:33](../../../ArkLib/ProofSystem/Binius/FRIBinius/Conformance.lean#L33) — The scalar source claim and the packed first oracle are the shared input relation.
- `theorem RandomEvaluation.mem_relIn_iff` [ArkLib/ProofSystem/Component/RandomEvaluation.lean:76](../../../ArkLib/ProofSystem/Component/RandomEvaluation.lean#L76) — (no docstring)

### `messageInterface` (2 declarations, 2 files)

- `instance Spartan.Assembly.messageInterface` [ArkLib/ProofSystem/Spartan/Protocol.lean:91](../../../ArkLib/ProofSystem/Spartan/Protocol.lean#L91) — (no docstring)
- `def Sumcheck.Interaction.Native.Core.messageInterface` [ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean:35](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Protocol.lean#L35) — Evaluation-only access to the actual round message.

### `monomial` (2 declarations, 2 files)

- `def GuruswamiSudan.monomial` [ArkLib/Data/CodingTheory/GuruswamiSudan/Basic.lean:109](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/Basic.lean#L109) — The monomial X^i Y^j as a bivariate polynomial.
- `theorem MvPolynomial.SupportWeightOffset.monomial` [ArkLib/ToMathlib/MvPolynomial/SupportWeightOffset.lean:60](../../../ArkLib/ToMathlib/MvPolynomial/SupportWeightOffset.lean#L60) — A monomial has allowance `d` when its exponent does. The coefficient is arbitrary; a zero coefficien

### `natDegree_det_le_sum_of_natDegree_le` (2 declarations, 2 files)

- `theorem ProximityGap.natDegree_det_le_sum_of_natDegree_le` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/BWMatrix.lean:121](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/AffineLines/BWMatrix.lean#L121) — The determinant of a square polynomial matrix has natural degree at most the sum of column-wise boun
- `theorem ProximityGap.CurveBW.natDegree_det_le_sum_of_natDegree_le` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/CurveBWMatrix.lean:46](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/CurveBWMatrix.lean#L46) — (no docstring)

### `ne_zero` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomainClass.ne_zero` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:81](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L81) — Every point of a coset FFT domain is nonzero.
- `theorem PolynomialDifferential.SeparantChain.ne_zero` [ArkLib/Data/Polynomial/Differential/SeparantChain.lean:115](../../../ArkLib/Data/Polynomial/Differential/SeparantChain.lean#L115) — The starting equation of a separant chain is nonzero.

### `occurrences` (2 declarations, 2 files)

- `def Plonk.Assembly.occurrences` [ArkLib/ProofSystem/Plonk/Assembly/Data.lean:55](../../../ArkLib/ProofSystem/Plonk/Assembly/Data.lean#L55) — Evaluate an executable table at each wire position.
- `def Plonk.ConstraintSystem.occurrences` [ArkLib/ProofSystem/Plonk/Relation/Basic.lean:26](../../../ArkLib/ProofSystem/Plonk/Relation/Basic.lean#L26) — The occurrence values induced by a full variable assignment.

### `ofIsEmpty` (2 declarations, 2 files)

- `def CWSSStructure.ofIsEmpty` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/NoChallenge.lean:68](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/NoChallenge.lean#L68) — The canonical coordinate-wise structure on a **challenge-free** protocol (`IsEmpty pSpec.ChallengeId
- `def Extractor.RoundByRound.ofIsEmpty` [ArkLib/OracleReduction/Security/RoundByRound.lean:129](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L129) — The extractor with empty intermediate witnesses, available when no input statement, full transcript

### `oracleInterface` (2 declarations, 2 files)

- `instance Spartan.Assembly.oracleInterface` [ArkLib/ProofSystem/Spartan/Protocol.lean:66](../../../ArkLib/ProofSystem/Spartan/Protocol.lean#L66) — (no docstring)
- `instance Spartan.Terminal.oracleInterface` [ArkLib/ProofSystem/Spartan/Terminal.lean:42](../../../ArkLib/ProofSystem/Spartan/Terminal.lean#L42) — (no docstring)

### `oracleProver_outputIsPure` (2 declarations, 2 files)

- `instance Spartan.FirstSumcheck.oracleProver_outputIsPure` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:190](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L190) — The honest prover's final output uses no ambient oracle queries.
- `instance Spartan.SecondSumcheck.oracleProver_outputIsPure` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:212](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L212) — The honest prover's final output uses no ambient oracle queries.

### `oracleVerifier_knowledgeSoundness` (2 declarations, 2 files)

- `theorem Sumcheck.Spec.oracleVerifier_knowledgeSoundness` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:528](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L528) — Ordinary knowledge soundness with the sum of the per-challenge errors.
- `theorem ToyProblem.Impl.IRS.oracleVerifier_knowledgeSoundness` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:989](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L989) — Existential knowledge soundness is retained as a corollary of the public exact-extractor theorem. Th

### `oracles` (2 declarations, 2 files)

- `def Interaction.Oracle.TypeTree.ExecutionPrefix.oracles` [ArkLib/Interaction/Oracle/Prefix.lean:249](../../../ArkLib/Interaction/Oracle/Prefix.lean#L249) — Oracle interfaces restricted to the selected residual, preserving branch dependence.
- `abbrev Interaction.Oracle.Protocol.oracles` [ArkLib/Interaction/Oracle/Protocol.lean:43](../../../ArkLib/Interaction/Oracle/Protocol.lean#L43) — Interfaces at oracle nodes; public nodes carry no interface.

### `outputIndexEmbedding` (2 declarations, 2 files)

- `def SendClaim.outputIndexEmbedding` [ArkLib/ProofSystem/Component/SendClaim.lean:96](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L96) — The oracle verifier for `SendClaim` is a **pure pass-through**: it returns the statement and exposes
- `def SendSingleWitness.outputIndexEmbedding` [ArkLib/ProofSystem/Component/SendWitness.lean:367](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L367) — The index embedding that exposes every input oracle and the single witness message as output oracles

### `outputOracle` (2 declarations, 2 files)

- `def Sumcheck.Interaction.SingleRound.outputOracle` [ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:31](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean#L31) — The output oracle routes queries to the original input polynomial.
- `def Sumcheck.Interaction.MultivariateRound.outputOracle` [ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:39](../../../ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean#L39) — The output oracle retains the original input behavior.

### `outputOracles` (2 declarations, 2 files)

- `def Plonk.Batch.outputOracles` [ArkLib/ProofSystem/Plonk/Batch/Reduction.lean:69](../../../ArkLib/ProofSystem/Plonk/Batch/Reduction.lean#L69) — Materialize all earlier oracles and the new power-weighted residual.
- `def Plonk.GrandProduct.outputOracles` [ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean:62](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Reduction.lean#L62) — Materialized residuals share their underlying retained wire and accumulator data.

### `outputRelationFor` (2 declarations, 2 files)

- `def ToyProblem.Spec.outputRelationFor` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:286](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L286) — The IOR-shaped **fixed-encoding** *relaxed* output relation. The soundness statement of L6.6/6.8 is
- `def ToyProblem.SimplifiedIOR.outputRelationFor` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:122](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L122) — The 1-arity relaxed relation `R̃¹_{C,δ}` — the output relation of the simplified IOR. Bundles the po

### `pSpecFold` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.pSpecFold` [ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean:216](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Spec.lean#L216) — One round polynomial message followed by one scalar challenge.
- `def Fri.Spec.pSpecFold` [ArkLib/ProofSystem/Fri/Spec/General.lean:55](../../../ArkLib/ProofSystem/Fri/Spec/General.lean#L55) — The sequence of non-final folding rounds.

### `package` (2 declarations, 2 files)

- `def CoordinateWise.CommittedScalar.package` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:278](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L278) — Bundled committed scalar phase, ready for CWSS composition. This lands in the **pure, escape-aware**
- `def RingSwitching.Lift.package` [ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean:327](../../../ArkLib/ProofSystem/RingSwitching/Lift/Reduction.lean#L327) — `Lift` as a composable escape-aware CWSS package. Computable: the purity field carries the verdict f

### `perfectCompleteness_and_knowledgeSoundness` (2 declarations, 2 files)

- `theorem RingSwitching.Packing.RingSwitch.perfectCompleteness_and_knowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/Packing/RingSwitch.lean:255](../../../ArkLib/ProofSystem/RingSwitching/Packing/RingSwitch.lean#L255) — The whole reduction is perfectly complete and knowledge sound with error `bat.error + 2m/\|C\|`.
- `theorem RingSwitching.Packing.TensorPrefix.perfectCompleteness_and_knowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/Packing/TensorPrefix.lean:278](../../../ArkLib/ProofSystem/RingSwitching/Packing/TensorPrefix.lean#L278) — Prefix packing is perfectly complete and knowledge sound with error `κ/\|L\| + 2ℓ'/\|L\|`.

### `perfectCompleteness_and_rbrKnowledgeSoundness` (2 declarations, 2 files)

- `theorem RingSwitching.Packing.RingSwitch.perfectCompleteness_and_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/Packing/RingSwitch.lean:226](../../../ArkLib/ProofSystem/RingSwitching/Packing/RingSwitch.lean#L226) — Completeness and round-by-round knowledge soundness with total challenge error `ε + 2m/\|C\|`.
- `theorem RingSwitching.Packing.TensorPrefix.perfectCompleteness_and_rbrKnowledgeSoundness` [ArkLib/ProofSystem/RingSwitching/Packing/TensorPrefix.lean:252](../../../ArkLib/ProofSystem/RingSwitching/Packing/TensorPrefix.lean#L252) — Prefix packing is complete and round-by-round knowledge sound, with total challenge error `κ / card

### `perfect_completeness` (2 declarations, 2 files)

- `theorem BatchedFri.Spec.BatchingRound.perfect_completeness` [ArkLib/ProofSystem/BatchedFri/Security.lean:192](../../../ArkLib/ProofSystem/BatchedFri/Security.lean#L192) — The honest execution preserves the relation with probability one for every radius.
- `theorem Fri.Spec.perfect_completeness` [ArkLib/ProofSystem/Fri/Spec/Completeness.lean:189](../../../ArkLib/ProofSystem/Fri/Spec/Completeness.lean#L189) — Exact input evaluations give perfect completeness for every query count.

### `perfectlyCorrect` (2 declarations, 2 files)

- `theorem ArkLib.Lattices.Ajtai.InnerOuter.perfectlyCorrect` [ArkLib/Commitments/Functional/Hachi/InnerOuter/Correctness.lean:194](../../../ArkLib/Commitments/Functional/Hachi/InnerOuter/Correctness.lean#L194) — **Unconditional perfect correctness with Hachi's balanced decomposition.** Both message and inner de
- `theorem ArkLib.Lattices.Ajtai.Simple.perfectlyCorrect` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Correctness.lean:37](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Correctness.lean#L37) — Simple Ajtai commitments are correct on short messages: an honest commitment to a message accepted b

### `permutationPolynomials` (2 declarations, 2 files)

- `def Plonk.permutationPolynomials` [ArkLib/ProofSystem/Plonk/Encoding/Basic.lean:125](../../../ArkLib/ProofSystem/Plonk/Encoding/Basic.lean#L125) — The three columns of successor labels, using noncomputable interpolation.
- `def Plonk.Computable.permutationPolynomials` [ArkLib/ProofSystem/Plonk/Encoding/Computable.lean:63](../../../ArkLib/ProofSystem/Plonk/Encoding/Computable.lean#L63) — Encode the position labels reached by the wiring permutation.

### `phases` (2 declarations, 2 files)

- `def Interaction.Oracle.PhasedRun.phases` [ArkLib/Interaction/Oracle/PhasedRun.lean:57](../../../ArkLib/Interaction/Oracle/PhasedRun.lean#L57) — Local actions and their concrete stopping boundaries, beginning with setup.
- `def Interaction.Oracle.WorldSegments.phases` [ArkLib/Interaction/Oracle/WorldSegments.lean:96](../../../ArkLib/Interaction/Oracle/WorldSegments.lean#L96) — List actual local actions with their full stopping boundaries. Sender actions occur before crossing

### `phases_flatten` (2 declarations, 2 files)

- `theorem Interaction.Oracle.PhasedRun.phases_flatten` [ArkLib/Interaction/Oracle/PhasedRun.lean:62](../../../ArkLib/Interaction/Oracle/PhasedRun.lean#L62) — The chronological regions account for the whole log without deleting duplicate queries.
- `theorem Interaction.Oracle.WorldSegments.phases_flatten` [ArkLib/Interaction/Oracle/WorldSegments.lean:113](../../../ArkLib/Interaction/Oracle/WorldSegments.lean#L113) — Decorating segments with concrete protocol boundaries preserves their chronological log.

### `phases_reached` (2 declarations, 2 files)

- `theorem Interaction.Oracle.PhasedRun.phases_reached` [ArkLib/Interaction/Oracle/PhasedRun.lean:67](../../../ArkLib/Interaction/Oracle/PhasedRun.lean#L67) — Every action boundary, including setup, extends to the same complete concrete path.
- `theorem Interaction.Oracle.WorldSegments.phases_reached` [ArkLib/Interaction/Oracle/WorldSegments.lean:135](../../../ArkLib/Interaction/Oracle/WorldSegments.lean#L135) — Every recorded action boundary is a concrete prefix of this same complete execution, including agree

### `points` (2 declarations, 2 files)

- `def Plonk.Batch.points` [ArkLib/ProofSystem/Plonk/Batch/Data.lean:26](../../../ArkLib/ProofSystem/Plonk/Batch/Data.lean#L26) — The finite set of row nodes.
- `def SumcheckDomain.points` [ArkLib/ProofSystem/Sumcheck/Domain.lean:68](../../../ArkLib/ProofSystem/Sumcheck/Domain.lean#L68) — The evaluation points of coordinate `i`, as a `Finset R`.

### `polynomial_val` (2 declarations, 2 files)

- `theorem Spartan.FirstSumcheck.polynomial_val` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:43](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L43) — The computational materialization agrees with the semantic first virtual polynomial.
- `theorem Spartan.SecondSumcheck.polynomial_val` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:42](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L42) — The computational materialization has precisely the second virtual polynomial's semantics.

### `pow` (2 declarations, 2 files)

- `theorem MvPolynomial.CoeffNatDegreeLE.pow` [ArkLib/ToMathlib/MvPolynomial/PolynomialCoefficients.lean:318](../../../ArkLib/ToMathlib/MvPolynomial/PolynomialCoefficients.lean#L318) — The `n`-th power multiplies the coefficient degree bound by `n`.
- `theorem MvPolynomial.SupportWeightOffset.pow` [ArkLib/ToMathlib/MvPolynomial/SupportWeightOffset.lean:90](../../../ArkLib/ToMathlib/MvPolynomial/SupportWeightOffset.lean#L90) — The `n`-th power multiplies the allowance by `n`.

### `preparedGatePolynomial` (2 declarations, 2 files)

- `def Plonk.preparedGatePolynomial` [ArkLib/ProofSystem/Plonk/Encoding/Basic.lean:227](../../../ArkLib/ProofSystem/Plonk/Encoding/Basic.lean#L227) — The prepared gate residual uses fixed selectors with cleared public constants. Its mathematical poly
- `def Plonk.Computable.preparedGatePolynomial` [ArkLib/ProofSystem/Plonk/Encoding/Computable.lean:122](../../../ArkLib/ProofSystem/Plonk/Encoding/Computable.lean#L122) — The executable prepared residual uses cleared fixed selectors and the public input once.

### `prepend` (2 declarations, 2 files)

- `def Interaction.Oracle.WorldSegments.prepend` [ArkLib/Interaction/Oracle/WorldSegments.lean:88](../../../ArkLib/Interaction/Oracle/WorldSegments.lean#L88) — Prefix labels on a residual phase are lifted through the already crossed concrete edge.
- `def SumcheckDomain.prepend` [ArkLib/ProofSystem/Sumcheck/Domain.lean:100](../../../ArkLib/ProofSystem/Sumcheck/Domain.lean#L100) — Prepend a coordinate with domain `D₀` in front of an existing `k`-coordinate domain family, yielding

### `prob_badChallenge_le` (2 declarations, 2 files)

- `theorem AffineFactorBadChallenge.prob_badChallenge_le` [ArkLib/Data/Polynomial/AffineFactorBadChallenge.lean:65](../../../ArkLib/Data/Polynomial/AffineFactorBadChallenge.lean#L65) — The chance of a zero factor among `\|U\|` factors is at most `\|U\| / \|F\|`.
- `theorem Plonk.prob_badChallenge_le` [ArkLib/ProofSystem/Plonk/Accumulator/Basic.lean:180](../../../ArkLib/ProofSystem/Plonk/Accumulator/Basic.lean#L180) — At most `3n / \|F\|` of joint uniform challenges have a zero denominator factor.

### `prob_fingerprint_eq_zero_le` (2 declarations, 2 files)

- `theorem PermutationFingerprint.prob_fingerprint_eq_zero_le` [ArkLib/Data/Polynomial/PermutationFingerprint.lean:146](../../../ArkLib/Data/Polynomial/PermutationFingerprint.lean#L146) — A false permutation claim passes a joint uniform challenge with probability at most `(\|U\| - 1) / \|F\|
- `theorem Plonk.ConstraintSystem.prob_fingerprint_eq_zero_le` [ArkLib/ProofSystem/Plonk/Relation/PermutationFingerprint.lean:55](../../../ArkLib/ProofSystem/Plonk/Relation/PermutationFingerprint.lean#L55) — A false copy claim passes a joint uniform challenge with probability at most `(3n - 1) / \|F\|`.

### `projectedRoundPolynomial` (2 declarations, 2 files)

- `def Sumcheck.Impl.Computable.projectedRoundPolynomial` [ArkLib/ProofSystem/Sumcheck/Impl/Projection.lean:60](../../../ArkLib/ProofSystem/Sumcheck/Impl/Projection.lean#L60) — Direct finite enumeration of the honest round polynomial on computable polynomial data. This constru
- `def Sumcheck.Spec.SingleRound.projectedRoundPolynomial` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:604](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L604) — The univariate round polynomial obtained from the multivariate sum-check oracle at round `i`.  This

### `prover_runToRound_last` (2 declarations, 2 files)

- `lemma ArkLib.Lattices.Ajtai.InnerOuter.prover_runToRound_last` [ArkLib/Commitments/Functional/Hachi/QuadEval/Completeness.lean:343](../../../ArkLib/Commitments/Functional/Hachi/QuadEval/Completeness.lean#L343) — **Honest execution of both rounds.** Running the Figure-3 prover to the last round draws the challen
- `lemma CoordinateWise.CommittedScalar.prover_runToRound_last` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:337](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L337) — **Honest execution of both rounds.** Running the prover shell to the last round appends the commitme

### `prover_run_eq` (2 declarations, 2 files)

- `lemma ArkLib.Lattices.Ajtai.InnerOuter.prover_run_eq` [ArkLib/Commitments/Functional/Hachi/QuadEval/Completeness.lean:387](../../../ArkLib/Commitments/Functional/Hachi/QuadEval/Completeness.lean#L387) — **The honest prover's run in closed form.** `prover_runToRound_last` followed by `output`: the prove
- `lemma CoordinateWise.CommittedScalar.prover_run_eq` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:371](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L371) — **The honest prover's run in closed form**: draw `c`, then emit the transcript `⟨K.com w, c⟩`, the o

### `publicInputPolynomial_toPoly` (2 declarations, 2 files)

- `theorem Plonk.Assembly.publicInputPolynomial_toPoly` [ArkLib/ProofSystem/Plonk/Assembly/Data.lean:48](../../../ArkLib/ProofSystem/Plonk/Assembly/Data.lean#L48) — Executable public-input coefficients represent the mathematical public polynomial.
- `theorem Plonk.Computable.publicInputPolynomial_toPoly` [ArkLib/ProofSystem/Plonk/Encoding/Computable.lean:104](../../../ArkLib/ProofSystem/Plonk/Encoding/Computable.lean#L104) — Executable public-input encoding agrees with the mathematical public-input encoding.

### `pullbackWitness` (2 declarations, 2 files)

- `def R1CS.pullbackWitness` [ArkLib/ProofSystem/ConstraintSystem/R1CS.lean:83](../../../ArkLib/ProofSystem/ConstraintSystem/R1CS.lean#L83) — Recover the original witness coordinates from a witness for the enlarged instance.
- `def Spartan.pullbackWitness` [ArkLib/ProofSystem/Spartan/Algebra/Layout.lean:124](../../../ArkLib/ProofSystem/Spartan/Algebra/Layout.lean#L124) — Restrict an enlarged Spartan witness to the original private coordinates.

### `queryBatch` (2 declarations, 2 files)

- `def GeneratorBatch.queryBatch` [ArkLib/ProofSystem/Component/GeneratorBatch.lean:85](../../../ArkLib/ProofSystem/Component/GeneratorBatch.lean#L85) — Answer a virtual batch query by combining the input evaluations.
- `def Plonk.Batch.queryBatch` [ArkLib/ProofSystem/Plonk/Batch/Reduction.lean:141](../../../ArkLib/ProofSystem/Plonk/Batch/Reduction.lean#L141) — The virtual batch is the component's query implementation in the retained context.

### `queryCodeword` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.QueryPhase.queryCodeword` [ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/QueryPhasePrelims.lean:161](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Soundness/QueryPhasePrelims.lean#L161) — The oracle computation that queries the committed oracle at position `j` at a point of its domain.
- `def Fri.Spec.QueryRound.queryCodeword` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:735](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L735) — Query committed word `i` at a point of its evaluation domain.

### `queryOracleReduction` (2 declarations, 2 files)

- `def Binius.BinaryBasefold.QueryPhase.queryOracleReduction` [ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase/Protocol.lean:184](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/QueryPhase/Protocol.lean#L184) — The oracle reduction for the final query phase.
- `def Fri.Spec.QueryRound.queryOracleReduction` [ArkLib/ProofSystem/Fri/Spec/SingleRound.lean:844](../../../ArkLib/ProofSystem/Fri/Spec/SingleRound.lean#L844) — The query reduction with its unchanged final polynomial witness.

### `rbrError_sum` (2 declarations, 2 files)

- `theorem RingSwitching.Packing.RingSwitch.rbrError_sum` [ArkLib/ProofSystem/RingSwitching/Packing/RingSwitch.lean:189](../../../ArkLib/ProofSystem/RingSwitching/Packing/RingSwitch.lean#L189) — The sum of the challenge errors is `ε + 2m/\|C\|`.
- `theorem RingSwitching.Packing.TensorPrefix.rbrError_sum` [ArkLib/ProofSystem/RingSwitching/Packing/TensorPrefix.lean:245](../../../ArkLib/ProofSystem/RingSwitching/Packing/TensorPrefix.lean#L245) — The challenge-index sum is `κ/\|L\| + 2ℓ'/\|L\|`.

### `rbrKnowledgeStateFunction` (2 declarations, 2 files)

- `def ToyProblem.Impl.IRS.rbrKnowledgeStateFunction` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:843](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L843) — Knowledge-state function paired with the executable interleaved-RS round-by-round extractor.  This i
- `def ToyProblem.Spec.rbrKnowledgeStateFunction` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:1220](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L1220) — The round-by-round knowledge state function: relaxed-relation membership at round 0, `GammaState` af

### `rbrWitMid` (2 declarations, 2 files)

- `def ToyProblem.Impl.IRS.rbrWitMid` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:351](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L351) — Intermediate witness types for the executable round-by-round extractor.
- `def ToyProblem.Spec.rbrWitMid` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:1095](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L1095) — L6.8 intermediate witness types: input witness at round 0, the γ-round candidate message during roun

### `readChallenges` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.readChallenges` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:137](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L137) — Read the round-1 sibling-challenge family off a full tree: a two-level peel — the round-0 helper str
- `def CoordinateWise.SingleRound.readChallenges` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:102](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L102) — Read the round-1 sibling-challenge family off a full tree: a two-level peel — the round-0 helper str

### `readChallenges_tree2` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.readChallenges_tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:167](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L167) — The round-1 reader computes on the star tree.
- `theorem CoordinateWise.SingleRound.readChallenges_tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:132](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L132) — The round-1 reader computes on the star tree.

### `readFinalPolynomial` (2 declarations, 2 files)

- `def Fri.Spec.Extractor.readFinalPolynomial` [ArkLib/ProofSystem/Fri/Spec/Extraction/Readers.lean:39](../../../ArkLib/ProofSystem/Fri/Spec/Extraction/Readers.lean#L39) — Read the final polynomial without traversing its coefficients.
- `def Fri.Spec.readFinalPolynomial` [ArkLib/ProofSystem/Fri/Spec/Transcript.lean:267](../../../ArkLib/ProofSystem/Fri/Spec/Transcript.lean#L267) — The final polynomial is a prover message fixed before the query vector.

### `readPre` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.readPre` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:119](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L119) — Read the round-0 message (the pre-challenge prover message) off a full tree.
- `def CoordinateWise.SingleRound.readPre` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:83](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L83) — Read the round-0 message (the pre-challenge carrier commitment) off a full tree.

### `readPre_tree2` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.readPre_tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:162](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L162) — The round-0 reader computes on the star tree.
- `theorem CoordinateWise.SingleRound.readPre_tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:127](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L127) — The round-0 reader computes on the star tree.

### `readWord` (2 declarations, 2 files)

- `def Fri.Spec.Extractor.readWord` [ArkLib/ProofSystem/Fri/Spec/Extraction/Readers.lean:28](../../../ArkLib/ProofSystem/Fri/Spec/Extraction/Readers.lean#L28) — Read one committed-word value at its actual domain point.
- `def Fri.Spec.readWord` [ArkLib/ProofSystem/Fri/Spec/Transcript.lean:196](../../../ArkLib/ProofSystem/Fri/Spec/Transcript.lean#L196) — Read the word committed before a folding challenge. The first word is the input; every later word is

### `recurrenceResidual` (2 declarations, 2 files)

- `def Plonk.Computable.recurrenceResidual` [ArkLib/ProofSystem/Plonk/Accumulator/Computable.lean:85](../../../ArkLib/ProofSystem/Plonk/Accumulator/Computable.lean#L85) — Compute the cyclic residual by substituting `ωX` in the accumulator.
- `def Plonk.recurrenceResidual` [ArkLib/ProofSystem/Plonk/Accumulator/Residual.lean:34](../../../ArkLib/ProofSystem/Plonk/Accumulator/Residual.lean#L34) — The cyclic recurrence residual, using noncomputable Mathlib polynomial arithmetic.

### `reduction_run_support` (2 declarations, 2 files)

- `lemma CoordinateWise.CommittedScalar.reduction_run_support` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:390](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L390) — **Honest-run characterization.** Every element of the support of an honest run is a success determin
- `theorem ReduceClaim.reduction_run_support` [ArkLib/ProofSystem/Component/ReduceClaim.lean:108](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L108) — **The `ReduceClaim` reduction's honest run, in closed form.** A zero-round reduction draws nothing a

### `reduction_verifier_eq_verifier` (2 declarations, 2 files)

- `lemma Sumcheck.Spec.reduction_verifier_eq_verifier` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:458](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L458) — (no docstring)
- `lemma Sumcheck.Spec.SingleRound.reduction_verifier_eq_verifier` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:979](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L979) — (no docstring)

### `refl` (2 declarations, 2 files)

- `def Interaction.Oracle.SourceEquiv.refl` [ArkLib/Interaction/Oracle/Source.lean:377](../../../ArkLib/Interaction/Oracle/Source.lean#L377) — Identity equivalence.
- `def ProtocolSpec.Equiv.refl` [ArkLib/OracleReduction/Equiv.lean:39](../../../ArkLib/OracleReduction/Equiv.lean#L39) — (no docstring)

### `relaxedRelationFor_iff_exists_outputRelationFor` (2 declarations, 2 files)

- `theorem ToyProblem.Spec.relaxedRelationFor_iff_exists_outputRelationFor` [ArkLib/ProofSystem/ToyProblem/Spec/General.lean:312](../../../ArkLib/ProofSystem/ToyProblem/Spec/General.lean#L312) — The language-level relaxed relation `RelaxedRelationFor` is precisely the existential closure of the
- `theorem ToyProblem.SimplifiedIOR.relaxedRelationFor_iff_exists_outputRelationFor` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:132](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L132) — The language-level one-word relaxed relation is precisely the existential closure of the witness-bea

### `rightpad` (2 declarations, 2 files)

- `def Fin.rightpad` [ArkLib/Data/Fin/Tuple/Defs.lean:93](../../../ArkLib/Data/Fin/Tuple/Defs.lean#L93) — Pad a `Fin`-indexed vector on the right with an element `a`. This becomes truncation if `n < m`.
- `def Matrix.rightpad` [ArkLib/Data/Matrix/Basic.lean:24](../../../ArkLib/Data/Matrix/Basic.lean#L24) — (no docstring)

### `roles` (2 declarations, 2 files)

- `def Interaction.Oracle.TypeTree.ExecutionPrefix.roles` [ArkLib/Interaction/Oracle/Prefix.lean:231](../../../ArkLib/Interaction/Oracle/Prefix.lean#L231) — Roles restricted to the exact residual selected by this prefix.
- `abbrev Interaction.Oracle.Protocol.roles` [ArkLib/Interaction/Oracle/Protocol.lean:39](../../../ArkLib/Interaction/Oracle/Protocol.lean#L39) — Roles at public nodes; oracle nodes are implicitly sender-owned.

### `rowProduct` (2 declarations, 2 files)

- `def Spartan.Computable.rowProduct` [ArkLib/ProofSystem/Spartan/Algebra/Computable.lean:28](../../../ArkLib/ProofSystem/Spartan/Algebra/Computable.lean#L28) — Construct the row-product polynomial directly from the matrix-vector product table.
- `def Spartan.Algebra.rowProduct` [ArkLib/ProofSystem/Spartan/Algebra/Identities.lean:35](../../../ArkLib/ProofSystem/Spartan/Algebra/Identities.lean#L35) — The multilinear row-product polynomial `L_M = MLE(Mz)`.

### `rowSum` (2 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.rowSum` [ArkLib/Commitments/Functional/Hachi/RingSwitch/Reduction.lean:452](../../../ArkLib/Commitments/Functional/Hachi/RingSwitch/Reduction.lean#L452) — Mathlib view of `cRowSum`, retained for degree and root-counting proofs.
- `def RingSwitching.Lift.Presentation.rowSum` [ArkLib/ProofSystem/RingSwitching/Lift/Presentation.lean:246](../../../ArkLib/ProofSystem/RingSwitching/Lift/Presentation.lean#L246) — The `i`-th lifted row's left-hand side `∑ⱼ rep(Mᵢⱼ)·rep(zⱼ) ∈ R[X]`, on the semantics of canonical r

### `run_succ` (2 declarations, 2 files)

- `theorem Matrix.ReadOnce.run_succ` [ArkLib/Data/Matrix/ReadOnce.lean:43](../../../ArkLib/Data/Matrix/ReadOnce.lean#L43) — A nonempty program applies its first layer, then runs the remaining layers.
- `theorem Interaction.Oracle.OrderedExecution.run_succ` [ArkLib/Interaction/Oracle/Composition.lean:162](../../../ArkLib/Interaction/Oracle/Composition.lean#L162) — Execution performs the first actual reduction, then either rejects or runs the suffix.

### `run_zero` (2 declarations, 2 files)

- `theorem Matrix.ReadOnce.run_zero` [ArkLib/Data/Matrix/ReadOnce.lean:39](../../../ArkLib/Data/Matrix/ReadOnce.lean#L39) — The empty program is the identity.
- `theorem Interaction.Oracle.OrderedExecution.run_zero` [ArkLib/Interaction/Oracle/Composition.lean:157](../../../ArkLib/Interaction/Oracle/Composition.lean#L157) — A zero-stage execution preserves both the closed claim and private prover state.

### `secondVirtual` (2 declarations, 2 files)

- `def Spartan.Computable.secondVirtual` [ArkLib/ProofSystem/Spartan/Algebra/Computable.lean:118](../../../ArkLib/ProofSystem/Spartan/Algebra/Computable.lean#L118) — Construct the second virtual polynomial from the three matrix slices and assignment.
- `def Spartan.Algebra.secondVirtual` [ArkLib/ProofSystem/Spartan/Algebra/Identities.lean:67](../../../ArkLib/ProofSystem/Spartan/Algebra/Identities.lean#L67) — The second sumcheck polynomial `H_{ρ,r_x}`, with three independent coefficients.

### `selectorPolynomials` (2 declarations, 2 files)

- `def Plonk.selectorPolynomials` [ArkLib/ProofSystem/Plonk/Encoding/Basic.lean:116](../../../ArkLib/ProofSystem/Plonk/Encoding/Basic.lean#L116) — The five selector columns, using noncomputable interpolation.
- `def Plonk.Computable.selectorPolynomials` [ArkLib/ProofSystem/Plonk/Encoding/Computable.lean:49](../../../ArkLib/ProofSystem/Plonk/Encoding/Computable.lean#L49) — Encode the five fixed selector columns.

### `seqCompose_completeness_of_guarded_verifiers` (2 declarations, 2 files)

- `theorem Reduction.seqCompose_completeness_of_guarded_verifiers` [ArkLib/OracleReduction/Composition/Sequential/GuardedNary.lean:84](../../../ArkLib/OracleReduction/Composition/Sequential/GuardedNary.lean#L84) — Pure prover outputs and guarded verifiers compose with the sum of the component errors when every co
- `theorem OracleReduction.seqCompose_completeness_of_guarded_verifiers` [ArkLib/OracleReduction/Composition/Sequential/OracleCompleteness.lean:77](../../../ArkLib/OracleReduction/Composition/Sequential/OracleCompleteness.lean#L77) — Pure prover outputs and guarded ordinary verifiers compose with the sum of the component errors when

### `seqCompose_materializeOutput` (2 declarations, 2 files)

- `theorem OracleVerifier.seqCompose_materializeOutput` [ArkLib/OracleReduction/Composition/Sequential/General.lean:408](../../../ArkLib/OracleReduction/Composition/Sequential/General.lean#L408) — Sequential composition retains an oracle family when every component materializes it unchanged.
- `theorem Sumcheck.Spec.seqCompose_materializeOutput` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:403](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L403) — Sum-check retains the original input polynomial as its output oracle.

### `seqCompose_perfectCompleteness_of_guarded_verifiers` (2 declarations, 2 files)

- `theorem Reduction.seqCompose_perfectCompleteness_of_guarded_verifiers` [ArkLib/OracleReduction/Composition/Sequential/GuardedNary.lean:117](../../../ArkLib/OracleReduction/Composition/Sequential/GuardedNary.lean#L117) — Pure prover outputs and guarded verifiers preserve perfect completeness of a finite sequence when ev
- `theorem OracleReduction.seqCompose_perfectCompleteness_of_guarded_verifiers` [ArkLib/OracleReduction/Composition/Sequential/OracleCompleteness.lean:103](../../../ArkLib/OracleReduction/Composition/Sequential/OracleCompleteness.lean#L103) — Pure prover outputs and guarded ordinary verifiers preserve perfect completeness of a finite oracle-

### `simulateQ_queryBatch` (2 declarations, 2 files)

- `theorem GeneratorBatch.simulateQ_queryBatch` [ArkLib/ProofSystem/Component/GeneratorBatch.lean:94](../../../ArkLib/ProofSystem/Component/GeneratorBatch.lean#L94) — Materializing a virtual query gives the weighted sum of evaluations.
- `theorem Plonk.Batch.simulateQ_queryBatch` [ArkLib/ProofSystem/Plonk/Batch/Reduction.lean:148](../../../ArkLib/ProofSystem/Plonk/Batch/Reduction.lean#L148) — Materializing the reindexed component query gives the degree-tightened batch.

### `simulate_challenge` (2 declarations, 2 files)

- `theorem Sumcheck.Interaction.SingleRound.simulate_challenge` [ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean:197](../../../ArkLib/ProofSystem/Sumcheck/Interaction/Closing.lean#L197) — The source interpreter forwards challenge effects without reordering or interpreting them.
- `theorem Sumcheck.Interaction.MultivariateRound.simulate_challenge` [ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:211](../../../ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean#L211) — Interpreting resource reads leaves the ambient challenge effect unchanged.

### `simulate_sumQueries` (2 declarations, 2 files)

- `theorem Sumcheck.Interaction.MultivariateRound.simulate_sumQueries` [ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:99](../../../ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean#L99) — Sum queries evaluate exactly the sent message, independently of the input behavior.
- `theorem Sumcheck.Interaction.SingleRound.simulate_sumQueries` [ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:96](../../../ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean#L96) — Reading a list of sent evaluations computes exactly their mathematical sum.

### `simulate_terminal` (2 declarations, 2 files)

- `theorem Sumcheck.Interaction.MultivariateRound.simulate_terminal` [ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:119](../../../ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean#L119) — The actual terminal computation reads its next target from the sent message.
- `theorem Sumcheck.Interaction.SingleRound.simulate_terminal` [ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:114](../../../ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean#L114) — The terminal program checks and evaluates the sent polynomial.

### `six_mul_sum` (2 declarations, 2 files)

- `theorem Polynomial.SymbolicInterpolation.six_mul_sum` [ArkLib/Data/Polynomial/SymbolicInterpolationSupport.lean:77](../../../ArkLib/Data/Polynomial/SymbolicInterpolationSupport.lean#L77) — (no docstring)
- `theorem CubicStaircase.six_mul_sum` [ArkLib/ToMathlib/Combinatorics/CubicStaircase.lean:100](../../../ArkLib/ToMathlib/Combinatorics/CubicStaircase.lean#L100) — The unrounded sum has the closed form `6 * ∑ s < n, (s + 1) * (L - s) = n * (n + 1) * (3 * L - 2 * n

### `spec` (2 declarations, 2 files)

- `abbrev Interaction.Oracle.OracleFamily.spec` [ArkLib/Interaction/Oracle/Virtual.lean:43](../../../ArkLib/Interaction/Oracle/Virtual.lean#L43) — The dependent query signature of the explicit interfaces.
- `def OracleInterface.spec` [ArkLib/OracleReduction/OracleInterface.lean:71](../../../ArkLib/OracleReduction/OracleInterface.lean#L71) — (no docstring)

### `stageSpec` (2 declarations, 2 files)

- `def Plonk.Assembly.stageSpec` [ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean:79](../../../ArkLib/ProofSystem/Plonk/Assembly/Reduction.lean#L79) — Stage protocol specifications in execution order.
- `abbrev Spartan.Assembly.stageSpec` [ArkLib/ProofSystem/Spartan/Protocol.lean:82](../../../ArkLib/ProofSystem/Spartan/Protocol.lean#L82) — The protocol of each stage, in transcript order.

### `straightlineExtractor` (2 declarations, 2 files)

- `def Spartan.straightlineExtractor` [ArkLib/ProofSystem/Spartan/Security.lean:125](../../../ArkLib/ProofSystem/Spartan/Security.lean#L125) — Recover the original R1CS witness by restricting the first transcript message, the attached padded w
- `def ToyProblem.Impl.IRS.straightlineExtractor` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:377](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L377) — Named executable straightline extractor used by the public exact-extractor game theorem.  Query logs

### `subgroupUnit` (2 declarations, 2 files)

- `def Domain.CosetFftDomain.subgroupUnit` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:101](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L101) — The subgroup element of a concrete coset domain at an additive index.
- `def Domain.FftDomain.subgroupUnit` [ArkLib/Data/Domain/FftDomain/Defs.lean:63](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L63) — The subgroup element of an FFT domain at an additive index.

### `subgroupUnit_add` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomain.subgroupUnit_add` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:109](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L109) — (no docstring)
- `lemma Domain.FftDomain.subgroupUnit_add` [ArkLib/Data/Domain/FftDomain/Defs.lean:71](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L71) — (no docstring)

### `subgroupUnit_neg` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomain.subgroupUnit_neg` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:115](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L115) — (no docstring)
- `lemma Domain.FftDomain.subgroupUnit_neg` [ArkLib/Data/Domain/FftDomain/Defs.lean:76](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L76) — (no docstring)

### `subgroupUnit_zero` (2 declarations, 2 files)

- `lemma Domain.CosetFftDomain.subgroupUnit_zero` [ArkLib/Data/Domain/CosetFftDomain/Defs.lean:105](../../../ArkLib/Data/Domain/CosetFftDomain/Defs.lean#L105) — (no docstring)
- `lemma Domain.FftDomain.subgroupUnit_zero` [ArkLib/Data/Domain/FftDomain/Defs.lean:67](../../../ArkLib/Data/Domain/FftDomain/Defs.lean#L67) — (no docstring)

### `subst` (2 declarations, 2 files)

- `def Interaction.Oracle.OpenClaim.subst` [ArkLib/Interaction/Oracle/Claim.lean:93](../../../ArkLib/Interaction/Oracle/Claim.lean#L93) — Substitute an upstream virtual view into the downstream claim's programs.
- `def Interaction.Oracle.VirtualOracle.subst` [ArkLib/Interaction/Oracle/Virtual.lean:155](../../../ArkLib/Interaction/Oracle/Virtual.lean#L155) — Compose a derived interface with a downstream view of that interface.

### `substSource` (2 declarations, 2 files)

- `def Interaction.Oracle.OpenClaim.substSource` [ArkLib/Interaction/Oracle/SourceRouting.lean:102](../../../ArkLib/Interaction/Oracle/SourceRouting.lean#L102) — Substitute source programs in a claim, retaining its statement and output family.
- `def Interaction.Oracle.VirtualOracle.substSource` [ArkLib/Interaction/Oracle/Virtual.lean:104](../../../ArkLib/Interaction/Oracle/Virtual.lean#L104) — Substitute query programs for every source query.

### `substWithSuffix` (2 declarations, 2 files)

- `def Interaction.Oracle.OpenClaim.substWithSuffix` [ArkLib/Interaction/Oracle/Claim.lean:108](../../../ArkLib/Interaction/Oracle/Claim.lean#L108) — Substitute the middle interface while retaining independent suffix resources.
- `def Interaction.Oracle.VirtualOracle.substWithSuffix` [ArkLib/Interaction/Oracle/Virtual.lean:171](../../../ArkLib/Interaction/Oracle/Virtual.lean#L171) — Substitution with additional downstream sources kept available.

### `sum` (2 declarations, 2 files)

- `def Interaction.Oracle.SourceCtx.sum` [ArkLib/Interaction/Oracle/Source.lean:74](../../../ArkLib/Interaction/Oracle/Source.lean#L74) — Disjoint query alternatives, realized by a pair of environments. This is signature addition, not a r
- `theorem MvPolynomial.SupportWeightOffset.sum` [ArkLib/ToMathlib/MvPolynomial/SupportWeightOffset.lean:97](../../../ArkLib/ToMathlib/MvPolynomial/SupportWeightOffset.lean#L97) — Finite sums keep a common allowance.

### `sumQueries` (2 declarations, 2 files)

- `def Sumcheck.Interaction.MultivariateRound.sumQueries` [ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:47](../../../ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean#L47) — Query and sum the sent message over the domain in list order.
- `def Sumcheck.Interaction.SingleRound.sumQueries` [ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:56](../../../ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean#L56) — Sum the sent polynomial's answers in the supplied domain order.

### `sum_challengeError` (2 declarations, 2 files)

- `theorem Fri.Spec.sum_challengeError` [ArkLib/ProofSystem/Fri/Spec/BadEvents.lean:158](../../../ArkLib/ProofSystem/Fri/Spec/BadEvents.lean#L158) — Summing over the actual protocol challenges counts every folding error exactly once, followed by the
- `theorem Spartan.sum_challengeError` [ArkLib/ProofSystem/Spartan/Security.lean:196](../../../ArkLib/ProofSystem/Spartan/Security.lean#L196) — The routed challenge schedule sums to the exact Spartan error ledger.

### `sumcheck_verifier_no_inputPolynomial_queries` (2 declarations, 2 files)

- `theorem Spartan.FirstSumcheck.sumcheck_verifier_no_inputPolynomial_queries` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:211](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L211) — The first sumcheck verifier queries only its round messages, never its virtual input.
- `theorem Sumcheck.Spec.sumcheck_verifier_no_inputPolynomial_queries` [ArkLib/ProofSystem/Sumcheck/Spec/General.lean:392](../../../ArkLib/ProofSystem/Sumcheck/Spec/General.lean#L392) — The full sum-check verifier queries only the univariate polynomials sent in the rounds.  It never qu

### `symm` (2 declarations, 2 files)

- `def Interaction.Oracle.SourceEquiv.symm` [ArkLib/Interaction/Oracle/Source.lean:381](../../../ArkLib/Interaction/Oracle/Source.lean#L381) — Reverse an equivalence.
- `def ProtocolSpec.Equiv.symm` [ArkLib/OracleReduction/Equiv.lean:44](../../../ArkLib/OracleReduction/Equiv.lean#L44) — (no docstring)

### `terminal` (2 declarations, 2 files)

- `def Sumcheck.Interaction.MultivariateRound.terminal` [ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean:56](../../../ArkLib/ProofSystem/Sumcheck/Interaction/MultivariateRound.lean#L56) — The terminal statement uses the sent polynomial's evaluation and extends the prefix.
- `def Sumcheck.Interaction.SingleRound.terminal` [ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean:65](../../../ArkLib/ProofSystem/Sumcheck/Interaction/SingleRound.lean#L65) — Query-dependent terminal output; a failed sum check is an explicit rejection.

### `toORelOut` (2 declarations, 2 files)

- `def SendClaim.toORelOut` [ArkLib/ProofSystem/Component/SendClaim.lean:180](../../../ArkLib/ProofSystem/Component/SendClaim.lean#L180) — The output relation of `SendClaim`: the input relation (read off the pass-through oracles at `inl`)
- `def SendSingleWitness.toORelOut` [ArkLib/ProofSystem/Component/SendWitness.lean:487](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L487) — (no docstring)

### `toPolynomial` (2 declarations, 2 files)

- `def ArkLib.Lattices.Hachi.toPolynomial` [ArkLib/Commitments/Functional/Hachi/EvalSplit.lean:202](../../../ArkLib/Commitments/Functional/Hachi/EvalSplit.lean#L202) — Inverse reshape of `toMatrix`: read the `2 ^ nl × 2 ^ nh` matrix back into the `2 ^ (nl + nh)` coeff
- `def ReedSolomon.toPolynomial` [ArkLib/Data/CodingTheory/ReedSolomon.lean:576](../../../ArkLib/Data/CodingTheory/ReedSolomon.lean#L576) — The linear map that maps a Reed-Solomon codeword to its associated polynomial.

### `topMsgAux` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.topMsgAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:108](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L108) — Index-generic round-0 message reader: peel the top `msgNode` of a tree at any index `a` together wit
- `def CoordinateWise.SingleRound.topMsgAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:72](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L72) — Index-generic round-0 message reader: peel the top `msgNode` of a tree at any index `a` together wit

### `transitionStraightlineExtractor` (2 declarations, 2 files)

- `def ToyProblem.Spec.transitionStraightlineExtractor` [ArkLib/ProofSystem/ToyProblem/Spec/KnowledgeSoundness.lean:44](../../../ArkLib/ProofSystem/ToyProblem/Spec/KnowledgeSoundness.lean#L44) — Turn a deterministic transition algorithm reading `(statement, γ, g)` into the straightline extracto
- `def ToyProblem.SimplifiedIOR.transitionStraightlineExtractor` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:335](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L335) — Turn a deterministic C6.9 transition algorithm into the straightline extractor shape used by ArkLib'

### `tree2` (2 declarations, 2 files)

- `def CoordinateWise.ScalarRound.tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:156](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L156) — The star tree: one message node carrying `v`, one challenge node carrying the sibling family, leaves
- `def CoordinateWise.SingleRound.tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:121](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L121) — The star tree: one message node carrying `v`, one challenge node carrying the sibling family, leaves

### `tree_shape` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.tree_shape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:216](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L216) — **Shape recovery.** Every full tree of the two-round scalar `pSpecScalar` is a star tree — one messa
- `theorem CoordinateWise.SingleRound.tree_shape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:183](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L183) — **Shape recovery.** Every full tree of the two-round `pSpec` is a star tree. This is the rewrite tha

### `tree_shape_aux` (2 declarations, 2 files)

- `theorem CoordinateWise.ScalarRound.tree_shape_aux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:200](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L200) — Shape recovery, level 0: every tree at round 0 is a `tree2`.
- `theorem CoordinateWise.SingleRound.tree_shape_aux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:165](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L165) — Shape recovery, level 0: every tree at round 0 is a `tree2`.

### `unflatten` (2 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.unflatten` [ArkLib/Commitments/Functional/Hachi/RingSwitch/Rlin.lean:117](../../../ArkLib/Commitments/Functional/Hachi/RingSwitch/Rlin.lean#L117) — Un-flatten a row-major block vector into blocks — the inverse of `PolyVec.flattenBlocks`.
- `def ToyProblem.Impl.IRS.unflatten` [ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean:83](../../../ArkLib/ProofSystem/ToyProblem/Impl/IRS.lean#L83) — Split a length-`k` scalar message into `s` rows of length `k / s`.

### `vecL2NormSq` (2 declarations, 2 files)

- `def ArkLib.Lattices.CyclotomicModulus.vecL2NormSq` [ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean:125](../../../ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean#L125) — Centered squared-`ℓ₂` norm of a vector: the sum of entrywise norms.
- `def ArkLib.Lattices.CenteredCoeffView.vecL2NormSq` [ArkLib/Data/Lattices/CyclotomicRing/Norms.lean:84](../../../ArkLib/Data/Lattices/CyclotomicRing/Norms.lean#L84) — Vector squared `ℓ₂` norm: the sum of entrywise squared `ℓ₂` norms.

### `verifierLocalView` (2 declarations, 2 files)

- `def Interaction.Oracle.LoggedRun.verifierLocalView` [ArkLib/Interaction/Oracle/LoggedRun.lean:53](../../../ArkLib/Interaction/Oracle/LoggedRun.lean#L53) — Verifier observations derived from the enclosing execution's log, without replay. This view contains
- `def Interaction.Oracle.TerminalRun.verifierLocalView` [ArkLib/Interaction/Oracle/TerminalRun.lean:110](../../../ArkLib/Interaction/Oracle/TerminalRun.lean#L110) — The local view is read from this result's source log, never obtained by replay.

### `verifierPureForm` (2 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.InnerOuter.verifierPureForm` [ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean:446](../../../ArkLib/Commitments/Functional/Hachi/QuadEval/Reduction.lean#L446) — **The pass-through verifier's purity as data** (`Verifier.PureForm`): the verdict is the pass-throug
- `def CoordinateWise.CommittedScalar.verifierPureForm` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean:246](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/CommittedScalar.lean#L246) — The committed-scalar verifier's purity **as data**: its verdict is the input statement extended by t

### `verifierQueryImpl` (2 declarations, 2 files)

- `def Spartan.FirstSumcheck.verifierQueryImpl` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:81](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L81) — Route the virtual input to its finite-table program and forward every other query.
- `def Sumcheck.Spec.SingleRound.verifierQueryImpl` [ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean:865](../../../ArkLib/ProofSystem/Sumcheck/Spec/SingleRound.lean#L865) — The verifier forwards base and message queries.  Its univariate input handler is unreachable because

### `verifier_coordinateWiseSpecialSoundWith` (2 declarations, 2 files)

- `theorem ReduceClaim.verifier_coordinateWiseSpecialSoundWith` [ArkLib/ProofSystem/Component/ReduceClaim.lean:209](../../../ArkLib/ProofSystem/Component/ReduceClaim.lean#L209) — **Coordinate-wise special soundness of `ReduceClaim`, named form.** The verifier is pure with no cha
- `theorem SendWitness.verifier_coordinateWiseSpecialSoundWith` [ArkLib/ProofSystem/Component/SendWitness.lean:137](../../../ArkLib/ProofSystem/Component/SendWitness.lean#L137) — **Coordinate-wise special soundness of `SendWitness`, named form.** The verifier has no challenge ro

### `verifier_knowledgeSoundness` (2 declarations, 2 files)

- `theorem Binius.FRIBinius.RingSwitch.verifier_knowledgeSoundness` [ArkLib/ProofSystem/Binius/FRIBinius/RingSwitch.lean:248](../../../ArkLib/ProofSystem/Binius/FRIBinius/RingSwitch.lean#L248) — The frontend is ordinarily knowledge sound for first-oracle compatibility.
- `theorem ToyProblem.SimplifiedIOR.verifier_knowledgeSoundness` [ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean:559](../../../ArkLib/ProofSystem/ToyProblem/Spec/SimplifiedIOR.lean#L559) — Legacy alphabet-generic straightline knowledge-soundness existence theorem for C6.9. It uses the non

### `verifier_toVerifier` (2 declarations, 2 files)

- `theorem RingSwitching.Packing.ProductSumcheck.verifier_toVerifier` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/SeqCompose.lean:102](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/SeqCompose.lean#L102) — Materialization commutes with loop-to-terminal composition.
- `theorem RingSwitching.Packing.RingSwitch.verifier_toVerifier` [ArkLib/ProofSystem/RingSwitching/Packing/RingSwitch.lean:101](../../../ArkLib/ProofSystem/RingSwitching/Packing/RingSwitch.lean#L101) — Materialization commutes with oracle-verifier append.

### `verifier_verify` (2 declarations, 2 files)

- `theorem RingSwitching.Packing.ProductSumcheck.Round.verifier_verify` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean:116](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean#L116) — Round verification with a clear polynomial message and preserved input oracles.
- `theorem RingSwitching.Packing.ProductSumcheck.Terminal.verifier_verify` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean:98](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Terminal.lean#L98) — Exact materialized execution, including absorbing rejection and oracle forwarding.

### `verify` (2 declarations, 2 files)

- `def ArkLib.Lattices.Ajtai.Simple.verify` [ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean:50](../../../ArkLib/Commitments/Ordinary/Ajtai/Simple/Scheme.lean#L50) — Verify a simple Ajtai opening by checking the matrix product.
- `def SimpleRO.verify` [ArkLib/Commitments/Ordinary/SimpleRO.lean:53](../../../ArkLib/Commitments/Ordinary/SimpleRO.lean#L53) — Verify an opening `r` of the commitment `cm` to message `v` by recomputing the hash.

### `wirePolynomials` (2 declarations, 2 files)

- `def Plonk.wirePolynomials` [ArkLib/ProofSystem/Plonk/Encoding/Basic.lean:72](../../../ArkLib/ProofSystem/Plonk/Encoding/Basic.lean#L72) — Three degree-bounded witness columns, obtained by noncomputable interpolation.
- `def Plonk.Computable.wirePolynomials` [ArkLib/ProofSystem/Plonk/Encoding/Computable.lean:58](../../../ArkLib/ProofSystem/Plonk/Encoding/Computable.lean#L58) — Encode the three occurrence columns.

### `aeval_monomialLift_iff` (2 declarations, 2 files)

- `theorem MvPolynomial.aeval_monomialLift_iff` [ArkLib/ToMathlib/RingTheory/Nullstellensatz/CappedBidegreeIncidence.lean:42](../../../ArkLib/ToMathlib/RingTheory/Nullstellensatz/CappedBidegreeIncidence.lean#L42) — (no docstring)
- `theorem MvPolynomial.aeval_monomialLift_iff` [ArkLib/ToMathlib/RingTheory/Nullstellensatz/CappedDegreeIncidence.lean:42](../../../ArkLib/ToMathlib/RingTheory/Nullstellensatz/CappedDegreeIncidence.lean#L42) — (no docstring)

### `finRange_val` (2 declarations, 2 files)

- `theorem CompPoly.Arithmetic.finRange_val` [ArkLib/ToCompPoly/Univariate/ArithmeticInterpolation.lean:42](../../../ArkLib/ToCompPoly/Univariate/ArithmeticInterpolation.lean#L42) — (no docstring)
- `theorem CompPoly.Arithmetic.finRange_val` [ArkLib/ToCompPoly/Univariate/ArithmeticInterpolationBound.lean:54](../../../ArkLib/ToCompPoly/Univariate/ArithmeticInterpolationBound.lean#L54) — (no docstring)

### `toList_zipIdx_eq_range` (2 declarations, 2 files)

- `theorem CompPoly.Arithmetic.toList_zipIdx_eq_range` [ArkLib/ToCompPoly/Univariate/ArithmeticEvaluation.lean:67](../../../ArkLib/ToCompPoly/Univariate/ArithmeticEvaluation.lean#L67) — (no docstring)
- `theorem CompPoly.Arithmetic.toList_zipIdx_eq_range` [ArkLib/ToCompPoly/Univariate/ArithmeticPolynomial.lean:150](../../../ArkLib/ToCompPoly/Univariate/ArithmeticPolynomial.lean#L150) — (no docstring)

### `two_mul_ncard_cast` (2 declarations, 2 files)

- `theorem MvPolynomial.two_mul_ncard_cast` [ArkLib/ToMathlib/RingTheory/MvPolynomial/AffineHilbertCappedBidegree.lean:79](../../../ArkLib/ToMathlib/RingTheory/MvPolynomial/AffineHilbertCappedBidegree.lean#L79) — For `C ≤ B`, twice the number of capped exponents on `Fin 2` with bounds `(B, C)`, cast to `ℚ`.
- `theorem MvPolynomial.two_mul_ncard_cast` [ArkLib/ToMathlib/RingTheory/MvPolynomial/AffineHilbertCappedDegree.lean:74](../../../ArkLib/ToMathlib/RingTheory/MvPolynomial/AffineHilbertCappedDegree.lean#L74) — For `C ≤ B`, twice the number of capped exponents on `Fin 2` with bounds `(B, C)`, cast to `ℚ`.

## Near-duplicate docstrings (Jaccard ≥ 0.85, 79 cross-file pairs)

Each pair has docstrings sharing a high fraction of (4+-letter) words, in different files. Most are unrelated coincidences in boilerplate; look for pairs where the *concept* matches.

- **1.00** `Binius.BinaryBasefold.firstOracleInterface_functional` [ArkLib/ProofSystem/Binius/BinaryBasefold/Commitment.lean:185](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Commitment.lean#L185) vs `Binius.BinaryBasefold.Opening.abstractInput_functional` [ArkLib/ProofSystem/Binius/BinaryBasefold/Opening.lean:361](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Opening.lean#L361)
    - a: Unique-radius compatibility determines the committed polynomial.
    - b: Unique-radius compatibility determines the committed polynomial.
- **1.00** `Binius.BinaryBasefold.firstOracleInterface_strictInitialCompatibility_honest` [ArkLib/ProofSystem/Binius/BinaryBasefold/Commitment.lean:192](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Commitment.lean#L192) vs `Binius.BinaryBasefold.Opening.abstractInput_strictInitialCompatibility_honest` [ArkLib/ProofSystem/Binius/BinaryBasefold/Opening.lean:367](../../../ArkLib/ProofSystem/Binius/BinaryBasefold/Opening.lean#L367)
    - a: Every source has an exact first-oracle encoding in this interface.
    - b: Every source has an exact first-oracle encoding in this interface.
- **1.00** `CoordinateWise.ScalarRound.branch_mem` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:264](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L264) vs `CoordinateWise.SingleRound.branch_mem` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:233](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L233)
    - a: Branch `j`'s transcript is one of the star tree's leaf transcripts.
    - b: Branch `j`'s transcript is one of the star tree's leaf transcripts.
- **1.00** `CoordinateWise.ScalarRound.branch_pre` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:249](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L249) vs `CoordinateWise.SingleRound.branch_pre` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:218](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L218)
    - a: Branch `j`'s transcript carries the shared message `v` at round 0.
    - b: Branch `j`'s transcript carries the shared message `v` at round 0.
- **1.00** `CoordinateWise.ScalarRound.branch_relOut_language` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:361](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L361) vs `CoordinateWise.SingleRound.branch_relOut_language` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:392](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L392)
    - a: Acceptance of the star tree specializes, per branch `j`, to membership of the branch's verifier outp
    - b: Acceptance of the star tree specializes, per branch `j`, to membership of the branch's verifier outp
- **1.00** `CoordinateWise.ScalarRound.chalPathAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:285](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L285) vs `CoordinateWise.SingleRound.chalPathAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:256](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L256)
    - a: Index-generic round-1 branch path: descend into sibling `j` of the challenge node.
    - b: Index-generic round-1 branch path: descend into sibling `j` of the challenge node.
- **1.00** `CoordinateWise.ScalarRound.chal_shape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:182](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L182) vs `CoordinateWise.SingleRound.chal_shape` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:147](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L147)
    - a: Shape recovery, level 1: every subtree at round 1 is a `chalNode` over leaves.
    - b: Shape recovery, level 1: every subtree at round 1 is a `chalNode` over leaves.
- **1.00** `CoordinateWise.ScalarRound.eq_leaf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:172](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L172) vs `CoordinateWise.SingleRound.eq_leaf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:137](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L137)
    - a: Shape recovery, level 2: every subtree at the last round is a leaf.
    - b: Shape recovery, level 2: every subtree at the last round is a leaf.
- **1.00** `CoordinateWise.ScalarRound.lastPathAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:278](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L278) vs `CoordinateWise.SingleRound.lastPathAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:249](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L249)
    - a: Index-generic: at the last round every tree is a leaf, so its only path is the empty one.
    - b: Index-generic: at the last round every tree is a leaf, so its only path is the empty one.
- **1.00** `CoordinateWise.ScalarRound.readChallenges` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:137](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L137) vs `CoordinateWise.SingleRound.readChallenges` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:102](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L102)
    - a: Read the round-1 sibling-challenge family off a full tree: a two-level peel — the round-0 helper str
    - b: Read the round-1 sibling-challenge family off a full tree: a two-level peel — the round-0 helper str
- **1.00** `CoordinateWise.ScalarRound.readChallenges_tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:167](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L167) vs `CoordinateWise.SingleRound.readChallenges_tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:132](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L132)
    - a: The round-1 reader computes on the star tree.
    - b: The round-1 reader computes on the star tree.
- **1.00** `CoordinateWise.ScalarRound.readPre_tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:162](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L162) vs `CoordinateWise.SingleRound.readPre_tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:127](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L127)
    - a: The round-0 reader computes on the star tree.
    - b: The round-0 reader computes on the star tree.
- **1.00** `CoordinateWise.ScalarRound.topMsgAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:108](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L108) vs `CoordinateWise.SingleRound.topMsgAux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:72](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L72)
    - a: Index-generic round-0 message reader: peel the top `msgNode` of a tree at any index `a` together wit
    - b: Index-generic round-0 message reader: peel the top `msgNode` of a tree at any index `a` together wit
- **1.00** `CoordinateWise.ScalarRound.tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:156](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L156) vs `CoordinateWise.SingleRound.tree2` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:121](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L121)
    - a: The star tree: one message node carrying `v`, one challenge node carrying the sibling family, leaves
    - b: The star tree: one message node carrying `v`, one challenge node carrying the sibling family, leaves
- **1.00** `CoordinateWise.ScalarRound.tree_shape_aux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:200](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L200) vs `CoordinateWise.SingleRound.tree_shape_aux` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:165](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L165)
    - a: Shape recovery, level 0: every tree at round 0 is a `tree2`.
    - b: Shape recovery, level 0: every tree at round 0 is a `tree2`.
- **1.00** `GeneratorBatch.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Component/GeneratorBatch.lean:177](../../../ArkLib/ProofSystem/Component/GeneratorBatch.lean#L177) vs `QuotientZeroTest.oracleReduction_perfectCompleteness` [ArkLib/ProofSystem/Component/QuotientZeroTest.lean:198](../../../ArkLib/ProofSystem/Component/QuotientZeroTest.lean#L198)
    - a: Perfect completeness for every ambient oracle implementation and initial state.
    - b: Perfect completeness for every ambient oracle implementation and initial state.
- **1.00** `GeneratorBatch.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/GeneratorBatch.lean:238](../../../ArkLib/ProofSystem/Component/GeneratorBatch.lean#L238) vs `QuotientZeroTest.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/QuotientZeroTest.lean:256](../../../ArkLib/ProofSystem/Component/QuotientZeroTest.lean#L256)
    - a: Existential form of the named fixed-prefix knowledge certificate.
    - b: Existential form of the named fixed-prefix knowledge certificate.
- **1.00** `Groups.exists_zmod_power_of_generator` [ArkLib/Commitments/Functional/KZG/Algebra.lean:108](../../../ArkLib/Commitments/Functional/KZG/Algebra.lean#L108) vs `KZG.CommitmentScheme.binding_exists_zmod_power_of_generator` [ArkLib/Commitments/Functional/KZG/Binding.lean:177](../../../ArkLib/Commitments/Functional/KZG/Binding.lean#L177)
    - a: Every element of a prime-order group is a `ZMod p` power of a nontrivial generator.
    - b: Every element of a prime-order group is a `ZMod p` power of a nontrivial generator.
- **1.00** `Groups.orderOf_eq_prime_of_ne_one` [ArkLib/Commitments/Functional/KZG/Algebra.lean:64](../../../ArkLib/Commitments/Functional/KZG/Algebra.lean#L64) vs `KZG.CommitmentScheme.binding_order_of_eq_prime_of_ne_one` [ArkLib/Commitments/Functional/KZG/Binding.lean:167](../../../ArkLib/Commitments/Functional/KZG/Binding.lean#L167)
    - a: A nontrivial element of a prime-order group has order `p`.
    - b: A nontrivial element of a prime-order group has order `p`.
- **1.00** `Interaction.Oracle.PhasedRun.terminalClosed_eq_reject_iff` [ArkLib/Interaction/Oracle/PhasedRun.lean:298](../../../ArkLib/Interaction/Oracle/PhasedRun.lean#L298) vs `Interaction.Oracle.TerminalRun.closed_eq_reject_iff` [ArkLib/Interaction/Oracle/TerminalRun.lean:87](../../../ArkLib/Interaction/Oracle/TerminalRun.lean#L87)
    - a: Closing cannot create or erase verifier rejection.
    - b: Closing cannot create or erase verifier rejection.
- **1.00** `Interaction.Oracle.executeStrategiesLogged` [ArkLib/Interaction/Oracle/LoggedExecution.lean:117](../../../ArkLib/Interaction/Oracle/LoggedExecution.lean#L117) vs `Interaction.Oracle.executeStrategiesPhased` [ArkLib/Interaction/Oracle/PhasedExecution.lean:80](../../../ArkLib/Interaction/Oracle/PhasedExecution.lean#L80)
    - a: Execute restricted strategies in the paired runner's ownership order, logging each verifier local ac
    - b: Execute restricted strategies in the paired runner's ownership order, logging each verifier local ac
- **1.00** `KZG.CommitmentScheme.map_binding_instance_drag` [ArkLib/Commitments/Functional/KZG/Binding.lean:645](../../../ArkLib/Commitments/Functional/KZG/Binding.lean#L645) vs `KZG.CommitmentScheme.map_instance_drag` [ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean:526](../../../ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean#L526)
    - a: Transition 3: dragging the map into the probability event.
    - b: Transition 3: dragging the map into the probability event
- **1.00** `MvPolynomial.cappedBidegreeExponents.finite` [ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedBidegree.lean:166](../../../ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedBidegree.lean#L166) vs `MvPolynomial.cappedDegreeExponents.finite` [ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedDegree.lean:122](../../../ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedDegree.lean#L122)
    - a: The capped exponents form a finite set when `σ` is finite.
    - b: The capped exponents form a finite set when `σ` is finite.
- **1.00** `MvPolynomial.cappedBidegreeExponents_add_subset` [ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedBidegree.lean:131](../../../ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedBidegree.lean#L131) vs `MvPolynomial.cappedDegreeExponents_add_subset` [ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedDegree.lean:104](../../../ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedDegree.lean#L104)
    - a: The bounds of capped exponents add under addition.
    - b: The bounds of capped exponents add under addition.
- **1.00** `MvPolynomial.monomialMap_cappedBidegreeExponents_surjective` [ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedBidegree.lean:233](../../../ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedBidegree.lean#L233) vs `MvPolynomial.monomialMap_cappedDegreeExponents_surjective` [ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedDegree.lean:158](../../../ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedDegree.lean#L158)
    - a: For positive `a`, `b` and `c`, the monomial map of the capped exponents is surjective.
    - b: For positive `b` and `c`, the monomial map of the capped exponents is surjective.
- **1.00** `MvPolynomial.mul_mem_restrictCappedBidegree` [ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedBidegree.lean:216](../../../ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedBidegree.lean#L216) vs `MvPolynomial.mul_mem_restrictCappedDegree` [ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedDegree.lean:142](../../../ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedDegree.lean#L142)
    - a: The bounds of capped polynomials add under multiplication.
    - b: The bounds of capped polynomials add under multiplication.
- **1.00** `MvPolynomial.restrictCappedBidegree.moduleFinite` [ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedBidegree.lean:238](../../../ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedBidegree.lean#L238) vs `MvPolynomial.restrictCappedDegree.moduleFinite` [ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedDegree.lean:163](../../../ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedDegree.lean#L163)
    - a: With finitely many variables, the capped polynomials form a finite module.
    - b: With finitely many variables, the capped polynomials form a finite module.
- **1.00** `MvPolynomial.single_mem_cappedBidegreeExponents` [ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedBidegree.lean:123](../../../ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedBidegree.lean#L123) vs `MvPolynomial.single_mem_cappedDegreeExponents` [ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedDegree.lean:96](../../../ArkLib/ToMathlib/RingTheory/MvPolynomial/CappedDegree.lean#L96)
    - a: For positive `a`, `b` and `c`, the exponent `Finsupp.single v 1` is a capped exponent.
    - b: For positive `b` and `c`, the exponent `Finsupp.single v 1` is a capped exponent.
- **1.00** `OracleVerifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/OracleReduction.lean:275](../../../ArkLib/OracleReduction/LiftContext/OracleReduction.lean#L275) vs `Verifier.liftContext_soundness` [ArkLib/OracleReduction/LiftContext/Reduction.lean:668](../../../ArkLib/OracleReduction/LiftContext/Reduction.lean#L668)
    - a: Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions
    - b: Lifting the reduction preserves soundness, assuming the lens satisfies its soundness conditions
- **1.00** `Plonk.Batch.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Plonk/Batch/Reduction.lean:306](../../../ArkLib/ProofSystem/Plonk/Batch/Reduction.lean#L306) vs `Plonk.GrandProduct.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Plonk/GrandProduct/Security.lean:100](../../../ArkLib/ProofSystem/Plonk/GrandProduct/Security.lean#L100)
    - a: Existential packaging of the named fixed-prefix certificate.
    - b: Existential packaging of the named fixed-prefix certificate.
- **1.00** `Prover.runToRound` [ArkLib/OracleReduction/Execution.lean:77](../../../ArkLib/OracleReduction/Execution.lean#L77) vs `Prover.runToRoundFS` [ArkLib/OracleReduction/FiatShamir/Basic.lean:125](../../../ArkLib/OracleReduction/FiatShamir/Basic.lean#L125)
    - a: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
    - b: Run the prover in an interactive reduction up to round index `i`, via first inputting the statement
- **1.00** `RandomEvaluation.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/RandomEvaluation.lean:144](../../../ArkLib/ProofSystem/Component/RandomEvaluation.lean#L144) vs `RandomQuery.oracleVerifier_rbrKnowledgeSoundness` [ArkLib/ProofSystem/Component/RandomQuery.lean:215](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L215)
    - a: Fixed-prefix round-by-round knowledge soundness, with error `d / |F|`.
    - b: Fixed-prefix round-by-round knowledge soundness with error `ε`.
- **1.00** `RandomEvaluation.rbrExtractor` [ArkLib/ProofSystem/Component/RandomEvaluation.lean:65](../../../ArkLib/ProofSystem/Component/RandomEvaluation.lean#L65) vs `RandomQuery.rbrExtractor` [ArkLib/ProofSystem/Component/RandomQuery.lean:120](../../../ArkLib/ProofSystem/Component/RandomQuery.lean#L120)
    - a: The round-by-round extractor retains the unique witness.
    - b: The round-by-round extractor retains the unique witness.
- **1.00** `Reduction.append_completeness_of_prover_factorization` [ArkLib/OracleReduction/Composition/Sequential/Append/Completeness.lean:98](../../../ArkLib/OracleReduction/Composition/Sequential/Append/Completeness.lean#L98) vs `Reduction.append_completeness_of_guarded_prover_factorization` [ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean:116](../../../ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean#L116)
    - a: Quantitative completeness from equality of simulated prover programs at every input and initial shar
    - b: Quantitative completeness from equality of simulated prover programs at every input and initial shar
- **1.00** `ReedSolomon.FirstOrder.Squarefree.singularCurveEquation_ne_zero` [ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/RetainedTail.lean:468](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/RetainedTail.lean#L468) vs `ReedSolomon.FirstOrder.Squarefree.singularEquation_ne_zero` [ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/TailBound.lean:612](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FirstOrder/Squarefree/TailBound.lean#L612)
    - a: The singular equation is nonzero when the derivative resultant is protected by the characteristic bo
    - b: The singular equation is nonzero when the derivative resultant is protected by the characteristic bo
- **1.00** `ReedSolomon.exists_mathematicalUniformRatePartition_baseCurve_exactPowerAgreement` [ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/MathematicalUniformRate.lean:94](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/MathematicalUniformRate.lean#L94) vs `ReedSolomon.exists_uniformRatePartition_baseCurve_exactPowerAgreement` [ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/UniformRate.lean:85](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/UniformRate.lean#L85)
    - a: The extension-field curve bound descends to challenges and candidates over the base field.
    - b: The extension-field curve bound descends to challenges and candidates over the base field.
- **1.00** `ReedSolomon.frobeniusRetainedPairFamily` [ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FrobeniusRetainedFamily.lean:44](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FrobeniusRetainedFamily.lean#L44) vs `ReedSolomon.frobeniusRetainedPowerTupleFamily` [ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedFrobeniusFamily.lean:46](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedFrobeniusFamily.lean#L46)
    - a: The sample interpolants that satisfy the Frobenius graph identities.
    - b: The sample interpolants that satisfy the Frobenius graph identities.
- **1.00** `ReedSolomon.mem_frobeniusRetainedPairFamily_iff` [ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FrobeniusRetainedFamily.lean:53](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FrobeniusRetainedFamily.lean#L53) vs `ReedSolomon.mem_frobeniusRetainedPowerTupleFamily_iff` [ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedFrobeniusFamily.lean:56](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedFrobeniusFamily.lean#L56)
    - a: Membership in the retained family is equivalent to Frobenius admissibility.
    - b: Membership in the retained family is equivalent to Frobenius admissibility.
- **1.00** `RingSwitching.Packing.Head.ProverState` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:157](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L157) vs `RingSwitching.Packing.ProductSumcheck.Round.ProverState` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean:76](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean#L76)
    - a: The honest state family at a fixed commitment oracle interface.
    - b: The honest state family at a fixed commitment oracle interface.
- **1.00** `RingSwitching.Packing.Head.proverForOracles` [ArkLib/ProofSystem/RingSwitching/Packing/Head.lean:140](../../../ArkLib/ProofSystem/RingSwitching/Packing/Head.lean#L140) vs `RingSwitching.Packing.ProductSumcheck.Round.proverForOracles` [ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean:61](../../../ArkLib/ProofSystem/RingSwitching/Packing/ProductSumcheck/Round.lean#L61)
    - a: The honest round algorithm depends only on the oracle family, independently of compatibility.
    - b: The honest round algorithm depends only on the oracle family, independently of compatibility.
- **1.00** `Spartan.FirstSumcheck.InnerCertificate` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:345](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L345) vs `Spartan.SecondSumcheck.InnerCertificate` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:348](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L348)
    - a: The data and bound furnished by the general sumcheck knowledge theorem.
    - b: The data and bound furnished by the general sumcheck knowledge theorem.
- **1.00** `Spartan.FirstSumcheck.contextLens_complete` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:250](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L250) vs `Spartan.SecondSumcheck.contextLens_complete` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:252](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L252)
    - a: Honest execution retains the materialized virtual polynomial when lifting completeness.
    - b: Honest execution retains the materialized virtual polynomial when lifting completeness.
- **1.00** `Spartan.FirstSumcheck.innerCertificate` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:363](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L363) vs `Spartan.SecondSumcheck.innerCertificate` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:366](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L366)
    - a: Choose the witness family, extractor, and state supplied by the proved general sumcheck certificate.
    - b: Choose the witness family, extractor, and state supplied by the proved general sumcheck certificate.
- **1.00** `Spartan.FirstSumcheck.intermediateWitness` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:370](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L370) vs `Spartan.SecondSumcheck.intermediateWitness` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:373](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L373)
    - a: The retained terminal witness paired with the chosen inner sumcheck witness family.
    - b: The retained terminal witness paired with the chosen inner sumcheck witness family.
- **1.00** `Spartan.FirstSumcheck.knowledgeStateFunction` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:385](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L385) vs `Spartan.SecondSumcheck.knowledgeStateFunction` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:388](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L388)
    - a: The inner semantic knowledge state transported through the virtual-polynomial lens. The underlying c
    - b: The inner semantic knowledge state transported through the virtual-polynomial lens. The underlying c
- **1.00** `Spartan.FirstSumcheck.oracleProver` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:177](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L177) vs `Spartan.SecondSumcheck.oracleProver` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:199](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L199)
    - a: The honest prover computes every round message and output target.
    - b: The honest prover computes every round message and output target.
- **1.00** `Spartan.FirstSumcheck.oracleProver_outputIsPure` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:190](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L190) vs `Spartan.SecondSumcheck.oracleProver_outputIsPure` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:212](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L212)
    - a: The honest prover's final output uses no ambient oracle queries.
    - b: The honest prover's final output uses no ambient oracle queries.
- **1.00** `Spartan.FirstSumcheck.oracleReduction_toReduction` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:237](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L237) vs `Spartan.SecondSumcheck.oracleReduction_toReduction` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:239](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L239)
    - a: Materializing the implemented reduction gives the ordinary context lift of sumcheck.
    - b: Materializing the implemented reduction gives the ordinary context lift of sumcheck.
- **1.00** `Spartan.FirstSumcheck.rbrExtractor` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:376](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L376) vs `Spartan.SecondSumcheck.rbrExtractor` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:379](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L379)
    - a: The chosen inner extractor lifted through the explicit virtual-polynomial lens. Its only noncomputab
    - b: The chosen inner extractor lifted through the explicit virtual-polynomial lens. Its only noncomputab
- **1.00** `Spartan.FirstSumcheck.rbrKnowledgeSoundnessWith` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:397](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L397) vs `Spartan.SecondSumcheck.rbrKnowledgeSoundnessWith` [ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean:407](../../../ArkLib/ProofSystem/Spartan/Sumcheck/Second.lean#L407)
    - a: Fixed-prefix knowledge soundness for the named lifted certificate, with error `3 / |R|` per challeng
    - b: Fixed-prefix knowledge soundness for the named lifted certificate, with error `2 / |R|` per challeng
- **1.00** `Verifier.coordinateWiseSpecialSound_iff_exists` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean:281](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/Basic.lean#L281) vs `Verifier.treeSpecialSound_iff_exists` [ArkLib/OracleReduction/Security/TranscriptTree/Basic.lean:783](../../../ArkLib/OracleReduction/Security/TranscriptTree/Basic.lean#L783)
    - a: The existential notion is definitionally the existential closure of the named one.
    - b: The existential notion is definitionally the existential closure of the named one.
- **0.94** `ArkLib.Lattices.CyclotomicModulus.Rq.eq_zero_of_l1Norm_eq_zero` [ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean:320](../../../ArkLib/Data/Lattices/CyclotomicRing/NormBounds/Basic.lean#L320) vs `ArkLib.Lattices.CyclotomicModulus.Rq.eq_zero_of_l2NormSq_eq_zero` [ArkLib/Data/Lattices/CyclotomicRing/NormBounds/LyubashevskySeiler.lean:311](../../../ArkLib/Data/Lattices/CyclotomicRing/NormBounds/LyubashevskySeiler.lean#L311)
    - a: A ring element with zero centered `ℓ₁` norm is `0`: every centered coefficient representative below
    - b: A ring element with zero centered squared `ℓ₂` norm is `0`: every centered coefficient representativ
- **0.94** `Reduction.append_completeness_of_pure_verifiers` [ArkLib/OracleReduction/Composition/Sequential/Append/Completeness.lean:140](../../../ArkLib/OracleReduction/Composition/Sequential/Append/Completeness.lean#L140) vs `Reduction.append_completeness_of_guarded_verifiers` [ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean:153](../../../ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean#L153)
    - a: Sequential composition preserves completeness for pure verifiers when the prover execution factors a
    - b: Sequential composition preserves completeness for guarded verifiers when the prover execution factor
- **0.93** `ReedSolomon.exists_mathematicalUniformRatePartition_curve_exactPowerAgreement` [ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/MathematicalUniformRate.lean:60](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/MathematicalUniformRate.lean#L60) vs `ReedSolomon.exists_uniformRatePartition_curve_exactPowerAgreement` [ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/UniformRate.lean:54](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/Capacity/UniformRate.lean#L54)
    - a: The mathematical uniform rate-partition parameters give an explicit exceptional-set bound for a powe
    - b: The uniform rate-partition parameters give an explicit exceptional-set bound for a power-batched rec
- **0.92** `CubicStaircase.count` [ArkLib/ToMathlib/Combinatorics/CubicStaircase.lean:52](../../../ArkLib/ToMathlib/Combinatorics/CubicStaircase.lean#L52) vs `QuadraticStaircase.count` [ArkLib/ToMathlib/Combinatorics/QuadraticStaircase.lean:50](../../../ArkLib/ToMathlib/Combinatorics/QuadraticStaircase.lean#L50)
    - a: The number of natural triples `(x, b₀, b₁)` with `x + D * (b₀ + b₁) < D * L`, written as a sum over
    - b: The number of natural pairs `(x, u)` with `x + D * u < D * L`, written as a sum over `u`: there are
- **0.90** `BatchedFri.Spec.batchedFRI_perfectCompleteness` [ArkLib/ProofSystem/BatchedFri/EndToEnd.lean:69](../../../ArkLib/ProofSystem/BatchedFri/EndToEnd.lean#L69) vs `Fri.Spec.perfect_completeness` [ArkLib/ProofSystem/Fri/Spec/Completeness.lean:189](../../../ArkLib/ProofSystem/Fri/Spec/Completeness.lean#L189)
    - a: Exact common input evaluations give perfect completeness for every query count.
    - b: Exact input evaluations give perfect completeness for every query count.
- **0.89** `CubicStaircase.count_ge_cubic` [ArkLib/ToMathlib/Combinatorics/CubicStaircase.lean:140](../../../ArkLib/ToMathlib/Combinatorics/CubicStaircase.lean#L140) vs `QuadraticStaircase.count_ge_quadratic` [ArkLib/ToMathlib/Combinatorics/QuadraticStaircase.lean:115](../../../ArkLib/ToMathlib/Combinatorics/QuadraticStaircase.lean#L115)
    - a: `D * (max L 0) ^ 3 / 6 ≤ count D L` for every weight `D` and every real cutoff `L`. There is no hypo
    - b: `D * (max L 0) ^ 2 / 2 ≤ count D L` for every weight `D` and every real cutoff `L`. There is no hypo
- **0.89** `ReedSolomon.HiddenDerivative.exactInterpolationExponents` [ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Index.lean:165](../../../ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Index.lean#L165) vs `ReedSolomon.HiddenDerivative.weightedSupportExponents` [ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/WeightedSupport/Basic.lean:92](../../../ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/WeightedSupport/Basic.lean#L92)
    - a: The finite set of eligible exponents. It is specified through `Set.Finite.toFinset`, so it is not an
    - b: The finite set of weighted-support eligible exponents. It is specified through `Set.Finite.toFinset`
- **0.89** `ReedSolomon.HiddenDerivative.firstOrderExponents` [ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/FirstOrder/Space.lean:86](../../../ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/FirstOrder/Space.lean#L86) vs `ReedSolomon.HiddenDerivative.exactInterpolationExponents` [ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Index.lean:165](../../../ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Index.lean#L165)
    - a: The finite set of first-order eligible exponents. It is specified through `Set.Finite.toFinset`, so
    - b: The finite set of eligible exponents. It is specified through `Set.Finite.toFinset`, so it is not an
- **0.88** `Reduction.append_perfectCompleteness_of_pure_verifiers` [ArkLib/OracleReduction/Composition/Sequential/Append/Completeness.lean:156](../../../ArkLib/OracleReduction/Composition/Sequential/Append/Completeness.lean#L156) vs `Reduction.append_perfectCompleteness_of_guarded_verifiers` [ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean:169](../../../ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean#L169)
    - a: Pure verifiers compose perfectly when prover execution factors at the seam and the suffix is perfect
    - b: Guarded verifiers compose perfectly when prover execution factors at the seam and the suffix is perf
- **0.88** `ArkLib.Lattices.Ajtai.InnerOuter.hypercubePoint` [ArkLib/Commitments/Functional/Hachi/ZeroCheck/Constraints.lean:856](../../../ArkLib/Commitments/Functional/Hachi/ZeroCheck/Constraints.lean#L856) vs `MvPolynomial.hypercubePoint` [ArkLib/Data/MvPolynomial/Hypercube.lean:34](../../../ArkLib/Data/MvPolynomial/Hypercube.lean#L34)
    - a: Assemble a point from a fixed prefix and a Boolean suffix.
    - b: Assemble a full point from a fixed prefix and a Boolean suffix.
- **0.88** `Fri.Spec.Extractor.arrayProgram` [ArkLib/ProofSystem/Fri/Spec/Extraction/Traversal.lean:40](../../../ArkLib/ProofSystem/Fri/Spec/Extraction/Traversal.lean#L40) vs `CompPoly.Arithmetic.certifiedOfFn` [ArkLib/ToCompPoly/Univariate/Arithmetic.lean:85](../../../ArkLib/ToCompPoly/Univariate/Arithmetic.lean#L85)
    - a: Build a field array by certified operations on its explicit index list.
    - b: Build an array by certified operations on its explicit index list.
- **0.88** `PolynomialDifferential.initialJetEquation_mem_of_mem_initialJetPrimeFamily` [ArkLib/Data/Polynomial/Differential/TaylorChartGeometry.lean:212](../../../ArkLib/Data/Polynomial/Differential/TaylorChartGeometry.lean#L212) vs `PolynomialDifferential.initialJetEquation_mem_of_mem_highTaylorPrimeFamily` [ArkLib/Data/Polynomial/Differential/TaylorChartIncidence.lean:139](../../../ArkLib/Data/Polynomial/Differential/TaylorChartIncidence.lean#L139)
    - a: Every member of the initial prime family contains the initial equation.
    - b: Every member of the high-cut prime family contains the initial equation.
- **0.88** `Reduction.completeness_of_pure_states` [ArkLib/OracleReduction/Composition/Sequential/Append/Completeness.lean:82](../../../ArkLib/OracleReduction/Composition/Sequential/Append/Completeness.lean#L82) vs `Reduction.completeness_of_guarded_states` [ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean:100](../../../ArkLib/OracleReduction/Composition/Sequential/GuardedCompleteness.lean#L100)
    - a: Completeness from every deterministic oracle state implies completeness from any initial state distr
    - b: Completeness from every deterministic oracle state implies completeness from any initial state distr
- **0.88** `ReedSolomon.frobeniusSparseTaylorCuts` [ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FrobeniusIncidence.lean:45](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/FrobeniusIncidence.lean#L45) vs `ReedSolomon.frobeniusPowerSparseTaylorNumerators` [ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerTupleIncidence.lean:52](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerTupleIncidence.lean#L52)
    - a: The common Taylor numerators whose indices are not divisible by the Frobenius exponent.
    - b: The Taylor numerators whose indices are not divisible by the Frobenius exponent.
- **0.88** `Spartan.Computable.firstVirtual_toPolynomial` [ArkLib/ProofSystem/Spartan/Algebra/Computable.lean:100](../../../ArkLib/ProofSystem/Spartan/Algebra/Computable.lean#L100) vs `Spartan.FirstSumcheck.polynomial_val` [ArkLib/ProofSystem/Spartan/Sumcheck/First.lean:43](../../../ArkLib/ProofSystem/Spartan/Sumcheck/First.lean#L43)
    - a: The first computational virtual polynomial agrees with the semantic polynomial.
    - b: The computational materialization agrees with the semantic first virtual polynomial.
- **0.86** `CoordinateWise.ScalarRound.branchPathOf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean:297](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/ScalarRound.lean#L297) vs `CoordinateWise.SingleRound.branchPathOf` [ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean:268](../../../ArkLib/OracleReduction/Security/CoordinateWiseSpecialSoundness/SingleRound.lean#L268)
    - a: The root-to-leaf path of branch `j` of an **arbitrary** full scalar-round tree — the index at which
    - b: The root-to-leaf path of branch `j` of an **arbitrary** full single-round tree — the index at which
- **0.86** `Domain.CosetFftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/CosetFftDomain/Ops.lean:114](../../../ArkLib/Data/Domain/CosetFftDomain/Ops.lean#L114) vs `Domain.FftDomainClass.domain_implies_char_ne_2` [ArkLib/Data/Domain/FftDomain/Ops.lean:164](../../../ArkLib/Data/Domain/FftDomain/Ops.lean#L164)
    - a: The existence of a nontrivial smooth coset FFT domain rules out characteristic `2`.
    - b: The existence of a nontrivial smooth FFT domain rules out characteristic `2`.
- **0.86** `KZG.CommitmentScheme.t_sdh_error_bound` [ArkLib/Commitments/Functional/KZG/Binding.lean:729](../../../ArkLib/Commitments/Functional/KZG/Binding.lean#L729) vs `KZG.CommitmentScheme.arsdh_error_bound` [ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean:613](../../../ArkLib/Commitments/Functional/KZG/FunctionBinding/Basic.lean#L613)
    - a: The `t`-SDH experiment is bounded by the error for reductions in the assumed class.
    - b: The ARSDH experiment is bounded by the error for reductions in the assumed class.
- **0.86** `OracleVerifier.id_knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:722](../../../ArkLib/OracleReduction/Security/Basic.lean#L722) vs `Verifier.id_rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:759](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L759)
    - a: The identity / trivial verifier is perfectly knowledge sound.
    - b: The identity / trivial verifier is perfectly round-by-round knowledge sound.
- **0.86** `PolynomialDifferential.initialJetSeparant_notMem_of_mem_initialJetPrimeFamily` [ArkLib/Data/Polynomial/Differential/TaylorChartGeometry.lean:218](../../../ArkLib/Data/Polynomial/Differential/TaylorChartGeometry.lean#L218) vs `PolynomialDifferential.initialJetSeparant_notMem_of_mem_highTaylorPrimeFamily` [ArkLib/Data/Polynomial/Differential/TaylorChartIncidence.lean:132](../../../ArkLib/Data/Polynomial/Differential/TaylorChartIncidence.lean#L132)
    - a: No member of the initial prime family contains the initial separant.
    - b: No member of the high-cut prime family contains the initial separant.
- **0.86** `PolynomialDifferential.jetDegree_jetDerivative_le_sub` [ArkLib/Data/Polynomial/Differential/DerivativeDescent.lean:191](../../../ArkLib/Data/Polynomial/Differential/DerivativeDescent.lean#L191) vs `MvPolynomial.degreeOf_iterate_pderiv_le_sub` [ArkLib/ToMathlib/MvPolynomial/PDeriv.lean:172](../../../ArkLib/ToMathlib/MvPolynomial/PDeriv.lean#L172)
    - a: `a` derivatives in `Y_s` lower the degree in `Y_s` by at least `a`, in every characteristic.
    - b: `a` partial derivatives in `X i` lower the degree in `X i` by at least `a`, in every characteristic.
- **0.86** `ReedSolomon.HiddenDerivative.differentialWeightedDegree_lt_of_mem_firstOrderSpace` [ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/FirstOrder/Space.lean:151](../../../ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/FirstOrder/Space.lean#L151) vs `ReedSolomon.HiddenDerivative.differentialWeightedDegree_lt_of_mem_exactInterpolationSpace` [ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Index.lean:276](../../../ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Index.lean#L276)
    - a: Every member of the first-order space has specialization-weighted degree below `m * A`. The hypothes
    - b: Every member of the exact space has specialization-weighted degree below `m * A`. The hypothesis `0
- **0.86** `ReedSolomon.HiddenDerivative.johnsonFinMatrix_eq_zero_of_grade_lt` [ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/JohnsonCertificate.lean:304](../../../ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/JohnsonCertificate.lean#L304) vs `ReedSolomon.HiddenDerivative.weightedJohnsonFinMatrix_eq_zero_of_grade_lt` [ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/WeightedJohnsonCertificate.lean:192](../../../ArkLib/Data/CodingTheory/HiddenDerivative/Interpolation/Symbolic/WeightedJohnsonCertificate.lean#L192)
    - a: Flattened rows above the source grade vanish.
    - b: Flattened rows above a source column's jet grade vanish.
- **0.86** `ReedSolomon.HiddenDerivative.regularJointStageSum_mono_height` [ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/HybridConstants.lean:619](../../../ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/HybridConstants.lean#L619) vs `ReedSolomon.HiddenDerivative.firstOrderCurveJointStageOne_mono_height` [ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/StageCharges.lean:194](../../../ArkLib/Data/CodingTheory/HiddenDerivative/Parameters/FirstOrder/StageCharges.lean#L194)
    - a: The regular joint stage sum increases with the challenge degree.
    - b: The joint stage degree increases with the challenge degree.
- **0.86** `ReedSolomon.mem_admissibleChartTupleFamilyAtExponent_iff` [ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedGraphCounting.lean:67](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/PowerBatchedGraphCounting.lean#L67) vs `ReedSolomon.mem_admissibleChartPairFamily_iff` [ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/PairCounting.lean:434](../../../ArkLib/Data/CodingTheory/ReedSolomon/MutualCorrelatedAgreement/TaylorChart/PairCounting.lean#L434)
    - a: When `k ≤ L`, membership in the finite family is equivalent to chart admissibility.
    - b: Membership in the finite family is equivalent to admissibility when `k ≤ L`.
- **0.86** `Spartan.Computable.secondVirtual_degreeOf_le` [ArkLib/ProofSystem/Spartan/Algebra/Computable.lean:139](../../../ArkLib/ProofSystem/Spartan/Algebra/Computable.lean#L139) vs `Spartan.Algebra.secondVirtual_degree_le_two` [ArkLib/ProofSystem/Spartan/Algebra/Identities.lean:202](../../../ArkLib/ProofSystem/Spartan/Algebra/Identities.lean#L202)
    - a: The second computational virtual polynomial has individual degree at most two.
    - b: The second virtual polynomial has individual degree at most two.
- **0.86** `Verifier.id_knowledgeSoundness` [ArkLib/OracleReduction/Security/Basic.lean:659](../../../ArkLib/OracleReduction/Security/Basic.lean#L659) vs `Verifier.id_rbrKnowledgeSoundness` [ArkLib/OracleReduction/Security/RoundByRound.lean:759](../../../ArkLib/OracleReduction/Security/RoundByRound.lean#L759)
    - a: The identity / trivial verifier is perfectly knowledge sound.
    - b: The identity / trivial verifier is perfectly round-by-round knowledge sound.
- **0.86** `proximity_gap_degree_bound` [ArkLib/Data/CodingTheory/GuruswamiSudan/Basic.lean:54](../../../ArkLib/Data/CodingTheory/GuruswamiSudan/Basic.lean#L54) vs `ProximityGap.D_X` [ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean:51](../../../ArkLib/Data/CodingTheory/ProximityGap/BCIKS20/ListDecoding/Guruswami.lean#L51)
    - a: The degree bound (i.e. `D_X(m) = (m + 1/2) * √ρ * n`) for instantiation of Guruswami-Sudan in Lemma
    - b: The degree bound (a.k.a. `D_X`) for instantiation of Guruswami-Sudan in Lemma 5.3 of [BCIKS20]. `D_X

